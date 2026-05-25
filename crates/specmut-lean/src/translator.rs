//! Five-pass translation from JSON IR (Phase A) to FOL `(Signature, Vec<Formula>)`.
//!
//! See the Phase B spec §4.2 for the algorithm.  In summary:
//!
//! 1. **Sorts** — built-ins (`Nat`/`Int`/`Bool`) plus everything in `ir.sorts`,
//!    plus mangled parameterized types harvested from usage.
//! 2. **Functions** — constructors + named functions + arithmetic operators
//!    auto-declared on first use.
//! 3. **Relations** — predicates + `leq`/`lt`/`mem` auto-declared on first use.
//! 4. **Predicate axioms** — equation lemmas → biconditionals (preferred over
//!    body for recursive predicates); body → biconditional fallback otherwise.
//! 5. **Theorem axioms** — hypothesis chain → implication chain, NNF-normalised
//!    and validated as sentences.
//!
//! Auto-declared symbols are merged into the signature after Pass 5 so the
//! `Signature::new` invariant check sees a consistent set.

use std::collections::{BTreeMap, BTreeSet};

use specmut_core::formula::{Formula, Term};
use specmut_core::signature::{
    FunctionSymbol, RelationSymbol, Signature, SignatureError, SortSymbol,
};

use crate::ir_types::{
    IRConstructor, IREquation, IRExpr, IRFunction, IRParam, IRPredicate, IRSort, IRTheorem,
    LeanIR, BUILTIN_SORTS,
};

/// Successful (possibly partial) result of translating a `LeanIR`.
#[derive(Debug)]
pub struct TranslationResult {
    /// The reconstructed FOL signature, after sort filtering + dedup.
    pub signature: Signature,
    /// Translated axioms (theorems + predicate equations + predicate bodies),
    /// deduplicated.
    pub axioms: Vec<Formula>,
    /// Provenance of each axiom — parallel to `axioms` (same length, same order).
    /// The slicer in `specmut_lean::slicer` reads this to split per theorem.
    /// After dedup, an axiom that arose from multiple sources keeps the
    /// first-seen origin only.
    pub axiom_origins: Vec<AxiomOrigin>,
    /// Theorems that successfully translated.
    pub translated_theorems: Vec<String>,
    /// `(name, reason)` for theorems that were skipped.
    pub skipped_theorems: Vec<(String, String)>,
    /// Predicates that successfully translated (at least one axiom emitted).
    pub translated_predicates: Vec<String>,
    /// `(name, reason)` for predicates that contributed no axioms.
    pub skipped_predicates: Vec<(String, String)>,
    /// Non-fatal warnings raised during translation, including any inherited
    /// from the input IR.
    pub warnings: Vec<String>,
    /// Metadata describing the sort-filtering pass: how many sorts were in the
    /// raw signature, how many survived, and which were dropped.
    pub sort_filter: SortFilterReport,
}

/// Where a translated axiom came from in the source IR.  Surfaced via
/// [`TranslationResult::axiom_origins`] so the per-theorem slicer can
/// partition the axiom set.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AxiomOrigin {
    /// One of the equation lemmas attached to a predicate.
    PredicateEquation {
        /// Predicate this equation defines.
        predicate_name: String,
        /// Position of the equation in the predicate's `equations` list,
        /// zero-indexed.
        equation_index: usize,
    },
    /// Fallback body translation for a predicate with no usable equations.
    PredicateBody {
        /// Predicate this body axiom defines.
        predicate_name: String,
    },
    /// A theorem statement.
    TheoremStatement {
        /// Source theorem identifier.
        theorem_name: String,
    },
}

/// What the sort-filter pass removed.  Surfaced in the JSON report so callers
/// understand why the model space stays bounded on Lean specs that drag in
/// stdlib types as type arguments.
#[derive(Debug, Clone, Default)]
pub struct SortFilterReport {
    /// Sort count before filtering.
    pub original_sorts: usize,
    /// Sort count after filtering (equals `signature.sorts.len()`).
    pub filtered_sorts: usize,
    /// Sort names that were dropped, sorted alphabetically.
    pub removed: Vec<String>,
}

/// Fatal translation errors.  Partial failures live in `skipped_*` vectors.
#[derive(Debug, thiserror::Error)]
pub enum TranslationError {
    /// Translation produced zero axioms across all theorems and predicates.
    #[error("no translatable content: {reason}")]
    NothingTranslatable {
        /// Diagnostic describing why nothing was translatable.
        reason: String,
    },

    /// `Signature::new` rejected the synthesised signature.
    #[error("signature construction failed: {0}")]
    SignatureError(#[from] SignatureError),
}

/// Stateless translator façade.
pub struct LeanTranslator;

impl LeanTranslator {
    /// Translate an IR document into a FOL signature + axioms.
    pub fn translate(ir: &LeanIR) -> Result<TranslationResult, TranslationError> {
        let mut state = State::new(ir);
        state.run_pass1_sorts();
        state.run_pass2_functions();
        state.run_pass3_relations();
        state.run_pass4_predicate_axioms();
        state.run_pass5_theorem_axioms();
        state.finalize()
    }
}

// ============================================================================
// Internal translator state
// ============================================================================

struct State<'a> {
    ir: &'a LeanIR,

    sort_map: BTreeMap<String, SortSymbol>,
    /// Predicate names from `ir.predicates` (and auto-declared ones from
    /// `leq`/`lt`/`mem`).  Used to disambiguate application heads as relation
    /// vs function in proposition context.
    predicate_names: BTreeSet<String>,
    /// Sorts of each predicate's parameters, by name — used to translate
    /// recursive references inside equations / theorems.
    predicate_arities: BTreeMap<String, Vec<SortSymbol>>,
    /// Function symbols declared explicitly (constructors + ir.functions).
    declared_functions: BTreeMap<String, FunctionSymbol>,
    /// Function symbols auto-declared during expression translation
    /// (arithmetic operators, succ/zero for nat literals).
    auto_functions: BTreeMap<String, FunctionSymbol>,
    /// Relation symbols declared from ir.predicates.
    declared_relations: BTreeMap<String, RelationSymbol>,
    /// Relation symbols auto-declared from `leq`/`lt`/`mem` usage.
    auto_relations: BTreeMap<String, RelationSymbol>,

    axioms: Vec<Formula>,
    axiom_origins: Vec<AxiomOrigin>,
    translated_theorems: Vec<String>,
    skipped_theorems: Vec<(String, String)>,
    translated_predicates: Vec<String>,
    skipped_predicates: Vec<(String, String)>,
    warnings: Vec<String>,
}

impl<'a> State<'a> {
    fn new(ir: &'a LeanIR) -> Self {
        Self {
            ir,
            sort_map: BTreeMap::new(),
            predicate_names: BTreeSet::new(),
            predicate_arities: BTreeMap::new(),
            declared_functions: BTreeMap::new(),
            auto_functions: BTreeMap::new(),
            declared_relations: BTreeMap::new(),
            auto_relations: BTreeMap::new(),
            axioms: Vec::new(),
            axiom_origins: Vec::new(),
            translated_theorems: Vec::new(),
            skipped_theorems: Vec::new(),
            translated_predicates: Vec::new(),
            skipped_predicates: Vec::new(),
            warnings: ir.warnings.clone(),
        }
    }

    fn record_axiom(&mut self, axiom: Formula, origin: AxiomOrigin) {
        self.axioms.push(axiom);
        self.axiom_origins.push(origin);
    }

    // ------------------------------------------------------------------------
    // Pass 1: sorts
    // ------------------------------------------------------------------------

    fn run_pass1_sorts(&mut self) {
        for name in BUILTIN_SORTS {
            self.sort_map.insert((*name).to_string(), SortSymbol::new(*name));
        }
        for IRSort { name, .. } in &self.ir.sorts {
            // Phase G: skip noise sort declarations (stdlib re-exports,
            // type-class dictionaries, etc.) entirely.
            if is_noise_sort_name(name) {
                continue;
            }
            self.sort_map
                .entry(name.clone())
                .or_insert_with(|| SortSymbol::new(name));
        }
        // Scan every sort identifier referenced anywhere in the IR.
        let mut referenced: BTreeSet<String> = BTreeSet::new();
        for c in &self.ir.constructors {
            referenced.insert(c.sort.clone());
            for f in &c.fields {
                referenced.insert(f.clone());
            }
        }
        for f in &self.ir.functions {
            for d in &f.domain {
                referenced.insert(d.clone());
            }
            referenced.insert(f.codomain.clone());
        }
        for p in &self.ir.predicates {
            for param in &p.params {
                referenced.insert(param.sort.clone());
            }
            for eq in &p.equations {
                for v in &eq.vars {
                    referenced.insert(v.sort.clone());
                }
            }
        }
        for name in referenced {
            // Phase G: same noise filter as for declared sorts.  Without
            // this, equation-lemma binders over `[Ord α]` would auto-
            // register `instOrd...` as a sort.
            if is_noise_sort_name(&name) {
                continue;
            }
            self.sort_map
                .entry(name.clone())
                .or_insert_with(|| SortSymbol::new(&name));
        }
    }

    fn resolve_sort(&mut self, name: &str) -> SortSymbol {
        if let Some(s) = self.sort_map.get(name) {
            return s.clone();
        }
        if is_unknown_sort(name) {
            // Fall back to a default sort.  The first declared sort if any,
            // otherwise `Nat`.  This branch is only hit for `_Unknown` /
            // `_Sort` placeholders the exporter couldn't classify.
            let fallback = self
                .sort_map
                .keys()
                .next()
                .cloned()
                .unwrap_or_else(|| "Nat".to_string());
            self.warnings.push(format!(
                "placeholder sort '{name}' fell back to '{fallback}'"
            ));
            return self.sort_map[&fallback].clone();
        }
        let symbol = SortSymbol::new(name);
        self.sort_map.insert(name.to_string(), symbol.clone());
        symbol
    }

    // ------------------------------------------------------------------------
    // Pass 2: functions
    // ------------------------------------------------------------------------

    fn run_pass2_functions(&mut self) {
        // Constructors become function symbols whose codomain is the parent inductive.
        let ctors: Vec<IRConstructor> = self.ir.constructors.clone();
        for c in ctors {
            // Phase G: a constructor that references a noise sort
            // (e.g. a field typed `[Inhabited α]`) does not represent
            // spec content.  Drop it.
            if is_noise_sort_name(&c.sort)
                || c.fields.iter().any(|f| is_noise_sort_name(f))
            {
                self.warnings.push(format!(
                    "skipped constructor '{}' — references noise sort",
                    c.name
                ));
                continue;
            }
            let codomain = self.resolve_sort(&c.sort);
            let domain: Vec<SortSymbol> = c
                .fields
                .iter()
                .map(|f| self.resolve_sort(f))
                .collect();
            let fn_sym = FunctionSymbol::new(&c.name, domain, codomain);
            self.declared_functions.insert(c.name.clone(), fn_sym);
        }
        // Named functions from IR.  Skip auto-derived type-class instances
        // (Lean conventionally prefixes those with `inst…`) — their equations
        // are pretty-print plumbing rather than spec content, and they tend
        // to drag in stdlib sorts (`Std_Format`, etc.) that bloat the model
        // space without representing the user's specification.
        let fns: Vec<IRFunction> = self.ir.functions.clone();
        for f in fns {
            if is_typeclass_instance(&f.name) {
                continue;
            }
            // Phase G: drop functions whose domain or codomain mentions
            // a Phase G noise sort.
            if is_noise_sort_name(&f.codomain)
                || f.domain.iter().any(|d| is_noise_sort_name(d))
            {
                self.warnings.push(format!(
                    "skipped function '{}' — references noise sort",
                    f.name
                ));
                continue;
            }
            let domain: Vec<SortSymbol> =
                f.domain.iter().map(|d| self.resolve_sort(d)).collect();
            let codomain = self.resolve_sort(&f.codomain);
            let fn_sym = FunctionSymbol::new(&f.name, domain, codomain);
            self.declared_functions.insert(f.name.clone(), fn_sym);
        }
    }

    // ------------------------------------------------------------------------
    // Pass 3: relations
    // ------------------------------------------------------------------------

    fn run_pass3_relations(&mut self) {
        let preds: Vec<IRPredicate> = self.ir.predicates.clone();
        for p in preds {
            // Phase G: a predicate whose own parameter list mentions a
            // noise sort isn't a spec predicate — drop it before it
            // pollutes the relation set.
            if p.params.iter().any(|param| is_noise_sort_name(&param.sort)) {
                self.warnings.push(format!(
                    "skipped predicate '{}' — parameter mentions noise sort",
                    p.name
                ));
                continue;
            }
            let arity: Vec<SortSymbol> =
                p.params.iter().map(|param| self.resolve_sort(&param.sort)).collect();
            self.predicate_arities.insert(p.name.clone(), arity.clone());
            self.predicate_names.insert(p.name.clone());
            let rel = RelationSymbol::new(&p.name, arity);
            self.declared_relations.insert(p.name.clone(), rel);
        }
    }

    // ------------------------------------------------------------------------
    // Pass 4: predicate axioms
    // ------------------------------------------------------------------------

    fn run_pass4_predicate_axioms(&mut self) {
        let predicates: Vec<IRPredicate> = self.ir.predicates.clone();
        for p in predicates {
            let mut emitted_any = false;
            // Prefer equations over body when present.
            if !p.equations.is_empty() {
                let mut pending_warnings: Vec<String> = Vec::new();
                for (i, eq) in p.equations.iter().enumerate() {
                    // Phase G: strip type-class dictionary arguments and
                    // other irrelevant unsupported nodes before
                    // translation.  Recovers equations that would
                    // otherwise fail on a single instance argument.
                    let sanitized = sanitize_equation(eq);
                    match self.translate_equation(&sanitized) {
                        Ok(axiom) => {
                            self.record_axiom(
                                axiom,
                                AxiomOrigin::PredicateEquation {
                                    predicate_name: p.name.clone(),
                                    equation_index: i,
                                },
                            );
                            emitted_any = true;
                        }
                        Err(e) => {
                            pending_warnings.push(format!(
                                "{}.eq_{}: {}",
                                p.name,
                                i + 1,
                                e
                            ));
                        }
                    }
                }
                // Phase G WI3: when at least one equation succeeded,
                // mark each per-equation warning as a "Partial:" entry
                // so callers can distinguish partial recovery from a
                // full skip.  When everything failed the warnings stay
                // as-is and the predicate falls through to the
                // skipped_predicates path below.
                if emitted_any {
                    for w in pending_warnings {
                        self.warnings.push(format!("Partial: {w}"));
                    }
                } else {
                    for w in pending_warnings {
                        self.warnings.push(w);
                    }
                }
            } else {
                // Fall back to body translation: ∀ params, P(params) ↔ body.
                match self.translate_predicate_body(&p) {
                    Ok(axiom) => {
                        self.record_axiom(
                            axiom,
                            AxiomOrigin::PredicateBody {
                                predicate_name: p.name.clone(),
                            },
                        );
                        emitted_any = true;
                    }
                    Err(e) => {
                        self.skipped_predicates
                            .push((p.name.clone(), e.to_string()));
                    }
                }
            }
            if emitted_any {
                self.translated_predicates.push(p.name.clone());
            } else if !p.equations.is_empty() {
                self.skipped_predicates.push((
                    p.name.clone(),
                    "all equations contained unsupported nodes".into(),
                ));
            }
        }
    }

    fn translate_equation(&mut self, eq: &IREquation) -> Result<Formula, ExprError> {
        let mut var_stack: Vec<(String, SortSymbol)> = Vec::new();
        for v in &eq.vars {
            let sort = self.resolve_sort(&v.sort);
            var_stack.push((v.name.clone(), sort));
        }
        // LHS/RHS translate in proposition context (the equation lemma is a Prop).
        let lhs = self.translate_prop(&eq.lhs, &mut var_stack)?;
        let rhs = self.translate_prop(&eq.rhs, &mut var_stack)?;
        // Emit `lhs ↔ rhs` desugared to (lhs → rhs) ∧ (rhs → lhs), then wrap
        // in universal quantifiers for each binder (in reverse so the
        // outermost binder is added last).
        let iff = and(implies(lhs.clone(), rhs.clone()), implies(rhs, lhs));
        let body = wrap_quantifiers(iff, &eq.vars, &self.sort_map);
        Ok(Formula::to_nnf(body))
    }

    fn translate_predicate_body(&mut self, p: &IRPredicate) -> Result<Formula, ExprError> {
        if contains_unsupported(&p.body) {
            return Err(ExprError::UnsupportedNode(
                "predicate body contains unsupported node".into(),
            ));
        }
        let mut var_stack: Vec<(String, SortSymbol)> = Vec::new();
        for param in &p.params {
            let sort = self.resolve_sort(&param.sort);
            var_stack.push((param.name.clone(), sort));
        }
        let body = self.translate_prop(&p.body, &mut var_stack)?;
        // Build the head atom P(p_0, p_1, ..., p_{n-1}) — the most recently
        // bound variable has de Bruijn index 0.
        let rel = self
            .declared_relations
            .get(&p.name)
            .cloned()
            .ok_or_else(|| ExprError::UnknownSymbol(p.name.clone()))?;
        let n = p.params.len();
        let args: Vec<Term> = (0..n).rev().map(Term::Var).collect();
        let head = Formula::Atom { relation: rel, args };
        let iff = and(
            implies(head.clone(), body.clone()),
            implies(body, head),
        );
        let wrapped = wrap_quantifiers(iff, &p.params, &self.sort_map);
        Ok(Formula::to_nnf(wrapped))
    }

    // ------------------------------------------------------------------------
    // Pass 5: theorem axioms
    // ------------------------------------------------------------------------

    fn run_pass5_theorem_axioms(&mut self) {
        let theorems: Vec<IRTheorem> = self.ir.theorems.clone();
        for t in theorems {
            match self.translate_theorem(&t) {
                Ok(f) => {
                    if !f.is_sentence() {
                        self.skipped_theorems.push((
                            t.name.clone(),
                            "translated formula has free variables".into(),
                        ));
                        continue;
                    }
                    self.record_axiom(
                        Formula::to_nnf(f),
                        AxiomOrigin::TheoremStatement {
                            theorem_name: t.name.clone(),
                        },
                    );
                    self.translated_theorems.push(t.name);
                }
                Err(e) => self
                    .skipped_theorems
                    .push((t.name.clone(), e.to_string())),
            }
        }
    }

    fn translate_theorem(&mut self, t: &IRTheorem) -> Result<Formula, ExprError> {
        // Hypotheses translate first (still in the outer context), then the
        // conclusion.  Hypotheses are propositions in their own right; we
        // chain them as a right-associated implication tree:
        //   H₁ → H₂ → … → Hₙ → C
        let mut var_stack: Vec<(String, SortSymbol)> = Vec::new();
        let hyp_formulas: Result<Vec<Formula>, ExprError> = t
            .hypotheses
            .iter()
            .map(|h| self.translate_prop(h.body(), &mut var_stack))
            .collect();
        let hyps = hyp_formulas?;
        let conclusion = self.translate_prop(&t.conclusion, &mut var_stack)?;
        let body = hyps.into_iter().rev().fold(conclusion, |acc, h| implies(h, acc));
        Ok(body)
    }

    // ------------------------------------------------------------------------
    // Expression translation
    // ------------------------------------------------------------------------

    /// Translate `e` in proposition position.  The caller's `var_stack` is
    /// shared across recursive calls but pops/pushes happen only at binder
    /// boundaries inside this function.
    fn translate_prop(
        &mut self,
        e: &IRExpr,
        var_stack: &mut Vec<(String, SortSymbol)>,
    ) -> Result<Formula, ExprError> {
        match e {
            IRExpr::True => Ok(Formula::Top),
            IRExpr::False => Ok(Formula::Bot),
            IRExpr::Unsupported { description } => {
                Err(ExprError::UnsupportedNode(description.clone()))
            }
            IRExpr::And { left, right } => {
                let l = self.translate_prop(left, var_stack)?;
                let r = self.translate_prop(right, var_stack)?;
                Ok(and(l, r))
            }
            IRExpr::Or { left, right } => {
                let l = self.translate_prop(left, var_stack)?;
                let r = self.translate_prop(right, var_stack)?;
                Ok(or(l, r))
            }
            IRExpr::Not { body } => {
                let inner = self.translate_prop(body, var_stack)?;
                Ok(Formula::Not(Box::new(inner)))
            }
            IRExpr::Implies { left, right } => {
                let l = self.translate_prop(left, var_stack)?;
                let r = self.translate_prop(right, var_stack)?;
                Ok(implies(l, r))
            }
            IRExpr::Iff { left, right } => {
                let l = self.translate_prop(left, var_stack)?;
                let r = self.translate_prop(right, var_stack)?;
                Ok(and(implies(l.clone(), r.clone()), implies(r, l)))
            }
            IRExpr::Forall { var, sort, body } => {
                let sort = self.resolve_sort(sort);
                var_stack.push((var.clone(), sort.clone()));
                let inner = self.translate_prop(body, var_stack);
                var_stack.pop();
                let inner = inner?;
                Ok(Formula::Forall {
                    sort,
                    body: Box::new(inner),
                })
            }
            IRExpr::Exists { var, sort, body } => {
                let sort = self.resolve_sort(sort);
                var_stack.push((var.clone(), sort.clone()));
                let inner = self.translate_prop(body, var_stack);
                var_stack.pop();
                let inner = inner?;
                Ok(Formula::Exists {
                    sort,
                    body: Box::new(inner),
                })
            }
            IRExpr::Eq { left, right } => {
                let l = self.translate_term(left, var_stack)?;
                let r = self.translate_term(right, var_stack)?;
                Ok(Formula::Eq(l, r))
            }
            IRExpr::Neq { left, right } => {
                let l = self.translate_term(left, var_stack)?;
                let r = self.translate_term(right, var_stack)?;
                Ok(Formula::Neq(l, r))
            }
            IRExpr::Leq { left, right } => {
                let l = self.translate_term(left, var_stack)?;
                let r = self.translate_term(right, var_stack)?;
                let s = infer_term_sort(&l, var_stack, &self.declared_functions, &self.auto_functions)
                    .unwrap_or_else(|| SortSymbol::new("Nat"));
                let rel = self.ensure_relation("leq", &[s.clone(), s]);
                Ok(Formula::Atom {
                    relation: rel,
                    args: vec![l, r],
                })
            }
            IRExpr::Lt { left, right } => {
                let l = self.translate_term(left, var_stack)?;
                let r = self.translate_term(right, var_stack)?;
                let s = infer_term_sort(&l, var_stack, &self.declared_functions, &self.auto_functions)
                    .unwrap_or_else(|| SortSymbol::new("Nat"));
                let rel = self.ensure_relation("lt", &[s.clone(), s]);
                Ok(Formula::Atom {
                    relation: rel,
                    args: vec![l, r],
                })
            }
            IRExpr::Mem { element, collection } => {
                let el = self.translate_term(element, var_stack)?;
                let col = self.translate_term(collection, var_stack)?;
                let el_sort = infer_term_sort(
                    &el,
                    var_stack,
                    &self.declared_functions,
                    &self.auto_functions,
                )
                .unwrap_or_else(|| SortSymbol::new("Nat"));
                let col_sort = infer_term_sort(
                    &col,
                    var_stack,
                    &self.declared_functions,
                    &self.auto_functions,
                )
                .unwrap_or_else(|| SortSymbol::new("Nat"));
                let rel = self.ensure_relation("mem", &[el_sort, col_sort]);
                Ok(Formula::Atom {
                    relation: rel,
                    args: vec![el, col],
                })
            }
            IRExpr::App { fn_name, args } => {
                // Application in proposition context: either a known predicate
                // (→ Atom) or a context mismatch (the IR claimed a function-app
                // is a Prop).
                if self.predicate_names.contains(fn_name) {
                    let arity = self.predicate_arities[fn_name].clone();
                    let filtered: Vec<&IRExpr> = args
                        .iter()
                        .filter(|a| !self.is_type_arg_noise(a))
                        .collect();
                    let translated_args: Result<Vec<Term>, _> = filtered
                        .iter()
                        .map(|a| self.translate_term(a, var_stack))
                        .collect();
                    let translated_args = translated_args?;
                    let relation = RelationSymbol::new(fn_name, arity);
                    return Ok(Formula::Atom {
                        relation,
                        args: translated_args,
                    });
                }
                Err(ExprError::ContextMismatch {
                    expected: "proposition",
                    got: format!("function application '{fn_name}'"),
                })
            }
            IRExpr::Var { name } => Err(ExprError::ContextMismatch {
                expected: "proposition",
                got: format!("bare variable reference '{name}'"),
            }),
            IRExpr::NatLit { value } => Err(ExprError::ContextMismatch {
                expected: "proposition",
                got: format!("nat literal {value}"),
            }),
        }
    }

    /// Translate `e` in term position.
    fn translate_term(
        &mut self,
        e: &IRExpr,
        var_stack: &mut Vec<(String, SortSymbol)>,
    ) -> Result<Term, ExprError> {
        match e {
            IRExpr::Var { name } => {
                // Search the var_stack from the END (most-recent binder first).
                // The de Bruijn index is the distance from the top.
                if let Some((idx, _)) = var_stack
                    .iter()
                    .rev()
                    .enumerate()
                    .find(|(_, (n, _))| n == name)
                {
                    return Ok(Term::Var(idx));
                }
                // Free constant: declare as a nullary function.
                let fn_sym = self.ensure_constant(name);
                Ok(Term::App {
                    function: fn_sym,
                    args: vec![],
                })
            }
            IRExpr::NatLit { value } => Ok(self.nat_literal(*value)),
            IRExpr::App { fn_name, args } => {
                // Strip type-argument noise.  Lean's elaborated form leaks
                // explicit type arguments like the `Nat` in `List.cons Nat x xs`;
                // these would clash with declared sorts if auto-declared as
                // function symbols.  We filter args that are bare references
                // to known sorts.
                let filtered_args: Vec<&IRExpr> = args
                    .iter()
                    .filter(|a| !self.is_type_arg_noise(a))
                    .collect();
                let translated_args: Result<Vec<Term>, _> = filtered_args
                    .iter()
                    .map(|a| self.translate_term(a, var_stack))
                    .collect();
                let translated_args = translated_args?;
                let fn_sym = self.lookup_or_auto_declare_function(fn_name, &translated_args, var_stack);
                Ok(Term::App {
                    function: fn_sym,
                    args: translated_args,
                })
            }
            IRExpr::Unsupported { description } => {
                Err(ExprError::UnsupportedNode(description.clone()))
            }
            other => Err(ExprError::ContextMismatch {
                expected: "term",
                got: format!("propositional node {:?}", node_kind(other)),
            }),
        }
    }

    fn nat_literal(&mut self, value: u64) -> Term {
        let nat = SortSymbol::new("Nat");
        let zero = FunctionSymbol::new("zero", vec![], nat.clone());
        let succ = FunctionSymbol::new("succ", vec![nat.clone()], nat);
        self.auto_functions
            .entry("zero".into())
            .or_insert_with(|| zero.clone());
        self.auto_functions
            .entry("succ".into())
            .or_insert_with(|| succ.clone());
        if value > 16 {
            self.warnings.push(format!(
                "literal {value} expanded into succ-chain of length {value}; \
                 model enumeration with small bounds will not represent it"
            ));
        }
        let mut term = Term::App {
            function: zero,
            args: vec![],
        };
        for _ in 0..value {
            term = Term::App {
                function: succ.clone(),
                args: vec![term],
            };
        }
        term
    }

    fn ensure_constant(&mut self, name: &str) -> FunctionSymbol {
        if let Some(f) = self.declared_functions.get(name) {
            return f.clone();
        }
        if let Some(f) = self.auto_functions.get(name) {
            return f.clone();
        }
        // Choose a default sort.  Prefer the only declared sort if there is
        // one (so e.g. an undeclared `Tree.leaf` in a Tree-only signature ends
        // up sorted as Tree); otherwise default to Nat.
        let codomain = self.default_sort();
        let fn_sym = FunctionSymbol::new(name, vec![], codomain);
        self.auto_functions.insert(name.to_string(), fn_sym.clone());
        self.warnings
            .push(format!("auto-declared constant '{name}' : {}", fn_sym.codomain.name));
        fn_sym
    }

    fn lookup_or_auto_declare_function(
        &mut self,
        name: &str,
        args: &[Term],
        var_stack: &[(String, SortSymbol)],
    ) -> FunctionSymbol {
        if let Some(f) = self.declared_functions.get(name) {
            return f.clone();
        }
        if let Some(f) = self.auto_functions.get(name) {
            return f.clone();
        }
        // Try to infer sorts from the argument terms.
        let inferred_domain: Vec<SortSymbol> = args
            .iter()
            .map(|t| {
                infer_term_sort(t, var_stack, &self.declared_functions, &self.auto_functions)
                    .unwrap_or_else(|| self.default_sort())
            })
            .collect();
        let codomain = inferred_domain.first().cloned().unwrap_or_else(|| self.default_sort());
        let fn_sym = FunctionSymbol::new(name, inferred_domain, codomain);
        self.auto_functions.insert(name.to_string(), fn_sym.clone());
        self.warnings
            .push(format!("auto-declared function '{name}' from usage"));
        fn_sym
    }

    fn ensure_relation(&mut self, name: &str, arity: &[SortSymbol]) -> RelationSymbol {
        if let Some(r) = self.declared_relations.get(name) {
            return r.clone();
        }
        if let Some(r) = self.auto_relations.get(name) {
            return r.clone();
        }
        // Avoid colliding with a sort or function symbol that already uses
        // this name — `Signature::new` will reject duplicates and ruin the
        // whole translation.
        let effective_name = self.unique_symbol_name(name);
        let rel = RelationSymbol::new(&effective_name, arity.to_vec());
        self.auto_relations.insert(effective_name.clone(), rel.clone());
        if effective_name != name {
            self.warnings.push(format!(
                "auto-declared relation '{effective_name}' (renamed from '{name}' to avoid sort collision)"
            ));
        } else {
            self.warnings.push(format!(
                "auto-declared relation '{name}' from usage"
            ));
        }
        rel
    }

    /// Produce a symbol name that doesn't collide with an existing sort,
    /// declared function, declared relation, or auto-declared symbol.  The
    /// `_auto_` prefix scheme matches the convention in the Phase D spec §7.1.
    fn unique_symbol_name(&self, name: &str) -> String {
        let taken = |n: &str| -> bool {
            self.sort_map.contains_key(n)
                || self.declared_functions.contains_key(n)
                || self.auto_functions.contains_key(n)
                || self.declared_relations.contains_key(n)
                || self.auto_relations.contains_key(n)
        };
        if !taken(name) {
            return name.to_string();
        }
        let candidate = format!("_auto_{name}");
        if !taken(&candidate) {
            return candidate;
        }
        // Pathological — append a counter until it's free.
        for i in 1u32.. {
            let next = format!("_auto_{name}_{i}");
            if !taken(&next) {
                return next;
            }
        }
        unreachable!("u32 exhausted while finding a free name");
    }

    /// True iff `e` is a bare reference to a known sort — i.e. type-argument
    /// noise emitted by Lean's elaborator (e.g. the `Nat` in
    /// `List.cons Nat x xs`).  These args must be stripped before
    /// auto-declaration, otherwise they collide with the sort by name.
    fn is_type_arg_noise(&self, e: &IRExpr) -> bool {
        match e {
            IRExpr::App { fn_name, args } if args.is_empty() => {
                self.sort_map.contains_key(fn_name)
            }
            _ => false,
        }
    }

    fn default_sort(&self) -> SortSymbol {
        // The first declared sort if any; otherwise Nat.  Stable across runs
        // because `sort_map` is a BTreeMap.
        self.sort_map
            .values()
            .next()
            .cloned()
            .unwrap_or_else(|| SortSymbol::new("Nat"))
    }

    // ------------------------------------------------------------------------
    // Finalisation
    // ------------------------------------------------------------------------

    fn finalize(mut self) -> Result<TranslationResult, TranslationError> {
        if self.axioms.is_empty() {
            return Err(TranslationError::NothingTranslatable {
                reason: format!(
                    "skipped {} theorems, {} predicates; no axioms emitted",
                    self.skipped_theorems.len(),
                    self.skipped_predicates.len()
                ),
            });
        }

        // Deduplicate axioms — recursive predicates and theorems can produce
        // identical formulas (e.g. an equation lemma whose normalised form
        // matches another's).  Dedupe before sort filtering so the reachable
        // set is computed from the canonical formula list.  Origins ride
        // along in parallel: when a duplicate is dropped, its origin goes
        // with it (first-seen origin survives).
        let (axioms, axiom_origins) = deduplicate_axioms_with_origins(
            std::mem::take(&mut self.axioms),
            std::mem::take(&mut self.axiom_origins),
        );

        let sorts: Vec<SortSymbol> = self.sort_map.values().cloned().collect();

        // Merge declared + auto-declared functions, preferring declared on conflict.
        let mut functions: BTreeMap<String, FunctionSymbol> = self.declared_functions;
        for (name, fn_sym) in self.auto_functions {
            functions.entry(name).or_insert(fn_sym);
        }
        let functions: Vec<FunctionSymbol> = functions.into_values().collect();

        let mut relations: BTreeMap<String, RelationSymbol> = self.declared_relations;
        for (name, rel) in self.auto_relations {
            relations.entry(name).or_insert(rel);
        }
        let relations: Vec<RelationSymbol> = relations.into_values().collect();

        let raw_signature = Signature::new(sorts, functions, relations)?;
        let original_sort_count = raw_signature.sorts.len();

        // Prune sorts (and dependent functions/relations) not reachable from
        // the axioms.  Drops stdlib noise like `Std_Format`/`Bool`/`Prop` that
        // Phase A surfaces as Lean type arguments but the spec never references.
        let signature = filter_signature(&raw_signature, &axioms)?;

        let mut removed: Vec<String> = raw_signature
            .sorts
            .iter()
            .filter(|s| !signature.sorts.contains(*s))
            .map(|s| s.name.clone())
            .collect();
        removed.sort();
        let sort_filter = SortFilterReport {
            original_sorts: original_sort_count,
            filtered_sorts: signature.sorts.len(),
            removed,
        };

        let mut warnings = self.warnings;
        if axioms.len() > 20 {
            warnings.push(format!(
                "large axiom set ({} axioms); mutation generation may be slow",
                axioms.len()
            ));
        }

        assert_eq!(
            axioms.len(),
            axiom_origins.len(),
            "axiom_origins parallel-vector invariant violated"
        );

        Ok(TranslationResult {
            signature,
            axioms,
            axiom_origins,
            translated_theorems: self.translated_theorems,
            skipped_theorems: self.skipped_theorems,
            translated_predicates: self.translated_predicates,
            skipped_predicates: self.skipped_predicates,
            warnings,
            sort_filter,
        })
    }
}

// ============================================================================
// Public helpers — sort filtering + dedup
// ============================================================================

/// Drop sorts (and the functions/relations that depend on them) not reachable
/// from `axioms`.
///
/// Reachability is computed in two passes:
///   1. Collect every sort syntactically referenced in the axioms (quantifier
///      binders, relation arities of atoms, function domains/codomains of
///      terms).
///   2. Transitively close: for every function symbol whose codomain *or any
///      domain element* is in the reachable set, mark every other sort it
///      mentions as reachable too.  Repeat until the set is stable.
///
/// This prevents stdlib types Lean surfaces as type arguments (`Std_Format`,
/// `Bool`, `Prop`) from inflating the model space.
pub fn filter_signature(
    sig: &Signature,
    axioms: &[Formula],
) -> Result<Signature, SignatureError> {
    use std::collections::BTreeSet;

    let mut reachable: BTreeSet<SortSymbol> = BTreeSet::new();
    for axiom in axioms {
        collect_sorts_from_formula(axiom, &mut reachable);
    }

    // Transitive closure via the function signatures.
    loop {
        let prev_len = reachable.len();
        for f in &sig.functions {
            let touches = std::iter::once(&f.codomain).chain(f.domain.iter()).any(|s| {
                reachable.contains(s)
            });
            if touches {
                reachable.insert(f.codomain.clone());
                for d in &f.domain {
                    reachable.insert(d.clone());
                }
            }
        }
        if reachable.len() == prev_len {
            break;
        }
    }

    // If nothing was reachable, the axioms are vacuous in this signature.
    // Keep the original signature so the caller can detect the situation
    // (rather than silently building an empty signature).
    if reachable.is_empty() {
        return Ok(sig.clone());
    }

    let sorts: Vec<SortSymbol> = sig
        .sorts
        .iter()
        .filter(|s| reachable.contains(*s))
        .cloned()
        .collect();

    let functions: Vec<FunctionSymbol> = sig
        .functions
        .iter()
        .filter(|f| {
            reachable.contains(&f.codomain) && f.domain.iter().all(|d| reachable.contains(d))
        })
        .cloned()
        .collect();

    let relations: Vec<RelationSymbol> = sig
        .relations
        .iter()
        .filter(|r| r.arity.iter().all(|s| reachable.contains(s)))
        .cloned()
        .collect();

    Signature::new(sorts, functions, relations)
}

/// Remove syntactically duplicate axioms.  Equality is structural (since
/// `Formula` is `Eq`), which after `to_nnf` normalises propositional shape;
/// two formulas with the same NNF produce the same key.
pub fn deduplicate_axioms(axioms: Vec<Formula>) -> Vec<Formula> {
    use std::collections::BTreeSet;
    let mut seen: BTreeSet<Formula> = BTreeSet::new();
    axioms.into_iter().filter(|a| seen.insert(a.clone())).collect()
}

/// Like [`deduplicate_axioms`] but propagates a parallel provenance vector.
/// On a duplicate axiom, the first-seen origin is kept; later duplicates and
/// their origins are dropped together so the two vectors stay the same length.
pub fn deduplicate_axioms_with_origins(
    axioms: Vec<Formula>,
    origins: Vec<AxiomOrigin>,
) -> (Vec<Formula>, Vec<AxiomOrigin>) {
    assert_eq!(
        axioms.len(),
        origins.len(),
        "deduplicate_axioms_with_origins requires parallel vectors"
    );
    use std::collections::BTreeSet;
    let mut seen: BTreeSet<Formula> = BTreeSet::new();
    let mut out_axioms: Vec<Formula> = Vec::with_capacity(axioms.len());
    let mut out_origins: Vec<AxiomOrigin> = Vec::with_capacity(origins.len());
    for (a, o) in axioms.into_iter().zip(origins) {
        if seen.insert(a.clone()) {
            out_axioms.push(a);
            out_origins.push(o);
        }
    }
    (out_axioms, out_origins)
}

/// Walk a `Formula` and stuff every sort it references into `out`.
fn collect_sorts_from_formula(f: &Formula, out: &mut std::collections::BTreeSet<SortSymbol>) {
    match f {
        Formula::Bot | Formula::Top => {}
        Formula::Atom { relation, args } | Formula::NegAtom { relation, args } => {
            for s in &relation.arity {
                out.insert(s.clone());
            }
            for a in args {
                collect_sorts_from_term(a, out);
            }
        }
        Formula::Eq(a, b) | Formula::Neq(a, b) => {
            collect_sorts_from_term(a, out);
            collect_sorts_from_term(b, out);
        }
        Formula::And(l, r) | Formula::Or(l, r) => {
            collect_sorts_from_formula(l, out);
            collect_sorts_from_formula(r, out);
        }
        Formula::Forall { sort, body } | Formula::Exists { sort, body } => {
            out.insert(sort.clone());
            collect_sorts_from_formula(body, out);
        }
        Formula::Not(inner) => collect_sorts_from_formula(inner, out),
    }
}

fn collect_sorts_from_term(t: &Term, out: &mut std::collections::BTreeSet<SortSymbol>) {
    if let Term::App { function, args } = t {
        out.insert(function.codomain.clone());
        for s in &function.domain {
            out.insert(s.clone());
        }
        for a in args {
            collect_sorts_from_term(a, out);
        }
    }
}

// ============================================================================
// Helpers
// ============================================================================

#[derive(Debug, thiserror::Error)]
#[allow(dead_code)]
pub(crate) enum ExprError {
    #[error("unsupported node: {0}")]
    UnsupportedNode(String),
    #[error("unknown sort: {0}")]
    UnknownSort(String),
    #[error("unknown symbol: {0}")]
    UnknownSymbol(String),
    #[error("context mismatch: expected {expected}, got {got}")]
    ContextMismatch {
        expected: &'static str,
        got: String,
    },
    #[error("formula has free variables: {0}")]
    FreeVariables(String),
}

/// True for sort identifiers that should never become real `SortSymbol`s.
/// Phase A emits `_Unknown` / `_Param` / `_Sort` placeholders when binder
/// types couldn't be resolved; we don't want these in the final signature.
fn is_unknown_sort(name: &str) -> bool {
    matches!(name, "_Unknown" | "_Sort" | "_Param")
}

/// Phase G: true for sort names produced by type-class plumbing or stdlib
/// re-exports.  These do not correspond to mathematical sorts the user
/// cares about; the translator suppresses them and any function/relation
/// that references them.
///
/// Patterns covered:
///   * `inst<Class>...` — type-class instance dictionaries
///   * `Decidable...` — decidability machinery
///   * `Repr...` / `*Repr*` — Repr / Format pretty-printing
///   * `IO.*` / `Std.*` / `System.*` / `EStateM.*` — stdlib re-exports
///   * `Prop` / `Type` / `Sort` — universe sorts (not first-order)
///   * `Hashable` / `Inhabited` / `ToString` — type-class dictionaries
pub fn is_noise_sort_name(name: &str) -> bool {
    // Placeholder sentinel names from Phase A.
    if is_unknown_sort(name) {
        return true;
    }
    if name == "Prop" || name == "Type" || name == "Sort" {
        return true;
    }
    if name.starts_with("inst") && name.chars().nth(4).is_some_and(|c| c.is_ascii_uppercase()) {
        return true;
    }
    if name.starts_with("Decidable")
        || name.starts_with("IO.")
        || name.starts_with("Std.")
        || name.starts_with("System.")
        || name.starts_with("EStateM.")
    {
        return true;
    }
    // Substring matches.  These are aggressive — the Phase G spec
    // explicitly opts in to stdlib-level filtering at the cost of
    // potentially shadowing oddly-named user sorts.
    let substrings = [
        "Repr", "Hashable", "Inhabited", "ToString", "CoeSort", "CoeHTCoe",
    ];
    substrings.iter().any(|sub| name.contains(*sub))
}

/// True iff `name` follows Lean's convention for an auto-derived type-class
/// instance: `inst<CapitalizedClass>...` (e.g. `instReprTree`).  These are
/// pretty-print / decidability plumbing; their equations don't belong in the
/// spec's FOL axiom set and they drag in stdlib sorts (`Std_Format`, `Repr`,
/// etc.) that bloat the model space.
pub(crate) fn is_typeclass_instance(name: &str) -> bool {
    if !name.starts_with("inst") {
        return false;
    }
    name.chars()
        .nth(4)
        .map(|c| c.is_ascii_uppercase())
        .unwrap_or(false)
}

fn implies(l: Formula, r: Formula) -> Formula {
    Formula::Or(Box::new(Formula::Not(Box::new(l))), Box::new(r))
}

fn and(l: Formula, r: Formula) -> Formula {
    Formula::And(Box::new(l), Box::new(r))
}

fn or(l: Formula, r: Formula) -> Formula {
    Formula::Or(Box::new(l), Box::new(r))
}

/// Wrap `body` in `∀ p:S` quantifiers for each `param`, outermost first.
fn wrap_quantifiers(
    body: Formula,
    params: &[IRParam],
    sort_map: &BTreeMap<String, SortSymbol>,
) -> Formula {
    params.iter().rev().fold(body, |acc, p| {
        let sort = sort_map
            .get(&p.sort)
            .cloned()
            .unwrap_or_else(|| SortSymbol::new(&p.sort));
        Formula::Forall {
            sort,
            body: Box::new(acc),
        }
    })
}

/// Best-effort sort inference for a translated term.  Used to set the arity
/// of auto-declared relations / functions.
fn infer_term_sort(
    term: &Term,
    var_stack: &[(String, SortSymbol)],
    declared: &BTreeMap<String, FunctionSymbol>,
    auto: &BTreeMap<String, FunctionSymbol>,
) -> Option<SortSymbol> {
    match term {
        Term::Var(idx) => {
            // de Bruijn — top of stack is index 0.
            let n = var_stack.len();
            if *idx < n {
                Some(var_stack[n - 1 - *idx].1.clone())
            } else {
                None
            }
        }
        Term::App { function, .. } => {
            if let Some(f) = declared.get(&function.name) {
                Some(f.codomain.clone())
            } else if let Some(f) = auto.get(&function.name) {
                Some(f.codomain.clone())
            } else {
                Some(function.codomain.clone())
            }
        }
    }
}

// ============================================================================
// Phase G: equation sanitization
// ============================================================================

/// Phase G: strip known-irrelevant nodes from an equation's LHS/RHS so a
/// single type-class dictionary argument doesn't doom the whole equation.
///
/// Strategy: drop `Unsupported` nodes whose description matches type-class
/// noise; drop bare type-class-method applications; descend through
/// connectives and binders.
pub fn sanitize_equation(eq: &IREquation) -> IREquation {
    IREquation {
        vars: eq.vars.clone(),
        lhs: sanitize_expr(&eq.lhs),
        rhs: sanitize_expr(&eq.rhs),
    }
}

/// True iff an `Unsupported` description names the kind of plumbing
/// Phase G is built to ignore (type-class instance dictionaries,
/// out-params, auto-params, decidability arguments).
pub fn is_typeclass_noise_desc(description: &str) -> bool {
    description.contains("inst")
        || description.contains("Decidable")
        || description.contains("Repr")
        || description.contains("BEq")
        || description.contains("Ord")
        || description.contains("Hashable")
        || description.contains("Inhabited")
        || description.contains("ToString")
        || description.contains("outParam")
        || description.contains("autoParam")
}

/// True iff an `IRExpr` looks like a type-class dictionary argument that
/// should be dropped from an enclosing application's argument list
/// (rather than being recursed into and replaced with `True`).
fn is_typeclass_arg(e: &IRExpr) -> bool {
    match e {
        IRExpr::Unsupported { description } => is_typeclass_noise_desc(description),
        IRExpr::App { fn_name, .. } => is_typeclass_method_name(fn_name),
        _ => false,
    }
}

/// True iff `fn_name` names a type-class instance / dictionary method
/// whose application can be safely stripped.
pub fn is_typeclass_method_name(fn_name: &str) -> bool {
    if fn_name.starts_with("inst")
        && fn_name.chars().nth(4).is_some_and(|c| c.is_ascii_uppercase())
    {
        return true;
    }
    fn_name.ends_with(".mk")
        || matches!(
            fn_name,
            "Decidable.decide"
                | "Repr.reprPrec"
                | "Repr.repr"
                | "BEq.beq"
                | "Ord.compare"
                | "Hashable.hash"
                | "ToString.toString"
        )
}

/// Recursive sanitiser.  Replaces noise nodes with neutral content
/// (`True`) and strips type-class arguments from applications.
pub fn sanitize_expr(expr: &IRExpr) -> IRExpr {
    match expr {
        // Replace type-class-noise Unsupported nodes with True; this
        // works because they appear in propositional positions inside
        // equation lemmas (typically as a decidability argument that
        // the propositional content doesn't actually depend on).
        IRExpr::Unsupported { description } if is_typeclass_noise_desc(description) => {
            IRExpr::True
        }

        // A type-class method app reduces to its "real" argument if
        // possible, otherwise to True.  E.g. `instOrdNat.compare a b`
        // collapses to True so the equation's surrounding shape stays
        // intact.
        IRExpr::App { fn_name, args } if is_typeclass_method_name(fn_name) => {
            let real_args: Vec<IRExpr> = args
                .iter()
                .filter(|a| !is_typeclass_arg(a))
                .map(sanitize_expr)
                .collect();
            match real_args.len() {
                0 => IRExpr::True,
                1 => real_args.into_iter().next().expect("len == 1"),
                _ => IRExpr::App {
                    fn_name: fn_name.clone(),
                    args: real_args,
                },
            }
        }

        // Generic app: drop type-class dictionary args (which would
        // become a confusing `True` if we ran them through
        // `sanitize_expr` here), then recurse into the survivors.
        IRExpr::App { fn_name, args } => IRExpr::App {
            fn_name: fn_name.clone(),
            args: args
                .iter()
                .filter(|a| !is_typeclass_arg(a))
                .map(sanitize_expr)
                .collect(),
        },

        IRExpr::And { left, right } => IRExpr::And {
            left: Box::new(sanitize_expr(left)),
            right: Box::new(sanitize_expr(right)),
        },
        IRExpr::Or { left, right } => IRExpr::Or {
            left: Box::new(sanitize_expr(left)),
            right: Box::new(sanitize_expr(right)),
        },
        IRExpr::Not { body } => IRExpr::Not {
            body: Box::new(sanitize_expr(body)),
        },
        IRExpr::Implies { left, right } => IRExpr::Implies {
            left: Box::new(sanitize_expr(left)),
            right: Box::new(sanitize_expr(right)),
        },
        IRExpr::Iff { left, right } => IRExpr::Iff {
            left: Box::new(sanitize_expr(left)),
            right: Box::new(sanitize_expr(right)),
        },
        IRExpr::Forall { var, sort, body } => IRExpr::Forall {
            var: var.clone(),
            sort: sort.clone(),
            body: Box::new(sanitize_expr(body)),
        },
        IRExpr::Exists { var, sort, body } => IRExpr::Exists {
            var: var.clone(),
            sort: sort.clone(),
            body: Box::new(sanitize_expr(body)),
        },
        IRExpr::Eq { left, right } => IRExpr::Eq {
            left: Box::new(sanitize_expr(left)),
            right: Box::new(sanitize_expr(right)),
        },
        IRExpr::Neq { left, right } => IRExpr::Neq {
            left: Box::new(sanitize_expr(left)),
            right: Box::new(sanitize_expr(right)),
        },
        IRExpr::Leq { left, right } => IRExpr::Leq {
            left: Box::new(sanitize_expr(left)),
            right: Box::new(sanitize_expr(right)),
        },
        IRExpr::Lt { left, right } => IRExpr::Lt {
            left: Box::new(sanitize_expr(left)),
            right: Box::new(sanitize_expr(right)),
        },
        IRExpr::Mem { element, collection } => IRExpr::Mem {
            element: Box::new(sanitize_expr(element)),
            collection: Box::new(sanitize_expr(collection)),
        },

        // Leaves: copy verbatim.
        IRExpr::Var { .. }
        | IRExpr::NatLit { .. }
        | IRExpr::True
        | IRExpr::False
        | IRExpr::Unsupported { .. } => expr.clone(),
    }
}

/// Recursively check whether an IRExpr (or any descendant) is `Unsupported`.
fn contains_unsupported(e: &IRExpr) -> bool {
    match e {
        IRExpr::Unsupported { .. } => true,
        IRExpr::App { args, .. } => args.iter().any(contains_unsupported),
        IRExpr::Forall { body, .. }
        | IRExpr::Exists { body, .. }
        | IRExpr::Not { body } => contains_unsupported(body),
        IRExpr::And { left, right }
        | IRExpr::Or { left, right }
        | IRExpr::Implies { left, right }
        | IRExpr::Iff { left, right }
        | IRExpr::Eq { left, right }
        | IRExpr::Neq { left, right }
        | IRExpr::Leq { left, right }
        | IRExpr::Lt { left, right } => {
            contains_unsupported(left) || contains_unsupported(right)
        }
        IRExpr::Mem { element, collection } => {
            contains_unsupported(element) || contains_unsupported(collection)
        }
        _ => false,
    }
}

/// Short tag for debug messages.
fn node_kind(e: &IRExpr) -> &'static str {
    match e {
        IRExpr::Var { .. } => "var",
        IRExpr::App { .. } => "app",
        IRExpr::Forall { .. } => "forall",
        IRExpr::Exists { .. } => "exists",
        IRExpr::And { .. } => "and",
        IRExpr::Or { .. } => "or",
        IRExpr::Not { .. } => "not",
        IRExpr::Implies { .. } => "implies",
        IRExpr::Iff { .. } => "iff",
        IRExpr::Eq { .. } => "eq",
        IRExpr::Neq { .. } => "neq",
        IRExpr::Leq { .. } => "leq",
        IRExpr::Lt { .. } => "lt",
        IRExpr::Mem { .. } => "mem",
        IRExpr::NatLit { .. } => "nat_lit",
        IRExpr::True => "true",
        IRExpr::False => "false",
        IRExpr::Unsupported { .. } => "unsupported",
    }
}
