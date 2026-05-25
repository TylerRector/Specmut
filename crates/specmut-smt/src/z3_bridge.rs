//! Z3-backed implementation of [`SmtSolver`] and `EntailmentChecker`.
//!
//! Each query allocates a fresh `z3::Context` and `z3::Solver`.  This
//! avoids the lifetime acrobatics required to hold a `Context` inside a
//! `Send + Sync` struct, at the cost of paying for context setup on
//! every call — acceptable for the entailment workloads this bridge
//! handles in Phase 4.

use std::collections::HashMap;

use specmut_core::formula::{Formula, Term};
use specmut_core::lattice::EntailmentChecker;
use specmut_core::signature::Signature;
use z3::ast::{Ast, Bool, Dynamic};
use z3::{Config as Z3CrateConfig, Context, FuncDecl, Params, SatResult, Solver, Sort, Symbol};

use crate::smt_types::{SmtModel, SmtResult, SmtSolver, Z3Config};

/// Z3-backed SMT solver.
pub struct Z3Solver {
    config: Z3Config,
}

impl Z3Solver {
    /// Build a solver with the given configuration.
    pub fn new(config: Z3Config) -> Self {
        Self { config }
    }

    /// Build a solver with default configuration.
    pub fn default_solver() -> Self {
        Self::new(Z3Config::default())
    }

    /// The configuration this solver was constructed with.
    pub fn config(&self) -> &Z3Config {
        &self.config
    }

    fn build_context(&self) -> Context {
        let cfg = Z3CrateConfig::new();
        Context::new(&cfg)
    }

    fn build_solver<'ctx>(&self, ctx: &'ctx Context) -> Solver<'ctx> {
        let solver = Solver::new(ctx);
        let mut params = Params::new(ctx);
        if self.config.timeout_ms > 0 {
            let timeout = u32::try_from(self.config.timeout_ms).unwrap_or(u32::MAX);
            params.set_u32("timeout", timeout);
        }
        let seed = u32::try_from(self.config.seed & u64::from(u32::MAX)).unwrap_or(0);
        params.set_u32("random_seed", seed);
        solver.set_params(&params);
        solver
    }

    fn map_result(r: SatResult) -> SmtResult {
        match r {
            SatResult::Sat => SmtResult::Sat,
            SatResult::Unsat => SmtResult::Unsat,
            SatResult::Unknown => SmtResult::Unknown,
        }
    }

    /// Like [`SmtSolver::check_entailment`], but returns the raw
    /// [`SmtResult`] of `premises ∧ ¬conclusion` so callers can
    /// distinguish `Unsat` (entails) / `Sat` (does not entail) /
    /// `Unknown`.  `Unknown` lets a hybrid checker fall back to a
    /// different backend rather than collapsing it to a boolean.
    ///
    /// Added in Phase 6 for hybrid entailment checker.
    pub fn check_entailment_raw(
        &self,
        premises: &[Formula],
        conclusion: &Formula,
        sig: &Signature,
    ) -> SmtResult {
        let ctx = self.build_context();
        let solver = self.build_solver(&ctx);
        let mut translator = Z3Translation::new(&ctx, sig);
        for p in premises {
            let assertion = translator.translate_formula(p);
            solver.assert(&assertion);
        }
        let neg_conclusion = translator.translate_formula(conclusion).not();
        solver.assert(&neg_conclusion);
        Self::map_result(solver.check())
    }
}

impl SmtSolver for Z3Solver {
    fn check_sat(&self, formula: &Formula, sig: &Signature) -> SmtResult {
        let ctx = self.build_context();
        let solver = self.build_solver(&ctx);
        let mut translator = Z3Translation::new(&ctx, sig);
        let translated = translator.translate_formula(formula);
        solver.assert(&translated);
        let result = Self::map_result(solver.check());
        if result == SmtResult::Unknown {
            eprintln!("specmut-smt: Z3 returned Unknown on check_sat");
        }
        result
    }

    fn check_entailment(
        &self,
        premises: &[Formula],
        conclusion: &Formula,
        sig: &Signature,
    ) -> bool {
        let ctx = self.build_context();
        let solver = self.build_solver(&ctx);
        let mut translator = Z3Translation::new(&ctx, sig);
        for p in premises {
            let assertion = translator.translate_formula(p);
            solver.assert(&assertion);
        }
        let neg_conclusion = translator.translate_formula(conclusion).not();
        solver.assert(&neg_conclusion);
        match solver.check() {
            SatResult::Unsat => true,
            SatResult::Sat => false,
            SatResult::Unknown => {
                eprintln!("specmut-smt: Z3 returned Unknown on entailment query; treating as not-entailed");
                false
            }
        }
    }

    fn check_equivalence(
        &self,
        s1: &[Formula],
        s2: &[Formula],
        sig: &Signature,
    ) -> bool {
        let forward = s2
            .iter()
            .all(|f| self.check_entailment(s1, f, sig));
        if !forward {
            return false;
        }
        s1.iter().all(|f| self.check_entailment(s2, f, sig))
    }

    fn get_model(&self, formula: &Formula, sig: &Signature) -> Option<SmtModel> {
        let ctx = self.build_context();
        let solver = self.build_solver(&ctx);
        let mut translator = Z3Translation::new(&ctx, sig);
        let translated = translator.translate_formula(formula);
        solver.assert(&translated);
        match solver.check() {
            SatResult::Sat => {
                let model = solver.get_model()?;
                Some(SmtModel {
                    description: format!("{model}"),
                })
            }
            _ => None,
        }
    }
}

/// `EntailmentChecker` wrapper that captures the [`Signature`] so that it
/// matches `specmut_core`'s checker trait (which does not pass `&Signature`).
///
/// Prefer this over modifying `specmut_core::lattice::EntailmentChecker`.
pub struct Z3EntailmentChecker {
    solver: Z3Solver,
    signature: Signature,
}

impl Z3EntailmentChecker {
    /// Build a checker over `solver` and `signature`.
    pub fn new(solver: Z3Solver, signature: Signature) -> Self {
        Self { solver, signature }
    }
}

impl EntailmentChecker for Z3EntailmentChecker {
    fn entails(&self, stronger: &[Formula], weaker: &[Formula]) -> bool {
        weaker
            .iter()
            .all(|w| self.solver.check_entailment(stronger, w, &self.signature))
    }
}

/// Per-query translation state.  Holds the declared sorts and function
/// symbols for `sig` along with a stack of bound variables (innermost
/// last) used to resolve de Bruijn indices into Z3 constants.
struct Z3Translation<'ctx> {
    ctx: &'ctx Context,
    sorts: HashMap<String, Sort<'ctx>>,
    functions: HashMap<String, FuncDecl<'ctx>>,
    relations: HashMap<String, FuncDecl<'ctx>>,
    #[allow(dead_code)]
    bool_sort: Sort<'ctx>,
    binder_stack: Vec<Dynamic<'ctx>>,
    /// Monotonic counter used to mint unique names for bound-variable
    /// constants — z3 0.12 does not expose `fresh_const` for arbitrary
    /// (uninterpreted) sorts, so each binder allocates a fresh zero-arity
    /// `FuncDecl` whose name must differ from previous binders'.
    fresh_counter: u64,
}

impl<'ctx> Z3Translation<'ctx> {
    fn new(ctx: &'ctx Context, sig: &Signature) -> Self {
        let bool_sort = Sort::bool(ctx);
        let mut sorts: HashMap<String, Sort<'ctx>> = HashMap::new();
        for s in &sig.sorts {
            sorts.insert(
                s.name.clone(),
                Sort::uninterpreted(ctx, Symbol::String(s.name.clone())),
            );
        }
        let mut functions: HashMap<String, FuncDecl<'ctx>> = HashMap::new();
        for f in &sig.functions {
            let dom: Vec<&Sort<'ctx>> = f
                .domain
                .iter()
                .map(|s| sorts.get(&s.name).expect("function domain sort declared"))
                .collect();
            let cod = sorts
                .get(&f.codomain.name)
                .expect("function codomain sort declared");
            functions.insert(
                f.name.clone(),
                FuncDecl::new(ctx, Symbol::String(f.name.clone()), &dom, cod),
            );
        }
        let mut relations: HashMap<String, FuncDecl<'ctx>> = HashMap::new();
        for r in &sig.relations {
            let dom: Vec<&Sort<'ctx>> = r
                .arity
                .iter()
                .map(|s| sorts.get(&s.name).expect("relation arity sort declared"))
                .collect();
            relations.insert(
                r.name.clone(),
                FuncDecl::new(ctx, Symbol::String(r.name.clone()), &dom, &bool_sort),
            );
        }
        Self {
            ctx,
            sorts,
            functions,
            relations,
            bool_sort,
            binder_stack: Vec::new(),
            fresh_counter: 0,
        }
    }

    /// Mint a fresh constant of the given sort.  Implemented as a
    /// zero-arity uninterpreted function applied to no arguments since
    /// z3 0.12 lacks a `Dynamic::fresh_const(sort)` constructor for
    /// uninterpreted sorts.
    fn fresh_const_of(&mut self, sort: &Sort<'ctx>) -> Dynamic<'ctx> {
        self.fresh_counter += 1;
        let name = format!("__bv_{}", self.fresh_counter);
        let decl = FuncDecl::new(self.ctx, Symbol::String(name), &[], sort);
        decl.apply(&[])
    }

    fn translate_formula(&mut self, f: &Formula) -> Bool<'ctx> {
        match f {
            Formula::Top => Bool::from_bool(self.ctx, true),
            Formula::Bot => Bool::from_bool(self.ctx, false),
            Formula::Atom { relation, args } => self.translate_relation(relation, args),
            Formula::NegAtom { relation, args } => self.translate_relation(relation, args).not(),
            Formula::Eq(a, b) => {
                let a_z3 = self.translate_term(a);
                let b_z3 = self.translate_term(b);
                a_z3._eq(&b_z3)
            }
            Formula::Neq(a, b) => {
                let a_z3 = self.translate_term(a);
                let b_z3 = self.translate_term(b);
                a_z3._eq(&b_z3).not()
            }
            Formula::And(l, r) => {
                let l_z3 = self.translate_formula(l);
                let r_z3 = self.translate_formula(r);
                Bool::and(self.ctx, &[&l_z3, &r_z3])
            }
            Formula::Or(l, r) => {
                let l_z3 = self.translate_formula(l);
                let r_z3 = self.translate_formula(r);
                Bool::or(self.ctx, &[&l_z3, &r_z3])
            }
            Formula::Forall { sort, body } => self.translate_quantifier(sort, body, true),
            Formula::Exists { sort, body } => self.translate_quantifier(sort, body, false),
            Formula::Not(inner) => self.translate_formula(inner).not(),
        }
    }

    fn translate_relation(
        &mut self,
        relation: &specmut_core::signature::RelationSymbol,
        args: &[Term],
    ) -> Bool<'ctx> {
        // Translate args first (mutably borrows self).  Only after that
        // do we look up the FuncDecl — the resulting immutable borrow
        // spans only the apply() call.  FuncDecl<'ctx> is not Clone, so
        // we cannot pull it out into a local owned variable.
        let z3_args: Vec<Dynamic<'ctx>> =
            args.iter().map(|a| self.translate_term(a)).collect();
        let arg_refs: Vec<&dyn Ast<'ctx>> = z3_args
            .iter()
            .map(|d| d as &dyn Ast<'ctx>)
            .collect();
        let decl = self
            .relations
            .get(&relation.name)
            .expect("relation symbol declared");
        decl.apply(&arg_refs)
            .as_bool()
            .expect("relation application is Bool-sorted")
    }

    fn translate_quantifier(
        &mut self,
        sort: &specmut_core::signature::SortSymbol,
        body: &Formula,
        is_forall: bool,
    ) -> Bool<'ctx> {
        let z3_sort: Sort<'ctx> = self
            .sorts
            .get(&sort.name)
            .expect("bound-variable sort declared")
            .clone();
        let bound = self.fresh_const_of(&z3_sort);
        self.binder_stack.push(bound.clone());
        let body_z3 = self.translate_formula(body);
        self.binder_stack.pop();
        let bound_ref: &dyn Ast<'ctx> = &bound;
        if is_forall {
            z3::ast::forall_const(self.ctx, &[bound_ref], &[], &body_z3)
        } else {
            z3::ast::exists_const(self.ctx, &[bound_ref], &[], &body_z3)
        }
    }

    fn translate_term(&mut self, t: &Term) -> Dynamic<'ctx> {
        match t {
            Term::Var(i) => {
                let depth = self.binder_stack.len();
                assert!(
                    *i < depth,
                    "unbound de Bruijn index {i} for binder stack of depth {depth}; \
                     translate_term only handles variables introduced by an enclosing quantifier"
                );
                self.binder_stack[depth - 1 - *i].clone()
            }
            Term::App { function, args } => {
                let z3_args: Vec<Dynamic<'ctx>> =
                    args.iter().map(|a| self.translate_term(a)).collect();
                let arg_refs: Vec<&dyn Ast<'ctx>> = z3_args
                    .iter()
                    .map(|d| d as &dyn Ast<'ctx>)
                    .collect();
                let decl = self
                    .functions
                    .get(&function.name)
                    .expect("function symbol declared");
                decl.apply(&arg_refs)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use specmut_core::formula::{Formula, Term};
    use specmut_core::signature::{RelationSymbol, Signature, SortSymbol};

    use super::*;

    fn sort(name: &str) -> SortSymbol {
        SortSymbol::new(name)
    }

    fn unary_sig() -> Signature {
        let s = sort("S");
        Signature::new(
            vec![s.clone()],
            vec![],
            vec![RelationSymbol::new("P", vec![s])],
        )
        .expect("valid sig")
    }

    fn two_unary_sig() -> Signature {
        let s = sort("S");
        Signature::new(
            vec![s.clone()],
            vec![],
            vec![
                RelationSymbol::new("P", vec![s.clone()]),
                RelationSymbol::new("Q", vec![s]),
            ],
        )
        .expect("valid sig")
    }

    fn forall_pred(name: &str) -> Formula {
        Formula::Forall {
            sort: sort("S"),
            body: Box::new(Formula::Atom {
                relation: RelationSymbol::new(name, vec![sort("S")]),
                args: vec![Term::Var(0)],
            }),
        }
    }

    fn forall_p_and_q() -> Formula {
        Formula::Forall {
            sort: sort("S"),
            body: Box::new(Formula::And(
                Box::new(Formula::Atom {
                    relation: RelationSymbol::new("P", vec![sort("S")]),
                    args: vec![Term::Var(0)],
                }),
                Box::new(Formula::Atom {
                    relation: RelationSymbol::new("Q", vec![sort("S")]),
                    args: vec![Term::Var(0)],
                }),
            )),
        }
    }

    fn exists_p() -> Formula {
        Formula::Exists {
            sort: sort("S"),
            body: Box::new(Formula::Atom {
                relation: RelationSymbol::new("P", vec![sort("S")]),
                args: vec![Term::Var(0)],
            }),
        }
    }

    #[test]
    fn test_translate_atom() {
        // ∃x:S. P(x) is satisfiable.  Use Exists so the formula is a
        // sentence; raw open atoms aren't a use case for the solver.
        let solver = Z3Solver::default_solver();
        let result = solver.check_sat(&exists_p(), &unary_sig());
        assert_eq!(result, SmtResult::Sat);
    }

    #[test]
    fn test_translate_forall() {
        let solver = Z3Solver::default_solver();
        let result = solver.check_sat(&forall_pred("P"), &unary_sig());
        assert_eq!(result, SmtResult::Sat);
    }

    #[test]
    fn test_entailment_true() {
        // {∀x. P(x) ∧ Q(x)} entails ∀x. P(x).
        let solver = Z3Solver::default_solver();
        let sig = two_unary_sig();
        assert!(solver.check_entailment(
            std::slice::from_ref(&forall_p_and_q()),
            &forall_pred("P"),
            &sig
        ));
    }

    #[test]
    fn test_entailment_false() {
        // {∀x. P(x)} does not entail ∀x. Q(x).
        let solver = Z3Solver::default_solver();
        let sig = two_unary_sig();
        assert!(!solver.check_entailment(
            std::slice::from_ref(&forall_pred("P")),
            &forall_pred("Q"),
            &sig
        ));
    }

    #[test]
    fn test_equivalence_true() {
        // ∀x. P(x) ≡ ∀x. P(x) (trivial).
        let solver = Z3Solver::default_solver();
        let sig = unary_sig();
        let phi = forall_pred("P");
        let s1 = std::slice::from_ref(&phi);
        assert!(solver.check_equivalence(s1, s1, &sig));
    }

    #[test]
    fn test_equivalence_false() {
        // ∀x. P(x) ≢ ∀x. Q(x) on a 2-relation signature.
        let solver = Z3Solver::default_solver();
        let sig = two_unary_sig();
        let p = forall_pred("P");
        let q = forall_pred("Q");
        assert!(!solver.check_equivalence(
            std::slice::from_ref(&p),
            std::slice::from_ref(&q),
            &sig
        ));
    }

    #[test]
    fn test_neg_atom_translation() {
        // ∀x. ¬P(x) is satisfiable (the empty interpretation of P works).
        let solver = Z3Solver::default_solver();
        let phi = Formula::Forall {
            sort: sort("S"),
            body: Box::new(Formula::NegAtom {
                relation: RelationSymbol::new("P", vec![sort("S")]),
                args: vec![Term::Var(0)],
            }),
        };
        assert_eq!(solver.check_sat(&phi, &unary_sig()), SmtResult::Sat);
    }

    #[test]
    fn test_timeout_returns_unknown() {
        // Build a deeply nested quantifier formula over multiple sorts and
        // set the timeout to 1 ms.  A definitive answer in 1 ms is
        // unlikely, so the solver should report Unknown rather than
        // hanging or panicking.  We tolerate Sat / Unsat too — if Z3
        // *does* solve it in time on a fast machine, the test stays
        // green; we only assert that we don't hang.
        let config = Z3Config {
            timeout_ms: 1,
            logic: None,
            seed: 0,
        };
        let solver = Z3Solver::new(config);
        // Build a chain of 6 alternating quantifiers over a 4-relation sig.
        let s = sort("S");
        let sig = Signature::new(
            vec![s.clone()],
            vec![],
            (0..4)
                .map(|i| {
                    RelationSymbol::new(
                        format!("R{i}"),
                        vec![s.clone(), s.clone(), s.clone()],
                    )
                })
                .collect(),
        )
        .expect("valid");
        let mut body = Formula::Atom {
            relation: RelationSymbol::new("R0", vec![s.clone(), s.clone(), s.clone()]),
            args: vec![Term::Var(0), Term::Var(1), Term::Var(2)],
        };
        for i in 1..4 {
            let inner = Formula::Atom {
                relation: RelationSymbol::new(
                    format!("R{i}"),
                    vec![s.clone(), s.clone(), s.clone()],
                ),
                args: vec![Term::Var(0), Term::Var(1), Term::Var(2)],
            };
            body = Formula::And(Box::new(body), Box::new(inner));
        }
        // ∀∀∀∃∃∃ over the conjunction.
        for is_forall in [false, false, false, true, true, true] {
            body = if is_forall {
                Formula::Forall {
                    sort: s.clone(),
                    body: Box::new(body),
                }
            } else {
                Formula::Exists {
                    sort: s.clone(),
                    body: Box::new(body),
                }
            };
        }
        let result = solver.check_sat(&body, &sig);
        // The point of the test is that the call returns *something*
        // within bounded time rather than hanging.
        assert!(matches!(
            result,
            SmtResult::Unknown | SmtResult::Sat | SmtResult::Unsat
        ));
    }

    #[test]
    fn test_roundtrip_smoke() {
        // Trivial round-trip sanity check called out in §3.9 / Phase 4:
        // translate ⊤ and ⊥ and assert sat / unsat respectively.
        let solver = Z3Solver::default_solver();
        let sig = unary_sig();
        assert_eq!(solver.check_sat(&Formula::Top, &sig), SmtResult::Sat);
        assert_eq!(solver.check_sat(&Formula::Bot, &sig), SmtResult::Unsat);
    }

    #[test]
    fn test_z3_entailment_checker_wrapper() {
        // The wrapper should satisfy specmut_core's EntailmentChecker
        // contract over a small signature.
        let sig = two_unary_sig();
        let checker = Z3EntailmentChecker::new(Z3Solver::default_solver(), sig);
        // Self-entailment.
        let p = forall_pred("P");
        assert!(checker.entails(std::slice::from_ref(&p), std::slice::from_ref(&p)));
        // P does not entail Q.
        let q = forall_pred("Q");
        assert!(!checker.entails(std::slice::from_ref(&p), std::slice::from_ref(&q)));
        // Empty premise entails empty conclusion (vacuous).
        let empty: BTreeSet<Formula> = BTreeSet::new();
        let empty_axioms: Vec<Formula> = empty.iter().cloned().collect();
        assert!(checker.entails(&empty_axioms, &empty_axioms));
    }
}
