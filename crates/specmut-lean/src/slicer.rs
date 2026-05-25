//! Theorem-scoped semantic slicing (Phase E).
//!
//! Given a translated Lean IR's global signature and axiom set, split the
//! work per-theorem so each theorem can be analyzed against a minimal
//! signature containing only the symbols it actually references.  The
//! union signature can be too large to enumerate at small bounds on real
//! Lean files; per-theorem signatures are typically much smaller because
//! each theorem touches only a fraction of the imported symbols.
//!
//! Algorithm summary:
//! 1. For each translated theorem, seed the slice with its axiom(s).
//! 2. Worklist-close over relation names: pull in every predicate equation
//!    (or body) axiom whose origin defines a referenced relation, then
//!    explore the relations *those* axioms reference.
//! 3. Reduce the global signature to the symbols reachable from the slice
//!    by delegating to [`filter_signature`] — the same closure used for the
//!    global sort-filtering pass.
//!
//! When a translation produced zero theorems (predicates-only file),
//! `slice_by_theorem` returns an empty vector; the caller should fall back
//! to a single global analysis run.

use std::collections::{BTreeSet, VecDeque};

use specmut_core::formula::{Formula, Term};
use specmut_core::signature::{FunctionSymbol, RelationSymbol, Signature, SortSymbol};

use crate::translator::{AxiomOrigin, TranslationResult};

/// A theorem plus the minimal supporting axiom set and reduced signature
/// needed to analyze it in isolation.
#[derive(Debug, Clone)]
pub struct TheoremSlice {
    /// Name of the theorem being analyzed.
    pub theorem_name: String,
    /// The theorem's translated axiom (NNF sentence).
    pub theorem_axiom: Formula,
    /// Predicate equations + bodies pulled in by the transitive closure.
    pub supporting_axioms: Vec<Formula>,
    /// Signature containing only the symbols reachable from this slice.
    pub signature: Signature,
    /// All axioms for this slice in original-index order
    /// (predicate axioms first, then the theorem axiom — same ordering as
    /// the translator emits).
    pub all_axioms: Vec<Formula>,
    /// Sort names in the reduced signature, for reporting.
    pub included_sorts: Vec<String>,
    /// Relation names in the reduced signature, for reporting.
    pub included_relations: Vec<String>,
    /// Function names in the reduced signature, for reporting.
    pub included_functions: Vec<String>,
    /// Sort names present in the global signature but dropped from this slice.
    pub excluded_sorts: Vec<String>,
}

/// Symbol bag returned by [`collect_symbols`] — exposed for testing the
/// symbol-traversal step independently of slicing.
#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct SymbolSet {
    /// Sort names referenced (via quantifier binders or symbol arities).
    pub sorts: BTreeSet<String>,
    /// Relation symbol names referenced.
    pub relation_names: BTreeSet<String>,
    /// Function symbol names referenced (constants included).
    pub function_names: BTreeSet<String>,
}

/// Slice a translation into per-theorem analysis units.
///
/// Returns one [`TheoremSlice`] per name in `translation.translated_theorems`.
/// When that list is empty, returns an empty vector and the caller should
/// fall back to global analysis.
pub fn slice_by_theorem(translation: &TranslationResult) -> Vec<TheoremSlice> {
    assert_eq!(
        translation.axioms.len(),
        translation.axiom_origins.len(),
        "slice_by_theorem: axiom_origins length mismatch"
    );

    let mut slices = Vec::with_capacity(translation.translated_theorems.len());
    for theorem_name in &translation.translated_theorems {
        if let Some(slice) = build_slice(
            theorem_name,
            &translation.signature,
            &translation.axioms,
            &translation.axiom_origins,
        ) {
            slices.push(slice);
        }
    }
    slices
}

/// Collect every sort / relation / function name referenced by the given
/// formulas.
pub fn collect_symbols(formulas: &[Formula]) -> SymbolSet {
    let mut s = SymbolSet::default();
    for f in formulas {
        collect_formula_symbols(f, &mut s);
    }
    s
}

fn build_slice(
    theorem_name: &str,
    global_sig: &Signature,
    all_axioms: &[Formula],
    origins: &[AxiomOrigin],
) -> Option<TheoremSlice> {
    let seed_indices: Vec<usize> = origins
        .iter()
        .enumerate()
        .filter_map(|(i, o)| match o {
            AxiomOrigin::TheoremStatement { theorem_name: tn } if tn == theorem_name => Some(i),
            _ => None,
        })
        .collect();
    // No axiom carries this theorem's origin — likely the theorem appeared
    // in `translated_theorems` but its axiom was dedup-collapsed.  Skip.
    if seed_indices.is_empty() {
        return None;
    }

    let mut included_indices: BTreeSet<usize> = seed_indices.iter().copied().collect();
    let mut visited_rels: BTreeSet<String> = BTreeSet::new();
    let mut worklist: VecDeque<String> = VecDeque::new();
    for &i in &seed_indices {
        let mut s = SymbolSet::default();
        collect_formula_symbols(&all_axioms[i], &mut s);
        for r in s.relation_names {
            worklist.push_back(r);
        }
    }

    while let Some(rel) = worklist.pop_front() {
        if !visited_rels.insert(rel.clone()) {
            continue;
        }
        for (i, o) in origins.iter().enumerate() {
            let defines_rel = match o {
                AxiomOrigin::PredicateEquation { predicate_name, .. } => predicate_name == &rel,
                AxiomOrigin::PredicateBody { predicate_name } => predicate_name == &rel,
                AxiomOrigin::TheoremStatement { .. } => false,
            };
            if defines_rel && included_indices.insert(i) {
                let mut s = SymbolSet::default();
                collect_formula_symbols(&all_axioms[i], &mut s);
                for new_rel in s.relation_names {
                    if !visited_rels.contains(&new_rel) {
                        worklist.push_back(new_rel);
                    }
                }
            }
        }
    }

    // BTreeSet preserves index order, so the resulting axiom vector is
    // already in original translator-emission order (predicate axioms before
    // the theorem axiom).
    let slice_axioms: Vec<Formula> = included_indices
        .iter()
        .map(|&i| all_axioms[i].clone())
        .collect();

    // Collect every symbol the slice's axioms actually reference, then
    // build a reduced signature keeping only matching relations / functions
    // (and the sorts they transitively need).  This is stricter than the
    // global `filter_signature` pass — that one only prunes by sort
    // reachability, which leaves untouched relations alone when their
    // arity sorts survive — and it's what shrinks the model space enough
    // to fit under `MODEL_SPACE_LIMIT` for real Lean files.
    let slice_symbols = collect_symbols(&slice_axioms);
    let reduced_sig = reduce_signature(global_sig, &slice_symbols).ok()?;

    let seed_set: BTreeSet<usize> = seed_indices.iter().copied().collect();
    let theorem_axiom = all_axioms[seed_indices[0]].clone();
    let supporting_axioms: Vec<Formula> = included_indices
        .iter()
        .filter(|i| !seed_set.contains(i))
        .map(|&i| all_axioms[i].clone())
        .collect();

    let included_sorts: Vec<String> = reduced_sig.sorts.iter().map(|s| s.name.clone()).collect();
    let included_relations: Vec<String> =
        reduced_sig.relations.iter().map(|r| r.name.clone()).collect();
    let included_functions: Vec<String> =
        reduced_sig.functions.iter().map(|f| f.name.clone()).collect();
    let mut excluded_sorts: Vec<String> = global_sig
        .sorts
        .iter()
        .filter(|s| !reduced_sig.sorts.contains(*s))
        .map(|s| s.name.clone())
        .collect();
    excluded_sorts.sort();

    Some(TheoremSlice {
        theorem_name: theorem_name.to_string(),
        theorem_axiom,
        supporting_axioms,
        signature: reduced_sig,
        all_axioms: slice_axioms,
        included_sorts,
        included_relations,
        included_functions,
        excluded_sorts,
    })
}

/// Build a signature containing only relations and functions named in
/// `syms`, plus the sorts they reach through their domain/codomain/arity.
///
/// Stricter than `translator::filter_signature`: that one keeps every
/// relation whose arity-sorts survive, which is too lenient for per-slice
/// analysis because relations the slice never mentions still bloat the
/// model space.  Here we filter by name match first, then add only the
/// sorts the kept symbols need.
fn reduce_signature(
    global_sig: &Signature,
    syms: &SymbolSet,
) -> Result<Signature, specmut_core::signature::SignatureError> {
    let kept_relations: Vec<RelationSymbol> = global_sig
        .relations
        .iter()
        .filter(|r| syms.relation_names.contains(&r.name))
        .cloned()
        .collect();
    let kept_functions: Vec<FunctionSymbol> = global_sig
        .functions
        .iter()
        .filter(|f| syms.function_names.contains(&f.name))
        .cloned()
        .collect();

    let mut needed_sort_names: BTreeSet<String> = syms.sorts.clone();
    for r in &kept_relations {
        for s in &r.arity {
            needed_sort_names.insert(s.name.clone());
        }
    }
    for f in &kept_functions {
        for s in &f.domain {
            needed_sort_names.insert(s.name.clone());
        }
        needed_sort_names.insert(f.codomain.name.clone());
    }

    let kept_sorts: Vec<SortSymbol> = global_sig
        .sorts
        .iter()
        .filter(|s| needed_sort_names.contains(&s.name))
        .cloned()
        .collect();

    Signature::new(kept_sorts, kept_functions, kept_relations)
}

fn collect_formula_symbols(f: &Formula, out: &mut SymbolSet) {
    match f {
        Formula::Bot | Formula::Top => {}
        Formula::Atom { relation, args } | Formula::NegAtom { relation, args } => {
            out.relation_names.insert(relation.name.clone());
            for s in &relation.arity {
                out.sorts.insert(s.name.clone());
            }
            for a in args {
                collect_term_symbols(a, out);
            }
        }
        Formula::Eq(a, b) | Formula::Neq(a, b) => {
            collect_term_symbols(a, out);
            collect_term_symbols(b, out);
        }
        Formula::And(l, r) | Formula::Or(l, r) => {
            collect_formula_symbols(l, out);
            collect_formula_symbols(r, out);
        }
        Formula::Forall { sort, body } | Formula::Exists { sort, body } => {
            out.sorts.insert(sort.name.clone());
            collect_formula_symbols(body, out);
        }
        // Post-NNF formulas don't contain Not, but handle defensively so the
        // helper is safe to call on pre-NNF inputs in tests.
        Formula::Not(inner) => collect_formula_symbols(inner, out),
    }
}

fn collect_term_symbols(t: &Term, out: &mut SymbolSet) {
    match t {
        Term::Var(_) => {}
        Term::App { function, args } => {
            out.function_names.insert(function.name.clone());
            for s in &function.domain {
                out.sorts.insert(s.name.clone());
            }
            out.sorts.insert(function.codomain.name.clone());
            for a in args {
                collect_term_symbols(a, out);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use specmut_core::signature::{FunctionSymbol, RelationSymbol, SortSymbol};

    fn s(name: &str) -> SortSymbol {
        SortSymbol::new(name)
    }

    #[test]
    fn collect_symbols_walks_atom_and_quantifier() {
        let nat = s("Nat");
        let p = RelationSymbol::new("P", vec![nat.clone()]);
        // ∀x:Nat. P(x)
        let phi = Formula::Forall {
            sort: nat.clone(),
            body: Box::new(Formula::Atom {
                relation: p.clone(),
                args: vec![Term::Var(0)],
            }),
        };
        let syms = collect_symbols(&[phi]);
        assert!(syms.sorts.contains("Nat"));
        assert!(syms.relation_names.contains("P"));
        assert!(syms.function_names.is_empty());
    }

    #[test]
    fn collect_symbols_walks_function_application() {
        let nat = s("Nat");
        let succ = FunctionSymbol::new("succ", vec![nat.clone()], nat.clone());
        // Eq(succ(Var(0)), Var(1))
        let phi = Formula::Eq(
            Term::App {
                function: succ.clone(),
                args: vec![Term::Var(0)],
            },
            Term::Var(1),
        );
        let syms = collect_symbols(&[phi]);
        assert!(syms.function_names.contains("succ"));
        assert!(syms.sorts.contains("Nat"));
        assert!(syms.relation_names.is_empty());
    }

    #[test]
    fn collect_symbols_nested_structure() {
        let s_a = s("A");
        let s_b = s("B");
        let f = FunctionSymbol::new("f", vec![s_a.clone()], s_b.clone());
        let q = RelationSymbol::new("Q", vec![s_b.clone()]);
        // (∀x:A. Q(f(x))) ∧ (∃y:A. ¬Q(f(y)))
        let left = Formula::Forall {
            sort: s_a.clone(),
            body: Box::new(Formula::Atom {
                relation: q.clone(),
                args: vec![Term::App {
                    function: f.clone(),
                    args: vec![Term::Var(0)],
                }],
            }),
        };
        let right = Formula::Exists {
            sort: s_a.clone(),
            body: Box::new(Formula::NegAtom {
                relation: q.clone(),
                args: vec![Term::App {
                    function: f.clone(),
                    args: vec![Term::Var(0)],
                }],
            }),
        };
        let phi = Formula::And(Box::new(left), Box::new(right));
        let syms = collect_symbols(&[phi]);
        assert_eq!(syms.sorts, ["A", "B"].iter().map(|s| s.to_string()).collect());
        assert_eq!(syms.relation_names, std::iter::once("Q".to_string()).collect());
        assert_eq!(syms.function_names, std::iter::once("f".to_string()).collect());
    }

    #[test]
    fn collect_symbols_quantifier_binder_sort() {
        // ∀x:Custom. ⊤ — the binder sort is the only thing referenced.
        let phi = Formula::Forall {
            sort: s("Custom"),
            body: Box::new(Formula::Top),
        };
        let syms = collect_symbols(&[phi]);
        assert!(syms.sorts.contains("Custom"));
        assert!(syms.relation_names.is_empty());
        assert!(syms.function_names.is_empty());
    }
}
