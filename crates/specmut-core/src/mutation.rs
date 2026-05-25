//! Mutation generation via join-irreducible decomposition and lattice
//! perturbations.
//!
//! See §3.6 and §5.2 of the specification document.
//!
//! Atomic-formula enumeration is local to this module (Phase 3): for each
//! relation `R` and every assignment of the relation's argument positions
//! to variable indices in `[0, MAX_VARS)`, we emit both `R(...)` and
//! `¬R(...)`.  These open atoms are universally closed before being used
//! to strengthen or replace components, so every mutant emitted is a
//! sentence in NNF (per FORMULA-01 / FORMULA-02 in §9.1).

use std::collections::{BTreeMap, BTreeSet};

use crate::formula::{Formula, Term};
use crate::lattice::{EntailmentChecker, SpecElement};
use crate::metric::JaccardMetric;
use crate::signature::{RelationSymbol, Signature, SortSymbol};

/// Phase 3 bound on the number of distinct variable indices used by
/// [`enumerate_atomic_formulas`].  Per the prompt: hardcoded to 3.
pub(crate) const MAX_VARS: usize = 3;

/// Classification of a mutant's relationship to the original spec.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, serde::Serialize)]
pub enum MutantClass {
    /// Mutant = `spec ∧ {new closed atom}`.  Strictly more restrictive.
    Strengthening,
    /// Mutant = `spec \ {axiom}`.  Strictly less restrictive.
    Weakening,
    /// Mutant = `(spec \ {axiom}) ∪ {new closed atom}`.
    Replacement,
}

/// A specification mutant with full provenance.
#[derive(Debug, Clone)]
pub struct Mutant {
    /// The mutated specification.
    pub spec: SpecElement,
    /// Classification of the mutation.
    pub class: MutantClass,
    /// Index into [`MutationResult::decomposition`] of the join-irreducible
    /// component that was perturbed.
    pub perturbed_component: usize,
    /// The original predicate that was modified (set for `Weakening` and
    /// `Replacement`).
    pub original_predicate: Option<Formula>,
    /// The replacement predicate (set for `Strengthening` and
    /// `Replacement`); already universally closed.
    pub replacement_predicate: Option<Formula>,
    /// Jaccard distance from the original spec.
    pub distance: f64,
}

/// Result of mutation generation.
#[derive(Debug, Clone)]
pub struct MutationResult {
    /// The join-irreducible decomposition of the original spec.
    pub decomposition: Vec<Formula>,
    /// All mutants produced and retained by the ε filter, sorted by
    /// ascending distance.
    pub mutants: Vec<Mutant>,
    /// Indices into [`Self::mutants`] of the ε-neighborhood.  After
    /// filtering at generation time this is `0..mutants.len()`.
    pub neighborhood_mutants: Vec<usize>,
    /// Total mutation candidates considered (before ε filter / dedup).
    pub total_generated: usize,
    /// Size of `neighborhood_mutants`.
    pub total_in_neighborhood: usize,
    /// Breakdown of `mutants` by [`MutantClass`].
    pub by_class: BTreeMap<MutantClass, usize>,
}

/// Generator for ε-neighborhood mutants.
pub struct MutationGenerator {
    metric: JaccardMetric,
    epsilon: f64,
}

impl MutationGenerator {
    /// Build a generator that scores candidates with `metric` and admits
    /// only mutants whose Jaccard distance to the spec is strictly less
    /// than `epsilon`.
    pub fn new(metric: JaccardMetric, epsilon: f64) -> Self {
        Self { metric, epsilon }
    }

    /// Compute the join-irreducible decomposition of `spec` per §5.1.
    ///
    /// For each axiom `aᵢ`, check whether `spec.axioms ∖ {aᵢ}` entails
    /// `aᵢ`; keep `aᵢ` only when it is not redundant.  A final pass
    /// asserts minimality (no kept component is entailed by the rest);
    /// failure panics — it would imply an unsound entailment backend or a
    /// need for iterative refinement.
    pub fn decompose(
        &self,
        spec: &SpecElement,
        entailment_checker: &dyn EntailmentChecker,
    ) -> Vec<Formula> {
        let axioms: Vec<Formula> = spec.axioms.iter().cloned().collect();
        let mut components = Vec::new();
        for i in 0..axioms.len() {
            let others: Vec<Formula> = axioms
                .iter()
                .enumerate()
                .filter(|(j, _)| *j != i)
                .map(|(_, f)| f.clone())
                .collect();
            if !entailment_checker.entails(&others, std::slice::from_ref(&axioms[i])) {
                components.push(axioms[i].clone());
            }
        }

        for i in 0..components.len() {
            let others: Vec<Formula> = components
                .iter()
                .enumerate()
                .filter(|(j, _)| *j != i)
                .map(|(_, f)| f.clone())
                .collect();
            assert!(
                !entailment_checker.entails(&others, std::slice::from_ref(&components[i])),
                "decomposition not minimal: component {i} is entailed by the rest"
            );
        }

        components
    }

    /// Generate every ε-mutant of `spec` per §5.2.
    ///
    /// For each join-irreducible component `jᵢ`:
    ///
    /// * **Weakening** — drop `jᵢ` from the axiom set.
    /// * **Strengthening** — universally close each atom `p` returned by
    ///   [`enumerate_atomic_formulas`] that is not already entailed by
    ///   the spec, then conjoin it.
    /// * **Replacement** — drop `jᵢ` and conjoin a closed `q ≠ jᵢ`.
    ///
    /// Each candidate's Jaccard distance is computed against the spec;
    /// candidates with distance strictly less than `epsilon` are kept.
    /// Duplicates (by [`SpecElement`] canonical key) are removed, and the
    /// surviving mutants are sorted by ascending distance.
    pub fn generate(
        &self,
        spec: &SpecElement,
        signature: &Signature,
        entailment_checker: &dyn EntailmentChecker,
    ) -> MutationResult {
        let decomposition = self.decompose(spec, entailment_checker);
        let raw_atoms = enumerate_atomic_formulas(signature);
        let closed_atoms: Vec<Formula> = raw_atoms
            .iter()
            .filter_map(|p| close_universal(p.clone(), signature))
            .collect();
        let spec_axioms: Vec<Formula> = spec.axioms.iter().cloned().collect();

        let mut mutants: Vec<Mutant> = Vec::new();
        let mut seen: BTreeSet<Vec<u8>> = BTreeSet::new();
        seen.insert(spec.canonical_key().to_vec());

        let mut total_generated: usize = 0;

        for (i, ji) in decomposition.iter().enumerate() {
            // Weakening — drop ji.
            {
                let mut next = spec.axioms.clone();
                next.remove(ji);
                self.consider(
                    SpecElement::new(next),
                    MutantClass::Weakening,
                    i,
                    Some(ji.clone()),
                    None,
                    &spec_axioms,
                    &mut seen,
                    &mut mutants,
                    &mut total_generated,
                );
            }

            // Strengthening — conjoin each closed atom not yet entailed.
            for p in &closed_atoms {
                if spec.axioms.contains(p) {
                    continue;
                }
                if entailment_checker.entails(&spec_axioms, std::slice::from_ref(p)) {
                    continue;
                }
                let mut next = spec.axioms.clone();
                next.insert(p.clone());
                self.consider(
                    SpecElement::new(next),
                    MutantClass::Strengthening,
                    i,
                    None,
                    Some(p.clone()),
                    &spec_axioms,
                    &mut seen,
                    &mut mutants,
                    &mut total_generated,
                );
            }

            // Replacement — drop ji, add a different closed atom.
            for q in &closed_atoms {
                if q == ji {
                    continue;
                }
                let mut next = spec.axioms.clone();
                next.remove(ji);
                next.insert(q.clone());
                self.consider(
                    SpecElement::new(next),
                    MutantClass::Replacement,
                    i,
                    Some(ji.clone()),
                    Some(q.clone()),
                    &spec_axioms,
                    &mut seen,
                    &mut mutants,
                    &mut total_generated,
                );
            }
        }

        mutants.sort_by(|a, b| {
            a.distance
                .partial_cmp(&b.distance)
                .unwrap_or(std::cmp::Ordering::Equal)
        });

        let neighborhood_mutants: Vec<usize> = (0..mutants.len()).collect();
        let total_in_neighborhood = mutants.len();
        let mut by_class: BTreeMap<MutantClass, usize> = BTreeMap::new();
        for m in &mutants {
            *by_class.entry(m.class).or_insert(0) += 1;
        }

        let result = MutationResult {
            decomposition,
            mutants,
            neighborhood_mutants,
            total_generated,
            total_in_neighborhood,
            by_class,
        };
        debug_assert_invariants(&result);
        result
    }

    #[allow(clippy::too_many_arguments)]
    fn consider(
        &self,
        candidate: SpecElement,
        class: MutantClass,
        component_idx: usize,
        original: Option<Formula>,
        replacement: Option<Formula>,
        spec_axioms: &[Formula],
        seen: &mut BTreeSet<Vec<u8>>,
        mutants: &mut Vec<Mutant>,
        total_generated: &mut usize,
    ) {
        if seen.contains(candidate.canonical_key()) {
            return;
        }
        seen.insert(candidate.canonical_key().to_vec());
        *total_generated += 1;
        let cand_axioms: Vec<Formula> = candidate.axioms.iter().cloned().collect();
        let d = self.metric.distance(spec_axioms, &cand_axioms).distance;
        // Skip distance-zero candidates: they are semantically equivalent
        // to the spec (different canonical form, same model set — typically
        // arising from vacuous-binder closings), and no implementation can
        // ever distinguish them, so they would dilute tightness scores.
        if d > 0.0 && d < self.epsilon {
            mutants.push(Mutant {
                spec: candidate,
                class,
                perturbed_component: component_idx,
                original_predicate: original,
                replacement_predicate: replacement,
                distance: d,
            });
        }
    }
}

/// Enumerate every atomic / negated-atomic formula over `signature` using
/// variable indices in `[0, MAX_VARS)`.
///
/// For a relation `R` of arity `r`, the function emits both `R(args)` and
/// `¬R(args)` for each of `MAX_VARS^r` argument tuples.  The returned
/// formulas are open (contain free de Bruijn variables); callers wishing
/// to use them as axioms must universally close them first.
pub(crate) fn enumerate_atomic_formulas(sig: &Signature) -> Vec<Formula> {
    let mut atoms = Vec::new();
    for r in &sig.relations {
        let arity = r.arity.len();
        let tuple_count = pow_usize(MAX_VARS, arity);
        for tuple_idx in 0..tuple_count {
            let args = decode_arg_tuple(tuple_idx, arity);
            let atom = Formula::Atom {
                relation: r.clone(),
                args: args.clone(),
            };
            let neg_atom = Formula::NegAtom {
                relation: r.clone(),
                args,
            };
            atoms.push(atom);
            atoms.push(neg_atom);
        }
    }
    atoms
}

fn decode_arg_tuple(mut idx: usize, arity: usize) -> Vec<Term> {
    // Position 0 is the most significant digit so numerical-order
    // iteration produces lexicographically ordered arg tuples.
    let mut args = vec![Term::Var(0); arity];
    for slot in (0..arity).rev() {
        args[slot] = Term::Var(idx % MAX_VARS);
        idx /= MAX_VARS;
    }
    args
}

fn pow_usize(base: usize, exp: usize) -> usize {
    let mut acc = 1usize;
    for _ in 0..exp {
        acc = acc.saturating_mul(base);
    }
    acc
}

/// Universally close the free variables of `f`.  Variable sorts are
/// inferred from the relation-symbol arities at the variable's occurrence
/// sites; any variable whose sort cannot be unambiguously inferred
/// (multiple incompatible arities at different positions) yields `None`.
///
/// Vacuous binders may be introduced when the free-variable index set
/// has gaps — the default sort (the first sort in the signature) is
/// used for those, since the binder does not constrain anything.
fn close_universal(f: Formula, sig: &Signature) -> Option<Formula> {
    let mut sorts: BTreeMap<usize, SortSymbol> = BTreeMap::new();
    if !infer_var_sorts(&f, 0, &mut sorts) {
        return None;
    }
    let free = f.free_vars();
    if free.is_empty() {
        return Some(f);
    }
    let max_idx = *free.iter().max()?;
    let default_sort = sig.sorts.iter().next()?.clone();
    let mut result = f;
    for i in 0..=max_idx {
        let sort = sorts.get(&i).cloned().unwrap_or_else(|| default_sort.clone());
        result = Formula::Forall {
            sort,
            body: Box::new(result),
        };
    }
    Some(result)
}

fn infer_var_sorts(
    f: &Formula,
    depth: usize,
    sorts: &mut BTreeMap<usize, SortSymbol>,
) -> bool {
    match f {
        Formula::Atom { relation, args } | Formula::NegAtom { relation, args } => {
            for (pos, arg) in args.iter().enumerate() {
                if !infer_term_sorts(arg, relation, pos, depth, sorts) {
                    return false;
                }
            }
            true
        }
        Formula::Eq(_, _) | Formula::Neq(_, _) => true,
        Formula::And(l, r) | Formula::Or(l, r) => {
            infer_var_sorts(l, depth, sorts) && infer_var_sorts(r, depth, sorts)
        }
        Formula::Forall { body, .. } | Formula::Exists { body, .. } => {
            infer_var_sorts(body, depth + 1, sorts)
        }
        Formula::Not(inner) => infer_var_sorts(inner, depth, sorts),
        Formula::Top | Formula::Bot => true,
    }
}

fn infer_term_sorts(
    t: &Term,
    relation: &RelationSymbol,
    pos: usize,
    depth: usize,
    sorts: &mut BTreeMap<usize, SortSymbol>,
) -> bool {
    match t {
        Term::Var(i) => {
            if *i >= depth {
                let free_idx = *i - depth;
                let arity_sort = match relation.arity.get(pos) {
                    Some(s) => s,
                    None => return false,
                };
                match sorts.get(&free_idx) {
                    Some(existing) if existing != arity_sort => return false,
                    _ => {
                        sorts.insert(free_idx, arity_sort.clone());
                    }
                }
            }
            true
        }
        Term::App { .. } => true,
    }
}

fn debug_assert_invariants(result: &MutationResult) {
    debug_assert_eq!(
        result.neighborhood_mutants.len(),
        result.total_in_neighborhood,
        "neighborhood_mutants vs total_in_neighborhood"
    );
    debug_assert_eq!(
        result.mutants.len(),
        result.total_in_neighborhood,
        "mutants vs total_in_neighborhood"
    );
    for m in &result.mutants {
        debug_assert!(
            (0.0..=1.0).contains(&m.distance),
            "METRIC-04: distance {} out of [0,1]",
            m.distance
        );
        for axiom in &m.spec.axioms {
            debug_assert!(
                !contains_not(axiom),
                "FORMULA-01: mutant axiom is not in NNF: {axiom:?}"
            );
            debug_assert!(
                axiom.is_sentence(),
                "FORMULA-02: mutant axiom has free vars: {axiom:?}"
            );
        }
    }
}

fn contains_not(f: &Formula) -> bool {
    match f {
        Formula::Not(_) => true,
        Formula::And(l, r) | Formula::Or(l, r) => contains_not(l) || contains_not(r),
        Formula::Forall { body, .. } | Formula::Exists { body, .. } => contains_not(body),
        Formula::Atom { .. }
        | Formula::NegAtom { .. }
        | Formula::Eq(_, _)
        | Formula::Neq(_, _)
        | Formula::Top
        | Formula::Bot => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lattice::ModelEntailmentChecker;
    use crate::model::ModelEnumerator;

    fn sort(name: &str) -> SortSymbol {
        SortSymbol::new(name)
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

    fn unary_pred(name: &str, var: usize) -> Formula {
        Formula::Atom {
            relation: RelationSymbol::new(name, vec![sort("S")]),
            args: vec![Term::Var(var)],
        }
    }

    fn forall_pred(name: &str) -> Formula {
        Formula::Forall {
            sort: sort("S"),
            body: Box::new(unary_pred(name, 0)),
        }
    }

    fn forall_p_and_q() -> Formula {
        // ∀x. P(x) ∧ Q(x)
        Formula::Forall {
            sort: sort("S"),
            body: Box::new(Formula::And(
                Box::new(unary_pred("P", 0)),
                Box::new(unary_pred("Q", 0)),
            )),
        }
    }

    fn checker_for(sig: &Signature) -> ModelEntailmentChecker {
        let models: Vec<_> = ModelEnumerator::new(sig.clone(), 2).enumerate().collect();
        ModelEntailmentChecker::new(models)
    }

    #[test]
    fn test_decompose_both_irreducible() {
        let sig = two_unary_sig();
        let checker = checker_for(&sig);
        let spec = SpecElement::from_axioms([forall_pred("P"), forall_pred("Q")]);
        let metric = JaccardMetric::from_signature(&sig, 2);
        let gen = MutationGenerator::new(metric, 1.0);
        let decomp = gen.decompose(&spec, &checker);
        assert_eq!(decomp.len(), 2);
    }

    #[test]
    fn test_decompose_redundant() {
        let sig = two_unary_sig();
        let checker = checker_for(&sig);
        // axiom 1 = ∀x. P(x) ∧ Q(x); axiom 2 = ∀x. P(x).  Axiom 2 is
        // entailed by axiom 1, so decomposition keeps only axiom 1.
        let spec = SpecElement::from_axioms([forall_p_and_q(), forall_pred("P")]);
        let metric = JaccardMetric::from_signature(&sig, 2);
        let gen = MutationGenerator::new(metric, 1.0);
        let decomp = gen.decompose(&spec, &checker);
        assert_eq!(decomp.len(), 1);
    }

    #[test]
    fn test_enumerate_atomic() {
        // 1 binary relation R over 1 sort S, MAX_VARS = 3.
        // 3^2 = 9 argument tuples × 2 (atom + neg) = 18 formulas.
        let s = sort("S");
        let sig = Signature::new(
            vec![s.clone()],
            vec![],
            vec![RelationSymbol::new("R", vec![s.clone(), s])],
        )
        .expect("valid sig");
        let atoms = enumerate_atomic_formulas(&sig);
        let expected = pow_usize(MAX_VARS, 2) * 2;
        assert_eq!(atoms.len(), expected);
        for f in &atoms {
            assert!(matches!(
                f,
                Formula::Atom { .. } | Formula::NegAtom { .. }
            ));
        }
    }

    #[test]
    fn test_weakening_mutant() {
        let sig = two_unary_sig();
        let checker = checker_for(&sig);
        let spec = SpecElement::from_axioms([forall_pred("P"), forall_pred("Q")]);
        let metric = JaccardMetric::from_signature(&sig, 2);
        let gen = MutationGenerator::new(metric, 1.0);
        let result = gen.generate(&spec, &sig, &checker);

        let weakenings: Vec<&Mutant> = result
            .mutants
            .iter()
            .filter(|m| m.class == MutantClass::Weakening)
            .collect();
        assert!(
            weakenings.len() >= result.decomposition.len(),
            "expected at least one weakening per component"
        );
        for w in weakenings {
            assert!(
                w.distance > 0.0,
                "weakening distance should be positive: {}",
                w.distance
            );
        }
    }

    #[test]
    fn test_mutant_deduplication() {
        let sig = two_unary_sig();
        let checker = checker_for(&sig);
        let spec = SpecElement::from_axioms([forall_pred("P")]);
        let metric = JaccardMetric::from_signature(&sig, 2);
        let gen = MutationGenerator::new(metric, 1.0);
        let result = gen.generate(&spec, &sig, &checker);
        let mut keys = BTreeSet::new();
        for m in &result.mutants {
            assert!(
                keys.insert(m.spec.canonical_key().to_vec()),
                "duplicate canonical key in mutant list"
            );
        }
    }

    #[test]
    fn test_mutants_sorted_by_distance() {
        let sig = two_unary_sig();
        let checker = checker_for(&sig);
        let spec = SpecElement::from_axioms([forall_pred("P"), forall_pred("Q")]);
        let metric = JaccardMetric::from_signature(&sig, 2);
        let gen = MutationGenerator::new(metric, 1.0);
        let result = gen.generate(&spec, &sig, &checker);
        for window in result.mutants.windows(2) {
            assert!(
                window[0].distance <= window[1].distance,
                "mutants not sorted: {} > {}",
                window[0].distance,
                window[1].distance
            );
        }
    }

    #[test]
    fn test_neighborhood_filter() {
        let sig = two_unary_sig();
        let checker = checker_for(&sig);
        let spec = SpecElement::from_axioms([forall_pred("P"), forall_pred("Q")]);
        let metric_strict = JaccardMetric::from_signature(&sig, 2);
        let strict_gen = MutationGenerator::new(metric_strict, 0.1);
        let strict_result = strict_gen.generate(&spec, &sig, &checker);
        for m in &strict_result.mutants {
            assert!(
                m.distance < 0.1,
                "mutant distance {} exceeds strict epsilon",
                m.distance
            );
        }

        let metric_loose = JaccardMetric::from_signature(&sig, 2);
        let loose_gen = MutationGenerator::new(metric_loose, 1.0);
        let loose_result = loose_gen.generate(&spec, &sig, &checker);
        assert!(
            loose_result.total_in_neighborhood >= strict_result.total_in_neighborhood,
            "loose neighborhood should be at least as large as strict"
        );
    }
}
