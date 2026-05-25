//! Counterexample-guided tightness evaluation.
//!
//! See §3.8 and §5.3 of the specification document.
//!
//! CEGIS is an *optimization* of the exhaustive evaluator in
//! [`crate::tightness`]: it visits the same mutants and reports the same
//! kill / alive verdicts, but uses the lattice ordering between mutants
//! to prune work — if an implementation kills a mutant `S'`, the same
//! implementation kills every mutant lattice-comparable to `S'` in the
//! correct direction (see §3.8 for the proof).
//!
//! # Ordering recap
//!
//! `leq(a, b)` is true iff `b` entails `a` (i.e. `b` is stronger,
//! `Mod(b) ⊆ Mod(a)`).  Under that convention:
//!
//! * **Lost-acceptance kill** (`impl ⊨ spec` but `impl ⊭ S'`): the same
//!   `impl` kills every `S''` *stronger* than `S'`.  Pruning condition:
//!   `lattice.leq(S', S'')`.
//! * **New-acceptance kill** (`impl ⊨ S'` but `impl ⊭ spec`): the same
//!   `impl` kills every `S''` *weaker* than `S'`.  Pruning condition:
//!   `lattice.leq(S'', S')`.
//!
//! When a mutant cannot be located in the lattice (e.g. because the
//! lattice was built locally around a different center), CEGIS falls
//! back to direct verification with no pruning.  The verdict still
//! matches the exhaustive evaluator's; only the prune count drops.

use std::collections::{BTreeMap, BTreeSet};

use crate::formula::Formula;
use crate::lattice::{SpecElement, SpecLattice};
use crate::metric::JaccardMetric;
use crate::model::FiniteModel;
use crate::mutation::MutationResult;
use crate::tightness::{MutantStatus, TightnessResult};

/// State of the CEGIS loop.  Returned alongside the [`TightnessResult`]
/// for diagnostics.
#[derive(Debug)]
pub struct CegisState {
    /// Mutants not yet visited.  Always empty after [`CegisEvaluator::run`]
    /// returns.
    pub unchecked: BTreeSet<usize>,
    /// Killed mutants → index of the implementation that distinguished
    /// the spec from the mutant.
    pub killed: BTreeMap<usize, usize>,
    /// Mutants proven alive (no implementation distinguishes them).
    pub alive: BTreeSet<usize>,
    /// Implementations that produced kills, in discovery order.
    pub counterexamples: Vec<FiniteModel>,
    /// Number of WHILE-loop iterations executed.
    pub iterations: usize,
    /// Number of mutants killed transitively (via lattice pruning) rather
    /// than direct verification.
    pub pruned: usize,
}

/// CEGIS evaluator parameterized by a lattice and a metric.
///
/// The lattice provides the ordering needed for pruning; the metric
/// provides distance values for the greedy nearest-first synthesizer.
pub struct CegisEvaluator {
    lattice: SpecLattice,
    #[allow(dead_code)]
    metric: JaccardMetric,
}

impl CegisEvaluator {
    /// Build an evaluator over the given lattice and metric.
    pub fn new(lattice: SpecLattice, metric: JaccardMetric) -> Self {
        Self { lattice, metric }
    }

    /// Run the CEGIS loop and return the equivalent [`TightnessResult`]
    /// along with the diagnostic [`CegisState`].
    ///
    /// Per §5.3: at each iteration we pick the unchecked mutant with the
    /// smallest distance from the spec, walk the implementation list
    /// looking for a kill, and if found, prune lattice-comparable
    /// unchecked mutants in the correct direction.  Mutants for which
    /// `lattice.find_element` returns `None` are verified directly with
    /// no pruning.
    pub fn run(
        &self,
        spec: &SpecElement,
        mutants: &MutationResult,
        implementations: &[FiniteModel],
    ) -> (TightnessResult, CegisState) {
        let mut state = CegisState {
            unchecked: mutants.neighborhood_mutants.iter().copied().collect(),
            killed: BTreeMap::new(),
            alive: BTreeSet::new(),
            counterexamples: Vec::new(),
            iterations: 0,
            pruned: 0,
        };
        // Record the kill direction per mutant so that pruned mutants can
        // be assembled into the `MutantStatus` list with the right value.
        let mut kill_directions: BTreeMap<usize, bool> = BTreeMap::new();

        let spec_axioms: Vec<Formula> = spec.axioms.iter().cloned().collect();

        while !state.unchecked.is_empty() {
            state.iterations += 1;

            // Synthesizer: pick the unchecked mutant with the smallest
            // distance.  Break ties on mutant index for determinism.
            let idx = pick_closest(&state.unchecked, mutants);
            state.unchecked.remove(&idx);

            let mutant_axioms: Vec<Formula> =
                mutants.mutants[idx].spec.axioms.iter().cloned().collect();

            // Verifier: scan implementations for a distinguishing one.
            let mut killer: Option<(usize, bool)> = None;
            for (impl_idx, impl_model) in implementations.iter().enumerate() {
                let sat_spec = impl_model.satisfies_spec(&spec_axioms);
                let sat_mutant = impl_model.satisfies_spec(&mutant_axioms);
                if sat_spec != sat_mutant {
                    killer = Some((impl_idx, sat_spec));
                    break;
                }
            }

            if let Some((impl_idx, direction)) = killer {
                state.killed.insert(idx, impl_idx);
                kill_directions.insert(idx, direction);
                state.counterexamples.push(implementations[impl_idx].clone());

                state.pruned += self.prune(
                    idx,
                    impl_idx,
                    direction,
                    mutants,
                    &mut state.unchecked,
                    &mut state.killed,
                    &mut kill_directions,
                );
            } else {
                state.alive.insert(idx);
            }
        }

        let killed_count = state.killed.len();
        let alive_count = state.alive.len();
        let neighborhood_size = mutants.neighborhood_mutants.len();
        let score = if neighborhood_size == 0 {
            0.0
        } else {
            killed_count as f64 / neighborhood_size as f64
        };

        let mutant_statuses: Vec<MutantStatus> = mutants
            .neighborhood_mutants
            .iter()
            .map(|&idx| {
                if let Some(&impl_idx) = state.killed.get(&idx) {
                    MutantStatus {
                        mutant_index: idx,
                        killed: true,
                        killing_implementations: vec![impl_idx],
                        direction: kill_directions.get(&idx).copied(),
                        witness: None,
                    }
                } else {
                    MutantStatus {
                        mutant_index: idx,
                        killed: false,
                        killing_implementations: Vec::new(),
                        direction: None,
                        witness: None,
                    }
                }
            })
            .collect();

        let result = TightnessResult {
            score,
            confidence_interval: (score, score),
            exhaustive: true,
            neighborhood_size,
            killed_count,
            alive_count,
            mutant_statuses,
        };

        debug_assert!(state.unchecked.is_empty(), "CEGIS-01: unchecked drained");
        debug_assert_eq!(
            state.killed.len() + state.alive.len(),
            neighborhood_size,
            "CEGIS-01: killed + alive partitions neighborhood"
        );
        for k in state.killed.keys() {
            debug_assert!(!state.alive.contains(k), "CEGIS-02: killed ∩ alive empty");
        }

        (result, state)
    }

    /// Prune mutants that `impl_idx` provably kills by lattice
    /// comparability.  Returns the number of mutants pruned.
    #[allow(clippy::too_many_arguments)]
    fn prune(
        &self,
        killed_mutant_idx: usize,
        impl_idx: usize,
        direction: bool,
        mutants: &MutationResult,
        unchecked: &mut BTreeSet<usize>,
        killed: &mut BTreeMap<usize, usize>,
        kill_directions: &mut BTreeMap<usize, bool>,
    ) -> usize {
        let killed_lattice_idx = match self
            .lattice
            .find_element(&mutants.mutants[killed_mutant_idx].spec)
        {
            Some(i) => i,
            None => return 0, // Mutant not in local lattice: skip pruning.
        };

        let candidates: Vec<usize> = unchecked
            .iter()
            .copied()
            .filter(|&idx2| {
                match self.lattice.find_element(&mutants.mutants[idx2].spec) {
                    Some(other) => {
                        if direction {
                            // Lost-acceptance: prune mutants stronger than the killed one.
                            self.lattice.leq(killed_lattice_idx, other)
                        } else {
                            // New-acceptance: prune mutants weaker than the killed one.
                            self.lattice.leq(other, killed_lattice_idx)
                        }
                    }
                    None => false,
                }
            })
            .collect();

        for idx2 in &candidates {
            unchecked.remove(idx2);
            killed.insert(*idx2, impl_idx);
            kill_directions.insert(*idx2, direction);
        }
        candidates.len()
    }
}

fn pick_closest(unchecked: &BTreeSet<usize>, mutants: &MutationResult) -> usize {
    *unchecked
        .iter()
        .min_by(|&&a, &&b| {
            mutants.mutants[a]
                .distance
                .partial_cmp(&mutants.mutants[b].distance)
                .unwrap_or(std::cmp::Ordering::Equal)
                .then(a.cmp(&b))
        })
        .expect("pick_closest called on empty unchecked set")
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use super::*;
    use crate::formula::Term;
    use crate::lattice::ModelEntailmentChecker;
    use crate::model::ModelEnumerator;
    use crate::mutation::{Mutant, MutantClass, MutationGenerator};
    use crate::signature::{RelationSymbol, Signature, SortSymbol};

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

    fn three_unary_sig() -> Signature {
        let s = sort("S");
        Signature::new(
            vec![s.clone()],
            vec![],
            vec![
                RelationSymbol::new("P", vec![s.clone()]),
                RelationSymbol::new("Q", vec![s.clone()]),
                RelationSymbol::new("R", vec![s]),
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

    fn full_setup(
        sig: Signature,
        spec: SpecElement,
        epsilon: f64,
    ) -> (MutationResult, SpecLattice, Vec<FiniteModel>) {
        let models: Vec<FiniteModel> =
            ModelEnumerator::new(sig.clone(), 2).enumerate().collect();
        let checker = ModelEntailmentChecker::new(models.clone());
        let metric_gen = JaccardMetric::from_signature(&sig, 2);
        let generator = MutationGenerator::new(metric_gen, epsilon);
        let mr = generator.generate(&spec, &sig, &checker);
        let lattice =
            SpecLattice::build_local(sig, spec, epsilon, 1, 2, &checker).expect("lattice ok");
        (mr, lattice, models)
    }

    #[test]
    fn test_cegis_matches_exhaustive() {
        let sig = two_unary_sig();
        let spec = SpecElement::from_axioms([forall_pred("P"), forall_pred("Q")]);
        let (mr, lattice, models) = full_setup(sig.clone(), spec.clone(), 1.0);

        let metric_exh = JaccardMetric::from_signature(&sig, 2);
        let exhaustive = crate::tightness::TightnessEvaluator::new(metric_exh).evaluate(
            &spec,
            &mr,
            &models,
        );

        let metric_cegis = JaccardMetric::from_signature(&sig, 2);
        let cegis = CegisEvaluator::new(lattice, metric_cegis);
        let (cegis_result, _state) = cegis.run(&spec, &mr, &models);

        assert_eq!(cegis_result.score, exhaustive.score);
        assert_eq!(cegis_result.killed_count, exhaustive.killed_count);
        assert_eq!(cegis_result.alive_count, exhaustive.alive_count);
    }

    #[test]
    fn test_cegis_prunes() {
        // Engineer a 2-mutant chain in the lattice:
        //   killed:    spec_A = {forall P, forall Q, forall R}     (one strengthening of spec)
        //   pruned:    spec_B = {forall P, forall Q, forall R, forall T}  (an even stronger spec)
        //
        // spec_B entails spec_A, so leq(spec_A, spec_B) = true.
        // For an `impl` that satisfies the original spec but not spec_A,
        // it also fails spec_B (since spec_B's axioms include spec_A's).
        // CEGIS should kill spec_A directly and prune spec_B.
        //
        // The lattice we build is centered on spec_A (with ε = 1.0) so
        // that both spec_A and spec_B (spec_A + forall T) appear in it.
        let s = sort("S");
        let sig = Signature::new(
            vec![s.clone()],
            vec![],
            vec![
                RelationSymbol::new("P", vec![s.clone()]),
                RelationSymbol::new("Q", vec![s.clone()]),
                RelationSymbol::new("R", vec![s.clone()]),
                RelationSymbol::new("T", vec![s]),
            ],
        )
        .expect("valid sig");
        let spec = SpecElement::from_axioms([forall_pred("P"), forall_pred("Q")]);
        let spec_a = SpecElement::from_axioms([
            forall_pred("P"),
            forall_pred("Q"),
            forall_pred("R"),
        ]);
        let spec_b = SpecElement::from_axioms([
            forall_pred("P"),
            forall_pred("Q"),
            forall_pred("R"),
            forall_pred("T"),
        ]);

        let models: Vec<FiniteModel> =
            ModelEnumerator::new(sig.clone(), 2).enumerate().collect();
        let checker = ModelEntailmentChecker::new(models.clone());

        // Lattice centered on spec_A so that its strengthening spec_B is
        // a direct neighbor.
        let metric_lat = JaccardMetric::from_signature(&sig, 2);
        let lattice = SpecLattice::build_local(
            sig.clone(),
            spec_a.clone(),
            1.0,
            1,
            2,
            &checker,
        )
        .expect("lattice ok");
        let _ = metric_lat;
        assert!(lattice.find_element(&spec_a).is_some(), "spec_A in lattice");
        assert!(lattice.find_element(&spec_b).is_some(), "spec_B in lattice");

        // Hand-built mutation result so the test does not depend on the
        // mutation generator producing this exact chain.
        let metric_dist = JaccardMetric::from_signature(&sig, 2);
        let spec_axioms_vec: Vec<Formula> = spec.axioms.iter().cloned().collect();
        let mutants_vec = vec![
            Mutant {
                spec: spec_a.clone(),
                class: MutantClass::Strengthening,
                perturbed_component: 0,
                original_predicate: None,
                replacement_predicate: Some(forall_pred("R")),
                distance: metric_dist
                    .distance(
                        &spec_axioms_vec,
                        &spec_a.axioms.iter().cloned().collect::<Vec<_>>(),
                    )
                    .distance,
            },
            Mutant {
                spec: spec_b.clone(),
                class: MutantClass::Strengthening,
                perturbed_component: 0,
                original_predicate: None,
                replacement_predicate: Some(forall_pred("T")),
                distance: metric_dist
                    .distance(
                        &spec_axioms_vec,
                        &spec_b.axioms.iter().cloned().collect::<Vec<_>>(),
                    )
                    .distance,
            },
        ];
        let mut by_class: BTreeMap<MutantClass, usize> = BTreeMap::new();
        by_class.insert(MutantClass::Strengthening, 2);
        let mr = MutationResult {
            decomposition: vec![forall_pred("P"), forall_pred("Q")],
            mutants: mutants_vec,
            neighborhood_mutants: vec![0, 1],
            total_generated: 2,
            total_in_neighborhood: 2,
            by_class,
        };

        // An implementation that satisfies the original spec but not
        // spec_A (R fails for some element).  It also fails spec_B
        // because spec_B is even stronger.
        let mut carriers: BTreeMap<SortSymbol, usize> = BTreeMap::new();
        carriers.insert(sort("S"), 2);
        let mut relations: BTreeMap<String, BTreeSet<Vec<usize>>> = BTreeMap::new();
        relations.insert("P".into(), [vec![0], vec![1]].into_iter().collect());
        relations.insert("Q".into(), [vec![0], vec![1]].into_iter().collect());
        relations.insert("R".into(), BTreeSet::new()); // R holds for nothing
        relations.insert("T".into(), [vec![0], vec![1]].into_iter().collect());
        let killer_impl = FiniteModel {
            signature: sig.clone(),
            carriers,
            function_interps: BTreeMap::new(),
            relation_interps: relations,
        };

        let metric_cegis = JaccardMetric::from_signature(&sig, 2);
        let cegis = CegisEvaluator::new(lattice, metric_cegis);
        let (result, state) = cegis.run(&spec, &mr, &[killer_impl]);

        assert_eq!(result.killed_count, 2, "both mutants should be killed");
        assert!(state.pruned > 0, "expected at least one mutant pruned");
        assert!(
            state.iterations < mr.total_in_neighborhood,
            "CEGIS should run fewer iterations than the neighborhood size; got {} iterations for {} mutants",
            state.iterations,
            mr.total_in_neighborhood
        );
    }

    #[test]
    fn test_cegis_no_lattice_fallback() {
        // Build a lattice from a spec unrelated to the mutants so that
        // find_element returns None for every mutant.  CEGIS should
        // complete without panic and still produce correct verdicts.
        let sig = three_unary_sig();
        let spec = SpecElement::from_axioms([forall_pred("P"), forall_pred("Q")]);
        let unrelated = SpecElement::from_axioms([forall_pred("R")]);
        let models: Vec<FiniteModel> =
            ModelEnumerator::new(sig.clone(), 2).enumerate().collect();
        let checker = ModelEntailmentChecker::new(models.clone());
        let mr_metric = JaccardMetric::from_signature(&sig, 2);
        let generator = MutationGenerator::new(mr_metric, 1.0);
        let mr = generator.generate(&spec, &sig, &checker);
        let lattice =
            SpecLattice::build_local(sig.clone(), unrelated, 0.0, 1, 2, &checker)
                .expect("lattice ok");

        let metric_exh = JaccardMetric::from_signature(&sig, 2);
        let exhaustive = crate::tightness::TightnessEvaluator::new(metric_exh).evaluate(
            &spec,
            &mr,
            &models,
        );
        let metric_cegis = JaccardMetric::from_signature(&sig, 2);
        let cegis = CegisEvaluator::new(lattice, metric_cegis);
        let (cegis_result, state) = cegis.run(&spec, &mr, &models);

        assert_eq!(cegis_result.score, exhaustive.score);
        // With no lattice overlap, no pruning occurs.
        assert_eq!(state.pruned, 0);
    }

    #[test]
    fn test_cegis_empty_implementations() {
        let sig = two_unary_sig();
        let spec = SpecElement::from_axioms([forall_pred("P"), forall_pred("Q")]);
        let (mr, lattice, _models) = full_setup(sig.clone(), spec.clone(), 1.0);
        let impls: Vec<FiniteModel> = vec![];

        let metric = JaccardMetric::from_signature(&sig, 2);
        let cegis = CegisEvaluator::new(lattice, metric);
        let (result, state) = cegis.run(&spec, &mr, &impls);

        if mr.total_in_neighborhood > 0 {
            assert_eq!(result.killed_count, 0);
            assert_eq!(result.score, 0.0);
        } else {
            assert_eq!(result.score, 0.0);
        }
        assert_eq!(state.pruned, 0, "no pruning with no implementations");
    }

    #[test]
    fn test_cegis_single_implementation_kills_all() {
        // Use the exhaustive impl set so every non-equivalent mutant has
        // some distinguishing model — equivalently, with `epsilon < 1.0`
        // we keep impls that produce a chain of kills.  We supply the
        // full impl pool, so CEGIS kills everything, possibly via
        // pruning.
        let sig = two_unary_sig();
        let spec = SpecElement::from_axioms([forall_pred("P"), forall_pred("Q")]);
        let (mr, lattice, models) = full_setup(sig.clone(), spec.clone(), 1.0);
        let metric = JaccardMetric::from_signature(&sig, 2);
        let cegis = CegisEvaluator::new(lattice, metric);
        let (result, _state) = cegis.run(&spec, &mr, &models);
        assert_eq!(result.score, 1.0);
        assert_eq!(result.alive_count, 0);
    }

    #[test]
    fn test_cegis_state_partition() {
        let sig = two_unary_sig();
        let spec = SpecElement::from_axioms([forall_pred("P"), forall_pred("Q")]);
        let (mr, lattice, models) = full_setup(sig.clone(), spec.clone(), 1.0);
        let metric = JaccardMetric::from_signature(&sig, 2);
        let cegis = CegisEvaluator::new(lattice, metric);
        let (_result, state) = cegis.run(&spec, &mr, &models);
        assert!(state.unchecked.is_empty());
        assert_eq!(
            state.killed.len() + state.alive.len(),
            mr.total_in_neighborhood
        );
        for k in state.killed.keys() {
            assert!(!state.alive.contains(k));
        }
    }
}
