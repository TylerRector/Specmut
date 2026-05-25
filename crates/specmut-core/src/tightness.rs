//! Exhaustive tightness evaluation.
//!
//! See §3.7 of the specification document.
//!
//! For each mutant in the ε-neighborhood we walk every supplied
//! implementation looking for one whose satisfaction differs between the
//! spec and the mutant; the first such implementation marks the mutant
//! as killed and we move on.  Phase 3 implements only the exhaustive
//! path — sampling and SMT-backed evaluation are out of scope.

use crate::formula::Formula;
use crate::lattice::SpecElement;
use crate::metric::JaccardMetric;
use crate::model::FiniteModel;
use crate::mutation::MutationResult;

/// Per-mutant detail produced by a tightness evaluation.
#[derive(Debug, Clone, PartialEq)]
pub struct MutantStatus {
    /// Index into `MutationResult::mutants`.
    pub mutant_index: usize,
    /// True iff some implementation distinguished the original spec from
    /// the mutant.
    pub killed: bool,
    /// Indices of the implementations that distinguished the mutant from
    /// the spec.  Empty when `killed == false`.
    pub killing_implementations: Vec<usize>,
    /// Direction of the distinguishing observation.
    ///
    /// * `Some(true)` — the implementation satisfies the original spec
    ///   but not the mutant.
    /// * `Some(false)` — the implementation satisfies the mutant but not
    ///   the original spec.
    /// * `None` — the mutant was not killed.
    pub direction: Option<bool>,
    /// Phase F: optional explanation of why a surviving (alive) mutant
    /// could not be killed.  Populated by post-processing in the CLI
    /// pipeline (the core evaluator leaves this `None`); see
    /// `specmut-cli::witness` for the extractor.  Killed mutants always
    /// keep this `None`.
    pub witness: Option<MutantWitness>,
}

/// Explanation attached to a surviving (alive) mutant: a concrete model
/// that distinguishes the mutant's axiom set from the original spec, plus
/// a brief human-readable interpretation.
#[derive(Debug, Clone, PartialEq, serde::Serialize)]
pub struct MutantWitness {
    /// One-line summary of the distinguishing model (carrier sizes and
    /// non-default interpretations).
    pub model_description: String,
    /// Which side the witness model lives on.
    pub direction: WitnessDirection,
    /// Relation / function values that drive the distinction.
    pub distinguishing_facts: Vec<String>,
    /// Auto-generated interpretation derived from the mutation class.
    pub interpretation: String,
}

/// Which side a [`MutantWitness`] satisfies.
#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize)]
pub enum WitnessDirection {
    /// Witness satisfies the mutant but NOT the original spec.  The
    /// mutant admits something the original rejects — the spec already
    /// constrains this case.
    MutantAdmits,
    /// Witness satisfies the original spec but NOT the mutant.  The
    /// mutant rejects something the spec admits — the missing constraint
    /// lives in the mutant relative to the spec.
    MutantRejects,
}

/// Result of a tightness evaluation.
#[derive(Debug, Clone, PartialEq)]
pub struct TightnessResult {
    /// Tightness score `τ ∈ [0, 1]`.
    pub score: f64,
    /// Confidence interval `[lower, upper]`.  For exhaustive evaluation
    /// this is `(score, score)`.
    pub confidence_interval: (f64, f64),
    /// Whether the evaluation visited every neighborhood mutant.
    pub exhaustive: bool,
    /// Size of `MutationResult::neighborhood_mutants`.
    pub neighborhood_size: usize,
    /// Number of mutants observed killed.
    pub killed_count: usize,
    /// Number of mutants observed alive.
    pub alive_count: usize,
    /// Per-mutant detail, in the order visited.
    pub mutant_statuses: Vec<MutantStatus>,
}

/// Tightness evaluator parameterized by a Jaccard metric.
///
/// The metric is retained for future phases (sampling, weighted scoring);
/// the exhaustive evaluator only relies on `FiniteModel::satisfies_spec`.
pub struct TightnessEvaluator {
    #[allow(dead_code)]
    metric: JaccardMetric,
}

impl TightnessEvaluator {
    /// Build an evaluator backed by `metric`.
    pub fn new(metric: JaccardMetric) -> Self {
        Self { metric }
    }

    /// Evaluate tightness exhaustively against every implementation.
    ///
    /// For each mutant in `mutants.neighborhood_mutants` we test each
    /// implementation in order until one is found whose satisfaction
    /// differs between the spec and the mutant; that implementation
    /// records the kill direction.  Mutants for which no implementation
    /// distinguishes spec from mutant are marked alive.
    ///
    /// Edge case: when the neighborhood is empty the score is `0.0`,
    /// not `NaN`.
    pub fn evaluate(
        &self,
        spec: &SpecElement,
        mutants: &MutationResult,
        implementations: &[FiniteModel],
    ) -> TightnessResult {
        let spec_axioms: Vec<Formula> = spec.axioms.iter().cloned().collect();
        let statuses: Vec<MutantStatus> = mutants
            .neighborhood_mutants
            .iter()
            .map(|&idx| {
                let mutant = &mutants.mutants[idx];
                let mutant_axioms: Vec<Formula> =
                    mutant.spec.axioms.iter().cloned().collect();
                Self::evaluate_one(idx, &spec_axioms, &mutant_axioms, implementations)
            })
            .collect();

        let killed_count = statuses.iter().filter(|s| s.killed).count();
        let alive_count = statuses.len() - killed_count;
        let neighborhood_size = mutants.neighborhood_mutants.len();
        let score = if neighborhood_size == 0 {
            0.0
        } else {
            killed_count as f64 / neighborhood_size as f64
        };
        let result = TightnessResult {
            score,
            confidence_interval: (score, score),
            exhaustive: true,
            neighborhood_size,
            killed_count,
            alive_count,
            mutant_statuses: statuses,
        };
        debug_assert_invariants(&result);
        result
    }

    fn evaluate_one(
        idx: usize,
        spec_axioms: &[Formula],
        mutant_axioms: &[Formula],
        implementations: &[FiniteModel],
    ) -> MutantStatus {
        for (impl_idx, impl_model) in implementations.iter().enumerate() {
            let sat_spec = impl_model.satisfies_spec(spec_axioms);
            let sat_mutant = impl_model.satisfies_spec(mutant_axioms);
            if sat_spec != sat_mutant {
                return MutantStatus {
                    mutant_index: idx,
                    killed: true,
                    killing_implementations: vec![impl_idx],
                    direction: Some(sat_spec),
                    witness: None,
                };
            }
        }
        MutantStatus {
            mutant_index: idx,
            killed: false,
            killing_implementations: Vec::new(),
            direction: None,
            witness: None,
        }
    }
}

fn debug_assert_invariants(result: &TightnessResult) {
    // CEGIS-01 (exhaustive specialization): killed + alive == neighborhood_size.
    debug_assert_eq!(
        result.killed_count + result.alive_count,
        result.neighborhood_size,
        "CEGIS-01: killed + alive should partition the neighborhood"
    );
    debug_assert!(
        (0.0..=1.0).contains(&result.score),
        "score out of [0,1]: {}",
        result.score
    );
}

#[cfg(test)]
mod tests {
    use std::collections::{BTreeMap, BTreeSet};

    use super::*;
    use crate::formula::Term;
    use crate::lattice::ModelEntailmentChecker;
    use crate::model::ModelEnumerator;
    use crate::mutation::{MutantClass, MutationGenerator};
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

    fn impl_with(
        sig: Signature,
        n: usize,
        p: Vec<Vec<usize>>,
        q: Vec<Vec<usize>>,
    ) -> FiniteModel {
        let mut carriers: BTreeMap<SortSymbol, usize> = BTreeMap::new();
        carriers.insert(sort("S"), n);
        let mut relation_interps: BTreeMap<String, BTreeSet<Vec<usize>>> = BTreeMap::new();
        relation_interps.insert("P".to_string(), p.into_iter().collect());
        relation_interps.insert("Q".to_string(), q.into_iter().collect());
        FiniteModel {
            signature: sig,
            carriers,
            function_interps: BTreeMap::new(),
            relation_interps,
        }
    }

    fn setup(epsilon: f64) -> (SpecElement, MutationResult, Signature) {
        let sig = two_unary_sig();
        let spec = SpecElement::from_axioms([forall_pred("P"), forall_pred("Q")]);
        let metric = JaccardMetric::from_signature(&sig, 2);
        let models: Vec<_> =
            ModelEnumerator::new(sig.clone(), 2).enumerate().collect();
        let checker = ModelEntailmentChecker::new(models);
        let gen = MutationGenerator::new(metric, epsilon);
        let mr = gen.generate(&spec, &sig, &checker);
        (spec, mr, sig)
    }

    #[test]
    fn test_all_killed() {
        // Use a pair of implementations that together distinguish every
        // mutant.  An "all P, no Q" impl breaks any mutant whose
        // satisfaction depends on Q; an "all Q, no P" impl breaks any
        // mutant whose satisfaction depends on P.  Pair with an empty
        // model for safety.
        let (spec, mr, sig) = setup(1.0);
        // Build every possible 2-element model to maximize the chance of
        // killing every mutant.  This is the exhaustive impl set.
        let impls: Vec<FiniteModel> =
            ModelEnumerator::new(sig.clone(), 2).enumerate().collect();
        let metric = JaccardMetric::from_signature(&sig, 2);
        let evaluator = TightnessEvaluator::new(metric);
        let result = evaluator.evaluate(&spec, &mr, &impls);
        assert_eq!(result.alive_count, 0);
        assert_eq!(result.score, 1.0);
    }

    #[test]
    fn test_all_alive() {
        let (spec, mr, sig) = setup(1.0);
        let metric = JaccardMetric::from_signature(&sig, 2);
        let evaluator = TightnessEvaluator::new(metric);
        let impls: Vec<FiniteModel> = vec![];
        let result = evaluator.evaluate(&spec, &mr, &impls);
        if mr.total_in_neighborhood > 0 {
            assert_eq!(result.killed_count, 0);
            assert_eq!(result.score, 0.0);
        } else {
            assert_eq!(result.score, 0.0);
        }
    }

    #[test]
    fn test_partial_kill() {
        let (spec, mr, sig) = setup(1.0);
        // Single impl: P = {0, 1}, Q = {}.  Satisfies the P-axiom but not
        // the Q-axiom.  It distinguishes the spec from mutants whose
        // satisfaction depends on Q being universal, but not from those
        // that only differ on P.
        let impls = vec![impl_with(
            sig.clone(),
            2,
            vec![vec![0], vec![1]],
            vec![],
        )];
        let metric = JaccardMetric::from_signature(&sig, 2);
        let evaluator = TightnessEvaluator::new(metric);
        let result = evaluator.evaluate(&spec, &mr, &impls);
        assert_eq!(
            result.killed_count + result.alive_count,
            result.neighborhood_size
        );
        assert!(result.score > 0.0 && result.score < 1.0, "{}", result.score);
    }

    #[test]
    fn test_direction_flag() {
        // Drop axiom Q to get the weakening to {forall P}: an impl that
        // satisfies the spec ({forall P, forall Q}) but only barely the
        // mutant ({forall P}) would record direction = Some(true).
        let (spec, mr, sig) = setup(1.0);
        let impls = vec![impl_with(
            sig.clone(),
            2,
            vec![vec![0], vec![1]],
            vec![vec![0]], // Q only holds for 0 → fails spec, satisfies mutant.
        )];
        let metric = JaccardMetric::from_signature(&sig, 2);
        let evaluator = TightnessEvaluator::new(metric);
        let result = evaluator.evaluate(&spec, &mr, &impls);
        let weakening_q_idx = mr
            .mutants
            .iter()
            .position(|m| {
                m.class == MutantClass::Weakening
                    && m.original_predicate.as_ref() == Some(&forall_pred("Q"))
            })
            .expect("weakening that drops Q should exist");
        let status = result
            .mutant_statuses
            .iter()
            .find(|s| s.mutant_index == weakening_q_idx)
            .expect("status for weakening-Q");
        assert!(status.killed);
        // impl ⊭ spec, impl ⊨ mutant  ⇒  direction = Some(false).
        assert_eq!(status.direction, Some(false));
    }

    #[test]
    fn test_exhaustive_flag() {
        let (spec, mr, sig) = setup(1.0);
        let metric = JaccardMetric::from_signature(&sig, 2);
        let evaluator = TightnessEvaluator::new(metric);
        let impls: Vec<FiniteModel> = vec![];
        let result = evaluator.evaluate(&spec, &mr, &impls);
        assert!(result.exhaustive);
        assert_eq!(result.confidence_interval, (result.score, result.score));
    }

    #[test]
    fn test_killing_implementations_recorded() {
        let (spec, mr, sig) = setup(1.0);
        let impls = vec![
            impl_with(sig.clone(), 2, vec![], vec![]), // impl 0
            impl_with(sig.clone(), 2, vec![vec![0]], vec![]), // impl 1
        ];
        let metric = JaccardMetric::from_signature(&sig, 2);
        let evaluator = TightnessEvaluator::new(metric);
        let result = evaluator.evaluate(&spec, &mr, &impls);
        for status in &result.mutant_statuses {
            if status.killed {
                for &impl_idx in &status.killing_implementations {
                    assert!(impl_idx < impls.len(), "bad impl index {impl_idx}");
                }
                assert_eq!(
                    status.killing_implementations.len(),
                    1,
                    "exhaustive evaluator records exactly one killing impl per killed mutant"
                );
            } else {
                assert!(status.killing_implementations.is_empty());
            }
        }
    }
}
