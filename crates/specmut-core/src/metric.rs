//! Jaccard distance over specifications, defined via the symmetric
//! difference of model sets restricted to a finite enumeration.
//!
//! See §3.5 of the specification document.

use crate::formula::Formula;
use crate::model::{FiniteModel, ModelEnumerator};
use crate::signature::Signature;

/// Result of a single distance computation, with auxiliary counting data
/// useful for interpreting the score.
///
/// Distances always lie in `[0.0, 1.0]`.  When both specs are unsatisfiable
/// over the enumerated model set, the union is empty and the distance is
/// reported as `0.0` (the two specs are equivalent — both are ⊥).
#[derive(Debug, Clone, PartialEq)]
pub struct DistanceResult {
    /// Jaccard distance `|Mod(S₁) △ Mod(S₂)| / |Mod(S₁) ∪ Mod(S₂)|`.
    pub distance: f64,
    /// `|Mod(S₁) ∩ Mod(S₂)|`.
    pub intersection_size: usize,
    /// `|Mod(S₁) ∪ Mod(S₂)|`.
    pub union_size: usize,
    /// `|Mod(S₁) △ Mod(S₂)|`.
    pub symmetric_difference_size: usize,
    /// `|Mod(S₁)|`.
    pub left_size: usize,
    /// `|Mod(S₂)|`.
    pub right_size: usize,
}

/// A Jaccard metric backed by a pre-enumerated model set.
///
/// All distance queries are evaluated against the same fixed [`FiniteModel`]
/// list, which makes them deterministic and amenable to caching.
pub struct JaccardMetric {
    models: Vec<FiniteModel>,
}

impl JaccardMetric {
    /// Construct a metric from an externally supplied model list.
    pub fn new(models: Vec<FiniteModel>) -> Self {
        Self { models }
    }

    /// Construct a metric by exhaustively enumerating all Σ-structures with
    /// the given carrier size.
    pub fn from_signature(signature: &Signature, max_domain_size: usize) -> Self {
        let models: Vec<FiniteModel> =
            ModelEnumerator::new(signature.clone(), max_domain_size).enumerate().collect();
        Self::new(models)
    }

    /// The underlying model list.  Mainly useful for tests and for sharing
    /// the enumeration with other components (e.g. an entailment checker).
    pub fn models(&self) -> &[FiniteModel] {
        &self.models
    }

    /// Compute the Jaccard distance between two specifications.
    ///
    /// Both specs are evaluated against every enumerated model.  See
    /// [`DistanceResult`] for the returned auxiliary counts.
    pub fn distance(&self, s1: &[Formula], s2: &[Formula]) -> DistanceResult {
        let mut left_size = 0usize;
        let mut right_size = 0usize;
        let mut intersection_size = 0usize;
        for m in &self.models {
            let in_left = m.satisfies_spec(s1);
            let in_right = m.satisfies_spec(s2);
            if in_left {
                left_size += 1;
            }
            if in_right {
                right_size += 1;
            }
            if in_left && in_right {
                intersection_size += 1;
            }
        }
        let union_size = left_size + right_size - intersection_size;
        let symmetric_difference_size = union_size - intersection_size;
        let distance = if union_size == 0 {
            0.0
        } else {
            symmetric_difference_size as f64 / union_size as f64
        };
        debug_assert!(
            (0.0..=1.0).contains(&distance),
            "Jaccard distance out of [0,1]: {distance}"
        );
        DistanceResult {
            distance,
            intersection_size,
            union_size,
            symmetric_difference_size,
            left_size,
            right_size,
        }
    }

    /// Single-model perturbations of `spec` within Jaccard distance `epsilon`.
    ///
    /// Returns `(addable, removable)` as model indices into [`Self::models`]:
    ///
    /// * `addable[i]` ∉ Mod(spec) and adding it alone keeps the distance
    ///   `1 / (|Mod(spec)| + 1) ≤ epsilon`.
    /// * `removable[i]` ∈ Mod(spec) and removing it alone keeps the
    ///   distance `1 / |Mod(spec)| ≤ epsilon`.
    pub fn epsilon_neighborhood_models(
        &self,
        spec: &[Formula],
        epsilon: f64,
    ) -> (Vec<usize>, Vec<usize>) {
        let mut in_spec: Vec<bool> = Vec::with_capacity(self.models.len());
        let mut mod_size: usize = 0;
        for m in &self.models {
            let s = m.satisfies_spec(spec);
            in_spec.push(s);
            if s {
                mod_size += 1;
            }
        }

        let mut addable = Vec::new();
        let mut removable = Vec::new();

        if mod_size == 0 {
            // Adding any single model produces |Mod| = 1, symmetric difference 1,
            // union 1 → distance 1.0.  Within epsilon only if epsilon >= 1.0.
            if epsilon >= 1.0 {
                addable.extend(0..self.models.len());
            }
            // No models to remove.
            return (addable, removable);
        }

        let add_distance = 1.0 / (mod_size as f64 + 1.0);
        let remove_distance = 1.0 / mod_size as f64;

        for (i, &is_in) in in_spec.iter().enumerate() {
            if is_in {
                if remove_distance <= epsilon {
                    removable.push(i);
                }
            } else if add_distance <= epsilon {
                addable.push(i);
            }
        }
        (addable, removable)
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use super::*;
    use crate::formula::Term;
    use crate::signature::{RelationSymbol, SortSymbol};

    fn unary_sig() -> Signature {
        let s = SortSymbol::new("S");
        Signature::new(
            vec![s.clone()],
            vec![],
            vec![RelationSymbol::new("R", vec![s])],
        )
        .expect("valid sig")
    }

    fn forall_r() -> Formula {
        let s = SortSymbol::new("S");
        Formula::Forall {
            sort: s.clone(),
            body: Box::new(Formula::Atom {
                relation: RelationSymbol::new("R", vec![s]),
                args: vec![Term::Var(0)],
            }),
        }
    }

    fn exists_r() -> Formula {
        let s = SortSymbol::new("S");
        Formula::Exists {
            sort: s.clone(),
            body: Box::new(Formula::Atom {
                relation: RelationSymbol::new("R", vec![s]),
                args: vec![Term::Var(0)],
            }),
        }
    }

    #[test]
    fn from_signature_unary_relation_domain_two_has_four_models() {
        let m = JaccardMetric::from_signature(&unary_sig(), 2);
        assert_eq!(m.models().len(), 4);
    }

    #[test]
    fn identity_distance_is_zero() {
        let m = JaccardMetric::from_signature(&unary_sig(), 2);
        let phi = forall_r();
        let d = m.distance(std::slice::from_ref(&phi), std::slice::from_ref(&phi));
        assert_eq!(d.distance, 0.0);
    }

    #[test]
    fn distance_is_symmetric() {
        let m = JaccardMetric::from_signature(&unary_sig(), 2);
        let s1 = vec![forall_r()];
        let s2 = vec![exists_r()];
        let d12 = m.distance(&s1, &s2);
        let d21 = m.distance(&s2, &s1);
        assert_eq!(d12.distance, d21.distance);
    }

    #[test]
    fn distance_is_bounded() {
        let m = JaccardMetric::from_signature(&unary_sig(), 2);
        let pairs = [
            (vec![], vec![forall_r()]),
            (vec![forall_r()], vec![exists_r()]),
            (vec![exists_r()], vec![]),
        ];
        for (s1, s2) in &pairs {
            let d = m.distance(s1, s2);
            assert!(
                (0.0..=1.0).contains(&d.distance),
                "distance out of bounds: {}",
                d.distance
            );
        }
    }

    #[test]
    fn triangle_inequality_holds() {
        let m = JaccardMetric::from_signature(&unary_sig(), 2);
        let s1: Vec<Formula> = vec![];
        let s2 = vec![exists_r()];
        let s3 = vec![forall_r()];
        let d12 = m.distance(&s1, &s2).distance;
        let d23 = m.distance(&s2, &s3).distance;
        let d13 = m.distance(&s1, &s3).distance;
        // Triangle inequality with a small float tolerance.
        assert!(d13 <= d12 + d23 + 1e-9, "{d13} > {d12} + {d23}");
    }

    #[test]
    fn distance_forall_r_to_empty_matches_failure_fraction() {
        // Over 4 unary-relation models on domain {0,1}:
        //   R = {}     → ∀x.R(x) is false
        //   R = {0}    → false
        //   R = {1}    → false
        //   R = {0,1}  → true
        // So Mod(∀x.R(x)) = 1 model, Mod(⊤) = 4 models, intersection = 1,
        // union = 4, symmetric difference = 3, Jaccard = 3/4.
        let m = JaccardMetric::from_signature(&unary_sig(), 2);
        let d = m.distance(&[forall_r()], &[]);
        assert_eq!(d.left_size, 1);
        assert_eq!(d.right_size, 4);
        assert_eq!(d.intersection_size, 1);
        assert_eq!(d.union_size, 4);
        assert_eq!(d.symmetric_difference_size, 3);
        assert!((d.distance - 0.75).abs() < 1e-12);
    }

    #[test]
    fn epsilon_neighborhood_addable_and_removable() {
        let m = JaccardMetric::from_signature(&unary_sig(), 2);
        let spec = vec![forall_r()]; // |Mod| = 1
        // Add distance = 1/2 = 0.5, remove distance = 1/1 = 1.0.
        let (addable, removable) = m.epsilon_neighborhood_models(&spec, 0.5);
        assert_eq!(addable.len(), 3); // the 3 non-satisfying models
        assert!(removable.is_empty()); // remove distance 1.0 > 0.5
        let (_, removable2) = m.epsilon_neighborhood_models(&spec, 1.0);
        assert_eq!(removable2.len(), 1);
    }

    #[test]
    fn unsatisfiable_pair_has_zero_distance() {
        // Use bot as the spec — every model fails it.
        let m = JaccardMetric::from_signature(&unary_sig(), 2);
        let bot = vec![Formula::Bot];
        let d = m.distance(&bot, &bot);
        assert_eq!(d.union_size, 0);
        assert_eq!(d.distance, 0.0);
    }

    #[test]
    fn distance_result_has_round_trip_counts() {
        let m = JaccardMetric::from_signature(&unary_sig(), 2);
        let s1: Vec<Formula> = vec![forall_r()];
        let s2: Vec<Formula> = vec![];
        let d = m.distance(&s1, &s2);
        assert_eq!(
            d.union_size,
            d.left_size + d.right_size - d.intersection_size
        );
        assert_eq!(d.symmetric_difference_size, d.union_size - d.intersection_size);
    }

    #[test]
    fn distance_handles_btreeset_axiom_collections() {
        // Smoke test that ordering of axioms in collection types does not
        // affect the result.
        let m = JaccardMetric::from_signature(&unary_sig(), 2);
        let mut a: BTreeSet<Formula> = BTreeSet::new();
        a.insert(forall_r());
        a.insert(exists_r());
        let axioms: Vec<Formula> = a.into_iter().collect();
        let d = m.distance(&axioms, &axioms);
        assert_eq!(d.distance, 0.0);
    }
}
