//! Phase F: semantic explainability data structures.
//!
//! All types in this module are derived from existing pipeline artefacts
//! (`Signature`, `MutationResult`, `TightnessResult`) — no new evaluation
//! is performed here.  Contribution analysis requires a second tightness
//! evaluation against a stripped axiom set; that's done by the caller and
//! the result is handed to [`TheoremContribution::from_kill_sets`].

use std::collections::BTreeSet;

use num_bigint::BigUint;
use serde::Serialize;
use specmut_core::mutation::{MutantClass, MutationResult};
use specmut_core::signature::Signature;
use specmut_core::tightness::TightnessResult;

use crate::slicer::TheoremSlice;

// ============================================================================
// Feature 1: Slice metrics
// ============================================================================

/// Quantitative summary of what slicing achieved for one theorem.
#[derive(Debug, Clone, Serialize)]
pub struct SliceMetrics {
    /// Sorts in the global (pre-slice) signature.
    pub original_sort_count: usize,
    /// Sorts retained in the slice signature.
    pub reduced_sort_count: usize,
    /// Functions in the global signature.
    pub original_function_count: usize,
    /// Functions in the slice signature.
    pub reduced_function_count: usize,
    /// Relations in the global signature.
    pub original_relation_count: usize,
    /// Relations in the slice signature.
    pub reduced_relation_count: usize,
    /// Total translated axioms before slicing.
    pub original_axiom_count: usize,
    /// Axioms surviving in the slice.
    pub reduced_axiom_count: usize,
    /// `log2` of the model space at the supplied carrier bound,
    /// pre-slice.  Bit-length of the `BigUint` model-space count, which
    /// approximates `log2` and stays finite even when the raw count is
    /// astronomical.
    pub original_model_space_log2: f64,
    /// `log2` of the model space at the supplied carrier bound, post-slice.
    pub reduced_model_space_log2: f64,
    /// `1 - reduced_space / original_space` as a percentage in `[0, 100]`.
    pub reduction_percentage: f64,
    /// Wall-clock time the slice's model enumeration took.
    pub enumeration_ms: u128,
    /// Mutants generated for the slice.
    pub mutant_count: usize,
    /// Mutants surviving (alive) after tightness evaluation.
    pub surviving_mutant_count: usize,
    /// Killed / generated, in `[0.0, 1.0]`.  `0.0` when no mutants exist.
    pub kill_rate: f64,
}

impl SliceMetrics {
    /// Build slice metrics from the global signature, the slice, the
    /// enumeration cost, and the mutation / tightness results.
    pub fn compute(
        global_sig: &Signature,
        slice: &TheoremSlice,
        global_axiom_count: usize,
        model_bound: usize,
        enumeration_ms: u128,
        mutation: &MutationResult,
        tightness: &TightnessResult,
    ) -> Self {
        let original_log2 = log2_model_space(global_sig, model_bound);
        let reduced_log2 = log2_model_space(&slice.signature, model_bound);
        let reduction_percentage = if original_log2 == 0.0 {
            0.0
        } else {
            // Slicing is a per-relation strict subset, so original_log2 ≥
            // reduced_log2.  Translate the log-space gap into a percentage
            // of the original space removed.  `100 * (1 - 2^(reduced -
            // original))` works without ever materialising the BigUint.
            let ratio_log = reduced_log2 - original_log2;
            (1.0_f64 - 2.0_f64.powf(ratio_log)).max(0.0) * 100.0
        };
        let mutant_count = mutation.total_in_neighborhood;
        let surviving = tightness.alive_count;
        let kill_rate = if mutant_count == 0 {
            0.0
        } else {
            tightness.killed_count as f64 / mutant_count as f64
        };
        Self {
            original_sort_count: global_sig.sorts.len(),
            reduced_sort_count: slice.signature.sorts.len(),
            original_function_count: global_sig.functions.len(),
            reduced_function_count: slice.signature.functions.len(),
            original_relation_count: global_sig.relations.len(),
            reduced_relation_count: slice.signature.relations.len(),
            original_axiom_count: global_axiom_count,
            reduced_axiom_count: slice.all_axioms.len(),
            original_model_space_log2: original_log2,
            reduced_model_space_log2: reduced_log2,
            reduction_percentage,
            enumeration_ms,
            mutant_count,
            surviving_mutant_count: surviving,
            kill_rate,
        }
    }
}

fn log2_model_space(sig: &Signature, model_bound: usize) -> f64 {
    let space: BigUint = sig.model_space_size(model_bound);
    // `BigUint::bits()` is `floor(log2(n)) + 1` for n > 0, 0 for n = 0.
    // For our purpose (a reporting log2) the off-by-one in the high bit is
    // immaterial — it stays consistent between original and reduced.
    let bits = space.bits();
    if bits == 0 {
        0.0
    } else {
        // Subtract 1 so that 2^k has log2 = k (matches the integer log).
        (bits - 1) as f64
    }
}

// ============================================================================
// Feature 4: Mutation taxonomy
// ============================================================================

/// Per-class mutation tallies and kill rates.  Counts mutants that
/// participated in the tightness evaluation (i.e. members of the
/// neighborhood).  Aggregating multiple `MutationTaxonomy` values is
/// supported via [`Self::merge`].
#[derive(Debug, Clone, Default, Serialize)]
pub struct MutationTaxonomy {
    /// Total weakening mutants in the neighborhood.
    pub weakening_total: usize,
    /// Weakening mutants killed.
    pub weakening_killed: usize,
    /// `weakening_killed / weakening_total` (0.0 when total is 0).
    pub weakening_kill_rate: f64,
    /// Total strengthening mutants in the neighborhood.
    pub strengthening_total: usize,
    /// Strengthening mutants killed.
    pub strengthening_killed: usize,
    /// Strengthening kill rate.
    pub strengthening_kill_rate: f64,
    /// Total replacement mutants in the neighborhood.
    pub replacement_total: usize,
    /// Replacement mutants killed.
    pub replacement_killed: usize,
    /// Replacement kill rate.
    pub replacement_kill_rate: f64,
}

impl MutationTaxonomy {
    /// Build a taxonomy from a single slice's mutation + tightness results.
    pub fn compute(mutation: &MutationResult, tightness: &TightnessResult) -> Self {
        let mut tax = Self::default();
        for status in &tightness.mutant_statuses {
            let class = match mutation.mutants.get(status.mutant_index) {
                Some(m) => m.class,
                None => continue,
            };
            let (total, killed) = match class {
                MutantClass::Weakening => {
                    (&mut tax.weakening_total, &mut tax.weakening_killed)
                }
                MutantClass::Strengthening => {
                    (&mut tax.strengthening_total, &mut tax.strengthening_killed)
                }
                MutantClass::Replacement => {
                    (&mut tax.replacement_total, &mut tax.replacement_killed)
                }
            };
            *total += 1;
            if status.killed {
                *killed += 1;
            }
        }
        tax.recompute_rates();
        tax
    }

    /// Sum the totals and killed counts of `other` into `self` and
    /// recompute kill rates.
    pub fn merge(&mut self, other: &Self) {
        self.weakening_total += other.weakening_total;
        self.weakening_killed += other.weakening_killed;
        self.strengthening_total += other.strengthening_total;
        self.strengthening_killed += other.strengthening_killed;
        self.replacement_total += other.replacement_total;
        self.replacement_killed += other.replacement_killed;
        self.recompute_rates();
    }

    fn recompute_rates(&mut self) {
        self.weakening_kill_rate = rate(self.weakening_killed, self.weakening_total);
        self.strengthening_kill_rate =
            rate(self.strengthening_killed, self.strengthening_total);
        self.replacement_kill_rate = rate(self.replacement_killed, self.replacement_total);
    }

    /// Generate a one-line diagnostic naming the weakest mutation class.
    /// Returns an empty string when the taxonomy has no mutants.
    pub fn diagnostic(&self) -> String {
        let total = self.weakening_total + self.strengthening_total + self.replacement_total;
        if total == 0 {
            return String::new();
        }
        let classes = [
            ("constraint removal", self.weakening_total, self.weakening_kill_rate),
            (
                "constraint addition",
                self.strengthening_total,
                self.strengthening_kill_rate,
            ),
            (
                "predicate replacement",
                self.replacement_total,
                self.replacement_kill_rate,
            ),
        ];
        // Among classes with at least one mutant, find the minimum kill rate.
        let weakest = classes
            .iter()
            .filter(|(_, total, _)| *total > 0)
            .min_by(|a, b| a.2.partial_cmp(&b.2).unwrap_or(std::cmp::Ordering::Equal));
        match weakest {
            Some((name, _, rate)) => format!(
                "Spec is weakest against {} ({:.0}% kill rate).",
                name,
                rate * 100.0
            ),
            None => String::new(),
        }
    }
}

fn rate(killed: usize, total: usize) -> f64 {
    if total == 0 {
        0.0
    } else {
        killed as f64 / total as f64
    }
}

// ============================================================================
// Feature 5: Neighborhood table
// ============================================================================

/// One row in the per-slice neighborhood table.
#[derive(Debug, Clone, Serialize)]
pub struct NeighborhoodEntry {
    /// Index into `MutationResult::mutants`.
    pub index: usize,
    /// Human-readable name (`"weakening:0"` etc.).
    pub mutation_name: String,
    /// Mutation class.
    pub class: MutantClass,
    /// Jaccard distance from the original spec, as recorded on the mutant.
    pub distance: f64,
    /// Outcome flag for downstream consumers.
    pub status: MutantOutcome,
    /// Index of the join-irreducible component the mutation perturbed.
    pub perturbed_component: usize,
    /// `|Mod(S) △ Mod(S')|` over the enumerated model pool.  Provided so
    /// downstream consumers don't have to re-evaluate.
    pub sym_diff_size: usize,
}

/// Outcome flag attached to a [`NeighborhoodEntry`].  `Equivalent` is
/// reserved for future use — the current evaluator never sets it because
/// any neighborhood mutant that yields zero distinguishing models gets
/// labelled `Alive` (no implementation killed it).
#[derive(Debug, Clone, Copy, Serialize, PartialEq, Eq)]
pub enum MutantOutcome {
    /// Mutant was killed by at least one implementation.
    Killed,
    /// Mutant survived all implementations (alive).
    Alive,
    /// Mutant is provably equivalent to the original spec under the model
    /// enumeration; reserved (never set by the current evaluator).
    Equivalent,
}

/// Build the full neighborhood table for a slice.  `sym_diff_sizes` is a
/// parallel vector keyed by `MutationResult::neighborhood_mutants` order
/// (one entry per mutant in the neighborhood); pass an empty slice if
/// the caller has not computed them, in which case all `sym_diff_size`
/// fields default to `0`.
pub fn build_neighborhood_table(
    mutation: &MutationResult,
    tightness: &TightnessResult,
    sym_diff_sizes: &[usize],
) -> Vec<NeighborhoodEntry> {
    let mut entries: Vec<NeighborhoodEntry> = tightness
        .mutant_statuses
        .iter()
        .enumerate()
        .filter_map(|(slot, status)| {
            let mutant = mutation.mutants.get(status.mutant_index)?;
            let sym_diff_size = sym_diff_sizes.get(slot).copied().unwrap_or(0);
            let status_tag = if status.killed {
                MutantOutcome::Killed
            } else {
                MutantOutcome::Alive
            };
            Some(NeighborhoodEntry {
                index: status.mutant_index,
                mutation_name: format!("{:?}:{}", mutant.class, status.mutant_index)
                    .to_lowercase(),
                class: mutant.class,
                distance: mutant.distance,
                status: status_tag,
                perturbed_component: mutant.perturbed_component,
                sym_diff_size,
            })
        })
        .collect();
    // Spec §2.5.4: sort ascending by distance for stable table output.
    entries.sort_by(|a, b| a.distance.partial_cmp(&b.distance).unwrap_or(std::cmp::Ordering::Equal));
    entries
}

// ============================================================================
// Feature 2: Theorem contribution
// ============================================================================

/// How much a single theorem contributes to the slice's tightness, measured
/// against a baseline tightness evaluation using only the supporting
/// (predicate-equation) axioms.
#[derive(Debug, Clone, Serialize)]
pub struct TheoremContribution {
    /// Theorem this contribution describes.
    pub theorem_name: String,
    /// Tightness of the full slice (theorem + supporting axioms).
    pub tightness: f64,
    /// Total mutants killed by the full slice.
    pub total_kills: usize,
    /// Mutants killed by the full slice but NOT by the supporting axioms
    /// alone.  Higher = the theorem statement contributes essential
    /// constraint.
    pub unique_kills: usize,
    /// Mutants killed by both the full slice and the supporting axioms
    /// alone — the theorem and the support overlap on these.
    pub shared_kills: usize,
    /// `total_kills / neighborhood_size`.
    pub kill_rate: f64,
    /// `unique_kills / total_kills` (0.0 when no mutants killed at all).
    pub unique_kill_rate: f64,
    /// Categorical strength derived from `unique_kill_rate`.
    pub contribution_strength: ContributionStrength,
}

/// Categorical contribution rating.
#[derive(Debug, Clone, Copy, Serialize, PartialEq, Eq)]
pub enum ContributionStrength {
    /// `unique_kill_rate > 0.5`.
    High,
    /// `0.1 < unique_kill_rate <= 0.5`.
    Medium,
    /// `0.0 < unique_kill_rate <= 0.1`.
    Low,
    /// The theorem killed no mutants — its addition adds no constraint
    /// visible at this `n`.
    None,
}

impl TheoremContribution {
    /// Build a contribution from the full tightness result and a baseline
    /// "supporting axioms only" tightness result.
    pub fn from_kill_sets(
        theorem_name: impl Into<String>,
        full: &TightnessResult,
        baseline: &TightnessResult,
    ) -> Self {
        let full_killed: BTreeSet<usize> = full
            .mutant_statuses
            .iter()
            .filter(|s| s.killed)
            .map(|s| s.mutant_index)
            .collect();
        let baseline_killed: BTreeSet<usize> = baseline
            .mutant_statuses
            .iter()
            .filter(|s| s.killed)
            .map(|s| s.mutant_index)
            .collect();
        let unique = full_killed.difference(&baseline_killed).count();
        let shared = full_killed.intersection(&baseline_killed).count();
        let total = full_killed.len();
        let unique_kill_rate = if total == 0 {
            0.0
        } else {
            unique as f64 / total as f64
        };
        let kill_rate = if full.neighborhood_size == 0 {
            0.0
        } else {
            total as f64 / full.neighborhood_size as f64
        };
        Self {
            theorem_name: theorem_name.into(),
            tightness: full.score,
            total_kills: total,
            unique_kills: unique,
            shared_kills: shared,
            kill_rate,
            unique_kill_rate,
            contribution_strength: classify_contribution(total, unique_kill_rate),
        }
    }
}

fn classify_contribution(total_kills: usize, unique_kill_rate: f64) -> ContributionStrength {
    if total_kills == 0 {
        return ContributionStrength::None;
    }
    if unique_kill_rate > 0.5 {
        ContributionStrength::High
    } else if unique_kill_rate > 0.1 {
        ContributionStrength::Medium
    } else {
        ContributionStrength::Low
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use specmut_core::tightness::MutantStatus;

    fn dummy_status(idx: usize, killed: bool) -> MutantStatus {
        MutantStatus {
            mutant_index: idx,
            killed,
            killing_implementations: if killed { vec![0] } else { vec![] },
            direction: if killed { Some(true) } else { None },
            witness: None,
        }
    }

    fn dummy_result(statuses: Vec<MutantStatus>) -> TightnessResult {
        let killed_count = statuses.iter().filter(|s| s.killed).count();
        let alive_count = statuses.len() - killed_count;
        let neighborhood_size = statuses.len();
        let score = if neighborhood_size == 0 {
            0.0
        } else {
            killed_count as f64 / neighborhood_size as f64
        };
        TightnessResult {
            score,
            confidence_interval: (score, score),
            exhaustive: true,
            neighborhood_size,
            killed_count,
            alive_count,
            mutant_statuses: statuses,
        }
    }

    #[test]
    fn taxonomy_diagnostic_is_empty_when_no_mutants() {
        let tax = MutationTaxonomy::default();
        assert!(tax.diagnostic().is_empty());
    }

    #[test]
    fn taxonomy_merge_accumulates_totals() {
        let mut a = MutationTaxonomy {
            weakening_total: 4,
            weakening_killed: 2,
            strengthening_total: 2,
            strengthening_killed: 2,
            replacement_total: 1,
            replacement_killed: 0,
            ..Default::default()
        };
        a.recompute_rates();
        let b = a.clone();
        a.merge(&b);
        assert_eq!(a.weakening_total, 8);
        assert_eq!(a.weakening_killed, 4);
        assert!((a.weakening_kill_rate - 0.5).abs() < 1e-9);
    }

    #[test]
    fn contribution_unique_kills_zero_when_baseline_matches_full() {
        let full = dummy_result(vec![dummy_status(0, true), dummy_status(1, true)]);
        let baseline = dummy_result(vec![dummy_status(0, true), dummy_status(1, true)]);
        let c = TheoremContribution::from_kill_sets("t", &full, &baseline);
        assert_eq!(c.total_kills, 2);
        assert_eq!(c.unique_kills, 0);
        assert_eq!(c.shared_kills, 2);
        assert_eq!(c.contribution_strength, ContributionStrength::Low);
    }

    #[test]
    fn contribution_strength_none_when_no_kills() {
        let full = dummy_result(vec![dummy_status(0, false)]);
        let baseline = dummy_result(vec![dummy_status(0, false)]);
        let c = TheoremContribution::from_kill_sets("t", &full, &baseline);
        assert_eq!(c.total_kills, 0);
        assert_eq!(c.contribution_strength, ContributionStrength::None);
    }

    #[test]
    fn contribution_strength_high_when_unique_majority() {
        // Full kills {0, 1, 2}, baseline kills nothing → unique = 3 of 3.
        let full = dummy_result(vec![
            dummy_status(0, true),
            dummy_status(1, true),
            dummy_status(2, true),
        ]);
        let baseline = dummy_result(vec![
            dummy_status(0, false),
            dummy_status(1, false),
            dummy_status(2, false),
        ]);
        let c = TheoremContribution::from_kill_sets("t", &full, &baseline);
        assert_eq!(c.unique_kills, 3);
        assert_eq!(c.contribution_strength, ContributionStrength::High);
    }

    #[test]
    fn classify_boundaries() {
        assert_eq!(classify_contribution(0, 0.0), ContributionStrength::None);
        assert_eq!(classify_contribution(5, 0.6), ContributionStrength::High);
        assert_eq!(classify_contribution(5, 0.5), ContributionStrength::Medium);
        assert_eq!(classify_contribution(5, 0.11), ContributionStrength::Medium);
        assert_eq!(classify_contribution(5, 0.1), ContributionStrength::Low);
        assert_eq!(classify_contribution(5, 0.05), ContributionStrength::Low);
    }
}
