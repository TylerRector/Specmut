//! Integration tests for Phase F analysis types.
//!
//! These tests build small synthetic `MutationResult` and `TightnessResult`
//! values to exercise the pure-data parts of `SliceMetrics`,
//! `MutationTaxonomy`, and `NeighborhoodEntry` without spinning up the
//! whole pipeline.  The full-pipeline behavior is covered by the CLI
//! e2e tests in specmut-cli.

use specmut_core::formula::{Formula, Term};
use specmut_core::lattice::SpecElement;
use specmut_core::mutation::{Mutant, MutantClass, MutationResult};
use specmut_core::signature::{RelationSymbol, Signature, SortSymbol};
use specmut_core::tightness::{MutantStatus, TightnessResult};
use specmut_lean::analysis::{
    build_neighborhood_table, MutantOutcome, MutationTaxonomy, NeighborhoodEntry,
    SliceMetrics, TheoremContribution,
};
use specmut_lean::slicer::TheoremSlice;

fn s(name: &str) -> SortSymbol {
    SortSymbol::new(name)
}

fn unary_rel(name: &str) -> RelationSymbol {
    RelationSymbol::new(name, vec![s("S")])
}

fn unary_sig() -> Signature {
    Signature::new(vec![s("S")], vec![], vec![unary_rel("P"), unary_rel("Q")]).unwrap()
}

fn empty_axiom() -> Formula {
    Formula::Top
}

fn make_mutant(idx: usize, class: MutantClass, distance: f64) -> Mutant {
    Mutant {
        spec: SpecElement::from_axioms(std::iter::once(empty_axiom())),
        class,
        perturbed_component: idx,
        original_predicate: Some(Formula::Atom {
            relation: unary_rel("P"),
            args: vec![Term::Var(0)],
        }),
        replacement_predicate: None,
        distance,
    }
}

fn make_status(idx: usize, killed: bool) -> MutantStatus {
    MutantStatus {
        mutant_index: idx,
        killed,
        killing_implementations: if killed { vec![0] } else { vec![] },
        direction: if killed { Some(true) } else { None },
        witness: None,
    }
}

fn tight_from(statuses: Vec<MutantStatus>) -> TightnessResult {
    let killed = statuses.iter().filter(|s| s.killed).count();
    let n = statuses.len();
    let alive = n - killed;
    let score = if n == 0 { 0.0 } else { killed as f64 / n as f64 };
    TightnessResult {
        score,
        confidence_interval: (score, score),
        exhaustive: true,
        neighborhood_size: n,
        killed_count: killed,
        alive_count: alive,
        mutant_statuses: statuses,
    }
}

fn mutation_with(mutants: Vec<Mutant>) -> MutationResult {
    use specmut_core::mutation::MutantClass;
    use std::collections::BTreeMap;
    let mut by_class: BTreeMap<MutantClass, usize> = BTreeMap::new();
    for m in &mutants {
        *by_class.entry(m.class).or_insert(0) += 1;
    }
    let total = mutants.len();
    MutationResult {
        decomposition: vec![],
        mutants,
        neighborhood_mutants: (0..total).collect(),
        total_generated: total,
        total_in_neighborhood: total,
        by_class,
    }
}

// ----------------------------------------------------------------------------
// §2.4.5 — Mutation taxonomy
// ----------------------------------------------------------------------------

#[test]
fn test_taxonomy_sums_equal_neighborhood_size() {
    let muts = mutation_with(vec![
        make_mutant(0, MutantClass::Weakening, 0.1),
        make_mutant(1, MutantClass::Strengthening, 0.2),
        make_mutant(2, MutantClass::Replacement, 0.3),
        make_mutant(3, MutantClass::Replacement, 0.3),
    ]);
    let tight = tight_from(vec![
        make_status(0, true),
        make_status(1, true),
        make_status(2, false),
        make_status(3, true),
    ]);
    let tax = MutationTaxonomy::compute(&muts, &tight);
    let sum = tax.weakening_total + tax.strengthening_total + tax.replacement_total;
    assert_eq!(sum, tight.neighborhood_size);
}

#[test]
fn test_taxonomy_rates_bounded_zero_to_one() {
    let muts = mutation_with(vec![
        make_mutant(0, MutantClass::Weakening, 0.1),
        make_mutant(1, MutantClass::Strengthening, 0.2),
    ]);
    let tight = tight_from(vec![make_status(0, true), make_status(1, false)]);
    let tax = MutationTaxonomy::compute(&muts, &tight);
    for rate in [
        tax.weakening_kill_rate,
        tax.strengthening_kill_rate,
        tax.replacement_kill_rate,
    ] {
        assert!(
            (0.0..=1.0).contains(&rate),
            "kill rate out of bounds: {rate}"
        );
    }
}

#[test]
fn test_taxonomy_diagnostic_non_empty_when_mutants_present() {
    let muts = mutation_with(vec![
        make_mutant(0, MutantClass::Weakening, 0.1),
        make_mutant(1, MutantClass::Strengthening, 0.2),
    ]);
    let tight = tight_from(vec![make_status(0, false), make_status(1, true)]);
    let tax = MutationTaxonomy::compute(&muts, &tight);
    assert!(!tax.diagnostic().is_empty());
}

// ----------------------------------------------------------------------------
// §2.5.4 — Neighborhood table
// ----------------------------------------------------------------------------

#[test]
fn test_neighborhood_table_complete() {
    let muts = mutation_with(vec![
        make_mutant(0, MutantClass::Weakening, 0.3),
        make_mutant(1, MutantClass::Strengthening, 0.1),
        make_mutant(2, MutantClass::Replacement, 0.2),
    ]);
    let tight = tight_from(vec![
        make_status(0, true),
        make_status(1, true),
        make_status(2, false),
    ]);
    let entries = build_neighborhood_table(&muts, &tight, &[]);
    assert_eq!(entries.len(), muts.mutants.len());
}

#[test]
fn test_neighborhood_table_sorted_by_distance() {
    let muts = mutation_with(vec![
        make_mutant(0, MutantClass::Weakening, 0.4),
        make_mutant(1, MutantClass::Strengthening, 0.1),
        make_mutant(2, MutantClass::Replacement, 0.25),
    ]);
    let tight = tight_from(vec![
        make_status(0, true),
        make_status(1, false),
        make_status(2, true),
    ]);
    let entries = build_neighborhood_table(&muts, &tight, &[]);
    for win in entries.windows(2) {
        assert!(
            win[0].distance <= win[1].distance,
            "entries not sorted by distance: {:?} > {:?}",
            win[0].distance,
            win[1].distance
        );
    }
}

#[test]
fn test_neighborhood_entry_status_classification() {
    let muts = mutation_with(vec![
        make_mutant(0, MutantClass::Weakening, 0.1),
        make_mutant(1, MutantClass::Strengthening, 0.2),
    ]);
    let tight = tight_from(vec![make_status(0, true), make_status(1, false)]);
    let entries = build_neighborhood_table(&muts, &tight, &[]);
    let killed = entries
        .iter()
        .find(|e| e.index == 0)
        .expect("entry for mutant 0");
    let alive = entries
        .iter()
        .find(|e| e.index == 1)
        .expect("entry for mutant 1");
    assert_eq!(killed.status, MutantOutcome::Killed);
    assert_eq!(alive.status, MutantOutcome::Alive);
}

// ----------------------------------------------------------------------------
// §2.1.4 — Slice metrics
// ----------------------------------------------------------------------------

#[test]
fn test_slice_metrics_populated_and_bounded() {
    let global = unary_sig();
    let slice_sig = Signature::new(vec![s("S")], vec![], vec![unary_rel("P")]).unwrap();
    let slice = TheoremSlice {
        theorem_name: "t".into(),
        theorem_axiom: empty_axiom(),
        supporting_axioms: vec![],
        signature: slice_sig,
        all_axioms: vec![empty_axiom()],
        included_sorts: vec!["S".into()],
        included_relations: vec!["P".into()],
        included_functions: vec![],
        excluded_sorts: vec![],
    };
    let muts = mutation_with(vec![
        make_mutant(0, MutantClass::Weakening, 0.1),
        make_mutant(1, MutantClass::Strengthening, 0.2),
    ]);
    let tight = tight_from(vec![make_status(0, true), make_status(1, false)]);
    let metrics =
        SliceMetrics::compute(&global, &slice, /* global_axioms = */ 4, /* n = */ 2, 12, &muts, &tight);
    assert_eq!(metrics.original_sort_count, global.sorts.len());
    assert_eq!(metrics.reduced_sort_count, slice.signature.sorts.len());
    assert_eq!(metrics.original_relation_count, global.relations.len());
    assert_eq!(metrics.reduced_relation_count, slice.signature.relations.len());
    assert_eq!(metrics.mutant_count, 2);
    assert_eq!(metrics.surviving_mutant_count, 1);
    assert!((0.0..=1.0).contains(&metrics.kill_rate));
    assert!(metrics.reduction_percentage >= 0.0);
    assert!(metrics.original_model_space_log2 >= metrics.reduced_model_space_log2);
}

#[test]
fn test_slice_metrics_log2_decreases_when_relation_dropped() {
    // Global sig has 2 unary relations over a 2-element domain → 2^(2*2)
    // possible interpretations per relation, 2^(2+2) = 16.
    // Slice sig has 1 unary relation → 2^2 = 4.  log2 drops by 2.
    let global = unary_sig();
    let slice_sig = Signature::new(vec![s("S")], vec![], vec![unary_rel("P")]).unwrap();
    let slice = TheoremSlice {
        theorem_name: "t".into(),
        theorem_axiom: empty_axiom(),
        supporting_axioms: vec![],
        signature: slice_sig,
        all_axioms: vec![empty_axiom()],
        included_sorts: vec!["S".into()],
        included_relations: vec!["P".into()],
        included_functions: vec![],
        excluded_sorts: vec![],
    };
    let tight = tight_from(vec![]);
    let muts = mutation_with(vec![]);
    let metrics = SliceMetrics::compute(&global, &slice, 0, 2, 0, &muts, &tight);
    assert!(
        metrics.original_model_space_log2 > metrics.reduced_model_space_log2,
        "log2 should decrease after dropping a relation: orig={}, reduced={}",
        metrics.original_model_space_log2,
        metrics.reduced_model_space_log2,
    );
}

#[test]
fn test_slice_metrics_reduction_percentage_in_range() {
    let global = unary_sig();
    // Slice keeps everything → 0% reduction.
    let same = TheoremSlice {
        theorem_name: "t".into(),
        theorem_axiom: empty_axiom(),
        supporting_axioms: vec![],
        signature: global.clone(),
        all_axioms: vec![empty_axiom()],
        included_sorts: vec!["S".into()],
        included_relations: vec!["P".into(), "Q".into()],
        included_functions: vec![],
        excluded_sorts: vec![],
    };
    let muts = mutation_with(vec![]);
    let tight = tight_from(vec![]);
    let m = SliceMetrics::compute(&global, &same, 0, 2, 0, &muts, &tight);
    assert!(
        m.reduction_percentage.abs() < 1e-6,
        "expected ~0% reduction when slice == global, got {}",
        m.reduction_percentage
    );
    assert!(m.reduction_percentage >= 0.0 && m.reduction_percentage <= 100.0);
}

// ----------------------------------------------------------------------------
// §2.2.5 — Theorem contribution (uniqueness)
// ----------------------------------------------------------------------------

#[test]
fn test_contribution_unique_kills_subtract_baseline() {
    // Full kills {0,1,2}, baseline kills {0} → unique = 2, shared = 1.
    let full = tight_from(vec![
        make_status(0, true),
        make_status(1, true),
        make_status(2, true),
    ]);
    let baseline = tight_from(vec![
        make_status(0, true),
        make_status(1, false),
        make_status(2, false),
    ]);
    let c = TheoremContribution::from_kill_sets("T1", &full, &baseline);
    assert_eq!(c.total_kills, 3);
    assert_eq!(c.unique_kills, 2);
    assert_eq!(c.shared_kills, 1);
}

// ----------------------------------------------------------------------------
// Neighborhood entries respect mutation classes
// ----------------------------------------------------------------------------

#[test]
fn test_neighborhood_entry_carries_class() {
    let muts = mutation_with(vec![
        make_mutant(0, MutantClass::Weakening, 0.1),
        make_mutant(1, MutantClass::Strengthening, 0.2),
        make_mutant(2, MutantClass::Replacement, 0.15),
    ]);
    let tight = tight_from(vec![
        make_status(0, true),
        make_status(1, false),
        make_status(2, true),
    ]);
    let entries: Vec<NeighborhoodEntry> = build_neighborhood_table(&muts, &tight, &[]);
    assert!(entries.iter().any(|e| e.class == MutantClass::Weakening));
    assert!(entries.iter().any(|e| e.class == MutantClass::Strengthening));
    assert!(entries.iter().any(|e| e.class == MutantClass::Replacement));
}
