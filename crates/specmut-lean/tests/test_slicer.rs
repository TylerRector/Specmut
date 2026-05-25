//! Integration tests for the theorem-scoped slicer (Phase E).
//!
//! Reuses the same JSON fixtures as the translator suite — Phase A is not
//! required at test time.

use std::collections::BTreeSet;

use num_bigint::BigUint;
use specmut_core::formula::Formula;
use specmut_core::signature::Signature;
use specmut_lean::ir_types::LeanIR;
use specmut_lean::slicer::slice_by_theorem;
use specmut_lean::translator::{AxiomOrigin, LeanTranslator, TranslationResult};

fn load_fixture(name: &str) -> LeanIR {
    let path = format!("tests/fixtures/{name}.ir.json");
    let contents = std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("missing fixture {path}: {e}"));
    serde_json::from_str(&contents).expect("fixture deserializes")
}

fn translate(name: &str) -> TranslationResult {
    let ir = load_fixture(name);
    LeanTranslator::translate(&ir).unwrap_or_else(|e| panic!("translate({name}) failed: {e}"))
}

/// Signature/model size limit used by `specmut-cli`.  Slices must fit under
/// this for the model enumerator to accept them at the supplied bound.
const MODEL_SPACE_LIMIT: u64 = 1 << 22;

// ----------------------------------------------------------------------------
// Translator invariant (Phase E §4)
// ----------------------------------------------------------------------------

#[test]
fn test_slice_axiom_provenance_parallel() {
    // Phase E adds `axiom_origins` parallel to `axioms`.  Every fixture
    // must satisfy len(axioms) == len(axiom_origins).
    for name in ["minimal", "bst", "hypotheses", "sort_lean"] {
        let r = translate(name);
        assert_eq!(
            r.axioms.len(),
            r.axiom_origins.len(),
            "axiom_origins parallel-vector invariant: fixture {name}"
        );
    }
}

// ----------------------------------------------------------------------------
// Slice production
// ----------------------------------------------------------------------------

#[test]
fn test_slice_per_translated_theorem() {
    // Slicer must emit exactly one slice per name in `translated_theorems`,
    // in the same order.
    for name in ["minimal", "bst", "hypotheses"] {
        let r = translate(name);
        let slices = slice_by_theorem(&r);
        let slice_names: Vec<_> = slices.iter().map(|s| s.theorem_name.clone()).collect();
        assert_eq!(
            slice_names, r.translated_theorems,
            "fixture {name}: slice names should match translated_theorems"
        );
    }
}

#[test]
fn test_slice_hypotheses_three_theorems() {
    // hypotheses.lean defines 3 theorems with no recursive predicates.
    // Each should produce a self-contained slice.
    let r = translate("hypotheses");
    let slices = slice_by_theorem(&r);
    assert_eq!(slices.len(), 3, "expected 3 slices for hypotheses fixture");
    for slice in &slices {
        // Every slice has at least the theorem axiom.
        assert!(!slice.all_axioms.is_empty());
        // Theorem axiom must be a sentence in NNF.
        assert!(slice.theorem_axiom.is_sentence());
        // Reduced signature is constructable.
        assert!(!slice.included_sorts.is_empty(), "slice should keep ≥1 sort");
    }
}

#[test]
fn test_slice_no_theorems_returns_empty() {
    // A predicates-only translation (manually constructed: empty theorems
    // list) yields no slices.  Caller falls back to global analysis.
    let r = translate("minimal");
    // Stub out the theorems and try again.
    let stripped = TranslationResult {
        signature: r.signature.clone(),
        axioms: r.axioms.clone(),
        axiom_origins: r.axiom_origins.clone(),
        translated_theorems: vec![],
        skipped_theorems: r.skipped_theorems.clone(),
        translated_predicates: r.translated_predicates.clone(),
        skipped_predicates: r.skipped_predicates.clone(),
        warnings: r.warnings.clone(),
        sort_filter: r.sort_filter.clone(),
    };
    assert!(slice_by_theorem(&stripped).is_empty());
}

// ----------------------------------------------------------------------------
// Slice closure
// ----------------------------------------------------------------------------

#[test]
fn test_slice_includes_supporting_predicate_equations() {
    // bst.lean's theorems reference `Sorted`.  The slices for those theorems
    // must include Sorted's defining equations.
    let r = translate("bst");
    let slices = slice_by_theorem(&r);
    // Find a slice whose theorem axiom references Sorted.
    let sorted_slice = slices.iter().find(|s| {
        let mut syms = specmut_lean::slicer::SymbolSet::default();
        for ax in &s.all_axioms {
            collect_into(ax, &mut syms);
        }
        syms.relation_names.contains("Sorted")
    });
    assert!(
        sorted_slice.is_some(),
        "expected at least one BST slice referencing Sorted"
    );
    if let Some(slice) = sorted_slice {
        // It must carry more axioms than just the theorem statement: the
        // Sorted equations should ride along as supporting axioms.
        assert!(
            !slice.supporting_axioms.is_empty(),
            "slice referencing Sorted should pull in Sorted's equations"
        );
    }
}

#[test]
fn test_slice_signature_is_subset_of_global() {
    // The reduced signature must never introduce a symbol the global
    // signature lacks.
    let r = translate("bst");
    let global_sort_names: BTreeSet<String> =
        r.signature.sorts.iter().map(|s| s.name.clone()).collect();
    let global_rel_names: BTreeSet<String> =
        r.signature.relations.iter().map(|x| x.name.clone()).collect();
    let global_fn_names: BTreeSet<String> =
        r.signature.functions.iter().map(|f| f.name.clone()).collect();
    for slice in slice_by_theorem(&r) {
        for s in &slice.included_sorts {
            assert!(global_sort_names.contains(s), "stray sort {s}");
        }
        for r_ in &slice.included_relations {
            assert!(global_rel_names.contains(r_), "stray relation {r_}");
        }
        for f in &slice.included_functions {
            assert!(global_fn_names.contains(f), "stray function {f}");
        }
    }
}

#[test]
fn test_slice_signature_valid_for_every_fixture() {
    // Each slice's reduced signature must satisfy `Signature::new`'s
    // invariants — same kind of construction the global filter is asked
    // to produce.
    for name in ["minimal", "bst", "hypotheses"] {
        let r = translate(name);
        for slice in slice_by_theorem(&r) {
            assert_valid_signature(&slice.signature, &slice.theorem_name);
        }
    }
}

// ----------------------------------------------------------------------------
// Slice reduces work
// ----------------------------------------------------------------------------

#[test]
fn test_bst_at_least_one_slice_fits_under_model_limit_at_n2() {
    // The whole point of Phase E: at least one BST theorem must produce a
    // slice whose model space at n=2 fits under the pipeline's
    // 2^22 ceiling.  Without slicing the union signature exceeds it.
    let r = translate("bst");
    let limit = BigUint::from(MODEL_SPACE_LIMIT);
    let mut any_fits = false;
    for slice in slice_by_theorem(&r) {
        let space = slice.signature.model_space_size(2);
        if space <= limit {
            any_fits = true;
            break;
        }
    }
    assert!(
        any_fits,
        "expected at least one BST slice with model space ≤ 2^22 at n=2"
    );
}

#[test]
fn test_slice_drops_sorts_versus_global_for_bst() {
    // Confirm at least one BST slice's reduced signature has strictly
    // fewer sorts than the global one — Phase E's value proposition.
    let r = translate("bst");
    let global_sort_count = r.signature.sorts.len();
    let any_smaller = slice_by_theorem(&r)
        .iter()
        .any(|s| s.included_sorts.len() < global_sort_count);
    assert!(
        any_smaller,
        "expected ≥1 BST slice with fewer sorts than the global signature \
         ({} sorts total)",
        global_sort_count
    );
}

#[test]
fn test_slice_records_excluded_sorts() {
    // If a slice has fewer sorts than the global signature, the difference
    // must show up in `excluded_sorts`.
    let r = translate("bst");
    let global_sort_count = r.signature.sorts.len();
    for slice in slice_by_theorem(&r) {
        let diff = global_sort_count - slice.included_sorts.len();
        assert_eq!(
            slice.excluded_sorts.len(),
            diff,
            "slice {} excluded_sorts ({}) should mirror sort-count delta ({})",
            slice.theorem_name,
            slice.excluded_sorts.len(),
            diff
        );
    }
}

// ----------------------------------------------------------------------------
// Helpers
// ----------------------------------------------------------------------------

fn collect_into(f: &Formula, into: &mut specmut_lean::slicer::SymbolSet) {
    let extra = specmut_lean::slicer::collect_symbols(std::slice::from_ref(f));
    for s in extra.sorts {
        into.sorts.insert(s);
    }
    for r in extra.relation_names {
        into.relation_names.insert(r);
    }
    for fname in extra.function_names {
        into.function_names.insert(fname);
    }
}

fn assert_valid_signature(sig: &Signature, ctx: &str) {
    // Roundtrip through Signature::new to confirm the invariants hold.
    let sorts: Vec<_> = sig.sorts.iter().cloned().collect();
    let functions: Vec<_> = sig.functions.iter().cloned().collect();
    let relations: Vec<_> = sig.relations.iter().cloned().collect();
    Signature::new(sorts, functions, relations)
        .unwrap_or_else(|e| panic!("slice {ctx}: signature failed roundtrip: {e}"));
}

// ----------------------------------------------------------------------------
// AxiomOrigin
// ----------------------------------------------------------------------------

#[test]
fn test_axiom_origins_cover_all_kinds_on_bst() {
    // bst.ir.json exercises both PredicateEquation (Sorted) and
    // TheoremStatement.  After dedup there should be at least one of each.
    let r = translate("bst");
    let mut has_pred = false;
    let mut has_thm = false;
    for origin in &r.axiom_origins {
        match origin {
            AxiomOrigin::PredicateEquation { .. } | AxiomOrigin::PredicateBody { .. } => {
                has_pred = true
            }
            AxiomOrigin::TheoremStatement { .. } => has_thm = true,
        }
    }
    assert!(has_pred, "BST should yield predicate-equation origins");
    assert!(has_thm, "BST should yield theorem-statement origins");
}
