//! Phase 3 integration test: end-to-end pipeline on a miniature sorting
//! spec.
//!
//! The repo-structure note in §2 of the specification puts integration
//! tests at the workspace root under `tests/integration/`.  Cargo
//! discovers per-crate tests under `crates/<crate>/tests/`; this file
//! lives there so it actually runs.  Move it if the repo ever adopts a
//! workspace-level test harness.

use specmut_core::formula::{Formula, Term};
use specmut_core::lattice::{ModelEntailmentChecker, SpecElement};
use specmut_core::metric::JaccardMetric;
use specmut_core::model::{FiniteModel, ModelEnumerator};
use specmut_core::mutation::MutationGenerator;
use specmut_core::signature::{RelationSymbol, Signature, SortSymbol};
use specmut_core::tightness::TightnessEvaluator;

fn elem() -> SortSymbol {
    SortSymbol::new("Elem")
}

fn leq_sym() -> RelationSymbol {
    RelationSymbol::new("leq", vec![elem(), elem()])
}

fn sorted_out_sym() -> RelationSymbol {
    RelationSymbol::new("sorted_out", vec![elem()])
}

fn sorting_signature() -> Signature {
    Signature::new(
        vec![elem()],
        vec![],
        vec![leq_sym(), sorted_out_sym()],
    )
    .expect("sorting signature is valid")
}

/// Axiom 1: ∀x:Elem. sorted_out(x).
///
/// A coarse "output is sorted" stand-in for this scaffold test — we want
/// a unary witness that the mutation pipeline can perturb.
fn axiom_sorted_out_all() -> Formula {
    Formula::Forall {
        sort: elem(),
        body: Box::new(Formula::Atom {
            relation: sorted_out_sym(),
            args: vec![Term::Var(0)],
        }),
    }
}

/// Axiom 2: ∀x:Elem. ∀y:Elem. leq(x, y) ∨ leq(y, x).
///
/// "leq is total" — a structural property of the output's ordering that
/// stands in for a permutation-style axiom in this miniature spec.
fn axiom_leq_total() -> Formula {
    Formula::Forall {
        sort: elem(),
        body: Box::new(Formula::Forall {
            sort: elem(),
            body: Box::new(Formula::Or(
                Box::new(Formula::Atom {
                    relation: leq_sym(),
                    args: vec![Term::Var(1), Term::Var(0)],
                }),
                Box::new(Formula::Atom {
                    relation: leq_sym(),
                    args: vec![Term::Var(0), Term::Var(1)],
                }),
            )),
        }),
    }
}

#[test]
fn test_sorting_tightness() {
    let sig = sorting_signature();
    let spec = SpecElement::from_axioms([axiom_sorted_out_all(), axiom_leq_total()]);

    // Pipeline: enumerate models at carrier size 2, build metric +
    // entailment checker, generate mutants, evaluate tightness.
    let metric = JaccardMetric::from_signature(&sig, 2);
    let models_for_checker: Vec<FiniteModel> =
        ModelEnumerator::new(sig.clone(), 2).enumerate().collect();
    let checker = ModelEntailmentChecker::new(models_for_checker);

    let generator = MutationGenerator::new(metric, 1.0);
    let mutation_result = generator.generate(&spec, &sig, &checker);

    assert!(
        !mutation_result.decomposition.is_empty(),
        "the spec should decompose into at least one join-irreducible component"
    );
    assert!(
        mutation_result.total_in_neighborhood > 0,
        "expected non-empty ε-neighborhood for ε = 1.0"
    );

    // Use the full enumerated model set as the implementation pool: with
    // every relation interpretation available, any mutant whose Jaccard
    // distance from the spec is positive must be distinguished by *some*
    // model in the pool (that model lies in the symmetric difference of
    // the two model sets).
    let impls: Vec<FiniteModel> =
        ModelEnumerator::new(sig.clone(), 2).enumerate().collect();

    let evaluator = TightnessEvaluator::new(JaccardMetric::from_signature(&sig, 2));
    let result = evaluator.evaluate(&spec, &mutation_result, &impls);

    assert!(result.exhaustive);
    assert_eq!(
        result.killed_count + result.alive_count,
        result.neighborhood_size
    );
    assert!(
        result.score > 0.0,
        "expected non-trivial tightness, got {} (killed {}/{})",
        result.score,
        result.killed_count,
        result.neighborhood_size,
    );
}
