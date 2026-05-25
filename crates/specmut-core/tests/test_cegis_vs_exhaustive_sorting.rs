//! Phase 4 integration test: CEGIS produces the same tightness score as
//! the exhaustive evaluator on the miniature sorting spec, and prunes at
//! least one mutant in the process.
//!
//! The mutation generator emits only single-step mutations, which by
//! themselves are typically incomparable in the lattice.  To force a
//! prunable chain we splice the *empty* spec into the mutation set as a
//! synthetic two-step weakening; it sits below every single-axiom
//! weakening in the lattice and is the natural target of new-acceptance
//! pruning when one of those single-axiom weakenings is killed.

use std::collections::BTreeSet;

use specmut_core::cegis::CegisEvaluator;
use specmut_core::formula::{Formula, Term};
use specmut_core::lattice::{ModelEntailmentChecker, SpecElement, SpecLattice};
use specmut_core::metric::JaccardMetric;
use specmut_core::model::{FiniteModel, ModelEnumerator};
use specmut_core::mutation::{Mutant, MutantClass, MutationGenerator};
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
    Signature::new(vec![elem()], vec![], vec![leq_sym(), sorted_out_sym()])
        .expect("sorting signature is valid")
}

fn axiom_sorted_out_all() -> Formula {
    Formula::Forall {
        sort: elem(),
        body: Box::new(Formula::Atom {
            relation: sorted_out_sym(),
            args: vec![Term::Var(0)],
        }),
    }
}

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
fn test_cegis_vs_exhaustive_sorting() {
    let sig = sorting_signature();
    let spec = SpecElement::from_axioms([axiom_sorted_out_all(), axiom_leq_total()]);

    let models: Vec<FiniteModel> =
        ModelEnumerator::new(sig.clone(), 2).enumerate().collect();
    let checker = ModelEntailmentChecker::new(models.clone());

    let generator = MutationGenerator::new(JaccardMetric::from_signature(&sig, 2), 1.0);
    let mut mutation_result = generator.generate(&spec, &sig, &checker);

    // Lattice centered on the spec.  Phase 2's build_local always inserts
    // `bottom` (the empty spec) and `top` (the inconsistent spec), and
    // strengthenings / weakenings for atoms in the lattice's enumeration
    // vocabulary — so we know the empty spec lives in the lattice
    // strictly below every single-axiom weakening.
    let lattice = SpecLattice::build_local(sig.clone(), spec.clone(), 1.0, 2, 2, &checker)
        .expect("lattice build_local should succeed");

    // Splice the empty spec into the mutation set so it sits in the
    // neighborhood alongside the single-axiom weakenings.  It is two
    // mutation steps away from `spec` but lives in the lattice, which is
    // all CEGIS needs for `leq`-based pruning.
    let empty_spec = SpecElement::new(BTreeSet::new());
    assert!(
        lattice.find_element(&empty_spec).is_some(),
        "empty spec should be in the lattice as `bottom`"
    );
    if mutation_result
        .mutants
        .iter()
        .all(|m| m.spec.canonical_key() != empty_spec.canonical_key())
    {
        let metric_for_distance = JaccardMetric::from_signature(&sig, 2);
        let spec_axioms_vec: Vec<Formula> = spec.axioms.iter().cloned().collect();
        let d = metric_for_distance
            .distance(
                &spec_axioms_vec,
                &empty_spec.axioms.iter().cloned().collect::<Vec<_>>(),
            )
            .distance;
        if d > 0.0 && d < 1.0 {
            let next_idx = mutation_result.mutants.len();
            mutation_result.mutants.push(Mutant {
                spec: empty_spec.clone(),
                class: MutantClass::Weakening,
                perturbed_component: 0,
                original_predicate: Some(axiom_sorted_out_all()),
                replacement_predicate: None,
                distance: d,
            });
            mutation_result.neighborhood_mutants.push(next_idx);
            mutation_result.total_in_neighborhood += 1;
            mutation_result.total_generated += 1;
            *mutation_result
                .by_class
                .entry(MutantClass::Weakening)
                .or_insert(0) += 1;
        }
    }

    // Resort by distance and renumber the neighborhood to keep Phase 3's
    // sorted-by-distance invariant.
    mutation_result.mutants.sort_by(|a, b| {
        a.distance
            .partial_cmp(&b.distance)
            .unwrap_or(std::cmp::Ordering::Equal)
    });
    mutation_result.neighborhood_mutants = (0..mutation_result.mutants.len()).collect();

    // Use the full enumerated model set as the implementation pool — every
    // non-equivalent mutant then has a distinguishing model.
    let impls: Vec<FiniteModel> =
        ModelEnumerator::new(sig.clone(), 2).enumerate().collect();

    let exhaustive = TightnessEvaluator::new(JaccardMetric::from_signature(&sig, 2))
        .evaluate(&spec, &mutation_result, &impls);
    let (cegis_result, state) =
        CegisEvaluator::new(lattice, JaccardMetric::from_signature(&sig, 2))
            .run(&spec, &mutation_result, &impls);

    assert_eq!(cegis_result.score, exhaustive.score);
    assert_eq!(cegis_result.killed_count, exhaustive.killed_count);
    assert_eq!(cegis_result.alive_count, exhaustive.alive_count);
    assert!(
        state.pruned > 0,
        "expected at least one pruned mutant; got pruned = {}, iterations = {} for {} neighborhood mutants",
        state.pruned,
        state.iterations,
        mutation_result.total_in_neighborhood,
    );
}
