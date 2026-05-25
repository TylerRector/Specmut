//! Phase F: witness extraction for surviving (alive) mutants.
//!
//! For each alive mutant `M` we look for a model from the already-enumerated
//! pool that distinguishes the original spec `S` from `M` and attach it to
//! the mutant's `MutantStatus` as an explanation.  No new models are
//! synthesized — we re-use what the pipeline already enumerated.
//!
//! The extractor lives in the cli (not core) because the "human-readable"
//! parts of a witness (model description, interpretation) are presentation
//! concerns that the core algebra layer shouldn't carry.

use specmut_core::formula::Formula;
use specmut_core::model::FiniteModel;
use specmut_core::mutation::{Mutant, MutantClass, MutationResult};
use specmut_core::tightness::{MutantWitness, TightnessResult, WitnessDirection};

/// Attach a [`MutantWitness`] to every alive mutant in `tightness` whose
/// signature is satisfied by at least one distinguishing model in `models`.
///
/// `spec_axioms` are the original spec's axioms (per-slice); `mutation`
/// gives the per-mutant axiom sets.  Mutants for which no distinguishing
/// model exists in the enumerated pool keep `witness = None`.
pub fn attach_witnesses_for_alive(
    spec_axioms: &[Formula],
    mutation: &MutationResult,
    models: &[FiniteModel],
    tightness: &mut TightnessResult,
) {
    for status in tightness.mutant_statuses.iter_mut() {
        if status.killed {
            continue;
        }
        let mutant = match mutation.mutants.get(status.mutant_index) {
            Some(m) => m,
            None => continue,
        };
        let mutant_axioms: Vec<Formula> = mutant.spec.axioms.iter().cloned().collect();

        if let Some(witness) = extract_witness(spec_axioms, &mutant_axioms, mutant, models) {
            status.witness = Some(witness);
        }
    }
}

/// Find a distinguishing model in `models` and build a witness from it.
///
/// "Smallest" preference: among distinguishing models we pick the one with
/// the smallest total carrier size first, then the fewest true relation
/// tuples.  Ties break by enumeration order.  Returns `None` when no
/// distinguishing model exists in the pool (so the mutant is equivalent
/// to the spec at this `-n`).
pub fn extract_witness(
    spec_axioms: &[Formula],
    mutant_axioms: &[Formula],
    mutant: &Mutant,
    models: &[FiniteModel],
) -> Option<MutantWitness> {
    let mut best: Option<(usize, &FiniteModel, WitnessDirection)> = None;
    for model in models {
        let sat_spec = safely_satisfies(model, spec_axioms);
        let sat_mutant = safely_satisfies(model, mutant_axioms);
        if sat_spec == sat_mutant {
            continue;
        }
        let direction = if !sat_spec && sat_mutant {
            WitnessDirection::MutantAdmits
        } else {
            WitnessDirection::MutantRejects
        };
        let weight = witness_weight(model);
        match &best {
            None => best = Some((weight, model, direction)),
            Some((w, _, _)) if weight < *w => best = Some((weight, model, direction)),
            _ => {}
        }
    }
    let (_, model, direction) = best?;

    let model_description = describe_model(model);
    let distinguishing_facts = distinguishing_facts(model);
    let interpretation = generate_interpretation(mutant, &model_description, direction);

    Some(MutantWitness {
        model_description,
        direction,
        distinguishing_facts,
        interpretation,
    })
}

fn safely_satisfies(model: &FiniteModel, axioms: &[Formula]) -> bool {
    std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| model.satisfies_spec(axioms)))
        .unwrap_or(false)
}

/// Lower weight = simpler model.  Carrier size dominates, then relation
/// "non-default" tuple count.
fn witness_weight(model: &FiniteModel) -> usize {
    let carrier_total: usize = model.carriers.values().sum();
    let rel_total: usize = model.relation_interps.values().map(|s| s.len()).sum();
    // Multiply carrier by a large enough factor that it dominates the
    // secondary key without overflowing for any reasonable problem size.
    carrier_total * 1_000_000 + rel_total
}

/// One-line summary of a model.
pub fn describe_model(model: &FiniteModel) -> String {
    let mut parts: Vec<String> = Vec::new();
    let carriers: Vec<String> = model
        .carriers
        .iter()
        .map(|(sort, n)| format!("|{}| = {}", sort.name, n))
        .collect();
    if !carriers.is_empty() {
        parts.push(carriers.join(", "));
    }
    let rels: Vec<String> = model
        .relation_interps
        .iter()
        .map(|(name, tuples)| {
            let inner = tuples
                .iter()
                .map(|t| {
                    format!(
                        "({})",
                        t.iter()
                            .map(|x| x.to_string())
                            .collect::<Vec<_>>()
                            .join(",")
                    )
                })
                .collect::<Vec<_>>()
                .join(", ");
            format!("{name} = {{{inner}}}")
        })
        .collect();
    if !rels.is_empty() {
        parts.push(rels.join("; "));
    }
    if parts.is_empty() {
        "<empty model>".to_string()
    } else {
        parts.join(" | ")
    }
}

/// Itemize each non-empty relation interpretation as a fact line.
fn distinguishing_facts(model: &FiniteModel) -> Vec<String> {
    let mut facts: Vec<String> = model
        .relation_interps
        .iter()
        .filter(|(_, tuples)| !tuples.is_empty())
        .map(|(name, tuples)| {
            let inner = tuples
                .iter()
                .map(|t| {
                    format!(
                        "{}({})",
                        name,
                        t.iter()
                            .map(|x| x.to_string())
                            .collect::<Vec<_>>()
                            .join(", ")
                    )
                })
                .collect::<Vec<_>>()
                .join(", ");
            inner
        })
        .collect();
    if facts.is_empty() {
        facts.push("(no non-empty relations in witness)".to_string());
    }
    facts
}

fn generate_interpretation(
    mutant: &Mutant,
    model_summary: &str,
    direction: WitnessDirection,
) -> String {
    match (mutant.class, direction) {
        (MutantClass::Weakening, WitnessDirection::MutantAdmits) => format!(
            "Removing the axiom admits a model the spec rejects ({model_summary}). \
             The dropped axiom carries constraint not derivable from the rest of the spec."
        ),
        (MutantClass::Weakening, WitnessDirection::MutantRejects) => format!(
            "After removing the axiom, the spec admits a model the mutant rejects ({model_summary}). \
             The axiom is partially redundant — its removal weakens constraint, but in this direction."
        ),
        (MutantClass::Strengthening, WitnessDirection::MutantAdmits) => format!(
            "Adding the new conjunct admits a model the original rejects ({model_summary}). \
             Unexpected: typically strengthening should never enlarge the model set."
        ),
        (MutantClass::Strengthening, WitnessDirection::MutantRejects) => format!(
            "Adding the new conjunct would reject a model the spec admits ({model_summary}). \
             The spec currently allows this — the constraint is missing."
        ),
        (MutantClass::Replacement, WitnessDirection::MutantAdmits) => format!(
            "After predicate replacement, a model the spec rejects becomes admissible ({model_summary}). \
             The original axiom carries a distinction the replacement loses."
        ),
        (MutantClass::Replacement, WitnessDirection::MutantRejects) => format!(
            "After predicate replacement, a model the spec admits becomes inadmissible ({model_summary}). \
             The replacement is strictly stronger on this model."
        ),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use specmut_core::formula::Term;
    use specmut_core::signature::{RelationSymbol, Signature, SortSymbol};
    use std::collections::{BTreeMap, BTreeSet};

    fn unary_model(name: &str, tuples: Vec<usize>) -> FiniteModel {
        let s = SortSymbol::new("S");
        let sig = Signature::new(
            vec![s.clone()],
            vec![],
            vec![RelationSymbol::new(name, vec![s.clone()])],
        )
        .expect("test sig valid");
        let mut carriers = BTreeMap::new();
        carriers.insert(s, 2);
        let mut rels: BTreeMap<String, BTreeSet<Vec<usize>>> = BTreeMap::new();
        rels.insert(
            name.to_string(),
            tuples.into_iter().map(|x| vec![x]).collect(),
        );
        FiniteModel {
            signature: sig,
            carriers,
            function_interps: BTreeMap::new(),
            relation_interps: rels,
        }
    }

    #[test]
    fn describe_model_non_empty() {
        let m = unary_model("P", vec![0, 1]);
        let d = describe_model(&m);
        assert!(d.contains("|S| = 2"));
        assert!(d.contains("P = {(0), (1)}"));
    }

    #[test]
    fn describe_model_empty_carriers() {
        let m = FiniteModel {
            signature: Signature::new(vec![], vec![], vec![]).expect("empty sig valid"),
            carriers: BTreeMap::new(),
            function_interps: BTreeMap::new(),
            relation_interps: BTreeMap::new(),
        };
        let d = describe_model(&m);
        assert_eq!(d, "<empty model>");
    }

    #[test]
    fn witness_weight_prefers_smaller_carrier() {
        let small = unary_model("P", vec![0]);
        let mut large = small.clone();
        large.carriers.values_mut().for_each(|v| *v += 5);
        assert!(witness_weight(&small) < witness_weight(&large));
    }

    #[test]
    fn distinguishing_facts_non_empty_relations() {
        let m = unary_model("P", vec![0, 1]);
        let facts = distinguishing_facts(&m);
        assert_eq!(facts.len(), 1);
        assert!(facts[0].contains("P(0)") && facts[0].contains("P(1)"));
    }

    #[test]
    fn extract_witness_finds_distinguishing_model() {
        use specmut_core::lattice::SpecElement;
        use specmut_core::mutation::{Mutant, MutantClass};

        // Spec: ∀x:S. P(x).  Mutant (weakening): no axioms.
        let s = SortSymbol::new("S");
        let p_rel = RelationSymbol::new("P", vec![s.clone()]);
        let spec = vec![Formula::Forall {
            sort: s.clone(),
            body: Box::new(Formula::Atom {
                relation: p_rel.clone(),
                args: vec![Term::Var(0)],
            }),
        }];
        let mutant_axioms: Vec<Formula> = vec![]; // weakening drops the axiom
        let mutant = Mutant {
            spec: SpecElement::from_axioms(mutant_axioms.iter().cloned()),
            class: MutantClass::Weakening,
            perturbed_component: 0,
            original_predicate: Some(spec[0].clone()),
            replacement_predicate: None,
            distance: 0.5,
        };
        // Models: one satisfies spec (P all), one doesn't (P empty).
        let m_full = unary_model("P", vec![0, 1]);
        let m_empty = unary_model("P", vec![]);
        let pool = vec![m_full, m_empty];
        let w = extract_witness(&spec, &mutant_axioms, &mutant, &pool)
            .expect("expected a distinguishing witness");
        // The empty model satisfies the weakened (no-axiom) mutant but
        // not the spec → direction = MutantAdmits.
        assert_eq!(w.direction, WitnessDirection::MutantAdmits);
        assert!(!w.interpretation.is_empty());
    }
}
