//! Text- and JSON-shaped report formatting.

use std::time::Duration;

use serde::Serialize;
use specmut_core::formula::Formula;
use specmut_core::mutation::{Mutant, MutantClass, MutationResult};
use specmut_core::signature::Signature;
use specmut_core::tightness::TightnessResult;
use specmut_parser::fol_parser::format_formula;

use specmut_core::tightness::{MutantWitness, WitnessDirection};
use specmut_lean::analysis::{
    ContributionStrength, MutationTaxonomy, NeighborhoodEntry, SliceMetrics, TheoremContribution,
};

use crate::lean_pipeline::{
    AggregateReport, DependencyClosure, SliceOutcome, SliceStatus, TranslationSummary,
};

/// Snapshot of the values rendered by [`render_text`] and
/// [`render_json`].  Owned data so the caller can drop the underlying
/// pipeline artefacts before formatting.
pub struct Report<'a> {
    /// Path to the input spec file (for header line).
    pub spec_path: String,
    /// Model bound supplied at the command line.
    pub model_bound: usize,
    /// Quantifier rank supplied at the command line.
    pub quantifier_rank: usize,
    /// Neighborhood radius.
    pub epsilon: f64,
    /// Random seed.
    pub seed: u64,
    /// Number of models in the enumerated metric pool.
    pub models_enumerated: usize,
    /// The (post-NNF) signature parsed from the source.
    pub signature: &'a Signature,
    /// Original axioms in NNF.  Reserved for future report sections.
    #[allow(dead_code)]
    pub axioms: &'a [Formula],
    /// Mutation result.
    pub mutation: &'a MutationResult,
    /// Tightness result.
    pub tightness: &'a TightnessResult,
    /// True iff CEGIS was the evaluator.
    pub cegis: bool,
    /// True iff Z3 was used for entailment checking.
    pub smt: bool,
    /// Count of `Unknown` Z3 responses that triggered the
    /// model-enumeration fallback.  Always `0` for runs without
    /// `--smt`.
    pub fallback_count: usize,
    /// Timing breakdown.
    pub timing: TimingBreakdown,
    /// Lean-specific translation metadata.  Populated only when the source
    /// was a `.lean` file processed with `--lean-full`; absent (null /
    /// omitted in JSON) for `.fol` and extraction-only paths.
    pub lean_translation: Option<LeanTranslationReport>,
}

/// JSON-serialisable view of the Lean translator + sort-filter metadata.
#[derive(Debug, Clone, Serialize)]
pub struct LeanTranslationReport {
    /// Names of theorems whose statements made it into the axiom set.
    pub translated_theorems: Vec<String>,
    /// `(name, reason)` for theorems the translator skipped.
    pub skipped_theorems: Vec<SkippedItem>,
    /// Names of predicates that contributed at least one axiom.
    pub translated_predicates: Vec<String>,
    /// `(name, reason)` for predicates the translator skipped.
    pub skipped_predicates: Vec<SkippedItem>,
    /// Non-fatal diagnostics emitted by the translator or inherited from IR.
    pub warnings: Vec<String>,
    /// Sort-filter pass metadata.
    pub sort_filter: SortFilterJson,
    /// How many implementation models were auto-selected from the
    /// satisfying set.  `0` when the user passed `-i` files explicitly
    /// or `--no-auto-impl`.
    pub auto_implementations: usize,
}

/// One `(name, reason)` row from `skipped_theorems` / `skipped_predicates`.
#[derive(Debug, Clone, Serialize)]
pub struct SkippedItem {
    /// Declaration identifier.
    pub name: String,
    /// Why the translator skipped it.
    pub reason: String,
}

/// Sort-filter report mirroring `specmut_lean::SortFilterReport` for JSON output.
#[derive(Debug, Clone, Serialize)]
pub struct SortFilterJson {
    /// Sort count before reachability pruning.
    pub original_sorts: usize,
    /// Sort count after pruning.
    pub filtered_sorts: usize,
    /// Sort names that were dropped.
    pub removed: Vec<String>,
}

/// Timing snapshots gathered by the pipeline.
#[derive(Debug, Clone, Copy, Default, Serialize)]
pub struct TimingBreakdown {
    /// Parse phase duration in milliseconds.
    pub parse_ms: u128,
    /// Model enumeration duration in milliseconds.
    pub enumeration_ms: u128,
    /// Mutation generation duration in milliseconds.
    pub mutation_ms: u128,
    /// Tightness evaluation duration in milliseconds.
    pub tightness_ms: u128,
    /// Total wall-clock duration in milliseconds.
    pub total_ms: u128,
}

impl TimingBreakdown {
    /// Update `total_ms` to the supplied [`Duration`].
    pub fn with_total(mut self, total: Duration) -> Self {
        self.total_ms = total.as_millis();
        self
    }
}

/// Render `report` as a human-readable text block.
pub fn render_text(report: &Report) -> String {
    let mut out = String::new();
    out.push_str("specmut v0.1.0 — Specification Tightness Analysis\n\n");
    out.push_str(&format!("Spec file:        {}\n", report.spec_path));
    out.push_str(&format!("Model bound:      {}\n", report.model_bound));
    out.push_str(&format!("Quantifier rank:  {}\n", report.quantifier_rank));
    out.push_str(&format!("Epsilon:          {}\n", report.epsilon));
    out.push_str(&format!("Seed:             {}\n", report.seed));
    out.push_str(&format!(
        "Models enumerated: {}\n",
        report.models_enumerated
    ));
    if report.cegis {
        out.push_str("Evaluator:        CEGIS\n");
    } else {
        out.push_str("Evaluator:        Exhaustive\n");
    }
    if report.smt {
        out.push_str("Entailment:       Z3 SMT (hybrid)\n");
    } else {
        out.push_str("Entailment:       Model enumeration\n");
    }
    out.push('\n');
    out.push_str("Signature:\n");
    out.push_str(&format!(
        "  Sorts:     {}\n",
        report
            .signature
            .sorts
            .iter()
            .map(|s| s.name.clone())
            .collect::<Vec<_>>()
            .join(", ")
    ));
    if !report.signature.relations.is_empty() {
        let rels: Vec<String> = report
            .signature
            .relations
            .iter()
            .map(|r| {
                format!(
                    "{}({})",
                    r.name,
                    r.arity
                        .iter()
                        .map(|s| s.name.clone())
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            })
            .collect();
        out.push_str(&format!("  Relations: {}\n", rels.join(", ")));
    }
    if !report.signature.functions.is_empty() {
        let funs: Vec<String> = report
            .signature
            .functions
            .iter()
            .map(|f| {
                format!(
                    "{}({}) -> {}",
                    f.name,
                    f.domain
                        .iter()
                        .map(|s| s.name.clone())
                        .collect::<Vec<_>>()
                        .join(", "),
                    f.codomain.name
                )
            })
            .collect();
        out.push_str(&format!("  Functions: {}\n", funs.join(", ")));
    }
    out.push('\n');

    out.push_str(&format!(
        "Decomposition: {} join-irreducible component(s)\n",
        report.mutation.decomposition.len()
    ));
    for (i, f) in report.mutation.decomposition.iter().enumerate() {
        out.push_str(&format!("  [{i}] {}\n", format_formula(f)));
    }
    out.push('\n');

    out.push_str(&format!(
        "Mutations: {} generated, {} in neighborhood (ε < {})\n",
        report.mutation.total_generated, report.mutation.total_in_neighborhood, report.epsilon
    ));
    out.push_str(&format!(
        "  Weakening:     {}\n",
        report
            .mutation
            .by_class
            .get(&MutantClass::Weakening)
            .copied()
            .unwrap_or(0)
    ));
    out.push_str(&format!(
        "  Strengthening: {}\n",
        report
            .mutation
            .by_class
            .get(&MutantClass::Strengthening)
            .copied()
            .unwrap_or(0)
    ));
    out.push_str(&format!(
        "  Replacement:   {}\n",
        report
            .mutation
            .by_class
            .get(&MutantClass::Replacement)
            .copied()
            .unwrap_or(0)
    ));
    out.push('\n');

    out.push_str(&format!(
        "Tightness: τ = {:.3} ({}/{} killed, {} alive)\n",
        report.tightness.score,
        report.tightness.killed_count,
        report.tightness.neighborhood_size,
        report.tightness.alive_count,
    ));
    out.push_str(&format!(
        "Confidence interval: [{:.3}, {:.3}]\n",
        report.tightness.confidence_interval.0, report.tightness.confidence_interval.1
    ));
    out.push('\n');

    let alive: Vec<&Mutant> = report
        .tightness
        .mutant_statuses
        .iter()
        .filter(|s| !s.killed)
        .filter_map(|s| report.mutation.mutants.get(s.mutant_index))
        .collect();
    if !alive.is_empty() {
        out.push_str("Alive mutants:\n");
        for m in alive.iter().take(10) {
            out.push_str(&format!(
                "  {:8?}  d={:.3}  perturbed=[{}]\n",
                m.class, m.distance, m.perturbed_component
            ));
        }
        if alive.len() > 10 {
            out.push_str(&format!("  ... and {} more\n", alive.len() - 10));
        }
    } else {
        out.push_str("Alive mutants: none\n");
    }
    out.push('\n');
    out.push_str(&format!(
        "Timing: parse {} ms, enumeration {} ms, mutation {} ms, tightness {} ms, total {} ms\n",
        report.timing.parse_ms,
        report.timing.enumeration_ms,
        report.timing.mutation_ms,
        report.timing.tightness_ms,
        report.timing.total_ms,
    ));
    if report.fallback_count > 0 {
        out.push_str(&format!(
            "\nNote: Z3 returned Unknown on {} queries; model enumeration was used as fallback.\n",
            report.fallback_count
        ));
    }
    out
}

/// Render `report` as the JSON shape described in §8.1.
pub fn render_json(report: &Report) -> String {
    let value = JsonReport::from_report(report);
    serde_json::to_string_pretty(&value).unwrap_or_else(|_| "{}".to_string())
}

#[derive(Serialize)]
struct JsonReport {
    version: &'static str,
    spec_file: String,
    parameters: JsonParameters,
    signature: JsonSignature,
    decomposition: Vec<JsonDecompositionItem>,
    tightness: JsonTightness,
    alive_mutants: Vec<JsonAliveMutant>,
    timing: TimingBreakdown,
    evaluator: &'static str,
    smt: bool,
    smt_fallback_count: usize,
    /// Lean-specific translation metadata.  Absent (omitted from JSON) for
    /// `.fol` inputs and the extraction-only Lean fallback path.
    #[serde(skip_serializing_if = "Option::is_none")]
    lean_translation: Option<LeanTranslationReport>,
}

#[derive(Serialize)]
struct JsonParameters {
    model_bound: usize,
    quantifier_rank: usize,
    epsilon: f64,
    seed: u64,
    models_enumerated: usize,
}

#[derive(Serialize)]
struct JsonSignature {
    sorts: Vec<String>,
    functions: Vec<JsonFunction>,
    relations: Vec<JsonRelation>,
}

#[derive(Serialize)]
struct JsonFunction {
    name: String,
    domain: Vec<String>,
    codomain: String,
}

#[derive(Serialize)]
struct JsonRelation {
    name: String,
    arity: Vec<String>,
}

#[derive(Serialize)]
struct JsonDecompositionItem {
    index: usize,
    formula: String,
}

#[derive(Serialize)]
struct JsonTightness {
    score: f64,
    confidence_interval: [f64; 2],
    exhaustive: bool,
    neighborhood_size: usize,
    killed: usize,
    alive: usize,
}

#[derive(Serialize)]
struct JsonAliveMutant {
    index: usize,
    class: String,
    perturbed_component: usize,
    distance: f64,
    formula_summary: String,
    /// Phase F: explanatory witness model for this surviving mutant.
    /// `None` when no distinguishing model exists in the enumerated pool.
    #[serde(skip_serializing_if = "Option::is_none")]
    witness: Option<MutantWitness>,
}

impl JsonReport {
    fn from_report(report: &Report) -> Self {
        let parameters = JsonParameters {
            model_bound: report.model_bound,
            quantifier_rank: report.quantifier_rank,
            epsilon: report.epsilon,
            seed: report.seed,
            models_enumerated: report.models_enumerated,
        };
        let signature = JsonSignature {
            sorts: report
                .signature
                .sorts
                .iter()
                .map(|s| s.name.clone())
                .collect(),
            functions: report
                .signature
                .functions
                .iter()
                .map(|f| JsonFunction {
                    name: f.name.clone(),
                    domain: f.domain.iter().map(|s| s.name.clone()).collect(),
                    codomain: f.codomain.name.clone(),
                })
                .collect(),
            relations: report
                .signature
                .relations
                .iter()
                .map(|r| JsonRelation {
                    name: r.name.clone(),
                    arity: r.arity.iter().map(|s| s.name.clone()).collect(),
                })
                .collect(),
        };
        let decomposition = report
            .mutation
            .decomposition
            .iter()
            .enumerate()
            .map(|(i, f)| JsonDecompositionItem {
                index: i,
                formula: format_formula(f),
            })
            .collect();
        let tightness = JsonTightness {
            score: report.tightness.score,
            confidence_interval: [
                report.tightness.confidence_interval.0,
                report.tightness.confidence_interval.1,
            ],
            exhaustive: report.tightness.exhaustive,
            neighborhood_size: report.tightness.neighborhood_size,
            killed: report.tightness.killed_count,
            alive: report.tightness.alive_count,
        };
        let alive_mutants: Vec<JsonAliveMutant> = report
            .tightness
            .mutant_statuses
            .iter()
            .filter(|s| !s.killed)
            .filter_map(|s| {
                report
                    .mutation
                    .mutants
                    .get(s.mutant_index)
                    .map(|m| (s.mutant_index, m))
            })
            .map(|(idx, m)| JsonAliveMutant {
                index: idx,
                class: format!("{:?}", m.class).to_lowercase(),
                perturbed_component: m.perturbed_component,
                distance: m.distance,
                formula_summary: m
                    .replacement_predicate
                    .as_ref()
                    .or(m.original_predicate.as_ref())
                    .map(format_formula)
                    .unwrap_or_default(),
                // Global (FOL) JSON path doesn't run witness extraction; the
                // sliced path attaches witnesses to the per-slice statuses.
                witness: None,
            })
            .collect();
        let evaluator = if report.cegis { "cegis" } else { "exhaustive" };
        Self {
            version: "0.1.0",
            spec_file: report.spec_path.clone(),
            parameters,
            signature,
            decomposition,
            tightness,
            alive_mutants,
            timing: report.timing,
            evaluator,
            smt: report.smt,
            smt_fallback_count: report.fallback_count,
            lean_translation: report.lean_translation.clone(),
        }
    }
}

// ============================================================================
// Sliced (per-theorem) reporting — Phase E
// ============================================================================

/// Top-level report for a [`LeanAnalysisOutcome::Sliced`] run.  Owns its
/// data so the caller can drop pipeline artefacts before formatting.
pub struct SlicedReport<'a> {
    /// Path to the input `.lean` spec.
    pub spec_path: String,
    /// Model bound passed on the command line.
    pub model_bound: usize,
    /// Quantifier rank passed on the command line.
    pub quantifier_rank: usize,
    /// Neighborhood radius.
    pub epsilon: f64,
    /// Random seed.
    pub seed: u64,
    /// True iff CEGIS was the evaluator.
    pub cegis: bool,
    /// True iff Z3 was used for entailment checking.
    pub smt: bool,
    /// Per-theorem outcomes, in translation order.
    pub slices: &'a [SliceOutcome],
    /// Translation summary shared across slices.
    pub translation_summary: &'a TranslationSummary,
    /// Aggregate τ across analyzed slices.
    pub aggregate: &'a AggregateReport,
}

/// Human-readable per-theorem report.
pub fn render_sliced_text(report: &SlicedReport<'_>) -> String {
    let mut out = String::new();
    out.push_str("specmut v0.1.0 — Lean Specification Tightness Analysis (per-theorem)\n\n");
    out.push_str(&format!("Spec file:        {}\n", report.spec_path));
    out.push_str(&format!("Model bound:      {}\n", report.model_bound));
    out.push_str(&format!("Quantifier rank:  {}\n", report.quantifier_rank));
    out.push_str(&format!("Epsilon:          {}\n", report.epsilon));
    out.push_str(&format!("Seed:             {}\n", report.seed));
    if report.cegis {
        out.push_str("Evaluator:        CEGIS\n");
    } else {
        out.push_str("Evaluator:        Exhaustive\n");
    }
    if report.smt {
        out.push_str("Entailment:       Z3 SMT (hybrid)\n");
    } else {
        out.push_str("Entailment:       Model enumeration\n");
    }
    out.push('\n');
    out.push_str(&format!(
        "Lean analysis: {} theorems, {} predicates translated\n",
        report.translation_summary.translated_theorems.len(),
        report.translation_summary.translated_predicates.len(),
    ));
    if report.translation_summary.sort_filter.original_sorts
        != report.translation_summary.sort_filter.filtered_sorts
    {
        out.push_str(&format!(
            "Sort filter: {} → {} sorts\n",
            report.translation_summary.sort_filter.original_sorts,
            report.translation_summary.sort_filter.filtered_sorts,
        ));
    }
    out.push('\n');

    for slice in report.slices {
        out.push_str(&format!("{:═^60}\n", ""));
        out.push_str(&format!("  Theorem: {}\n", slice.theorem_name));
        out.push_str(&format!("{:═^60}\n", ""));
        out.push_str(&format!(
            "  Sorts:     {} ({})\n",
            slice.included_sorts.join(", "),
            slice.included_sorts.len()
        ));
        if !slice.included_relations.is_empty() {
            out.push_str(&format!(
                "  Relations: {} ({})\n",
                slice.included_relations.join(", "),
                slice.included_relations.len()
            ));
        }
        if !slice.included_functions.is_empty() {
            out.push_str(&format!(
                "  Functions: {} ({})\n",
                slice.included_functions.join(", "),
                slice.included_functions.len()
            ));
        }
        if !slice.excluded_sorts.is_empty() {
            out.push_str(&format!(
                "  Excluded:  {}\n",
                slice.excluded_sorts.join(", ")
            ));
        }
        match &slice.status {
            SliceStatus::Analyzed {
                outcome,
                auto_implementations,
                metrics,
                taxonomy,
                contribution,
                ..
            } => {
                out.push_str("\n  Slice reduction:\n");
                out.push_str(&format!(
                    "    Sorts:     {} global → {} retained ({:.0}% removed)\n",
                    metrics.original_sort_count,
                    metrics.reduced_sort_count,
                    pct_removed(metrics.original_sort_count, metrics.reduced_sort_count)
                ));
                out.push_str(&format!(
                    "    Functions: {} → {}\n",
                    metrics.original_function_count, metrics.reduced_function_count
                ));
                out.push_str(&format!(
                    "    Relations: {} → {}\n",
                    metrics.original_relation_count, metrics.reduced_relation_count
                ));
                out.push_str(&format!(
                    "    Model space: 2^{:.0} → 2^{:.0} ({} models in {} ms)\n",
                    metrics.original_model_space_log2,
                    metrics.reduced_model_space_log2,
                    outcome.models_enumerated,
                    metrics.enumeration_ms,
                ));
                out.push_str(&format!("  Auto-impls: {}\n", auto_implementations));
                out.push('\n');
                out.push_str(&format!(
                    "  Tightness: τ = {:.3} ({}/{} killed, {} alive)\n",
                    outcome.tightness.score,
                    outcome.tightness.killed_count,
                    outcome.tightness.neighborhood_size,
                    outcome.tightness.alive_count,
                ));

                out.push_str("\n  Mutation breakdown:\n");
                push_taxonomy_lines(&mut out, taxonomy, "    ");

                // Alive mutants with their witnesses.
                let alive_statuses: Vec<_> = outcome
                    .tightness
                    .mutant_statuses
                    .iter()
                    .filter(|s| !s.killed)
                    .collect();
                if !alive_statuses.is_empty() {
                    out.push_str("\n  Surviving mutants:\n");
                    for status in alive_statuses.iter().take(5) {
                        if let Some(m) = outcome.mutation.mutants.get(status.mutant_index) {
                            out.push_str(&format!(
                                "    #{} [{:?}, d={:.3}] perturbed=[{}]\n",
                                status.mutant_index,
                                m.class,
                                m.distance,
                                m.perturbed_component,
                            ));
                            if let Some(w) = status.witness.as_ref() {
                                out.push_str(&format!(
                                    "      Witness: {} ({})\n",
                                    w.model_description,
                                    witness_direction_label(w.direction)
                                ));
                                out.push_str(&format!(
                                    "      Interpretation: {}\n",
                                    w.interpretation
                                ));
                            }
                        }
                    }
                    if alive_statuses.len() > 5 {
                        out.push_str(&format!(
                            "    ... and {} more\n",
                            alive_statuses.len() - 5
                        ));
                    }
                }

                if let Some(c) = contribution {
                    out.push_str("\n  Theorem contribution:\n");
                    out.push_str(&format!(
                        "    {} kills {} mutants ({} unique, {} shared)\n",
                        c.theorem_name, c.total_kills, c.unique_kills, c.shared_kills
                    ));
                    out.push_str(&format!(
                        "    Strength: {} (unique kill rate {:.0}%)\n",
                        strength_label(c.contribution_strength),
                        c.unique_kill_rate * 100.0
                    ));
                }
            }
            SliceStatus::Skipped { reason } => {
                out.push_str("  [SKIPPED]\n");
                out.push_str(&format!("  Reason: {reason}\n"));
            }
        }
        out.push('\n');
    }

    out.push_str(&format!("{:═^60}\n", ""));
    out.push_str("  Summary\n");
    out.push_str(&format!("{:═^60}\n", ""));
    let agg = report.aggregate;
    out.push_str(&format!(
        "  Analyzed: {}/{} theorems\n",
        agg.analyzed_count, report.slices.len()
    ));
    if agg.analyzed_count > 0 {
        out.push_str(&format!("  Mean τ: {:.3}", agg.mean_tightness));
        if agg.tightness_variance > 0.0 {
            out.push_str(&format!("  (σ² = {:.3})", agg.tightness_variance));
        }
        out.push('\n');
        out.push_str(&format!(
            "  Range:  [{:.3}, {:.3}]\n",
            agg.min_tightness, agg.max_tightness
        ));
        out.push_str(&format!(
            "  Total mutants: {} ({} killed, {:.0}% kill rate)\n",
            agg.total_mutants_generated,
            agg.total_mutants_killed,
            agg.total_kill_rate * 100.0
        ));
        out.push_str(&format!(
            "  Avg model-space reduction: {:.1}%\n",
            agg.average_model_space_reduction_pct
        ));
    }
    if agg.skipped_count > 0 {
        out.push_str(&format!(
            "  Skipped: {} (model space exceeded)\n",
            agg.skipped_count
        ));
    }

    if !agg.contributions.is_empty() {
        out.push_str("\n  Theorem contribution ranking:\n");
        for c in &agg.contributions {
            out.push_str(&format!(
                "    {:30}  τ={:.3}  unique_kills={}  strength={}\n",
                c.theorem_name,
                c.tightness,
                c.unique_kills,
                strength_label(c.contribution_strength),
            ));
        }
    }

    if agg.total_mutants_generated > 0 {
        out.push_str("\n  Mutation taxonomy:\n");
        push_taxonomy_lines(&mut out, &agg.taxonomy, "    ");
        let line = agg.taxonomy.diagnostic();
        if !line.is_empty() {
            out.push_str(&format!("    → {line}\n"));
        }
    }

    if !agg.weak_theorem_candidates.is_empty() {
        out.push_str(&format!(
            "\n  Weak theorem candidates (τ < 0.1): {}\n",
            agg.weak_theorem_candidates.join(", ")
        ));
    }

    if !agg.diagnostic_summary.is_empty() {
        out.push_str(&format!("\n  Diagnostic: {}\n", agg.diagnostic_summary));
    }

    out
}

fn pct_removed(original: usize, reduced: usize) -> f64 {
    if original == 0 {
        0.0
    } else {
        100.0 * (1.0 - reduced as f64 / original as f64)
    }
}

fn push_taxonomy_lines(out: &mut String, tax: &MutationTaxonomy, prefix: &str) {
    out.push_str(&format!(
        "{prefix}Weakening:     {}/{} killed ({:.0}%)\n",
        tax.weakening_killed,
        tax.weakening_total,
        tax.weakening_kill_rate * 100.0
    ));
    out.push_str(&format!(
        "{prefix}Strengthening: {}/{} killed ({:.0}%)\n",
        tax.strengthening_killed,
        tax.strengthening_total,
        tax.strengthening_kill_rate * 100.0
    ));
    out.push_str(&format!(
        "{prefix}Replacement:   {}/{} killed ({:.0}%)\n",
        tax.replacement_killed,
        tax.replacement_total,
        tax.replacement_kill_rate * 100.0
    ));
}

fn strength_label(s: ContributionStrength) -> &'static str {
    match s {
        ContributionStrength::High => "HIGH",
        ContributionStrength::Medium => "MEDIUM",
        ContributionStrength::Low => "LOW",
        ContributionStrength::None => "NONE",
    }
}

fn witness_direction_label(d: WitnessDirection) -> &'static str {
    match d {
        WitnessDirection::MutantAdmits => "mutant admits, spec rejects",
        WitnessDirection::MutantRejects => "spec admits, mutant rejects",
    }
}

/// JSON shape for the per-theorem report.  Inhabits the same JSON namespace
/// as [`render_json`] but with `analysis_mode: "per_theorem"` and a
/// `theorem_slices` array in place of the single-tightness section.
pub fn render_sliced_json(report: &SlicedReport<'_>) -> String {
    let value = SlicedJson::from_report(report);
    serde_json::to_string_pretty(&value).unwrap_or_else(|_| "{}".to_string())
}

#[derive(Serialize)]
struct SlicedJson {
    version: &'static str,
    spec_file: String,
    analysis_mode: &'static str,
    parameters: JsonParameters,
    evaluator: &'static str,
    smt: bool,
    lean_translation: LeanTranslationReport,
    theorem_slices: Vec<JsonSlice>,
    summary: JsonSummary,
}

#[derive(Serialize)]
struct JsonSlice {
    theorem_name: String,
    status: &'static str,
    signature: JsonSignature,
    excluded_sorts: Vec<String>,
    dependency_closure: DependencyClosure,
    #[serde(skip_serializing_if = "Option::is_none")]
    model_count: Option<usize>,
    #[serde(skip_serializing_if = "Option::is_none")]
    auto_implementations: Option<usize>,
    #[serde(skip_serializing_if = "Option::is_none")]
    tightness: Option<JsonTightness>,
    #[serde(skip_serializing_if = "Option::is_none")]
    alive_mutants: Option<Vec<JsonAliveMutant>>,
    #[serde(skip_serializing_if = "Option::is_none")]
    skip_reason: Option<String>,
    // Phase F additions:
    #[serde(skip_serializing_if = "Option::is_none")]
    metrics: Option<SliceMetrics>,
    #[serde(skip_serializing_if = "Option::is_none")]
    taxonomy: Option<MutationTaxonomy>,
    #[serde(skip_serializing_if = "Option::is_none")]
    neighborhood_table: Option<Vec<NeighborhoodEntry>>,
    #[serde(skip_serializing_if = "Option::is_none")]
    contribution: Option<TheoremContribution>,
}

#[derive(Serialize)]
struct JsonSummary {
    analyzed: usize,
    skipped: usize,
    mean_tightness: f64,
    min_tightness: f64,
    max_tightness: f64,
    // Phase F aggregate diagnostics:
    tightness_variance: f64,
    average_model_space_reduction_pct: f64,
    total_mutants_generated: usize,
    total_mutants_killed: usize,
    total_kill_rate: f64,
    taxonomy: MutationTaxonomy,
    contributions: Vec<TheoremContribution>,
    weak_theorem_candidates: Vec<String>,
    diagnostic_summary: String,
}

impl SlicedJson {
    fn from_report(report: &SlicedReport<'_>) -> Self {
        let parameters = JsonParameters {
            model_bound: report.model_bound,
            quantifier_rank: report.quantifier_rank,
            epsilon: report.epsilon,
            seed: report.seed,
            // Per-theorem mode reports model_count per slice; surface 0
            // at the top level so `parameters` stays uniform with the
            // global JSON shape.
            models_enumerated: 0,
        };
        let lean_translation = translation_summary_to_report(report.translation_summary);
        let evaluator = if report.cegis { "cegis" } else { "exhaustive" };

        let theorem_slices: Vec<JsonSlice> = report
            .slices
            .iter()
            .map(|slice| {
                let signature_summary = JsonSignature {
                    sorts: slice.included_sorts.clone(),
                    functions: slice
                        .included_functions
                        .iter()
                        .map(|name| JsonFunction {
                            name: name.clone(),
                            domain: Vec::new(),
                            codomain: String::new(),
                        })
                        .collect(),
                    relations: slice
                        .included_relations
                        .iter()
                        .map(|name| JsonRelation {
                            name: name.clone(),
                            arity: Vec::new(),
                        })
                        .collect(),
                };
                match &slice.status {
                    SliceStatus::Analyzed {
                        outcome,
                        auto_implementations,
                        metrics,
                        taxonomy,
                        neighborhood,
                        contribution,
                    } => {
                        let tightness = JsonTightness {
                            score: outcome.tightness.score,
                            confidence_interval: [
                                outcome.tightness.confidence_interval.0,
                                outcome.tightness.confidence_interval.1,
                            ],
                            exhaustive: outcome.tightness.exhaustive,
                            neighborhood_size: outcome.tightness.neighborhood_size,
                            killed: outcome.tightness.killed_count,
                            alive: outcome.tightness.alive_count,
                        };
                        let alive: Vec<JsonAliveMutant> = outcome
                            .tightness
                            .mutant_statuses
                            .iter()
                            .filter(|s| !s.killed)
                            .filter_map(|s| {
                                outcome
                                    .mutation
                                    .mutants
                                    .get(s.mutant_index)
                                    .map(|m| (s.mutant_index, m, s))
                            })
                            .map(|(idx, m, status)| JsonAliveMutant {
                                index: idx,
                                class: format!("{:?}", m.class).to_lowercase(),
                                perturbed_component: m.perturbed_component,
                                distance: m.distance,
                                formula_summary: m
                                    .replacement_predicate
                                    .as_ref()
                                    .or(m.original_predicate.as_ref())
                                    .map(format_formula)
                                    .unwrap_or_default(),
                                witness: status.witness.clone(),
                            })
                            .collect();
                        JsonSlice {
                            theorem_name: slice.theorem_name.clone(),
                            status: "analyzed",
                            signature: signature_summary,
                            excluded_sorts: slice.excluded_sorts.clone(),
                            dependency_closure: slice.dependency_closure.clone(),
                            model_count: Some(outcome.models_enumerated),
                            auto_implementations: Some(*auto_implementations),
                            tightness: Some(tightness),
                            alive_mutants: Some(alive),
                            skip_reason: None,
                            metrics: Some(metrics.clone()),
                            taxonomy: Some(taxonomy.clone()),
                            neighborhood_table: Some(neighborhood.clone()),
                            contribution: contribution.clone(),
                        }
                    }
                    SliceStatus::Skipped { reason } => JsonSlice {
                        theorem_name: slice.theorem_name.clone(),
                        status: "skipped",
                        signature: signature_summary,
                        excluded_sorts: slice.excluded_sorts.clone(),
                        dependency_closure: slice.dependency_closure.clone(),
                        model_count: None,
                        auto_implementations: None,
                        tightness: None,
                        alive_mutants: None,
                        skip_reason: Some(reason.clone()),
                        metrics: None,
                        taxonomy: None,
                        neighborhood_table: None,
                        contribution: None,
                    },
                }
            })
            .collect();

        let summary = JsonSummary {
            analyzed: report.aggregate.analyzed_count,
            skipped: report.aggregate.skipped_count,
            mean_tightness: report.aggregate.mean_tightness,
            min_tightness: report.aggregate.min_tightness,
            max_tightness: report.aggregate.max_tightness,
            tightness_variance: report.aggregate.tightness_variance,
            average_model_space_reduction_pct: report
                .aggregate
                .average_model_space_reduction_pct,
            total_mutants_generated: report.aggregate.total_mutants_generated,
            total_mutants_killed: report.aggregate.total_mutants_killed,
            total_kill_rate: report.aggregate.total_kill_rate,
            taxonomy: report.aggregate.taxonomy.clone(),
            contributions: report.aggregate.contributions.clone(),
            weak_theorem_candidates: report.aggregate.weak_theorem_candidates.clone(),
            diagnostic_summary: report.aggregate.diagnostic_summary.clone(),
        };

        Self {
            version: "0.1.0",
            spec_file: report.spec_path.clone(),
            analysis_mode: "per_theorem",
            parameters,
            evaluator,
            smt: report.smt,
            lean_translation,
            theorem_slices,
            summary,
        }
    }
}

fn translation_summary_to_report(s: &TranslationSummary) -> LeanTranslationReport {
    LeanTranslationReport {
        translated_theorems: s.translated_theorems.clone(),
        skipped_theorems: s
            .skipped_theorems
            .iter()
            .map(|(name, reason)| SkippedItem {
                name: name.clone(),
                reason: reason.clone(),
            })
            .collect(),
        translated_predicates: s.translated_predicates.clone(),
        skipped_predicates: s
            .skipped_predicates
            .iter()
            .map(|(name, reason)| SkippedItem {
                name: name.clone(),
                reason: reason.clone(),
            })
            .collect(),
        warnings: s.warnings.clone(),
        sort_filter: SortFilterJson {
            original_sorts: s.sort_filter.original_sorts,
            filtered_sorts: s.sort_filter.filtered_sorts,
            removed: s.sort_filter.removed.clone(),
        },
        auto_implementations: s.auto_implementations,
    }
}
