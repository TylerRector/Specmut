//! Lean → tightness analysis orchestration.
//!
//! Wires `specmut-lean`'s runner + translator into the existing pipeline:
//! 1. Run the regex extractor for the fallback summary.
//! 2. Invoke the Lean exporter via [`LeanRunner`] to get JSON IR.
//! 3. Translate the IR to `(Signature, Vec<Formula>)`.
//! 4. Slice the translation per theorem (Phase E) and run the downstream
//!    pipeline once per slice.  Fall back to a single global run when the
//!    translation has no theorems, or when the user supplied explicit
//!    implementation models that can't be projected to slice signatures.
//!
//! Returns a [`LeanAnalysisOutcome`] that the CLI top level renders.  Errors
//! at any step degrade to "show the extraction summary instead" — only when
//! the user explicitly asks for full analysis AND every theorem/predicate
//! fails to translate do we surface a hard error.
//!
//! This module is only compiled into `specmut-cli` and only used from the
//! `.lean + --lean-full` branch of `main.rs`.

use std::path::{Path, PathBuf};
use std::time::Instant;

use num_bigint::BigUint;
use specmut_core::formula::Formula;
use specmut_core::lattice::SpecElement;
use specmut_core::metric::JaccardMetric;
use specmut_core::model::FiniteModel;
use specmut_core::mutation::MutationResult;
use specmut_core::signature::Signature;
use specmut_core::tightness::TightnessResult;
use specmut_lean::analysis::{
    build_neighborhood_table, MutationTaxonomy, NeighborhoodEntry, SliceMetrics,
    TheoremContribution,
};
use specmut_lean::runner::{LeanPipelineError, LeanRunner};
use specmut_lean::slicer::{slice_by_theorem, TheoremSlice};
use specmut_lean::translator::{
    AxiomOrigin, LeanTranslator, SortFilterReport, TranslationError, TranslationResult,
};
use specmut_lean::ContributionStrength;
use specmut_parser::lean_parser::{LeanExtraction, LeanParser};

use crate::pipeline::{self, PipelineError, PipelineOutcome, PipelineParams};

/// Default cap on the number of auto-selected implementation models.
pub const DEFAULT_MAX_AUTO_IMPLS: usize = 5;

/// Hard ceiling on per-slice model space.  Mirrors the constant in
/// `pipeline.rs` so the slicer can pre-screen before paying the
/// enumeration cost and surface a clean "skipped" entry rather than
/// `MODEL_BOUND_EXCEEDED`.
const MODEL_SPACE_LIMIT: u64 = 1 << 22;

/// Outcome of running the Lean analysis pipeline.
//
// Sliced carries a Vec of slice outcomes, each of which embeds the
// AggregateReport, taxonomy, contributions, etc.  Global is a single
// boxed PipelineOutcome.  The asymmetry is intentional and the sliced
// path dominates real use, so we tolerate the size delta.
#[allow(clippy::large_enum_variant)]
pub enum LeanAnalysisOutcome {
    /// Per-theorem sliced analysis (Phase E).  Default path when the
    /// translation has at least one theorem and the user did not supply
    /// explicit implementation models.
    Sliced {
        /// One entry per translated theorem, in translation order.
        slices: Vec<SliceOutcome>,
        /// Translation summary shared across all slices.
        translation_summary: TranslationSummary,
        /// Aggregate τ across analyzed slices.
        aggregate: AggregateReport,
    },
    /// Phase D global analysis: a single pipeline run over the union
    /// signature.  Used when the translation has no theorems
    /// (predicates-only file) or when the user supplied `-i` impls.
    Global {
        /// Outcome from [`pipeline::run_with_models_and_impls`].
        outcome: Box<PipelineOutcome>,
        /// Translation summary.
        translation_summary: TranslationSummary,
    },
    /// The Lean exporter or translator produced nothing usable, but the regex
    /// extractor recovered a summary the CLI can still surface.  Soft failure
    /// path — the CLI prints the extraction and exits 0.
    ExtractionOnly {
        /// What the regex extractor saw.
        extraction: LeanExtraction,
        /// Diagnostic explaining why full analysis didn't run.
        reason: String,
    },
}

/// One theorem's analysis result inside a [`LeanAnalysisOutcome::Sliced`].
pub struct SliceOutcome {
    /// Source theorem name.
    pub theorem_name: String,
    /// Status: analyzed (pipeline ran) or skipped (model space too large
    /// at the requested bound).
    pub status: SliceStatus,
    /// Sort names in the reduced signature.
    pub included_sorts: Vec<String>,
    /// Relation names in the reduced signature.
    pub included_relations: Vec<String>,
    /// Function names in the reduced signature.
    pub included_functions: Vec<String>,
    /// Sort names dropped from the global signature for this slice.
    pub excluded_sorts: Vec<String>,
    /// Phase F (§2.6): the slice's "dependency closure" — what symbols
    /// and axioms it retained.  Mirrors the per-slice fields above plus
    /// the formatted axiom origin names.
    pub dependency_closure: DependencyClosure,
}

/// Phase F: a slice's resolved dependency closure, ready for JSON
/// emission.
#[derive(Debug, Clone, serde::Serialize)]
pub struct DependencyClosure {
    /// Sort names in the slice signature.
    pub sorts: Vec<String>,
    /// Relation names in the slice signature.
    pub relations: Vec<String>,
    /// Function names in the slice signature.
    pub functions: Vec<String>,
    /// Number of axioms in the slice (predicate eqs + theorem).
    pub axiom_count: usize,
    /// Origin names, e.g. `"Sorted.eq_1"`, `"find_insert"`.  Same length
    /// and order as the slice's `all_axioms`.
    pub axiom_origins: Vec<String>,
}

/// Status field of [`SliceOutcome`].
//
// `Analyzed` is intentionally large (it carries the PipelineOutcome plus
// the Phase F metrics/taxonomy/neighborhood/contribution).  Boxing each
// individual field would obscure the data shape; `Skipped` only happens
// rarely so the size asymmetry is fine.
#[allow(clippy::large_enum_variant)]
pub enum SliceStatus {
    /// Pipeline ran successfully for this slice.
    Analyzed {
        /// Pipeline outcome (boxed because `PipelineOutcome` is large).
        outcome: Box<PipelineOutcome>,
        /// Number of impls auto-selected from the satisfying model pool.
        auto_implementations: usize,
        /// Phase F (§2.1): per-slice signature / model-space / mutation
        /// metrics.
        metrics: SliceMetrics,
        /// Phase F (§2.4): per-class mutation kill rates.
        taxonomy: MutationTaxonomy,
        /// Phase F (§2.5): full neighborhood table for this slice.
        neighborhood: Vec<NeighborhoodEntry>,
        /// Phase F (§2.2): theorem contribution analysis (`None` when
        /// the baseline tightness run failed or was skipped).
        contribution: Option<TheoremContribution>,
    },
    /// Slice was skipped — most commonly because its model space at the
    /// requested bound exceeded the [`MODEL_SPACE_LIMIT`] ceiling.
    Skipped {
        /// Why we skipped — surfaced in the report.
        reason: String,
    },
}

/// Aggregate tightness across the analyzed slices in a [`LeanAnalysisOutcome::Sliced`].
#[derive(Debug, Clone)]
pub struct AggregateReport {
    /// Mean of `tightness.score` over analyzed slices (0.0 when none).
    pub mean_tightness: f64,
    /// Minimum τ across analyzed slices (0.0 when none).
    pub min_tightness: f64,
    /// Maximum τ across analyzed slices (0.0 when none).
    pub max_tightness: f64,
    /// How many slices were analyzed.
    pub analyzed_count: usize,
    /// How many slices were skipped.
    pub skipped_count: usize,

    // Phase F (§2.7): semantic diagnostics.
    /// Variance of `tightness.score` across analyzed slices (0.0 when ≤ 1
    /// analyzed slice).  Population variance.
    pub tightness_variance: f64,
    /// Mean of `metrics.reduction_percentage` over analyzed slices.
    pub average_model_space_reduction_pct: f64,
    /// Sum of `neighborhood_size` across analyzed slices.
    pub total_mutants_generated: usize,
    /// Sum of `killed_count` across analyzed slices.
    pub total_mutants_killed: usize,
    /// `total_mutants_killed / total_mutants_generated` (0.0 when none).
    pub total_kill_rate: f64,
    /// Per-class kill rates aggregated across analyzed slices.
    pub taxonomy: MutationTaxonomy,
    /// Per-theorem contribution rankings, present only for slices where
    /// the baseline tightness evaluation was computed.
    pub contributions: Vec<TheoremContribution>,
    /// Theorem names with `tightness < 0.1`.
    pub weak_theorem_candidates: Vec<String>,
    /// Auto-generated paragraph that combines coverage, variance, weak
    /// candidates, taxonomy, and reduction.  Empty when there's nothing
    /// meaningful to say (e.g. zero analyzed slices).
    pub diagnostic_summary: String,
}

/// Summary fields rendered alongside the tightness report.
#[derive(Debug, Clone)]
pub struct TranslationSummary {
    /// Names of theorems that translated successfully.
    pub translated_theorems: Vec<String>,
    /// Names of predicates that translated successfully (≥1 axiom each).
    pub translated_predicates: Vec<String>,
    /// `(name, reason)` for theorems the translator skipped.
    pub skipped_theorems: Vec<(String, String)>,
    /// `(name, reason)` for predicates the translator skipped.
    pub skipped_predicates: Vec<(String, String)>,
    /// Non-fatal warnings (inherited from the IR + emitted during translation).
    pub warnings: Vec<String>,
    /// Metadata from the sort-filter pass.
    pub sort_filter: SortFilterReport,
    /// Number of implementation models auto-selected from the satisfying set.
    /// `0` when the user passed explicit `-i` files or `--no-auto-impl`.
    /// In sliced mode this is the *total* across all slices.
    pub auto_implementations: usize,
}

impl From<&TranslationResult> for TranslationSummary {
    fn from(r: &TranslationResult) -> Self {
        Self {
            translated_theorems: r.translated_theorems.clone(),
            translated_predicates: r.translated_predicates.clone(),
            skipped_theorems: r.skipped_theorems.clone(),
            skipped_predicates: r.skipped_predicates.clone(),
            warnings: r.warnings.clone(),
            sort_filter: r.sort_filter.clone(),
            auto_implementations: 0,
        }
    }
}

/// Errors surfaced to the CLI when the Lean pipeline fails hard.
#[derive(Debug, thiserror::Error)]
pub enum LeanAnalysisError {
    /// Could not read the spec file.
    #[error("could not read '{path}': {source}")]
    Io {
        /// File path that failed.
        path: String,
        /// Underlying I/O error.
        #[source]
        source: std::io::Error,
    },

    /// The regex extractor itself failed (very rare — only on malformed Lean).
    #[error("regex extraction failed: {0}")]
    Extraction(String),

    /// Translation produced zero axioms — the only fatal Lean-pipeline failure.
    #[error("Lean translation produced no axioms: {0}")]
    NothingTranslatable(String),

    /// Downstream pipeline rejected the translated FOL.
    #[error("pipeline error: {0}")]
    Pipeline(#[from] PipelineError),
}

/// Top-level entry point.
///
/// Runs the regex extractor first (always available, used as a fallback).
/// Then attempts the full Lean export → translate → slice/global path.
/// Slicing (Phase E) runs when the translation has theorems AND the user
/// did not pass `-i` files; otherwise the pipeline runs once over the
/// global signature (Phase D semantics).
///
/// Soft-fails to `ExtractionOnly` if the lean binary is missing or the
/// exporter errors; hard-fails only when every theorem and predicate skipped.
pub fn run_lean_analysis(
    target_path: &Path,
    lean_path: &Path,
    lean_timeout: u64,
    params: &PipelineParams,
    disable_auto_impl: bool,
) -> Result<LeanAnalysisOutcome, LeanAnalysisError> {
    let source = std::fs::read_to_string(target_path).map_err(|source| LeanAnalysisError::Io {
        path: target_path.display().to_string(),
        source,
    })?;
    let extraction = LeanParser
        .extract(&source)
        .map_err(|e| LeanAnalysisError::Extraction(e.to_string()))?;

    let runner = LeanRunner::new(lean_path.to_path_buf(), lean_timeout);
    if !runner.lean_available() {
        return Ok(LeanAnalysisOutcome::ExtractionOnly {
            extraction,
            reason: format!(
                "lean binary not found at '{}'; install via elan or pass --lean-path",
                lean_path.display()
            ),
        });
    }

    // Step 2 & 3: export → translate.  Any error here degrades to
    // ExtractionOnly *except* the hard case of NothingTranslatable.
    let translation = match runner
        .export(target_path)
        .map_err(LeanPhase::Runner)
        .and_then(|ir| LeanTranslator::translate(&ir).map_err(LeanPhase::Translator))
    {
        Ok(t) => t,
        Err(LeanPhase::Runner(e)) => {
            return Ok(LeanAnalysisOutcome::ExtractionOnly {
                extraction,
                reason: format!("lean exporter failed: {e}"),
            });
        }
        Err(LeanPhase::Translator(TranslationError::NothingTranslatable { reason })) => {
            return Err(LeanAnalysisError::NothingTranslatable(reason));
        }
        Err(LeanPhase::Translator(other)) => {
            return Ok(LeanAnalysisOutcome::ExtractionOnly {
                extraction,
                reason: format!("Lean translation failed: {other}"),
            });
        }
    };

    let mut translation_summary = TranslationSummary::from(&translation);

    // User-supplied impls and predicates-only translations both bypass
    // slicing: in the first case the impl models are parsed against the
    // global signature and can't be projected to slice signatures
    // safely; in the second there are no theorems to slice by.
    if !params.impls.is_empty() || translation.translated_theorems.is_empty() {
        let outcome =
            run_global_analysis(&translation, params, disable_auto_impl, &mut translation_summary)?;
        return Ok(LeanAnalysisOutcome::Global {
            outcome: Box::new(outcome),
            translation_summary,
        });
    }

    // Phase E: per-theorem slicing.
    let slices = slice_by_theorem(&translation);
    if slices.is_empty() {
        // Defensive: translated_theorems was non-empty but the slicer
        // produced nothing (e.g. axioms dedup-collapsed).  Treat the
        // same as predicates-only and fall back.
        let outcome =
            run_global_analysis(&translation, params, disable_auto_impl, &mut translation_summary)?;
        return Ok(LeanAnalysisOutcome::Global {
            outcome: Box::new(outcome),
            translation_summary,
        });
    }

    let global_axiom_count = translation.axioms.len();
    let mut slice_outcomes = Vec::with_capacity(slices.len());
    let mut total_auto_impls: usize = 0;

    for slice in &slices {
        let outcome = analyze_slice(
            slice,
            &translation,
            global_axiom_count,
            params,
            disable_auto_impl,
        )?;
        if let SliceStatus::Analyzed {
            auto_implementations, ..
        } = &outcome.status
        {
            total_auto_impls += *auto_implementations;
        }
        slice_outcomes.push(outcome);
    }

    translation_summary.auto_implementations = total_auto_impls;
    let aggregate = aggregate_slice_outcomes(&slice_outcomes);

    Ok(LeanAnalysisOutcome::Sliced {
        slices: slice_outcomes,
        translation_summary,
        aggregate,
    })
}

/// Phase D path: enumerate over the union signature once.  Shared between
/// the predicates-only fallback and the explicit-impl fallback.
fn run_global_analysis(
    translation: &TranslationResult,
    params: &PipelineParams,
    disable_auto_impl: bool,
    translation_summary: &mut TranslationSummary,
) -> Result<PipelineOutcome, LeanAnalysisError> {
    let overall_start = Instant::now();
    let parse_start = Instant::now();
    let signature: Signature = translation.signature.clone();
    let axioms: Vec<Formula> = translation.axioms.clone();
    let parse_ms = parse_start.elapsed().as_millis();

    let enum_start = Instant::now();
    let models = pipeline::enumerate_models_for_signature(&signature, params.model_bound)?;
    let enumeration_ms = enum_start.elapsed().as_millis();

    let mut implementations: Vec<FiniteModel> = Vec::new();
    for path in &params.impls {
        let text = std::fs::read_to_string(path).map_err(|e| {
            LeanAnalysisError::Pipeline(pipeline::PipelineError::Io {
                path: path.display().to_string(),
                source: e,
            })
        })?;
        implementations.push(
            crate::model_file::parse_model_file(&text, &signature).map_err(|e| {
                LeanAnalysisError::Pipeline(pipeline::PipelineError::ModelParse(e))
            })?,
        );
    }

    if implementations.is_empty() && !disable_auto_impl {
        let auto = auto_select_implementations(&models, &axioms, DEFAULT_MAX_AUTO_IMPLS);
        translation_summary.auto_implementations = auto.len();
        if auto.is_empty() {
            translation_summary.warnings.push(format!(
                "no model at -n {} satisfies the spec; τ will be 0.0 — try increasing -n",
                params.model_bound
            ));
        }
        implementations = auto;
    }

    let outcome = pipeline::run_with_models_and_impls(
        params,
        signature,
        axioms,
        models,
        implementations,
        parse_ms,
        enumeration_ms,
        overall_start,
    )?;
    Ok(outcome)
}

/// Build the per-slice `DependencyClosure` from translator artefacts.
fn build_dependency_closure(slice: &TheoremSlice, translation: &TranslationResult) -> DependencyClosure {
    // Map slice axioms back to global indices by formula equality.  This
    // is O(slice_axioms * global_axioms) but both vectors are small.
    let mut origin_names: Vec<String> = Vec::with_capacity(slice.all_axioms.len());
    for axiom in &slice.all_axioms {
        if let Some(idx) = translation.axioms.iter().position(|g| g == axiom) {
            origin_names.push(format_origin(&translation.axiom_origins[idx]));
        } else {
            // Shouldn't happen because slice axioms are taken from the
            // translation, but stay defensive.
            origin_names.push("<unknown>".into());
        }
    }
    DependencyClosure {
        sorts: slice.included_sorts.clone(),
        relations: slice.included_relations.clone(),
        functions: slice.included_functions.clone(),
        axiom_count: slice.all_axioms.len(),
        axiom_origins: origin_names,
    }
}

fn format_origin(origin: &AxiomOrigin) -> String {
    match origin {
        AxiomOrigin::PredicateEquation {
            predicate_name,
            equation_index,
        } => format!("{}.eq_{}", predicate_name, equation_index + 1),
        AxiomOrigin::PredicateBody { predicate_name } => format!("{}.body", predicate_name),
        AxiomOrigin::TheoremStatement { theorem_name } => theorem_name.clone(),
    }
}

/// Compute `|Mod(S) △ Mod(M)|` for every neighborhood mutant using the
/// shared enumerated model pool.
fn compute_sym_diff_sizes(
    spec_axioms: &[Formula],
    mutation: &MutationResult,
    models: &[FiniteModel],
) -> Vec<usize> {
    let metric = JaccardMetric::new(models.to_vec());
    mutation
        .neighborhood_mutants
        .iter()
        .map(|&idx| {
            let m = &mutation.mutants[idx];
            let m_axioms: Vec<Formula> = m.spec.axioms.iter().cloned().collect();
            metric.distance(spec_axioms, &m_axioms).symmetric_difference_size
        })
        .collect()
}

/// Re-run tightness against the "supporting axioms only" baseline (slice
/// minus the theorem statement) so we can compute unique vs shared kills.
///
/// Returns `None` if the slice has no theorem-origin axiom we can identify
/// or if any predicate / pipeline call fails; the caller treats this as
/// "skip contribution analysis for this slice".
fn compute_baseline_tightness(
    slice: &TheoremSlice,
    translation: &TranslationResult,
    mutation: &MutationResult,
    models: &[FiniteModel],
    impls: &[FiniteModel],
) -> Option<TightnessResult> {
    // Drop axioms whose origin is the slice's theorem.
    let supporting: Vec<Formula> = slice
        .all_axioms
        .iter()
        .filter(|axiom| {
            let idx = match translation.axioms.iter().position(|g| g == *axiom) {
                Some(i) => i,
                None => return true,
            };
            !matches!(
                translation.axiom_origins[idx],
                AxiomOrigin::TheoremStatement { ref theorem_name } if theorem_name == &slice.theorem_name
            )
        })
        .cloned()
        .collect();
    if supporting.len() == slice.all_axioms.len() {
        // No theorem axiom found → contribution analysis is meaningless.
        return None;
    }
    let spec = SpecElement::from_axioms(supporting.iter().cloned());
    let evaluator = specmut_core::tightness::TightnessEvaluator::new(JaccardMetric::new(
        models.to_vec(),
    ));
    Some(evaluator.evaluate(&spec, mutation, impls))
}

/// Run the per-slice pipeline.  Returns a `SliceOutcome::Skipped` when
/// the model space at `params.model_bound` exceeds `MODEL_SPACE_LIMIT`
/// before paying the enumeration cost.
fn analyze_slice(
    slice: &TheoremSlice,
    translation: &TranslationResult,
    global_axiom_count: usize,
    params: &PipelineParams,
    disable_auto_impl: bool,
) -> Result<SliceOutcome, LeanAnalysisError> {
    let dependency_closure = build_dependency_closure(slice, translation);
    let space = slice.signature.model_space_size(params.model_bound);
    if space > BigUint::from(MODEL_SPACE_LIMIT) {
        return Ok(SliceOutcome {
            theorem_name: slice.theorem_name.clone(),
            status: SliceStatus::Skipped {
                reason: format!(
                    "model space at n={} exceeds limit {} ({} relations, {} functions, {} sorts)",
                    params.model_bound,
                    MODEL_SPACE_LIMIT,
                    slice.included_relations.len(),
                    slice.included_functions.len(),
                    slice.included_sorts.len(),
                ),
            },
            included_sorts: slice.included_sorts.clone(),
            included_relations: slice.included_relations.clone(),
            included_functions: slice.included_functions.clone(),
            excluded_sorts: slice.excluded_sorts.clone(),
            dependency_closure,
        });
    }

    let overall_start = Instant::now();
    let parse_start = Instant::now();
    let parse_ms = parse_start.elapsed().as_millis();
    let enum_start = Instant::now();
    let models = pipeline::enumerate_models_for_signature(&slice.signature, params.model_bound)?;
    let enumeration_ms = enum_start.elapsed().as_millis();

    let impls = if disable_auto_impl {
        Vec::new()
    } else {
        auto_select_implementations(&models, &slice.all_axioms, DEFAULT_MAX_AUTO_IMPLS)
    };
    let auto_impls_count = impls.len();

    let models_for_pipeline = models.clone();
    let impls_for_pipeline = impls.clone();

    let mut outcome = pipeline::run_with_models_and_impls(
        params,
        slice.signature.clone(),
        slice.all_axioms.clone(),
        models_for_pipeline,
        impls_for_pipeline,
        parse_ms,
        enumeration_ms,
        overall_start,
    )?;

    // Phase F derived data.
    let metrics = SliceMetrics::compute(
        &translation.signature,
        slice,
        global_axiom_count,
        params.model_bound,
        enumeration_ms,
        &outcome.mutation,
        &outcome.tightness,
    );
    let taxonomy = MutationTaxonomy::compute(&outcome.mutation, &outcome.tightness);
    let sym_diff_sizes = compute_sym_diff_sizes(&slice.all_axioms, &outcome.mutation, &models);
    let neighborhood = build_neighborhood_table(&outcome.mutation, &outcome.tightness, &sym_diff_sizes);

    let baseline = compute_baseline_tightness(slice, translation, &outcome.mutation, &models, &impls);
    let contribution = baseline.as_ref().map(|b| {
        TheoremContribution::from_kill_sets(slice.theorem_name.clone(), &outcome.tightness, b)
    });

    // Attach witnesses to alive mutants in-place.
    crate::witness::attach_witnesses_for_alive(
        &slice.all_axioms,
        &outcome.mutation,
        &models,
        &mut outcome.tightness,
    );

    Ok(SliceOutcome {
        theorem_name: slice.theorem_name.clone(),
        status: SliceStatus::Analyzed {
            outcome: Box::new(outcome),
            auto_implementations: auto_impls_count,
            metrics,
            taxonomy,
            neighborhood,
            contribution,
        },
        included_sorts: slice.included_sorts.clone(),
        included_relations: slice.included_relations.clone(),
        included_functions: slice.included_functions.clone(),
        excluded_sorts: slice.excluded_sorts.clone(),
        dependency_closure,
    })
}

/// Phase E+F aggregate: τ stats plus the diagnostic semantic-explainability
/// fields.
fn aggregate_slice_outcomes(slices: &[SliceOutcome]) -> AggregateReport {
    let mut analyzed_scores: Vec<f64> = Vec::new();
    let mut analyzed_reductions: Vec<f64> = Vec::new();
    let mut total_mutants: usize = 0;
    let mut total_killed: usize = 0;
    let mut taxonomy = MutationTaxonomy::default();
    let mut contributions: Vec<TheoremContribution> = Vec::new();
    let mut weak_candidates: Vec<String> = Vec::new();

    for slice in slices {
        if let SliceStatus::Analyzed {
            outcome,
            metrics,
            taxonomy: tax,
            contribution,
            ..
        } = &slice.status
        {
            analyzed_scores.push(outcome.tightness.score);
            analyzed_reductions.push(metrics.reduction_percentage);
            total_mutants += outcome.tightness.neighborhood_size;
            total_killed += outcome.tightness.killed_count;
            taxonomy.merge(tax);
            if let Some(c) = contribution {
                contributions.push(c.clone());
            }
            if outcome.tightness.score < 0.1 {
                weak_candidates.push(slice.theorem_name.clone());
            }
        }
    }

    let analyzed_count = analyzed_scores.len();
    let skipped_count = slices.len() - analyzed_count;
    let (mean, min, max) = if analyzed_scores.is_empty() {
        (0.0, 0.0, 0.0)
    } else {
        let mean = analyzed_scores.iter().sum::<f64>() / analyzed_scores.len() as f64;
        let min = analyzed_scores.iter().copied().fold(f64::INFINITY, f64::min);
        let max = analyzed_scores.iter().copied().fold(f64::NEG_INFINITY, f64::max);
        (mean, min, max)
    };
    let variance = if analyzed_scores.len() < 2 {
        0.0
    } else {
        let m = mean;
        analyzed_scores.iter().map(|x| (x - m).powi(2)).sum::<f64>()
            / analyzed_scores.len() as f64
    };
    let average_reduction = if analyzed_reductions.is_empty() {
        0.0
    } else {
        analyzed_reductions.iter().sum::<f64>() / analyzed_reductions.len() as f64
    };
    let total_kill_rate = if total_mutants == 0 {
        0.0
    } else {
        total_killed as f64 / total_mutants as f64
    };

    // Sort contributions descending by unique_kills, then by tightness.
    contributions.sort_by(|a, b| {
        b.unique_kills
            .cmp(&a.unique_kills)
            .then_with(|| {
                b.tightness
                    .partial_cmp(&a.tightness)
                    .unwrap_or(std::cmp::Ordering::Equal)
            })
            .then_with(|| a.theorem_name.cmp(&b.theorem_name))
    });

    let diagnostic_summary = generate_diagnostic_summary(
        analyzed_count,
        skipped_count,
        mean,
        variance,
        &weak_candidates,
        &taxonomy,
        average_reduction,
    );

    AggregateReport {
        mean_tightness: mean,
        min_tightness: min,
        max_tightness: max,
        analyzed_count,
        skipped_count,
        tightness_variance: variance,
        average_model_space_reduction_pct: average_reduction,
        total_mutants_generated: total_mutants,
        total_mutants_killed: total_killed,
        total_kill_rate,
        taxonomy,
        contributions,
        weak_theorem_candidates: weak_candidates,
        diagnostic_summary,
    }
}

#[allow(clippy::too_many_arguments)]
fn generate_diagnostic_summary(
    analyzed_count: usize,
    skipped_count: usize,
    mean: f64,
    variance: f64,
    weak_candidates: &[String],
    taxonomy: &MutationTaxonomy,
    average_reduction_pct: f64,
) -> String {
    if analyzed_count == 0 && skipped_count == 0 {
        return String::new();
    }
    let mut parts: Vec<String> = Vec::new();
    parts.push(format!(
        "{}/{} theorems analyzed successfully.",
        analyzed_count,
        analyzed_count + skipped_count
    ));
    if analyzed_count > 0 {
        if mean > 0.8 {
            parts.push("Specification is well-constrained (mean τ > 0.8).".into());
        } else if mean > 0.5 {
            parts.push("Specification has moderate constraint coverage.".into());
        } else {
            parts.push("Specification has significant constraint gaps.".into());
        }
        if variance > 0.05 {
            parts.push(format!(
                "Tightness varies significantly across theorems (σ² = {variance:.3}); some theorems may be much weaker than others."
            ));
        }
        if !weak_candidates.is_empty() {
            parts.push(format!(
                "Weak theorem candidates (τ < 0.1): {}. These theorems may be redundant or vacuously satisfied.",
                weak_candidates.join(", ")
            ));
        }
        let tax_line = taxonomy.diagnostic();
        if !tax_line.is_empty() {
            parts.push(tax_line);
        }
        if average_reduction_pct > 0.0 {
            parts.push(format!(
                "Semantic slicing reduced model space by {average_reduction_pct:.1}% on average."
            ));
        }
    }
    parts.join(" ")
}

// Used only when contribution_strength wants a Display-like rendering.
#[allow(dead_code)]
fn strength_label(s: ContributionStrength) -> &'static str {
    match s {
        ContributionStrength::High => "HIGH",
        ContributionStrength::Medium => "MEDIUM",
        ContributionStrength::Low => "LOW",
        ContributionStrength::None => "NONE",
    }
}

/// Pick up to `max_impls` enumerated models that satisfy every axiom.
///
/// "Satisfying" here uses [`FiniteModel::satisfies_spec`].  No diversity
/// heuristic — we simply take the first `max_impls` satisfying models in
/// enumeration order.  Enumeration order is deterministic, so the choice
/// is reproducible across runs.
///
/// Robustness: the core model evaluator panics when an axiom asks it to
/// evaluate a function call on out-of-domain argument values (e.g. a
/// `NatLit(5)` term against an `n=2` domain).  We wrap the per-model
/// check in `catch_unwind` and treat panics as "this model doesn't
/// satisfy", preserving deterministic semantics on well-formed inputs
/// and degrading gracefully on pathological ones.
pub fn auto_select_implementations(
    models: &[FiniteModel],
    axioms: &[Formula],
    max_impls: usize,
) -> Vec<FiniteModel> {
    models
        .iter()
        .filter(|m| safely_satisfies(m, axioms))
        .take(max_impls)
        .cloned()
        .collect()
}

fn safely_satisfies(model: &FiniteModel, axioms: &[Formula]) -> bool {
    std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| model.satisfies_spec(axioms)))
        .unwrap_or(false)
}

/// Render the translation summary as a human-readable block appended to the
/// text/HTML report.  JSON callers should serialise the [`TranslationSummary`]
/// directly via serde — for now the CLI uses this textual form for both.
pub fn format_translation_summary(s: &TranslationSummary) -> String {
    let mut out = String::new();
    out.push_str(&format!(
        "Lean analysis: {} theorems, {} predicates translated\n",
        s.translated_theorems.len(),
        s.translated_predicates.len()
    ));
    if !s.translated_theorems.is_empty() {
        out.push_str(&format!(
            "  Translated theorems: {}\n",
            s.translated_theorems.join(", ")
        ));
    }
    if !s.translated_predicates.is_empty() {
        out.push_str(&format!(
            "  Translated predicates: {}\n",
            s.translated_predicates.join(", ")
        ));
    }
    for (name, reason) in &s.skipped_theorems {
        out.push_str(&format!("  Skipped theorem {name}: {reason}\n"));
    }
    for (name, reason) in &s.skipped_predicates {
        out.push_str(&format!("  Skipped predicate {name}: {reason}\n"));
    }
    if s.sort_filter.original_sorts != s.sort_filter.filtered_sorts {
        out.push_str(&format!(
            "  Sort filter: {} → {} sorts (removed: {})\n",
            s.sort_filter.original_sorts,
            s.sort_filter.filtered_sorts,
            if s.sort_filter.removed.is_empty() {
                "—".to_string()
            } else {
                s.sort_filter.removed.join(", ")
            }
        ));
    }
    if s.auto_implementations > 0 {
        out.push_str(&format!(
            "  Auto-selected {} implementation model(s) from satisfying set\n",
            s.auto_implementations
        ));
    }
    if !s.warnings.is_empty() {
        out.push_str(&format!("  ({} warnings)\n", s.warnings.len()));
    }
    out
}

/// Render the Phase 5 extraction summary in a stable text format.  Pulled out
/// of `main.rs` so the fallback path can call it from this module.
pub fn format_extraction_summary(extraction: &LeanExtraction) -> String {
    let mut text = String::new();
    text.push_str("specmut v0.1.0 — Lean extraction summary\n\n");
    text.push_str(&format!(
        "Predicates discovered: {}\n",
        extraction.predicates.len()
    ));
    for p in &extraction.predicates {
        text.push_str(&format!(
            "  {:25} class={:?}  param_sorts=[{}]\n",
            p.name,
            p.relation_type,
            p.param_sorts.join(", ")
        ));
    }
    text.push('\n');
    text.push_str(&format!(
        "Theorems discovered: {}\n",
        extraction.theorems.len()
    ));
    for t in &extraction.theorems {
        text.push_str(&format!(
            "  {:25} references=[{}]\n",
            t.name,
            t.referenced_predicates.join(", ")
        ));
    }
    text
}

/// Internal phase tag used so the caller can distinguish runner vs translator failures.
enum LeanPhase {
    Runner(LeanPipelineError),
    Translator(TranslationError),
}

// silence unused warning when the field happens not to be read by some build
impl std::fmt::Debug for LeanPhase {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LeanPhase::Runner(e) => write!(f, "Runner({e})"),
            LeanPhase::Translator(e) => write!(f, "Translator({e})"),
        }
    }
}

// Keeps `PathBuf` usable as a path in the error type.
#[allow(dead_code)]
const _: () = {
    let _ = std::mem::size_of::<PathBuf>();
};
