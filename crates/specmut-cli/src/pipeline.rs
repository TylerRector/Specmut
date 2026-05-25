//! End-to-end pipeline: parse → enumerate → mutate → evaluate.

use std::path::{Path, PathBuf};
use std::sync::atomic::Ordering;
use std::sync::atomic::AtomicUsize;
use std::sync::Arc;
use std::time::Instant;

use specmut_core::cegis::CegisEvaluator;
use specmut_core::formula::Formula;
use specmut_core::lattice::{
    EntailmentChecker, ModelEntailmentChecker, SpecElement, SpecLattice,
};
use specmut_core::metric::JaccardMetric;
use specmut_core::model::{FiniteModel, ModelEnumerator};
use specmut_core::mutation::{MutationGenerator, MutationResult};
use specmut_core::signature::Signature;
use specmut_core::tightness::{TightnessEvaluator, TightnessResult};
use specmut_parser::fol_parser::FolParser;
use specmut_parser::SpecParser;
use thiserror::Error;

use crate::model_file::{parse_model_file, ModelParseError};
use crate::output::TimingBreakdown;

/// Errors raised by the pipeline orchestration layer.  These wrap the
/// underlying parser / signature / model errors so `main` can map them
/// to exit codes.
#[derive(Debug, Error)]
pub enum PipelineError {
    /// File I/O failure when reading the spec or an implementation.
    #[error("I/O error on '{path}': {source}")]
    Io {
        /// Path that failed.
        path: String,
        /// Underlying error.
        #[source]
        source: std::io::Error,
    },
    /// Parse error in the spec file.
    #[error(transparent)]
    Parse(#[from] specmut_parser::ParseError),
    /// Parse error in an implementation model file.
    #[error(transparent)]
    ModelParse(#[from] ModelParseError),
    /// Model bound produced too large an enumeration space.
    #[error("model bound {bound} produces too many models (limit {limit})")]
    ModelBoundExceeded {
        /// The requested bound.
        bound: usize,
        /// The configured ceiling.
        limit: usize,
    },
}

/// Pipeline configuration mirroring CLI flags.
#[derive(Debug, Clone)]
pub struct PipelineParams {
    /// Path to the spec file.
    pub spec_path: PathBuf,
    /// Implementation model files.
    pub impls: Vec<PathBuf>,
    /// Maximum carrier size for model enumeration.
    pub model_bound: usize,
    /// Maximum quantifier rank (used by the lattice in CEGIS mode).
    pub quantifier_rank: usize,
    /// ε-neighborhood radius.
    pub epsilon: f64,
    /// Random seed (currently unused — reserved for future sampling).
    pub seed: u64,
    /// Use CEGIS instead of exhaustive evaluation.
    pub cegis: bool,
    /// SMT configuration; `Some` enables the Z3-first hybrid
    /// entailment checker, `None` uses model enumeration only.
    pub smt: Option<SmtParams>,
}

/// Configuration for the SMT-backed entailment checker.  Used only
/// when the `smt` feature is enabled; the fields are dead code in
/// non-SMT builds.
#[derive(Debug, Clone)]
#[cfg_attr(not(feature = "smt"), allow(dead_code))]
pub struct SmtParams {
    /// Per-query timeout in milliseconds.
    pub timeout_ms: u64,
    /// Optional SMT-LIB logic (e.g. `"QF_UF"`).
    pub logic: Option<String>,
}

/// All artefacts produced by the pipeline.
pub struct PipelineOutcome {
    /// Parsed signature.
    pub signature: Signature,
    /// Parsed axioms.
    pub axioms: Vec<Formula>,
    /// SpecElement wrapping the axioms.  Retained for downstream
    /// consumers (e.g. richer report sections); not all paths read it.
    #[allow(dead_code)]
    pub spec: SpecElement,
    /// Mutation generation result.
    pub mutation: MutationResult,
    /// Tightness evaluation result.
    pub tightness: TightnessResult,
    /// Number of models enumerated for the metric pool.
    pub models_enumerated: usize,
    /// Number of times the hybrid entailment checker fell back from Z3
    /// to model enumeration because Z3 returned `Unknown`.  Always `0`
    /// when SMT is not enabled.
    pub fallback_count: usize,
    /// Timing breakdown.
    pub timing: TimingBreakdown,
}

/// Hard ceiling on the enumeration space.  If the relation-only model
/// count exceeds this, the pipeline aborts with
/// [`PipelineError::ModelBoundExceeded`].  Keeps a runaway `-n` flag
/// from OOMing the machine.
const MODEL_SPACE_LIMIT: u64 = 1 << 22;

/// Drive the full pipeline starting from a spec file on disk.
pub fn run(params: &PipelineParams) -> Result<PipelineOutcome, PipelineError> {
    let overall_start = Instant::now();
    let parse_start = Instant::now();
    let spec_text = std::fs::read_to_string(&params.spec_path).map_err(|e| PipelineError::Io {
        path: params.spec_path.display().to_string(),
        source: e,
    })?;
    let (signature, axioms) = FolParser.parse(&spec_text)?;
    let parse_ms = parse_start.elapsed().as_millis();
    run_with_signature(params, signature, axioms, parse_ms, overall_start)
}

/// Enumerate every finite model up to `model_bound` for the given signature,
/// returning the materialised vector.  Returns `Err(ModelBoundExceeded)` if
/// the model-space count exceeds the hard ceiling.
///
/// Public so [`crate::lean_pipeline`] can enumerate models once and reuse the
/// result for auto-implementation selection without paying for enumeration
/// twice inside [`run_with_models_and_impls`].
pub fn enumerate_models_for_signature(
    sig: &Signature,
    model_bound: usize,
) -> Result<Vec<FiniteModel>, PipelineError> {
    let model_space = ModelEnumerator::new(sig.clone(), model_bound).count();
    let limit_big = num_bigint::BigUint::from(MODEL_SPACE_LIMIT);
    if model_space > limit_big {
        return Err(PipelineError::ModelBoundExceeded {
            bound: model_bound,
            limit: MODEL_SPACE_LIMIT as usize,
        });
    }
    Ok(ModelEnumerator::new(sig.clone(), model_bound).enumerate().collect())
}

/// Drive the pipeline starting from a pre-parsed signature and axioms.
/// Used by the Lean elaboration path, which produces these directly
/// without going through the FOL parser.
pub fn run_with_signature(
    params: &PipelineParams,
    signature: Signature,
    axioms: Vec<Formula>,
    parse_ms: u128,
    overall_start: Instant,
) -> Result<PipelineOutcome, PipelineError> {
    let enum_start = Instant::now();
    let models = enumerate_models_for_signature(&signature, params.model_bound)?;
    let enumeration_ms = enum_start.elapsed().as_millis();

    // Read implementation models from disk for the FOL path.  The Lean
    // path uses `run_with_models_and_impls` directly and supplies its own.
    let mut implementations: Vec<FiniteModel> = Vec::new();
    for path in &params.impls {
        let text = std::fs::read_to_string(path).map_err(|e| PipelineError::Io {
            path: path.display().to_string(),
            source: e,
        })?;
        implementations.push(parse_model_file(&text, &signature)?);
    }

    run_with_models_and_impls(
        params,
        signature,
        axioms,
        models,
        implementations,
        parse_ms,
        enumeration_ms,
        overall_start,
    )
}

/// Drive the pipeline with everything pre-computed: signature, axioms, the
/// enumerated model pool, and the implementations.  The Lean pipeline uses
/// this entry so it can enumerate once, auto-select impls from satisfying
/// models, and avoid double work.
#[allow(clippy::too_many_arguments)]
pub fn run_with_models_and_impls(
    params: &PipelineParams,
    signature: Signature,
    axioms: Vec<Formula>,
    models: Vec<FiniteModel>,
    implementations: Vec<FiniteModel>,
    parse_ms: u128,
    enumeration_ms: u128,
    overall_start: Instant,
) -> Result<PipelineOutcome, PipelineError> {
    let spec = SpecElement::from_axioms(axioms.iter().cloned());

    let models_enumerated = models.len();

    let metric = JaccardMetric::new(models.clone());
    let bundle = build_entailment_bundle(&signature, &models, params.smt.as_ref());
    let entailment_ref: &dyn EntailmentChecker = bundle.checker.as_ref();

    // Generate mutations.
    let mutation_start = Instant::now();
    let generator = MutationGenerator::new(metric, params.epsilon);
    let mutation = generator.generate(&spec, &signature, entailment_ref);
    let mutation_ms = mutation_start.elapsed().as_millis();

    // Tightness evaluation.
    let tightness_start = Instant::now();
    let tightness = if params.cegis {
        let lattice_metric = JaccardMetric::new(models.clone());
        let lattice = SpecLattice::build_local(
            signature.clone(),
            spec.clone(),
            params.epsilon,
            params.quantifier_rank,
            params.model_bound,
            entailment_ref,
        )
        .map_err(|_| PipelineError::ModelBoundExceeded {
            bound: params.model_bound,
            limit: MODEL_SPACE_LIMIT as usize,
        })?;
        let evaluator = CegisEvaluator::new(lattice, lattice_metric);
        let (result, _state) = evaluator.run(&spec, &mutation, &implementations);
        result
    } else {
        let evaluator = TightnessEvaluator::new(JaccardMetric::new(models));
        evaluator.evaluate(&spec, &mutation, &implementations)
    };
    let tightness_ms = tightness_start.elapsed().as_millis();

    let timing = TimingBreakdown {
        parse_ms,
        enumeration_ms,
        mutation_ms,
        tightness_ms,
        total_ms: 0,
    }
    .with_total(overall_start.elapsed());

    let fallback_count = bundle.fallback_counter.load(Ordering::Relaxed);

    Ok(PipelineOutcome {
        signature,
        axioms,
        spec,
        mutation,
        tightness,
        models_enumerated,
        fallback_count,
        timing,
    })
}

/// Bundle returned by [`build_entailment_bundle`] — a trait-object
/// checker plus a shared counter that the [`HybridEntailmentChecker`]
/// uses to record how many times it had to fall back from Z3 to model
/// enumeration.  For non-SMT builds (or runs without `--smt`) the
/// counter stays at zero.
struct EntailmentBundle {
    checker: Box<dyn EntailmentChecker>,
    fallback_counter: Arc<AtomicUsize>,
}

fn build_entailment_bundle(
    signature: &Signature,
    models: &[FiniteModel],
    smt: Option<&SmtParams>,
) -> EntailmentBundle {
    let counter = Arc::new(AtomicUsize::new(0));
    #[cfg(feature = "smt")]
    {
        if let Some(smt_params) = smt {
            let checker = crate::hybrid_checker::HybridEntailmentChecker::new(
                signature.clone(),
                models.to_vec(),
                smt_params.timeout_ms,
                smt_params.logic.clone(),
                counter.clone(),
            );
            return EntailmentBundle {
                checker: Box::new(checker),
                fallback_counter: counter,
            };
        }
    }
    let _ = signature; // unused on non-SMT builds and when smt is None
    let _ = smt;
    EntailmentBundle {
        checker: Box::new(ModelEntailmentChecker::new(models.to_vec())),
        fallback_counter: counter,
    }
}

/// Whether `path` looks like a `.lean` file.
pub fn is_lean_path(path: &Path) -> bool {
    matches!(
        path.extension().and_then(|s| s.to_str()),
        Some("lean") | Some("Lean")
    )
}

/// Whether `path` looks like a Dafny source file.
pub fn is_dafny_path(path: &Path) -> bool {
    matches!(
        path.extension().and_then(|s| s.to_str()),
        Some("dfy") | Some("Dfy")
    )
}
