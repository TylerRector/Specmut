//! `specmut` — command-line front-end for the Phase 5 pipeline.

mod compare;
mod config;
mod exit_codes;
mod html;
#[cfg(feature = "smt")]
mod hybrid_checker;
mod lean_pipeline;
mod model_file;
mod output;
mod pipeline;
mod witness;

use std::path::PathBuf;
use std::process::ExitCode;

use clap::{Args, Parser, Subcommand};
use specmut_parser::dafny_parser::DafnyParser;
use specmut_parser::lean_elaborator::{LeanElaborator, LeanError};
use specmut_parser::lean_parser::LeanParser;
use tracing_subscriber::EnvFilter;

use crate::config::Config;
use crate::output::{
    render_json, render_sliced_json, render_sliced_text, render_text, Report, SlicedReport,
};
use crate::pipeline::{is_dafny_path, is_lean_path, run, PipelineError, PipelineParams};

/// `specmut analyze sort.fol -n 5 -e 0.15 -f text`.
#[derive(Debug, Parser)]
#[command(name = "specmut", version, about = "Specification tightness analysis")]
struct Cli {
    #[command(subcommand)]
    command: Command,
}

#[derive(Debug, Subcommand)]
enum Command {
    /// Analyze a specification file.
    Analyze(AnalyzeArgs),
    /// Compare tightness across multiple specification files.
    Compare(CompareArgs),
}

#[derive(Debug, Args)]
struct CompareArgs {
    /// Spec files to compare, in evolution order.  Order matters: each
    /// entry's Δτ is computed against the previous entry.
    #[arg(required = true)]
    spec_files: Vec<PathBuf>,

    /// Output file (default: stdout).
    #[arg(short = 'o', long = "output", value_name = "FILE")]
    output: Option<PathBuf>,

    /// Output format: `text` (default) or `json`.
    #[arg(short = 'f', long = "format")]
    format: Option<String>,

    /// Maximum carrier size for model enumeration.
    #[arg(short = 'n', long = "model-bound")]
    model_bound: Option<usize>,

    /// Maximum quantifier rank for the local lattice.
    #[arg(short = 'k', long = "quantifier-rank")]
    quantifier_rank: Option<usize>,

    /// Neighborhood radius.
    #[arg(short = 'e', long = "epsilon")]
    epsilon: Option<f64>,

    /// Random seed.
    #[arg(short = 's', long = "seed")]
    seed: Option<u64>,

    /// Path to the `lean` binary for `.lean` spec files.
    #[arg(long = "lean-path", default_value = "lean")]
    lean_path: PathBuf,

    /// Wall-clock timeout for the Lean exporter subprocess, in seconds.
    #[arg(long = "lean-timeout", default_value_t = 60)]
    lean_timeout: u64,

    /// Disable auto-impl selection for `.lean` specs.
    #[arg(long = "no-auto-impl")]
    no_auto_impl: bool,
}

#[derive(Debug, Args)]
struct AnalyzeArgs {
    /// Path to the specification file (.fol or .lean).
    spec_file: PathBuf,

    /// Implementation `.model` file(s).
    #[arg(short = 'i', long = "impl", value_name = "FILE")]
    impls: Vec<PathBuf>,

    /// Optional configuration file.
    #[arg(short = 'c', long = "config", value_name = "FILE")]
    config: Option<PathBuf>,

    /// Maximum carrier size for model enumeration.
    #[arg(short = 'n', long = "model-bound")]
    model_bound: Option<usize>,

    /// Maximum quantifier rank for the local lattice.
    #[arg(short = 'k', long = "quantifier-rank")]
    quantifier_rank: Option<usize>,

    /// Neighborhood radius.
    #[arg(short = 'e', long = "epsilon")]
    epsilon: Option<f64>,

    /// Random seed.
    #[arg(short = 's', long = "seed")]
    seed: Option<u64>,

    /// Output file (default: stdout).
    #[arg(short = 'o', long = "output", value_name = "FILE")]
    output: Option<PathBuf>,

    /// Output format: `text` or `json`.
    #[arg(short = 'f', long = "format")]
    format: Option<String>,

    /// Use CEGIS acceleration.
    #[arg(long = "cegis")]
    cegis: bool,

    /// Path to the `lean` binary used for `.lean` elaboration.  Falls
    /// back to the Phase 5 regex extractor when `lean` is missing.
    #[arg(long = "lean-path", default_value = "lean")]
    lean_path: PathBuf,

    /// Enable full Lean→FOL translation via the Phase A exporter.  Without
    /// this flag, `.lean` files use the Phase 5 regex extractor / Phase 7
    /// best-effort elaborator and emit a summary only.  With this flag, the
    /// JSON IR pipeline runs and a tightness score is produced.
    #[arg(long = "lean-full")]
    lean_full: bool,

    /// Wall-clock timeout for the Lean exporter subprocess, in seconds.
    #[arg(long = "lean-timeout", default_value_t = 60)]
    lean_timeout: u64,

    /// Disable auto-selection of implementation models from the
    /// satisfying set.  By default, when no `-i` files are supplied,
    /// the Lean pipeline picks up to five satisfying models from the
    /// enumerated pool so tightness has something to compare against.
    #[arg(long = "no-auto-impl")]
    no_auto_impl: bool,

    /// Use Z3 SMT solver for entailment checking (requires --features smt).
    #[arg(long = "smt")]
    smt: bool,

    /// SMT solver timeout per query, in milliseconds.
    #[arg(long = "smt-timeout", default_value_t = 5000)]
    smt_timeout: u64,

    /// SMT-LIB logic name; `auto` lets Z3 pick.
    #[arg(long = "smt-logic", default_value = "auto")]
    smt_logic: String,

    /// Enable debug logging.
    #[arg(short = 'v', long = "verbose")]
    verbose: bool,
}

fn main() -> ExitCode {
    // Wrap the run loop in catch_unwind so a panic surfaces as
    // EXIT_INTERNAL_ERROR rather than propagating to the process abort
    // hook.
    let result = std::panic::catch_unwind(|| {
        let cli = Cli::parse();
        match cli.command {
            Command::Analyze(args) => run_analyze(args),
            Command::Compare(args) => run_compare_cmd(args),
        }
    });
    let code = match result {
        Ok(code) => code,
        Err(_) => {
            eprintln!("specmut: internal error — panic caught at top level");
            exit_codes::INTERNAL_ERROR
        }
    };
    ExitCode::from(code as u8)
}

fn run_analyze(args: AnalyzeArgs) -> i32 {
    if args.verbose {
        let _ = tracing_subscriber::fmt()
            .with_env_filter(EnvFilter::new("debug"))
            .try_init();
    }

    // Load config, then apply CLI overrides.
    let mut config_params = if let Some(path) = &args.config {
        match Config::load(path) {
            Ok(cfg) => Some(cfg),
            Err(e) => {
                eprintln!("specmut: {e}");
                return exit_codes::CONFIG_ERROR;
            }
        }
    } else {
        None
    };

    let mut model_bound = args.model_bound;
    let mut quantifier_rank = args.quantifier_rank;
    let mut epsilon = args.epsilon;
    let mut seed = args.seed;
    let mut format = args.format.clone();
    let mut impls = args.impls.clone();
    let mut spec_path = args.spec_file.clone();

    if let Some(cfg) = config_params.as_mut() {
        if model_bound.is_none() {
            model_bound = Some(cfg.parameters.model_bound);
        }
        if quantifier_rank.is_none() {
            quantifier_rank = Some(cfg.parameters.quantifier_rank);
        }
        if epsilon.is_none() {
            epsilon = Some(cfg.parameters.epsilon);
        }
        if seed.is_none() {
            seed = Some(cfg.parameters.seed);
        }
        if format.is_none() {
            format = Some(cfg.output.report_format.clone());
        }
        if impls.is_empty() && !cfg.project.implementations.is_empty() {
            impls = cfg
                .project
                .implementations
                .iter()
                .map(PathBuf::from)
                .collect();
        }
        if args.spec_file.as_os_str().is_empty() {
            spec_path = PathBuf::from(&cfg.project.spec_file);
        }
    }

    // Resolve --smt against the build's feature gate.  If --smt was
    // passed but the crate was built without `--features smt`, exit
    // with EXIT_SMT_UNAVAILABLE.
    let smt_config = if args.smt {
        #[cfg(feature = "smt")]
        {
            Some(pipeline::SmtParams {
                timeout_ms: args.smt_timeout,
                logic: if args.smt_logic == "auto" {
                    None
                } else {
                    Some(args.smt_logic.clone())
                },
            })
        }
        #[cfg(not(feature = "smt"))]
        {
            eprintln!(
                "specmut: SMT support not compiled in. Rebuild with: cargo build --features specmut-cli/smt"
            );
            return exit_codes::SMT_UNAVAILABLE;
        }
    } else {
        None
    };

    let params = PipelineParams {
        spec_path: spec_path.clone(),
        impls,
        model_bound: model_bound.unwrap_or(2),
        quantifier_rank: quantifier_rank.unwrap_or(2),
        epsilon: epsilon.unwrap_or(0.15),
        seed: seed.unwrap_or(42),
        cegis: args.cegis,
        smt: smt_config,
    };
    let format = format.unwrap_or_else(|| "text".to_string());

    // Dafny files are extraction-only — no FOL translation in Phase 7.
    if is_dafny_path(&params.spec_path) {
        return handle_dafny(&params.spec_path, &args.output);
    }

    // Lean files: either the Phase C full-IR pipeline (--lean-full) or the
    // Phase 7 best-effort elaborator → Phase 5 extraction fallback.
    if is_lean_path(&params.spec_path) {
        if args.lean_full {
            return handle_lean_full(&args, &params, &format);
        }
        return handle_lean(&args, &params);
    }

    // FOL path.
    let outcome = match run(&params) {
        Ok(o) => o,
        Err(e) => return map_pipeline_error(e),
    };

    let report = Report {
        spec_path: params.spec_path.display().to_string(),
        model_bound: params.model_bound,
        quantifier_rank: params.quantifier_rank,
        epsilon: params.epsilon,
        seed: params.seed,
        models_enumerated: outcome.models_enumerated,
        signature: &outcome.signature,
        axioms: &outcome.axioms,
        mutation: &outcome.mutation,
        tightness: &outcome.tightness,
        cegis: params.cegis,
        smt: params.smt.is_some(),
        fallback_count: outcome.fallback_count,
        timing: outcome.timing,
        lean_translation: None,
    };
    let rendered = match format.as_str() {
        "json" => render_json(&report),
        "html" => {
            // Try the Python visualizer first; fall back to the pure-Rust
            // builder if Python or the package isn't available.  We
            // serialize once so both paths see the same JSON.
            let json = render_json(&report);
            html::try_python_html(&json).unwrap_or_else(|| html::generate_fallback_html(&report))
        }
        _ => render_text(&report),
    };

    if let Some(path) = &args.output {
        if let Err(e) = std::fs::write(path, rendered) {
            eprintln!("specmut: could not write '{}': {e}", path.display());
            return exit_codes::CONFIG_ERROR;
        }
    } else {
        println!("{rendered}");
    }

    exit_codes::SUCCESS
}

fn map_pipeline_error(err: PipelineError) -> i32 {
    eprintln!("specmut: {err}");
    match err {
        PipelineError::Io { .. } => exit_codes::PARSE_ERROR,
        PipelineError::Parse(_) => exit_codes::PARSE_ERROR,
        PipelineError::ModelParse(_) => exit_codes::PARSE_ERROR,
        PipelineError::ModelBoundExceeded { .. } => exit_codes::MODEL_BOUND_EXCEEDED,
    }
}

fn handle_dafny(spec_path: &std::path::Path, output: &Option<PathBuf>) -> i32 {
    let source = match std::fs::read_to_string(spec_path) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("specmut: could not read '{}': {e}", spec_path.display());
            return exit_codes::PARSE_ERROR;
        }
    };
    let extraction = match DafnyParser.extract(&source) {
        Ok(e) => e,
        Err(e) => {
            eprintln!("specmut: {e}");
            return exit_codes::PARSE_ERROR;
        }
    };
    let mut text = String::new();
    text.push_str("specmut v0.1.0 — Dafny extraction summary\n\n");
    text.push_str(&format!("Methods: {}\n", extraction.methods.len()));
    for m in &extraction.methods {
        text.push_str(&format!(
            "  {} — {} requires, {} ensures, {} modifies\n",
            m.name,
            m.requires.len(),
            m.ensures.len(),
            m.modifies.len()
        ));
    }
    text.push_str(&format!("Functions: {}\n", extraction.functions.len()));
    for f in &extraction.functions {
        text.push_str(&format!(
            "  {}: {} — {} requires, {} ensures\n",
            f.name,
            f.return_type,
            f.requires.len(),
            f.ensures.len()
        ));
    }
    text.push_str(&format!("Predicates: {}\n", extraction.predicates.len()));
    for p in &extraction.predicates {
        text.push_str(&format!("  {} ({} params)\n", p.name, p.params.len()));
    }
    text.push_str(
        "\nDafny analysis is extraction-only in this version. Full FOL translation \
         requires Boogie integration (not yet implemented).\n",
    );
    write_output(output, &text);
    exit_codes::SUCCESS
}

fn handle_lean(args: &AnalyzeArgs, params: &PipelineParams) -> i32 {
    let source = match std::fs::read_to_string(&params.spec_path) {
        Ok(s) => s,
        Err(e) => {
            eprintln!(
                "specmut: could not read '{}': {e}",
                params.spec_path.display()
            );
            return exit_codes::PARSE_ERROR;
        }
    };
    let extraction = match LeanParser.extract(&source) {
        Ok(e) => e,
        Err(e) => {
            eprintln!("specmut: {e}");
            return exit_codes::PARSE_ERROR;
        }
    };

    let elaborator = LeanElaborator::new(args.lean_path.clone());
    match elaborator.elaborate(&params.spec_path, &extraction) {
        Ok(elab) => {
            // Successful elaboration: run the full pipeline against the
            // recovered signature and axioms.
            let parse_start = std::time::Instant::now();
            let overall_start = std::time::Instant::now();
            let outcome = match pipeline::run_with_signature(
                params,
                elab.signature.clone(),
                elab.axioms.clone(),
                parse_start.elapsed().as_millis(),
                overall_start,
            ) {
                Ok(o) => o,
                Err(e) => return map_pipeline_error(e),
            };
            // For Lean inputs we always emit the extraction summary on
            // top of whichever format the user asked for, so the
            // recovered FOL is visible alongside the analysis.
            let format = args.format.clone().unwrap_or_else(|| "text".to_string());
            let report = Report {
                spec_path: params.spec_path.display().to_string(),
                model_bound: params.model_bound,
                quantifier_rank: params.quantifier_rank,
                epsilon: params.epsilon,
                seed: params.seed,
                models_enumerated: outcome.models_enumerated,
                signature: &outcome.signature,
                axioms: &outcome.axioms,
                mutation: &outcome.mutation,
                tightness: &outcome.tightness,
                cegis: params.cegis,
                smt: params.smt.is_some(),
                fallback_count: outcome.fallback_count,
                timing: outcome.timing,
                lean_translation: None,
            };
            let mut rendered = match format.as_str() {
                "json" => render_json(&report),
                "html" => {
                    let json = render_json(&report);
                    html::try_python_html(&json)
                        .unwrap_or_else(|| html::generate_fallback_html(&report))
                }
                _ => render_text(&report),
            };
            if !elab.warnings.is_empty() && format != "json" {
                rendered.push_str("\nLean elaboration warnings:\n");
                for w in &elab.warnings {
                    rendered.push_str(&format!("  - {w}\n"));
                }
            }
            write_output(&args.output, &rendered);
            exit_codes::SUCCESS
        }
        Err(LeanError::UnsupportedConstruct { description }) => {
            let mut text = render_lean_extraction(&extraction);
            text.push_str(&format!(
                "\nLean elaboration: unsupported construct — {description}\n"
            ));
            text.push_str(
                "Falling back to extraction summary; rerun with a .fol spec to \
                 compute tightness.\n",
            );
            write_output(&args.output, &text);
            exit_codes::SUCCESS
        }
        Err(LeanError::BinaryNotFound { path }) => {
            let mut text = render_lean_extraction(&extraction);
            text.push_str(&format!(
                "\nLean elaboration skipped: `lean` binary not found at '{}'.\n\
                 Install Lean 4 and pass --lean-path to enable elaboration; \
                 the extraction above is informational only.\n",
                path.display()
            ));
            write_output(&args.output, &text);
            exit_codes::SUCCESS
        }
        Err(e) => {
            // Any other Phase 7 elaborator error — timeout, lean crash, output
            // parse — degrade to the extraction summary so the user always
            // gets something.  Phase D made this the policy for `--lean-full`
            // too; we mirror it here so `.lean` files without the flag
            // behave consistently regardless of whether lean is on PATH.
            let mut text = render_lean_extraction(&extraction);
            text.push_str(&format!("\nLean elaboration error (using extraction summary): {e}\n"));
            text.push_str("Use --lean-full for the JSON IR pipeline.\n");
            write_output(&args.output, &text);
            exit_codes::SUCCESS
        }
    }
}

/// Project the lean_pipeline `TranslationSummary` into the JSON-friendly
/// `output::LeanTranslationReport`.  Lifted into a helper so the (de)structuring
/// is local to one place.
fn translation_summary_to_json(
    s: &lean_pipeline::TranslationSummary,
) -> output::LeanTranslationReport {
    output::LeanTranslationReport {
        translated_theorems: s.translated_theorems.clone(),
        skipped_theorems: s
            .skipped_theorems
            .iter()
            .map(|(name, reason)| output::SkippedItem {
                name: name.clone(),
                reason: reason.clone(),
            })
            .collect(),
        translated_predicates: s.translated_predicates.clone(),
        skipped_predicates: s
            .skipped_predicates
            .iter()
            .map(|(name, reason)| output::SkippedItem {
                name: name.clone(),
                reason: reason.clone(),
            })
            .collect(),
        warnings: s.warnings.clone(),
        sort_filter: output::SortFilterJson {
            original_sorts: s.sort_filter.original_sorts,
            filtered_sorts: s.sort_filter.filtered_sorts,
            removed: s.sort_filter.removed.clone(),
        },
        auto_implementations: s.auto_implementations,
    }
}

/// Phase C: full Lean→FOL pipeline routed through the JSON IR exporter.
///
/// On a successful translation, renders the same `Report` shape the FOL path
/// produces, appended with a translation summary (translated/skipped decls,
/// warnings).  On a soft failure (lean missing, exporter error, all-skipped
/// translation that still produced *something*), prints the regex extraction
/// summary plus the reason and exits 0.  Hard-exits with PARSE_ERROR only
/// when the translator returned `NothingTranslatable`.
fn handle_lean_full(args: &AnalyzeArgs, params: &PipelineParams, format: &str) -> i32 {
    use crate::lean_pipeline::{
        format_extraction_summary, format_translation_summary, run_lean_analysis,
        LeanAnalysisError, LeanAnalysisOutcome,
    };

    let outcome = run_lean_analysis(
        &params.spec_path,
        &args.lean_path,
        args.lean_timeout,
        params,
        args.no_auto_impl,
    );

    match outcome {
        Ok(LeanAnalysisOutcome::Sliced {
            slices,
            translation_summary,
            aggregate,
        }) => {
            let sliced = SlicedReport {
                spec_path: params.spec_path.display().to_string(),
                model_bound: params.model_bound,
                quantifier_rank: params.quantifier_rank,
                epsilon: params.epsilon,
                seed: params.seed,
                cegis: params.cegis,
                smt: params.smt.is_some(),
                slices: &slices,
                translation_summary: &translation_summary,
                aggregate: &aggregate,
            };
            let rendered = match format {
                "json" => render_sliced_json(&sliced),
                // HTML for sliced output isn't a separate template yet;
                // fall back to text so the user always gets something.
                _ => render_sliced_text(&sliced),
            };
            write_output(&args.output, &rendered);
            exit_codes::SUCCESS
        }
        Ok(LeanAnalysisOutcome::Global {
            outcome,
            translation_summary,
        }) => {
            let lean_translation = Some(translation_summary_to_json(&translation_summary));
            let report = Report {
                spec_path: params.spec_path.display().to_string(),
                model_bound: params.model_bound,
                quantifier_rank: params.quantifier_rank,
                epsilon: params.epsilon,
                seed: params.seed,
                models_enumerated: outcome.models_enumerated,
                signature: &outcome.signature,
                axioms: &outcome.axioms,
                mutation: &outcome.mutation,
                tightness: &outcome.tightness,
                cegis: params.cegis,
                smt: params.smt.is_some(),
                fallback_count: outcome.fallback_count,
                timing: outcome.timing,
                lean_translation,
            };
            let mut rendered = match format {
                "json" => render_json(&report),
                "html" => {
                    let json = render_json(&report);
                    html::try_python_html(&json)
                        .unwrap_or_else(|| html::generate_fallback_html(&report))
                }
                _ => render_text(&report),
            };
            if format != "json" {
                rendered.push('\n');
                rendered.push_str(&format_translation_summary(&translation_summary));
            }
            write_output(&args.output, &rendered);
            exit_codes::SUCCESS
        }
        Ok(LeanAnalysisOutcome::ExtractionOnly { extraction, reason }) => {
            let mut text = format_extraction_summary(&extraction);
            text.push('\n');
            text.push_str(&format!("Lean full analysis unavailable: {reason}\n"));
            text.push_str(
                "Falling back to the extraction summary above. \
                 Install lean (https://leanprover.github.io/) for full analysis.\n",
            );
            write_output(&args.output, &text);
            exit_codes::SUCCESS
        }
        Err(LeanAnalysisError::NothingTranslatable(reason)) => {
            eprintln!("specmut: Lean translation produced no axioms: {reason}");
            eprintln!(
                "Hint: every theorem/predicate used constructs outside the supported \
                 first-order subset. Try a simpler spec or pass --lean-full off to \
                 see the extraction summary."
            );
            exit_codes::PARSE_ERROR
        }
        Err(LeanAnalysisError::Pipeline(e)) => map_pipeline_error(e),
        Err(LeanAnalysisError::Io { path, source }) => {
            eprintln!("specmut: could not read '{path}': {source}");
            exit_codes::PARSE_ERROR
        }
        Err(LeanAnalysisError::Extraction(msg)) => {
            eprintln!("specmut: {msg}");
            exit_codes::PARSE_ERROR
        }
    }
}

fn render_lean_extraction(extraction: &specmut_parser::lean_parser::LeanExtraction) -> String {
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

fn write_output(output: &Option<PathBuf>, text: &str) {
    if let Some(path) = output {
        if let Err(e) = std::fs::write(path, text) {
            eprintln!("specmut: could not write '{}': {e}", path.display());
        }
    } else {
        print!("{text}");
    }
}

#[allow(dead_code)]
fn print_lean_summary(
    extraction: &specmut_parser::lean_parser::LeanExtraction,
    output: &Option<PathBuf>,
) {
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
    text.push_str("\nLean files are extraction-only in Phase 5; rerun with a .fol spec to compute tightness.\n");
    if let Some(path) = output {
        if let Err(e) = std::fs::write(path, &text) {
            eprintln!("specmut: could not write '{}': {e}", path.display());
        }
    } else {
        print!("{text}");
    }
}

/// Run the `compare` subcommand: analyze each spec, print a comparison
/// table.  Always exits 0 unless writing the output fails — individual
/// per-spec errors are recorded inside the table.
fn run_compare_cmd(args: CompareArgs) -> i32 {
    let params = pipeline::PipelineParams {
        spec_path: PathBuf::new(), // overridden per-file inside compare.rs
        impls: Vec::new(),
        model_bound: args.model_bound.unwrap_or(2),
        quantifier_rank: args.quantifier_rank.unwrap_or(2),
        epsilon: args.epsilon.unwrap_or(0.15),
        seed: args.seed.unwrap_or(42),
        cegis: false,
        smt: None,
    };
    let format = args.format.clone().unwrap_or_else(|| "text".to_string());
    let results = compare::run_compare(
        &args.spec_files,
        &params,
        &args.lean_path,
        args.lean_timeout,
        args.no_auto_impl,
    );
    let rendered = match format.as_str() {
        "json" => compare::render_compare_json(&results),
        _ => compare::render_compare_text(&results),
    };
    if let Some(path) = &args.output {
        if let Err(e) = std::fs::write(path, rendered) {
            eprintln!("specmut: could not write '{}': {e}", path.display());
            return exit_codes::CONFIG_ERROR;
        }
    } else {
        println!("{rendered}");
    }
    exit_codes::SUCCESS
}
