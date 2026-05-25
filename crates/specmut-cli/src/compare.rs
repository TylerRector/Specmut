//! Phase F (§2.8): `compare` subcommand for spec-evolution analysis.
//!
//! Runs the analysis pipeline against each supplied spec file and prints
//! a comparison table with per-file τ + Δτ.  Lean files with `--lean-full`
//! contribute their aggregate (mean) tightness; FOL files contribute the
//! global tightness; everything else is reported as unavailable.

use std::path::{Path, PathBuf};

use serde::Serialize;

use crate::lean_pipeline::{run_lean_analysis, LeanAnalysisError, LeanAnalysisOutcome, SliceStatus};
use crate::pipeline::{self, is_dafny_path, is_lean_path, PipelineError, PipelineParams};

/// Per-spec aggregate stats compared in the output table.
#[derive(Debug, Clone, Serialize)]
pub struct SingleResult {
    /// Spec file path (as supplied).
    pub spec_path: String,
    /// Sort count of the spec's (post-slice / post-translate) signature.
    pub sort_count: usize,
    /// Relation count.
    pub relation_count: usize,
    /// Function count.
    pub function_count: usize,
    /// Total axiom count.
    pub axiom_count: usize,
    /// Mean tightness (aggregate for Lean, global for FOL).  `None` when
    /// no τ could be computed (e.g. extraction-only fallback).
    pub mean_tightness: Option<f64>,
    /// Difference vs. the previous entry's `mean_tightness`.  `None` for
    /// the first entry or when either side is `None`.
    pub delta_tightness: Option<f64>,
    /// Human-readable note (e.g. "Lean (sliced)", "FOL", "extraction-only").
    pub mode: String,
}

/// Compare report — one entry per input spec, in input order.
#[derive(Debug, Clone, Serialize)]
pub struct CompareReport {
    /// Per-spec results.
    pub results: Vec<SingleResult>,
}

/// Run the comparison.  Errors from individual specs are folded into
/// `SingleResult.mode` so the table still renders; only the very first
/// I/O failure on a spec aborts the whole call.
pub fn run_compare(
    spec_files: &[PathBuf],
    params: &PipelineParams,
    lean_path: &Path,
    lean_timeout: u64,
    disable_auto_impl: bool,
) -> Vec<SingleResult> {
    let mut results: Vec<SingleResult> = Vec::with_capacity(spec_files.len());
    for spec in spec_files {
        let mut local_params = params.clone();
        local_params.spec_path = spec.clone();

        let result = analyze_one(spec, &local_params, lean_path, lean_timeout, disable_auto_impl);
        results.push(result);
    }
    // Compute delta_tightness in a second pass so each entry references
    // its predecessor.
    let mut prev: Option<f64> = None;
    for r in results.iter_mut() {
        r.delta_tightness = match (prev, r.mean_tightness) {
            (Some(p), Some(now)) => Some(now - p),
            _ => None,
        };
        if let Some(now) = r.mean_tightness {
            prev = Some(now);
        }
    }
    results
}

fn analyze_one(
    spec: &Path,
    params: &PipelineParams,
    lean_path: &Path,
    lean_timeout: u64,
    disable_auto_impl: bool,
) -> SingleResult {
    if is_dafny_path(spec) {
        return SingleResult {
            spec_path: spec.display().to_string(),
            sort_count: 0,
            relation_count: 0,
            function_count: 0,
            axiom_count: 0,
            mean_tightness: None,
            delta_tightness: None,
            mode: "Dafny (extraction-only; no τ)".to_string(),
        };
    }
    if is_lean_path(spec) {
        return analyze_lean(spec, params, lean_path, lean_timeout, disable_auto_impl);
    }
    analyze_fol(spec, params)
}

fn analyze_fol(spec: &Path, params: &PipelineParams) -> SingleResult {
    match pipeline::run(params) {
        Ok(o) => SingleResult {
            spec_path: spec.display().to_string(),
            sort_count: o.signature.sorts.len(),
            relation_count: o.signature.relations.len(),
            function_count: o.signature.functions.len(),
            axiom_count: o.axioms.len(),
            mean_tightness: Some(o.tightness.score),
            delta_tightness: None,
            mode: "FOL".to_string(),
        },
        Err(e) => SingleResult {
            spec_path: spec.display().to_string(),
            sort_count: 0,
            relation_count: 0,
            function_count: 0,
            axiom_count: 0,
            mean_tightness: None,
            delta_tightness: None,
            mode: format!("FOL — error: {e}"),
        },
    }
}

fn analyze_lean(
    spec: &Path,
    params: &PipelineParams,
    lean_path: &Path,
    lean_timeout: u64,
    disable_auto_impl: bool,
) -> SingleResult {
    let outcome = run_lean_analysis(spec, lean_path, lean_timeout, params, disable_auto_impl);
    match outcome {
        Ok(LeanAnalysisOutcome::Sliced {
            slices, aggregate, ..
        }) => {
            // Sum slice-level signature stats — there's no single sig for
            // sliced runs.  We surface per-slice means as a single line.
            let (sorts, rels, funs, axioms) = sum_slice_signatures(&slices);
            SingleResult {
                spec_path: spec.display().to_string(),
                sort_count: sorts,
                relation_count: rels,
                function_count: funs,
                axiom_count: axioms,
                mean_tightness: Some(aggregate.mean_tightness),
                delta_tightness: None,
                mode: format!(
                    "Lean sliced ({}/{} analyzed)",
                    aggregate.analyzed_count,
                    aggregate.analyzed_count + aggregate.skipped_count
                ),
            }
        }
        Ok(LeanAnalysisOutcome::Global { outcome, .. }) => SingleResult {
            spec_path: spec.display().to_string(),
            sort_count: outcome.signature.sorts.len(),
            relation_count: outcome.signature.relations.len(),
            function_count: outcome.signature.functions.len(),
            axiom_count: outcome.axioms.len(),
            mean_tightness: Some(outcome.tightness.score),
            delta_tightness: None,
            mode: "Lean (global)".to_string(),
        },
        Ok(LeanAnalysisOutcome::ExtractionOnly { reason, .. }) => SingleResult {
            spec_path: spec.display().to_string(),
            sort_count: 0,
            relation_count: 0,
            function_count: 0,
            axiom_count: 0,
            mean_tightness: None,
            delta_tightness: None,
            mode: format!("Lean (extraction only): {reason}"),
        },
        Err(LeanAnalysisError::Pipeline(PipelineError::ModelBoundExceeded { bound, limit })) => {
            SingleResult {
                spec_path: spec.display().to_string(),
                sort_count: 0,
                relation_count: 0,
                function_count: 0,
                axiom_count: 0,
                mean_tightness: None,
                delta_tightness: None,
                mode: format!("Lean — model bound {bound} exceeded (limit {limit})"),
            }
        }
        Err(e) => SingleResult {
            spec_path: spec.display().to_string(),
            sort_count: 0,
            relation_count: 0,
            function_count: 0,
            axiom_count: 0,
            mean_tightness: None,
            delta_tightness: None,
            mode: format!("Lean — error: {e}"),
        },
    }
}

fn sum_slice_signatures(slices: &[crate::lean_pipeline::SliceOutcome]) -> (usize, usize, usize, usize) {
    // For comparison purposes report the *maximum* per-slice symbol count;
    // that's a stable proxy for "how big any one theorem's slice was."
    // Axioms is the sum of axiom counts across analyzed slices.
    let mut sorts = 0usize;
    let mut rels = 0usize;
    let mut funs = 0usize;
    let mut axioms = 0usize;
    for slice in slices {
        sorts = sorts.max(slice.included_sorts.len());
        rels = rels.max(slice.included_relations.len());
        funs = funs.max(slice.included_functions.len());
        if let SliceStatus::Analyzed { outcome, .. } = &slice.status {
            axioms += outcome.axioms.len();
        }
    }
    (sorts, rels, funs, axioms)
}

/// Render the comparison as a human-readable aligned table.
pub fn render_compare_text(results: &[SingleResult]) -> String {
    let mut out = String::new();
    out.push_str("specmut v0.1.0 — Specification Comparison\n\n");
    out.push_str(&format!(
        "{:<40} {:>6} {:>5} {:>5} {:>7} {:>9} {:>8}  {}\n",
        "Spec", "Sorts", "Rels", "Funs", "Axioms", "τ (mean)", "Δτ", "Mode"
    ));
    out.push_str(&format!("{:-<100}\n", ""));
    for r in results {
        let tau = match r.mean_tightness {
            Some(v) => format!("{v:.3}"),
            None => "—".to_string(),
        };
        let delta = match r.delta_tightness {
            Some(v) if v >= 0.0 => format!("+{v:.3}"),
            Some(v) => format!("{v:.3}"),
            None => "—".to_string(),
        };
        out.push_str(&format!(
            "{:<40} {:>6} {:>5} {:>5} {:>7} {:>9} {:>8}  {}\n",
            truncate(&r.spec_path, 40),
            r.sort_count,
            r.relation_count,
            r.function_count,
            r.axiom_count,
            tau,
            delta,
            r.mode
        ));
    }
    out
}

/// Render the comparison as a JSON document.
pub fn render_compare_json(results: &[SingleResult]) -> String {
    let report = CompareReport {
        results: results.to_vec(),
    };
    serde_json::to_string_pretty(&report).unwrap_or_else(|_| "{}".to_string())
}

fn truncate(s: &str, max: usize) -> String {
    if s.chars().count() <= max {
        s.to_string()
    } else {
        let take = max.saturating_sub(3);
        let prefix: String = s.chars().take(take).collect();
        format!("{prefix}...")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn delta_computed_against_previous_only() {
        let mut entries = [
            SingleResult {
                spec_path: "a".into(),
                sort_count: 1,
                relation_count: 1,
                function_count: 0,
                axiom_count: 1,
                mean_tightness: Some(0.2),
                delta_tightness: None,
                mode: "FOL".into(),
            },
            SingleResult {
                spec_path: "b".into(),
                sort_count: 1,
                relation_count: 1,
                function_count: 0,
                axiom_count: 1,
                mean_tightness: Some(0.5),
                delta_tightness: None,
                mode: "FOL".into(),
            },
            SingleResult {
                spec_path: "c".into(),
                sort_count: 1,
                relation_count: 1,
                function_count: 0,
                axiom_count: 1,
                mean_tightness: None,
                delta_tightness: None,
                mode: "n/a".into(),
            },
            SingleResult {
                spec_path: "d".into(),
                sort_count: 1,
                relation_count: 1,
                function_count: 0,
                axiom_count: 1,
                mean_tightness: Some(0.8),
                delta_tightness: None,
                mode: "FOL".into(),
            },
        ];
        // Apply the same second-pass delta logic as run_compare.
        let mut prev: Option<f64> = None;
        for r in entries.iter_mut() {
            r.delta_tightness = match (prev, r.mean_tightness) {
                (Some(p), Some(now)) => Some(now - p),
                _ => None,
            };
            if let Some(now) = r.mean_tightness {
                prev = Some(now);
            }
        }
        assert!(entries[0].delta_tightness.is_none());
        assert!(
            (entries[1].delta_tightness.expect("delta[1] computed") - 0.3).abs() < 1e-9
        );
        // Missing tightness yields no delta but doesn't reset `prev`.
        assert!(entries[2].delta_tightness.is_none());
        assert!(
            (entries[3].delta_tightness.expect("delta[3] computed") - 0.3).abs() < 1e-9
        );
    }

    #[test]
    fn render_compare_text_has_header_and_rows() {
        let entries = vec![SingleResult {
            spec_path: "x.fol".into(),
            sort_count: 1,
            relation_count: 2,
            function_count: 3,
            axiom_count: 4,
            mean_tightness: Some(0.55),
            delta_tightness: None,
            mode: "FOL".into(),
        }];
        let text = render_compare_text(&entries);
        assert!(text.contains("Spec"));
        assert!(text.contains("x.fol"));
        assert!(text.contains("0.550"));
    }
}
