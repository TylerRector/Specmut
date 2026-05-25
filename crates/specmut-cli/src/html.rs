//! HTML report generation.
//!
//! The CLI emits HTML via two paths:
//!
//! 1. Subprocess: invoke `python3 -m specmut_viz.report ...` when the
//!    [`specmut_viz`](../python/specmut_viz) package is available.  That
//!    path embeds graphviz-rendered Hasse / dependency diagrams.
//! 2. Pure-Rust fallback: a single-file HTML report with no diagrams,
//!    built by string formatting.  No template-engine dependency.
//!
//! The fallback is always available; the subprocess path is best-effort.

use std::path::PathBuf;
use std::process::Command;

use specmut_core::formula::Formula;
use specmut_core::mutation::{Mutant, MutantClass};

use crate::output::Report;

/// Try the Python visualizer; return its HTML if it succeeded, else
/// `None`.  Discovery order matches §6 of the prompt:
///
/// 1. `SPECMUT_VIZ_PATH` env var (explicit PYTHONPATH override).
/// 2. `<binary>/../python` (development checkout layout).
/// 3. Installed `specmut-viz` package on PATH.
pub fn try_python_html(report_json: &str) -> Option<String> {
    let tmp = tempfile::Builder::new()
        .prefix("specmut-report-")
        .suffix(".json")
        .tempfile()
        .ok()?;
    std::fs::write(tmp.path(), report_json).ok()?;
    let out_tmp = tempfile::Builder::new()
        .prefix("specmut-report-")
        .suffix(".html")
        .tempfile()
        .ok()?;

    let mut cmd = Command::new("python3");
    cmd.arg("-m")
        .arg("specmut_viz.report")
        .arg("--json")
        .arg(tmp.path())
        .arg("-o")
        .arg(out_tmp.path())
        .arg("--hasse")
        .arg("--deps")
        // Suppress stderr noise (`ModuleNotFoundError: No module named
        // 'specmut_viz'`) on the discovery-failure path; we surface a
        // single tracing debug line instead and fall back cleanly.
        .stderr(std::process::Stdio::null());

    if let Some(viz_path) = python_module_path() {
        let existing = std::env::var_os("PYTHONPATH");
        let combined = match existing {
            Some(v) => {
                let mut s = std::ffi::OsString::from(viz_path);
                s.push(":");
                s.push(v);
                s
            }
            None => std::ffi::OsString::from(viz_path),
        };
        cmd.env("PYTHONPATH", combined);
    }

    let status = cmd.status().ok()?;
    if !status.success() {
        return None;
    }
    std::fs::read_to_string(out_tmp.path()).ok()
}

fn python_module_path() -> Option<PathBuf> {
    if let Ok(p) = std::env::var("SPECMUT_VIZ_PATH") {
        let path = PathBuf::from(p);
        if path.exists() {
            return Some(path);
        }
    }
    if let Ok(exe) = std::env::current_exe() {
        let candidate = exe
            .parent()
            .and_then(|p| p.parent())
            .and_then(|p| p.parent())
            .map(|p| p.join("python"));
        if let Some(path) = candidate {
            if path.join("specmut_viz").exists() {
                return Some(path);
            }
        }
    }
    None
}

/// Build a single-file HTML report from `report` using string
/// formatting only.  No external assets or template engine.
pub fn generate_fallback_html(report: &Report) -> String {
    let mut html = String::new();
    html.push_str("<!DOCTYPE html>\n<html lang=\"en\">\n<head>\n");
    html.push_str("<meta charset=\"utf-8\">\n");
    html.push_str("<title>specmut — Tightness Report</title>\n");
    html.push_str("<style>\n");
    html.push_str(FALLBACK_CSS);
    html.push_str("</style>\n</head>\n<body>\n");
    html.push_str("<h1>specmut — Specification Tightness Report</h1>\n");

    html.push_str("<section><h2>Summary</h2>\n");
    let score = report.tightness.score;
    let score_class = score_color_class(score);
    html.push_str(&format!(
        "<p class=\"score {score_class}\">τ = {score:.3}</p>\n",
        score = score
    ));
    html.push_str(&format!(
        "<p>Confidence interval: [{:.3}, {:.3}]</p>\n",
        report.tightness.confidence_interval.0, report.tightness.confidence_interval.1
    ));
    html.push_str(&format!(
        "<p>{killed}/{total} mutants killed, {alive} alive in the ε &lt; {epsilon} neighborhood.</p>\n",
        killed = report.tightness.killed_count,
        total = report.tightness.neighborhood_size,
        alive = report.tightness.alive_count,
        epsilon = report.epsilon,
    ));
    if report.fallback_count > 0 {
        html.push_str(&format!(
            "<p class=\"note\">Z3 returned <code>Unknown</code> on {} queries; model enumeration was used as fallback.</p>\n",
            report.fallback_count
        ));
    }
    html.push_str("</section>\n");

    html.push_str("<section><h2>Parameters</h2>\n<table>\n");
    html.push_str("<tr><th>Spec file</th><td>");
    html.push_str(&escape(&report.spec_path));
    html.push_str("</td></tr>\n");
    html.push_str(&format!(
        "<tr><th>Model bound</th><td>{}</td></tr>\n",
        report.model_bound
    ));
    html.push_str(&format!(
        "<tr><th>Quantifier rank</th><td>{}</td></tr>\n",
        report.quantifier_rank
    ));
    html.push_str(&format!(
        "<tr><th>Epsilon</th><td>{}</td></tr>\n",
        report.epsilon
    ));
    html.push_str(&format!(
        "<tr><th>Seed</th><td>{}</td></tr>\n",
        report.seed
    ));
    html.push_str(&format!(
        "<tr><th>Models enumerated</th><td>{}</td></tr>\n",
        report.models_enumerated
    ));
    html.push_str(&format!(
        "<tr><th>Evaluator</th><td>{}</td></tr>\n",
        if report.cegis { "CEGIS" } else { "Exhaustive" }
    ));
    html.push_str(&format!(
        "<tr><th>Entailment</th><td>{}</td></tr>\n",
        if report.smt {
            "Z3 SMT (hybrid)"
        } else {
            "Model enumeration"
        }
    ));
    html.push_str("</table>\n</section>\n");

    html.push_str("<section><h2>Signature</h2>\n<table>\n");
    html.push_str("<tr><th>Sorts</th><td>");
    html.push_str(&escape(
        &report
            .signature
            .sorts
            .iter()
            .map(|s| s.name.clone())
            .collect::<Vec<_>>()
            .join(", "),
    ));
    html.push_str("</td></tr>\n");
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
        html.push_str(&format!(
            "<tr><th>Relations</th><td>{}</td></tr>\n",
            escape(&rels.join(", "))
        ));
    }
    if !report.signature.functions.is_empty() {
        let funs: Vec<String> = report
            .signature
            .functions
            .iter()
            .map(|f| {
                format!(
                    "{}({}) → {}",
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
        html.push_str(&format!(
            "<tr><th>Functions</th><td>{}</td></tr>\n",
            escape(&funs.join(", "))
        ));
    }
    html.push_str("</table>\n</section>\n");

    html.push_str("<section><h2>Decomposition</h2>\n<ol>\n");
    for f in &report.mutation.decomposition {
        html.push_str(&format!(
            "<li><code>{}</code></li>\n",
            escape(&specmut_parser::fol_parser::format_formula(f))
        ));
    }
    html.push_str("</ol>\n</section>\n");

    html.push_str("<section><h2>Mutants</h2>\n<table>\n");
    html.push_str("<tr><th>Index</th><th>Class</th><th>Component</th><th>Distance</th><th>Status</th></tr>\n");
    for status in &report.tightness.mutant_statuses {
        let mutant = match report.mutation.mutants.get(status.mutant_index) {
            Some(m) => m,
            None => continue,
        };
        let (status_text, status_class) = if status.killed {
            ("killed", "killed")
        } else {
            ("alive", "alive")
        };
        html.push_str(&format!(
            "<tr><td>{idx}</td><td>{cls:?}</td><td>{comp}</td><td>{dist:.3}</td><td class=\"{status_class}\">{status_text}</td></tr>\n",
            idx = status.mutant_index,
            cls = mutant.class,
            comp = mutant.perturbed_component,
            dist = mutant.distance,
        ));
    }
    html.push_str("</table>\n</section>\n");

    let alive_mutants: Vec<&Mutant> = report
        .tightness
        .mutant_statuses
        .iter()
        .filter(|s| !s.killed)
        .filter_map(|s| report.mutation.mutants.get(s.mutant_index))
        .collect();
    if !alive_mutants.is_empty() {
        html.push_str("<section><h2>Alive mutant details</h2>\n<ul>\n");
        for m in alive_mutants {
            html.push_str(&format!(
                "<li>{class:?} (component [{comp}], d = {dist:.3}): {summary}</li>\n",
                class = m.class,
                comp = m.perturbed_component,
                dist = m.distance,
                summary = escape(&render_alive_summary(m)),
            ));
        }
        html.push_str("</ul>\n</section>\n");
    }

    html.push_str("<section><h2>Timing</h2>\n<table>\n");
    html.push_str(&format!(
        "<tr><th>Parse</th><td>{} ms</td></tr>\n",
        report.timing.parse_ms
    ));
    html.push_str(&format!(
        "<tr><th>Enumeration</th><td>{} ms</td></tr>\n",
        report.timing.enumeration_ms
    ));
    html.push_str(&format!(
        "<tr><th>Mutation</th><td>{} ms</td></tr>\n",
        report.timing.mutation_ms
    ));
    html.push_str(&format!(
        "<tr><th>Tightness</th><td>{} ms</td></tr>\n",
        report.timing.tightness_ms
    ));
    html.push_str(&format!(
        "<tr><th>Total</th><td>{} ms</td></tr>\n",
        report.timing.total_ms
    ));
    html.push_str("</table>\n</section>\n");

    html.push_str("<footer><p>specmut v0.1.0 — fallback HTML report (no diagrams).</p></footer>\n");
    html.push_str("</body>\n</html>\n");
    html
}

fn render_alive_summary(m: &Mutant) -> String {
    let render = specmut_parser::fol_parser::format_formula;
    match m.class {
        MutantClass::Weakening => {
            m.original_predicate.as_ref().map_or_else(
                || "weakening".to_string(),
                |f: &Formula| format!("removed {}", render(f)),
            )
        }
        MutantClass::Strengthening => m.replacement_predicate.as_ref().map_or_else(
            || "strengthening".to_string(),
            |f| format!("added {}", render(f)),
        ),
        MutantClass::Replacement => match (&m.original_predicate, &m.replacement_predicate) {
            (Some(orig), Some(repl)) => {
                format!("replaced {} with {}", render(orig), render(repl))
            }
            _ => "replacement".to_string(),
        },
    }
}

fn score_color_class(score: f64) -> &'static str {
    if score >= 0.8 {
        "high"
    } else if score >= 0.5 {
        "mid"
    } else {
        "low"
    }
}

fn escape(s: &str) -> String {
    s.replace('&', "&amp;")
        .replace('<', "&lt;")
        .replace('>', "&gt;")
        .replace('"', "&quot;")
}

const FALLBACK_CSS: &str = r#"
body { font-family: -apple-system, BlinkMacSystemFont, sans-serif; max-width: 900px; margin: 2em auto; padding: 0 1em; color: #2c3e50; }
h1 { border-bottom: 2px solid #2c3e50; padding-bottom: 0.3em; }
h2 { margin-top: 2em; }
section { margin-bottom: 2em; }
.score { font-size: 3em; font-weight: bold; margin: 0.2em 0; }
.score.high { color: #27ae60; }
.score.mid { color: #f39c12; }
.score.low { color: #e74c3c; }
table { border-collapse: collapse; width: 100%; }
th, td { padding: 8px 12px; border: 1px solid #ddd; text-align: left; }
th { background: #2c3e50; color: white; }
tr:nth-child(even) td { background: #f9f9f9; }
.killed { color: #27ae60; font-weight: 600; }
.alive { color: #e74c3c; font-weight: 600; }
.note { background: #fff3cd; border-left: 4px solid #f39c12; padding: 0.5em 1em; }
code { font-family: ui-monospace, Menlo, monospace; }
footer { border-top: 1px solid #ddd; margin-top: 3em; padding-top: 1em; color: #95a5a6; font-size: 0.9em; }
"#;

#[cfg(test)]
mod tests {
    use super::*;
    use specmut_core::cegis::CegisState;
    use specmut_core::formula::{Formula, Term};
    use specmut_core::lattice::SpecElement;
    use specmut_core::model::FiniteModel;
    use specmut_core::mutation::{Mutant, MutantClass, MutationResult};
    use specmut_core::signature::{RelationSymbol, Signature, SortSymbol};
    use specmut_core::tightness::{MutantStatus, TightnessResult};

    use crate::output::{Report, TimingBreakdown};

    fn fake_setup() -> (
        Signature,
        Vec<Formula>,
        SpecElement,
        MutationResult,
        TightnessResult,
    ) {
        let s = SortSymbol::new("S");
        let sig = Signature::new(
            vec![s.clone()],
            vec![],
            vec![RelationSymbol::new("P", vec![s.clone()])],
        )
        .expect("valid sig");
        let phi = Formula::Forall {
            sort: s.clone(),
            body: Box::new(Formula::Atom {
                relation: RelationSymbol::new("P", vec![s.clone()]),
                args: vec![Term::Var(0)],
            }),
        };
        let axioms = vec![phi.clone()];
        let spec = SpecElement::from_axioms([phi.clone()]);
        let empty: Vec<Formula> = Vec::new();
        let mutant = Mutant {
            spec: SpecElement::from_axioms(empty),
            class: MutantClass::Weakening,
            perturbed_component: 0,
            original_predicate: Some(phi.clone()),
            replacement_predicate: None,
            distance: 0.42,
        };
        let mutation = MutationResult {
            decomposition: vec![phi],
            mutants: vec![mutant],
            neighborhood_mutants: vec![0],
            total_generated: 1,
            total_in_neighborhood: 1,
            by_class: [(MutantClass::Weakening, 1usize)].into_iter().collect(),
        };
        let tightness = TightnessResult {
            score: 0.0,
            confidence_interval: (0.0, 0.0),
            exhaustive: true,
            neighborhood_size: 1,
            killed_count: 0,
            alive_count: 1,
            mutant_statuses: vec![MutantStatus {
                mutant_index: 0,
                killed: false,
                killing_implementations: vec![],
                direction: None,
                witness: None,
            }],
        };
        let _ = CegisState {
            unchecked: Default::default(),
            killed: Default::default(),
            alive: Default::default(),
            counterexamples: vec![],
            iterations: 0,
            pruned: 0,
        };
        let _ = FiniteModel {
            signature: sig.clone(),
            carriers: Default::default(),
            function_interps: Default::default(),
            relation_interps: Default::default(),
        };
        (sig, axioms, spec, mutation, tightness)
    }

    #[test]
    fn test_fallback_html_valid() {
        let (sig, axioms, _spec, mutation, tightness) = fake_setup();
        let report = Report {
            spec_path: "test.fol".to_string(),
            model_bound: 2,
            quantifier_rank: 1,
            epsilon: 0.5,
            seed: 42,
            models_enumerated: 4,
            signature: &sig,
            axioms: &axioms,
            mutation: &mutation,
            tightness: &tightness,
            cegis: false,
            smt: false,
            fallback_count: 0,
            timing: TimingBreakdown::default(),
            lean_translation: None,
        };
        let html = generate_fallback_html(&report);
        assert!(html.starts_with("<!DOCTYPE html>"), "missing doctype");
        assert!(
            html.contains("τ = 0.000"),
            "missing score line:\n{html}"
        );
        // One alive mutant → at least one alive-class table cell.
        assert!(html.contains("class=\"alive\""), "missing alive row");
    }

    #[test]
    fn test_score_color_class() {
        assert_eq!(score_color_class(0.9), "high");
        assert_eq!(score_color_class(0.6), "mid");
        assert_eq!(score_color_class(0.3), "low");
        assert_eq!(score_color_class(0.8), "high");
        assert_eq!(score_color_class(0.5), "mid");
    }

    #[test]
    fn test_html_includes_fallback_note() {
        let (sig, axioms, _spec, mutation, tightness) = fake_setup();
        let report = Report {
            spec_path: "test.fol".to_string(),
            model_bound: 2,
            quantifier_rank: 1,
            epsilon: 0.5,
            seed: 42,
            models_enumerated: 4,
            signature: &sig,
            axioms: &axioms,
            mutation: &mutation,
            tightness: &tightness,
            cegis: false,
            smt: true,
            fallback_count: 3,
            timing: TimingBreakdown::default(),
            lean_translation: None,
        };
        let html = generate_fallback_html(&report);
        assert!(html.contains("3 queries"), "fallback note missing");
    }
}
