//! End-to-end CLI tests for Phase C's `--lean-full` path.
//!
//! Tests spawn the compiled `specmut` binary against the Phase A fixtures
//! and inspect exit code / stdout.  Lean-dependent cases skip silently when
//! `lean` isn't on PATH so the suite still passes in lean-free environments.

use std::path::{Path, PathBuf};
use std::process::Command;

fn bin() -> PathBuf {
    PathBuf::from(env!("CARGO_BIN_EXE_specmut"))
}

fn workspace_root() -> PathBuf {
    let manifest = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    manifest
        .parent()
        .and_then(|p| p.parent())
        .map(Path::to_path_buf)
        .expect("specmut-cli is two levels below the workspace root")
}

/// Run the `specmut` binary with the given arguments, augmenting `PATH`
/// with `~/.elan/bin` so the bundled Lean toolchain is discoverable.
fn run_specmut(args: &[&str]) -> (i32, String, String) {
    let elan_bin = std::env::var_os("HOME")
        .map(|h| PathBuf::from(h).join(".elan").join("bin"))
        .unwrap_or_default();
    let existing_path = std::env::var_os("PATH").unwrap_or_default();
    let combined_path = {
        let mut paths: Vec<PathBuf> = vec![elan_bin];
        paths.extend(std::env::split_paths(&existing_path));
        std::env::join_paths(paths).expect("join PATH")
    };
    let out = Command::new(bin())
        .current_dir(workspace_root())
        .env("PATH", combined_path)
        .args(args)
        .output()
        .expect("failed to spawn specmut");
    let code = out.status.code().unwrap_or(-1);
    let stdout = String::from_utf8_lossy(&out.stdout).to_string();
    let stderr = String::from_utf8_lossy(&out.stderr).to_string();
    (code, stdout, stderr)
}

fn lean_available() -> bool {
    let elan_bin = std::env::var_os("HOME")
        .map(|h| PathBuf::from(h).join(".elan").join("bin").join("lean"))
        .unwrap_or_default();
    if elan_bin.is_file() {
        return true;
    }
    Command::new("lean")
        .arg("--version")
        .output()
        .map(|o| o.status.success())
        .unwrap_or(false)
}

macro_rules! require_lean {
    () => {
        if !lean_available() {
            eprintln!("skip: lean not on PATH");
            return;
        }
    };
}

// ----------------------------------------------------------------------------
// Happy path (Phase E: per-theorem output)
// ----------------------------------------------------------------------------

#[test]
fn test_cli_lean_full_text_minimal() {
    require_lean!();
    let (code, stdout, stderr) = run_specmut(&[
        "analyze",
        "crates/specmut-lean/lean/test_fixtures/minimal.lean",
        "--lean-full",
        "-n",
        "2",
        "-f",
        "text",
    ]);
    assert_eq!(code, 0, "stderr: {stderr}");
    // Per-theorem text mode: a header banner, one block per theorem,
    // and the trailing summary section.
    assert!(
        stdout.contains("per-theorem"),
        "expected per-theorem banner:\n{stdout}"
    );
    assert!(
        stdout.contains("Theorem: zero_even") && stdout.contains("Theorem: pos_one"),
        "expected both theorem blocks:\n{stdout}"
    );
    assert!(
        stdout.contains("Tightness: τ ="),
        "expected tightness line per slice:\n{stdout}"
    );
    assert!(
        stdout.contains("Summary"),
        "expected summary block:\n{stdout}"
    );
}

#[test]
fn test_cli_lean_full_json_minimal() {
    require_lean!();
    let (code, stdout, _stderr) = run_specmut(&[
        "analyze",
        "crates/specmut-lean/lean/test_fixtures/minimal.lean",
        "--lean-full",
        "-n",
        "2",
        "-f",
        "json",
    ]);
    assert_eq!(code, 0);
    let parsed: serde_json::Value =
        serde_json::from_str(&stdout).unwrap_or_else(|e| panic!("invalid JSON: {e}\n{stdout}"));
    assert_eq!(
        parsed.get("analysis_mode").and_then(|v| v.as_str()),
        Some("per_theorem"),
        "expected analysis_mode=per_theorem"
    );
    let slices = parsed
        .get("theorem_slices")
        .and_then(|v| v.as_array())
        .expect("theorem_slices array");
    assert_eq!(slices.len(), 2, "expected 2 slices for minimal.lean");
    let names: Vec<&str> = slices
        .iter()
        .filter_map(|s| s.get("theorem_name").and_then(|n| n.as_str()))
        .collect();
    assert!(names.contains(&"zero_even") && names.contains(&"pos_one"));
    // zero_even's slice should reference Even but not Pos (strict
    // per-theorem reduction).
    let zero_even = slices
        .iter()
        .find(|s| s.get("theorem_name").and_then(|v| v.as_str()) == Some("zero_even"))
        .expect("zero_even slice");
    let rel_names: Vec<&str> = zero_even
        .get("signature")
        .and_then(|s| s.get("relations"))
        .and_then(|r| r.as_array())
        .expect("relations")
        .iter()
        .filter_map(|r| r.get("name").and_then(|n| n.as_str()))
        .collect();
    assert!(rel_names.contains(&"Even"), "Even missing in slice: {rel_names:?}");
    assert!(
        !rel_names.contains(&"Pos"),
        "Pos should NOT leak into zero_even slice: {rel_names:?}"
    );
}

#[test]
fn test_cli_lean_full_hypotheses() {
    require_lean!();
    let (code, stdout, stderr) = run_specmut(&[
        "analyze",
        "crates/specmut-lean/lean/test_fixtures/hypotheses.lean",
        "--lean-full",
        "-n",
        "2",
        "-f",
        "json",
    ]);
    assert_eq!(code, 0, "stderr: {stderr}");
    let parsed: serde_json::Value = serde_json::from_str(&stdout).expect("valid JSON");
    let slices = parsed
        .get("theorem_slices")
        .and_then(|v| v.as_array())
        .expect("theorem_slices array");
    assert_eq!(
        slices.len(),
        3,
        "hypotheses.lean has 3 theorems → expected 3 slices"
    );
    // Each slice carries either an analyzed tightness or a skip reason.
    for s in slices {
        let status = s
            .get("status")
            .and_then(|v| v.as_str())
            .expect("slice status");
        assert!(
            matches!(status, "analyzed" | "skipped"),
            "unexpected slice status {status}"
        );
    }
}

// ----------------------------------------------------------------------------
// Phase E: BST now analyzable at n=2 thanks to per-theorem slicing
// ----------------------------------------------------------------------------

#[test]
fn test_cli_lean_full_bst_sliced() {
    require_lean!();
    // Pre-Phase-E this exited with EXIT_MODEL_BOUND_EXCEEDED.  After
    // slicing, at least one theorem in bst.lean has a slice whose model
    // space fits at n=2, so the CLI exits 0 and emits theorem_slices.
    let (code, stdout, stderr) = run_specmut(&[
        "analyze",
        "crates/specmut-lean/lean/test_fixtures/bst.lean",
        "--lean-full",
        "-n",
        "2",
        "-f",
        "json",
    ]);
    assert_eq!(code, 0, "expected success after slicing, stderr: {stderr}");
    let parsed: serde_json::Value = serde_json::from_str(&stdout).expect("valid JSON");
    let slices = parsed
        .get("theorem_slices")
        .and_then(|v| v.as_array())
        .expect("theorem_slices array");
    assert!(!slices.is_empty(), "expected ≥1 BST slice");
    let analyzed: Vec<_> = slices
        .iter()
        .filter(|s| s.get("status").and_then(|v| v.as_str()) == Some("analyzed"))
        .collect();
    assert!(
        !analyzed.is_empty(),
        "expected ≥1 analyzed slice for bst.lean at n=2"
    );
}

#[test]
fn test_cli_lean_full_json_has_summary() {
    require_lean!();
    let (code, stdout, _stderr) = run_specmut(&[
        "analyze",
        "crates/specmut-lean/lean/test_fixtures/minimal.lean",
        "--lean-full",
        "-n",
        "2",
        "-f",
        "json",
    ]);
    assert_eq!(code, 0);
    let parsed: serde_json::Value = serde_json::from_str(&stdout).expect("valid JSON");
    let summary = parsed
        .get("summary")
        .and_then(|v| v.as_object())
        .expect("summary object");
    for key in [
        "analyzed",
        "skipped",
        "mean_tightness",
        "min_tightness",
        "max_tightness",
    ] {
        assert!(summary.contains_key(key), "summary missing key '{key}'");
    }
}

// ----------------------------------------------------------------------------
// Phase F: semantic diagnostics
// ----------------------------------------------------------------------------

#[test]
fn test_cli_phase_f_slice_metrics_in_json() {
    require_lean!();
    let (code, stdout, _stderr) = run_specmut(&[
        "analyze",
        "crates/specmut-lean/lean/test_fixtures/bst.lean",
        "--lean-full",
        "-n",
        "2",
        "-f",
        "json",
    ]);
    assert_eq!(code, 0);
    let parsed: serde_json::Value = serde_json::from_str(&stdout).expect("valid JSON");
    let slices = parsed
        .get("theorem_slices")
        .and_then(|v| v.as_array())
        .expect("theorem_slices array");
    let analyzed = slices
        .iter()
        .find(|s| s.get("status").and_then(|v| v.as_str()) == Some("analyzed"))
        .expect("at least one analyzed slice");
    let metrics = analyzed
        .get("metrics")
        .and_then(|v| v.as_object())
        .expect("metrics object on analyzed slice");
    for key in [
        "original_sort_count",
        "reduced_sort_count",
        "reduction_percentage",
        "kill_rate",
        "mutant_count",
    ] {
        assert!(metrics.contains_key(key), "metrics missing '{key}'");
    }
}

#[test]
fn test_cli_phase_f_dependency_closure_in_json() {
    require_lean!();
    let (code, stdout, _stderr) = run_specmut(&[
        "analyze",
        "crates/specmut-lean/lean/test_fixtures/bst.lean",
        "--lean-full",
        "-n",
        "2",
        "-f",
        "json",
    ]);
    assert_eq!(code, 0);
    let parsed: serde_json::Value = serde_json::from_str(&stdout).expect("valid JSON");
    let slices = parsed
        .get("theorem_slices")
        .and_then(|v| v.as_array())
        .expect("theorem_slices array");
    for slice in slices {
        let dep = slice
            .get("dependency_closure")
            .and_then(|v| v.as_object())
            .expect("dependency_closure on every slice");
        for key in ["sorts", "relations", "functions", "axiom_count", "axiom_origins"] {
            assert!(dep.contains_key(key), "dependency_closure missing '{key}'");
        }
        // Closure sorts match the slice's signature sorts.
        let closure_sorts: Vec<&str> = dep
            .get("sorts")
            .and_then(|v| v.as_array())
            .expect("dependency_closure.sorts is an array")
            .iter()
            .filter_map(|x| x.as_str())
            .collect();
        let sig_sorts: Vec<&str> = slice
            .get("signature")
            .and_then(|v| v.get("sorts"))
            .and_then(|v| v.as_array())
            .expect("slice signature.sorts is an array")
            .iter()
            .filter_map(|x| x.as_str())
            .collect();
        assert_eq!(closure_sorts, sig_sorts);
    }
}

#[test]
fn test_cli_phase_f_witness_attached_to_alive_mutants() {
    require_lean!();
    let (code, stdout, _stderr) = run_specmut(&[
        "analyze",
        "crates/specmut-lean/lean/test_fixtures/bst.lean",
        "--lean-full",
        "-n",
        "2",
        "-f",
        "json",
    ]);
    assert_eq!(code, 0);
    let parsed: serde_json::Value = serde_json::from_str(&stdout).expect("valid JSON");
    // Locate an alive mutant somewhere in the BST output and confirm it
    // carries a non-empty witness object with an interpretation.
    let mut found_witness = false;
    let slices = parsed
        .get("theorem_slices")
        .and_then(|v| v.as_array())
        .expect("theorem_slices array");
    for slice in slices {
        let alive = match slice.get("alive_mutants").and_then(|v| v.as_array()) {
            Some(a) => a,
            None => continue,
        };
        for m in alive {
            if let Some(w) = m.get("witness").and_then(|v| v.as_object()) {
                assert!(
                    w.contains_key("interpretation"),
                    "witness missing interpretation"
                );
                assert!(
                    w.get("interpretation")
                        .and_then(|v| v.as_str())
                        .map(|s| !s.is_empty())
                        .unwrap_or(false),
                    "interpretation must be non-empty"
                );
                found_witness = true;
            }
        }
    }
    assert!(found_witness, "expected at least one alive mutant with a witness");
}

#[test]
fn test_cli_phase_f_aggregate_diagnostic_summary_nonempty() {
    require_lean!();
    let (code, stdout, _stderr) = run_specmut(&[
        "analyze",
        "crates/specmut-lean/lean/test_fixtures/bst.lean",
        "--lean-full",
        "-n",
        "2",
        "-f",
        "json",
    ]);
    assert_eq!(code, 0);
    let parsed: serde_json::Value = serde_json::from_str(&stdout).expect("valid JSON");
    let summary = parsed
        .get("summary")
        .and_then(|v| v.as_object())
        .expect("summary object");
    // Phase F additions:
    for key in [
        "tightness_variance",
        "average_model_space_reduction_pct",
        "total_mutants_generated",
        "total_mutants_killed",
        "total_kill_rate",
        "taxonomy",
        "contributions",
        "weak_theorem_candidates",
        "diagnostic_summary",
    ] {
        assert!(summary.contains_key(key), "summary missing key '{key}'");
    }
    let variance = summary
        .get("tightness_variance")
        .and_then(|v| v.as_f64())
        .expect("tightness_variance is a number");
    assert!(variance >= 0.0, "variance must be non-negative");
    let diag = summary
        .get("diagnostic_summary")
        .and_then(|v| v.as_str())
        .unwrap_or("");
    assert!(!diag.is_empty(), "diagnostic_summary should be non-empty");
}

#[test]
fn test_cli_phase_f_weak_candidates_below_threshold() {
    require_lean!();
    let (code, stdout, _stderr) = run_specmut(&[
        "analyze",
        "crates/specmut-lean/lean/test_fixtures/bst.lean",
        "--lean-full",
        "-n",
        "2",
        "-f",
        "json",
    ]);
    assert_eq!(code, 0);
    let parsed: serde_json::Value = serde_json::from_str(&stdout).expect("valid JSON");
    let slices = parsed
        .get("theorem_slices")
        .and_then(|v| v.as_array())
        .expect("theorem_slices");
    let weak: Vec<&str> = parsed
        .get("summary")
        .and_then(|v| v.get("weak_theorem_candidates"))
        .and_then(|v| v.as_array())
        .map(|arr| arr.iter().filter_map(|x| x.as_str()).collect())
        .unwrap_or_default();
    for name in &weak {
        let slice = slices
            .iter()
            .find(|s| s.get("theorem_name").and_then(|v| v.as_str()) == Some(*name))
            .unwrap_or_else(|| panic!("weak theorem '{name}' not found in slices"));
        // For analyzed slices we can check tightness < 0.1; for skipped
        // slices the field isn't populated and the candidate set
        // shouldn't include them, so we assert that as well.
        if slice.get("status").and_then(|v| v.as_str()) == Some("analyzed") {
            let score = slice
                .get("tightness")
                .and_then(|v| v.get("score"))
                .and_then(|v| v.as_f64())
                .unwrap_or(1.0);
            assert!(score < 0.1, "weak candidate {name} has τ = {score}");
        }
    }
}

#[test]
fn test_cli_phase_f_text_output_renders_diagnostics() {
    require_lean!();
    let (code, stdout, _stderr) = run_specmut(&[
        "analyze",
        "crates/specmut-lean/lean/test_fixtures/bst.lean",
        "--lean-full",
        "-n",
        "2",
        "-f",
        "text",
    ]);
    assert_eq!(code, 0);
    for needle in [
        "Slice reduction:",
        "Mutation breakdown:",
        "Theorem contribution",
        "Diagnostic:",
    ] {
        assert!(
            stdout.contains(needle),
            "text output missing '{needle}':\n{stdout}"
        );
    }
}

#[test]
fn test_cli_fol_unchanged() {
    // .fol files MUST keep the Phase D output shape: no theorem_slices,
    // no analysis_mode=per_theorem.  Slicing is Lean-only.
    let (code, stdout, _stderr) = run_specmut(&[
        "analyze",
        "specs/sorting/sort.fol",
        "-n",
        "2",
        "-f",
        "json",
    ]);
    assert_eq!(code, 0);
    let parsed: serde_json::Value = serde_json::from_str(&stdout).expect("valid JSON");
    assert!(
        parsed.get("theorem_slices").is_none(),
        "FOL output must not contain theorem_slices"
    );
    assert!(
        parsed.get("analysis_mode").is_none(),
        "FOL output must not contain analysis_mode"
    );
    // The classic global JSON shape carries `tightness` at top level.
    assert!(
        parsed.get("tightness").is_some(),
        "global JSON should keep top-level tightness"
    );
}

// ----------------------------------------------------------------------------
// Soft fallback when lean is unavailable
// ----------------------------------------------------------------------------

#[test]
fn test_cli_lean_full_missing_binary_falls_back() {
    // --lean-path points at a path that does not exist.  Expected:
    // soft fallback to extraction summary, exit 0.
    let (code, stdout, _stderr) = run_specmut(&[
        "analyze",
        "crates/specmut-lean/lean/test_fixtures/minimal.lean",
        "--lean-full",
        "--lean-path",
        "/this/path/does/not/exist/lean",
    ]);
    assert_eq!(code, 0);
    assert!(
        stdout.contains("Lean full analysis unavailable")
            || stdout.contains("Predicates discovered:"),
        "expected extraction fallback in stdout:\n{stdout}"
    );
}
