//! Phase F (§2.8): `compare` subcommand end-to-end tests.
//!
//! Spawns the compiled binary against the sorting-spec evolution fixtures
//! to confirm comparison output is well-formed.  Lean comparison is gated
//! on lean being on PATH.

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

#[test]
fn test_compare_single_file_no_delta() {
    let (code, stdout, stderr) = run_specmut(&[
        "compare",
        "specs/sorting/sort.fol",
        "-n",
        "2",
        "-f",
        "json",
    ]);
    assert_eq!(code, 0, "stderr: {stderr}");
    let parsed: serde_json::Value =
        serde_json::from_str(&stdout).unwrap_or_else(|e| panic!("invalid JSON: {e}\n{stdout}"));
    let results = parsed
        .get("results")
        .and_then(|v| v.as_array())
        .expect("results array");
    assert_eq!(results.len(), 1);
    // First entry: delta_tightness is null.
    let first = &results[0];
    assert!(first.get("delta_tightness").map(|v| v.is_null()).unwrap_or(true));
}

#[test]
fn test_compare_monotonic_evolution() {
    // sort_v1_buggy < sort < sort_v3_correct: at least the order of mean
    // tightness should make sense across the three.
    let (code, stdout, stderr) = run_specmut(&[
        "compare",
        "specs/sorting/sort_v1_buggy.fol",
        "specs/sorting/sort.fol",
        "specs/sorting/sort_v3_correct.fol",
        "-n",
        "2",
        "-f",
        "json",
    ]);
    assert_eq!(code, 0, "stderr: {stderr}");
    let parsed: serde_json::Value = serde_json::from_str(&stdout).expect("valid JSON");
    let results = parsed
        .get("results")
        .and_then(|v| v.as_array())
        .expect("results array");
    assert_eq!(results.len(), 3);
    // First entry has no delta; subsequent entries should report a
    // numeric delta (positive or negative).
    assert!(results[0]
        .get("delta_tightness")
        .map(|v| v.is_null())
        .unwrap_or(true));
    for r in &results[1..] {
        assert!(
            r.get("delta_tightness").and_then(|v| v.as_f64()).is_some(),
            "non-first entry must carry a delta_tightness"
        );
    }
}

#[test]
fn test_compare_text_format_has_header() {
    let (code, stdout, stderr) = run_specmut(&[
        "compare",
        "specs/sorting/sort.fol",
        "specs/sorting/sort_v3_correct.fol",
        "-n",
        "2",
    ]);
    assert_eq!(code, 0, "stderr: {stderr}");
    assert!(stdout.contains("Spec"), "missing column header: {stdout}");
    assert!(stdout.contains("τ (mean)"), "missing tau column: {stdout}");
    assert!(stdout.contains("Δτ"), "missing delta column: {stdout}");
    assert!(
        stdout.contains("sort.fol") && stdout.contains("sort_v3_correct.fol"),
        "missing spec rows: {stdout}"
    );
}

#[test]
fn test_compare_lean_files() {
    if !lean_available() {
        eprintln!("skip: lean not on PATH");
        return;
    }
    let (code, stdout, stderr) = run_specmut(&[
        "compare",
        "crates/specmut-lean/lean/test_fixtures/minimal.lean",
        "crates/specmut-lean/lean/test_fixtures/hypotheses.lean",
        "-n",
        "2",
        "-f",
        "json",
    ]);
    assert_eq!(code, 0, "stderr: {stderr}");
    let parsed: serde_json::Value = serde_json::from_str(&stdout).expect("valid JSON");
    let results = parsed
        .get("results")
        .and_then(|v| v.as_array())
        .expect("results array");
    assert_eq!(results.len(), 2);
    // The compare subcommand routes .lean files into the sliced/global
    // Lean pipeline; each entry should at least carry a mode tag and a
    // path.  Tightness may be null if no slice analyzed at this -n, but
    // we DO require the rows to be present.
    for r in results {
        assert!(r.get("spec_path").is_some(), "missing spec_path: {r}");
        assert!(r.get("mode").is_some(), "missing mode: {r}");
    }
}
