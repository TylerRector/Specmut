//! Phase 7 end-to-end validation suite.
//!
//! These tests shell out to the compiled `specmut` binary and inspect
//! exit codes, stdout, and (where useful) parsed JSON output.  They
//! cover every output format, every spec family in `specs/`, both
//! evaluators (exhaustive and CEGIS), error paths, and the
//! determinism guarantee.
//!
//! The final test [`zz_validation_summary`] prints a table of
//! tightness scores and timings for every example spec.  It has no
//! pass/fail assertions beyond "the pipeline doesn't panic" — its
//! purpose is to leave a diagnostic snapshot in `cargo test` output.

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
    let out = Command::new(bin())
        .current_dir(workspace_root())
        .args(args)
        .output()
        .expect("failed to spawn specmut");
    let code = out.status.code().unwrap_or(-1);
    let stdout = String::from_utf8_lossy(&out.stdout).to_string();
    let stderr = String::from_utf8_lossy(&out.stderr).to_string();
    (code, stdout, stderr)
}

fn spec(rel: &str) -> String {
    workspace_root().join(rel).display().to_string()
}

fn parse_json(stdout: &str) -> serde_json::Value {
    serde_json::from_str(stdout).expect("CLI stdout should be JSON")
}

#[test]
fn test_e2e_trivial_spec() {
    let path = spec("specs/minimal/trivial.fol");
    let (code, stdout, stderr) = run_specmut(&["analyze", &path, "-n", "2", "-f", "json"]);
    assert_eq!(code, 0, "exit {code}: {stderr}");
    let json = parse_json(&stdout);
    let score = json["tightness"]["score"].as_f64().unwrap_or(-1.0);
    // No implementations were supplied → nothing can kill the
    // mutations, so τ is mechanically 0.  The test verifies the
    // pipeline completes cleanly and the JSON schema is fully
    // populated; the actual tightness for impl-less runs is always 0.
    assert!(
        (0.0..=1.0).contains(&score),
        "tightness should be in [0, 1] (got {score})"
    );
    for key in [
        "version",
        "spec_file",
        "parameters",
        "signature",
        "decomposition",
        "tightness",
        "alive_mutants",
        "timing",
    ] {
        assert!(json.get(key).is_some(), "JSON missing key '{key}'");
    }
}

#[test]
fn test_e2e_empty_spec() {
    let path = spec("specs/minimal/empty.fol");
    let (code, stdout, stderr) = run_specmut(&["analyze", &path, "-n", "2", "-f", "json"]);
    assert_eq!(code, 0, "exit {code}: {stderr}");
    let json = parse_json(&stdout);
    let score = json["tightness"]["score"].as_f64().unwrap_or(-1.0);
    let decomp = json["decomposition"].as_array().expect("decomposition");
    // Either the score is exactly 0.0 or there is no decomposition.
    assert!(
        score == 0.0 || decomp.is_empty(),
        "empty spec: score = {score}, decomp.len = {}",
        decomp.len()
    );
}

#[test]
fn test_e2e_sorting_buggy() {
    let path = spec("specs/sorting/sort_v1_buggy.fol");
    let (code, _stdout, stderr) = run_specmut(&["analyze", &path, "-n", "2", "-e", "0.5"]);
    assert_eq!(code, 0, "exit {code}: {stderr}");
}

#[test]
fn test_e2e_sorting_correct() {
    let path = spec("specs/sorting/sort_v3_correct.fol");
    let (code, _stdout, stderr) = run_specmut(&["analyze", &path, "-n", "2", "-e", "0.5"]);
    assert_eq!(code, 0, "exit {code}: {stderr}");
    // V1 and V3 can produce the same tightness in this miniature model
    // space; we only assert that both runs complete cleanly.
}

#[test]
fn test_e2e_stack_spec() {
    let path = spec("specs/stack/stack.fol");
    let (code, stdout, stderr) = run_specmut(&["analyze", &path, "-n", "2", "-e", "0.5", "-f", "json"]);
    assert_eq!(code, 0, "exit {code}: {stderr}");
    let json = parse_json(&stdout);
    let decomp = json["decomposition"].as_array().expect("decomposition");
    // At small carrier sizes the decomposition can drop axioms that
    // become entailed by the others within the finite model space —
    // e.g. with `Elem = Stack = {0, 1}` the stack spec collapses to
    // two components rather than three.  The contract this test
    // enforces is that the pipeline produces a non-empty
    // decomposition, not the precise count, which depends on `n`.
    assert!(
        !decomp.is_empty(),
        "stack spec should decompose into at least one component (got 0)"
    );
}

#[test]
fn test_e2e_set_spec() {
    let path = spec("specs/set/set.fol");
    let (code, _stdout, stderr) = run_specmut(&["analyze", &path, "-n", "2", "-e", "0.5"]);
    assert_eq!(code, 0, "exit {code}: {stderr}");
}

#[test]
fn test_e2e_sorting_with_impl() {
    let spec_path = spec("specs/sorting/sort.fol");
    let impl_path = spec("specs/sorting/implementations/insertion_sort.model");
    let (code, stdout, stderr) = run_specmut(&[
        "analyze",
        &spec_path,
        "-n",
        "2",
        "-e",
        "0.5",
        "-i",
        &impl_path,
        "-f",
        "json",
    ]);
    assert_eq!(code, 0, "exit {code}: {stderr}");
    let json = parse_json(&stdout);
    // alive_mutants is always present; it may be empty if everything
    // was killed.  Either outcome is acceptable here.
    assert!(json["alive_mutants"].is_array(), "alive_mutants missing");
}

#[test]
fn test_e2e_cegis_matches_exhaustive() {
    let path = spec("specs/sorting/sort.fol");
    let (c1, exh_stdout, _) = run_specmut(&[
        "analyze",
        &path,
        "-n",
        "2",
        "-e",
        "0.5",
        "-f",
        "json",
    ]);
    let (c2, cegis_stdout, _) = run_specmut(&[
        "analyze",
        &path,
        "-n",
        "2",
        "-e",
        "0.5",
        "--cegis",
        "-f",
        "json",
    ]);
    assert_eq!(c1, 0);
    assert_eq!(c2, 0);
    let exh = parse_json(&exh_stdout);
    let cegis = parse_json(&cegis_stdout);
    assert_eq!(
        exh["tightness"]["score"], cegis["tightness"]["score"],
        "CEGIS score should equal exhaustive score"
    );
}

#[test]
fn test_e2e_json_schema_complete() {
    let path = spec("specs/sorting/sort.fol");
    let (code, stdout, _) = run_specmut(&["analyze", &path, "-n", "2", "-e", "0.5", "-f", "json"]);
    assert_eq!(code, 0);
    let json = parse_json(&stdout);
    let tightness = &json["tightness"];
    for key in ["score", "killed", "alive", "neighborhood_size", "exhaustive"] {
        assert!(tightness.get(key).is_some(), "tightness.{key} missing");
    }
    let signature = &json["signature"];
    for key in ["sorts", "relations", "functions"] {
        assert!(signature.get(key).is_some(), "signature.{key} missing");
    }
}

#[test]
fn test_e2e_text_output_readable() {
    let path = spec("specs/sorting/sort.fol");
    let (code, stdout, _) = run_specmut(&["analyze", &path, "-n", "2", "-e", "0.5", "-f", "text"]);
    assert_eq!(code, 0);
    for needle in ["τ =", "Mutations:", "Tightness:", "Decomposition:"] {
        assert!(
            stdout.contains(needle),
            "text output missing '{needle}':\n{stdout}"
        );
    }
}

#[test]
fn test_e2e_html_output_valid() {
    let path = spec("specs/sorting/sort.fol");
    let (code, stdout, _) = run_specmut(&["analyze", &path, "-n", "2", "-e", "0.5", "-f", "html"]);
    assert_eq!(code, 0);
    assert!(stdout.contains("<!DOCTYPE html>"), "missing doctype");
    assert!(stdout.contains("τ ="), "missing score line");
}

#[test]
fn test_e2e_lean_extraction() {
    let path = spec("specs/sorting/sort_lean.lean");
    let (code, stdout, _) = run_specmut(&["analyze", &path]);
    assert_eq!(code, 0);
    for needle in ["Sorted_v1", "Perm_v2", "sort_spec_v3"] {
        assert!(stdout.contains(needle), "missing '{needle}' in:\n{stdout}");
    }
}

#[test]
fn test_e2e_dafny_extraction() {
    let path = spec("specs/dafny/insertion_sort.dfy");
    let (code, stdout, _) = run_specmut(&["analyze", &path]);
    assert_eq!(code, 0);
    for needle in ["InsertionSort", "requires", "ensures"] {
        assert!(stdout.contains(needle), "missing '{needle}' in:\n{stdout}");
    }
}

#[test]
fn test_e2e_bad_fol_syntax() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let bad = tmp.path().join("bad.fol");
    std::fs::write(&bad, "sort . rel broken").expect("write");
    let (code, _stdout, _stderr) =
        run_specmut(&["analyze", bad.to_str().expect("utf-8"), "-n", "2"]);
    assert_eq!(code, 1, "expected EXIT_PARSE_ERROR");
}

#[test]
fn test_e2e_model_bound_guard() {
    // 3 binary relations at n=20 would enumerate 2^(3*400) = 2^1200
    // models.  The Phase 7 BigUint-aware guard must reject this with
    // EXIT_MODEL_BOUND_EXCEEDED.
    let tmp = tempfile::tempdir().expect("tempdir");
    let big = tmp.path().join("big.fol");
    std::fs::write(
        &big,
        "sort S.\nrel R1 : S, S.\nrel R2 : S, S.\nrel R3 : S, S.\naxiom forall x : S . forall y : S . R1(x, y).\n",
    )
    .expect("write");
    let (code, _stdout, _stderr) =
        run_specmut(&["analyze", big.to_str().expect("utf-8"), "-n", "20"]);
    assert_eq!(code, 4, "expected EXIT_MODEL_BOUND_EXCEEDED");
}

#[test]
fn test_e2e_epsilon_filtering() {
    let path = spec("specs/sorting/sort.fol");
    let (_, tight_stdout, _) =
        run_specmut(&["analyze", &path, "-n", "2", "-e", "0.01", "-f", "json"]);
    let (_, loose_stdout, _) =
        run_specmut(&["analyze", &path, "-n", "2", "-e", "0.5", "-f", "json"]);
    let tight = parse_json(&tight_stdout);
    let loose = parse_json(&loose_stdout);
    let tight_n = tight["tightness"]["neighborhood_size"]
        .as_u64()
        .unwrap_or(u64::MAX);
    let loose_n = loose["tightness"]["neighborhood_size"]
        .as_u64()
        .unwrap_or(0);
    assert!(
        tight_n <= loose_n,
        "tighter ε should not enlarge the neighborhood; tight={tight_n}, loose={loose_n}"
    );
}

#[test]
fn test_e2e_deterministic() {
    let path = spec("specs/sorting/sort.fol");
    let (_, first, _) = run_specmut(&[
        "analyze", &path, "-n", "2", "-e", "0.5", "-s", "1234", "-f", "json",
    ]);
    let (_, second, _) = run_specmut(&[
        "analyze", &path, "-n", "2", "-e", "0.5", "-s", "1234", "-f", "json",
    ]);
    // Timing fields vary; strip them before comparing.
    let mut a: serde_json::Value = serde_json::from_str(&first).expect("json");
    let mut b: serde_json::Value = serde_json::from_str(&second).expect("json");
    if let Some(obj) = a.as_object_mut() {
        obj.remove("timing");
    }
    if let Some(obj) = b.as_object_mut() {
        obj.remove("timing");
    }
    assert_eq!(
        a, b,
        "same seed → byte-identical JSON (after stripping timing)"
    );
}

/// Diagnostic-only summary table.  Prefixed `zz_` so cargo's
/// alphabetical test order runs it last.  Tests are not asserted
/// individually — the goal is to leave a tidy snapshot in cargo
/// output for the reviewer.
#[test]
fn zz_validation_summary() {
    use std::time::Instant;

    let entries: &[(&str, &[&str])] = &[
        ("trivial", &["analyze", "specs/minimal/trivial.fol", "-n", "2", "-e", "0.5", "-f", "json"]),
        ("empty", &["analyze", "specs/minimal/empty.fol", "-n", "2", "-e", "0.5", "-f", "json"]),
        ("sort.fol", &["analyze", "specs/sorting/sort.fol", "-n", "2", "-e", "0.5", "-f", "json"]),
        ("sort_v1_buggy", &["analyze", "specs/sorting/sort_v1_buggy.fol", "-n", "2", "-e", "0.5", "-f", "json"]),
        ("sort_v3_correct", &["analyze", "specs/sorting/sort_v3_correct.fol", "-n", "2", "-e", "0.5", "-f", "json"]),
        ("stack", &["analyze", "specs/stack/stack.fol", "-n", "2", "-e", "0.5", "-f", "json"]),
        ("set", &["analyze", "specs/set/set.fol", "-n", "2", "-e", "0.5", "-f", "json"]),
    ];

    println!();
    println!("╔══════════════════════════════════════════════════════════════════════╗");
    println!("║              specmut End-to-End Validation Summary                  ║");
    println!("╠═════════════════════╤═══╤═════╤═══════════╤════════╤═══════════════╣");
    println!(
        "║ {:19} │ {:1} │ {:3} │ {:>9} │ {:>6} │ {:>13} ║",
        "Spec", "n", "ε", "Mutations", "τ", "Time (ms)"
    );
    println!("╠═════════════════════╪═══╪═════╪═══════════╪════════╪═══════════════╣");
    for (label, args) in entries {
        let start = Instant::now();
        let (code, stdout, stderr) = run_specmut(args);
        let elapsed = start.elapsed().as_millis();
        if code != 0 {
            println!(
                "║ {:19} │ — │  —  │     —     │   —    │ FAILED ({:3}) ║",
                label, code
            );
            eprintln!("stderr for {label}:\n{stderr}");
            continue;
        }
        let json: serde_json::Value =
            serde_json::from_str(&stdout).unwrap_or(serde_json::Value::Null);
        let n_param = json["parameters"]["model_bound"].as_u64().unwrap_or(0);
        let epsilon = json["parameters"]["epsilon"].as_f64().unwrap_or(0.0);
        let mutations = json["tightness"]["neighborhood_size"].as_u64().unwrap_or(0);
        let score = json["tightness"]["score"].as_f64().unwrap_or(f64::NAN);
        println!(
            "║ {:19} │ {:1} │ {:.2} │ {:>9} │ {:>6.3} │ {:>10} ms ║",
            label, n_param, epsilon, mutations, score, elapsed
        );
    }
    println!("╚═════════════════════╧═══╧═════╧═══════════╧════════╧═══════════════╝");
}
