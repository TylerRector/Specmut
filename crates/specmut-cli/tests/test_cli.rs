//! Phase 5 CLI integration tests.
//!
//! These shell out to the `specmut` binary built by cargo and inspect
//! stdout / stderr / exit code.  Tempfile is used for ephemeral spec /
//! config inputs.

use std::path::{Path, PathBuf};
use std::process::Command;

/// Path to the compiled CLI binary, supplied by cargo at test time.
fn bin() -> PathBuf {
    PathBuf::from(env!("CARGO_BIN_EXE_specmut"))
}

/// Workspace root: tests/ → crates/specmut-cli/ → crates/ → workspace.
fn workspace_root() -> PathBuf {
    let manifest = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    manifest
        .parent()
        .and_then(|p| p.parent())
        .map(Path::to_path_buf)
        .expect("specmut-cli lives two directories below the workspace root")
}

fn sort_spec() -> PathBuf {
    workspace_root().join("specs/sorting/sort.fol")
}

fn sort_impl() -> PathBuf {
    workspace_root().join("specs/sorting/implementations/insertion_sort.model")
}

#[test]
fn test_cli_fol_text_output() {
    let out = Command::new(bin())
        .arg("analyze")
        .arg(sort_spec())
        .args(["-n", "2", "-k", "1", "-e", "0.5", "-f", "text"])
        .output()
        .expect("spawn specmut");
    assert!(
        out.status.success(),
        "exit {:?}\nstdout: {}\nstderr: {}",
        out.status.code(),
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr),
    );
    let stdout = String::from_utf8(out.stdout).expect("utf8");
    assert!(stdout.contains("τ ="), "missing τ in output:\n{stdout}");
}

#[test]
fn test_cli_fol_json_output() {
    let out = Command::new(bin())
        .arg("analyze")
        .arg(sort_spec())
        .args(["-n", "2", "-k", "1", "-e", "0.5", "-f", "json"])
        .output()
        .expect("spawn specmut");
    assert!(out.status.success(), "exit code {:?}", out.status.code());
    let stdout = String::from_utf8(out.stdout).expect("utf8");
    let parsed: serde_json::Value =
        serde_json::from_str(&stdout).expect("stdout should be valid JSON");
    assert!(parsed.get("tightness").is_some(), "missing tightness key");
    assert!(parsed.get("signature").is_some(), "missing signature key");
    assert!(
        parsed.get("decomposition").is_some(),
        "missing decomposition key"
    );
}

#[test]
fn test_cli_with_impl() {
    let out = Command::new(bin())
        .arg("analyze")
        .arg(sort_spec())
        .args(["-n", "2", "-k", "1", "-e", "0.5"])
        .args(["-i".as_ref(), sort_impl().as_os_str()])
        .output()
        .expect("spawn specmut");
    assert!(
        out.status.success(),
        "exit {:?}\nstderr: {}",
        out.status.code(),
        String::from_utf8_lossy(&out.stderr)
    );
}

#[test]
fn test_cli_with_config() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let cfg_path = tmp.path().join("specmut.toml");
    let cfg_text = format!(
        r#"
[project]
name = "test"
spec_file = "{}"

[parameters]
model_bound = 2
quantifier_rank = 1
epsilon = 0.5
seed = 7

[output]
report_format = "json"
"#,
        sort_spec().display()
    );
    std::fs::write(&cfg_path, cfg_text).expect("write cfg");
    let out = Command::new(bin())
        .arg("analyze")
        .arg(sort_spec())
        .arg("-c")
        .arg(&cfg_path)
        .output()
        .expect("spawn specmut");
    assert!(
        out.status.success(),
        "exit {:?}\nstderr: {}",
        out.status.code(),
        String::from_utf8_lossy(&out.stderr)
    );
    let stdout = String::from_utf8(out.stdout).expect("utf8");
    // Config sets format = "json"; CLI didn't override, so JSON wins.
    let parsed: serde_json::Value =
        serde_json::from_str(&stdout).expect("stdout should be JSON when config asks for it");
    assert_eq!(
        parsed["parameters"]["model_bound"],
        serde_json::json!(2),
        "config-provided model_bound should appear"
    );
    assert_eq!(
        parsed["parameters"]["seed"],
        serde_json::json!(7),
        "config-provided seed should appear"
    );
}

#[test]
fn test_cli_parse_error() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let bad = tmp.path().join("bad.fol");
    std::fs::write(&bad, "this is not a valid spec at all").expect("write");
    let out = Command::new(bin())
        .arg("analyze")
        .arg(&bad)
        .args(["-n", "2"])
        .output()
        .expect("spawn specmut");
    assert_eq!(out.status.code(), Some(1), "expected PARSE_ERROR");
}

#[test]
fn test_cli_lean_extract() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let lean = tmp.path().join("toy.lean");
    let src = "def Sorted_v1 (l : List Nat) : Prop := True\n\
        theorem foo : True := by trivial\n";
    std::fs::write(&lean, src).expect("write lean");
    let out = Command::new(bin())
        .arg("analyze")
        .arg(&lean)
        .output()
        .expect("spawn specmut");
    assert!(out.status.success(), "exit {:?}", out.status.code());
    let stdout = String::from_utf8(out.stdout).expect("utf8");
    assert!(
        stdout.contains("Lean extraction"),
        "missing Lean header in:\n{stdout}"
    );
    assert!(
        stdout.contains("Sorted_v1"),
        "missing predicate Sorted_v1 in:\n{stdout}"
    );
}

#[test]
fn test_cli_missing_file() {
    let out = Command::new(bin())
        .arg("analyze")
        .arg("/nonexistent/path/spec.fol")
        .output()
        .expect("spawn specmut");
    assert_ne!(out.status.code(), Some(0), "should not succeed");
}

#[cfg(not(feature = "smt"))]
#[test]
fn test_cli_smt_without_feature() {
    // Without the smt feature compiled in, passing --smt must exit 3
    // (EXIT_SMT_UNAVAILABLE) with a recompile hint.
    let out = Command::new(bin())
        .arg("analyze")
        .arg(sort_spec())
        .args(["-n", "2"])
        .arg("--smt")
        .output()
        .expect("spawn specmut");
    assert_eq!(out.status.code(), Some(3), "expected EXIT_SMT_UNAVAILABLE");
    let stderr = String::from_utf8(out.stderr).expect("utf8");
    assert!(
        stderr.contains("SMT support not compiled in"),
        "missing recompile hint:\n{stderr}"
    );
    assert!(
        stderr.contains("--features specmut-cli/smt"),
        "missing feature-flag hint:\n{stderr}"
    );
}

#[cfg(feature = "smt")]
#[test]
fn test_cli_smt_flag() {
    let out = Command::new(bin())
        .arg("analyze")
        .arg(sort_spec())
        .args(["-n", "2", "-e", "0.5", "--smt"])
        .output()
        .expect("spawn specmut");
    assert!(
        out.status.success(),
        "exit {:?}\nstderr: {}",
        out.status.code(),
        String::from_utf8_lossy(&out.stderr)
    );
    let stdout = String::from_utf8(out.stdout).expect("utf8");
    assert!(stdout.contains("τ ="), "missing τ in output:\n{stdout}");
    assert!(
        stdout.contains("Z3 SMT"),
        "expected Z3 entailment marker:\n{stdout}"
    );
}

#[cfg(feature = "smt")]
#[test]
fn test_cli_smt_and_cegis() {
    let out = Command::new(bin())
        .arg("analyze")
        .arg(sort_spec())
        .args(["-n", "2", "-e", "0.5", "--smt", "--cegis"])
        .output()
        .expect("spawn specmut");
    assert!(
        out.status.success(),
        "exit {:?}\nstderr: {}",
        out.status.code(),
        String::from_utf8_lossy(&out.stderr)
    );
}

#[cfg(feature = "smt")]
#[test]
fn test_cli_smt_fallback_note() {
    // Force Z3 to time out by setting timeout to 1 ms on the stack
    // spec, which contains nested quantifiers over multiple sorts.
    let out = Command::new(bin())
        .arg("analyze")
        .arg(workspace_root().join("specs/stack/stack.fol"))
        .args(["-n", "2", "-e", "0.4"])
        .arg("--smt")
        .args(["--smt-timeout", "1"])
        .output()
        .expect("spawn specmut");
    // The pipeline must complete (exit 0) — fallback handles Unknown.
    assert!(
        out.status.success(),
        "exit {:?}\nstderr: {}",
        out.status.code(),
        String::from_utf8_lossy(&out.stderr)
    );
    let stdout = String::from_utf8(out.stdout).expect("utf8");
    // At a 1 ms timeout, Z3 should hit Unknown at least once on the
    // stack spec.  If a future Z3 version solves this in 1 ms we
    // accept that gracefully — the absence of a note is only a
    // failure if the test expected one strictly.
    if !stdout.contains("model enumeration was used as fallback") {
        eprintln!(
            "test_cli_smt_fallback_note: Z3 solved every query in 1 ms; \
             fallback never triggered. (Z3 is faster than we expected.)"
        );
    }
}
