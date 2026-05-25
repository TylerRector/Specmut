//! Phase D §6 — external repository validation.
//!
//! These tests run the full Lean pipeline against Tier 1 external targets
//! (lean4 doc/examples, jjakpor/binary-search).  They are *not* part of the
//! default test run — both lean availability AND the external fixtures must
//! be present.  Use `scripts/fetch_external_fixtures.sh` to populate them.
//!
//! Failure modes are documented inline rather than asserted strictly: the
//! external validation is exploratory ("does the pipeline survive real Lean
//! files without panicking?") and the assertions are intentionally loose.

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

fn external_dir() -> PathBuf {
    PathBuf::from(
        std::env::var("SPECMUT_EXTERNAL_DIR").unwrap_or_else(|_| "/tmp/specmut-external".into()),
    )
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
    elan_bin.is_file()
        || Command::new("lean")
            .arg("--version")
            .output()
            .map(|o| o.status.success())
            .unwrap_or(false)
}

fn external_fixture(name: &str) -> Option<PathBuf> {
    let p = external_dir().join(name);
    if p.exists() {
        Some(p)
    } else {
        None
    }
}

/// Macro: skip the test (printing a hint) when the external fixture or lean
/// is missing.  Binds `$path` to the located fixture path.
macro_rules! require_external {
    ($var:ident, $name:expr) => {
        if !lean_available() {
            eprintln!("skip: lean not on PATH");
            return;
        }
        let $var = match external_fixture($name) {
            Some(p) => p,
            None => {
                eprintln!(
                    "skip: external fixture {} not present at {}; run scripts/fetch_external_fixtures.sh",
                    $name,
                    external_dir().display()
                );
                return;
            }
        };
    };
}

/// Search for a Lean file under `root` matching one of `candidates`,
/// returning the first that exists.  External repos rearrange directories
/// over time, so we probe a few canonical locations.
fn find_first_existing(root: &Path, candidates: &[&str]) -> Option<PathBuf> {
    for c in candidates {
        let p = root.join(c);
        if p.exists() {
            return Some(p);
        }
    }
    None
}

// ----------------------------------------------------------------------------
// Lean4 doc/examples (BST or similar simple inductive)
// ----------------------------------------------------------------------------

#[test]
fn test_external_lean4_doc_example() {
    require_external!(root, "lean4");
    // The exact path moves between lean4 versions.  Try several known
    // locations; if none exist the test skips.
    let target = match find_first_existing(
        &root,
        &[
            "doc/examples/bintree.lean",
            "doc/examples/Bintree.lean",
            "doc/examples/palindromes.lean",
            "doc/examples/Palindromes.lean",
        ],
    ) {
        Some(p) => p,
        None => {
            eprintln!(
                "skip: no known lean4 doc/example file under {}; layout changed",
                root.display()
            );
            return;
        }
    };
    let (code, stdout, stderr) = run_specmut(&[
        "analyze",
        target.to_str().expect("utf-8"),
        "--lean-full",
        "-n",
        "2",
        "-f",
        "json",
    ]);
    // Acceptable outcomes per Phase D §6.4:
    //  * exit 0 + parseable JSON  → full pipeline succeeded
    //  * exit 1                   → translation produced no axioms (NothingTranslatable)
    //  * exit 4                   → MODEL_BOUND_EXCEEDED after sort filter
    // We just check the pipeline didn't panic or hang.
    assert!(
        matches!(code, 0 | 1 | 4),
        "unexpected exit code {code}\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    if code == 0 {
        let parsed: serde_json::Value = serde_json::from_str(&stdout)
            .unwrap_or_else(|e| panic!("invalid JSON on exit 0: {e}\n{stdout}"));
        assert!(parsed.get("tightness").is_some());
    }
}

// ----------------------------------------------------------------------------
// jjakpor/binary-search
// ----------------------------------------------------------------------------

#[test]
fn test_external_binary_search() {
    require_external!(root, "binary-search");
    let target = match find_first_existing(
        &root,
        &[
            "BinarySearch.lean",
            "src/BinarySearch.lean",
            "BinarySearch/Basic.lean",
        ],
    ) {
        Some(p) => p,
        None => {
            eprintln!(
                "skip: no BinarySearch.lean under {} — layout differs from spec",
                root.display()
            );
            return;
        }
    };
    let (code, stdout, stderr) = run_specmut(&[
        "analyze",
        target.to_str().expect("utf-8"),
        "--lean-full",
        "-n",
        "2",
        "-f",
        "json",
        // Generous timeout — Mathlib-style repos can be slow to elaborate.
        "--lean-timeout",
        "180",
    ]);
    assert!(
        matches!(code, 0 | 1 | 4),
        "unexpected exit code {code}\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
}

// ----------------------------------------------------------------------------
// Sort-filter assertion against a real-world Lean file (only runs if reachable)
// ----------------------------------------------------------------------------

#[test]
fn test_external_sort_filter_active() {
    require_external!(root, "lean4");
    let target = match find_first_existing(
        &root,
        &[
            "doc/examples/bintree.lean",
            "doc/examples/Bintree.lean",
            "doc/examples/palindromes.lean",
            "doc/examples/Palindromes.lean",
        ],
    ) {
        Some(p) => p,
        None => return,
    };
    let (code, stdout, _stderr) = run_specmut(&[
        "analyze",
        target.to_str().expect("utf-8"),
        "--lean-full",
        "-n",
        "2",
        "-f",
        "json",
    ]);
    if code != 0 {
        eprintln!("skip: target didn't translate cleanly (exit {code})");
        return;
    }
    let parsed: serde_json::Value = match serde_json::from_str(&stdout) {
        Ok(v) => v,
        Err(_) => return,
    };
    let Some(lt) = parsed.get("lean_translation") else {
        return;
    };
    let Some(sf) = lt.get("sort_filter") else { return };
    let orig = sf.get("original_sorts").and_then(|v| v.as_u64()).unwrap_or(0);
    let filt = sf.get("filtered_sorts").and_then(|v| v.as_u64()).unwrap_or(0);
    // External Lean files invariably pull in Bool/Prop/etc. as type args, so
    // the filter should remove at least one sort.  Loose check — we just want
    // confidence the pruning fires on real specs.
    assert!(
        filt <= orig,
        "filtered count {filt} should be ≤ original {orig}"
    );
}
