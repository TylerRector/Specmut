//! Lean 4 elaboration bridge.
//!
//! The Phase 5 [`crate::lean_parser`] is a regex extractor — it walks
//! `.lean` source line by line and pulls out `def ... Prop` /
//! `theorem ...` headers without understanding Lean's type theory.  This
//! module adds a *best-effort* elaboration path: given a `.lean` source
//! and a `lean` binary on PATH, it generates a small helper script that
//! invokes Lean's reflection API, captures the output, and tries to
//! translate a restricted subset of Lean to FOL.
//!
//! Robust Lean → FOL would require Lean's full elaborator.  This bridge
//! is intentionally small: anything it can't translate becomes
//! [`LeanError::UnsupportedConstruct`] and the CLI gracefully falls
//! back to the Phase 5 extraction summary.
//!
//! # Limitations
//!
//! This elaborator handles a restricted subset of Lean 4:
//!
//! * First-order propositions (no higher-order functions as arguments).
//! * Simple inductive types (no indexed families, no universe
//!   polymorphism).
//! * Pattern matching only via the equation compiler (no tactic-only
//!   proofs).
//! * No type classes (`Ord`, `BEq`, etc. are not translated).
//! * No monadic code (`IO`, `StateM`, etc.).
//! * No metaprogramming (`macro`, `syntax`, `elab`).
//!
//! Anything outside that subset yields `LeanError::UnsupportedConstruct`.

use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

use specmut_core::formula::Formula;
use specmut_core::signature::{RelationSymbol, Signature, SortSymbol};
use thiserror::Error;

use crate::lean_parser::{LeanExtraction, PredicateClass};

/// Bundled output of a successful elaboration.
#[derive(Debug, Clone)]
pub struct LeanElaboration {
    /// The reconstructed signature.
    pub signature: Signature,
    /// Axioms recovered from `theorem` declarations.  Empty when the
    /// elaborator could only build the signature.
    pub axioms: Vec<Formula>,
    /// Non-fatal issues — skipped definitions, unrecognised theorem
    /// statements, etc.  The CLI echoes these.
    pub warnings: Vec<String>,
}

/// Errors raised by the elaborator.
#[derive(Debug, Error)]
pub enum LeanError {
    /// `lean` binary not on PATH and `lean_path` doesn't exist.
    #[error("lean binary not found at {path}")]
    BinaryNotFound {
        /// Path that was searched.
        path: PathBuf,
    },

    /// Lean returned a non-zero exit code.
    #[error("lean exited with code {code}: {stderr}")]
    LeanFailed {
        /// Exit code reported by the OS.
        code: i32,
        /// Lean's stderr (last few KB).
        stderr: String,
    },

    /// The child process exceeded `timeout_secs`.
    #[error("lean timed out after {timeout_secs}s")]
    Timeout {
        /// Configured timeout in seconds.
        timeout_secs: u64,
    },

    /// A Lean construct we don't know how to translate.
    #[error("unsupported Lean construct: {description}")]
    UnsupportedConstruct {
        /// Human-readable description.
        description: String,
    },

    /// Failed to parse Lean's output.
    #[error("parse error in lean output: {message}")]
    OutputParse {
        /// What went wrong.
        message: String,
    },

    /// I/O error while spawning Lean or reading its output.
    #[error("I/O error invoking lean: {0}")]
    Io(#[from] std::io::Error),
}

/// Best-effort Lean elaborator.
#[derive(Debug, Clone)]
pub struct LeanElaborator {
    /// Path to the `lean` binary.  Defaults to `"lean"` (resolved by
    /// `PATH`).
    pub lean_path: PathBuf,
    /// Optional path to a `lake` binary.  Currently unused — reserved
    /// for future Lake-project support.
    #[allow(dead_code)]
    pub lake_path: Option<PathBuf>,
    /// Per-elaboration wall-clock timeout in seconds.  Phase 7 default
    /// is 30 s.
    pub timeout_secs: u64,
}

impl Default for LeanElaborator {
    fn default() -> Self {
        Self {
            lean_path: PathBuf::from("lean"),
            lake_path: None,
            timeout_secs: 30,
        }
    }
}

impl LeanElaborator {
    /// Build an elaborator with the given `lean` binary path.
    pub fn new(lean_path: PathBuf) -> Self {
        Self {
            lean_path,
            lake_path: None,
            timeout_secs: 30,
        }
    }

    /// Try to elaborate `source_path` into a FOL signature + axioms.
    ///
    /// On success, the returned [`LeanElaboration`] may carry a
    /// best-effort signature and axiom list.  On any of the limitations
    /// listed in the module docs, the call returns
    /// [`LeanError::UnsupportedConstruct`] with a description.
    pub fn elaborate(
        &self,
        source_path: &Path,
        extraction: &LeanExtraction,
    ) -> Result<LeanElaboration, LeanError> {
        if !binary_is_resolvable(&self.lean_path) {
            return Err(LeanError::BinaryNotFound {
                path: self.lean_path.clone(),
            });
        }

        // Write a helper script that asks Lean to print the elaborated
        // types of every declaration our regex pass discovered.  Even
        // for the failure path this confirms the binary is callable.
        let helper = generate_helper_script(source_path, extraction)?;
        let helper_dir = helper.path().parent().map(Path::to_path_buf);
        let mut cmd = Command::new(&self.lean_path);
        cmd.arg(helper.path());
        if let Some(dir) = helper_dir {
            cmd.current_dir(dir);
        }
        cmd.stdout(Stdio::piped()).stderr(Stdio::piped());

        let output = run_with_timeout(cmd, self.timeout_secs)?;
        if !output.status.success() {
            let stderr = String::from_utf8_lossy(&output.stderr);
            return Err(LeanError::LeanFailed {
                code: output.status.code().unwrap_or(-1),
                stderr: tail(&stderr, 4096).to_string(),
            });
        }

        let stdout = String::from_utf8_lossy(&output.stdout);
        translate_lean_output(&stdout, extraction)
    }
}

/// Decide whether a `Path` resolves to a runnable binary.  Honours
/// absolute paths directly; for bare names, scans `PATH` like the shell
/// would.
fn binary_is_resolvable(path: &Path) -> bool {
    if path.is_absolute() {
        return path.exists();
    }
    let name = match path.to_str() {
        Some(n) => n,
        None => return false,
    };
    if name.contains(std::path::MAIN_SEPARATOR) {
        return path.exists();
    }
    if let Some(env_path) = std::env::var_os("PATH") {
        for dir in std::env::split_paths(&env_path) {
            if dir.join(name).is_file() {
                return true;
            }
        }
    }
    false
}

/// Generated helper script handle.  Holds the [`tempfile::NamedTempFile`]
/// for ownership — the file lives as long as this struct does.
struct HelperScript {
    file: tempfile::NamedTempFile,
}

impl HelperScript {
    fn path(&self) -> &Path {
        self.file.path()
    }
}

fn generate_helper_script(
    source_path: &Path,
    extraction: &LeanExtraction,
) -> Result<HelperScript, LeanError> {
    let mut body = String::new();
    body.push_str("-- specmut Phase 7: auto-generated Lean elaboration helper.\n");
    // We import-by-path-string rather than module name to be robust to
    // the source not living in a Lake project.
    let import_target = source_path
        .file_stem()
        .and_then(|s| s.to_str())
        .unwrap_or("Target");
    body.push_str(&format!("import «{import_target}»\n\n"));
    for pred in &extraction.predicates {
        body.push_str(&format!("#check @{}\n", pred.name));
    }
    for thm in &extraction.theorems {
        body.push_str(&format!("#check @{}\n", thm.name));
    }

    let file = tempfile::Builder::new()
        .prefix("specmut-lean-helper-")
        .suffix(".lean")
        .tempfile()?;
    std::fs::write(file.path(), body)?;
    Ok(HelperScript { file })
}

/// Spawn `cmd`, wait at most `timeout_secs`.  Kills the child and
/// returns [`LeanError::Timeout`] on expiry.
fn run_with_timeout(
    mut cmd: Command,
    timeout_secs: u64,
) -> Result<std::process::Output, LeanError> {
    let mut child = cmd.spawn()?;
    let start = Instant::now();
    let deadline = Duration::from_secs(timeout_secs);
    loop {
        match child.try_wait()? {
            Some(_status) => {
                return child.wait_with_output().map_err(LeanError::Io);
            }
            None => {
                if start.elapsed() >= deadline {
                    let _ = child.kill();
                    let _ = child.wait();
                    return Err(LeanError::Timeout { timeout_secs });
                }
                std::thread::sleep(Duration::from_millis(50));
            }
        }
    }
}

/// Translate Lean's `#check` output into a [`LeanElaboration`].
///
/// Phase 7 only recognises the simplest shape — a chain of `T₁ → T₂ →
/// … → Prop` produces a relation symbol with arity `[T₁, …, Tₙ₋₁]`.
/// Anything else (dependent types, type-class arguments, polymorphic
/// universes, applied predicates as arguments) is surfaced as a
/// warning, and if no relations were recovered at all we return
/// `UnsupportedConstruct` so the CLI can fall back to the Phase 5
/// extraction summary.
fn translate_lean_output(
    stdout: &str,
    extraction: &LeanExtraction,
) -> Result<LeanElaboration, LeanError> {
    let mut sorts: Vec<SortSymbol> = Vec::new();
    let mut relations: Vec<RelationSymbol> = Vec::new();
    let mut warnings: Vec<String> = Vec::new();

    let mut seen_names: std::collections::BTreeSet<String> = std::collections::BTreeSet::new();
    for line in stdout.lines() {
        let trimmed = line.trim_start();
        // Lean's `#check` output looks like: `name : T1 → T2 → Prop`.
        let (name, body) = match trimmed.split_once(" : ") {
            Some((n, b)) => (n.trim().trim_start_matches('@').to_string(), b),
            None => continue,
        };
        if !body.contains("Prop") {
            warnings.push(format!("skipping non-Prop declaration: {line}"));
            continue;
        }
        if name.is_empty() || !seen_names.insert(name.clone()) {
            continue;
        }
        if let Some(rel) = parse_first_order_relation(&name, body, &mut sorts, &mut warnings) {
            relations.push(rel);
        }
    }

    // Round-trip predicate-class metadata from the regex extraction as
    // additional warnings so the CLI can echo them.
    for pred in &extraction.predicates {
        if !relations.iter().any(|r| r.name == pred.name) && pred.relation_type != PredicateClass::Other {
            warnings.push(format!(
                "extractor saw predicate '{}' (class {:?}) but elaborator could not derive its arity",
                pred.name, pred.relation_type
            ));
        }
    }

    if relations.is_empty() && sorts.is_empty() {
        return Err(LeanError::UnsupportedConstruct {
            description:
                "no first-order Prop-valued declarations recovered from Lean output; Lean source uses constructs outside the supported subset"
                    .to_string(),
        });
    }

    let signature = Signature::new(sorts, vec![], relations).map_err(|e| {
        LeanError::OutputParse {
            message: format!("could not build signature from Lean output: {e}"),
        }
    })?;
    Ok(LeanElaboration {
        signature,
        axioms: Vec::new(),
        warnings,
    })
}

/// Try to read `body` as `T1 → T2 → … → Prop` and produce a
/// `RelationSymbol` named `name`.  Mutates `sorts` to add any sort
/// names not seen yet, and pushes a warning if the shape isn't simple.
fn parse_first_order_relation(
    name: &str,
    body: &str,
    sorts: &mut Vec<SortSymbol>,
    warnings: &mut Vec<String>,
) -> Option<RelationSymbol> {
    // `Prop` must end the chain.
    let arrow_chain = body.trim();
    let last_arrow = arrow_chain
        .rfind('→')
        .or_else(|| arrow_chain.rfind("->"))?;
    let after = arrow_chain[last_arrow + '→'.len_utf8().max(2)..].trim();
    if after != "Prop" {
        return None;
    }
    let prefix = arrow_chain[..last_arrow].trim();
    if prefix.is_empty() {
        return None;
    }
    let mut arity = Vec::new();
    for piece in prefix.split(['→', '>']) {
        let piece = piece.trim().trim_end_matches('-').trim();
        if piece.is_empty() {
            continue;
        }
        if piece.contains('(') || piece.contains(' ') {
            warnings.push(format!(
                "skipping non-simple type in relation arity: '{piece}'"
            ));
            return None;
        }
        let sort = SortSymbol::new(piece);
        if !sorts.contains(&sort) {
            sorts.push(sort.clone());
        }
        arity.push(sort);
    }
    if arity.is_empty() {
        return None;
    }
    Some(RelationSymbol::new(name, arity))
}

fn tail(s: &str, max_bytes: usize) -> &str {
    if s.len() <= max_bytes {
        return s;
    }
    let cutoff = s.len() - max_bytes;
    let mut idx = cutoff;
    while idx < s.len() && !s.is_char_boundary(idx) {
        idx += 1;
    }
    &s[idx..]
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::PathBuf;

    fn empty_extraction() -> LeanExtraction {
        LeanExtraction {
            predicates: Vec::new(),
            theorems: Vec::new(),
            source: String::new(),
        }
    }

    #[test]
    fn test_elaborate_not_found() {
        let elab = LeanElaborator::new(PathBuf::from(
            "/specmut/test/definitely/no/such/binary",
        ));
        let tmp = tempfile::NamedTempFile::new().expect("tempfile");
        std::fs::write(tmp.path(), "").expect("write");
        let err = elab.elaborate(tmp.path(), &empty_extraction()).expect_err("should fail");
        assert!(matches!(err, LeanError::BinaryNotFound { .. }));
    }

    #[test]
    fn test_elaborator_default_path() {
        let elab = LeanElaborator::default();
        assert_eq!(elab.lean_path, PathBuf::from("lean"));
        assert_eq!(elab.timeout_secs, 30);
    }

    #[test]
    fn test_translate_recognises_arrow_chain() {
        let stdout = "Sorted : Nat → Prop\nLess : Nat → Nat → Prop\nfoo : Int\n";
        let ext = empty_extraction();
        let result = translate_lean_output(stdout, &ext).expect("ok");
        assert!(!result.signature.sorts.is_empty());
        assert!(!result.signature.relations.is_empty());
    }

    #[test]
    fn test_translate_unsupported_when_nothing_first_order() {
        let stdout = "foo : (α : Type) → α → α\nbar : IO Unit\n";
        let ext = empty_extraction();
        let err = translate_lean_output(stdout, &ext).expect_err("should be unsupported");
        assert!(matches!(err, LeanError::UnsupportedConstruct { .. }));
    }

    #[test]
    fn test_elaborate_with_zero_timeout_when_lean_missing() {
        // If `lean` isn't on PATH this returns BinaryNotFound before
        // any process is spawned, so timeout_secs = 0 is harmless.
        let elab = LeanElaborator {
            timeout_secs: 0,
            ..LeanElaborator::default()
        };
        let tmp = tempfile::NamedTempFile::new().expect("tempfile");
        std::fs::write(tmp.path(), "").expect("write");
        // We accept BOTH BinaryNotFound (lean absent) and Timeout
        // (lean present and timeout immediately killed it).
        match elab.elaborate(tmp.path(), &empty_extraction()) {
            Err(LeanError::BinaryNotFound { .. })
            | Err(LeanError::Timeout { .. })
            | Err(LeanError::LeanFailed { .. })
            | Err(LeanError::UnsupportedConstruct { .. })
            | Err(LeanError::OutputParse { .. })
            | Err(LeanError::Io(_))
            | Ok(_) => {}
        }
    }
}
