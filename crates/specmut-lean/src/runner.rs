//! Subprocess management for the Phase A Lean exporter.
//!
//! `LeanRunner` resolves the `lean` binary, detects Lake projects, writes the
//! bundled `specmut_export.lean` script to a temp file, runs it on the target,
//! and parses the JSON output.  Errors are surfaced via [`LeanPipelineError`].
//!
//! The exporter script is embedded via `include_str!` so installed binaries
//! ship without needing the source tree.

use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

use crate::ir_types::LeanIR;

/// The Lean exporter source, embedded at compile time.  We write it to a temp
/// file at runtime so `lean --run` can read it as a path argument.
const EXPORT_SCRIPT_CONTENT: &str = include_str!("../lean/specmut_export.lean");

/// Default timeout for the Lean exporter, in seconds.
pub const DEFAULT_TIMEOUT_SECS: u64 = 60;

/// Manages a `lean` subprocess that exports a target file's IR to JSON.
#[derive(Debug, Clone)]
pub struct LeanRunner {
    /// Path to the `lean` binary.  Defaults to `"lean"`, resolved via `PATH`.
    pub lean_path: PathBuf,
    /// Per-invocation wall-clock timeout.
    pub timeout_secs: u64,
}

impl Default for LeanRunner {
    fn default() -> Self {
        Self {
            lean_path: PathBuf::from("lean"),
            timeout_secs: DEFAULT_TIMEOUT_SECS,
        }
    }
}

impl LeanRunner {
    /// Build a runner from an explicit binary path and timeout.
    pub fn new(lean_path: PathBuf, timeout_secs: u64) -> Self {
        Self {
            lean_path,
            timeout_secs,
        }
    }

    /// True iff `self.lean_path` resolves to a runnable binary.  Used by
    /// callers to decide whether to attempt the full Lean pipeline or fall
    /// back to the regex extractor.
    pub fn lean_available(&self) -> bool {
        binary_on_path(&self.lean_path)
    }

    /// Detect if `target_path` is inside a Lake project.
    ///
    /// Walks from the file's parent directory toward the filesystem root,
    /// looking for `lakefile.lean` or `lakefile.toml`.  Returns the project
    /// root (the directory containing the lakefile) on the first hit.
    pub fn detect_lake_project(target_path: &Path) -> Option<PathBuf> {
        let dir = if target_path.is_dir() {
            target_path
        } else {
            target_path.parent()?
        };
        let mut current: &Path = dir;
        loop {
            if current.join("lakefile.lean").exists() || current.join("lakefile.toml").exists() {
                return Some(current.to_path_buf());
            }
            current = current.parent()?;
        }
    }

    /// Run the exporter on `target_path` and return the parsed IR.
    ///
    /// Steps: (1) check the lean binary exists, (2) write the embedded script
    /// to a temp file, (3) decide Lake-or-bare invocation, (4) spawn, time-
    /// limit, capture stdout/stderr, (5) parse JSON, (6) attach stderr as
    /// warnings.
    pub fn export(&self, target_path: &Path) -> Result<LeanIR, LeanPipelineError> {
        if !self.lean_available() {
            return Err(LeanPipelineError::LeanNotFound {
                path: self.lean_path.clone(),
            });
        }

        // Write the embedded script to a temp file.
        let mut script_file = tempfile::Builder::new()
            .prefix("specmut-export-")
            .suffix(".lean")
            .tempfile()?;
        script_file
            .write_all(EXPORT_SCRIPT_CONTENT.as_bytes())
            .map_err(LeanPipelineError::Io)?;
        script_file.flush()?;

        let lake_project = Self::detect_lake_project(target_path);
        let (stdout, stderr) =
            self.run_lean_command(script_file.path(), target_path, lake_project.as_deref())?;

        // Parse stdout — scan for the first `{` in case Lean emitted other text.
        let json_payload = find_json_start(&stdout).ok_or(LeanPipelineError::EmptyOutput)?;
        let mut ir: LeanIR =
            serde_json::from_str(json_payload).map_err(|e| LeanPipelineError::JsonParse {
                message: format!(
                    "{e} (first 200 chars of stdout: {})",
                    truncate(&stdout, 200)
                ),
            })?;

        // Attach non-empty stderr as warnings so downstream callers see them.
        let stderr_trimmed = stderr.trim();
        if !stderr_trimmed.is_empty() {
            ir.warnings.push(format!("lean stderr: {stderr_trimmed}"));
        }

        Ok(ir)
    }

    /// Spawn the Lean subprocess and wait for it (subject to `timeout_secs`).
    fn run_lean_command(
        &self,
        export_script: &Path,
        target_path: &Path,
        lake_project: Option<&Path>,
    ) -> Result<(String, String), LeanPipelineError> {
        let mut cmd = if let Some(project_dir) = lake_project {
            let lake = find_on_path("lake").ok_or(LeanPipelineError::LakeNotFound {
                project_dir: project_dir.to_path_buf(),
            })?;
            let mut c = Command::new(lake);
            c.arg("env").arg("lean");
            c.current_dir(project_dir);
            c
        } else {
            Command::new(&self.lean_path)
        };
        cmd.arg("--run").arg(export_script).arg(target_path);
        cmd.stdout(Stdio::piped()).stderr(Stdio::piped());

        let mut child = cmd.spawn()?;
        let start = Instant::now();
        let timeout = Duration::from_secs(self.timeout_secs);
        loop {
            match child.try_wait()? {
                Some(status) => {
                    let output = child.wait_with_output()?;
                    let stdout = String::from_utf8_lossy(&output.stdout).into_owned();
                    let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
                    if !status.success() {
                        return Err(LeanPipelineError::ExporterFailed {
                            code: status.code().unwrap_or(-1),
                            stderr,
                        });
                    }
                    return Ok((stdout, stderr));
                }
                None => {
                    if start.elapsed() >= timeout {
                        let _ = child.kill();
                        let _ = child.wait();
                        return Err(LeanPipelineError::ExporterTimeout {
                            timeout_secs: self.timeout_secs,
                        });
                    }
                    std::thread::sleep(Duration::from_millis(50));
                }
            }
        }
    }
}

/// Errors surfaced by the Lean → IR pipeline.
#[derive(Debug, thiserror::Error)]
pub enum LeanPipelineError {
    /// The `lean` binary couldn't be resolved.
    #[error("lean binary not found at '{}'; install lean via elan or pass --lean-path", path.display())]
    LeanNotFound {
        /// The path that was searched.
        path: PathBuf,
    },

    /// A Lake project was detected but `lake` isn't on PATH.
    #[error("lake project detected at '{}' but lake binary not found on PATH", project_dir.display())]
    LakeNotFound {
        /// The project directory containing the lakefile.
        project_dir: PathBuf,
    },

    /// Lean exited with a non-zero status code.
    #[error("lean exporter failed (exit {code}):\n{stderr}")]
    ExporterFailed {
        /// The exit code reported by the OS.
        code: i32,
        /// The captured stderr.
        stderr: String,
    },

    /// The exporter ran past its wall-clock budget.
    #[error("lean exporter timed out after {timeout_secs}s")]
    ExporterTimeout {
        /// The configured timeout.
        timeout_secs: u64,
    },

    /// The exporter produced no usable stdout.
    #[error("lean exporter produced no output on stdout")]
    EmptyOutput,

    /// stdout couldn't be parsed as JSON.
    #[error("failed to parse exporter JSON output: {message}")]
    JsonParse {
        /// Human-readable diagnostic.
        message: String,
    },

    /// Downstream translation rejected the IR (all theorems/predicates skipped).
    #[error("translation failed: {0}")]
    Translation(#[from] crate::translator::TranslationError),

    /// File or process I/O failed.
    #[error("I/O error: {0}")]
    Io(#[from] std::io::Error),
}

// ----------------------------------------------------------------------------
// Helpers
// ----------------------------------------------------------------------------

/// True iff `path` resolves to a runnable file.  Honours absolute paths; for
/// bare names scans the host's `PATH`.
fn binary_on_path(path: &Path) -> bool {
    if path.is_absolute() {
        return path.is_file();
    }
    let name = match path.to_str() {
        Some(n) => n,
        None => return false,
    };
    if name.contains(std::path::MAIN_SEPARATOR) {
        return path.is_file();
    }
    find_on_path(name).is_some()
}

/// Search `$PATH` for a bare command name; return the first resolved absolute path.
fn find_on_path(name: &str) -> Option<PathBuf> {
    let path = std::env::var_os("PATH")?;
    std::env::split_paths(&path).find_map(|dir| {
        let candidate = dir.join(name);
        if candidate.is_file() {
            Some(candidate)
        } else {
            None
        }
    })
}

/// Find the first `{` in `s` and return the substring from there.
fn find_json_start(s: &str) -> Option<&str> {
    let pos = s.find('{')?;
    Some(&s[pos..])
}

/// Char-boundary–safe truncation for diagnostics.
fn truncate(s: &str, max_bytes: usize) -> &str {
    if s.len() <= max_bytes {
        return s;
    }
    let mut end = max_bytes;
    while end > 0 && !s.is_char_boundary(end) {
        end -= 1;
    }
    &s[..end]
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;

    fn lean_on_path() -> bool {
        Command::new("lean").arg("--version").output().is_ok()
    }

    macro_rules! require_lean {
        () => {
            if !lean_on_path() {
                eprintln!("skip: lean not on PATH");
                return;
            }
        };
    }

    fn fixture_path(rel: &str) -> PathBuf {
        PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("lean")
            .join("test_fixtures")
            .join(rel)
    }

    #[test]
    fn test_runner_default_creation() {
        let r = LeanRunner::default();
        assert_eq!(r.lean_path, PathBuf::from("lean"));
        assert_eq!(r.timeout_secs, DEFAULT_TIMEOUT_SECS);
    }

    #[test]
    fn test_export_script_embedded() {
        assert!(!EXPORT_SCRIPT_CONTENT.is_empty(), "embedded script empty");
        assert!(
            EXPORT_SCRIPT_CONTENT.contains("specmut_export")
                || EXPORT_SCRIPT_CONTENT.contains("Specmut.Export"),
            "embedded script doesn't look like specmut_export.lean"
        );
    }

    #[test]
    fn test_find_json_start_with_prefix() {
        let s = "warning: foo\n  warning: bar\n{\"a\": 1}";
        let parsed = find_json_start(s).expect("found");
        assert!(parsed.starts_with('{'));
    }

    #[test]
    fn test_find_json_start_none() {
        assert!(find_json_start("no json here").is_none());
    }

    #[test]
    fn test_detect_lake_none() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let file = tmp.path().join("plain.lean");
        fs::write(&file, "").expect("write");
        assert!(LeanRunner::detect_lake_project(&file).is_none());
    }

    #[test]
    fn test_detect_lake_found() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let sub = tmp.path().join("sub");
        fs::create_dir(&sub).expect("create sub");
        fs::write(tmp.path().join("lakefile.lean"), "").expect("write lakefile");
        let target = sub.join("file.lean");
        fs::write(&target, "").expect("write target");
        let detected = LeanRunner::detect_lake_project(&target).expect("found");
        assert_eq!(
            detected.canonicalize().expect("canon"),
            tmp.path().canonicalize().expect("canon")
        );
    }

    #[test]
    fn test_detect_lake_toml_found() {
        let tmp = tempfile::tempdir().expect("tempdir");
        fs::write(tmp.path().join("lakefile.toml"), "").expect("write toml");
        let target = tmp.path().join("file.lean");
        fs::write(&target, "").expect("write target");
        assert!(LeanRunner::detect_lake_project(&target).is_some());
    }

    #[test]
    fn test_lean_available_check() {
        // Always callable; returns true only when lean is on PATH.
        let r = LeanRunner::default();
        let _ = r.lean_available();
    }

    #[test]
    fn test_export_minimal() {
        require_lean!();
        let r = LeanRunner::default();
        let ir = r.export(&fixture_path("minimal.lean")).expect("export");
        assert_eq!(ir.predicates.len(), 2);
        assert_eq!(ir.theorems.len(), 2);
    }

    #[test]
    fn test_export_bst() {
        require_lean!();
        let r = LeanRunner::default();
        let ir = r.export(&fixture_path("bst.lean")).expect("export");
        assert_eq!(ir.sorts.len(), 1);
        assert_eq!(ir.constructors.len(), 2);
        assert_eq!(ir.predicates.len(), 1);
        assert!(!ir.predicates[0].equations.is_empty());
    }

    #[test]
    fn test_export_nonexistent_file() {
        require_lean!();
        let r = LeanRunner::default();
        let err = r
            .export(Path::new("/nonexistent/path/to/file.lean"))
            .expect_err("should fail");
        // The Lean process will exit non-zero when the file doesn't exist.
        assert!(matches!(err, LeanPipelineError::ExporterFailed { .. }));
    }

    #[test]
    fn test_export_timeout_does_not_panic() {
        require_lean!();
        // 0s timeout: should either return Timeout, fail, or (very rarely)
        // complete on a fast machine.  Just assert no panic.
        let r = LeanRunner::new(PathBuf::from("lean"), 0);
        let _ = r.export(&fixture_path("minimal.lean"));
    }
}
