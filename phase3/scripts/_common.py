"""Shared helpers for the Phase H pipeline.

All pipeline scripts assume the working directory is the Phase H root
(``phase3/``) or the project root (``specmut/``).  The constants below resolve
paths relative to this file so scripts can be invoked from either location.
"""

from __future__ import annotations

import os
import shutil
import sys
from pathlib import Path

PHASE3 = Path(__file__).resolve().parent.parent
PROJECT_ROOT = PHASE3.parent

BENCHMARKS = PHASE3 / "benchmarks"
GENERATED = PHASE3 / "generated"
LEAN_RESULTS = PHASE3 / "lean_results"
SPECMUT_RESULTS = PHASE3 / "specmut_results"
AGGREGATE = PHASE3 / "aggregate"
PROMPTS = PHASE3 / "prompts"

DEFAULTS = {
    "model_bound": 2,
    "epsilon": 1.0,
    "lean_timeout_sec": 60,
    "specmut_timeout_sec": 120,
    "models": ["deepseek", "qwen"],
    "rounds": [1, 2, 3],
    "weak_tau_threshold": 0.3,
}


def specmut_bin() -> Path:
    """Locate the specmut release binary, building it if necessary."""
    p = PROJECT_ROOT / "target" / "release" / "specmut"
    if not p.exists():
        sys.exit(f"specmut binary not found at {p}; run 'cargo build --release' first")
    return p


def ensure_lean_on_path() -> None:
    """Prepend ~/.elan/bin to PATH if elan-installed Lean is present.

    The Lean exporter (Phase A) is invoked by specmut as a subprocess and
    needs `lean` on PATH.  We don't fail if Lean is missing — lean_check.py
    will report that condition.
    """
    elan = Path.home() / ".elan" / "bin"
    if elan.exists() and shutil.which("lean") is None:
        os.environ["PATH"] = f"{elan}{os.pathsep}{os.environ.get('PATH','')}"


def list_tasks() -> list[str]:
    return sorted(p.name for p in BENCHMARKS.iterdir() if p.is_dir())


def list_models() -> list[str]:
    if not GENERATED.exists():
        return []
    return sorted(p.name for p in GENERATED.iterdir() if p.is_dir())


def list_versions(model: str, task: str) -> list[int]:
    d = GENERATED / model / task
    if not d.exists():
        return []
    out = []
    for f in d.iterdir():
        if f.suffix == ".lean" and f.stem.startswith("v"):
            try:
                out.append(int(f.stem[1:]))
            except ValueError:
                continue
    return sorted(out)


def reference_path(task: str) -> Path:
    return BENCHMARKS / task / "reference.lean"


def analyzable_reference_path(task: str) -> Path:
    """Return the projection produced by ``scripts/reduce.py``.

    This is what ``run_specmut.py`` analyzes for the human-reference column.
    The verbatim ``reference.lean`` carries provenance; the projection carries
    only the structure specmut's bounded analysis can consume.
    """
    return BENCHMARKS / task / "reference_analyzable.lean"


def provenance_path(task: str) -> Path:
    return BENCHMARKS / task / "provenance.toml"


def load_provenance(task: str) -> dict | None:
    """Best-effort load of a task's provenance.toml.

    Returns None when the file is missing (e.g., synthetic task with no
    upstream).  We use tomllib (stdlib in 3.11+).
    """
    p = provenance_path(task)
    if not p.exists():
        return None
    try:
        import tomllib  # type: ignore[import-not-found]
        return tomllib.loads(p.read_text())
    except Exception:
        return None


def generated_path(model: str, task: str, version: int) -> Path:
    return GENERATED / model / task / f"v{version}.lean"


def lean_result_path(model: str, task: str, version: int) -> Path:
    return LEAN_RESULTS / model / task / f"v{version}.json"


def specmut_result_path(source: str, task: str, version: int | None = None) -> Path:
    """source = 'human' or '<model_name>'."""
    if source == "human":
        return SPECMUT_RESULTS / "human" / task / "reference.json"
    assert version is not None
    return SPECMUT_RESULTS / source / task / f"v{version}.json"
