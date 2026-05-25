"""Shared helpers for the Phase 4 pipeline.

Constants resolve relative to this file so scripts work whether invoked from
phase4/ or the project root.  The config is loaded once and cached.
"""

from __future__ import annotations

import hashlib
import os
import shutil
import sys
from functools import lru_cache
from pathlib import Path

PHASE4 = Path(__file__).resolve().parent.parent
PROJECT_ROOT = PHASE4.parent

BENCHMARKS = PHASE4 / "benchmarks"
GENERATED = PHASE4 / "generated"
LEAN_RESULTS = PHASE4 / "lean_results"
SPECMUT_RESULTS = PHASE4 / "specmut_results"
FEEDBACK = PHASE4 / "feedback"
DETERMINISM = PHASE4 / "determinism"
AGGREGATE = PHASE4 / "aggregate"

def _resolve_config_path() -> Path:
    """Honor PHASE4_CONFIG env var so a variant config (e.g. the qwen-only
    template-constrained run) can be selected without forking every script.

    PHASE4_CONFIG may be absolute or relative to the project root.
    """
    env = os.environ.get("PHASE4_CONFIG")
    if env:
        p = Path(env)
        if not p.is_absolute():
            p = (PROJECT_ROOT / p).resolve()
        if not p.exists():
            sys.exit(f"PHASE4_CONFIG={env} but {p} does not exist")
        return p
    return PHASE4 / "config.toml"


CONFIG_PATH = _resolve_config_path()


@lru_cache(maxsize=1)
def load_config() -> dict:
    import tomllib
    return tomllib.loads(CONFIG_PATH.read_text())


def ollama_url(config: dict | None = None) -> str:
    """Model-server URL for generation requests.

    Read from the OLLAMA_URL environment variable so no host/port is stored
    in the repository.  Set it for your environment, e.g.:
        export OLLAMA_URL=http://host:port
    Falls back to [generation].ollama_url only if that key is present in the
    active config (it is intentionally absent in the published configs).
    """
    env = os.environ.get("OLLAMA_URL")
    if env:
        return env
    cfg = config if config is not None else load_config()
    url = cfg.get("generation", {}).get("ollama_url")
    if not url:
        sys.exit("OLLAMA_URL is not set — export OLLAMA_URL=http://host:port "
                 "to point at your model server.")
    return url


def model_slots() -> list[tuple[str, dict]]:
    """Return [(slot_name, model_block), ...] in slot order m1, m2, m3."""
    models = load_config()["models"]
    return [(k, models[k]) for k in sorted(models.keys())]


def model_names() -> list[str]:
    return [m[1]["name"] for m in model_slots()]


def list_tasks() -> list[str]:
    return sorted(p.name for p in BENCHMARKS.iterdir() if p.is_dir())


def reference_path(task: str) -> Path:
    return BENCHMARKS / task / "reference.lean"


def trivial_path(task: str) -> Path:
    return BENCHMARKS / task / "trivial.lean"


def partial_path(task: str) -> Path:
    return BENCHMARKS / task / "partial.lean"


def prompt_path(task: str) -> Path:
    """Path to the per-task prompt.

    The qwen-only template-constrained variant uses a stricter prompt
    file (``prompt_qwen.txt``); routing is controlled by the
    ``[prompts] filename`` setting in the active config, defaulting to
    the original ``prompt.txt`` when unset (so the frozen experiment is
    unaffected).
    """
    try:
        fname = load_config().get("prompts", {}).get("filename", "prompt.txt")
    except Exception:
        fname = "prompt.txt"
    return BENCHMARKS / task / fname


def scaffold_path(task: str) -> Path:
    """Path to the per-task scaffold (axioms + helper predicates).

    Generated baseline/repaired files are formed by concatenating this
    scaffold (when present) with the LLM-produced theorem statements.
    This is the structural shift that lets the LLM emit theorem-only
    output while specmut still sees a self-contained file with all the
    vocabulary it needs to mutate.

    Returns the path even if the file does not exist; callers should
    check ``.exists()`` and fall back to non-scaffolded behavior so the
    original (non-qwen-only) config still works.
    """
    return BENCHMARKS / task / "scaffold.lean"


def baseline_path(model: str, task: str, replicate: int) -> Path:
    return GENERATED / "baseline" / _model_dir(model) / task / f"rep_{replicate:02d}.lean"


def repaired_path(model: str, task: str, replicate: int) -> Path:
    return GENERATED / "repaired" / _model_dir(model) / task / f"rep_{replicate:02d}.lean"


def baseline_meta_path(model: str, task: str, replicate: int) -> Path:
    return baseline_path(model, task, replicate).with_suffix(".meta.json")


def repaired_meta_path(model: str, task: str, replicate: int) -> Path:
    return repaired_path(model, task, replicate).with_suffix(".meta.json")


def lean_result_path(condition: str, model: str | None, task: str,
                     replicate: int | None = None,
                     control_type: str | None = None) -> Path:
    """Path for a single lean_check JSON.

    condition: "baseline" | "repaired" | "references" | "controls"
    """
    if condition == "references":
        return LEAN_RESULTS / "references" / f"{task}.json"
    if condition == "controls":
        assert control_type is not None
        return LEAN_RESULTS / "controls" / f"{task}_{control_type}.json"
    assert model is not None and replicate is not None
    return LEAN_RESULTS / condition / _model_dir(model) / task / f"rep_{replicate:02d}.json"


def specmut_result_path(condition: str, model: str | None, task: str,
                        replicate: int | None = None,
                        control_type: str | None = None) -> Path:
    if condition == "references":
        return SPECMUT_RESULTS / "references" / f"{task}.json"
    if condition == "controls":
        assert control_type is not None
        return SPECMUT_RESULTS / "controls" / f"{task}_{control_type}.json"
    assert model is not None and replicate is not None
    return SPECMUT_RESULTS / condition / _model_dir(model) / task / f"rep_{replicate:02d}.json"


def feedback_path(model: str, task: str, replicate: int) -> Path:
    return FEEDBACK / _model_dir(model) / task / f"rep_{replicate:02d}.json"


def _model_dir(model: str) -> str:
    """Filesystem-safe directory name for a model.

    Ollama tags include `:` (e.g. ``qwen2.5-coder:7b``) which is fine on
    Linux but causes confusion in tooling.  Replace with ``__``.
    """
    return model.replace("/", "_").replace(":", "__")


def baseline_seed(base_seed: int, replicate_index: int) -> int:
    """Deterministic seed scheme from the spec."""
    return base_seed * 1000 + replicate_index


def repair_seed(base_seed: int, replicate_index: int) -> int:
    return base_seed * 1000 + replicate_index + 500


def prompt_sha256(prompt_text: str) -> str:
    return hashlib.sha256(prompt_text.encode("utf-8")).hexdigest()


def specmut_bin() -> Path:
    p = PROJECT_ROOT / "target" / "release" / "specmut"
    if not p.exists():
        sys.exit(f"specmut binary not found at {p}; cargo build --release first")
    return p


def ensure_lean_on_path() -> None:
    elan = Path.home() / ".elan" / "bin"
    if elan.exists() and shutil.which("lean") is None:
        os.environ["PATH"] = f"{elan}{os.pathsep}{os.environ.get('PATH','')}"


def replicate_indices() -> range:
    cfg = load_config()
    return range(1, cfg["experiment"]["replicates"] + 1)
