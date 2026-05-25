#!/usr/bin/env python3
"""Phase 4 Stage 4: validate that specmut is deterministic on identical input.

Selects 5 successfully-analyzed baseline files (one per task when possible),
runs specmut 3 times on each, and verifies all semantic fields are bitwise
identical across runs.  Timing fields (``timing``, ``elapsed_sec``,
``runtime_sec``) are excluded — wall-clock varies and is not a correctness
signal.

If any other field differs across runs, the validation halts the pipeline
because variance estimates downstream would be contaminated.  Logs every
mismatch field-by-field.
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from _common import (
    DETERMINISM,
    PHASE4,
    SPECMUT_RESULTS,
    ensure_lean_on_path,
    list_tasks,
    load_config,
    specmut_bin,
)


IGNORED_DEFAULT = (
    "timing", "elapsed_sec", "runtime_sec",
    "enumeration_ms", "analysis_ms",
    "_ms", "_sec", "_ns", "_us",
    "timestamp", "timestamp_utc",
)


def _is_ignored(key: str, ignored: set[str]) -> bool:
    """Match a key against ignored entries.

    An ignored entry that starts with ``_`` is treated as a SUFFIX
    matcher (e.g. ``_ms`` matches ``enumeration_ms``, ``analysis_ms``).
    Anything else is an exact-name match.  This is what fixes the prior
    false-positive determinism failure where ``metrics.enumeration_ms``
    flipped runs to "non_deterministic" even though every semantic
    field — tau, killed/survived sets, theorem slice status — was
    bitwise identical across runs.
    """
    if key in ignored:
        return True
    for entry in ignored:
        if entry.startswith("_") and key.endswith(entry):
            return True
    return False


def _scrub(obj, ignored: set[str]):
    """Recursively drop any dict key matching ``ignored`` (exact or suffix)."""
    if isinstance(obj, dict):
        return {k: _scrub(v, ignored) for k, v in obj.items()
                if not _is_ignored(k, ignored)}
    if isinstance(obj, list):
        return [_scrub(x, ignored) for x in obj]
    return obj


def _diff_paths(a, b, prefix: str = "") -> list[str]:
    """Return list of paths where a and b differ (after scrubbing)."""
    if type(a) is not type(b):
        return [f"{prefix} types {type(a).__name__} vs {type(b).__name__}"]
    if isinstance(a, dict):
        out = []
        for k in set(a) | set(b):
            out.extend(_diff_paths(a.get(k), b.get(k), f"{prefix}.{k}"))
        return out
    if isinstance(a, list):
        if len(a) != len(b):
            return [f"{prefix} list len {len(a)} vs {len(b)}"]
        out = []
        for i, (x, y) in enumerate(zip(a, b)):
            out.extend(_diff_paths(x, y, f"{prefix}[{i}]"))
        return out
    if a != b:
        return [f"{prefix}: {a!r} vs {b!r}"]
    return []


def select_files(config: dict) -> list[Path]:
    """Pick one successfully-analyzed baseline per task, up to files_to_test.

    Falls back to the reference spec when no baseline has been analyzed yet
    (allows the determinism check to run even before any LLM generation).
    """
    target = config["determinism"]["files_to_test"]
    selected: list[Path] = []
    for task in list_tasks():
        # Prefer a baseline that analyzed successfully.
        baseline_root = SPECMUT_RESULTS / "baseline"
        found = None
        if baseline_root.exists():
            for f in sorted(baseline_root.rglob(f"*/{task}/rep_*.json")):
                try:
                    r = json.loads(f.read_text())
                    if r.get("analysis_status") == "success":
                        found = Path(r["file"]).resolve()
                        if not found.is_absolute():
                            found = (PHASE4.parent / r["file"]).resolve()
                        break
                except Exception:
                    continue
        if found is None:
            ref = PHASE4 / "benchmarks" / task / "reference.lean"
            if ref.exists():
                found = ref
        if found is not None:
            selected.append(found)
        if len(selected) >= target:
            break
    return selected


def run_one(spec_path: Path, *, model_bound: int, epsilon: float,
            timeout: int) -> dict | None:
    bin_ = specmut_bin()
    tmp_out = Path("/tmp") / f"phase4_det_{time.monotonic_ns()}.json"
    cmd = [str(bin_), "analyze", str(spec_path), "--lean-full",
           "-n", str(model_bound), "-e", str(epsilon),
           "-f", "json", "-o", str(tmp_out)]
    try:
        proc = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        return None
    if proc.returncode != 0 or not tmp_out.exists() or tmp_out.stat().st_size == 0:
        if tmp_out.exists():
            tmp_out.unlink()
        return None
    raw = json.loads(tmp_out.read_text())
    tmp_out.unlink()
    return raw


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--force", action="store_true")
    args = ap.parse_args()
    ensure_lean_on_path()
    config = load_config()
    n = config["analysis"]["n"]
    eps = config["analysis"]["epsilon"]
    timeout = config["analysis"]["specmut_timeout_sec"]
    runs_per = config["determinism"]["runs_per_file"]
    ignored = set(config["determinism"]["ignored_fields"])

    log_path = DETERMINISM / "validation_log.json"
    log_path.parent.mkdir(parents=True, exist_ok=True)
    if log_path.exists() and not args.force:
        prev = json.loads(log_path.read_text())
        if prev.get("all_deterministic") is True:
            print(f"  [cached] determinism already validated: {log_path}")
            return 0

    files = select_files(config)
    if not files:
        sys.exit("no analyzable files found for determinism check")

    print(f"  Running determinism check on {len(files)} files × {runs_per} runs...")
    per_file: list[dict] = []
    failures: list[dict] = []
    all_ok = True

    for fp in files:
        outputs = []
        runs_meta = []
        run_failed = False
        for r in range(runs_per):
            start = time.monotonic()
            raw = run_one(fp, model_bound=n, epsilon=eps, timeout=timeout)
            elapsed = round(time.monotonic() - start, 3)
            runs_meta.append({"run": r, "elapsed_sec": elapsed,
                              "ok": raw is not None})
            if raw is None:
                run_failed = True
                break
            outputs.append(_scrub(raw, ignored))
        file_entry = {"file": str(fp.relative_to(PHASE4.parent)
                                   if fp.is_relative_to(PHASE4.parent) else fp),
                      "runs": runs_meta}
        if run_failed:
            file_entry["status"] = "subprocess_failure"
            all_ok = False
            failures.append({"file": str(fp), "reason": "specmut failed mid-validation"})
        else:
            diffs = []
            for i in range(1, len(outputs)):
                diffs.extend(_diff_paths(outputs[0], outputs[i]))
            if diffs:
                file_entry["status"] = "non_deterministic"
                file_entry["diffs"] = diffs[:20]
                all_ok = False
                failures.append({"file": str(fp), "n_diffs": len(diffs),
                                 "sample": diffs[:5]})
            else:
                file_entry["status"] = "deterministic"
        per_file.append(file_entry)
        print(f"    [{file_entry['status']}] {fp.name}")

    log = {
        "files_tested": len(files),
        "runs_per_file": runs_per,
        "ignored_fields": sorted(ignored),
        "all_deterministic": all_ok,
        "per_file": per_file,
        "failures": failures,
    }
    log_path.write_text(json.dumps(log, indent=2))
    print(f"\n  Wrote {log_path}")
    if not all_ok:
        print("  !! NON-DETERMINISM DETECTED — pipeline downstream stats are invalidated.")
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
