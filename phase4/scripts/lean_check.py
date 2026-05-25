#!/usr/bin/env python3
"""Phase 4 Stage 2: Lean compile/typecheck for every .lean artifact.

Runs ``lean <file>`` per artifact, categorizing exit code + output into one
of ``compile_success``, ``compile_failure``, or ``compile_timeout``.  Pure
``sorry`` warnings + unused-variable lints are tolerated; only error lines
flip success to false.

Covers four file classes:
  - generated/baseline/{model}/{task}/rep_NN.lean
  - generated/repaired/{model}/{task}/rep_NN.lean
  - benchmarks/{task}/reference.lean
  - benchmarks/{task}/{trivial,partial}.lean

Each writes a JSON sidecar with full classification + timing + warnings.
"""

from __future__ import annotations

import argparse
import json
import re
import shutil
import subprocess
import sys
import time
from concurrent.futures import ProcessPoolExecutor, as_completed
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from _common import (
    LEAN_RESULTS,
    PHASE4,
    baseline_path,
    ensure_lean_on_path,
    lean_result_path,
    list_tasks,
    load_config,
    model_slots,
    partial_path,
    reference_path,
    repaired_path,
    replicate_indices,
    trivial_path,
)

ERROR_LINE_RE = re.compile(r":\d+:\d+: error(?:\([^)]*\))?:.*")
WARN_LINE_RE = re.compile(r":\d+:\d+: warning:.*")


def _categorize(returncode: int, combined: str, timeout: bool) -> tuple[str, list[str], list[str]]:
    """Classify a lean run into (status, errors, warnings)."""
    errors = ERROR_LINE_RE.findall(combined)
    warnings = WARN_LINE_RE.findall(combined)
    if timeout:
        return "compile_timeout", errors, warnings
    if returncode == 0 and not errors:
        return "compile_success", errors, warnings
    return "compile_failure", errors, warnings


def run_lean(target: Path, timeout: int) -> dict:
    if shutil.which("lean") is None:
        return {
            "status": "compile_failure",
            "errors": ["lean toolchain not found"],
            "warnings": [],
            "elapsed_sec": 0.0,
            "exit_code": -1,
        }
    start = time.monotonic()
    try:
        proc = subprocess.run(["lean", str(target)], capture_output=True,
                              text=True, timeout=timeout)
        timed_out = False
    except subprocess.TimeoutExpired:
        proc = None
        timed_out = True
    elapsed = round(time.monotonic() - start, 3)
    combined = (proc.stdout + proc.stderr) if proc else ""
    rc = proc.returncode if proc else -2
    status, errors, warnings = _categorize(rc, combined, timed_out)
    return {
        "status": status,
        "errors": errors,
        "warnings": warnings,
        "elapsed_sec": elapsed,
        "exit_code": rc,
    }


def check_one(spec_path: Path, out_path: Path, *, force: bool, timeout: int,
              tags: dict) -> str:
    if out_path.exists() and not force:
        return "cached"
    if not spec_path.exists():
        return "missing"
    result = run_lean(spec_path, timeout=timeout)
    result["file"] = str(spec_path.relative_to(PHASE4.parent))
    result.update(tags)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(result, indent=2))
    return result["status"]


def _check_worker(args: tuple) -> tuple[Path, str]:
    """Module-level worker wrapper for ProcessPoolExecutor (must be picklable)."""
    spec_path, out_path, force, timeout, tags = args
    ensure_lean_on_path()  # each subprocess starts with a fresh environment
    status = check_one(spec_path, out_path, force=force, timeout=timeout, tags=tags)
    return spec_path, status


def _collect_work(args, *, timeout: int, tasks, models) -> list[tuple]:
    """Build the (spec_path, out_path, force, timeout, tags) work list."""
    work = []
    if args.condition in ("all", "references"):
        for task in tasks:
            spec = reference_path(task)
            out = lean_result_path("references", None, task)
            tags = {"condition": "references", "task": task}
            work.append((spec, out, args.force, timeout, tags))
    if args.condition in ("all", "controls"):
        for task in tasks:
            for kind, path_fn in (("trivial", trivial_path),
                                  ("partial", partial_path)):
                spec = path_fn(task)
                out = lean_result_path("controls", None, task, control_type=kind)
                tags = {"condition": "controls", "task": task,
                        "control_type": kind}
                work.append((spec, out, args.force, timeout, tags))
    if args.condition in ("all", "baseline", "repaired"):
        for cond in (["baseline", "repaired"] if args.condition == "all"
                     else [args.condition]):
            path_fn = baseline_path if cond == "baseline" else repaired_path
            for model in models:
                for task in tasks:
                    for r in list(replicate_indices()):
                        spec = path_fn(model, task, r)
                        if not spec.exists():
                            continue
                        out = lean_result_path(cond, model, task, replicate=r)
                        tags = {"condition": cond, "task": task,
                                "model": model, "replicate": r}
                        work.append((spec, out, args.force, timeout, tags))
    return work


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--condition", choices=["all", "baseline", "repaired",
                                            "references", "controls"],
                    default="all")
    ap.add_argument("--task")
    ap.add_argument("--model")
    ap.add_argument("--force", action="store_true")
    ap.add_argument("--parallel", type=int, default=1,
                    help="number of concurrent lean processes (default 1)")
    args = ap.parse_args()
    ensure_lean_on_path()
    config = load_config()
    timeout = config["analysis"]["lean_timeout_sec"]

    tasks = [args.task] if args.task else list_tasks()
    slots = model_slots()
    if args.model:
        slots = [s for s in slots if s[1]["name"] == args.model or s[0] == args.model]
    models = [s[1]["name"] for s in slots]
    summary: dict[str, int] = {}

    def bump(s: str) -> None:
        summary[s] = summary.get(s, 0) + 1

    work = _collect_work(args, timeout=timeout, tasks=tasks, models=models)
    total = len(work)
    print(f"  {total} files to check  ({'sequential' if args.parallel <= 1 else f'parallel={args.parallel}'})")

    if args.parallel <= 1:
        for w in work:
            spec, status = _check_worker(w)
            bump(status)
            print(f"  [{status:18}] {spec.relative_to(PHASE4.parent)}")
    else:
        done = 0
        with ProcessPoolExecutor(max_workers=args.parallel) as ex:
            futures = {ex.submit(_check_worker, w): w[0] for w in work}
            for fut in as_completed(futures):
                spec = futures[fut]
                try:
                    _, status = fut.result()
                except Exception as e:
                    status = f"worker_error({type(e).__name__})"
                bump(status)
                done += 1
                print(f"  [{status:18}] ({done}/{total}) {spec.relative_to(PHASE4.parent)}")

    print(f"\nLean check: {summary}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
