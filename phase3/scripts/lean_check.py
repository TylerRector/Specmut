#!/usr/bin/env python3
"""Phase H Stage 2: Lean compile/typecheck for every generated spec.

Invokes ``lean <file>`` as a subprocess, captures stdout+stderr+exit code, and
writes a JSON result per file at ``lean_results/{model}/{task}/v{round}.json``.

Warnings from ``sorry`` are tracked separately from hard errors.  A spec with
only ``sorry`` warnings still counts as ``typecheck_success: true``; only a
non-zero exit code (or no Lean toolchain) flips success to ``false``.

Idempotent: existing result JSON is skipped unless ``--force`` is passed.
"""

from __future__ import annotations

import argparse
import json
import re
import shutil
import subprocess
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from _common import (
    DEFAULTS,
    LEAN_RESULTS,
    PHASE3,
    analyzable_reference_path,
    ensure_lean_on_path,
    generated_path,
    lean_result_path,
    list_models,
    list_tasks,
    list_versions,
    reference_path,
)

ERROR_RE = re.compile(r":\d+:\d+: error:")
WARN_RE = re.compile(r":\d+:\d+: warning:")


def run_lean(target: Path, timeout: int) -> dict:
    if shutil.which("lean") is None:
        return {
            "compile_success": False,
            "typecheck_success": False,
            "errors": ["lean toolchain not found on PATH"],
            "warnings": [],
            "elapsed_sec": 0.0,
            "exit_code": -1,
        }
    start = time.monotonic()
    try:
        proc = subprocess.run(
            ["lean", str(target)],
            capture_output=True,
            text=True,
            timeout=timeout,
        )
    except subprocess.TimeoutExpired:
        return {
            "compile_success": False,
            "typecheck_success": False,
            "errors": [f"lean timeout after {timeout}s"],
            "warnings": [],
            "elapsed_sec": float(timeout),
            "exit_code": -2,
        }
    elapsed = time.monotonic() - start
    combined = proc.stdout + proc.stderr
    errors = [m.group(0) + combined[m.end():].splitlines()[0] for m in ERROR_RE.finditer(combined)]
    warnings = [m.group(0) + combined[m.end():].splitlines()[0] for m in WARN_RE.finditer(combined)]
    typecheck_ok = proc.returncode == 0 and not errors
    return {
        "compile_success": proc.returncode == 0,
        "typecheck_success": typecheck_ok,
        "errors": errors,
        "warnings": warnings,
        "elapsed_sec": round(elapsed, 3),
        "exit_code": proc.returncode,
    }


def check_one(spec_path: Path, out_path: Path, *, force: bool, timeout: int,
              model: str, task: str, version: int) -> str:
    if out_path.exists() and not force:
        return "cached"
    if not spec_path.exists():
        return "missing"
    result = run_lean(spec_path, timeout=timeout)
    result["file"] = str(spec_path.relative_to(PHASE3.parent))
    result["model"] = model
    result["task"] = task
    result["version"] = version
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(result, indent=2))
    return "ok" if result["typecheck_success"] else "fail"


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--timeout", type=int, default=DEFAULTS["lean_timeout_sec"])
    ap.add_argument("--task")
    ap.add_argument("--model")
    ap.add_argument("--force", action="store_true")
    ap.add_argument("--skip-reference", action="store_true",
                    help="skip lean check for human references (they are sanity-checked by hand)")
    args = ap.parse_args()
    ensure_lean_on_path()

    tasks = [args.task] if args.task else list_tasks()
    models = [args.model] if args.model else list_models()

    summary = {"ok": 0, "fail": 0, "cached": 0, "missing": 0}

    # References:
    # - benchmarks/{task}/reference.lean (verbatim GitHub artifact)
    # - benchmarks/{task}/reference_analyzable.lean (reduce.py projection)
    # Both are typechecked separately so the report can distinguish "real
    # spec compiles" from "analyzable projection compiles".
    if not args.skip_reference:
        for task in tasks:
            spec = reference_path(task)
            out = LEAN_RESULTS / "human" / task / "reference.json"
            status = check_one(spec, out, force=args.force, timeout=args.timeout,
                               model="human", task=task, version=0)
            summary[status] = summary.get(status, 0) + 1
            print(f"  [{status:7}] {spec.relative_to(PHASE3.parent)}")
            ana_spec = analyzable_reference_path(task)
            ana_out = LEAN_RESULTS / "human" / task / "reference_analyzable.json"
            status = check_one(ana_spec, ana_out, force=args.force, timeout=args.timeout,
                               model="human", task=task, version=0)
            summary[status] = summary.get(status, 0) + 1
            print(f"  [{status:7}] {ana_spec.relative_to(PHASE3.parent)}")

    for model in models:
        for task in tasks:
            for v in list_versions(model, task):
                spec = generated_path(model, task, v)
                out = lean_result_path(model, task, v)
                status = check_one(spec, out, force=args.force, timeout=args.timeout,
                                   model=model, task=task, version=v)
                summary[status] = summary.get(status, 0) + 1
                print(f"  [{status:7}] {spec.relative_to(PHASE3.parent)}")

    print(f"\nLean check stage: {summary}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
