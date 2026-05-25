#!/usr/bin/env python3
"""Phase 4 Stage 3: specmut analysis with Phase 4 outcome classification.

Invokes specmut on every artifact that passed Lean typecheck and emits a
JSON record with the Phase 4 extended schema:

  - analysis_status: success | timeout | model_bound_exceeded
                     | translation_failed | unsupported_constructs
                     | tau_zero | insufficient_mutations
  - runtime_sec, model_space_estimate, theorem_coverage, slice_success_rate
  - per_theorem entries with slice_status

Decisions:
  - Lean files with no preceding lean_result are skipped (we won't analyze
    files that haven't gone through stage 2).
  - Files with status != compile_success are skipped here — they cannot be
    analyzed and downstream aggregation knows that from lean_results.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
import time
from concurrent.futures import ProcessPoolExecutor, as_completed
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from _common import (
    LEAN_RESULTS,
    PHASE4,
    SPECMUT_RESULTS,
    baseline_path,
    ensure_lean_on_path,
    lean_result_path,
    list_tasks,
    load_config,
    model_slots,
    partial_path,
    reference_path,
    repaired_path,
    specmut_bin,
    specmut_result_path,
    trivial_path,
)

WEAK_THRESHOLD_DEFAULT = 0.3


# Stderr patterns that map to specific analysis_status values.
STATUS_PATTERNS = [
    (re.compile(r"model bound \d+ produces too many models"), "model_bound_exceeded"),
    (re.compile(r"no axioms emitted|skipped \d+ theorems, \d+ predicates"),
        "translation_failed"),
    (re.compile(r"outside the supported first-order subset"), "unsupported_constructs"),
]


def _classify_error(stderr: str) -> str:
    for pat, label in STATUS_PATTERNS:
        if pat.search(stderr):
            return label
    return "translation_failed"


def _project_tightness(raw: dict, *, weak_threshold: float) -> dict:
    """Project raw specmut JSON into the Phase 4 record shape.

    Handles both the Sliced (theorem_slices) and Global (top-level tightness)
    output forms.  Global mode is treated as a single synthetic slice.
    """
    if "theorem_slices" in raw:
        slices = raw["theorem_slices"]
        summary = raw.get("summary", {})
        per_theorem = []
        analyzed_slices = 0
        weak_theorems = []
        total_mut = 0
        total_killed = 0
        total_alive = 0
        for s in slices:
            if s["status"] != "analyzed":
                per_theorem.append({
                    "name": s["theorem_name"],
                    "tau": None,
                    "kill_rate": None,
                    "surviving_mutants": None,
                    "total_mutants": None,
                    "slice_status": s.get("skip_reason", "skipped"),
                    "model_space_size": s.get("model_count"),
                })
                continue
            t = s["tightness"]
            n = t["killed"] + t["alive"]
            kr = (t["killed"] / n) if n else 0.0
            total_mut += n; total_killed += t["killed"]; total_alive += t["alive"]
            analyzed_slices += 1
            if t["score"] < weak_threshold:
                weak_theorems.append(s["theorem_name"])
            per_theorem.append({
                "name": s["theorem_name"],
                "tau": t["score"],
                "kill_rate": kr,
                "surviving_mutants": t["alive"],
                "total_mutants": n,
                "slice_status": "success",
                "model_space_size": s.get("model_count"),
            })
        theorem_coverage = (analyzed_slices / len(slices)) if slices else 0.0
        slice_success_rate = theorem_coverage
        return {
            "analysis_mode": "per_theorem",
            "average_tau": summary.get("mean_tightness", 0.0),
            "min_tau": summary.get("min_tightness", 0.0),
            "max_tau": summary.get("max_tightness", 0.0),
            "tau_variance": summary.get("tightness_variance", 0.0),
            "theorem_count": len(slices),
            "analyzed_slices": analyzed_slices,
            "total_mutants": total_mut,
            "killed_mutants": total_killed,
            "surviving_mutants": total_alive,
            "kill_rate": (total_killed / total_mut) if total_mut else 0.0,
            "weak_theorems": weak_theorems,
            "per_theorem": per_theorem,
            "theorem_coverage": theorem_coverage,
            "slice_success_rate": slice_success_rate,
            "model_space_estimate": raw.get("parameters", {}).get("models_enumerated", 0),
            "taxonomy": summary.get("taxonomy", {}),
        }
    # Global path.
    t = raw.get("tightness", {})
    n = t.get("killed", 0) + t.get("alive", 0)
    kr = (t.get("killed", 0) / n) if n else 0.0
    lt = raw.get("lean_translation", {}) or {}
    translated = lt.get("translated_theorems", []) or []
    weak = ["(global)"] if (t.get("score", 0.0) < weak_threshold) else []
    return {
        "analysis_mode": "global",
        "average_tau": t.get("score", 0.0),
        "min_tau": t.get("score", 0.0),
        "max_tau": t.get("score", 0.0),
        "tau_variance": 0.0,
        "theorem_count": len(translated),
        "analyzed_slices": 1 if t else 0,
        "total_mutants": n,
        "killed_mutants": t.get("killed", 0),
        "surviving_mutants": t.get("alive", 0),
        "kill_rate": kr,
        "weak_theorems": weak,
        "per_theorem": [{
            "name": "(global)",
            "tau": t.get("score", 0.0),
            "kill_rate": kr,
            "surviving_mutants": t.get("alive", 0),
            "total_mutants": n,
            "slice_status": "success" if n > 0 else "insufficient_mutations",
            "model_space_size": raw.get("parameters", {}).get("models_enumerated", 0),
        }],
        "theorem_coverage": 1.0 if translated else 0.0,
        "slice_success_rate": 1.0 if (t and n > 0) else 0.0,
        "model_space_estimate": raw.get("parameters", {}).get("models_enumerated", 0),
        "taxonomy": {},
    }


def _finalize_status(record: dict) -> str:
    """Assign analysis_status per the priority order in the spec."""
    if record.get("subprocess_status") == "timeout":
        return "timeout"
    if record.get("subprocess_status") == "specmut_error":
        return record.get("error_category", "translation_failed")
    if record["total_mutants"] == 0:
        return "insufficient_mutations" if record["theorem_count"] else "translation_failed"
    if record["average_tau"] == 0.0 and record["surviving_mutants"] > 0:
        return "tau_zero"
    if record["total_mutants"] < 3:
        return "insufficient_mutations"
    return "success"


def run_specmut(spec_path: Path, *, model_bound: int, epsilon: float,
                timeout: int) -> dict:
    bin_ = specmut_bin()
    tmp_out = Path("/tmp") / f"phase4_specmut_{time.monotonic_ns()}.json"
    cmd = [
        str(bin_), "analyze", str(spec_path),
        "--lean-full",
        "-n", str(model_bound),
        "-e", str(epsilon),
        "-f", "json",
        "-o", str(tmp_out),
    ]
    start = time.monotonic()
    try:
        proc = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout)
        timed_out = False
    except subprocess.TimeoutExpired:
        proc = None
        timed_out = True
    elapsed = round(time.monotonic() - start, 3)
    if timed_out:
        return {"subprocess_status": "timeout", "runtime_sec": elapsed,
                "raw_stderr": ""}
    if proc.returncode != 0 or not tmp_out.exists() or tmp_out.stat().st_size == 0:
        msg = (proc.stderr or proc.stdout or "").strip().splitlines()
        last = msg[-1][:200] if msg else "(no output)"
        category = _classify_error("\n".join(msg))
        if tmp_out.exists():
            tmp_out.unlink()
        return {"subprocess_status": "specmut_error",
                "error_category": category,
                "specmut_error": last,
                "runtime_sec": elapsed,
                "raw_stderr": "\n".join(msg)[:1000]}
    raw = json.loads(tmp_out.read_text())
    tmp_out.unlink()
    return {"subprocess_status": "ok", "raw": raw, "runtime_sec": elapsed}


def _lean_passed(lr_path: Path) -> bool:
    if not lr_path.exists():
        return False
    try:
        return json.loads(lr_path.read_text()).get("status") == "compile_success"
    except Exception:
        return False


def _analyze_worker(args: tuple) -> tuple[Path, str]:
    """Picklable worker for ProcessPoolExecutor."""
    (spec_path, lr, out, tags, model_bound, epsilon, timeout, force,
     weak_threshold) = args
    ensure_lean_on_path()
    status = analyze_one(spec_path, lr, out, tags,
                         model_bound=model_bound, epsilon=epsilon,
                         timeout=timeout, force=force,
                         weak_threshold=weak_threshold)
    return spec_path, status


def analyze_one(spec_path: Path, lean_result: Path, out_path: Path,
                tags: dict, *, model_bound: int, epsilon: float, timeout: int,
                force: bool, weak_threshold: float) -> str:
    if out_path.exists() and not force:
        return "cached"
    if not spec_path.exists():
        return "missing"
    if not _lean_passed(lean_result):
        # Lean failed — record a skipped analysis so the file is accounted for.
        record = {
            "file": str(spec_path.relative_to(PHASE4.parent)),
            "analysis_status": "skipped_lean_failure",
            "runtime_sec": 0.0,
            **tags,
        }
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_path.write_text(json.dumps(record, indent=2))
        return "skipped_lean_failure"

    sub = run_specmut(spec_path, model_bound=model_bound, epsilon=epsilon,
                      timeout=timeout)
    if sub["subprocess_status"] == "ok":
        proj = _project_tightness(sub["raw"], weak_threshold=weak_threshold)
        record = {
            "file": str(spec_path.relative_to(PHASE4.parent)),
            "runtime_sec": sub["runtime_sec"],
            **proj,
            **tags,
        }
        record["analysis_status"] = _finalize_status(
            record | {"subprocess_status": "ok"}
        )
    else:
        record = {
            "file": str(spec_path.relative_to(PHASE4.parent)),
            "runtime_sec": sub["runtime_sec"],
            "average_tau": 0.0, "min_tau": 0.0, "max_tau": 0.0,
            "tau_variance": 0.0, "theorem_count": 0,
            "total_mutants": 0, "killed_mutants": 0,
            "surviving_mutants": 0, "kill_rate": 0.0,
            "weak_theorems": [], "per_theorem": [],
            "theorem_coverage": 0.0, "slice_success_rate": 0.0,
            "model_space_estimate": 0,
            "specmut_error": sub.get("specmut_error"),
            "raw_stderr_excerpt": sub.get("raw_stderr"),
            "analysis_mode": "failed",
            **tags,
        }
        record["analysis_status"] = _finalize_status(record | sub)

    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(record, indent=2))
    return record["analysis_status"]


def _collect_work(args, *, n: int, eps: float, timeout: int, weak: float,
                  tasks, models) -> list[tuple]:
    work = []
    if args.condition in ("all", "references"):
        for task in tasks:
            spec = reference_path(task)
            lr = lean_result_path("references", None, task)
            out = specmut_result_path("references", None, task)
            tags = {"condition": "references", "task": task}
            work.append((spec, lr, out, tags, n, eps, timeout, args.force, weak))
    if args.condition in ("all", "controls"):
        for task in tasks:
            for kind, path_fn in (("trivial", trivial_path),
                                  ("partial", partial_path)):
                spec = path_fn(task)
                lr = lean_result_path("controls", None, task, control_type=kind)
                out = specmut_result_path("controls", None, task, control_type=kind)
                tags = {"condition": "controls", "task": task, "control_type": kind}
                work.append((spec, lr, out, tags, n, eps, timeout, args.force, weak))
    if args.condition in ("all", "baseline", "repaired"):
        from _common import replicate_indices as _ri
        for cond in (["baseline", "repaired"] if args.condition == "all"
                     else [args.condition]):
            path_fn = baseline_path if cond == "baseline" else repaired_path
            for model in models:
                for task in tasks:
                    for r in list(_ri()):
                        spec = path_fn(model, task, r)
                        if not spec.exists():
                            continue
                        lr = lean_result_path(cond, model, task, replicate=r)
                        out = specmut_result_path(cond, model, task, replicate=r)
                        tags = {"condition": cond, "task": task,
                                "model": model, "replicate": r}
                        work.append((spec, lr, out, tags, n, eps, timeout,
                                     args.force, weak))
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
                    help="number of concurrent specmut processes (default 1). "
                         "Each specmut process may peak at 1-4 GiB RAM — cap "
                         "to (available_RAM_GiB / 4) on memory-tight hosts.")
    args = ap.parse_args()
    ensure_lean_on_path()
    config = load_config()
    timeout = config["analysis"]["specmut_timeout_sec"]
    n = config["analysis"]["n"]
    eps = config["analysis"]["epsilon"]
    weak = config["thresholds"]["weak_theorem_tau"]
    tasks = [args.task] if args.task else list_tasks()
    slots = model_slots()
    if args.model:
        slots = [s for s in slots if s[1]["name"] == args.model or s[0] == args.model]
    models = [s[1]["name"] for s in slots]

    summary: dict[str, int] = {}

    def bump(s: str) -> None:
        summary[s] = summary.get(s, 0) + 1

    work = _collect_work(args, n=n, eps=eps, timeout=timeout, weak=weak,
                         tasks=tasks, models=models)
    total = len(work)
    print(f"  {total} files to analyze  "
          f"({'sequential' if args.parallel <= 1 else f'parallel={args.parallel}'})")

    if args.parallel <= 1:
        for w in work:
            spec, status = _analyze_worker(w)
            bump(status)
            print(f"  [{status:22}] {spec.relative_to(PHASE4.parent)}")
    else:
        done = 0
        with ProcessPoolExecutor(max_workers=args.parallel) as ex:
            futures = {ex.submit(_analyze_worker, w): w[0] for w in work}
            for fut in as_completed(futures):
                spec = futures[fut]
                try:
                    _, status = fut.result()
                except Exception as e:
                    status = f"worker_error({type(e).__name__})"
                bump(status)
                done += 1
                print(f"  [{status:22}] ({done}/{total}) {spec.relative_to(PHASE4.parent)}")

    print(f"\nrun_specmut: {summary}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
