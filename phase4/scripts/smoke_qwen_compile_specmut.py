#!/usr/bin/env python3
"""Phase 4 (qwen-only variant) smoke test against the live LLM.

Two modes — pick one with the threshold flags:

  --plumbing-thresholds  (default; pairs naturally with --reps 1)
      Cheap "does it run at all" gate.  Generates N reps × 4 tasks,
      requires every generation to complete and at least
      ``--min-specmut-success`` tasks to reach analysis_status=success.

  --decision-thresholds  (pairs with --reps 5)
      Per-task minimum compile + analyzable counts.  This is the gate
      that should pass before a full multi-replicate run.  Per-task
      requirements are baked in:
        list_min     : ≥ 4/5 lean_ok, ≥ 3/5 analyzable
        list_reverse : ≥ 4/5 lean_ok, ≥ 3/5 analyzable
        set_insert   : ≥ 4/5 lean_ok, ≥ 2/5 nonzero-tau analyzable
        sorting      : ≥ 3/5 lean_ok, ≥ 2/5 analyzable

Order matters: run ``preflight_qwen_templates.py`` FIRST (no LLM, ideal
inputs).  If preflight fails, the prompts/scaffolds are wrong.  If
preflight passes but plumbing-smoke fails, the LLM transport / model
server config is wrong.  If plumbing-smoke passes but decision-smoke
fails, the prompts let the model produce too much variation — tighten
further before a full run.

Usage (with a model server reachable at $OLLAMA_URL):

    export OLLAMA_URL=http://host:port
    export PHASE4_CONFIG=phase4/config_qwen_specmut_feedback_pilot5.toml
    python3 phase4/scripts/preflight_qwen_templates.py
    python3 phase4/scripts/smoke_qwen_compile_specmut.py --reps 1 --plumbing-thresholds
    python3 phase4/scripts/smoke_qwen_compile_specmut.py --reps 5 --decision-thresholds
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from _common import (
    PHASE4,
    baseline_meta_path,
    baseline_path,
    ensure_lean_on_path,
    lean_result_path,
    list_tasks,
    load_config,
    specmut_result_path,
)
from generate_baseline import generate_one
from lean_check import check_one
from run_specmut import analyze_one


EXPECTED_TASKS = ("list_min", "list_reverse", "set_insert", "sorting")

# decision-mode minimums.  rep_count is configurable via --reps but the
# minimums below assume reps=5; with --reps M the requirement is rescaled
# proportionally (rounded up) so the user can run --reps 10 etc.
DECISION_MIN_PER_5: dict[str, tuple[int, int, str]] = {
    # task          : (lean_min_per_5, analyzable_min_per_5, analyzability_kind)
    "list_min":      (4, 3, "specmut_success"),
    "list_reverse":  (4, 3, "specmut_success"),
    "set_insert":    (4, 2, "nonzero_tau"),
    "sorting":       (3, 2, "specmut_success"),
}


def _scale(m: int, reps: int, base: int = 5) -> int:
    """Rescale a per-5 minimum to actual reps, rounding up."""
    if reps <= 0: return 0
    return max(1, (m * reps + base - 1) // base) if m > 0 else 0


def _row(*cols: str, widths=(14, 8, 8, 8, 14, 6)) -> str:
    parts = []
    for c, w in zip(cols, widths):
        parts.append(f"{c:{w}}")
    return "  " + " | ".join(parts)


def _record(task: str, model: str, replicate: int, *, config: dict,
            force: bool) -> dict:
    """Run gen → sanitize-meta → lean → specmut for one (task, replicate)."""
    n = config["analysis"]["n"]
    eps = config["analysis"]["epsilon"]
    lean_timeout = config["analysis"]["lean_timeout_sec"]
    specmut_timeout = config["analysis"]["specmut_timeout_sec"]
    weak = config.get("thresholds", {}).get("weak_theorem_tau", 0.3)

    gen_status = generate_one(model, task, replicate, config=config, force=force)
    try:
        meta = json.loads(baseline_meta_path(model, task, replicate).read_text())
    except Exception:
        meta = {}
    san_status = meta.get("sanitizer_status") or "n/a"

    lean_status = check_one(
        baseline_path(model, task, replicate),
        lean_result_path("baseline", model, task, replicate=replicate),
        force=force, timeout=lean_timeout,
        tags={"condition": "baseline", "task": task,
              "model": model, "replicate": replicate},
    )

    spec_status = analyze_one(
        baseline_path(model, task, replicate),
        lean_result_path("baseline", model, task, replicate=replicate),
        specmut_result_path("baseline", model, task, replicate=replicate),
        tags={"condition": "baseline", "task": task,
              "model": model, "replicate": replicate},
        model_bound=n, epsilon=eps, timeout=specmut_timeout,
        force=force, weak_threshold=weak,
    )

    tau = None
    sp_path = specmut_result_path("baseline", model, task, replicate=replicate)
    if sp_path.exists():
        try:
            rec = json.loads(sp_path.read_text())
            if rec.get("analysis_status") == "success":
                tau = rec.get("average_tau", 0.0)
        except Exception:
            pass

    return {
        "task": task, "replicate": replicate,
        "gen": gen_status, "sanitizer": san_status,
        "lean": lean_status, "specmut": spec_status, "tau": tau,
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--reps", type=int, default=1,
                    help="replicates per task (default 1)")
    ap.add_argument("--force", action="store_true",
                    help="ignore cached generations / lean / specmut results")
    grp = ap.add_mutually_exclusive_group()
    grp.add_argument("--plumbing-thresholds", action="store_true",
                     help="cheap 'does it run' gate (default mode)")
    grp.add_argument("--decision-thresholds", action="store_true",
                     help="per-task production-gate thresholds")
    ap.add_argument("--min-specmut-success", type=int, default=2,
                    help="(plumbing) minimum specmut successes across "
                         "the run (default 2)")
    args = ap.parse_args()

    mode = "decision" if args.decision_thresholds else "plumbing"
    ensure_lean_on_path()
    config = load_config()
    model_block = config["models"].get("m1")
    if not model_block:
        sys.exit("config has no [models.m1]; the qwen-only config must define m1")
    model = model_block["name"]
    if "qwen" not in model.lower():
        print(f"  WARNING: smoke test was designed for qwen models, got {model!r}",
              file=sys.stderr)

    tasks = list_tasks()
    missing = set(EXPECTED_TASKS) - set(tasks)
    extra = set(tasks) - set(EXPECTED_TASKS)
    if missing:
        sys.exit(f"benchmarks missing: {sorted(missing)}")
    if extra:
        print(f"  NOTE: extra benchmark dirs present (will be smoked): {sorted(extra)}")

    print(f"\nPhase 4 qwen-only smoke ({mode} mode, reps={args.reps}, model: {model})")
    print(f"  config: {config.get('experiment', {}).get('name', '?')}")
    print(_row("task", "rep", "gen", "san", "lean", "spec", "tau",
               widths=(14, 4, 10, 16, 18, 22, 6)))
    print("  " + "-" * 110)

    # rows by task
    rows: dict[str, list[dict]] = {t: [] for t in tasks}

    for task in sorted(tasks):
        for r in range(1, args.reps + 1):
            rec = _record(task, model, r, config=config, force=args.force)
            rows[task].append(rec)
            tau_s = f"{rec['tau']:.3f}" if rec["tau"] is not None else "—"
            gen_short = rec["gen"][:10]
            print(_row(task, str(r), gen_short, rec["sanitizer"],
                       rec["lean"], rec["specmut"], tau_s,
                       widths=(14, 4, 10, 16, 18, 22, 6)))

    # ---- evaluate ----
    print()
    overall_ok = True

    if mode == "plumbing":
        total_specmut_ok = sum(1 for t in rows for x in rows[t]
                               if x["specmut"] == "success")
        total_compiled = sum(1 for t in rows for x in rows[t]
                             if x["lean"] == "compile_success")
        total_gens = sum(len(rows[t]) for t in rows)
        print(f"  total compiled  : {total_compiled}/{total_gens}")
        print(f"  total specmut OK: {total_specmut_ok}/{total_gens}  "
              f"(min required: {args.min_specmut_success})")
        if total_compiled == 0:
            overall_ok = False
            print("  !! plumbing FAILED: nothing compiled — check Ollama / sanitizer")
        if total_specmut_ok < args.min_specmut_success:
            overall_ok = False
            print(f"  !! plumbing FAILED: only {total_specmut_ok} specmut successes")
    else:
        # decision mode — per-task minimums
        print(f"  per-task decision thresholds (scaled from per-5 to per-{args.reps}):")
        for task in EXPECTED_TASKS:
            if task not in rows or not rows[task]:
                print(f"    {task:14}: NO DATA — overall FAIL"); overall_ok = False; continue
            lean_min_5, ana_min_5, kind = DECISION_MIN_PER_5[task]
            lean_min = _scale(lean_min_5, args.reps)
            ana_min = _scale(ana_min_5, args.reps)
            lean_ok = sum(1 for x in rows[task] if x["lean"] == "compile_success")
            if kind == "nonzero_tau":
                ana_ok = sum(1 for x in rows[task]
                             if x["specmut"] == "success"
                             and x["tau"] is not None and x["tau"] > 0.0)
            else:
                ana_ok = sum(1 for x in rows[task] if x["specmut"] == "success")
            status = "ok" if (lean_ok >= lean_min and ana_ok >= ana_min) else "FAIL"
            if status != "ok":
                overall_ok = False
            print(f"    {task:14}: lean={lean_ok}/{args.reps} (min {lean_min}), "
                  f"{kind}={ana_ok}/{args.reps} (min {ana_min})  [{status}]")

    if overall_ok:
        if mode == "plumbing":
            print("  -- plumbing smoke OK -- now run decision smoke before sbatch:")
            print("     python3 phase4/scripts/smoke_qwen_compile_specmut.py --reps 5 --decision-thresholds --force")
        else:
            print("  -- decision smoke OK -- safe to clean caches + sbatch")
        return 0
    print("  !! smoke FAILED — do NOT submit sbatch")
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
