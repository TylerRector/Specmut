#!/usr/bin/env python3
"""Phase 4 (qwen-only variant) template pre-flight.

Runs the WHOLE downstream pipeline (sanitize → compose → lean → specmut)
against HAND-WRITTEN ideal theorem files — no LLM involved.  This is the
strongest pre-flight gate: if it fails, the prompts/scaffolds are
broken at the level of "even a perfect output wouldn't analyze", and
running Qwen 200 times will not fix it.

Ideal templates live under:
    phase4/tmp_qwen_preflight/<task>_theorems.lean

They are concatenated against the live scaffold for each task and
written to:
    phase4/tmp_qwen_preflight/<task>_generated.lean

Output table per task:
    task | sanitizer | lean | specmut | tau | notes

Exit code:
    0  — all 4 tasks: sanitizer ok, lean compile_success, specmut
         analysis_status=success (tau > 0)
    1  — at least one stage failed somewhere

Run this BEFORE the smoke test against the live LLM.
"""

from __future__ import annotations

import argparse
import json
import os
import shutil
import subprocess
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from _common import (
    PHASE4,
    PROJECT_ROOT,
    ensure_lean_on_path,
    load_config,
    scaffold_path,
    specmut_bin,
)
from sanitize_generated import sanitize_text, STATUS_OK


PREFLIGHT_DIR = PHASE4 / "tmp_qwen_preflight"
EXPECTED_TASKS = ("list_min", "list_reverse", "set_insert", "sorting")

# Soft tau thresholds applied ONLY in --repair mode.  These do NOT fail the
# preflight by themselves (stage failures still do); they print a clear WARN
# so a weak repair template is caught before a real run.  list_min is the
# ceiling/control task and has no threshold.  (op, value): warn if
# `tau op value` is True.
REPAIR_TAU_WARN = {
    "list_reverse": ("<", 0.80),
    "set_insert":   ("<", 0.80),
    "sorting":      ("<=", 0.136),
}


def _tau_below(op: str, tau: float, value: float) -> bool:
    return (tau < value) if op == "<" else (tau <= value)


def _read_theorem_block(task: str, *, repair: bool = False) -> str:
    """Read the hand-written ideal theorem block for ``task``.

    With ``repair=True`` reads ``<task>_repair_theorems.lean`` (the REQUIRED
    stronger theorem the specmut-informed repair must produce) instead of the
    baseline ideal.  This is the gate that catches an OOM / model-bound blowup
    in a repair template (e.g. the set_insert membership equivalence) BEFORE a
    real run consumes the GPU budget.
    """
    suffix = "_repair_theorems.lean" if repair else "_theorems.lean"
    p = PREFLIGHT_DIR / f"{task}{suffix}"
    if not p.exists():
        sys.exit(f"missing ideal template: {p}\n"
                 f"  (this script is paired with the templates under "
                 f"phase4/tmp_qwen_preflight/; both must exist)")
    return p.read_text()


def _read_scaffold(task: str) -> str:
    sp = scaffold_path(task)
    if not sp.exists():
        sys.exit(f"missing scaffold: {sp}")
    return sp.read_text()


def _compose(scaffold: str, theorems: str) -> str:
    """Mirror generate_baseline._compose_lean_file's prepend layout."""
    return (scaffold.rstrip() + "\n\n"
            "-- ↓↓↓ qwen-only LLM-generated theorems ↓↓↓\n"
            + theorems.lstrip())


def _run_lean(file_path: Path, timeout: int) -> tuple[str, str]:
    """Return (status, last_err_or_warn_line)."""
    if shutil.which("lean") is None:
        return "lean_missing", "lean binary not on PATH"
    try:
        proc = subprocess.run(["lean", str(file_path)],
                              capture_output=True, text=True,
                              timeout=timeout)
    except subprocess.TimeoutExpired:
        return "compile_timeout", f"timeout after {timeout}s"
    combined = (proc.stdout or "") + (proc.stderr or "")
    errs = [ln for ln in combined.splitlines() if " error" in ln]
    if proc.returncode == 0 and not errs:
        return "compile_success", ""
    return "compile_failure", (errs[-1] if errs else combined[:160])


def _run_specmut(file_path: Path, *, n: int, eps: float,
                 timeout: int) -> tuple[str, float | None, str]:
    """Return (status, tau, notes)."""
    bin_ = specmut_bin()
    tmp = Path("/tmp") / f"preflight_{file_path.stem}_{time.monotonic_ns()}.json"
    try:
        proc = subprocess.run(
            [str(bin_), "analyze", str(file_path), "--lean-full",
             "-n", str(n), "-e", str(eps), "-f", "json", "-o", str(tmp)],
            capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        if tmp.exists(): tmp.unlink()
        return "timeout", None, f"timeout {timeout}s"
    rc = proc.returncode
    if not tmp.exists() or tmp.stat().st_size == 0:
        last = (proc.stderr or proc.stdout or "").strip().splitlines()
        if rc in (137, -9):
            return "oom_killed", None, f"SIGKILL (rc={rc}) — model space too large"
        return "specmut_error", None, (last[-1][:140] if last else f"rc={rc}, no JSON")

    raw = json.loads(tmp.read_text())
    tmp.unlink()
    if "theorem_slices" in raw:
        s = raw.get("summary", {})
        tau = s.get("mean_tightness", 0.0)
        n_analyzed = sum(1 for x in raw["theorem_slices"] if x["status"] == "analyzed")
        n_total = len(raw["theorem_slices"])
        return "success", tau, f"per_theorem  analyzed={n_analyzed}/{n_total}"
    t = raw.get("tightness", {})
    tau = t.get("score", 0.0)
    killed = t.get("killed", 0)
    alive = t.get("alive", 0)
    total = killed + alive
    if total == 0:
        return "insufficient_mutations", 0.0, "no mutations generated"
    if tau == 0.0 and alive > 0:
        return "tau_zero", 0.0, f"global  killed=0/{total}  (theorem too weak)"
    return "success", tau, f"global  killed={killed}/{total}"


def _row(task: str, san: str, lean: str, spec: str, tau, notes: str) -> str:
    tau_s = f"{tau:.3f}" if isinstance(tau, float) else "—"
    return f"  {task:14} | {san:16} | {lean:18} | {spec:22} | {tau_s:>6} | {notes}"


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--keep", action="store_true",
                    help="keep tmp_qwen_preflight/<task>_generated.lean after run")
    ap.add_argument("--skip-specmut", action="store_true",
                    help="skip specmut analysis (lean check only)")
    ap.add_argument("--repair", action="store_true",
                    help="validate the REQUIRED specmut-informed repair "
                         "templates (<task>_repair_theorems.lean) instead of "
                         "the baseline ideals — run this before the "
                         "specmut-feedback pilot to catch OOM/model-bound "
                         "blowups (esp. set_insert membership equivalence)")
    args = ap.parse_args()

    ensure_lean_on_path()
    config = load_config()
    n = config["analysis"]["n"]
    eps = config["analysis"]["epsilon"]
    lean_timeout = config["analysis"]["lean_timeout_sec"]
    specmut_timeout = config["analysis"]["specmut_timeout_sec"]

    if not PREFLIGHT_DIR.exists():
        sys.exit(f"preflight dir missing: {PREFLIGHT_DIR}")

    # Safety: tmp_qwen_preflight must NOT be under phase4/benchmarks
    # (or list_tasks would discover it as a fake task).
    benchmarks = PHASE4 / "benchmarks"
    if benchmarks in PREFLIGHT_DIR.parents:
        sys.exit(f"preflight dir {PREFLIGHT_DIR} is inside {benchmarks} — "
                 f"would contaminate task discovery; move it.")

    print(f"\nPhase 4 qwen-only template pre-flight")
    print(f"  config: {config.get('experiment', {}).get('name', '?')}")
    print(f"  n={n}  epsilon={eps}  lean_timeout={lean_timeout}s  "
          f"specmut_timeout={specmut_timeout}s")
    print(_row("task", "sanitizer", "lean", "specmut", "tau", "notes"))
    print("  " + "-" * 110)

    overall_ok = True
    summary: dict[str, str] = {}
    threshold_warnings: list[str] = []

    gen_suffix = "_repair_generated.lean" if args.repair else "_generated.lean"
    if args.repair:
        print("  MODE: validating REQUIRED repair templates "
              "(<task>_repair_theorems.lean)")

    for task in EXPECTED_TASKS:
        theorems = _read_theorem_block(task, repair=args.repair)
        scaffold = _read_scaffold(task)

        # Sanitizer (against the theorem block, with scaffold provided
        # for line-count purposes).
        sr = sanitize_text(theorems, scaffold=scaffold, config=config)
        san = sr.status

        # Compose final file
        final_path = PREFLIGHT_DIR / f"{task}{gen_suffix}"
        if sr.status == STATUS_OK:
            final_text = _compose(scaffold, sr.cleaned)
        else:
            # If the ideal template itself fails the sanitizer, that's a
            # template bug — write the rejected text so the user can see it.
            final_text = (f"-- preflight sanitizer rejected template ({sr.status})\n"
                          f"-- violations: {sr.violations}\n"
                          + theorems)
        final_path.write_text(final_text)

        if sr.status != STATUS_OK:
            print(_row(task, san, "—", "—", None,
                       f"template fails sanitizer: {sr.violations[:1]}"))
            overall_ok = False
            summary[task] = f"sanitizer:{san}"
            continue

        # Lean
        lean_status, lean_msg = _run_lean(final_path, lean_timeout)
        if lean_status != "compile_success":
            print(_row(task, san, lean_status, "—", None, lean_msg[:80]))
            overall_ok = False
            summary[task] = lean_status
            continue

        # Specmut
        if args.skip_specmut:
            print(_row(task, san, lean_status, "skipped", None, "--skip-specmut"))
            summary[task] = "lean_ok_skipped_specmut"
            continue
        spec_status, tau, notes = _run_specmut(final_path, n=n, eps=eps,
                                               timeout=specmut_timeout)
        if spec_status != "success":
            overall_ok = False
        print(_row(task, san, lean_status, spec_status, tau, notes))
        summary[task] = spec_status

        # Soft tau threshold check (repair mode only).
        if args.repair and spec_status == "success" and task in REPAIR_TAU_WARN:
            op, val = REPAIR_TAU_WARN[task]
            if isinstance(tau, (int, float)) and _tau_below(op, tau, val):
                threshold_warnings.append(
                    f"{task}: repair tau={tau:.3f} {op} {val} "
                    f"— template likely too weak; revisit before a real run")

        if not args.keep:
            # Keep the composed file around for inspection regardless;
            # the --keep flag is kept for compatibility but defaults to keep.
            pass

    print()
    print("  per-task outcomes:", summary)

    if args.repair and threshold_warnings:
        print()
        print("  ** repair tau WARNINGS (soft — not a hard failure) **")
        for w in threshold_warnings:
            print(f"     WARN  {w}")
        print("     thresholds: list_reverse>=0.80, set_insert>=0.80, "
              "sorting>0.136 (list_min ceiling, no threshold)")

    if overall_ok:
        if args.repair:
            print("  -- repair preflight: all templates compiled + analyzed "
                  "(status=success)")
            if threshold_warnings:
                print("     but at least one tau is below target (see WARN "
                      "above) — inspect before submitting the pilot.")
            else:
                print("     and all tau thresholds met — repair templates look "
                      "stronger than the prior pilot.")
        else:
            print("  -- preflight OK -- prompts + scaffolds are consistent")
            print("     Next: bash phase4/scripts/verify_qwen.sh && \\")
            print("           python3 phase4/scripts/smoke_qwen_compile_specmut.py --reps 1 --plumbing-thresholds")
        return 0
    else:
        print("  !! preflight FAILED — DO NOT run smoke or sbatch yet.")
        print("     A repair template did not reach sanitizer=ok / "
              "lean=compile_success / specmut=success.")
        print("     Composed files preserved at phase4/tmp_qwen_preflight/")
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
