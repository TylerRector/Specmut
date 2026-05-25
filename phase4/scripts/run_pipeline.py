#!/usr/bin/env python3
"""Phase 4 top-level driver.

Runs all 10 stages in order with caching + resume support.  Stages 1, 6 hit
the Ollama HTTP API; everything else is local.

Stage order (matching the spec):

  1. generate_baseline
  2. lean_check (baseline + references + controls)
  3. run_specmut (baseline + references + controls)
  4. validate_determinism  (halts pipeline on failure)
  5. generate_feedback
  6. generate_repaired
  7. lean_check (repaired)
  8. run_specmut (repaired)
  9. aggregate
 10. report

Use ``--from-stage NAME`` to resume.  Use ``--force`` to ignore caches.
"""

from __future__ import annotations

import argparse
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent

STAGES: list[tuple[str, list[str]]] = [
    ("generate_baseline",       [sys.executable, str(HERE / "generate_baseline.py")]),
    ("lean_check_baseline",     [sys.executable, str(HERE / "lean_check.py"),
                                  "--condition", "all"]),  # covers baseline+ref+controls
    ("run_specmut_baseline",    [sys.executable, str(HERE / "run_specmut.py"),
                                  "--condition", "all"]),
    ("validate_determinism",    [sys.executable, str(HERE / "validate_determinism.py")]),
    ("generate_feedback",       [sys.executable, str(HERE / "generate_feedback.py")]),
    ("generate_repaired",       [sys.executable, str(HERE / "generate_repaired.py")]),
    ("lean_check_repaired",     [sys.executable, str(HERE / "lean_check.py"),
                                  "--condition", "repaired"]),
    ("run_specmut_repaired",    [sys.executable, str(HERE / "run_specmut.py"),
                                  "--condition", "repaired"]),
    ("aggregate",               [sys.executable, str(HERE / "aggregate.py")]),
    ("report",                  [sys.executable, str(HERE / "report.py")]),
]

STAGE_NAMES = [n for n, _ in STAGES]


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--from-stage", choices=STAGE_NAMES,
                    help="resume from this stage")
    ap.add_argument("--only", choices=STAGE_NAMES,
                    help="run only this stage")
    ap.add_argument("--force", action="store_true",
                    help="pass --force to stages that support it")
    ap.add_argument("--parallel-llm", type=int, default=1,
                    help="concurrent Ollama requests for generation stages")
    ap.add_argument("--parallel-lean", type=int, default=1,
                    help="concurrent lean typecheck processes")
    ap.add_argument("--parallel-specmut", type=int, default=1,
                    help="concurrent specmut analyses (cap to RAM/4GiB)")
    ap.add_argument("--halt-on-determinism-failure", action="store_true",
                    default=True,
                    help="abort if validate_determinism exits non-zero")
    ap.add_argument("--continue-on-error", action="store_true",
                    help="don't abort on stage failure (debug only)")
    args = ap.parse_args()

    forceable = {
        "generate_baseline", "lean_check_baseline", "run_specmut_baseline",
        "validate_determinism", "generate_feedback", "generate_repaired",
        "lean_check_repaired", "run_specmut_repaired",
    }
    parallel_by_stage = {
        "generate_baseline":   args.parallel_llm,
        "generate_repaired":   args.parallel_llm,
        "lean_check_baseline": args.parallel_lean,
        "lean_check_repaired": args.parallel_lean,
        "run_specmut_baseline": args.parallel_specmut,
        "run_specmut_repaired": args.parallel_specmut,
    }

    started = bool(args.only)
    for name, cmd in STAGES:
        if args.only and name != args.only:
            continue
        if args.from_stage and not started:
            if name != args.from_stage:
                print(f"-- skipping {name} (resume target: {args.from_stage})")
                continue
            started = True
        full = list(cmd)
        if args.force and name in forceable:
            full.append("--force")
        if name in parallel_by_stage and parallel_by_stage[name] > 1:
            full += ["--parallel", str(parallel_by_stage[name])]
        print(f"\n=== {name} ===")
        rc = subprocess.run(full).returncode
        if rc != 0:
            if name == "validate_determinism" and args.halt_on_determinism_failure:
                print(f"!! {name} exit {rc} — HALTING (determinism check failed)")
                return rc
            if args.continue_on_error:
                print(f"!! {name} exit {rc} (continuing — --continue-on-error)")
            else:
                print(f"!! {name} exit {rc} — aborting")
                return rc
    print("\nPhase 4 pipeline complete.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
