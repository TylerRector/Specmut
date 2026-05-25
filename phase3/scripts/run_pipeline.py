#!/usr/bin/env python3
"""Phase H top-level driver — runs all five stages in order.

Each stage caches its outputs, so re-running this script is cheap.  Use
``--force`` to ignore caches and regenerate everything.
"""

from __future__ import annotations

import argparse
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
STAGES = [
    ("generate", "generate.py"),
    ("reduce", "reduce.py"),         # NEW: programmatic analyzable projection
    ("lean_check", "lean_check.py"),
    ("run_specmut", "run_specmut.py"),
    ("aggregate", "aggregate.py"),
    ("report", "report.py"),
]


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--force", action="store_true", help="ignore caches")
    ap.add_argument("--from-stage", choices=[s for s, _ in STAGES],
                    help="resume from this stage")
    ap.add_argument("-n", "--model-bound", type=int,
                    help="forwarded to run_specmut.py")
    ap.add_argument("-e", "--epsilon", type=float,
                    help="forwarded to run_specmut.py")
    args = ap.parse_args()

    started = False
    for name, script in STAGES:
        if args.from_stage and not started:
            if name != args.from_stage:
                print(f"-- skipping {name} (resume target: {args.from_stage})")
                continue
            started = True
        cmd = [sys.executable, str(HERE / script)]
        if args.force and name in ("generate", "reduce", "lean_check", "run_specmut"):
            cmd.append("--force")
        # Always validate reduce output — broken projections must fail loud.
        if name == "reduce":
            cmd.append("--validate")
        if name == "run_specmut":
            if args.model_bound is not None:
                cmd += ["-n", str(args.model_bound)]
            if args.epsilon is not None:
                cmd += ["-e", str(args.epsilon)]
        print(f"\n=== {name} ===")
        rc = subprocess.run(cmd).returncode
        if rc != 0:
            print(f"!! stage {name} failed (exit {rc}); aborting")
            return rc
    print("\nPhase H pipeline complete.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
