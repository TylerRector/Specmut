#!/usr/bin/env python3
"""Phase H Stage 1: LLM specification generation.

Default backend is ``stub`` — pre-staged ``.lean`` files in ``generated/`` are
treated as canonical LLM output.  This lets the pipeline run end-to-end on a
laptop without API keys, while preserving the per-(model, task, round) layout
expected by every downstream stage.

The script is idempotent: if the target ``.lean`` already exists, it is left
untouched.  Pass ``--force`` to regenerate.

Other backends (``ollama``, ``anthropic``) are stubbed so the surface is in
place; they raise NotImplementedError until wired up to real APIs.  The Phase H
specification policy explicitly permits manual refinement rounds — keeping the
default backend at ``stub`` is the supported workflow.
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from _common import (
    DEFAULTS,
    GENERATED,
    PROMPTS,
    generated_path,
    list_models,
    list_tasks,
    list_versions,
)


def stub_backend(model: str, task: str, version: int, target: Path) -> bool:
    """Treat pre-staged files as canonical LLM output.

    Returns True if the file is present (i.e. "generation succeeded"), False
    otherwise.  Never writes to the filesystem — the file is the source of
    truth, not generated here.
    """
    return target.exists()


def ollama_backend(model: str, task: str, version: int, target: Path) -> bool:  # noqa: ARG001
    raise NotImplementedError(
        "ollama backend not implemented; stage pre-generated files in generated/ "
        "or invoke ollama manually and drop the .lean files in place."
    )


def anthropic_backend(model: str, task: str, version: int, target: Path) -> bool:  # noqa: ARG001
    raise NotImplementedError(
        "anthropic backend not implemented; stage pre-generated files in generated/."
    )


BACKENDS = {
    "stub": stub_backend,
    "ollama": ollama_backend,
    "anthropic": anthropic_backend,
}


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--backend", choices=list(BACKENDS), default="stub")
    ap.add_argument("--task", help="restrict to one task")
    ap.add_argument("--model", help="restrict to one model")
    ap.add_argument("--rounds", type=int, nargs="+", default=DEFAULTS["rounds"])
    ap.add_argument("--force", action="store_true")
    args = ap.parse_args()

    backend = BACKENDS[args.backend]
    tasks = [args.task] if args.task else list_tasks()
    models = [args.model] if args.model else (list_models() or DEFAULTS["models"])

    if not tasks:
        sys.exit("no tasks found under benchmarks/")
    if not models:
        sys.exit("no models found under generated/; pass --model NAME or stage files")

    ok = miss = 0
    for model in models:
        for task in tasks:
            prompt = PROMPTS / f"{task}.md"
            if not prompt.exists():
                print(f"warn: no prompt template at {prompt} (continuing)")
            for v in args.rounds:
                target = generated_path(model, task, v)
                target.parent.mkdir(parents=True, exist_ok=True)
                if target.exists() and not args.force:
                    ok += 1
                    print(f"  cached {target.relative_to(GENERATED.parent)}")
                    continue
                produced = backend(model, task, v, target)
                if produced:
                    ok += 1
                    print(f"  wrote  {target.relative_to(GENERATED.parent)}")
                else:
                    miss += 1
                    print(f"  MISS   {target.relative_to(GENERATED.parent)} (stage manually)")

    # Also report what was already staged that we didn't explicitly enumerate,
    # so the operator sees the full picture.
    print(f"\nGenerate stage: {ok} present, {miss} missing")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
