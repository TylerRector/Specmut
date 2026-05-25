#!/usr/bin/env python3
"""Phase 4 Stage 6: second-pass LLM generation with feedback in the prompt.

Each baseline becomes a 1:1 paired repair attempt.  Prompt structure:

  <original task prompt>

  Your previous attempt was:
  ```lean
  <original output>
  ```

  <feedback text from generate_feedback.py>

  Produce a revised specification.

Decoding uses the same temperature/top_p as the baseline but a different
seed (``repair_seed`` from _common).  Same Ollama backend.

Skip-if-cached.  Every baseline produces exactly one repair, including those
that failed compilation — the feedback for failures describes the failure
mode in plain language.
"""

from __future__ import annotations

import argparse
import datetime
import json
import sys
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path
from urllib import error, request

sys.path.insert(0, str(Path(__file__).resolve().parent))
from _common import (
    GENERATED,
    PHASE4,
    baseline_meta_path,
    baseline_path,
    feedback_path,
    list_tasks,
    load_config,
    model_slots,
    ollama_url,
    prompt_path,
    prompt_sha256,
    repair_seed,
    repaired_meta_path,
    repaired_path,
    replicate_indices,
    specmut_result_path,
)
from generate_baseline import (  # reuse
    _compose_lean_file,
    _ollama_generate,
    _read_scaffold,
    _strip_code_fence,
    _write_failure_stub,
    _write_rejected_stub,
)
from sanitize_generated import STATUS_OK
from repair_templates import (
    build_repair_prompt,
    build_specmut_summary,
    strip_scaffold,
)
from validate_repair_template import validate_repair, STATUS_OK as REPAIR_TEMPLATE_OK


def _repair_mode(config: dict) -> str:
    """Active repair mode.

    "specmut_informed_constrained" enables the Experiment-B variant that
    feeds the baseline specmut result + a task-specific required theorem
    template into the prompt and semantically validates the output.  Any
    other value (or a missing [repair] section) keeps the legacy
    feedback-text repair path so the frozen / qwen-only configs are
    unaffected.
    """
    return str(config.get("repair", {}).get("mode", "feedback_text"))


def _load_baseline_specmut(model: str, task: str, replicate: int) -> dict | None:
    p = specmut_result_path("baseline", model, task, replicate=replicate)
    if not p.exists():
        return None
    try:
        return json.loads(p.read_text())
    except Exception:
        return None


def _compose_specmut_informed_prompt(task: str, baseline_lean: str,
                                     feedback_text: str,
                                     specmut_record: dict | None) -> str:
    base_prompt = prompt_path(task).read_text()
    baseline_theorems = strip_scaffold(baseline_lean)
    summary = build_specmut_summary(specmut_record, task)
    return build_repair_prompt(
        task=task, base_prompt=base_prompt,
        baseline_theorems=baseline_theorems,
        specmut_summary=summary, feedback_text=feedback_text)


def _compose_repair_prompt(task: str, baseline_lean: str, feedback_text: str,
                           *, template_constrained: bool = False) -> str:
    base_prompt = prompt_path(task).read_text().rstrip()
    # Strip the scaffold portion of the previous attempt from the prompt
    # context — it's noise the LLM doesn't need to re-emit, and including
    # it inside ```lean fences would confuse the theorem-only constraint.
    prev = baseline_lean.strip()
    marker = "-- ↓↓↓ qwen-only LLM-generated theorems ↓↓↓"
    if template_constrained and marker in prev:
        prev = prev.split(marker, 1)[1].strip()

    trailing = (
        "Now produce a revised THEOREM BLOCK that addresses the weaknesses "
        "above.  Output ONLY raw Lean theorem declarations — no scaffold, "
        "no definitions, no markdown fences.  The scaffold will be "
        "prepended automatically."
        if template_constrained
        else
        "Now produce a revised, self-contained Lean 4 specification "
        "that addresses the weaknesses above. Output ONLY the Lean code."
    )

    return (
        f"{base_prompt}\n\n"
        f"Your previous attempt was:\n"
        f"```lean\n{prev}\n```\n\n"
        f"{feedback_text.strip()}\n\n"
        f"{trailing}"
    )


def repair_one(model: str, task: str, replicate: int, *,
               config: dict, force: bool) -> str:
    rep_lean = repaired_path(model, task, replicate)
    rep_meta = repaired_meta_path(model, task, replicate)
    if rep_lean.exists() and rep_meta.exists() and not force:
        return "cached"

    base_lean = baseline_path(model, task, replicate)
    fb_path = feedback_path(model, task, replicate)
    if not base_lean.exists():
        return "missing_baseline"
    if not fb_path.exists():
        return "missing_feedback"

    baseline_text = base_lean.read_text()
    fb = json.loads(fb_path.read_text())
    template_constrained = bool(config.get("scaffold", {}).get("enabled"))
    mode = _repair_mode(config)
    specmut_informed = (mode == "specmut_informed_constrained")
    baseline_specmut = _load_baseline_specmut(model, task, replicate) \
        if specmut_informed else None
    if specmut_informed:
        prompt = _compose_specmut_informed_prompt(
            task, baseline_text, fb["feedback_text"], baseline_specmut)
    else:
        prompt = _compose_repair_prompt(task, baseline_text, fb["feedback_text"],
                                        template_constrained=template_constrained)
    seed = repair_seed(config["experiment"]["base_seed"], replicate)
    gen_cfg = config["generation"]
    start = time.monotonic()
    status = "ok"; error_msg: str | None = None; raw_response = ""

    try:
        raw_response, _ = _ollama_generate(
            url=ollama_url(config),
            model=model, prompt=prompt,
            temperature=gen_cfg["temperature"],
            top_p=gen_cfg["top_p"],
            max_tokens=gen_cfg["max_tokens"],
            seed=seed,
            timeout_sec=gen_cfg["generation_timeout_sec"],
        )
    except error.URLError as e:
        status, error_msg = "transport_failed", str(e.reason)
    except TimeoutError:
        status, error_msg = "timeout", f"{gen_cfg['generation_timeout_sec']}s"
    except Exception as e:
        status, error_msg = "exception", f"{type(e).__name__}: {e}"
    elapsed = round(time.monotonic() - start, 2)

    rep_lean.parent.mkdir(parents=True, exist_ok=True)
    sanitizer_status: str | None = None
    sanitizer_violations: list[str] = []
    sanitizer_theorem_count = 0
    sanitizer_line_count = 0
    scaffold = _read_scaffold(task, config)

    # Semantic repair-template validation (specmut-informed mode only).
    #
    # When [repair].block_on_semantic_rejection is true (the compliance-gated
    # revised pilot), ONLY repair_template_ok passes: any other status causes
    # the repaired output to be replaced with a rejected stub (→ Lean
    # compile_failure → not counted as a successful repaired theorem), exactly
    # like syntax rejection.  The raw Qwen output is preserved in a sidecar.
    #
    # IMPORTANT (scientific validity): we REJECT invalid repairs; we never
    # substitute the required template programmatically.  The repaired theorem
    # is always the model's own output or a rejection stub — never an
    # auto-inserted answer.  This keeps the LLM-repair claim intact.
    repair_template_status: str | None = None
    repair_template_reasons: list[str] = []
    repair_no_change: bool | None = None
    repair_required_present: bool | None = None
    repair_target_fn_present: bool | None = None
    repair_template_theorem_count: int | None = None
    repair_semantic_blocked: bool = False
    repair_block_reason: str | None = None
    raw_output_path: str | None = None
    cleaned_block: str | None = None

    block = bool(config.get("repair", {}).get("block_on_semantic_rejection", False))

    def _reject(stub_status: str, reasons: list[str]) -> None:
        """Write the raw output sidecar + a rejected stub (compile_failure)."""
        nonlocal repair_semantic_blocked, repair_block_reason, raw_output_path
        side = rep_lean.with_suffix(".rejected_raw.txt")
        side.write_text(raw_response)
        raw_output_path = str(side.relative_to(PHASE4.parent))
        _write_rejected_stub(rep_lean, model=model, task=task,
                             replicate=replicate,
                             sanitizer_status=stub_status,
                             violations=reasons)
        repair_semantic_blocked = True
        repair_block_reason = (f"{stub_status}: {reasons[0]}"
                               if reasons else stub_status)

    if status == "ok":
        body, sr = _compose_lean_file(raw_response, scaffold=scaffold,
                                      config=config)
        sanitizer_status = sr.status
        sanitizer_violations = sr.violations
        sanitizer_theorem_count = sr.theorem_count
        sanitizer_line_count = sr.line_count
        cleaned_block = sr.cleaned

        if sr.status != STATUS_OK:
            # Syntax rejection (sanitizer) — always a stub, independent of the
            # semantic-blocking flag.
            _reject(sr.status, sr.violations)
            if specmut_informed:
                repair_template_status = "repair_syntax_rejected"
                repair_template_reasons = [f"syntax sanitizer: {sr.status}"]
                repair_block_reason = f"repair_syntax_rejected: {sr.status}"
        elif specmut_informed:
            vr = validate_repair(sr.cleaned, baseline_text, task, config=config)
            repair_template_status = vr.status
            repair_template_reasons = vr.reasons
            repair_no_change = vr.no_change
            repair_required_present = vr.required_present
            repair_target_fn_present = vr.target_fn_present
            repair_template_theorem_count = vr.theorem_count
            if vr.status == REPAIR_TEMPLATE_OK:
                rep_lean.write_text(body)            # the only path that passes
            elif block:
                _reject(vr.status, vr.reasons)       # blocked → stub
            else:
                rep_lean.write_text(body)            # non-blocking: score it
        else:
            # Legacy / non-specmut-informed mode: unchanged behavior.
            rep_lean.write_text(body)
    else:
        _write_failure_stub(rep_lean, model=model, task=task,
                            replicate=replicate,
                            reason=f"{status}: {error_msg}")
        if specmut_informed:
            repair_template_status = "repair_generation_failed"
            repair_template_reasons = [f"generation: {status}"]
            repair_semantic_blocked = block
            repair_block_reason = f"repair_generation_failed: {status}"

    meta = {
        "model": model, "task": task, "replicate": replicate,
        "stage": "repaired",
        "repair_mode": mode,
        "temperature": gen_cfg["temperature"],
        "top_p": gen_cfg["top_p"],
        "max_tokens": gen_cfg["max_tokens"],
        "seed": seed,
        "timestamp_utc": datetime.datetime.utcnow().isoformat() + "Z",
        "prompt_sha256": prompt_sha256(prompt),
        "baseline_prompt_sha256": prompt_sha256(prompt_path(task).read_text()),
        "feedback_source": str(fb_path.relative_to(PHASE4.parent)),
        "generation_status": status,
        "error": error_msg,
        "elapsed_sec": elapsed,
        "ollama_url": ollama_url(config),
        "scaffold_used": scaffold is not None,
        "sanitizer_status": sanitizer_status,
        "sanitizer_violations": sanitizer_violations,
        "sanitizer_theorem_count": sanitizer_theorem_count,
        "sanitizer_line_count": sanitizer_line_count,
        # specmut-informed constrained repair provenance.
        "specmut_informed": specmut_informed,
        "baseline_analysis_status": (baseline_specmut or {}).get("analysis_status")
            if specmut_informed else None,
        "baseline_tau": (baseline_specmut or {}).get("average_tau")
            if specmut_informed else None,
        "repair_template_status": repair_template_status,
        "repair_template_reasons": repair_template_reasons,
        "repair_no_change": repair_no_change,
        "repair_required_theorem_present": repair_required_present,
        # spec.md alias for the same fact (required membership core present).
        "repair_template_required_core_present": repair_required_present,
        "repair_target_fn_present": repair_target_fn_present,
        "repair_template_theorem_count": repair_template_theorem_count,
        # Compliance-gated blocking provenance.
        "repair_semantic_blocked": repair_semantic_blocked,
        "repair_block_reason": repair_block_reason,
        "raw_output_path": raw_output_path,
    }
    rep_meta.write_text(json.dumps(meta, indent=2))
    if status == "ok" and sanitizer_status and sanitizer_status != STATUS_OK:
        return f"sanitizer:{sanitizer_status}"
    if specmut_informed and repair_template_status \
            and repair_template_status != "repair_template_ok":
        return f"tmpl:{repair_template_status}"
    return status


def _repair_worker(args: tuple) -> tuple[str, str, int, str]:
    model, task, r, config, force = args
    status = repair_one(model, task, r, config=config, force=force)
    return model, task, r, status


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--task")
    ap.add_argument("--model")
    ap.add_argument("--replicate", type=int)
    ap.add_argument("--force", action="store_true")
    ap.add_argument("--parallel", type=int, default=1,
                    help="number of concurrent Ollama requests (default 1)")
    args = ap.parse_args()

    config = load_config()
    tasks = [args.task] if args.task else list_tasks()
    slots = model_slots()
    if args.model:
        slots = [s for s in slots if s[1]["name"] == args.model or s[0] == args.model]
    replicates = [args.replicate] if args.replicate else list(replicate_indices())

    work: list[tuple] = []
    for slot_name, model_block in slots:
        model = model_block["name"]
        for task in tasks:
            for r in replicates:
                work.append((model, task, r, config, args.force))
    total = len(work)
    print(f"  {total} repairs to perform  "
          f"({'sequential' if args.parallel <= 1 else f'parallel={args.parallel}'})")

    summary: dict[str, int] = {}
    if args.parallel <= 1:
        for w in work:
            model, task, r, s = _repair_worker(w)
            summary[s] = summary.get(s, 0) + 1
            tag = repaired_path(model, task, r).relative_to(GENERATED.parent)
            print(f"  [{s:14}] {tag}")
    else:
        done = 0
        with ThreadPoolExecutor(max_workers=args.parallel) as ex:
            futures = {ex.submit(_repair_worker, w): w for w in work}
            for fut in as_completed(futures):
                try:
                    model, task, r, s = fut.result()
                except Exception as e:
                    model, task, r, _, _ = futures[fut]
                    s = f"worker_error({type(e).__name__})"
                summary[s] = summary.get(s, 0) + 1
                tag = repaired_path(model, task, r).relative_to(GENERATED.parent)
                done += 1
                print(f"  [{s:14}] ({done}/{total}) {tag}")

    print(f"\nGenerate repaired: {summary}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
