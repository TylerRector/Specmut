#!/usr/bin/env python3
"""Phase 4 Stage 1: baseline LLM generation against the Ollama HTTP API.

For each (model, task, replicate) triple in config.toml, POST to
``{ollama_url}/api/generate`` with the task's prompt and a deterministic seed.
Generated text is written to ``generated/baseline/{model}/{task}/rep_NN.lean``
and decoding parameters + provenance to the sibling ``.meta.json``.

This stage is the experiment's source of truth for stochastic variation:
temperature > 0 makes every replicate different, but the seed scheme keeps
each replicate individually reproducible from (base_seed, replicate_index).

Skip-if-cached.  Failed generations (timeout, HTTP error, refused connection)
are recorded in the meta.json with ``status: "failed"`` and a stub ``.lean``
file containing only a comment — downstream stages classify it as
``compile_failure`` (no Lean code to typecheck) so attrition propagates
cleanly without special-casing.
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
    baseline_seed,
    list_tasks,
    load_config,
    model_slots,
    ollama_url,
    prompt_path,
    prompt_sha256,
    replicate_indices,
    scaffold_path,
)
from sanitize_generated import sanitize_text, STATUS_OK


def _ollama_generate(url: str, model: str, prompt: str, *,
                     temperature: float, top_p: float, max_tokens: int,
                     seed: int, timeout_sec: int) -> tuple[str, dict]:
    """Single non-streaming Ollama generate request.

    Returns (text, raw_meta).  Raises on HTTP/transport failure so the caller
    can record the error in the meta.json.
    """
    body = {
        "model": model,
        "prompt": prompt,
        "stream": False,
        "options": {
            "temperature": temperature,
            "top_p": top_p,
            "num_predict": max_tokens,
            "seed": seed,
        },
    }
    req = request.Request(
        f"{url.rstrip('/')}/api/generate",
        data=json.dumps(body).encode("utf-8"),
        headers={"Content-Type": "application/json"},
        method="POST",
    )
    with request.urlopen(req, timeout=timeout_sec) as resp:
        raw = json.loads(resp.read().decode("utf-8"))
    return raw.get("response", ""), raw


def _strip_code_fence(text: str) -> str:
    """LLMs often wrap code in ```lean ... ```.  Strip the fence if present
    so the file is direct Lean source.
    """
    lines = text.strip().splitlines()
    if lines and lines[0].lstrip().startswith("```"):
        lines = lines[1:]
        # Trim trailing fence if any.
        if lines and lines[-1].lstrip().startswith("```"):
            lines = lines[:-1]
    return "\n".join(lines).strip() + "\n"


def _write_failure_stub(lean_path: Path, *, model: str, task: str,
                       replicate: int, reason: str) -> None:
    """Emit a Lean stub for transport / generation failures.

    Must force ``lean`` to emit a real error so ``lean_check.py``
    classifies it as ``compile_failure``.  A comment-only file would
    return rc=0 and silently be counted as a successful compile.
    """
    lean_path.parent.mkdir(parents=True, exist_ok=True)
    safe_reason = "".join(c if c.isalnum() else "_" for c in reason)[:60]
    lean_path.write_text(
        f"-- Phase 4 baseline generation FAILED.\n"
        f"-- model: {model}\n"
        f"-- task: {task}\n"
        f"-- replicate: {replicate}\n"
        f"-- reason: {reason}\n"
        f"#check Phase4GenerationFailed_{safe_reason}\n"
    )


def _read_scaffold(task: str, config: dict) -> str | None:
    """Return the scaffold text for ``task`` if the active config enables
    it (the qwen-only template-constrained variant) and the scaffold
    file exists.  Otherwise return None (preserves the original frozen
    experiment's behavior of writing only raw LLM output).
    """
    sc = config.get("scaffold")
    if not sc or not sc.get("enabled", False):
        return None
    p = scaffold_path(task)
    if not p.exists():
        return None
    return p.read_text()


def _write_rejected_stub(lean_path: Path, *, model: str, task: str,
                         replicate: int, sanitizer_status: str,
                         violations: list[str]) -> None:
    """Write a Lean stub for sanitizer-rejected outputs.

    The file MUST cause ``lean`` to exit with a real error (not just
    rc=0 on a comment-only file), otherwise ``lean_check.py`` will
    classify it as ``compile_success`` and the rejection silently
    becomes a successful Lean run.  The trailing line
    ``#check Phase4SanitizerRejected`` references an undefined
    identifier and reliably produces a
    ``<file>:<line>:<col>: error: unknown identifier`` line that
    matches ``ERROR_LINE_RE`` in lean_check.py.

    The raw rejected text is preserved in a sibling ``.rejected_raw.txt``
    sidecar for inspection / paper write-up.
    """
    lean_path.parent.mkdir(parents=True, exist_ok=True)
    v = "\n".join(f"--   - {x}" for x in violations[:10]) or "--   (none)"
    lean_path.write_text(
        f"-- Phase 4 (qwen-only) generation REJECTED by sanitizer.\n"
        f"-- model: {model}\n"
        f"-- task: {task}\n"
        f"-- replicate: {replicate}\n"
        f"-- sanitizer_status: {sanitizer_status}\n"
        f"-- violations:\n{v}\n"
        f"-- (raw output preserved in {lean_path.stem}.rejected_raw.txt)\n"
        f"-- The following line is intentional: it forces Lean to emit\n"
        f"-- an error so lean_check classifies this as compile_failure\n"
        f"-- rather than silently accepting a comment-only file.\n"
        f"#check Phase4SanitizerRejected_{sanitizer_status}\n"
    )


def _compose_lean_file(raw_response: str, *, scaffold: str | None,
                       config: dict) -> tuple[str, object]:
    """Sanitize + (optionally) prepend scaffold, returning the final
    file text and the SanitizeResult.  Pure; no I/O.

    When scaffold is None, behaves as a thin wrapper that still runs
    the sanitizer (which is a no-op when [sanitizer] is absent from the
    config), so the original frozen experiment is unchanged.
    """
    result = sanitize_text(raw_response, scaffold=scaffold, config=config)
    if result.status != STATUS_OK:
        # Caller decides whether to write the rejected stub or the
        # cleaned text — we return the cleaned text so it can be saved
        # to the .rejected_raw.txt sidecar.
        return result.cleaned, result
    body = result.cleaned
    if scaffold is not None:
        # Prepend with a one-line separator so the seam is visible in
        # the generated file (useful for debugging).
        body = scaffold.rstrip() + "\n\n-- ↓↓↓ qwen-only LLM-generated theorems ↓↓↓\n" + body
    return body, result


def generate_one(model: str, task: str, replicate: int, *,
                 config: dict, force: bool) -> str:
    lean_path = baseline_path(model, task, replicate)
    meta_path = baseline_meta_path(model, task, replicate)
    if lean_path.exists() and meta_path.exists() and not force:
        return "cached"

    prompt = prompt_path(task).read_text()
    seed = baseline_seed(config["experiment"]["base_seed"], replicate)
    gen_cfg = config["generation"]
    start = time.monotonic()
    status = "ok"
    error_msg: str | None = None
    raw_response = ""

    try:
        raw_response, raw_meta = _ollama_generate(
            url=ollama_url(config),
            model=model,
            prompt=prompt,
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
    lean_path.parent.mkdir(parents=True, exist_ok=True)

    sanitizer_status: str | None = None
    sanitizer_violations: list[str] = []
    sanitizer_theorem_count = 0
    sanitizer_line_count = 0
    scaffold = _read_scaffold(task, config)

    if status == "ok":
        body, sr = _compose_lean_file(raw_response, scaffold=scaffold,
                                      config=config)
        sanitizer_status = sr.status
        sanitizer_violations = sr.violations
        sanitizer_theorem_count = sr.theorem_count
        sanitizer_line_count = sr.line_count
        if sr.status == STATUS_OK:
            lean_path.write_text(body)
        else:
            # Preserve the raw (post-cleaning) text for inspection, but
            # write a deterministic rejected stub as the .lean so the
            # downstream Lean check categorizes this as compile_failure
            # rather than risking accidental compilation of malformed
            # output without the scaffold.
            (lean_path.with_suffix(".rejected_raw.txt")).write_text(
                raw_response)
            _write_rejected_stub(lean_path, model=model, task=task,
                                 replicate=replicate,
                                 sanitizer_status=sr.status,
                                 violations=sr.violations)
    else:
        _write_failure_stub(lean_path, model=model, task=task,
                            replicate=replicate, reason=f"{status}: {error_msg}")

    meta = {
        "model": model,
        "task": task,
        "replicate": replicate,
        "stage": "baseline",
        "temperature": gen_cfg["temperature"],
        "top_p": gen_cfg["top_p"],
        "max_tokens": gen_cfg["max_tokens"],
        "seed": seed,
        "timestamp_utc": datetime.datetime.utcnow().isoformat() + "Z",
        "prompt_sha256": prompt_sha256(prompt),
        "generation_status": status,
        "error": error_msg,
        "elapsed_sec": elapsed,
        "ollama_url": ollama_url(config),
        "scaffold_used": scaffold is not None,
        "sanitizer_status": sanitizer_status,
        "sanitizer_violations": sanitizer_violations,
        "sanitizer_theorem_count": sanitizer_theorem_count,
        "sanitizer_line_count": sanitizer_line_count,
    }
    meta_path.write_text(json.dumps(meta, indent=2))
    # If sanitizer rejected, surface that as the externally-reported status
    # so the worker progress log distinguishes it from generation success.
    if status == "ok" and sanitizer_status and sanitizer_status != STATUS_OK:
        return f"sanitizer:{sanitizer_status}"
    return status


def _gen_worker(args: tuple) -> tuple[str, str, int, str]:
    """Thread-safe wrapper (only does HTTP + file IO).  Returns
    (model, task, replicate, status)."""
    model, task, r, config, force = args
    status = generate_one(model, task, r, config=config, force=force)
    return model, task, r, status


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--task")
    ap.add_argument("--model", help="match a model slot name (m1/m2/m3) or full Ollama tag")
    ap.add_argument("--replicate", type=int)
    ap.add_argument("--force", action="store_true")
    ap.add_argument("--parallel", type=int, default=1,
                    help="number of concurrent Ollama requests (default 1). "
                         "Useful when Ollama is CUDA-backed and can batch.")
    args = ap.parse_args()

    config = load_config()
    tasks = [args.task] if args.task else list_tasks()
    slots = model_slots()
    if args.model:
        slots = [s for s in slots
                 if s[0] == args.model or s[1]["name"] == args.model]
        if not slots:
            sys.exit(f"no model slot matches '{args.model}'")
    replicates = [args.replicate] if args.replicate else list(replicate_indices())

    work: list[tuple] = []
    for slot_name, model_block in slots:
        model = model_block["name"]
        for task in tasks:
            for r in replicates:
                work.append((model, task, r, config, args.force))
    total = len(work)
    print(f"  {total} generations to perform  "
          f"({'sequential' if args.parallel <= 1 else f'parallel={args.parallel}'})")

    summary: dict[str, int] = {}
    if args.parallel <= 1:
        for w in work:
            model, task, r, status = _gen_worker(w)
            summary[status] = summary.get(status, 0) + 1
            tag = baseline_path(model, task, r).relative_to(GENERATED.parent)
            print(f"  [{status:14}] {tag}")
    else:
        # Threads (not processes) — Ollama work is I/O bound on the client
        # side; the GPU work happens server-side.
        done = 0
        with ThreadPoolExecutor(max_workers=args.parallel) as ex:
            futures = {ex.submit(_gen_worker, w): w for w in work}
            for fut in as_completed(futures):
                try:
                    model, task, r, status = fut.result()
                except Exception as e:
                    model, task, r, _, _ = futures[fut]
                    status = f"worker_error({type(e).__name__})"
                summary[status] = summary.get(status, 0) + 1
                tag = baseline_path(model, task, r).relative_to(GENERATED.parent)
                done += 1
                print(f"  [{status:14}] ({done}/{total}) {tag}")

    print(f"\nGenerate baseline: {summary}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
