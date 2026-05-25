#!/usr/bin/env python3
"""Phase H Stage 3: run specmut on every spec that typechecked.

Invokes ``specmut analyze --lean-full -n N -e EPSILON -f json -o OUT`` as a
subprocess, then re-shapes the raw output into the Phase H schema documented
in the spec appendix.

specmut produces one of three shapes:
- **Sliced** (Phase E):    {analysis_mode: 'per_theorem', theorem_slices: [...], summary: {...}}
- **Global** (Phase D):    {tightness: {...}, alive_mutants: [...], lean_translation: {...}}
- **Error**:               non-zero exit + plain text error on stderr

We normalize all three into the same downstream schema so the aggregator
doesn't need to branch.  Witnesses are extracted from the Sliced path only;
Global-mode results have ``witnesses: []``.

Skip-if-cached. Failure-tolerant: a single spec timing out or panicking does
not abort the run.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from _common import (
    DEFAULTS,
    PHASE3,
    analyzable_reference_path,
    ensure_lean_on_path,
    generated_path,
    lean_result_path,
    list_models,
    list_tasks,
    list_versions,
    reference_path,
    specmut_bin,
    specmut_result_path,
)

WEAK_THRESHOLD = DEFAULTS["weak_tau_threshold"]


def _summarise_sliced(raw: dict) -> dict:
    """Project a Phase E/F Sliced JSON down to the Phase H schema."""
    summary = raw.get("summary", {})
    slices = raw.get("theorem_slices", [])
    per_theorem = []
    witnesses = []
    weak = []
    total_mut = 0
    total_alive = 0
    total_killed = 0
    contrib_index = {c["theorem"]: c for c in summary.get("contributions", [])}

    for s in slices:
        if s["status"] != "analyzed":
            per_theorem.append({
                "name": s["theorem_name"],
                "tau": None,
                "kill_rate": None,
                "surviving_mutants": None,
                "total_mutants": None,
                "contribution": "None",
                "skip_reason": s.get("skip_reason"),
            })
            continue
        t = s["tightness"]
        n = t["killed"] + t["alive"]
        kr = (t["killed"] / n) if n else 0.0
        total_mut += n
        total_killed += t["killed"]
        total_alive += t["alive"]
        contrib_entry = contrib_index.get(s["theorem_name"], {})
        per_theorem.append({
            "name": s["theorem_name"],
            "tau": t["score"],
            "kill_rate": kr,
            "surviving_mutants": t["alive"],
            "total_mutants": n,
            "contribution": contrib_entry.get("strength", "None"),
        })
        if t["score"] < WEAK_THRESHOLD:
            weak.append(s["theorem_name"])
        for m in (s.get("alive_mutants") or []):
            wit = m.get("witness")
            if wit is None:
                continue
            witnesses.append({
                "theorem": s["theorem_name"],
                "mutant_class": m.get("class"),
                "distance": m.get("distance"),
                "preserved_properties": wit.get("preserved_properties", []),
                "unconstrained_behaviors": wit.get("unconstrained_behaviors", []),
                "interpretation": wit.get("interpretation", ""),
                "model_description": wit.get("model_description", ""),
            })

    return {
        "analysis_mode": "per_theorem",
        "average_tau": summary.get("mean_tightness", 0.0),
        "min_tau": summary.get("min_tightness", 0.0),
        "max_tau": summary.get("max_tightness", 0.0),
        "tau_variance": summary.get("tightness_variance", 0.0),
        "slice_count": len(slices),
        "theorem_count": summary.get("analyzed", 0) + summary.get("skipped", 0),
        "analyzed_theorem_count": summary.get("analyzed", 0),
        "skipped_theorem_count": summary.get("skipped", 0),
        "total_mutants": total_mut,
        "surviving_mutants": total_alive,
        "killed_mutants": total_killed,
        "kill_rate": (total_killed / total_mut) if total_mut else 0.0,
        "weak_theorems": weak,
        "per_theorem": per_theorem,
        "witnesses": witnesses,
        "taxonomy": summary.get("taxonomy", {}),
        "diagnostic_summary": summary.get("diagnostic_summary", ""),
    }


CLASS_INTERPRETATION = {
    "weakening": (
        "The specification was strictly weakened along this dimension and still "
        "admits at least one implementation that satisfies it — meaning the spec "
        "does not constrain the predicate beyond what the weaker form requires."
    ),
    "strengthening": (
        "A strictly stronger variant of the original axiom remains satisfiable: "
        "the auto-implementation models do not distinguish between the spec and "
        "its strengthened form, suggesting the spec admits implementations that "
        "happen to satisfy the stronger property by accident."
    ),
    "replacement": (
        "The original predicate was replaced by a different relation; the "
        "specification does not pin down which atomic predicate must hold, so "
        "an implementation satisfying the replacement also satisfies the spec."
    ),
}


def _synth_witness(mutant: dict, theorem_names: list[str]) -> dict:
    """Build a Phase H-shaped witness from a Global-mode alive_mutant.

    Global mode (Phase D) does not run the Phase F witness extractor, so
    specmut leaves ``witness: None`` on every alive mutant.  We synthesize a
    minimally-informative witness from the data that *is* present —
    mutant class, perturbed component, formula summary, distance — so the
    report still surfaces actionable diagnostics.

    The synthetic interpretation is class-based, not model-based: it explains
    *why this category of mutant tends to survive*, not which concrete model
    distinguishes original from mutant.  The latter requires sliced mode.
    """
    cls = mutant.get("class", "?")
    interpretation = CLASS_INTERPRETATION.get(cls,
        "The mutant survives all auto-selected implementations of the spec — "
        "the spec is silent on whatever distinguishing behavior this perturbation "
        "would expose."
    )
    formula = mutant.get("formula_summary", "")
    perturbed = mutant.get("perturbed_component")
    pieces = []
    if formula:
        pieces.append(f"perturbed axiom: {formula}")
    if perturbed is not None:
        pieces.append(f"component index {perturbed}")
    return {
        "theorem": ", ".join(theorem_names) if theorem_names else "(global)",
        "mutant_class": cls,
        "distance": mutant.get("distance"),
        "preserved_properties": [
            "every auto-selected implementation model satisfies both "
            "the original and this mutated axiom"
        ],
        "unconstrained_behaviors": pieces or ["(no formula summary available)"],
        "interpretation": interpretation,
        "model_description": (
            "(synthetic — Phase F per-model witnesses populate only on the "
            "per-theorem sliced path; this spec landed in global mode)"
        ),
    }


def _summarise_global(raw: dict) -> dict:
    """Project a Phase D Global JSON down to the Phase H schema.

    Global mode has no per-theorem breakdown, so we synthesize a single
    per_theorem entry labeled "(global)" and build best-effort witnesses
    from the alive_mutants array.  These are class-level interpretations,
    not the model-level witnesses that Phase F populates on the sliced path.
    """
    t = raw.get("tightness", {})
    n = t.get("killed", 0) + t.get("alive", 0)
    kr = (t.get("killed", 0) / n) if n else 0.0
    lt = raw.get("lean_translation", {}) or {}
    translated = lt.get("translated_theorems", []) or []
    weak = ["(global)"] if (t.get("score", 0.0) < WEAK_THRESHOLD) else []
    alive = raw.get("alive_mutants", []) or []
    # Cap synthetic witnesses to a small number so the report stays readable.
    max_witnesses = 6
    witnesses = [_synth_witness(m, translated) for m in alive[:max_witnesses]]
    return {
        "analysis_mode": "global",
        "average_tau": t.get("score", 0.0),
        "min_tau": t.get("score", 0.0),
        "max_tau": t.get("score", 0.0),
        "tau_variance": 0.0,
        "slice_count": 0,
        "theorem_count": len(translated),
        "analyzed_theorem_count": len(translated),
        "skipped_theorem_count": len(lt.get("skipped_theorems", []) or []),
        "total_mutants": n,
        "surviving_mutants": t.get("alive", 0),
        "killed_mutants": t.get("killed", 0),
        "kill_rate": kr,
        "weak_theorems": weak,
        "per_theorem": [{
            "name": "(global)",
            "tau": t.get("score", 0.0),
            "kill_rate": kr,
            "surviving_mutants": t.get("alive", 0),
            "total_mutants": n,
            "contribution": "None",
            "translated_theorem_names": translated,
        }],
        "witnesses": witnesses,
        "taxonomy": {},
        "diagnostic_summary": "",
    }


def _empty_result(reason: str) -> dict:
    return {
        "analysis_mode": "failed",
        "average_tau": 0.0,
        "min_tau": 0.0,
        "max_tau": 0.0,
        "tau_variance": 0.0,
        "slice_count": 0,
        "theorem_count": 0,
        "analyzed_theorem_count": 0,
        "skipped_theorem_count": 0,
        "total_mutants": 0,
        "surviving_mutants": 0,
        "killed_mutants": 0,
        "kill_rate": 0.0,
        "weak_theorems": [],
        "per_theorem": [],
        "witnesses": [],
        "taxonomy": {},
        "diagnostic_summary": "",
        "specmut_error": reason,
    }


def run_specmut(spec_path: Path, *, model_bound: int, epsilon: float,
                timeout: int) -> tuple[dict, dict]:
    """Run specmut and return (normalized, raw) result dicts.

    raw is None when specmut errored before producing JSON.
    """
    bin_ = specmut_bin()
    tmp_out = Path("/tmp") / f"phase3_specmut_{time.monotonic_ns()}.json"
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
    except subprocess.TimeoutExpired:
        return _empty_result(f"specmut timeout after {timeout}s") | {"elapsed_sec": float(timeout)}, None
    elapsed = round(time.monotonic() - start, 3)
    if proc.returncode != 0 or not tmp_out.exists() or tmp_out.stat().st_size == 0:
        msg = (proc.stderr or proc.stdout or "(no output)").strip().splitlines()[-1][:200]
        if tmp_out.exists():
            tmp_out.unlink()
        return _empty_result(f"specmut exit {proc.returncode}: {msg}") | {"elapsed_sec": elapsed}, None
    raw = json.loads(tmp_out.read_text())
    tmp_out.unlink()
    if "theorem_slices" in raw:
        normalized = _summarise_sliced(raw)
    elif "tightness" in raw:
        normalized = _summarise_global(raw)
    else:
        normalized = _empty_result("unknown specmut JSON shape")
    normalized["elapsed_sec"] = elapsed
    return normalized, raw


def lean_passed(model: str, task: str, version: int) -> bool:
    """Check whether lean_check.py marked this spec typecheck_success.

    If no lean result exists yet, we assume it's OK and let specmut decide.
    """
    p = lean_result_path(model, task, version)
    if not p.exists():
        return True
    try:
        return json.loads(p.read_text()).get("typecheck_success", False)
    except Exception:
        return True


def run_one(spec_path: Path, out_path: Path, *, source: str, task: str,
            version: int, model_bound: int, epsilon: float, timeout: int,
            force: bool) -> str:
    if out_path.exists() and not force:
        return "cached"
    if not spec_path.exists():
        return "missing"
    normalized, raw = run_specmut(spec_path, model_bound=model_bound,
                                   epsilon=epsilon, timeout=timeout)
    record = {
        "file": str(spec_path.relative_to(PHASE3.parent)),
        "source": "human" if source == "human" else "llm",
        "model": source,
        "task": task,
        "version": version,
        "parameters": {"model_bound": model_bound, "epsilon": epsilon},
        **normalized,
    }
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(record, indent=2))
    return "ok" if record["analysis_mode"] != "failed" else "fail"


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("-n", "--model-bound", type=int, default=DEFAULTS["model_bound"])
    ap.add_argument("-e", "--epsilon", type=float, default=DEFAULTS["epsilon"])
    ap.add_argument("--timeout", type=int, default=DEFAULTS["specmut_timeout_sec"])
    ap.add_argument("--task")
    ap.add_argument("--model")
    ap.add_argument("--force", action="store_true")
    ap.add_argument("--skip-failed-typecheck", action="store_true",
                    help="don't run specmut on files that did not typecheck")
    args = ap.parse_args()
    ensure_lean_on_path()

    tasks = [args.task] if args.task else list_tasks()
    models = [args.model] if args.model else list_models()
    summary = {"ok": 0, "fail": 0, "cached": 0, "missing": 0, "skipped_no_tc": 0}

    # References: analyze the *projected* file (reference_analyzable.lean),
    # not the verbatim one.  The verbatim file is the provenance anchor —
    # it stays intact on disk and gets surfaced in the report alongside the
    # projection's τ score.  The projection is what specmut can actually
    # consume given its bounded analysis.
    for task in tasks:
        spec = analyzable_reference_path(task)
        out = specmut_result_path("human", task)
        status = run_one(spec, out, source="human", task=task, version=0,
                         model_bound=args.model_bound, epsilon=args.epsilon,
                         timeout=args.timeout, force=args.force)
        summary[status] = summary.get(status, 0) + 1
        print(f"  [{status:7}] {spec.relative_to(PHASE3.parent)}")

    for model in models:
        for task in tasks:
            for v in list_versions(model, task):
                if args.skip_failed_typecheck and not lean_passed(model, task, v):
                    summary["skipped_no_tc"] += 1
                    print(f"  [skip-tc] {model}/{task}/v{v}")
                    continue
                spec = generated_path(model, task, v)
                out = specmut_result_path(model, task, v)
                status = run_one(spec, out, source=model, task=task, version=v,
                                 model_bound=args.model_bound, epsilon=args.epsilon,
                                 timeout=args.timeout, force=args.force)
                summary[status] = summary.get(status, 0) + 1
                print(f"  [{status:7}] {spec.relative_to(PHASE3.parent)}")

    print(f"\nspecmut stage: {summary}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
