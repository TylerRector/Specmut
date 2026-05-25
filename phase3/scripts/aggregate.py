#!/usr/bin/env python3
"""Phase H Stage 4: aggregate per-spec results into cross-experiment views.

Reads every JSON under ``specmut_results/`` and ``lean_results/`` and writes
three artifacts to ``aggregate/``:

- **summary.json**     — per-model averages and totals, per-task tables.
- **comparison.json**  — human reference vs each (model, round) per task.
- **progression.json** — trajectory of τ / kill rate across rounds, per (task, model).

All artifacts are overwritten on every run. No caching here — aggregation is
cheap, and downstream tools expect a single source of truth.
"""

from __future__ import annotations

import json
import statistics
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from _common import (
    AGGREGATE,
    LEAN_RESULTS,
    SPECMUT_RESULTS,
    analyzable_reference_path,
    list_models,
    list_tasks,
    load_provenance,
    reference_path,
)


def _file_loc(path) -> int:
    try:
        return sum(1 for _ in path.open())
    except Exception:
        return 0


def load_specmut(path: Path) -> dict | None:
    if not path.exists():
        return None
    try:
        return json.loads(path.read_text())
    except Exception:
        return None


def load_lean(path: Path) -> dict | None:
    if not path.exists():
        return None
    try:
        return json.loads(path.read_text())
    except Exception:
        return None


def lean_compile_success(model: str, task: str, version: int | None) -> bool:
    if model == "human":
        p = LEAN_RESULTS / "human" / task / "reference.json"
    else:
        p = LEAN_RESULTS / model / task / f"v{version}.json"
    lr = load_lean(p)
    if lr is None:
        return False
    return bool(lr.get("typecheck_success"))


def analyzable_compile_success(task: str) -> bool:
    lr = load_lean(LEAN_RESULTS / "human" / task / "reference_analyzable.json")
    if lr is None:
        return False
    return bool(lr.get("typecheck_success"))


def build_comparison() -> dict:
    tasks_out = []
    for task in list_tasks():
        comparisons = []
        # Human reference first — note compile_success here is for the
        # verbatim reference.lean (the canonical GitHub artifact), while
        # tau/kill_rate are from analyzing the reduced projection.
        human = load_specmut(SPECMUT_RESULTS / "human" / task / "reference.json")
        ana_compile = analyzable_compile_success(task)
        ref_compile = lean_compile_success("human", task, None)
        if human is not None:
            comparisons.append({
                "source": "human_reference",
                "compile_success": ref_compile,
                "analyzable_compile_success": ana_compile,
                "tau": human["average_tau"],
                "kill_rate": human["kill_rate"],
                "theorem_count": human["theorem_count"],
                "weak_theorems": len(human["weak_theorems"]),
                "surviving_mutants": human["surviving_mutants"],
                "total_mutants": human["total_mutants"],
                "analysis_mode": human["analysis_mode"],
            })
        for model in list_models():
            d = SPECMUT_RESULTS / model / task
            if not d.exists():
                continue
            for f in sorted(d.glob("v*.json")):
                r = load_specmut(f)
                if r is None:
                    continue
                comparisons.append({
                    "source": f"{model}/v{r['version']}",
                    "compile_success": lean_compile_success(model, task, r["version"]),
                    "tau": r["average_tau"],
                    "kill_rate": r["kill_rate"],
                    "theorem_count": r["theorem_count"],
                    "weak_theorems": len(r["weak_theorems"]),
                    "surviving_mutants": r["surviving_mutants"],
                    "total_mutants": r["total_mutants"],
                    "analysis_mode": r["analysis_mode"],
                })
        tasks_out.append({"task": task, "comparisons": comparisons})
    return {"tasks": tasks_out}


def build_progression() -> dict:
    trajectories = []
    for task in list_tasks():
        for model in list_models():
            d = SPECMUT_RESULTS / model / task
            if not d.exists():
                continue
            points = []
            for f in sorted(d.glob("v*.json"), key=lambda p: int(p.stem[1:])):
                r = load_specmut(f)
                if r is None:
                    continue
                points.append({
                    "version": r["version"],
                    "tau": r["average_tau"],
                    "kill_rate": r["kill_rate"],
                    "weak_theorems": len(r["weak_theorems"]),
                    "compile_success": lean_compile_success(model, task, r["version"]),
                    "analysis_mode": r["analysis_mode"],
                })
            if points:
                trajectories.append({"task": task, "model": model, "points": points})
    return {"trajectories": trajectories}


def build_summary() -> dict:
    # Per-model aggregate metrics across all (task, round) combinations.
    per_model = {}
    for model in list_models():
        taus, kill_rates, mut_counts, weak_counts = [], [], [], []
        compile_pass = compile_fail = 0
        for task in list_tasks():
            for f in sorted((SPECMUT_RESULTS / model / task).glob("v*.json")) \
                     if (SPECMUT_RESULTS / model / task).exists() else []:
                r = load_specmut(f)
                if r is None:
                    continue
                taus.append(r["average_tau"])
                kill_rates.append(r["kill_rate"])
                mut_counts.append(r["total_mutants"])
                weak_counts.append(len(r["weak_theorems"]))
                if lean_compile_success(model, task, r["version"]):
                    compile_pass += 1
                else:
                    compile_fail += 1
        per_model[model] = {
            "n_specs": len(taus),
            "mean_tau": statistics.fmean(taus) if taus else 0.0,
            "stdev_tau": statistics.stdev(taus) if len(taus) >= 2 else 0.0,
            "mean_kill_rate": statistics.fmean(kill_rates) if kill_rates else 0.0,
            "total_mutants": sum(mut_counts),
            "mean_weak_theorems": statistics.fmean(weak_counts) if weak_counts else 0.0,
            "compile_pass": compile_pass,
            "compile_fail": compile_fail,
        }

    human = {}
    for task in list_tasks():
        r = load_specmut(SPECMUT_RESULTS / "human" / task / "reference.json")
        prov = load_provenance(task)
        ref_loc = _file_loc(reference_path(task))
        ana_loc = _file_loc(analyzable_reference_path(task))
        block = {
            "provenance": prov,  # may be None
            "reference_loc": ref_loc,
            "analyzable_loc": ana_loc,
            "reference_compile_success": lean_compile_success("human", task, None),
            "analyzable_compile_success": analyzable_compile_success(task),
        }
        if r is not None:
            block.update({
                "tau": r["average_tau"],
                "kill_rate": r["kill_rate"],
                "weak_theorems": len(r["weak_theorems"]),
                "total_mutants": r["total_mutants"],
                "analysis_mode": r["analysis_mode"],
                "specmut_error": r.get("specmut_error"),
            })
        else:
            block.update({
                "tau": None,
                "kill_rate": None,
                "weak_theorems": None,
                "total_mutants": 0,
                "analysis_mode": "missing",
                "specmut_error": None,
            })
        human[task] = block

    return {
        "tasks": list_tasks(),
        "models": list_models(),
        "human_reference": human,
        "per_model": per_model,
    }


def main() -> int:
    AGGREGATE.mkdir(parents=True, exist_ok=True)
    summary = build_summary()
    comparison = build_comparison()
    progression = build_progression()

    (AGGREGATE / "summary.json").write_text(json.dumps(summary, indent=2))
    (AGGREGATE / "comparison.json").write_text(json.dumps(comparison, indent=2))
    (AGGREGATE / "progression.json").write_text(json.dumps(progression, indent=2))

    print(f"Aggregate wrote {len(list(AGGREGATE.glob('*.json')))} artifacts to {AGGREGATE}")
    # Print a quick condensed view so the operator sees the headline result.
    for t in comparison["tasks"]:
        print(f"\n  Task: {t['task']}")
        for c in t["comparisons"]:
            print(f"    {c['source']:<22} tau={c['tau']:.3f}  kr={c['kill_rate']:.3f}  "
                  f"compile={c['compile_success']}  weak={c['weak_theorems']}  mode={c['analysis_mode']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
