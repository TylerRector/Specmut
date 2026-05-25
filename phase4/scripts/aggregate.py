#!/usr/bin/env python3
"""Phase 4 Stage 9: full statistical aggregation.

Reads everything under lean_results/, specmut_results/, feedback/,
determinism/, and writes:

  - aggregate/experiment_a.json   (descriptive distributions, controls, cross-model tests)
  - aggregate/experiment_b.json   (paired tests, Wilcoxon, McNemar, effect sizes)
  - aggregate/summary.json        (high-level snapshot)

Uses scipy.stats for nonparametric tests + BCa bootstrap CIs (manual
implementation since scipy.stats.bootstrap can compute BCa).
"""

from __future__ import annotations

import argparse
import json
import math
import statistics
import sys
from pathlib import Path

import numpy as np
from scipy import stats

sys.path.insert(0, str(Path(__file__).resolve().parent))
from _common import (
    AGGREGATE,
    DETERMINISM,
    LEAN_RESULTS,
    PHASE4,
    SPECMUT_RESULTS,
    feedback_path,
    list_tasks,
    load_config,
    model_slots,
    repaired_meta_path,
    replicate_indices,
)


# Repair-template statuses emitted by validate_repair_template.py +
# generate_repaired.py, in a fixed order for stable breakdown dicts.
REPAIR_TEMPLATE_STATUSES = [
    "repair_template_ok",
    "repair_no_change",
    "repair_required_theorem_missing",
    "repair_irrelevant_tautology",
    "repair_wrong_task_template",
    "repair_forbidden_freeform",
    "repair_too_many_theorems",
    "repair_template_rejected",
    "repair_syntax_rejected",
    "repair_generation_failed",
]


def _repaired_template_breakdown(model: str, task: str) -> dict:
    """Tally repair_template_status across all replicates for a cell.

    Reads the repaired .meta.json files (written by generate_repaired.py in
    specmut-informed mode).  Returns a dict with every status (zero-filled)
    plus the convenience counts the spec asks for.
    """
    counts = {s: 0 for s in REPAIR_TEMPLATE_STATUSES}
    counts["unknown_or_legacy"] = 0
    for r in replicate_indices():
        mp = repaired_meta_path(model, task, r)
        if not mp.exists():
            continue
        try:
            meta = json.loads(mp.read_text())
        except Exception:
            continue
        st = meta.get("repair_template_status")
        if st in counts:
            counts[st] += 1
        elif st is None:
            counts["unknown_or_legacy"] += 1
        else:
            counts[st] = counts.get(st, 0) + 1
    return counts


def _repaired_status_by_replicate(model: str, task: str) -> dict:
    """Map replicate -> repair_template_status from the repaired meta files.

    Used to split the paired Δτ analysis into an 'all repairs' view and a
    'template_ok only' view.  Replicates without a recorded status map to
    'unknown_or_legacy'.
    """
    out: dict = {}
    for r in replicate_indices():
        mp = repaired_meta_path(model, task, r)
        if not mp.exists():
            continue
        try:
            meta = json.loads(mp.read_text())
        except Exception:
            continue
        out[r] = meta.get("repair_template_status") or "unknown_or_legacy"
    return out


# ---------- I/O helpers ---------- #

def _read(p: Path) -> dict | None:
    if not p.exists():
        return None
    try:
        return json.loads(p.read_text())
    except Exception:
        return None


def _baseline_records(model: str, task: str) -> list[dict]:
    out = []
    for r in replicate_indices():
        sm = SPECMUT_RESULTS / "baseline" / _model_dir(model) / task / f"rep_{r:02d}.json"
        record = _read(sm)
        if record is None:
            # Fall back to lean result so attrition counts include compile failures.
            lr = LEAN_RESULTS / "baseline" / _model_dir(model) / task / f"rep_{r:02d}.json"
            lr_data = _read(lr)
            if lr_data is None:
                continue
            record = {
                "replicate": r, "model": model, "task": task,
                "analysis_status": "skipped_lean_failure",
                "average_tau": 0.0, "kill_rate": 0.0, "surviving_mutants": 0,
                "total_mutants": 0, "theorem_count": 0, "weak_theorems": [],
                "per_theorem": [], "lean_status": lr_data.get("status"),
            }
        record["replicate"] = r
        out.append(record)
    return out


def _repaired_records(model: str, task: str) -> list[dict]:
    out = []
    for r in replicate_indices():
        sm = SPECMUT_RESULTS / "repaired" / _model_dir(model) / task / f"rep_{r:02d}.json"
        record = _read(sm)
        if record is None:
            lr = LEAN_RESULTS / "repaired" / _model_dir(model) / task / f"rep_{r:02d}.json"
            lr_data = _read(lr)
            if lr_data is None:
                continue
            record = {
                "replicate": r, "model": model, "task": task,
                "analysis_status": "skipped_lean_failure",
                "average_tau": 0.0, "kill_rate": 0.0, "surviving_mutants": 0,
                "total_mutants": 0, "theorem_count": 0, "weak_theorems": [],
                "per_theorem": [], "lean_status": lr_data.get("status"),
            }
        record["replicate"] = r
        out.append(record)
    return out


def _model_dir(model: str) -> str:
    return model.replace("/", "_").replace(":", "__")


# ---------- statistical helpers ---------- #

def _bca_ci(values: list[float], *, n_resamples: int = 10000,
            seed: int = 0, ci: float = 0.95) -> list[float] | None:
    """BCa bootstrap CI for the median.  Returns None for empty input."""
    if not values:
        return None
    if len(values) == 1:
        return [values[0], values[0]]
    res = stats.bootstrap(
        (np.asarray(values),), np.median,
        confidence_level=ci, n_resamples=n_resamples,
        method="BCa", random_state=seed,
    )
    return [float(res.confidence_interval.low),
            float(res.confidence_interval.high)]


def _bh_adjust(pvalues: list[float]) -> list[float]:
    """Benjamini-Hochberg FDR adjustment.  Returns the same length as input."""
    if not pvalues:
        return []
    pv = np.asarray(pvalues)
    n = len(pv)
    order = np.argsort(pv)
    adj = np.empty(n)
    prev = 1.0
    for rank, idx in enumerate(reversed(order)):
        k = n - rank
        val = pv[idx] * n / k
        prev = min(prev, val)
        adj[idx] = min(prev, 1.0)
    return adj.tolist()


def _rank_biserial(x: list[float], y: list[float]) -> float:
    """Mann-Whitney rank-biserial effect size for two-group comparison."""
    if not x or not y:
        return 0.0
    n_x = len(x); n_y = len(y)
    u, _ = stats.mannwhitneyu(x, y, alternative="two-sided")
    return float(1.0 - (2 * u) / (n_x * n_y))


def _matched_rank_biserial(diffs: list[float]) -> float:
    """Matched-pairs rank-biserial r for paired Wilcoxon."""
    nonzero = [d for d in diffs if d != 0]
    if not nonzero:
        return 0.0
    ranks = stats.rankdata([abs(d) for d in nonzero])
    pos = sum(r for r, d in zip(ranks, nonzero) if d > 0)
    neg = sum(r for r, d in zip(ranks, nonzero) if d < 0)
    total = pos + neg
    if total == 0:
        return 0.0
    return float((pos - neg) / total)


# ---------- experiment A ---------- #

def build_experiment_a() -> dict:
    cfg = load_config()
    cells = []
    pvals_to_correct: list[tuple[str, float]] = []
    neg_control_tests = []
    cross_model_tests = []

    tasks = list_tasks()
    models = [m[1]["name"] for m in model_slots()]

    # Controls: load reference, trivial, partial per task once.
    controls = []
    for task in tasks:
        ref = _read(SPECMUT_RESULTS / "references" / f"{task}.json") or {}
        for kind in ("trivial", "partial"):
            p = SPECMUT_RESULTS / "controls" / f"{task}_{kind}.json"
            d = _read(p) or {}
            controls.append({
                "task": task,
                "control_type": kind,
                "tau": d.get("average_tau", 0.0),
                "kill_rate": d.get("kill_rate", 0.0),
                "analysis_status": d.get("analysis_status", "missing"),
            })
        controls.append({
            "task": task, "control_type": "reference",
            "tau": ref.get("average_tau", 0.0),
            "kill_rate": ref.get("kill_rate", 0.0),
            "analysis_status": ref.get("analysis_status", "missing"),
        })

    # Per (model, task) cell.
    for model in models:
        for task in tasks:
            records = _baseline_records(model, task)
            n_gen = len(records)
            n_compiled = sum(1 for r in records
                             if r.get("analysis_status") not in (None, "skipped_lean_failure"))
            n_success = sum(1 for r in records
                            if r.get("analysis_status") == "success")

            taus = [r["average_tau"] for r in records
                    if r.get("analysis_status") == "success"]
            krs = [r["kill_rate"] for r in records
                   if r.get("analysis_status") == "success"]
            surv = [r.get("surviving_mutants", 0) for r in records
                    if r.get("analysis_status") == "success"]
            cov = [r.get("theorem_coverage", 0.0) for r in records
                   if r.get("analysis_status") == "success"]
            ss = [r.get("slice_success_rate", 0.0) for r in records
                  if r.get("analysis_status") == "success"]
            runtimes = [r.get("runtime_sec", 0.0) for r in records
                        if r.get("analysis_status") == "success"]
            mspace = [r.get("model_space_estimate", 0) for r in records
                      if r.get("analysis_status") == "success"]

            # Failure breakdown — count every record by its status.
            breakdown = {}
            for r in records:
                k = r.get("analysis_status", "unknown")
                breakdown[k] = breakdown.get(k, 0) + 1
            # Add compile failures observed only in lean_results.
            for r in range(1, cfg["experiment"]["replicates"] + 1):
                # Only the explicit-compile-failure case (no specmut record at all).
                if not any(rec["replicate"] == r for rec in records):
                    breakdown["compile_failure"] = breakdown.get("compile_failure", 0) + 1
                    n_gen += 0  # do not double-count

            cell = {
                "model": model,
                "task": task,
                "n_generated": cfg["experiment"]["replicates"],
                "n_records": n_gen,
                "n_compiled": n_compiled,
                "n_analyzable": n_success,
                "compile_rate": (n_compiled / cfg["experiment"]["replicates"])
                                if cfg["experiment"]["replicates"] else 0.0,
                "analyzable_rate": (n_success / max(n_compiled, 1)) if n_compiled else 0.0,
                "tau_values": taus,
                "tau_median": float(np.median(taus)) if taus else None,
                "tau_iqr": [float(np.percentile(taus, 25)),
                            float(np.percentile(taus, 75))] if len(taus) >= 2 else None,
                "tau_ci_95": _bca_ci(taus),
                "kill_rate_median": float(np.median(krs)) if krs else None,
                "kill_rate_iqr": [float(np.percentile(krs, 25)),
                                  float(np.percentile(krs, 75))] if len(krs) >= 2 else None,
                "surviving_mutant_mean": float(np.mean(surv)) if surv else None,
                "theorem_coverage_mean": float(np.mean(cov)) if cov else None,
                "slice_success_rate_mean": float(np.mean(ss)) if ss else None,
                "runtime_median_sec": float(np.median(runtimes)) if runtimes else None,
                "runtime_p95_sec": float(np.percentile(runtimes, 95)) if len(runtimes) >= 2 else None,
                "model_space_median": float(np.median(mspace)) if mspace else None,
                "cv_tau": float(np.std(taus) / np.mean(taus))
                          if taus and np.mean(taus) > 0 else None,
                "failure_breakdown": breakdown,
            }
            cells.append(cell)

            # Negative-control tests: compare LLM tau vs trivial tau for this task.
            triv = next((c for c in controls
                         if c["task"] == task and c["control_type"] == "trivial"), None)
            if triv is not None and taus:
                triv_vec = [triv["tau"]] * max(len(taus), 5)  # repeat single point
                u, p = stats.mannwhitneyu(taus, triv_vec, alternative="greater")
                neg_control_tests.append({
                    "task": task,
                    "model": model,
                    "comparison": f"{model}_baseline_vs_trivial",
                    "test": "mann_whitney_u",
                    "statistic": float(u),
                    "p_value": float(p),
                    "effect_size_rank_biserial": _rank_biserial(taus, triv_vec),
                })
                pvals_to_correct.append(("neg_control", p))

    # BH-adjust negative control p-values.
    if neg_control_tests:
        ps = [t["p_value"] for t in neg_control_tests]
        adj = _bh_adjust(ps)
        for t, a in zip(neg_control_tests, adj):
            t["p_adjusted"] = float(a)

    # Cross-model Kruskal-Wallis per task.
    cm_pvals = []
    for task in tasks:
        group_taus = []
        for model in models:
            recs = _baseline_records(model, task)
            taus = [r["average_tau"] for r in recs if r.get("analysis_status") == "success"]
            if taus:
                group_taus.append(taus)
        if len(group_taus) >= 2 and all(g for g in group_taus):
            try:
                h, p = stats.kruskal(*group_taus)
                cross_model_tests.append({
                    "task": task,
                    "test": "kruskal_wallis",
                    "n_groups": len(group_taus),
                    "statistic": float(h),
                    "p_value": float(p),
                })
                cm_pvals.append(p)
            except Exception:
                continue
    if cross_model_tests:
        adj = _bh_adjust(cm_pvals)
        for t, a in zip(cross_model_tests, adj):
            t["p_adjusted"] = float(a)

    det = _read(DETERMINISM / "validation_log.json") or {}
    determinism = {
        "files_tested": det.get("files_tested", 0),
        "runs_per_file": det.get("runs_per_file", 0),
        "all_deterministic": det.get("all_deterministic"),
    }

    return {
        "cells": cells,
        "controls": controls,
        "cross_model_tests": cross_model_tests,
        "negative_control_tests": neg_control_tests,
        "determinism": determinism,
    }


# ---------- experiment B ---------- #

def build_experiment_b() -> dict:
    cfg = load_config()
    cells = []
    all_pairs: list[tuple[float, float]] = []
    tasks = list_tasks()
    models = [m[1]["name"] for m in model_slots()]
    cell_pvals_for_correction: list[float] = []
    cell_index_for_correction: list[int] = []

    for model in models:
        for task in tasks:
            base = _baseline_records(model, task)
            rep = _repaired_records(model, task)
            base_by_r = {r["replicate"]: r for r in base}
            rep_by_r = {r["replicate"]: r for r in rep}
            pair_keys = sorted(set(base_by_r) & set(rep_by_r))

            n_total = cfg["experiment"]["replicates"]
            n_both_compiled = 0
            n_both_analyzable = 0
            compile_a = 0; compile_b = 0
            baseline_compile = []; repaired_compile = []
            baseline_analyz = []; repaired_analyz = []

            cell_pairs = []
            for r in pair_keys:
                b = base_by_r[r]; rp = rep_by_r[r]
                b_compiled = b.get("analysis_status") not in (None, "skipped_lean_failure")
                rp_compiled = rp.get("analysis_status") not in (None, "skipped_lean_failure")
                b_an = b.get("analysis_status") == "success"
                rp_an = rp.get("analysis_status") == "success"
                if b_compiled: compile_a += 1
                if rp_compiled: compile_b += 1
                baseline_compile.append(b_compiled)
                repaired_compile.append(rp_compiled)
                baseline_analyz.append(b_an)
                repaired_analyz.append(rp_an)
                if b_compiled and rp_compiled:
                    n_both_compiled += 1
                if b_an and rp_an:
                    n_both_analyzable += 1
                cell_pairs.append({
                    "replicate": r,
                    "baseline_tau": b.get("average_tau", 0.0),
                    "repaired_tau": rp.get("average_tau", 0.0),
                    "delta_tau": rp.get("average_tau", 0.0) - b.get("average_tau", 0.0),
                    "baseline_compiled": b_compiled,
                    "repaired_compiled": rp_compiled,
                    "baseline_analyzable": b_an,
                    "repaired_analyzable": rp_an,
                })

            # McNemar on paired compile: a = both compile, b = base only,
            # c = rep only, d = both fail.
            t1 = [(bc, rc) for bc, rc in zip(baseline_compile, repaired_compile)]
            n_a = sum(1 for bc, rc in t1 if bc and rc)
            n_b = sum(1 for bc, rc in t1 if bc and not rc)
            n_c = sum(1 for bc, rc in t1 if not bc and rc)
            n_d = sum(1 for bc, rc in t1 if not bc and not rc)
            # scipy doesn't have McNemar directly outside statsmodels — use binomial.
            mcnemar_p = stats.binomtest(min(n_b, n_c), n_b + n_c, p=0.5).pvalue \
                        if (n_b + n_c) > 0 else 1.0

            # Wilcoxon paired tau on both_analyzable pairs.
            both = [p for p in cell_pairs
                    if p["baseline_analyzable"] and p["repaired_analyzable"]]
            wilcoxon_p = None; wilcoxon_stat = None; effect = None
            delta_med = None; delta_ci = None
            n_imp = n_reg = n_unc = 0
            # BUGFIX: descriptive stats (median Δτ, improved/regressed/unchanged
            # counts) must be computed for ANY n >= 1 — previously they were
            # gated behind `len(both) >= 5`, so a single dropped pair (e.g. a
            # set_insert replicate that failed Lean on both sides) silently
            # zeroed delta_tau_median / n_improved for an otherwise all-positive
            # task.  Only the INFERENTIAL Wilcoxon test stays gated on sample
            # size (it is meaningless with very few nonzero pairs).
            _EPS = 1e-9
            diffs = [p["delta_tau"] for p in both]
            if diffs:
                delta_med = float(np.median(diffs))
                delta_ci = _bca_ci(diffs)
                n_imp = sum(1 for d in diffs if d > _EPS)
                n_reg = sum(1 for d in diffs if d < -_EPS)
                n_unc = sum(1 for d in diffs if abs(d) <= _EPS)
                all_pairs.extend((p["baseline_tau"], p["repaired_tau"]) for p in both)
                nonzero = [d for d in diffs if abs(d) > _EPS]
                if len(both) >= 5 and nonzero:
                    try:
                        ws = stats.wilcoxon(diffs, alternative="two-sided",
                                            zero_method="wilcox")
                        wilcoxon_stat = float(ws.statistic)
                        wilcoxon_p = float(ws.pvalue)
                        effect = _matched_rank_biserial(diffs)
                    except Exception:
                        wilcoxon_p = None

            # Raw paired value lists (over both-analyzable pairs) — exposed
            # for downstream plotting / re-analysis.
            baseline_tau_values = [p["baseline_tau"] for p in both]
            repaired_tau_values = [p["repaired_tau"] for p in both]
            paired_delta_tau_values = [p["delta_tau"] for p in both]

            # Repair-template status tallies (specmut-informed mode).
            tmpl = _repaired_template_breakdown(model, task)
            status_by_r = _repaired_status_by_replicate(model, task)

            # ---- compliance counts ----
            n_repairs = sum(tmpl.values())
            ok_count = tmpl.get("repair_template_ok", 0)
            invalid_count = n_repairs - ok_count
            valid_repair_rate = (ok_count / n_repairs) if n_repairs else None

            # ---- two paired-Δτ views ----
            # 'all repairs': every both-analyzable pair (current behavior).
            # 'template_ok': both-analyzable pairs whose repair passed semantic
            #   validation.  When blocking is ON these coincide (invalid repairs
            #   become non-analyzable stubs); when OFF, template_ok isolates the
            #   compliant subset.
            def _delta_view(pairs: list) -> dict:
                dv = [p["delta_tau"] for p in pairs]
                if not dv:
                    return {"n": 0, "values": [], "median": None,
                            "pos": 0, "neg": 0, "zero": 0}
                return {
                    "n": len(dv),
                    "values": dv,
                    "median": float(np.median(dv)),
                    "pos": sum(1 for d in dv if d > _EPS),
                    "neg": sum(1 for d in dv if d < -_EPS),
                    "zero": sum(1 for d in dv if abs(d) <= _EPS),
                }
            both_ok = [p for p in both
                       if status_by_r.get(p["replicate"]) == "repair_template_ok"]
            view_all = _delta_view(both)
            view_ok = _delta_view(both_ok)

            cell = {
                "model": model,
                "task": task,
                "n_pairs_total": n_total,
                "n_pairs_both_compiled": n_both_compiled,
                "n_pairs_both_analyzable": n_both_analyzable,
                # Explicit n behind the paired Δτ descriptive stats below
                # (== number of both-analyzable pairs == len(diffs)).
                "n_pairs": len(both),
                "baseline_compile_rate": (compile_a / max(len(pair_keys), 1)),
                "repaired_compile_rate": (compile_b / max(len(pair_keys), 1)),
                "compile_mcnemar_p": float(mcnemar_p),
                "baseline_tau_median": (float(np.median(baseline_tau_values))
                                        if both else None),
                "repaired_tau_median": (float(np.median(repaired_tau_values))
                                        if both else None),
                "delta_tau_median": delta_med,
                "delta_tau_ci_95": delta_ci,
                "wilcoxon_statistic": wilcoxon_stat,
                "wilcoxon_p": wilcoxon_p,
                "effect_size_matched_rank_biserial": effect,
                "n_improved": n_imp,
                "n_regressed": n_reg,
                "n_unchanged": n_unc,
                # Spec-mandated convenience aliases / raw lists.
                "positive_delta_count": n_imp,
                "negative_delta_count": n_reg,
                "zero_delta_count": n_unc,
                "baseline_tau_values": baseline_tau_values,
                "repaired_tau_values": repaired_tau_values,
                "paired_delta_tau_values": paired_delta_tau_values,
                # Repair-template diagnostics + compliance.
                "repair_template_breakdown": tmpl,
                "repair_no_change_count": tmpl.get("repair_no_change", 0),
                "repair_template_rejected_count": tmpl.get("repair_template_rejected", 0),
                "repair_required_theorem_missing_count":
                    tmpl.get("repair_required_theorem_missing", 0),
                "repair_too_many_theorems_count":
                    tmpl.get("repair_too_many_theorems", 0),
                "repair_template_ok_count": ok_count,
                "repair_invalid_count": invalid_count,
                "n_repairs": n_repairs,
                "valid_repair_rate": valid_repair_rate,
                # ---- paired Δτ: ALL repairs (both-analyzable) ----
                "n_pairs_all_repairs": view_all["n"],
                "paired_delta_tau_values_all_repairs": view_all["values"],
                "delta_tau_median_all_repairs": view_all["median"],
                "positive_delta_count_all_repairs": view_all["pos"],
                "negative_delta_count_all_repairs": view_all["neg"],
                "zero_delta_count_all_repairs": view_all["zero"],
                # ---- paired Δτ: template_ok repairs only ----
                "n_pairs_template_ok": view_ok["n"],
                "paired_delta_tau_values_template_ok": view_ok["values"],
                "delta_tau_median_template_ok": view_ok["median"],
                "positive_delta_count_template_ok": view_ok["pos"],
                "negative_delta_count_template_ok": view_ok["neg"],
                "zero_delta_count_template_ok": view_ok["zero"],
                "pairs": cell_pairs,
            }
            cells.append(cell)
            if wilcoxon_p is not None:
                cell_pvals_for_correction.append(wilcoxon_p)
                cell_index_for_correction.append(len(cells) - 1)

    # Adjust within-cell Wilcoxon p-values across all cells with valid tests.
    if cell_pvals_for_correction:
        adj = _bh_adjust(cell_pvals_for_correction)
        for idx, a in zip(cell_index_for_correction, adj):
            cells[idx]["wilcoxon_p_adjusted"] = float(a)

    # Aggregate test across all paired (baseline, repaired) on analyzable pairs.
    agg = {}
    if all_pairs:
        bvec = [p[0] for p in all_pairs]
        rvec = [p[1] for p in all_pairs]
        diffs = [r - b for b, r in all_pairs]
        if any(d != 0 for d in diffs):
            try:
                ws = stats.wilcoxon(diffs, alternative="two-sided", zero_method="wilcox")
                agg = {
                    "n_pairs": len(all_pairs),
                    "wilcoxon_statistic": float(ws.statistic),
                    "wilcoxon_p": float(ws.pvalue),
                    "delta_tau_median": float(np.median(diffs)),
                    "delta_tau_ci_95": _bca_ci(diffs),
                    "effect_size_matched_rank_biserial": _matched_rank_biserial(diffs),
                }
            except Exception:
                agg = {"n_pairs": len(all_pairs), "wilcoxon_p": None,
                       "delta_tau_median": float(np.median(diffs))}
        else:
            agg = {"n_pairs": len(all_pairs), "wilcoxon_p": None,
                   "delta_tau_median": 0.0}

    # Top-level repair-template summary across all cells.
    repair_summary = {s: 0 for s in REPAIR_TEMPLATE_STATUSES}
    repair_summary["unknown_or_legacy"] = 0
    for c in cells:
        for k, v in c.get("repair_template_breakdown", {}).items():
            repair_summary[k] = repair_summary.get(k, 0) + v
    repair_summary["total_delta_positive"] = sum(c["positive_delta_count"] for c in cells)
    repair_summary["total_delta_negative"] = sum(c["negative_delta_count"] for c in cells)
    repair_summary["total_delta_zero"] = sum(c["zero_delta_count"] for c in cells)
    # Per-task non-ceiling improvement flag (positive median delta).
    repair_summary["tasks_with_positive_median_delta"] = sorted({
        c["task"] for c in cells
        if c.get("delta_tau_median") is not None and c["delta_tau_median"] > 0
    })

    return {"cells": cells, "aggregate_test": agg,
            "repair_template_summary": repair_summary}


# ---------- summary ---------- #

def build_summary(exp_a: dict, exp_b: dict) -> dict:
    return {
        "tasks": list_tasks(),
        "models": [m[1]["name"] for m in model_slots()],
        "n_cells": len(exp_a["cells"]),
        "n_generations_total": sum(c["n_records"] for c in exp_a["cells"])
                              + sum(c["n_pairs_both_compiled"] for c in exp_b["cells"]),
        "determinism_validated": exp_a["determinism"].get("all_deterministic"),
        "experiment_a_summary": {
            "cells_with_analyzable_n_ge_5": sum(
                1 for c in exp_a["cells"] if (c["n_analyzable"] or 0) >= 5),
            "median_compile_rate": float(np.median(
                [c["compile_rate"] for c in exp_a["cells"]])) if exp_a["cells"] else None,
            "median_analyzable_rate": float(np.median(
                [c["analyzable_rate"] for c in exp_a["cells"]])) if exp_a["cells"] else None,
        },
        "experiment_b_summary": {
            "aggregate_wilcoxon_p": exp_b["aggregate_test"].get("wilcoxon_p"),
            "aggregate_delta_tau_median": exp_b["aggregate_test"].get("delta_tau_median"),
            "cells_with_sig_improvement_p05": sum(
                1 for c in exp_b["cells"]
                if c.get("wilcoxon_p") is not None and c["wilcoxon_p"] < 0.05
                and (c.get("delta_tau_median") or 0) > 0),
        },
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    args = ap.parse_args()
    AGGREGATE.mkdir(parents=True, exist_ok=True)
    print("  Building Experiment A...")
    exp_a = build_experiment_a()
    (AGGREGATE / "experiment_a.json").write_text(json.dumps(exp_a, indent=2))
    print("  Building Experiment B...")
    exp_b = build_experiment_b()
    (AGGREGATE / "experiment_b.json").write_text(json.dumps(exp_b, indent=2))
    print("  Building summary...")
    summary = build_summary(exp_a, exp_b)
    (AGGREGATE / "summary.json").write_text(json.dumps(summary, indent=2))
    print(f"\n  Wrote 3 JSON artifacts to {AGGREGATE}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
