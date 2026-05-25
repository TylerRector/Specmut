#!/usr/bin/env python3
"""Phase 4 — one-shot read-only summary of the specmut-informed repair pilot.

Reads phase4/aggregate/experiment_b.json (produced by aggregate.py) and
prints a compact per-task table:

  task | baseline median tau | repaired median tau | delta median |
  +delta / -delta / =delta | repair_no_change | repair_template_rejected

No Ollama / Lean / specmut.  Pure read of the aggregate artifact.

Usage:
  python3 phase4/scripts/analyze_specmut_feedback.py
  python3 phase4/scripts/analyze_specmut_feedback.py --json
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from _common import AGGREGATE


def _fmt(x) -> str:
    return "  n/a" if x is None else f"{x:6.3f}"


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--exp-b", type=Path,
                    default=AGGREGATE / "experiment_b.json")
    ap.add_argument("--json", action="store_true")
    args = ap.parse_args()

    if not args.exp_b.exists():
        sys.exit(f"{args.exp_b} not found — run aggregate.py first "
                 f"(or the full pipeline).")
    data = json.loads(args.exp_b.read_text())
    cells = data.get("cells", [])

    import statistics as _stats
    _EPS = 1e-9
    COMPLIANCE_THRESHOLD = 0.8

    def _delta_stats(c: dict) -> dict:
        """Δτ median + sign counts.  Prefers the explicit all-repairs view;
        falls back to legacy keys; recomputes from the raw value list when the
        stored stats are absent or were zeroed by the old `len(both) >= 5`
        bug.  (Counts are recomputed, never silently trusted, when the value
        list is present.)
        """
        vals = (c.get("paired_delta_tau_values_all_repairs")
                or c.get("paired_delta_tau_values") or [])
        med = c.get("delta_tau_median_all_repairs", c.get("delta_tau_median"))
        pos = c.get("positive_delta_count_all_repairs", c.get("positive_delta_count"))
        neg = c.get("negative_delta_count_all_repairs", c.get("negative_delta_count"))
        zero = c.get("zero_delta_count_all_repairs", c.get("zero_delta_count"))
        zeroed = (pos in (0, None) and neg in (0, None) and zero in (0, None))
        if vals and (med is None or zeroed):
            med = float(_stats.median(vals))
            pos = sum(1 for d in vals if d > _EPS)
            neg = sum(1 for d in vals if d < -_EPS)
            zero = sum(1 for d in vals if abs(d) <= _EPS)
        return {"median": med, "pos": pos or 0, "neg": neg or 0,
                "zero": zero or 0}

    def _compliance(c: dict) -> dict:
        """valid_rate + status counts, tolerant of stale aggregates."""
        bd = c.get("repair_template_breakdown") or {}
        ok = c.get("repair_template_ok_count", bd.get("repair_template_ok", 0)) or 0
        missing = c.get("repair_required_theorem_missing_count",
                        bd.get("repair_required_theorem_missing", 0)) or 0
        too_many = c.get("repair_too_many_theorems_count",
                         bd.get("repair_too_many_theorems", 0)) or 0
        n_rep = c.get("n_repairs") or (sum(bd.values()) if bd else None)
        invalid = c.get("repair_invalid_count")
        if invalid is None and n_rep is not None:
            invalid = n_rep - ok
        rate = c.get("valid_repair_rate")
        if rate is None and n_rep:
            rate = ok / n_rep
        return {"ok": ok, "invalid": invalid or 0, "missing": missing,
                "too_many": too_many, "valid_rate": rate,
                "no_change": c.get("repair_no_change_count", 0) or 0}

    rows = []
    for c in cells:
        ds = _delta_stats(c)
        comp = _compliance(c)
        rows.append({
            "model": c.get("model"), "task": c.get("task"),
            "n_pairs": (c.get("n_pairs_all_repairs")
                        or c.get("n_pairs") or c.get("n_pairs_both_analyzable")),
            "valid_rate": comp["valid_rate"],
            "baseline_tau_median": c.get("baseline_tau_median"),
            "repaired_tau_median": c.get("repaired_tau_median"),
            "delta_tau_median": ds["median"],
            "positive_delta_count": ds["pos"],
            "negative_delta_count": ds["neg"],
            "zero_delta_count": ds["zero"],
            "ok": comp["ok"], "invalid": comp["invalid"],
            "missing": comp["missing"], "too_many": comp["too_many"],
            "no_change": comp["no_change"],
            "wilcoxon_p": c.get("wilcoxon_p"),
            # template-ok-only view (when present)
            "delta_tau_median_template_ok": c.get("delta_tau_median_template_ok"),
            "n_pairs_template_ok": c.get("n_pairs_template_ok"),
        })

    if args.json:
        print(json.dumps({
            "rows": rows,
            "repair_template_summary": data.get("repair_template_summary", {}),
            "aggregate_test": data.get("aggregate_test", {}),
        }, indent=2))
        return 0

    def _rate(x) -> str:
        return "  n/a" if x is None else f"{x:5.2f}"

    print()
    print("Phase 4 — specmut-informed constrained repair pilot (compliance-gated)")
    print("=" * 116)
    hdr = (f"{'task':<13} {'n':>3} {'valid':>6} {'base_tau':>9} {'rep_tau':>9} "
           f"{'d_tau':>8} {'+':>3} {'-':>3} {'=':>3} "
           f"{'ok':>3} {'inval':>6} {'miss':>5} {'tooMany':>8} {'noChg':>6} "
           f"{'wilcox_p':>9}")
    print(hdr)
    print("-" * 116)
    for r in rows:
        print(f"{r['task']:<13} {str(r['n_pairs'] or 0):>3} "
              f"{_rate(r['valid_rate'])} "
              f"{_fmt(r['baseline_tau_median'])} {_fmt(r['repaired_tau_median'])} "
              f"{_fmt(r['delta_tau_median'])} "
              f"{r['positive_delta_count']:>3} {r['negative_delta_count']:>3} "
              f"{r['zero_delta_count']:>3} "
              f"{r['ok']:>3} {r['invalid']:>6} {r['missing']:>5} "
              f"{r['too_many']:>8} {r['no_change']:>6} "
              f"{_fmt(r['wilcoxon_p'])}")
    print("-" * 116)
    print("  cols: valid=valid_repair_rate, ok/inval/miss/tooMany/noChg = "
          "repair_template status counts; d_tau over ALL both-analyzable pairs.")

    # Repair-template status totals.
    summ = data.get("repair_template_summary", {})
    print("\nRepair-template status totals (all cells):")
    if summ:
        for k, v in summ.items():
            if isinstance(v, int) and v:
                print(f"  {k:<38} {v}")
    else:
        agg_counts: dict = {}
        for r in rows:
            for k in ("ok", "invalid", "missing", "too_many", "no_change"):
                agg_counts[k] = agg_counts.get(k, 0) + (r[k] or 0)
        for k, v in agg_counts.items():
            print(f"  {k:<38} {v}")

    pos_tasks = [r["task"] for r in rows
                 if r["delta_tau_median"] is not None
                 and r["delta_tau_median"] > _EPS]
    print(f"\nTasks with positive median delta tau: "
          f"{', '.join(pos_tasks) if pos_tasks else '(none)'}")

    pass_tasks = [r["task"] for r in rows
                  if r["valid_rate"] is not None
                  and r["valid_rate"] >= COMPLIANCE_THRESHOLD]
    print(f"Tasks passing compliance (valid_repair_rate >= "
          f"{COMPLIANCE_THRESHOLD:.1f}): "
          f"{', '.join(pass_tasks) if pass_tasks else '(none)'}")

    # Warnings.
    warns = []
    for r in rows:
        if r["valid_rate"] is not None and r["valid_rate"] < COMPLIANCE_THRESHOLD:
            warns.append(f"{r['task']}: valid_repair_rate="
                         f"{r['valid_rate']:.2f} < {COMPLIANCE_THRESHOLD}")
        if r["missing"]:
            warns.append(f"{r['task']}: {r['missing']} repair_required_theorem_missing")
        if r["too_many"]:
            warns.append(f"{r['task']}: {r['too_many']} repair_too_many_theorems")
    if warns:
        print("\n  ** COMPLIANCE WARNINGS **")
        for w in warns:
            print(f"     WARN  {w}")

    agg = data.get("aggregate_test", {})
    if agg:
        print(f"\nAggregate paired test (all repairs): n_pairs={agg.get('n_pairs')}, "
              f"delta_median={agg.get('delta_tau_median')}, "
              f"wilcoxon_p={agg.get('wilcoxon_p')}")
    print()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
