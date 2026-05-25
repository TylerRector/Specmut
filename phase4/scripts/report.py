#!/usr/bin/env python3
"""Phase 4 Stage 10: HTML report assembly.

Reads aggregate/{experiment_a,experiment_b,summary}.json and renders a
single self-contained HTML file with PNG plots inlined as base64 and the
statistical tables as plain HTML.

Sections:
  1. Pre-registration block (frozen config + benchmark gate log).
  2. Determinism panel.
  3. KPI strip (counts at each pipeline stage).
  4. Attrition overview.
  5. Experiment A: distributions, control separation, attrition flow,
     model comparison, statistical tables, cross-model tests.
  6. Experiment B: paired trajectories, Δτ histogram, refinement summary,
     compile-rate change, outcome pie, per-cell statistical tables.
  7. Interpretation block (auto-generated narrative based on results).
"""

from __future__ import annotations

import argparse
import base64
import datetime
import html
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
sys.path.insert(0, str(Path(__file__).resolve().parent.parent.parent / "python"))

from _common import AGGREGATE, BENCHMARKS, CONFIG_PATH, PHASE4

import specmut_viz


def _img(png: bytes, alt: str) -> str:
    if not png:
        return f"<p><em>(plot empty: {html.escape(alt)})</em></p>"
    return (f'<img src="data:image/png;base64,{base64.b64encode(png).decode("ascii")}"'
            f' alt="{html.escape(alt)}" />')


def _kpi(exp_a: dict, exp_b: dict, summary: dict) -> str:
    cells = exp_a.get("cells", [])
    n_gen = sum(c.get("n_generated", 0) for c in cells)
    n_compiled = sum(c.get("n_compiled", 0) for c in cells)
    n_analyzable = sum(c.get("n_analyzable", 0) for c in cells)
    n_pairs_analyzable = sum(c.get("n_pairs_both_analyzable", 0)
                             for c in exp_b.get("cells", []))
    agg_p = (exp_b.get("aggregate_test") or {}).get("wilcoxon_p")
    agg_dt = (exp_b.get("aggregate_test") or {}).get("delta_tau_median")
    return f"""
<div class="kpis">
  <div class="kpi"><div class="kpi-label">Baseline generations</div>
    <div class="kpi-val">{n_gen}</div></div>
  <div class="kpi"><div class="kpi-label">Compiled</div>
    <div class="kpi-val">{n_compiled}</div></div>
  <div class="kpi"><div class="kpi-label">Analyzable</div>
    <div class="kpi-val">{n_analyzable}</div></div>
  <div class="kpi"><div class="kpi-label">Paired analyzable</div>
    <div class="kpi-val">{n_pairs_analyzable}</div></div>
  <div class="kpi"><div class="kpi-label">Aggregate Wilcoxon p</div>
    <div class="kpi-val">{agg_p if agg_p is None else f"{agg_p:.4f}"}</div></div>
  <div class="kpi"><div class="kpi-label">Aggregate Δτ med</div>
    <div class="kpi-val">{agg_dt if agg_dt is None else f"{agg_dt:+.3f}"}</div></div>
</div>"""


def _pre_registration(prereg_path: Path) -> str:
    if not prereg_path.exists():
        return "<p><em>(no pre_registration_log.json present)</em></p>"
    d = json.loads(prereg_path.read_text())
    rows = ['<table class="prereg"><thead><tr>'
            '<th>Task</th><th>Reference τ</th><th>Killed/Total</th><th>Status</th>'
            '<th>Notes</th></tr></thead><tbody>']
    for r in d.get("results", []):
        notes = []
        if r.get("replaces"):
            notes.append(f"replaces <code>{html.escape(r['replaces'])}</code>")
        if r.get("replacement_reason"):
            notes.append(html.escape(r["replacement_reason"][:200]))
        rows.append(
            f"<tr><td><code>{html.escape(r['task'])}</code></td>"
            f"<td class='num'>{r.get('reference_tau',0):.3f}</td>"
            f"<td class='num'>{r.get('killed',0)}/{r.get('total',0)}</td>"
            f"<td>{html.escape(r.get('status','—'))}</td>"
            f"<td>{'<br/>'.join(notes)}</td></tr>"
        )
    rows.append("</tbody></table>")
    if d.get("notes"):
        rows.append("<ul>")
        for n in d["notes"]:
            rows.append(f"<li>{html.escape(n)}</li>")
        rows.append("</ul>")
    return "\n".join(rows)


def _interpretation(exp_a: dict, exp_b: dict) -> str:
    """Auto-generated 1-paragraph narrative from the aggregate results."""
    parts = []
    cells_a = exp_a.get("cells", [])
    cells_b = exp_b.get("cells", [])
    # Determinism
    det = exp_a.get("determinism", {}) or {}
    if det.get("all_deterministic") is True:
        parts.append("specmut was determinism-validated on identical inputs.")
    elif det.get("all_deterministic") is False:
        parts.append("specmut FAILED determinism validation — all statistical claims below are tentative.")
    # Compile / analyzability rates
    if cells_a:
        median_compile = sum(c["compile_rate"] for c in cells_a) / len(cells_a)
        median_analyz = sum(c["analyzable_rate"] for c in cells_a) / len(cells_a)
        parts.append(f"Across cells, mean LLM compile rate is "
                     f"{median_compile:.0%}; of compilable specs, "
                     f"{median_analyz:.0%} reached successful analysis.")
    # Negative control separation
    nct = exp_a.get("negative_control_tests", [])
    sig = sum(1 for t in nct if t.get("p_adjusted") is not None and t["p_adjusted"] < 0.05)
    if nct:
        parts.append(f"Negative-control separation tests: {sig}/{len(nct)} cells "
                     f"reject 'LLM τ ≤ trivial τ' at FDR-adjusted p<0.05.")
    # Aggregate Wilcoxon
    agg = exp_b.get("aggregate_test", {}) or {}
    if agg.get("wilcoxon_p") is not None:
        sign = "+" if (agg.get("delta_tau_median") or 0) > 0 else ""
        parts.append(f"Aggregate paired Wilcoxon on Δτ: median {sign}{agg.get('delta_tau_median',0):.3f}, "
                     f"p = {agg['wilcoxon_p']:.4f} (n={agg.get('n_pairs',0)}).")
    # Per-cell sig improvements
    n_sig_imp = sum(1 for c in cells_b
                    if c.get("wilcoxon_p") is not None and c["wilcoxon_p"] < 0.05
                    and (c.get("delta_tau_median") or 0) > 0)
    if cells_b:
        parts.append(f"{n_sig_imp}/{len(cells_b)} (model, task) cells "
                     f"show significant baseline → repaired improvement at p<0.05.")
    return "<p class='narrative'>" + " ".join(parts) + "</p>"


CSS = """
body { font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", Helvetica, Arial, sans-serif;
       max-width: 1200px; margin: 1.5em auto; padding: 0 1em; color: #222; }
h1 { border-bottom: 2px solid #2c7a4d; padding-bottom: 0.3em; }
h2 { border-bottom: 1px solid #ccc; padding-bottom: 0.2em; margin-top: 1.5em; }
h3 { color: #555; }
.kpis { display: flex; flex-wrap: wrap; gap: 0.6em; margin: 0.6em 0 1em 0; }
.kpi { padding: 0.6em 1em; border-left: 3px solid #2c7a4d; background: #f6fbf8; min-width: 140px; }
.kpi-label { font-size: 0.85em; color: #555; }
.kpi-val { font-size: 1.5em; font-weight: 600; color: #2c7a4d; font-variant-numeric: tabular-nums; }
img { max-width: 100%; display: block; margin: 0.8em 0; border: 1px solid #eee; }
table.prereg { border-collapse: collapse; width: 100%; font-size: 0.92em; margin: 0.6em 0; }
table.prereg th, table.prereg td { border: 1px solid #ddd; padding: 4px 8px; vertical-align: top; }
table.prereg th { background: #f4f4f4; }
table.prereg td.num { text-align: right; font-variant-numeric: tabular-nums; }
.narrative { background: #fdfdf6; border-left: 3px solid #dba03b; padding: 0.7em 1em; }
.note { color: #666; font-size: 0.92em; }
"""


def build_report() -> str:
    exp_a = json.loads((AGGREGATE / "experiment_a.json").read_text())
    exp_b = json.loads((AGGREGATE / "experiment_b.json").read_text())
    summary = json.loads((AGGREGATE / "summary.json").read_text())

    images = {
        "tau_dist": specmut_viz.render_tau_distributions(exp_a),
        "compile_vs_sem": specmut_viz.render_compile_vs_semantic(exp_a),
        "attrition_flow": specmut_viz.render_attrition_flow(exp_a),
        "model_comp": specmut_viz.render_model_comparison(exp_a),
        "neg_control": specmut_viz.render_negative_control_separation(exp_a),
        "paired_traj": specmut_viz.render_paired_trajectories(exp_b),
        "delta_hist": specmut_viz.render_delta_tau_distribution(exp_b),
        "refine_summary": specmut_viz.render_refinement_summary(exp_b),
        "compile_change": specmut_viz.render_compile_rate_change(exp_b),
        "outcome_pie": specmut_viz.render_outcome_pie(exp_b),
        "attrition_overview": specmut_viz.render_attrition_overview(exp_a, exp_b),
    }

    cfg_text = CONFIG_PATH.read_text() if CONFIG_PATH.exists() else "(no config.toml)"
    prereg = _pre_registration(BENCHMARKS / "pre_registration_log.json")

    now = datetime.datetime.now().strftime("%Y-%m-%d %H:%M")

    return f"""<!DOCTYPE html><html><head><meta charset="utf-8"/>
<title>Phase 4 — Statistical Evaluation of specmut Semantic Signals</title>
<style>{CSS}{specmut_viz.STATS_CSS}</style>
</head><body>

<h1>Phase 4 — Statistical Evaluation of specmut Semantic Signals</h1>
<p><em>Generated {now}. Pre-registered observational + paired-intervention
study: Experiment A characterizes specmut metrics; Experiment B tests whether
specmut-derived semantic feedback improves LLM output.</em></p>

<h2>Headline metrics</h2>
{_kpi(exp_a, exp_b, summary)}

<h2>Auto-generated interpretation</h2>
{_interpretation(exp_a, exp_b)}

<h2>Pre-registration</h2>
<p>Configuration was frozen before any generation began.  Reference specs
passed the τ &gt; 0 gate at n=2.  Tasks that failed the gate were replaced —
see the notes column below.</p>
{prereg}
<details><summary>Show full <code>config.toml</code></summary>
<pre>{html.escape(cfg_text)}</pre></details>

<h2>Determinism</h2>
{specmut_viz.render_determinism_block(exp_a)}

<h2>Attrition overview</h2>
{_img(images["attrition_overview"], "attrition overview")}

<h1>Experiment A — Analyzer Validation</h1>

<h2>τ distributions per (model, task)</h2>
<p>Violin/box per cell.  Reference (green ◇), partial (yellow ▢) and trivial
(red ✕) controls overlaid for visual separation.</p>
{_img(images["tau_dist"], "tau distributions")}

<h2>Negative-control separation</h2>
{_img(images["neg_control"], "negative control separation")}
<p>Mann-Whitney U (LLM &gt; trivial), FDR-adjusted:</p>
{specmut_viz.render_negative_control_table(exp_a)}

<h2>Per-cell descriptive statistics</h2>
{specmut_viz.render_experiment_a_cells(exp_a)}

<h2>Cross-model comparison</h2>
{_img(images["model_comp"], "cross-model")}
{specmut_viz.render_cross_model_table(exp_a)}

<h2>Attrition per cell</h2>
{_img(images["attrition_flow"], "attrition flow")}

<h2>Compile success vs semantic tightness</h2>
{_img(images["compile_vs_sem"], "compile vs tau")}

<h1>Experiment B — Semantic-Feedback Refinement</h1>

<h2>Paired τ trajectories</h2>
{_img(images["paired_traj"], "paired trajectories")}

<h2>Distribution of Δτ</h2>
{_img(images["delta_hist"], "delta tau histogram")}

<h2>Median τ: baseline vs repaired</h2>
{_img(images["refine_summary"], "refinement summary")}

<h2>Compile rate change</h2>
{_img(images["compile_change"], "compile rate change")}

<h2>Refinement outcomes</h2>
{_img(images["outcome_pie"], "outcome pie")}

<h2>Per-cell paired statistics</h2>
{specmut_viz.render_experiment_b_cells(exp_b)}

</body></html>"""


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("-o", "--output", type=Path, default=AGGREGATE / "report.html")
    args = ap.parse_args()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    text = build_report()
    args.output.write_text(text)
    print(f"  Wrote {args.output} ({len(text):,} bytes)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
