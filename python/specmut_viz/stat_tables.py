"""Aligned HTML tables for Phase 4 statistical outputs."""

from __future__ import annotations

import html
from typing import Iterable


def _fmt(v, *, digits: int = 3) -> str:
    if v is None:
        return "—"
    if isinstance(v, (int,)) and not isinstance(v, bool):
        return str(v)
    if isinstance(v, float):
        if v != v:
            return "NaN"
        return f"{v:.{digits}f}"
    if isinstance(v, list):
        return "[" + ", ".join(_fmt(x, digits=digits) for x in v) + "]"
    return html.escape(str(v))


def render_experiment_a_cells(exp_a: dict) -> str:
    cells = exp_a.get("cells", [])
    rows = ['<table class="stats"><thead><tr>'
            '<th>Model</th><th>Task</th><th>N gen</th><th>Compile rate</th>'
            '<th>Analyzable rate</th><th>τ median</th><th>τ IQR</th>'
            '<th>τ 95% CI (BCa)</th><th>Kill rate (med)</th>'
            '<th>CV(τ)</th><th>Theorem cov.</th>'
            '<th>Runtime med (s)</th></tr></thead><tbody>']
    for c in cells:
        rows.append(
            f"<tr><td>{html.escape(c['model'])}</td>"
            f"<td>{html.escape(c['task'])}</td>"
            f"<td class='num'>{_fmt(c['n_generated'])}</td>"
            f"<td class='num'>{_fmt(c['compile_rate'])}</td>"
            f"<td class='num'>{_fmt(c['analyzable_rate'])}</td>"
            f"<td class='num'>{_fmt(c['tau_median'])}</td>"
            f"<td class='num'>{_fmt(c['tau_iqr'])}</td>"
            f"<td class='num'>{_fmt(c['tau_ci_95'])}</td>"
            f"<td class='num'>{_fmt(c['kill_rate_median'])}</td>"
            f"<td class='num'>{_fmt(c['cv_tau'])}</td>"
            f"<td class='num'>{_fmt(c['theorem_coverage_mean'])}</td>"
            f"<td class='num'>{_fmt(c['runtime_median_sec'])}</td></tr>"
        )
    rows.append("</tbody></table>")
    return "\n".join(rows)


def render_experiment_b_cells(exp_b: dict) -> str:
    cells = exp_b.get("cells", [])
    rows = ['<table class="stats"><thead><tr>'
            '<th>Model</th><th>Task</th><th>Pairs (both analyzable)</th>'
            '<th>Baseline τ med</th><th>Repaired τ med</th><th>Δτ med</th>'
            '<th>Δτ 95% CI</th><th>Wilcoxon p</th><th>p adj (BH)</th>'
            '<th>Effect (r)</th><th>Imp/Reg/Unc</th>'
            '<th>Compile McNemar p</th></tr></thead><tbody>']
    for c in cells:
        rows.append(
            f"<tr><td>{html.escape(c['model'])}</td>"
            f"<td>{html.escape(c['task'])}</td>"
            f"<td class='num'>{_fmt(c['n_pairs_both_analyzable'])}</td>"
            f"<td class='num'>{_fmt(c['baseline_tau_median'])}</td>"
            f"<td class='num'>{_fmt(c['repaired_tau_median'])}</td>"
            f"<td class='num'>{_fmt(c['delta_tau_median'])}</td>"
            f"<td class='num'>{_fmt(c['delta_tau_ci_95'])}</td>"
            f"<td class='num'>{_fmt(c.get('wilcoxon_p'))}</td>"
            f"<td class='num'>{_fmt(c.get('wilcoxon_p_adjusted'))}</td>"
            f"<td class='num'>{_fmt(c.get('effect_size_matched_rank_biserial'))}</td>"
            f"<td class='num'>{c.get('n_improved',0)}/{c.get('n_regressed',0)}/{c.get('n_unchanged',0)}</td>"
            f"<td class='num'>{_fmt(c['compile_mcnemar_p'])}</td></tr>"
        )
    rows.append("</tbody></table>")
    return "\n".join(rows)


def render_negative_control_table(exp_a: dict) -> str:
    tests = exp_a.get("negative_control_tests", [])
    rows = ['<table class="stats"><thead><tr>'
            '<th>Task</th><th>Model</th><th>Comparison</th>'
            '<th>U</th><th>p</th><th>p adj (BH)</th><th>Effect (rank-biserial)</th>'
            '</tr></thead><tbody>']
    for t in tests:
        rows.append(
            f"<tr><td>{html.escape(t['task'])}</td>"
            f"<td>{html.escape(t.get('model','—'))}</td>"
            f"<td>{html.escape(t['comparison'])}</td>"
            f"<td class='num'>{_fmt(t['statistic'])}</td>"
            f"<td class='num'>{_fmt(t['p_value'])}</td>"
            f"<td class='num'>{_fmt(t.get('p_adjusted'))}</td>"
            f"<td class='num'>{_fmt(t.get('effect_size_rank_biserial'))}</td></tr>"
        )
    rows.append("</tbody></table>")
    return "\n".join(rows)


def render_cross_model_table(exp_a: dict) -> str:
    tests = exp_a.get("cross_model_tests", [])
    rows = ['<table class="stats"><thead><tr>'
            '<th>Task</th><th>Test</th><th>N groups</th>'
            '<th>Statistic</th><th>p</th><th>p adj (BH)</th>'
            '</tr></thead><tbody>']
    for t in tests:
        rows.append(
            f"<tr><td>{html.escape(t['task'])}</td>"
            f"<td>{html.escape(t['test'])}</td>"
            f"<td class='num'>{t['n_groups']}</td>"
            f"<td class='num'>{_fmt(t['statistic'])}</td>"
            f"<td class='num'>{_fmt(t['p_value'])}</td>"
            f"<td class='num'>{_fmt(t.get('p_adjusted'))}</td></tr>"
        )
    rows.append("</tbody></table>")
    return "\n".join(rows)


def render_determinism_block(exp_a: dict) -> str:
    d = exp_a.get("determinism", {}) or {}
    status = ("validated" if d.get("all_deterministic") is True
              else "FAILED" if d.get("all_deterministic") is False
              else "not run")
    return (
        f'<div class="det-block">'
        f'<b>Determinism:</b> {html.escape(status)}.  Files tested: '
        f'{d.get("files_tested", "—")} × {d.get("runs_per_file", "—")} runs.'
        f'</div>'
    )


STATS_CSS = """
table.stats { border-collapse: collapse; width: 100%; font-size: 0.85em; margin: 0.7em 0; }
table.stats th, table.stats td { border: 1px solid #ddd; padding: 3px 6px; }
table.stats th { background: #f4f4f4; }
table.stats td.num { text-align: right; font-variant-numeric: tabular-nums; }
.det-block { padding: 0.6em 1em; background: #f6fbf8; border-left: 3px solid #2c7a4d;
             margin: 0.6em 0; font-size: 0.95em; }
"""
