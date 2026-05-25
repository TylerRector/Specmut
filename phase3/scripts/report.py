#!/usr/bin/env python3
"""Phase H Stage 5: assemble a static HTML report.

Pulls the aggregate JSON, calls into specmut_viz to render PNG plots, and
emits a single self-contained HTML file at ``aggregate/report.html``.  PNGs
are inlined as base64 — no external assets, no JavaScript.

Sections:
  1. Headline table: human reference vs. each LLM round, per task.
  2. τ comparison chart.
  3. Kill-rate comparison chart.
  4. Refinement-trajectory chart.
  5. Mutant survival breakdown chart.
  6. Compile-vs-τ scatter (the "compile success ≠ semantic strength" plot).
  7. Witness gallery: surviving-mutant witnesses with interpretations.
  8. Per-task drill-down: every analyzed spec's per-theorem table.

The report is intended to be opened in a browser and reviewed end-to-end.
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

from _common import (
    AGGREGATE,
    PHASE3,
    SPECMUT_RESULTS,
    analyzable_reference_path,
    list_models,
    list_tasks,
    reference_path,
)

import specmut_viz


def _img_tag(png_bytes: bytes, *, alt: str) -> str:
    encoded = base64.b64encode(png_bytes).decode("ascii")
    return f'<img src="data:image/png;base64,{encoded}" alt="{html.escape(alt)}" />'


def _load_all_specmut_records() -> list[dict]:
    """Load every per-spec JSON under specmut_results/ as a flat list."""
    out = []
    if not SPECMUT_RESULTS.exists():
        return out
    for f in SPECMUT_RESULTS.rglob("*.json"):
        try:
            out.append(json.loads(f.read_text()))
        except Exception:
            continue
    return out


def _comparison_table(comparison: dict) -> str:
    rows = ['<table class="comparison"><thead><tr>'
            '<th>Task</th><th>Source</th><th>Compile</th><th>τ</th>'
            '<th>Kill rate</th><th>Mutants</th><th>Weak theorems</th><th>Mode</th>'
            '</tr></thead><tbody>']
    for task_block in comparison["tasks"]:
        task = task_block["task"]
        for c in task_block["comparisons"]:
            tau_class = ""
            if c["tau"] >= 0.7:
                tau_class = "strong"
            elif c["tau"] < 0.3:
                tau_class = "weak"
            compile_marker = "✓" if c["compile_success"] else "✗"
            rows.append(
                f'<tr><td>{html.escape(task)}</td>'
                f'<td>{html.escape(c["source"])}</td>'
                f'<td class="ctr">{compile_marker}</td>'
                f'<td class="num {tau_class}">{c["tau"]:.3f}</td>'
                f'<td class="num">{c["kill_rate"]:.3f}</td>'
                f'<td class="num">{c["total_mutants"]}</td>'
                f'<td class="num">{c["weak_theorems"]}</td>'
                f'<td>{html.escape(c["analysis_mode"])}</td></tr>'
            )
    rows.append("</tbody></table>")
    return "\n".join(rows)


def _per_theorem_drilldown(records: list[dict]) -> str:
    """For every spec, render its per-theorem table (sliced mode) or single global row."""
    by_task: dict[str, list[dict]] = {}
    for r in records:
        by_task.setdefault(r["task"], []).append(r)
    out = []
    for task in sorted(by_task):
        out.append(f'<details class="task-drill"><summary>{html.escape(task)}</summary>')
        for r in sorted(by_task[task], key=lambda x: (x["model"], x.get("version", 0))):
            label = "human reference" if r["model"] == "human" else f'{r["model"]}/v{r["version"]}'
            out.append(f'<div class="spec-block"><h4>{html.escape(label)} — '
                       f'τ={r["average_tau"]:.3f}, mode={html.escape(r["analysis_mode"])}</h4>')
            if r["analysis_mode"] == "failed":
                err = r.get("specmut_error", "(unknown error)")
                out.append(f'<p class="error">specmut error: {html.escape(err)}</p>')
                out.append('</div>')
                continue
            if not r["per_theorem"]:
                out.append('<p><em>No per-theorem data.</em></p></div>')
                continue
            out.append('<table class="per-theorem"><thead><tr>'
                       '<th>Theorem</th><th>τ</th><th>Kill rate</th>'
                       '<th>Surviving</th><th>Total mutants</th><th>Contribution</th>'
                       '</tr></thead><tbody>')
            for pt in r["per_theorem"]:
                tau_val = pt.get("tau")
                tau_str = f"{tau_val:.3f}" if isinstance(tau_val, (int, float)) else "—"
                kr_val = pt.get("kill_rate")
                kr_str = f"{kr_val:.3f}" if isinstance(kr_val, (int, float)) else "—"
                out.append(
                    f'<tr><td><code>{html.escape(pt["name"])}</code></td>'
                    f'<td class="num">{tau_str}</td>'
                    f'<td class="num">{kr_str}</td>'
                    f'<td class="num">{pt.get("surviving_mutants","—")}</td>'
                    f'<td class="num">{pt.get("total_mutants","—")}</td>'
                    f'<td>{html.escape(str(pt.get("contribution","None")))}</td></tr>'
                )
            out.append('</tbody></table></div>')
        out.append('</details>')
    return "\n".join(out)


CSS = """
body { font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", Helvetica, Arial, sans-serif;
       max-width: 1100px; margin: 1.5em auto; padding: 0 1em; color: #222; }
.note { color: #666; font-size: 0.92em; }
table.provenance th, table.provenance td { font-size: 0.88em; }
table.provenance a { color: #2952a3; text-decoration: none; }
table.provenance a:hover { text-decoration: underline; }
h1 { border-bottom: 2px solid #2c7a4d; padding-bottom: 0.3em; }
h2 { border-bottom: 1px solid #ccc; padding-bottom: 0.2em; margin-top: 2em; }
h3 { color: #555; }
table { border-collapse: collapse; margin: 0.8em 0; width: 100%; font-size: 0.92em; }
th, td { border: 1px solid #ddd; padding: 4px 8px; text-align: left; }
th { background: #f4f4f4; }
.num { text-align: right; font-variant-numeric: tabular-nums; }
.ctr { text-align: center; }
.weak { color: #c64a3e; font-weight: 600; }
.strong { color: #2c7a4d; font-weight: 600; }
img { max-width: 100%; display: block; margin: 1em 0; border: 1px solid #eee; }
details.task-drill > summary { font-weight: 600; cursor: pointer; padding: 0.4em 0;
                               border-top: 1px solid #ddd; }
details.task-drill > summary:hover { background: #fafafa; }
.spec-block { margin: 0.6em 0 1.2em 1em; }
.spec-block h4 { margin: 0.4em 0 0.3em 0; font-family: monospace; font-size: 0.95em; }
.error { color: #c64a3e; font-family: monospace; }
.kpi { display: inline-block; padding: 0.6em 1em; margin: 0.4em 0.6em 0.4em 0;
       border-left: 3px solid #2c7a4d; background: #f6fbf8; min-width: 140px; }
.kpi-label { font-size: 0.85em; color: #555; }
.kpi-val { font-size: 1.5em; font-weight: 600; color: #2c7a4d; }
"""


def _kpi_block(comparison: dict, records: list[dict]) -> str:
    n_specs = sum(1 for r in records if r["model"] != "human")
    n_human = sum(1 for r in records if r["model"] == "human")
    n_failed = sum(1 for r in records if r["analysis_mode"] == "failed")
    n_compile_ok = 0
    n_compile_total = 0
    for t in comparison["tasks"]:
        for c in t["comparisons"]:
            if c["source"] == "human_reference":
                continue
            n_compile_total += 1
            if c["compile_success"]:
                n_compile_ok += 1
    weak_count = sum(
        1 for t in comparison["tasks"] for c in t["comparisons"]
        if c["source"] != "human_reference" and c["tau"] < 0.3
    )
    return f"""
<div>
  <span class="kpi"><div class="kpi-label">LLM specs analyzed</div>
    <div class="kpi-val">{n_specs}</div></span>
  <span class="kpi"><div class="kpi-label">Human references</div>
    <div class="kpi-val">{n_human}</div></span>
  <span class="kpi"><div class="kpi-label">Compile pass (LLM)</div>
    <div class="kpi-val">{n_compile_ok}/{n_compile_total}</div></span>
  <span class="kpi"><div class="kpi-label">Weak (τ&lt;0.3)</div>
    <div class="kpi-val">{weak_count}/{n_compile_total}</div></span>
  <span class="kpi"><div class="kpi-label">specmut failures</div>
    <div class="kpi-val">{n_failed}</div></span>
</div>
"""


def _provenance_section(summary: dict) -> str:
    """Render the provenance table — one row per task with source URL, commit,
    license, and the LOC / compile / analyze status of both the verbatim
    reference and its reduce.py projection.
    """
    rows = ['<table class="provenance"><thead><tr>'
            '<th>Task</th>'
            '<th>Source (GitHub)</th>'
            '<th>Commit</th>'
            '<th>License</th>'
            '<th>Ref&nbsp;LOC</th>'
            '<th>Proj&nbsp;LOC</th>'
            '<th>Ref&nbsp;compile</th>'
            '<th>Proj&nbsp;compile</th>'
            '<th>Proj&nbsp;analyzable?</th>'
            '</tr></thead><tbody>']
    for task, block in summary.get("human_reference", {}).items():
        prov = block.get("provenance") or {}
        src_url = prov.get("source_url", "—")
        src_label = prov.get("source_path", "—")
        commit = prov.get("commit_sha", "—")
        commit_short = (commit[:8] if commit and commit != "—" else "—")
        license_ = prov.get("license", "—")
        ref_loc = block.get("reference_loc", "—")
        ana_loc = block.get("analyzable_loc", "—")
        ref_ok = "✓" if block.get("reference_compile_success") else "✗"
        ana_ok = "✓" if block.get("analyzable_compile_success") else "✗"
        analyze_status = "✓ (τ=%.3f)" % (block.get("tau") or 0.0) if (
            block.get("analysis_mode") not in (None, "failed", "missing")
        ) else "✗ exceeds bounds"
        src_link = (
            f'<a href="{html.escape(src_url)}" target="_blank">{html.escape(src_label)}</a>'
            if src_url and src_url != "—" else "—"
        )
        rows.append(
            f'<tr><td><code>{html.escape(task)}</code></td>'
            f'<td>{src_link}</td>'
            f'<td><code>{html.escape(commit_short)}</code></td>'
            f'<td>{html.escape(license_)}</td>'
            f'<td class="num">{ref_loc}</td>'
            f'<td class="num">{ana_loc}</td>'
            f'<td class="ctr">{ref_ok}</td>'
            f'<td class="ctr">{ana_ok}</td>'
            f'<td>{html.escape(analyze_status)}</td></tr>'
        )
    rows.append("</tbody></table>")
    note = (
        '<p class="note"><em>The verbatim reference is the canonical artifact '
        'from the upstream repository.  ``reduce.py`` derives a smaller '
        '<code>reference_analyzable.lean</code> that strips proof bodies, '
        'attributes, macros, and dependency closures of dropped helpers so '
        "specmut's bounded analysis at n=2 can attempt translation.  When "
        'the projection exceeds bounds even after reduction, that is itself a '
        "Phase H finding — current specmut cannot analyze idiomatic real-world "
        'Lean specs without further tightening of the analyzable subset.</em></p>'
    )
    return "\n".join(rows) + note


def build_report() -> str:
    comparison = json.loads((AGGREGATE / "comparison.json").read_text())
    progression = json.loads((AGGREGATE / "progression.json").read_text())
    summary = json.loads((AGGREGATE / "summary.json").read_text())
    records = _load_all_specmut_records()

    img_tau = _img_tag(specmut_viz.render_tau_comparison(comparison), alt="τ comparison")
    img_kill = _img_tag(specmut_viz.render_kill_rate_comparison(comparison), alt="kill rate")
    img_prog = _img_tag(specmut_viz.render_progression(progression), alt="refinement")
    img_surv = _img_tag(specmut_viz.render_survival(comparison), alt="survival")
    img_cvt = _img_tag(specmut_viz.render_compile_vs_tau(comparison), alt="compile vs τ")

    witnesses_html = specmut_viz.render_all_witnesses(records)

    now = datetime.datetime.now().strftime("%Y-%m-%d %H:%M")
    body = f"""<!DOCTYPE html><html><head><meta charset="utf-8"/>
<title>Phase H — Semantic Adequacy Demonstration</title>
<style>{CSS}{specmut_viz.WITNESS_CSS}</style>
</head><body>

<h1>Phase H — Semantic Adequacy Demonstration</h1>
<p><em>Generated {now}. specmut Phase H: comparing human-written (real GitHub
sourced) vs. LLM-generated Lean 4 specifications under tightness analysis.</em></p>

<h2>Headline metrics</h2>
{_kpi_block(comparison, records)}

<h2>Human-reference provenance</h2>
{_provenance_section(summary)}

<h2>Tightness (τ): human reference vs. LLM</h2>
<p>Each task's τ scores are grouped by source.  The green bar is the human
reference; LLM bars are colored by refinement round (v1 red, v2 yellow, v3 blue).
The horizontal dashed line marks the weak-spec threshold (τ&lt;0.3).</p>
{img_tau}

<h2>Kill rate: human reference vs. LLM</h2>
<p>Kill rate is the fraction of mutants the specification rejects.  Round-1
specs typically declare a function with no theorems — there are no mutants
to kill, so the bar is empty.</p>
{img_kill}

<h2>Refinement trajectory</h2>
<p>τ over rounds, per (task, model).  This is the headline Phase H claim:
specmut diagnostics fed back into the prompt produce measurable semantic
strengthening, weak (round 1) → strong (round 3).</p>
{img_prog}

<h2>Mutant survival breakdown</h2>
<p>Stacked bars: killed (green) vs. surviving (red).  Note that some round-2
specs produce <em>high</em> kill rate but a <em>tiny</em> mutant pool — high τ
on a small denominator can be misleading.  Compare absolute kill counts.</p>
{img_surv}

<h2>Compile success does not imply tightness</h2>
<p>Every point is one LLM-generated spec.  Compile-pass clusters span the full
τ range, demonstrating the core Phase H argument: kernel acceptance is
necessary but not sufficient evidence of specification quality.</p>
{img_cvt}

<h2>Headline comparison table</h2>
{_comparison_table(comparison)}

<h2>Surviving-mutant witnesses</h2>
<p>For each surviving mutant, specmut's Phase F infrastructure can attach a
minimal distinguishing model showing what the spec failed to constrain.</p>
{witnesses_html}

<h2>Per-task drill-down</h2>
{_per_theorem_drilldown(records)}

</body></html>"""
    return body


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("-o", "--output", type=Path, default=AGGREGATE / "report.html")
    args = ap.parse_args()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    html_text = build_report()
    args.output.write_text(html_text)
    print(f"Wrote {args.output} ({len(html_text):,} bytes)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
