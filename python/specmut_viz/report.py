"""HTML report generation."""

from __future__ import annotations

import argparse
import json
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, Optional

import jinja2

from .dependency_graph import render_dependency_svg
from .hasse import render_hasse_svg


_TEMPLATE = r"""<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<title>specmut — Tightness Report</title>
<style>
body { font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", sans-serif;
       max-width: 900px; margin: 2em auto; padding: 0 1em; color: #2c3e50; }
h1 { border-bottom: 2px solid #2c3e50; padding-bottom: 0.3em; }
h2 { margin-top: 2em; }
section { margin-bottom: 2em; }
.score { font-size: 3em; font-weight: 700; margin: 0.2em 0; }
.score.high { color: #27ae60; }
.score.mid  { color: #f39c12; }
.score.low  { color: #e74c3c; }
table { border-collapse: collapse; width: 100%; }
th, td { padding: 8px 12px; border: 1px solid #ddd; text-align: left; }
th { background: #2c3e50; color: white; }
tr:nth-child(even) td { background: #f9f9f9; }
.killed { color: #27ae60; font-weight: 600; }
.alive  { color: #e74c3c; font-weight: 600; }
.equivalent { color: #95a5a6; }
.note { background: #fff3cd; border-left: 4px solid #f39c12; padding: 0.5em 1em; }
.svg-container { text-align: center; margin: 2em 0; }
.svg-container svg { max-width: 100%; height: auto; }
code { font-family: ui-monospace, Menlo, monospace; }
footer { border-top: 1px solid #ddd; margin-top: 3em; padding-top: 1em;
         color: #95a5a6; font-size: 0.9em; }
</style>
</head>
<body>
<h1>specmut — Specification Tightness Report</h1>

<section>
  <h2>Summary</h2>
  <p class="score {{ score_class }}">τ = {{ "%.3f"|format(tightness.score) }}</p>
  <p>Confidence interval: [{{ "%.3f"|format(tightness.confidence_interval[0]) }}, {{ "%.3f"|format(tightness.confidence_interval[1]) }}]</p>
  <p>{{ tightness.killed }}/{{ tightness.neighborhood_size }} mutants killed,
     {{ tightness.alive }} alive in the ε &lt; {{ parameters.epsilon }} neighborhood.</p>
  {% if smt_fallback_count and smt_fallback_count > 0 %}
  <p class="note">Z3 returned <code>Unknown</code> on {{ smt_fallback_count }} queries; model enumeration was used as fallback.</p>
  {% endif %}
</section>

<section>
  <h2>Parameters</h2>
  <table>
    <tr><th>Spec file</th><td><code>{{ spec_file }}</code></td></tr>
    <tr><th>Model bound</th><td>{{ parameters.model_bound }}</td></tr>
    <tr><th>Quantifier rank</th><td>{{ parameters.quantifier_rank }}</td></tr>
    <tr><th>Epsilon</th><td>{{ parameters.epsilon }}</td></tr>
    <tr><th>Seed</th><td>{{ parameters.seed }}</td></tr>
    <tr><th>Models enumerated</th><td>{{ parameters.models_enumerated }}</td></tr>
    <tr><th>Evaluator</th><td>{{ evaluator }}</td></tr>
    {% if smt %}
    <tr><th>Entailment</th><td>Z3 SMT (hybrid)</td></tr>
    {% else %}
    <tr><th>Entailment</th><td>Model enumeration</td></tr>
    {% endif %}
  </table>
</section>

<section>
  <h2>Signature</h2>
  <table>
    <tr><th>Sorts</th><td>{{ signature.sorts|join(", ") }}</td></tr>
    {% if signature.relations %}
    <tr><th>Relations</th><td>
      {% for r in signature.relations -%}
        <code>{{ r.name }}({{ r.arity|join(", ") }})</code>{{ ", " if not loop.last else "" }}
      {%- endfor %}
    </td></tr>
    {% endif %}
    {% if signature.functions %}
    <tr><th>Functions</th><td>
      {% for f in signature.functions -%}
        <code>{{ f.name }}({{ f.domain|join(", ") }}) → {{ f.codomain }}</code>{{ ", " if not loop.last else "" }}
      {%- endfor %}
    </td></tr>
    {% endif %}
  </table>
</section>

<section>
  <h2>Decomposition</h2>
  <ol>
    {% for d in decomposition %}
    <li><code>{{ d.formula }}</code></li>
    {% endfor %}
  </ol>
</section>

{% if hasse_svg %}
<section>
  <h2>Hasse diagram</h2>
  <div class="svg-container">{{ hasse_svg|safe }}</div>
</section>
{% endif %}

{% if dependency_svg %}
<section>
  <h2>Component dependency / status graph</h2>
  <div class="svg-container">{{ dependency_svg|safe }}</div>
</section>
{% endif %}

{% if alive_mutants %}
<section>
  <h2>Alive mutants</h2>
  <table>
    <tr><th>Index</th><th>Class</th><th>Component</th><th>Distance</th><th>Detail</th></tr>
    {% for m in alive_mutants %}
    <tr>
      <td>{{ m.index }}</td>
      <td>{{ m.class }}</td>
      <td>{{ m.perturbed_component }}</td>
      <td>{{ "%.3f"|format(m.distance) }}</td>
      <td><code>{{ m.formula_summary }}</code></td>
    </tr>
    {% endfor %}
  </table>
</section>
{% endif %}

<section>
  <h2>Timing</h2>
  <table>
    <tr><th>Parse</th><td>{{ timing.parse_ms }} ms</td></tr>
    <tr><th>Enumeration</th><td>{{ timing.enumeration_ms }} ms</td></tr>
    <tr><th>Mutation</th><td>{{ timing.mutation_ms }} ms</td></tr>
    <tr><th>Tightness</th><td>{{ timing.tightness_ms }} ms</td></tr>
    <tr><th>Total</th><td>{{ timing.total_ms }} ms</td></tr>
  </table>
</section>

<footer>
  <p>specmut {{ version }} — generated {{ timestamp }}.</p>
</footer>
</body>
</html>
"""


def _score_class(score: float) -> str:
    if score >= 0.8:
        return "high"
    if score >= 0.5:
        return "mid"
    return "low"


def generate_html_report(
    report_json: Dict[str, Any],
    output_path: str | Path,
    *,
    hasse_svg: Optional[str] = None,
    dependency_svg: Optional[str] = None,
) -> str:
    """Generate a self-contained HTML report and return its path.

    ``hasse_svg`` / ``dependency_svg`` are optional inline SVG strings
    (no ``<?xml`` preamble required); embed them directly via the
    ``|safe`` Jinja filter.  Pass ``None`` to skip a section.
    """
    template = jinja2.Environment(
        autoescape=jinja2.select_autoescape(["html"]),
        keep_trailing_newline=True,
    ).from_string(_TEMPLATE)
    score = float(report_json.get("tightness", {}).get("score", 0.0))
    rendered = template.render(
        spec_file=report_json.get("spec_file", "spec"),
        parameters=report_json.get("parameters", {}),
        signature=report_json.get("signature", {}),
        decomposition=report_json.get("decomposition", []),
        tightness=report_json.get("tightness", {}),
        alive_mutants=report_json.get("alive_mutants", []),
        timing=report_json.get("timing", {}),
        evaluator=report_json.get("evaluator", "exhaustive"),
        smt=report_json.get("smt", False),
        smt_fallback_count=report_json.get("smt_fallback_count", 0),
        score_class=_score_class(score),
        hasse_svg=hasse_svg,
        dependency_svg=dependency_svg,
        version=report_json.get("version", "0.1.0"),
        timestamp=datetime.now(timezone.utc).isoformat(timespec="seconds"),
    )
    output_path = Path(output_path)
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(rendered, encoding="utf-8")
    return str(output_path)


def main(argv: Optional[list[str]] = None) -> int:
    """CLI entry point.

    Usage:
        specmut-viz --json report.json -o report.html [--hasse] [--deps]
    """
    parser = argparse.ArgumentParser(
        prog="specmut-viz",
        description="Generate an HTML report from a specmut JSON output file.",
    )
    parser.add_argument(
        "--json",
        required=True,
        type=Path,
        help="Path to the JSON report emitted by `specmut analyze -f json`.",
    )
    parser.add_argument(
        "-o",
        "--output",
        required=True,
        type=Path,
        help="Path to write the HTML report.",
    )
    parser.add_argument(
        "--hasse",
        action="store_true",
        help="Embed the Hasse diagram as inline SVG.",
    )
    parser.add_argument(
        "--deps",
        action="store_true",
        help="Embed the component dependency / status graph as inline SVG.",
    )
    args = parser.parse_args(argv)

    report = json.loads(args.json.read_text(encoding="utf-8"))

    hasse_svg = None
    dependency_svg = None
    if args.hasse:
        try:
            hasse_svg = _strip_xml_prefix(render_hasse_svg(report))
        except Exception as e:  # noqa: BLE001  — render failures are best-effort
            print(f"specmut-viz: Hasse rendering failed: {e}", file=sys.stderr)
    if args.deps:
        try:
            dependency_svg = _strip_xml_prefix(render_dependency_svg(report))
        except Exception as e:  # noqa: BLE001
            print(f"specmut-viz: dependency rendering failed: {e}", file=sys.stderr)

    generate_html_report(
        report,
        args.output,
        hasse_svg=hasse_svg,
        dependency_svg=dependency_svg,
    )
    return 0


def _strip_xml_prefix(svg: str) -> str:
    """Remove the ``<?xml ... ?>`` and ``<!DOCTYPE ... >`` headers so the
    SVG is safe to embed inside HTML."""
    out = svg
    if out.startswith("<?xml"):
        end = out.find("?>")
        if end != -1:
            out = out[end + 2 :].lstrip()
    if out.lower().startswith("<!doctype"):
        end = out.find(">")
        if end != -1:
            out = out[end + 1 :].lstrip()
    return out


if __name__ == "__main__":
    raise SystemExit(main())
