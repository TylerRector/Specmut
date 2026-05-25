"""Hasse-style mutant diagram rendered with graphviz."""

from __future__ import annotations

from pathlib import Path
from typing import Any, Dict

import graphviz


# Node colors per §3.11.  The CSS classes elsewhere keep these in sync.
_CENTER_FILL = "#2c3e50"
_CENTER_FONT = "#ffffff"
_KILLED_FILL = "#2ecc71"
_KILLED_STROKE = "#27ae60"
_ALIVE_FILL = "#e74c3c"
_ALIVE_STROKE = "#c0392b"
_EQUIV_FILL = "#95a5a6"


def render_hasse_diagram(
    report_json: Dict[str, Any],
    output_path: str | Path,
    *,
    format: str = "svg",
) -> str:
    """Render a Hasse-style diagram for the spec and its mutants.

    The center node is the original spec; mutants fan out around it,
    colored by status (killed / alive / equivalent) and ranked by class
    (strengthening above, weakening below, replacement on the sides).

    Returns the path of the rendered file.

    The ``format`` argument is forwarded to graphviz; ``"svg"`` is the
    expected default for embedding in the HTML report.
    """
    output_path = Path(output_path)
    spec_label = _truncate(report_json.get("spec_file", "spec"))
    graph = graphviz.Digraph("specmut_hasse", format=format)
    graph.attr(rankdir="TB", overlap="false", splines="true")
    graph.attr("node", fontname="Helvetica", fontsize="10")
    graph.attr("edge", fontname="Helvetica", fontsize="9")

    # Center node.
    graph.node(
        "center",
        label=f"{spec_label}\\n(original spec)",
        shape="rectangle",
        style="filled,bold",
        peripheries="2",
        fillcolor=_CENTER_FILL,
        fontcolor=_CENTER_FONT,
    )

    killed_indices = {
        m.get("index")
        for m in report_json.get("alive_mutants", [])
        if False
    }
    # The JSON exports only alive mutants; everything else in the
    # mutation neighborhood was killed.  We don't get a per-mutant
    # listing for kills, so we render a bucket node summarizing them.
    tightness = report_json.get("tightness", {})
    killed_count = int(tightness.get("killed", 0))
    alive_mutants = list(report_json.get("alive_mutants", []))

    if killed_count > 0:
        graph.node(
            "killed_bucket",
            label=f"killed mutants\\nn = {killed_count}",
            shape="rectangle",
            style="rounded,filled",
            color=_KILLED_STROKE,
            fillcolor=_KILLED_FILL,
        )
        graph.edge("center", "killed_bucket", style="solid")

    # Alive mutants individually.
    for m in alive_mutants:
        idx = m.get("index", 0)
        cls = m.get("class", "?")
        dist = float(m.get("distance", 0.0))
        node_id = f"alive_{idx}"
        size = 0.8 + min(1.5, dist * 2.0)
        graph.node(
            node_id,
            label=f"#{idx} {cls}\\nd = {dist:.3f}",
            shape="rectangle",
            style="rounded,filled,dashed",
            color=_ALIVE_STROKE,
            fillcolor=_ALIVE_FILL,
            width=f"{size:.2f}",
        )
        # Weight tightens the edge for closer mutants.
        weight = max(1, int(round(10.0 * (1.0 - dist))))
        graph.edge("center", node_id, style="dashed", weight=str(weight))

    _ = killed_indices  # reserved for future per-kill rendering
    output_path.parent.mkdir(parents=True, exist_ok=True)
    rendered = graph.render(
        filename=output_path.stem,
        directory=str(output_path.parent),
        cleanup=True,
        format=format,
    )
    return rendered


def render_hasse_svg(report_json: Dict[str, Any]) -> str:
    """Return an SVG string without writing to disk.

    Convenience wrapper used by ``report.generate_html_report`` when it
    wants to embed the diagram inline.
    """
    graph = _build_graph(report_json)
    return graph.pipe(format="svg").decode("utf-8", errors="replace")


def _build_graph(report_json: Dict[str, Any]) -> graphviz.Digraph:
    """Internal: same logic as ``render_hasse_diagram`` but returns the
    Digraph rather than calling render()."""
    spec_label = _truncate(report_json.get("spec_file", "spec"))
    graph = graphviz.Digraph("specmut_hasse")
    graph.attr(rankdir="TB", overlap="false", splines="true")
    graph.attr("node", fontname="Helvetica", fontsize="10")
    graph.attr("edge", fontname="Helvetica", fontsize="9")
    graph.node(
        "center",
        label=f"{spec_label}\\n(original spec)",
        shape="rectangle",
        style="filled,bold",
        peripheries="2",
        fillcolor=_CENTER_FILL,
        fontcolor=_CENTER_FONT,
    )
    tightness = report_json.get("tightness", {})
    killed_count = int(tightness.get("killed", 0))
    if killed_count > 0:
        graph.node(
            "killed_bucket",
            label=f"killed mutants\\nn = {killed_count}",
            shape="rectangle",
            style="rounded,filled",
            color=_KILLED_STROKE,
            fillcolor=_KILLED_FILL,
        )
        graph.edge("center", "killed_bucket", style="solid")
    for m in report_json.get("alive_mutants", []):
        idx = m.get("index", 0)
        cls = m.get("class", "?")
        dist = float(m.get("distance", 0.0))
        node_id = f"alive_{idx}"
        size = 0.8 + min(1.5, dist * 2.0)
        graph.node(
            node_id,
            label=f"#{idx} {cls}\\nd = {dist:.3f}",
            shape="rectangle",
            style="rounded,filled,dashed",
            color=_ALIVE_STROKE,
            fillcolor=_ALIVE_FILL,
            width=f"{size:.2f}",
        )
        weight = max(1, int(round(10.0 * (1.0 - dist))))
        graph.edge("center", node_id, style="dashed", weight=str(weight))
    return graph


def _truncate(s: str, limit: int = 32) -> str:
    if len(s) <= limit:
        return s
    return s[: limit - 1] + "…"
