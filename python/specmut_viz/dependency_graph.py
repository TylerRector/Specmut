"""Component dependency / status graph.

The JSON output from the CLI lists alive mutants and the components they
perturb, but does not include enough information to *infer* dependencies
between components without re-running the tightness evaluation.  This
module therefore renders a status-only graph (green = essential, red =
redundant, yellow = partial) and labels itself accordingly.
"""

from __future__ import annotations

from collections import defaultdict
from pathlib import Path
from typing import Any, Dict

import graphviz


_ESSENTIAL_FILL = "#2ecc71"
_REDUNDANT_FILL = "#e74c3c"
_PARTIAL_FILL = "#f1c40f"


def render_dependency_graph(
    report_json: Dict[str, Any],
    output_path: str | Path,
    *,
    format: str = "svg",
) -> str:
    """Render a component-status graph.  Returns the file path."""
    graph = _build_graph(report_json)
    output_path = Path(output_path)
    output_path.parent.mkdir(parents=True, exist_ok=True)
    return graph.render(
        filename=output_path.stem,
        directory=str(output_path.parent),
        cleanup=True,
        format=format,
    )


def render_dependency_svg(report_json: Dict[str, Any]) -> str:
    """Return SVG content directly for inline embedding."""
    graph = _build_graph(report_json)
    return graph.pipe(format="svg").decode("utf-8", errors="replace")


def _classify_components(
    report_json: Dict[str, Any],
) -> Dict[int, str]:
    """For each component index, determine essential / redundant /
    partial based on its weakening mutants' alive/killed status.

    We can derive this from the alive_mutants list and the
    tightness.killed count, but only with partial information: we know
    which weakenings are alive (in the list) and which are killed (the
    delta).  When the JSON lists every weakening as alive we tag the
    component redundant; when none appear alive we tag it essential;
    mixed → partial.
    """
    decomposition = report_json.get("decomposition", [])
    weakening_status: Dict[int, Dict[str, int]] = defaultdict(
        lambda: {"alive": 0, "killed": 0}
    )

    # Alive weakenings are listed in alive_mutants.
    for m in report_json.get("alive_mutants", []):
        if (m.get("class") or "").lower() != "weakening":
            continue
        idx = int(m.get("perturbed_component", 0))
        weakening_status[idx]["alive"] += 1

    # Total weakenings per component come from the mutation by_class
    # data, but the §8.1 schema doesn't expose that directly.  Best we
    # can do is assume there's one weakening per component (one per
    # join-irreducible).  Killed weakenings = max(0, 1 - alive).
    for idx in range(len(decomposition)):
        info = weakening_status[idx]
        total = max(info["alive"], 1)
        info["killed"] = max(0, total - info["alive"])

    out: Dict[int, str] = {}
    for idx in range(len(decomposition)):
        info = weakening_status[idx]
        if info["alive"] == 0:
            out[idx] = "essential"
        elif info["killed"] == 0:
            out[idx] = "redundant"
        else:
            out[idx] = "partial"
    return out


def _build_graph(report_json: Dict[str, Any]) -> graphviz.Digraph:
    statuses = _classify_components(report_json)
    decomposition = report_json.get("decomposition", [])
    graph = graphviz.Digraph("specmut_components")
    graph.attr(rankdir="LR", overlap="false")
    graph.attr("node", fontname="Helvetica", fontsize="10", shape="rectangle", style="rounded,filled")
    for entry in decomposition:
        idx = int(entry.get("index", 0))
        formula = entry.get("formula", "")
        status = statuses.get(idx, "partial")
        fill = {
            "essential": _ESSENTIAL_FILL,
            "redundant": _REDUNDANT_FILL,
            "partial": _PARTIAL_FILL,
        }[status]
        graph.node(
            f"comp_{idx}",
            label=f"[{idx}] {_truncate(formula)}\\nstatus: {status}",
            fillcolor=fill,
        )
    # No dependency edges — we don't have enough JSON to infer them
    # without re-running tightness.  Add a caption node instead.
    graph.attr(label="component status only — dependency inference requires re-evaluation")
    return graph


def _truncate(s: str, limit: int = 40) -> str:
    if len(s) <= limit:
        return s
    return s[: limit - 1] + "…"
