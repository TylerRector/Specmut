"""Attrition diagram for Phase 4 — outcome counts as a Sankey-like flow.

Implemented as a stacked horizontal bar by stage rather than a full Sankey to
avoid pulling in extra dependencies.  The visual point is: how many of the
N_generated artifacts reached each milestone.
"""

from __future__ import annotations

import io

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np


def render_attrition_overview(exp_a: dict, exp_b: dict | None = None, *,
                              width: float = 9.0, height: float = 4.0) -> bytes:
    """Single horizontal bar per stage showing how many specs made it."""
    cells = exp_a.get("cells", [])
    n_total = sum(c.get("n_generated", 0) for c in cells)
    n_records = sum(c.get("n_records", 0) for c in cells)
    n_compiled = sum(c.get("n_compiled", 0) for c in cells)
    n_analyzable = sum(c.get("n_analyzable", 0) for c in cells)
    n_pairs_compiled = 0
    n_pairs_analyzable = 0
    if exp_b is not None:
        n_pairs_compiled = sum(c.get("n_pairs_both_compiled", 0)
                               for c in exp_b.get("cells", []))
        n_pairs_analyzable = sum(c.get("n_pairs_both_analyzable", 0)
                                 for c in exp_b.get("cells", []))

    labels = [
        "Baseline: generated",
        "Baseline: compiled",
        "Baseline: analyzable",
    ]
    values = [n_total, n_compiled, n_analyzable]
    colors = ["#3a7cc0", "#2c7a4d", "#dba03b"]
    if exp_b is not None:
        labels += ["Paired: both compiled", "Paired: both analyzable"]
        values += [n_pairs_compiled, n_pairs_analyzable]
        colors += ["#9b3edc", "#c64a3e"]

    fig, ax = plt.subplots(figsize=(width, height))
    y = np.arange(len(labels))
    ax.barh(y, values, color=colors, edgecolor="black", linewidth=0.4)
    for i, v in enumerate(values):
        ax.text(v + max(values) * 0.01, i, str(v), va="center", fontsize=9)
    ax.set_yticks(y)
    ax.set_yticklabels(labels, fontsize=9)
    ax.invert_yaxis()
    ax.set_xlabel("Count")
    ax.set_title("Phase 4 attrition: from generation to analyzable pair")
    fig.tight_layout()
    buf = io.BytesIO()
    fig.savefig(buf, format="png", dpi=120)
    plt.close(fig)
    return buf.getvalue()
