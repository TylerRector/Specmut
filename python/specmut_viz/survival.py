"""Phase H mutant-survival charts (stacked bars).

Each bar shows killed vs surviving mutants per spec.  The shape of the bars
reflects two distinct failure modes:

- Tall bars with mostly red (surviving): rich mutant pool, weak constraints.
- Short bars with green only: trivial spec; mutation generator finds little to
  perturb.  The pipeline records this as a separate failure category.
"""

from __future__ import annotations

import io
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np


KILLED_COLOR = "#2c7a4d"
ALIVE_COLOR = "#c64a3e"


def render_survival(comparison: dict, *,
                    title: str = "Mutant survival per spec",
                    width: float = 10.0,
                    height_per_task: float = 2.0) -> bytes:
    """Per-task stacked bars: killed (green) + surviving (red).

    A spec that produced zero mutants (failed translation or trivial signature)
    renders as an empty bar — visually distinguishing semantic-emptiness from
    actual constraint coverage.
    """
    tasks = comparison["tasks"]
    n = len(tasks)
    fig, axes = plt.subplots(n, 1, figsize=(width, height_per_task * max(n, 1)),
                             squeeze=False)
    fig.suptitle(title, fontsize=13)
    for i, task_block in enumerate(tasks):
        ax = axes[i, 0]
        labels = [c["source"] for c in task_block["comparisons"]]
        killed = [c.get("total_mutants", 0) - c.get("surviving_mutants", 0)
                  for c in task_block["comparisons"]]
        alive = [c.get("surviving_mutants", 0) for c in task_block["comparisons"]]
        x = np.arange(len(labels))
        ax.bar(x, killed, color=KILLED_COLOR, label="killed")
        ax.bar(x, alive, bottom=killed, color=ALIVE_COLOR, label="surviving")
        ax.set_xticks(x)
        ax.set_xticklabels(labels, rotation=30, ha="right", fontsize=8)
        ax.set_title(task_block["task"], loc="left", fontsize=10)
        ax.set_ylabel("mutants", fontsize=9)
        if i == 0:
            ax.legend(loc="upper right", fontsize=8)
    fig.tight_layout(rect=(0, 0, 1, 0.97))
    buf = io.BytesIO()
    fig.savefig(buf, format="png", dpi=120)
    plt.close(fig)
    return buf.getvalue()
