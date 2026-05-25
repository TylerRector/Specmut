"""Phase H refinement-trajectory plots.

Consumes ``aggregate/progression.json`` and draws one line per (task, model)
showing τ and kill-rate across rounds.  The trajectory plot is the key
visualization for the Phase H claim that specmut diagnostics enable iterative
specification strengthening.
"""

from __future__ import annotations

import io

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt


def render_progression(progression: dict, *,
                       title: str = "Refinement trajectory",
                       width: float = 9.0, height: float = 5.5) -> bytes:
    """Render τ trajectories per (task, model). Returns PNG bytes.

    Each task gets its own subplot; within a subplot each model is a line.
    The reference τ for the task is drawn as a horizontal dashed line for
    comparison.
    """
    trajectories = progression["trajectories"]
    tasks = sorted({t["task"] for t in trajectories})
    n_tasks = len(tasks)
    fig, axes = plt.subplots(n_tasks, 1, figsize=(width, height * max(n_tasks, 1) / 3),
                             squeeze=False, sharex=True)
    fig.suptitle(title, fontsize=13)

    cmap = plt.get_cmap("tab10")
    for i, task in enumerate(tasks):
        ax = axes[i, 0]
        task_trajectories = [t for t in trajectories if t["task"] == task]
        models = sorted({t["model"] for t in task_trajectories})
        for j, model in enumerate(models):
            entry = next((t for t in task_trajectories if t["model"] == model), None)
            if entry is None:
                continue
            xs = [p["version"] for p in entry["points"]]
            ys = [p["tau"] for p in entry["points"]]
            ax.plot(xs, ys, marker="o", color=cmap(j), label=model, linewidth=1.6)
            for x, y, point in zip(xs, ys, entry["points"]):
                ax.annotate(f"{y:.2f}", (x, y),
                            textcoords="offset points", xytext=(0, 6),
                            ha="center", fontsize=7)
        ax.set_title(task, loc="left", fontsize=10)
        ax.set_ylim(-0.05, 1.05)
        ax.set_ylabel("τ", fontsize=9)
        ax.grid(True, alpha=0.2)
        ax.axhline(0.3, color="#bbbbbb", lw=0.5, linestyle="--")
        ax.legend(loc="lower right", fontsize=8)
    axes[-1, 0].set_xlabel("refinement round")
    fig.tight_layout(rect=(0, 0, 1, 0.97))
    buf = io.BytesIO()
    fig.savefig(buf, format="png", dpi=120)
    plt.close(fig)
    return buf.getvalue()
