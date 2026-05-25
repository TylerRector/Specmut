"""Phase 4 Experiment A plots.

Each function consumes ``aggregate/experiment_a.json`` and returns PNG bytes.
The plots are intentionally compact (one figure per question) so the report
can scan them quickly.
"""

from __future__ import annotations

import io
from typing import Iterable

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np


CELL_FACE = "#3a7cc0"
CONTROL_TRIVIAL = "#c64a3e"
CONTROL_PARTIAL = "#dba03b"
CONTROL_REFERENCE = "#2c7a4d"


def _grid(n: int) -> tuple[int, int]:
    """Return (rows, cols) for an n-cell figure grid roughly 16:9."""
    if n <= 3:
        return (1, n)
    cols = min(n, 5)
    rows = (n + cols - 1) // cols
    return (rows, cols)


def render_tau_distributions(exp_a: dict, *, width: float = 12.0,
                             height: float = 7.0) -> bytes:
    """Violin/box per (model, task) cell with control overlays.

    Cells are laid out as a (tasks × models) grid for direct comparison.
    """
    cells = exp_a["cells"]
    if not cells:
        return b""
    tasks = sorted({c["task"] for c in cells})
    models = sorted({c["model"] for c in cells})
    controls = exp_a.get("controls", [])

    fig, axes = plt.subplots(len(tasks), len(models),
                             figsize=(width, height),
                             squeeze=False, sharey=True)
    fig.suptitle("Experiment A — τ distributions per (model, task)", fontsize=13)

    for i, task in enumerate(tasks):
        for j, model in enumerate(models):
            ax = axes[i, j]
            cell = next((c for c in cells
                         if c["task"] == task and c["model"] == model), None)
            taus = (cell or {}).get("tau_values") or []
            if taus:
                parts = ax.violinplot([taus], showmeans=False, showmedians=True)
                for body in parts["bodies"]:
                    body.set_facecolor(CELL_FACE)
                    body.set_alpha(0.6)
            # Overlay reference & controls for this task.
            for ck, color, marker in (("reference", CONTROL_REFERENCE, "D"),
                                      ("partial", CONTROL_PARTIAL, "s"),
                                      ("trivial", CONTROL_TRIVIAL, "x")):
                ctl = next((c for c in controls
                            if c["task"] == task and c["control_type"] == ck), None)
                if ctl is not None:
                    ax.scatter([1], [ctl["tau"]], color=color, marker=marker,
                               s=60, edgecolor="black", linewidth=0.4,
                               zorder=3, label=ck if i == 0 and j == 0 else None)
            ax.set_ylim(-0.05, 1.05)
            ax.set_xticks([])
            if j == 0:
                ax.set_ylabel(task, fontsize=9)
            if i == 0:
                ax.set_title(model, fontsize=9)
            ax.grid(True, axis="y", alpha=0.2)
    if axes.size:
        axes[0, 0].legend(loc="upper right", fontsize=7)
    fig.tight_layout(rect=(0, 0, 1, 0.96))
    buf = io.BytesIO()
    fig.savefig(buf, format="png", dpi=120)
    plt.close(fig)
    return buf.getvalue()


def render_compile_vs_semantic(exp_a: dict, *, width: float = 8.0,
                               height: float = 5.5) -> bytes:
    """Scatter of compile rate vs median τ per cell."""
    cells = exp_a["cells"]
    fig, ax = plt.subplots(figsize=(width, height))
    xs = [c["compile_rate"] for c in cells]
    ys = [c["tau_median"] if c["tau_median"] is not None else 0.0 for c in cells]
    labels = [f"{c['model'].split(':')[0]}/{c['task']}" for c in cells]
    ax.scatter(xs, ys, c=CELL_FACE, s=42, alpha=0.8, edgecolor="black", linewidth=0.4)
    for x, y, lbl in zip(xs, ys, labels):
        ax.annotate(lbl, (x, y), xytext=(4, 4),
                    textcoords="offset points", fontsize=7, alpha=0.7)
    ax.set_xlabel("Compile rate")
    ax.set_ylabel("Median τ")
    ax.set_xlim(-0.05, 1.05)
    ax.set_ylim(-0.05, 1.05)
    ax.grid(True, alpha=0.2)
    ax.set_title("Compile success vs semantic tightness, per (model, task) cell")
    fig.tight_layout()
    buf = io.BytesIO()
    fig.savefig(buf, format="png", dpi=120)
    plt.close(fig)
    return buf.getvalue()


def render_attrition_flow(exp_a: dict, *, width: float = 12.0,
                          height: float = 6.0) -> bytes:
    """Stacked bar per (model, task) cell showing failure breakdown."""
    cells = exp_a["cells"]
    if not cells:
        return b""
    categories = []
    for c in cells:
        for k in c.get("failure_breakdown", {}).keys():
            if k not in categories:
                categories.append(k)
    categories = sorted(categories)
    color_map = {
        "success": "#2c7a4d",
        "tau_zero": "#dba03b",
        "insufficient_mutations": "#dbd83b",
        "translation_failed": "#9b3edc",
        "model_bound_exceeded": "#3a7cc0",
        "unsupported_constructs": "#c64a3e",
        "timeout": "#666666",
        "compile_failure": "#222222",
        "skipped_lean_failure": "#444444",
    }
    labels = [f"{c['model'].split(':')[0]}\n{c['task']}" for c in cells]
    x = np.arange(len(cells))
    fig, ax = plt.subplots(figsize=(width, height))
    bottom = np.zeros(len(cells))
    for cat in categories:
        vals = np.array([c.get("failure_breakdown", {}).get(cat, 0) for c in cells])
        if vals.sum() == 0:
            continue
        ax.bar(x, vals, bottom=bottom, label=cat,
               color=color_map.get(cat, "#bbbbbb"))
        bottom += vals
    ax.set_xticks(x)
    ax.set_xticklabels(labels, rotation=45, ha="right", fontsize=7)
    ax.set_ylabel("Count")
    ax.set_title("Experiment A — attrition per (model, task) cell")
    ax.legend(loc="upper right", fontsize=7, ncol=2)
    fig.tight_layout()
    buf = io.BytesIO()
    fig.savefig(buf, format="png", dpi=120)
    plt.close(fig)
    return buf.getvalue()


def render_model_comparison(exp_a: dict, *, width: float = 8.0,
                            height: float = 5.0) -> bytes:
    """Boxplot of τ by model, aggregated across tasks."""
    cells = exp_a["cells"]
    by_model: dict[str, list[float]] = {}
    for c in cells:
        m = c["model"]
        by_model.setdefault(m, []).extend(c.get("tau_values") or [])
    models = sorted(by_model)
    data = [by_model[m] for m in models]
    fig, ax = plt.subplots(figsize=(width, height))
    ax.boxplot(data, labels=models, showfliers=True)
    ax.set_ylabel("τ")
    ax.set_ylim(-0.05, 1.05)
    ax.set_title("Cross-model τ distribution (aggregated over tasks)")
    ax.grid(True, axis="y", alpha=0.2)
    plt.setp(ax.get_xticklabels(), rotation=15, ha="right", fontsize=8)
    fig.tight_layout()
    buf = io.BytesIO()
    fig.savefig(buf, format="png", dpi=120)
    plt.close(fig)
    return buf.getvalue()


def render_negative_control_separation(exp_a: dict, *, width: float = 10.0,
                                       height: float = 5.0) -> bytes:
    """Strip plot per task: trivial vs partial vs LLM vs reference τ."""
    cells = exp_a["cells"]
    controls = exp_a.get("controls", [])
    tasks = sorted({c["task"] for c in cells})
    fig, axes = plt.subplots(1, len(tasks), figsize=(width, height),
                             squeeze=False, sharey=True)
    fig.suptitle("Negative-control separation: τ for each variant per task", fontsize=12)
    for i, task in enumerate(tasks):
        ax = axes[0, i]
        # Trivial / partial / reference single points.
        groups = [("trivial", CONTROL_TRIVIAL, 0),
                  ("partial", CONTROL_PARTIAL, 1),
                  ("reference", CONTROL_REFERENCE, 3)]
        for name, color, xpos in groups:
            ctl = next((c for c in controls
                        if c["task"] == task and c["control_type"] == name), None)
            if ctl is not None:
                ax.scatter([xpos], [ctl["tau"]], color=color, s=70,
                           edgecolor="black", linewidth=0.5, zorder=3,
                           label=name)
        # LLM τ values at x=2 (jittered).
        llm_taus = []
        for c in cells:
            if c["task"] == task:
                llm_taus.extend(c.get("tau_values") or [])
        if llm_taus:
            rng = np.random.default_rng(7)
            xs = 2 + rng.uniform(-0.18, 0.18, size=len(llm_taus))
            ax.scatter(xs, llm_taus, color=CELL_FACE, s=18, alpha=0.6, label="LLM")
        ax.set_xticks([0, 1, 2, 3])
        ax.set_xticklabels(["trivial", "partial", "LLM", "ref"], fontsize=8)
        ax.set_title(task, fontsize=9)
        ax.set_ylim(-0.05, 1.05)
        ax.grid(True, axis="y", alpha=0.2)
    fig.tight_layout(rect=(0, 0, 1, 0.94))
    buf = io.BytesIO()
    fig.savefig(buf, format="png", dpi=120)
    plt.close(fig)
    return buf.getvalue()
