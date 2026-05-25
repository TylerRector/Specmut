"""Phase H comparison plots — human reference vs LLM variants.

Consumes ``aggregate/comparison.json`` produced by ``phase3/scripts/aggregate.py``
and renders grouped bar charts for τ and kill rate.

Each per-task chart groups every LLM (model, round) bar next to the human
reference bar so the eye can compare directly.  This is the headline
visualization for the Phase H claim that compile success ≠ semantic quality.
"""

from __future__ import annotations

import io
from typing import Iterable

import matplotlib

matplotlib.use("Agg")  # backend-safe — no display server
import matplotlib.pyplot as plt
import numpy as np


HUMAN_COLOR = "#2c7a4d"   # green
LLM_COLORS = {
    "v1": "#c64a3e",
    "v2": "#dba03b",
    "v3": "#3a7cc0",
}
DEFAULT_LLM_COLOR = "#6f6f6f"


def _bar_color(label: str) -> str:
    if label == "human_reference":
        return HUMAN_COLOR
    # label shape: "{model}/v{n}"
    if "/" in label:
        suffix = label.split("/", 1)[1]
        return LLM_COLORS.get(suffix, DEFAULT_LLM_COLOR)
    return DEFAULT_LLM_COLOR


def render_tau_comparison(comparison: dict, *, title: str = "Tightness τ — human vs. LLM",
                          width: float = 10.0, height_per_task: float = 1.6) -> bytes:
    """Return PNG bytes for a per-task τ comparison chart."""
    tasks = comparison["tasks"]
    n_tasks = len(tasks)
    fig, axes = plt.subplots(n_tasks, 1, figsize=(width, height_per_task * max(n_tasks, 1)),
                             squeeze=False)
    fig.suptitle(title, fontsize=13)
    for i, task_block in enumerate(tasks):
        ax = axes[i, 0]
        labels = [c["source"] for c in task_block["comparisons"]]
        taus = [c["tau"] for c in task_block["comparisons"]]
        colors = [_bar_color(l) for l in labels]
        x = np.arange(len(labels))
        ax.bar(x, taus, color=colors)
        ax.set_xticks(x)
        ax.set_xticklabels(labels, rotation=30, ha="right", fontsize=8)
        ax.set_ylim(0, 1.05)
        ax.set_ylabel("τ", fontsize=9)
        ax.set_title(task_block["task"], fontsize=10, loc="left")
        ax.axhline(0.3, color="#bbbbbb", lw=0.7, linestyle="--")
        for xi, t in zip(x, taus):
            ax.text(xi, t + 0.02, f"{t:.2f}", ha="center", va="bottom", fontsize=7)
    fig.tight_layout(rect=(0, 0, 1, 0.97))
    buf = io.BytesIO()
    fig.savefig(buf, format="png", dpi=120)
    plt.close(fig)
    return buf.getvalue()


def render_kill_rate_comparison(comparison: dict, *,
                                title: str = "Kill rate — human vs. LLM",
                                width: float = 10.0,
                                height_per_task: float = 1.6) -> bytes:
    """Return PNG bytes for a per-task kill-rate comparison chart."""
    tasks = comparison["tasks"]
    n_tasks = len(tasks)
    fig, axes = plt.subplots(n_tasks, 1, figsize=(width, height_per_task * max(n_tasks, 1)),
                             squeeze=False)
    fig.suptitle(title, fontsize=13)
    for i, task_block in enumerate(tasks):
        ax = axes[i, 0]
        labels = [c["source"] for c in task_block["comparisons"]]
        krs = [c["kill_rate"] for c in task_block["comparisons"]]
        colors = [_bar_color(l) for l in labels]
        x = np.arange(len(labels))
        ax.bar(x, krs, color=colors)
        ax.set_xticks(x)
        ax.set_xticklabels(labels, rotation=30, ha="right", fontsize=8)
        ax.set_ylim(0, 1.05)
        ax.set_ylabel("kill rate", fontsize=9)
        ax.set_title(task_block["task"], fontsize=10, loc="left")
        for xi, t in zip(x, krs):
            ax.text(xi, t + 0.02, f"{t:.2f}", ha="center", va="bottom", fontsize=7)
    fig.tight_layout(rect=(0, 0, 1, 0.97))
    buf = io.BytesIO()
    fig.savefig(buf, format="png", dpi=120)
    plt.close(fig)
    return buf.getvalue()


def render_compile_vs_tau(comparison: dict, *,
                          title: str = "Compile success vs. semantic tightness",
                          width: float = 8.0, height: float = 5.0) -> bytes:
    """Scatter plot demonstrating that compile success doesn't predict τ.

    Each point is a (model, round, task) sample.  X is binary (compile pass/fail),
    Y is τ.  The cluster of compile-passing points at low τ is the headline
    Phase H argument.
    """
    xs, ys, colors = [], [], []
    for t in comparison["tasks"]:
        for c in t["comparisons"]:
            if c["source"] == "human_reference":
                continue
            xs.append(1.0 if c["compile_success"] else 0.0)
            ys.append(c["tau"])
            colors.append(HUMAN_COLOR if c["compile_success"] else "#c64a3e")
    fig, ax = plt.subplots(figsize=(width, height))
    # Jitter X so coincident points don't overlap exactly.
    rng = np.random.default_rng(0)
    xs_jittered = np.array(xs) + rng.uniform(-0.08, 0.08, size=len(xs))
    ax.scatter(xs_jittered, ys, c=colors, s=42, alpha=0.8, edgecolor="black", linewidth=0.4)
    ax.set_xlim(-0.4, 1.4)
    ax.set_xticks([0, 1])
    ax.set_xticklabels(["compile FAIL", "compile PASS"])
    ax.set_ylim(-0.05, 1.05)
    ax.axhline(0.3, color="#bbbbbb", lw=0.7, linestyle="--",
               label="weak threshold (τ=0.3)")
    ax.set_ylabel("Tightness τ")
    ax.set_title(title)
    ax.legend(loc="upper left", fontsize=8)
    fig.tight_layout()
    buf = io.BytesIO()
    fig.savefig(buf, format="png", dpi=120)
    plt.close(fig)
    return buf.getvalue()
