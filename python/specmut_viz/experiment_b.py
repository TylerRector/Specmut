"""Phase 4 Experiment B plots — paired baseline vs repaired comparisons."""

from __future__ import annotations

import io

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

BASELINE_COLOR = "#c64a3e"
REPAIRED_COLOR = "#2c7a4d"
IMPROVE_COLOR = "#2c7a4d"
REGRESS_COLOR = "#c64a3e"
UNCHANGED_COLOR = "#777777"


def render_paired_trajectories(exp_b: dict, *, width: float = 12.0,
                               height: float = 7.0) -> bytes:
    """Spaghetti plot: baseline → repaired τ per (model, task)."""
    cells = exp_b["cells"]
    if not cells:
        return b""
    tasks = sorted({c["task"] for c in cells})
    models = sorted({c["model"] for c in cells})
    fig, axes = plt.subplots(len(tasks), len(models),
                             figsize=(width, height),
                             squeeze=False, sharey=True)
    fig.suptitle("Experiment B — paired τ trajectories: baseline → repaired", fontsize=13)
    for i, task in enumerate(tasks):
        for j, model in enumerate(models):
            ax = axes[i, j]
            cell = next((c for c in cells
                         if c["task"] == task and c["model"] == model), None)
            if cell is None:
                continue
            for p in cell.get("pairs", []):
                if not (p.get("baseline_analyzable") and p.get("repaired_analyzable")):
                    continue
                b = p["baseline_tau"]; r = p["repaired_tau"]
                color = (IMPROVE_COLOR if r > b
                         else REGRESS_COLOR if r < b
                         else UNCHANGED_COLOR)
                ax.plot([0, 1], [b, r], color=color, alpha=0.5, linewidth=1.2)
                ax.scatter([0, 1], [b, r], color=color, s=18, zorder=3)
            ax.set_xlim(-0.2, 1.2)
            ax.set_xticks([0, 1])
            ax.set_xticklabels(["baseline", "repaired"], fontsize=7)
            ax.set_ylim(-0.05, 1.05)
            if j == 0:
                ax.set_ylabel(task, fontsize=9)
            if i == 0:
                ax.set_title(model, fontsize=9)
            ax.grid(True, axis="y", alpha=0.2)
    fig.tight_layout(rect=(0, 0, 1, 0.96))
    buf = io.BytesIO()
    fig.savefig(buf, format="png", dpi=120)
    plt.close(fig)
    return buf.getvalue()


def render_delta_tau_distribution(exp_b: dict, *, width: float = 8.0,
                                  height: float = 4.5) -> bytes:
    """Histogram of Δτ = τ_repaired − τ_baseline across all analyzable pairs."""
    cells = exp_b["cells"]
    diffs = []
    for c in cells:
        for p in c.get("pairs", []):
            if p.get("baseline_analyzable") and p.get("repaired_analyzable"):
                diffs.append(p["delta_tau"])
    fig, ax = plt.subplots(figsize=(width, height))
    if diffs:
        bins = np.linspace(-1.0, 1.0, 21)
        ax.hist(diffs, bins=bins, color="#3a7cc0", edgecolor="black", linewidth=0.4)
        med = np.median(diffs)
        ax.axvline(med, color="#c64a3e", lw=1.5, label=f"median Δτ = {med:.3f}")
        ax.axvline(0, color="#bbbbbb", lw=0.8, linestyle="--")
        ax.legend(loc="upper right", fontsize=9)
    ax.set_xlabel("Δτ = τ_repaired − τ_baseline")
    ax.set_ylabel("Count")
    ax.set_title("Distribution of paired Δτ (analyzable pairs only)")
    ax.grid(True, alpha=0.2)
    fig.tight_layout()
    buf = io.BytesIO()
    fig.savefig(buf, format="png", dpi=120)
    plt.close(fig)
    return buf.getvalue()


def render_refinement_summary(exp_b: dict, *, width: float = 10.0,
                              height: float = 5.0) -> bytes:
    """Grouped bars: median baseline τ vs median repaired τ per (model, task)."""
    cells = [c for c in exp_b["cells"]
             if c.get("baseline_tau_median") is not None
             and c.get("repaired_tau_median") is not None]
    if not cells:
        fig, ax = plt.subplots(figsize=(width, height))
        ax.text(0.5, 0.5, "No analyzable pairs available", ha="center",
                va="center", transform=ax.transAxes)
        buf = io.BytesIO(); fig.savefig(buf, format="png", dpi=120); plt.close(fig)
        return buf.getvalue()
    labels = [f"{c['model'].split(':')[0]}/{c['task']}" for c in cells]
    base = [c["baseline_tau_median"] for c in cells]
    rep = [c["repaired_tau_median"] for c in cells]
    x = np.arange(len(cells))
    w = 0.36
    fig, ax = plt.subplots(figsize=(width, height))
    ax.bar(x - w/2, base, w, color=BASELINE_COLOR, label="baseline")
    ax.bar(x + w/2, rep, w, color=REPAIRED_COLOR, label="repaired")
    ax.set_xticks(x)
    ax.set_xticklabels(labels, rotation=45, ha="right", fontsize=7)
    ax.set_ylim(0, 1.05)
    ax.set_ylabel("Median τ")
    ax.set_title("Median τ: baseline vs repaired per (model, task)")
    ax.legend(loc="upper right", fontsize=9)
    fig.tight_layout()
    buf = io.BytesIO()
    fig.savefig(buf, format="png", dpi=120)
    plt.close(fig)
    return buf.getvalue()


def render_compile_rate_change(exp_b: dict, *, width: float = 8.0,
                               height: float = 4.5) -> bytes:
    """Per-cell compile rate before vs after feedback."""
    cells = exp_b["cells"]
    labels = [f"{c['model'].split(':')[0]}/{c['task']}" for c in cells]
    base = [c["baseline_compile_rate"] for c in cells]
    rep = [c["repaired_compile_rate"] for c in cells]
    x = np.arange(len(cells))
    w = 0.36
    fig, ax = plt.subplots(figsize=(width, height))
    ax.bar(x - w/2, base, w, color=BASELINE_COLOR, label="baseline")
    ax.bar(x + w/2, rep, w, color=REPAIRED_COLOR, label="repaired")
    ax.set_xticks(x)
    ax.set_xticklabels(labels, rotation=45, ha="right", fontsize=7)
    ax.set_ylim(0, 1.05)
    ax.set_ylabel("Compile rate")
    ax.set_title("Compile rate: baseline vs repaired")
    ax.legend(loc="upper right", fontsize=9)
    fig.tight_layout()
    buf = io.BytesIO()
    fig.savefig(buf, format="png", dpi=120)
    plt.close(fig)
    return buf.getvalue()


def render_outcome_pie(exp_b: dict, *, width: float = 5.0,
                       height: float = 5.0) -> bytes:
    """Single pie chart of n_improved / n_regressed / n_unchanged aggregated."""
    cells = exp_b["cells"]
    imp = sum(c.get("n_improved", 0) or 0 for c in cells)
    reg = sum(c.get("n_regressed", 0) or 0 for c in cells)
    unc = sum(c.get("n_unchanged", 0) or 0 for c in cells)
    fig, ax = plt.subplots(figsize=(width, height))
    if (imp + reg + unc) == 0:
        ax.text(0.5, 0.5, "No analyzable pairs",
                ha="center", va="center", transform=ax.transAxes)
    else:
        ax.pie([imp, reg, unc],
               labels=[f"improved ({imp})", f"regressed ({reg})", f"unchanged ({unc})"],
               colors=[IMPROVE_COLOR, REGRESS_COLOR, UNCHANGED_COLOR],
               autopct="%1.0f%%", startangle=90,
               wedgeprops={"edgecolor": "white", "linewidth": 1})
    ax.set_title("Refinement outcomes (all cells)", fontsize=11)
    fig.tight_layout()
    buf = io.BytesIO()
    fig.savefig(buf, format="png", dpi=120)
    plt.close(fig)
    return buf.getvalue()
