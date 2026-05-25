"""specmut_viz — visualization and HTML report generation.

The package consumes the JSON output of the specmut CLI (matching §8.1
of the spec) and produces:

* ``hasse.render_hasse_diagram``       — Hasse-style mutant diagram (SVG).
* ``dependency_graph.render_dependency_graph`` — Component status graph (SVG).
* ``report.generate_html_report``      — Self-contained HTML report.

All three are invoked by the Rust CLI via ``python3 -m specmut_viz.report``
when the package is on ``PYTHONPATH``; the CLI falls back to a pure-Rust
HTML renderer when the package isn't available.
"""

# The Phase 7 surfaces (hasse, dependency_graph, report) depend on graphviz
# and are loaded lazily so that Phase H tooling can run without graphviz
# installed.  Import them directly from their submodules if you need them.
from .comparison import (
    render_tau_comparison,
    render_kill_rate_comparison,
    render_compile_vs_tau,
)
from .progression import render_progression
from .survival import render_survival
from .witness_report import (
    render_witness_block,
    render_witnesses_for_spec,
    render_all_witnesses,
    WITNESS_CSS,
)
# Phase 4 modules
from .experiment_a import (
    render_tau_distributions,
    render_compile_vs_semantic,
    render_attrition_flow,
    render_model_comparison,
    render_negative_control_separation,
)
from .experiment_b import (
    render_paired_trajectories,
    render_delta_tau_distribution,
    render_refinement_summary,
    render_compile_rate_change,
    render_outcome_pie,
)
from .stat_tables import (
    render_experiment_a_cells,
    render_experiment_b_cells,
    render_negative_control_table,
    render_cross_model_table,
    render_determinism_block,
    STATS_CSS,
)
from .attrition import render_attrition_overview

__all__ = [
    "render_tau_comparison",
    "render_kill_rate_comparison",
    "render_compile_vs_tau",
    "render_progression",
    "render_survival",
    "render_witness_block",
    "render_witnesses_for_spec",
    "render_all_witnesses",
    "WITNESS_CSS",
    # Phase 4
    "render_tau_distributions",
    "render_compile_vs_semantic",
    "render_attrition_flow",
    "render_model_comparison",
    "render_negative_control_separation",
    "render_paired_trajectories",
    "render_delta_tau_distribution",
    "render_refinement_summary",
    "render_compile_rate_change",
    "render_outcome_pie",
    "render_experiment_a_cells",
    "render_experiment_b_cells",
    "render_negative_control_table",
    "render_cross_model_table",
    "render_determinism_block",
    "STATS_CSS",
    "render_attrition_overview",
]

__version__ = "0.1.0"
