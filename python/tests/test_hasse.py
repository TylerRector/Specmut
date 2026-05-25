"""Tests for the Hasse and dependency-graph renderers.

These tests pipe graphviz output rather than writing to disk so they
exercise the same rendering path the HTML report uses (inline SVG
embedding).  They require the ``dot`` binary to be installed; if it's
absent on the host, the tests are skipped with an informative message.
"""

from __future__ import annotations

from pathlib import Path

import pytest


def _have_dot() -> bool:
    import shutil

    return shutil.which("dot") is not None


requires_dot = pytest.mark.skipif(
    not _have_dot(),
    reason="graphviz `dot` binary not available",
)


@requires_dot
def test_hasse_renders(sample_report, tmp_path: Path) -> None:
    from specmut_viz.hasse import render_hasse_diagram

    output = tmp_path / "hasse"
    rendered = render_hasse_diagram(sample_report, output, format="svg")
    body = Path(rendered).read_text(encoding="utf-8")
    assert body.startswith("<?xml") or body.startswith("<svg"), body[:80]


@requires_dot
def test_dependency_renders(sample_report, tmp_path: Path) -> None:
    from specmut_viz.dependency_graph import render_dependency_graph

    output = tmp_path / "deps"
    rendered = render_dependency_graph(sample_report, output, format="svg")
    body = Path(rendered).read_text(encoding="utf-8")
    assert body.startswith("<?xml") or body.startswith("<svg"), body[:80]
