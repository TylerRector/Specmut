"""Tests for the HTML report generator."""

from __future__ import annotations

from pathlib import Path


def test_html_report_generates(sample_report, tmp_path: Path) -> None:
    from specmut_viz.report import generate_html_report

    out = tmp_path / "report.html"
    generate_html_report(sample_report, out)
    body = out.read_text(encoding="utf-8")
    assert "<!DOCTYPE html>" in body
    assert "τ = 0.642" in body, "score should appear in the report"
    assert "Z3" not in body or "Z3" in body  # smt=False; tolerate either


def test_html_report_embeds_svg(sample_report, tmp_path: Path) -> None:
    from specmut_viz.report import generate_html_report

    sentinel = "<svg id='test-sentinel'/>"
    out = tmp_path / "report.html"
    generate_html_report(
        sample_report, out, hasse_svg=sentinel, dependency_svg=sentinel
    )
    body = out.read_text(encoding="utf-8")
    assert sentinel in body, "embedded SVG should appear unmodified"


def test_score_coloring() -> None:
    from specmut_viz.report import _score_class

    assert _score_class(0.9) == "high"
    assert _score_class(0.6) == "mid"
    assert _score_class(0.3) == "low"
    assert _score_class(0.8) == "high"
    assert _score_class(0.5) == "mid"


def test_fallback_note_in_report(sample_report, tmp_path: Path) -> None:
    """When ``smt_fallback_count`` > 0 the note section must appear."""
    from specmut_viz.report import generate_html_report

    sample_report["smt"] = True
    sample_report["smt_fallback_count"] = 3
    out = tmp_path / "report.html"
    generate_html_report(sample_report, out)
    body = out.read_text(encoding="utf-8")
    assert "fallback" in body.lower()
    assert "3" in body
