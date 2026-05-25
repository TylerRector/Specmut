"""Phase H witness rendering.

Witnesses are concrete distinguishing models attached to alive mutants by
Phase F.  When present, they explain *why* a mutant survived — typically by
naming one preserved property and one unconstrained behavior.

This module emits formatted HTML blocks suitable for embedding in the
Phase H report.  No matplotlib here — witnesses are textual.
"""

from __future__ import annotations

import html
from typing import Iterable


def render_witness_block(witness: dict) -> str:
    """Render a single witness dict as an HTML <div>."""
    theorem = html.escape(str(witness.get("theorem", "?")))
    mutant_class = html.escape(str(witness.get("mutant_class", "?")))
    preserved = witness.get("preserved_properties") or []
    unconstrained = witness.get("unconstrained_behaviors") or []
    interpretation = html.escape(str(witness.get("interpretation", "")))
    model_desc = html.escape(str(witness.get("model_description", "")))
    distance = witness.get("distance")
    parts = [
        f'<div class="witness">',
        f'  <div class="witness-head"><b>Mutant</b> ({mutant_class}'
        + (f', d={distance:.3f}' if isinstance(distance, (int, float)) else '')
        + f') survives <code>{theorem}</code></div>',
    ]
    if preserved:
        parts.append('  <div><b>Preserved:</b><ul>')
        for p in preserved:
            parts.append(f'    <li>{html.escape(str(p))}</li>')
        parts.append('  </ul></div>')
    if unconstrained:
        parts.append('  <div><b>Unconstrained:</b><ul>')
        for u in unconstrained:
            parts.append(f'    <li>{html.escape(str(u))}</li>')
        parts.append('  </ul></div>')
    if model_desc:
        parts.append(f'  <div><b>Witness model:</b> <code>{model_desc}</code></div>')
    if interpretation:
        parts.append(f'  <div class="interpretation"><b>Interpretation:</b> {interpretation}</div>')
    parts.append('</div>')
    return "\n".join(parts)


def render_witnesses_for_spec(record: dict, *, max_per_spec: int = 5) -> str:
    """Render witnesses extracted from a specmut_results JSON record.

    Returns an HTML <section> with the file label and up to max_per_spec
    witness blocks.  Returns empty string when no witnesses are present.
    """
    witnesses = record.get("witnesses") or []
    if not witnesses:
        return ""
    file_label = html.escape(record.get("file", "?"))
    out = [f'<section class="witnesses">',
           f'  <h4>{file_label}</h4>']
    for w in witnesses[:max_per_spec]:
        out.append(render_witness_block(w))
    if len(witnesses) > max_per_spec:
        out.append(f'  <p class="more">… and {len(witnesses) - max_per_spec} more.</p>')
    out.append('</section>')
    return "\n".join(out)


def render_all_witnesses(records: Iterable[dict], *,
                         max_per_spec: int = 3) -> str:
    """Render witnesses from multiple records into a single HTML section."""
    blocks = []
    for r in records:
        block = render_witnesses_for_spec(r, max_per_spec=max_per_spec)
        if block:
            blocks.append(block)
    if not blocks:
        return ('<p class="no-witnesses"><em>No Phase F witnesses present in this run. '
                'Witnesses are populated only on specmut\'s per-theorem sliced path; '
                'specs that fall back to global mode produce τ scores without '
                'concrete distinguishing models.</em></p>')
    return "\n".join(blocks)


WITNESS_CSS = """
.witness { border-left: 3px solid #c64a3e; padding: 0.5em 0.8em; margin: 0.7em 0;
           background: #fff7f5; font-size: 0.95em; }
.witness-head { margin-bottom: 0.4em; }
.witness ul { margin: 0.2em 0 0.4em 1.4em; padding: 0; }
.witness .interpretation { margin-top: 0.5em; color: #555; }
.witnesses h4 { margin: 0.6em 0 0.3em 0; font-family: monospace; }
.no-witnesses { color: #777; font-size: 0.95em; }
"""
