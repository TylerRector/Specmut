#!/usr/bin/env python3
"""Phase 4 (qwen-only variant) generation sanitizer / format validator.

The qwen-only template-constrained prompts ask the LLM for theorem-only
output. This module enforces the grammar BEFORE Lean ever sees the file:

  - strips markdown code fences (```lean ... ```)
  - strips prose / blank lines before the first `theorem ` or `--` line
  - rejects forbidden keywords (def, inductive, axiom, by, ...) unless
    they originated from the scaffold prepended above the LLM output
  - enforces ≤ max_theorems theorem declarations
  - enforces every theorem ends with `:= sorry`
  - enforces ≤ max_lines total

All limits and the forbidden-keyword list come from the active config's
``[sanitizer]`` section. If the section is absent, ``sanitize_text`` is a
no-op that returns the input unchanged with status ``ok`` — preserving
the original (non-qwen-only) experiment's behavior.

Two entry points:

  sanitize_text(text, *, scaffold=None, config=None) -> SanitizeResult
      Pure function. Used in-process by generate_baseline.py.

  CLI:
      python sanitize_generated.py path/to/file.lean [--scaffold path]
      Prints the sanitizer status and writes the cleaned file in place
      (or to --out).
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path
from typing import Iterable

sys.path.insert(0, str(Path(__file__).resolve().parent))
from _common import load_config


# Status values written into baseline/repaired meta.json under
# ``sanitizer_status``.  Downstream stages should treat anything other
# than "ok" as format_rejected attrition.
STATUS_OK = "ok"
STATUS_FORMAT_REJECTED = "format_rejected"
STATUS_FORBIDDEN_KEYWORD = "forbidden_keyword"
STATUS_TOO_MANY_THEOREMS = "too_many_theorems"
STATUS_MISSING_SORRY = "missing_sorry"
STATUS_TOO_LONG = "too_long"
STATUS_EMPTY = "empty"

# Theorem header detection: matches a line starting with optional
# whitespace then `theorem ` followed by an identifier. Used to count
# top-level theorems and to find the first theorem when stripping prose.
_THEOREM_RE = re.compile(r"^\s*theorem\s+[A-Za-z_]")


@dataclass
class SanitizeResult:
    status: str
    cleaned: str
    violations: list[str] = field(default_factory=list)
    theorem_count: int = 0
    line_count: int = 0


# ---------------------------------------------------------------------------
# helpers

def _strip_code_fences(text: str) -> str:
    """Remove ```lean ... ``` (or ``` ... ```) wrappers."""
    lines = text.strip().splitlines()
    # Repeatedly strip a leading fence and its matching trailing fence.
    while lines and lines[0].lstrip().startswith("```"):
        lines = lines[1:]
        if lines and lines[-1].lstrip().startswith("```"):
            lines = lines[:-1]
    # Also strip any stray ``` lines anywhere.
    lines = [ln for ln in lines if not ln.strip().startswith("```")]
    return "\n".join(lines).rstrip() + ("\n" if lines else "")


def _strip_leading_prose(text: str) -> str:
    """Drop lines before the first `theorem ` or `--` comment line.

    The LLM sometimes prepends "Here is the Lean code:" or similar; the
    Lean parser would reject that line. We only drop a line if it is
    clearly prose (does not start with a Lean keyword we permit), to
    avoid accidentally eating a continuation line of a multi-line decl.
    """
    lines = text.splitlines()
    # Tokens whose presence at the start of a line means we have entered the
    # Lean source proper.  Includes FORBIDDEN keywords as well — the goal of
    # this pass is only to strip natural-language prose, not to enforce
    # grammar; the forbidden-keyword scan that runs after this is what
    # rejects `def`/`axiom`/etc.  If we excluded them here, those lines
    # would be silently dropped as "prose" and the rejection would never
    # fire.  Blank lines are handled separately (dropped while still in
    # the "prose" prefix, kept once we're inside the code block).
    permitted_prefixes = (
        "theorem ", "--", "/-", "/--",
        "def ", "inductive ", "axiom ", "lemma ", "example ",
        "namespace ", "open ", "import ", "structure ", "class ",
        "abbrev ", "instance ", "notation ", "macro ", "syntax ",
        "elab ", "mutual ", "variable ", "end ", "end\n",
        "#check", "#eval", "#print",
    )
    out: list[str] = []
    keeping = False
    for ln in lines:
        s = ln.lstrip()
        if not keeping:
            if not s:
                continue  # drop leading blank lines
            if any(s.startswith(p) for p in permitted_prefixes):
                keeping = True
                out.append(ln)
            else:
                # drop this prose line
                continue
        else:
            out.append(ln)
    return "\n".join(out).rstrip() + ("\n" if out else "")


def _count_theorems(text: str) -> int:
    return sum(1 for ln in text.splitlines() if _THEOREM_RE.match(ln))


_SORRY_RE = re.compile(r":=\s*sorry\s*$")
# A line consisting of just `sorry` (possibly indented, possibly with a
# trailing comment).  Common LLM pattern when the `:=` and the `sorry`
# are on separate lines:
#     theorem t : Prop :=
#       sorry
# The whole-theorem `_SORRY_RE` still catches that case across the joined
# decl text (because `\s` includes `\n`), but the per-line block extractor
# in `_extract_theorem_blocks` needs an explicit "this line closes the
# block" signal — otherwise it keeps slurping trailing prose.
_SORRY_LINE_RE = re.compile(r"^\s*sorry\b")


def _extract_theorem_blocks(text: str) -> str:
    """Re-emit text containing ONLY complete theorem blocks.

    Walks the cleaned source line-by-line. When a `theorem ` line is
    seen, collect subsequent lines (the theorem body, possibly multi-
    line) until a line ending in `:= sorry` is reached.  Anything
    BEFORE the first `theorem `, BETWEEN complete theorems (other than
    blank separators), or AFTER the last `:= sorry` is dropped.

    This is the trailing-prose fix.  Without it, a model that says
    "That's all." after the last theorem causes the last theorem's
    group to contain the prose line, which fails the `:= sorry`
    suffix match and trips ``missing_sorry``.
    """
    lines = text.splitlines()
    out: list[str] = []
    i = 0
    n = len(lines)
    while i < n:
        ln = lines[i]
        if _THEOREM_RE.match(ln):
            block = [ln]
            i += 1
            closed = bool(_SORRY_RE.search(ln.rstrip()))
            while i < n and not closed:
                nxt = lines[i]
                # If a new theorem starts before we closed this one, the
                # block is malformed; emit what we have so far and let the
                # downstream check catch the missing sorry.
                if _THEOREM_RE.match(nxt):
                    break
                block.append(nxt)
                stripped = nxt.rstrip()
                if _SORRY_RE.search(stripped) or _SORRY_LINE_RE.match(stripped):
                    closed = True
                    i += 1
                    break
                i += 1
            out.extend(block)
            if closed and i < n:
                # blank-separate from next decl for readability
                out.append("")
        else:
            i += 1
    # Strip any double blank tail
    while out and not out[-1].strip():
        out.pop()
    return "\n".join(out) + ("\n" if out else "")


def _all_theorems_end_with_sorry(text: str) -> tuple[bool, list[str]]:
    """Group lines into theorem declarations and verify each ends with
    `:= sorry` (allowing whitespace).

    Returns (ok, missing_theorem_names).
    """
    # A theorem decl runs from a `theorem ` line up to (but not
    # including) the next `theorem ` line or EOF.
    lines = text.splitlines()
    decls: list[list[str]] = []
    cur: list[str] = []
    for ln in lines:
        if _THEOREM_RE.match(ln):
            if cur:
                decls.append(cur)
            cur = [ln]
        else:
            if cur:
                cur.append(ln)
    if cur:
        decls.append(cur)
    missing: list[str] = []
    # Accept either form:
    #   ... := sorry            (whole-decl trailing pattern)
    #   ...
    #     sorry                 (bare `sorry` on the final line; the
    #                            `:=` was earlier in the decl)
    sorry_tail_re = re.compile(r":=\s*sorry\s*$")
    bare_sorry_re = re.compile(r"^\s*sorry\b\s*$", re.MULTILINE)
    for d in decls:
        joined = "\n".join(d).rstrip()
        name = d[0].split()[1] if len(d[0].split()) >= 2 else "<unknown>"
        ok = bool(sorry_tail_re.search(joined)) or bool(
            bare_sorry_re.search(joined) and ":=" in joined)
        if not ok:
            missing.append(name)
    return (not missing, missing)


def _find_forbidden(text: str, forbidden: Iterable[str]) -> list[str]:
    """Return the list of forbidden tokens that appear in text.

    Tokens are matched as substrings on a per-line basis after stripping
    inline `--` comments, so a comment containing the word `axiom` does
    not trigger a violation.
    """
    hits: list[str] = []
    for raw in text.splitlines():
        # Strip line comments before scanning.
        code = raw.split("--", 1)[0]
        for tok in forbidden:
            if tok in code:
                hits.append(f"{tok!r} in line: {raw.strip()[:80]}")
                break
    return hits


# ---------------------------------------------------------------------------
# public

def sanitize_text(text: str, *, scaffold: str | None = None,
                  config: dict | None = None) -> SanitizeResult:
    """Apply sanitizer rules to raw LLM output.

    ``scaffold`` is the per-task scaffold text that will be prepended
    above the LLM block. It is NOT scanned for forbidden keywords (it's
    trusted benchmark code) but IS counted toward max_lines and toward
    the theorem count check (scaffolds in this experiment have no
    theorems, so this is conservative).

    ``config`` defaults to the active config (PHASE4_CONFIG). If the
    config has no ``[sanitizer]`` section, this function returns the
    input unchanged with status ``ok`` (so the original frozen
    experiment is unaffected).
    """
    cfg = config if config is not None else load_config()
    san = cfg.get("sanitizer")
    if san is None:
        return SanitizeResult(status=STATUS_OK, cleaned=text,
                              theorem_count=_count_theorems(text),
                              line_count=len(text.splitlines()))

    max_theorems = int(san.get("max_theorems", 2))
    max_lines = int(san.get("max_lines", 60))
    require_sorry = bool(san.get("require_sorry", True))
    forbidden = list(san.get("forbidden_keywords", []))

    violations: list[str] = []
    cleaned = _strip_code_fences(text)
    cleaned = _strip_leading_prose(cleaned)
    # Scan for forbidden keywords on the pre-extraction text, but only
    # through the last `:= sorry`-ending line — anything past that is
    # trailing prose ("That's all!") and would yield benign false hits
    # like "begin"/"open " when used as English.  Doing the scan BEFORE
    # `_extract_theorem_blocks` is what makes a `def helper` line
    # between theorems get flagged as forbidden_keyword instead of
    # being silently dropped.
    lines = cleaned.splitlines()
    last_sorry = -1
    for idx, ln in enumerate(lines):
        if _SORRY_RE.search(ln.rstrip()):
            last_sorry = idx
    scan_lines = lines if last_sorry < 0 else lines[: last_sorry + 1]
    hits = _find_forbidden("\n".join(scan_lines), forbidden)
    if hits:
        # Stage cleaned (without extraction) so the rejected_raw sidecar
        # preserves the original structure for inspection.
        return SanitizeResult(status=STATUS_FORBIDDEN_KEYWORD,
                              cleaned=cleaned, violations=hits,
                              theorem_count=_count_theorems(cleaned),
                              line_count=len(cleaned.splitlines()))

    # Drop trailing prose after the last `:= sorry`, and intra-theorem junk.
    cleaned = _extract_theorem_blocks(cleaned)

    if not cleaned.strip():
        return SanitizeResult(status=STATUS_EMPTY, cleaned=cleaned,
                              violations=["empty after sanitization"])

    # Re-run forbidden check on the extracted text — defensive, since
    # _extract_theorem_blocks shouldn't introduce anything new but might
    # leave us with a body containing a forbidden tactic.
    hits = _find_forbidden(cleaned, forbidden)
    if hits:
        violations.extend(hits)
        return SanitizeResult(status=STATUS_FORBIDDEN_KEYWORD,
                              cleaned=cleaned, violations=violations,
                              theorem_count=_count_theorems(cleaned),
                              line_count=len(cleaned.splitlines()))

    n_theorems = _count_theorems(cleaned)
    if n_theorems == 0:
        violations.append("no theorem declarations found")
        return SanitizeResult(status=STATUS_FORMAT_REJECTED,
                              cleaned=cleaned, violations=violations,
                              theorem_count=0,
                              line_count=len(cleaned.splitlines()))
    if n_theorems > max_theorems:
        violations.append(f"{n_theorems} theorems > max_theorems {max_theorems}")
        return SanitizeResult(status=STATUS_TOO_MANY_THEOREMS,
                              cleaned=cleaned, violations=violations,
                              theorem_count=n_theorems,
                              line_count=len(cleaned.splitlines()))

    if require_sorry:
        ok, missing = _all_theorems_end_with_sorry(cleaned)
        if not ok:
            violations.append(f"missing := sorry in: {missing}")
            return SanitizeResult(status=STATUS_MISSING_SORRY,
                                  cleaned=cleaned, violations=violations,
                                  theorem_count=n_theorems,
                                  line_count=len(cleaned.splitlines()))

    # Length check uses scaffold + cleaned to reflect the final file size.
    combined_lines = len((scaffold or "").splitlines()) + len(cleaned.splitlines())
    if combined_lines > max_lines:
        violations.append(f"{combined_lines} lines > max_lines {max_lines}")
        return SanitizeResult(status=STATUS_TOO_LONG,
                              cleaned=cleaned, violations=violations,
                              theorem_count=n_theorems,
                              line_count=combined_lines)

    return SanitizeResult(status=STATUS_OK, cleaned=cleaned,
                          theorem_count=n_theorems,
                          line_count=combined_lines)


# ---------------------------------------------------------------------------
# CLI

def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("file", type=Path)
    ap.add_argument("--scaffold", type=Path, default=None)
    ap.add_argument("--out", type=Path, default=None,
                    help="write cleaned text here (default: overwrite in place)")
    ap.add_argument("--json", action="store_true",
                    help="emit JSON status to stdout")
    args = ap.parse_args()

    text = args.file.read_text()
    scaffold = args.scaffold.read_text() if args.scaffold and args.scaffold.exists() else None
    result = sanitize_text(text, scaffold=scaffold)

    out = args.out or args.file
    out.write_text(result.cleaned)

    if args.json:
        print(json.dumps({
            "status": result.status,
            "violations": result.violations,
            "theorem_count": result.theorem_count,
            "line_count": result.line_count,
            "file": str(args.file),
        }, indent=2))
    else:
        print(f"[{result.status}] {args.file}  "
              f"theorems={result.theorem_count}  lines={result.line_count}")
        for v in result.violations:
            print(f"  - {v}")

    return 0 if result.status == STATUS_OK else 1


if __name__ == "__main__":
    raise SystemExit(main())
