#!/usr/bin/env python3
"""Phase H Stage 1b: semantic projection from real Lean to specmut-analyzable.

Reads ``benchmarks/{task}/reference.lean`` (a verbatim file from a real GitHub
project) and emits ``benchmarks/{task}/reference_analyzable.lean`` — a smaller
artifact that preserves the file's *semantic structure* (inductive datatypes,
recursive predicates, theorem signatures) while stripping the *infrastructure*
that explodes specmut's finite-model analysis at n=2.

Pipeline (in order):

  1. ``_strip_comments``      — drop ``/-! ... -/``, ``/- ... -/`` blocks and
                                ``-- line comments``.
  2. ``_strip_imports_etc``   — drop ``import``/``set_option`` lines.
  3. ``_strip_commands``      — drop ``#eval``/``#check``/``#print``/``#reduce``
                                blocks along with their indented continuations.
  4. ``_split_into_blocks``   — partition into top-level declarations.
  5. per-block transforms:
       - ``lemma`` / ``example`` / ``instance``     → drop.
       - ``theorem``                                → replace proof body with
                                                      ``sorry`` via depth-aware
                                                      ``:=`` location.
       - ``inductive`` / ``structure`` / ``class``  → strip ``deriving`` clause.
       - everything else                            → keep verbatim.

Output is validated by ``--validate``: ``lean`` is run on the result and any
hard errors abort with a non-zero exit code.  ``sorry`` warnings are
permitted (they're how the projection conveys "no proof committed").

The transforms are deliberately text-level: a true Lean parser would tie this
stage to a moving grammar.  When a file uses constructs we don't recognize
(``#guard``, custom attributes with complex parameters, etc.), the projection
may need refinement — that's why the pipeline always runs ``--validate``.
"""

from __future__ import annotations

import argparse
import re
import shutil
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from _common import BENCHMARKS, PHASE3, ensure_lean_on_path, list_tasks


DECL_KEYWORDS = (
    "theorem", "lemma", "example",
    "def", "abbrev", "axiom",
    "inductive", "structure", "class", "instance",
    "notation", "infix", "infixl", "infixr", "prefix", "postfix",
    "macro", "elab", "syntax",
    "variable", "namespace", "end", "open", "section",
)
DECL_START_RE = re.compile(
    r"^\s*(?:@\[[^\]]+\]\s+)?"  # optional attribute prefix
    r"(?P<kw>" + "|".join(DECL_KEYWORDS) + r")\b"
)

DROP_KEYWORDS = {
    "lemma", "example", "instance",
    # Macros / elaborators / custom syntax are proof infrastructure — they
    # don't carry semantic constraints on the spec's domain objects.
    "macro", "elab", "syntax",
}

# Theorems decorated with these attributes are simp/rewrite/optimization
# hints, not specification axioms.  Drop them along with their proof bodies.
DROP_ATTRIBUTE_PATTERNS = (
    r"@\[csimp\]",
    r"@\[simp[^\]]*\]",
    r"@\[ext[^\]]*\]",
    r"@\[reducible[^\]]*\]",
    r"@\[inline[^\]]*\]",
    r"@\[macro_inline[^\]]*\]",
    r"@\[specialize[^\]]*\]",
    r"@\[unused_variables_ignore[^\]]*\]",
    r"@\[deprecated[^\]]*\]",
)
DROP_ATTRIBUTE_RE = re.compile("|".join(DROP_ATTRIBUTE_PATTERNS))

BLOCK_COMMENT_RE = re.compile(r"/-[-!]?.*?-/", re.DOTALL)

IMPORT_RE = re.compile(r"^\s*import\b.*\n?", re.MULTILINE)
SET_OPTION_RE = re.compile(r"^\s*set_option\b.*\n?", re.MULTILINE)

COMMAND_LINE_RE = re.compile(r"^\s*#\w+\b")
# A deriving clause may span multiple words at end of an inductive block.
DERIVING_RE = re.compile(r"\bderiving\s+[A-Za-z_][\w]*(?:\s*,\s*[A-Za-z_][\w]*)*", re.MULTILINE)

OPEN_BRACKETS = "([{⟨"
CLOSE_BRACKETS = ")]}⟩"


def _strip_comments(src: str) -> str:
    """Drop block and line comments while preserving line offsets where possible.

    Order matters: block comments first (including ``/-!``, ``/--``, ``/-``
    variants), then line comments.  Doing it in the other order can leave
    a stray ``-/`` on a line whose opener got chopped at ``--`` by the
    line-comment stripper.
    """
    src = BLOCK_COMMENT_RE.sub(
        lambda m: "\n" * m.group(0).count("\n"), src,
    )
    out_lines = []
    for ln in src.splitlines():
        i = ln.find("--")
        if i >= 0:
            ln = ln[:i].rstrip()
        out_lines.append(ln)
    return "\n".join(out_lines) + "\n"


def _strip_imports_etc(src: str) -> str:
    src = IMPORT_RE.sub("", src)
    src = SET_OPTION_RE.sub("", src)
    return src


def _strip_commands(src: str) -> str:
    """Drop ``#eval`` / ``#check`` / ``#print`` / ``#reduce`` blocks plus their
    indented continuation lines.

    A continuation line is one starting with whitespace AND whose first
    non-whitespace char isn't a top-level decl keyword.
    """
    lines = src.splitlines(keepends=True)
    out = []
    i = 0
    while i < len(lines):
        ln = lines[i]
        if COMMAND_LINE_RE.match(ln):
            # Skip this line and any subsequent purely-indented continuation lines.
            i += 1
            while i < len(lines):
                nxt = lines[i]
                if not nxt.strip():
                    out.append(nxt)  # preserve blank-line separator
                    i += 1
                    break
                # If the next non-blank line is at column 0 and looks like a
                # new declaration, stop swallowing.
                if not nxt.startswith((" ", "\t")) and not DECL_START_RE.match(nxt):
                    # leading-column line that isn't a decl — also stop.
                    # (could be another `#command` line)
                    if COMMAND_LINE_RE.match(nxt):
                        # Loop will re-enter command-stripping for it.
                        break
                    break
                if DECL_START_RE.match(nxt):
                    break
                # Continuation — drop it.
                i += 1
            continue
        out.append(ln)
        i += 1
    return "".join(out)


def _split_into_blocks(src: str) -> list[tuple[str | None, list[str]]]:
    """Split source into (decl_keyword, lines) blocks."""
    lines = src.splitlines(keepends=True)
    blocks: list[tuple[str | None, list[str]]] = []
    cur_kw: str | None = None
    cur: list[str] = []
    for ln in lines:
        m = DECL_START_RE.match(ln)
        if m:
            if cur:
                blocks.append((cur_kw, cur))
            cur_kw = m.group("kw")
            cur = [ln]
        else:
            cur.append(ln)
    if cur:
        blocks.append((cur_kw, cur))
    return blocks


def _strip_deriving(text: str) -> str:
    return DERIVING_RE.sub("", text)


def _find_top_level_separator(text: str) -> int:
    """Find the first ``:=`` that appears at bracket depth 0.

    This is the proof-body separator for theorems / def-with-term-body.
    Returns the index of the ``:`` of the ``:=`` token, or -1 if not found.

    The scan ignores ``:=`` occurrences inside parens, brackets, braces, and
    ⟨ ⟩ — those are typically default-value bindings inside hypotheses.
    """
    depth = 0
    i = 0
    in_str = False
    str_quote = ""
    while i < len(text):
        c = text[i]
        if in_str:
            if c == "\\" and i + 1 < len(text):
                i += 2
                continue
            if c == str_quote:
                in_str = False
            i += 1
            continue
        if c == '"':
            in_str = True
            str_quote = '"'
            i += 1
            continue
        if c in OPEN_BRACKETS:
            depth += 1
            i += 1
            continue
        if c in CLOSE_BRACKETS:
            depth -= 1
            i += 1
            continue
        if depth == 0 and c == ":" and i + 1 < len(text) and text[i+1] == "=":
            return i
        i += 1
    return -1


def _sorryize_proof(block_text: str) -> str:
    """Replace a theorem's proof body with ``sorry`` using depth-aware location."""
    sep = _find_top_level_separator(block_text)
    if sep < 0:
        return block_text
    head = block_text[:sep].rstrip()
    return f"{head} := sorry\n"


DECL_NAME_RE = re.compile(
    r"^\s*(?:@\[[^\]]+\]\s+)?"
    r"(?:theorem|lemma|def|abbrev|axiom|inductive|structure|class|instance)\s+"
    r"(?P<name>[A-Za-z_][\w'.]*)"
)
# Match an identifier (rough — over-matches into keywords, but used only
# against names we've explicitly tracked, so false positives are harmless).
IDENT_RE = re.compile(r"[A-Za-z_][\w'.]*")


def _decl_name(block_text: str) -> str | None:
    m = DECL_NAME_RE.match(block_text)
    return m.group("name") if m else None


def _references_any(block_text: str, names: set[str]) -> bool:
    """Return True if any tracked name appears as a token in block_text.

    Strips the declaration's own leading identifier (otherwise a theorem
    can never reference itself).  Operates on the raw text — over-matches
    are acceptable here because the tracked-name set is small and specific.
    """
    own = _decl_name(block_text)
    text = block_text
    if own:
        text = re.sub(r"^\s*(?:@\[[^\]]+\]\s+)?"
                      r"(?:theorem|lemma|def|abbrev|axiom|inductive|structure|class|instance)\s+"
                      + re.escape(own),
                      "", text)
    return any(re.search(r"\b" + re.escape(n) + r"\b", text) for n in names)


def reduce_source(src: str) -> str:
    src = _strip_comments(src)
    src = _strip_imports_etc(src)
    src = _strip_commands(src)

    blocks = _split_into_blocks(src)

    # Iterative reduction: drop blocks that reference any name we've dropped.
    # Run to fixed point so the closure of orphan dependencies is removed.
    out_blocks: list[str] = []
    dropped_names: set[str] = set()
    fixed = False
    pass_idx = 0
    keep = list(blocks)
    while not fixed and pass_idx < 5:
        fixed = True
        next_keep = []
        for kw, lines in keep:
            block_text = "".join(lines)
            name = _decl_name(block_text)
            should_drop, reason = False, ""

            if kw is None:
                if not block_text.strip():
                    continue
                next_keep.append((kw, lines))
                continue
            if kw in DROP_KEYWORDS:
                should_drop, reason = True, f"keyword {kw}"
            elif re.match(r"^\s*local\s+(macro|elab|syntax|instance)\b", block_text):
                should_drop, reason = True, "local macro/elab/syntax/instance"
            elif kw == "theorem" and DROP_ATTRIBUTE_RE.search(block_text):
                should_drop, reason = True, "attribute-tagged theorem"
            elif kw == "def" and re.search(r"^where\b", block_text, re.MULTILINE):
                should_drop, reason = True, "def with where-clause"
            elif name and dropped_names and _references_any(block_text, dropped_names):
                should_drop, reason = True, "references dropped symbol"

            if should_drop:
                fixed = False
                if name:
                    dropped_names.add(name)
                    # Also track the short name so `Tree.foo` matches `t.foo`
                    # under Lean's dot-notation.
                    if "." in name:
                        dropped_names.add(name.rsplit(".", 1)[-1])
                continue
            next_keep.append((kw, lines))
        keep = next_keep
        pass_idx += 1

    # Final per-kind transforms on the survivors.
    for kw, lines in keep:
        block_text = "".join(lines)
        if kw in {"inductive", "structure", "class"}:
            out_blocks.append(_strip_deriving(block_text))
            continue
        if kw == "theorem":
            out_blocks.append(_sorryize_proof(block_text))
            continue
        out_blocks.append(_strip_deriving(block_text))

    text = "".join(out_blocks)
    # Collapse runs of blank lines to at most two for readability.
    text = re.sub(r"\n{3,}", "\n\n", text)
    return text


def reduce_file(src_path: Path, dst_path: Path) -> tuple[int, int]:
    src_text = src_path.read_text()
    dst_text = reduce_source(src_text)
    dst_path.parent.mkdir(parents=True, exist_ok=True)
    dst_path.write_text(dst_text)
    return src_text.count("\n"), dst_text.count("\n")


ERROR_LINE_RE = re.compile(r":\d+:\d+: error(?:\([^)]*\))?:.*")


def validate(dst_path: Path, timeout: int = 30) -> tuple[bool, str]:
    """Run ``lean`` on dst_path; treat any line matching ERROR_LINE_RE as fatal.

    Pure ``sorry`` warnings + ``unused variable`` linter notes don't fail —
    they're expected after sorryization.
    """
    if shutil.which("lean") is None:
        return False, "lean not on PATH"
    try:
        proc = subprocess.run(["lean", str(dst_path)], capture_output=True,
                              text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        return False, f"lean timeout after {timeout}s"
    combined = proc.stdout + proc.stderr
    m = ERROR_LINE_RE.search(combined)
    if m:
        return False, m.group(0)
    # Exit code may be 1 from linter warnings — that's OK as long as no
    # error lines surfaced.
    return True, ""


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--task", help="restrict to one task")
    ap.add_argument("--force", action="store_true")
    ap.add_argument("--validate", action="store_true")
    args = ap.parse_args()
    ensure_lean_on_path()

    tasks = [args.task] if args.task else list_tasks()
    summary = {"reduced": 0, "cached": 0, "validate_ok": 0, "validate_fail": 0}

    for task in tasks:
        src = BENCHMARKS / task / "reference.lean"
        dst = BENCHMARKS / task / "reference_analyzable.lean"
        if not src.exists():
            print(f"  [missing] {src}")
            continue
        if dst.exists() and not args.force:
            summary["cached"] += 1
            print(f"  [cached]  {dst.relative_to(PHASE3.parent)}")
        else:
            src_n, dst_n = reduce_file(src, dst)
            summary["reduced"] += 1
            print(f"  [reduced] {task}: {src_n} → {dst_n} lines "
                  f"({100*(1-dst_n/max(src_n,1)):.0f}% smaller)")
        if args.validate:
            ok, msg = validate(dst)
            if ok:
                summary["validate_ok"] += 1
                print(f"  [valid]   {dst.relative_to(PHASE3.parent)}")
            else:
                summary["validate_fail"] += 1
                print(f"  [INVALID] {dst.relative_to(PHASE3.parent)}: {msg}")

    print(f"\nReduce stage: {summary}")
    return 0 if summary.get("validate_fail", 0) == 0 else 1


if __name__ == "__main__":
    raise SystemExit(main())
