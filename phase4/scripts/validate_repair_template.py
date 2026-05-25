#!/usr/bin/env python3
"""Phase 4 — semantic validator for specmut-informed constrained repairs.

The syntax sanitizer (sanitize_generated.py) checks FORMAT: theorem-only,
`:= sorry`, no forbidden keywords, line/theorem limits.  This module checks
SEMANTICS of a repaired theorem block against the task's required stronger
theorem template and the baseline it was supposed to improve.

It is NON-BLOCKING by default: it returns a status that is recorded in the
repaired meta.json (``repair_template_status``).  The repaired .lean file is
still written and still scored by specmut, so we can observe (rather than
assume) that tautological / no-change repairs really do fail to raise tau.
The aggregator uses the recorded status to count and, optionally, to filter.

Statuses (see the spec):
  repair_template_ok
  repair_no_change
  repair_required_theorem_missing
  repair_irrelevant_tautology
  repair_wrong_task_template
  repair_forbidden_freeform
  repair_template_rejected        (empty / no theorem at all)

Entry point:
  validate_repair(repaired_theorems, baseline_theorems, task, *, config=None)
      -> RepairValidationResult
"""

from __future__ import annotations

import argparse
import json
import sys
from dataclasses import dataclass, field
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from repair_templates import (
    TAUTOLOGY_CORES,
    get_spec,
    normalize,
    strip_scaffold,
)

STATUS_OK = "repair_template_ok"
STATUS_NO_CHANGE = "repair_no_change"
STATUS_REQUIRED_MISSING = "repair_required_theorem_missing"
STATUS_TAUTOLOGY = "repair_irrelevant_tautology"
STATUS_WRONG_TASK = "repair_wrong_task_template"
STATUS_FORBIDDEN = "repair_forbidden_freeform"
STATUS_REJECTED = "repair_template_rejected"
STATUS_TOO_MANY = "repair_too_many_theorems"

# Substrings that should never appear in a theorem-only block; their presence
# means freeform Lean leaked past (defensive — the syntax sanitizer normally
# catches these first).
_FREEFORM_MARKERS = (
    "def ", "axiom ", "inductive ", "lemma ", "example ",
    ":= by", " by ", "namespace ", "structure ", "class ",
)


@dataclass
class RepairValidationResult:
    status: str
    reasons: list[str] = field(default_factory=list)
    no_change: bool = False
    required_present: bool = False
    target_fn_present: bool = False
    tautology_present: bool = False
    theorem_count: int = 0


def _has_theorem(text: str) -> bool:
    return any(ln.lstrip().startswith("theorem ") for ln in text.splitlines())


def _count_theorems(text: str) -> int:
    return sum(1 for ln in text.splitlines() if ln.lstrip().startswith("theorem "))


def validate_repair(repaired_theorems: str, baseline_theorems: str,
                    task: str, *, config: dict | None = None
                    ) -> RepairValidationResult:
    """Validate a repaired theorem block (LLM output, post-sanitizer, pre-
    scaffold) against the task's required template and the baseline block.

    ``repaired_theorems`` / ``baseline_theorems`` may be either the raw
    theorem block or a full composed .lean file; the scaffold is stripped.

    STATUS ORDERING (first match wins):
      1. empty / no theorem            -> repair_template_rejected
      2. freeform construct present    -> repair_forbidden_freeform
      2a. unknown task                 -> ok (not validated)
      2b. theorem_count != 1           -> repair_too_many_theorems
            (checked BEFORE the required-core check, so a membership theorem
             plus an extra theorem is repair_too_many_theorems, not ok)
      3. off-task forbidden core       -> repair_wrong_task_template
      4. target fn absent              -> repair_wrong_task_template
      5. identical to baseline         -> repair_no_change
            (ceiling task with the required core present is OK instead)
      6. required core missing         -> repair_irrelevant_tautology (if a
            content-free proposition is present) else
            repair_required_theorem_missing
      7. required core present         -> repair_template_ok
    """
    rep_block = strip_scaffold(repaired_theorems)
    base_block = strip_scaffold(baseline_theorems)
    spec = get_spec(task)

    res = RepairValidationResult(status=STATUS_OK)

    if not rep_block.strip() or not _has_theorem(rep_block):
        res.status = STATUS_REJECTED
        res.reasons.append("repaired block contains no theorem declaration")
        return res

    rep_norm = normalize(rep_block)
    base_norm = normalize(base_block)
    res.theorem_count = _count_theorems(rep_block)

    # 1. Freeform leak (defensive).
    for m in _FREEFORM_MARKERS:
        if m in rep_block:
            res.status = STATUS_FORBIDDEN
            res.reasons.append(f"freeform construct present: {m!r}")
            return res

    # 2. Unknown task — nothing to validate against; accept conservatively.
    if spec is None:
        res.reasons.append(f"no repair spec for task {task!r}; not validated")
        return res

    # 2b. Exactly-one-theorem rule (revised protocol).  Every task — including
    #    list_min — must emit exactly ONE theorem.  average_tau is the MEAN
    #    across theorem slices, so a second, weaker theorem only drags the
    #    repaired tau down (this is what regressed list_reverse / sorting in
    #    the first pilot).  More than one theorem is a hard reject here even
    #    though the strict syntax sanitizer (config max_theorems=2) would
    #    still let it through — the sanitizer is intentionally NOT changed.
    if res.theorem_count != 1:
        res.status = STATUS_TOO_MANY
        res.reasons.append(
            f"repaired block has {res.theorem_count} theorems; exactly 1 "
            f"required for the revised single-theorem repair protocol")
        return res

    res.target_fn_present = normalize(spec.target_fn) in rep_norm
    res.required_present = all(c in rep_norm for c in spec.required_cores)
    res.tautology_present = any(c in rep_norm for c in TAUTOLOGY_CORES)

    # 3. Off-task forbidden cores (e.g. sorting `++` append claims).
    for c in spec.forbidden_cores:
        if c in rep_norm:
            res.status = STATUS_WRONG_TASK
            res.reasons.append(f"off-task construct {c!r} present")
            return res

    # 4. Target function must appear somewhere in the block.
    if not res.target_fn_present:
        res.status = STATUS_WRONG_TASK
        res.reasons.append(
            f"target function {spec.target_fn!r} not mentioned in repaired block")
        return res

    # 5. No-change (identical to baseline).  Allowed/expected for ceiling
    #    tasks, but still reported so the aggregator can count it.
    if base_block.strip() and rep_norm == base_norm:
        res.no_change = True
        if spec.ceiling:
            # For the ceiling task an unchanged, correct lower-bound theorem
            # is the desired outcome — accept it as OK if the required core is
            # present, else fall through to the missing check below.
            if res.required_present:
                res.status = STATUS_OK
                res.reasons.append("ceiling task: unchanged required theorem (expected)")
                return res
        else:
            res.status = STATUS_NO_CHANGE
            res.reasons.append("repaired block identical to baseline")
            return res

    # 6. Required stronger theorem present?
    if not res.required_present:
        if res.tautology_present:
            res.status = STATUS_TAUTOLOGY
            res.reasons.append(
                "required theorem missing and a tautology (content-free "
                "proposition) is present")
        else:
            res.status = STATUS_REQUIRED_MISSING
            res.reasons.append(
                f"required theorem core(s) {spec.required_cores} not found")
        return res

    # 7. Required present.  A benign extra tautology alongside a strong
    #    theorem is noted but not rejected.
    res.status = STATUS_OK
    if res.tautology_present:
        res.reasons.append(
            "required theorem present; a tautological extra theorem was also "
            "detected (not rejected)")
    return res


# ---------------------------------------------------------------------------
# CLI (for manual inspection of a repaired/baseline file pair)

def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--task", required=True)
    ap.add_argument("--repaired", type=Path, required=True)
    ap.add_argument("--baseline", type=Path, default=None)
    ap.add_argument("--json", action="store_true")
    args = ap.parse_args()

    rep = args.repaired.read_text()
    base = args.baseline.read_text() if args.baseline and args.baseline.exists() else ""
    r = validate_repair(rep, base, args.task)

    if args.json:
        print(json.dumps({
            "status": r.status,
            "reasons": r.reasons,
            "no_change": r.no_change,
            "required_present": r.required_present,
            "target_fn_present": r.target_fn_present,
            "tautology_present": r.tautology_present,
            "theorem_count": r.theorem_count,
        }, indent=2))
    else:
        print(f"[{r.status}] {args.repaired}")
        for x in r.reasons:
            print(f"  - {x}")
    return 0 if r.status in (STATUS_OK,) else 1


if __name__ == "__main__":
    raise SystemExit(main())
