#!/usr/bin/env python3
"""Pure-Python static self-check for the repair-template semantic validator.

No Ollama / Lean / lake / specmut resources are touched — this
only exercises validate_repair_template.validate_repair on hand-written theorem
blocks and asserts the expected status.  Run it after editing the validator or
the templates to confirm the compliance rules still hold.

Exit code: 0 if every case matches its expectation, 1 otherwise.

Usage:
  python3 phase4/scripts/check_repair_validator_cases.py
"""

from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from repair_templates import SCAFFOLD_MARKER, get_spec
from validate_repair_template import (
    STATUS_OK,
    STATUS_REQUIRED_MISSING,
    STATUS_TOO_MANY,
    STATUS_WRONG_TASK,
    validate_repair,
)


def _block(theorems: str) -> str:
    """Wrap a theorem block as a composed file (scaffold + marker + body)."""
    return "scaffold-placeholder\n" + SCAFFOLD_MARKER + "\n" + theorems.strip()


# A baseline that differs from every repair (so the no-change rule never fires
# spuriously); contains no target function, no required core.
DIFF_BASELINE = _block("theorem baseline (xs : List Nat) : True := sorry")


# (label, task, repaired_block, expected_status_or_predicate)
#   expected may be a status string (==) or the literal "not_ok" (status != ok)
CASES = [
    # --- list_reverse ---
    ("valid list_reverse membership", "list_reverse",
     "theorem t (xs : List Nat) : ∀ y, y ∈ rev xs ↔ y ∈ xs := sorry",
     STATUS_OK),
    ("invalid list_reverse length", "list_reverse",
     "theorem t (xs : List Nat) : (rev xs).length = xs.length := sorry",
     "not_ok"),
    ("invalid list_reverse IsMax/maxOf", "list_reverse",
     "theorem t (xs : List Nat) : IsMax (maxOf xs) (rev xs) := sorry",
     "not_ok"),
    # --- set_insert ---
    ("valid set_insert membership", "set_insert",
     "theorem t (k : Nat) (xs : List Nat) : ∀ x, x ∈ setInsert k xs ↔ x = k ∨ x ∈ xs := sorry",
     STATUS_OK),
    ("set_insert Distinct-only", "set_insert",
     "theorem t (k : Nat) (xs : List Nat) : Distinct xs → Distinct (setInsert k xs) := sorry",
     "not_ok"),
    ("set_insert membership + extra", "set_insert",
     "theorem t (k : Nat) (xs : List Nat) : ∀ x, x ∈ setInsert k xs ↔ x = k ∨ x ∈ xs := sorry\n"
     "theorem e (k : Nat) (xs : List Nat) : Distinct xs → Distinct (setInsert k xs) := sorry",
     STATUS_TOO_MANY),
    # --- sorting ---
    ("valid sorting membership", "sorting",
     "theorem t (xs : List Nat) : ∀ y, y ∈ sort xs ↔ y ∈ xs := sorry",
     STATUS_OK),
    ("sorting length", "sorting",
     "theorem t (xs : List Nat) : (sort xs).length = xs.length := sorry",
     "not_ok"),
    ("sorting IsSorted-only", "sorting",
     "theorem t (xs : List Nat) : IsSorted (sort xs) := sorry",
     "not_ok"),
    ("sorting membership + extra", "sorting",
     "theorem t (xs : List Nat) : ∀ y, y ∈ sort xs ↔ y ∈ xs := sorry\n"
     "theorem e (xs : List Nat) : IsSorted (sort xs) := sorry",
     STATUS_TOO_MANY),
    # --- list_min ---
    ("valid list_min", "list_min",
     "theorem t (xs : List Nat) : IsMin (listMin xs) xs := sorry",
     STATUS_OK),
    ("list_min + second theorem", "list_min",
     "theorem t (xs : List Nat) : IsMin (listMin xs) xs := sorry\n"
     "theorem e (xs : List Nat) : IsMin (listMin xs) xs := sorry",
     STATUS_TOO_MANY),
]


def main() -> int:
    # Sanity: the validator's required cores must match the live templates,
    # so a verbatim required_template always validates ok.
    template_failures = []
    for task in ("list_min", "list_reverse", "set_insert", "sorting"):
        spec = get_spec(task)
        vr = validate_repair(_block(spec.required_template), DIFF_BASELINE, task)
        if vr.status != STATUS_OK:
            template_failures.append((task, vr.status, vr.reasons))

    failures = []
    print("repair validator static cases")
    print("-" * 72)
    for label, task, block, expected in CASES:
        vr = validate_repair(_block(block), DIFF_BASELINE, task)
        if expected == "not_ok":
            ok = (vr.status != STATUS_OK)
            exp_s = "not repair_template_ok"
        else:
            ok = (vr.status == expected)
            exp_s = expected
        mark = "PASS" if ok else "FAIL"
        if not ok:
            failures.append((label, expected, vr.status))
        print(f"  [{mark}] {label:38} -> {vr.status:32} (expected {exp_s})")

    if template_failures:
        print("\n  !! required_template does NOT self-validate:")
        for t, s, why in template_failures:
            print(f"     {t}: {s}  {why}")

    print("-" * 72)
    print("status ordering (validate_repair): "
          "empty/no-theorem -> freeform -> unknown-task -> "
          "EXACTLY-ONE (too_many) -> off-task/target -> no-change -> "
          "required-core-missing (tautology if a content-free prop is present) "
          "-> ok")

    n_fail = len(failures) + len(template_failures)
    if n_fail:
        print(f"\nRESULT: {n_fail} failure(s).")
        return 1
    print(f"\nRESULT: all {len(CASES)} cases + 4 template self-checks passed.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
