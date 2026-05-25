#!/usr/bin/env python3
"""Phase 4 Stage 5: produce structured semantic feedback from specmut JSON.

For each baseline that has a specmut result (success or otherwise), this
stage emits a deterministic JSON record under feedback/{model}/{task}/rep_NN.json
combining:
  - components: structured diagnostic (per-theorem τ, surviving mutants with
                witnesses, missing-invariant hints derived from class-of-mutant)
  - feedback_text: the rendered prompt fragment fed to the LLM in stage 6

The text template is fixed.  Same input always produces the same output —
this is a precondition for the experiment being a clean controlled comparison.

For baselines that didn't reach analyzability (compile failure, model bound
exceeded, etc.) the feedback explains the failure mode in plain language so
the LLM has at least *some* signal to act on.
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from _common import (
    FEEDBACK,
    PHASE4,
    SPECMUT_RESULTS,
    feedback_path,
    lean_result_path,
    list_tasks,
    load_config,
    model_slots,
    replicate_indices,
    specmut_result_path,
)


# Class-of-mutant → natural-language interpretation of why this category of
# mutant tends to survive when the spec is weak.  Same text as used by Phase
# H's witness rendering, kept consistent so the LLM sees the same vocabulary.
CLASS_INTERPRETATION = {
    "weakening": (
        "The specification was weakened on this axis and still admits at least "
        "one implementation that satisfies it — the spec does not constrain "
        "this property beyond what the weaker form requires."
    ),
    "strengthening": (
        "A strictly stronger variant of an axiom remained satisfiable.  The "
        "spec admits implementations that happen to satisfy the stronger "
        "property by accident; an essential constraint is missing."
    ),
    "replacement": (
        "An axiom's predicate was substituted by a different relation and the "
        "spec still has satisfying models — the spec does not pin down which "
        "atomic predicate must hold."
    ),
}


HEADER = (
    "Mutation analysis found semantic weaknesses in your specification:\n\n"
    "Overall tightness (τ): {tau:.3f}   (0 = vacuous, 1 = fully constrained)\n"
    "Mutant kill rate: {kill_rate:.3f}\n"
    "Theorems with τ < 0.3: {weak_count}\n"
)


def _missing_invariant_hints(per_theorem: list[dict],
                             surviving: list[dict]) -> list[str]:
    """Heuristic, deterministic, content-free hints derived from mutant counts.

    We don't fabricate domain-specific advice ("add a permutation theorem")
    because that would be a confound — Phase 4 measures whether structured
    diagnostic input alone improves output, not whether explicit answers do.
    Instead we surface category-level patterns:
        - many weakening survivors → spec is broadly weak
        - many strengthening survivors → spec has accidental looseness
        - many replacement survivors → spec doesn't pin down which predicate
    """
    classes = {}
    for m in surviving:
        c = m.get("class") or m.get("mutant_class") or "unknown"
        classes[c] = classes.get(c, 0) + 1

    hints: list[str] = []
    if classes.get("weakening", 0) >= 3:
        hints.append(
            "Many weakening mutants survived: at least one theorem fails to "
            "fully constrain its predicate.  Consider adding a tighter "
            "behavioral constraint."
        )
    if classes.get("strengthening", 0) >= 3:
        hints.append(
            "Strengthened versions of your axioms remain satisfiable: the "
            "spec accepts implementations that go beyond what's stated.  Add "
            "a theorem that rules out over-constrained behavior."
        )
    if classes.get("replacement", 0) >= 3:
        hints.append(
            "Many replacement mutants survived: the spec doesn't tie its "
            "theorems to a specific predicate.  Consider explicitly relating "
            "the named predicates to the function's output."
        )
    weak_count = sum(1 for pt in per_theorem if isinstance(pt.get("tau"), (int, float))
                     and pt["tau"] < 0.3)
    if weak_count >= 1:
        hints.append(
            f"{weak_count} theorem(s) have τ < 0.3 — these theorems are likely "
            "vacuous or trivially satisfied.  Strengthen their statements."
        )
    return hints


def _format_witness_block(m: dict) -> str:
    """Render a single surviving mutant as a short block for the LLM prompt."""
    cls = m.get("mutant_class") or m.get("class") or "?"
    formula = (m.get("formula_summary") or m.get("formula") or "(no formula summary)")[:200]
    interp = CLASS_INTERPRETATION.get(cls, "Mutant survived all selected implementations.")
    return (
        f"  - class: {cls}\n"
        f"    perturbed axiom: {formula}\n"
        f"    why it survives: {interp}\n"
    )


def _extract_surviving_mutants(specmut_record: dict) -> list[dict]:
    """Pull surviving-mutant entries from either Sliced or Global mode."""
    out = []
    # Sliced mode keeps mutants nested under per_theorem; Global mode flattens
    # them at top level.  Phase 4 normalizer stores them under per_theorem
    # only when present.
    raw_per = specmut_record.get("per_theorem") or []
    for pt in raw_per:
        # Phase 4 normalization doesn't carry the raw alive_mutants list per
        # theorem; we synthesize a placeholder entry per weak theorem so the
        # feedback at least has something to point at.
        tau = pt.get("tau")
        if isinstance(tau, (int, float)) and tau < 0.7 and (pt.get("surviving_mutants") or 0) > 0:
            out.append({
                "theorem": pt.get("name", "?"),
                "class": "unknown",
                "formula": f"(theorem {pt.get('name')} survives {pt.get('surviving_mutants')} mutants)",
                "tau": tau,
            })
    return out


def _is_template_constrained() -> bool:
    """True when the active config enables the qwen-only scaffold mode.

    Used to swap the feedback text so the repair-pass LLM is not told
    "use `axiom` for the function, `def` for predicates" — which would
    instantly trigger the sanitizer's forbidden-keyword check on every
    repaired output.
    """
    try:
        return bool(load_config().get("scaffold", {}).get("enabled"))
    except Exception:
        return False


_QWEN_REPAIR_RULES_REMINDER = (
    "\n\nIMPORTANT — output grammar (unchanged from baseline):\n"
    "- Return ONLY raw Lean theorem declarations. No prose. No markdown fences.\n"
    "- Do NOT use def, axiom, inductive, lemma, example, by, match, import,\n"
    "  namespace, open, class, structure, instance — the scaffold ALREADY\n"
    "  declares the axioms and helper predicates.\n"
    "- Use the same allowed identifiers listed in the original task prompt.\n"
    "- Each theorem must end with `:= sorry`.\n"
)


def build_feedback(specmut_record: dict) -> dict:
    status = specmut_record.get("analysis_status", "unknown")
    components: dict = {
        "analysis_status": status,
        "overall_tau": specmut_record.get("average_tau", 0.0),
        "overall_kill_rate": specmut_record.get("kill_rate", 0.0),
        "weak_theorems": [
            {"name": pt["name"], "tau": pt.get("tau"),
             "issue": ("All mutants survive — no behavioral constraint imposed."
                       if pt.get("surviving_mutants") == pt.get("total_mutants")
                       else "Mutant kill rate is low.")}
            for pt in (specmut_record.get("per_theorem") or [])
            if isinstance(pt.get("tau"), (int, float)) and pt["tau"] < 0.3
        ],
        "surviving_mutants": _extract_surviving_mutants(specmut_record),
        "missing_invariant_hints": _missing_invariant_hints(
            specmut_record.get("per_theorem") or [],
            specmut_record.get("alive_mutants") or specmut_record.get("witnesses") or [],
        ),
    }

    if status in ("success", "tau_zero", "insufficient_mutations"):
        text_parts = [HEADER.format(
            tau=components["overall_tau"],
            kill_rate=components["overall_kill_rate"],
            weak_count=len(components["weak_theorems"]),
        )]
        if components["weak_theorems"]:
            text_parts.append("\nWeak theorems (τ < 0.3):\n")
            for w in components["weak_theorems"]:
                tau = w["tau"] if w["tau"] is not None else 0.0
                text_parts.append(f"  - {w['name']}: τ={tau:.3f}. {w['issue']}\n")
        if components["surviving_mutants"]:
            text_parts.append("\nSurviving mutants by theorem:\n")
            for m in components["surviving_mutants"][:8]:
                text_parts.append(_format_witness_block(m))
        if components["missing_invariant_hints"]:
            text_parts.append("\nDiagnostic hints:\n")
            for h in components["missing_invariant_hints"]:
                text_parts.append(f"  - {h}\n")
        text_parts.append(
            "\nPlease revise the specification to address these weaknesses. "
            "Add or strengthen theorems to eliminate the surviving mutants."
        )
        feedback_text = "".join(text_parts)
    elif status == "skipped_lean_failure":
        if _is_template_constrained():
            feedback_text = (
                "Your previous theorem block did not compile.  The scaffold "
                "above your output ALREADY declares the axioms and helper "
                "predicates — your job is only to write 1–2 theorem "
                "statements that typecheck against that scaffold.  Re-read "
                "the allowed-identifiers list in the prompt and rewrite the "
                "theorems using only those identifiers."
            )
        else:
            feedback_text = (
                "Your previous specification did not compile in Lean.  Please "
                "produce a self-contained Lean 4 specification that typechecks "
                "(uses `axiom` for the function, `def` for predicates, and "
                "`:= sorry` for theorem proofs).  Avoid imports beyond Lean's core."
            )
    elif status in ("model_bound_exceeded",):
        if _is_template_constrained():
            feedback_text = (
                "Your previous theorems compiled but specmut hit the model "
                "bound at n=2.  Avoid existentials (∃) and avoid any "
                "construct that mentions the axiomatic function on both "
                "sides of a membership / equality (e.g. `f xs ∈ xs`).  Use "
                "the IsMin / IsMax / Distinct / IsSorted predicate forms "
                "shown in the prompt examples."
            )
        else:
            feedback_text = (
                "Your previous specification compiled but its signature was too "
                "rich for finite-model analysis at n=2.  Keep the signature "
                "compact: avoid introducing additional auxiliary functions or "
                "polymorphic types.  Use a small set of recursive predicates "
                "and 1–2 focused theorems."
            )
    elif status in ("translation_failed", "unsupported_constructs"):
        if _is_template_constrained():
            feedback_text = (
                "Your previous theorems used constructs outside specmut's "
                "analyzable subset.  Stick to ∀ and the named predicates "
                "(IsMin / IsMax / Distinct / IsSorted).  No existentials, "
                "no polymorphism, no typeclass parameters.  See the prompt's "
                "acceptable shape examples."
            )
        else:
            feedback_text = (
                "Your previous specification used constructs outside the analyzable "
                "subset.  Avoid: inductive predicates (`inductive ... → Prop`), "
                "polymorphic type variables (`α`, `β`), and typeclass parameters "
                "(`[DecidableEq α]`).  Use monomorphic `def`-based predicates "
                "on List Nat / Nat only."
            )
    elif status == "timeout":
        feedback_text = (
            "Your previous specification took too long to analyze.  Simplify "
            "the theorem statements — drop existentials, drop nested "
            "membership over the axiomatic function."
        )
    else:
        feedback_text = (
            "Your previous specification could not be analyzed.  Please "
            "produce a simpler, more direct theorem block using only the "
            "allowed identifiers from the prompt."
        )

    if _is_template_constrained():
        feedback_text = feedback_text + _QWEN_REPAIR_RULES_REMINDER

    return {"components": components, "feedback_text": feedback_text,
            "analysis_status": status}


def process_one(model: str, task: str, replicate: int, *, force: bool) -> str:
    sm_path = specmut_result_path("baseline", model, task, replicate=replicate)
    fb_path = feedback_path(model, task, replicate)
    if fb_path.exists() and not force:
        return "cached"
    if not sm_path.exists():
        # No specmut result — derive feedback from lean_result instead.
        lr_path = lean_result_path("baseline", model, task, replicate=replicate)
        if lr_path.exists():
            lr = json.loads(lr_path.read_text())
            fb = build_feedback({"analysis_status": "skipped_lean_failure"})
            fb["source_lean_result"] = str(lr_path.relative_to(PHASE4.parent))
            fb_path.parent.mkdir(parents=True, exist_ok=True)
            fb_path.write_text(json.dumps(fb, indent=2))
            return "from_lean_failure"
        return "missing"
    sm = json.loads(sm_path.read_text())
    fb = build_feedback(sm)
    fb["source_specmut_result"] = str(sm_path.relative_to(PHASE4.parent))
    fb_path.parent.mkdir(parents=True, exist_ok=True)
    fb_path.write_text(json.dumps(fb, indent=2))
    return "ok"


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--task")
    ap.add_argument("--model")
    ap.add_argument("--replicate", type=int)
    ap.add_argument("--force", action="store_true")
    args = ap.parse_args()

    tasks = [args.task] if args.task else list_tasks()
    slots = model_slots()
    if args.model:
        slots = [s for s in slots if s[1]["name"] == args.model or s[0] == args.model]
    models = [s[1]["name"] for s in slots]
    replicates = [args.replicate] if args.replicate else list(replicate_indices())

    summary: dict[str, int] = {}
    for model in models:
        for task in tasks:
            for r in replicates:
                status = process_one(model, task, r, force=args.force)
                summary[status] = summary.get(status, 0) + 1
                print(f"  [{status:18}] {feedback_path(model, task, r).relative_to(PHASE4.parent)}")
    print(f"\nFeedback stage: {summary}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
