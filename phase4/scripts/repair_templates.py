#!/usr/bin/env python3
"""Phase 4 — specmut-informed constrained repair: per-task templates + helpers.

This module is the single source of truth for the "specmut-informed
constrained repair" Experiment-B variant.  It is shared by:

  - generate_repaired.py        (builds the repair prompt)
  - validate_repair_template.py (semantic validation of the repaired block)
  - analyze_specmut_feedback.py  (reporting)

It defines, per task:
  - the mutation TARGET function name (must appear in the repaired block),
  - whether the task is a CEILING task (list_min: saturated, no improvement
    expected, identical-to-baseline is acceptable),
  - the REQUIRED stronger theorem the repair must contain (literal text shown
    to the model, plus whitespace-insensitive "cores" the validator checks),
  - per-task forbidden substrings (e.g. sorting `++` append claims),
  - a short task-specific diagnosis fed into the repair prompt.

It also builds the compact specmut result summary that is injected into the
repair prompt, so the model sees the actual mutation outcome of its previous
attempt — not just generic feedback text.

NOTE: nothing here runs Ollama / Lean / specmut.  Pure string logic.
"""

from __future__ import annotations

from dataclasses import dataclass, field

# Marker that generate_baseline.py writes between the scaffold and the
# LLM-produced theorem block.  Used to recover the theorem-only portion of a
# composed .lean file.
SCAFFOLD_MARKER = "-- ↓↓↓ qwen-only LLM-generated theorems ↓↓↓"


@dataclass(frozen=True)
class TaskRepairSpec:
    task: str
    target_fn: str
    ceiling: bool
    # Literal text the prompt instructs the model to include (the model may
    # rename the theorem; only the proposition matters to the validator).
    required_template: str
    # Whitespace-stripped substrings that must ALL be present for the required
    # theorem to be considered included.
    required_cores: tuple[str, ...]
    # Optional extra theorem the prompt offers (not validated as required).
    optional_template: str = ""
    # Whitespace-stripped substrings that, if present, mark the repair as
    # off-task (e.g. sorting append claims `xs ++ ys`).
    forbidden_cores: tuple[str, ...] = ()
    # One-line, task-specific diagnosis injected into the repair prompt.
    diagnosis: str = ""
    # Max theorems the repair should emit for this task.
    max_theorems: int = 2
    # Human-readable forbidden patterns shown in the (literal) repair prompt so
    # the model is told exactly what NOT to emit for this task.  These are
    # prompt guidance; the validator enforces correctness via required_cores.
    prompt_forbidden: tuple[str, ...] = ()


TASK_REPAIR_SPECS: dict[str, TaskRepairSpec] = {
    "list_min": TaskRepairSpec(
        task="list_min",
        target_fn="listMin",
        ceiling=True,
        required_template=(
            "theorem listMin_lower_bound_generated (xs : List Nat) :\n"
            "    IsMin (listMin xs) xs := sorry"
        ),
        required_cores=("IsMin(listMinxs)xs",),
        diagnosis=(
            "list_min is a CEILING task: the IsMin lower-bound theorem already "
            "saturates specmut at tau ~= 0.95 at n=2.  Existentials (exists) and "
            "membership of `listMin xs` OOM the analysis.  Do NOT try to add a "
            "second theorem; keep the single lower-bound theorem."
        ),
        max_theorems=1,
        prompt_forbidden=("any second theorem",),
    ),
    "list_reverse": TaskRepairSpec(
        task="list_reverse",
        target_fn="rev",
        ceiling=False,
        # REVISED after pilot 5.  The previous involution template
        # `rev (rev xs) = xs` produced a single-mutant slice with tau=0.0 and,
        # because average_tau is the MEAN across theorem slices, halved the
        # repaired tau to 0.303.  The membership/permutation shape
        # `∀ y, y ∈ rev xs ↔ y ∈ xs` was OBSERVED at tau=0.96 in a pilot
        # baseline (rev_is_permutation_generated).  Single strong theorem ->
        # highest mean tau; no weak theorem to drag it down.
        required_template=(
            "theorem rev_membership_preserved_repaired (xs : List Nat) :\n"
            "    ∀ y, y ∈ rev xs ↔ y ∈ xs := sorry"
        ),
        required_cores=("∈revxs↔",),
        optional_template="",
        diagnosis=(
            "Your previous involution template `rev (rev xs) = xs` is satisfied "
            "by the identity function and yields a single-mutant, tau=0 slice "
            "that drags the mean tau down.  The element-preservation law "
            "`∀ y, y ∈ rev xs ↔ y ∈ xs` pins down that rev keeps exactly the "
            "input elements; this scored tau≈0.96 in pilot data.  Emit ONLY "
            "this one theorem — adding a weaker second theorem lowers the mean."
        ),
        max_theorems=1,
        prompt_forbidden=(
            "`length` / `.length`", "`IsMax`", "`maxOf`",
            "`rev (rev xs)` (the involution shape)",
            "any second theorem",
        ),
    ),
    "set_insert": TaskRepairSpec(
        task="set_insert",
        target_fn="setInsert",
        ceiling=False,
        required_template=(
            "theorem setInsert_membership_repaired (k : Nat) (xs : List Nat) :\n"
            "    ∀ x, x ∈ setInsert k xs ↔ x = k ∨ x ∈ xs := sorry"
        ),
        required_cores=("∈setInsertkxs↔", "x=k∨x∈xs"),
        diagnosis=(
            "Your previous set_insert theorems were tautological or only said "
            "`Distinct` is preserved, which many wrong implementations satisfy. "
            "The membership characterization "
            "`x in setInsert k xs <-> x = k or x in xs` pins down exactly what "
            "setInsert must contain and kills the surviving mutants.  This "
            "single theorem scored tau≈0.92 in the pilot — emit ONLY it; a "
            "second, weaker theorem lowers the mean tau.  Do NOT emit "
            "content-free claims such as `x = y or x != y`."
        ),
        # Revised protocol: single-theorem repair for every task.  The pilot's
        # 2-theorem set_insert repair (membership + Distinct) averaged 0.747;
        # the membership theorem alone was 0.923.
        max_theorems=1,
        prompt_forbidden=(
            "`Distinct` (Distinct-preservation only)",
            "idempotent-only claims (e.g. `setInsert k (setInsert k xs)`)",
            "any second theorem",
        ),
    ),
    "sorting": TaskRepairSpec(
        task="sorting",
        target_fn="sort",
        ceiling=False,
        # REVISED after pilot 5.  `IsSorted (sort xs)` only scored tau=0.273
        # (a constant sorted list of the right shape satisfies it), and the
        # `(sort xs).length = xs.length` template collapsed to a single-mutant
        # tau=0 slice that halved the mean to 0.136.  By analogy to the
        # set_insert membership win (tau=0.923) and the rev permutation slice
        # (tau=0.96), the element-preservation law
        # `∀ y, y ∈ sort xs ↔ y ∈ xs` should be the strong constraint: it
        # forces sort to output exactly the input's elements.
        # NOTE: this membership shape is NOT yet observed for `sort`; it is a
        # hypothesis to be gated by `preflight_qwen_templates.py --repair`.
        required_template=(
            "theorem sort_membership_preserved_repaired (xs : List Nat) :\n"
            "    ∀ y, y ∈ sort xs ↔ y ∈ xs := sorry"
        ),
        required_cores=("∈sortxs↔",),
        optional_template="",
        forbidden_cores=("++",),
        diagnosis=(
            "Your previous sortedness/length templates were weak: "
            "`IsSorted (sort xs)` scored only tau≈0.27 (a constant sorted list "
            "satisfies it) and `(sort xs).length = xs.length` was a "
            "single-mutant tau=0 slice that halved the mean.  The "
            "element-preservation law `∀ y, y ∈ sort xs ↔ y ∈ xs` forces sort "
            "to keep exactly the input elements.  Emit ONLY this one theorem; "
            "do NOT make claims about `xs ++ ys`."
        ),
        max_theorems=1,
        prompt_forbidden=(
            "`length` / `.length`", "`IsSorted`",
            "stability-style claims", "`xs ++ ys` append claims",
            "any second theorem",
        ),
    ),
}


def get_spec(task: str) -> TaskRepairSpec | None:
    return TASK_REPAIR_SPECS.get(task)


# Whitespace-stripped tautology cores the validator rejects when they are the
# repair's only constraining content.
TAUTOLOGY_CORES: tuple[str, ...] = (
    "x=y∨x≠y",   # x = y or x != y
    "x≠y∨x=y",
    "x=x",
    "y=y",
    "a=a",
    "x∨¬x",      # x or not x
    "¬x∨x",
    ":True:=sorry",
    "↔True",          # <-> True
    "True↔",
)


def normalize(text: str) -> str:
    """Whitespace-insensitive normalization for substring matching.

    Drops `--` comment lines entirely, then removes ALL whitespace so the
    cores above match regardless of the model's formatting / binder spacing.
    Unicode logical symbols are preserved.
    """
    kept: list[str] = []
    for raw in text.splitlines():
        code = raw.split("--", 1)[0]
        kept.append(code)
    joined = "".join(kept)
    return "".join(joined.split())


def strip_scaffold(file_text: str) -> str:
    """Return only the LLM theorem block from a composed .lean file.

    Splits on SCAFFOLD_MARKER; if absent, returns the input unchanged (the
    file was never scaffold-composed).
    """
    if SCAFFOLD_MARKER in file_text:
        return file_text.split(SCAFFOLD_MARKER, 1)[1].strip()
    return file_text.strip()


# ---------------------------------------------------------------------------
# specmut summary for the prompt

def build_specmut_summary(record: dict | None, task: str) -> str:
    """Compact, deterministic textual summary of a baseline specmut record.

    Designed to be short enough to fit the repair prompt while carrying the
    signal the model needs: overall tau, status, mutant kill counts, and the
    per-theorem tau breakdown (which theorem is weak).
    """
    if record is None:
        return ("MUTATION ANALYSIS: unavailable (no specmut result for the "
                "baseline attempt).")

    status = record.get("analysis_status", "unknown")
    lines = ["MUTATION ANALYSIS of your previous attempt (specmut):"]
    lines.append(f"  analysis_status : {status}")

    if status not in ("success", "tau_zero", "insufficient_mutations"):
        # Non-analyzable baseline: report the failure mode only.
        if record.get("specmut_error"):
            lines.append(f"  error           : {record['specmut_error']}")
        lines.append(
            "  (the previous attempt was not analyzable; produce the required "
            "theorem below so the revised attempt is analyzable AND strong.)")
        return "\n".join(lines)

    tau = record.get("average_tau", 0.0)
    kr = record.get("kill_rate", 0.0)
    killed = record.get("killed_mutants", 0)
    surviving = record.get("surviving_mutants", 0)
    total = record.get("total_mutants", 0)
    lines.append(f"  baseline tau    : {tau:.3f}   (0 = vacuous, 1 = fully constrained)")
    lines.append(f"  mutant kill rate: {kr:.3f}   ({killed} killed / {surviving} survived / {total} total)")

    per = record.get("per_theorem") or []
    if per:
        lines.append("  per-theorem:")
        for pt in per[:6]:
            name = pt.get("name", "?")
            t = pt.get("tau")
            sm = pt.get("surviving_mutants")
            if isinstance(t, (int, float)):
                lines.append(f"    - {name}: tau={t:.3f}, survived={sm}")
            else:
                st = pt.get("slice_status", "skipped")
                lines.append(f"    - {name}: not analyzed ({st})")
    weak = record.get("weak_theorems") or []
    if weak:
        lines.append(f"  weak theorems (tau < 0.3): {', '.join(str(w) for w in weak)}")
    return "\n".join(lines)


# ---------------------------------------------------------------------------
# repair prompt

_GRAMMAR_REMINDER = (
    "OUTPUT GRAMMAR (HARD — unchanged from baseline):\n"
    "- Return ONLY raw Lean theorem declarations. No prose. No markdown fences.\n"
    "- Do NOT emit def, axiom, inductive, lemma, example, by, match, import,\n"
    "  namespace, open, class, structure, instance, abbrev, notation, #check.\n"
    "  The scaffold ALREADY declares the axioms and helper predicates and will\n"
    "  be prepended automatically.\n"
    "- Use ONLY the identifiers listed in the task prompt above.\n"
    "- Every theorem must end with `:= sorry`.\n"
)


_LITERAL_INSTRUCTIONS = (
    "You must output EXACTLY ONE Lean theorem.\n"
    "Copy the required theorem shape exactly.\n"
    "Do not invent a different property.\n"
    "Do not add a second theorem.\n"
    "Do not include explanations, markdown, comments, imports, definitions, "
    "axioms, examples, helper lemmas, or proofs.\n"
    "The theorem must end with := sorry.\n"
    "Any output that does not match the exact required theorem shape will be "
    "rejected and counted as invalid."
)


def build_repair_prompt(*, task: str, base_prompt: str,
                        baseline_theorems: str, specmut_summary: str,
                        feedback_text: str) -> str:
    """Compose the specmut-informed constrained repair prompt.

    Structure:
      <strict task grammar prompt>
      <your previous theorem block>
      <specmut mutation analysis of that block>
      <generic diagnostic feedback>           (from generate_feedback.py)
      <task-specific diagnosis>
      <REQUIRED stronger theorem template>
      <grammar reminder>
    """
    spec = get_spec(task)
    parts: list[str] = [base_prompt.rstrip(), ""]

    parts.append("Your previous theorem block was:")
    parts.append("```lean")
    parts.append(baseline_theorems.strip() or "(empty / rejected)")
    parts.append("```")
    parts.append("")
    parts.append(specmut_summary.strip())
    parts.append("")

    if feedback_text.strip():
        parts.append("Diagnostic feedback:")
        parts.append(feedback_text.strip())
        parts.append("")

    if spec is not None:
        if spec.diagnosis:
            parts.append("TASK-SPECIFIC DIAGNOSIS:")
            parts.append(spec.diagnosis.strip())
            parts.append("")

        # Literal, unambiguous instruction block (compliance-gated protocol).
        parts.append(_LITERAL_INSTRUCTIONS)
        parts.append("")

        if spec.prompt_forbidden:
            parts.append(f"For the `{spec.task}` task, you MUST NOT use:")
            for f in spec.prompt_forbidden:
                parts.append(f"  - {f}")
            parts.append("")

        parts.append("THE REQUIRED THEOREM (output exactly this shape, "
                     "you may keep the name):")
        parts.append("```lean")
        parts.append(spec.required_template)
        parts.append("```")
        parts.append("")

    parts.append(_GRAMMAR_REMINDER)
    parts.append(
        "Now output the one required theorem and nothing else. Begin with "
        "`theorem ` on the first line.")
    return "\n".join(parts)
