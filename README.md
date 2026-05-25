# specmut

Specification mutation testing for measuring formal-specification tightness.

A proof only protects the property that was specified. If a specification is
weaker than the intended behavior, a verifier can certify code while leaving the
real defect untouched. `specmut` treats a specification as a set of accepted
models, generates nearby specification mutants, and measures the fraction whose
model sets differ from the original. The resulting tightness score
`τ ∈ [0, 1]` is a quantitative test for under-constraint: a tight specification
kills most nearby mutants, a loose one does not.

## What it does

- Parses first-order-logic (`.fol`) and Lean theorem statements into an internal
  logical representation.
- Generates a bounded neighborhood of specification mutants (strengthening,
  weakening, replacement).
- Compares mutant model sets against the original using bounded finite-model
  enumeration and an SMT (Z3) backend.
- Reports a tightness score, surviving mutants (as candidate weaknesses), and
  per-theorem summaries in JSON or HTML.

`specmut` does not prove theorems. For Lean input it analyzes the proposition a
theorem states, not its proof term.

## Layout

```
crates/                Rust workspace (the tool)
  specmut-core/        mutation, model enumeration, tightness metric
  specmut-smt/         Z3 backend
  specmut-parser/      FOL / Lean front ends
  specmut-lean/        Lean slicing + IR translation
  specmut-cli/         command-line binary
python/                specmut_viz: reporting / plotting package
specs/                 example specifications and implementations
phase4/                LLM specification-repair experiment (scripts + benchmarks)
```

## Build

```
cargo build --release          # binary at target/release/specmut
```

Lean analysis requires Lean 4 on `PATH` (via elan). The Python reporting layer:

```
cd python && pip install -e .
```

## Usage

Analyze a specification file and print a JSON tightness report:

```
target/release/specmut analyze specs/sorting/sort.fol -n 3 -f json
```

Analyze a Lean file (per-theorem slicing):

```
target/release/specmut analyze path/to/File.lean --lean-full -n 2 -f json
```

Key flags: `-n/--model-bound` (carrier size for model enumeration),
`-e/--epsilon` (mutation neighborhood radius), `-f/--format` (`json`/`html`),
`-o/--out` (output path).

## LLM specification-repair experiment

`phase4/` contains an experiment that tests whether mutation feedback can steer
a small code model toward tighter Lean theorem statements. Each task supplies a
Lean scaffold (axioms + helper predicates); the model emits theorem-only output,
which is sanitized, type-checked, analyzed, and in the specmut-informed
variant, repaired against a required theorem template. Pipeline stages live in
`phase4/scripts/` and are driven by `run_pipeline.py`; task definitions are under
`phase4/benchmarks/`.

## Configuration

The experiment talks to a model server over HTTP. The server URL is **not**
stored in the repo; set it in your environment before running the generation
stages:

```sh
export OLLAMA_URL=http://host:port      # your model server
export PHASE4_CONFIG=phase4/config_qwen_specmut_feedback_pilot5.toml
```

The model tag is set in the chosen `phase4/config*.toml` under `[models]`.
