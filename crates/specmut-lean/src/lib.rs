//! Lean 4 → FOL translation for specmut.
//!
//! Consumes the JSON IR produced by `lean/specmut_export.lean` (Phase A) and
//! produces a `(Signature, Vec<Formula>)` pair that
//! `specmut-cli::pipeline::run_with_signature` can drive directly.
//!
//! # Modules
//!
//! * [`ir_types`] — serde structs for the JSON IR.
//! * [`translator`] — the 5-pass `LeanTranslator` that turns IR into FOL.
//!
//! # Boundary
//!
//! This crate is intentionally Lean-binary-free.  Subprocess management and
//! Lake-project detection live in Phase C inside `specmut-cli`.  Every test
//! here reads a pre-generated JSON fixture; the `lean` toolchain is not
//! required at test time.

#![deny(rust_2018_idioms)]

pub mod analysis;
pub mod ir_types;
pub mod runner;
pub mod slicer;
pub mod translator;

pub use analysis::{
    build_neighborhood_table, ContributionStrength, MutantOutcome, MutationTaxonomy,
    NeighborhoodEntry, SliceMetrics, TheoremContribution,
};
pub use ir_types::{IRExpr, LeanIR};
pub use runner::{LeanPipelineError, LeanRunner};
pub use slicer::{slice_by_theorem, TheoremSlice};
pub use translator::{
    deduplicate_axioms, deduplicate_axioms_with_origins, filter_signature, AxiomOrigin,
    LeanTranslator, SortFilterReport, TranslationError, TranslationResult,
};
