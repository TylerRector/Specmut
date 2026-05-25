//! `specmut-core` — Phase 1 of the lattice-theoretic specification mutation
//! testing framework.
//!
//! This crate provides the foundational algebraic types over which the rest of
//! the pipeline is built: first-order signatures, NNF-normalized formulas with
//! de Bruijn indexing, and finite Σ-structures together with an enumerator and
//! evaluator. There is no I/O, no SMT integration, and no randomness — every
//! operation is deterministic.

pub mod cegis;
pub mod formula;
pub mod lattice;
pub mod metric;
pub mod model;
pub mod mutation;
pub mod signature;
pub mod tightness;

pub use cegis::{CegisEvaluator, CegisState};
pub use formula::{Formula, Term};
pub use lattice::{
    EntailmentChecker, LatticeConstructionError, ModelEntailmentChecker, SpecElement, SpecLattice,
};
pub use metric::{DistanceResult, JaccardMetric};
pub use model::{FiniteModel, ModelEnumerator};
pub use mutation::{Mutant, MutantClass, MutationGenerator, MutationResult};
pub use signature::{FunctionSymbol, RelationSymbol, Signature, SignatureError, SortSymbol};
pub use tightness::{MutantStatus, TightnessEvaluator, TightnessResult};
