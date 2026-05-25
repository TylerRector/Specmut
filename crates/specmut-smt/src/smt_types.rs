//! Solver-agnostic types shared by the SMT bridge.

use specmut_core::formula::Formula;
use specmut_core::signature::Signature;

/// Three-valued outcome of a satisfiability query.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SmtResult {
    /// The formula is satisfiable.
    Sat,
    /// The formula is unsatisfiable.
    Unsat,
    /// The solver returned without a definitive answer (e.g. timeout).
    Unknown,
}

/// Solver-side description of a model returned by [`SmtSolver::get_model`].
///
/// Phase 4 returns only the solver's textual representation; building a
/// full [`specmut_core::model::FiniteModel`] from a Z3 model is deferred.
#[derive(Debug, Clone)]
pub struct SmtModel {
    /// Solver-supplied textual description of the model.
    pub description: String,
}

/// Configuration for the Z3 backend.
#[derive(Debug, Clone)]
pub struct Z3Config {
    /// Per-query timeout in milliseconds.
    pub timeout_ms: u64,
    /// Optional SMT-LIB logic name (e.g. `"QF_UF"`).
    pub logic: Option<String>,
    /// Random seed for reproducible behavior.
    pub seed: u64,
}

impl Default for Z3Config {
    fn default() -> Self {
        Self {
            timeout_ms: 5000,
            logic: None,
            seed: 42,
        }
    }
}

/// Trait abstracting over SMT solver backends.
///
/// All query methods take an explicit [`Signature`] because the
/// translation needs sort and function-symbol declarations the formula
/// itself does not carry.
pub trait SmtSolver: Send + Sync {
    /// Check satisfiability of `formula` under `sig`.
    fn check_sat(&self, formula: &Formula, sig: &Signature) -> SmtResult;

    /// Check whether `premises` together entail `conclusion`.  Returns
    /// `true` only on definitive `Unsat` of `premises ∧ ¬conclusion`;
    /// `Sat` or `Unknown` both yield `false` (conservative).
    fn check_entailment(
        &self,
        premises: &[Formula],
        conclusion: &Formula,
        sig: &Signature,
    ) -> bool;

    /// Check whether two specs have the same model set — symmetric
    /// pairwise entailment.
    fn check_equivalence(&self, s1: &[Formula], s2: &[Formula], sig: &Signature) -> bool;

    /// Extract a model for `formula` if it is satisfiable.
    fn get_model(&self, formula: &Formula, sig: &Signature) -> Option<SmtModel>;
}
