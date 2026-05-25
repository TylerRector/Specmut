//! Z3-first entailment checker with model-enumeration fallback.
//!
//! Z3 returns three values: `Sat`, `Unsat`, and `Unknown`.  The
//! `EntailmentChecker` trait in `specmut-core` is boolean, so a wrapper
//! that strictly forwards to Z3 must collapse `Unknown` to one of the
//! two answers — typically `false` (conservative).  That loses
//! information whenever the formula sits just outside Z3's decidable
//! fragment.  The hybrid checker keeps that information: on `Unknown`
//! it consults a model-enumeration checker instead, and increments a
//! shared atomic counter so the CLI can report how often the fallback
//! fired.

use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;

use specmut_core::formula::Formula;
use specmut_core::lattice::{EntailmentChecker, ModelEntailmentChecker};
use specmut_core::model::FiniteModel;
use specmut_core::signature::Signature;
use specmut_smt::smt_types::SmtResult;
use specmut_smt::z3_bridge::Z3Solver;
use specmut_smt::Z3Config;

/// Z3-first entailment checker.  See module docs.
pub struct HybridEntailmentChecker {
    solver: Z3Solver,
    signature: Signature,
    model_fallback: ModelEntailmentChecker,
    fallback_count: Arc<AtomicUsize>,
}

impl HybridEntailmentChecker {
    /// Build a hybrid checker with the given Z3 configuration and a
    /// pre-enumerated model set as the fallback backend.  The returned
    /// checker increments `fallback_count` once per `Unknown` per
    /// conclusion formula.
    pub fn new(
        signature: Signature,
        models: Vec<FiniteModel>,
        timeout_ms: u64,
        logic: Option<String>,
        fallback_count: Arc<AtomicUsize>,
    ) -> Self {
        let config = Z3Config {
            timeout_ms,
            logic,
            seed: 42,
        };
        Self {
            solver: Z3Solver::new(config),
            signature,
            model_fallback: ModelEntailmentChecker::new(models),
            fallback_count,
        }
    }
}

impl EntailmentChecker for HybridEntailmentChecker {
    fn entails(&self, stronger: &[Formula], weaker: &[Formula]) -> bool {
        // The trait contract is "every model of stronger is a model of
        // weaker".  We check that conclusion-by-conclusion: for each
        // formula `w` in `weaker`, the Z3 query `stronger ∧ ¬w` must be
        // `Unsat` for entailment to hold.
        for w in weaker {
            match self
                .solver
                .check_entailment_raw(stronger, w, &self.signature)
            {
                SmtResult::Unsat => continue,
                SmtResult::Sat => return false,
                SmtResult::Unknown => {
                    self.fallback_count.fetch_add(1, Ordering::Relaxed);
                    if !self
                        .model_fallback
                        .entails(stronger, std::slice::from_ref(w))
                    {
                        return false;
                    }
                }
            }
        }
        true
    }
}
