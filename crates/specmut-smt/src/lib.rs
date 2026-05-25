//! Z3 / SMT bridge for the specmut framework.
//!
//! See §3.9 and §6 of the specification document.

pub mod smt_types;
pub mod z3_bridge;

pub use smt_types::{SmtModel, SmtResult, SmtSolver, Z3Config};
pub use z3_bridge::{Z3EntailmentChecker, Z3Solver};
