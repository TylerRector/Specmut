//! Process exit codes used by the CLI.  Mirrors §8.2.

/// Successful run.
pub const SUCCESS: i32 = 0;
/// Parse error in the input spec.
pub const PARSE_ERROR: i32 = 1;
/// Signature error (undefined sort, duplicate, etc.) — Phase 5 routes
/// these through `PARSE_ERROR`'s sibling because they originate in the
/// parser layer; this constant is reserved for direct signature failures
/// downstream of parsing.
#[allow(dead_code)]
pub const SIGNATURE_ERROR: i32 = 2;
/// SMT backend unavailable.  Reserved; not used in Phase 5.
#[allow(dead_code)]
pub const SMT_UNAVAILABLE: i32 = 3;
/// Model bound produced a model space too large for the configured
/// memory budget.
pub const MODEL_BOUND_EXCEEDED: i32 = 4;
/// Configuration file error.
pub const CONFIG_ERROR: i32 = 5;
/// Internal error / invariant violation.  Returned when a panic escaped
/// the main pipeline.
pub const INTERNAL_ERROR: i32 = 10;
