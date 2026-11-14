//! New checker boundary. R0 deliberately cannot produce a checked unit.

#[cfg(test)]
pub(crate) mod steps;

use std::convert::Infallible;

/// Closed set of reasons a unit must take the old road, before any effects.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Declined {
    NotBuilt,
}

/// O(1), with no allocations, warnings, writes or publication.
/// The uninhabited success type prevents a stub from pretending to check a unit.
pub(crate) fn check_unit() -> Result<Infallible, Declined> {
    Err(Declined::NotBuilt)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn not_built_cannot_publish() {
        assert_eq!(check_unit(), Err(Declined::NotBuilt));
        assert_eq!(std::mem::size_of::<Declined>(), 0);
    }
}

pub mod graph;
pub mod level;
pub mod template;

pub mod segment;
pub mod publish;
pub mod bridge;

pub mod canonical;

// R3 skeleton: bodies are `todo!`, so parameters are unused and an output
// vector looks like a slice to clippy. Each build slice removes the
// allowance from the module it completes (CHECKER_REWRITE.md, "R3 as
// designed").
pub mod expand;
#[allow(dead_code, unused_variables, clippy::ptr_arg)]
pub mod relate;
#[allow(dead_code, unused_variables, clippy::ptr_arg)]
pub mod rows;
#[allow(dead_code, unused_variables, clippy::ptr_arg)]
pub mod unify;

// R4 skeleton: bodies are `todo!`. Each build slice removes the allowance
// from the module it completes (CHECKER_REWRITE.md, "R4 as designed").
pub mod name_table;
#[allow(dead_code, unused_variables, clippy::ptr_arg)]
pub mod names;
#[allow(dead_code, unused_variables, clippy::ptr_arg)]
pub mod scope;

// The old environment's report of its bindings, opens and lookups, for the
// R4 oracle. Not compiled without debug assertions.
#[cfg(debug_assertions)]
pub(crate) mod scope_trace;
// The R4 oracle: the trace replayed on `Scopes`, under `RESCRIPT_CHECKER=both`
// in builds with debug assertions.
#[cfg(debug_assertions)]
pub(crate) mod scope_oracle;

#[cfg(test)]
mod differential;
#[cfg(test)]
mod r3_tests;
// The R4 tests read the old environment's trace, which exists with debug
// assertions only.
#[cfg(all(test, debug_assertions))]
mod r4_tests;
