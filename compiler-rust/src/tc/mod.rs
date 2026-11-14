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

// R3 skeleton: each build slice removes the allowance from the module it
// completes (CHECKER_REWRITE.md, "R3 as designed").
#[allow(dead_code, unused_variables)]
pub mod expand;
#[allow(dead_code, unused_variables)]
pub mod relate;
#[allow(dead_code, unused_variables)]
pub mod rows;
#[allow(dead_code, unused_variables)]
pub mod unify;

#[cfg(test)]
mod differential;
