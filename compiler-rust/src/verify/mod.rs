//! Checks beyond types (docs/verify): purity.
//!
//! The parser records whether a file has an attribute these checks read, so
//! a file without one pays nothing.

pub mod purity;

/// Whether an attribute name asks for a check of this module.
pub fn is_verify_attribute(name: &str) -> bool {
    purity::is_effect_attribute(name)
}
