//! Checks beyond types (docs/verify): purity, laws and their proofs, and
//! specs.
//!
//! The parser records whether a file has an attribute these checks read, so
//! a file without one pays nothing.

pub mod laws;
mod prove;
pub mod purity;
pub mod shape;
pub mod specs;

use std::sync::{Arc, Mutex};

/// Whether an attribute name asks for a check of this module.
pub fn is_verify_attribute(name: &str) -> bool {
    purity::is_effect_attribute(name) || is_check_attribute(name)
}

/// Whether an attribute name marks a binding as a check (`@law`, `@spec`):
/// a statement about the program that is no part of it.
pub fn is_check_attribute(name: &str) -> bool {
    name == laws::LAW || name == specs::SPEC
}

/// What a compile does with the checks of a file.
#[derive(Debug, Clone, Default)]
pub enum Checks {
    /// Type check them and leave them out of the JavaScript, as a build
    /// does.
    #[default]
    LeftOut,
    /// Compile them into the JavaScript as exports, ignoring the file's
    /// interface, and describe each one here, as `rescript verify` does.
    Kept(Arc<Mutex<Vec<laws::Item>>>),
}

impl Checks {
    /// Keep the checks, with an empty list for their descriptions.
    pub fn kept() -> Self {
        Checks::Kept(Arc::new(Mutex::new(Vec::new())))
    }

    /// Whether checks are compiled into the JavaScript.
    pub fn are_kept(&self) -> bool {
        matches!(self, Checks::Kept(_))
    }
}
