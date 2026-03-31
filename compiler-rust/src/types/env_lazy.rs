//! Lazy module component building, matching OCaml's EnvLazy.
//!
//! In OCaml, module components are built lazily via `EnvLazy.force`.
//! The first `get_components` call forces `components_of_module_maker`,
//! which triggers `scrape_alias → find_module → ps_sig` cascade.
//! This cascade forces `ps_sig` renames at the exact right point
//! in the stamp sequence.

use std::cell::RefCell;
use std::collections::HashMap;

use crate::types::context::TypeContext;
use crate::types::decl::Signature;

/// Tracks which modules have had their components "built" (forced).
/// When a module is first accessed for value lookup, its components
/// are built, which triggers the ps_sig rename cascade.
///
/// This matches OCaml's `get_components → EnvLazy.force(components_of_module_maker)`.
pub struct ModuleComponentTracker {
    /// Modules whose components have been built (forced).
    forced: RefCell<HashMap<String, bool>>,
}

impl ModuleComponentTracker {
    pub fn new() -> Self {
        Self {
            forced: RefCell::new(HashMap::new()),
        }
    }

    /// Check if a module's components have been forced.
    pub fn is_forced(&self, name: &str) -> bool {
        self.forced.borrow().get(name).copied().unwrap_or(false)
    }

    /// Mark a module's components as forced.
    pub fn mark_forced(&self, name: &str) {
        self.forced.borrow_mut().insert(name.to_string(), true);
    }
}
