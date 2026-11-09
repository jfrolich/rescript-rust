//! Compilation context types.
//!
//! [`IdGenerator`] replaces OCaml's global `Ident.currentstamp`: each
//! compilation owns one (shared with its `TypeContext`), so independent
//! compilations can run concurrently.

use std::sync::atomic::{AtomicI32, Ordering};

use crate::ident::{Ident, IdentFlags};
/// Thread-safe identifier and type ID generator.
///
/// This replaces the global `Ident.currentstamp` from the OCaml implementation.
/// Multiple threads can safely generate unique identifiers concurrently.
///
/// # Example
///
/// ```rust
/// use rescript_compiler::context::IdGenerator;
///
/// let id_gen = IdGenerator::new();
/// let id1 = id_gen.create("x");
/// let id2 = id_gen.create("y");
///
/// assert_ne!(id1.stamp(), id2.stamp());
/// ```
#[derive(Debug)]
pub struct IdGenerator {
    /// Current stamp for identifiers. Starts at 0 (0 is reserved for persistent).
    current_stamp: AtomicI32,
    /// Next ID for type expressions.
    next_type_id: AtomicI32,
}

impl IdGenerator {
    /// Create a new ID generator with the current stamp at 0.
    pub fn new() -> Self {
        Self {
            current_stamp: AtomicI32::new(0),
            next_type_id: AtomicI32::new(1),
        }
    }

    /// Create a new ID generator with a specific current stamp.
    ///
    /// Useful for resuming compilation or testing.
    pub fn with_start_stamp(start: i32) -> Self {
        Self {
            current_stamp: AtomicI32::new(start.max(0)),
            next_type_id: AtomicI32::new(1),
        }
    }

    /// Increment the stamp counter and return the new current stamp.
    #[inline]
    pub fn next_stamp(&self) -> i32 {
        self.current_stamp.fetch_add(1, Ordering::Relaxed) + 1
    }

    /// Advance the stamp counter by `count` and return the new current stamp.
    #[inline]
    pub fn advance_stamp_by(&self, count: i32) -> i32 {
        if count <= 0 {
            return self.current_stamp();
        }
        self.current_stamp.fetch_add(count, Ordering::Relaxed) + count
    }

    /// Get the next type ID and increment the counter.
    #[inline]
    pub fn next_type_id(&self) -> i32 {
        self.next_type_id.fetch_add(1, Ordering::Relaxed)
    }

    /// Get the current stamp value without incrementing.
    #[inline]
    pub fn current_stamp(&self) -> i32 {
        self.current_stamp.load(Ordering::Relaxed)
    }

    /// Set the current stamp to at least the given value.
    ///
    /// This is used to synchronize stamps when loading compiled modules.
    #[inline]
    pub fn set_current_stamp(&self, t: i32) {
        // Update to max of current and t
        let mut current = self.current_stamp.load(Ordering::Relaxed);
        while t > current {
            match self.current_stamp.compare_exchange_weak(
                current,
                t,
                Ordering::Relaxed,
                Ordering::Relaxed,
            ) {
                Ok(_) => break,
                Err(c) => current = c,
            }
        }
    }

    /// Restore the stamp counter to an exact value.
    ///
    /// This is used around isolated source-fallback type checking. OCaml's
    /// compiler/ml/env.ml:669-678 builds persistent `ps_comps` while loading a
    /// different unit, but that work does not advance the current unit's later
    /// binder stamps.
    #[inline]
    pub fn restore_current_stamp(&self, stamp: i32) {
        self.current_stamp.store(stamp.max(0), Ordering::Relaxed);
    }

    /// Create a new local identifier.
    #[inline]
    pub fn create(&self, name: impl Into<crate::name::Name>) -> Ident {
        let stamp = self.next_stamp();
        Ident::new(name, stamp, IdentFlags::NONE)
    }
}

impl Default for IdGenerator {
    fn default() -> Self {
        Self::new()
    }
}

impl Clone for IdGenerator {
    /// Creates a new generator with the same current state.
    ///
    /// Note: The cloned generator will produce different stamps than the original
    /// after cloning, as they maintain independent counters.
    fn clone(&self) -> Self {
        Self {
            current_stamp: AtomicI32::new(self.current_stamp.load(Ordering::Relaxed)),
            next_type_id: AtomicI32::new(self.next_type_id.load(Ordering::Relaxed)),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Arc;

    #[test]
    fn test_id_generator_sequential() {
        let id_gen = IdGenerator::new();
        let stamps: Vec<i32> = (0..100).map(|_| id_gen.next_stamp()).collect();

        // All stamps should be unique and increasing
        for i in 1..stamps.len() {
            assert!(stamps[i] > stamps[i - 1]);
        }
    }

    #[test]
    fn test_id_generator_concurrent() {
        use std::thread;

        let id_gen = Arc::new(IdGenerator::new());
        let mut handles = vec![];

        for _ in 0..10 {
            let id_gen = id_gen.clone();
            handles.push(thread::spawn(move || {
                (0..1000).map(|_| id_gen.next_stamp()).collect::<Vec<_>>()
            }));
        }

        let all_stamps: Vec<i32> = handles
            .into_iter()
            .flat_map(|h| h.join().unwrap())
            .collect();

        // All stamps should be unique
        let unique: std::collections::HashSet<_> = all_stamps.iter().collect();
        assert_eq!(unique.len(), all_stamps.len());
    }
}
