//! String interning for efficient storage and sharing.
//!
//! This module provides string interning, which stores each unique string
//! only once and returns a lightweight index. When the same string is
//! interned multiple times, the same index is returned.
//!
//! This is critical for matching OCaml's behavior where identifier strings
//! are interned, causing Marshal to share them via back-references.
//!
//! # String Storage
//!
//! Strings are stored as `Rc<str>` to enable cheap sharing between entries.
//! When `push_interned()` is called for a string that already exists,
//! the Rc refcount is incremented (no heap allocation) and a NEW StrIdx
//! is returned. This gives unique indices for marshal identity while
//! avoiding duplicate string allocations.
//!
//! # Example
//!
//! ```ignore
//! use rescript_compiler::intern::Interner;
//!
//! let mut interner = Interner::new();
//! let idx1 = interner.intern("hello");
//! let idx2 = interner.intern("hello");
//! assert_eq!(idx1, idx2);  // Same string = same index
//!
//! let idx3 = interner.intern("world");
//! assert_ne!(idx1, idx3);  // Different string = different index
//!
//! assert_eq!(interner.get(idx1), "hello");
//! ```

use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::rc::Rc;

// ============================================================================
// String Index
// ============================================================================

/// Index into the string interner.
///
/// This is a lightweight 4-byte value that can be copied freely.
/// Two StrIdx values are equal if and only if they refer to the same string.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize, Default)]
pub struct StrIdx(pub u32);

impl StrIdx {
    /// Create a StrIdx from a raw u32 value.
    #[inline]
    pub fn from_raw(idx: u32) -> Self {
        StrIdx(idx)
    }

    /// Get the raw u32 value.
    #[inline]
    pub fn raw(self) -> u32 {
        self.0
    }
}

// ============================================================================
// String Interner
// ============================================================================

/// String interner that stores unique strings and returns indices.
///
/// This provides O(1) lookup of previously interned strings and guarantees
/// that identical strings get the same index via `intern()`.
///
/// For parser identifiers that need unique StrIdx values (for marshal
/// identity-based sharing), use `push_interned()` which returns a fresh
/// StrIdx but shares the underlying Rc<str> data to avoid allocation.
#[derive(Debug)]
pub struct Interner {
    /// Maps string content to StrIdx — used by `intern()` for deduplication.
    /// Only `intern()` reads/writes this map.
    map: HashMap<Rc<str>, StrIdx>,
    /// Cache for `push_interned()` — maps string content to a shared Rc<str>.
    /// Separate from `map` so that `push_interned` never affects `intern()` lookups.
    rc_cache: HashMap<Box<str>, Rc<str>>,
    /// Stores the actual strings, indexed by StrIdx
    strings: Vec<Rc<str>>,
}

impl Default for Interner {
    fn default() -> Self {
        Self::new()
    }
}

impl Interner {
    /// Create a new empty interner.
    pub fn new() -> Self {
        Self {
            map: HashMap::new(),
            rc_cache: HashMap::new(),
            strings: Vec::new(),
        }
    }

    /// Create a new interner with pre-allocated capacity.
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            map: HashMap::with_capacity(capacity),
            rc_cache: HashMap::with_capacity(capacity),
            strings: Vec::with_capacity(capacity),
        }
    }

    /// Intern a string, returning its index.
    ///
    /// If the string was previously interned, returns the existing index.
    /// Otherwise, stores the string and returns a new index.
    pub fn intern(&mut self, s: &str) -> StrIdx {
        if let Some(&idx) = self.map.get(s) {
            return idx;
        }

        let idx = StrIdx(self.strings.len() as u32);
        let rc: Rc<str> = Rc::from(s);
        self.map.insert(rc.clone(), idx);
        self.strings.push(rc);
        idx
    }

    /// Intern an owned string, returning its index.
    ///
    /// This avoids an allocation if the string is not already interned.
    pub fn intern_owned(&mut self, s: String) -> StrIdx {
        if let Some(&idx) = self.map.get(s.as_str()) {
            return idx;
        }

        let idx = StrIdx(self.strings.len() as u32);
        let rc: Rc<str> = Rc::from(s);
        self.map.insert(rc.clone(), idx);
        self.strings.push(rc);
        idx
    }

    /// Push a string without deduplication, always creating a new entry.
    ///
    /// Use this for dynamic strings (from user input/tokens) that should NOT
    /// be shared during marshalling. Each call returns a unique index.
    ///
    /// For static strings that should be shared, use `intern()` instead.
    /// For dynamic strings that should have unique indices but share storage,
    /// use `push_interned()`.
    pub fn push(&mut self, s: String) -> StrIdx {
        let idx = StrIdx(self.strings.len() as u32);
        self.strings.push(Rc::from(s));
        // Note: We don't add to the map, so this string won't be found by intern()
        idx
    }

    /// Push a string with a unique StrIdx but shared storage.
    ///
    /// Like `push()`, this always returns a NEW StrIdx (unique for marshal
    /// identity). But unlike `push()`, if the string content is already known
    /// in the interner, it shares the `Rc<str>` data instead of allocating
    /// a new string. This avoids heap allocations for duplicate identifiers.
    ///
    /// Use this for parser identifiers where:
    /// - Each occurrence needs a unique StrIdx (for marshal parity)
    /// - But the string data can be shared to save allocations
    #[inline]
    pub fn push_interned(&mut self, s: &str) -> StrIdx {
        let idx = StrIdx(self.strings.len() as u32);
        if let Some(rc) = self.rc_cache.get(s) {
            // String already seen — clone the Rc (refcount bump only, no heap alloc)
            self.strings.push(rc.clone());
        } else {
            // First time seeing this string — allocate Rc and cache it
            let rc: Rc<str> = Rc::from(s);
            self.rc_cache.insert(s.into(), rc.clone());
            self.strings.push(rc);
        }
        idx
    }

    /// Get the string for an index.
    ///
    /// # Panics
    ///
    /// Panics if the index is invalid.
    #[inline]
    pub fn get(&self, idx: StrIdx) -> &str {
        &self.strings[idx.0 as usize]
    }

    /// Get the string for an index, returning None if invalid.
    pub fn try_get(&self, idx: StrIdx) -> Option<&str> {
        self.strings.get(idx.0 as usize).map(|s| &**s)
    }

    /// Return the number of unique strings interned.
    pub fn len(&self) -> usize {
        self.strings.len()
    }

    /// Check if the interner is empty.
    pub fn is_empty(&self) -> bool {
        self.strings.is_empty()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_intern_returns_same_idx_for_same_string() {
        let mut interner = Interner::new();
        let idx1 = interner.intern("hello");
        let idx2 = interner.intern("hello");
        assert_eq!(idx1, idx2);
    }

    #[test]
    fn test_intern_returns_different_idx_for_different_string() {
        let mut interner = Interner::new();
        let idx1 = interner.intern("hello");
        let idx2 = interner.intern("world");
        assert_ne!(idx1, idx2);
    }

    #[test]
    fn test_get_returns_interned_string() {
        let mut interner = Interner::new();
        let idx = interner.intern("hello");
        assert_eq!(interner.get(idx), "hello");
    }

    #[test]
    fn test_intern_owned() {
        let mut interner = Interner::new();
        let idx1 = interner.intern_owned("hello".to_string());
        let idx2 = interner.intern("hello");
        assert_eq!(idx1, idx2);
    }

    #[test]
    fn test_len() {
        let mut interner = Interner::new();
        assert_eq!(interner.len(), 0);
        interner.intern("a");
        assert_eq!(interner.len(), 1);
        interner.intern("b");
        assert_eq!(interner.len(), 2);
        interner.intern("a"); // Already interned
        assert_eq!(interner.len(), 2);
    }

    #[test]
    fn test_push_interned_unique_idx() {
        let mut interner = Interner::new();
        let idx1 = interner.push_interned("hello");
        let idx2 = interner.push_interned("hello");
        // Different indices (unique for marshal identity)
        assert_ne!(idx1, idx2);
        // Same content
        assert_eq!(interner.get(idx1), "hello");
        assert_eq!(interner.get(idx2), "hello");
    }

    #[test]
    fn test_push_interned_does_not_pollute_intern_map() {
        let mut interner = Interner::new();
        // push_interned first
        let idx1 = interner.push_interned("hello");
        // intern should NOT find "hello" in the map — it should create fresh
        let idx2 = interner.intern("hello");
        // Different indices
        assert_ne!(idx1, idx2);
        // Same content
        assert_eq!(interner.get(idx1), "hello");
        assert_eq!(interner.get(idx2), "hello");
        // intern again returns the interned idx, not the push_interned one
        let idx3 = interner.intern("hello");
        assert_eq!(idx2, idx3);
    }
}
