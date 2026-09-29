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
//! Strings are stored as `Box<str>` for minimal overhead (one pointer + one
//! length, no refcount). `push_interned()` always allocates a fresh `Box<str>`
//! and returns a unique StrIdx — this gives unique indices for marshal identity.
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
/// StrIdx with its own `Box<str>` allocation.
#[derive(Debug)]
pub struct Interner {
    /// `StrIdx` of each string deduplicated by `intern()`, keyed by content.
    /// Only `intern()`/`intern_owned()` read or write this table.
    table: hashbrown::HashTable<StrIdx>,
    hasher: ahash::RandomState,
    /// All strings back to back; `spans[idx]` is the byte range of `idx`.
    /// One buffer instead of an allocation per string.
    bytes: String,
    spans: Vec<(u32, u32)>,
}

impl Default for Interner {
    fn default() -> Self {
        Self::new()
    }
}

fn interner_hasher() -> ahash::RandomState {
    ahash::RandomState::with_seeds(
        0x243f_6a88_85a3_08d3,
        0x1319_8a2e_0370_7344,
        0xa409_3822_299f_31d0,
        0x082e_fa98_ec4e_6c89,
    )
}

impl Interner {
    /// Create a new empty interner.
    pub fn new() -> Self {
        Self {
            table: hashbrown::HashTable::new(),
            hasher: interner_hasher(),
            bytes: String::new(),
            spans: Vec::new(),
        }
    }

    /// Create a new interner with pre-allocated capacity.
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            table: hashbrown::HashTable::with_capacity(capacity),
            hasher: interner_hasher(),
            bytes: String::with_capacity(capacity * 8),
            spans: Vec::with_capacity(capacity),
        }
    }

    #[inline]
    fn push_str(&mut self, s: &str) -> StrIdx {
        let idx = StrIdx(self.spans.len() as u32);
        let start = self.bytes.len();
        self.bytes.push_str(s);
        let end = self.bytes.len();
        assert!(end <= u32::MAX as usize, "interned strings exceed 4 GiB");
        self.spans.push((start as u32, end as u32));
        idx
    }

    /// Intern a string, returning its index.
    ///
    /// If the string was already interned with `intern()`, returns the existing index.
    pub fn intern(&mut self, s: &str) -> StrIdx {
        let hash = self.hasher.hash_one(s);
        let (bytes, spans) = (&self.bytes, &self.spans);
        let span_str = |idx: StrIdx| {
            let (start, end) = spans[idx.0 as usize];
            &bytes[start as usize..end as usize]
        };
        if let Some(&idx) = self.table.find(hash, |&idx| span_str(idx) == s) {
            return idx;
        }
        let idx = self.push_str(s);
        let (bytes, spans, hasher) = (&self.bytes, &self.spans, &self.hasher);
        self.table.insert_unique(hash, idx, |&idx| {
            let (start, end) = spans[idx.0 as usize];
            hasher.hash_one(&bytes[start as usize..end as usize])
        });
        idx
    }

    /// Intern an owned string, returning its index.
    pub fn intern_owned(&mut self, s: String) -> StrIdx {
        self.intern(&s)
    }

    /// Push a string without deduplication, always creating a new entry.
    ///
    /// Use this for dynamic strings (from user input/tokens) that should NOT
    /// be shared during marshalling. Each call returns a unique index.
    ///
    /// For static strings that should be shared, use `intern()` instead.
    /// For dynamic strings that should have unique indices, use `push_interned()`.
    pub fn push(&mut self, s: String) -> StrIdx {
        // Not added to the table, so this string won't be found by intern().
        self.push_str(&s)
    }

    /// Push a string with a unique StrIdx.
    ///
    /// Like `push()`, this always returns a NEW StrIdx (unique for marshal
    /// identity).
    ///
    /// Use this for parser identifiers where each occurrence needs a unique
    /// StrIdx (for marshal parity).
    #[inline]
    pub fn push_interned(&mut self, s: &str) -> StrIdx {
        self.push_str(s)
    }

    /// Get the string for an index.
    ///
    /// # Panics
    ///
    /// Panics if the index is invalid.
    #[inline]
    #[inline]
    pub fn get(&self, idx: StrIdx) -> &str {
        let (start, end) = self.spans[idx.0 as usize];
        &self.bytes[start as usize..end as usize]
    }

    /// Get the string for an index, returning None if invalid.
    pub fn try_get(&self, idx: StrIdx) -> Option<&str> {
        let &(start, end) = self.spans.get(idx.0 as usize)?;
        Some(&self.bytes[start as usize..end as usize])
    }

    /// Return the number of strings (interned or pushed).
    pub fn len(&self) -> usize {
        self.spans.len()
    }

    /// Reserve storage for additional strings without changing existing indices.
    pub fn reserve(&mut self, additional: usize) {
        self.spans.reserve(additional);
    }

    /// Check if the interner is empty.
    pub fn is_empty(&self) -> bool {
        self.spans.is_empty()
    }

    /// Copy of every string by index, without the deduplication table.
    pub fn snapshot(&self) -> InternedStrings {
        InternedStrings {
            bytes: self.bytes.clone(),
            spans: self.spans.clone(),
        }
    }
}

/// Read-only copy of an `Interner`'s strings (see `Interner::snapshot`).
#[derive(Debug, Clone, Default)]
pub struct InternedStrings {
    bytes: String,
    spans: Vec<(u32, u32)>,
}

impl InternedStrings {
    /// The string at `idx`, if the snapshot has it.
    pub fn get(&self, idx: StrIdx) -> Option<&str> {
        let &(start, end) = self.spans.get(idx.0 as usize)?;
        Some(&self.bytes[start as usize..end as usize])
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
