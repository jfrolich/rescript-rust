//! Identifier types and operations.
//!
//! This module provides the core [`Ident`] type used throughout the compiler
//! to represent identifiers with unique stamps for disambiguation.
//!
//! # Concurrency
//!
//! Unlike the OCaml implementation which uses a global `currentstamp` counter,
//! this implementation requires an [`IdGenerator`] to be passed explicitly.
//! This enables concurrent compilation of multiple files. The legacy
//! [`Ident::create_local`] counter is thread-local so parallel in-process
//! compilations can reset OCaml-style stamps without racing each other.
//!
//! # Example
//!
//! ```rust
//! use rescript_compiler::ident::Ident;
//! use rescript_compiler::context::IdGenerator;
//!
//! let id_gen = IdGenerator::new();
//! let id1 = id_gen.create("x");
//! let id2 = id_gen.create("x");
//!
//! // Same name but different stamps
//! assert_eq!(id1.name(), "x");
//! assert_eq!(id2.name(), "x");
//! assert_ne!(id1.stamp(), id2.stamp());
//! assert!(!id1.same(&id2));  // Different identifiers
//! ```

use crate::name::Name;
use serde::{Deserialize, Serialize};
use std::cell::{Cell, RefCell};
use std::fmt;
use std::hash::{Hash, Hasher};

thread_local! {
    static LOCAL_IDENT_COUNTER: Cell<i32> = const { Cell::new(0) };
    /// While a published signature is encoded (`saving_store_stamps`).
    static SAVED_STORE_STAMPS: RefCell<Option<SavedStoreStamps>> = const { RefCell::new(None) };
}

/// First stamp of the binders of a worker's shared type store
/// (`types::thread_store::next_store_stamp`). Compilation-local stamps stay
/// far below it.
pub const STORE_STAMP_BASE: i32 = 1 << 29;

struct SavedStoreStamps {
    stamps: crate::fast_hash::AHashMap<i32, i32>,
    /// A store stamp missing from `stamps` was encoded.
    unmapped: bool,
}

/// Run `encode` with identifiers whose stamp is a store stamp in `stamps`
/// serialized with the stamp it maps to. Returns `encode`'s result and
/// whether an identifier with a store stamp missing from `stamps` was
/// serialized (it is serialized unchanged).
///
/// Used to save a compilation's signature with the local stamps its store
/// binders stand for (see `TypeContext::saved_store_stamps`).
pub fn saving_store_stamps<R>(
    stamps: crate::fast_hash::AHashMap<i32, i32>,
    encode: impl FnOnce() -> R,
) -> (R, bool) {
    let outer = SAVED_STORE_STAMPS.with(|saved| {
        saved.replace(Some(SavedStoreStamps {
            stamps,
            unmapped: false,
        }))
    });
    let result = encode();
    let saved = SAVED_STORE_STAMPS.with(|saved| saved.replace(outer));
    (result, saved.is_some_and(|saved| saved.unmapped))
}

/// The stamp a store-range `stamp` is serialized with.
#[cold]
fn saved_store_stamp(stamp: i32) -> i32 {
    SAVED_STORE_STAMPS.with(|saved| match saved.borrow_mut().as_mut() {
        Some(saved) => saved.stamps.get(&stamp).copied().unwrap_or_else(|| {
            saved.unmapped = true;
            stamp
        }),
        None => stamp,
    })
}

/// Flags for identifier properties.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default, Serialize, Deserialize)]
pub struct IdentFlags(u8);

impl IdentFlags {
    /// No flags set.
    pub const NONE: Self = Self(0);
    /// Identifier is global.
    pub const GLOBAL: Self = Self(1);
    /// Identifier is a predefined exception.
    pub const PREDEF_EXN: Self = Self(2);
    /// Identifier denotes a hard-coded JavaScript API binding.
    pub const JS: Self = Self(8);
    /// Identifier denotes a JavaScript object binding.
    pub const JS_OBJECT: Self = Self(32);

    /// Check if the global flag is set.
    #[inline]
    pub fn is_global(self) -> bool {
        self.0 & Self::GLOBAL.0 != 0
    }

    /// Check if the predefined exception flag is set.
    #[inline]
    pub fn is_predef_exn(self) -> bool {
        self.0 & Self::PREDEF_EXN.0 != 0
    }

    /// Whether this identifier denotes a JavaScript binding.
    #[inline]
    pub fn is_js(self) -> bool {
        self.0 & Self::JS.0 != 0
    }

    #[inline]
    pub(crate) fn bits(self) -> u8 {
        self.0
    }

    /// Set the global flag.
    #[inline]
    pub fn with_global(self) -> Self {
        Self(self.0 | Self::GLOBAL.0)
    }

    /// Set the predefined exception flag.
    #[inline]
    pub fn with_predef_exn(self) -> Self {
        Self(self.0 | Self::PREDEF_EXN.0)
    }

    /// Create from raw bits (truncating any unknown bits).
    #[inline]
    pub fn from_bits_truncate(bits: u8) -> Self {
        Self(bits & 0x2b)
    }
}

/// A unique identifier with a name and stamp.
///
/// Identifiers are used throughout the compiler to represent variables,
/// types, modules, and other named entities. Each identifier has:
///
/// - A `name`: The string representation
/// - A `stamp`: A unique integer for disambiguation
/// - `flags`: Properties like global or predefined exception
///
/// # Stamp Semantics
///
/// - `stamp > 0`: A local identifier created by `create`
/// - `stamp = 0`: A persistent (global) identifier
/// - `stamp = -1`: A hidden identifier
///
/// # Equality
///
/// Two identifiers are considered the "same" (`same` method) if:
/// - Both have non-zero stamps and the stamps are equal, OR
/// - Both have stamp 0 and the names are equal
#[derive(Clone, Copy, Deserialize)]
pub struct Ident {
    name: Name,
    stamp: i32,
    flags: IdentFlags,
}

impl Serialize for Ident {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        /// The derived encoding of `Ident`.
        #[derive(Serialize)]
        #[serde(rename = "Ident")]
        struct Repr<'a> {
            name: &'a Name,
            stamp: i32,
            flags: IdentFlags,
        }
        let stamp = if self.stamp >= STORE_STAMP_BASE {
            saved_store_stamp(self.stamp)
        } else {
            self.stamp
        };
        Repr {
            name: &self.name,
            stamp,
            flags: self.flags,
        }
        .serialize(serializer)
    }
}

impl Ident {
    /// Create a new identifier with explicit stamp and flags.
    ///
    /// Prefer using [`IdGenerator::create`] for normal identifier creation.
    #[inline]
    pub fn new(name: impl Into<Name>, stamp: i32, flags: IdentFlags) -> Self {
        Self {
            name: name.into(),
            stamp,
            flags,
        }
    }

    /// Create a persistent (global) identifier with stamp 0.
    ///
    /// Persistent identifiers represent globally visible names like
    /// module names or external declarations.
    #[inline]
    pub fn create_persistent(name: impl Into<Name>) -> Self {
        Self {
            name: name.into(),
            stamp: 0,
            flags: IdentFlags::GLOBAL,
        }
    }

    /// Create a local identifier with an auto-incrementing stamp.
    ///
    /// This uses a thread-local counter for stamp generation. For new compiler
    /// code, prefer using [`IdGenerator`] explicitly so the counter is tied to
    /// the current compilation context.
    ///
    /// This is mainly useful for tests and simple cases where
    /// an explicit generator is not available.
    #[inline]
    pub fn create_local(name: impl Into<Name>) -> Self {
        let stamp = LOCAL_IDENT_COUNTER.with(|counter| {
            let stamp = counter.get() + 1;
            counter.set(stamp);
            stamp
        });
        let name = name.into();
        Self {
            name,
            stamp,
            flags: IdentFlags::NONE,
        }
    }

    /// Get the current stamp used by [`Ident::create_local`].
    #[inline]
    pub fn current_local_stamp() -> i32 {
        LOCAL_IDENT_COUNTER.with(Cell::get)
    }

    /// Set the local stamp counter (matches OCaml's `Ident.set_current_time`).
    #[inline]
    pub fn set_current_time(stamp: i32) {
        LOCAL_IDENT_COUNTER.with(|counter| counter.set(stamp));
    }

    /// Get the name of this identifier.
    #[inline]
    pub fn name(&self) -> &'static str {
        self.name.as_str()
    }

    /// The interned name, for use as a cheap map key.
    #[inline]
    pub fn name_atom(&self) -> Name {
        self.name
    }

    /// Get the stamp of this identifier.
    #[inline]
    pub fn stamp(&self) -> i32 {
        self.stamp
    }

    /// Get the flags of this identifier.
    #[inline]
    pub fn flags(&self) -> IdentFlags {
        self.flags
    }

    /// Create a unique toplevel name.
    ///
    /// Format: `name/stamp`
    #[inline]
    pub fn unique_toplevel_name(&self) -> String {
        format!("{}/{}", self.name, self.stamp)
    }

    /// Check if this is a persistent identifier (stamp = 0).
    #[inline]
    pub fn is_persistent(&self) -> bool {
        self.stamp == 0
    }

    /// Check if this is a hidden identifier (stamp = -1).
    #[inline]
    pub fn is_hidden(&self) -> bool {
        self.stamp == -1
    }

    /// Check if the global flag is set.
    #[inline]
    pub fn is_global(&self) -> bool {
        self.flags.is_global()
    }

    /// Check if this is a predefined exception.
    #[inline]
    pub fn is_predef_exn(&self) -> bool {
        self.flags.is_predef_exn()
    }

    /// Whether this identifier denotes a JavaScript binding.
    #[inline]
    pub fn is_js(&self) -> bool {
        self.flags.is_js()
    }

    /// Create an unstamped JavaScript identifier with the JS flag.
    pub fn create_js(name: impl Into<Name>) -> Self {
        Self::new(name, 0, IdentFlags::JS)
    }

    /// Get the binding time (same as stamp).
    #[inline]
    pub fn binding_time(&self) -> i32 {
        self.stamp
    }

    /// Check if two identifiers have the same name (ignoring stamp).
    #[inline]
    pub fn equal(&self, other: &Self) -> bool {
        self.name == other.name
    }

    /// Check if two identifiers are the same.
    ///
    /// Two identifiers are the same if:
    /// - Both have non-zero stamps and the stamps are equal, OR
    /// - Both have stamp 0 and the names are equal
    #[inline]
    pub fn same(&self, other: &Self) -> bool {
        if self.stamp != 0 {
            self.stamp == other.stamp
        } else {
            other.stamp == 0 && self.name == other.name
        }
    }

    /// Create a new identifier with the same name but with global flag set.
    #[inline]
    pub fn with_global(&self) -> Self {
        Self {
            name: self.name,
            stamp: self.stamp,
            flags: self.flags.with_global(),
        }
    }

    /// Create a hidden version of this identifier (stamp = -1).
    #[inline]
    pub fn hide(&self) -> Self {
        Self {
            name: self.name,
            stamp: -1,
            flags: self.flags,
        }
    }

    /// Copy this identifier with a stamp reserved earlier from the generator.
    #[inline]
    pub(crate) fn with_stamp(&self, stamp: i32) -> Self {
        Self {
            name: self.name,
            stamp,
            flags: self.flags,
        }
    }

    /// Rename this identifier with a new stamp from the generator.
    ///
    /// This creates a new identifier with the same name and flags
    /// but a fresh stamp.
    #[inline]
    pub fn rename(&self, id_gen: &super::context::IdGenerator) -> Self {
        let stamp = id_gen.next_stamp();
        Self {
            name: self.name,
            stamp,
            flags: self.flags,
        }
    }
}

impl fmt::Debug for Ident {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.stamp {
            0 => write!(f, "{}!", self.name),
            -1 => write!(f, "{}#", self.name),
            n => {
                write!(f, "{}/{}", self.name, n)?;
                if self.is_global() {
                    write!(f, "g")?;
                }
                Ok(())
            }
        }
    }
}

impl fmt::Display for Ident {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.name)
    }
}

impl PartialEq for Ident {
    /// Equality based on `same` semantics.
    fn eq(&self, other: &Self) -> bool {
        self.same(other)
    }
}

impl Eq for Ident {}

impl Hash for Ident {
    /// Consistent with `Eq` (`same`): a stamped ident is identified by its
    /// stamp alone, an unstamped one by its name. Flags never take part.
    fn hash<H: Hasher>(&self, state: &mut H) {
        if self.stamp != 0 {
            self.stamp.hash(state);
        } else {
            self.name.hash(state);
        }
    }
}

impl Ord for Ident {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        // First compare by stamp
        match self.stamp.cmp(&other.stamp) {
            std::cmp::Ordering::Equal => {}
            ord => return ord,
        }
        // Then by name
        match self.name.cmp(&other.name) {
            std::cmp::Ordering::Equal => {}
            ord => return ord,
        }
        // Finally by flags
        self.flags.0.cmp(&other.flags.0)
    }
}

impl PartialOrd for Ident {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

/// A table mapping identifiers to values.
///
/// This is implemented using an IndexMap for efficient iteration
/// while maintaining insertion order within each name.
///
/// Unlike the OCaml AVL tree implementation, this uses standard
/// Rust collections. The tradeoff is slightly different performance
/// characteristics but much simpler code.
pub type IdentTable<T> = indexmap::IndexMap<Ident, T, ahash::RandomState>;

/// Create a new identifier table.
pub fn new_ident_table<T>() -> IdentTable<T> {
    IdentTable::with_hasher(ahash::RandomState::new())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::context::IdGenerator;

    #[test]
    fn javascript_flags_preserve_reference_bits_and_identity() {
        let js = Ident::create_js("Math");
        let global = Ident::new("Math", 0, IdentFlags::GLOBAL);
        assert!(js.is_js());
        assert!(!js.is_global());
        assert_eq!(js.flags().bits(), 8);
        assert!(global.is_global());
        assert_eq!(IdentFlags::from_bits_truncate(8), IdentFlags::JS);
        assert_eq!(IdentFlags::from_bits_truncate(32), IdentFlags::JS_OBJECT);
    }

    #[test]
    fn test_create_persistent() {
        let id = Ident::create_persistent("String");
        assert_eq!(id.name(), "String");
        assert_eq!(id.stamp(), 0);
        assert!(id.is_persistent());
        assert!(id.is_global());
    }

    #[test]
    fn test_create_with_generator() {
        let id_gen = IdGenerator::new();
        let id1 = id_gen.create("x");
        let id2 = id_gen.create("x");
        let id3 = id_gen.create("y");

        assert_eq!(id1.name(), "x");
        assert_eq!(id2.name(), "x");
        assert_eq!(id3.name(), "y");

        // All have different stamps
        assert_ne!(id1.stamp(), id2.stamp());
        assert_ne!(id1.stamp(), id3.stamp());
        assert_ne!(id2.stamp(), id3.stamp());

        // Same name but not same identifier
        assert!(id1.equal(&id2));
        assert!(!id1.same(&id2));
    }

    #[test]
    fn test_same_persistent() {
        let id1 = Ident::create_persistent("Mod");
        let id2 = Ident::create_persistent("Mod");
        let id3 = Ident::create_persistent("Other");

        // Persistent identifiers with same name are same
        assert!(id1.same(&id2));
        assert!(!id1.same(&id3));
    }

    #[test]
    fn test_hide() {
        let id_gen = IdGenerator::new();
        let id = id_gen.create("x");
        let hidden = id.hide();

        assert_eq!(hidden.stamp(), -1);
        assert!(hidden.is_hidden());
        assert_eq!(hidden.name(), id.name());
    }

    #[test]
    fn test_rename() {
        let id_gen = IdGenerator::new();
        let id1 = id_gen.create("x");
        let id2 = id1.rename(&id_gen);

        assert_eq!(id1.name(), id2.name());
        assert_ne!(id1.stamp(), id2.stamp());
        assert!(!id1.same(&id2));
    }

    #[test]
    fn test_unique_names() {
        let id_gen = IdGenerator::new();
        let id = id_gen.create("foo");

        let toplevel = id.unique_toplevel_name();

        assert!(toplevel.starts_with("foo/"));
    }

    #[test]
    fn test_debug_format() {
        let persistent = Ident::create_persistent("Mod");
        let id_gen = IdGenerator::new();
        let local = id_gen.create("x");
        let hidden = local.hide();
        let global = local.with_global();

        assert!(format!("{:?}", persistent).contains("!"));
        assert!(format!("{:?}", hidden).contains("#"));
        assert!(format!("{:?}", global).contains("g"));
    }

    #[test]
    fn test_concurrent_generation() {
        use std::sync::Arc;
        use std::thread;

        let id_gen = Arc::new(IdGenerator::new());
        let mut handles = vec![];

        for _ in 0..10 {
            let id_gen = id_gen.clone();
            handles.push(thread::spawn(move || {
                let mut ids = vec![];
                for i in 0..100 {
                    ids.push(id_gen.create(format!("var{}", i)));
                }
                ids
            }));
        }

        let all_ids: Vec<Ident> = handles
            .into_iter()
            .flat_map(|h| h.join().unwrap())
            .collect();

        // All stamps should be unique
        let stamps: std::collections::HashSet<i32> = all_ids.iter().map(|id| id.stamp()).collect();
        assert_eq!(stamps.len(), all_ids.len());
    }
}

#[cfg(test)]
mod hash_contract_tests {
    use super::*;
    use std::collections::hash_map::DefaultHasher;

    fn hash_of(id: &Ident) -> u64 {
        let mut h = DefaultHasher::new();
        id.hash(&mut h);
        h.finish()
    }

    #[test]
    fn idents_equal_under_same_hash_alike() {
        for (a, b) in [
            (
                Ident::new("nonzero", 7, IdentFlags::GLOBAL),
                Ident::new("different", 7, IdentFlags::NONE),
            ),
            (
                Ident::new("stampzero", 0, IdentFlags::PREDEF_EXN),
                Ident::new("stampzero", 0, IdentFlags::NONE),
            ),
        ] {
            assert_eq!(a, b);
            assert_eq!(hash_of(&a), hash_of(&b));
        }
    }
}
