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
use std::cell::Cell;
use std::fmt;
use std::hash::{Hash, Hasher};

thread_local! {
    static LOCAL_IDENT_COUNTER: Cell<i32> = const { Cell::new(0) };
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
#[derive(Clone, Copy, Serialize, Deserialize)]
pub struct Ident {
    name: Name,
    stamp: i32,
    flags: IdentFlags,
    /// Which `Ident.t` block this is, for identifiers decoded from a
    /// compiled interface (see [`IdentOrigin`]). Never compared, hashed or
    /// serialized.
    #[serde(skip)]
    origin: IdentOrigin,
}

/// The physical identity of an identifier read from a compiled interface.
///
/// OCaml's `Ident.t` is a heap block: an identifier unmarshalled from a
/// `.cmi` is a block of its own, apart from the compiler's `Predef.ident_*`
/// or any identifier of the compilation, even with the same stamp and name.
/// Rust identifiers are values, so a decoded one carries the number of its
/// marshal block, or of its block in the saved interface a stored graph was
/// imported from (0 for every other identifier). Its only reader went with
/// `Includemod.is_big`, which counted each block once. Three bytes, in the padding after `flags`.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct IdentOrigin([u8; 3]);

impl IdentOrigin {
    /// The largest origin number.
    pub const MAX: u32 = 0x00FF_FFFF;
    /// The origins of graphs a compilation imports into its own arena,
    /// restarting with each compilation.
    pub const COMPILATION: std::ops::Range<u32> = 1..0x0040_0000;
    /// The origins of graphs imported into a worker's store, which a
    /// worker's compilations share for one build.
    pub const STORE: std::ops::Range<u32> = 0x0040_0000..0x0080_0000;
    /// The origins of graphs published to the process-wide shared pool for
    /// one build.
    pub const SHARED: std::ops::Range<u32> = 0x0080_0000..0x0100_0000;

    /// The origin `next` holds in `range`, advancing it. The ranges keep the
    /// three importer kinds apart. Within one allocator an origin is never
    /// handed out twice: running out is an error rather than a reuse of an
    /// origin some identifier may still hold. Crossing allocator lifetimes
    /// requires remapping; these numeric ranges do not identify instances.
    pub fn next_in(range: std::ops::Range<u32>, next: &std::cell::Cell<u32>) -> Self {
        Self::validate_range(&range);
        let origin = next.get();
        assert!(
            range.start <= origin,
            "identifier origin counter {origin:#x} is below its range {range:x?}"
        );
        assert!(
            origin < range.end,
            "identifier origins exhausted: {} identifier blocks imported in the range {range:x?}",
            range.end - range.start
        );
        next.set(origin + 1);
        Self::new(origin)
    }

    /// The `n`-th origin of `range` for an allocator shared by threads,
    /// checked as [`IdentOrigin::next_in`] checks it.
    pub fn nth_in(range: std::ops::Range<u32>, n: u32) -> Self {
        Self::validate_range(&range);
        assert!(
            n < range.end - range.start,
            "identifier origins exhausted: {} identifier blocks imported in the range {range:x?}",
            range.end - range.start
        );
        Self::new(range.start + n)
    }

    fn validate_range(range: &std::ops::Range<u32>) {
        assert!(
            *range == Self::COMPILATION || *range == Self::STORE || *range == Self::SHARED,
            "invalid identifier origin range {range:x?}"
        );
    }

    /// The origin numbered `n`.
    pub fn new(n: u32) -> Self {
        assert!(n <= Self::MAX, "identifier origins exhausted");
        let [a, b, c, _] = n.to_le_bytes();
        Self([a, b, c])
    }

    /// The number of this origin; 0 for an identifier not decoded.
    pub fn get(self) -> u32 {
        let [a, b, c] = self.0;
        u32::from_le_bytes([a, b, c, 0])
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
            origin: IdentOrigin::default(),
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
            origin: IdentOrigin::default(),
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
            origin: IdentOrigin::default(),
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

    #[inline]
    pub fn is_js(&self) -> bool {
        self.flags.is_js()
    }

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
            // `Ident.make_global` sets the flag of the same block.
            origin: self.origin,
        }
    }

    /// This identifier as the decoded block numbered by `origin`.
    #[inline]
    pub fn with_origin(self, origin: IdentOrigin) -> Self {
        Self { origin, ..self }
    }

    /// The block this identifier was decoded from, if any.
    #[inline]
    pub fn origin(&self) -> IdentOrigin {
        self.origin
    }

    /// Create a hidden version of this identifier (stamp = -1).
    #[inline]
    pub fn hide(&self) -> Self {
        Self {
            name: self.name,
            stamp: -1,
            flags: self.flags,
            origin: IdentOrigin::default(),
        }
    }

    /// Copy this identifier with a stamp reserved earlier from the generator.
    #[inline]
    pub(crate) fn with_stamp(&self, stamp: i32) -> Self {
        Self {
            name: self.name,
            stamp,
            flags: self.flags,
            origin: IdentOrigin::default(),
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
            origin: IdentOrigin::default(),
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
                    ids.push(id_gen.create(&format!("var{}", i)));
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
mod origin_tests {
    use super::*;
    use std::cell::Cell;
    use std::ops::Range;

    const RANGES: [Range<u32>; 3] = [
        IdentOrigin::COMPILATION,
        IdentOrigin::STORE,
        IdentOrigin::SHARED,
    ];

    #[test]
    fn origin_ranges_are_disjoint_nonzero_and_fit_three_bytes() {
        assert_eq!(IdentOrigin::COMPILATION.start, 1, "0 is no origin");
        assert_eq!(IdentOrigin::COMPILATION.end, IdentOrigin::STORE.start);
        assert_eq!(IdentOrigin::STORE.end, IdentOrigin::SHARED.start);
        assert_eq!(IdentOrigin::SHARED.end, IdentOrigin::MAX + 1);
        assert_eq!(std::mem::size_of::<Ident>(), 16);
    }

    /// An allocator hands out the last origin of its range once, then
    /// refuses: it never returns to an origin it already handed out.
    #[test]
    fn each_range_ends_without_reusing_an_origin() {
        for range in RANGES {
            let next = Cell::new(range.end - 2);
            let a = IdentOrigin::next_in(range.clone(), &next);
            let b = IdentOrigin::next_in(range.clone(), &next);
            assert_eq!((a.get(), b.get()), (range.end - 2, range.end - 1));
            for _ in 0..2 {
                let again = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                    IdentOrigin::next_in(range.clone(), &next)
                }));
                assert!(
                    again.is_err(),
                    "{range:x?} handed out an origin past its end"
                );
                assert_eq!(next.get(), range.end, "the counter does not wrap");
            }
            let span = range.end - range.start;
            assert_eq!(
                IdentOrigin::nth_in(range.clone(), span - 1).get(),
                range.end - 1
            );
            assert!(std::panic::catch_unwind(|| IdentOrigin::nth_in(range.clone(), span)).is_err());
        }
    }

    #[test]
    fn invalid_ranges_are_refused_before_advancing() {
        for range in [0..1, 1..1, 5..4, 1..u32::MAX, 2..10] {
            let next = Cell::new(range.start);
            assert!(
                std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                    IdentOrigin::next_in(range.clone(), &next)
                }))
                .is_err()
            );
            assert_eq!(next.get(), range.start);
            assert!(std::panic::catch_unwind(|| IdentOrigin::nth_in(range.clone(), 0)).is_err());
        }
    }

    #[test]
    fn a_counter_outside_its_range_is_refused() {
        for range in RANGES {
            let below = Cell::new(range.start - 1);
            assert!(
                std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| IdentOrigin::next_in(
                    range.clone(),
                    &below
                )))
                .is_err()
            );
        }
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
