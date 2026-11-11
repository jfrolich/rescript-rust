//! Compact location handles for declarations, attributes and type labels.
//!
//! OCaml `Types` declarations (`compiler/ml/types.mli`: `val_loc`, `type_loc`,
//! `ld_loc`, `cd_loc`, `ext_loc`, `md_loc`, `mtd_loc`), their attributes and
//! the `Labelled`/`Optional` argument labels of `Tarrow` carry a full
//! `Location.t`. Subst copies those values unchanged unless saving without
//! `-keep-locs` (`compiler/ml/subst.ml:57-58`), and `Env` keys usage tables
//! by `(name, loc)` (`compiler/ml/env.ml`: `value_declarations`,
//! `type_declarations`, `used_constructors`).
//!
//! Rust keeps the same values, but outside the declarations: a declaration
//! holds an 8-byte [`DeclLoc`], and the full `Location` lives in an
//! append-only table owned by whichever arena owns the declaration:
//!
//! - [`DeclLocKind::Source`] needs no table. A location-free compilation's
//!   locations have no coordinates (`ParseArena::with_locations(false)`): only
//!   the source file, the ghost flag and an opaque declaration origin, all of
//!   which fit in the handle. `Location::none()` is a source handle as well.
//! - [`DeclLocKind::Local`] indexes the compiling `TypeContext`'s table.
//! - [`DeclLocKind::Store`] indexes the worker's `ThreadTypeStore` table, for
//!   declarations built into the store (`TypeContext::build_in_store`).
//! - [`DeclLocKind::Shared`] indexes the table of one immutable graph of the
//!   process-wide `SharedTypePool`; the handle names the graph by its base.
//! - [`DeclLocKind::Portable`] indexes a [`DeclLocTable`] that travels with
//!   an owned value (a `PortableSignature`, a GenType declaration cache entry)
//!   across context lifetimes.
//!
//! Handles are copied with their declarations, so copies keep pointing at the
//! same entry. Resolving a handle reproduces exactly the `Location` the
//! declaration was built with; output formats (`.cmi`, `.cmt`, sexps,
//! diagnostics, editor analysis) resolve at their boundary and are unchanged.
//!
//! A source handle keeps the file identity: two units' declarations with the
//! same origin ordinal are different declarations. Local and store handles
//! carry the identity of their owning table, so resolving one with the wrong
//! owner fails loudly instead of reading an unrelated entry.

use crate::intern::StrIdx;
use crate::location::{Location, LocationOrigin, Position};
use serde::{Deserialize, Serialize};

const KIND_SHIFT: u32 = 29;
const GHOST_BIT: u32 = 1 << 28;
const INDEX_MASK: u32 = GHOST_BIT - 1;

/// Owner of the location a [`DeclLoc`] denotes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DeclLocKind {
    /// The handle itself holds a location without coordinates.
    Source = 0,
    /// An entry of the compiling `TypeContext`'s table.
    Local = 1,
    /// An entry of the worker's `ThreadTypeStore` table.
    Store = 2,
    /// An entry of a `SharedTypePool` graph's table.
    Shared = 3,
    /// An entry of a [`DeclLocTable`] that travels with an owned value.
    Portable = 4,
}

/// Handle for a declaration, attribute or type-label location (see the
/// module documentation). `Default` is `Location::none()`.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct DeclLoc {
    /// Source: file name index. Local/Store: the owning table's identity.
    /// Shared: base index of the owning graph. Portable: 0.
    owner: u32,
    /// Kind (top three bits), ghost flag (source only) and table index or
    /// source origin.
    bits: u32,
}

impl Default for DeclLoc {
    fn default() -> Self {
        Self::none()
    }
}

impl std::fmt::Debug for DeclLoc {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.kind() {
            DeclLocKind::Source => f
                .debug_struct("DeclLoc::Source")
                .field("file", &self.owner)
                .field("ghost", &(self.bits & GHOST_BIT != 0))
                .field("origin", &(self.bits & INDEX_MASK))
                .finish(),
            kind => f
                .debug_struct("DeclLoc")
                .field("kind", &kind)
                .field("owner", &self.owner)
                .field("index", &self.index())
                .finish(),
        }
    }
}

impl DeclLoc {
    /// `Location::none()`.
    pub const fn none() -> Self {
        DeclLoc {
            owner: 0,
            bits: GHOST_BIT,
        }
    }

    /// Which table, if any, holds the location.
    pub fn kind(self) -> DeclLocKind {
        match self.bits >> KIND_SHIFT {
            0 => DeclLocKind::Source,
            1 => DeclLocKind::Local,
            2 => DeclLocKind::Store,
            3 => DeclLocKind::Shared,
            4 => DeclLocKind::Portable,
            other => unreachable!("invalid declaration location kind {other}"),
        }
    }

    /// The table index of a non-source handle.
    pub fn index(self) -> usize {
        debug_assert!(self.kind() != DeclLocKind::Source);
        (self.bits & INDEX_MASK) as usize
    }

    pub(crate) fn owner(self) -> u32 {
        self.owner
    }

    pub(crate) fn table(kind: DeclLocKind, owner: u32, index: usize) -> Self {
        debug_assert!(kind != DeclLocKind::Source);
        let index = u32::try_from(index)
            .ok()
            .filter(|index| *index <= INDEX_MASK)
            .expect("declaration location table overflow");
        DeclLoc {
            owner,
            bits: ((kind as u32) << KIND_SHIFT) | index,
        }
    }

    /// The handle of a location without coordinates: both ends are the
    /// coordinate-free position of one file. Lossless: [`Self::source_location`]
    /// rebuilds the same value. `None` for a location with coordinates.
    #[inline]
    pub fn source(loc: &Location) -> Option<Self> {
        let start = loc.loc_start;
        if start != loc.loc_end || start.line != 0 || start.bol != 0 || start.cnum != 0 {
            return None;
        }
        Some(DeclLoc {
            owner: start.file_name.raw(),
            bits: loc.origin.raw() | if loc.loc_ghost { GHOST_BIT } else { 0 },
        })
    }

    /// The location of a source handle.
    #[inline]
    pub fn source_location(self) -> Option<Location> {
        if self.kind() != DeclLocKind::Source {
            return None;
        }
        let pos = Position {
            file_name: StrIdx::from_raw(self.owner),
            line: 0,
            bol: 0,
            cnum: 0,
        };
        Some(Location {
            loc_start: pos,
            loc_end: pos,
            loc_ghost: self.bits & GHOST_BIT != 0,
            origin: LocationOrigin::new(self.bits & INDEX_MASK),
        })
    }

    /// The file of a source handle.
    pub(crate) fn source_file(self) -> Option<StrIdx> {
        (self.kind() == DeclLocKind::Source).then(|| StrIdx::from_raw(self.owner))
    }

    /// The same source handle naming another file.
    pub(crate) fn with_source_file(self, file: StrIdx) -> Self {
        debug_assert_eq!(self.kind(), DeclLocKind::Source);
        DeclLoc {
            owner: file.raw(),
            bits: self.bits,
        }
    }
}

/// Resolves declaration location handles of one owner context.
pub trait DeclLocs {
    /// The location `loc` denotes.
    fn resolve_loc(&self, loc: DeclLoc) -> Location;
}

/// A location table that travels with an owned value (a portable signature,
/// a cached GenType declaration). Interns equal locations once. Skipped by
/// interface digests (`digest_ser`).
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct DeclLocTable {
    locations: Vec<Location>,
    #[serde(skip)]
    index: crate::fast_hash::AHashMap<Location, u32>,
}

impl PartialEq for DeclLocTable {
    fn eq(&self, other: &Self) -> bool {
        self.locations == other.locations
    }
}

impl Eq for DeclLocTable {}

impl DeclLocTable {
    /// Whether the table holds no locations.
    pub fn is_empty(&self) -> bool {
        self.locations.is_empty()
    }

    /// The number of locations in the table.
    pub fn len(&self) -> usize {
        self.locations.len()
    }

    /// The locations, by handle index.
    pub fn locations(&self) -> &[Location] {
        &self.locations
    }

    /// The locations, by handle index, for rewriting in place.
    pub fn locations_mut(&mut self) -> &mut [Location] {
        &mut self.locations
    }

    /// A portable handle for `loc` (a source handle when it has no
    /// coordinates).
    pub fn intern(&mut self, loc: Location) -> DeclLoc {
        if let Some(source) = DeclLoc::source(&loc) {
            return source;
        }
        if self.index.len() != self.locations.len() {
            // Decoded tables do not carry their index.
            self.index = (self.locations.iter().enumerate())
                .map(|(i, loc)| (*loc, i as u32))
                .collect();
        }
        let next = self.locations.len();
        let index = *self.index.entry(loc).or_insert_with(|| {
            self.locations.push(loc);
            next as u32
        });
        DeclLoc::table(DeclLocKind::Portable, 0, index as usize)
    }

    /// The location of a portable or source handle.
    pub fn resolve(&self, loc: DeclLoc) -> Location {
        match loc.kind() {
            DeclLocKind::Source => loc.source_location().unwrap(),
            DeclLocKind::Portable => self.locations[loc.index()],
            kind => panic!("{kind:?} declaration location resolved by a portable table"),
        }
    }
}

impl DeclLocs for DeclLocTable {
    fn resolve_loc(&self, loc: DeclLoc) -> Location {
        self.resolve(loc)
    }
}

/// Append-only interning table owned by a `TypeContext` or worker store.
#[derive(Debug, Default)]
pub(crate) struct OwnedDeclLocs {
    locations: std::cell::RefCell<Vec<Location>>,
    index: std::cell::RefCell<crate::fast_hash::AHashMap<Location, u32>>,
}

impl OwnedDeclLocs {
    /// Index of `loc`, appending it the first time. Equal locations share an
    /// entry, so handles of one table compare like the locations they denote.
    pub(crate) fn intern(&self, loc: Location) -> usize {
        if let Some(index) = self.index.borrow().get(&loc) {
            return *index as usize;
        }
        let mut locations = self.locations.borrow_mut();
        let index = locations.len();
        locations.push(loc);
        self.index.borrow_mut().insert(loc, index as u32);
        index
    }

    /// Append a block of locations as is (an imported table), returning the
    /// index of its first entry.
    pub(crate) fn append(&self, locs: impl IntoIterator<Item = Location>) -> usize {
        let mut locations = self.locations.borrow_mut();
        let base = locations.len();
        locations.extend(locs);
        base
    }

    pub(crate) fn get(&self, index: usize) -> Location {
        self.locations.borrow()[index]
    }

    pub(crate) fn len(&self) -> usize {
        self.locations.borrow().len()
    }
}

/// Identity of a `TypeContext` or worker store table, carried by its handles.
pub(crate) fn next_table_owner() -> u32 {
    static NEXT: std::sync::atomic::AtomicU32 = std::sync::atomic::AtomicU32::new(1);
    NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
}

/// How the handles of a portable table map into the table of an importing
/// owner: portable entry `i` becomes entry `base + i` of `kind`/`owner`, and
/// source handles rename their file.
pub(crate) struct DeclLocImport<'a> {
    pub(crate) kind: DeclLocKind,
    pub(crate) owner: u32,
    pub(crate) base: usize,
    pub(crate) files: &'a dyn Fn(StrIdx) -> StrIdx,
}

impl DeclLocImport<'_> {
    pub(crate) fn import(&self, loc: DeclLoc) -> DeclLoc {
        match loc.kind() {
            DeclLocKind::Source => loc.with_source_file((self.files)(loc.source_file().unwrap())),
            DeclLocKind::Portable => DeclLoc::table(self.kind, self.owner, self.base + loc.index()),
            kind => panic!("{kind:?} declaration location in a portable signature"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn located(file: u32, line: i32, ghost: bool) -> Location {
        Location {
            loc_start: Position::new(StrIdx::from_raw(file), line, 3, 7),
            loc_end: Position::new(StrIdx::from_raw(file), line, 3, 9),
            loc_ghost: ghost,
            origin: LocationOrigin::default(),
        }
    }

    #[test]
    fn handle_is_eight_bytes() {
        assert_eq!(std::mem::size_of::<DeclLoc>(), 8);
        assert_eq!(std::mem::size_of::<Option<DeclLoc>>(), 12);
    }

    #[test]
    fn none_is_a_source_handle() {
        assert_eq!(DeclLoc::source(&Location::none()), Some(DeclLoc::none()));
        assert_eq!(DeclLoc::none().source_location(), Some(Location::none()));
        assert_eq!(DeclLoc::default(), DeclLoc::none());
    }

    #[test]
    fn source_handles_round_trip_and_keep_file_identity() {
        let absent = |file: u32, origin: u32, ghost: bool| {
            let pos = Position {
                file_name: StrIdx::from_raw(file),
                ..Position::default()
            };
            Location {
                loc_start: pos,
                loc_end: pos,
                loc_ghost: ghost,
                origin: LocationOrigin::new(origin),
            }
        };
        let a = absent(5, 42, false);
        // The same origin ordinal in another unit's source arena.
        let b = absent(6, 42, false);
        let c = absent(5, 42, true);
        let (ha, hb, hc) = (
            DeclLoc::source(&a).unwrap(),
            DeclLoc::source(&b).unwrap(),
            DeclLoc::source(&c).unwrap(),
        );
        assert_ne!(ha, hb);
        assert_ne!(ha, hc);
        assert_eq!(ha.source_location(), Some(a));
        assert_eq!(hb.source_location(), Some(b));
        assert_eq!(hc.source_location(), Some(c));
        assert!(DeclLoc::source(&located(5, 1, false)).is_none());
    }

    #[test]
    fn portable_table_interns_and_imports() {
        let mut table = DeclLocTable::default();
        let l1 = located(9, 3, false);
        let l2 = located(9, 4, true);
        let h1 = table.intern(l1);
        let h2 = table.intern(l2);
        assert_eq!(table.intern(l1), h1);
        assert_ne!(h1, h2);
        assert_eq!(table.len(), 2);
        assert_eq!(table.resolve(h2), l2);
        // A decoded table rebuilds its index before interning.
        let mut decoded: DeclLocTable =
            crate::binser::from_slice(&crate::binser::to_vec(&table).unwrap()).unwrap();
        assert_eq!(decoded.intern(l2), h2);
        assert_eq!(decoded.len(), 2);
        let renamed = |file: StrIdx| StrIdx::from_raw(file.raw() + 100);
        let import = DeclLocImport {
            kind: DeclLocKind::Store,
            owner: 7,
            base: 10,
            files: &renamed,
        };
        let imported = import.import(h2);
        assert_eq!(imported.kind(), DeclLocKind::Store);
        assert_eq!(imported.index(), 11);
        assert_eq!(imported.owner(), 7);
        let source = DeclLoc::none().with_source_file(StrIdx::from_raw(3));
        assert_eq!(
            import.import(source).source_file(),
            Some(StrIdx::from_raw(103))
        );
    }

    #[test]
    fn owned_table_interns_equal_locations_once() {
        let table = OwnedDeclLocs::default();
        let l1 = located(1, 2, false);
        assert_eq!(table.intern(l1), 0);
        assert_eq!(table.intern(located(1, 3, false)), 1);
        assert_eq!(table.intern(l1), 0);
        assert_eq!(table.append([l1]), 2);
        assert_eq!(table.get(2), l1);
        assert_eq!(table.len(), 3);
    }
}
