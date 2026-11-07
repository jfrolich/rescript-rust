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
    Source = 0,
    Local = 1,
    Store = 2,
    Shared = 3,
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
    instances: Vec<LocationInstance>,
    #[serde(skip)]
    instance_index: crate::fast_hash::AHashMap<(u64, u32), u32>,
    #[serde(skip)]
    index: crate::fast_hash::AHashMap<Location, u32>,
}

impl PartialEq for DeclLocTable {
    fn eq(&self, other: &Self) -> bool {
        self.locations == other.locations && self.instances == other.instances
    }
}

impl Eq for DeclLocTable {}

impl DeclLocTable {
    pub fn is_empty(&self) -> bool {
        self.locations.is_empty()
    }

    pub fn len(&self) -> usize {
        self.locations.len()
    }

    pub fn locations(&self) -> &[Location] {
        &self.locations
    }

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
        assert!(
            next < IDENTITY_INDEX_BIT,
            "portable coordinate table exhausted"
        );
        let index = *self.index.entry(loc).or_insert_with(|| {
            self.locations.push(loc);
            next as u32
        });
        DeclLoc::table(DeclLocKind::Portable, 0, index as usize)
    }

    /// Keep allocation sharing independently of coordinate interning. Identity
    /// keys come from the producer, never from the coordinate values.
    pub(crate) fn intern_with_identity(
        &mut self,
        loc: Location,
        identity: LocationIdentity,
    ) -> DeclLoc {
        // Even a coordinate-free value may denote a real decoded allocation.
        // Give it a coordinate entry instead of converting it to a source handle.
        if self.index.len() != self.locations.len() {
            self.index = self
                .locations
                .iter()
                .enumerate()
                .map(|(i, loc)| (*loc, i as u32))
                .collect();
        }
        let next = self.locations.len();
        assert!(
            next < IDENTITY_INDEX_BIT,
            "portable coordinate table exhausted"
        );
        let coordinate = *self.index.entry(loc).or_insert_with(|| {
            self.locations.push(loc);
            next as u32
        });
        if self.instance_index.len() != self.instances.len() {
            self.instance_index = self
                .instances
                .iter()
                .enumerate()
                .map(|(i, entry)| ((entry.identity.scope, entry.identity.location), i as u32))
                .collect();
        }
        let key = (identity.scope, identity.location);
        let index = if let Some(&index) = self.instance_index.get(&key) {
            assert_eq!(
                self.instances[index as usize],
                LocationInstance {
                    coordinate,
                    identity
                }
            );
            index
        } else {
            let index = self.instances.len();
            assert!(
                index < IDENTITY_INDEX_BIT,
                "portable provenance table exhausted"
            );
            self.instances.push(LocationInstance {
                coordinate,
                identity,
            });
            self.instance_index.insert(key, index as u32);
            index as u32
        };
        DeclLoc::table(
            DeclLocKind::Portable,
            0,
            IDENTITY_INDEX_BIT | index as usize,
        )
    }

    pub(crate) fn identity(&self, index: usize) -> Option<LocationIdentity> {
        (index & IDENTITY_INDEX_BIT != 0)
            .then(|| self.instances[index & !IDENTITY_INDEX_BIT].identity)
    }

    pub(crate) fn get(&self, index: usize) -> Location {
        let coordinate = if index & IDENTITY_INDEX_BIT == 0 {
            index
        } else {
            self.instances[index & !IDENTITY_INDEX_BIT].coordinate as usize
        };
        self.locations[coordinate]
    }

    /// A new import owns new allocations, including for two live stores.
    /// Retain sharing within each producer scope, but never its namespace.
    pub(crate) fn remap_for_import(&mut self, files: &dyn Fn(StrIdx) -> StrIdx) {
        for loc in &mut self.locations {
            loc.loc_start.file_name = files(loc.loc_start.file_name);
            loc.loc_end.file_name = files(loc.loc_end.file_name);
        }
        let mut scopes = crate::fast_hash::AHashMap::default();
        for instance in &mut self.instances {
            instance.identity.scope = *scopes
                .entry(instance.identity.scope)
                .or_insert_with(|| (next_table_owner() as u64) << 32);
        }
        self.index.clear();
        self.instance_index.clear();
    }

    /// The location of a portable or source handle.
    pub fn resolve(&self, loc: DeclLoc) -> Location {
        match loc.kind() {
            DeclLocKind::Source => loc.source_location().unwrap(),
            DeclLocKind::Portable => self.get(loc.index()),
            kind => panic!("{kind:?} declaration location resolved by a portable table"),
        }
    }
}

impl FromIterator<Location> for DeclLocTable {
    fn from_iter<T: IntoIterator<Item = Location>>(iter: T) -> Self {
        Self {
            locations: iter.into_iter().collect(),
            ..Self::default()
        }
    }
}

impl DeclLocs for DeclLocTable {
    fn resolve_loc(&self, loc: DeclLoc) -> Location {
        self.resolve(loc)
    }
}

/// Allocation identities of a location and its two position blocks. The
/// scope is assigned by the owner of the source allocations, never inferred
/// from coordinates. Copies retain these keys; equal coordinates alone do
/// not imply a shared allocation.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub(crate) struct LocationIdentity {
    pub(crate) scope: u64,
    pub(crate) location: u32,
    pub(crate) start: u32,
    pub(crate) end: u32,
}

// Provenance-bearing handles use the upper half of the existing table-index
// bits. Ordinary coordinate-only locations keep their existing direct index
// and pay for no provenance storage.
const IDENTITY_INDEX_BIT: usize = 1 << 27;

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct LocationInstance {
    coordinate: u32,
    identity: LocationIdentity,
}

/// Append-only interning table owned by a `TypeContext` or worker store.
#[derive(Debug, Default)]
pub(crate) struct OwnedDeclLocs {
    locations: std::cell::RefCell<Vec<Location>>,
    index: std::cell::RefCell<crate::fast_hash::AHashMap<Location, u32>>,
    instances: std::cell::RefCell<Vec<LocationInstance>>,
    instance_index: std::cell::RefCell<crate::fast_hash::AHashMap<(u64, u32), u32>>,
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
        assert!(
            index < IDENTITY_INDEX_BIT,
            "declaration coordinate table exhausted"
        );
        locations.push(loc);
        self.index.borrow_mut().insert(loc, index as u32);
        index
    }

    /// Keep coordinate interning while distinguishing physical allocations.
    /// Reusing one source location must also reuse both of its position keys.
    pub(crate) fn intern_with_identity(&self, loc: Location, identity: LocationIdentity) -> usize {
        let coordinate = self.intern(loc);
        let key = (identity.scope, identity.location);
        if let Some(&index) = self.instance_index.borrow().get(&key) {
            let instances = self.instances.borrow();
            let instance = &instances[index as usize];
            assert_eq!(
                instance.coordinate as usize, coordinate,
                "location allocation changed coordinates"
            );
            assert_eq!(
                instance.identity, identity,
                "location allocation changed position identity"
            );
            return IDENTITY_INDEX_BIT | index as usize;
        }
        let mut instances = self.instances.borrow_mut();
        let index = instances.len();
        assert!(
            index < IDENTITY_INDEX_BIT,
            "declaration provenance table exhausted"
        );
        instances.push(LocationInstance {
            coordinate: coordinate as u32,
            identity,
        });
        self.instance_index.borrow_mut().insert(key, index as u32);
        IDENTITY_INDEX_BIT | index
    }

    pub(crate) fn identity(&self, index: usize) -> Option<LocationIdentity> {
        if index & IDENTITY_INDEX_BIT == 0 {
            None
        } else {
            Some(self.instances.borrow()[index & !IDENTITY_INDEX_BIT].identity)
        }
    }

    /// Append a block of locations as is (an imported table), returning the
    /// index of its first entry.
    pub(crate) fn append(&self, locs: impl IntoIterator<Item = Location>) -> usize {
        let mut locations = self.locations.borrow_mut();
        let base = locations.len();
        locations.extend(locs);
        assert!(
            locations.len() <= IDENTITY_INDEX_BIT,
            "declaration coordinate table exhausted"
        );
        base
    }

    /// Append coordinates and map the portable allocation handles separately.
    pub(crate) fn append_portable(&self, table: &DeclLocTable) -> (usize, Vec<usize>) {
        let base = self.append(table.locations.iter().copied());
        let mut owned = self.instances.borrow_mut();
        let mut index = self.instance_index.borrow_mut();
        let instances = table
            .instances
            .iter()
            .map(|entry| {
                let offset = owned.len();
                assert!(
                    offset < IDENTITY_INDEX_BIT,
                    "declaration provenance table exhausted"
                );
                owned.push(LocationInstance {
                    coordinate: u32::try_from(base + entry.coordinate as usize).unwrap(),
                    identity: entry.identity,
                });
                assert!(
                    index
                        .insert(
                            (entry.identity.scope, entry.identity.location),
                            offset as u32
                        )
                        .is_none()
                );
                IDENTITY_INDEX_BIT | offset
            })
            .collect();
        (base, instances)
    }

    pub(crate) fn get(&self, index: usize) -> Location {
        let coordinate = if index & IDENTITY_INDEX_BIT == 0 {
            index
        } else {
            self.instances.borrow()[index & !IDENTITY_INDEX_BIT].coordinate as usize
        };
        self.locations.borrow()[coordinate]
    }

    pub(crate) fn len(&self) -> usize {
        self.locations.borrow().len()
    }
}

/// Identity of a `TypeContext` or worker store table, carried by its handles.
pub(crate) fn next_table_owner() -> u32 {
    static NEXT: std::sync::atomic::AtomicU32 = std::sync::atomic::AtomicU32::new(1);
    NEXT.fetch_update(
        std::sync::atomic::Ordering::Relaxed,
        std::sync::atomic::Ordering::Relaxed,
        |next| next.checked_add(1),
    )
    .expect("declaration location owners exhausted")
}

/// How the handles of a portable table map into the table of an importing
/// owner: portable entry `i` becomes entry `base + i` of `kind`/`owner`, and
/// source handles rename their file. Provenance handles use the separately
/// mapped instance indices (shared graphs keep their own table unchanged).
pub(crate) struct DeclLocImport<'a> {
    pub(crate) kind: DeclLocKind,
    pub(crate) owner: u32,
    pub(crate) base: usize,
    pub(crate) instances: Vec<usize>,
    pub(crate) files: &'a dyn Fn(StrIdx) -> StrIdx,
}

impl DeclLocImport<'_> {
    pub(crate) fn import(&self, loc: DeclLoc) -> DeclLoc {
        match loc.kind() {
            DeclLocKind::Source => loc.with_source_file((self.files)(loc.source_file().unwrap())),
            DeclLocKind::Portable => {
                let index =
                    if loc.index() & IDENTITY_INDEX_BIT != 0 && self.kind != DeclLocKind::Shared {
                        self.instances[loc.index() & !IDENTITY_INDEX_BIT]
                    } else {
                        self.base + loc.index()
                    };
                DeclLoc::table(self.kind, self.owner, index)
            }
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
    fn coordinate_interning_does_not_merge_allocation_identities() {
        let table = OwnedDeclLocs::default();
        let loc = located(1, 2, false);
        let identity = LocationIdentity {
            scope: 7,
            location: 3,
            start: 4,
            end: 5,
        };
        let first = table.intern_with_identity(loc, identity);
        let copied = table.intern_with_identity(loc, identity);
        let adjacent = table.intern_with_identity(
            loc,
            LocationIdentity {
                location: 6,
                start: 5,
                end: 7,
                ..identity
            },
        );
        let other_scope = table.intern_with_identity(
            loc,
            LocationIdentity {
                scope: 8,
                ..identity
            },
        );
        assert_eq!(first, copied);
        assert_ne!(first, adjacent);
        assert_ne!(first, other_scope);
        assert_eq!(table.len(), 1, "all allocations share one coordinate value");
        assert_eq!(
            table.identity(first).unwrap().end,
            table.identity(adjacent).unwrap().start
        );
        for index in [first, copied, adjacent, other_scope] {
            assert_eq!(table.get(index), loc);
            let handle = DeclLoc::table(DeclLocKind::Local, 1, index);
            assert_eq!(handle.index(), index);
        }
        assert_eq!(table.identity(table.intern(loc)), None);
    }

    #[test]
    fn a_location_allocation_cannot_change_its_position_blocks() {
        let table = OwnedDeclLocs::default();
        let loc = located(1, 2, false);
        let identity = LocationIdentity {
            scope: 7,
            location: 3,
            start: 4,
            end: 5,
        };
        table.intern_with_identity(loc, identity);
        assert!(
            std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                table.intern_with_identity(loc, LocationIdentity { end: 9, ..identity })
            }))
            .is_err()
        );
    }

    #[test]
    fn parser_allocation_handles_survive_arena_moves_and_separate_arenas() {
        use crate::context::IdGenerator;
        use crate::parse_arena::ParseArena;
        use crate::types::TypeContext;
        let ctx = TypeContext::new(std::sync::Arc::new(IdGenerator::new()));
        let make_arena = || {
            let mut arena = ParseArena::new();
            let start = arena.push_pos(StrIdx(1), 1, 0, 2);
            let end = arena.push_pos(StrIdx(1), 1, 0, 3);
            let a = arena.mk_loc(start, end);
            let b = arena.mk_loc(start, end);
            (arena, a, b)
        };
        let (arena, a, b) = make_arena();
        let first = ctx.intern_ast_loc(&arena, a);
        let moved = Box::new(arena);
        assert_eq!(first, ctx.intern_ast_loc(&moved, a));
        let distinct = ctx.intern_ast_loc(&moved, b);
        assert_ne!(first, distinct);
        assert_eq!(ctx.resolve_loc(first), ctx.resolve_loc(distinct));
        let (other, a, _) = make_arena();
        assert_ne!(first, ctx.intern_ast_loc(&other, a));
        assert_eq!(ctx.local_decl_loc_count(), 1);

        let mut free = ParseArena::with_locations(false);
        let a = free.mk_loc(free.none_pos(), free.none_pos());
        let loc = ctx.intern_ast_loc(&free, a);
        assert_eq!(loc.kind(), DeclLocKind::Source);
        assert_eq!(
            ctx.local_decl_loc_count(),
            1,
            "location-free builds allocate no records"
        );
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
            instances: Vec::new(),
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
