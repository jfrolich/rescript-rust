//! Location handles for the typedtree -> raw Lambda conversion.
//!
//! The converter and `Matching` attach a [`LamLoc`] to each node they build
//! instead of a full `Location`. Handle creation is separate from semantic
//! coordinate reads (`__LOC__`, assertion and match-failure payloads), which
//! still read the parse arena and request a located retry when it stores no
//! coordinates.

use crate::raw_lambda::builder::RawLambdaBuilder;
use std::cell::RefCell;
use std::sync::Arc;

use crate::lambda::{LamLoc, LamLocTable};
use crate::location::Location;
use crate::parse_arena::{LocIdx, ParseArena};

/// Builds the per-compilation [`LamLocTable`] of one raw-Lambda conversion.
/// A location-free arena yields an opaque table with no coordinate rows.
#[derive(Debug)]
pub struct LamLocBuilder {
    table: RefCell<LamLocTable>,
    /// Handle already created for each primary arena location index.
    by_idx: RefCell<Vec<Option<LamLoc>>>,
}

impl LamLocBuilder {
    /// A builder for the locations of `arena`; it records coordinates only
    /// when the arena stores locations.
    pub fn new(arena: &ParseArena) -> Self {
        Self {
            table: RefCell::new(if arena.stores_locations() {
                LamLocTable::located(Arc::new(arena.source_file_names()))
            } else {
                LamLocTable::opaque()
            }),
            by_idx: RefCell::new(Vec::new()),
        }
    }

    /// Whether handles resolve to source coordinates.
    pub fn is_located(&self) -> bool {
        self.table.borrow().is_located()
    }

    /// The handle of an arena location, deduplicated by index.
    pub fn from_idx(&self, arena: &ParseArena, idx: LocIdx) -> LamLoc {
        if !self.is_located() {
            return LamLoc::NONE;
        }
        let raw = idx.0 as usize;
        if raw < arena.location_count() {
            if let Some(Some(handle)) = self.by_idx.borrow().get(raw) {
                return *handle;
            }
            let handle = self.intern(arena.to_location(idx));
            let mut by_idx = self.by_idx.borrow_mut();
            if by_idx.len() <= raw {
                by_idx.resize(raw + 1, None);
            }
            by_idx[raw] = Some(handle);
            return handle;
        }
        self.intern(arena.to_location(idx))
    }

    /// The handle of a location that does not come from an arena index
    /// (declaration locations, `Location.none`).
    pub fn intern(&self, loc: Location) -> LamLoc {
        self.table.borrow_mut().intern(loc)
    }

    /// Resolve a handle; `None` for a location-free conversion.
    pub fn get(&self, loc: LamLoc) -> Option<Location> {
        self.table.borrow().get(loc)
    }

    /// The table that resolves every handle created so far.
    pub fn take_table(&self, arena: &ParseArena) -> LamLocTable {
        self.by_idx.borrow_mut().clear();
        let mut table = std::mem::take(&mut *self.table.borrow_mut());
        table.set_file_names(Arc::new(arena.source_file_names()));
        table
    }
}

/// The parse arena, the conversion's location builder and its raw Lambda
/// arena, threaded through
/// `Matching` where OCaml reads `pat.pat_loc` and attaches it to nodes.
pub struct LocArena<'a, B: RawLambdaBuilder> {
    /// The parse arena locations are read from.
    pub arena: &'a ParseArena,
    /// The builder location handles are recorded in.
    pub locs: &'a LamLocBuilder,
    /// The raw Lambda arena the conversion builds into.
    pub b: &'a B,
}

impl<'a, B: RawLambdaBuilder> LocArena<'a, B> {
    /// Bundles the conversion's arenas and location builder.
    pub fn new(arena: &'a ParseArena, locs: &'a LamLocBuilder, b: &'a B) -> Self {
        Self { arena, locs, b }
    }

    /// Node handle for an arena location.
    pub fn lam_loc(&self, idx: LocIdx) -> LamLoc {
        self.locs.from_idx(self.arena, idx)
    }
}

impl<B: RawLambdaBuilder> std::ops::Deref for LocArena<'_, B> {
    type Target = ParseArena;

    fn deref(&self) -> &ParseArena {
        self.arena
    }
}

impl<'a, B: RawLambdaBuilder> Copy for LocArena<'a, B> {}
impl<'a, B: RawLambdaBuilder> Clone for LocArena<'a, B> {
    fn clone(&self) -> Self {
        *self
    }
}
