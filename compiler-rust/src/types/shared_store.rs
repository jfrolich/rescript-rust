//! Process-wide pool of immutable dependency type graphs.
//!
//! Every worker of an in-process build loads the same `.cmi`-equivalent
//! signatures (OCaml: one `persistent_structures` entry per process,
//! `compiler/ml/env.ml:669-678`). The per-worker `ThreadTypeStore` already
//! avoids re-internalizing a signature for every unit on one worker; this pool
//! goes one step further and internalizes each dependency graph once per
//! build, for all workers.
//!
//! Layout follows Zig's `InternPool`: a node index is a position in one
//! global index space, split into fixed-size pages. Each published graph owns
//! a page-aligned range, and the page table maps a page to its graph through a
//! `OnceLock`, so readers on any thread resolve an index with two loads and no
//! lock. A graph is complete before its pages are published and is never
//! written afterwards: OCaml never mutates generic dependency nodes in place
//! outside a compilation (`Btype.copy`/`Ctype.instance`), and the Rust writes
//! that do reach a dependency node (`link_type`, level marking, abbreviation
//! memos) go to the reading compilation's overlays in `TypeContext`.
//!
//! References carry `type_expr::STORE_REF_TAG | SHARED_REF_TAG`.

use super::type_expr::{TypeDesc, TypeExprRef};
use super::variant_runtime::{Layout, LayoutRef};
use crate::cmi::persistent_env::PersStruct;
use crate::cmi::portable_types::PortablePersStruct;
use crate::fast_hash::AHashMap as HashMap;
use crate::intern::StrIdx;
use std::sync::atomic::{AtomicU32, Ordering};
use std::sync::{Arc, Mutex, OnceLock, RwLock};

const PAGE_BITS: u32 = 10;
const PAGE_SIZE: u32 = 1 << PAGE_BITS;
/// Index space of one pool (64M nodes, a 64K-entry page table); a graph
/// that does not fit falls back to worker-local internalization.
const MAX_SHARED_INDEX: u32 = 1 << 26;

/// Node ids of shared nodes: disjoint from compilation-local ids and from
/// worker-store ids (`thread_store::STORE_TYPE_ID_BASE = 1 << 30`).
const SHARED_TYPE_ID_BASE: i32 = 0x6000_0000;

/// First synthetic longident component index owned by the pool. Worker
/// stores use `0xE000_0000..`, compilation contexts `0xF000_0000..`.
const SHARED_LONGIDENT_IDX_BASE: u32 = 0xD000_0000;

/// One immutable dependency node.
#[derive(Debug)]
pub(crate) struct SharedTypeNode {
    pub(crate) desc: TypeDesc,
    pub(crate) level: i32,
    pub(crate) id: i32,
}

/// One published dependency graph: nodes and variant layouts at
/// `base..base + len`.
#[derive(Debug)]
pub(crate) struct SharedGraph {
    base: u32,
    nodes: Box<[SharedTypeNode]>,
    layouts: Box<[Layout]>,
    /// Locations of the graph's declarations and type labels
    /// (`DeclLocKind::Shared` handles naming this graph by `base`).
    locations: Box<[crate::location::Location]>,
}

/// Internalization slot of one portable dependency signature.
struct PersSlot {
    /// Keeps the portable struct alive so its address cannot be reused as a
    /// key for another graph.
    _owner: Arc<PortablePersStruct>,
    ps: OnceLock<Option<Arc<PersStruct>>>,
}

/// Page table: page number -> the graph published on that page. Readers keep
/// their own handle to it (`SharedPages::clone`) so a node read does not
/// go through the pool.
pub(crate) type SharedPages = Arc<[OnceLock<Arc<SharedGraph>>]>;

/// Location `index` of the graph published at `base`.
pub(crate) fn page_location(
    pages: &[OnceLock<Arc<SharedGraph>>],
    base: u32,
    index: usize,
) -> crate::location::Location {
    let graph = pages[(base >> PAGE_BITS) as usize]
        .get()
        .expect("shared declaration location refers to an unpublished graph");
    assert_eq!(
        graph.base, base,
        "shared declaration location names no graph"
    );
    graph.locations[index]
}

/// Resolve shared node `idx` through a page table.
#[inline]
pub(crate) fn page_node(pages: &[OnceLock<Arc<SharedGraph>>], idx: u32) -> &SharedTypeNode {
    let graph = pages[(idx >> PAGE_BITS) as usize]
        .get()
        .expect("shared type index refers to an unpublished page");
    &graph.nodes[(idx - graph.base) as usize]
}

/// Node descriptors with levels, variant layouts and locations of a graph
/// being published.
pub(crate) type SharedGraphParts = (
    Vec<(TypeDesc, i32)>,
    Vec<Layout>,
    Vec<crate::location::Location>,
);

pub(crate) struct SharedTypePool {
    generation: u64,
    pages: SharedPages,
    next_index: AtomicU32,
    pers: Mutex<HashMap<usize, Arc<PersSlot>>>,
    longident_names: RwLock<HashMap<u32, String>>,
    next_longident_idx: AtomicU32,
    /// The next origin of an identifier block of a published graph.
    next_ident_origin: AtomicU32,
}

impl SharedTypePool {
    /// An identifier origin for a graph being published.
    pub(crate) fn fresh_ident_origin(&self) -> crate::ident::IdentOrigin {
        use crate::ident::IdentOrigin;
        let span = IdentOrigin::SHARED.end - IdentOrigin::SHARED.start;
        let n = self.next_ident_origin.fetch_add(1, Ordering::Relaxed);
        IdentOrigin::new(IdentOrigin::SHARED.start + n % span)
    }

    fn new(generation: u64) -> Self {
        let pages = (0..MAX_SHARED_INDEX / PAGE_SIZE)
            .map(|_| OnceLock::new())
            .collect();
        SharedTypePool {
            generation,
            pages,
            next_index: AtomicU32::new(0),
            pers: Mutex::new(HashMap::new()),
            longident_names: RwLock::new(HashMap::new()),
            next_longident_idx: AtomicU32::new(SHARED_LONGIDENT_IDX_BASE),
            next_ident_origin: AtomicU32::new(0),
        }
    }

    pub(crate) fn pages(&self) -> SharedPages {
        self.pages.clone()
    }

    #[inline]
    fn graph(&self, idx: u32) -> &SharedGraph {
        self.pages[(idx >> PAGE_BITS) as usize]
            .get()
            .expect("shared type index refers to an unpublished page")
    }

    pub(crate) fn contains(&self, idx: u32) -> bool {
        self.pages
            .get((idx >> PAGE_BITS) as usize)
            .and_then(OnceLock::get)
            .is_some_and(|graph| ((idx - graph.base) as usize) < graph.nodes.len())
    }

    pub(crate) fn layout(&self, layout: LayoutRef) -> &Layout {
        let idx = layout.shared_index();
        let graph = self.graph(idx);
        &graph.layouts[(idx - graph.base) as usize]
    }

    /// Reserve a page-aligned index range for a graph with `nodes` nodes and
    /// `layouts` variant layouts; `None` when the pool is full.
    fn reserve(&self, nodes: usize, layouts: usize) -> Option<(u32, u32)> {
        let len = u32::try_from(nodes.max(layouts).max(1)).ok()?;
        let reserved = len.checked_add(PAGE_SIZE - 1)? & !(PAGE_SIZE - 1);
        let base = self.next_index.fetch_add(reserved, Ordering::Relaxed);
        let end = base.checked_add(reserved)?;
        (end <= MAX_SHARED_INDEX).then_some((base, end))
    }

    /// Build and publish one graph. `build` receives the base index and
    /// returns the node descriptors (with levels) and layouts, which must
    /// match the reserved sizes, and the graph's location table.
    pub(crate) fn publish(
        &self,
        nodes: usize,
        layouts: usize,
        build: impl FnOnce(u32) -> SharedGraphParts,
    ) -> Option<u32> {
        let (base, end) = self.reserve(nodes, layouts)?;
        let (descs, built_layouts, locations) = build(base);
        assert_eq!(descs.len(), nodes, "shared graph node count changed");
        assert_eq!(
            built_layouts.len(),
            layouts,
            "shared graph layout count changed"
        );
        let graph = Arc::new(SharedGraph {
            base,
            nodes: descs
                .into_iter()
                .enumerate()
                .map(|(offset, (desc, level))| SharedTypeNode {
                    desc,
                    level,
                    id: SHARED_TYPE_ID_BASE + (base as i32) + offset as i32,
                })
                .collect(),
            layouts: built_layouts.into_boxed_slice(),
            locations: locations.into_boxed_slice(),
        });
        for page in (base >> PAGE_BITS)..(end >> PAGE_BITS) {
            let published = self.pages[page as usize].set(graph.clone());
            assert!(published.is_ok(), "shared type page published twice");
        }
        Some(base)
    }

    /// The shared internalization of `pps`, building it with `build` the
    /// first time any worker asks. Concurrent requests for the same struct
    /// wait for the first builder. `None` when `build` could not place the
    /// graph in the pool.
    pub(crate) fn pers_struct(
        &self,
        pps: &Arc<PortablePersStruct>,
        build: impl FnOnce() -> Option<Arc<PersStruct>>,
    ) -> Option<Arc<PersStruct>> {
        let key = Arc::as_ptr(pps) as usize;
        let slot = self
            .pers
            .lock()
            .unwrap()
            .entry(key)
            .or_insert_with(|| {
                Arc::new(PersSlot {
                    _owner: pps.clone(),
                    ps: OnceLock::new(),
                })
            })
            .clone();
        slot.ps.get_or_init(build).clone()
    }

    pub(crate) fn intern_longident_name(&self, name: &str) -> StrIdx {
        let raw = self.next_longident_idx.fetch_add(1, Ordering::Relaxed);
        assert!(raw < 0xE000_0000, "shared longident index range exhausted");
        self.longident_names
            .write()
            .unwrap()
            .insert(raw, name.to_string());
        StrIdx::from_raw(raw)
    }

    pub(crate) fn longident_name(&self, idx: StrIdx) -> Option<String> {
        let raw = idx.raw();
        if !(SHARED_LONGIDENT_IDX_BASE..0xE000_0000).contains(&raw) {
            return None;
        }
        self.longident_names.read().unwrap().get(&raw).cloned()
    }
}

/// Shared reference to node `offset` of the graph published at `base`.
#[inline]
pub(crate) fn shared_ref(base: u32, offset: usize) -> TypeExprRef {
    TypeExprRef::from_shared_index(base + offset as u32)
}

static POOL: Mutex<Option<Arc<SharedTypePool>>> = Mutex::new(None);

/// The pool of build `generation`; a pool from an earlier build is replaced
/// (and freed once the last worker store holding it is dropped).
pub(crate) fn pool_for(generation: u64) -> Arc<SharedTypePool> {
    let mut slot = POOL.lock().unwrap();
    match &*slot {
        Some(pool) if pool.generation == generation => pool.clone(),
        _ => {
            let pool = Arc::new(SharedTypePool::new(generation));
            *slot = Some(pool.clone());
            pool
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn published_graphs_are_readable_from_other_threads() {
        let pool = Arc::new(SharedTypePool::new(u64::MAX));
        let base = pool
            .publish(3, 0, |_| {
                (
                    vec![
                        (TypeDesc::Tnil, 7),
                        (
                            TypeDesc::Tvar(
                                Some("a".into()),
                                crate::types::type_expr::VarDescBlock::OWN,
                            ),
                            8,
                        ),
                        (TypeDesc::Tnil, 9),
                    ],
                    Vec::new(),
                    vec![crate::location::Location::in_file(StrIdx::from_raw(4))],
                )
            })
            .unwrap();
        let second = pool
            .publish(1, 0, |_| {
                (vec![(TypeDesc::Tnil, 1)], Vec::new(), Vec::new())
            })
            .unwrap();
        assert_eq!(second % PAGE_SIZE, 0);
        assert_ne!(base, second);
        let reader = pool.clone();
        std::thread::spawn(move || {
            assert_eq!(page_node(&reader.pages(), base + 1).level, 8);
            assert!(matches!(
                page_node(&reader.pages(), base + 1).desc,
                TypeDesc::Tvar(Some(_), ..)
            ));
            assert!(reader.contains(base + 2));
            assert_eq!(
                page_location(&reader.pages(), base, 0),
                crate::location::Location::in_file(StrIdx::from_raw(4))
            );
            assert!(!reader.contains(base + 3));
            let r = shared_ref(base, 2);
            assert!(r.is_store() && r.is_shared());
            assert_eq!(r.shared_index(), base + 2);
        })
        .join()
        .unwrap();
    }
}
