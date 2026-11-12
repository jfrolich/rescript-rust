//! Process-wide pool of immutable dependency type graphs.
//!
//! Every worker of an in-process build loads the same `.cmi`-equivalent
//! signatures (OCaml: one `persistent_structures` entry per process,
//! `compiler/ml/env.ml:669-678`). The per-worker `ThreadTypeStore` already
//! keeps what one worker builds; this pool holds each dependency graph once
//! per build, for all workers. It belongs to the build's `World`
//! (`types/world.rs`), whose unit table says which graph is which unit's.
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

use super::type_expr::{
    PackageLidsRef, RowDesc, RowDescRef, SHARED_REF_BITS, TypeArg, TypeArgList, TypeDesc,
    TypeExprRef, TypeRefList,
};
use crate::parser::longident::Longident;
use super::variant_runtime::{Layout, LayoutRef};
use crate::fast_hash::AHashMap as HashMap;
use crate::intern::StrIdx;
use std::sync::atomic::{AtomicU32, Ordering};
use std::sync::{Arc, OnceLock, RwLock};

const PAGE_BITS: u32 = 10;
const PAGE_SIZE: u32 = 1 << PAGE_BITS;
/// Index space of one pool (64M nodes, a 64K-entry page table); a graph
/// that does not fit falls back to worker-local internalization.
const MAX_SHARED_INDEX: u32 = 1 << 26;

/// First synthetic longident component index owned by the pool. Worker
/// stores use `0xE000_0000..`, compilation contexts `0xF000_0000..`.
const SHARED_LONGIDENT_IDX_BASE: u32 = 0xD000_0000;

/// One immutable dependency node.
#[derive(Debug)]
pub(crate) struct SharedTypeNode {
    pub(crate) desc: TypeDesc,
    pub(crate) level: i32,
}

/// One published dependency graph: nodes and variant layouts at
/// `base..base + len`.
#[derive(Debug)]
pub(crate) struct SharedGraph {
    base: u32,
    nodes: Box<[SharedTypeNode]>,
    /// Descriptor payloads, indexed after the nodes (see
    /// [`SharedGraphSizes`]).
    lists: Box<[TypeExprRef]>,
    args: Box<[TypeArg]>,
    rows: Box<[RowDesc]>,
    lids: Box<[Vec<Longident>]>,
    layouts: Box<[Layout]>,
    /// Locations of the graph's declarations and type labels
    /// (`DeclLocKind::Shared` handles naming this graph by `base`).
    locations: super::decl_loc::DeclLocTable,
    /// Cold serialization metadata; never consulted by type-node readers.
    pub(crate) carried: crate::cmi::shared_reader::Carried,
}

impl SharedGraph {
    /// A graph retained for hashing/storage, before any importer needs pool addresses.
    pub(crate) fn detached(parts: SharedGraphParts) -> Self {
        let mut graph = Self::from_parts(0, parts);
        graph.base = u32::MAX;
        graph
    }

    pub(crate) fn is_detached(&self) -> bool {
        self.base == u32::MAX
    }

    /// The first importer gives an immutable detached graph pool addresses.
    /// Storage may still be reading the original arrays concurrently.
    pub(crate) fn copy_parts(&self) -> SharedGraphParts {
        SharedGraphParts {
            nodes: self.nodes.iter().map(|n| (n.desc, n.level)).collect(),
            payloads: SharedGraphPayloads {
                lists: self.lists.to_vec(),
                args: self.args.to_vec(),
                rows: self.rows.to_vec(),
                lids: self.lids.to_vec(),
            },
            layouts: self.layouts.to_vec(),
            locations: self.locations.clone(),
            carried: self.carried.clone(),
        }
    }

    pub(crate) fn sizes(&self) -> SharedGraphSizes {
        SharedGraphSizes {
            nodes: self.nodes.len(),
            layouts: self.layouts.len(),
            list_items: self.lists.len(),
            arg_items: self.args.len(),
            rows: self.rows.len(),
            lids: self.lids.len(),
        }
    }

    /// Move an exclusively owned detached graph into its reserved pool slot.
    pub(crate) fn take_parts(&mut self) -> SharedGraphParts {
        assert!(self.is_detached());
        SharedGraphParts {
            nodes: std::mem::take(&mut self.nodes)
                .into_vec()
                .into_iter()
                .map(|n| (n.desc, n.level))
                .collect(),
            payloads: SharedGraphPayloads {
                lists: std::mem::take(&mut self.lists).into_vec(),
                args: std::mem::take(&mut self.args).into_vec(),
                rows: std::mem::take(&mut self.rows).into_vec(),
                lids: std::mem::take(&mut self.lids).into_vec(),
            },
            layouts: std::mem::take(&mut self.layouts).into_vec(),
            locations: std::mem::take(&mut self.locations),
            carried: std::mem::take(&mut self.carried),
        }
    }

    fn from_parts(base: u32, parts: SharedGraphParts) -> Self {
        Self {
            base,
            nodes: parts
                .nodes
                .into_iter()
                .map(|(desc, level)| SharedTypeNode { desc, level })
                .collect(),
            lists: parts.payloads.lists.into_boxed_slice(),
            args: parts.payloads.args.into_boxed_slice(),
            rows: parts.payloads.rows.into_boxed_slice(),
            lids: parts.payloads.lids.into_boxed_slice(),
            layouts: parts.layouts.into_boxed_slice(),
            locations: parts.locations.without_interning_indexes(),
            carried: parts.carried,
        }
    }

    /// The graph's first shared index.
    pub(crate) fn base(&self) -> u32 {
        self.base
    }

    /// The nodes, by offset from the base.
    pub(crate) fn nodes(&self) -> &[SharedTypeNode] {
        &self.nodes
    }

    /// The variant layouts, by offset from the base.
    pub(crate) fn layouts(&self) -> &[Layout] {
        &self.layouts
    }

    /// The location table of the graph's declarations and labels.
    pub(crate) fn locations(&self) -> &super::decl_loc::DeclLocTable {
        &self.locations
    }

    /// The offset of the node `r` names, `None` when it is no node of this
    /// graph.
    pub(crate) fn node_offset(&self, r: TypeExprRef) -> Option<usize> {
        if self.is_detached() {
            return (!r.is_store() && r.index() < self.nodes.len()).then_some(r.index());
        }
        if !r.is_shared() {
            return None;
        }
        let offset = r.shared_index().checked_sub(self.base)? as usize;
        (offset < self.nodes.len()).then_some(offset)
    }

    /// Offset from the base of a payload index of this graph.
    fn payload_offset(&self, raw: u32) -> usize {
        ((raw & !SHARED_REF_BITS) - self.base) as usize
    }

    /// The elements of a type list of one of this graph's nodes.
    pub(crate) fn list(&self, list: TypeRefList) -> &[TypeExprRef] {
        if list.is_empty() {
            return &[];
        }
        let start = if self.is_detached() {
            list.raw_start() as usize
        } else {
            self.payload_offset(list.raw_start()) - self.nodes.len()
        };
        &self.lists[start..start + list.len()]
    }

    /// The parameters of an arrow node of this graph.
    pub(crate) fn args(&self, list: TypeArgList) -> &[TypeArg] {
        if list.is_empty() {
            return &[];
        }
        let start = if self.is_detached() {
            list.raw_start() as usize
        } else {
            self.payload_offset(list.raw_start()) - self.nodes.len() - self.lists.len()
        };
        &self.args[start..start + list.len()]
    }

    /// The row of a variant node of this graph.
    pub(crate) fn row(&self, row: RowDescRef) -> &RowDesc {
        let index = if self.is_detached() {
            row.raw() as usize
        } else {
            self.payload_offset(row.raw()) - self.nodes.len() - self.lists.len() - self.args.len()
        };
        &self.rows[index]
    }

    /// The constraint names of a package node of this graph.
    pub(crate) fn lids(&self, lids: PackageLidsRef) -> &[Longident] {
        let index = if self.is_detached() {
            lids.raw() as usize
        } else {
            self.payload_offset(lids.raw())
                - self.nodes.len()
                - self.lists.len()
                - self.args.len()
                - self.rows.len()
        };
        &self.lids[index]
    }
}

/// The graph published at `base`.
pub(crate) fn graph_at(pages: &[OnceLock<Arc<SharedGraph>>], base: u32) -> &Arc<SharedGraph> {
    let graph = pages[(base >> PAGE_BITS) as usize]
        .get()
        .expect("no shared graph is published at this index");
    assert_eq!(graph.base, base, "shared index is not the base of a graph");
    graph
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
    graph.locations.get(index)
}

pub(crate) fn page_location_identity(
    pages: &[OnceLock<Arc<SharedGraph>>],
    base: u32,
    index: usize,
) -> Option<super::decl_loc::LocationIdentity> {
    let graph = pages[(base >> PAGE_BITS) as usize]
        .get()
        .expect("shared location refers to an unpublished graph");
    assert_eq!(graph.base, base);
    graph.locations.identity(index)
}

/// The graph owning shared index `idx`, and `idx`'s offset in it.
#[inline]
fn page_graph(pages: &[OnceLock<Arc<SharedGraph>>], raw: u32) -> (&SharedGraph, usize) {
    let idx = raw & !SHARED_REF_BITS;
    let graph = pages[(idx >> PAGE_BITS) as usize]
        .get()
        .expect("shared type index refers to an unpublished page");
    (graph, (idx - graph.base) as usize)
}

/// The elements of a shared type list.
#[inline]
pub(crate) fn page_list(pages: &[OnceLock<Arc<SharedGraph>>], list: TypeRefList) -> &[TypeExprRef] {
    let (graph, offset) = page_graph(pages, list.raw_start());
    let start = offset - graph.nodes.len();
    &graph.lists[start..start + list.len()]
}

/// The parameters of a shared arrow parameter list.
#[inline]
pub(crate) fn page_args(pages: &[OnceLock<Arc<SharedGraph>>], list: TypeArgList) -> &[TypeArg] {
    let (graph, offset) = page_graph(pages, list.raw_start());
    let start = offset - graph.nodes.len() - graph.lists.len();
    &graph.args[start..start + list.len()]
}

/// A shared row.
#[inline]
pub(crate) fn page_row(pages: &[OnceLock<Arc<SharedGraph>>], row: RowDescRef) -> &RowDesc {
    let (graph, offset) = page_graph(pages, row.raw());
    &graph.rows[offset - graph.nodes.len() - graph.lists.len() - graph.args.len()]
}

/// The constraint names of a shared package type.
#[inline]
pub(crate) fn page_lids(
    pages: &[OnceLock<Arc<SharedGraph>>],
    lids: PackageLidsRef,
) -> &[Longident] {
    let (graph, offset) = page_graph(pages, lids.raw());
    &graph.lids
        [offset - graph.nodes.len() - graph.lists.len() - graph.args.len() - graph.rows.len()]
}

#[inline]
pub(crate) fn page_node(pages: &[OnceLock<Arc<SharedGraph>>], idx: u32) -> &SharedTypeNode {
    let graph = pages[(idx >> PAGE_BITS) as usize]
        .get()
        .expect("shared type index refers to an unpublished page");
    &graph.nodes[(idx - graph.base) as usize]
}

/// Sizes of a graph to publish. The graph's shared indices are its nodes,
/// then its type-list elements, arrow parameters, rows and package
/// constraint lists, in that order; variant layouts index separately from
/// the same base.
#[derive(Clone, Copy, Debug, Default)]
pub(crate) struct SharedGraphSizes {
    pub(crate) nodes: usize,
    pub(crate) list_items: usize,
    pub(crate) arg_items: usize,
    pub(crate) rows: usize,
    pub(crate) lids: usize,
    pub(crate) layouts: usize,
}

impl SharedGraphSizes {
    /// Offset of the first type-list element from the graph's base.
    pub(crate) fn lists_start(&self) -> usize {
        self.nodes
    }

    pub(crate) fn args_start(&self) -> usize {
        self.lists_start() + self.list_items
    }

    pub(crate) fn rows_start(&self) -> usize {
        self.args_start() + self.arg_items
    }

    pub(crate) fn lids_start(&self) -> usize {
        self.rows_start() + self.rows
    }

    fn indices(&self) -> usize {
        self.lids_start() + self.lids
    }
}

/// Descriptor payloads of a graph being published (see [`SharedGraphSizes`]).
#[derive(Default)]
pub(crate) struct SharedGraphPayloads {
    pub(crate) lists: Vec<TypeExprRef>,
    pub(crate) args: Vec<TypeArg>,
    pub(crate) rows: Vec<RowDesc>,
    pub(crate) lids: Vec<Vec<Longident>>,
}

/// Node descriptors with levels, payloads, variant layouts and locations of
/// a graph being published.
pub(crate) struct SharedGraphParts {
    pub(crate) nodes: Vec<(TypeDesc, i32)>,
    pub(crate) payloads: SharedGraphPayloads,
    pub(crate) layouts: Vec<Layout>,
    pub(crate) locations: super::decl_loc::DeclLocTable,
    pub(crate) carried: crate::cmi::shared_reader::Carried,
}

pub(crate) struct SharedTypePool {
    pages: SharedPages,
    next_index: AtomicU32,
    shuffle: Option<u64>,
    reservations: AtomicU32,
    longident_names: Arc<RwLock<HashMap<u32, String>>>,
    next_longident_idx: AtomicU32,
}

impl SharedTypePool {












    pub(crate) fn new() -> Self {
        static SEED: OnceLock<Option<u64>> = OnceLock::new();
        Self::with_seed(*SEED.get_or_init(|| {
            std::env::var("RESCRIPT_WORLD_SHUFFLE").ok()?.parse().ok()
        }))
    }

    fn with_seed(shuffle: Option<u64>) -> Self {
        let pages = (0..MAX_SHARED_INDEX / PAGE_SIZE)
            .map(|_| OnceLock::new())
            .collect();
        SharedTypePool {
            pages,
            next_index: AtomicU32::new(0),
            shuffle,
            reservations: AtomicU32::new(0),
            longident_names: Arc::new(RwLock::new(HashMap::new())),
            next_longident_idx: AtomicU32::new(SHARED_LONGIDENT_IDX_BASE),
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
        let base = if let Some(seed) = self.shuffle {
            let n = self.reservations.fetch_add(1, Ordering::Relaxed);
            // SplitMix64: a fixed mixer, independent of process hash seeds.
            let mut hash = seed.wrapping_add(u64::from(n).wrapping_mul(0x9e3779b97f4a7c15));
            hash = (hash ^ (hash >> 30)).wrapping_mul(0xbf58476d1ce4e5b9);
            hash = (hash ^ (hash >> 27)).wrapping_mul(0x94d049bb133111eb);
            hash ^= hash >> 31;
            let skip = (hash % 4) as u32 * PAGE_SIZE;
            self.next_index.fetch_add(reserved + skip, Ordering::Relaxed) + skip
        } else {
            self.next_index.fetch_add(reserved, Ordering::Relaxed)
        };
        let end = base.checked_add(reserved)?;
        (end <= MAX_SHARED_INDEX).then_some((base, end))
    }

    /// Build and publish one graph. `build` receives the base index and
    /// returns the graph's parts, which must match `sizes`.
    pub(crate) fn publish(
        &self,
        sizes: SharedGraphSizes,
        build: impl FnOnce(u32) -> SharedGraphParts,
    ) -> Option<u32> {
        let (base, end) = self.reserve(sizes.indices(), sizes.layouts)?;
        let SharedGraphParts {
            nodes: descs,
            payloads,
            layouts: built_layouts,
            locations,
            carried,
        } = build(base);
        assert_eq!(descs.len(), sizes.nodes, "shared graph node count changed");
        assert_eq!(
            payloads.lists.len(),
            sizes.list_items,
            "shared graph list size changed"
        );
        assert_eq!(
            payloads.args.len(),
            sizes.arg_items,
            "shared graph parameter count changed"
        );
        assert_eq!(
            payloads.rows.len(),
            sizes.rows,
            "shared graph row count changed"
        );
        assert_eq!(
            payloads.lids.len(),
            sizes.lids,
            "shared graph package count changed"
        );
        assert_eq!(
            built_layouts.len(),
            sizes.layouts,
            "shared graph layout count changed"
        );
        crate::perf_counters::record_signature_nodes_frozen(sizes.nodes);
        let graph = Arc::new(SharedGraph::from_parts(base, SharedGraphParts {
            nodes: descs, payloads, layouts: built_layouts, locations, carried,
        }));
        for page in (base >> PAGE_BITS)..(end >> PAGE_BITS) {
            let published = self.pages[page as usize].set(graph.clone());
            assert!(published.is_ok(), "shared type page published twice");
        }
        Some(base)
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

    pub(crate) fn names(&self) -> Arc<RwLock<HashMap<u32, String>>> {
        self.longident_names.clone()
    }

    pub(crate) fn names_ref(&self) -> &RwLock<HashMap<u32, String>> {
        &self.longident_names
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

#[cfg(test)]
mod tests {
    use super::*;



    #[test]
    fn shuffled_graphs_keep_descriptors_and_levels() {
        let pools = [
            SharedTypePool::with_seed(Some(1)),
            SharedTypePool::with_seed(Some(2)),
        ];
        let mut bases = [Vec::new(), Vec::new()];
        for (index, pool) in pools.iter().enumerate() {
            for graph in 0..3 {
                let base = pool
                    .publish(
                        SharedGraphSizes {
                            nodes: 2,
                            ..Default::default()
                        },
                        |_| SharedGraphParts {
                            nodes: vec![(TypeDesc::Tnil, graph), (TypeDesc::Tvar(None), graph + 1)],
                            payloads: Default::default(),
                            layouts: Vec::new(),
                            locations: Default::default(),
                            carried: Default::default(),
                        },
                    )
                    .unwrap();
                bases[index].push(base);
                assert!(matches!(page_node(&pool.pages, base).desc, TypeDesc::Tnil));
                assert!(matches!(
                    page_node(&pool.pages, base + 1).desc,
                    TypeDesc::Tvar(None)
                ));
                assert_eq!(page_node(&pool.pages, base).level, graph);
                assert_eq!(page_node(&pool.pages, base + 1).level, graph + 1);
            }
        }
        assert_ne!(bases[0], bases[1]);
        assert!(
            bases
                .iter()
                .any(|bases| bases.windows(2).any(|pair| pair[1] - pair[0] > PAGE_SIZE))
        );
    }

    #[test]
    fn published_graphs_are_readable_from_other_threads() {
        let pool = Arc::new(SharedTypePool::new());
        let base = pool
            .publish(
                SharedGraphSizes {
                    nodes: 3,
                    ..Default::default()
                },
                |_| SharedGraphParts {
                    nodes: vec![
                        (TypeDesc::Tnil, 7),
                        (
                            TypeDesc::Tvar(
                                Some("a".into()),
                            ),
                            8,
                        ),
                        (TypeDesc::Tnil, 9),
                    ],
                    payloads: Default::default(),
                    layouts: Vec::new(),
                    carried: Default::default(),
                    locations: [crate::location::Location::in_file(StrIdx::from_raw(4))]
                        .into_iter()
                        .collect(),
                },
            )
            .unwrap();
        let second = pool
            .publish(
                SharedGraphSizes {
                    nodes: 1,
                    ..Default::default()
                },
                |_| SharedGraphParts {
                    nodes: vec![(TypeDesc::Tnil, 1)],
                    payloads: Default::default(),
                    layouts: Vec::new(),
                    locations: Default::default(),
                    carried: Default::default(),
                },
            )
            .unwrap();
        assert_eq!(second % PAGE_SIZE, 0);
        assert_ne!(base, second);
        let reader = pool.clone();
        std::thread::spawn(move || {
            assert_eq!(page_node(&reader.pages(), base + 1).level, 8);
            assert!(matches!(
                page_node(&reader.pages(), base + 1).desc,
                TypeDesc::Tvar(Some(_))
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
