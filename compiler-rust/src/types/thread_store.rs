//! Per-thread persistent type store.
//!
//! OCaml's `persistent_structures` table (`compiler/ml/env.ml:669-678`)
//! shares loaded signatures within a compilation, but `Res_compmisc.init_path`
//! resets it between units (`compiler/core/res_compmisc.ml:35`). The Rust
//! in-process build avoids re-internalizing immutable raw dependency storage
//! for every unit on a worker. Each compilation isolates descriptor, level,
//! memo and row writes in `TypeContext` overlays; forced component binders and
//! substitution state remain unit-local, matching `initial_env`'s identifier
//! reset (`compiler/core/res_compmisc.ml:49`).
//!
//! References into the store carry `type_expr::STORE_REF_TAG`. The store is
//! `!Send` by construction and is only reached through the exclusive owned lease a
//! `TypeContext` takes at creation; no node or store is refcounted.
//!
//! Design: `projects/in-process-performance/THREAD_TYPE_STORE.md`.

use super::context::TypeArena;
use super::decl::{Signature, TypeDeclaration};
use super::type_expr::{
    AbbrevMemo, AbbrevMemoRef, FieldKind, FieldKindRef, RowField, RowFieldRef, TypeDesc, TypeExpr,
    TypeExprRef,
};
use super::variant_runtime::{Layout, LayoutRef};
use crate::cmi::persistent_env::PersStruct;
use crate::cmi::portable_types::PortablePersStruct;
use crate::intern::StrIdx;
use std::cell::{Cell, RefCell};
use std::collections::{HashMap, HashSet};
use std::ops::Deref;
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};

/// First node id handed out by a store. Compilation-local ids start at the
/// `IdGenerator` base and never reach this range in practice.
const STORE_TYPE_ID_BASE: i32 = 1 << 30;

/// First synthetic longident component index owned by a store. Compilation
/// contexts hand out `0xF000_0000..`; parse arenas count from zero.
const STORE_LONGIDENT_IDX_BASE: u32 = 0xE000_0000;

/// Build generation. `begin_build` bumps it once per `rescript build`; a
/// worker whose store was filled during an earlier build (watch mode) drops
/// that store and starts empty, so no store outlives the build that published
/// the signatures it holds and long-running processes do not accumulate every
/// republished graph.
static BUILD_GENERATION: AtomicU64 = AtomicU64::new(0);

/// Start a new build: stores filled by earlier builds are discarded on their
/// next lease.
pub fn begin_build() {
    BUILD_GENERATION.fetch_add(1, Ordering::SeqCst);
}

/// Dependency signature internalized once into the store.
struct PersEntry {
    /// Keeps the portable struct alive so its address cannot be reused as a
    /// key for a different graph.
    _owner: Arc<PortablePersStruct>,
    ps: Arc<PersStruct>,
}

/// Shared dependency state for one worker thread.
pub(crate) struct ThreadTypeStore {
    types: TypeArena,
    /// Initial memo values of store `Tconstr` nodes (always `Mnil` after
    /// internalization, like `compiler/ml/subst.ml:173-177` on save). Writes go
    /// to the reading compilation's overlay.
    abbrevs: RefCell<Vec<AbbrevMemo>>,
    row_fields: RefCell<Vec<Option<RowField>>>,
    field_kinds: RefCell<Vec<Option<FieldKind>>>,
    variant_layouts: RefCell<Vec<Layout>>,
    next_type_id: Cell<i32>,
    /// Internalized dependency signatures keyed by the identity of the
    /// portable struct they were built from (`compiler/ml/env.ml:669-678`:
    /// one `persistent_structures` entry per read unit).
    pers: RefCell<HashMap<usize, PersEntry>>,
    /// Signatures retained by `pers`; their items keep one address for the
    /// life of the store.
    shared_signatures: RefCell<HashSet<usize>>,
    /// One `Arc` per declaration of a store-owned signature, keyed by the
    /// declaration's address, so per-unit registries share an allocation
    /// instead of cloning every dependency declaration for every compilation.
    type_decl_arcs: RefCell<HashMap<usize, Arc<TypeDeclaration>>>,
    /// Synthetic longident component names used by store `Tpackage` nodes.
    longident_names: RefCell<HashMap<u32, String>>,
    next_longident_idx: Cell<u32>,
    generation: u64,
}

impl ThreadTypeStore {
    fn new() -> Self {
        ThreadTypeStore {
            types: TypeArena::new(),
            abbrevs: RefCell::new(Vec::new()),
            row_fields: RefCell::new(Vec::new()),
            field_kinds: RefCell::new(Vec::new()),
            variant_layouts: RefCell::new(Vec::new()),
            next_type_id: Cell::new(STORE_TYPE_ID_BASE),
            pers: RefCell::new(HashMap::new()),
            shared_signatures: RefCell::new(HashSet::new()),
            type_decl_arcs: RefCell::new(HashMap::new()),
            longident_names: RefCell::new(HashMap::new()),
            next_longident_idx: Cell::new(STORE_LONGIDENT_IDX_BASE),
            generation: BUILD_GENERATION.load(Ordering::SeqCst),
        }
    }

    /// The shared internalization of `pps`, if this thread already built one.
    pub(crate) fn pers_struct(&self, pps: &Arc<PortablePersStruct>) -> Option<Arc<PersStruct>> {
        self.pers
            .borrow()
            .get(&(Arc::as_ptr(pps) as usize))
            .map(|entry| entry.ps.clone())
    }

    /// Record the shared internalization of `pps`.
    pub(crate) fn insert_pers_struct(&self, pps: Arc<PortablePersStruct>, ps: Arc<PersStruct>) {
        self.shared_signatures
            .borrow_mut()
            .insert(Arc::as_ptr(&ps.ps_sig) as usize);
        self.pers
            .borrow_mut()
            .insert(Arc::as_ptr(&pps) as usize, PersEntry { _owner: pps, ps });
    }

    /// Whether `sig` is retained by this store, so references into its items
    /// stay valid for the store's lifetime.
    pub(crate) fn owns_signature(&self, sig: &Arc<Signature>) -> bool {
        self.shared_signatures
            .borrow()
            .contains(&(Arc::as_ptr(sig) as usize))
    }

    /// Shared handle for a declaration that lives inside a store-owned
    /// signature (`owns_signature` must hold for its root). Equal in content to
    /// `Arc::new(decl.clone())`; allocated once per store.
    pub(crate) fn shared_type_decl(&self, decl: &TypeDeclaration) -> Arc<TypeDeclaration> {
        let key = decl as *const TypeDeclaration as usize;
        if let Some(shared) = self.type_decl_arcs.borrow().get(&key) {
            return shared.clone();
        }
        let shared = Arc::new(decl.clone());
        self.type_decl_arcs.borrow_mut().insert(key, shared.clone());
        shared
    }

    pub(crate) fn pers_struct_count(&self) -> usize {
        self.pers.borrow().len()
    }

    /// Intern a longident component name for a store node.
    pub(crate) fn intern_longident_name(&self, name: &str) -> StrIdx {
        let raw = self.next_longident_idx.get();
        self.next_longident_idx.set(raw + 1);
        self.longident_names
            .borrow_mut()
            .insert(raw, name.to_string());
        StrIdx::from_raw(raw)
    }

    pub(crate) fn longident_name(&self, idx: StrIdx) -> Option<String> {
        self.longident_names.borrow().get(&idx.raw()).cloned()
    }

    pub(crate) fn snapshot_longident_names(&self) -> Vec<(u32, String)> {
        self.longident_names
            .borrow()
            .iter()
            .map(|(raw, name)| (*raw, name.clone()))
            .collect()
    }

    #[inline]
    pub(crate) fn node(&self, r: TypeExprRef) -> &TypeExpr {
        self.types.get_at(r.store_index())
    }

    pub(crate) fn type_count(&self) -> usize {
        self.types.len()
    }

    pub(crate) fn alloc_type(&self, desc: TypeDesc, level: i32) -> TypeExprRef {
        let id = self.next_type_id.get();
        self.next_type_id
            .set(id.checked_add(1).expect("thread store type id exhausted"));
        TypeExprRef::from_store_index(self.types.push_raw(TypeExpr::new(desc, level, id)))
    }

    pub(crate) fn abbrev(&self, memo: AbbrevMemoRef) -> AbbrevMemo {
        self.abbrevs
            .borrow()
            .get(memo.store_index())
            .cloned()
            .unwrap_or(AbbrevMemo::Mnil)
    }

    pub(crate) fn alloc_abbrev(&self, memo: AbbrevMemo) -> AbbrevMemoRef {
        let mut abbrevs = self.abbrevs.borrow_mut();
        let idx = abbrevs.len();
        abbrevs.push(memo);
        AbbrevMemoRef::from_store_index(idx)
    }

    pub(crate) fn row_field(&self, rf: RowFieldRef) -> Option<RowField> {
        self.row_fields
            .borrow()
            .get(rf.store_index())
            .cloned()
            .flatten()
    }

    pub(crate) fn alloc_row_field(&self, field: Option<RowField>) -> RowFieldRef {
        let mut row_fields = self.row_fields.borrow_mut();
        let idx = row_fields.len();
        row_fields.push(field);
        RowFieldRef::from_store_index(idx)
    }

    pub(crate) fn alloc_field_kind(&self, kind: Option<FieldKind>) -> FieldKindRef {
        let mut field_kinds = self.field_kinds.borrow_mut();
        let idx = field_kinds.len();
        field_kinds.push(kind);
        FieldKindRef::from_store_index(idx)
    }

    pub(crate) fn with_variant_layout<R>(
        &self,
        layout_ref: LayoutRef,
        read: impl FnOnce(&Layout) -> R,
    ) -> R {
        let layouts = self.variant_layouts.borrow();
        let Some(layout) = layouts.get(layout_ref.store_index()) else {
            panic!("variant layout reference belongs to another thread store")
        };
        read(layout)
    }

    pub(crate) fn alloc_complete_variant_layout(&self, layout: Layout) -> LayoutRef {
        let mut layouts = self.variant_layouts.borrow_mut();
        let idx = layouts.len();
        layouts.push(layout);
        LayoutRef::from_store_index(idx)
    }
}

thread_local! {
    static THREAD_TYPE_STORE: RefCell<Option<Box<ThreadTypeStore>>> = const { RefCell::new(None) };
}

/// Exclusive ownership during a compilation. Nested contexts get a separate
/// store, so level marking cannot leak into another live compilation. Returning
/// the store to the worker slot avoids reference counting and arena teardown.
pub(crate) struct StoreLease(Option<Box<ThreadTypeStore>>);

impl Deref for StoreLease {
    type Target = ThreadTypeStore;

    fn deref(&self) -> &ThreadTypeStore {
        self.0.as_deref().expect("live store lease")
    }
}

impl Drop for StoreLease {
    fn drop(&mut self) {
        // A panic may leave a mark traversal unfinished. Do not reuse its graph.
        if !std::thread::panicking() {
            let store = self.0.take();
            // TLS may already be gone during thread shutdown.
            let _returned = THREAD_TYPE_STORE.try_with(|slot| slot.replace(store));
        }
    }
}

pub(crate) fn current() -> StoreLease {
    let generation = BUILD_GENERATION.load(Ordering::SeqCst);
    StoreLease(Some(THREAD_TYPE_STORE.with(
        |slot| match slot.borrow_mut().take() {
            Some(store) if store.generation == generation => store,
            _ => Box::new(ThreadTypeStore::new()),
        },
    )))
}

const OVERLAY_PAGE: usize = 256;

/// Sparse, page-allocated map from store cell index to this compilation's
/// value for that cell. Reads are two indexed loads; pages are allocated on
/// first write, so a compilation that touches a handful of dependency memos
/// pays for a handful of pages, not for the whole store.
#[derive(Clone, Debug)]
pub(crate) struct PagedOverlay<T> {
    pages: Vec<Option<Box<[Option<T>]>>>,
}

impl<T: Clone> PagedOverlay<T> {
    pub(crate) fn new() -> Self {
        PagedOverlay { pages: Vec::new() }
    }

    #[inline]
    pub(crate) fn get(&self, idx: usize) -> Option<&T> {
        self.pages
            .get(idx / OVERLAY_PAGE)?
            .as_deref()?
            .get(idx % OVERLAY_PAGE)?
            .as_ref()
    }

    pub(crate) fn set(&mut self, idx: usize, value: T) {
        let page = idx / OVERLAY_PAGE;
        if page >= self.pages.len() {
            self.pages.resize_with(page + 1, || None);
        }
        let slot =
            self.pages[page].get_or_insert_with(|| vec![None; OVERLAY_PAGE].into_boxed_slice());
        slot[idx % OVERLAY_PAGE] = Some(value);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::type_expr::GENERIC_LEVEL;

    #[test]
    fn overlay_pages_and_clones_are_independent() {
        let mut overlay = PagedOverlay::new();
        for index in [0, 255, 256, 4096] {
            assert_eq!(overlay.get(index), None);
            overlay.set(index, Some(index));
        }
        let snapshot = overlay.clone();
        overlay.set(255, None);
        assert_eq!(overlay.get(255), Some(&None));
        assert_eq!(snapshot.get(255), Some(&Some(255)));
        assert_eq!(overlay.get(257), None);
        assert!(overlay.pages[2].is_none());
    }

    #[test]
    fn store_lease_is_exclusive_and_reused() {
        // Isolate the worker slot from other unit tests on the harness thread.
        std::thread::spawn(|| {
            let outer = current();
            let outer_ty = outer.alloc_type(TypeDesc::Tnil, GENERIC_LEVEL);
            let nested = current();
            assert_eq!(nested.type_count(), 0);
            nested.alloc_type(TypeDesc::Tvar(None), GENERIC_LEVEL);
            assert!(matches!(*outer.node(outer_ty).desc(), TypeDesc::Tnil));
            drop(nested);
            drop(outer);
            let reused = current();
            assert_eq!(reused.type_count(), 1);
            assert!(matches!(*reused.node(outer_ty).desc(), TypeDesc::Tnil));
        })
        .join()
        .unwrap();
    }

    #[test]
    fn new_build_generation_discards_the_worker_store() {
        std::thread::spawn(|| {
            let lease = current();
            lease.alloc_type(TypeDesc::Tnil, GENERIC_LEVEL);
            drop(lease);
            assert_eq!(current().type_count(), 1);
            begin_build();
            assert_eq!(current().type_count(), 0);
        })
        .join()
        .unwrap();
    }

    #[test]
    fn panicking_compilation_does_not_recycle_store() {
        std::thread::spawn(|| {
            let result = std::panic::catch_unwind(|| {
                let lease = current();
                lease.alloc_type(TypeDesc::Tnil, GENERIC_LEVEL);
                panic!("unfinished traversal");
            });
            assert!(result.is_err());
            assert_eq!(current().type_count(), 0);
        })
        .join()
        .unwrap();
    }
}
