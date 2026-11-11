//! Reusable visit marks and copy tables for type-graph walks.
//!
//! OCaml marks the nodes a walk has seen in the nodes themselves
//! (`Btype.mark_type` / `unmark_type` flip the level sign). Rust type nodes
//! of other compilations are shared, so marks live beside the graph instead:
//! compilation-local nodes get dense arrays indexed by node (allocated a page
//! at a time), stamped with an epoch so that clearing is one increment, and store nodes go into a hash
//! table that keeps its capacity between walks. Tables come from a per-thread
//! pool, so a walk allocates nothing once the pool is warm.
//!
//! Membership and lookups are exact per [`TypeExprRef`], like the hash sets
//! these replace. Nothing iterates a table, so no result depends on order.

use std::cell::RefCell;
use std::hash::{BuildHasherDefault, Hasher};
use std::ops::{Deref, DerefMut};

use super::type_expr::TypeExprRef;

/// Multiplicative hash of a node handle (handles are already unique ids).
#[derive(Default, Clone, Copy)]
pub(crate) struct NodeHasher(u64);

impl Hasher for NodeHasher {
    #[inline]
    fn finish(&self) -> u64 {
        self.0
    }

    #[inline]
    fn write(&mut self, bytes: &[u8]) {
        for &b in bytes {
            self.0 = (self.0.rotate_left(8) ^ u64::from(b)).wrapping_mul(0x9E37_79B9_7F4A_7C15);
        }
    }

    #[inline]
    fn write_u32(&mut self, n: u32) {
        self.0 = u64::from(n).wrapping_mul(0x9E37_79B9_7F4A_7C15);
    }
}

type StoreTable<V> = std::collections::HashMap<TypeExprRef, V, BuildHasherDefault<NodeHasher>>;

/// Local nodes per page of marks. Walks touch a few scattered regions of a
/// large local arena, so marks are allocated a page at a time rather than as
/// one array spanning the highest node seen.
const PAGE_BITS: usize = 10;
const PAGE_SIZE: usize = 1 << PAGE_BITS;

/// One page of a [`TypeNodeTable`]: per node, its write epoch and value.
type Page<V> = Box<[(u32, V)]>;

/// Map from type nodes to `V`, cleared in O(1) between uses.
pub(crate) struct TypeNodeTable<V: Copy> {
    epoch: u32,
    /// Per local node, by page: the epoch it was last written in, and its
    /// value. Entries from older epochs are absent.
    pages: Vec<Option<Page<V>>>,
    store: StoreTable<V>,
}

impl<V: Copy> TypeNodeTable<V> {
    fn new() -> Self {
        Self {
            epoch: 1,
            pages: Vec::new(),
            store: StoreTable::default(),
        }
    }

    /// Forget every entry.
    pub(crate) fn clear(&mut self) {
        if self.epoch == u32::MAX {
            self.epoch = 0;
            self.pages.clear();
        }
        self.epoch += 1;
        self.store.clear();
    }

    #[inline]
    pub(crate) fn get(&self, ty: TypeExprRef) -> Option<V> {
        if ty.is_store() {
            return self.store.get(&ty).copied();
        }
        let idx = ty.index();
        let page = self.pages.get(idx >> PAGE_BITS)?.as_ref()?;
        let (epoch, value) = page[idx & (PAGE_SIZE - 1)];
        (epoch == self.epoch).then_some(value)
    }

    /// Set the value of `ty`, returning the previous one.
    #[inline]
    pub(crate) fn insert(&mut self, ty: TypeExprRef, value: V) -> Option<V> {
        if ty.is_store() {
            return self.store.insert(ty, value);
        }
        let idx = ty.index();
        let epoch = self.epoch;
        let page = self.page_mut(idx >> PAGE_BITS, value);
        let slot = &mut page[idx & (PAGE_SIZE - 1)];
        let previous = (slot.0 == epoch).then_some(slot.1);
        *slot = (epoch, value);
        previous
    }

    #[inline]
    fn page_mut(&mut self, page: usize, filler: V) -> &mut [(u32, V)] {
        if page >= self.pages.len() {
            self.pages.resize_with(page + 1, || None);
        }
        self.pages[page].get_or_insert_with(|| vec![(0, filler); PAGE_SIZE].into_boxed_slice())
    }
}

/// Set of visited type nodes.
pub(crate) type TypeVisitSet = TypeNodeTable<()>;

impl TypeNodeTable<()> {
    /// Add `ty`; `false` if it was already present (like `HashSet::insert`).
    #[inline]
    pub(crate) fn visit(&mut self, ty: TypeExprRef) -> bool {
        self.insert(ty, ()).is_none()
    }
}

/// Tables kept per thread for reuse. Bounded so a burst of nested walks does
/// not pin memory forever.
const POOL_LIMIT: usize = 16;
/// Store tables that grew beyond this many entries are dropped, not pooled.
const POOLED_STORE_CAPACITY: usize = 1 << 14;

pub(crate) trait PooledTable: Sized + 'static {
    /// A cleared table from the thread's pool, or a new one.
    fn take() -> Self;
    /// Clear `self` and keep it for the next [`PooledTable::take`].
    fn recycle(self);
}

macro_rules! pooled_table {
    ($value:ty, $pool:ident) => {
        thread_local! {
            static $pool: RefCell<Vec<TypeNodeTable<$value>>> = const { RefCell::new(Vec::new()) };
        }

        impl PooledTable for TypeNodeTable<$value> {
            fn take() -> Self {
                $pool
                    .try_with(|pool| pool.borrow_mut().pop())
                    .ok()
                    .flatten()
                    .unwrap_or_else(TypeNodeTable::new)
            }

            fn recycle(mut self) {
                if self.store.capacity() > POOLED_STORE_CAPACITY {
                    return;
                }
                self.clear();
                $pool
                    .try_with(|pool| {
                        let mut pool = pool.borrow_mut();
                        if pool.len() < POOL_LIMIT {
                            pool.push(self);
                        }
                    })
                    .ok();
            }
        }
    };
}

pooled_table!((), VISIT_SET_POOL);
pooled_table!(TypeExprRef, REF_TABLE_POOL);

/// A cleared table borrowed from the thread's pool, returned on drop.
pub(crate) struct Pooled<T: PooledTable> {
    table: Option<T>,
}

impl<T: PooledTable> Pooled<T> {
    pub(crate) fn take() -> Self {
        Self {
            table: Some(T::take()),
        }
    }
}

impl<T: PooledTable> Deref for Pooled<T> {
    type Target = T;
    #[inline]
    fn deref(&self) -> &T {
        self.table
            .as_ref()
            .expect("pooled table present until drop")
    }
}

impl<T: PooledTable> DerefMut for Pooled<T> {
    #[inline]
    fn deref_mut(&mut self) -> &mut T {
        self.table
            .as_mut()
            .expect("pooled table present until drop")
    }
}

impl<T: PooledTable> Drop for Pooled<T> {
    fn drop(&mut self) {
        if let Some(table) = self.table.take() {
            table.recycle();
        }
    }
}

/// A pooled, empty set of visited type nodes.
pub(crate) fn visit_set() -> Pooled<TypeVisitSet> {
    Pooled::take()
}

/// A pooled, empty map from type nodes to type nodes (copy memo tables).
pub(crate) fn ref_table() -> Pooled<TypeNodeTable<TypeExprRef>> {
    Pooled::take()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn local_and_store_marks_clear_between_uses() {
        let local = TypeExprRef(5);
        let store = TypeExprRef::from_store_index(7);
        {
            let mut set = visit_set();
            assert!(set.visit(local));
            assert!(!set.visit(local));
            assert!(set.visit(store));
            assert!(set.get(store).is_some());
            // A nested walk gets its own table.
            let mut inner = visit_set();
            assert!(inner.get(local).is_none());
            assert!(inner.visit(local));
        }
        let set = visit_set();
        assert!(set.get(local).is_none());
        assert!(set.get(store).is_none());
    }

    #[test]
    fn ref_table_returns_previous_values() {
        let mut table = ref_table();
        let a = TypeExprRef(3);
        let b = TypeExprRef(4000);
        assert_eq!(table.insert(a, b), None);
        assert_eq!(table.insert(a, a), Some(b));
        assert_eq!(table.get(a), Some(a));
        assert_eq!(table.get(b), None);
    }

    #[test]
    fn epoch_wraparound_forgets_old_marks() {
        let mut table = TypeNodeTable::<()>::new();
        table.epoch = u32::MAX;
        assert!(table.visit(TypeExprRef(1)));
        table.clear();
        assert!(table.get(TypeExprRef(1)).is_none());
        assert!(table.visit(TypeExprRef(1)));
    }
}
