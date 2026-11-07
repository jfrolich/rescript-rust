//! Cold allocation evidence for paths constructed by strengthening/prefixing.
//!
//! `Pdot (p, Ident.name id, pos)` retains both `p` and the identifier's name
//! string (compiler/ml/mtype.ml:62-64, compiler/ml/env.ml:1383-1417).
//! Neither path spelling nor the interned `Name` identifies these allocations.
//! The table gives each such construction a fresh, retained Arc carrier while
//! recording the actual shared prefix separately. Path copies keep the carrier;
//! a fresh construction, even with identical contents, gets another carrier.

use super::Path;
use crate::fast_hash::AHashMap;
use crate::ident::Ident;
use std::sync::Arc;

/// Evidence attached to one constructed dotted path, not to its spelling.
#[derive(Clone)]
pub(crate) struct DottedAllocation {
    /// Keeps the key allocation alive until this table is dropped. The carrier
    /// is a value-equivalent copy of `prefix`; it is not a second OCaml prefix.
    carrier: Arc<Path>,
    pub(crate) prefix: Arc<Path>,
    pub(crate) name: NameAllocation,
    text: crate::name::Name,
    position: i32,
}

impl DottedAllocation {
    pub(crate) fn key(&self) -> usize {
        Arc::as_ptr(&self.carrier) as usize
    }
}

type IdentNameKey = (i32, crate::name::Name, u32);

fn name_key(id: &Ident) -> IdentNameKey {
    (id.stamp(), id.name_atom(), id.origin().get())
}

/// The source allocation of a name string, independent of its interned text.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) enum NameAllocation {
    Ident(IdentNameKey),
    Source { scope: u64, string: u32 },
}

impl NameAllocation {
    pub(crate) fn of_ident(id: &Ident) -> Self {
        Self::Ident(name_key(id))
    }
}

/// Owned by a compilation, worker store, or shared-pool publication scope.
/// No address survives its retained allocation and no contents are used as keys.
#[derive(Default)]
pub(crate) struct PathProvenance {
    dotted: AHashMap<usize, DottedAllocation>,
    names: AHashMap<IdentNameKey, NameAllocation>,
    /// Table size at which unreachable dots are next released.
    next_sweep: usize,
}

/// Smallest table size at which a sweep runs.
const FIRST_SWEEP: usize = 4096;

impl PathProvenance {
    pub(crate) fn record_name(&mut self, id: &Ident, allocation: NameAllocation) {
        if let Some(previous) = self.names.insert(name_key(id), allocation) {
            assert_eq!(previous, allocation, "identifier name allocation changed");
        }
    }

    pub(crate) fn name(&self, id: &Ident) -> Option<NameAllocation> {
        self.names.get(&name_key(id)).copied()
    }

    /// A single allocation of `Pdot(prefix, Ident.name name, pos)`.
    /// Clone the resulting Path to retain that allocation. To construct a new
    /// Pdot, call this again rather than reusing its carrier for another suffix.
    pub(crate) fn dotted(
        &mut self,
        prefix: Arc<Path>,
        text: crate::name::Name,
        name: NameAllocation,
        pos: i32,
    ) -> Path {
        let carrier = Arc::new((*prefix).clone());
        let entry = DottedAllocation {
            carrier: carrier.clone(),
            prefix,
            name,
            text,
            position: pos,
        };
        if self.dotted.len() >= self.next_sweep.max(FIRST_SWEEP) {
            self.release_unreachable();
        }
        assert!(self.dotted.insert(entry.key(), entry).is_none());
        Path::Pdot(carrier, text, pos)
    }

    /// The shared prefix and suffix name allocation of a tracked dot, without
    /// copying its record.
    pub(crate) fn parts(&self, path: &Path) -> Option<(&Arc<Path>, NameAllocation)> {
        self.get(path).map(|entry| (&entry.prefix, entry.name))
    }

    /// Drop the entries no path can reach. A dot is looked up only through a
    /// `Path` holding its carrier, so a carrier held by this table alone
    /// belongs to a dropped allocation. Dropping the entry frees that carrier;
    /// a later allocation at the same address gets a new entry. Sweeps run
    /// when the table has doubled since the last one, so each insertion pays
    /// amortized constant work.
    fn release_unreachable(&mut self) {
        self.dotted
            .retain(|_, entry| Arc::strong_count(&entry.carrier) > 1);
        self.next_sweep = self.dotted.len() * 2;
    }

    pub(crate) fn get(&self, path: &Path) -> Option<&DottedAllocation> {
        let Path::Pdot(carrier, name, position) = path else {
            return None;
        };
        let entry = self.dotted.get(&(Arc::as_ptr(carrier) as usize))?;
        assert_eq!(*name, entry.text, "path carrier reused for another suffix");
        assert_eq!(
            *position, entry.position,
            "path carrier reused for another position"
        );
        Some(entry)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn source_names_share_by_parser_allocation_not_spelling() {
        use crate::types::context::TypeContext;
        let ctx = TypeContext::new(Arc::new(crate::context::IdGenerator::new()));
        let mut arena = crate::parse_arena::ParseArena::new();
        let name = arena.push_string("field");
        let equal_name = arena.push_string("field");
        assert_ne!(name, equal_name);
        let label = ctx.create_ast_ident(&arena, name);
        let accessor = ctx.create_ast_ident(&arena, name);
        let unrelated = ctx.create_ast_ident(&arena, equal_name);
        assert_ne!(label.stamp(), accessor.stamp());
        assert_eq!(
            ctx.ident_name_allocation(&label),
            ctx.ident_name_allocation(&accessor)
        );
        assert_ne!(
            ctx.ident_name_allocation(&label),
            ctx.ident_name_allocation(&unrelated)
        );
        let renamed = ctx.rename_ident(&accessor);
        assert_eq!(
            ctx.ident_name_allocation(&label),
            ctx.ident_name_allocation(&renamed)
        );
        let mut other = crate::parse_arena::ParseArena::new();
        let other_name = other.push_string("field");
        let other_id = ctx.create_ast_ident(&other, other_name);
        assert_ne!(
            ctx.ident_name_allocation(&label),
            ctx.ident_name_allocation(&other_id)
        );
        let moved = Box::new(arena);
        let copied = ctx.create_ast_ident(&moved, name);
        assert_eq!(
            ctx.ident_name_allocation(&label),
            ctx.ident_name_allocation(&copied)
        );
        assert_eq!(std::mem::size_of::<Ident>(), 16);
    }

    #[test]
    fn dotted_allocations_keep_prefix_sharing_without_content_keys() {
        let mut table = PathProvenance::default();
        let root = Arc::new(Path::Pident(Ident::create_persistent("Root")));
        let equal_root = Arc::new((*root).clone());
        let name = Ident::create_persistent("t");
        let a = table.dotted(
            root.clone(),
            name.name_atom(),
            NameAllocation::of_ident(&name),
            -1,
        );
        let copy = a.clone();
        let b = table.dotted(
            root.clone(),
            name.name_atom(),
            NameAllocation::of_ident(&name),
            -1,
        );
        let c = table.dotted(
            equal_root.clone(),
            name.name_atom(),
            NameAllocation::of_ident(&name),
            -1,
        );
        assert_eq!(a, b);
        assert_eq!(b, c);
        assert_eq!(
            table.get(&a).unwrap().key(),
            table.get(&copy).unwrap().key()
        );
        assert_ne!(table.get(&a).unwrap().key(), table.get(&b).unwrap().key());
        assert!(Arc::ptr_eq(
            &table.get(&a).unwrap().prefix,
            &table.get(&b).unwrap().prefix
        ));
        assert!(!Arc::ptr_eq(
            &table.get(&a).unwrap().prefix,
            &table.get(&c).unwrap().prefix
        ));
        let carrier = Arc::downgrade(&table.get(&a).unwrap().carrier);
        drop(a);
        drop(copy);
        assert!(carrier.upgrade().is_some(), "table prevents address reuse");
        drop(table);
        assert!(
            carrier.upgrade().is_none(),
            "scope releases retained allocations"
        );
        assert_eq!(std::mem::size_of::<Path>(), 24);
        assert_eq!(std::mem::size_of::<Ident>(), 16);
    }

    #[test]
    fn dropped_dots_are_released_while_reachable_ones_keep_their_evidence() {
        let mut table = PathProvenance::default();
        let root = Arc::new(Path::Pident(Ident::create_persistent("Root")));
        let name = Ident::create_persistent("t");
        let make = |table: &mut PathProvenance| {
            table.dotted(
                root.clone(),
                name.name_atom(),
                NameAllocation::of_ident(&name),
                -1,
            )
        };
        let kept = make(&mut table);
        let kept_key = table.get(&kept).unwrap().key();
        let dropped = make(&mut table);
        let dropped_carrier = Arc::downgrade(&table.get(&dropped).unwrap().carrier);
        drop(dropped);
        // Fill past the sweep threshold with dots nobody holds.
        for _ in 0..FIRST_SWEEP {
            drop(make(&mut table));
        }
        assert!(
            dropped_carrier.upgrade().is_none(),
            "an unreachable dot's carrier is freed"
        );
        let entry = table.get(&kept).expect("a reachable dot keeps its entry");
        assert_eq!(entry.key(), kept_key);
        assert!(Arc::ptr_eq(&entry.prefix, &root));
        assert!(table.dotted.len() < FIRST_SWEEP);
        // A dot made after the sweep is new evidence, never an old entry.
        let fresh = make(&mut table);
        assert_ne!(table.get(&fresh).unwrap().key(), kept_key);
    }
}
