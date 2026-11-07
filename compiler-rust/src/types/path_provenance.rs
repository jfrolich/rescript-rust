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
    pub(crate) name: Ident,
    position: i32,
}

impl DottedAllocation {
    pub(crate) fn key(&self) -> usize {
        Arc::as_ptr(&self.carrier) as usize
    }
}

/// Owned by a compilation, worker store, or shared-pool publication scope.
/// No address survives its retained allocation and no contents are used as keys.
#[derive(Default)]
pub(crate) struct PathProvenance {
    dotted: AHashMap<usize, DottedAllocation>,
}

impl PathProvenance {
    /// A single allocation of `Pdot(prefix, Ident.name name, pos)`.
    /// Clone the resulting Path to retain that allocation. To construct a new
    /// Pdot, call this again rather than reusing its carrier for another suffix.
    pub(crate) fn dotted(&mut self, prefix: Arc<Path>, name: Ident, pos: i32) -> Path {
        let carrier = Arc::new((*prefix).clone());
        let entry = DottedAllocation {
            carrier: carrier.clone(),
            prefix,
            name,
            position: pos,
        };
        assert!(self.dotted.insert(entry.key(), entry).is_none());
        Path::Pdot(carrier, name.name_atom(), pos)
    }

    pub(crate) fn get(&self, path: &Path) -> Option<&DottedAllocation> {
        let Path::Pdot(carrier, name, position) = path else {
            return None;
        };
        let entry = self.dotted.get(&(Arc::as_ptr(carrier) as usize))?;
        assert_eq!(
            *name,
            entry.name.name_atom(),
            "path carrier reused for another suffix"
        );
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
    fn dotted_allocations_keep_prefix_sharing_without_content_keys() {
        let mut table = PathProvenance::default();
        let root = Arc::new(Path::Pident(Ident::create_persistent("Root")));
        let equal_root = Arc::new((*root).clone());
        let name = Ident::create_persistent("t");
        let a = table.dotted(root.clone(), name, -1);
        let copy = a.clone();
        let b = table.dotted(root.clone(), name, -1);
        let c = table.dotted(equal_root.clone(), name, -1);
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
}
