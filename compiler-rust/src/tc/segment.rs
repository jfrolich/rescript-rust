//! Immutable publication pools. Names and paths are indices, never owned per item.
use super::graph::{Node, Param, Ty};
use super::template::Template;

/// A namespace tag occupies one byte in an export row.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum ExportKind {
    Value,
    Type,
    Constructor,
    Label,
    Module,
    ModuleType,
}

/// One name in an export table. Payload indexes the pool selected by kind.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(C)]
pub struct ExportItem {
    pub name: u32,
    pub payload: u32,
    pub kind: ExportKind,
}

/// A contiguous export-table range; the root table is child table zero.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
#[repr(C)]
pub struct ChildTable {
    pub start: u32,
    pub len: u32,
}

/// Cold type-declaration metadata; all references index segment pools.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(C)]
pub struct TypeDecl {
    pub kind: u8,
    pub flags: u8,
    pub arity: u16,
    pub params: u32,
    pub manifest: u32,
    pub members: u32,
    pub member_len: u32,
    pub path: u32,
    pub loc: u32,
    pub variance: u32,
}

/// Constructor or record-label metadata, kept out of the type-node array.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(C)]
pub struct MemberDecl {
    pub name: u32,
    pub args: u32,
    pub tag_or_pos: u32,
    pub flags: u32,
}

/// Published storage contains no graph context, cell, lock or borrowed data.
/// Each table's items are sorted by numeric interned name. Equal names in
/// different namespaces are adjacent; lookup returns any matching namespace.
#[derive(Default)]
pub struct Segment {
    pub nodes: Box<[Node]>,
    pub lists: Box<[Ty]>,
    pub params: Box<[Param]>,
    pub templates: Box<[Template]>,
    pub type_declarations: Box<[TypeDecl]>,
    pub members: Box<[MemberDecl]>,
    pub items: Box<[ExportItem]>,
    pub children: Box<[ChildTable]>,
    pub digest: [u8; 32],
}

impl Segment {
    /// O(log n) probes, O(1) stack and no allocation, for n root exports.
    /// Returns None for an empty segment. Names use the publisher's interner.
    pub fn lookup(&self, name: u32) -> Option<&ExportItem> {
        self.children.first().and_then(|&table| self.lookup_in(table, name))
    }

    /// O(log n) probes, at most floor(log2(n)) + 1 for a nonempty table.
    /// The caller supplies a valid table range; invalid ranges panic.
    pub fn lookup_in(&self, table: ChildTable, name: u32) -> Option<&ExportItem> {
        let start = table.start as usize;
        let items = &self.items[start..start + table.len as usize];
        let mut lo = 0;
        let mut hi = items.len();
        while lo < hi {
            #[cfg(test)]
            super::steps::tick();
            let mid = lo + (hi - lo) / 2;
            match items[mid].name.cmp(&name) {
                std::cmp::Ordering::Less => lo = mid + 1,
                std::cmp::Ordering::Greater => hi = mid,
                std::cmp::Ordering::Equal => return Some(&items[mid]),
            }
        }
        None
    }
}

/// O(1), compile-time trait assertion; no runtime work.
const fn assert_send_sync<T: Send + Sync>() {}
const _: () = assert_send_sync::<Segment>();

#[cfg(test)]
mod tests {
    use super::*;
    use crate::tc::steps;

    #[test]
    fn sizes() {
        assert_eq!(std::mem::size_of::<ExportKind>(), 1);
        assert_eq!(std::mem::size_of::<ExportItem>(), 12);
        assert_eq!(std::mem::size_of::<ChildTable>(), 8);
        assert_eq!(std::mem::size_of::<TypeDecl>(), 32);
        assert_eq!(std::mem::size_of::<MemberDecl>(), 16);
        assert_eq!(std::mem::size_of::<Segment>(), 160);
    }

    #[test]
    fn ten_thousand_names_need_at_most_fifteen_probes() {
        let segment = Segment {
            items: (0..10000).map(|i| ExportItem {
                name: i * 2,
                payload: i,
                kind: ExportKind::Value,
            }).collect(),
            children: Box::new([ChildTable { start: 0, len: 10000 }]),
            ..Segment::default()
        };
        for name in 0..=20000 {
            let probes = steps::scope(|| {
                let found = segment.lookup(name);
                assert_eq!(found.map(|item| item.payload),
                    (name < 20000 && name % 2 == 0).then_some(name / 2));
            });
            assert!(probes <= 15, "{name}: {probes} probes");
        }
        assert!(segment.lookup(u32::MAX).is_none());
    }

    #[test]
    fn child_tables_are_independent_and_empty_tables_are_valid() {
        let segment = Segment {
            items: Box::new([
                ExportItem { name: 7, payload: 0, kind: ExportKind::Module },
                ExportItem { name: 7, payload: 1, kind: ExportKind::Value },
            ]),
            children: Box::new([
                ChildTable { start: 0, len: 1 },
                ChildTable { start: 1, len: 1 },
                ChildTable { start: 2, len: 0 },
            ]),
            ..Segment::default()
        };
        assert_eq!(segment.lookup(7).unwrap().kind, ExportKind::Module);
        assert_eq!(segment.lookup_in(segment.children[1], 7).unwrap().payload, 1);
        assert!(segment.lookup_in(segment.children[2], 7).is_none());
        assert!(Segment::default().lookup(7).is_none());
    }
}
