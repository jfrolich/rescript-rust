//! Hashing a type graph: what a signature's fingerprint and item digests
//! read of the types they mention.
//!
//! The hash is defined over the *graph*, not over the tree a graph unfolds
//! to. The nodes reachable from the roots of one hashed value (the whole
//! signature for the fingerprint, one top-level item for its digest) are
//! numbered in first-visit order, and every reference to a node is hashed
//! as that number. A reference to a node seen before is therefore a
//! back-reference, and the node's own record is hashed once. Two graphs
//! hash alike exactly when they are the same graph up to renaming of nodes:
//! the same nodes, the same sharing, the same cycles. Node identity is part
//! of what a dependent can observe of an interface
//! (`docs/CHECKER_REDESIGN.md`, I.2.1 and I.3.3 rules 5 and 8), so two
//! different sharings of one unfolded type are two interfaces.
//!
//! The walk is written once, against [`TypeGraph`], and reads the portable
//! graph of a stored interface and the frozen pages of the shared pool
//! through it. Both hash the same stream, which the signature equality
//! check compares per unit (`signature_check.rs`).
//!
//! Cost: one record per node and one number per reference, so a walk is
//! linear in the nodes and edges reachable from its roots. Nothing recurses
//! on the depth of a type and nothing searches a stack: a node waits in the
//! numbering order until its record is written.

use std::borrow::Cow;
use std::hash::{Hash, Hasher};

use super::portable_types::PortableLongident;
use crate::name::Name;
use crate::types::asttypes::{Label, MutableFlag};
use crate::types::path::Path;
use crate::types::type_expr::TypeExprRef;
use crate::types::{VariantLayout, VariantLayoutRef};

/// A type graph that can be hashed: the portable graph of a stored
/// interface, or one graph of the shared pool. Nodes have dense slots
/// `0..slots()`; descriptors refer to nodes by `Ref`.
pub trait TypeGraph {
    /// How a descriptor names another node.
    type Ref: Copy;
    /// One parameter of an arrow.
    type Arg;
    /// The payload of a polymorphic variant.
    type Row;
    /// One field of a row.
    type RowField;
    /// How an object field names its mutability cell.
    type Mutability: Copy;
    /// One constraint name of a package type.
    type Lid;

    /// The number of nodes.
    fn slots(&self) -> usize;
    /// The slot of the node `r` names; `None` when it names no node of this
    /// graph (a damaged stored graph).
    fn slot(&self, r: Self::Ref) -> Option<usize>;
    /// The reference a signature holds, as the graph's descriptors name it.
    fn root(&self, r: TypeExprRef) -> Self::Ref;
    /// The descriptor of the node in `slot`.
    fn node(&self, slot: usize) -> Node<'_, Self>;
    /// The label of an arrow parameter (without its location) and its type.
    fn arg<'a>(&'a self, arg: &'a Self::Arg) -> (ArgKind, Option<&'a str>, Self::Ref);
    /// The parts of a row.
    fn row<'a>(&'a self, row: &'a Self::Row) -> Row<'a, Self>;
    /// One field of a row.
    fn row_field<'a>(&'a self, field: &'a Self::RowField) -> RowFieldView<'a, Self>;
    /// The value of a mutability cell.
    fn mutability(&self, cell: Self::Mutability) -> Option<MutableFlag>;
    /// The constraint names of a package type, with their names resolved.
    fn package_lids<'a>(&'a self, lids: &'a [Self::Lid]) -> Cow<'a, [PortableLongident]>;
    /// Hash constraint names without requiring a temporary owned tree.
    fn hash_package_lids(&self, lids: &[Self::Lid], hasher: &mut impl Hasher) {
        self.package_lids(lids).hash(hasher);
    }
    /// The layout a variant declaration of the signature refers to.
    fn layout(&self, layout: VariantLayoutRef) -> Option<&VariantLayout>;
}

/// The kind of an arrow parameter's label.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ArgKind {
    /// No label.
    Nolabel,
    /// `~label`.
    Labelled,
    /// `~label=?`.
    Optional,
}

/// One node of a [`TypeGraph`], as hashing reads it.
pub enum Node<'a, G: TypeGraph + ?Sized> {
    /// A type variable.
    Tvar(Option<Name>),
    /// A function type.
    Tarrow {
        /// The parameters.
        args: &'a [G::Arg],
        /// The result.
        ret: G::Ref,
    },
    /// A tuple.
    Ttuple(&'a [G::Ref]),
    /// A type constructor applied to arguments.
    Tconstr {
        /// The constructor.
        path: Path,
        /// The arguments.
        args: &'a [G::Ref],
    },
    /// An object type.
    Tobject {
        /// The field list.
        fields: G::Ref,
    },
    /// One field of an object's field list.
    Tfield {
        /// The field's name.
        name: Name,
        /// Its mutability cell.
        mutability: G::Mutability,
        /// Its type.
        typ: G::Ref,
        /// The rest of the list.
        rest: G::Ref,
    },
    /// The end of a closed field list.
    Tnil,
    /// An alias of another node.
    Tlink(G::Ref),
    /// A substitution placeholder for another node.
    Tsubst(G::Ref),
    /// A polymorphic variant.
    Tvariant(&'a G::Row),
    /// A universally quantified variable.
    Tunivar(Option<Name>),
    /// A polymorphic type.
    Tpoly {
        /// The quantified type.
        body: G::Ref,
        /// The variables it quantifies over.
        vars: &'a [G::Ref],
    },
    /// A first-class module type.
    Tpackage {
        /// The module type.
        path: Path,
        /// The constrained names.
        lids: &'a [G::Lid],
        /// What they are bound to.
        args: &'a [G::Ref],
    },
}

/// The parts of a polymorphic variant row.
pub struct Row<'a, G: TypeGraph + ?Sized> {
    /// The tags, in order.
    pub fields: &'a [(Label, G::RowField)],
    /// The row variable.
    pub more: G::Ref,
    /// Whether no other tags are allowed.
    pub closed: bool,
    /// Whether unification may not extend the row.
    pub fixed: bool,
    /// The abbreviation the row was expanded from.
    pub name: Option<(Path, &'a [G::Ref])>,
}

/// One field of a row.
pub enum RowFieldView<'a, G: TypeGraph + ?Sized> {
    /// The tag is present, with its argument.
    Rpresent(Option<G::Ref>),
    /// The tag may be present.
    Reither {
        /// Whether it may have no argument.
        constant: bool,
        /// The argument types it may have.
        types: &'a [G::Ref],
        /// Whether a pattern matched it.
        matched: bool,
    },
    /// The tag is absent.
    Rabsent,
}

/// Not numbered in the current scope.
const UNNUMBERED: u32 = u32::MAX;
/// What a reference to no node hashes as.
const DANGLING: u32 = u32::MAX - 1;

/// Hash a path by its names, without stamps, so that a digest does not move
/// when a recompilation numbers a dependency's identifiers differently.
pub fn hash_path_by_name(hasher: &mut impl Hasher, path: &Path) {
    use crate::types::path::PathView as P;
    match path.view() {
        P::Pident(ident) => {
            0u8.hash(hasher);
            ident.name().hash(hasher);
        }
        P::Pdot(base, field, _pos) => {
            1u8.hash(hasher);
            hash_path_by_name(hasher, base);
            field.hash(hasher);
        }
        P::Papply(f, x) => {
            2u8.hash(hasher);
            hash_path_by_name(hasher, f);
            hash_path_by_name(hasher, x);
        }
    }
}

/// The walk over one [`TypeGraph`] that hashes the types a value mentions.
///
/// A *scope* is one hashed value: [`GraphWalk::begin_scope`] starts one.
/// Within a scope every node gets a number the first time a reference to it
/// is hashed, and its record is hashed once, so the cost of a scope is
/// linear in the nodes and edges reachable from the references hashed in it
/// (see the module documentation).
pub struct GraphWalk<'g, G: TypeGraph + ?Sized> {
    graph: &'g G,
    /// The number of each slot in the current scope, or [`UNNUMBERED`].
    number: Vec<u32>,
    /// The slots numbered in the current scope, in numbering order.
    order: Vec<u32>,
    /// How many slots of `order` have had their record hashed.
    written: usize,
    /// Node records hashed since the walk was created.
    records: u64,
}

impl<G: TypeGraph + ?Sized> Drop for GraphWalk<'_, G> {
    fn drop(&mut self) {
        crate::perf_counters::record_signature_nodes_hashed(self.records);
    }
}

impl<'g, G: TypeGraph + ?Sized> GraphWalk<'g, G> {
    /// A walk over `graph`, in its first scope. Allocates one number per
    /// node of the graph, once.
    pub fn new(graph: &'g G) -> Self {
        GraphWalk {
            graph,
            number: vec![UNNUMBERED; graph.slots()],
            order: Vec::new(),
            written: 0,
            records: 0,
        }
    }

    /// The graph walked.
    pub fn graph(&self) -> &'g G {
        self.graph
    }

    /// Node records hashed so far, over every scope: the step count of the
    /// walk.
    pub fn records(&self) -> u64 {
        self.records
    }

    /// Forget the numbering: the next reference starts a new hashed value.
    /// Costs the number of nodes the scope that ends numbered.
    pub fn begin_scope(&mut self) {
        for slot in self.order.drain(..) {
            self.number[slot as usize] = UNNUMBERED;
        }
        self.written = 0;
    }

    /// Hash the type a signature refers to by `r`.
    pub fn type_ref(&mut self, hasher: &mut impl Hasher, r: TypeExprRef) {
        let r = self.graph.root(r);
        self.reference(hasher, r);
        while self.written < self.order.len() {
            let slot = self.order[self.written] as usize;
            self.written += 1;
            self.records += 1;
            self.record(hasher, slot);
        }
    }

    /// Hash a reference as the number of its node, numbering the node when
    /// this is the first reference to it in the scope. A first reference
    /// hashes the count of nodes numbered so far, which no back-reference
    /// can, so the stream tells the two apart.
    fn reference(&mut self, hasher: &mut impl Hasher, r: G::Ref) {
        let Some(slot) = self.graph.slot(r) else {
            hasher.write_u32(DANGLING);
            return;
        };
        let mut number = self.number[slot];
        if number == UNNUMBERED {
            number = self.order.len() as u32;
            self.number[slot] = number;
            self.order.push(slot as u32);
        }
        hasher.write_u32(number);
    }

    fn references(&mut self, hasher: &mut impl Hasher, refs: &[G::Ref]) {
        hasher.write_usize(refs.len());
        for r in refs {
            self.reference(hasher, *r);
        }
    }

    /// Hash the record of one node: its own data, and its children as
    /// references.
    fn record(&mut self, hasher: &mut impl Hasher, slot: usize) {
        let graph = self.graph;
        match graph.node(slot) {
            Node::Tvar(name) => {
                hasher.write_u8(0);
                name.hash(hasher);
            }
            Node::Tarrow { args, ret } => {
                hasher.write_u8(1);
                hasher.write_usize(args.len());
                for arg in args {
                    // The label's kind and name; not where it was written.
                    let (kind, name, typ) = graph.arg(arg);
                    kind.hash(hasher);
                    if let Some(name) = name {
                        name.hash(hasher);
                    }
                    self.reference(hasher, typ);
                }
                self.reference(hasher, ret);
            }
            Node::Ttuple(elems) => {
                hasher.write_u8(2);
                self.references(hasher, elems);
            }
            Node::Tconstr { path, args } => {
                hasher.write_u8(3);
                hash_path_by_name(hasher, &path);
                self.references(hasher, args);
            }
            Node::Tobject { fields } => {
                hasher.write_u8(4);
                self.reference(hasher, fields);
            }
            Node::Tfield {
                name,
                mutability,
                typ,
                rest,
            } => {
                hasher.write_u8(5);
                name.hash(hasher);
                graph.mutability(mutability).hash(hasher);
                self.reference(hasher, typ);
                self.reference(hasher, rest);
            }
            Node::Tnil => hasher.write_u8(6),
            Node::Tlink(target) => {
                hasher.write_u8(7);
                self.reference(hasher, target);
            }
            Node::Tsubst(target) => {
                hasher.write_u8(8);
                self.reference(hasher, target);
            }
            Node::Tvariant(row) => {
                hasher.write_u8(9);
                let row = graph.row(row);
                hasher.write_usize(row.fields.len());
                for (label, field) in row.fields {
                    label.hash(hasher);
                    match graph.row_field(field) {
                        RowFieldView::Rpresent(None) => hasher.write_u8(0),
                        RowFieldView::Rpresent(Some(typ)) => {
                            hasher.write_u8(1);
                            self.reference(hasher, typ);
                        }
                        RowFieldView::Reither {
                            constant,
                            types,
                            matched,
                        } => {
                            hasher.write_u8(2);
                            constant.hash(hasher);
                            self.references(hasher, types);
                            matched.hash(hasher);
                        }
                        RowFieldView::Rabsent => hasher.write_u8(3),
                    }
                }
                self.reference(hasher, row.more);
                row.closed.hash(hasher);
                row.fixed.hash(hasher);
                match row.name {
                    Some((path, args)) => {
                        true.hash(hasher);
                        hash_path_by_name(hasher, &path);
                        self.references(hasher, args);
                    }
                    None => false.hash(hasher),
                }
            }
            Node::Tunivar(name) => {
                hasher.write_u8(10);
                name.hash(hasher);
            }
            Node::Tpoly { body, vars } => {
                hasher.write_u8(11);
                self.reference(hasher, body);
                self.references(hasher, vars);
            }
            Node::Tpackage { path, lids, args } => {
                hasher.write_u8(12);
                hash_path_by_name(hasher, &path);
                graph.hash_package_lids(lids, hasher);
                self.references(hasher, args);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::super::portable_types::{
        HashGraph, PortableRowDesc, PortableTypeDesc, PortableTypeEntry,
    };
    use super::*;

    fn entry(desc: PortableTypeDesc) -> PortableTypeEntry {
        PortableTypeEntry { desc, level: 0 }
    }

    fn graph(entries: &[PortableTypeEntry]) -> HashGraph<'_> {
        HashGraph {
            entries,
            layouts: &[],
            mutabilities: &[],
        }
    }

    /// The hash of the types at `roots`, as one scope, and the number of
    /// node records the walk wrote.
    fn hash(entries: &[PortableTypeEntry], roots: &[usize]) -> (u64, u64) {
        let graph = graph(entries);
        let mut walk = GraphWalk::new(&graph);
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        for root in roots {
            walk.type_ref(&mut hasher, TypeExprRef::from_usize(*root));
        }
        (hasher.finish(), walk.records())
    }

    fn int() -> PortableTypeDesc {
        PortableTypeDesc::Tconstr {
            path: Path::pident(crate::ident::Ident::create_persistent("int")),
            args: Vec::new(),
        }
    }

    #[test]
    fn a_chain_of_ten_thousand_nodes_is_walked_in_ten_thousand_steps() {
        const N: usize = 10_000;
        let mut entries: Vec<_> = (0..N - 1)
            .map(|i| entry(PortableTypeDesc::Ttuple(vec![i + 1])))
            .collect();
        entries.push(entry(int()));
        let (_, records) = hash(&entries, &[0]);
        assert_eq!(records, N as u64);
    }

    #[test]
    fn a_node_shared_by_ten_thousand_parents_is_visited_once() {
        const N: usize = 10_000;
        // Entry 0 is the shared node, itself a subgraph of three nodes;
        // entries 3..3+N are its parents, entry 3+N is their tuple.
        let mut entries = vec![
            entry(PortableTypeDesc::Ttuple(vec![1, 2])),
            entry(int()),
            entry(int()),
        ];
        entries.extend((0..N).map(|_| entry(PortableTypeDesc::Ttuple(vec![0]))));
        entries.push(entry(PortableTypeDesc::Ttuple((3..3 + N).collect())));
        let (_, records) = hash(&entries, &[3 + N]);
        assert_eq!(records, (N + 4) as u64);
    }

    #[test]
    fn a_cycle_is_walked_once() {
        const N: usize = 10_000;
        let entries: Vec<_> = (0..N)
            .map(|i| entry(PortableTypeDesc::Ttuple(vec![(i + 1) % N])))
            .collect();
        let (_, records) = hash(&entries, &[0]);
        assert_eq!(records, N as u64);
        // Every root of a scope shares the numbering: a second root in the
        // cycle writes nothing more.
        let (_, records) = hash(&entries, &[0, N / 2]);
        assert_eq!(records, N as u64);
    }

    #[test]
    fn every_scope_walks_what_it_reaches() {
        let entries = vec![entry(PortableTypeDesc::Ttuple(vec![1, 1])), entry(int())];
        let graph = graph(&entries);
        let mut walk = GraphWalk::new(&graph);
        let mut hashes = Vec::new();
        for _ in 0..3 {
            walk.begin_scope();
            let mut hasher = std::collections::hash_map::DefaultHasher::new();
            walk.type_ref(&mut hasher, TypeExprRef::from_usize(0));
            hashes.push(hasher.finish());
        }
        assert_eq!(walk.records(), 6);
        assert!(hashes.iter().all(|hash| *hash == hashes[0]));
    }

    #[test]
    fn sharing_is_hashed() {
        // `(int, int)` with one `int` node at both positions, and with two.
        let shared = vec![entry(PortableTypeDesc::Ttuple(vec![1, 1])), entry(int())];
        let distinct = vec![
            entry(PortableTypeDesc::Ttuple(vec![1, 2])),
            entry(int()),
            entry(int()),
        ];
        assert_ne!(hash(&shared, &[0]).0, hash(&distinct, &[0]).0);
        // Two roots that are one node, and two equal nodes.
        assert_ne!(hash(&distinct, &[1, 1]).0, hash(&distinct, &[1, 2]).0);
    }

    #[test]
    fn the_hash_does_not_depend_on_where_nodes_are_stored() {
        // `(int, 'a) => 'a`, stored in two orders.
        let var = || PortableTypeDesc::Tvar(Some(Name::new("a")));
        let arrow = |arg: usize, ret: usize| PortableTypeDesc::Tarrow {
            args: vec![(crate::types::asttypes::ArgLabel::Nolabel, arg)],
            ret,
        };
        let one = vec![
            entry(arrow(1, 3)),
            entry(PortableTypeDesc::Ttuple(vec![2, 3])),
            entry(int()),
            entry(var()),
        ];
        let other = vec![
            entry(var()),
            entry(int()),
            entry(PortableTypeDesc::Ttuple(vec![1, 0])),
            entry(arrow(2, 0)),
        ];
        assert_eq!(hash(&one, &[0]).0, hash(&other, &[3]).0);
        // The result is another variable of the same name.
        let two_vars = vec![
            entry(arrow(1, 4)),
            entry(PortableTypeDesc::Ttuple(vec![2, 3])),
            entry(int()),
            entry(var()),
            entry(var()),
        ];
        assert_ne!(hash(&one, &[0]).0, hash(&two_vars, &[0]).0);
    }

    #[test]
    fn a_reference_to_no_node_is_hashed_without_a_walk() {
        let entries = vec![entry(PortableTypeDesc::Ttuple(vec![7]))];
        let (_, records) = hash(&entries, &[0]);
        assert_eq!(records, 1);
    }

    #[test]
    fn rows_are_hashed_through_their_references() {
        let row = |more: usize| {
            PortableTypeDesc::Tvariant(PortableRowDesc {
                row_fields: vec![(
                    "A".into(),
                    super::super::portable_types::PortableRowField::Rpresent(Some(1)),
                )],
                row_more: more,
                row_closed: true,
                row_fixed: false,
                row_name: None,
            })
        };
        let a = vec![entry(row(2)), entry(int()), entry(PortableTypeDesc::Tnil)];
        let b = vec![entry(row(1)), entry(int()), entry(PortableTypeDesc::Tnil)];
        assert_ne!(hash(&a, &[0]).0, hash(&b, &[0]).0);
        assert_eq!(hash(&a, &[0]).1, 3);
    }
}
