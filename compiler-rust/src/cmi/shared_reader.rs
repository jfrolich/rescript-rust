//! Reading one frozen graph of the shared pool without a `TypeContext`.
//!
//! Two readers, both for stage P3b of the checker redesign
//! (`docs/CHECKER_REDESIGN.md`, H.1.5), where the shared graph is built
//! first and the portable form is derived from it:
//!
//! - [`FrozenGraph`] implements [`TypeGraph`], so a signature's fingerprint
//!   and item digests are computed from the shared pages by the walk that
//!   computes them from the portable graph (`graph_hash`).
//! - [`portable_signature`] is the inverse of
//!   `portable_types::internalize_signature_into_shared`: it writes the
//!   portable signature a frozen graph was built from. The pages do not
//!   hold everything that signature holds; [`Carried`] is the rest, and
//!   says so field by field.
//!
//! Serialization metadata lives with the frozen graph, including outside check mode.
//! Every function here is linear in the graph it reads.

use std::borrow::Cow;

use super::graph_hash::{ArgKind, Node, Row, RowFieldView, TypeGraph};
use super::portable_types::{
    PortableLongident, PortableRowDesc, PortableRowField, PortableSignature, PortableTypeDesc,
    PortableTypeEntry, PortableTypeGraph, SignatureRefMap, remap_signature_refs,
};
use crate::fast_hash::AHashMap;
use crate::intern::StrIdx;
use crate::parser::longident::Longident;
use crate::types::asttypes::{ArgLabel, Located, MutableFlag};
use crate::types::decl::Signature;
use crate::types::decl_loc::{DeclLoc, DeclLocKind};
use crate::types::shared_store::{SharedGraph, SharedTypePool};
use crate::types::type_expr::{
    GENERIC_LEVEL, MutabilityRef, RowDesc, RowField, TypeArg, TypeDesc, TypeExprRef,
};
use crate::types::variant_runtime::{ShapeAllocation, ShapeImport};
use crate::types::{VariantLayout, VariantLayoutRef};

/// One published graph of the shared pool, read in place.
pub(crate) struct FrozenGraph<'a> {
    graph: &'a SharedGraph,
    pool: &'a SharedTypePool,
}

impl<'a> FrozenGraph<'a> {
    /// The graph `pool` published at `base`.
    pub(crate) fn new(pool: &'a SharedTypePool, graph: &'a SharedGraph) -> Self {
        FrozenGraph { graph, pool }
    }

    fn portable_longident(&self, lid: &Longident) -> PortableLongident {
        let name = |idx: StrIdx| {
            self.pool
                .longident_name(idx)
                .expect("a shared package constraint names its components in the pool")
        };
        match lid {
            Longident::Lident(idx) => PortableLongident::Lident(name(*idx)),
            Longident::Ldot(prefix, idx) => {
                PortableLongident::Ldot(Box::new(self.portable_longident(prefix)), name(*idx))
            }
            Longident::Lapply(functor, arg) => PortableLongident::Lapply(
                Box::new(self.portable_longident(functor)),
                Box::new(self.portable_longident(arg)),
            ),
        }
    }
}

impl TypeGraph for FrozenGraph<'_> {
    type Ref = TypeExprRef;
    type Arg = TypeArg;
    type Row = RowDesc;
    type RowField = RowField;
    type Mutability = MutabilityRef;
    type Lid = Longident;

    fn slots(&self) -> usize {
        self.graph.nodes().len()
    }

    fn slot(&self, r: TypeExprRef) -> Option<usize> {
        self.graph.node_offset(r)
    }

    fn root(&self, r: TypeExprRef) -> TypeExprRef {
        r
    }

    fn node(&self, slot: usize) -> Node<'_, Self> {
        let graph = self.graph;
        match &graph.nodes()[slot].desc {
            TypeDesc::Tvar(name) => Node::Tvar(*name),
            TypeDesc::Tarrow { args, ret } => Node::Tarrow {
                args: graph.args(*args),
                ret: *ret,
            },
            TypeDesc::Ttuple(elems) => Node::Ttuple(graph.list(*elems)),
            TypeDesc::Tconstr { path, args, .. } => Node::Tconstr {
                path: *path,
                args: graph.list(*args),
            },
            TypeDesc::Tobject { fields } => Node::Tobject { fields: *fields },
            TypeDesc::Tfield {
                name,
                mutability,
                typ,
                rest,
            } => Node::Tfield {
                name: *name,
                mutability: *mutability,
                typ: *typ,
                rest: *rest,
            },
            TypeDesc::Tnil => Node::Tnil,
            TypeDesc::Tlink(target) => Node::Tlink(*target),
            TypeDesc::Tsubst(target) => Node::Tsubst(*target),
            TypeDesc::Tvariant(row) => Node::Tvariant(graph.row(*row)),
            TypeDesc::Tunivar(name) => Node::Tunivar(*name),
            TypeDesc::Tpoly { body, vars } => Node::Tpoly {
                body: *body,
                vars: graph.list(*vars),
            },
            TypeDesc::Tpackage { path, lids, args } => Node::Tpackage {
                path: *path,
                lids: graph.lids(*lids),
                args: graph.list(*args),
            },
        }
    }

    fn arg<'a>(&'a self, arg: &'a TypeArg) -> (ArgKind, Option<&'a str>, TypeExprRef) {
        let label = arg.label();
        let kind = if label.is_nolabel() {
            ArgKind::Nolabel
        } else if label.is_optional() {
            ArgKind::Optional
        } else {
            ArgKind::Labelled
        };
        (kind, label.label_name(), arg.typ)
    }

    fn row<'a>(&'a self, row: &'a RowDesc) -> Row<'a, Self> {
        Row {
            fields: &row.row_fields,
            more: row.row_more,
            closed: row.row_closed,
            fixed: row.row_fixed,
            name: row
                .row_name
                .as_ref()
                .map(|(path, args)| (*path, args.as_slice())),
        }
    }

    fn row_field<'a>(&'a self, field: &'a RowField) -> RowFieldView<'a, Self> {
        match field {
            RowField::Rpresent(typ) => RowFieldView::Rpresent(*typ),
            RowField::Reither {
                constant,
                types,
                matched,
                ..
            } => RowFieldView::Reither {
                constant: *constant,
                types,
                matched: *matched,
            },
            RowField::Rabsent => RowFieldView::Rabsent,
        }
    }

    fn mutability(&self, cell: MutabilityRef) -> Option<MutableFlag> {
        // A published graph holds persistent cells, whose value is in the
        // reference (`MutabilityRef::new_persistent`).
        cell.is_persistent().then(|| cell.persistent_value())
    }

    fn package_lids<'a>(&'a self, lids: &'a [Longident]) -> Cow<'a, [PortableLongident]> {
        Cow::Owned(
            lids.iter()
                .map(|lid| self.portable_longident(lid))
                .collect(),
        )
    }

    fn hash_package_lids(&self, lids: &[Longident], hasher: &mut impl std::hash::Hasher) {
        use std::hash::Hash;
        // Match PortableLongident's derived Hash, borrowing the interned names
        // under one read lock instead of allocating a portable tree per node.
        fn lid(l: &Longident, names: &AHashMap<u32, String>, h: &mut impl std::hash::Hasher) {
            match l {
                Longident::Lident(name) => {
                    0isize.hash(h);
                    names.get(&name.raw()).expect("shared constraint name").hash(h);
                }
                Longident::Ldot(prefix, name) => {
                    1isize.hash(h);
                    lid(prefix, names, h);
                    names.get(&name.raw()).expect("shared constraint name").hash(h);
                }
                Longident::Lapply(functor, arg) => {
                    2isize.hash(h);
                    lid(functor, names, h);
                    lid(arg, names, h);
                }
            }
        }
        self.pool.with_longident_names(|names| {
            lids.len().hash(hasher);
            for l in lids {
                lid(l, names, hasher);
            }
        });
    }

    fn layout(&self, layout: VariantLayoutRef) -> Option<&VariantLayout> {
        if !layout.is_shared() {
            return None;
        }
        let offset = layout.shared_index().checked_sub(self.graph.base())?;
        self.graph.layouts().get(offset as usize)
    }
}

/// What a frozen graph does not hold of the portable signature it was built
/// from. Stored once beside the node arrays in the frozen graph: readers
/// need none of it for type checking, but serialization needs all of it.
/// No field enlarges an individual node.
#[derive(Debug, Default)]
pub(crate) struct Carried {
    /// `PortableSignature::cmi_longident_names`: the file names of the
    /// signature's and of the raw signature's locations, with their
    /// portable keys. The pages name a file by a pool index allocated at
    /// import, and hold neither the keys, nor their order, nor the names
    /// that only the raw signature uses.
    pub(crate) file_names: Vec<(u32, String)>,
    /// The producer's scope of each allocation scope of the import, for the
    /// location table's identities and the shapes' attribute strings. The
    /// import replaces a scope by a hash of the unit and the scope
    /// (`variant_runtime::identity_in_namespace`).
    pub(crate) scopes: AHashMap<u64, u64>,
    /// The producer's allocation of each shape allocation of the import,
    /// replaced the same way.
    pub(crate) allocations: AHashMap<ShapeAllocation, ShapeAllocation>,
    /// The level of every `Tlink` entry that is not at the generic level,
    /// by entry index. The import stores every link at the generic level.
    pub(crate) link_levels: Vec<(u32, i32)>,
}

impl Carried {
    /// Record what importing `graph` rewrote: `scopes` is the map the
    /// location table's import returned, `shapes` the shape import after
    /// the layouts and the signature went through it.
    pub(crate) fn record_import(
        &mut self,
        graph: &PortableTypeGraph,
        scopes: &AHashMap<u64, u64>,
        shapes: ShapeImport<'_>,
    ) {
        let (other_scopes, allocations) = shapes.into_maps();
        for (producer, imported) in scopes.iter().chain(other_scopes.iter()) {
            let previous = self.scopes.insert(*imported, *producer);
            assert!(
                previous.is_none_or(|previous| previous == *producer),
                "two allocation scopes were imported as one"
            );
        }
        for (producer, imported) in allocations {
            let previous = self.allocations.insert(imported, producer);
            assert!(
                previous.is_none_or(|previous| previous == producer),
                "two shape allocations were imported as one"
            );
        }
        self.link_levels = graph
            .entries
            .iter()
            .enumerate()
            .filter(|(_, entry)| {
                matches!(entry.desc, PortableTypeDesc::Tlink(_)) && entry.level != GENERIC_LEVEL
            })
            .map(|(index, entry)| (index as u32, entry.level))
            .collect();
    }

    /// Which parts the inverse needs for this unit, by name: an empty part
    /// is not needed.
    pub(crate) fn needed(&self) -> Vec<&'static str> {
        let mut needed = Vec::new();
        if !self.file_names.is_empty() {
            needed.push("file names");
        }
        if !self.scopes.is_empty() {
            needed.push("allocation scopes");
        }
        if !self.allocations.is_empty() {
            needed.push("shape allocations");
        }
        if !self.link_levels.is_empty() {
            needed.push("link levels");
        }
        needed
    }
}

/// Renames the references of a shared signature to portable indices.
struct PortableRefs<'a> {
    graph: &'a SharedGraph,
}

impl SignatureRefMap for PortableRefs<'_> {
    fn ty(&self, r: TypeExprRef) -> TypeExprRef {
        let offset = self
            .graph
            .node_offset(r)
            .expect("a shared signature refers to nodes of its own graph");
        TypeExprRef::from_usize(offset)
    }

    fn layout(&self, r: VariantLayoutRef) -> VariantLayoutRef {
        VariantLayoutRef(r.shared_index() - self.graph.base())
    }
}

/// The portable signature that `sig`, a signature whose types are nodes of
/// `frozen`, was internalized from: the inverse of
/// `portable_types::internalize_signature_into_shared`. All serialization
/// metadata is read from the frozen graph. Linear in the signature and graph.
pub(crate) fn portable_signature(
    frozen: &FrozenGraph<'_>,
    sig: &Signature,
) -> PortableSignature {
    let graph = frozen.graph;
    let carried = &graph.carried;
    let base = graph.base();

    // File names: pool index -> name -> portable key. A file the import did
    // not rename (the empty name, a name without a key) is kept.
    let keys: AHashMap<&str, u32> = carried
        .file_names
        .iter()
        .map(|(key, name)| (name.as_str(), *key))
        .collect();
    let file = |file: StrIdx| -> StrIdx {
        frozen
            .pool
            .longident_name(file)
            .and_then(|name| keys.get(name.as_str()).copied())
            .map_or(file, StrIdx::from_raw)
    };
    let loc = |loc: DeclLoc| -> DeclLoc {
        match loc.kind() {
            DeclLocKind::Source => loc.with_source_file(file(loc.source_file().unwrap())),
            DeclLocKind::Shared => {
                assert_eq!(loc.owner(), base, "a location of another shared graph");
                DeclLoc::table(DeclLocKind::Portable, 0, loc.index())
            }
            kind => panic!("{kind:?} declaration location in a shared signature"),
        }
    };
    let label = |label: ArgLabel| -> ArgLabel {
        match label {
            ArgLabel::Nolabel => ArgLabel::Nolabel,
            ArgLabel::Labelled(l) => ArgLabel::Labelled(Located::new(l.txt, loc(l.loc))),
            ArgLabel::Optional(l) => ArgLabel::Optional(Located::new(l.txt, loc(l.loc))),
        }
    };
    let index = |r: TypeExprRef| -> usize {
        graph
            .node_offset(r)
            .expect("a shared node refers to nodes of its own graph")
    };
    let indices = |refs: &[TypeExprRef]| -> Vec<usize> { refs.iter().map(|r| index(*r)).collect() };

    // Mutability cells: the portable graph numbers the cells in the order
    // its entries first use them (`TypeGraphSerializer::serialize_mutability`
    // runs when an entry's descriptor is written, in entry order).
    let mut mutabilities: Vec<MutableFlag> = Vec::new();
    let mut cells: AHashMap<MutabilityRef, usize> = AHashMap::default();

    let mut link_levels = carried.link_levels.iter().copied().peekable();
    let mut entries = Vec::with_capacity(graph.nodes().len());
    for (i, node) in graph.nodes().iter().enumerate() {
        let desc = match &node.desc {
            TypeDesc::Tvar(name) => PortableTypeDesc::Tvar(*name),
            TypeDesc::Tarrow { args, ret } => PortableTypeDesc::Tarrow {
                args: graph
                    .args(*args)
                    .iter()
                    .map(|arg| (label(arg.label().to_arg_label()), index(arg.typ)))
                    .collect(),
                ret: index(*ret),
            },
            TypeDesc::Ttuple(elems) => PortableTypeDesc::Ttuple(indices(graph.list(*elems))),
            TypeDesc::Tconstr { path, args, .. } => PortableTypeDesc::Tconstr {
                path: *path,
                args: indices(graph.list(*args)),
            },
            TypeDesc::Tobject { fields } => PortableTypeDesc::Tobject {
                fields: index(*fields),
            },
            TypeDesc::Tfield {
                name,
                mutability,
                typ,
                rest,
            } => {
                let cell = *cells.entry(*mutability).or_insert_with(|| {
                    mutabilities.push(mutability.persistent_value());
                    mutabilities.len() - 1
                });
                PortableTypeDesc::Tfield {
                    name: *name,
                    mutability: cell,
                    typ: index(*typ),
                    rest: index(*rest),
                }
            }
            TypeDesc::Tnil => PortableTypeDesc::Tnil,
            TypeDesc::Tlink(target) => PortableTypeDesc::Tlink(index(*target)),
            TypeDesc::Tsubst(target) => PortableTypeDesc::Tsubst(index(*target)),
            TypeDesc::Tvariant(row) => {
                let row = graph.row(*row);
                PortableTypeDesc::Tvariant(PortableRowDesc {
                    row_fields: row
                        .row_fields
                        .iter()
                        .map(|(label, field)| {
                            let field = match field {
                                RowField::Rpresent(typ) => {
                                    PortableRowField::Rpresent(typ.map(index))
                                }
                                RowField::Reither {
                                    constant,
                                    types,
                                    matched,
                                    ..
                                } => PortableRowField::Reither {
                                    constant: *constant,
                                    types: indices(types),
                                    matched: *matched,
                                },
                                RowField::Rabsent => PortableRowField::Rabsent,
                            };
                            (label.clone(), field)
                        })
                        .collect(),
                    row_more: index(row.row_more),
                    row_closed: row.row_closed,
                    row_fixed: row.row_fixed,
                    row_name: row
                        .row_name
                        .as_ref()
                        .map(|(path, args)| (*path, indices(args))),
                })
            }
            TypeDesc::Tunivar(name) => PortableTypeDesc::Tunivar(*name),
            TypeDesc::Tpoly { body, vars } => PortableTypeDesc::Tpoly {
                body: index(*body),
                vars: indices(graph.list(*vars)),
            },
            TypeDesc::Tpackage { path, lids, args } => PortableTypeDesc::Tpackage {
                path: *path,
                lids: graph
                    .lids(*lids)
                    .iter()
                    .map(|lid| frozen.portable_longident(lid))
                    .collect(),
                args: indices(graph.list(*args)),
            },
        };
        let level = match link_levels.next_if(|(index, _)| *index as usize == i) {
            Some((_, level)) => level,
            None => node.level,
        };
        entries.push(PortableTypeEntry { desc, level });
    }

    // Shapes: back to the producer's allocations and scopes.
    let mut shapes = ShapeImport::with_allocations(&carried.scopes, carried.allocations.clone());
    let variant_layouts = graph
        .layouts()
        .iter()
        .cloned()
        .map(|mut layout| {
            shapes.layout(&mut layout);
            layout
        })
        .collect();

    // Locations: the graph's table, with the producer's file keys and
    // scopes.
    let mut locations = graph.locations().clone();
    locations.remap_for_import_with(&file, |scope| {
        *carried
            .scopes
            .get(&scope)
            .expect("an allocation scope of the import has a producer scope")
    });

    let mut ps_sig = sig.clone();
    remap_signature_refs(&mut ps_sig, &PortableRefs { graph });
    crate::types::decl::for_each_signature_location(&mut ps_sig, &mut |l| *l = loc(*l));
    shapes.signature(&mut ps_sig);

    PortableSignature {
        ps_sig,
        cmi_longident_names: carried.file_names.clone(),
        type_graph: PortableTypeGraph {
            entries,
            variant_layouts,
            mutabilities,
        },
        locations,
    }
}
