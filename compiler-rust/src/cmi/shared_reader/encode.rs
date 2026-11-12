//! Borrowed storage view of a detached graph. Variant and field order are the
//! PortableSignature wire format; signature-check compares the actual bytes
//! against the independent portable serializer for every published unit.
use super::*;
use serde::ser::{Serialize, SerializeSeq, SerializeStruct, Serializer};

pub(super) fn view<'a>(reader: &'a FrozenGraph<'_>, sig: &'a Signature) -> impl Serialize + 'a {
    let mut cells = AHashMap::default();
    let mut mutabilities = Vec::new();
    for node in reader.graph.nodes() {
        if let TypeDesc::Tfield { mutability, .. } = node.desc {
            cells.entry(mutability).or_insert_with(|| {
                let index = mutabilities.len();
                mutabilities.push(mutability.persistent_value());
                index
            });
        }
    }
    let metadata = portable_export(reader, sig, false);
    SignatureWire {
        ps_sig: metadata.ps_sig,
        cmi_longident_names: &reader.graph.carried.file_names,
        type_graph: GraphWire {
            reader,
            cells,
            mutabilities,
            layouts: metadata.type_graph.variant_layouts,
            file_keys: reader
                .graph
                .carried
                .file_names
                .iter()
                .map(|(key, name)| (name.as_str(), *key))
                .collect(),
        },
        locations: metadata.locations,
    }
}

#[derive(serde::Serialize)]
struct SignatureWire<'a, 'g> {
    ps_sig: Cow<'a, Signature>,
    cmi_longident_names: &'a [(u32, String)],
    type_graph: GraphWire<'a, 'g>,
    locations: Cow<'a, crate::types::decl_loc::DeclLocTable>,
}

struct GraphWire<'a, 'g> {
    reader: &'a FrozenGraph<'g>,
    cells: AHashMap<MutabilityRef, usize>,
    mutabilities: Vec<MutableFlag>,
    layouts: Vec<VariantLayout>,
    file_keys: AHashMap<&'a str, u32>,
}
impl Serialize for GraphWire<'_, '_> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let mut out = serializer.serialize_struct("PortableTypeGraph", 3)?;
        out.serialize_field("entries", &Entries(self))?;
        out.serialize_field("variant_layouts", &self.layouts)?;
        out.serialize_field("mutabilities", &self.mutabilities)?;
        out.end()
    }
}
struct Entries<'a, 'b, 'g>(&'a GraphWire<'b, 'g>);
impl Serialize for Entries<'_, '_, '_> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let wire = self.0;
        let graph = wire.reader.graph;
        let mut seq = serializer.serialize_seq(Some(graph.nodes().len()))?;
        let mut link_levels = graph.carried.link_levels.iter().copied().peekable();
        for (index, node) in graph.nodes().iter().enumerate() {
            let desc = match node.desc {
                TypeDesc::Tvar(n) => Desc::Tvar(n),
                TypeDesc::Tarrow { args, ret } => Desc::Tarrow {
                    args: Args(wire.reader, graph.args(args), &wire.file_keys),
                    ret: node_index(graph, ret),
                },
                TypeDesc::Ttuple(xs) => Desc::Ttuple(Refs(graph, graph.list(xs))),
                TypeDesc::Tconstr { path, args, .. } => Desc::Tconstr {
                    path,
                    args: Refs(graph, graph.list(args)),
                },
                TypeDesc::Tobject { fields } => Desc::Tobject {
                    fields: node_index(graph, fields),
                },
                TypeDesc::Tfield {
                    name,
                    mutability,
                    typ,
                    rest,
                } => Desc::Tfield {
                    name,
                    mutability: wire.cells[&mutability],
                    typ: node_index(graph, typ),
                    rest: node_index(graph, rest),
                },
                TypeDesc::Tnil => Desc::Tnil,
                TypeDesc::Tlink(r) => Desc::Tlink(node_index(graph, r)),
                TypeDesc::Tsubst(r) => Desc::Tsubst(node_index(graph, r)),
                TypeDesc::Tvariant(row) => {
                    let row = graph.row(row);
                    Desc::Tvariant(RowWire {
                        row_fields: Fields(graph, &row.row_fields),
                        row_more: node_index(graph, row.row_more),
                        row_closed: row.row_closed,
                        row_fixed: row.row_fixed,
                        row_name: row
                            .row_name
                            .as_ref()
                            .map(|(path, refs)| (path, Refs(graph, refs))),
                    })
                }
                TypeDesc::Tunivar(n) => Desc::Tunivar(n),
                TypeDesc::Tpoly { body, vars } => Desc::Tpoly {
                    body: node_index(graph, body),
                    vars: Refs(graph, graph.list(vars)),
                },
                TypeDesc::Tpackage { path, lids, args } => Desc::Tpackage {
                    path,
                    lids: Lids {
                        reader: wire.reader,
                        lids: graph.lids(lids),
                    },
                    args: Refs(graph, graph.list(args)),
                },
            };
            seq.serialize_element(&Entry {
                desc,
                level: link_levels
                    .next_if(|(at, _)| *at as usize == index)
                    .map_or(node.level, |(_, level)| level),
            })?;
        }
        seq.end()
    }
}
#[derive(serde::Serialize)]
struct Entry<'a, 'g> {
    desc: Desc<'a, 'g>,
    level: i32,
}

// Keep variant and field order identical to PortableTypeDesc. The equality
// oracle is independently derived from that type, not from this view.
#[derive(serde::Serialize)]
enum Desc<'a, 'g> {
    Tvar(Option<crate::name::Name>),
    Tarrow {
        args: Args<'a, 'g>,
        ret: usize,
    },
    Ttuple(Refs<'a>),
    Tconstr {
        path: crate::types::Path,
        args: Refs<'a>,
    },
    Tobject {
        fields: usize,
    },
    Tfield {
        name: crate::name::Name,
        mutability: usize,
        typ: usize,
        rest: usize,
    },
    Tnil,
    Tlink(usize),
    Tsubst(usize),
    Tvariant(RowWire<'a>),
    Tunivar(Option<crate::name::Name>),
    Tpoly {
        body: usize,
        vars: Refs<'a>,
    },
    Tpackage {
        path: crate::types::Path,
        lids: Lids<'a, 'g>,
        args: Refs<'a>,
    },
}
fn node_index(graph: &SharedGraph, r: TypeExprRef) -> usize {
    graph
        .node_offset(r)
        .expect("a frozen graph owns its references")
}

struct Refs<'a>(&'a SharedGraph, &'a [TypeExprRef]);
impl Serialize for Refs<'_> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let mut seq = serializer.serialize_seq(Some(self.1.len()))?;
        for r in self.1 {
            seq.serialize_element(&node_index(self.0, *r))?;
        }
        seq.end()
    }
}
struct Args<'a, 'g>(
    &'a FrozenGraph<'g>,
    &'a [TypeArg],
    &'a AHashMap<&'a str, u32>,
);
impl Serialize for Args<'_, '_> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let mut seq = serializer.serialize_seq(Some(self.1.len()))?;
        for arg in self.1 {
            let loc = |l: DeclLoc| {
                if self.0.graph.is_detached() {
                    return l;
                }
                match l.kind() {
                    DeclLocKind::Shared => DeclLoc::table(DeclLocKind::Portable, 0, l.index()),
                    DeclLocKind::Source => {
                        let file = l.source_file().unwrap();
                        let names = self.0.names.read().unwrap();
                        let portable = names
                            .get(&file.raw())
                            .and_then(|name| self.2.get(name.as_str()).copied())
                            .map_or(file, StrIdx::from_raw);
                        l.with_source_file(portable)
                    }
                    kind => panic!("{kind:?} label in installed graph"),
                }
            };
            let label = match arg.label().to_arg_label() {
                ArgLabel::Nolabel => ArgLabel::Nolabel,
                ArgLabel::Labelled(l) => ArgLabel::Labelled(Located::new(l.txt, loc(l.loc))),
                ArgLabel::Optional(l) => ArgLabel::Optional(Located::new(l.txt, loc(l.loc))),
            };
            seq.serialize_element(&(label, node_index(self.0.graph, arg.typ)))?;
        }
        seq.end()
    }
}
#[derive(serde::Serialize)]
struct RowWire<'a> {
    row_fields: Fields<'a>,
    row_more: usize,
    row_closed: bool,
    row_fixed: bool,
    row_name: Option<(&'a crate::types::Path, Refs<'a>)>,
}
struct Fields<'a>(
    &'a SharedGraph,
    &'a [(crate::types::asttypes::Label, RowField)],
);
#[derive(serde::Serialize)]
enum Field<'a> {
    Rpresent(Option<usize>),
    Reither {
        constant: bool,
        types: Refs<'a>,
        matched: bool,
    },
    Rabsent,
}
impl Serialize for Fields<'_> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let mut seq = serializer.serialize_seq(Some(self.1.len()))?;
        for (label, field) in self.1 {
            let field = match field {
                RowField::Rpresent(r) => Field::Rpresent(r.map(|r| node_index(self.0, r))),
                RowField::Reither {
                    constant,
                    types,
                    matched,
                    ..
                } => Field::Reither {
                    constant: *constant,
                    types: Refs(self.0, types),
                    matched: *matched,
                },
                RowField::Rabsent => Field::Rabsent,
            };
            seq.serialize_element(&(label, field))?;
        }
        seq.end()
    }
}
struct Lids<'a, 'g> {
    reader: &'a FrozenGraph<'g>,
    lids: &'a [Longident],
}
impl Serialize for Lids<'_, '_> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let names = self.reader.names.read().unwrap();
        let mut seq = serializer.serialize_seq(Some(self.lids.len()))?;
        for lid in self.lids {
            seq.serialize_element(&Lid { names: &names, lid })?;
        }
        seq.end()
    }
}
struct Lid<'a> {
    names: &'a AHashMap<u32, String>,
    lid: &'a Longident,
}
#[derive(serde::Serialize)]
enum LidWire<'a> {
    Lident(&'a str),
    Ldot(Lid<'a>, &'a str),
    Lapply(Lid<'a>, Lid<'a>),
}
impl Serialize for Lid<'_> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let at = |lid| Lid {
            names: self.names,
            lid,
        };
        let name = |idx: StrIdx| {
            self.names
                .get(&idx.raw())
                .expect("frozen constraint name")
                .as_str()
        };
        match self.lid {
            Longident::Lident(n) => LidWire::Lident(name(*n)),
            Longident::Ldot(p, n) => LidWire::Ldot(at(p), name(*n)),
            Longident::Lapply(f, x) => LidWire::Lapply(at(f), at(x)),
        }
        .serialize(serializer)
    }
}
