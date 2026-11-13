//! Tests of [`super::to_old`]. Bridge tests may name old types.

use super::*;
use crate::tc::graph::Graph;
use crate::tc::publish::publish;
use crate::tc::steps;
use crate::types::shared_store::SharedTypePool;

const N: u32 = 10_000;

macro_rules! fixture {
    ($($field:ident: $ty:ty),* $(,)?) => {
        /// Segment metadata under construction, before the type graph.
        #[derive(Default)]
        struct Fixture {
            $($field: Vec<$ty>,)*
            type_declarations: Vec<TypeDecl>,
            members: Vec<MemberDecl>,
        }

        impl Fixture {
            /// O(rows): the metadata as a segment with no type pools.
            fn into_segment(self, unit: UnitRow) -> Segment {
                Segment {
                    type_declarations: self.type_declarations.into(),
                    members: self.members.into(),
                    signature: SignaturePools {
                        unit: Some(unit),
                        $($field: self.$field.into(),)*
                        roots: Box::default(),
                    },
                    ..Segment::default()
                }
            }
        }
    };
}

fixture!(
    bytes: u8, strings: Range, ranges: Range, indices: u32, identifiers: IdentRow,
    paths: PathRow, longidents: LongidentRow, ordered_items: SignatureItemRow,
    signatures: Range, values: ValueRow, modules: ModuleRow, module_types: ModuleTypeRow,
    type_details: TypeDetailsRow, inlined_records: InlinedRecordRow,
    record_representations: RecordRepresentationRow, labels: LabelRow,
    constructor_arguments: ConstructorArgumentsRow, constructors: ConstructorRow,
    extensions: ExtensionRow, block_types: BlockTypeRow, shapes: ShapeRow,
    literals: LiteralRow, layouts: LayoutRow, runtime_constructors: RuntimeConstructorRow,
    attributes: AttributeRow, attribute_payloads: AttributePayloadRow,
    semantic_strings: SemanticStringRow, deprecations: DeprecatedRow,
    string_pairs: StringPair, string_int_pairs: StringIntPair,
    marshal_fragments: MarshalFragmentRow, primitives: PrimitiveRow,
    constant_arguments: ConstantArgumentRow, ffi_attributes: FfiAttributeRow,
    ffi_params: FfiParamRow, ffi: FfiRow, external_declarations: ExternalDeclRow,
    external_modules: ExternalModuleRow, inline_constants: InlineConstantRow,
    variants: VariantRow, row_fields: RowFieldRow, packages: PackageRow, variance: u8,
    locations: LocationRow, descriptor_extras: ExtraDescriptor,
);

/// Amortized O(1): append a row and return its index.
fn add<T>(pool: &mut Vec<T>, row: T) -> u32 {
    pool.push(row);
    (pool.len() - 1) as u32
}

impl Fixture {
    /// O(length): a new string row.
    fn string(&mut self, text: &str) -> u32 {
        let start = self.bytes.len() as u32;
        self.bytes.extend_from_slice(text.as_bytes());
        add(
            &mut self.strings,
            Range {
                start,
                len: text.len() as u32,
            },
        )
    }

    /// O(1): the unit `Test`, identifier 0 and path 0, whose signature is
    /// signature row 0.
    fn unit(&mut self) -> UnitRow {
        let name = self.string("Test");
        let ident = add(
            &mut self.identifiers,
            IdentRow {
                name,
                stamp: 0,
                flags: u32::from(IdentFlags::GLOBAL.bits()),
                scope: UNIT_SCOPE,
            },
        );
        let path = add(&mut self.paths, PathRow::Ident(ident));
        add(&mut self.signatures, Range::default());
        UnitRow {
            name,
            deprecated: NONE,
            signature: 0,
            path,
        }
    }

    /// O(1): a location; line 0 is coordinate-free.
    fn loc(&mut self, file: Option<&str>, line: i32) -> u32 {
        let filename = match file {
            Some(file) => self.string(file),
            None => NONE,
        };
        let position = PositionRow {
            filename,
            line,
            beginning_of_line: 0,
            offset: line * 10,
        };
        add(
            &mut self.locations,
            LocationRow {
                start: position,
                end: PositionRow {
                    offset: position.offset + 1 - i32::from(line == 0),
                    ..position
                },
                origin: 0,
                ghost: line == 0,
            },
        )
    }

    /// O(1): an identifier row.
    fn ident(&mut self, name: &str, stamp: i32, scope: u32) -> u32 {
        let name = self.string(name);
        add(
            &mut self.identifiers,
            IdentRow {
                name,
                stamp,
                flags: 0,
                scope,
            },
        )
    }

    /// O(1): an item's binder and its binder-address path.
    fn binder(&mut self, name: &str, stamp: i32) -> (u32, u32) {
        let scope = self.ordered_items.len() as u32;
        let ident = self.ident(name, stamp, scope);
        (ident, add(&mut self.paths, PathRow::Ident(ident)))
    }

    /// O(1): append a value item whose type is root `ty`.
    fn value(&mut self, name: &str, stamp: i32, ty: u32) -> u32 {
        let (ident, path) = self.binder(name, stamp);
        let loc = self.loc(None, 0);
        let declaration = add(
            &mut self.values,
            ValueRow {
                ty,
                primitive: NONE,
                attributes: Range::default(),
                loc,
                path,
            },
        );
        add(
            &mut self.ordered_items,
            SignatureItemRow {
                ident,
                declaration,
                kind: SignatureKind::Value,
                status: ItemStatus::Ordinary,
            },
        )
    }

    /// O(1): close signature row `index` over the items from `start`.
    fn close(&mut self, index: u32, start: u32) {
        self.signatures[index as usize] = Range {
            start,
            len: self.ordered_items.len() as u32 - start,
        };
    }
}

/// O(1).
fn var(graph: &mut Graph, level: u32) -> Ty {
    graph.push(Node {
        head: VAR,
        level,
        a: NONE,
        b: 0,
    })
}

/// O(children).
fn listed(graph: &mut Graph, head: u32, level: u32, a: u32, children: &[Ty]) -> Ty {
    let b = graph.lists.len() as u32;
    graph.lists.extend_from_slice(children);
    graph.push(Node {
        head: head | (children.len() as u32) << 8,
        level,
        a,
        b,
    })
}

/// O(children).
fn tuple(graph: &mut Graph, level: u32, children: &[Ty]) -> Ty {
    listed(graph, TUPLE, level, 0, children)
}

/// O(children): an extended descriptor with payload row `extra`.
fn extended(graph: &mut Graph, level: u32, extra: u32, children: &[Ty]) -> Ty {
    listed(graph, TUPLE | EXTENDED, level, extra, children)
}

/// O(arguments).
fn constr(graph: &mut Graph, level: u32, path: u32, args: &[Ty]) -> Ty {
    let b = graph.lists.len() as u32;
    graph.lists.push(Ty(NONE));
    graph.lists.extend_from_slice(args);
    graph.push(Node {
        head: CONSTR | (args.len() as u32) << 8,
        level,
        a: path,
        b,
    })
}

/// O(nodes): publish one scheme per item, as `from_old` does, with a
/// synthetic tuple for an item of several roots, then name the roots as
/// `from_old::resolve_roots` does.
fn finish(mut graph: Graph, schemes: &[&[Ty]], fixture: Fixture, unit: UnitRow) -> Segment {
    let mut publish_roots = Vec::new();
    for roots in schemes {
        if let [root] = roots {
            publish_roots.push(*root);
            continue;
        }
        publish_roots.push(tuple(&mut graph, GENERIC, roots));
    }
    let mut segment = publish(graph, &publish_roots, fixture.into_segment(unit));
    let mut out = Vec::new();
    let mut lists = 0usize;
    for (index, roots) in schemes.iter().enumerate() {
        let template = segment.templates[index];
        if roots.len() == 1 {
            let ty = if template.node_len == 0 {
                Ty(template.nodes)
            } else {
                Ty(RELATIVE)
            };
            out.push(SchemeRoot {
                template: index as u32,
                ty,
            });
        } else {
            for &reference in &segment.template_lists[lists..lists + roots.len()] {
                let ty = if reference.0 & RELATIVE != 0 {
                    reference
                } else {
                    segment.template_externals[reference.0 as usize]
                };
                out.push(SchemeRoot {
                    template: index as u32,
                    ty,
                });
            }
        }
        lists += template.list_len as usize;
    }
    segment.signature.roots = out.into();
    segment
}

/// O(1): an old node's descriptor.
fn desc(graph: &SharedGraph, r: TypeExprRef) -> TypeDesc {
    graph.nodes()[graph.node_offset(r).expect("a node of the graph")].desc
}

/// O(1): an old node's level.
fn level(graph: &SharedGraph, r: TypeExprRef) -> i32 {
    graph.nodes()[graph.node_offset(r).expect("a node of the graph")].level
}

/// O(1): the type of a value item.
fn value_type(item: &SignatureItem) -> TypeExprRef {
    match item {
        SignatureItem::SigValue(_, decl) => decl.val_type,
        other => panic!("not a value: {other:?}"),
    }
}

/// Drop deep old values where their recursive destructors have room.
fn drop_on_a_large_stack<T: Send + 'static>(value: T) {
    std::thread::Builder::new()
        .stack_size(256 * 1024 * 1024)
        .spawn(move || drop(value))
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn sizes() {
    assert_eq!(std::mem::size_of::<Frame>(), 16);
    assert_eq!(std::mem::size_of::<LidTask>(), 8);
    assert_eq!(std::mem::size_of::<SigTask>(), 8);
    assert_eq!(std::mem::size_of::<Output>(), 104);
    assert_eq!(std::mem::size_of::<Visits>(), 8);
    assert_eq!(std::mem::size_of::<Rebuild<'static>>(), 480);
}

#[test]
fn equal_nodes_stay_distinct_and_repeated_positions_stay_shared() {
    // let x: ('a, 'a, 'b, '_w); let y: '_w; let z: '_w; type t<'p> = ('p, 'p)
    let mut graph = Graph::default();
    let a = var(&mut graph, GENERIC);
    let b = var(&mut graph, GENERIC);
    let weak = var(&mut graph, 3);
    let x = tuple(&mut graph, GENERIC, &[a, a, b, weak]);
    let parameter = var(&mut graph, GENERIC);
    let manifest = tuple(&mut graph, GENERIC, &[parameter, parameter]);
    let mut f = Fixture::default();
    let unit = f.unit();
    // Roots: 0 x, 1 y, 2 z, 3 t's parameter, 4 t's manifest.
    f.value("x", 1, 0);
    f.value("y", 2, 1);
    f.value("z", 3, 2);
    let (ident, path) = f.binder("t", 4);
    let loc = f.loc(None, 0);
    let shape = add(&mut f.shapes, ShapeRow::Unstated);
    let variance = add(&mut f.variance, Variance::full().bits());
    let declaration = add(
        &mut f.type_declarations,
        TypeDecl {
            kind: DeclarationKind::Abstract,
            flags: 16,
            arity: 1,
            params: 3,
            manifest: 4,
            members: 0,
            member_len: 0,
            path,
            loc,
            variance,
        },
    );
    add(
        &mut f.type_details,
        TypeDetailsRow {
            parameter_roots: Range { start: 3, len: 1 },
            variance: Range {
                start: variance,
                len: 1,
            },
            attributes: Range::default(),
            inlined_records: Range::default(),
            representation: NONE,
            shape,
            newtype_level: NONE,
            scope_level: NONE,
        },
    );
    add(
        &mut f.ordered_items,
        SignatureItemRow {
            ident,
            declaration,
            kind: SignatureKind::Type,
            status: ItemStatus::Recursive(RecStatus::Not),
        },
    );
    f.close(0, 0);
    let segment = finish(
        graph,
        &[&[x], &[weak], &[weak], &[parameter, manifest]],
        f,
        unit,
    );
    let (output, visits) = run(&segment);
    // One shared node, three nodes of x's template, and t's parameter and
    // manifest: the synthetic tuple has no old node.
    assert_eq!(visits.count, 6);
    let published = output.into_published();
    let graph = &published.graph;
    assert!(graph.is_detached());
    assert_eq!(graph.nodes().len(), 6);
    let signature = &published.signature;
    let TypeDesc::Ttuple(list) = desc(graph, value_type(&signature[0])) else {
        panic!("x is a tuple");
    };
    let slots = graph.list(list);
    assert_eq!(slots.len(), 4);
    assert_eq!(slots[0], slots[1], "a repeated position stays one node");
    assert_ne!(slots[0], slots[2], "an equal node stays distinct");
    assert_eq!(slots[3], value_type(&signature[1]));
    assert_eq!(slots[3], value_type(&signature[2]));
    assert_eq!(level(graph, value_type(&signature[0])), GENERIC_LEVEL);
    assert_eq!(level(graph, slots[0]), GENERIC_LEVEL);
    assert_eq!(level(graph, slots[3]), 3);
    let SignatureItem::SigType(id, decl, OldRecStatus::TrecNot) = &signature[3] else {
        panic!("t is a type");
    };
    assert_eq!((id.name(), id.stamp()), ("t", 4));
    assert!(decl.type_path.is_none(), "an absent path comes back absent");
    assert_eq!(decl.type_params.len(), 1);
    let TypeDesc::Ttuple(list) = desc(graph, decl.type_manifest.unwrap()) else {
        panic!("t's manifest is a tuple");
    };
    assert_eq!(
        graph.list(list),
        &[decl.type_params[0], decl.type_params[0]]
    );
    assert_eq!(decl.type_variance[0].bits(), Variance::full().bits());
}

#[test]
fn ten_thousand_deep_types_make_one_old_node_per_node_on_a_two_mb_stack() {
    std::thread::Builder::new()
        .stack_size(2 * 1024 * 1024)
        .spawn(|| {
            let mut graph = Graph::default();
            let mut chains = [Ty(0); 2];
            for (chain, level) in chains.iter_mut().zip([GENERIC, 1]) {
                *chain = var(&mut graph, level);
                for _ in 1..N {
                    *chain = tuple(&mut graph, level, &[*chain]);
                }
            }
            let mut f = Fixture::default();
            let unit = f.unit();
            f.value("generic", 1, 0);
            f.value("local", 2, 1);
            f.close(0, 0);
            let segment = finish(graph, &[&[chains[0]], &[chains[1]]], f, unit);
            assert_eq!(segment.template_nodes.len(), N as usize);
            assert_eq!(segment.nodes.len(), N as usize);
            let mut result = None;
            let count = steps::scope(|| result = Some(run(&segment)));
            let (output, visits) = result.unwrap();
            assert_eq!(visits.count, 2 * u64::from(N));
            // 2N nodes, 2(N - 1) list slots, two items, three paths and two
            // locations.
            assert_eq!(count, 4 * u64::from(N) + 5);
            let published = output.into_published();
            let graph = &published.graph;
            for (item, expected) in published.signature.iter().zip([GENERIC_LEVEL, 1]) {
                let mut ty = value_type(item);
                for _ in 1..N {
                    assert_eq!(level(graph, ty), expected);
                    let TypeDesc::Ttuple(list) = desc(graph, ty) else {
                        panic!("a chain link is a tuple");
                    };
                    ty = graph.list(list)[0];
                }
                assert!(matches!(desc(graph, ty), TypeDesc::Tvar(None)));
            }
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn ten_thousand_nested_modules_on_a_two_mb_stack() {
    let output = std::thread::Builder::new()
        .stack_size(2 * 1024 * 1024)
        .spawn(|| {
            let mut f = Fixture::default();
            let unit = f.unit();
            for i in 0..N {
                let (ident, path) = f.binder("M", i as i32 + 1);
                let loc = f.loc(None, 0);
                let signature = add(&mut f.signatures, Range::default());
                let module_type = add(&mut f.module_types, ModuleTypeRow::Signature(signature));
                let declaration = add(
                    &mut f.modules,
                    ModuleRow {
                        module_type,
                        attributes: Range::default(),
                        loc,
                        path,
                    },
                );
                let start = f.ordered_items.len() as u32;
                add(
                    &mut f.ordered_items,
                    SignatureItemRow {
                        ident,
                        declaration,
                        kind: SignatureKind::Module,
                        status: ItemStatus::Recursive(RecStatus::Not),
                    },
                );
                f.close(signature - 1, start);
            }
            let segment = f.into_segment(unit);
            let mut result = None;
            let count = steps::scope(|| result = Some(run(&segment)));
            // Per level one path, one location, one item and one module type.
            assert_eq!(count, 4 * u64::from(N) + 1);
            let (output, visits) = result.unwrap();
            assert_eq!(visits.count, 0);
            let mut signature: &Signature = &output.signature;
            for i in 0..N {
                let [SignatureItem::SigModule(id, decl, OldRecStatus::TrecNot)] = &signature[..]
                else {
                    panic!("one module per level");
                };
                assert_eq!(id.stamp(), i as i32 + 1);
                assert!(decl.md_path.is_none());
                let ModuleType::MtySignature(inner) = &decl.md_type else {
                    panic!("a nested signature");
                };
                signature = &**inner;
            }
            assert!(signature.is_empty());
            output
        })
        .unwrap()
        .join()
        .unwrap();
    drop_on_a_large_stack(output);
}

#[test]
fn ten_thousand_deep_paths_and_longidents_on_a_two_mb_stack() {
    let lid = std::thread::Builder::new()
        .stack_size(2 * 1024 * 1024)
        .spawn(|| {
            let mut f = Fixture::default();
            let unit = f.unit();
            let name = f.string("M");
            for i in 0..N {
                add(
                    &mut f.paths,
                    PathRow::Dot {
                        parent: unit.path + i,
                        name,
                        position: i as i32,
                    },
                );
            }
            add(&mut f.longidents, LongidentRow::Ident(name));
            for i in 1..N {
                add(
                    &mut f.longidents,
                    LongidentRow::Dot {
                        parent: i - 1,
                        name,
                    },
                );
            }
            f.close(0, 0);
            let segment = f.into_segment(unit);
            let mut rebuild = Rebuild::new(&segment);
            assert_eq!(steps::scope(|| rebuild.paths()), u64::from(N) + 1);
            let mut path = rebuild.paths[N as usize];
            for i in (0..N).rev() {
                let crate::types::path::PathView::Pdot(parent, name, position) = *path.view()
                else {
                    panic!("a dotted path");
                };
                assert_eq!((name.as_str(), position), ("M", i as i32));
                path = parent;
            }
            assert_eq!(path, rebuild.paths[0]);
            let mut lid = None;
            assert_eq!(
                steps::scope(|| lid = Some(rebuild.longident(N - 1))),
                u64::from(N)
            );
            let lid = lid.unwrap();
            let mut at = &lid;
            for _ in 1..N {
                let Longident::Ldot(prefix, name) = at else {
                    panic!("a dotted longident");
                };
                assert_eq!(*name, StrIdx::from_raw(0));
                at = &**prefix;
            }
            assert_eq!(*at, Longident::Lident(StrIdx::from_raw(0)));
            assert_eq!(rebuild.components, ["M"]);
            lid
        })
        .unwrap()
        .join()
        .unwrap();
    drop_on_a_large_stack(lid);
}

#[test]
fn every_extended_descriptor_maps_to_its_old_descriptor() {
    let mut f = Fixture::default();
    let unit = f.unit();
    let int = f.ident("int", 0, NONE);
    let int = add(&mut f.paths, PathRow::Ident(int));
    let name = f.string("name");
    let a = f.string("a");
    let x = f.string("x");
    let y = f.string("y");
    let label_loc = f.loc(Some("File.res"), 3);
    let mut graph = Graph::default();
    let extra = |f: &mut Fixture, row: ExtraDescriptor| add(&mut f.descriptor_extras, row);

    // {"name": int}
    let string = constr(&mut graph, GENERIC, int, &[]);
    let nil = extra(&mut f, ExtraDescriptor::Nil);
    let nil = extended(&mut graph, GENERIC, nil, &[]);
    let field = extra(
        &mut f,
        ExtraDescriptor::Field {
            name,
            mutable: true,
        },
    );
    let field = extended(&mut graph, GENERIC, field, &[string, nil]);
    let object = extra(&mut f, ExtraDescriptor::Object);
    let object = extended(&mut graph, GENERIC, object, &[field]);

    // 'a. ('a, ~x: 'a, ?y: 'a) => 'a
    let univar = extra(&mut f, ExtraDescriptor::Univar(a));
    let univar = extended(&mut graph, GENERIC, univar, &[]);
    let start = graph.params.len() as u32;
    graph.params.extend([
        Param {
            ty: univar,
            label: NONE,
            loc: NONE,
        },
        Param {
            ty: univar,
            label: x << 1,
            loc: label_loc,
        },
        Param {
            ty: univar,
            label: y << 1 | 1,
            loc: label_loc,
        },
    ]);
    let arrow = graph.push(Node {
        head: ARROW | 3 << 8,
        level: GENERIC,
        a: univar.0,
        b: start,
    });
    let poly = extra(&mut f, ExtraDescriptor::Poly);
    let poly = extended(&mut graph, GENERIC, poly, &[arrow, univar]);

    // [< #A(int) | #B | -#C | #D(int & int) ] as 'more, named int<int>
    let argument = constr(&mut graph, GENERIC, int, &[]);
    let more = var(&mut graph, GENERIC);
    let fields = f.row_fields.len() as u32;
    for (label, types, kind) in [
        ("A", Range { start: 0, len: 1 }, RowFieldKind::Present),
        ("B", Range { start: 1, len: 0 }, RowFieldKind::Present),
        ("C", Range { start: 1, len: 0 }, RowFieldKind::Absent),
        (
            "D",
            Range { start: 1, len: 2 },
            RowFieldKind::Either {
                constant: false,
                matched: true,
            },
        ),
    ] {
        let name = f.string(label);
        add(
            &mut f.row_fields,
            RowFieldRow {
                name,
                types,
                link: NONE,
                kind,
            },
        );
    }
    let row = add(
        &mut f.variants,
        VariantRow {
            fields: Range {
                start: fields,
                len: 4,
            },
            more: 3,
            name: int,
            name_arguments: Range { start: 4, len: 1 },
            closed: true,
            fixed: false,
        },
    );
    let row = extra(&mut f, ExtraDescriptor::Variant(row));
    let variant = extended(
        &mut graph,
        GENERIC,
        row,
        &[argument, argument, argument, more, argument],
    );

    // module(M.N with F(X), <unresolved>, M.<unresolved>) with one argument
    let m = f.string("M");
    let n = f.string("N");
    let functor = f.string("F");
    let argument_name = f.string("X");
    let lid_m = add(&mut f.longidents, LongidentRow::Ident(m));
    let lid_mn = add(
        &mut f.longidents,
        LongidentRow::Dot {
            parent: lid_m,
            name: n,
        },
    );
    let lid_f = add(&mut f.longidents, LongidentRow::Ident(functor));
    let lid_x = add(&mut f.longidents, LongidentRow::Ident(argument_name));
    let lid_fx = add(
        &mut f.longidents,
        LongidentRow::Apply {
            functor: lid_f,
            argument: lid_x,
        },
    );
    let lid_unresolved = add(&mut f.longidents, LongidentRow::Unresolved);
    let lid_m_unresolved = add(
        &mut f.longidents,
        LongidentRow::Dot {
            parent: lid_m,
            name: NONE,
        },
    );
    let lids = f.indices.len() as u32;
    f.indices
        .extend([lid_mn, lid_fx, lid_unresolved, lid_m_unresolved]);
    let package = add(
        &mut f.packages,
        PackageRow {
            path: int,
            longidents: Range {
                start: lids,
                len: 4,
            },
            arguments: Range { start: 0, len: 1 },
        },
    );
    let package = extra(&mut f, ExtraDescriptor::Package(package));
    let package_argument = constr(&mut graph, GENERIC, int, &[]);
    let package = extended(&mut graph, GENERIC, package, &[package_argument]);

    // A substitution marker, and a shared (non-generic) empty object.
    let target = var(&mut graph, GENERIC);
    let substitution = extra(&mut f, ExtraDescriptor::Substitution);
    let substitution = extended(&mut graph, GENERIC, substitution, &[target]);
    let local_nil = extra(&mut f, ExtraDescriptor::Nil);
    let local_nil = extended(&mut graph, 2, local_nil, &[]);
    let local_object = extra(&mut f, ExtraDescriptor::Object);
    let local_object = extended(&mut graph, 2, local_object, &[local_nil]);

    for (index, name) in ["object", "poly", "variant", "package", "subst", "local"]
        .into_iter()
        .enumerate()
    {
        f.value(name, index as i32 + 1, index as u32);
    }
    f.close(0, 0);
    let segment = finish(
        graph,
        &[
            &[object],
            &[poly],
            &[variant],
            &[package],
            &[substitution],
            &[local_object],
        ],
        f,
        unit,
    );
    let published = to_old(&segment).into_published();
    let graph = &published.graph;
    let signature = &published.signature;
    let names = published.names.read().unwrap();

    let TypeDesc::Tobject { fields } = desc(graph, value_type(&signature[0])) else {
        panic!("an object");
    };
    let TypeDesc::Tfield {
        name,
        mutability,
        typ,
        rest,
    } = desc(graph, fields)
    else {
        panic!("a field");
    };
    assert_eq!(name.as_str(), "name");
    assert!(mutability.is_persistent());
    assert_eq!(mutability.persistent_value(), MutableFlag::Mutable);
    assert!(matches!(desc(graph, typ), TypeDesc::Tconstr { .. }));
    assert!(matches!(desc(graph, rest), TypeDesc::Tnil));

    let TypeDesc::Tpoly { body, vars } = desc(graph, value_type(&signature[1])) else {
        panic!("a polytype");
    };
    let vars = graph.list(vars);
    assert_eq!(vars.len(), 1);
    assert!(matches!(desc(graph, vars[0]), TypeDesc::Tunivar(Some(a)) if a.as_str() == "a"));
    let TypeDesc::Tarrow { args, ret } = desc(graph, body) else {
        panic!("an arrow");
    };
    assert_eq!(ret, vars[0]);
    let args = graph.args(args);
    assert_eq!(args.len(), 3);
    assert!(args.iter().all(|arg| arg.typ == vars[0]));
    assert!(args[0].label().is_nolabel());
    assert_eq!(args[0].label().loc(), DeclLoc::none());
    assert!(args[1].label().is_labelled());
    assert_eq!(args[1].label().label_name(), Some("x"));
    assert!(args[2].label().is_optional());
    assert_eq!(args[2].label().label_name(), Some("y"));
    let loc = args[1].label().loc();
    assert_eq!(loc.kind(), DeclLocKind::Portable);
    let location = graph.locations().get(loc.index());
    assert_eq!((location.loc_start.line, location.loc_start.cnum), (3, 30));
    let file = location.loc_start.file_name.raw();
    assert!(
        graph
            .carried
            .file_names
            .iter()
            .any(|(key, name)| *key == file && name == "File.res")
    );

    let TypeDesc::Tvariant(row) = desc(graph, value_type(&signature[2])) else {
        panic!("a variant");
    };
    let row = graph.row(row);
    assert!(row.row_closed && !row.row_fixed);
    assert!(matches!(desc(graph, row.row_more), TypeDesc::Tvar(None)));
    let labels: Vec<&str> = row
        .row_fields
        .iter()
        .map(|(label, _)| label.as_str())
        .collect();
    assert_eq!(labels, ["A", "B", "C", "D"]);
    let RowField::Rpresent(Some(present)) = &row.row_fields[0].1 else {
        panic!("a present field with an argument");
    };
    assert!(matches!(row.row_fields[1].1, RowField::Rpresent(None)));
    assert!(matches!(row.row_fields[2].1, RowField::Rabsent));
    let RowField::Reither {
        constant: false,
        types,
        matched: true,
        link,
    } = &row.row_fields[3].1
    else {
        panic!("an either field");
    };
    assert_eq!(types, &[*present, *present], "one node in every position");
    assert_eq!(*link, RowFieldRef::null());
    let (row_path, row_arguments) = row.row_name.as_ref().expect("a named row");
    assert_eq!(row_path.name(), "int");
    assert_eq!(row_arguments, &[*present]);

    let TypeDesc::Tpackage { path, lids, args } = desc(graph, value_type(&signature[3])) else {
        panic!("a package");
    };
    assert_eq!(path.name(), "int");
    assert_eq!(graph.list(args).len(), 1);
    let text = |name: StrIdx| names.get(&name.raw()).map(String::as_str);
    let lids = graph.lids(lids);
    assert_eq!(lids.len(), 4);
    let Longident::Ldot(prefix, last) = &lids[0] else {
        panic!("M.N");
    };
    assert_eq!(**prefix, Longident::Lident(StrIdx::from_raw(0)));
    assert_eq!(
        (text(StrIdx::from_raw(0)), text(*last)),
        (Some("M"), Some("N"))
    );
    let Longident::Lapply(f_lid, x_lid) = &lids[1] else {
        panic!("F(X)");
    };
    let (Longident::Lident(f_name), Longident::Lident(x_name)) = (&**f_lid, &**x_lid) else {
        panic!("F and X are identifiers");
    };
    assert_eq!((text(*f_name), text(*x_name)), (Some("F"), Some("X")));
    assert_eq!(lids[2], Longident::Lident(UNRESOLVED));
    assert_eq!(text(UNRESOLVED), None);
    assert!(matches!(&lids[3], Longident::Ldot(_, name) if *name == UNRESOLVED));

    let TypeDesc::Tsubst(target) = desc(graph, value_type(&signature[4])) else {
        panic!("a substitution");
    };
    assert!(matches!(desc(graph, target), TypeDesc::Tvar(None)));

    let local = value_type(&signature[5]);
    assert_eq!(level(graph, local), 2);
    let TypeDesc::Tobject { fields } = desc(graph, local) else {
        panic!("a shared object");
    };
    assert!(matches!(desc(graph, fields), TypeDesc::Tnil));
    assert_eq!(level(graph, fields), 2);
}

#[test]
fn every_metadata_variant_maps_to_its_old_variant() {
    let mut f = Fixture::default();
    let unit = f.unit();
    let text = f.string("text");
    let other = f.string("other");
    let plain = f.loc(None, 0);
    let located = f.loc(Some("File.res"), 7);

    // Attribute payloads.
    let pair = add(
        &mut f.string_pairs,
        StringPair {
            first: text,
            second: other,
        },
    );
    let pairs = Range {
        start: pair,
        len: 1,
    };
    let tuple = f.indices.len() as u32;
    f.indices.extend([text, other]);
    let strings = Range {
        start: tuple,
        len: 2,
    };
    let fragment_bytes = f.bytes.len() as u32;
    f.bytes.extend_from_slice(&[0, 255, 7]);
    let fragment = add(
        &mut f.marshal_fragments,
        MarshalFragmentRow {
            bytes: Range {
                start: fragment_bytes,
                len: 3,
            },
            objects: 1,
            size_32: 2,
            size_64: 3,
        },
    );
    let deprecated = |f: &mut Fixture, reason: SemanticStringValue| {
        add(
            &mut f.deprecations,
            DeprecatedRow {
                reason,
                migrate: fragment,
                migrate_in_pipe_chain: NONE,
                can_be_automigrated: true,
            },
        )
    };
    let missing = deprecated(&mut f, SemanticStringValue::Missing);
    let valid = deprecated(&mut f, SemanticStringValue::Valid(text));
    let invalid = deprecated(&mut f, SemanticStringValue::Invalid(located));
    let semantic_valid = add(
        &mut f.semantic_strings,
        SemanticStringRow {
            value: SemanticStringValue::Valid(text),
            braces: 2,
            template: true,
        },
    );
    let semantic_invalid = add(
        &mut f.semantic_strings,
        SemanticStringRow {
            value: SemanticStringValue::Invalid(plain),
            braces: 0,
            template: false,
        },
    );
    let payloads = [
        AttributePayloadRow::Empty,
        AttributePayloadRow::Str(text),
        AttributePayloadRow::Int(-3),
        AttributePayloadRow::IntLiteral(text),
        AttributePayloadRow::Float(text),
        AttributePayloadRow::BigInt(text),
        AttributePayloadRow::Bool(true),
        AttributePayloadRow::Ident(text),
        AttributePayloadRow::Deprecated(missing),
        AttributePayloadRow::Deprecated(valid),
        AttributePayloadRow::Deprecated(invalid),
        AttributePayloadRow::Structure(pairs),
        AttributePayloadRow::SemanticString(semantic_valid),
        AttributePayloadRow::SemanticString(semantic_invalid),
        AttributePayloadRow::StrTuple(strings),
    ];
    let first_payload = f.attribute_payloads.len() as u32;
    f.attribute_payloads.extend(payloads);
    let attribute = add(
        &mut f.attributes,
        AttributeRow {
            name: other,
            payload: first_payload + 1,
            name_loc: located,
            loc: plain,
        },
    );

    // FFI descriptions.
    let int_pair = add(
        &mut f.string_int_pairs,
        StringIntPair {
            name: text,
            value: 5,
        },
    );
    let ranged = add(&mut f.ranges, pairs);
    let constants = [
        ConstantArgumentRow::Int(9),
        ConstantArgumentRow::String(text),
        ConstantArgumentRow::Json(other),
    ]
    .map(|row| add(&mut f.constant_arguments, row));
    let attrs = [
        FfiAttributeRow::PolyVarString(pairs),
        FfiAttributeRow::PolyVar(NONE),
        FfiAttributeRow::PolyVar(ranged),
        FfiAttributeRow::Int(Range {
            start: int_pair,
            len: 1,
        }),
        FfiAttributeRow::Constant(constants[0]),
        FfiAttributeRow::Constant(constants[1]),
        FfiAttributeRow::Constant(constants[2]),
        FfiAttributeRow::Unit,
        FfiAttributeRow::Nothing,
        FfiAttributeRow::Ignore,
        FfiAttributeRow::Unwrap,
    ]
    .map(|row| add(&mut f.ffi_attributes, row));
    let call_params = f.ffi_params.len() as u32;
    for label in [
        FfiLabelRow::Labelled,
        FfiLabelRow::Positional,
        FfiLabelRow::Optional,
    ] {
        add(
            &mut f.ffi_params,
            FfiParamRow {
                attribute: attrs[0],
                label,
            },
        );
    }
    let object_params = f.ffi_params.len() as u32;
    for label in [
        FfiLabelRow::ObjectEmpty,
        FfiLabelRow::ObjectLabel(text),
        FfiLabelRow::ObjectOptional {
            name: other,
            no_nested_option: true,
        },
    ] {
        add(
            &mut f.ffi_params,
            FfiParamRow {
                attribute: attrs[8],
                label,
            },
        );
    }
    let named = add(
        &mut f.external_modules,
        ExternalModuleRow {
            bundle: text,
            binding_hint: other,
            import_attributes: ranged,
        },
    );
    let bare = add(
        &mut f.external_modules,
        ExternalModuleRow {
            bundle: text,
            binding_hint: NONE,
            import_attributes: NONE,
        },
    );
    let kinds = [
        ExternalKindRow::Value(text),
        ExternalKindRow::Send(text),
        ExternalKindRow::New(text),
        ExternalKindRow::Get(text),
        ExternalKindRow::Set(text),
        ExternalKindRow::GetIndex,
        ExternalKindRow::SetIndex,
    ];
    let sources = [
        ModuleSourceRow::Absent,
        ModuleSourceRow::Itself,
        ModuleSourceRow::Named(named),
        ModuleSourceRow::Named(bare),
    ];
    let declarations: Vec<u32> = kinds
        .iter()
        .zip(sources.iter().cycle())
        .map(|(&kind, &module)| {
            add(
                &mut f.external_declarations,
                ExternalDeclRow {
                    kind,
                    module,
                    scopes: strings,
                    effective_arity: 4,
                    variadic: true,
                },
            )
        })
        .collect();
    let wrappers = [
        ReturnWrapperRow::Unset,
        ReturnWrapperRow::Identity,
        ReturnWrapperRow::NullToOption,
        ReturnWrapperRow::NullUndefinedToOption,
    ];
    let calls: Vec<u32> = wrappers
        .iter()
        .map(|&return_wrapper| {
            add(
                &mut f.ffi,
                FfiRow::Call {
                    params: Range {
                        start: call_params,
                        len: 3,
                    },
                    declaration: declarations[0],
                    return_wrapper,
                },
            )
        })
        .collect();
    let object = add(
        &mut f.ffi,
        FfiRow::Object(Range {
            start: object_params,
            len: 3,
        }),
    );
    let inlines = [
        InlineConstantRow::String(text),
        InlineConstantRow::Bool(true),
        InlineConstantRow::Int(-4),
        InlineConstantRow::Bigint {
            positive: false,
            digits: other,
        },
        InlineConstantRow::Float(text),
    ]
    .map(|row| add(&mut f.inline_constants, row));
    let primitives = [
        PrimitiveKindRow::Intrinsic,
        PrimitiveKindRow::External(calls[0]),
        PrimitiveKindRow::Inline(inlines[0]),
    ]
    .map(|kind| {
        add(
            &mut f.primitives,
            PrimitiveRow {
                name: text,
                arity: 2,
                kind,
                native_float: true,
                from_constructor: false,
            },
        )
    });

    // Runtime representations.
    let literals = [
        LiteralRow::String(text),
        LiteralRow::Int(-1),
        LiteralRow::Float(text),
        LiteralRow::BigInt(other),
        LiteralRow::Bool(false),
        LiteralRow::Null,
        LiteralRow::Undefined,
    ]
    .map(|row| add(&mut f.literals, row));
    let blocks = [
        BlockTypeRow::Number,
        BlockTypeRow::String,
        BlockTypeRow::Bigint,
        BlockTypeRow::Boolean,
        BlockTypeRow::Array,
        BlockTypeRow::Symbol,
        BlockTypeRow::Function,
        BlockTypeRow::Object,
        BlockTypeRow::Unknown,
        BlockTypeRow::Class {
            name: text,
            ancestors: strings,
        },
    ]
    .map(|row| add(&mut f.block_types, row));
    let shapes = [
        ShapeRow::Unstated,
        ShapeRow::NeverUndefined,
        ShapeRow::Recognized(blocks[9]),
    ]
    .map(|row| add(&mut f.shapes, row));
    let cases = f.runtime_constructors.len() as u32;
    for row in [
        RuntimeConstructorRow::Constant {
            name: text,
            literal: literals[0],
        },
        RuntimeConstructorRow::Tagged {
            name: other,
            literal: literals[1],
            tag_name: text,
        },
        RuntimeConstructorRow::Tagged {
            name: other,
            literal: literals[2],
            tag_name: NONE,
        },
        RuntimeConstructorRow::Untagged {
            name: text,
            literal: literals[3],
            block_type: blocks[4],
        },
    ] {
        add(&mut f.runtime_constructors, row);
    }
    let layout = add(
        &mut f.layouts,
        LayoutRow {
            constructors: Range {
                start: cases,
                len: 4,
            },
            tag_name: other,
            unboxed: true,
        },
    );
    let representations = [
        RecordRepresentationRow::Regular,
        RecordRepresentationRow::Array,
        RecordRepresentationRow::Unboxed(true),
        RecordRepresentationRow::Extension,
        RecordRepresentationRow::Inlined {
            name: text,
            position: 3,
            layout,
        },
    ]
    .map(|row| add(&mut f.record_representations, row));
    f.close(0, 0);
    let segment = f.into_segment(unit);
    let mut rebuild = Rebuild::new(&segment);
    rebuild.locations();
    rebuild.paths();
    rebuild.layouts();
    let owned = |text: &str| text.to_owned();

    // Locations: a coordinate-free one is a source handle, any other one an
    // entry of the location table, with its file carried by key.
    assert_eq!(rebuild.loc(plain), DeclLoc::none());
    let handle = rebuild.loc(located);
    assert_eq!(handle.kind(), DeclLocKind::Portable);
    let location = rebuild.coordinates[handle.index()];
    assert_eq!(
        (
            location.loc_start.line,
            location.loc_end.cnum,
            location.loc_ghost
        ),
        (7, 71, false)
    );
    let key = location.loc_start.file_name.raw();
    assert_eq!(rebuild.file_names, [(key, owned("File.res"))]);

    let payload = |row: u32| rebuild.attribute_payload(first_payload + row);
    assert_eq!(payload(0), AttributePayload::Empty);
    assert_eq!(payload(1), AttributePayload::Str(owned("text")));
    assert_eq!(payload(2), AttributePayload::Int(-3));
    assert_eq!(payload(3), AttributePayload::IntLiteral(owned("text")));
    assert_eq!(payload(4), AttributePayload::Float(owned("text")));
    assert_eq!(payload(5), AttributePayload::BigInt(owned("text")));
    assert_eq!(payload(6), AttributePayload::Bool(true));
    assert_eq!(payload(7), AttributePayload::Ident(owned("text")));
    let migrate = Some(MarshalFragment {
        bytes: vec![0, 255, 7],
        objects: 1,
        size_32: 2,
        size_64: 3,
    });
    for (row, reason) in [
        (8, Ok(None)),
        (9, Ok(Some(owned("text")))),
        (10, Err(rebuild.loc(located))),
    ] {
        assert_eq!(
            payload(row),
            AttributePayload::Deprecated {
                reason,
                can_be_automigrated: true,
                migrate: migrate.clone(),
                migrate_in_pipe_chain: None,
            }
        );
    }
    assert_eq!(
        payload(11),
        AttributePayload::Structure(vec![(owned("text"), owned("other"))])
    );
    assert_eq!(
        payload(12),
        AttributePayload::SemanticString(Box::new(SemanticStringPayload {
            semantic: Ok(owned("text")),
            braces: 2,
            template: true,
        }))
    );
    assert_eq!(
        payload(13),
        AttributePayload::SemanticString(Box::new(SemanticStringPayload {
            semantic: Err(DeclLoc::none()),
            braces: 0,
            template: false,
        }))
    );
    assert_eq!(
        payload(14),
        AttributePayload::StrTuple(vec![owned("text"), owned("other")])
    );
    let attributes = rebuild.attributes(Range {
        start: attribute,
        len: 1,
    });
    assert_eq!(attributes.len(), 1);
    assert_eq!(attributes[0].attr_name.txt, "other");
    assert_eq!(attributes[0].attr_name.loc, rebuild.loc(located));
    assert_eq!(attributes[0].attr_loc, DeclLoc::none());
    assert_eq!(attributes[0].attr_payload, payload(1));

    let pairs_old = vec![(owned("text"), owned("other"))];
    let expected_attrs = [
        ffi::Attr::PolyVarString {
            descr: pairs_old.clone(),
        },
        ffi::Attr::PolyVar { descr: None },
        ffi::Attr::PolyVar {
            descr: Some(pairs_old.clone()),
        },
        ffi::Attr::Int(vec![(owned("text"), 5)]),
        ffi::Attr::ArgCst(ffi::Cst::ArgIntLit(9)),
        ffi::Attr::ArgCst(ffi::Cst::ArgStringLit(owned("text"))),
        ffi::Attr::ArgCst(ffi::Cst::ArgJsonLit(owned("other"))),
        ffi::Attr::ExternUnit,
        ffi::Attr::Nothing,
        ffi::Attr::Ignore,
        ffi::Attr::Unwrap,
    ];
    for (row, expected) in attrs.iter().zip(expected_attrs) {
        assert_eq!(rebuild.ffi_attribute(*row), expected);
    }
    let expected_kinds = [
        ffi::DeclKind::DeclVal {
            name: owned("text"),
        },
        ffi::DeclKind::DeclSend {
            name: owned("text"),
        },
        ffi::DeclKind::DeclNew {
            name: owned("text"),
        },
        ffi::DeclKind::DeclGet {
            name: owned("text"),
        },
        ffi::DeclKind::DeclSet {
            name: owned("text"),
        },
        ffi::DeclKind::DeclGetIndex,
        ffi::DeclKind::DeclSetIndex,
    ];
    let expected_modules = [
        None,
        Some(ffi::ModuleSource::ModuleItself),
        Some(ffi::ModuleSource::ModuleNamed(ffi::ExternalModuleName {
            bundle: owned("text"),
            module_bind_name: ffi::ModuleBindName::PhintName(owned("other")),
            import_attributes: Some(pairs_old.clone()),
        })),
        Some(ffi::ModuleSource::ModuleNamed(ffi::ExternalModuleName {
            bundle: owned("text"),
            module_bind_name: ffi::ModuleBindName::PhintNothing,
            import_attributes: None,
        })),
    ];
    for (index, (kind, module_)) in expected_kinds
        .into_iter()
        .zip(expected_modules.iter().cycle())
        .enumerate()
    {
        assert_eq!(
            rebuild.external_declaration(declarations[index]),
            ffi::ExternalDecl {
                kind,
                module_: module_.clone(),
                scopes: vec![owned("text"), owned("other")],
                variadic: true,
                effective_arity: 4,
            }
        );
    }
    let call_labels = [
        ffi::LabelNoname::ArgLabel,
        ffi::LabelNoname::ArgEmpty,
        ffi::LabelNoname::ArgOptional,
    ];
    let expected_wrappers = [
        ffi::ReturnWrapper::ReturnUnset,
        ffi::ReturnWrapper::ReturnIdentity,
        ffi::ReturnWrapper::ReturnNullToOpt,
        ffi::ReturnWrapper::ReturnNullUndefinedToOpt,
    ];
    for (call, wrapper) in calls.iter().zip(expected_wrappers) {
        let ffi::ExternalFfi::FfiBs(params, return_wrapper, declaration) = rebuild.ffi(*call)
        else {
            panic!("a call");
        };
        assert_eq!(return_wrapper, wrapper);
        assert_eq!(declaration, rebuild.external_declaration(declarations[0]));
        let labels: Vec<_> = params.iter().map(|param| param.arg_label).collect();
        assert_eq!(labels, call_labels);
        assert!(
            params
                .iter()
                .all(|param| param.arg_type == expected_attrs_first())
        );
    }
    let ffi::ExternalFfi::FfiObjCreate(params) = rebuild.ffi(object) else {
        panic!("an object creation");
    };
    let labels: Vec<_> = params
        .iter()
        .map(|param| param.obj_arg_label.clone())
        .collect();
    assert_eq!(
        labels,
        [
            ffi::Label::ObjEmpty,
            ffi::Label::ObjLabel {
                name: owned("text")
            },
            ffi::Label::ObjOptional {
                name: owned("other"),
                for_sure_no_nested_option: true,
            },
        ]
    );
    assert!(
        params
            .iter()
            .all(|param| param.obj_arg_type == ffi::Attr::Nothing)
    );
    let expected_inlines = [
        ffi::InlineConst::ConstString(owned("text")),
        ffi::InlineConst::ConstBool(true),
        ffi::InlineConst::ConstInt(-4),
        ffi::InlineConst::ConstBigint {
            positive: false,
            digits: owned("other"),
        },
        ffi::InlineConst::ConstFloat(owned("text")),
    ];
    for (row, expected) in inlines.iter().zip(expected_inlines) {
        assert_eq!(rebuild.inline_constant(*row), expected);
    }
    let kinds: Vec<_> = primitives
        .iter()
        .map(|row| {
            let primitive = rebuild.primitive(*row);
            assert_eq!(primitive.prim_name, "text");
            assert_eq!(primitive.prim_arity, 2);
            assert!(primitive.prim_native_float && !primitive.prim_from_constructor);
            primitive.prim_kind
        })
        .collect();
    assert!(matches!(kinds[0], PrimKind::KindIntrinsic));
    assert!(
        matches!(&kinds[1], PrimKind::KindExternal(external) if **external == rebuild.ffi(calls[0]))
    );
    assert!(
        matches!(&kinds[2], PrimKind::KindInlineConst(constant) if **constant == ffi::InlineConst::ConstString(owned("text")))
    );

    let expected_literals = [
        LiteralTag::String(owned("text")),
        LiteralTag::Int(-1),
        LiteralTag::Float(owned("text")),
        LiteralTag::BigInt(owned("other")),
        LiteralTag::Bool(false),
        LiteralTag::Null,
        LiteralTag::Undefined,
    ];
    for (row, expected) in literals.iter().zip(expected_literals) {
        assert_eq!(rebuild.literal(*row), expected);
    }
    let class = BlockType::Instance(Instance::Class {
        name: owned("text"),
        ancestors: vec![owned("text"), owned("other")],
        blocks: ClassBlocks::fresh(2),
    });
    let expected_blocks = [
        BlockType::Number,
        BlockType::String,
        BlockType::Bigint,
        BlockType::Boolean,
        BlockType::Instance(Instance::Array(ShapeAllocation::fresh())),
        BlockType::Symbol,
        BlockType::Function,
        BlockType::Object,
        BlockType::Unknown,
        class.clone(),
    ];
    // Block equality ignores allocation identity, which `from_old` drops.
    for (row, expected) in blocks.iter().zip(expected_blocks) {
        assert_eq!(rebuild.block_type(*row), expected);
    }
    assert_eq!(rebuild.shape(shapes[0]), ValueShape::Unstated);
    assert_eq!(rebuild.shape(shapes[1]), ValueShape::NeverUndefined);
    assert_eq!(
        rebuild.shape(shapes[2]).block_type(),
        Some(&class),
        "a recognized shape keeps its kind"
    );
    let layout = &rebuild.layouts[layout as usize];
    assert!(layout.unboxed);
    assert_eq!(layout.matching_facts.tag_name.as_deref(), Some("other"));
    assert!(
        matches!(&layout.constructors[0], ConstructorCase::Constant(tag) if tag.name.as_str() == "text" && tag.literal == LiteralTag::String(owned("text")))
    );
    assert!(matches!(
        &layout.constructors[1],
        ConstructorCase::Block(Block::Tagged(TaggedBlock { tag, tag_name: Some(name) }))
            if tag.name.as_str() == "other" && tag.literal == LiteralTag::Int(-1) && name == "text"
    ));
    assert!(matches!(
        &layout.constructors[2],
        ConstructorCase::Block(Block::Tagged(TaggedBlock { tag_name: None, .. }))
    ));
    assert!(matches!(
        &layout.constructors[3],
        ConstructorCase::Block(Block::Untagged {
            block_type: BlockType::Instance(Instance::Array(_)),
            ..
        })
    ));
    assert_eq!(
        layout.matching_facts.literal_tags,
        [LiteralTag::String(owned("text"))]
    );
    assert_eq!(layout.matching_facts.block_types.len(), 1);
    let expected_representations = [
        RecordRepresentation::RecordRegular,
        RecordRepresentation::RecordArray,
        RecordRepresentation::RecordUnboxed(true),
        RecordRepresentation::RecordExtension,
        RecordRepresentation::RecordInlined {
            name: owned("text"),
            representation: ConstructorReference {
                variant: LayoutRef::from_usize(0),
                position: 3,
            },
        },
    ];
    for (row, expected) in representations.iter().zip(expected_representations) {
        assert_eq!(rebuild.record_representation(*row), expected);
    }
}

/// O(1): the old form of the first FFI attribute row of the metadata test.
fn expected_attrs_first() -> ffi::Attr {
    ffi::Attr::PolyVarString {
        descr: vec![("text".to_owned(), "other".to_owned())],
    }
}

#[test]
fn every_item_kind_keeps_identifiers_paths_and_declarations() {
    let mut f = Fixture::default();
    let unit = f.unit();
    let mut graph = Graph::default();
    let weak = var(&mut graph, 1);
    let loc = f.loc(None, 0);
    let empty = Range::default();
    let shape = add(&mut f.shapes, ShapeRow::Unstated);
    let roots = |start: u32, len: u32| Range { start, len };

    // 0: let v (absent path); 1: let u (path Test.u, position 1).
    f.value("v", 1, 0);
    let u_name = f.string("u");
    let u_path = add(
        &mut f.paths,
        PathRow::Dot {
            parent: unit.path,
            name: u_name,
            position: 1,
        },
    );
    let u = f.value("u", 2, 1);
    let u_value = f.ordered_items[u as usize].declaration;
    f.values[u_value as usize].path = u_path;

    // 2: type r = {x: '_w, mutable y?: '_w}, rec first.
    let type_item = |f: &mut Fixture,
                     name: &str,
                     stamp: i32,
                     kind: DeclarationKind,
                     flags: u8,
                     members: (u32, u32),
                     details: TypeDetailsRow,
                     status: RecStatus| {
        let (ident, path) = f.binder(name, stamp);
        let declaration = add(
            &mut f.type_declarations,
            TypeDecl {
                kind,
                flags,
                arity: 0,
                params: details.parameter_roots.start,
                manifest: NONE,
                members: members.0,
                member_len: members.1,
                path,
                loc,
                variance: details.variance.start,
            },
        );
        add(&mut f.type_details, details);
        add(
            &mut f.ordered_items,
            SignatureItemRow {
                ident,
                declaration,
                kind: SignatureKind::Type,
                status: ItemStatus::Recursive(status),
            },
        );
    };
    let details =
        |representation: u32, inlined_records: Range, levels: (u32, u32)| TypeDetailsRow {
            parameter_roots: Range::default(),
            variance: Range::default(),
            attributes: Range::default(),
            inlined_records,
            representation,
            shape,
            newtype_level: levels.0,
            scope_level: levels.1,
        };
    let label = |f: &mut Fixture, name: &str, root: u32, mutable: bool, optional: bool| {
        let ident = f.ident(name, 0, NONE);
        let runtime_name = if mutable { NONE } else { f.string("ex") };
        add(
            &mut f.labels,
            LabelRow {
                ident,
                runtime_name,
                ty: root,
                attributes: Range::default(),
                loc,
                mutable,
                optional,
            },
        )
    };
    let x = label(&mut f, "x", 2, false, false);
    let y = label(&mut f, "y", 3, true, true);
    let members = f.members.len() as u32;
    for (position, (label, flags)) in [(x, 0), (y, 3)].into_iter().enumerate() {
        let name = f.labels[label as usize].ident;
        let name = f.identifiers[name as usize].name;
        add(
            &mut f.members,
            MemberDecl {
                name,
                args: label,
                tag_or_pos: position as u32,
                flags,
            },
        );
    }
    let regular = add(
        &mut f.record_representations,
        RecordRepresentationRow::Regular,
    );
    type_item(
        &mut f,
        "r",
        3,
        DeclarationKind::Record,
        0,
        (members, 2),
        details(regular, empty, (NONE, NONE)),
        RecStatus::First,
    );

    // 3: type c = A | B('_w): '_w, with an inlined record {z: '_w}, a local
    // constraint at levels (2, -1), private, immediate and unboxed; rec next.
    let literal = add(&mut f.literals, LiteralRow::Int(1));
    let a = f.ident("A", 0, NONE);
    let b = f.ident("B", 0, NONE);
    let no_arguments = add(
        &mut f.constructor_arguments,
        ConstructorArgumentsRow::Tuple(roots(4, 0)),
    );
    let b_arguments = add(
        &mut f.constructor_arguments,
        ConstructorArgumentsRow::Tuple(roots(4, 1)),
    );
    let first_constructor = f.constructors.len() as u32;
    for (ident, runtime_tag, arguments, result) in
        [(a, literal, no_arguments, NONE), (b, NONE, b_arguments, 5)]
    {
        add(
            &mut f.constructors,
            ConstructorRow {
                ident,
                runtime_tag,
                arguments,
                result,
                attributes: Range::default(),
                loc,
            },
        );
    }
    let members = f.members.len() as u32;
    for position in 0..2 {
        let constructor = f.constructors[(first_constructor + position) as usize];
        let name = f.identifiers[constructor.ident as usize].name;
        add(
            &mut f.members,
            MemberDecl {
                name,
                args: first_constructor + position,
                tag_or_pos: position,
                flags: if position == 0 { 1 } else { 2 },
            },
        );
    }
    let layout = add(
        &mut f.layouts,
        LayoutRow {
            constructors: Range::default(),
            tag_name: NONE,
            unboxed: false,
        },
    );
    let z = label(&mut f, "z", 6, false, false);
    let inlined_name = f.string("c.B");
    let inlined = add(
        &mut f.inlined_records,
        InlinedRecordRow {
            name: inlined_name,
            labels: Range { start: z, len: 1 },
        },
    );
    type_item(
        &mut f,
        "c",
        4,
        DeclarationKind::Variant,
        1 | 2 | 4 | 8,
        (members, 2),
        details(
            layout,
            Range {
                start: inlined,
                len: 1,
            },
            (2, -1i32 as u32),
        ),
        RecStatus::Next,
    );

    // 4: type o = .., rec not (no roots).
    let no_members = f.members.len() as u32;
    type_item(
        &mut f,
        "o",
        5,
        DeclarationKind::Open,
        0,
        (no_members, 0),
        details(NONE, empty, (NONE, NONE)),
        RecStatus::Not,
    );

    // 5: exception E({w: '_w}), extending exn.
    let exn = f.ident("exn", 0, NONE);
    let exn = add(&mut f.paths, PathRow::Ident(exn));
    let w = label(&mut f, "w", 7, false, false);
    let record_arguments = add(
        &mut f.constructor_arguments,
        ConstructorArgumentsRow::Record(Range { start: w, len: 1 }),
    );
    let extension = add(
        &mut f.extensions,
        ExtensionRow {
            path: exn,
            parameters: roots(7, 0),
            result: NONE,
            arguments: record_arguments,
            attributes: Range::default(),
            loc,
            private: true,
            exception: true,
        },
    );
    let (ident, _) = f.binder("E", 6);
    add(
        &mut f.ordered_items,
        SignatureItemRow {
            ident,
            declaration: extension,
            kind: SignatureKind::Extension,
            status: ItemStatus::Extension(ExtensionStatus::Exception),
        },
    );

    // 6: module M: Test.u's module type path; 7: module N = alias (absent).
    // 8: module type S = {let s}; 9: module type F = (X: S) => {};
    // 10: module type G = () => S; 11: module type H.
    let module =
        |f: &mut Fixture, name: &str, stamp: i32, module_type: u32, kind: SignatureKind| {
            let (ident, path) = f.binder(name, stamp);
            let declaration = add(
                &mut f.modules,
                ModuleRow {
                    module_type,
                    attributes: Range::default(),
                    loc,
                    path,
                },
            );
            add(
                &mut f.ordered_items,
                SignatureItemRow {
                    ident,
                    declaration,
                    kind,
                    status: if kind == SignatureKind::Module {
                        ItemStatus::Recursive(RecStatus::Not)
                    } else {
                        ItemStatus::Ordinary
                    },
                },
            )
        };
    let ident_type = add(&mut f.module_types, ModuleTypeRow::Ident(u_path));
    module(&mut f, "M", 7, ident_type, SignatureKind::Module);
    let alias = add(
        &mut f.module_types,
        ModuleTypeRow::Alias {
            path: unit.path,
            present: false,
        },
    );
    module(&mut f, "N", 8, alias, SignatureKind::Module);
    let s_signature = add(&mut f.signatures, Range::default());
    let s_type = add(&mut f.module_types, ModuleTypeRow::Signature(s_signature));
    module(&mut f, "S", 9, s_type, SignatureKind::ModuleType);
    let functor_row = f.module_types.len() as u32 + 2;
    let parameter = f.ident("X", 20, FUNCTOR_SCOPE | functor_row);
    let parameter_type = add(&mut f.module_types, ModuleTypeRow::Ident(u_path));
    let f_signature = add(&mut f.signatures, Range::default());
    let result = add(&mut f.module_types, ModuleTypeRow::Signature(f_signature));
    let functor = add(
        &mut f.module_types,
        ModuleTypeRow::Functor {
            parameter,
            parameter_type,
            result,
        },
    );
    module(&mut f, "F", 10, functor, SignatureKind::ModuleType);
    let generative_row = f.module_types.len() as u32 + 1;
    let generative_parameter = f.ident("*", 21, FUNCTOR_SCOPE | generative_row);
    let generative_result = add(&mut f.module_types, ModuleTypeRow::Ident(u_path));
    let generative = add(
        &mut f.module_types,
        ModuleTypeRow::Functor {
            parameter: generative_parameter,
            parameter_type: NONE,
            result: generative_result,
        },
    );
    module(&mut f, "G", 11, generative, SignatureKind::ModuleType);
    module(&mut f, "H", 12, NONE, SignatureKind::ModuleType);
    for kind in [SignatureKind::Class, SignatureKind::ClassType] {
        add(
            &mut f.ordered_items,
            SignatureItemRow {
                ident: NONE,
                declaration: NONE,
                kind,
                status: ItemStatus::Ordinary,
            },
        );
    }
    f.close(0, 0);
    let start = f.ordered_items.len() as u32;
    f.value("s", 13, 8);
    f.close(s_signature, start);
    let start = f.ordered_items.len() as u32;
    f.close(f_signature, start);
    let schemes: [&[Ty]; 6] = [
        &[weak],
        &[weak],
        &[weak, weak],
        &[weak, weak, weak],
        &[weak],
        &[weak],
    ];
    let segment = finish(graph, &schemes, f, unit);
    let (output, visits) = run(&segment);
    assert_eq!(visits.count, 1, "only the shared node; no synthetic tuple");
    assert_eq!(output.unit(), "Test");
    assert_eq!(output.deprecated(), None);
    let w = TypeExprRef::from_usize(0);
    let signature = output.signature();
    assert_eq!(signature.len(), 14);

    let SignatureItem::SigValue(v, v_decl) = &signature[0] else {
        panic!("v");
    };
    assert_eq!((v.name(), v.stamp(), v.flags().bits()), ("v", 1, 0));
    assert!(v_decl.val_path.is_none());
    assert!(matches!(v_decl.val_kind, ValueKind::ValReg));
    assert_eq!(v_decl.val_type, w);
    let SignatureItem::SigValue(_, u_decl) = &signature[1] else {
        panic!("u");
    };
    let u_path = u_decl.val_path.expect("a present path stays present");
    assert_eq!(u_path.name(), "Test.u");
    let crate::types::path::PathView::Pdot(unit_path, _, 1) = *u_path.view() else {
        panic!("Test.u at position 1");
    };
    let head = unit_path.as_pident().expect("the unit");
    assert_eq!(
        (head.stamp(), head.flags().bits()),
        (0, IdentFlags::GLOBAL.bits())
    );

    let SignatureItem::SigType(_, r, OldRecStatus::TrecFirst) = &signature[2] else {
        panic!("r");
    };
    let TypeKind::TypeRecord(labels, RecordRepresentation::RecordRegular) = &r.type_kind else {
        panic!("a regular record");
    };
    assert_eq!(labels.len(), 2);
    assert_eq!(labels[0].ld_id.name(), "x");
    assert_eq!(labels[0].ld_runtime_name.as_deref(), Some("ex"));
    assert_eq!(labels[0].ld_mutable, MutableFlag::Immutable);
    assert_eq!(labels[1].ld_mutable, MutableFlag::Mutable);
    assert!(labels[1].ld_optional && !labels[0].ld_optional);
    assert!(labels.iter().all(|label| label.ld_type == w));
    assert!(r.type_path.is_none() && r.type_manifest.is_none());
    assert_eq!(r.type_private, PrivateFlag::Public);

    let SignatureItem::SigType(_, c, OldRecStatus::TrecNext) = &signature[3] else {
        panic!("c");
    };
    let TypeKind::TypeVariant(constructors, layout) = &c.type_kind else {
        panic!("a variant");
    };
    assert_eq!(*layout, LayoutRef::from_usize(0));
    assert_eq!(constructors[0].cd_id.name(), "A");
    assert_eq!(constructors[0].cd_runtime_tag, Some(LiteralTag::Int(1)));
    assert!(
        matches!(&constructors[0].cd_args, ConstructorArguments::CstrTuple(args) if args.is_empty())
    );
    assert!(constructors[0].cd_res.is_none());
    assert!(
        matches!(&constructors[1].cd_args, ConstructorArguments::CstrTuple(args) if args == &[w])
    );
    assert_eq!(constructors[1].cd_res, Some(w));
    assert_eq!(c.type_private, PrivateFlag::Private);
    assert!(c.type_immediate);
    assert_eq!(c.type_representation, TypeRepresentation::Unboxed);
    assert_eq!(c.type_newtype_level, Some((2, -1)));
    let [TypeInlinedType::Record { type_name, labels }] = &c.type_inlined_types[..] else {
        panic!("one inlined record");
    };
    assert_eq!(type_name, "c.B");
    assert_eq!(labels[0].ld_type, w);

    let SignatureItem::SigType(_, o, OldRecStatus::TrecNot) = &signature[4] else {
        panic!("o");
    };
    assert!(matches!(o.type_kind, TypeKind::TypeOpen));
    assert_eq!(o.type_representation, TypeRepresentation::Boxed);
    assert!(o.type_newtype_level.is_none());

    let SignatureItem::SigTypext(e, ext, ExtStatus::TextException) = &signature[5] else {
        panic!("E");
    };
    assert_eq!(e.stamp(), 6);
    assert_eq!(ext.ext_type_path.name(), "exn");
    assert!(ext.ext_is_exception);
    assert_eq!(ext.ext_private, PrivateFlag::Private);
    assert!(ext.ext_ret_type.is_none());
    assert!(
        matches!(&ext.ext_args, ConstructorArguments::CstrRecord(labels) if labels[0].ld_type == w)
    );

    let SignatureItem::SigModule(_, m, OldRecStatus::TrecNot) = &signature[6] else {
        panic!("M");
    };
    assert!(m.md_path.is_none());
    assert!(matches!(&m.md_type, ModuleType::MtyIdent(path) if *path == u_path));
    let SignatureItem::SigModule(_, n, _) = &signature[7] else {
        panic!("N");
    };
    assert!(matches!(
        &n.md_type,
        ModuleType::MtyAlias(AliasPresence::MtaAbsent, path) if **path == unit_path
    ));
    let SignatureItem::SigModtype(_, s) = &signature[8] else {
        panic!("S");
    };
    let Some(ModuleType::MtySignature(inner)) = &s.mtd_type else {
        panic!("a signature");
    };
    assert!(matches!(&inner[..], [SignatureItem::SigValue(id, _)] if id.name() == "s"));
    let SignatureItem::SigModtype(_, functor) = &signature[9] else {
        panic!("F");
    };
    let Some(ModuleType::MtyFunctor {
        param,
        param_type: Some(param_type),
        result,
    }) = &functor.mtd_type
    else {
        panic!("an applicative functor");
    };
    assert_eq!((param.name(), param.stamp()), ("X", 20));
    assert!(matches!(&**param_type, ModuleType::MtyIdent(_)));
    assert!(matches!(&**result, ModuleType::MtySignature(inner) if inner.is_empty()));
    let SignatureItem::SigModtype(_, generative) = &signature[10] else {
        panic!("G");
    };
    assert!(matches!(
        &generative.mtd_type,
        Some(ModuleType::MtyFunctor {
            param_type: None,
            ..
        })
    ));
    let SignatureItem::SigModtype(_, abstract_type) = &signature[11] else {
        panic!("H");
    };
    assert!(abstract_type.mtd_type.is_none());
    assert!(matches!(signature[12], SignatureItem::SigClass));
    assert!(matches!(signature[13], SignatureItem::SigClassType));
}

#[test]
fn publication_into_a_pool_interns_components_once() {
    let mut f = Fixture::default();
    let unit = f.unit();
    let m = f.string("M");
    let lid_m = add(&mut f.longidents, LongidentRow::Ident(m));
    let lid_mm = add(
        &mut f.longidents,
        LongidentRow::Dot {
            parent: lid_m,
            name: m,
        },
    );
    let lids = f.indices.len() as u32;
    f.indices.push(lid_mm);
    let package = add(
        &mut f.packages,
        PackageRow {
            path: unit.path,
            longidents: Range {
                start: lids,
                len: 1,
            },
            arguments: Range::default(),
        },
    );
    let package = add(&mut f.descriptor_extras, ExtraDescriptor::Package(package));
    let mut graph = Graph::default();
    let root = extended(&mut graph, 1, package, &[]);
    f.value("p", 1, 0);
    f.close(0, 0);
    let segment = finish(graph, &[&[root]], f, unit);
    let pool = SharedTypePool::new();
    let output = to_old(&segment);
    {
        let names = output.published.names.read().unwrap();
        assert_eq!(names.len(), 1);
        assert_eq!(names[&0].as_str(), "M");
    }
    let published = output.into_pool(&pool);
    assert!(std::ptr::eq(published.names.as_ref(), pool.names_ref()));
    let TypeDesc::Tpackage { lids, .. } = published.graph.nodes()[0].desc else {
        panic!("a package");
    };
    let [Longident::Ldot(prefix, last)] = published.graph.lids(lids) else {
        panic!("M.M");
    };
    let Longident::Lident(first) = **prefix else {
        panic!("M");
    };
    assert_eq!(first, *last, "one pool name per distinct component");
    assert_eq!(pool.longident_name(first).as_deref(), Some("M"));
}
