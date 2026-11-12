//! Direct publication sink. The checker is visited once; dense scratch indices
//! are relocated while freezing the arrays after their sizes are known.
use super::*;
use crate::types::shared_store::{SharedGraphParts, SharedGraphPayloads};
use crate::types::type_expr::{
    PackageLidsRef, RowDescRef, SHARED_REF_BITS, TypeArgList, TypeRefList,
};

#[derive(Default)]
struct DirectSink {
    nodes: Vec<(TypeDesc, i32)>,
    payloads: SharedGraphPayloads,
    cells: Vec<MutabilityRef>,
    nonshareable: bool,
}

impl DirectSink {
    fn list(&mut self, items: &[TypeExprRef]) -> TypeRefList {
        let start = self.payloads.lists.len();
        self.payloads.lists.extend_from_slice(items);
        TypeRefList::from_parts(start as u32, items.len())
    }
    fn args(&mut self, args: &[TypeArg]) -> TypeArgList {
        let start = self.payloads.args.len();
        self.payloads.args.extend_from_slice(args);
        TypeArgList::from_parts(start as u32, args.len())
    }
}

impl SignatureSink for DirectSink {
    type Desc = TypeDesc;
    fn reserve(&mut self) -> usize {
        let index = self.nodes.len();
        self.nodes.push((TypeDesc::Tnil, 0));
        index
    }
    fn write(&mut self, index: usize, desc: TypeDesc, level: i32) {
        self.nonshareable |= matches!(desc, TypeDesc::Tsubst(_));
        self.nodes[index] = (desc, level);
    }
    fn describe(ser: &mut TypeGraphSerializer<'_, '_, Self>, desc: &TypeDesc) -> TypeDesc {
        fn ty(ser: &mut TypeGraphSerializer<'_, '_, DirectSink>, r: TypeExprRef) -> TypeExprRef {
            TypeExprRef::from_usize(ser.serialize_type(r))
        }
        fn list(
            ser: &mut TypeGraphSerializer<'_, '_, DirectSink>,
            xs: impl Iterator<Item = TypeExprRef>,
        ) -> TypeRefList {
            let xs: crate::types::type_expr::TypeRefs = xs.map(|r| ty(ser, r)).collect();
            ser.sink.list(&xs)
        }
        fn lid(ser: &TypeGraphSerializer<'_, '_, DirectSink>, l: &Longident) -> Longident {
            let name = |idx| {
                ser.ctx
                    .thread_store()
                    .shared_pool()
                    .intern_longident_name(&ser.resolve_longident_component(idx))
            };
            match l {
                Longident::Lident(n) => Longident::Lident(name(*n)),
                Longident::Ldot(p, n) => Longident::Ldot(Box::new(lid(ser, p)), name(*n)),
                Longident::Lapply(f, a) => {
                    Longident::Lapply(Box::new(lid(ser, f)), Box::new(lid(ser, a)))
                }
            }
        }
        match desc {
            TypeDesc::Tvar(n) => TypeDesc::Tvar(*n),
            TypeDesc::Tunivar(n) => TypeDesc::Tunivar(*n),
            TypeDesc::Tnil => TypeDesc::Tnil,
            TypeDesc::Tarrow { args, ret } => {
                let args: crate::types::type_expr::TypeArgs = ser
                    .ctx
                    .type_args(args)
                    .iter()
                    .map(|a| {
                        let label = ser.portable_label(&a.label().to_arg_label());
                        TypeArg::new(label, ty(ser, a.typ))
                    })
                    .collect();
                let ret = ty(ser, *ret);
                TypeDesc::Tarrow {
                    args: ser.sink.args(&args),
                    ret,
                }
            }
            TypeDesc::Ttuple(xs) => TypeDesc::Ttuple(list(ser, ser.ctx.type_list(xs).iter())),
            TypeDesc::Tconstr { path, args, .. } => TypeDesc::Tconstr {
                path: *path,
                args: list(ser, ser.ctx.type_list(args).iter()),
                abbrev: AbbrevMemoRef::nil(),
            },
            TypeDesc::Tobject { fields } => TypeDesc::Tobject {
                fields: ty(ser, *fields),
            },
            TypeDesc::Tfield {
                name,
                mutability,
                typ,
                rest,
            } => {
                let index = ser.serialize_mutability(*mutability);
                if index == ser.sink.cells.len() {
                    ser.sink
                        .cells
                        .push(MutabilityRef::new_persistent(ser.mutabilities[index]));
                }
                let mutability = ser.sink.cells[index];
                TypeDesc::Tfield {
                    name: *name,
                    mutability,
                    typ: ty(ser, *typ),
                    rest: ty(ser, *rest),
                }
            }
            TypeDesc::Tlink(r) => TypeDesc::Tlink(ty(ser, *r)),
            TypeDesc::Tsubst(r) => TypeDesc::Tsubst(ty(ser, *r)),
            TypeDesc::Tpoly { body, vars } => TypeDesc::Tpoly {
                body: ty(ser, *body),
                vars: list(ser, ser.ctx.type_list(vars).iter()),
            },
            TypeDesc::Tpackage { path, lids, args } => {
                let lids = ser
                    .ctx
                    .package_lids(lids)
                    .iter()
                    .map(|l| lid(ser, l))
                    .collect();
                let args = list(ser, ser.ctx.type_list(args).iter());
                let index = ser.sink.payloads.lids.len();
                ser.sink.payloads.lids.push(lids);
                TypeDesc::Tpackage {
                    path: *path,
                    lids: PackageLidsRef::from_raw(index as u32),
                    args,
                }
            }
            TypeDesc::Tvariant(r) => {
                let row = ser.ctx.row_desc(r);
                let fields = row
                    .row_fields
                    .iter()
                    .map(|(label, field)| {
                        let field = match field {
                            RowField::Rpresent(r) => RowField::Rpresent(r.map(|r| ty(ser, r))),
                            RowField::Reither {
                                constant,
                                types,
                                matched,
                                ..
                            } => RowField::Reither {
                                constant: *constant,
                                types: types.iter().map(|r| ty(ser, *r)).collect(),
                                matched: *matched,
                                link: RowFieldRef::null(),
                            },
                            RowField::Rabsent => RowField::Rabsent,
                        };
                        (label.clone(), field)
                    })
                    .collect();
                let row_more = ty(ser, row.row_more);
                let row_name = row
                    .row_name
                    .as_ref()
                    .map(|(p, xs)| (*p, xs.iter().map(|r| ty(ser, *r)).collect()));
                let index = ser.sink.payloads.rows.len();
                ser.sink.payloads.rows.push(RowDesc {
                    row_fields: fields,
                    row_more,
                    row_closed: row.row_closed,
                    row_fixed: row.row_fixed,
                    row_name,
                });
                TypeDesc::Tvariant(RowDescRef::from_raw(index as u32))
            }
        }
    }
}

/// Build a graph and raw signature while the producer context is alive. No
/// PortableTypeEntry is created for the main signature. None selects the old
/// non-shareable/full-pool fallback before anything is exposed to dependents.
pub(super) fn build(
    ps: &PersStruct,
    ctx: &TypeContext,
    arena: Option<&ParseArena>,
) -> Option<(
    super::super::shared_reader::PublishedGraph,
    Option<PortableRawSignature>,
)> {
    let mut files = PortableFileNames::default();
    let mut ser = TypeGraphSerializer::<DirectSink>::new(ctx, arena, &mut files);
    let mut sig = ps.ps_sig.as_ref().clone();
    ser.remap_signature(&mut sig);
    ser.remap_signature_locations(&mut sig);
    if ser.sink.nonshareable {
        crate::perf_counters::record_signature_fallback(false);
        return None;
    }
    let mut sink = ser.sink;
    let locations = ser.locations;
    let layouts = ser.variant_layouts;
    let raw = ctx
        .find_raw_module_sig(&ps.ps_name)
        .map(|sig| serialize_signature(&sig, ctx, arena, &mut files));
    let mut raw = raw.map(
        |(raw_ps_sig, raw_type_graph, raw_locations)| PortableRawSignature {
            raw_ps_sig,
            raw_type_graph,
            raw_locations,
            cmi_longident_names: files.names.clone(),
        },
    );
    if ctx.has_saved_store_stamps() {
        let stamps = std::cell::OnceCell::new();
        let saved = |stamp| {
            stamps
                .get_or_init(|| ctx.saved_store_stamps())
                .get(&stamp)
                .copied()
        };
        remap_saved_stamps(
            &mut sig,
            &mut PortableTypeGraph {
                entries: vec![],
                variant_layouts: vec![],
                mutabilities: vec![],
            },
            &saved,
        );
        for (desc, _) in &mut sink.nodes {
            match desc {
                TypeDesc::Tconstr { path, .. } | TypeDesc::Tpackage { path, .. } => {
                    remap_saved_path(path, &saved)
                }
                _ => {}
            }
        }
        for row in &mut sink.payloads.rows {
            if let Some((path, _)) = &mut row.row_name {
                remap_saved_path(path, &saved);
            }
        }
        if let Some(raw) = &mut raw {
            remap_saved_stamps(&mut raw.raw_ps_sig, &mut raw.raw_type_graph, &saved);
        }
    }
    let graph = crate::types::shared_store::SharedGraph::detached(SharedGraphParts {
        nodes: sink.nodes, payloads: sink.payloads, layouts, locations,
        carried: super::super::shared_reader::Carried {
            file_names: files.names, ..Default::default()
        },
    });
    Some((super::super::shared_reader::PublishedGraph {
        graph: Arc::new(graph), signature: Arc::new(sig),
        names: ctx.thread_store().shared_pool().names(),
    }, raw))
}

/// Called under the pool's per-publication OnceLock, only by an importer.
/// No checker traversal or portable intermediate is needed here.
pub(super) fn promote(
    source: &mut super::super::shared_reader::PublishedGraph,
    filename: &str,
    pool: &crate::types::shared_store::SharedTypePool,
) -> Option<super::super::shared_reader::PublishedGraph> {
    assert!(source.graph.is_detached());
    let sizes = source.graph.sizes();
    let mut sig = Vec::new();
    // Reserve first: pool exhaustion leaves the detached source intact for
    // the private fallback. The normal source is owned only by this slot.
    let base = pool.publish(sizes, |base| {
        let parts = match Arc::get_mut(&mut source.graph) {
            Some(graph) => graph.take_parts(),
            None => source.graph.copy_parts(),
        };
        let mut sink = DirectSink {
            nodes: parts.nodes,
            payloads: parts.payloads,
            ..Default::default()
        };
        let mut locations = parts.locations;
        let mut layouts = parts.layouts;
        sig = std::mem::take(Arc::make_mut(&mut source.signature));
        let intern = |name: &str| pool.intern_longident_name(name);
        let files = FileRemap::new(&parts.carried.file_names, &intern);
        let map_file = |file| files.map(file);
        let namespace = interface_namespace(filename);
        let scopes = locations.remap_for_import_with(&map_file, |scope| {
            crate::types::variant_runtime::identity_in_namespace(namespace, scope)
        });
        let mut shapes =
            crate::types::variant_runtime::ShapeImport::with_namespace(&scopes, Some(namespace));
        for layout in &mut layouts {
            shapes.layout(layout);
        }
        shapes.signature(&mut sig);
        let mut carried = super::super::shared_reader::Carried {
            file_names: files.original.to_vec(),
            ..Default::default()
        };
        carried.record_maps(&scopes, shapes);
        // Relocation is a flat pass over arrays, not another checker walk.
        let ty = |r: &mut TypeExprRef| *r = crate::types::shared_store::shared_ref(base, r.index());
        let list = |xs: &mut TypeRefList| {
            *xs = TypeRefList::from_parts(
                SHARED_REF_BITS | (base + sizes.lists_start() as u32 + xs.raw_start()),
                xs.len(),
            )
        };
        let locs = shared_decl_locs(base, &map_file);
        for (i, (desc, level)) in sink.nodes.iter_mut().enumerate() {
            match desc {
                TypeDesc::Tarrow { args, ret } => {
                    *args = TypeArgList::from_parts(
                        SHARED_REF_BITS | (base + sizes.args_start() as u32 + args.raw_start()),
                        args.len(),
                    );
                    ty(ret);
                }
                TypeDesc::Ttuple(xs) => list(xs),
                TypeDesc::Tconstr { args, abbrev, .. } => {
                    list(args);
                    *abbrev = AbbrevMemoRef::from_shared_index(base + i as u32);
                }
                TypeDesc::Tobject { fields } => ty(fields),
                TypeDesc::Tfield { typ, rest, .. } => {
                    ty(typ);
                    ty(rest);
                }
                TypeDesc::Tlink(r) => {
                    ty(r);
                    if *level != GENERIC_LEVEL {
                        carried.link_levels.push((i as u32, *level));
                    }
                    *level = GENERIC_LEVEL;
                }
                TypeDesc::Tsubst(r) => ty(r),
                TypeDesc::Tvariant(row) => {
                    *row = RowDescRef::from_raw(
                        SHARED_REF_BITS | (base + sizes.rows_start() as u32 + row.raw()),
                    )
                }
                TypeDesc::Tpoly { body, vars } => {
                    ty(body);
                    list(vars);
                }
                TypeDesc::Tpackage { lids, args, .. } => {
                    *lids = PackageLidsRef::from_raw(
                        SHARED_REF_BITS | (base + sizes.lids_start() as u32 + lids.raw()),
                    );
                    list(args);
                }
                TypeDesc::Tvar(_) | TypeDesc::Tunivar(_) | TypeDesc::Tnil => {}
            }
        }
        for r in &mut sink.payloads.lists {
            ty(r);
        }
        for arg in &mut sink.payloads.args {
            *arg = TypeArg::new(
                import_label(&arg.label().to_arg_label(), &locs),
                crate::types::shared_store::shared_ref(base, arg.typ.index()),
            );
        }
        for row in &mut sink.payloads.rows {
            ty(&mut row.row_more);
            for (_, field) in &mut row.row_fields {
                match field {
                    RowField::Rpresent(Some(r)) => ty(r),
                    RowField::Reither { types, .. } => {
                        for r in types {
                            ty(r);
                        }
                    }
                    RowField::Rpresent(None) | RowField::Rabsent => {}
                }
            }
            if let Some((_, args)) = &mut row.row_name {
                for r in args {
                    ty(r);
                }
            }
        }
        struct Refs(u32);
        impl SignatureRefMap for Refs {
            fn ty(&self, r: TypeExprRef) -> TypeExprRef {
                crate::types::shared_store::shared_ref(self.0, r.index())
            }
            fn layout(&self, r: crate::types::VariantLayoutRef) -> crate::types::VariantLayoutRef {
                crate::types::VariantLayoutRef::from_shared_index(self.0 + r.0)
            }
        }
        remap_signature_refs(&mut sig, &Refs(base));
        import_signature_locations(&mut sig, &locs);
        SharedGraphParts {
            nodes: sink.nodes,
            payloads: sink.payloads,
            layouts,
            locations,
            carried,
        }
    });
    let Some(base) = base else {
        crate::perf_counters::record_signature_fallback(true);
        return None;
    };
    Some(super::super::shared_reader::PublishedGraph {
        graph: crate::types::shared_store::graph_at(&pool.pages(), base).clone(),
        signature: Arc::new(sig),
        names: pool.names(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn direct_walk_visits_each_source_node_once() {
        // The existing serializer is recursive. Use the same large-stack
        // convention as the compiler's deep type fixtures; count source reads,
        // not just the number of records left in the sink.
        std::thread::Builder::new()
            .stack_size(64 * 1024 * 1024)
            .spawn(|| {
                const N: usize = 10_000;
                let ctx = TypeContext::new(Arc::new(crate::context::IdGenerator::new()));
                let leaf = ctx.new_type(TypeDesc::Tnil);
                let mut chain = leaf;
                for _ in 1..N {
                    chain = ctx.new_type(TypeDesc::Ttuple(ctx.new_type_list(&[chain])));
                }
                let parents: Vec<_> = (0..N)
                    .map(|_| ctx.new_type(TypeDesc::Ttuple(ctx.new_type_list(&[leaf]))))
                    .collect();
                let root = ctx.new_type(TypeDesc::Ttuple(ctx.new_type_list(&parents)));
                for (root, expected) in [(chain, N), (root, N + 2)] {
                    let mut files = PortableFileNames::default();
                    let mut ser = TypeGraphSerializer::<DirectSink>::new(&ctx, None, &mut files);
                    ser.serialize_type(root);
                    assert_eq!(ser.visits, expected);
                    ser.serialize_type(root);
                    assert_eq!(ser.visits, expected);
                    assert_eq!(ser.sink.nodes.len(), expected);
                }
            })
            .unwrap()
            .join()
            .unwrap();
    }
}
