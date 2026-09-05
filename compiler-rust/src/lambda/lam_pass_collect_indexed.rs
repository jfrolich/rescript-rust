//! Indexed counterpart of `lam_pass_collect`.
//!
//! This module is intentionally not wired into production yet. It exercises
//! the real collect/arity algorithm against [`IndexedLambda`] while keeping
//! Lambda-bearing metadata as owner-bound [`NodeId`] values.

use ahash::{AHashMap, AHashSet};

use crate::ident::Ident;
use crate::lambda::indexed::{IndexedLambda, NodeId, NodeView};
use crate::lambda::lam_analysis::SMALL_INLINE_SIZE;
use crate::lambda::lam_arity::Arity;
use crate::lambda::lam_compat::FieldDbgInfo;
use crate::lambda::lam_compile_context::{
    BoxedNullable, ExternalArityFieldTable, ExternalArityInfo, ExternalArityTable, RecFlag,
};
use crate::lambda::lam_constant::Constant;
use crate::lambda::lam_pass_collect::ExternalArityResolver;
use crate::lambda::lam_primitive::{Mutable, Primitive};
use crate::lambda::{InlineAttribute, Lambda};

#[derive(Debug, Clone)]
pub enum IndexedElement {
    Na,
    SimpleForm(NodeId),
}

#[derive(Debug, Clone)]
pub enum IndexedIdKind {
    NormalOptional(NodeId),
    OptionalBlock(NodeId, BoxedNullable),
    ImmutableBlock(Vec<IndexedElement>),
    MutableBlock(Vec<IndexedElement>),
    Constant(Constant),
    Module(Ident),
    FunctionId {
        arity: Arity,
        lambda: Option<(NodeId, RecFlag)>,
    },
    Exception,
    Parameter,
    Na,
}

/// Collect metadata cannot outlive or be interpreted without its arena.
pub struct IndexedLamStats<'arena> {
    arena: &'arena IndexedLambda,
    pub export_idents: AHashSet<Ident>,
    pub ident_tbl: AHashMap<Ident, IndexedIdKind>,
    pub external_arities: ExternalArityTable,
    #[cfg(test)]
    visited: Vec<NodeId>,
}

impl<'arena> IndexedLamStats<'arena> {
    pub fn new(arena: &'arena IndexedLambda, exports: impl IntoIterator<Item = Ident>) -> Self {
        Self {
            arena,
            export_idents: exports.into_iter().collect(),
            ident_tbl: AHashMap::new(),
            external_arities: ExternalArityTable::default(),
            #[cfg(test)]
            visited: vec![],
        }
    }

    pub fn arena(&self) -> &'arena IndexedLambda {
        self.arena
    }
}

fn element_of_node(arena: &IndexedLambda, node: NodeId) -> IndexedElement {
    match arena.view(node) {
        NodeView::Var(_) | NodeView::Const(_) => IndexedElement::SimpleForm(node),
        NodeView::Prim(Primitive::Pfield(_, FieldDbgInfo::Module { .. }), [base], _)
            if matches!(
                arena.view(*base),
                NodeView::GlobalModule(_, _) | NodeView::Var(_)
            ) =>
        {
            IndexedElement::SimpleForm(node)
        }
        _ => IndexedElement::Na,
    }
}

fn kind_of_block(arena: &IndexedLambda, args: &[NodeId]) -> IndexedIdKind {
    IndexedIdKind::ImmutableBlock(
        args.iter()
            .map(|node| element_of_node(arena, *node))
            .collect(),
    )
}

fn alias_ident_or_global(
    meta: &mut IndexedLamStats<'_>,
    target: Ident,
    source: &Ident,
    source_kind: IndexedIdKind,
) {
    match source_kind {
        IndexedIdKind::Na => {
            if let Some(kind) = meta.ident_tbl.get(source).cloned() {
                meta.ident_tbl.insert(target, kind);
            }
        }
        kind => {
            meta.ident_tbl.insert(target, kind);
        }
    }
}

fn arity_of_var(table: &AHashMap<Ident, IndexedIdKind>, id: &Ident) -> Arity {
    match table.get(id) {
        Some(IndexedIdKind::FunctionId { arity, .. }) => arity.clone(),
        _ => Arity::na(),
    }
}

fn external_modules_mut(
    table: &mut ExternalArityTable,
    dynamic: bool,
) -> &mut AHashMap<String, ExternalArityFieldTable> {
    if dynamic {
        &mut table.dynamic_imports
    } else {
        &mut table.static_imports
    }
}

fn lookup_external(
    table: &mut ExternalArityTable,
    module: &Ident,
    dynamic: bool,
    field: &str,
    resolver: &mut ExternalArityResolver<'_>,
) -> Option<ExternalArityInfo> {
    let modules = if dynamic {
        &table.dynamic_imports
    } else {
        &table.static_imports
    };
    if let Some(cached) = modules
        .get(module.name())
        .and_then(|fields| fields.get(field))
    {
        return cached.clone();
    }
    let resolved = resolver(module, dynamic, field);
    external_modules_mut(table, dynamic)
        .entry(module.name().to_string())
        .or_default()
        .insert(field.to_string(), resolved.clone());
    resolved
}

fn cached_external(
    table: &ExternalArityTable,
    module: &Ident,
    dynamic: bool,
    field: &str,
) -> Option<ExternalArityInfo> {
    let modules = if dynamic {
        &table.dynamic_imports
    } else {
        &table.static_imports
    };
    modules
        .get(module.name())
        .and_then(|fields| fields.get(field))
        .and_then(Clone::clone)
}

fn all_arities<F>(
    arena: &IndexedLambda,
    table: &AHashMap<Ident, IndexedIdKind>,
    nodes: impl IntoIterator<Item = NodeId>,
    lookup: &mut F,
) -> Arity
where
    F: FnMut(&Ident, bool, &str) -> Option<ExternalArityInfo>,
{
    let mut nodes = nodes.into_iter();
    let Some(first) = nodes.next() else {
        return Arity::na();
    };
    let mut acc = get_arity_impl(arena, table, first, lookup);
    for node in nodes {
        let Arity::Info { arities, variadic } = acc else {
            return Arity::na();
        };
        let Arity::Info {
            arities: other,
            variadic: other_variadic,
        } = get_arity_impl(arena, table, node, lookup)
        else {
            return Arity::na();
        };
        acc = Arity::merge_arities(&arities, &other, variadic, other_variadic);
    }
    acc
}

fn get_arity_impl<F>(
    arena: &IndexedLambda,
    table: &AHashMap<Ident, IndexedIdKind>,
    node: NodeId,
    lookup: &mut F,
) -> Arity
where
    F: FnMut(&Ident, bool, &str) -> Option<ExternalArityInfo>,
{
    match arena.view(node) {
        NodeView::Var(id) => arity_of_var(table, id),
        NodeView::Const(_) => Arity::non_function(),
        NodeView::Let(_, _, _, body) | NodeView::LetRec(_, body) => {
            get_arity_impl(arena, table, body, lookup)
        }
        NodeView::Prim(Primitive::Pfield(_, FieldDbgInfo::Module { name }), [base], _) => {
            if let NodeView::GlobalModule(module, dynamic) = arena.view(*base) {
                return match lookup(module, dynamic, name) {
                    Some(ExternalArityInfo::Single(arity)) => arity,
                    _ => Arity::na(),
                };
            }
            Arity::na()
        }
        NodeView::Prim(Primitive::Pfield(index, _), [inner], _) => {
            if let NodeView::Prim(Primitive::Pfield(_, FieldDbgInfo::Module { name }), [base], _) =
                arena.view(*inner)
                && let NodeView::GlobalModule(module, dynamic) = arena.view(*base)
            {
                return match lookup(module, dynamic, name) {
                    Some(ExternalArityInfo::Submodule(arities)) => arities
                        .get(*index as usize)
                        .cloned()
                        .unwrap_or_else(Arity::na),
                    _ => Arity::na(),
                };
            }
            Arity::na()
        }
        NodeView::Prim(Primitive::Praise, _, _) => Arity::raise(),
        NodeView::GlobalModule(_, _) | NodeView::Prim(_, _, _) => Arity::na(),
        NodeView::Apply(function, args, _, _) => {
            match get_arity_impl(arena, table, function, lookup) {
                Arity::Na => Arity::na(),
                Arity::Info {
                    mut arities,
                    variadic,
                } => {
                    let mut remaining = args.len() as i32;
                    loop {
                        match arities.first().copied() {
                            Some(head) if remaining == head => {
                                arities.remove(0);
                                return Arity::info(arities, variadic);
                            }
                            Some(head) if remaining > head => {
                                arities.remove(0);
                                remaining -= head;
                            }
                            Some(head) => {
                                arities[0] = head - remaining;
                                return Arity::info(arities, variadic);
                            }
                            None => {
                                return if variadic {
                                    Arity::raise()
                                } else {
                                    Arity::na()
                                };
                            }
                        }
                    }
                }
            }
        }
        NodeView::Function(arity, _, body, _) => {
            get_arity_impl(arena, table, body, lookup).merge(arity)
        }
        NodeView::Switch {
            consts,
            blocks,
            fail_action,
            ..
        } => {
            let nodes = fail_action
                .into_iter()
                .chain(consts.iter().map(|(_, node)| *node))
                .chain(blocks.iter().map(|(_, node)| *node));
            all_arities(arena, table, nodes, lookup)
        }
        NodeView::StringSwitch(_, cases, default) => {
            let nodes = default
                .into_iter()
                .chain(cases.iter().map(|(_, node)| *node));
            all_arities(arena, table, nodes, lookup)
        }
        NodeView::StaticCatch(_, _, _, handler) => get_arity_impl(arena, table, handler, lookup),
        NodeView::TryWith(body, _, handler) => all_arities(arena, table, [body, handler], lookup),
        NodeView::IfThenElse(_, then_node, else_node) => {
            all_arities(arena, table, [then_node, else_node], lookup)
        }
        NodeView::Sequence(_, second) => get_arity_impl(arena, table, second, lookup),
        NodeView::StaticRaise(_, _) => Arity::na(),
        NodeView::While(_, _)
        | NodeView::For(_, _, _, _, _)
        | NodeView::ForOf(_, _, _)
        | NodeView::ForAwaitOf(_, _, _)
        | NodeView::Break
        | NodeView::Continue
        | NodeView::Assign(_, _) => Arity::non_function(),
    }
}

pub fn get_arity(meta: &IndexedLamStats<'_>, node: NodeId) -> Arity {
    let mut lookup = |module: &Ident, dynamic: bool, field: &str| {
        cached_external(&meta.external_arities, module, dynamic, field)
    };
    get_arity_impl(meta.arena, &meta.ident_tbl, node, &mut lookup)
}

fn get_arity_external(
    meta: &mut IndexedLamStats<'_>,
    node: NodeId,
    resolver: &mut ExternalArityResolver<'_>,
) -> Arity {
    let arena = meta.arena;
    let table = &meta.ident_tbl;
    let external = &mut meta.external_arities;
    let mut lookup = |module: &Ident, dynamic: bool, field: &str| {
        lookup_external(external, module, dynamic, field, resolver)
    };
    get_arity_impl(arena, table, node, &mut lookup)
}

fn indexed_size(arena: &IndexedLambda, node: NodeId) -> i32 {
    const TOO_BIG: i32 = 1000;
    fn constant_size(constant: &Constant) -> i32 {
        match constant {
            Constant::Some(inner) => constant_size(inner),
            Constant::Block {
                tag_info, elements, ..
            } => {
                let missing = match tag_info {
                    crate::lambda::TagInfo::Record { .. }
                    | crate::lambda::TagInfo::RecordInlined { .. } => tag_info
                        .logical_field_count()
                        .saturating_sub(elements.len()),
                    _ => 0,
                };
                missing as i32 + elements.iter().map(constant_size).sum::<i32>()
            }
            _ => 1,
        }
    }
    fn nodes_size(arena: &IndexedLambda, initial: i32, nodes: &[NodeId]) -> Option<i32> {
        let mut total = initial;
        for node in nodes {
            total += inner(arena, *node)?;
        }
        Some(total)
    }
    fn inner(arena: &IndexedLambda, node: NodeId) -> Option<i32> {
        match arena.view(node) {
            NodeView::Var(_)
            | NodeView::GlobalModule(_, _)
            | NodeView::Break
            | NodeView::Continue => Some(1),
            NodeView::Const(constant) => Some(constant_size(constant)),
            NodeView::Let(_, _, value, body) => {
                Some(1 + inner(arena, value)? + inner(arena, body)?)
            }
            NodeView::LetRec(_, _) => None,
            NodeView::Prim(primitive, args, _) => {
                match primitive {
                    Primitive::Pfield(_, FieldDbgInfo::Module { .. }) if matches!(args, [base] if matches!(arena.view(*base), NodeView::GlobalModule(_, _) | NodeView::Var(_))) =>
                    {
                        return Some(1);
                    }
                    Primitive::Praise | Primitive::PisNotNone if args.len() == 1 => {
                        return inner(arena, args[0]);
                    }
                    Primitive::Pmakeblock(
                        tag @ (crate::lambda::TagInfo::Record { .. }
                        | crate::lambda::TagInfo::RecordInlined { .. }),
                        _,
                    ) => {
                        return nodes_size(
                            arena,
                            1 + tag.logical_field_count().saturating_sub(args.len()) as i32,
                            args,
                        );
                    }
                    Primitive::PjsObjectCreate(params) => {
                        let logical = params
                            .iter()
                            .filter(|param| {
                                !matches!(
                                    param.obj_arg_type,
                                    crate::lambda::lam_primitive::ExternalArgAttr::ArgCst(_)
                                )
                            })
                            .count();
                        return nodes_size(
                            arena,
                            1 + logical.saturating_sub(args.len()) as i32,
                            args,
                        );
                    }
                    Primitive::PrawJsCode(_) => return None,
                    _ => {}
                }
                nodes_size(arena, 1, args)
            }
            NodeView::Apply(function, args, _, _) => {
                nodes_size(arena, inner(arena, function)?, args)
            }
            NodeView::Function(_, _, body, _) => inner(arena, body),
            NodeView::StaticRaise(_, args) => nodes_size(arena, 1, args),
            NodeView::IfThenElse(a, b, c) => {
                Some(1 + inner(arena, a)? + inner(arena, b)? + inner(arena, c)?)
            }
            NodeView::Sequence(a, b) => Some(inner(arena, a)? + inner(arena, b)?),
            NodeView::Assign(_, value) => Some(1 + inner(arena, value)?),
            NodeView::Switch { .. }
            | NodeView::StringSwitch(_, _, _)
            | NodeView::StaticCatch(_, _, _, _)
            | NodeView::TryWith(_, _, _)
            | NodeView::While(_, _)
            | NodeView::For(_, _, _, _, _)
            | NodeView::ForOf(_, _, _)
            | NodeView::ForAwaitOf(_, _, _) => None,
        }
    }
    inner(arena, node).unwrap_or(TOO_BIG)
}

fn indexed_no_side_effects(arena: &IndexedLambda, node: NodeId) -> bool {
    fn not_zero(arena: &IndexedLambda, node: NodeId) -> bool {
        matches!(arena.view(node), NodeView::Const(Constant::Int { i, .. }) if *i != 0)
            || matches!(arena.view(node), NodeView::Const(Constant::NativeInt { i, .. }) if *i != 0)
            || matches!(arena.view(node), NodeView::Const(Constant::BigInt { value, .. }) if value != "0")
    }
    fn pure_primitive(primitive: &Primitive, arena: &IndexedLambda, args: &[NodeId]) -> bool {
        match primitive {
            Primitive::Pmodint
            | Primitive::Pdivint
            | Primitive::Pdivbigint
            | Primitive::Pmodbigint => args.get(1).is_some_and(|node| not_zero(arena, *node)),
            Primitive::PtaggedTemplate
            | Primitive::PjsApply
            | Primitive::PjsRuntimeApply
            | Primitive::PjsCall { .. }
            | Primitive::PinitMod
            | Primitive::PupdateMod
            | Primitive::PjsUnsafeDowngrade { .. }
            | Primitive::Pdebugger
            | Primitive::PjsFnMethod
            | Primitive::Pawait
            | Primitive::Parraysets
            | Primitive::Parraysetu
            | Primitive::Poffsetref(_)
            | Primitive::Praise
            | Primitive::Psetfield(_, _) => false,
            Primitive::PrawJsCode(info) => {
                use crate::binary_ast::ppx::{
                    JsExpClassification, JsStmtClassification, classify_js_exp, classify_js_stmt,
                };
                if info.is_stmt {
                    matches!(
                        classify_js_stmt(&info.code),
                        JsStmtClassification::JsStmtComment
                    )
                } else {
                    matches!(
                        classify_js_exp(&info.code),
                        JsExpClassification::JsFunction { .. }
                            | JsExpClassification::JsLiteral { .. }
                    )
                }
            }
            _ => true,
        }
    }
    match arena.view(node) {
        NodeView::Var(_)
        | NodeView::Const(_)
        | NodeView::Function(_, _, _, _)
        | NodeView::GlobalModule(_, _) => true,
        NodeView::Prim(primitive, args, _) => {
            args.iter()
                .all(|node| indexed_no_side_effects(arena, *node))
                && pure_primitive(primitive, arena, args)
        }
        NodeView::Let(_, _, value, body) | NodeView::Sequence(value, body) => {
            indexed_no_side_effects(arena, value) && indexed_no_side_effects(arena, body)
        }
        NodeView::LetRec(bindings, body) => {
            bindings
                .iter()
                .all(|(_, node)| indexed_no_side_effects(arena, *node))
                && indexed_no_side_effects(arena, body)
        }
        NodeView::TryWith(body, _, handler) => {
            indexed_no_side_effects(arena, body) && indexed_no_side_effects(arena, handler)
        }
        NodeView::IfThenElse(a, b, c) => {
            indexed_no_side_effects(arena, a)
                && indexed_no_side_effects(arena, b)
                && indexed_no_side_effects(arena, c)
        }
        NodeView::Apply(function, args, _, _) => {
            matches!(arena.view(function), NodeView::Prim(Primitive::Pfield(_, FieldDbgInfo::Module { name }), _, _) if name == "from_fun" && args.len() == 1)
                && indexed_no_side_effects(arena, args[0])
        }
        NodeView::Switch { .. }
        | NodeView::StringSwitch(_, _, _)
        | NodeView::StaticRaise(_, _)
        | NodeView::StaticCatch(_, _, _, _)
        | NodeView::While(_, _)
        | NodeView::For(_, _, _, _, _)
        | NodeView::ForOf(_, _, _)
        | NodeView::ForAwaitOf(_, _, _)
        | NodeView::Break
        | NodeView::Continue
        | NodeView::Assign(_, _) => false,
    }
}

fn function_payload_needed(
    arena: &IndexedLambda,
    params: &[Ident],
    body: NodeId,
    attr: &crate::lambda::FunctionAttribute,
) -> bool {
    if attr.async_ || attr.directive.is_some() {
        return false;
    }
    if attr.is_a_functor {
        return true;
    }
    match attr.inline {
        InlineAttribute::Always => true,
        InlineAttribute::Never => false,
        InlineAttribute::Default => {
            let body_size = indexed_size(arena, body);
            let parameter_test = match arena.view(body) {
                NodeView::Switch { scrutinee, .. } | NodeView::IfThenElse(scrutinee, _, _) => {
                    matches!(arena.view(scrutinee), NodeView::Var(id) if params.iter().any(|param| param == id))
                }
                _ => false,
            };
            body_size < SMALL_INLINE_SIZE
                || body_size < 10 && indexed_no_side_effects(arena, body)
                || parameter_test
        }
    }
}

fn annotate(
    meta: &mut IndexedLamStats<'_>,
    rec_flag: RecFlag,
    id: Ident,
    arity: Arity,
    lambda: Option<NodeId>,
) {
    meta.ident_tbl.insert(
        id,
        IndexedIdKind::FunctionId {
            arity,
            lambda: lambda.map(|node| (node, rec_flag)),
        },
    );
}

fn collect_bind(
    meta: &mut IndexedLamStats<'_>,
    rec_flag: RecFlag,
    id: &Ident,
    node: NodeId,
    resolver: &mut Option<&mut ExternalArityResolver<'_>>,
) {
    match meta.arena.view(node) {
        NodeView::Const(value) => {
            meta.ident_tbl
                .insert(id.clone(), IndexedIdKind::Constant(value.clone()));
        }
        NodeView::Prim(Primitive::Pmakeblock(_, Mutable::Immutable), args, _) => {
            meta.ident_tbl
                .insert(id.clone(), kind_of_block(meta.arena, args));
            for arg in args {
                collect(meta, *arg, resolver);
            }
        }
        NodeView::Prim(Primitive::Psome | Primitive::PsomeNotNest, [arg], _) => {
            meta.ident_tbl
                .insert(id.clone(), IndexedIdKind::NormalOptional(*arg));
            collect(meta, *arg, resolver);
        }
        NodeView::Prim(Primitive::PnullToOpt, [arg], _)
            if matches!(meta.arena.view(*arg), NodeView::Var(_)) =>
        {
            meta.ident_tbl.insert(
                id.clone(),
                IndexedIdKind::OptionalBlock(*arg, BoxedNullable::Null),
            );
        }
        NodeView::Prim(Primitive::PnullUndefinedToOpt, [arg], _)
            if matches!(meta.arena.view(*arg), NodeView::Var(_)) =>
        {
            meta.ident_tbl.insert(
                id.clone(),
                IndexedIdKind::OptionalBlock(*arg, BoxedNullable::NullUndefined),
            );
        }
        NodeView::GlobalModule(source, _) => {
            alias_ident_or_global(
                meta,
                id.clone(),
                source,
                IndexedIdKind::Module(source.clone()),
            );
        }
        NodeView::Var(source) => alias_ident_or_global(meta, id.clone(), source, IndexedIdKind::Na),
        NodeView::Function(_, params, body, attr) => {
            let params = params.to_vec();
            let keep_payload = function_payload_needed(meta.arena, &params, body, attr);
            for param in &params {
                meta.ident_tbl
                    .insert(param.clone(), IndexedIdKind::Parameter);
            }
            let arity = match resolver.as_deref_mut() {
                Some(resolver) => get_arity_external(meta, node, resolver),
                None => get_arity(meta, node),
            };
            annotate(
                meta,
                rec_flag,
                id.clone(),
                arity,
                keep_payload.then_some(node),
            );
            collect(meta, body, resolver);
        }
        _ => {
            collect(meta, node, resolver);
            if meta.export_idents.contains(id) {
                let arity = match resolver.as_deref_mut() {
                    Some(resolver) => get_arity_external(meta, node, resolver),
                    None => get_arity(meta, node),
                };
                annotate(meta, rec_flag, id.clone(), arity, Some(node));
            }
        }
    }
}

fn collect(
    meta: &mut IndexedLamStats<'_>,
    node: NodeId,
    resolver: &mut Option<&mut ExternalArityResolver<'_>>,
) {
    #[cfg(test)]
    meta.visited.push(node);
    match meta.arena.view(node) {
        NodeView::Const(_)
        | NodeView::Var(_)
        | NodeView::GlobalModule(_, _)
        | NodeView::Break
        | NodeView::Continue => {}
        NodeView::Apply(function, args, _, _) => {
            collect(meta, function, resolver);
            for arg in args {
                collect(meta, *arg, resolver);
            }
        }
        NodeView::Function(_, params, body, _) => {
            let params = params.to_vec();
            for param in params {
                meta.ident_tbl.insert(param, IndexedIdKind::Parameter);
            }
            collect(meta, body, resolver);
        }
        NodeView::Let(_, id, value, body) => {
            let id = id.clone();
            collect_bind(meta, RecFlag::NonRec, &id, value, resolver);
            collect(meta, body, resolver);
        }
        NodeView::LetRec(bindings, body) => {
            let bindings = bindings.to_vec();
            let rec_flag = if bindings.len() == 1 {
                RecFlag::SelfRec
            } else {
                RecFlag::Rec
            };
            for (id, value) in bindings {
                collect_bind(meta, rec_flag, &id, value, resolver);
            }
            collect(meta, body, resolver);
        }
        NodeView::Prim(_, args, _) | NodeView::StaticRaise(_, args) => {
            for arg in args {
                collect(meta, *arg, resolver);
            }
        }
        NodeView::Switch {
            scrutinee,
            consts,
            blocks,
            fail_action,
            ..
        } => {
            collect(meta, scrutinee, resolver);
            for (_, body) in consts {
                collect(meta, *body, resolver);
            }
            for (_, body) in blocks {
                collect(meta, *body, resolver);
            }
            if let Some(fail) = fail_action {
                collect(meta, fail, resolver);
            }
        }
        NodeView::StringSwitch(scrutinee, cases, default) => {
            collect(meta, scrutinee, resolver);
            for (_, body) in cases {
                collect(meta, *body, resolver);
            }
            if let Some(default) = default {
                collect(meta, default, resolver);
            }
        }
        NodeView::StaticCatch(body, _, _, handler) | NodeView::TryWith(body, _, handler) => {
            collect(meta, body, resolver);
            collect(meta, handler, resolver);
        }
        NodeView::IfThenElse(a, b, c) | NodeView::For(_, a, b, _, c) => {
            collect(meta, a, resolver);
            collect(meta, b, resolver);
            collect(meta, c, resolver);
        }
        NodeView::Sequence(a, b)
        | NodeView::While(a, b)
        | NodeView::ForOf(_, a, b)
        | NodeView::ForAwaitOf(_, a, b) => {
            collect(meta, a, resolver);
            collect(meta, b, resolver);
        }
        NodeView::Assign(_, value) => collect(meta, value, resolver),
    }
}

pub fn collect_info(meta: &mut IndexedLamStats<'_>, root: NodeId) {
    collect(meta, root, &mut None);
}

pub fn collect_info_with_external_arity(
    meta: &mut IndexedLamStats<'_>,
    root: NodeId,
    resolver: &mut ExternalArityResolver<'_>,
) {
    collect(meta, root, &mut Some(resolver));
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ident::IdentFlags;
    use crate::lambda::lam_compile_context::{Element, IdKind, LamStats};
    use crate::lambda::lam_pass_collect as tree;
    use crate::lambda::{FunctionAttribute, LambdaSwitch, SwitchDispatch, SwitchKey};
    use crate::location::Location;

    fn id(name: &str, stamp: i32) -> Ident {
        Ident::new(name, stamp, IdentFlags::NONE)
    }

    fn tree_kind(kind: &IdKind) -> String {
        match kind {
            IdKind::NormalOptional(node) => format!("normal:{node:?}"),
            IdKind::OptionalBlock(node, boxed) => format!("optional:{boxed:?}:{node:?}"),
            IdKind::ImmutableBlock(elements) => format!(
                "immutable:{}",
                elements
                    .iter()
                    .map(|element| match element {
                        Element::Na => "na".into(),
                        Element::SimpleForm(node) => format!("simple:{node:?}"),
                    })
                    .collect::<Vec<_>>()
                    .join("|")
            ),
            IdKind::MutableBlock(elements) => format!("mutable:{}", elements.len()),
            IdKind::Constant(value) => format!("constant:{value:?}"),
            IdKind::Module(id) => format!("module:{id:?}"),
            IdKind::FunctionId { arity, lambda } => {
                format!("function:{arity:?}:{}", lambda.is_some())
            }
            IdKind::Exception => "exception".into(),
            IdKind::Parameter => "parameter".into(),
            IdKind::Na => "na".into(),
        }
    }

    fn indexed_kind(arena: &IndexedLambda, kind: &IndexedIdKind) -> String {
        match kind {
            IndexedIdKind::NormalOptional(node) => {
                format!("normal:{:?}", arena.materialize_node(*node))
            }
            IndexedIdKind::OptionalBlock(node, boxed) => {
                format!("optional:{boxed:?}:{:?}", arena.materialize_node(*node))
            }
            IndexedIdKind::ImmutableBlock(elements) => format!(
                "immutable:{}",
                elements
                    .iter()
                    .map(|element| match element {
                        IndexedElement::Na => "na".into(),
                        IndexedElement::SimpleForm(node) =>
                            format!("simple:{:?}", arena.materialize_node(*node)),
                    })
                    .collect::<Vec<_>>()
                    .join("|")
            ),
            IndexedIdKind::MutableBlock(elements) => format!("mutable:{}", elements.len()),
            IndexedIdKind::Constant(value) => format!("constant:{value:?}"),
            IndexedIdKind::Module(id) => format!("module:{id:?}"),
            IndexedIdKind::FunctionId { arity, lambda } => {
                format!("function:{arity:?}:{}", lambda.is_some())
            }
            IndexedIdKind::Exception => "exception".into(),
            IndexedIdKind::Parameter => "parameter".into(),
            IndexedIdKind::Na => "na".into(),
        }
    }

    fn tree_collect_order(lambda: &Lambda, out: &mut Vec<String>) {
        fn bind(lambda: &Lambda, out: &mut Vec<String>) {
            match lambda {
                Lambda::Lconst(_) | Lambda::LglobalModule(_, _) | Lambda::Lvar(_) => {}
                Lambda::Lprim(crate::lambda::PrimInfo {
                    primitive: Primitive::Pmakeblock(_, Mutable::Immutable),
                    args,
                    ..
                }) => {
                    for arg in args {
                        tree_collect_order(arg, out);
                    }
                }
                Lambda::Lprim(crate::lambda::PrimInfo {
                    primitive: Primitive::Psome | Primitive::PsomeNotNest,
                    args,
                    ..
                }) if args.len() == 1 => tree_collect_order(&args[0], out),
                Lambda::Lprim(crate::lambda::PrimInfo {
                    primitive: Primitive::PnullToOpt | Primitive::PnullUndefinedToOpt,
                    args,
                    ..
                }) if matches!(args.as_slice(), [Lambda::Lvar(_)]) => {}
                Lambda::Lfunction(function) => tree_collect_order(&function.body, out),
                other => tree_collect_order(other, out),
            }
        }
        out.push(format!("{lambda:?}"));
        match lambda {
            Lambda::Lconst(_)
            | Lambda::Lvar(_)
            | Lambda::LglobalModule(_, _)
            | Lambda::Lbreak
            | Lambda::Lcontinue => {}
            Lambda::Lapply(apply) => {
                tree_collect_order(&apply.ap_func, out);
                for arg in &apply.ap_args {
                    tree_collect_order(arg, out);
                }
            }
            Lambda::Lfunction(function) => tree_collect_order(&function.body, out),
            Lambda::Llet(_, _, value, body) => {
                bind(value, out);
                tree_collect_order(body, out);
            }
            Lambda::Lletrec(bindings, body) => {
                for (_, value) in bindings {
                    bind(value, out);
                }
                tree_collect_order(body, out);
            }
            Lambda::Lprim(info) => {
                for arg in &info.args {
                    tree_collect_order(arg, out);
                }
            }
            Lambda::Lswitch(scrutinee, switch) => {
                tree_collect_order(scrutinee, out);
                for (_, body) in &switch.sw_consts {
                    tree_collect_order(body, out);
                }
                for (_, body) in &switch.sw_blocks {
                    tree_collect_order(body, out);
                }
                if let Some(fail) = &switch.sw_failaction {
                    tree_collect_order(fail, out);
                }
            }
            Lambda::LstringSwitch(scrutinee, cases, default) => {
                tree_collect_order(scrutinee, out);
                for (_, body) in cases {
                    tree_collect_order(body, out);
                }
                if let Some(default) = default {
                    tree_collect_order(default, out);
                }
            }
            Lambda::LstaticRaise(_, args) => {
                for arg in args {
                    tree_collect_order(arg, out);
                }
            }
            Lambda::LstaticCatch(body, _, handler) | Lambda::LtryWith(body, _, handler) => {
                tree_collect_order(body, out);
                tree_collect_order(handler, out);
            }
            Lambda::LifThenElse(a, b, c) | Lambda::Lfor(_, a, b, _, c) => {
                tree_collect_order(a, out);
                tree_collect_order(b, out);
                tree_collect_order(c, out);
            }
            Lambda::Lsequence(a, b)
            | Lambda::Lwhile(a, b)
            | Lambda::Lfor_of(_, a, b)
            | Lambda::Lfor_await_of(_, a, b) => {
                tree_collect_order(a, out);
                tree_collect_order(b, out);
            }
            Lambda::Lassign(_, value) => tree_collect_order(value, out),
        }
    }

    #[test]
    fn collect_and_arity_match_tree_metadata_across_ordered_variants() {
        let x = id("x", 1);
        let f = id("f", 2);
        let block = id("block", 3);
        let optional = id("optional", 4);
        let function = Lambda::function_(
            1,
            vec![x.clone()],
            Lambda::Lvar(x),
            FunctionAttribute::default(),
        );
        let makeblock = Lambda::prim(
            Primitive::Pmakeblock(crate::lambda::TagInfo::Tuple, Mutable::Immutable),
            vec![Lambda::Lconst(Constant::int(1)), Lambda::Lvar(f.clone())],
            Location::none(),
        );
        let some = Lambda::prim(
            Primitive::Psome,
            vec![Lambda::Lvar(block.clone())],
            Location::none(),
        );
        let tail = Lambda::Lswitch(
            Box::new(Lambda::Lvar(optional.clone())),
            LambdaSwitch {
                sw_consts_full: false,
                sw_consts: vec![
                    (SwitchKey::Int(2), Lambda::Lvar(f.clone())),
                    (SwitchKey::Int(1), Lambda::Lconst(Constant::int(0))),
                ],
                sw_blocks_full: true,
                sw_blocks: vec![],
                sw_failaction: Some(Box::new(Lambda::Lvar(block.clone()))),
                sw_dispatch: SwitchDispatch::Direct,
            },
        );
        let lambda = Lambda::let_(
            crate::lambda::LetKind::Strict,
            f.clone(),
            function,
            Lambda::let_(
                crate::lambda::LetKind::Strict,
                block.clone(),
                makeblock,
                Lambda::let_(crate::lambda::LetKind::Strict, optional.clone(), some, tail),
            ),
        );
        let exports = vec![optional];
        let mut expected_order = vec![];
        tree_collect_order(&lambda, &mut expected_order);
        let mut tree_meta = LamStats::new(exports.clone());
        tree::collect_info(&mut tree_meta, &lambda);
        let indexed = IndexedLambda::from_lambda(lambda);
        let mut indexed_meta = IndexedLamStats::new(&indexed, exports);
        collect_info(&mut indexed_meta, indexed.root());
        let mut expected = tree_meta
            .ident_tbl
            .iter()
            .map(|(id, kind)| (format!("{id:?}"), tree_kind(kind)))
            .collect::<Vec<_>>();
        expected.sort();
        let mut actual = indexed_meta
            .ident_tbl
            .iter()
            .map(|(id, kind)| (format!("{id:?}"), indexed_kind(&indexed, kind)))
            .collect::<Vec<_>>();
        actual.sort();
        assert_eq!(expected, actual);
        let actual_order = indexed_meta
            .visited
            .iter()
            .map(|node| format!("{:?}", indexed.materialize_node(*node)))
            .collect::<Vec<_>>();
        assert_eq!(expected_order, actual_order);
        assert_eq!(
            tree::get_arity(&tree_meta, &indexed.materialize()),
            get_arity(&indexed_meta, indexed.root())
        );
    }

    #[test]
    fn external_arity_lookup_matches_tree_collect() {
        let module = id("Dependency", 1);
        let exported = id("exported", 2);
        let value = Lambda::prim(
            Primitive::Pfield(0, FieldDbgInfo::Module { name: "run".into() }),
            vec![Lambda::LglobalModule(module, false)],
            Location::none(),
        );
        let lambda = Lambda::let_(
            crate::lambda::LetKind::Strict,
            exported.clone(),
            value,
            Lambda::Lvar(exported.clone()),
        );
        let mut tree_meta = LamStats::new(vec![exported.clone()]);
        let mut tree_resolver = |_: &Ident, _: bool, _: &str| {
            Some(ExternalArityInfo::Single(Arity::info(vec![2], false)))
        };
        tree::collect_info_with_external_arity(&mut tree_meta, &lambda, &mut tree_resolver);

        let indexed = IndexedLambda::from_lambda(lambda);
        let mut indexed_meta = IndexedLamStats::new(&indexed, [exported.clone()]);
        let mut indexed_resolver = |_: &Ident, _: bool, _: &str| {
            Some(ExternalArityInfo::Single(Arity::info(vec![2], false)))
        };
        collect_info_with_external_arity(&mut indexed_meta, indexed.root(), &mut indexed_resolver);
        assert_eq!(
            tree_kind(tree_meta.ident_tbl.get(&exported).unwrap()),
            indexed_kind(&indexed, indexed_meta.ident_tbl.get(&exported).unwrap())
        );
    }

    #[test]
    fn shared_child_is_visited_once_per_ordered_edge() {
        let shared_tree = Lambda::Lvar(id("shared", 1));
        let mut indexed = IndexedLambda::from_lambda(shared_tree);
        let shared = indexed.root();
        let root = indexed.append_sequence(shared, shared);
        let materialized = indexed.materialize_node(root);
        let mut expected = vec![];
        tree_collect_order(&materialized, &mut expected);
        let mut meta = IndexedLamStats::new(&indexed, []);
        collect_info(&mut meta, root);
        assert_eq!(meta.visited, vec![root, shared, shared]);
        let actual = meta
            .visited
            .iter()
            .map(|node| format!("{:?}", indexed.materialize_node(*node)))
            .collect::<Vec<_>>();
        assert_eq!(expected, actual);
    }
}
