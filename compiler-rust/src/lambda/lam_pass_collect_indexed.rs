//! Indexed counterpart of `lam_pass_collect`.
//!
//! This module is intentionally not wired into production yet. It exercises
//! the real collect/arity algorithm against [`IndexedLambda`] while keeping
//! Lambda-bearing metadata as [`NodeId`] values owned by the same compilation context.

use ahash::{AHashMap, AHashSet};

use crate::ident::Ident;
use crate::lambda::indexed::{IndexedLambda, NodeId, NodeView};
use crate::lambda::lam_arity::Arity;
use crate::lambda::lam_compat::FieldDbgInfo;
use crate::lambda::lam_compile_context::{
    BoxedNullable, ExternalArityFieldTable, ExternalArityInfo, ExternalArityTable, RecFlag,
};
use crate::lambda::lam_constant::Constant;
use crate::lambda::lam_pass_collect::ExternalArityResolver;
use crate::lambda::lam_primitive::{Mutable, Primitive};
#[cfg(test)]
use crate::lambda::{InlineAttribute, Lambda};

#[derive(Debug, Clone)]
pub(crate) enum IndexedElement {
    Na,
    SimpleForm(NodeId),
}

#[derive(Debug, Clone)]
pub(crate) enum IndexedIdKind {
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

/// Identifier metadata for one indexed compilation. Raw IDs are interpreted only
/// by owner-scoped context entrypoints; this table deliberately carries no arena borrow.
pub(crate) struct IndexedLamStats {
    /// Ordered exports from `Translmod.transl_implementation`. The set below
    /// serves membership checks, while coercion and CMJ export preserve this list.
    pub exports: Vec<Ident>,
    pub export_idents: AHashSet<Ident>,
    pub ident_tbl: AHashMap<Ident, IndexedIdKind>,
    pub external_arities: ExternalArityTable,
    #[cfg(test)]
    visited: Vec<NodeId>,
}

impl IndexedLamStats {
    pub(crate) fn new(exports: impl IntoIterator<Item = Ident>) -> Self {
        let exports = exports.into_iter().collect::<Vec<_>>();
        Self {
            export_idents: exports.iter().cloned().collect(),
            exports,
            ident_tbl: AHashMap::new(),
            external_arities: ExternalArityTable::default(),
            #[cfg(test)]
            visited: vec![],
        }
    }

    pub(crate) fn retained_roots(&self) -> impl Iterator<Item = NodeId> + '_ {
        self.ident_tbl.values().flat_map(|kind| {
            let mut roots = Vec::new();
            match kind {
                IndexedIdKind::NormalOptional(node) | IndexedIdKind::OptionalBlock(node, _) => {
                    roots.push(*node);
                }
                IndexedIdKind::ImmutableBlock(elements) | IndexedIdKind::MutableBlock(elements) => {
                    roots.extend(elements.iter().filter_map(|element| match element {
                        IndexedElement::SimpleForm(node) => Some(*node),
                        IndexedElement::Na => None,
                    }));
                }
                IndexedIdKind::FunctionId {
                    lambda: Some((node, _)),
                    ..
                } => roots.push(*node),
                IndexedIdKind::Constant(_)
                | IndexedIdKind::Module(_)
                | IndexedIdKind::FunctionId { lambda: None, .. }
                | IndexedIdKind::Exception
                | IndexedIdKind::Parameter
                | IndexedIdKind::Na => {}
            }
            roots
        })
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

pub(crate) fn kind_of_block(arena: &IndexedLambda, args: &[NodeId]) -> IndexedIdKind {
    IndexedIdKind::ImmutableBlock(
        args.iter()
            .map(|node| element_of_node(arena, *node))
            .collect(),
    )
}

fn alias_ident_or_global(
    meta: &mut IndexedLamStats,
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
        NodeView::Prim(Primitive::Pfield(_, FieldDbgInfo::Module { name }), [base], _)
            if matches!(arena.view(*base), NodeView::GlobalModule(_, _)) =>
        {
            let NodeView::GlobalModule(module, dynamic) = arena.view(*base) else {
                unreachable!("guarded by GlobalModule match")
            };
            match lookup(module, dynamic, name) {
                Some(ExternalArityInfo::Single(arity)) => arity,
                _ => Arity::na(),
            }
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

pub(crate) fn get_arity(arena: &IndexedLambda, meta: &IndexedLamStats, node: NodeId) -> Arity {
    let mut lookup = |module: &Ident, dynamic: bool, field: &str| {
        cached_external(&meta.external_arities, module, dynamic, field)
    };
    get_arity_impl(arena, &meta.ident_tbl, node, &mut lookup)
}

pub(crate) fn get_arity_external(
    arena: &IndexedLambda,
    meta: &mut IndexedLamStats,
    node: NodeId,
    resolver: &mut ExternalArityResolver<'_>,
) -> Arity {
    let table = &meta.ident_tbl;
    let external = &mut meta.external_arities;
    let mut lookup = |module: &Ident, dynamic: bool, field: &str| {
        lookup_external(external, module, dynamic, field, resolver)
    };
    get_arity_impl(arena, table, node, &mut lookup)
}

pub(crate) fn indexed_size(arena: &IndexedLambda, node: NodeId) -> i32 {
    const TOO_BIG: i32 = 1000;
    fn constant_size(constant: &Constant) -> i32 {
        match constant {
            Constant::Some(inner) => constant_size(inner),
            Constant::Block {
                tag_info, elements, ..
            } => {
                let missing = match &**tag_info {
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

fn annotate(
    meta: &mut IndexedLamStats,
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
    arena: &IndexedLambda,
    meta: &mut IndexedLamStats,
    rec_flag: RecFlag,
    id: &Ident,
    node: NodeId,
    resolver: &mut Option<&mut ExternalArityResolver<'_>>,
) {
    match arena.view(node) {
        NodeView::Const(value) => {
            meta.ident_tbl
                .insert(id.clone(), IndexedIdKind::Constant(value.clone()));
        }
        NodeView::Prim(Primitive::Pmakeblock(_, Mutable::Immutable), args, _) => {
            meta.ident_tbl
                .insert(id.clone(), kind_of_block(arena, args));
            for arg in args {
                collect(arena, meta, *arg, resolver);
            }
        }
        NodeView::Prim(Primitive::Psome | Primitive::PsomeNotNest, [arg], _) => {
            meta.ident_tbl
                .insert(id.clone(), IndexedIdKind::NormalOptional(*arg));
            collect(arena, meta, *arg, resolver);
        }
        NodeView::Prim(Primitive::PnullToOpt, [arg], _)
            if matches!(arena.view(*arg), NodeView::Var(_)) =>
        {
            meta.ident_tbl.insert(
                id.clone(),
                IndexedIdKind::OptionalBlock(*arg, BoxedNullable::Null),
            );
        }
        NodeView::Prim(Primitive::PnullUndefinedToOpt, [arg], _)
            if matches!(arena.view(*arg), NodeView::Var(_)) =>
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
        NodeView::Function(_, params, body, _) => {
            let params = params.to_vec();
            for param in &params {
                meta.ident_tbl
                    .insert(param.clone(), IndexedIdKind::Parameter);
            }
            let arity = match resolver.as_deref_mut() {
                Some(resolver) => get_arity_external(arena, meta, node, resolver),
                None => get_arity(arena, meta, node),
            };
            annotate(meta, rec_flag, id.clone(), arity, Some(node));
            collect(arena, meta, body, resolver);
        }
        _ => {
            collect(arena, meta, node, resolver);
            if meta.export_idents.contains(id) {
                let arity = match resolver.as_deref_mut() {
                    Some(resolver) => get_arity_external(arena, meta, node, resolver),
                    None => get_arity(arena, meta, node),
                };
                annotate(meta, rec_flag, id.clone(), arity, Some(node));
            }
        }
    }
}

fn collect(
    arena: &IndexedLambda,
    meta: &mut IndexedLamStats,
    node: NodeId,
    resolver: &mut Option<&mut ExternalArityResolver<'_>>,
) {
    #[cfg(test)]
    meta.visited.push(node);
    match arena.view(node) {
        NodeView::Const(_)
        | NodeView::Var(_)
        | NodeView::GlobalModule(_, _)
        | NodeView::Break
        | NodeView::Continue => {}
        NodeView::Apply(function, args, _, _) => {
            collect(arena, meta, function, resolver);
            for arg in args {
                collect(arena, meta, *arg, resolver);
            }
        }
        NodeView::Function(_, params, body, _) => {
            let params = params.to_vec();
            for param in params {
                meta.ident_tbl.insert(param, IndexedIdKind::Parameter);
            }
            collect(arena, meta, body, resolver);
        }
        NodeView::Let(_, id, value, body) => {
            let id = id.clone();
            collect_bind(arena, meta, RecFlag::NonRec, &id, value, resolver);
            collect(arena, meta, body, resolver);
        }
        NodeView::LetRec(bindings, body) => {
            let bindings = bindings.to_vec();
            let rec_flag = if bindings.len() == 1 {
                RecFlag::SelfRec
            } else {
                RecFlag::Rec
            };
            for (id, value) in bindings {
                collect_bind(arena, meta, rec_flag, &id, value, resolver);
            }
            collect(arena, meta, body, resolver);
        }
        NodeView::Prim(_, args, _) | NodeView::StaticRaise(_, args) => {
            for arg in args {
                collect(arena, meta, *arg, resolver);
            }
        }
        NodeView::Switch {
            scrutinee,
            consts,
            blocks,
            fail_action,
            ..
        } => {
            collect(arena, meta, scrutinee, resolver);
            for (_, body) in consts {
                collect(arena, meta, *body, resolver);
            }
            for (_, body) in blocks {
                collect(arena, meta, *body, resolver);
            }
            if let Some(fail) = fail_action {
                collect(arena, meta, fail, resolver);
            }
        }
        NodeView::StringSwitch(scrutinee, cases, default) => {
            collect(arena, meta, scrutinee, resolver);
            for (_, body) in cases {
                collect(arena, meta, *body, resolver);
            }
            if let Some(default) = default {
                collect(arena, meta, default, resolver);
            }
        }
        NodeView::StaticCatch(body, _, _, handler) | NodeView::TryWith(body, _, handler) => {
            collect(arena, meta, body, resolver);
            collect(arena, meta, handler, resolver);
        }
        NodeView::IfThenElse(a, b, c) | NodeView::For(_, a, b, _, c) => {
            collect(arena, meta, a, resolver);
            collect(arena, meta, b, resolver);
            collect(arena, meta, c, resolver);
        }
        NodeView::Sequence(a, b)
        | NodeView::While(a, b)
        | NodeView::ForOf(_, a, b)
        | NodeView::ForAwaitOf(_, a, b) => {
            collect(arena, meta, a, resolver);
            collect(arena, meta, b, resolver);
        }
        NodeView::Assign(_, value) => collect(arena, meta, value, resolver),
    }
}

pub(crate) fn collect_info(arena: &IndexedLambda, meta: &mut IndexedLamStats, root: NodeId) {
    collect(arena, meta, root, &mut None);
}

pub(crate) fn collect_info_with_external_arity(
    arena: &IndexedLambda,
    meta: &mut IndexedLamStats,
    root: NodeId,
    resolver: &mut ExternalArityResolver<'_>,
) {
    collect(arena, meta, root, &mut Some(resolver));
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
            IdKind::FunctionId { arity, lambda } => format!(
                "function:{arity:?}:{}",
                lambda
                    .as_ref()
                    .map(|(lambda, rec_flag)| format!("{lambda:?}:{rec_flag:?}"))
                    .unwrap_or_else(|| "none".into())
            ),
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
            IndexedIdKind::FunctionId { arity, lambda } => format!(
                "function:{arity:?}:{}",
                lambda
                    .as_ref()
                    .map(|(node, rec_flag)| format!(
                        "{:?}:{rec_flag:?}",
                        arena.materialize_node(*node)
                    ))
                    .unwrap_or_else(|| "none".into())
            ),
            IndexedIdKind::Exception => "exception".into(),
            IndexedIdKind::Parameter => "parameter".into(),
            IndexedIdKind::Na => "na".into(),
        }
    }

    fn tree_collect_order(lambda: &Lambda, out: &mut Vec<String>) {
        fn bind(lambda: &Lambda, out: &mut Vec<String>) {
            match lambda {
                Lambda::Lconst(_) | Lambda::LglobalModule(_, _) | Lambda::Lvar(_) => {}
                Lambda::Lprim(__prim2)
                    if matches!(
                        __prim2.as_ref(),
                        crate::lambda::PrimInfo {
                            primitive: Primitive::Pmakeblock(_, Mutable::Immutable),
                            args: _,
                            ..
                        }
                    ) =>
                {
                    let crate::lambda::PrimInfo {
                        primitive: Primitive::Pmakeblock(_, Mutable::Immutable),
                        args,
                        ..
                    } = __prim2.as_ref()
                    else {
                        unreachable!()
                    };

                    for arg in args {
                        tree_collect_order(arg, out);
                    }
                }
                Lambda::Lprim(__prim1)
                    if matches!(__prim1.as_ref(), crate::lambda::PrimInfo {
                    primitive: Primitive::Psome | Primitive::PsomeNotNest,
                    args,
                    ..
                } if args.len() == 1) =>
                {
                    let crate::lambda::PrimInfo {
                        primitive: Primitive::Psome | Primitive::PsomeNotNest,
                        args,
                        ..
                    } = __prim1.as_ref()
                    else {
                        unreachable!()
                    };
                    tree_collect_order(&args[0], out)
                }
                Lambda::Lprim(__prim0)
                    if matches!(__prim0.as_ref(), crate::lambda::PrimInfo {
                    primitive: Primitive::PnullToOpt | Primitive::PnullUndefinedToOpt,
                    args,
                    ..
                } if matches!(args.as_slice(), [Lambda::Lvar(_)])) =>
                {
                    let crate::lambda::PrimInfo {
                        primitive: Primitive::PnullToOpt | Primitive::PnullUndefinedToOpt,
                        args,
                        ..
                    } = __prim0.as_ref()
                    else {
                        unreachable!()
                    };
                }
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
            Box::new(LambdaSwitch {
                sw_consts_full: false,
                sw_consts: vec![
                    (SwitchKey::Int(2), Lambda::Lvar(f.clone())),
                    (SwitchKey::Int(1), Lambda::Lconst(Constant::int(0))),
                ],
                sw_blocks_full: true,
                sw_blocks: vec![],
                sw_failaction: Some(Box::new(Lambda::Lvar(block.clone()))),
                sw_dispatch: SwitchDispatch::Direct,
            }),
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
        let mut indexed_meta = IndexedLamStats::new(exports);
        collect_info(&indexed, &mut indexed_meta, indexed.root());
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
            get_arity(&indexed, &indexed_meta, indexed.root())
        );
    }

    #[test]
    fn get_arity_matches_tree_across_control_flow_variants() {
        fn function(arity: i32) -> Lambda {
            Lambda::function_(
                arity,
                (0..arity).map(|n| id("p", 100 + n)).collect(),
                Lambda::Lconst(Constant::int(0)),
                FunctionAttribute::default(),
            )
        }
        fn assert_same(lambda: Lambda) {
            let mut tree_meta = LamStats::new(vec![]);
            tree::collect_info(&mut tree_meta, &lambda);
            let expected = tree::get_arity(&tree_meta, &lambda);
            let indexed = IndexedLambda::from_lambda(lambda);
            let mut indexed_meta = IndexedLamStats::new([]);
            collect_info(&indexed, &mut indexed_meta, indexed.root());
            assert_eq!(expected, get_arity(&indexed, &indexed_meta, indexed.root()));
        }
        let apply_info = crate::lambda::ApInfo {
            loc: Location::none(),
            inlined: crate::lambda::InlineAttribute::Default,
            status: crate::lambda::ApplyStatus::Na,
        };
        for sample in [
            Lambda::Lconst(Constant::int(0)),
            function(2),
            Lambda::apply(
                function(2),
                vec![Lambda::Lconst(Constant::int(1))],
                apply_info,
                false,
            ),
            Lambda::Lswitch(
                Box::new(Lambda::Lconst(Constant::int(0))),
                Box::new(LambdaSwitch {
                    sw_consts_full: false,
                    sw_consts: vec![(SwitchKey::Int(1), function(1))],
                    sw_blocks_full: true,
                    sw_blocks: vec![(SwitchKey::Int(2), function(1))],
                    sw_failaction: Some(Box::new(function(1))),
                    sw_dispatch: SwitchDispatch::Direct,
                }),
            ),
            Lambda::LstringSwitch(
                Box::new(Lambda::Lconst(Constant::int(0))),
                vec![("a".into(), function(1)), ("b".into(), function(1))],
                Some(Box::new(function(1))),
            ),
            Lambda::LstaticCatch(
                Box::new(Lambda::LstaticRaise(1, vec![])),
                (1, vec![]),
                Box::new(function(1)),
            ),
            Lambda::LtryWith(Box::new(function(1)), id("exn", 5), Box::new(function(1))),
            Lambda::LifThenElse(
                Box::new(Lambda::Lconst(Constant::JsTrue)),
                Box::new(function(1)),
                Box::new(function(1)),
            ),
            Lambda::Lsequence(
                Box::new(Lambda::Lconst(Constant::int(0))),
                Box::new(function(1)),
            ),
            Lambda::LstaticRaise(1, vec![]),
            Lambda::Lwhile(
                Box::new(Lambda::Lconst(Constant::JsTrue)),
                Box::new(Lambda::Lconst(Constant::int(0))),
            ),
        ] {
            assert_same(sample);
        }
    }

    #[test]
    fn retained_function_payloads_rec_flags_and_optional_kinds_match_tree() {
        fn function(body: Lambda, inline: crate::lambda::InlineAttribute) -> Lambda {
            Lambda::function_(
                0,
                vec![],
                body,
                FunctionAttribute {
                    inline,
                    ..FunctionAttribute::default()
                },
            )
        }
        let always = id("always", 20);
        let never = id("never", 21);
        let single_rec = id("singleRec", 22);
        let mutual_a = id("mutualA", 23);
        let mutual_b = id("mutualB", 24);
        let source = id("source", 25);
        let null_opt = id("nullOpt", 26);
        let null_undefined_opt = id("nullUndefinedOpt", 27);
        let long_body = (0..12)
            .rev()
            .fold(Lambda::Lconst(Constant::int(0)), |body, n| {
                Lambda::Lsequence(Box::new(Lambda::Lconst(Constant::int(n))), Box::new(body))
            });
        let lambda = Lambda::let_(
            crate::lambda::LetKind::Strict,
            always.clone(),
            function(long_body, crate::lambda::InlineAttribute::Always),
            Lambda::let_(
                crate::lambda::LetKind::Strict,
                never.clone(),
                function(
                    Lambda::Lconst(Constant::int(0)),
                    crate::lambda::InlineAttribute::Never,
                ),
                Lambda::letrec(
                    vec![(
                        single_rec.clone(),
                        function(
                            Lambda::Lvar(single_rec.clone()),
                            crate::lambda::InlineAttribute::Default,
                        ),
                    )],
                    Lambda::letrec(
                        vec![
                            (
                                mutual_a.clone(),
                                function(
                                    Lambda::Lvar(mutual_b.clone()),
                                    crate::lambda::InlineAttribute::Default,
                                ),
                            ),
                            (
                                mutual_b.clone(),
                                function(
                                    Lambda::Lvar(mutual_a.clone()),
                                    crate::lambda::InlineAttribute::Default,
                                ),
                            ),
                        ],
                        Lambda::let_(
                            crate::lambda::LetKind::Alias,
                            source.clone(),
                            Lambda::Lconst(Constant::int(1)),
                            Lambda::let_(
                                crate::lambda::LetKind::Strict,
                                null_opt.clone(),
                                Lambda::prim(
                                    Primitive::PnullToOpt,
                                    vec![Lambda::Lvar(source.clone())],
                                    Location::none(),
                                ),
                                Lambda::let_(
                                    crate::lambda::LetKind::Strict,
                                    null_undefined_opt.clone(),
                                    Lambda::prim(
                                        Primitive::PnullUndefinedToOpt,
                                        vec![Lambda::Lvar(source)],
                                        Location::none(),
                                    ),
                                    Lambda::Lvar(null_undefined_opt.clone()),
                                ),
                            ),
                        ),
                    ),
                ),
            ),
        );
        let mut tree_meta = LamStats::new(vec![]);
        tree::collect_info(&mut tree_meta, &lambda);
        let indexed = IndexedLambda::from_lambda(lambda);
        let mut indexed_meta = IndexedLamStats::new([]);
        collect_info(&indexed, &mut indexed_meta, indexed.root());
        for ident in [
            always,
            single_rec,
            mutual_a,
            mutual_b,
            null_opt,
            null_undefined_opt,
        ] {
            assert_eq!(
                tree_kind(tree_meta.ident_tbl.get(&ident).unwrap()),
                indexed_kind(&indexed, indexed_meta.ident_tbl.get(&ident).unwrap()),
                "metadata differs for {ident:?}"
            );
        }
        assert!(matches!(
            tree_meta.ident_tbl.get(&never),
            Some(IdKind::FunctionId { lambda: None, .. })
        ));
        assert!(matches!(
            indexed_meta.ident_tbl.get(&never),
            Some(IndexedIdKind::FunctionId {
                lambda: Some(_),
                ..
            })
        ));
    }

    #[test]
    fn bound_functions_always_retain_node_ids_like_ocaml_collect() {
        fn raw_function(params: Vec<Ident>, body: Lambda, attr: FunctionAttribute) -> Lambda {
            Lambda::Lfunction(Box::new(crate::lambda::LFunction {
                arity: params.len() as i32,
                params,
                body: Box::new(body),
                attr,
            }))
        }
        fn sequences(count: i32) -> Lambda {
            (1..count).fold(Lambda::Lconst(Constant::int(0)), |body, n| {
                Lambda::Lsequence(Box::new(Lambda::Lconst(Constant::int(n))), Box::new(body))
            })
        }
        let param = id("param", 60);
        let parameter_switch = Lambda::Lswitch(
            Box::new(Lambda::Lvar(param.clone())),
            Box::new(LambdaSwitch {
                sw_consts_full: true,
                sw_consts: vec![(SwitchKey::Int(0), Lambda::Lconst(Constant::int(0)))],
                sw_blocks_full: true,
                sw_blocks: vec![],
                sw_failaction: None,
                sw_dispatch: SwitchDispatch::Direct,
            }),
        );
        let impure_medium = Lambda::Lsequence(
            Box::new(Lambda::Lassign(
                id("mutable", 61),
                Box::new(Lambda::Lconst(Constant::int(0))),
            )),
            Box::new(sequences(3)),
        );
        let mut async_attr = FunctionAttribute {
            inline: crate::lambda::InlineAttribute::Always,
            ..FunctionAttribute::default()
        };
        async_attr.async_ = true;
        let directive_attr = FunctionAttribute {
            inline: crate::lambda::InlineAttribute::Always,
            directive: Some("use server".into()),
            ..FunctionAttribute::default()
        };
        let functor_attr = FunctionAttribute {
            inline: crate::lambda::InlineAttribute::Never,
            is_a_functor: true,
            ..FunctionAttribute::default()
        };
        let cases = vec![
            (
                id("always", 70),
                raw_function(
                    vec![],
                    sequences(12),
                    FunctionAttribute {
                        inline: crate::lambda::InlineAttribute::Always,
                        ..FunctionAttribute::default()
                    },
                ),
                true,
            ),
            (
                id("never", 71),
                raw_function(
                    vec![],
                    Lambda::Lconst(Constant::int(0)),
                    FunctionAttribute {
                        inline: crate::lambda::InlineAttribute::Never,
                        ..FunctionAttribute::default()
                    },
                ),
                false,
            ),
            (
                id("defaultSmall", 72),
                raw_function(
                    vec![],
                    Lambda::Lconst(Constant::int(0)),
                    FunctionAttribute::default(),
                ),
                true,
            ),
            (
                id("defaultPureMedium", 73),
                raw_function(vec![], sequences(6), FunctionAttribute::default()),
                true,
            ),
            (
                id("defaultPureLarge", 74),
                raw_function(vec![], sequences(12), FunctionAttribute::default()),
                false,
            ),
            (
                id("defaultImpureMedium", 75),
                raw_function(vec![], impure_medium, FunctionAttribute::default()),
                false,
            ),
            (
                id("parameterDriven", 76),
                raw_function(vec![param], parameter_switch, FunctionAttribute::default()),
                true,
            ),
            (
                id("asyncAlways", 77),
                raw_function(vec![], Lambda::Lconst(Constant::int(0)), async_attr),
                false,
            ),
            (
                id("directiveAlways", 78),
                raw_function(vec![], Lambda::Lconst(Constant::int(0)), directive_attr),
                false,
            ),
            (
                id("functorNever", 79),
                raw_function(vec![], Lambda::Lconst(Constant::int(0)), functor_attr),
                true,
            ),
        ];
        let lambda = cases.iter().rev().fold(
            Lambda::Lconst(Constant::int(0)),
            |body, (ident, function, _)| {
                Lambda::Llet(
                    crate::lambda::LetKind::Strict,
                    ident.clone(),
                    Box::new(function.clone()),
                    Box::new(body),
                )
            },
        );
        let mut tree_meta = LamStats::new(vec![]);
        tree::collect_info(&mut tree_meta, &lambda);
        let mut context =
            crate::lambda::indexed::IndexedLambdaContext::from_lambda(lambda.clone(), []);
        context.collect_info();
        context.simplify_exits(&crate::context::IdGenerator::with_start_stamp(100));
        let retained = context.storage_measurements();
        assert!(retained.metadata_retained_only_side_payload_shallow_bytes > 0);
        let indexed = IndexedLambda::from_lambda(lambda);
        let mut indexed_meta = IndexedLamStats::new([]);
        collect_info(&indexed, &mut indexed_meta, indexed.root());
        for (ident, function, old_tree_payload) in cases {
            let tree_kind_value = tree_meta.ident_tbl.get(&ident).unwrap();
            let indexed_kind_value = indexed_meta.ident_tbl.get(&ident).unwrap();
            if old_tree_payload {
                assert_eq!(
                    tree_kind(tree_kind_value),
                    indexed_kind(&indexed, indexed_kind_value)
                );
            } else {
                // OCaml `lam_pass_collect.ml:34-37,79-89` always stores the
                // bound function. Current recursive Rust conditionally drops
                // large/never/async/directive payloads to compensate for tree
                // cloning; indexed NodeIds do not need that compensation.
                assert!(matches!(
                    tree_kind_value,
                    IdKind::FunctionId { lambda: None, .. }
                ));
            }
            let IndexedIdKind::FunctionId { lambda, .. } = indexed_kind_value else {
                panic!("expected function metadata for {ident:?}")
            };
            let Some((node, rec_flag)) = lambda else {
                panic!("indexed collect dropped bound function {ident:?}")
            };
            assert_eq!(
                format!("{function:#?}"),
                format!("{:#?}", indexed.materialize_node(*node))
            );
            assert!(matches!(rec_flag, RecFlag::NonRec));
        }
    }

    #[test]
    fn collect_reaches_bindings_under_loop_and_assignment_arms() {
        let assigned = id("assigned", 40);
        let for_bound = id("forBound", 41);
        let for_of_bound = id("forOfBound", 42);
        let for_await_bound = id("forAwaitBound", 43);
        let loop_id = id("loop", 44);
        let binding = |ident: Ident, value: i32| {
            Lambda::Llet(
                crate::lambda::LetKind::Strict,
                ident.clone(),
                Box::new(Lambda::Lconst(Constant::int(value))),
                Box::new(Lambda::Lvar(ident)),
            )
        };
        let lambda = Lambda::Lsequence(
            Box::new(Lambda::Lassign(
                id("target", 45),
                Box::new(binding(assigned.clone(), 1)),
            )),
            Box::new(Lambda::Lsequence(
                Box::new(Lambda::Lfor(
                    loop_id.clone(),
                    Box::new(Lambda::Lconst(Constant::int(0))),
                    Box::new(Lambda::Lconst(Constant::int(1))),
                    crate::lambda::DirectionFlag::Upto,
                    Box::new(binding(for_bound.clone(), 2)),
                )),
                Box::new(Lambda::Lsequence(
                    Box::new(Lambda::Lfor_of(
                        loop_id.clone(),
                        Box::new(Lambda::Lvar(loop_id.clone())),
                        Box::new(binding(for_of_bound.clone(), 3)),
                    )),
                    Box::new(Lambda::Lfor_await_of(
                        loop_id.clone(),
                        Box::new(Lambda::Lvar(loop_id)),
                        Box::new(binding(for_await_bound.clone(), 4)),
                    )),
                )),
            )),
        );
        let mut tree_meta = LamStats::new(vec![]);
        tree::collect_info(&mut tree_meta, &lambda);
        let indexed = IndexedLambda::from_lambda(lambda);
        let mut indexed_meta = IndexedLamStats::new([]);
        collect_info(&indexed, &mut indexed_meta, indexed.root());
        for ident in [assigned, for_bound, for_of_bound, for_await_bound] {
            let expected = tree_meta.ident_tbl.get(&ident).unwrap();
            let actual = indexed_meta.ident_tbl.get(&ident).unwrap();
            assert_eq!(tree_kind(expected), indexed_kind(&indexed, actual));
            assert!(matches!(actual, IndexedIdKind::Constant(_)));
        }
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
        let mut indexed_meta = IndexedLamStats::new([exported.clone()]);
        let mut indexed_resolver = |_: &Ident, _: bool, _: &str| {
            Some(ExternalArityInfo::Single(Arity::info(vec![2], false)))
        };
        collect_info_with_external_arity(
            &indexed,
            &mut indexed_meta,
            indexed.root(),
            &mut indexed_resolver,
        );
        assert_eq!(
            tree_kind(tree_meta.ident_tbl.get(&exported).unwrap()),
            indexed_kind(&indexed, indexed_meta.ident_tbl.get(&exported).unwrap())
        );
    }

    #[test]
    fn cached_external_misses_do_not_reresolve_and_keep_import_modes_separate() {
        fn field(module: Ident, dynamic: bool) -> Lambda {
            Lambda::Lprim(Box::new(crate::lambda::PrimInfo {
                primitive: Primitive::Pfield(
                    0,
                    FieldDbgInfo::Module {
                        name: "missing".into(),
                    },
                ),
                args: vec![Lambda::LglobalModule(module, dynamic)],
                loc: Location::none(),
            }))
        }
        let static_one = id("staticOne", 50);
        let static_two = id("staticTwo", 51);
        let dynamic = id("dynamic", 52);
        let module = id("Dependency", 53);
        let lambda = Lambda::Llet(
            crate::lambda::LetKind::Strict,
            static_one.clone(),
            Box::new(field(module.clone(), false)),
            Box::new(Lambda::Llet(
                crate::lambda::LetKind::Strict,
                static_two.clone(),
                Box::new(field(module.clone(), false)),
                Box::new(Lambda::Llet(
                    crate::lambda::LetKind::Strict,
                    dynamic.clone(),
                    Box::new(field(module, true)),
                    Box::new(Lambda::Lvar(dynamic.clone())),
                )),
            )),
        );
        let exports = vec![static_one, static_two, dynamic];
        let mut tree_calls = vec![];
        let mut tree_resolver = |module: &Ident, dynamic: bool, field: &str| {
            tree_calls.push((module.name().to_string(), dynamic, field.to_string()));
            None
        };
        let mut tree_meta = LamStats::new(exports.clone());
        tree::collect_info_with_external_arity(&mut tree_meta, &lambda, &mut tree_resolver);
        let indexed = IndexedLambda::from_lambda(lambda);
        let mut indexed_calls = vec![];
        let mut indexed_resolver = |module: &Ident, dynamic: bool, field: &str| {
            indexed_calls.push((module.name().to_string(), dynamic, field.to_string()));
            None
        };
        let mut indexed_meta = IndexedLamStats::new(exports);
        collect_info_with_external_arity(
            &indexed,
            &mut indexed_meta,
            indexed.root(),
            &mut indexed_resolver,
        );
        assert_eq!(tree_calls, indexed_calls);
        assert_eq!(
            indexed_calls,
            vec![
                ("Dependency".into(), false, "missing".into()),
                ("Dependency".into(), true, "missing".into()),
            ]
        );
    }

    #[test]
    fn nested_submodule_arity_preserves_fallthrough_and_cache_order() {
        fn nested(module: Ident, dynamic: bool, outer: FieldDbgInfo, field: &str) -> Lambda {
            Lambda::prim(
                Primitive::Pfield(0, outer),
                vec![Lambda::prim(
                    Primitive::Pfield(0, FieldDbgInfo::Module { name: field.into() }),
                    vec![Lambda::LglobalModule(module, dynamic)],
                    Location::none(),
                )],
                Location::none(),
            )
        }
        fn resolved(dynamic: bool) -> ExternalArityInfo {
            ExternalArityInfo::Submodule(vec![Arity::info(
                vec![if dynamic { 3 } else { 2 }],
                false,
            )])
        }

        let static_export = id("staticExport", 10);
        let static_export_again = id("staticExportAgain", 11);
        let dynamic_export = id("dynamicExport", 12);
        let static_value = || {
            nested(
                id("StaticDependency", 1),
                false,
                FieldDbgInfo::Module {
                    name: "outer".into(),
                },
                "StaticSubmodule",
            )
        };
        let lambda = Lambda::let_(
            crate::lambda::LetKind::Strict,
            static_export.clone(),
            static_value(),
            Lambda::let_(
                crate::lambda::LetKind::Strict,
                static_export_again.clone(),
                static_value(),
                Lambda::let_(
                    crate::lambda::LetKind::Strict,
                    dynamic_export.clone(),
                    nested(
                        id("DynamicDependency", 2),
                        true,
                        FieldDbgInfo::Tuple,
                        "DynamicSubmodule",
                    ),
                    Lambda::Lvar(dynamic_export.clone()),
                ),
            ),
        );
        let exports = vec![
            static_export.clone(),
            static_export_again.clone(),
            dynamic_export.clone(),
        ];

        let mut tree_calls = vec![];
        let mut tree_resolver = |module: &Ident, dynamic: bool, field: &str| {
            tree_calls.push((module.name().to_string(), dynamic, field.to_string()));
            Some(resolved(dynamic))
        };
        let mut tree_meta = LamStats::new(exports.clone());
        tree::collect_info_with_external_arity(&mut tree_meta, &lambda, &mut tree_resolver);

        let indexed = IndexedLambda::from_lambda(lambda);
        let mut indexed_calls = vec![];
        let mut indexed_resolver = |module: &Ident, dynamic: bool, field: &str| {
            indexed_calls.push((module.name().to_string(), dynamic, field.to_string()));
            Some(resolved(dynamic))
        };
        let mut indexed_meta = IndexedLamStats::new(exports.clone());
        collect_info_with_external_arity(
            &indexed,
            &mut indexed_meta,
            indexed.root(),
            &mut indexed_resolver,
        );

        assert_eq!(tree_calls, indexed_calls);
        assert_eq!(
            tree_calls,
            vec![
                ("StaticDependency".into(), false, "StaticSubmodule".into()),
                ("DynamicDependency".into(), true, "DynamicSubmodule".into()),
            ]
        );
        for export in exports {
            assert_eq!(
                tree_kind(tree_meta.ident_tbl.get(&export).unwrap()),
                indexed_kind(&indexed, indexed_meta.ident_tbl.get(&export).unwrap())
            );
        }
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
        let mut meta = IndexedLamStats::new([]);
        collect_info(&indexed, &mut meta, root);
        assert_eq!(meta.visited, vec![root, shared, shared]);
        let actual = meta
            .visited
            .iter()
            .map(|node| format!("{:?}", indexed.materialize_node(*node)))
            .collect::<Vec<_>>();
        assert_eq!(expected, actual);
    }
}

#[cfg(test)]
mod indexed_size_sparse_tests {
    use super::*;
    use crate::lambda::lam_primitive::{ExternalArgAttr, ExternalObjLabel, ExternalObjSpec};
    use crate::lambda::{Constant, Lambda, TagInfo};
    use crate::location::Location;
    use crate::parser::ast::MutableFlag;

    fn sparse_tag() -> TagInfo {
        TagInfo::Record {
            fields: (0..6).map(|i| (format!("f{i}"), false)).collect(),
            logical_field_count: Some(6),
            mutable_flag: MutableFlag::Immutable,
        }
    }

    #[test]
    fn weighted_size_counts_omitted_record_and_object_fields() {
        let constant = Lambda::const_(Constant::Block {
            tag_info: Box::new(sparse_tag()),
            elements: vec![Constant::int(1)],
        });
        let store = IndexedLambda::from_lambda(constant);
        assert_eq!(indexed_size(&store, store.root()), 6);

        let block = Lambda::prim(
            Primitive::Pmakeblock(sparse_tag(), Mutable::Immutable),
            vec![Lambda::const_(Constant::int(1))],
            Location::none(),
        );
        let store = IndexedLambda::from_lambda(block);
        assert_eq!(indexed_size(&store, store.root()), 7);

        let params = (0..6)
            .map(|i| ExternalObjSpec {
                obj_arg_type: ExternalArgAttr::Nothing,
                obj_arg_label: ExternalObjLabel::Label {
                    name: format!("f{i}"),
                },
            })
            .collect();
        let object = Lambda::prim(
            Primitive::PjsObjectCreate(params),
            vec![Lambda::const_(Constant::int(1))],
            Location::none(),
        );
        let store = IndexedLambda::from_lambda(object);
        assert_eq!(indexed_size(&store, store.root()), 7);
    }
}
