//! Indexed beta reduction and capture-avoiding bounded-variable rewrite.
//! Mirrors `lam_beta_reduce_util.ml`, `lam_beta_reduce.ml`, and `lam_bounded_vars.ml`.

use ahash::AHashMap;

use crate::context::IdGenerator;
use crate::ident::Ident;
use crate::lambda::indexed::{IndexedLambda, NodeId, NodeSnapshot, NodeView};
use crate::lambda::lam_analysis_indexed::no_side_effects;
use crate::lambda::lam_closure::StatsMap;
use crate::lambda::lam_compat::LetKind;
use crate::lambda::lam_indexed_helpers::{
    VariableSubstitution, append_rebuilt, append_refine_let, map_children,
};
use crate::lambda::lam_pass_collect_indexed::{IndexedIdKind, IndexedLamStats, kind_of_block};
use crate::lambda::lam_primitive::{Mutable, Primitive};
use crate::location::Location;

struct Usage {
    node: NodeId,
    used: bool,
}

pub(crate) fn simple_beta_reduce(
    store: &mut IndexedLambda,
    params: &[Ident],
    body: NodeId,
    args: &[NodeId],
) -> Option<NodeId> {
    let mut usages: AHashMap<Ident, Usage> = params
        .iter()
        .cloned()
        .zip(args.iter().copied())
        .map(|(id, node)| (id, Usage { node, used: false }))
        .collect();
    fn replace(
        store: &IndexedLambda,
        usages: &mut AHashMap<Ident, Usage>,
        nodes: &[NodeId],
    ) -> Option<Vec<NodeId>> {
        nodes
            .iter()
            .map(|node| match store.view(*node) {
                NodeView::Var(id) => match usages.get_mut(id) {
                    Some(usage) if !usage.used => {
                        usage.used = true;
                        Some(usage.node)
                    }
                    Some(_) => None,
                    None => Some(*node),
                },
                NodeView::Const(_) => Some(*node),
                _ => None,
            })
            .collect()
    }
    let mut result = match store.snapshot(body) {
        NodeSnapshot::Prim(primitive, body_args, loc) => {
            let body_args = replace(store, &mut usages, &body_args)?;
            append_rebuilt(store, NodeSnapshot::Prim(primitive, body_args, loc))
        }
        NodeSnapshot::Apply(function, body_args, info, _)
            if {
                match store.view(function) {
                    NodeView::Var(_) => true,
                    NodeView::Prim(Primitive::Pfield(_, _), [base], _) => {
                        matches!(store.view(*base), NodeView::GlobalModule(_, _))
                    }
                    _ => false,
                }
            } =>
        {
            let body_args = replace(store, &mut usages, &body_args)?;
            let function = if let NodeView::Var(id) = store.view(function) {
                match usages.get_mut(id) {
                    Some(usage) if !usage.used => {
                        usage.used = true;
                        usage.node
                    }
                    Some(_) => return None,
                    None => function,
                }
            } else {
                function
            };
            // `Lam.apply` default resets transformed JSX in simple beta reduction.
            append_rebuilt(store, NodeSnapshot::Apply(function, body_args, info, false))
        }
        _ => return None,
    };
    for usage in usages.values() {
        if !usage.used {
            result = append_rebuilt(store, NodeSnapshot::Sequence(usage.node, result));
        }
    }
    Some(result)
}

fn rebind(
    store: &mut IndexedLambda,
    map: &mut VariableSubstitution,
    id_gen: &IdGenerator,
    id: &Ident,
) -> Ident {
    let fresh = id.rename(id_gen);
    let var = store.append(NodeSnapshot::Var(fresh.clone()));
    map.insert(id.clone(), var);
    fresh
}

fn rewrite_bounded(
    store: &mut IndexedLambda,
    map: &mut VariableSubstitution,
    node: NodeId,
    id_gen: &IdGenerator,
) -> NodeId {
    match store.snapshot(node) {
        NodeSnapshot::Var(id) => map.get(&id).copied().unwrap_or(node),
        NodeSnapshot::Const(_)
        | NodeSnapshot::GlobalModule(_, _)
        | NodeSnapshot::Break
        | NodeSnapshot::Continue => node,
        NodeSnapshot::Let(kind, id, value, body) => {
            let id = rebind(store, map, id_gen, &id);
            let value = rewrite_bounded(store, map, value, id_gen);
            let body = rewrite_bounded(store, map, body, id_gen);
            append_rebuilt(store, NodeSnapshot::Let(kind, id, value, body))
        }
        NodeSnapshot::LetRec(bindings, body) => {
            let fresh: Vec<_> = bindings
                .iter()
                .map(|(id, _)| rebind(store, map, id_gen, id))
                .collect();
            let bindings = fresh
                .into_iter()
                .zip(bindings)
                .map(|(id, (_, value))| {
                    let value = rewrite_bounded(store, map, value, id_gen);
                    (id, value)
                })
                .collect();
            let body = rewrite_bounded(store, map, body, id_gen);
            append_rebuilt(store, NodeSnapshot::LetRec(bindings, body))
        }
        NodeSnapshot::Function(arity, params, body, attr) => {
            let params = params
                .iter()
                .map(|id| rebind(store, map, id_gen, id))
                .collect();
            let body = rewrite_bounded(store, map, body, id_gen);
            append_rebuilt(store, NodeSnapshot::Function(arity, params, body, attr))
        }
        NodeSnapshot::StaticCatch(body, exit, params, handler) => {
            let body = rewrite_bounded(store, map, body, id_gen);
            let params = params
                .iter()
                .map(|id| rebind(store, map, id_gen, id))
                .collect();
            let handler = rewrite_bounded(store, map, handler, id_gen);
            append_rebuilt(
                store,
                NodeSnapshot::StaticCatch(body, exit, params, handler),
            )
        }
        NodeSnapshot::TryWith(body, id, handler) => {
            let body = rewrite_bounded(store, map, body, id_gen);
            let id = rebind(store, map, id_gen, &id);
            let handler = rewrite_bounded(store, map, handler, id_gen);
            append_rebuilt(store, NodeSnapshot::TryWith(body, id, handler))
        }
        NodeSnapshot::For(id, from, to, direction, body) => {
            let id = rebind(store, map, id_gen, &id);
            // Preserve `lam_bounded_vars.ml`'s two traversals of `l1`.
            let first_from = rewrite_bounded(store, map, from, id_gen);
            let to = rewrite_bounded(store, map, to, id_gen);
            let body = rewrite_bounded(store, map, body, id_gen);
            let from = rewrite_bounded(store, map, first_from, id_gen);
            append_rebuilt(store, NodeSnapshot::For(id, from, to, direction, body))
        }
        NodeSnapshot::ForOf(id, iterable, body) | NodeSnapshot::ForAwaitOf(id, iterable, body) => {
            let await_ = matches!(store.snapshot(node), NodeSnapshot::ForAwaitOf(_, _, _));
            let id = rebind(store, map, id_gen, &id);
            let iterable = rewrite_bounded(store, map, iterable, id_gen);
            let body = rewrite_bounded(store, map, body, id_gen);
            append_rebuilt(
                store,
                if await_ {
                    NodeSnapshot::ForAwaitOf(id, iterable, body)
                } else {
                    NodeSnapshot::ForOf(id, iterable, body)
                },
            )
        }
        snapshot => {
            let mapped = map_children(store, snapshot, |store, child| {
                rewrite_bounded(store, map, child, id_gen)
            });
            append_rebuilt(store, mapped)
        }
    }
}

fn boxed_optional(store: &IndexedLambda, node: NodeId) -> bool {
    matches!(
        store.view(node),
        NodeView::Prim(Primitive::PnullToOpt | Primitive::PnullUndefinedToOpt, _, _)
    )
}

fn register_kind(store: &IndexedLambda, meta: &mut IndexedLamStats, id: Ident, arg: NodeId) {
    match store.view(arg) {
        NodeView::Prim(Primitive::Pmakeblock(_, Mutable::Immutable), args, _) => {
            meta.ident_tbl.insert(id, kind_of_block(store, args));
        }
        NodeView::Prim(Primitive::Psome | Primitive::PsomeNotNest, [value], _) => {
            meta.ident_tbl
                .insert(id, IndexedIdKind::NormalOptional(*value));
        }
        _ => {}
    }
}

fn propagate(
    store: &mut IndexedLambda,
    meta: &mut IndexedLamStats,
    stats: Option<&StatsMap>,
    params: &[Ident],
    body: NodeId,
    args: &[NodeId],
    id_gen: &IdGenerator,
) -> NodeId {
    if let Some(result) = simple_beta_reduce(store, params, body, args) {
        return result;
    }
    let mut bindings = Vec::new();
    let mut map = VariableSubstitution::new();
    for (param, arg) in params.iter().zip(args.iter().copied()) {
        let direct = matches!(store.view(arg), NodeView::Const(_) | NodeView::Var(_))
            || stats.is_some_and(|stats| {
                !matches!(store.view(arg), NodeView::GlobalModule(_, _))
                    && no_side_effects(store, arg)
                    && stats
                        .get(param)
                        .is_some_and(|stat| stat.top_and_used_zero_or_one())
            });
        if direct {
            map.insert(param.clone(), arg);
            continue;
        }
        let fresh = param.rename(id_gen);
        let fresh_var = store.append(NodeSnapshot::Var(fresh.clone()));
        let (binding, replacement) = if boxed_optional(store, arg) {
            let binding = append_rebuilt(
                store,
                NodeSnapshot::Prim(Primitive::Pidentity, vec![arg], Location::none()),
            );
            let replacement = append_rebuilt(
                store,
                NodeSnapshot::Prim(Primitive::Pidentity, vec![fresh_var], Location::none()),
            );
            (binding, replacement)
        } else {
            (arg, fresh_var)
        };
        bindings.push((fresh, binding));
        map.insert(param.clone(), replacement);
    }
    let mut result = rewrite_bounded(store, &mut map, body, id_gen);
    for (id, arg) in bindings.into_iter().rev() {
        register_kind(store, meta, id.clone(), arg);
        result = append_refine_let(store, LetKind::Strict, id, arg, result);
    }
    result
}

pub(crate) fn propagate_beta_reduce(
    store: &mut IndexedLambda,
    meta: &mut IndexedLamStats,
    params: &[Ident],
    body: NodeId,
    args: &[NodeId],
    id_gen: &IdGenerator,
) -> NodeId {
    propagate(store, meta, None, params, body, args, id_gen)
}

pub(crate) fn propagate_beta_reduce_with_map(
    store: &mut IndexedLambda,
    meta: &mut IndexedLamStats,
    stats: &StatsMap,
    params: &[Ident],
    body: NodeId,
    args: &[NodeId],
    id_gen: &IdGenerator,
) -> NodeId {
    propagate(store, meta, Some(stats), params, body, args, id_gen)
}
