//! Indexed beta reduction and capture-avoiding bounded-variable rewrite.
//! Mirrors `lam_beta_reduce_util.ml`, `lam_beta_reduce.ml`, and `lam_bounded_vars.ml`.

use ahash::AHashMap;

use crate::context::IdGenerator;
use crate::ident::Ident;
#[cfg(test)]
use crate::lambda::LamLoc;
use crate::lambda::indexed::{IndexedLambda, NodeId, NodeSnapshot, NodeView};
use crate::lambda::lam_analysis_indexed::no_side_effects;
use crate::lambda::lam_closure::StatsMap;
use crate::lambda::lam_compat::LetKind;
use crate::lambda::lam_indexed_helpers::{
    VariableSubstitution, append_rebuilt, append_refine_let, map_children,
};
use crate::lambda::lam_pass_collect_indexed::{IndexedIdKind, IndexedLamStats, kind_of_block};
use crate::lambda::lam_primitive::{Mutable, Primitive};

struct Usage {
    node: NodeId,
    used: bool,
}

#[derive(Default)]
pub(crate) struct BetaDiagnostics {
    #[cfg(test)]
    pub(crate) substitution_peak_unique_nodes: usize,
}

impl BetaDiagnostics {
    fn record(&mut self, store: &IndexedLambda, map: &VariableSubstitution) {
        #[cfg(test)]
        {
            let roots = map.values().copied().collect::<Vec<_>>();
            self.substitution_peak_unique_nodes = self
                .substitution_peak_unique_nodes
                .max(store.reachable_unique_nodes(&roots));
        }
        #[cfg(not(test))]
        let _ = (store, map);
    }
}

pub(crate) fn simple_beta_reduce(
    store: &mut IndexedLambda,
    params: &[Ident],
    body: NodeId,
    args: &[NodeId],
) -> Option<NodeId> {
    let indices: AHashMap<Ident, usize> = params
        .iter()
        .cloned()
        .enumerate()
        .map(|(i, id)| (id, i))
        .collect();
    let mut usages: Vec<Usage> = args
        .iter()
        .copied()
        .map(|node| Usage { node, used: false })
        .collect();
    fn replace(
        store: &IndexedLambda,
        indices: &AHashMap<Ident, usize>,
        usages: &mut [Usage],
        nodes: &[NodeId],
    ) -> Option<Vec<NodeId>> {
        nodes
            .iter()
            .map(|node| match store.view(*node) {
                NodeView::Var(id) => match indices.get(id).map(|index| &mut usages[*index]) {
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
            let body_args = replace(store, &indices, &mut usages, &body_args)?;
            append_rebuilt(store, NodeSnapshot::Prim(primitive, body_args, loc))
        }
        NodeSnapshot::Apply(function, body_args, info)
            if match store.view(function) {
                NodeView::Var(_) => true,
                NodeView::Prim(Primitive::Pfield(_, _), [base], _) => {
                    matches!(store.view(*base), NodeView::GlobalModule(_))
                }
                _ => false,
            } =>
        {
            let body_args = replace(store, &indices, &mut usages, &body_args)?;
            let function = if let NodeView::Var(id) = store.view(function) {
                match indices.get(id).map(|index| &mut usages[*index]) {
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
            append_rebuilt(store, NodeSnapshot::Apply(function, body_args, info))
        }
        _ => return None,
    };
    // `Lam_beta_reduce_util.seq_unused`: sequence the unused arguments
    // before the body, in parameter order.
    for usage in usages.iter().rev() {
        if !usage.used {
            result = append_rebuilt(store, NodeSnapshot::Sequence(usage.node, result));
        }
    }
    Some(result)
}

pub(crate) fn no_names_beta_reduce(
    store: &mut IndexedLambda,
    params: &[Ident],
    body: NodeId,
    args: &[NodeId],
) -> NodeId {
    if let Some(node) = simple_beta_reduce(store, params, body, args) {
        return node;
    }
    params
        .iter()
        .cloned()
        .zip(args.iter().copied())
        .fold(body, |body, (param, arg)| {
            append_refine_let(store, LetKind::Strict, param, arg, body)
        })
}

fn rebind(
    store: &mut IndexedLambda,
    map: &mut VariableSubstitution,
    diagnostics: &mut BetaDiagnostics,
    id_gen: &IdGenerator,
    id: &Ident,
) -> Ident {
    let fresh = id.rename(id_gen);
    let var = store.append(NodeSnapshot::Var(fresh));
    map.insert(*id, var);
    diagnostics.record(store, map);
    fresh
}

fn rewrite_bounded(
    store: &mut IndexedLambda,
    map: &mut VariableSubstitution,
    diagnostics: &mut BetaDiagnostics,
    node: NodeId,
    id_gen: &IdGenerator,
) -> NodeId {
    match store.snapshot(node) {
        NodeSnapshot::Var(id) => map.get(&id).copied().unwrap_or(node),
        NodeSnapshot::Const(_)
        | NodeSnapshot::GlobalModule(_)
        | NodeSnapshot::Break
        | NodeSnapshot::Continue => node,
        NodeSnapshot::Let(kind, id, value, body) => {
            let id = rebind(store, map, diagnostics, id_gen, &id);
            let value = rewrite_bounded(store, map, diagnostics, value, id_gen);
            let body = rewrite_bounded(store, map, diagnostics, body, id_gen);
            append_rebuilt(store, NodeSnapshot::Let(kind, id, value, body))
        }
        NodeSnapshot::LetRec(bindings, body) => {
            let fresh: Vec<_> = bindings
                .iter()
                .map(|(id, _)| rebind(store, map, diagnostics, id_gen, id))
                .collect();
            let bindings = fresh
                .into_iter()
                .zip(bindings)
                .map(|(id, (_, value))| {
                    let value = rewrite_bounded(store, map, diagnostics, value, id_gen);
                    (id, value)
                })
                .collect();
            let body = rewrite_bounded(store, map, diagnostics, body, id_gen);
            append_rebuilt(store, NodeSnapshot::LetRec(bindings, body))
        }
        NodeSnapshot::Function(arity, params, body, attr, loc) => {
            let params = params
                .iter()
                .map(|id| rebind(store, map, diagnostics, id_gen, id))
                .collect();
            let body = rewrite_bounded(store, map, diagnostics, body, id_gen);
            append_rebuilt(
                store,
                NodeSnapshot::Function(arity, params, body, attr, loc),
            )
        }
        NodeSnapshot::StaticCatch(body, exit, params, handler) => {
            let body = rewrite_bounded(store, map, diagnostics, body, id_gen);
            let params = params
                .iter()
                .map(|id| rebind(store, map, diagnostics, id_gen, id))
                .collect();
            let handler = rewrite_bounded(store, map, diagnostics, handler, id_gen);
            append_rebuilt(
                store,
                NodeSnapshot::StaticCatch(body, exit, params, handler),
            )
        }
        NodeSnapshot::TryWith(body, id, handler) => {
            let body = rewrite_bounded(store, map, diagnostics, body, id_gen);
            let id = rebind(store, map, diagnostics, id_gen, &id);
            let handler = rewrite_bounded(store, map, diagnostics, handler, id_gen);
            append_rebuilt(store, NodeSnapshot::TryWith(body, id, handler))
        }
        // lam_bounded_vars.ml: `let l1 = aux l1 in let l2 = aux l2 in try_finally l1 l2`.
        NodeSnapshot::TryFinally(body, finally) => {
            let body = rewrite_bounded(store, map, diagnostics, body, id_gen);
            let finally = rewrite_bounded(store, map, diagnostics, finally, id_gen);
            append_rebuilt(store, NodeSnapshot::TryFinally(body, finally))
        }
        NodeSnapshot::For(id, from, to, direction, body) => {
            let id = rebind(store, map, diagnostics, id_gen, &id);
            // Preserve `lam_bounded_vars.ml`'s two traversals of `l1`.
            let first_from = rewrite_bounded(store, map, diagnostics, from, id_gen);
            let to = rewrite_bounded(store, map, diagnostics, to, id_gen);
            let body = rewrite_bounded(store, map, diagnostics, body, id_gen);
            let from = rewrite_bounded(store, map, diagnostics, first_from, id_gen);
            append_rebuilt(store, NodeSnapshot::For(id, from, to, direction, body))
        }
        NodeSnapshot::ForOf(id, iterable, body) | NodeSnapshot::ForAwaitOf(id, iterable, body) => {
            let await_ = matches!(store.snapshot(node), NodeSnapshot::ForAwaitOf(_, _, _));
            let id = rebind(store, map, diagnostics, id_gen, &id);
            let iterable = rewrite_bounded(store, map, diagnostics, iterable, id_gen);
            let body = rewrite_bounded(store, map, diagnostics, body, id_gen);
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
                rewrite_bounded(store, map, diagnostics, child, id_gen)
            });
            append_rebuilt(store, mapped)
        }
    }
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
    diagnostics: &mut BetaDiagnostics,
) -> NodeId {
    if let Some(result) = simple_beta_reduce(store, params, body, args) {
        return result;
    }
    let mut bindings = Vec::new();
    let mut map = VariableSubstitution::new();
    for (param, arg) in params.iter().zip(args.iter().copied()) {
        let direct = matches!(store.view(arg), NodeView::Const(_) | NodeView::Var(_))
            || stats.is_some_and(|stats| {
                !matches!(store.view(arg), NodeView::GlobalModule(_))
                    && no_side_effects(store, arg)
                    && stats
                        .get(param)
                        .is_some_and(|stat| stat.top_and_used_zero_or_one())
            });
        if direct {
            map.insert(*param, arg);
            diagnostics.record(store, &map);
            continue;
        }
        let fresh = param.rename(id_gen);
        let fresh_var = store.append(NodeSnapshot::Var(fresh));
        bindings.push((fresh, arg));
        map.insert(*param, fresh_var);
        diagnostics.record(store, &map);
    }
    let mut result = rewrite_bounded(store, &mut map, diagnostics, body, id_gen);
    for (id, arg) in bindings.into_iter().rev() {
        register_kind(store, meta, id, arg);
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
    diagnostics: &mut BetaDiagnostics,
) -> NodeId {
    propagate(store, meta, None, params, body, args, id_gen, diagnostics)
}

pub(crate) fn propagate_beta_reduce_with_map(
    store: &mut IndexedLambda,
    meta: &mut IndexedLamStats,
    stats: &StatsMap,
    params: &[Ident],
    body: NodeId,
    args: &[NodeId],
    id_gen: &IdGenerator,
    diagnostics: &mut BetaDiagnostics,
) -> NodeId {
    propagate(
        store,
        meta,
        Some(stats),
        params,
        body,
        args,
        id_gen,
        diagnostics,
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ident::IdentFlags;

    fn ids(start: i32, count: usize) -> Vec<Ident> {
        (0..count)
            .map(|i| Ident::new(format!("p{i}"), start + i as i32, IdentFlags::NONE))
            .collect()
    }

    fn effect(name: &str) -> crate::lambda::Lambda {
        crate::lambda::Lambda::prim(
            Primitive::PjsCall {
                prim_name: name.into(),
                arg_types: vec![],
                ffi: Box::new(crate::lambda::lam_primitive::ExternalDecl::test_val("", 0)),
            },
            vec![],
            LamLoc::NONE,
        )
    }

    #[test]
    fn unused_effectful_arguments_are_evaluated_in_parameter_order() {
        let params = ids(1, 3);
        let body = crate::lambda::Lambda::prim(
            Primitive::Pidentity,
            vec![crate::lambda::Lambda::var(params[0])],
            LamLoc::NONE,
        );
        let mut store = IndexedLambda::from_lambda(body);
        let root = store.root();
        let args: Vec<_> = ["a", "b", "c"]
            .into_iter()
            .map(|name| store.append_compat_lambda(effect(name)))
            .collect();
        let reduced = simple_beta_reduce(&mut store, &params, root, &args).unwrap();
        let mut names = Vec::new();
        let mut current = store.materialize_node(reduced);
        while let crate::lambda::Lambda::Lsequence(first, rest) = current {
            if let crate::lambda::Lambda::Lprim(info) = *first
                && let Primitive::PjsCall { prim_name, .. } = info.primitive
            {
                names.push(prim_name);
            }
            current = *rest;
        }
        assert_eq!(names, vec!["b", "c"]);
    }
}
