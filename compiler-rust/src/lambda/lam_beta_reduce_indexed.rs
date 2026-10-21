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
#[cfg(test)]
use crate::location::Location;

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

fn mix(mut h: u32, mut d: u32) -> u32 {
    d = d.wrapping_mul(0xcc9e2d51);
    d = d.rotate_left(15);
    d = d.wrapping_mul(0x1b873593);
    h ^= d;
    h.rotate_left(13).wrapping_mul(5).wrapping_add(0xe6546b64)
}
fn finish(mut h: u32) -> u32 {
    h ^= h >> 16;
    h = h.wrapping_mul(0x85ebca6b);
    h ^= h >> 13;
    h = h.wrapping_mul(0xc2b2ae35);
    h ^= h >> 16;
    h & 0x3fff_ffff
}
fn ident_hash(id: &Ident) -> u32 {
    if id.stamp() != 0 {
        // The native C stub's `MIX(h, d)` receives OCaml's tagged 64-bit
        // `value d`; its macro shifts/multiplies that width before truncating
        // into the 32-bit accumulator.
        let mut tagged = (id.stamp() as u64).wrapping_mul(2).wrapping_add(1);
        tagged = tagged.wrapping_mul(0xcc9e2d51);
        tagged = (tagged << 15) | (tagged >> 17);
        tagged = tagged.wrapping_mul(0x1b873593);
        let mut h = tagged as u32;
        h = h.rotate_left(13);
        h = h.wrapping_mul(5).wrapping_add(0xe6546b64);
        return finish(h);
    }
    let bytes = id.name().as_bytes();
    let mut h = 0;
    let mut i = 0;
    while i + 4 <= bytes.len() {
        h = mix(
            h,
            u32::from_le_bytes([bytes[i], bytes[i + 1], bytes[i + 2], bytes[i + 3]]),
        );
        i += 4;
    }
    if i < bytes.len() {
        let mut word = 0;
        for (shift, byte) in bytes[i..].iter().enumerate() {
            word |= (*byte as u32) << (shift * 8);
        }
        h = mix(h, word);
    }
    finish(h ^ bytes.len() as u32)
}

/// Reproduces `Hash_ident` bucket traversal, including retained resize capacity.
fn reference_fold_order(params: &[Ident], capacity: &mut usize) -> Vec<usize> {
    let mut buckets: Vec<Vec<usize>> = vec![Vec::new(); (*capacity).max(32).next_power_of_two()];
    for (entry, id) in params.iter().enumerate() {
        let bucket = (ident_hash(id) as usize) & (buckets.len() - 1);
        buckets[bucket].insert(0, entry);
        if entry + 1 > buckets.len() << 1 {
            let mut resized = vec![Vec::new(); buckets.len() * 2];
            for old in &buckets {
                for &index in old {
                    let bucket = (ident_hash(&params[index]) as usize) & (resized.len() - 1);
                    resized[bucket].push(index);
                }
            }
            buckets = resized;
        }
    }
    *capacity = buckets.len();
    buckets.into_iter().flatten().collect()
}

pub(crate) fn simple_beta_reduce(
    store: &mut IndexedLambda,
    params: &[Ident],
    body: NodeId,
    args: &[NodeId],
    hash_capacity: &mut usize,
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
    let (mut result, fold_order) = match store.snapshot(body) {
        NodeSnapshot::Prim(primitive, body_args, loc) => {
            let fold_order = reference_fold_order(params, hash_capacity);
            let body_args = replace(store, &indices, &mut usages, &body_args)?;
            (
                append_rebuilt(store, NodeSnapshot::Prim(primitive, body_args, loc)),
                fold_order,
            )
        }
        NodeSnapshot::Apply(function, body_args, info, _)
            if match store.view(function) {
                NodeView::Var(_) => true,
                NodeView::Prim(Primitive::Pfield(_, _), [base], _) => {
                    matches!(store.view(*base), NodeView::GlobalModule(_))
                }
                _ => false,
            } =>
        {
            let fold_order = reference_fold_order(params, hash_capacity);
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
            (
                append_rebuilt(store, NodeSnapshot::Apply(function, body_args, info, false)),
                fold_order,
            )
        }
        _ => return None,
    };
    for index in fold_order {
        let usage = &usages[index];
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
    hash_capacity: &mut usize,
) -> NodeId {
    if let Some(node) = simple_beta_reduce(store, params, body, args, hash_capacity) {
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
    let var = store.append(NodeSnapshot::Var(fresh.clone()));
    map.insert(id.clone(), var);
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
    hash_capacity: &mut usize,
    diagnostics: &mut BetaDiagnostics,
) -> NodeId {
    if let Some(result) = simple_beta_reduce(store, params, body, args, hash_capacity) {
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
            map.insert(param.clone(), arg);
            diagnostics.record(store, &map);
            continue;
        }
        let fresh = param.rename(id_gen);
        let fresh_var = store.append(NodeSnapshot::Var(fresh.clone()));
        bindings.push((fresh, arg));
        map.insert(param.clone(), fresh_var);
        diagnostics.record(store, &map);
    }
    let mut result = rewrite_bounded(store, &mut map, diagnostics, body, id_gen);
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
    hash_capacity: &mut usize,
    diagnostics: &mut BetaDiagnostics,
) -> NodeId {
    propagate(
        store,
        meta,
        None,
        params,
        body,
        args,
        id_gen,
        hash_capacity,
        diagnostics,
    )
}

pub(crate) fn propagate_beta_reduce_with_map(
    store: &mut IndexedLambda,
    meta: &mut IndexedLamStats,
    stats: &StatsMap,
    params: &[Ident],
    body: NodeId,
    args: &[NodeId],
    id_gen: &IdGenerator,
    hash_capacity: &mut usize,
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
        hash_capacity,
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
                transformed_jsx: false,
            },
            vec![],
            Location::none(),
        )
    }

    #[test]
    fn unused_effectful_arguments_follow_reference_hash_fold_order() {
        let params = ids(1, 3);
        let body = crate::lambda::Lambda::prim(
            Primitive::Pidentity,
            vec![crate::lambda::Lambda::var(params[0].clone())],
            Location::none(),
        );
        let mut store = IndexedLambda::from_lambda(body);
        let root = store.root();
        let args: Vec<_> = ["a", "b", "c"]
            .into_iter()
            .map(|name| store.append_compat_lambda(effect(name)))
            .collect();
        let mut capacity = 32;
        let reduced = simple_beta_reduce(&mut store, &params, root, &args, &mut capacity).unwrap();
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
        assert_eq!(names, vec!["c", "b"]);
    }

    #[test]
    fn failed_simple_reduction_retains_reference_resize_capacity() {
        let params = ids(1, 65);
        let body = crate::lambda::Lambda::prim(
            Primitive::Paddint,
            vec![
                crate::lambda::Lambda::var(params[0].clone()),
                crate::lambda::Lambda::var(params[0].clone()),
            ],
            Location::none(),
        );
        let mut store = IndexedLambda::from_lambda(body);
        let root = store.root();
        let args: Vec<_> = (0..65)
            .map(|i| {
                store.append_compat_lambda(crate::lambda::Lambda::const_(
                    crate::lambda::Constant::int(i),
                ))
            })
            .collect();
        let mut capacity = 32;
        assert!(simple_beta_reduce(&mut store, &params, root, &args, &mut capacity).is_none());
        assert_eq!(capacity, 64);
    }

    #[test]
    fn hash_ident_fold_order_preserves_collisions_resize_and_clear_capacity() {
        let mut capacity = 32;
        assert_eq!(
            reference_fold_order(&ids(1, 6), &mut capacity),
            vec![3, 1, 5, 2, 4, 0]
        );
        let expected = vec![
            13, 65, 0, 32, 50, 3, 42, 58, 57, 64, 39, 28, 34, 49, 4, 30, 25, 23, 20, 1, 61, 69, 8,
            6, 37, 47, 18, 38, 46, 5, 9, 66, 60, 52, 55, 56, 54, 31, 59, 14, 16, 53, 45, 63, 27,
            29, 21, 24, 11, 44, 12, 40, 36, 33, 10, 62, 48, 51, 35, 68, 26, 22, 15, 67, 43, 41, 2,
            19, 17, 7,
        ];
        assert_eq!(reference_fold_order(&ids(7, 70), &mut capacity), expected);
        assert_eq!(capacity, 64);
        assert_eq!(
            reference_fold_order(&ids(77, 6), &mut capacity),
            vec![0, 2, 4, 5, 1, 3]
        );
    }
}
