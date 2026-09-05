//! Indexed port of `lam_exit_count.ml`, `lam_subst.ml`, and
//! `lam_pass_exits.ml`. This is an inactive migration pass: one owning context
//! keeps the canonical root, append-only arena, and ID-bearing metadata.

use ahash::AHashMap;

use crate::context::IdGenerator;
use crate::ident::Ident;
use crate::lambda::indexed::{IndexedLambda, IndexedLambdaContext, NodeId, NodeSnapshot, NodeView};
use crate::lambda::lam_analysis::EXIT_INLINE_SIZE;
use crate::lambda::lam_compat::LetKind;
use crate::lambda::lam_constant::Constant;
use crate::lambda::lam_pass_collect_indexed::indexed_size;
use crate::lambda::lam_primitive::Primitive;

pub(crate) type ExitCounts = AHashMap<i32, u32>;
struct ExitSubstitutions {
    entries: AHashMap<i32, (Vec<Ident>, NodeId)>,
    #[cfg(test)]
    peak_unique_nodes: usize,
}

impl ExitSubstitutions {
    fn new() -> Self {
        Self {
            entries: AHashMap::new(),
            #[cfg(test)]
            peak_unique_nodes: 0,
        }
    }

    fn get(&self, exit: &i32) -> Option<&(Vec<Ident>, NodeId)> {
        self.entries.get(exit)
    }

    fn insert(&mut self, store: &IndexedLambda, exit: i32, value: (Vec<Ident>, NodeId)) {
        self.entries.insert(exit, value);
        #[cfg(test)]
        {
            let roots = self
                .entries
                .values()
                .map(|(_, handler)| *handler)
                .collect::<Vec<_>>();
            self.peak_unique_nodes = self
                .peak_unique_nodes
                .max(store.reachable_unique_nodes(&roots));
        }
    }
}

type VariableSubstitution = AHashMap<Ident, NodeId>;

fn increment(counts: &mut ExitCounts, exit: i32) {
    *counts.entry(exit).or_insert(0) += 1;
}

fn count_exit(counts: &ExitCounts, exit: i32) -> u32 {
    counts.get(&exit).copied().unwrap_or(0)
}

/// Exact traversal order from `compiler/core/lam_exit_count.ml:51-110`.
pub(crate) fn count_exits(store: &IndexedLambda, root: NodeId) -> ExitCounts {
    fn count(store: &IndexedLambda, node: NodeId, counts: &mut ExitCounts) {
        match store.view(node) {
            NodeView::StaticRaise(exit, args) => {
                increment(counts, exit);
                for arg in args {
                    count(store, *arg, counts);
                }
            }
            NodeView::StaticCatch(body, exit, _, handler) => {
                count(store, body, counts);
                if count_exit(counts, exit) > 0 {
                    count(store, handler, counts);
                }
            }
            NodeView::StringSwitch(scrutinee, cases, default) => {
                count(store, scrutinee, counts);
                for (_, body) in cases {
                    count(store, *body, counts);
                }
                if let Some(default) = default {
                    count(store, default, counts);
                }
            }
            NodeView::Var(_)
            | NodeView::GlobalModule(_, _)
            | NodeView::Const(_)
            | NodeView::Break
            | NodeView::Continue => {}
            NodeView::Apply(function, args, _, _) => {
                count(store, function, counts);
                for arg in args {
                    count(store, *arg, counts);
                }
            }
            NodeView::Function(_, _, body, _) => count(store, body, counts),
            NodeView::Let(_, _, value, body) => {
                // OCaml deliberately visits the body before the value.
                count(store, body, counts);
                count(store, value, counts);
            }
            NodeView::LetRec(bindings, body) => {
                for (_, value) in bindings {
                    count(store, *value, counts);
                }
                count(store, body, counts);
            }
            NodeView::Prim(_, args, _) => {
                for arg in args {
                    count(store, *arg, counts);
                }
            }
            NodeView::Switch {
                scrutinee,
                consts_full,
                consts,
                blocks_full,
                blocks,
                fail_action,
                ..
            } => {
                if let Some(fail) = fail_action {
                    count(store, fail, counts);
                    if !consts_full && !blocks_full {
                        count(store, fail, counts);
                    }
                }
                count(store, scrutinee, counts);
                for (_, body) in consts {
                    count(store, *body, counts);
                }
                for (_, body) in blocks {
                    count(store, *body, counts);
                }
            }
            NodeView::TryWith(body, _, handler) => {
                count(store, body, counts);
                count(store, handler, counts);
            }
            NodeView::IfThenElse(a, b, c) | NodeView::For(_, a, b, _, c) => {
                count(store, a, counts);
                count(store, b, counts);
                count(store, c, counts);
            }
            NodeView::Sequence(a, b)
            | NodeView::While(a, b)
            | NodeView::ForOf(_, a, b)
            | NodeView::ForAwaitOf(_, a, b) => {
                count(store, a, counts);
                count(store, b, counts);
            }
            NodeView::Assign(_, value) => count(store, value, counts),
        }
    }
    let mut counts = ExitCounts::new();
    count(store, root, &mut counts);
    counts
}

/// `Lam_pass_exits.no_bounded_variables`, preserving short-circuit order.
pub(crate) fn no_bounded_variables(store: &IndexedLambda, node: NodeId) -> bool {
    match store.view(node) {
        NodeView::Var(_)
        | NodeView::GlobalModule(_, _)
        | NodeView::Const(_)
        | NodeView::Break
        | NodeView::Continue => true,
        NodeView::Assign(_, value) => no_bounded_variables(store, value),
        NodeView::Apply(function, args, _, _) => {
            no_bounded_variables(store, function)
                && args.iter().all(|node| no_bounded_variables(store, *node))
        }
        NodeView::Prim(_, args, _) | NodeView::StaticRaise(_, args) => {
            args.iter().all(|node| no_bounded_variables(store, *node))
        }
        NodeView::Switch {
            scrutinee,
            consts,
            blocks,
            fail_action,
            ..
        } => {
            no_bounded_variables(store, scrutinee)
                && consts
                    .iter()
                    .all(|(_, node)| no_bounded_variables(store, *node))
                && blocks
                    .iter()
                    .all(|(_, node)| no_bounded_variables(store, *node))
                && fail_action.is_none_or(|node| no_bounded_variables(store, node))
        }
        NodeView::StringSwitch(scrutinee, cases, default) => {
            no_bounded_variables(store, scrutinee)
                && cases
                    .iter()
                    .all(|(_, node)| no_bounded_variables(store, *node))
                && default.is_none_or(|node| no_bounded_variables(store, node))
        }
        NodeView::IfThenElse(a, b, c) => {
            no_bounded_variables(store, a)
                && no_bounded_variables(store, b)
                && no_bounded_variables(store, c)
        }
        NodeView::Sequence(a, b) | NodeView::While(a, b) => {
            no_bounded_variables(store, a) && no_bounded_variables(store, b)
        }
        NodeView::StaticCatch(body, _, params, handler) => {
            params.is_empty()
                && no_bounded_variables(store, body)
                && no_bounded_variables(store, handler)
        }
        NodeView::Function(_, params, body, _) => {
            params.is_empty() && no_bounded_variables(store, body)
        }
        NodeView::LetRec(bindings, body) => {
            bindings.is_empty() && no_bounded_variables(store, body)
        }
        NodeView::Let(_, _, _, _)
        | NodeView::TryWith(_, _, _)
        | NodeView::For(_, _, _, _, _)
        | NodeView::ForOf(_, _, _)
        | NodeView::ForAwaitOf(_, _, _) => false,
    }
}

fn list_eq_approx(store: &IndexedLambda, left: &[NodeId], right: &[NodeId]) -> bool {
    left.len() == right.len()
        && left
            .iter()
            .zip(right)
            .all(|(left, right)| eq_approx(store, *left, *right))
}

fn eq_approx(store: &IndexedLambda, left: NodeId, right: NodeId) -> bool {
    match (store.view(left), store.view(right)) {
        (NodeView::GlobalModule(a, ad), NodeView::GlobalModule(b, bd)) => a.same(b) && ad == bd,
        (NodeView::Var(a), NodeView::Var(b)) => a.same(b),
        (NodeView::Const(a), NodeView::Const(b)) => a.eq_approx(b),
        (NodeView::Apply(af, aa, _, _), NodeView::Apply(bf, ba, _, _)) => {
            eq_approx(store, af, bf) && list_eq_approx(store, aa, ba)
        }
        (NodeView::IfThenElse(a1, a2, a3), NodeView::IfThenElse(b1, b2, b3)) => {
            eq_approx(store, a1, b1) && eq_approx(store, a2, b2) && eq_approx(store, a3, b3)
        }
        (NodeView::Sequence(a1, a2), NodeView::Sequence(b1, b2))
        | (NodeView::While(a1, a2), NodeView::While(b1, b2)) => {
            eq_approx(store, a1, b1) && eq_approx(store, a2, b2)
        }
        (NodeView::Break, NodeView::Break) | (NodeView::Continue, NodeView::Continue) => true,
        (NodeView::Assign(a, av), NodeView::Assign(b, bv)) => a.same(b) && eq_approx(store, av, bv),
        (NodeView::StaticRaise(a, aa), NodeView::StaticRaise(b, ba)) => {
            a == b && list_eq_approx(store, aa, ba)
        }
        (NodeView::Prim(ap, aa, _), NodeView::Prim(bp, ba, _)) => {
            ap.eq_approx(bp) && list_eq_approx(store, aa, ba)
        }
        (NodeView::StringSwitch(aa, ac, ad), NodeView::StringSwitch(ba, bc, bd)) => {
            eq_approx(store, aa, ba)
                && match (ad, bd) {
                    (None, None) => true,
                    (Some(a), Some(b)) => eq_approx(store, a, b),
                    _ => false,
                }
                && ac.len() == bc.len()
                && ac
                    .iter()
                    .zip(bc)
                    .all(|((ak, av), (bk, bv))| ak == bk && eq_approx(store, *av, *bv))
        }
        _ => false,
    }
}

fn boolean_location(store: &IndexedLambda, node: NodeId) -> Option<crate::location::Location> {
    match store.view(node) {
        NodeView::Prim(
            Primitive::Pnot
            | Primitive::Psequand
            | Primitive::Psequor
            | Primitive::Pisout(_)
            | Primitive::PisNotNone
            | Primitive::Pobjcomp(_)
            | Primitive::Pboolcomp(_)
            | Primitive::Pintcomp(_)
            | Primitive::Pfloatcomp(_)
            | Primitive::Pbigintcomp(_)
            | Primitive::Pstringcomp(_),
            _,
            loc,
        ) => Some(loc.clone()),
        _ => None,
    }
}

fn is_assert_false(store: &IndexedLambda, node: NodeId) -> bool {
    matches!(
        store.view(node),
        NodeView::Const(Constant::Int {
            comment: Some(crate::lambda::lam_constant::PointerInfo::AssertFalse),
            ..
        })
    )
}
fn is_true(store: &IndexedLambda, node: NodeId) -> bool {
    matches!(store.view(node), NodeView::Const(Constant::JsTrue))
}
fn is_false(store: &IndexedLambda, node: NodeId) -> bool {
    matches!(store.view(node), NodeView::Const(Constant::JsFalse))
}

fn append_not(store: &mut IndexedLambda, loc: crate::location::Location, node: NodeId) -> NodeId {
    if let NodeSnapshot::Prim(Primitive::Pintcomp(crate::lambda::Comparison::Neq), args, old_loc) =
        store.snapshot(node)
    {
        store.append(NodeSnapshot::Prim(
            Primitive::Pintcomp(crate::lambda::Comparison::Eq),
            args,
            old_loc,
        ))
    } else {
        append_rebuilt(store, NodeSnapshot::Prim(Primitive::Pnot, vec![node], loc))
    }
}

fn complete_range(cases: &[(crate::lambda::SwitchKey, NodeId)], start: i32, finish: i32) -> bool {
    match cases.split_first() {
        None => finish < start,
        Some(((crate::lambda::SwitchKey::Int(value), _), rest)) => {
            start <= finish && *value == start && complete_range(rest, start + 1, finish)
        }
        Some(_) => false,
    }
}

fn append_if(
    store: &mut IndexedLambda,
    condition: NodeId,
    then_node: NodeId,
    else_node: NodeId,
) -> NodeId {
    if let NodeView::Const(value) = store.view(condition) {
        let truthy = match value {
            Constant::Int { i, .. } => Some(*i != 0),
            Constant::Char(value) => Some(*value != 0),
            Constant::JsFalse
            | Constant::JsNull
            | Constant::ModuleAlias
            | Constant::JsUndefined { .. } => Some(false),
            Constant::JsTrue
            | Constant::String { .. }
            | Constant::ImmString(_)
            | Constant::Pointer(_)
            | Constant::Float(_)
            | Constant::BigInt { .. }
            | Constant::Block { .. } => Some(true),
            Constant::Some(inner) => {
                fn inner_truthy(value: &Constant) -> Option<bool> {
                    match value {
                        Constant::Some(inner) => inner_truthy(inner),
                        Constant::Int { i, .. } => Some(*i != 0),
                        Constant::Char(value) => Some(*value != 0),
                        Constant::JsFalse
                        | Constant::JsNull
                        | Constant::ModuleAlias
                        | Constant::JsUndefined { .. } => Some(false),
                        Constant::JsTrue
                        | Constant::String { .. }
                        | Constant::ImmString(_)
                        | Constant::Pointer(_)
                        | Constant::Float(_)
                        | Constant::BigInt { .. }
                        | Constant::Block { .. } => Some(true),
                        Constant::Constructor(tag) => match &tag.tag_type {
                            None => Some(tag.name != "[]"),
                            Some(crate::types::VariantTagType::String(value)) => {
                                Some(!value.is_empty())
                            }
                            Some(crate::types::VariantTagType::Int(value)) => Some(*value != 0),
                            Some(crate::types::VariantTagType::Bool(value)) => Some(*value),
                            Some(
                                crate::types::VariantTagType::Null
                                | crate::types::VariantTagType::Undefined,
                            ) => Some(false),
                            Some(
                                crate::types::VariantTagType::Float(_)
                                | crate::types::VariantTagType::BigInt(_)
                                | crate::types::VariantTagType::Untagged(_),
                            ) => None,
                        },
                        Constant::NativeInt { .. } => None,
                    }
                }
                inner_truthy(inner)
            }
            Constant::Constructor(tag) => match &tag.tag_type {
                None => Some(tag.name != "[]"),
                Some(crate::types::VariantTagType::String(value)) => Some(!value.is_empty()),
                Some(crate::types::VariantTagType::Int(value)) => Some(*value != 0),
                Some(crate::types::VariantTagType::Bool(value)) => Some(*value),
                Some(
                    crate::types::VariantTagType::Null | crate::types::VariantTagType::Undefined,
                ) => Some(false),
                Some(
                    crate::types::VariantTagType::Float(_)
                    | crate::types::VariantTagType::BigInt(_)
                    | crate::types::VariantTagType::Untagged(_),
                ) => None,
            },
            // OCaml Lambda has no native-int constant in this branch.
            Constant::NativeInt { .. } => None,
        };
        return match truthy {
            Some(true) => then_node,
            Some(false) => else_node,
            None => store.append(NodeSnapshot::IfThenElse(condition, then_node, else_node)),
        };
    }
    if is_assert_false(store, else_node) {
        return append_rebuilt(store, NodeSnapshot::Sequence(condition, then_node));
    }
    if is_assert_false(store, then_node) {
        return append_rebuilt(store, NodeSnapshot::Sequence(condition, else_node));
    }
    if is_true(store, then_node) && is_false(store, else_node) {
        return if boolean_location(store, condition).is_some() {
            condition
        } else {
            store.append(NodeSnapshot::IfThenElse(condition, then_node, else_node))
        };
    }
    if is_false(store, then_node) && is_true(store, else_node) {
        return match boolean_location(store, condition) {
            Some(loc) => append_not(store, loc, condition),
            None => store.append(NodeSnapshot::IfThenElse(condition, then_node, else_node)),
        };
    }
    if matches!(
        store.view(then_node),
        NodeView::Prim(Primitive::Praise, _, _)
    ) {
        return if matches!(store.view(else_node), NodeView::Const(_)) {
            store.append(NodeSnapshot::IfThenElse(condition, then_node, else_node))
        } else {
            let unit = store.append(NodeSnapshot::Const(Constant::JsUndefined { is_unit: true }));
            let first = store.append(NodeSnapshot::IfThenElse(condition, then_node, unit));
            append_rebuilt(store, NodeSnapshot::Sequence(first, else_node))
        };
    }
    match store.snapshot(condition) {
        NodeSnapshot::Prim(Primitive::Pisout(offset), args, loc) => {
            if let [range_node, variable_node] = args.as_slice()
                && let NodeView::Const(Constant::Int { i: range, .. }) = store.view(*range_node)
                && let NodeView::Var(variable) = store.view(*variable_node)
                && let NodeSnapshot::Switch {
                    scrutinee,
                    consts_full: _,
                    consts,
                    blocks_full,
                    blocks,
                    fail_action,
                    dispatch,
                } = store.snapshot(else_node)
                && let NodeView::Var(other) = store.view(scrutinee)
                && blocks.is_empty()
                && blocks_full
                && fail_action.is_none()
                && variable.same(other)
                && complete_range(&consts, -offset, *range - offset)
            {
                return store.append(NodeSnapshot::Switch {
                    scrutinee,
                    consts_full: false,
                    consts,
                    blocks_full,
                    blocks,
                    fail_action: Some(then_node),
                    dispatch,
                });
            }
            let condition = store.append(NodeSnapshot::Prim(Primitive::Pisout(offset), args, loc));
            store.append(NodeSnapshot::IfThenElse(condition, then_node, else_node))
        }
        NodeSnapshot::Prim(Primitive::Pisint, args, loc) => {
            append_pisint_if(store, args, loc, then_node, else_node)
        }
        _ => store.append(NodeSnapshot::IfThenElse(condition, then_node, else_node)),
    }
}

fn append_pisint_if(
    store: &mut IndexedLambda,
    args: Vec<NodeId>,
    loc: crate::location::Location,
    then_node: NodeId,
    else_node: NodeId,
) -> NodeId {
    let [variable_node] = args.as_slice() else {
        let condition = store.append(NodeSnapshot::Prim(Primitive::Pisint, args, loc));
        return store.append(NodeSnapshot::IfThenElse(condition, then_node, else_node));
    };
    let NodeView::Var(variable) = store.view(*variable_node) else {
        let condition = store.append(NodeSnapshot::Prim(Primitive::Pisint, args, loc));
        return store.append(NodeSnapshot::IfThenElse(condition, then_node, else_node));
    };
    if let NodeView::IfThenElse(predicate, _, branch_false) = store.view(then_node)
        && let NodeView::Prim(Primitive::Pintcomp(crate::lambda::Comparison::Eq), [lhs, rhs], _) =
            store.view(predicate)
        && matches!(store.view(*lhs), NodeView::Var(id) if variable.same(id))
        && matches!(store.view(*rhs), NodeView::Const(_))
        && eq_approx(store, branch_false, else_node)
    {
        return then_node;
    }
    if let NodeView::Prim(Primitive::Pintcomp(crate::lambda::Comparison::Eq), [lhs, rhs], _) =
        store.view(then_node)
        && matches!(store.view(*lhs), NodeView::Var(id) if variable.same(id))
        && matches!(store.view(*rhs), NodeView::Const(_))
        && is_false(store, else_node)
    {
        return then_node;
    }
    if let NodeView::IfThenElse(predicate, branch_true, branch_false) = store.view(then_node)
        && let NodeSnapshot::Prim(
            Primitive::Pintcomp(crate::lambda::Comparison::Neq),
            predicate_args,
            predicate_loc,
        ) = store.snapshot(predicate)
        && let [lhs, rhs] = predicate_args.as_slice()
        && matches!(store.view(*lhs), NodeView::Var(id) if variable.same(id))
        && matches!(store.view(*rhs), NodeView::Const(_))
        && eq_approx(store, branch_true, else_node)
    {
        let predicate = store.append(NodeSnapshot::Prim(
            Primitive::Pintcomp(crate::lambda::Comparison::Eq),
            predicate_args,
            predicate_loc,
        ));
        return store.append(NodeSnapshot::IfThenElse(
            predicate,
            branch_false,
            branch_true,
        ));
    }
    if let NodeSnapshot::Prim(
        Primitive::Pintcomp(crate::lambda::Comparison::Neq),
        predicate_args,
        predicate_loc,
    ) = store.snapshot(then_node)
        && let [lhs, rhs] = predicate_args.as_slice()
        && matches!(store.view(*lhs), NodeView::Var(id) if variable.same(id))
        && matches!(store.view(*rhs), NodeView::Const(_))
        && is_true(store, else_node)
    {
        return store.append(NodeSnapshot::Prim(
            Primitive::Pintcomp(crate::lambda::Comparison::Neq),
            predicate_args,
            predicate_loc,
        ));
    }
    if let NodeSnapshot::Prim(Primitive::Pnot, outer_args, _) = store.snapshot(then_node)
        && let [inner] = outer_args.as_slice()
        && let NodeSnapshot::Prim(
            Primitive::Pintcomp(crate::lambda::Comparison::Eq),
            predicate_args,
            predicate_loc,
        ) = store.snapshot(*inner)
        && let [lhs, rhs] = predicate_args.as_slice()
        && matches!(store.view(*lhs), NodeView::Var(id) if variable.same(id))
        && matches!(store.view(*rhs), NodeView::Const(_))
        && is_true(store, else_node)
    {
        return store.append(NodeSnapshot::Prim(
            Primitive::Pintcomp(crate::lambda::Comparison::Neq),
            predicate_args,
            predicate_loc,
        ));
    }
    let condition = store.append(NodeSnapshot::Prim(Primitive::Pisint, args, loc));
    store.append(NodeSnapshot::IfThenElse(condition, then_node, else_node))
}

fn append_rebuilt(store: &mut IndexedLambda, node: NodeSnapshot) -> NodeId {
    match node {
        NodeSnapshot::Apply(function, args, info, jsx) => {
            fn eta_args(
                store: &IndexedLambda,
                params: &[Ident],
                inner: &[NodeId],
                outer: &[NodeId],
            ) -> Option<Vec<NodeId>> {
                if params.len() != inner.len() || params.len() != outer.len() {
                    return None;
                }
                params.iter().zip(inner).all(|(param, node)| {
                    matches!(store.view(*node), NodeView::Var(id) if param.same(id))
                }).then(|| outer.to_vec())
            }
            if let NodeSnapshot::Function(_, params, body, _) = store.snapshot(function) {
                match store.snapshot(body) {
                    NodeSnapshot::Prim(primitive, inner, _)
                        if !matches!(
                            primitive,
                            Primitive::PnullToOpt
                                | Primitive::PnullUndefinedToOpt
                                | Primitive::PisNull
                                | Primitive::PisNullUndefined
                                | Primitive::Ptypeof
                        ) =>
                    {
                        if let Some(args) = eta_args(store, &params, &inner, &args) {
                            return store.append(NodeSnapshot::Prim(primitive, args, info.loc));
                        }
                    }
                    NodeSnapshot::Prim(
                        wrapper @ (Primitive::PnullToOpt
                        | Primitive::PnullUndefinedToOpt
                        | Primitive::PisNull
                        | Primitive::PisNullUndefined
                        | Primitive::Ptypeof),
                        wrapped,
                        _,
                    ) => {
                        if let [inner] = wrapped.as_slice()
                            && let NodeSnapshot::Prim(inner_primitive, inner_args, _) =
                                store.snapshot(*inner)
                        {
                            if let Some(args) = eta_args(store, &params, &inner_args, &args) {
                                let inner = store.append(NodeSnapshot::Prim(
                                    inner_primitive,
                                    args,
                                    info.loc.clone(),
                                ));
                                return store.append(NodeSnapshot::Prim(
                                    wrapper,
                                    vec![inner],
                                    info.loc,
                                ));
                            }
                        } else if let Some(args) = eta_args(store, &params, &wrapped, &args) {
                            return store.append(NodeSnapshot::Prim(wrapper, args, info.loc));
                        }
                    }
                    NodeSnapshot::Sequence(first, second) => {
                        if let NodeSnapshot::Prim(primitive, inner, _) = store.snapshot(first)
                            && matches!(store.view(second), NodeView::Const(_))
                            && let Some(args) = eta_args(store, &params, &inner, &args)
                        {
                            let call = store.append(NodeSnapshot::Prim(primitive, args, info.loc));
                            return store.append(NodeSnapshot::Sequence(call, second));
                        }
                    }
                    _ => {}
                }
            }
            if let NodeSnapshot::Let(kind, id, value, body) = store.snapshot(function)
                && matches!(store.view(body), NodeView::Function(_, _, _, _))
            {
                let apply = append_rebuilt(store, NodeSnapshot::Apply(body, args, info, jsx));
                return store.append(NodeSnapshot::Let(kind, id, value, apply));
            }
            store.append(NodeSnapshot::Apply(function, args, info, jsx))
        }
        NodeSnapshot::Prim(
            Primitive::Pmakeblock(crate::lambda::TagInfo::Module(fields), mutable),
            args,
            loc,
        ) => {
            let source = (!fields.is_empty() && fields.len() == args.len())
                .then(|| args.first())
                .flatten()
                .and_then(|first| match store.view(*first) {
                    NodeView::Prim(
                        Primitive::Pfield(0, crate::lambda::FieldDbgInfo::Module { name }),
                        [source],
                        _,
                    ) if name == &fields[0] => match store.view(*source) {
                        NodeView::Var(id) | NodeView::GlobalModule(id, _) => {
                            Some((*source, id.clone()))
                        }
                        _ => None,
                    },
                    _ => None,
                });
            let reconstructs_source = source.as_ref().is_some_and(|(_, source_id)| {
                args.iter().zip(fields.iter()).enumerate().all(|(index, (arg, expected_name))| {
                    matches!(store.view(*arg), NodeView::Prim(Primitive::Pfield(position, crate::lambda::FieldDbgInfo::Module { name }), [base], _)
                        if *position as usize == index && name == expected_name
                            && matches!(store.view(*base), NodeView::Var(id) | NodeView::GlobalModule(id, _) if id.same(source_id)))
                })
            });
            if reconstructs_source {
                source.expect("checked source").0
            } else {
                store.append(NodeSnapshot::Prim(
                    Primitive::Pmakeblock(crate::lambda::TagInfo::Module(fields), mutable),
                    args,
                    loc,
                ))
            }
        }
        NodeSnapshot::Prim(primitive, args, loc)
            if args
                .iter()
                .all(|node| matches!(store.view(*node), NodeView::Const(_))) =>
        {
            if let (
                Primitive::Pintcomp(
                    operation @ (crate::lambda::Comparison::Eq | crate::lambda::Comparison::Neq),
                ),
                [left, right],
            ) = (&primitive, args.as_slice())
                && let (
                    NodeView::Const(Constant::Constructor(left)),
                    NodeView::Const(Constant::Constructor(right)),
                ) = (store.view(*left), store.view(*right))
                && left.tag_type.is_none()
                && right.tag_type.is_none()
            {
                let equal = left.name == right.name;
                let result = match operation {
                    crate::lambda::Comparison::Eq => equal,
                    crate::lambda::Comparison::Neq => !equal,
                    _ => unreachable!(),
                };
                return store.append(NodeSnapshot::Const(if result {
                    Constant::JsTrue
                } else {
                    Constant::JsFalse
                }));
            }
            let lambda_args = args
                .iter()
                .map(|node| match store.view(*node) {
                    NodeView::Const(value) => crate::lambda::Lambda::Lconst(value.clone()),
                    _ => unreachable!(),
                })
                .collect::<Vec<_>>();
            match crate::lambda::Lambda::prim(primitive.clone(), lambda_args, loc.clone()) {
                crate::lambda::Lambda::Lconst(value) => store.append(NodeSnapshot::Const(value)),
                _ => store.append(NodeSnapshot::Prim(primitive, args, loc)),
            }
        }
        NodeSnapshot::Switch {
            scrutinee,
            consts_full,
            consts,
            blocks_full,
            blocks,
            fail_action,
            dispatch,
        } => {
            let known_constant = matches!(
                store.view(scrutinee),
                NodeView::Const(
                    Constant::Constructor(_) | Constant::Int { .. } | Constant::Block { .. }
                )
            );
            let selected = match store.view(scrutinee) {
                NodeView::Const(Constant::Constructor(tag)) => consts.iter().find(|(key, _)| matches!(key, crate::lambda::SwitchKey::Constructor(crate::types::VariantConstructorCase::Constant(candidate)) if candidate == tag)).map(|(_, node)| *node),
                NodeView::Const(Constant::Int { i, comment }) => consts.iter().find(|(key, _)| {
                    matches!(key, crate::lambda::SwitchKey::Int(value) if value == i)
                        || comment.is_none() && matches!(key,
                            crate::lambda::SwitchKey::Constructor(
                                crate::types::VariantConstructorCase::Constant(tag)
                            ) if matches!(tag.tag_type, Some(crate::types::VariantTagType::Int(value)) if value == *i)
                        )
                }).map(|(_, node)| *node),
                NodeView::Const(Constant::Block { tag_info, .. }) => {
                    let runtime = match tag_info {
                        crate::lambda::TagInfo::Constructor { runtime, .. } | crate::lambda::TagInfo::RecordInlined { runtime, .. } => Some(runtime),
                        _ => None,
                    };
                    blocks.iter().find(|(key, _)| matches!((key, runtime), (crate::lambda::SwitchKey::Constructor(crate::types::VariantConstructorCase::Block(candidate)), Some(runtime)) if &candidate.runtime == runtime)).map(|(_, node)| *node)
                }
                _ => None,
            };
            if known_constant {
                if let Some(selected) = selected.or(fail_action) {
                    return selected;
                }
            }
            store.append(NodeSnapshot::Switch {
                scrutinee,
                consts_full,
                consts,
                blocks_full,
                blocks,
                fail_action,
                dispatch,
            })
        }
        NodeSnapshot::StringSwitch(scrutinee, cases, default) => {
            let known_constant = matches!(
                store.view(scrutinee),
                NodeView::Const(Constant::String {
                    delim: None | Some(crate::lambda::lam_constant::StringDelim::NoQuotes),
                    ..
                }) | NodeView::Const(Constant::ImmString(_))
            );
            let selected = match store.view(scrutinee) {
                NodeView::Const(Constant::String {
                    s,
                    delim: None | Some(crate::lambda::lam_constant::StringDelim::NoQuotes),
                })
                | NodeView::Const(Constant::ImmString(s)) => cases
                    .iter()
                    .find(|(key, _)| key == s)
                    .map(|(_, node)| *node),
                _ => None,
            };
            if known_constant {
                if let Some(selected) = selected.or(default) {
                    return selected;
                }
            }
            store.append(NodeSnapshot::StringSwitch(scrutinee, cases, default))
        }
        NodeSnapshot::IfThenElse(condition, then_node, else_node) => {
            append_if(store, condition, then_node, else_node)
        }
        NodeSnapshot::Sequence(first, second) => match store.snapshot(first) {
            NodeSnapshot::Prim(Primitive::Pmakeblock(_, _), args, _) if !args.is_empty() => {
                let mut args = args.into_iter();
                let mut result = args.next().expect("non-empty makeblock args");
                for arg in args {
                    result = append_rebuilt(store, NodeSnapshot::Sequence(result, arg));
                }
                append_rebuilt(store, NodeSnapshot::Sequence(result, second))
            }
            NodeSnapshot::Prim(Primitive::PnullToOpt | Primitive::PnullUndefinedToOpt, args, _)
                if args.len() == 1 =>
            {
                append_rebuilt(store, NodeSnapshot::Sequence(args[0], second))
            }
            _ => store.append(NodeSnapshot::Sequence(first, second)),
        },
        node => store.append(node),
    }
}

fn substitute(
    store: &mut IndexedLambda,
    substitutions: &VariableSubstitution,
    node: NodeId,
) -> NodeId {
    if substitutions.is_empty() {
        return node;
    }
    match store.snapshot(node) {
        NodeSnapshot::Var(id) => substitutions.get(&id).copied().unwrap_or(node),
        NodeSnapshot::Const(_)
        | NodeSnapshot::GlobalModule(_, _)
        | NodeSnapshot::Break
        | NodeSnapshot::Continue => node,
        snapshot => {
            let mapped = map_children(store, snapshot, |store, child| {
                substitute(store, substitutions, child)
            });
            append_rebuilt(store, mapped)
        }
    }
}

fn map_children(
    store: &mut IndexedLambda,
    node: NodeSnapshot,
    mut map: impl FnMut(&mut IndexedLambda, NodeId) -> NodeId,
) -> NodeSnapshot {
    match node {
        NodeSnapshot::Apply(f, args, info, jsx) => NodeSnapshot::Apply(
            map(store, f),
            args.into_iter().map(|x| map(store, x)).collect(),
            info,
            jsx,
        ),
        NodeSnapshot::Function(a, p, body, attr) => {
            NodeSnapshot::Function(a, p, map(store, body), attr)
        }
        NodeSnapshot::Let(k, id, value, body) => {
            NodeSnapshot::Let(k, id, map(store, value), map(store, body))
        }
        NodeSnapshot::LetRec(bindings, body) => NodeSnapshot::LetRec(
            bindings
                .into_iter()
                .map(|(id, x)| (id, map(store, x)))
                .collect(),
            map(store, body),
        ),
        NodeSnapshot::Prim(p, args, loc) => {
            NodeSnapshot::Prim(p, args.into_iter().map(|x| map(store, x)).collect(), loc)
        }
        NodeSnapshot::Switch {
            scrutinee,
            consts_full,
            consts,
            blocks_full,
            blocks,
            fail_action,
            dispatch,
        } => NodeSnapshot::Switch {
            scrutinee: map(store, scrutinee),
            consts_full,
            consts: consts
                .into_iter()
                .map(|(k, x)| (k, map(store, x)))
                .collect(),
            blocks_full,
            blocks: blocks
                .into_iter()
                .map(|(k, x)| (k, map(store, x)))
                .collect(),
            fail_action: fail_action.map(|x| map(store, x)),
            dispatch,
        },
        NodeSnapshot::StringSwitch(s, cases, default) => NodeSnapshot::StringSwitch(
            map(store, s),
            cases.into_iter().map(|(k, x)| (k, map(store, x))).collect(),
            default.map(|x| map(store, x)),
        ),
        NodeSnapshot::StaticRaise(i, args) => {
            NodeSnapshot::StaticRaise(i, args.into_iter().map(|x| map(store, x)).collect())
        }
        NodeSnapshot::StaticCatch(body, i, ids, handler) => {
            NodeSnapshot::StaticCatch(map(store, body), i, ids, map(store, handler))
        }
        NodeSnapshot::TryWith(body, id, handler) => {
            NodeSnapshot::TryWith(map(store, body), id, map(store, handler))
        }
        NodeSnapshot::IfThenElse(a, b, c) => {
            NodeSnapshot::IfThenElse(map(store, a), map(store, b), map(store, c))
        }
        NodeSnapshot::Sequence(a, b) => NodeSnapshot::Sequence(map(store, a), map(store, b)),
        NodeSnapshot::While(a, b) => NodeSnapshot::While(map(store, a), map(store, b)),
        NodeSnapshot::For(id, a, b, d, c) => {
            NodeSnapshot::For(id, map(store, a), map(store, b), d, map(store, c))
        }
        NodeSnapshot::ForOf(id, a, b) => NodeSnapshot::ForOf(id, map(store, a), map(store, b)),
        NodeSnapshot::ForAwaitOf(id, a, b) => {
            NodeSnapshot::ForAwaitOf(id, map(store, a), map(store, b))
        }
        NodeSnapshot::Assign(id, x) => NodeSnapshot::Assign(id, map(store, x)),
        leaf => leaf,
    }
}

fn simplify(
    store: &mut IndexedLambda,
    counts: &ExitCounts,
    substitutions: &mut ExitSubstitutions,
    id_gen: &IdGenerator,
    node: NodeId,
) -> NodeId {
    match store.snapshot(node) {
        NodeSnapshot::StaticCatch(body, exit, params, handler) => {
            let occurrences = count_exit(counts, exit);
            if occurrences == 0 {
                return simplify(store, counts, substitutions, id_gen, body);
            }
            if matches!(store.view(handler), NodeView::Var(_) | NodeView::Const(_))
                || occurrences == 1 && exit >= 0
            {
                let handler = simplify(store, counts, substitutions, id_gen, handler);
                substitutions.insert(store, exit, (params, handler));
                return simplify(store, counts, substitutions, id_gen, body);
            }
            let handler = simplify(store, counts, substitutions, id_gen, handler);
            let inline = exit >= 0 && no_bounded_variables(store, handler) && {
                let size = indexed_size(store, handler);
                occurrences <= 2 && size < EXIT_INLINE_SIZE || size < 5
            };
            if inline {
                substitutions.insert(store, exit, (params, handler));
                simplify(store, counts, substitutions, id_gen, body)
            } else {
                let body = simplify(store, counts, substitutions, id_gen, body);
                store.append(NodeSnapshot::StaticCatch(body, exit, params, handler))
            }
        }
        NodeSnapshot::StaticRaise(exit, args) if args.is_empty() => substitutions
            .get(&exit)
            .map(|(_, handler)| *handler)
            .unwrap_or(node),
        NodeSnapshot::StaticRaise(exit, args) => {
            let args: Vec<_> = args
                .into_iter()
                .map(|x| simplify(store, counts, substitutions, id_gen, x))
                .collect();
            let Some((params, handler)) = substitutions.get(&exit).cloned() else {
                return store.append(NodeSnapshot::StaticRaise(exit, args));
            };
            let renamed: Vec<_> = params.iter().map(|id| id.rename(id_gen)).collect();
            let env: VariableSubstitution = params
                .iter()
                .cloned()
                .zip(
                    renamed
                        .iter()
                        .cloned()
                        .map(|id| store.append(NodeSnapshot::Var(id))),
                )
                .collect();
            let mut result = substitute(store, &env, handler);
            for (id, arg) in renamed.into_iter().zip(args).rev() {
                result = store.append(NodeSnapshot::Let(LetKind::Strict, id, arg, result));
            }
            result
        }
        NodeSnapshot::Var(_)
        | NodeSnapshot::Const(_)
        | NodeSnapshot::GlobalModule(_, _)
        | NodeSnapshot::Break
        | NodeSnapshot::Continue => node,
        snapshot => {
            let mapped = map_children(store, snapshot, |store, child| {
                simplify(store, counts, substitutions, id_gen, child)
            });
            append_rebuilt(store, mapped)
        }
    }
}

impl IndexedLambdaContext {
    /// Runs indexed exit simplification over the canonical root and appends
    /// replacements to the same store. Existing metadata IDs remain valid.
    pub fn simplify_exits(&mut self, id_gen: &IdGenerator) {
        let root = self.current_root();
        let counts = count_exits(self.store(), root);
        let mut substitutions = ExitSubstitutions::new();
        let rewritten = simplify(self.store_mut(), &counts, &mut substitutions, id_gen, root);
        self.replace_root(rewritten);
        #[cfg(test)]
        self.record_substitution_table_peak(substitutions.peak_unique_nodes);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ident::IdentFlags;
    use crate::lambda::lam_compile_context::{IdKind, LamStats};
    use crate::lambda::lam_pass_collect as tree_collect;
    use crate::lambda::lam_pass_collect_indexed::IndexedIdKind;
    use crate::lambda::lam_pass_exits as tree;
    use crate::lambda::{DirectionFlag, Lambda, LambdaSwitch, SwitchDispatch, SwitchKey};
    use crate::location::Location;

    fn id(name: &str, stamp: i32) -> Ident {
        Ident::new(name, stamp, IdentFlags::NONE)
    }

    fn simplify_indexed(lambda: Lambda, start_stamp: i32) -> Lambda {
        let mut context = IndexedLambdaContext::from_lambda(lambda, []);
        context.simplify_exits(&IdGenerator::with_start_stamp(start_stamp));
        context.materialize()
    }

    fn assert_exit_parity(lambda: Lambda, start_stamp: i32) -> IndexedLambdaContext {
        let tree_gen = IdGenerator::with_start_stamp(start_stamp);
        let indexed_gen = IdGenerator::with_start_stamp(start_stamp);
        let expected = tree::simplify_exits(&lambda, &tree_gen);
        let mut context = IndexedLambdaContext::from_lambda(lambda, []);
        context.simplify_exits(&indexed_gen);
        assert_eq!(
            format!("{expected:#?}"),
            format!("{:#?}", context.materialize())
        );
        assert_eq!(tree_gen.current_stamp(), indexed_gen.current_stamp());
        context
    }

    #[test]
    fn exit_count_and_bounded_analysis_match_tree_across_control_families() {
        let x = id("x", 1);
        let raise = || Lambda::LstaticRaise(7, vec![Lambda::Lvar(x.clone())]);
        let switch = Lambda::Lswitch(
            Box::new(raise()),
            LambdaSwitch {
                sw_consts_full: false,
                sw_consts: vec![(SwitchKey::Int(0), raise())],
                sw_blocks_full: false,
                sw_blocks: vec![(SwitchKey::Int(1), raise())],
                sw_failaction: Some(Box::new(raise())),
                sw_dispatch: SwitchDispatch::Direct,
            },
        );
        let lambda = Lambda::Lsequence(
            Box::new(Lambda::LstringSwitch(
                Box::new(raise()),
                vec![("a".into(), switch)],
                Some(Box::new(raise())),
            )),
            Box::new(Lambda::LtryWith(
                Box::new(Lambda::LifThenElse(
                    Box::new(raise()),
                    Box::new(raise()),
                    Box::new(raise()),
                )),
                x.clone(),
                Box::new(Lambda::Lfor(
                    x.clone(),
                    Box::new(raise()),
                    Box::new(raise()),
                    DirectionFlag::Upto,
                    Box::new(Lambda::Lfor_of(
                        x.clone(),
                        Box::new(raise()),
                        Box::new(Lambda::Lfor_await_of(
                            x.clone(),
                            Box::new(raise()),
                            Box::new(Lambda::Lassign(x.clone(), Box::new(raise()))),
                        )),
                    )),
                )),
            )),
        );
        let indexed = IndexedLambda::from_lambda(lambda.clone());
        assert_eq!(
            tree::count_helper(&lambda),
            count_exits(&indexed, indexed.root())
        );
        assert_eq!(
            tree::no_bounded_variables(&lambda),
            no_bounded_variables(&indexed, indexed.root())
        );

        let skipped = Lambda::LstaticCatch(
            Box::new(Lambda::unit()),
            (9, vec![]),
            Box::new(Lambda::LstaticRaise(7, vec![])),
        );
        let indexed = IndexedLambda::from_lambda(skipped.clone());
        assert_eq!(
            tree::count_helper(&skipped),
            count_exits(&indexed, indexed.root())
        );
    }

    #[test]
    fn simplify_exits_matches_tree_for_elimination_inlining_and_freshening() {
        let x = id("x", 10);
        let y = id("y", 11);
        let samples = [
            Lambda::LstaticCatch(
                Box::new(Lambda::unit()),
                (1, vec![]),
                Box::new(Lambda::true_()),
            ),
            Lambda::LstaticCatch(
                Box::new(Lambda::LstaticRaise(2, vec![])),
                (2, vec![]),
                Box::new(Lambda::true_()),
            ),
            Lambda::LstaticCatch(
                Box::new(Lambda::LstaticRaise(
                    3,
                    vec![Lambda::Lconst(Constant::int(4))],
                )),
                (3, vec![x.clone()]),
                Box::new(Lambda::Lvar(x.clone())),
            ),
            Lambda::LstaticCatch(
                Box::new(Lambda::Lsequence(
                    Box::new(Lambda::LstaticRaise(4, vec![Lambda::Lvar(y.clone())])),
                    Box::new(Lambda::LstaticRaise(4, vec![Lambda::Lvar(y.clone())])),
                )),
                (4, vec![x.clone()]),
                Box::new(Lambda::Lsequence(
                    Box::new(Lambda::Lvar(x.clone())),
                    Box::new(Lambda::Lconst(Constant::int(1))),
                )),
            ),
            Lambda::LstaticCatch(
                Box::new(Lambda::Lsequence(
                    Box::new(Lambda::LstaticRaise(-1, vec![])),
                    Box::new(Lambda::LstaticRaise(-1, vec![])),
                )),
                (-1, vec![]),
                Box::new(Lambda::Lsequence(
                    Box::new(Lambda::unit()),
                    Box::new(Lambda::unit()),
                )),
            ),
            Lambda::LstaticCatch(
                Box::new(Lambda::LstaticCatch(
                    Box::new(Lambda::LstaticRaise(61, vec![])),
                    (61, vec![]),
                    Box::new(Lambda::LstaticRaise(60, vec![])),
                )),
                (60, vec![]),
                Box::new(Lambda::true_()),
            ),
            Lambda::LstaticCatch(
                Box::new(Lambda::Lsequence(
                    Box::new(Lambda::LstaticRaise(6, vec![])),
                    Box::new(Lambda::LstaticRaise(6, vec![])),
                )),
                (6, vec![]),
                Box::new(Lambda::Llet(
                    LetKind::Strict,
                    x.clone(),
                    Box::new(Lambda::unit()),
                    Box::new(Lambda::Lvar(x.clone())),
                )),
            ),
        ];
        for sample in samples {
            assert_exit_parity(sample, 30);
        }
    }

    #[test]
    fn rewritten_children_use_the_same_smart_constructor_decisions() {
        let loc = crate::location::Location::none();
        let caught = |body: Lambda, handler: Lambda| {
            Lambda::LstaticCatch(Box::new(body), (70, vec![]), Box::new(handler))
        };
        let raise = || Lambda::LstaticRaise(70, vec![]);
        let eta_param = id("eta", 5);
        // `lam_pass_exits.ml:168-183` simplifies the handler before storing
        // it, and `lam_subst.ml:30-66` then applies smart constructors while
        // replacing catch parameters only with fresh variables.
        let parameter = id("parameter", 9);
        assert_exit_parity(
            Lambda::LstaticCatch(
                Box::new(Lambda::LstaticRaise(72, vec![Lambda::unit()])),
                (72, vec![parameter.clone()]),
                Box::new(Lambda::Lsequence(
                    Box::new(Lambda::Lprim(crate::lambda::PrimInfo {
                        primitive: Primitive::Pnot,
                        args: vec![Lambda::true_()],
                        loc: loc.clone(),
                    })),
                    Box::new(Lambda::Lvar(parameter)),
                )),
            ),
            80,
        );

        let raw_unchanged_sibling = Lambda::Lsequence(
            Box::new(Lambda::Lprim(crate::lambda::PrimInfo {
                primitive: Primitive::Pnot,
                args: vec![Lambda::true_()],
                loc: loc.clone(),
            })),
            Box::new(Lambda::LstaticCatch(
                Box::new(Lambda::unit()),
                (71, vec![]),
                Box::new(Lambda::true_()),
            )),
        );
        assert_exit_parity(raw_unchanged_sibling, 80);

        let cases = [
            caught(
                Lambda::LifThenElse(
                    Box::new(raise()),
                    Box::new(Lambda::true_()),
                    Box::new(Lambda::false_()),
                ),
                Lambda::true_(),
            ),
            caught(
                Lambda::Lprim(crate::lambda::PrimInfo {
                    primitive: Primitive::Pnot,
                    args: vec![raise()],
                    loc: loc.clone(),
                }),
                Lambda::true_(),
            ),
            caught(
                Lambda::Lswitch(
                    Box::new(raise()),
                    LambdaSwitch {
                        sw_consts_full: true,
                        sw_consts: vec![(SwitchKey::Int(1), Lambda::true_())],
                        sw_blocks_full: true,
                        sw_blocks: vec![],
                        sw_failaction: Some(Box::new(Lambda::false_())),
                        sw_dispatch: SwitchDispatch::Direct,
                    },
                ),
                Lambda::Lconst(Constant::int(1)),
            ),
            caught(
                Lambda::LstringSwitch(
                    Box::new(raise()),
                    vec![("yes".into(), Lambda::true_())],
                    Some(Box::new(Lambda::false_())),
                ),
                Lambda::Lconst(Constant::string("yes")),
            ),
            caught(
                Lambda::LifThenElse(
                    Box::new(raise()),
                    Box::new(Lambda::true_()),
                    Box::new(Lambda::false_()),
                ),
                Lambda::Lprim(crate::lambda::PrimInfo {
                    primitive: Primitive::Pnot,
                    args: vec![Lambda::Lvar(id("boolean", 6))],
                    loc: loc.clone(),
                }),
            ),
            caught(
                Lambda::LifThenElse(
                    Box::new(raise()),
                    Box::new(Lambda::unit()),
                    Box::new(Lambda::Lconst(Constant::int_with_comment(
                        0,
                        crate::lambda::lam_constant::PointerInfo::AssertFalse,
                    ))),
                ),
                Lambda::Lvar(id("condition", 7)),
            ),
            caught(
                Lambda::Lapply(crate::lambda::Apply {
                    ap_func: Box::new(raise()),
                    ap_args: vec![Lambda::true_()],
                    ap_info: crate::lambda::ApInfo {
                        loc: loc.clone(),
                        inlined: crate::lambda::InlineAttribute::Default,
                        status: crate::lambda::ApplyStatus::Na,
                    },
                    ap_transformed_jsx: false,
                }),
                Lambda::function_(
                    1,
                    vec![eta_param.clone()],
                    Lambda::Lprim(crate::lambda::PrimInfo {
                        primitive: Primitive::Pnot,
                        args: vec![Lambda::Lvar(eta_param)],
                        loc: loc.clone(),
                    }),
                    crate::lambda::FunctionAttribute::default(),
                ),
            ),
            caught(
                Lambda::Lapply(crate::lambda::Apply {
                    ap_func: Box::new(raise()),
                    ap_args: vec![Lambda::true_()],
                    ap_info: crate::lambda::ApInfo {
                        loc: loc.clone(),
                        inlined: crate::lambda::InlineAttribute::Default,
                        status: crate::lambda::ApplyStatus::Na,
                    },
                    ap_transformed_jsx: false,
                }),
                Lambda::function_(
                    1,
                    vec![id("wrapped", 8)],
                    Lambda::Lprim(crate::lambda::PrimInfo {
                        primitive: Primitive::PnullToOpt,
                        args: vec![Lambda::Lprim(crate::lambda::PrimInfo {
                            primitive: Primitive::Pnot,
                            args: vec![Lambda::Lvar(id("wrapped", 8))],
                            loc: loc.clone(),
                        })],
                        loc: loc.clone(),
                    }),
                    crate::lambda::FunctionAttribute::default(),
                ),
            ),
            caught(
                Lambda::Lsequence(Box::new(raise()), Box::new(Lambda::unit())),
                Lambda::Lprim(crate::lambda::PrimInfo {
                    primitive: Primitive::PnullToOpt,
                    args: vec![Lambda::Lvar(id("v", 4))],
                    loc,
                }),
            ),
        ];
        for case in cases {
            assert_exit_parity(case, 80);
        }
    }

    #[test]
    fn direct_and_nested_wrapper_eta_match_reference_order_and_fallback_metadata() {
        let wrappers = [
            Primitive::PnullToOpt,
            Primitive::PnullUndefinedToOpt,
            Primitive::PisNull,
            Primitive::PisNullUndefined,
            Primitive::Ptypeof,
        ];
        for (index, wrapper) in wrappers.into_iter().enumerate() {
            for nested in [false, true] {
                let body_loc = Location::new_for_error("eta.res", 1, 2);
                let apply_loc = Location::new_for_error("eta.res", 10, 20);
                let left = id("left", 200 + index as i32 * 2);
                let right = id("right", 201 + index as i32 * 2);
                let inner = if nested {
                    Lambda::Lprim(crate::lambda::PrimInfo {
                        primitive: Primitive::Pidentity,
                        args: vec![Lambda::Lvar(left.clone()), Lambda::Lvar(right.clone())],
                        loc: body_loc.clone(),
                    })
                } else {
                    Lambda::Lvar(left.clone())
                };
                let body_args = if nested {
                    vec![inner]
                } else {
                    vec![inner, Lambda::Lvar(right.clone())]
                };
                let function = Lambda::function_(
                    2,
                    vec![left, right],
                    Lambda::Lprim(crate::lambda::PrimInfo {
                        primitive: wrapper.clone(),
                        args: body_args,
                        loc: body_loc,
                    }),
                    crate::lambda::FunctionAttribute::default(),
                );
                let apply = Lambda::Lapply(crate::lambda::Apply {
                    ap_func: Box::new(Lambda::LstaticRaise(91, vec![])),
                    ap_args: vec![
                        Lambda::Lconst(Constant::int(1)),
                        Lambda::Lconst(Constant::int(2)),
                    ],
                    ap_info: crate::lambda::ApInfo {
                        loc: apply_loc.clone(),
                        inlined: crate::lambda::InlineAttribute::Never,
                        status: crate::lambda::ApplyStatus::Uncurry,
                    },
                    ap_transformed_jsx: true,
                });
                let input = Lambda::LstaticCatch(Box::new(apply), (91, vec![]), Box::new(function));
                if nested {
                    assert_exit_parity(input, 300);
                } else {
                    // OCaml `lam.ml:160-172` lets direct wrappers reach the
                    // generic eta arm. Current recursive Rust returns early
                    // from its broader wrapper match.
                    let result = simplify_indexed(input, 300);
                    let Lambda::Lprim(info) = result else {
                        panic!("expected direct wrapper eta")
                    };
                    assert_eq!(info.primitive, wrapper);
                    assert_eq!(info.loc, apply_loc);
                    assert!(matches!(
                        info.args.as_slice(),
                        [
                            Lambda::Lconst(Constant::Int { i: 1, .. }),
                            Lambda::Lconst(Constant::Int { i: 2, .. })
                        ]
                    ));
                }
            }
        }

        let parameter = id("fallback", 250);
        let attr = crate::lambda::FunctionAttribute {
            async_: true,
            inline: crate::lambda::InlineAttribute::Never,
            is_a_functor: true,
            return_unit: true,
            directive: Some("use server".into()),
            one_unit_arg: true,
        };
        let function = Lambda::function_(
            7,
            vec![parameter.clone()],
            Lambda::Lprim(crate::lambda::PrimInfo {
                primitive: Primitive::Ptypeof,
                args: vec![Lambda::Lconst(Constant::int(0))],
                loc: Location::none(),
            }),
            attr,
        );
        let result = simplify_indexed(
            Lambda::LstaticCatch(
                Box::new(Lambda::Lapply(crate::lambda::Apply {
                    ap_func: Box::new(Lambda::LstaticRaise(92, vec![])),
                    ap_args: vec![Lambda::Lvar(parameter)],
                    ap_info: crate::lambda::ApInfo {
                        loc: Location::none(),
                        inlined: crate::lambda::InlineAttribute::Always,
                        status: crate::lambda::ApplyStatus::InferFull,
                    },
                    ap_transformed_jsx: true,
                })),
                (92, vec![]),
                Box::new(function),
            ),
            300,
        );
        let Lambda::Lapply(apply) = result else {
            panic!("expected eta fallback application")
        };
        assert!(apply.ap_transformed_jsx);
        assert_eq!(apply.ap_info.status, crate::lambda::ApplyStatus::InferFull);
        let Lambda::Lfunction(function) = *apply.ap_func else {
            panic!("expected function metadata")
        };
        assert_eq!(function.arity, 7);
        assert!(function.attr.async_ && function.attr.is_a_functor && function.attr.one_unit_arg);
        assert_eq!(function.attr.directive.as_deref(), Some("use server"));
    }

    #[test]
    fn unsupported_switch_constants_do_not_select_the_default() {
        for constant in [
            Constant::JsTrue,
            Constant::string("value"),
            Constant::Float("1.5".into()),
        ] {
            for default in [None, Some(Box::new(Lambda::false_()))] {
                let switch = Lambda::Lswitch(
                    Box::new(Lambda::Lconst(constant.clone())),
                    LambdaSwitch {
                        sw_consts_full: false,
                        sw_consts: vec![],
                        sw_blocks_full: false,
                        sw_blocks: vec![],
                        sw_failaction: default,
                        sw_dispatch: SwitchDispatch::Direct,
                    },
                );
                let catch = Lambda::LstaticCatch(
                    Box::new(Lambda::unit()),
                    (90, vec![]),
                    Box::new(Lambda::true_()),
                );
                let result =
                    simplify_indexed(Lambda::Lsequence(Box::new(switch), Box::new(catch)), 100);
                let Lambda::Lsequence(first, _) = result else {
                    panic!("expected sequence")
                };
                assert!(
                    matches!(*first, Lambda::Lswitch(_, _)),
                    "unsupported constant selected default"
                );
            }
        }
    }

    #[test]
    fn no_catch_still_runs_reference_smart_constructors() {
        let loc = Location::none();
        let not_true = || {
            Lambda::Lprim(crate::lambda::PrimInfo {
                primitive: Primitive::Pnot,
                args: vec![Lambda::true_()],
                loc: loc.clone(),
            })
        };
        assert!(matches!(
            simplify_indexed(not_true(), 0),
            Lambda::Lconst(Constant::JsFalse)
        ));
        let result = simplify_indexed(
            Lambda::Lsequence(
                Box::new(not_true()),
                Box::new(Lambda::LstaticRaise(99, vec![])),
            ),
            0,
        );
        assert!(matches!(result, Lambda::Lsequence(first, second)
            if matches!(*first, Lambda::Lconst(Constant::JsFalse))
                && matches!(*second, Lambda::LstaticRaise(99, ref args) if args.is_empty())));
    }

    #[test]
    fn inherited_smart_constructor_debt_follows_ocaml_reference() {
        use crate::types::{VariantBlockType, VariantTag, VariantTagType};
        for tag_type in [
            VariantTagType::Float("1.0".into()),
            VariantTagType::BigInt("1".into()),
            VariantTagType::Untagged(VariantBlockType::Unknown),
        ] {
            let condition = Constant::Constructor(VariantTag {
                name: "C".into(),
                tag_type: Some(tag_type),
            });
            let result = simplify_indexed(
                Lambda::LifThenElse(
                    Box::new(Lambda::Lconst(condition)),
                    Box::new(Lambda::true_()),
                    Box::new(Lambda::false_()),
                ),
                0,
            );
            assert!(matches!(result, Lambda::LifThenElse(_, _, _)));
        }

        let int_tag = VariantTag {
            name: "One".into(),
            tag_type: Some(VariantTagType::Int(1)),
        };
        let result = simplify_indexed(
            Lambda::Lswitch(
                Box::new(Lambda::Lconst(Constant::int(1))),
                LambdaSwitch {
                    sw_consts_full: true,
                    sw_consts: vec![(
                        SwitchKey::Constructor(crate::types::VariantConstructorCase::Constant(
                            int_tag,
                        )),
                        Lambda::true_(),
                    )],
                    sw_blocks_full: true,
                    sw_blocks: vec![],
                    sw_failaction: Some(Box::new(Lambda::false_())),
                    sw_dispatch: SwitchDispatch::Direct,
                },
            ),
            0,
        );
        assert!(matches!(result, Lambda::Lconst(Constant::JsTrue)));

        for (operation, expected) in [
            (crate::lambda::Comparison::Eq, Constant::JsFalse),
            (crate::lambda::Comparison::Neq, Constant::JsTrue),
        ] {
            let left = Constant::Constructor(VariantTag {
                name: "A".into(),
                tag_type: None,
            });
            let right = Constant::Constructor(VariantTag {
                name: "B".into(),
                tag_type: None,
            });
            let result = simplify_indexed(
                Lambda::Lprim(crate::lambda::PrimInfo {
                    primitive: Primitive::Pintcomp(operation),
                    args: vec![Lambda::Lconst(left), Lambda::Lconst(right)],
                    loc: Location::none(),
                }),
                0,
            );
            assert_eq!(
                format!("{result:?}"),
                format!("{:?}", Lambda::Lconst(expected))
            );
        }
    }

    #[test]
    fn simplify_exits_rewrites_all_control_families_in_source_order() {
        let x = id("x", 1);
        let mut lambda = Lambda::LstaticCatch(
            Box::new(Lambda::LstaticRaise(20, vec![])),
            (20, vec![]),
            Box::new(Lambda::LglobalModule(id("M", 0), false)),
        );
        lambda = Lambda::Lassign(x.clone(), Box::new(lambda));
        lambda = Lambda::Lfor_await_of(
            x.clone(),
            Box::new(Lambda::Lvar(x.clone())),
            Box::new(lambda),
        );
        lambda = Lambda::Lfor_of(
            x.clone(),
            Box::new(Lambda::Lvar(x.clone())),
            Box::new(lambda),
        );
        lambda = Lambda::Lfor(
            x.clone(),
            Box::new(Lambda::Lvar(x.clone())),
            Box::new(Lambda::Lconst(Constant::int(3))),
            DirectionFlag::Upto,
            Box::new(lambda),
        );
        lambda = Lambda::LifThenElse(
            Box::new(Lambda::Lvar(x.clone())),
            Box::new(lambda),
            Box::new(Lambda::unit()),
        );
        lambda = Lambda::LtryWith(Box::new(lambda), id("exn", 2), Box::new(Lambda::unit()));
        lambda = Lambda::LstringSwitch(
            Box::new(Lambda::Lvar(x.clone())),
            vec![("case".into(), lambda)],
            Some(Box::new(Lambda::unit())),
        );
        lambda = Lambda::Lswitch(
            Box::new(Lambda::Lvar(x)),
            LambdaSwitch {
                sw_consts_full: true,
                sw_consts: vec![(SwitchKey::Int(0), lambda)],
                sw_blocks_full: true,
                sw_blocks: vec![],
                sw_failaction: None,
                sw_dispatch: SwitchDispatch::Direct,
            },
        );
        assert_exit_parity(lambda, 40);
    }

    #[test]
    fn shared_raise_occurrences_are_freshened_independently() {
        let x = id("x", 1);
        let mut store = IndexedLambda::from_lambda(Lambda::LstaticRaise(30, vec![Lambda::unit()]));
        let shared_raise = store.root();
        let body = store.append(NodeSnapshot::Sequence(shared_raise, shared_raise));
        let handler = store.append(NodeSnapshot::Var(x.clone()));
        let root = store.append(NodeSnapshot::StaticCatch(body, 30, vec![x], handler));
        store.set_root(root);
        let mut context = IndexedLambdaContext::from_store(store, []);
        let id_gen = IdGenerator::with_start_stamp(100);
        context.simplify_exits(&id_gen);
        let Lambda::Lsequence(first, second) = context.materialize() else {
            panic!("expected sequence");
        };
        let (Lambda::Llet(_, first_id, _, _), Lambda::Llet(_, second_id, _, _)) = (*first, *second)
        else {
            panic!("expected independently substituted lets");
        };
        assert_ne!(first_id, second_id);
        assert_eq!(id_gen.current_stamp(), 102);
    }

    #[test]
    fn storage_metrics_partition_large_child_and_case_payloads() {
        let loc = Location::none();
        let cases = (0..32)
            .map(|case| {
                let args = (0..16)
                    .map(|value| Lambda::Lconst(Constant::int(case * 16 + value)))
                    .collect::<Vec<_>>();
                (
                    SwitchKey::Int(case),
                    Lambda::Lprim(crate::lambda::PrimInfo {
                        primitive: Primitive::Pmakearray,
                        args,
                        loc: loc.clone(),
                    }),
                )
            })
            .collect::<Vec<_>>();
        let lambda = Lambda::Lswitch(
            Box::new(Lambda::Lvar(id("scrutinee", 400))),
            LambdaSwitch {
                sw_consts_full: true,
                sw_consts: cases,
                sw_blocks_full: true,
                sw_blocks: vec![],
                sw_failaction: None,
                sw_dispatch: SwitchDispatch::Direct,
            },
        );
        let mut context = IndexedLambdaContext::from_lambda(lambda, []);
        context.simplify_exits(&IdGenerator::with_start_stamp(500));
        let metrics = context.storage_measurements();
        assert!(metrics.current_live_side_payload_shallow_bytes > 32 * 16 * 4);
        assert!(metrics.superseded_unreachable_side_payload_shallow_bytes > 32 * 16 * 4);
        assert_eq!(metrics.metadata_retained_only_side_payload_shallow_bytes, 0);
        assert_eq!(
            metrics.current_live_side_payload_shallow_bytes
                + metrics.metadata_retained_only_side_payload_shallow_bytes
                + metrics.superseded_unreachable_side_payload_shallow_bytes,
            metrics.side_payload_shallow_occupied_bytes
        );
        assert!(
            metrics.side_payload_shallow_capacity_bytes
                >= metrics.side_payload_shallow_occupied_bytes
        );
    }

    #[test]
    fn collect_exits_collect_keeps_one_store_and_identifier_frontier() {
        let x = id("x", 1);
        let f = id("f", 2);
        let lambda = Lambda::Llet(
            LetKind::Strict,
            f.clone(),
            Box::new(Lambda::function_(
                1,
                vec![x.clone()],
                Lambda::LstaticCatch(
                    Box::new(Lambda::LstaticRaise(12, vec![Lambda::unit()])),
                    (12, vec![x.clone()]),
                    Box::new(Lambda::Lvar(x)),
                ),
                crate::lambda::FunctionAttribute {
                    inline: crate::lambda::InlineAttribute::Always,
                    ..crate::lambda::FunctionAttribute::default()
                },
            )),
            Box::new(Lambda::Lvar(f.clone())),
        );
        let mut tree_meta = LamStats::new(vec![f.clone()]);
        tree_collect::collect_info(&mut tree_meta, &lambda);
        let tree_gen = IdGenerator::with_start_stamp(50);
        let expected = tree::simplify_exits(&lambda, &tree_gen);
        tree_collect::collect_info(&mut tree_meta, &expected);
        let mut context = IndexedLambdaContext::from_lambda(lambda, [f.clone()]);
        context.collect_info();
        let retained_before = context
            .metadata()
            .ident_tbl
            .values()
            .filter(|kind| {
                matches!(
                    kind,
                    IndexedIdKind::FunctionId {
                        lambda: Some(_),
                        ..
                    }
                )
            })
            .count();
        let allocations_before = context.node_count();
        let indexed_gen = IdGenerator::with_start_stamp(50);
        context.simplify_exits(&indexed_gen);
        let retained_before_recollect = context.storage_measurements();
        assert!(retained_before_recollect.metadata_retained_only_side_payload_shallow_bytes > 0);
        assert_eq!(context.substitution_table_peak_unique_nodes(), 1);
        context.collect_info();
        assert_eq!(
            format!("{expected:#?}"),
            format!("{:#?}", context.materialize())
        );
        assert_eq!(tree_gen.current_stamp(), indexed_gen.current_stamp());
        assert!(retained_before > 0);
        assert!(context.node_count() > allocations_before);
        match (
            tree_meta.ident_tbl.get(&f),
            context.metadata().ident_tbl.get(&f),
        ) {
            (
                Some(IdKind::FunctionId {
                    arity: tree_arity,
                    lambda: Some((tree_lambda, tree_rec)),
                }),
                Some(IndexedIdKind::FunctionId {
                    arity: indexed_arity,
                    lambda: Some((indexed_lambda, indexed_rec)),
                }),
            ) => {
                assert_eq!(tree_arity, indexed_arity);
                assert_eq!(tree_rec, indexed_rec);
                assert_eq!(
                    format!("{tree_lambda:#?}"),
                    format!("{:#?}", context.store().materialize_node(*indexed_lambda))
                );
            }
            kinds => panic!("collect metadata differs after exits: {kinds:?}"),
        }
        assert!(
            context
                .metadata()
                .ident_tbl
                .values()
                .any(|kind| matches!(kind, IndexedIdKind::FunctionId { .. }))
        );

        let first = context.storage_measurements();
        assert_eq!(first.node_allocations, 11);
        assert_eq!(first.node_allocations, context.node_count());
        assert_eq!(first.current_root_edge_visits, 5);
        assert_eq!(first.current_root_unique_nodes, 6);
        assert_eq!(first.metadata_unique_nodes, 4);
        assert_eq!(first.live_unique_nodes, 6);
        assert_eq!(first.superseded_nodes, 5);
        assert_eq!(
            first.superseded_nodes,
            first.node_allocations - first.live_unique_nodes
        );
        assert!(first.hot_node_capacity_bytes >= first.hot_node_occupied_bytes);
        assert!(
            first.side_payload_shallow_capacity_bytes >= first.side_payload_shallow_occupied_bytes
        );
        assert!(!first.nested_heap_bytes_included);
        assert_eq!(
            first.current_live_side_payload_shallow_bytes
                + first.metadata_retained_only_side_payload_shallow_bytes
                + first.superseded_unreachable_side_payload_shallow_bytes,
            first.side_payload_shallow_occupied_bytes
        );

        // OCaml always walks and rebuilds smart constructors, even without a catch.
        context.simplify_exits(&indexed_gen);
        let second = context.storage_measurements();
        assert_eq!(second.node_allocations, 14);
        assert_eq!(
            second.current_root_unique_nodes,
            first.current_root_unique_nodes
        );
        assert_eq!(second.superseded_nodes, 6);
    }
}
