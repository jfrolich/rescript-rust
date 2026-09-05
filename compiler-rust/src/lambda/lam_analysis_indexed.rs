//! Borrowed analyses for compilation-owned indexed Lambda.
//! Direct counterparts of `lam_analysis.ml` and `lam_hit.ml`.

use ahash::AHashSet;

use crate::ident::Ident;
use crate::lambda::indexed::{IndexedLambda, NodeId, NodeView};
use crate::lambda::lam_analysis::is_pure_primitive;
use crate::lambda::lam_compat::FieldDbgInfo;
use crate::lambda::lam_constant::Constant;
use crate::lambda::lam_primitive::Primitive;

pub(crate) fn hit_variable(store: &IndexedLambda, target: &Ident, node: NodeId) -> bool {
    hit_variables(store, std::slice::from_ref(target), node)
}

pub(crate) fn hit_variables(store: &IndexedLambda, targets: &[Ident], node: NodeId) -> bool {
    fn hit(store: &IndexedLambda, targets: &[Ident], node: NodeId) -> bool {
        let ident = |id: &Ident| targets.iter().any(|target| target.same(id));
        match store.view(node) {
            NodeView::Var(id) => ident(id),
            NodeView::Assign(id, value) => ident(id) || hit(store, targets, value),
            NodeView::Apply(function, args, _, _) => {
                hit(store, targets, function) || args.iter().any(|node| hit(store, targets, *node))
            }
            NodeView::Function(_, _, body, _) => hit(store, targets, body),
            NodeView::Let(_, _, value, body) => {
                hit(store, targets, value) || hit(store, targets, body)
            }
            NodeView::LetRec(bindings, body) => {
                hit(store, targets, body)
                    || bindings.iter().any(|(_, node)| hit(store, targets, *node))
            }
            NodeView::Prim(_, args, _) | NodeView::StaticRaise(_, args) => {
                args.iter().any(|node| hit(store, targets, *node))
            }
            NodeView::Switch {
                scrutinee,
                consts,
                blocks,
                fail_action,
                ..
            } => {
                hit(store, targets, scrutinee)
                    || consts.iter().any(|(_, node)| hit(store, targets, *node))
                    || blocks.iter().any(|(_, node)| hit(store, targets, *node))
                    || fail_action.is_some_and(|node| hit(store, targets, node))
            }
            NodeView::StringSwitch(scrutinee, cases, default) => {
                hit(store, targets, scrutinee)
                    || cases.iter().any(|(_, node)| hit(store, targets, *node))
                    || default.is_some_and(|node| hit(store, targets, node))
            }
            NodeView::StaticCatch(body, _, _, handler) | NodeView::TryWith(body, _, handler) => {
                hit(store, targets, body) || hit(store, targets, handler)
            }
            NodeView::IfThenElse(a, b, c) | NodeView::For(_, a, b, _, c) => {
                hit(store, targets, a) || hit(store, targets, b) || hit(store, targets, c)
            }
            NodeView::Sequence(a, b)
            | NodeView::While(a, b)
            | NodeView::ForOf(_, a, b)
            | NodeView::ForAwaitOf(_, a, b) => hit(store, targets, a) || hit(store, targets, b),
            NodeView::GlobalModule(_, _)
            | NodeView::Const(_)
            | NodeView::Break
            | NodeView::Continue => false,
        }
    }
    hit(store, targets, node)
}

pub(crate) fn no_side_effects(store: &IndexedLambda, node: NodeId) -> bool {
    match store.view(node) {
        NodeView::Var(_)
        | NodeView::Const(_)
        | NodeView::Function(_, _, _, _)
        | NodeView::GlobalModule(_, _) => true,
        NodeView::Prim(primitive, args, _) => {
            args.iter().all(|node| no_side_effects(store, *node))
                && is_pure_primitive(
                    primitive,
                    args.get(1).and_then(|node| match store.view(*node) {
                        NodeView::Const(constant) => Some(constant),
                        _ => None,
                    }),
                )
        }
        NodeView::Let(_, _, value, body) => {
            no_side_effects(store, value) && no_side_effects(store, body)
        }
        NodeView::TryWith(body, _, handler) => {
            no_side_effects(store, body) && no_side_effects(store, handler)
        }
        NodeView::IfThenElse(a, b, c) => {
            no_side_effects(store, a) && no_side_effects(store, b) && no_side_effects(store, c)
        }
        NodeView::Sequence(a, b) => no_side_effects(store, a) && no_side_effects(store, b),
        NodeView::LetRec(bindings, body) => {
            bindings
                .iter()
                .all(|(_, node)| no_side_effects(store, *node))
                && no_side_effects(store, body)
        }
        NodeView::Apply(function, args, _, _) => matches!(
            store.view(function),
            NodeView::Prim(Primitive::Pfield(_, FieldDbgInfo::Module { name }), _, _)
                if name == "from_fun" && args.len() == 1 && no_side_effects(store, args[0])
        ),
        NodeView::Switch { .. }
        | NodeView::StringSwitch(_, _, _)
        | NodeView::StaticRaise(_, _)
        | NodeView::StaticCatch(_, _, _, _)
        | NodeView::Break
        | NodeView::Continue
        | NodeView::While(_, _)
        | NodeView::For(_, _, _, _, _)
        | NodeView::ForOf(_, _, _)
        | NodeView::ForAwaitOf(_, _, _)
        | NodeView::Assign(_, _) => false,
    }
}

const TOO_BIG: i32 = 1000;

pub(crate) fn size(store: &IndexedLambda, node: NodeId) -> i32 {
    fn constant_size(constant: &Constant) -> i32 {
        match constant {
            Constant::Some(value) => constant_size(value),
            Constant::Block { elements, .. } => elements.iter().map(constant_size).sum(),
            _ => 1,
        }
    }
    fn inner(store: &IndexedLambda, node: NodeId) -> Option<i32> {
        let sum = |nodes: &[NodeId], initial: i32| -> Option<i32> {
            nodes
                .iter()
                .try_fold(initial, |acc, node| Some(acc + inner(store, *node)?))
        };
        match store.view(node) {
            NodeView::Var(_) | NodeView::GlobalModule(_, _) => Some(1),
            NodeView::Const(value) => Some(constant_size(value)),
            NodeView::Let(_, _, a, b) => Some(1 + inner(store, a)? + inner(store, b)?),
            NodeView::LetRec(_, _) => None,
            NodeView::Prim(Primitive::Pfield(_, FieldDbgInfo::Module { .. }), [base], _)
                if matches!(
                    store.view(*base),
                    NodeView::GlobalModule(_, _) | NodeView::Var(_)
                ) =>
            {
                Some(1)
            }
            NodeView::Prim(Primitive::Praise | Primitive::PisNotNone, [arg], _) => {
                inner(store, *arg)
            }
            NodeView::Prim(Primitive::PrawJsCode(_), _, _) => None,
            NodeView::Prim(_, args, _) => sum(args, 1),
            NodeView::Apply(function, args, _, _) => sum(args, inner(store, function)?),
            NodeView::Function(_, _, body, _) => inner(store, body),
            NodeView::StaticRaise(_, args) => sum(args, 1),
            NodeView::IfThenElse(a, b, c) => {
                Some(1 + inner(store, a)? + inner(store, b)? + inner(store, c)?)
            }
            NodeView::Sequence(a, b) => Some(inner(store, a)? + inner(store, b)?),
            NodeView::Break | NodeView::Continue => Some(1),
            NodeView::Assign(_, value) => Some(1 + inner(store, value)?),
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
    inner(store, node).unwrap_or(TOO_BIG)
}

pub(crate) fn is_closed(store: &IndexedLambda, exports: &AHashSet<Ident>, node: NodeId) -> bool {
    // Kept here for callers that only need the conservative closed predicate.
    fn walk(
        store: &IndexedLambda,
        node: NodeId,
        bound: &mut AHashSet<Ident>,
        free: &mut Vec<Ident>,
    ) {
        match store.view(node) {
            NodeView::Var(id) => {
                if !bound.contains(id) && !id.is_global() {
                    free.push(id.clone());
                }
            }
            NodeView::Function(_, params, body, _) => {
                bound.extend(params.iter().cloned());
                walk(store, body, bound, free);
            }
            NodeView::Let(_, id, value, body) => {
                walk(store, value, bound, free);
                bound.insert(id.clone());
                walk(store, body, bound, free);
            }
            NodeView::LetRec(bindings, body) => {
                bound.extend(bindings.iter().map(|(id, _)| id.clone()));
                for (_, n) in bindings {
                    walk(store, *n, bound, free);
                }
                walk(store, body, bound, free);
            }
            snapshot => {
                let children: Vec<NodeId> = match snapshot {
                    NodeView::Apply(f, a, _, _) => {
                        std::iter::once(f).chain(a.iter().copied()).collect()
                    }
                    NodeView::Prim(_, a, _) | NodeView::StaticRaise(_, a) => a.to_vec(),
                    NodeView::StaticCatch(a, _, _, b)
                    | NodeView::TryWith(a, _, b)
                    | NodeView::Sequence(a, b)
                    | NodeView::While(a, b)
                    | NodeView::ForOf(_, a, b)
                    | NodeView::ForAwaitOf(_, a, b) => vec![a, b],
                    NodeView::IfThenElse(a, b, c) | NodeView::For(_, a, b, _, c) => vec![a, b, c],
                    NodeView::Assign(_, a) => vec![a],
                    NodeView::Switch {
                        scrutinee,
                        consts,
                        blocks,
                        fail_action,
                        ..
                    } => std::iter::once(scrutinee)
                        .chain(consts.iter().map(|x| x.1))
                        .chain(blocks.iter().map(|x| x.1))
                        .chain(fail_action)
                        .collect(),
                    NodeView::StringSwitch(s, c, d) => std::iter::once(s)
                        .chain(c.iter().map(|x| x.1))
                        .chain(d)
                        .collect(),
                    _ => vec![],
                };
                for child in children {
                    walk(store, child, bound, free);
                }
            }
        }
    }
    let mut bound = exports.clone();
    let mut free = vec![];
    walk(store, node, &mut bound, &mut free);
    free.is_empty()
}
