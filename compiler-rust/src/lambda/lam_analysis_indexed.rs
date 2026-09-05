//! Borrowed analyses for compilation-owned indexed Lambda.
//! Direct counterparts of `lam_analysis.ml` and `lam_hit.ml`.

use ahash::AHashSet;

use crate::ident::Ident;
use crate::lambda::indexed::{IndexedLambda, NodeId, NodeView};
use crate::lambda::lam_analysis::is_pure_primitive;
use crate::lambda::lam_closure::{Position, StatsMap, VarStats};
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

pub(crate) fn is_closed_with_map(
    store: &IndexedLambda,
    exports: &AHashSet<Ident>,
    params: &[Ident],
    node: NodeId,
) -> (bool, StatsMap) {
    let mut stats: StatsMap = params
        .iter()
        .cloned()
        .map(|id| (id, VarStats::fresh()))
        .collect();
    let mut local = exports.clone();
    fn after(store: &IndexedLambda, node: NodeId, position: Position) -> Position {
        if position != Position::Begin || no_side_effects(store, node) {
            position
        } else {
            Position::NotBegin
        }
    }
    fn iter(
        store: &IndexedLambda,
        node: NodeId,
        position: Position,
        stats: &mut StatsMap,
        local: &mut AHashSet<Ident>,
    ) {
        match store.view(node) {
            NodeView::Var(id) => {
                if !local.contains(id) {
                    stats
                        .entry(id.clone())
                        .or_insert_with(VarStats::fresh)
                        .update(position);
                }
            }
            NodeView::Assign(id, value) => {
                if !local.contains(id) {
                    stats
                        .entry(id.clone())
                        .or_insert_with(VarStats::fresh)
                        .update(position);
                }
                iter(store, value, position, stats, local);
            }
            NodeView::Apply(function, args, _, _) => {
                iter(store, function, position, stats, local);
                let position = after(store, function, position);
                for node in args {
                    iter(store, *node, position, stats, local);
                }
            }
            NodeView::Prim(_, args, _) => {
                for node in args {
                    iter(store, *node, position, stats, local);
                }
            }
            NodeView::Function(_, params, body, _) => {
                local.extend(params.iter().cloned());
                iter(store, body, Position::Sink, stats, local);
            }
            NodeView::Let(_, id, value, body) => {
                iter(store, value, position, stats, local);
                local.insert(id.clone());
                iter(store, body, Position::Sink, stats, local);
            }
            NodeView::LetRec(bindings, body) => {
                local.extend(bindings.iter().map(|(id, _)| id.clone()));
                for (_, node) in bindings {
                    iter(store, *node, Position::Sink, stats, local);
                }
                iter(store, body, Position::Sink, stats, local);
            }
            NodeView::Switch {
                scrutinee,
                consts_full,
                blocks_full,
                consts,
                blocks,
                fail_action,
                ..
            } => {
                iter(store, scrutinee, position, stats, local);
                let next = after(store, scrutinee, position);
                for (_, n) in consts {
                    iter(store, *n, next, stats, local);
                }
                for (_, n) in blocks {
                    iter(store, *n, next, stats, local);
                }
                if let Some(n) = fail_action {
                    iter(
                        store,
                        n,
                        if consts_full || blocks_full {
                            next
                        } else {
                            Position::Sink
                        },
                        stats,
                        local,
                    );
                }
            }
            NodeView::StringSwitch(scrutinee, cases, default) => {
                iter(store, scrutinee, position, stats, local);
                let next = after(store, scrutinee, position);
                for (_, n) in cases {
                    iter(store, *n, next, stats, local);
                }
                if let Some(n) = default {
                    iter(store, n, next, stats, local);
                }
            }
            NodeView::StaticRaise(_, args) => {
                for n in args {
                    iter(store, *n, Position::Sink, stats, local);
                }
            }
            NodeView::StaticCatch(body, _, params, handler) => {
                iter(store, body, Position::Sink, stats, local);
                local.extend(params.iter().cloned());
                iter(store, handler, Position::Sink, stats, local);
            }
            NodeView::TryWith(body, _, handler) => {
                iter(store, body, position, stats, local);
                iter(store, handler, Position::Sink, stats, local);
            }
            NodeView::IfThenElse(condition, then_, else_) => {
                iter(store, condition, position, stats, local);
                let next = after(store, condition, position);
                iter(store, then_, next, stats, local);
                iter(store, else_, next, stats, local);
            }
            NodeView::Sequence(a, b) => {
                iter(store, a, position, stats, local);
                iter(store, b, Position::Sink, stats, local);
            }
            NodeView::While(a, b) => {
                iter(store, a, Position::Sink, stats, local);
                iter(store, b, Position::Sink, stats, local);
            }
            NodeView::For(id, a, b, _, c) => {
                local.insert(id.clone());
                iter(store, a, Position::Sink, stats, local);
                iter(store, b, Position::Sink, stats, local);
                iter(store, c, Position::Sink, stats, local);
            }
            NodeView::ForOf(id, a, b) | NodeView::ForAwaitOf(id, a, b) => {
                local.insert(id.clone());
                iter(store, a, Position::Sink, stats, local);
                iter(store, b, Position::Sink, stats, local);
            }
            NodeView::GlobalModule(_, _)
            | NodeView::Const(_)
            | NodeView::Break
            | NodeView::Continue => {}
        }
    }
    iter(store, node, Position::Begin, &mut stats, &mut local);
    (stats.len() == params.len(), stats)
}
