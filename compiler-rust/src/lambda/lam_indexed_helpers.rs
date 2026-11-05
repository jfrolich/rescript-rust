//! Shared smart constructors, child mapping, and substitution for indexed Lambda passes.
//!
//! These mirror `compiler/core/lam.ml` and `compiler/core/lam_subst.ml` and
//! are shared by exits, beta reduction, alias simplification, and deep flatten.

use ahash::AHashMap;
use crate::lambda::LamLoc;

use crate::ident::Ident;
use crate::lambda::indexed::{IndexedLambda, NodeId, NodeSnapshot, NodeView};
use crate::lambda::lam_analysis_indexed::{hit_variable, no_side_effects};
use crate::lambda::lam_compat::LetKind;
use crate::lambda::lam_constant::Constant;
use crate::lambda::lam_primitive::Primitive;

pub(crate) type VariableSubstitution = AHashMap<Ident, NodeId>;

/// Indexed `Lam_util.refine_let`, preserving its ordered rewrite clauses.
pub(crate) fn append_refine_let(
    store: &mut IndexedLambda,
    kind: LetKind,
    param: Ident,
    arg: NodeId,
    body: NodeId,
) -> NodeId {
    if matches!(store.view(body), NodeView::Var(id) if id.same(&param)) {
        return arg;
    }
    if let NodeSnapshot::Prim(primitive, args, loc) = store.snapshot(body)
        && let [only] = args.as_slice()
        && matches!(store.view(*only), NodeView::Var(id) if id.same(&param))
        && !matches!(primitive, Primitive::Pmakeblock(_, _))
    {
        return append_rebuilt(store, NodeSnapshot::Prim(primitive, vec![arg], loc));
    }
    if let NodeSnapshot::Apply(function, args, info, jsx) = store.snapshot(body)
        && let [only] = args.as_slice()
        && matches!(store.view(*only), NodeView::Var(id) if id.same(&param))
        && !hit_variable(store, &param, function)
    {
        return append_rebuilt(store, NodeSnapshot::Apply(function, vec![arg], info, jsx));
    }
    fn safe_to_alias(store: &IndexedLambda, node: NodeId) -> bool {
        match store.view(node) {
            NodeView::Var(_) | NodeView::Const(_) => true,
            // lam_util.ml: a template without interpolations is a literal.
            NodeView::Prim(Primitive::Ptemplate(segments), [], _) if segments.len() == 1 => true,
            NodeView::Prim(
                Primitive::Pfield(_, crate::lambda::FieldDbgInfo::Module { .. }),
                [base],
                _,
            ) if matches!(
                store.view(*base),
                NodeView::GlobalModule(_) | NodeView::Var(_)
            ) =>
            {
                true
            }
            NodeView::Prim(Primitive::PsomeNotNest, [inner], _) => safe_to_alias(store, *inner),
            _ => false,
        }
    }
    let kind = match kind {
        LetKind::Strict | LetKind::StrictOpt if safe_to_alias(store, arg) => LetKind::Alias,
        LetKind::Strict
            if matches!(store.view(arg), NodeView::Function(_, _, _, _, _))
                || no_side_effects(store, arg) =>
        {
            LetKind::StrictOpt
        }
        kind => kind,
    };
    store.append(NodeSnapshot::Let(kind, param, arg, body))
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
        (NodeView::GlobalModule(a), NodeView::GlobalModule(b)) => a.same(b),
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

fn boolean_location(store: &IndexedLambda, node: NodeId) -> Option<LamLoc> {
    match store.view(node) {
        NodeView::Prim(
            Primitive::Pnot
            | Primitive::Psequand
            | Primitive::Psequor
            | Primitive::PisNotNone
            | Primitive::Pobjcomp(_)
            | Primitive::Pboolcomp(_)
            | Primitive::Pintcomp(_)
            | Primitive::Pfloatcomp(_)
            | Primitive::Pbigintcomp(_)
            | Primitive::Pstringcomp(_),
            _,
            loc,
        ) => Some(*loc),
        _ => None,
    }
}

fn is_assert_false(store: &IndexedLambda, node: NodeId) -> bool {
    matches!(
        store.view(node),
        NodeView::Const(Constant::Int { comment: Some(info), .. })
            if matches!(**info, crate::lambda::lam_constant::PointerInfo::AssertFalse)
    )
}
fn is_true(store: &IndexedLambda, node: NodeId) -> bool {
    matches!(store.view(node), NodeView::Const(Constant::JsTrue))
}
fn is_false(store: &IndexedLambda, node: NodeId) -> bool {
    matches!(store.view(node), NodeView::Const(Constant::JsFalse))
}

fn append_not(store: &mut IndexedLambda, loc: LamLoc, node: NodeId) -> NodeId {
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
            | Constant::String(_)
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
                        | Constant::String(_)
                        | Constant::ImmString(_)
                        | Constant::Pointer(_)
                        | Constant::Float(_)
                        | Constant::BigInt { .. }
                        | Constant::Block { .. } => Some(true),
                        Constant::Constructor(tag) => match &tag.literal {
                            None => Some(tag.name != "[]"),
                            Some(crate::types::VariantLiteralTag::String(value)) => {
                                Some(!value.is_empty())
                            }
                            Some(crate::types::VariantLiteralTag::Int(value)) => Some(*value != 0),
                            Some(crate::types::VariantLiteralTag::Bool(value)) => Some(*value),
                            Some(
                                crate::types::VariantLiteralTag::Null
                                | crate::types::VariantLiteralTag::Undefined,
                            ) => Some(false),
                            Some(
                                crate::types::VariantLiteralTag::Float(_)
                                | crate::types::VariantLiteralTag::BigInt(_),
                            ) => None,
                        },
                        Constant::NativeInt { .. } => None,
                    }
                }
                inner_truthy(inner)
            }
            Constant::Constructor(tag) => match &tag.literal {
                None => Some(tag.name != "[]"),
                Some(crate::types::VariantLiteralTag::String(value)) => Some(!value.is_empty()),
                Some(crate::types::VariantLiteralTag::Int(value)) => Some(*value != 0),
                Some(crate::types::VariantLiteralTag::Bool(value)) => Some(*value),
                Some(
                    crate::types::VariantLiteralTag::Null
                    | crate::types::VariantLiteralTag::Undefined,
                ) => Some(false),
                Some(
                    crate::types::VariantLiteralTag::Float(_)
                    | crate::types::VariantLiteralTag::BigInt(_),
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
        NodeSnapshot::Prim(Primitive::Pisint, args, loc) => {
            append_pisint_if(store, args, loc, then_node, else_node)
        }
        _ => store.append(NodeSnapshot::IfThenElse(condition, then_node, else_node)),
    }
}

fn append_pisint_if(
    store: &mut IndexedLambda,
    args: Vec<NodeId>,
    loc: LamLoc,
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

pub(crate) fn append_rebuilt(store: &mut IndexedLambda, node: NodeSnapshot) -> NodeId {
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
            if let NodeSnapshot::Function(_, params, body, _, _) = store.snapshot(function) {
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
                            // lambda.ml `apply` builds through the folding `prim`.
                            return append_rebuilt(
                                store,
                                NodeSnapshot::Prim(primitive, args, info.loc),
                            );
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
                                let inner = append_rebuilt(
                                    store,
                                    NodeSnapshot::Prim(inner_primitive, args, info.loc),
                                );
                                return append_rebuilt(
                                    store,
                                    NodeSnapshot::Prim(wrapper, vec![inner], info.loc),
                                );
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
                            let call = append_rebuilt(
                                store,
                                NodeSnapshot::Prim(primitive, args, info.loc),
                            );
                            return append_rebuilt(store, NodeSnapshot::Sequence(call, second));
                        }
                    }
                    _ => {}
                }
            }
            if let NodeSnapshot::Let(kind, id, value, body) = store.snapshot(function)
                && matches!(store.view(body), NodeView::Function(_, _, _, _, _))
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
                        NodeView::Var(id) | NodeView::GlobalModule(id) => Some((*source, *id)),
                        _ => None,
                    },
                    _ => None,
                });
            let reconstructs_source = source.as_ref().is_some_and(|(_, source_id)| {
                args.iter().zip(fields.iter()).enumerate().all(|(index, (arg, expected_name))| {
                    matches!(store.view(*arg), NodeView::Prim(Primitive::Pfield(position, crate::lambda::FieldDbgInfo::Module { name }), [base], _)
                        if *position as usize == index && name == expected_name
                            && matches!(store.view(*base), NodeView::Var(id) | NodeView::GlobalModule(id) if id.same(source_id)))
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
                && left.literal.is_none()
                && right.literal.is_none()
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
            match crate::lambda::Lambda::prim(primitive.clone(), lambda_args, loc) {
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
                            ) if matches!(tag.literal, Some(crate::types::VariantLiteralTag::Int(value)) if value == i64::from(*i))
                        )
                }).map(|(_, node)| *node),
                NodeView::Const(Constant::Block { tag_info, .. }) => {
                    let runtime = match &**tag_info {
                        crate::lambda::TagInfo::Constructor { runtime, .. } => Some(crate::types::VariantBlock::Tagged((**runtime).clone())),
                        crate::lambda::TagInfo::RecordInlined { runtime, .. } => Some((**runtime).clone()),
                        _ => None,
                    };
                    blocks.iter().find(|(key, _)| matches!((key, runtime.as_ref()), (crate::lambda::SwitchKey::Constructor(crate::types::VariantConstructorCase::Block(candidate)), Some(runtime)) if candidate == runtime)).map(|(_, node)| *node)
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
                NodeView::Const(Constant::String(_)) | NodeView::Const(Constant::ImmString(_))
            );
            let selected = match store.view(scrutinee) {
                NodeView::Const(Constant::String(s)) | NodeView::Const(Constant::ImmString(s)) => {
                    cases
                        .iter()
                        .find(|(key, _)| key == s)
                        .map(|(_, node)| *node)
                }
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
        // `Lambda.prim` folds a primitive over one or two constants.
        NodeSnapshot::Prim(primitive, args, loc)
            if matches!(args.len(), 1 | 2)
                && args
                    .iter()
                    .all(|arg| matches!(store.view(*arg), NodeView::Const(_))) =>
        {
            let consts = args
                .iter()
                .map(|arg| match store.view(*arg) {
                    NodeView::Const(c) => crate::lambda::Lambda::Lconst(c.clone()),
                    _ => unreachable!(),
                })
                .collect();
            match crate::lambda::Lambda::prim(primitive.clone(), consts, loc) {
                folded @ crate::lambda::Lambda::Lconst(_) => store.append_compat_lambda(folded),
                _ => store.append(NodeSnapshot::Prim(primitive, args, loc)),
            }
        }
        node => store.append(node),
    }
}

pub(crate) fn substitute(
    store: &mut IndexedLambda,
    substitutions: &VariableSubstitution,
    node: NodeId,
) -> NodeId {
    // `Lambda_traverse.subst_lambda` (lambda_traverse.ml:235-241): replace
    // variables; `shallow_map_sharing` rebuilds through the smart
    // constructors only the nodes whose children changed.
    match store.snapshot(node) {
        NodeSnapshot::Var(id) => substitutions.get(&id).copied().unwrap_or(node),
        NodeSnapshot::Const(_)
        | NodeSnapshot::GlobalModule(_)
        | NodeSnapshot::Break
        | NodeSnapshot::Continue => node,
        snapshot => {
            let mut changed = false;
            let mapped = map_children(store, snapshot, |store, child| {
                let mapped = substitute(store, substitutions, child);
                changed |= mapped != child;
                mapped
            });
            if !changed {
                return node;
            }
            append_rebuilt(store, mapped)
        }
    }
}

pub(crate) fn map_children(
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
        NodeSnapshot::Function(a, p, body, attr, loc) => {
            NodeSnapshot::Function(a, p, map(store, body), attr, loc)
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
