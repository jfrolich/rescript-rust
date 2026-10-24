//! Indexed port of `compiler/core/lam_pass_eliminate_ref.ml`.

use crate::ident::Ident;
use crate::lambda::indexed::{IndexedLambda, NodeId, NodeSnapshot, NodeView};
use crate::lambda::lam_analysis_indexed::hit_variable;
use crate::lambda::lam_indexed_helpers::append_rebuilt;
use crate::lambda::lam_primitive::Primitive;

#[derive(Debug, Clone, Copy)]
pub(crate) struct RealReference;

pub(crate) fn eliminate_ref(
    store: &mut IndexedLambda,
    target: &Ident,
    node: NodeId,
) -> Result<NodeId, RealReference> {
    match store.snapshot(node) {
        NodeSnapshot::Var(id) => {
            if id.same(target) {
                Err(RealReference)
            } else {
                Ok(node)
            }
        }
        NodeSnapshot::Prim(Primitive::Pfield(0, _), args, _) if matches!(args.as_slice(), [value] if matches!(store.view(*value), NodeView::Var(id) if id.same(target))) => {
            Ok(store.append(NodeSnapshot::Var(*target)))
        }
        NodeSnapshot::Function(_, _, _, _, _) => {
            if hit_variable(store, target, node) {
                Err(RealReference)
            } else {
                Ok(node)
            }
        }
        NodeSnapshot::Prim(Primitive::Psetfield(0, _), args, _) if matches!(args.as_slice(), [base, _] if matches!(store.view(*base), NodeView::Var(id) if id.same(target))) =>
        {
            let value = eliminate_ref(store, target, args[1])?;
            Ok(store.append(NodeSnapshot::Assign(*target, value)))
        }
        NodeSnapshot::Const(_)
        | NodeSnapshot::GlobalModule(_)
        | NodeSnapshot::Break
        | NodeSnapshot::Continue => Ok(node),
        NodeSnapshot::Apply(function, args, info, jsx) => {
            let args = args
                .into_iter()
                .map(|node| eliminate_ref(store, target, node))
                .collect::<Result<Vec<_>, _>>()?;
            let function = eliminate_ref(store, target, function)?;
            Ok(append_rebuilt(
                store,
                NodeSnapshot::Apply(function, args, info, jsx),
            ))
        }
        NodeSnapshot::Let(kind, id, value, body) => {
            let body = eliminate_ref(store, target, body)?;
            let value = eliminate_ref(store, target, value)?;
            Ok(append_rebuilt(
                store,
                NodeSnapshot::Let(kind, id, value, body),
            ))
        }
        NodeSnapshot::LetRec(bindings, body) => {
            let body = eliminate_ref(store, target, body)?;
            let bindings = bindings
                .into_iter()
                .map(|(id, value)| eliminate_ref(store, target, value).map(|value| (id, value)))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(append_rebuilt(store, NodeSnapshot::LetRec(bindings, body)))
        }
        NodeSnapshot::Prim(primitive, args, loc) => {
            let args = args
                .into_iter()
                .map(|node| eliminate_ref(store, target, node))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(append_rebuilt(
                store,
                NodeSnapshot::Prim(primitive, args, loc),
            ))
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
            let fail_action = fail_action
                .map(|node| eliminate_ref(store, target, node))
                .transpose()?;
            let blocks = blocks
                .into_iter()
                .map(|(key, node)| eliminate_ref(store, target, node).map(|node| (key, node)))
                .collect::<Result<Vec<_>, _>>()?;
            let consts = consts
                .into_iter()
                .map(|(key, node)| eliminate_ref(store, target, node).map(|node| (key, node)))
                .collect::<Result<Vec<_>, _>>()?;
            let scrutinee = eliminate_ref(store, target, scrutinee)?;
            Ok(append_rebuilt(
                store,
                NodeSnapshot::Switch {
                    scrutinee,
                    consts_full,
                    consts,
                    blocks_full,
                    blocks,
                    fail_action,
                    dispatch,
                },
            ))
        }
        NodeSnapshot::StringSwitch(scrutinee, cases, default) => {
            let default = default
                .map(|node| eliminate_ref(store, target, node))
                .transpose()?;
            let cases = cases
                .into_iter()
                .map(|(key, node)| eliminate_ref(store, target, node).map(|node| (key, node)))
                .collect::<Result<Vec<_>, _>>()?;
            let scrutinee = eliminate_ref(store, target, scrutinee)?;
            Ok(append_rebuilt(
                store,
                NodeSnapshot::StringSwitch(scrutinee, cases, default),
            ))
        }
        NodeSnapshot::StaticRaise(exit, args) => {
            let args = args
                .into_iter()
                .map(|node| eliminate_ref(store, target, node))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(append_rebuilt(store, NodeSnapshot::StaticRaise(exit, args)))
        }
        NodeSnapshot::StaticCatch(body, exit, params, handler) => {
            let handler = eliminate_ref(store, target, handler)?;
            let body = eliminate_ref(store, target, body)?;
            Ok(append_rebuilt(
                store,
                NodeSnapshot::StaticCatch(body, exit, params, handler),
            ))
        }
        NodeSnapshot::TryWith(body, id, handler) => {
            let handler = eliminate_ref(store, target, handler)?;
            let body = eliminate_ref(store, target, body)?;
            Ok(append_rebuilt(
                store,
                NodeSnapshot::TryWith(body, id, handler),
            ))
        }
        NodeSnapshot::IfThenElse(condition, then_node, else_node) => {
            let else_node = eliminate_ref(store, target, else_node)?;
            let then_node = eliminate_ref(store, target, then_node)?;
            let condition = eliminate_ref(store, target, condition)?;
            Ok(append_rebuilt(
                store,
                NodeSnapshot::IfThenElse(condition, then_node, else_node),
            ))
        }
        NodeSnapshot::Sequence(first, second) => {
            let second = eliminate_ref(store, target, second)?;
            let first = eliminate_ref(store, target, first)?;
            Ok(append_rebuilt(store, NodeSnapshot::Sequence(first, second)))
        }
        NodeSnapshot::While(condition, body) => {
            let body = eliminate_ref(store, target, body)?;
            let condition = eliminate_ref(store, target, condition)?;
            Ok(append_rebuilt(store, NodeSnapshot::While(condition, body)))
        }
        NodeSnapshot::For(id, from, to, direction, body) => {
            let body = eliminate_ref(store, target, body)?;
            let to = eliminate_ref(store, target, to)?;
            let from = eliminate_ref(store, target, from)?;
            Ok(append_rebuilt(
                store,
                NodeSnapshot::For(id, from, to, direction, body),
            ))
        }
        NodeSnapshot::ForOf(id, iterable, body) => {
            let body = eliminate_ref(store, target, body)?;
            let iterable = eliminate_ref(store, target, iterable)?;
            Ok(append_rebuilt(
                store,
                NodeSnapshot::ForOf(id, iterable, body),
            ))
        }
        NodeSnapshot::ForAwaitOf(id, iterable, body) => {
            let body = eliminate_ref(store, target, body)?;
            let iterable = eliminate_ref(store, target, iterable)?;
            Ok(append_rebuilt(
                store,
                NodeSnapshot::ForAwaitOf(id, iterable, body),
            ))
        }
        NodeSnapshot::Assign(id, value) => {
            let value = eliminate_ref(store, target, value)?;
            Ok(append_rebuilt(store, NodeSnapshot::Assign(id, value)))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ident::IdentFlags;
    use crate::lambda::lam_compat::{FieldDbgInfo, SetFieldDbgInfo};
    use crate::lambda::{Constant, FunctionAttribute, Lambda};
    use crate::location::Location;

    fn id(name: &str, stamp: i32) -> Ident {
        Ident::new(name, stamp, IdentFlags::NONE)
    }

    #[test]
    fn rewrites_reads_writes_offsets_and_preserves_flags() {
        let reference = id("reference", 1);
        let input = Lambda::seq(
            Lambda::prim(
                Primitive::Pfield(0, FieldDbgInfo::Tuple),
                vec![Lambda::var(reference)],
                Location::none(),
            ),
            Lambda::seq(
                Lambda::prim(
                    Primitive::Psetfield(0, SetFieldDbgInfo::RecordSet("value".into())),
                    vec![Lambda::var(reference), Lambda::const_(Constant::int(2))],
                    Location::none(),
                ),
                Lambda::prim(
                    Primitive::Psetfield(0, SetFieldDbgInfo::RecordSet("contents".into())),
                    vec![
                        Lambda::var(reference),
                        Lambda::prim(
                            Primitive::Paddint,
                            vec![
                                Lambda::prim(
                                    Primitive::Pfield(0, FieldDbgInfo::Tuple),
                                    vec![Lambda::var(reference)],
                                    Location::none(),
                                ),
                                Lambda::const_(Constant::int(1)),
                            ],
                            Location::none(),
                        ),
                    ],
                    Location::none(),
                ),
            ),
        );
        let mut store = IndexedLambda::from_lambda(input);
        let root = store.root();
        let result = eliminate_ref(&mut store, &reference, root).unwrap();
        let expected = Lambda::seq(
            Lambda::var(reference),
            Lambda::seq(
                Lambda::assign(reference, Lambda::const_(Constant::int(2))),
                Lambda::assign(
                    reference,
                    Lambda::prim(
                        Primitive::Paddint,
                        vec![Lambda::var(reference), Lambda::const_(Constant::int(1))],
                        Location::none(),
                    ),
                ),
            ),
        );
        assert_eq!(
            format!("{:#?}", store.materialize_node(result)),
            format!("{expected:#?}")
        );
        let Lambda::Lsequence(first, _) = store.materialize_node(result) else {
            panic!("expected sequence")
        };
        let Lambda::Lvar(actual) = *first else {
            panic!("expected variable")
        };
        assert_eq!(actual.name(), reference.name());
        assert_eq!(actual.stamp(), reference.stamp());
        assert_eq!(actual.flags(), reference.flags());
    }

    #[test]
    fn closure_capture_aborts_but_unrelated_closure_reuses_node() {
        let reference = id("reference", 1);
        let parameter = id("parameter", 2);
        for (body, succeeds) in [
            (Lambda::var(reference), false),
            (Lambda::const_(Constant::int(0)), true),
        ] {
            let function = Lambda::function_(
                1,
                vec![parameter],
                body,
                FunctionAttribute::default(),
                crate::location::Location::none(),
            );
            let mut store = IndexedLambda::from_lambda(function);
            let root = store.root();
            let before = store.node_count();
            let result = eliminate_ref(&mut store, &reference, root);
            assert_eq!(result.is_ok(), succeeds);
            if succeeds {
                assert_eq!(result.unwrap(), root);
                assert_eq!(store.node_count(), before);
            }
        }
    }
}
