//! Indexed port of `compiler/core/lam_pass_eliminate_ref.ml`.

use crate::ident::Ident;
use crate::lambda::indexed::{IndexedLambda, NodeId, NodeSnapshot, NodeView};
use crate::lambda::lam_analysis_indexed::hit_variable;
use crate::lambda::lam_indexed_helpers::{append_rebuilt, map_children};
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
        NodeSnapshot::Prim(Primitive::Pfield(0, _), args, _)
            if matches!(args.as_slice(), [value] if matches!(store.view(*value), NodeView::Var(id) if id.same(target))) =>
        {
            Ok(store.append(NodeSnapshot::Var(target.clone())))
        }
        NodeSnapshot::Function(_, _, _, _) => {
            if hit_variable(store, target, node) {
                Err(RealReference)
            } else {
                Ok(node)
            }
        }
        NodeSnapshot::Prim(Primitive::Psetfield(0, _), args, _)
            if matches!(args.as_slice(), [base, _] if matches!(store.view(*base), NodeView::Var(id) if id.same(target))) =>
        {
            let value = eliminate_ref(store, target, args[1])?;
            Ok(store.append(NodeSnapshot::Assign(target.clone(), value)))
        }
        NodeSnapshot::Prim(Primitive::Poffsetref(delta), args, loc)
            if matches!(args.as_slice(), [base] if matches!(store.view(*base), NodeView::Var(id) if id.same(target))) =>
        {
            let variable = store.append(NodeSnapshot::Var(target.clone()));
            let value = append_rebuilt(
                store,
                NodeSnapshot::Prim(Primitive::Poffsetint(delta), vec![variable], loc),
            );
            Ok(store.append(NodeSnapshot::Assign(target.clone(), value)))
        }
        NodeSnapshot::Const(_)
        | NodeSnapshot::GlobalModule(_, _)
        | NodeSnapshot::Break
        | NodeSnapshot::Continue => Ok(node),
        snapshot => {
            let mut failure = None;
            let mapped = map_children(store, snapshot, |store, child| {
                if failure.is_some() {
                    return child;
                }
                match eliminate_ref(store, target, child) {
                    Ok(node) => node,
                    Err(error) => {
                        failure = Some(error);
                        child
                    }
                }
            });
            match failure {
                Some(error) => Err(error),
                None => Ok(append_rebuilt(store, mapped)),
            }
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
                vec![Lambda::var(reference.clone())],
                Location::none(),
            ),
            Lambda::seq(
                Lambda::prim(
                    Primitive::Psetfield(0, SetFieldDbgInfo::RecordSet("value".into())),
                    vec![
                        Lambda::var(reference.clone()),
                        Lambda::const_(Constant::int(2)),
                    ],
                    Location::none(),
                ),
                Lambda::prim(
                    Primitive::Poffsetref(1),
                    vec![Lambda::var(reference.clone())],
                    Location::none(),
                ),
            ),
        );
        let mut store = IndexedLambda::from_lambda(input);
        let root = store.root();
        let result = eliminate_ref(&mut store, &reference, root).unwrap();
        let expected = Lambda::seq(
            Lambda::var(reference.clone()),
            Lambda::seq(
                Lambda::assign(reference.clone(), Lambda::const_(Constant::int(2))),
                Lambda::assign(
                    reference.clone(),
                    Lambda::prim(
                        Primitive::Poffsetint(1),
                        vec![Lambda::var(reference.clone())],
                        Location::none(),
                    ),
                ),
            ),
        );
        assert_eq!(format!("{:#?}", store.materialize_node(result)), format!("{expected:#?}"));
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
            (Lambda::var(reference.clone()), false),
            (Lambda::const_(Constant::int(0)), true),
        ] {
            let function = Lambda::function_(
                1,
                vec![parameter.clone()],
                body,
                FunctionAttribute::default(),
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
