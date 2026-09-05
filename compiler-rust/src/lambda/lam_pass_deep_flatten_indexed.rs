//! Indexed port of `compiler/core/lam_pass_deep_flatten.ml`.

use ahash::AHashMap;

use crate::context::IdGenerator;
use crate::ident::Ident;
use crate::lambda::indexed::{IndexedLambda, IndexedLambdaContext, NodeId, NodeSnapshot, NodeView};
use crate::lambda::lam_analysis_indexed::{hit_variable, hit_variables};
use crate::lambda::lam_compat::LetKind;
use crate::lambda::lam_indexed_helpers::{append_rebuilt, append_refine_let, map_children};
use crate::lambda::lam_primitive::{Mutable, Primitive};
use crate::location::Location;

enum Group {
    Single(LetKind, Ident, NodeId),
    Recursive(Vec<(Ident, NodeId)>),
    Nop(NodeId),
}

fn lambda_of_groups(store: &mut IndexedLambda, groups: Vec<Group>, mut result: NodeId) -> NodeId {
    for group in groups.into_iter().rev() {
        result = match group {
            Group::Single(kind, id, value) => append_refine_let(store, kind, id, value, result),
            Group::Recursive(bindings) => store.append(NodeSnapshot::LetRec(bindings, result)),
            Group::Nop(value) => append_rebuilt(store, NodeSnapshot::Sequence(value, result)),
        };
    }
    result
}

fn rhs_is_beta_residue(store: &IndexedLambda, node: NodeId) -> bool {
    match store.view(node) {
        NodeView::Let(LetKind::Alias | LetKind::Strict | LetKind::StrictOpt, _, value, rest)
            if matches!(
                store.view(value),
                NodeView::Prim(Primitive::Pmakeblock(_, Mutable::Immutable), _, _)
                    | NodeView::Var(_)
            ) =>
        {
            rhs_is_beta_residue(store, rest)
        }
        NodeView::Apply(_, _, _, _) => true,
        _ => false,
    }
}

fn eliminate_tuple(
    store: &IndexedLambda,
    tuple: &Ident,
    node: NodeId,
    mapping: &mut AHashMap<i32, Ident>,
) -> Option<NodeId> {
    if let NodeView::Let(LetKind::Alias, projected, value, body) = store.view(node)
        && let NodeView::Prim(Primitive::Pfield(index, _), [base], _) = store.view(value)
        && matches!(store.view(*base), NodeView::Var(id) if id.same(tuple))
    {
        mapping.insert(*index, projected.clone());
        return eliminate_tuple(store, tuple, body, mapping);
    }
    (!hit_variable(store, tuple, node)).then_some(node)
}

fn flatten(
    store: &mut IndexedLambda,
    groups: &mut Vec<Group>,
    node: NodeId,
    id_gen: &IdGenerator,
) -> NodeId {
    match store.snapshot(node) {
        NodeSnapshot::Let(kind, id, value, body) => {
            if let NodeSnapshot::Prim(
                primitive @ (Primitive::PnullToOpt | Primitive::PnullUndefinedToOpt),
                args,
                loc,
            ) = store.snapshot(value)
                && let [arg] = args.as_slice()
            {
                if matches!(store.view(*arg), NodeView::Var(_)) {
                    let value = aux(store, value, id_gen);
                    groups.push(Group::Single(kind, id, value));
                    return flatten(store, groups, body, id_gen);
                }
                let fresh = id.rename(id_gen);
                let fresh_var = store.append(NodeSnapshot::Var(fresh.clone()));
                let wrapped = append_rebuilt(
                    store,
                    NodeSnapshot::Prim(primitive, vec![fresh_var], Location::none()),
                );
                let inner = store.append(NodeSnapshot::Let(LetKind::Alias, id, wrapped, body));
                let rewritten = store.append(NodeSnapshot::Let(kind, fresh, *arg, inner));
                let _ = loc;
                return flatten(store, groups, rewritten, id_gen);
            }

            if rhs_is_beta_residue(store, value) {
                let value = aux(store, value, id_gen);
                groups.push(Group::Single(kind, id, value));
                return flatten(store, groups, body, id_gen);
            }

            let value = flatten(store, groups, value, id_gen);
            let named_block = matches!(id.name(), "match" | "include" | "param")
                && matches!(kind, LetKind::Alias | LetKind::Strict | LetKind::StrictOpt)
                && matches!(
                    store.view(value),
                    NodeView::Prim(Primitive::Pmakeblock(_, Mutable::Immutable), _, _)
                );
            if named_block {
                let mut mapping = AHashMap::new();
                if let Some(body) = eliminate_tuple(store, &id, body, &mut mapping) {
                    let NodeSnapshot::Prim(_, args, _) = store.snapshot(value) else {
                        unreachable!()
                    };
                    for (index, arg) in args.into_iter().enumerate() {
                        match mapping.get(&(index as i32)) {
                            Some(projected) => {
                                groups.push(Group::Single(kind, projected.clone(), arg))
                            }
                            None => groups.push(Group::Nop(arg)),
                        }
                    }
                    return flatten(store, groups, body, id_gen);
                }
            }
            groups.push(Group::Single(kind, id, value));
            flatten(store, groups, body, id_gen)
        }
        NodeSnapshot::LetRec(bindings, body) => {
            let bindings = bindings
                .into_iter()
                .map(|(id, value)| (id, aux(store, value, id_gen)))
                .collect();
            groups.push(Group::Recursive(bindings));
            flatten(store, groups, body, id_gen)
        }
        NodeSnapshot::Sequence(left, right) => {
            let left = flatten(store, groups, left, id_gen);
            groups.push(Group::Nop(left));
            flatten(store, groups, right, id_gen)
        }
        _ => aux(store, node, id_gen),
    }
}

fn aux(store: &mut IndexedLambda, node: NodeId, id_gen: &IdGenerator) -> NodeId {
    match store.snapshot(node) {
        NodeSnapshot::Let(_, _, _, _) => {
            let mut groups = Vec::new();
            let result = flatten(store, &mut groups, node, id_gen);
            lambda_of_groups(store, groups, result)
        }
        NodeSnapshot::LetRec(bindings, body) => {
            let collections: Vec<_> = bindings.iter().map(|(id, _)| id.clone()).collect();
            let bindings: Vec<_> = bindings
                .into_iter()
                .map(|(id, value)| (id, aux(store, value, id_gen)))
                .collect();
            let mut recursive = Vec::new();
            let mut wrap = Vec::new();
            let mut stop = false;
            for (id, value) in bindings {
                if stop || hit_variables(store, &collections, value) {
                    recursive.push((id, value));
                    stop = true;
                } else {
                    wrap.push(Group::Single(LetKind::Strict, id, value));
                }
            }
            let body = aux(store, body, id_gen);
            let body = store.append(NodeSnapshot::LetRec(recursive, body));
            lambda_of_groups(store, wrap, body)
        }
        NodeSnapshot::Sequence(left, right) => {
            let left = aux(store, left, id_gen);
            let right = aux(store, right, id_gen);
            append_rebuilt(store, NodeSnapshot::Sequence(left, right))
        }
        NodeSnapshot::Var(_)
        | NodeSnapshot::GlobalModule(_, _)
        | NodeSnapshot::Const(_)
        | NodeSnapshot::Break
        | NodeSnapshot::Continue => node,
        snapshot => {
            let mapped = map_children(store, snapshot, |store, child| aux(store, child, id_gen));
            append_rebuilt(store, mapped)
        }
    }
}

impl IndexedLambdaContext {
    /// Runs deep flatten over the canonical root in the existing store.
    pub fn deep_flatten(&mut self, id_gen: &IdGenerator) {
        let root = self.current_root();
        let root = aux(self.store_mut(), root, id_gen);
        self.replace_root(root);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ident::IdentFlags;
    use crate::lambda::lam_compat::FieldDbgInfo;
    use crate::lambda::{Constant, Lambda, TagInfo};

    fn id(name: &str, stamp: i32) -> Ident {
        Ident::new(name, stamp, IdentFlags::NONE)
    }
    fn int(value: i32) -> Lambda {
        Lambda::const_(Constant::int(value))
    }

    fn assert_matches_tree(input: Lambda, start_stamp: i32) {
        let expected_gen = IdGenerator::with_start_stamp(start_stamp);
        let expected = crate::lambda::lam_pass_deep_flatten::deep_flatten_owned_with_id_gen(
            input.clone(),
            &expected_gen,
        );
        let actual_gen = IdGenerator::with_start_stamp(start_stamp);
        let mut context = IndexedLambdaContext::from_lambda(input, []);
        context.deep_flatten(&actual_gen);
        assert_eq!(
            format!("{:#?}", context.materialize()),
            format!("{expected:#?}")
        );
        assert_eq!(actual_gen.current_stamp(), expected_gen.current_stamp());
    }

    #[test]
    fn tuple_projection_elimination_matches_reference() {
        let tuple = id("match", 1);
        let projected = id("field", 2);
        let input = Lambda::let_(
            LetKind::Strict,
            tuple.clone(),
            Lambda::prim(
                Primitive::Pmakeblock(TagInfo::Tuple, Mutable::Immutable),
                vec![int(10), int(20)],
                Location::none(),
            ),
            Lambda::let_(
                LetKind::Alias,
                projected.clone(),
                Lambda::prim(
                    Primitive::Pfield(1, FieldDbgInfo::Tuple),
                    vec![Lambda::var(tuple)],
                    Location::none(),
                ),
                Lambda::var(projected),
            ),
        );
        assert_matches_tree(input, 10);
    }

    #[test]
    fn null_to_opt_argument_uses_caller_generator_once() {
        let value = id("value", 1);
        let input = Lambda::let_(
            LetKind::Strict,
            value.clone(),
            Lambda::prim(
                Primitive::PnullToOpt,
                vec![Lambda::prim(
                    Primitive::Paddint,
                    vec![int(1), int(2)],
                    Location::none(),
                )],
                Location::none(),
            ),
            Lambda::var(value),
        );
        assert_matches_tree(input, 40);
    }

    #[test]
    fn recursive_extraction_stops_after_first_dependency() {
        let a = id("a", 1);
        let b = id("b", 2);
        let c = id("c", 3);
        let input = Lambda::letrec(
            vec![
                (a.clone(), int(1)),
                (b.clone(), Lambda::var(a.clone())),
                (c.clone(), int(3)),
            ],
            Lambda::var(b),
        );
        let generator = IdGenerator::with_start_stamp(10);
        let mut context = IndexedLambdaContext::from_lambda(input, []);
        context.deep_flatten(&generator);
        let expected = Lambda::let_(
            LetKind::Alias,
            a,
            int(1),
            Lambda::letrec(
                vec![(id("b", 2), Lambda::var(id("a", 1))), (c, int(3))],
                Lambda::var(id("b", 2)),
            ),
        );
        assert_eq!(
            format!("{:#?}", context.materialize()),
            format!("{expected:#?}")
        );
        assert_eq!(generator.current_stamp(), 10);
    }
}
