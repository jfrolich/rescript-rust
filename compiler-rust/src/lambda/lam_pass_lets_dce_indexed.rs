//! Indexed let simplification for `compiler/core/lam_pass_lets_dce.ml`.

use ahash::AHashMap;

use crate::ident::Ident;
use crate::lambda::indexed::{IndexedLambda, IndexedLambdaContext, NodeId, NodeSnapshot, NodeView};
use crate::lambda::lam_analysis_indexed::no_side_effects;
use crate::lambda::lam_beta_reduce_indexed::simple_beta_reduce;
use crate::lambda::lam_compat::{FieldDbgInfo, LetKind};
use crate::lambda::lam_constant::Constant;
use crate::lambda::lam_indexed_helpers::{append_rebuilt, append_refine_let, map_children};
use crate::lambda::lam_pass_count_indexed::{OccurrenceTable, collect_occurs};
use crate::lambda::lam_pass_eliminate_ref_indexed::eliminate_ref;
use crate::lambda::lam_primitive::{Mutable, Primitive};

struct Lets<'a> {
    occurrences: &'a OccurrenceTable,
    substitutions: AHashMap<Ident, NodeId>,
    strings: AHashMap<Ident, String>,
    beta_hash_capacity: &'a mut usize,
}

impl Lets<'_> {
    fn used(&self, id: &Ident) -> bool {
        self.occurrences.get(id).times > 0
    }
}

fn no_names_beta_reduce(
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

fn string_value(store: &IndexedLambda, state: &Lets<'_>, node: NodeId) -> Option<String> {
    match store.view(node) {
        NodeView::Const(Constant::String { s, delim: None }) => Some(s.clone()),
        NodeView::Var(id) => state.strings.get(id).cloned(),
        _ => None,
    }
}

fn simplify(store: &mut IndexedLambda, state: &mut Lets<'_>, node: NodeId) -> NodeId {
    match store.snapshot(node) {
        NodeSnapshot::Var(id) => state.substitutions.get(&id).copied().unwrap_or(node),
        NodeSnapshot::Let(kind, id, value, body)
            if matches!(kind, LetKind::Strict | LetKind::Alias | LetKind::StrictOpt)
                && matches!(store.view(value), NodeView::Var(_)) =>
        {
            let source = simplify(store, state, value);
            state.substitutions.insert(id, source);
            simplify(store, state, body)
        }
        NodeSnapshot::Let(LetKind::Strict, id, value, body)
            if matches!(store.view(value), NodeView::Prim(Primitive::Pmakeblock(_, Mutable::Mutable), args, _) if args.len() == 1) =>
        {
            let NodeSnapshot::Prim(primitive, mut args, loc) = store.snapshot(value) else {
                unreachable!()
            };
            let init = args.pop().expect("checked ref initializer");
            let init = simplify(store, state, init);
            let body = simplify(store, state, body);
            match eliminate_ref(store, &id, body) {
                Ok(body) => append_refine_let(store, LetKind::Variable, id, init, body),
                Err(_) => {
                    let reference = append_rebuilt(
                        store,
                        NodeSnapshot::Prim(primitive, vec![init], loc),
                    );
                    append_refine_let(store, LetKind::Strict, id, reference, body)
                }
            }
        }
        NodeSnapshot::Let(LetKind::Alias, id, value, body) => {
            let info = state.occurrences.get(&id);
            if info.times == 0 {
                return simplify(store, state, body);
            }
            let small_constant = matches!(
                store.view(value),
                NodeView::Const(
                    Constant::Int { .. }
                        | Constant::Constructor(_)
                        | Constant::Char(_)
                        | Constant::Float(_)
                        | Constant::BigInt { .. }
                        | Constant::Pointer(_)
                        | Constant::JsTrue
                        | Constant::JsFalse
                        | Constant::JsUndefined { .. }
                )
            );
            let module_field = matches!(
                store.view(value),
                NodeView::Prim(Primitive::Pfield(_, _), [base], _)
                    if matches!(store.view(*base), NodeView::GlobalModule(_, _))
            );
            let substitute = (info.times == 1 && !info.captured)
                || (info.times == 1
                    && info.captured
                    && matches!(store.view(value), NodeView::Const(_) | NodeView::Var(_)))
                || small_constant
                || module_field;
            if substitute {
                let value = simplify(store, state, value);
                state.substitutions.insert(id, value);
                return simplify(store, state, body);
            }
            if let NodeView::Const(Constant::String { s, delim: None }) = store.view(value) {
                state.strings.insert(id.clone(), s.clone());
                let body = simplify(store, state, body);
                return append_rebuilt(
                    store,
                    NodeSnapshot::Let(LetKind::Alias, id, value, body),
                );
            }
            let value = simplify(store, state, value);
            let body = simplify(store, state, body);
            append_rebuilt(
                store,
                NodeSnapshot::Let(LetKind::Alias, id, value, body),
            )
        }
        NodeSnapshot::Let(LetKind::StrictOpt, id, value, body) => {
            if !state.used(&id) {
                return simplify(store, state, body);
            }
            if let NodeSnapshot::Prim(primitive, mut args, loc) = store.snapshot(value)
                && matches!(primitive, Primitive::Pmakeblock(_, Mutable::Mutable))
                && args.len() == 1
            {
                let init = simplify(store, state, args.pop().expect("checked ref initializer"));
                let body = simplify(store, state, body);
                return match eliminate_ref(store, &id, body) {
                    Ok(body) => append_refine_let(store, LetKind::Variable, id, init, body),
                    Err(_) => {
                        let reference = append_rebuilt(
                            store,
                            NodeSnapshot::Prim(primitive, vec![init], loc),
                        );
                        append_refine_let(store, LetKind::StrictOpt, id, reference, body)
                    }
                };
            }
            let value = simplify(store, state, value);
            if let NodeView::Const(Constant::String { s, delim: None }) = store.view(value) {
                state.strings.insert(id.clone(), s.clone());
                let body = simplify(store, state, body);
                return append_rebuilt(
                    store,
                    NodeSnapshot::Let(LetKind::Alias, id, value, body),
                );
            }
            let body = simplify(store, state, body);
            append_refine_let(store, LetKind::StrictOpt, id, value, body)
        }
        NodeSnapshot::Let(kind @ (LetKind::Strict | LetKind::Variable), id, value, body) => {
            if !state.used(&id) {
                let value = simplify(store, state, value);
                let body = simplify(store, state, body);
                return if no_side_effects(store, value) {
                    body
                } else {
                    append_rebuilt(store, NodeSnapshot::Sequence(value, body))
                };
            }
            let value = simplify(store, state, value);
            if kind == LetKind::Strict
                && let NodeView::Const(Constant::String { s, delim: None }) = store.view(value)
            {
                state.strings.insert(id.clone(), s.clone());
                let body = simplify(store, state, body);
                return append_rebuilt(
                    store,
                    NodeSnapshot::Let(LetKind::Alias, id, value, body),
                );
            }
            let body = simplify(store, state, body);
            append_refine_let(store, kind, id, value, body)
        }
        NodeSnapshot::Sequence(first, second) => {
            let first = simplify(store, state, first);
            let second = simplify(store, state, second);
            append_rebuilt(store, NodeSnapshot::Sequence(first, second))
        }
        NodeSnapshot::Apply(function, args, info, jsx) => {
            if let NodeSnapshot::Function(_, params, body, attr) = store.snapshot(function)
                && params.len() == args.len()
                && !attr.async_
                && attr.directive.is_none()
            {
                let reduced = no_names_beta_reduce(
                    store,
                    &params,
                    body,
                    &args,
                    state.beta_hash_capacity,
                );
                return simplify(store, state, reduced);
            }
            let function = simplify(store, state, function);
            let args = args
                .into_iter()
                .map(|node| simplify(store, state, node))
                .collect();
            append_rebuilt(store, NodeSnapshot::Apply(function, args, info, jsx))
        }
        NodeSnapshot::Prim(Primitive::Pstringadd, args, loc) if args.len() == 2 => {
            let left = simplify(store, state, args[0]);
            let right = simplify(store, state, args[1]);
            match (
                string_value(store, state, left),
                string_value(store, state, right),
            ) {
                (Some(left), Some(right)) => store.append(NodeSnapshot::Const(Constant::String {
                    s: left + &right,
                    delim: None,
                })),
                _ => append_rebuilt(
                    store,
                    NodeSnapshot::Prim(Primitive::Pstringadd, vec![left, right], loc),
                ),
            }
        }
        NodeSnapshot::Const(_)
        | NodeSnapshot::GlobalModule(_, _)
        | NodeSnapshot::Break
        | NodeSnapshot::Continue => node,
        snapshot => {
            let mapped = map_children(store, snapshot, |store, child| {
                simplify(store, state, child)
            });
            append_rebuilt(store, mapped)
        }
    }
}

impl IndexedLambdaContext {
    pub fn simplify_lets(&mut self) {
        let root = self.current_root();
        let root = {
            let (store, _, beta_hash_capacity) = self.optimizer_parts_mut();
            let occurrences = collect_occurs(store, root, beta_hash_capacity);
            simplify(
                store,
                &mut Lets {
                    occurrences: &occurrences,
                    substitutions: AHashMap::with_capacity(32),
                    strings: AHashMap::with_capacity(32),
                    beta_hash_capacity,
                },
                root,
            )
        };
        self.replace_root(root);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ident::IdentFlags;
    use crate::lambda::lam_compat::SetFieldDbgInfo;
    use crate::lambda::{Constant, FunctionAttribute, Lambda};
    use crate::location::Location;

    fn id(name: &str, stamp: i32) -> Ident {
        Ident::new(name, stamp, IdentFlags::NONE)
    }
    fn int(value: i32) -> Lambda {
        Lambda::const_(Constant::int(value))
    }
    fn run(input: Lambda) -> Lambda {
        let mut context = IndexedLambdaContext::from_lambda(input, []);
        context.simplify_lets();
        context.materialize()
    }
    fn assert_exact(actual: &Lambda, expected: &Lambda) {
        assert_eq!(format!("{actual:#?}"), format!("{expected:#?}"));
    }

    #[test]
    fn drops_pure_unused_binding_but_sequences_effectful_initializer() {
        let value = id("value", 1);
        let result = id("result", 2);
        assert_exact(
            &run(Lambda::let_(
                LetKind::Strict,
                value.clone(),
                int(1),
                Lambda::var(result.clone()),
            )),
            &Lambda::var(result.clone()),
        );
        let effect = Lambda::prim(
            Primitive::PjsCall {
                prim_name: "effect".into(),
                arg_types: vec![],
                ffi: crate::lambda::lam_primitive::ExternalFfiSpec {
                    kind: crate::lambda::lam_primitive::ExternalFfiKind::Default,
                    spec: None,
                    obj_params: None,
                    return_wrapper: crate::lambda::lam_primitive::ExternalReturnWrapper::Identity,
                    inline_constant: None,
                },
                dynamic_import: false,
                transformed_jsx: false,
            },
            vec![],
            Location::none(),
        );
        assert_exact(
            &run(Lambda::let_(
                LetKind::Variable,
                value,
                effect.clone(),
                Lambda::var(result.clone()),
            )),
            &Lambda::seq(effect, Lambda::var(result)),
        );
    }

    #[test]
    fn aliases_and_strings_follow_reference_decisions() {
        let once = id("once", 1);
        assert_exact(
            &run(Lambda::let_(
                LetKind::Alias,
                once.clone(),
                int(7),
                Lambda::var(once),
            )),
            &int(7),
        );
        let left = id("left", 2);
        let right = id("right", 3);
        let concat = Lambda::prim(
            Primitive::Pstringadd,
            vec![Lambda::var(left.clone()), Lambda::var(right.clone())],
            Location::none(),
        );
        let input = Lambda::let_(
            LetKind::Alias,
            left,
            Lambda::const_(Constant::string("a")),
            Lambda::let_(
                LetKind::Alias,
                right,
                Lambda::const_(Constant::string("b")),
                concat,
            ),
        );
        assert_exact(&run(input), &Lambda::const_(Constant::string("ab")));
    }

    #[test]
    fn reifies_independent_reference_reads_and_writes() {
        let reference = id("reference", 1);
        let read = || {
            Lambda::prim(
                Primitive::Pfield(0, FieldDbgInfo::Tuple),
                vec![Lambda::var(reference.clone())],
                Location::none(),
            )
        };
        let write = Lambda::prim(
            Primitive::Psetfield(0, SetFieldDbgInfo::RecordSet("value".into())),
            vec![Lambda::var(reference.clone()), int(2)],
            Location::none(),
        );
        let input = Lambda::let_(
            LetKind::Strict,
            reference.clone(),
            Lambda::prim(
                Primitive::Pmakeblock(crate::lambda::TagInfo::Tuple, Mutable::Mutable),
                vec![int(1)],
                Location::none(),
            ),
            Lambda::seq(write, read()),
        );
        let expected = Lambda::let_(
            LetKind::Variable,
            reference.clone(),
            int(1),
            Lambda::seq(
                Lambda::assign(reference.clone(), int(2)),
                Lambda::var(reference),
            ),
        );
        assert_exact(&run(input), &expected);
    }

    #[test]
    fn closure_reference_keeps_mutable_block() {
        let reference = id("reference", 1);
        let parameter = id("parameter", 2);
        let closure = Lambda::function_(
            1,
            vec![parameter],
            Lambda::prim(
                Primitive::Pfield(0, FieldDbgInfo::Tuple),
                vec![Lambda::var(reference.clone())],
                Location::none(),
            ),
            FunctionAttribute::default(),
        );
        let input = Lambda::let_(
            LetKind::Strict,
            reference.clone(),
            Lambda::prim(
                Primitive::Pmakeblock(crate::lambda::TagInfo::Tuple, Mutable::Mutable),
                vec![int(1)],
                Location::none(),
            ),
            closure,
        );
        let actual = run(input);
        let Lambda::Llet(LetKind::StrictOpt, actual_id, value, _) = actual else {
            panic!("expected retained reference")
        };
        assert_eq!(actual_id.name(), reference.name());
        assert_eq!(actual_id.stamp(), reference.stamp());
        assert_eq!(actual_id.flags(), reference.flags());
        assert!(matches!(*value, Lambda::Lprim(_)));
    }
}
