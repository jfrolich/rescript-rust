//! Indexed let simplification for `compiler/core/lam_pass_lets_dce.ml`.

use ahash::AHashMap;

use crate::ident::Ident;
use crate::lambda::indexed::{IndexedLambda, IndexedLambdaContext, NodeId, NodeSnapshot, NodeView};
use crate::lambda::lam_analysis_indexed::no_side_effects;
use crate::lambda::lam_beta_reduce_indexed::no_names_beta_reduce;
use crate::lambda::lam_compat::{FieldDbgInfo, LetKind};
use crate::lambda::lam_constant::Constant;
use crate::lambda::lam_indexed_helpers::{append_rebuilt, append_refine_let};
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

fn string_value(store: &IndexedLambda, state: &Lets<'_>, node: NodeId) -> Option<String> {
    match store.view(node) {
        NodeView::Const(Constant::String(s)) => Some(s.clone()),
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
        NodeSnapshot::Let(LetKind::Strict, id, value, body) if matches!(store.view(value), NodeView::Prim(Primitive::Pmakeblock(_, Mutable::Mutable), args, _) if args.len() == 1) =>
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
                    let reference =
                        append_rebuilt(store, NodeSnapshot::Prim(primitive, vec![init], loc));
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
                    if matches!(store.view(*base), NodeView::GlobalModule(_))
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
            if let NodeView::Const(Constant::String(s)) = store.view(value) {
                state.strings.insert(id.clone(), s.clone());
                let body = simplify(store, state, body);
                return append_rebuilt(store, NodeSnapshot::Let(LetKind::Alias, id, value, body));
            }
            let body = simplify(store, state, body);
            let value = simplify(store, state, value);
            append_rebuilt(store, NodeSnapshot::Let(LetKind::Alias, id, value, body))
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
                        let reference =
                            append_rebuilt(store, NodeSnapshot::Prim(primitive, vec![init], loc));
                        append_refine_let(store, LetKind::StrictOpt, id, reference, body)
                    }
                };
            }
            let value = simplify(store, state, value);
            if let NodeView::Const(Constant::String(s)) = store.view(value) {
                state.strings.insert(id.clone(), s.clone());
                let body = simplify(store, state, body);
                return append_rebuilt(store, NodeSnapshot::Let(LetKind::Alias, id, value, body));
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
                && let NodeView::Const(Constant::String(s)) = store.view(value)
            {
                state.strings.insert(id.clone(), s.clone());
                let body = simplify(store, state, body);
                return append_rebuilt(store, NodeSnapshot::Let(LetKind::Alias, id, value, body));
            }
            let body = simplify(store, state, body);
            append_refine_let(store, kind, id, value, body)
        }
        NodeSnapshot::Sequence(first, second) => {
            let second = simplify(store, state, second);
            let first = simplify(store, state, first);
            append_rebuilt(store, NodeSnapshot::Sequence(first, second))
        }
        NodeSnapshot::Apply(function, args, info, jsx) => {
            if let NodeSnapshot::Function(_, params, body, attr) = store.snapshot(function)
                && params.len() == args.len()
                && !attr.async_
                && attr.directive.is_none()
            {
                let reduced =
                    no_names_beta_reduce(store, &params, body, &args, state.beta_hash_capacity);
                return simplify(store, state, reduced);
            }
            let args = args
                .into_iter()
                .map(|node| simplify(store, state, node))
                .collect();
            let function = simplify(store, state, function);
            append_rebuilt(store, NodeSnapshot::Apply(function, args, info, jsx))
        }
        NodeSnapshot::Prim(Primitive::Pstringadd, args, loc) if args.len() == 2 => {
            let left = simplify(store, state, args[0]);
            let right = simplify(store, state, args[1]);
            match (
                string_value(store, state, left),
                string_value(store, state, right),
            ) {
                (Some(left), Some(right)) => {
                    store.append(NodeSnapshot::Const(Constant::String(left + &right)))
                }
                _ => append_rebuilt(
                    store,
                    NodeSnapshot::Prim(Primitive::Pstringadd, vec![left, right], loc),
                ),
            }
        }
        NodeSnapshot::Const(_)
        | NodeSnapshot::GlobalModule(_)
        | NodeSnapshot::Break
        | NodeSnapshot::Continue => node,
        NodeSnapshot::Function(arity, params, body, attr) => {
            let body = simplify(store, state, body);
            append_rebuilt(store, NodeSnapshot::Function(arity, params, body, attr))
        }
        NodeSnapshot::LetRec(bindings, body) => {
            let body = simplify(store, state, body);
            let bindings = bindings
                .into_iter()
                .map(|(id, value)| (id, simplify(store, state, value)))
                .collect();
            append_rebuilt(store, NodeSnapshot::LetRec(bindings, body))
        }
        NodeSnapshot::Prim(primitive, args, loc) => {
            let args = args
                .into_iter()
                .map(|node| simplify(store, state, node))
                .collect();
            append_rebuilt(store, NodeSnapshot::Prim(primitive, args, loc))
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
            // The `let ... and ...` group in the reference runs left-to-right.
            let scrutinee = simplify(store, state, scrutinee);
            let consts = consts
                .into_iter()
                .map(|(key, node)| (key, simplify(store, state, node)))
                .collect();
            let blocks = blocks
                .into_iter()
                .map(|(key, node)| (key, simplify(store, state, node)))
                .collect();
            let fail_action = fail_action.map(|node| simplify(store, state, node));
            append_rebuilt(
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
            )
        }
        NodeSnapshot::StringSwitch(scrutinee, cases, default) => {
            let default = default.map(|node| simplify(store, state, node));
            let cases = cases
                .into_iter()
                .map(|(key, node)| (key, simplify(store, state, node)))
                .collect();
            let scrutinee = simplify(store, state, scrutinee);
            append_rebuilt(store, NodeSnapshot::StringSwitch(scrutinee, cases, default))
        }
        NodeSnapshot::StaticRaise(exit, args) => {
            let args = args
                .into_iter()
                .map(|node| simplify(store, state, node))
                .collect();
            append_rebuilt(store, NodeSnapshot::StaticRaise(exit, args))
        }
        NodeSnapshot::StaticCatch(body, exit, params, handler) => {
            let handler = simplify(store, state, handler);
            let body = simplify(store, state, body);
            append_rebuilt(
                store,
                NodeSnapshot::StaticCatch(body, exit, params, handler),
            )
        }
        NodeSnapshot::TryWith(body, id, handler) => {
            let handler = simplify(store, state, handler);
            let body = simplify(store, state, body);
            append_rebuilt(store, NodeSnapshot::TryWith(body, id, handler))
        }
        NodeSnapshot::IfThenElse(condition, then_node, else_node) => {
            let else_node = simplify(store, state, else_node);
            let then_node = simplify(store, state, then_node);
            let condition = simplify(store, state, condition);
            append_rebuilt(
                store,
                NodeSnapshot::IfThenElse(condition, then_node, else_node),
            )
        }
        NodeSnapshot::While(condition, body) => {
            let body = simplify(store, state, body);
            let condition = simplify(store, state, condition);
            append_rebuilt(store, NodeSnapshot::While(condition, body))
        }
        NodeSnapshot::For(id, from, to, direction, body) => {
            let body = simplify(store, state, body);
            let to = simplify(store, state, to);
            let from = simplify(store, state, from);
            append_rebuilt(store, NodeSnapshot::For(id, from, to, direction, body))
        }
        NodeSnapshot::ForOf(id, iterable, body) => {
            let body = simplify(store, state, body);
            let iterable = simplify(store, state, iterable);
            append_rebuilt(store, NodeSnapshot::ForOf(id, iterable, body))
        }
        NodeSnapshot::ForAwaitOf(id, iterable, body) => {
            let body = simplify(store, state, body);
            let iterable = simplify(store, state, iterable);
            append_rebuilt(store, NodeSnapshot::ForAwaitOf(id, iterable, body))
        }
        NodeSnapshot::Assign(id, value) => {
            let value = simplify(store, state, value);
            append_rebuilt(store, NodeSnapshot::Assign(id, value))
        }
    }
}

impl IndexedLambdaContext {
    /// Counts occurrences, eliminates references, and simplifies lets in one store.
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
    use crate::context::IdGenerator;
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
                ffi: Box::new(crate::lambda::lam_primitive::ExternalDecl::test_val("", 0)),
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
    fn strict_opt_unused_skips_effectful_initializer() {
        let value = id("value", 1);
        let result = id("result", 2);
        let effect = Lambda::prim(
            Primitive::PjsCall {
                prim_name: "must_not_run".into(),
                arg_types: vec![],
                ffi: Box::new(crate::lambda::lam_primitive::ExternalDecl::test_val("", 0)),
                transformed_jsx: false,
            },
            vec![],
            Location::new_for_error("lets.res", 1, 2),
        );
        assert_exact(
            &run(Lambda::let_(
                LetKind::StrictOpt,
                value,
                effect,
                Lambda::var(result.clone()),
            )),
            &Lambda::var(result),
        );
    }

    #[test]
    fn native_int_alias_is_not_reference_small_constant() {
        let value = id("value", 1);
        let native = Lambda::const_(Constant::NativeInt {
            i: 7,
            comment: None,
        });
        let actual = run(Lambda::let_(
            LetKind::Alias,
            value.clone(),
            native.clone(),
            Lambda::seq(Lambda::var(value.clone()), Lambda::var(value.clone())),
        ));
        let expected = Lambda::let_(
            LetKind::Alias,
            value.clone(),
            native,
            Lambda::seq(Lambda::var(value.clone()), Lambda::var(value)),
        );
        assert_exact(&actual, &expected);
    }

    #[test]
    fn inlineable_function_beta_reduces_but_async_function_does_not() {
        let parameter = id("parameter", 1);
        let call = |attr: FunctionAttribute| {
            Lambda::apply(
                Lambda::function_(
                    1,
                    vec![parameter.clone()],
                    Lambda::prim(
                        Primitive::Paddint,
                        vec![Lambda::var(parameter.clone()), int(1)],
                        Location::none(),
                    ),
                    attr,
                ),
                vec![int(2)],
                crate::lambda::ApInfo {
                    loc: Location::new_for_error("lets.res", 3, 4),
                    inlined: crate::lambda::InlineAttribute::Default,
                    status: crate::lambda::ApplyStatus::Na,
                },
                true,
            )
        };
        assert_exact(
            &run(call(FunctionAttribute::default())),
            &Lambda::prim(Primitive::Paddint, vec![int(2), int(1)], Location::none()),
        );
        let async_attr = FunctionAttribute {
            async_: true,
            ..FunctionAttribute::default()
        };
        let async_call = call(async_attr.clone());
        assert_exact(&run(async_call.clone()), &async_call);
    }

    #[test]
    fn occurrence_and_let_beta_share_native_hash_capacity() {
        let params = (0..65)
            .map(|index| id(&format!("p{index}"), index + 1))
            .collect::<Vec<_>>();
        let input = Lambda::apply(
            Lambda::function_(
                65,
                params.clone(),
                Lambda::prim(
                    Primitive::Paddint,
                    vec![
                        Lambda::var(params[0].clone()),
                        Lambda::var(params[0].clone()),
                    ],
                    Location::none(),
                ),
                FunctionAttribute::default(),
            ),
            (0..65).map(int).collect(),
            crate::lambda::ApInfo {
                loc: Location::none(),
                inlined: crate::lambda::InlineAttribute::Default,
                status: crate::lambda::ApplyStatus::Na,
            },
            false,
        );
        let mut context = IndexedLambdaContext::from_lambda(input, []);
        context.simplify_lets();
        let (_, _, capacity) = context.optimizer_parts_mut();
        assert_eq!(*capacity, 64);
        assert_exact(
            &context.materialize(),
            &Lambda::prim(Primitive::Paddint, vec![int(0), int(0)], Location::none()),
        );
    }

    #[test]
    fn smart_control_flow_runs_after_child_simplification() {
        let value = id("value", 1);
        let input = Lambda::LifThenElse(
            Box::new(Lambda::const_(Constant::JsTrue)),
            Box::new(Lambda::let_(
                LetKind::Alias,
                value.clone(),
                int(9),
                Lambda::var(value),
            )),
            Box::new(Lambda::prim(
                Primitive::PjsCall {
                    prim_name: "unselected".into(),
                    arg_types: vec![],
                    ffi: Box::new(crate::lambda::lam_primitive::ExternalDecl::test_val("", 0)),
                    transformed_jsx: false,
                },
                vec![],
                Location::none(),
            )),
        );
        assert_exact(&run(input), &int(9));
    }

    #[test]
    fn recursive_and_control_flow_occurrences_keep_bindings() {
        let value = id("value", 1);
        let recursive = id("recursive", 2);
        let input = Lambda::let_(
            LetKind::Strict,
            value.clone(),
            int(4),
            Lambda::letrec(
                vec![(
                    recursive.clone(),
                    Lambda::function_(
                        0,
                        vec![],
                        Lambda::if_(
                            Lambda::const_(Constant::JsTrue),
                            Lambda::var(value.clone()),
                            Lambda::var(recursive),
                        ),
                        FunctionAttribute::default(),
                    ),
                )],
                Lambda::var(value.clone()),
            ),
        );
        let actual = run(input);
        let Lambda::Llet(_, actual, _, _) = actual else {
            panic!("expected retained outer binding")
        };
        assert_eq!(
            (actual.name(), actual.stamp(), actual.flags()),
            (value.name(), value.stamp(), value.flags())
        );
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
    fn full_indexed_sequence_keeps_one_store_generator_and_metadata_roots() {
        let function = id("function", 1);
        let attr = FunctionAttribute {
            inline: crate::lambda::InlineAttribute::Never,
            ..FunctionAttribute::default()
        };
        let input = Lambda::let_(
            LetKind::Strict,
            function.clone(),
            Lambda::function_(2, vec![id("a", 2), id("b", 3)], int(0), attr.clone()),
            Lambda::apply(
                Lambda::var(function.clone()),
                vec![int(1)],
                crate::lambda::ApInfo {
                    loc: Location::new_for_error("pipeline.res", 10, 20),
                    inlined: crate::lambda::InlineAttribute::Default,
                    status: crate::lambda::ApplyStatus::Na,
                },
                true,
            ),
        );
        let generator = IdGenerator::with_start_stamp(200);
        let mut context = IndexedLambdaContext::from_lambda(input, [function.clone()]);
        context.collect_info();
        context.simplify_exits(&generator);
        context.collect_info();
        let mut inline = |_: &Ident, _: &str| None;
        context.simplify_alias(&generator, false, &mut inline);
        context.deep_flatten(&generator);
        let mut arity = |_: &Ident, _: &str| None;
        context.alpha_conversion_with_external_arity(&generator, &mut arity);
        context.simplify_lets();

        assert_eq!(generator.current_stamp(), 201);
        let expected_param = Ident::new("param", 201, IdentFlags::NONE);
        let expected = Lambda::let_(
            LetKind::StrictOpt,
            function.clone(),
            Lambda::function_(2, vec![id("a", 2), id("b", 3)], int(0), attr),
            Lambda::function_(
                1,
                vec![expected_param.clone()],
                Lambda::apply(
                    Lambda::var(function),
                    vec![int(1), Lambda::var(expected_param.clone())],
                    crate::lambda::ApInfo {
                        loc: Location::new_for_error("pipeline.res", 10, 20),
                        inlined: crate::lambda::InlineAttribute::Default,
                        status: crate::lambda::ApplyStatus::InferFull,
                    },
                    false,
                ),
                FunctionAttribute::default(),
            ),
        );
        assert_exact(&context.materialize(), &expected);
        let Lambda::Llet(_, _, _, eta) = context.materialize() else {
            panic!("expected let")
        };
        let Lambda::Lfunction(eta) = *eta else {
            panic!("expected eta")
        };
        assert_eq!(
            (
                eta.params[0].name(),
                eta.params[0].stamp(),
                eta.params[0].flags()
            ),
            (
                expected_param.name(),
                expected_param.stamp(),
                expected_param.flags()
            )
        );
        assert_eq!(
            context.storage_measurements(),
            crate::lambda::indexed::IndexedStorageMeasurements {
                node_allocations: 21,
                current_root_edge_visits: 7,
                current_root_unique_nodes: 8,
                metadata_unique_nodes: 2,
                backend_unique_nodes: 0,
                live_unique_nodes: 9,
                superseded_nodes: 12,
                hot_node_occupied_bytes: 168,
                hot_node_capacity_bytes: 256,
                side_payload_shallow_occupied_bytes: 1140,
                side_payload_shallow_capacity_bytes: 1600,
                nested_heap_bytes_included: false,
                current_live_side_payload_shallow_bytes: 384,
                backend_retained_only_side_payload_shallow_bytes: 0,
                metadata_retained_only_side_payload_shallow_bytes: 80,
                superseded_unreachable_side_payload_shallow_bytes: 676,
            }
        );
    }

    #[test]
    fn direct_reference_keeps_mutable_block_after_refine_let() {
        let reference = Ident::new("reference", 1, IdentFlags::PREDEF_EXN);
        let input = Lambda::let_(
            LetKind::Strict,
            reference.clone(),
            Lambda::prim(
                Primitive::Pmakeblock(crate::lambda::TagInfo::Tuple, Mutable::Mutable),
                vec![int(1)],
                Location::new_for_error("ref.res", 1, 2),
            ),
            Lambda::var(reference.clone()),
        );
        let actual = run(input);
        let Lambda::Lprim(primitive) = actual else {
            panic!("expected retained reference block")
        };
        assert!(matches!(
            primitive.primitive,
            Primitive::Pmakeblock(crate::lambda::TagInfo::Tuple, Mutable::Mutable)
        ));
        assert_eq!(primitive.loc, Location::new_for_error("ref.res", 1, 2));
        assert!(matches!(
            primitive.args.as_slice(),
            [Lambda::Lconst(Constant::Int { i: 1, .. })]
        ));
    }

    #[test]
    fn shared_reference_reads_are_rewritten_independently() {
        let reference = id("reference", 1);
        let input = Lambda::let_(
            LetKind::Strict,
            reference.clone(),
            Lambda::prim(
                Primitive::Pmakeblock(crate::lambda::TagInfo::Tuple, Mutable::Mutable),
                vec![int(1)],
                Location::none(),
            ),
            Lambda::prim(
                Primitive::Pfield(0, FieldDbgInfo::Tuple),
                vec![Lambda::var(reference.clone())],
                Location::none(),
            ),
        );
        let mut context = IndexedLambdaContext::from_lambda(input, []);
        let NodeView::Let(kind, id, value, read) = context.store().view(context.current_root())
        else {
            panic!("expected let")
        };
        let (kind, id, value, read) = (kind, id.clone(), value, read);
        let body = context.store_mut().append_sequence(read, read);
        let root = context
            .store_mut()
            .append(NodeSnapshot::Let(kind, id, value, body));
        context.replace_root(root);
        context.simplify_lets();
        let expected = Lambda::let_(
            LetKind::Variable,
            reference.clone(),
            int(1),
            Lambda::seq(Lambda::var(reference.clone()), Lambda::var(reference)),
        );
        assert_exact(&context.materialize(), &expected);
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
