//! Indexed alpha conversion and eta expansion for
//! `compiler/core/lam_pass_alpha_conversion.ml` and `lam_eta_conversion.ml`.

use crate::context::IdGenerator;
use crate::ident::Ident;
use crate::lambda::indexed::{IndexedLambda, IndexedLambdaContext, NodeId, NodeSnapshot, NodeView};
use crate::lambda::lam_compat::{FieldDbgInfo, LetKind};
use crate::lambda::lam_constant::Constant;
use crate::lambda::lam_indexed_helpers::{append_rebuilt, map_children};
use crate::lambda::lam_pass_collect::ExternalArityResolver;
use crate::lambda::lam_pass_collect_indexed::{IndexedLamStats, get_arity_external};
use crate::lambda::lam_primitive::Primitive;
use crate::lambda::{ApInfo, ApplyStatus, FunctionAttribute};
use crate::location::Location;

fn safe_to_share(store: &IndexedLambda, node: NodeId) -> bool {
    match store.view(node) {
        NodeView::Var(_) | NodeView::Function(_, _, _, _) => true,
        NodeView::Const(
            Constant::Int { .. }
            | Constant::Constructor(_)
            | Constant::Char(_)
            | Constant::String { .. }
            | Constant::ImmString(_)
            | Constant::Float(_)
            | Constant::BigInt { .. }
            | Constant::Pointer(_)
            | Constant::JsTrue
            | Constant::JsFalse
            | Constant::JsUndefined { .. },
        ) => true,
        NodeView::Prim(Primitive::Pfield(_, FieldDbgInfo::Module { .. }), _, _) => true,
        _ => false,
    }
}

fn transform_under_supply(
    store: &mut IndexedLambda,
    id_gen: &IdGenerator,
    missing: i32,
    info: ApInfo,
    function: NodeId,
    args: Vec<NodeId>,
) -> NodeId {
    let extra_params = (0..missing)
        .map(|_| id_gen.create("param"))
        .collect::<Vec<_>>();
    let extra_args = extra_params
        .iter()
        .map(|id| store.append(NodeSnapshot::Var(id.clone())))
        .collect::<Vec<_>>();

    let mut shared = Vec::with_capacity(args.len() + 1);
    shared.push(function);
    shared.extend(args);
    let mut bindings = Vec::new();
    for node in &mut shared {
        if !safe_to_share(store, *node) {
            let id = id_gen.create("partial_arg");
            bindings.push((id.clone(), *node));
            *node = store.append(NodeSnapshot::Var(id));
        }
    }
    let function = shared.remove(0);
    shared.extend(extra_args);
    let body = append_rebuilt(store, NodeSnapshot::Apply(function, shared, info, false));
    let mut result = append_rebuilt(
        store,
        NodeSnapshot::Function(missing, extra_params, body, FunctionAttribute::default()),
    );
    // `Ext_list.fold_left bindings rest` wraps each next binding outside the
    // previous result, so the last source binding is outermost.
    for (id, value) in bindings {
        result = append_rebuilt(store, NodeSnapshot::Let(LetKind::Strict, id, value, result));
    }
    result
}

fn simplify_many(
    store: &mut IndexedLambda,
    metadata: &mut IndexedLamStats,
    id_gen: &IdGenerator,
    external: &mut ExternalArityResolver<'_>,
    nodes: Vec<NodeId>,
) -> Vec<NodeId> {
    nodes
        .into_iter()
        .map(|node| simplify(store, metadata, id_gen, external, node))
        .collect()
}

fn simplify(
    store: &mut IndexedLambda,
    metadata: &mut IndexedLamStats,
    id_gen: &IdGenerator,
    external: &mut ExternalArityResolver<'_>,
    node: NodeId,
) -> NodeId {
    match store.snapshot(node) {
        NodeSnapshot::Var(_)
        | NodeSnapshot::GlobalModule(_, _)
        | NodeSnapshot::Const(_)
        | NodeSnapshot::Break
        | NodeSnapshot::Continue => node,
        NodeSnapshot::Apply(function, args, info, jsx) => {
            let arities = get_arity_external(store, metadata, function, external).extract_arity();
            let len = args.len() as i32;
            match arities.first().copied() {
                None | Some(0) => {
                    let function = simplify(store, metadata, id_gen, external, function);
                    let args = simplify_many(store, metadata, id_gen, external, args);
                    append_rebuilt(store, NodeSnapshot::Apply(function, args, info, jsx))
                }
                Some(arity) if arity == len => {
                    let function = simplify(store, metadata, id_gen, external, function);
                    let args = simplify_many(store, metadata, id_gen, external, args);
                    let info = ApInfo {
                        status: ApplyStatus::InferFull,
                        ..info
                    };
                    append_rebuilt(store, NodeSnapshot::Apply(function, args, info, jsx))
                }
                Some(arity) if arity > len => {
                    let function = simplify(store, metadata, id_gen, external, function);
                    let args = simplify_many(store, metadata, id_gen, external, args);
                    let info = ApInfo {
                        status: ApplyStatus::InferFull,
                        ..info
                    };
                    transform_under_supply(store, id_gen, arity - len, info, function, args)
                }
                Some(arity) => {
                    let split = arity as usize;
                    let function = simplify(store, metadata, id_gen, external, function);
                    let first =
                        simplify_many(store, metadata, id_gen, external, args[..split].to_vec());
                    let rest =
                        simplify_many(store, metadata, id_gen, external, args[split..].to_vec());
                    let inner_info = ApInfo {
                        status: ApplyStatus::InferFull,
                        ..info.clone()
                    };
                    let inner = append_rebuilt(
                        store,
                        NodeSnapshot::Apply(function, first, inner_info, false),
                    );
                    append_rebuilt(store, NodeSnapshot::Apply(inner, rest, info, jsx))
                }
            }
        }
        snapshot => {
            let mapped = map_children(store, snapshot, |store, child| {
                simplify(store, metadata, id_gen, external, child)
            });
            append_rebuilt(store, mapped)
        }
    }
}

impl IndexedLambdaContext {
    /// Runs alpha conversion over the canonical root with external arity lookup.
    pub fn alpha_conversion_with_external_arity(
        &mut self,
        id_gen: &IdGenerator,
        external: &mut ExternalArityResolver<'_>,
    ) {
        let root = self.current_root();
        let root = {
            let (store, metadata, _) = self.optimizer_parts_mut();
            simplify(store, metadata, id_gen, external, root)
        };
        self.replace_root(root);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ident::IdentFlags;
    use crate::lambda::lam_compile_context::ExternalArityInfo;
    use crate::lambda::{Apply, Constant, Lambda};

    fn id(name: &str, stamp: i32) -> Ident {
        Ident::new(name, stamp, IdentFlags::NONE)
    }
    fn info(status: ApplyStatus) -> ApInfo {
        ApInfo {
            loc: Location::none(),
            inlined: crate::lambda::InlineAttribute::Default,
            status,
        }
    }
    fn apply(function: Lambda, args: Vec<Lambda>, status: ApplyStatus, jsx: bool) -> Lambda {
        Lambda::Lapply(Apply {
            ap_func: Box::new(function),
            ap_args: args,
            ap_info: info(status),
            ap_transformed_jsx: jsx,
        })
    }
    fn run(input: Lambda, start: i32) -> (Lambda, i32) {
        let generator = IdGenerator::with_start_stamp(start);
        let mut context = IndexedLambdaContext::from_lambda(input, []);
        context.collect_info();
        let mut external = |_: &Ident, _: bool, _: &str| None;
        context.alpha_conversion_with_external_arity(&generator, &mut external);
        (context.materialize(), generator.current_stamp())
    }

    #[test]
    fn indexed_branches_match_tree_reference_port_without_effectful_eta_bindings() {
        let function = id("function", 1);
        let definition = Lambda::function_(
            2,
            vec![id("a", 2), id("b", 3)],
            Lambda::const_(Constant::int(0)),
            FunctionAttribute::default(),
        );
        let input = Lambda::let_(
            LetKind::Strict,
            function.clone(),
            definition,
            Lambda::seq(
                apply(
                    Lambda::var(function.clone()),
                    vec![],
                    ApplyStatus::Na,
                    false,
                ),
                Lambda::seq(
                    apply(
                        Lambda::var(function.clone()),
                        vec![Lambda::const_(Constant::int(1))],
                        ApplyStatus::Na,
                        true,
                    ),
                    Lambda::seq(
                        apply(
                            Lambda::var(function.clone()),
                            vec![
                                Lambda::const_(Constant::int(1)),
                                Lambda::const_(Constant::int(2)),
                            ],
                            ApplyStatus::Na,
                            false,
                        ),
                        apply(
                            Lambda::var(function),
                            vec![
                                Lambda::const_(Constant::int(1)),
                                Lambda::const_(Constant::int(2)),
                                Lambda::const_(Constant::int(3)),
                            ],
                            ApplyStatus::Na,
                            true,
                        ),
                    ),
                ),
            ),
        );
        let mut tree_metadata = crate::lambda::lam_compile_context::LamStats::new(vec![]);
        crate::lambda::lam_pass_collect::collect_info(&mut tree_metadata, &input);
        let mut tree_external = |_: &Ident, _: bool, _: &str| None;
        let expected =
            crate::lambda::lam_pass_alpha_conversion::alpha_conversion_with_external_arity_owned(
                &mut tree_metadata,
                input.clone(),
                &mut tree_external,
            );
        let indexed_generator = IdGenerator::new();
        let mut context = IndexedLambdaContext::from_lambda(input, []);
        context.collect_info();
        let mut indexed_external = |_: &Ident, _: bool, _: &str| None;
        context.alpha_conversion_with_external_arity(&indexed_generator, &mut indexed_external);
        assert_eq!(
            format!("{expected:#?}"),
            format!("{:#?}", context.materialize())
        );
        assert_eq!(
            indexed_generator.current_stamp(),
            tree_metadata.id_gen.current_stamp()
        );
    }

    #[test]
    fn external_arity_queries_follow_edge_order_and_preserve_location() {
        let module = id("External", 0);
        let location = Location::new_for_error("alpha.res", 10, 20);
        let access = |name: &str| {
            Lambda::prim(
                Primitive::Pfield(0, FieldDbgInfo::Module { name: name.into() }),
                vec![Lambda::LglobalModule(module.clone(), true)],
                location.clone(),
            )
        };
        let call = |function, argument, jsx| {
            Lambda::Lapply(Apply {
                ap_func: Box::new(function),
                ap_args: vec![Lambda::const_(Constant::int(argument))],
                ap_info: ApInfo {
                    loc: location.clone(),
                    inlined: crate::lambda::InlineAttribute::Default,
                    status: ApplyStatus::Na,
                },
                ap_transformed_jsx: jsx,
            })
        };
        let input = Lambda::seq(
            call(access("first"), 1, false),
            call(access("second"), 2, true),
        );
        let generator = IdGenerator::with_start_stamp(10);
        let mut context = IndexedLambdaContext::from_lambda(input, []);
        context.collect_info();
        let mut calls = Vec::new();
        let mut external = |module: &Ident, dynamic: bool, field: &str| {
            calls.push((module.name().to_string(), dynamic, field.to_string()));
            Some(ExternalArityInfo::Single(
                crate::lambda::lam_arity::Arity::info(vec![1], false),
            ))
        };
        context.alpha_conversion_with_external_arity(&generator, &mut external);
        assert_eq!(
            calls,
            vec![
                ("External".into(), true, "first".into()),
                ("External".into(), true, "second".into())
            ]
        );
        let Lambda::Lsequence(first, second) = context.materialize() else {
            panic!("expected sequence")
        };
        for (node, jsx) in [(*first, false), (*second, true)] {
            let Lambda::Lapply(call) = node else {
                panic!("expected call")
            };
            assert_eq!(call.ap_info.status, ApplyStatus::InferFull);
            assert_eq!(call.ap_info.loc, location);
            assert_eq!(call.ap_transformed_jsx, jsx);
        }
        assert_eq!(generator.current_stamp(), 10);
    }

    #[test]
    fn exact_and_over_application_preserve_status_jsx_and_location() {
        let function = id("function", 1);
        let p = id("p", 2);
        let q = id("q", 3);
        let definition = Lambda::function_(
            2,
            vec![p.clone(), q.clone()],
            Lambda::var(p),
            FunctionAttribute::default(),
        );
        for (args, over) in [
            (
                vec![
                    Lambda::const_(Constant::int(1)),
                    Lambda::const_(Constant::int(2)),
                ],
                false,
            ),
            (
                vec![
                    Lambda::const_(Constant::int(1)),
                    Lambda::const_(Constant::int(2)),
                    Lambda::const_(Constant::int(3)),
                ],
                true,
            ),
        ] {
            let input = Lambda::let_(
                LetKind::Strict,
                function.clone(),
                definition.clone(),
                apply(Lambda::var(function.clone()), args, ApplyStatus::Na, true),
            );
            let (actual, frontier) = run(input, 20);
            let Lambda::Llet(_, _, _, body) = actual else {
                panic!("expected let")
            };
            if over {
                let Lambda::Lapply(outer) = *body else {
                    panic!("expected outer apply")
                };
                assert!(outer.ap_transformed_jsx);
                assert_eq!(outer.ap_info.status, ApplyStatus::Na);
                let Lambda::Lapply(inner) = *outer.ap_func else {
                    panic!("expected inner apply")
                };
                assert!(!inner.ap_transformed_jsx);
                assert_eq!(inner.ap_info.status, ApplyStatus::InferFull);
            } else {
                let Lambda::Lapply(call) = *body else {
                    panic!("expected apply")
                };
                assert!(call.ap_transformed_jsx);
                assert_eq!(call.ap_info.status, ApplyStatus::InferFull);
            }
            assert_eq!(frontier, 20);
        }
    }

    #[test]
    fn effectful_function_and_argument_use_reference_eta_binding_order() {
        let known = id("known", 1);
        let effect = |name: &str| {
            Lambda::prim(
                Primitive::PjsCall {
                    prim_name: name.into(),
                    arg_types: vec![],
                    ffi: crate::lambda::lam_primitive::ExternalFfiSpec {
                        kind: crate::lambda::lam_primitive::ExternalFfiKind::Default,
                        spec: None,
                        obj_params: None,
                        return_wrapper:
                            crate::lambda::lam_primitive::ExternalReturnWrapper::Identity,
                        inline_constant: None,
                    },
                    dynamic_import: false,
                    transformed_jsx: false,
                },
                vec![],
                Location::none(),
            )
        };
        let function_expression = Lambda::let_(
            LetKind::Strict,
            id("side", 2),
            effect("callee"),
            Lambda::var(known.clone()),
        );
        let input = Lambda::let_(
            LetKind::Strict,
            known,
            Lambda::function_(
                3,
                vec![id("a", 3), id("b", 4), id("c", 5)],
                Lambda::const_(Constant::int(0)),
                FunctionAttribute::default(),
            ),
            apply(
                function_expression,
                vec![effect("argument")],
                ApplyStatus::Na,
                true,
            ),
        );
        let (actual, frontier) = run(input, 100);
        assert_eq!(frontier, 104);
        let Lambda::Llet(_, _, _, body) = actual else {
            panic!("expected definition")
        };
        let Lambda::Llet(LetKind::Strict, outer, outer_value, inner) = *body else {
            panic!("expected outer argument binding")
        };
        assert_eq!(
            (outer.name(), outer.stamp(), outer.flags()),
            ("partial_arg", 104, IdentFlags::NONE)
        );
        assert!(matches!(*outer_value, Lambda::Lprim(_)));
        let Lambda::Llet(LetKind::Strict, inner_id, inner_value, eta) = *inner else {
            panic!("expected inner function binding")
        };
        assert_eq!(
            (inner_id.name(), inner_id.stamp(), inner_id.flags()),
            ("partial_arg", 103, IdentFlags::NONE)
        );
        assert!(matches!(*inner_value, Lambda::Llet(_, _, _, _)));
        let Lambda::Lfunction(function) = *eta else {
            panic!("expected eta function")
        };
        assert_eq!(function.params.len(), 2);
        assert_eq!(
            (
                function.params[0].name(),
                function.params[0].stamp(),
                function.params[0].flags()
            ),
            ("param", 101, IdentFlags::NONE)
        );
        assert_eq!(
            (
                function.params[1].name(),
                function.params[1].stamp(),
                function.params[1].flags()
            ),
            ("param", 102, IdentFlags::NONE)
        );
        let Lambda::Lapply(call) = *function.body else {
            panic!("expected eta call")
        };
        assert!(!call.ap_transformed_jsx);
        assert_eq!(call.ap_info.status, ApplyStatus::InferFull);
    }

    #[test]
    fn shared_under_application_freshens_each_semantic_edge() {
        let function = id("function", 1);
        let input = Lambda::let_(
            LetKind::Strict,
            function.clone(),
            Lambda::function_(
                2,
                vec![id("a", 2), id("b", 3)],
                Lambda::const_(Constant::int(0)),
                FunctionAttribute::default(),
            ),
            apply(
                Lambda::var(function),
                vec![Lambda::const_(Constant::int(1))],
                ApplyStatus::Na,
                false,
            ),
        );
        let generator = IdGenerator::with_start_stamp(50);
        let mut context = IndexedLambdaContext::from_lambda(input, []);
        context.collect_info();
        let original = context.current_root();
        let NodeView::Let(kind, id, value, call) = context.store().view(original) else {
            panic!("expected input let")
        };
        let (kind, id, value, call) = (kind, id.clone(), value, call);
        let shared_body = context.store_mut().append_sequence(call, call);
        let root = context
            .store_mut()
            .append(NodeSnapshot::Let(kind, id, value, shared_body));
        context.replace_root(root);
        let mut external = |_: &Ident, _: bool, _: &str| None;
        context.alpha_conversion_with_external_arity(&generator, &mut external);
        assert_eq!(generator.current_stamp(), 52);
        let Lambda::Llet(_, _, _, body) = context.materialize() else {
            panic!("expected let")
        };
        let Lambda::Lsequence(first, second) = *body else {
            panic!("expected sequence")
        };
        let (Lambda::Lfunction(first), Lambda::Lfunction(second)) = (*first, *second) else {
            panic!("expected independently expanded functions")
        };
        assert_eq!(
            (
                first.params[0].name(),
                first.params[0].stamp(),
                first.params[0].flags()
            ),
            ("param", 51, IdentFlags::NONE)
        );
        assert_eq!(
            (
                second.params[0].name(),
                second.params[0].stamp(),
                second.params[0].flags()
            ),
            ("param", 52, IdentFlags::NONE)
        );
    }

    #[test]
    fn repeated_alpha_call_preserves_frontier_and_async_metadata() {
        let function = id("function", 1);
        let attr = FunctionAttribute {
            async_: true,
            ..FunctionAttribute::default()
        };
        let input = Lambda::let_(
            LetKind::Strict,
            function.clone(),
            Lambda::function_(
                2,
                vec![id("a", 2), id("b", 3)],
                Lambda::const_(Constant::int(0)),
                attr.clone(),
            ),
            apply(
                Lambda::var(function),
                vec![Lambda::const_(Constant::int(1))],
                ApplyStatus::Na,
                true,
            ),
        );
        let generator = IdGenerator::with_start_stamp(70);
        let mut context = IndexedLambdaContext::from_lambda(input, []);
        context.collect_info();
        let mut external = |_: &Ident, _: bool, _: &str| None;
        context.alpha_conversion_with_external_arity(&generator, &mut external);
        let once = format!("{:#?}", context.materialize());
        assert_eq!(generator.current_stamp(), 71);
        context.alpha_conversion_with_external_arity(&generator, &mut external);
        assert_eq!(format!("{:#?}", context.materialize()), once);
        assert_eq!(generator.current_stamp(), 71);
        let Lambda::Llet(_, _, definition, _) = context.materialize() else {
            panic!("expected let")
        };
        let Lambda::Lfunction(definition) = *definition else {
            panic!("expected function")
        };
        assert_eq!(definition.attr.inline, attr.inline);
        assert_eq!(definition.attr.is_a_functor, attr.is_a_functor);
        assert_eq!(definition.attr.return_unit, attr.return_unit);
        assert_eq!(definition.attr.async_, attr.async_);
        assert_eq!(definition.attr.directive, attr.directive);
        assert_eq!(definition.attr.one_unit_arg, attr.one_unit_arg);
    }

    #[test]
    fn under_application_uses_pipeline_generator_and_reference_binding_order() {
        let effect = |name: &str| {
            Lambda::prim(
                Primitive::PjsCall {
                    prim_name: name.into(),
                    arg_types: vec![],
                    ffi: crate::lambda::lam_primitive::ExternalFfiSpec {
                        kind: crate::lambda::lam_primitive::ExternalFfiKind::Default,
                        spec: None,
                        obj_params: None,
                        return_wrapper:
                            crate::lambda::lam_primitive::ExternalReturnWrapper::Identity,
                        inline_constant: None,
                    },
                    dynamic_import: false,
                    transformed_jsx: false,
                },
                vec![],
                Location::none(),
            )
        };
        // A direct known function gives one missing parameter and one captured
        // effectful argument. The callee itself remains safe when it is a var.
        let known = id("known2", 9);
        let input = Lambda::let_(
            LetKind::Strict,
            known.clone(),
            Lambda::function_(
                2,
                vec![id("x", 10), id("y", 11)],
                Lambda::const_(Constant::int(0)),
                FunctionAttribute::default(),
            ),
            apply(
                Lambda::var(known),
                vec![effect("argument")],
                ApplyStatus::Na,
                true,
            ),
        );
        let (actual, frontier) = run(input, 100);
        assert_eq!(frontier, 102);
        let Lambda::Llet(_, _, _, body) = actual else {
            panic!("expected definition")
        };
        let Lambda::Llet(LetKind::Strict, partial, value, eta) = *body else {
            panic!("expected partial binding")
        };
        assert_eq!(partial.name(), "partial_arg");
        assert_eq!(partial.stamp(), 102);
        assert_eq!(partial.flags(), IdentFlags::NONE);
        assert!(matches!(*value, Lambda::Lprim(_)));
        let Lambda::Lfunction(function) = *eta else {
            panic!("expected eta function")
        };
        assert_eq!(function.arity, 1);
        assert_eq!(function.params[0].name(), "param");
        assert_eq!(function.params[0].stamp(), 101);
        assert_eq!(function.params[0].flags(), IdentFlags::NONE);
        let Lambda::Lapply(call) = *function.body else {
            panic!("expected eta call")
        };
        assert!(!call.ap_transformed_jsx);
        assert_eq!(call.ap_info.status, ApplyStatus::InferFull);
    }
}
