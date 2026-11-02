//! Indexed alpha conversion and eta expansion for
//! `compiler/core/lam_pass_alpha_conversion.ml` and `lam_eta_conversion.ml`.

use crate::context::IdGenerator;
use crate::lambda::indexed::{IndexedLambda, IndexedLambdaContext, NodeId, NodeSnapshot, NodeView};
use crate::lambda::lam_compat::{FieldDbgInfo, LetKind};
use crate::lambda::lam_constant::Constant;
use crate::lambda::lam_indexed_helpers::append_rebuilt;
use crate::lambda::lam_pass_collect::ExternalArityResolver;
use crate::lambda::lam_pass_collect_indexed::{IndexedLamStats, get_arity_external};
use crate::lambda::lam_primitive::Primitive;
use crate::lambda::{ApInfo, ApplyStatus, FunctionAttribute};

fn safe_to_share(store: &IndexedLambda, node: NodeId) -> bool {
    match store.view(node) {
        NodeView::Var(_) | NodeView::Function(_, _, _, _, _) => true,
        NodeView::Const(
            Constant::Int { .. }
            | Constant::Constructor(_)
            | Constant::Char(_)
            | Constant::String(_)
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
        .map(|id| store.append(NodeSnapshot::Var(*id)))
        .collect::<Vec<_>>();

    let mut shared = Vec::with_capacity(args.len() + 1);
    shared.push(function);
    shared.extend(args);
    let mut replacements = vec![None; shared.len()];
    for index in (0..shared.len()).rev() {
        if !safe_to_share(store, shared[index]) {
            replacements[index] = Some(id_gen.create("partial_arg"));
        }
    }
    let mut bindings = Vec::new();
    for (node, replacement) in shared.iter_mut().zip(replacements) {
        if let Some(id) = replacement {
            bindings.push((id, *node));
            *node = store.append(NodeSnapshot::Var(id));
        }
    }
    let function = shared.remove(0);
    shared.extend(extra_args);
    let body = append_rebuilt(store, NodeSnapshot::Apply(function, shared, info));
    let mut result = append_rebuilt(
        store,
        // lam_eta_conversion.ml:65 (before its removal): `~loc:Location.none`.
        NodeSnapshot::Function(
            missing,
            extra_params,
            body,
            FunctionAttribute::default(),
            crate::location::Location::none(),
        ),
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
        | NodeSnapshot::GlobalModule(_)
        | NodeSnapshot::Const(_)
        | NodeSnapshot::Break
        | NodeSnapshot::Continue => node,
        NodeSnapshot::Apply(function, args, info) => {
            let arities = get_arity_external(store, metadata, function, external).extract_arity();
            let len = args.len() as i32;
            match arities.first().copied() {
                None | Some(0) => {
                    // Native OCaml evaluates the `Lam.apply` arguments
                    // right-to-left; `Ext_list.map` itself runs left-to-right.
                    let args = simplify_many(store, metadata, id_gen, external, args);
                    let function = simplify(store, metadata, id_gen, external, function);
                    append_rebuilt(store, NodeSnapshot::Apply(function, args, info))
                }
                Some(arity) if arity == len => {
                    let args = simplify_many(store, metadata, id_gen, external, args);
                    let function = simplify(store, metadata, id_gen, external, function);
                    let info = ApInfo {
                        status: ApplyStatus::InferFull,
                        ..info
                    };
                    append_rebuilt(store, NodeSnapshot::Apply(function, args, info))
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
                    // The outer apply evaluates the rest list before the inner
                    // apply. The inner apply evaluates its first list before
                    // its function.
                    let rest =
                        simplify_many(store, metadata, id_gen, external, args[split..].to_vec());
                    let first =
                        simplify_many(store, metadata, id_gen, external, args[..split].to_vec());
                    let function = simplify(store, metadata, id_gen, external, function);
                    let inner_info = ApInfo {
                        status: ApplyStatus::InferFull,
                        ..info.clone()
                    };
                    let inner =
                        append_rebuilt(store, NodeSnapshot::Apply(function, first, inner_info));
                    append_rebuilt(store, NodeSnapshot::Apply(inner, rest, info))
                }
            }
        }
        NodeSnapshot::Function(arity, params, body, attr, loc) => {
            let body = simplify(store, metadata, id_gen, external, body);
            append_rebuilt(
                store,
                NodeSnapshot::Function(arity, params, body, attr, loc),
            )
        }
        NodeSnapshot::Let(kind, id, value, body) => {
            let body = simplify(store, metadata, id_gen, external, body);
            let value = simplify(store, metadata, id_gen, external, value);
            append_rebuilt(store, NodeSnapshot::Let(kind, id, value, body))
        }
        NodeSnapshot::LetRec(bindings, body) => {
            let bindings = bindings
                .into_iter()
                .map(|(id, value)| (id, simplify(store, metadata, id_gen, external, value)))
                .collect();
            let body = simplify(store, metadata, id_gen, external, body);
            append_rebuilt(store, NodeSnapshot::LetRec(bindings, body))
        }
        NodeSnapshot::Prim(primitive, args, loc) => {
            let args = simplify_many(store, metadata, id_gen, external, args);
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
            let fail_action =
                fail_action.map(|node| simplify(store, metadata, id_gen, external, node));
            let blocks = blocks
                .into_iter()
                .map(|(key, node)| (key, simplify(store, metadata, id_gen, external, node)))
                .collect();
            let consts = consts
                .into_iter()
                .map(|(key, node)| (key, simplify(store, metadata, id_gen, external, node)))
                .collect();
            let scrutinee = simplify(store, metadata, id_gen, external, scrutinee);
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
            let default = default.map(|node| simplify(store, metadata, id_gen, external, node));
            let cases = cases
                .into_iter()
                .map(|(key, node)| (key, simplify(store, metadata, id_gen, external, node)))
                .collect();
            let scrutinee = simplify(store, metadata, id_gen, external, scrutinee);
            append_rebuilt(store, NodeSnapshot::StringSwitch(scrutinee, cases, default))
        }
        NodeSnapshot::StaticRaise(exit, args) => {
            let args = simplify_many(store, metadata, id_gen, external, args);
            append_rebuilt(store, NodeSnapshot::StaticRaise(exit, args))
        }
        NodeSnapshot::StaticCatch(body, exit, params, handler) => {
            let handler = simplify(store, metadata, id_gen, external, handler);
            let body = simplify(store, metadata, id_gen, external, body);
            append_rebuilt(
                store,
                NodeSnapshot::StaticCatch(body, exit, params, handler),
            )
        }
        NodeSnapshot::TryWith(body, id, handler) => {
            let handler = simplify(store, metadata, id_gen, external, handler);
            let body = simplify(store, metadata, id_gen, external, body);
            append_rebuilt(store, NodeSnapshot::TryWith(body, id, handler))
        }
        NodeSnapshot::IfThenElse(condition, then_node, else_node) => {
            let else_node = simplify(store, metadata, id_gen, external, else_node);
            let then_node = simplify(store, metadata, id_gen, external, then_node);
            let condition = simplify(store, metadata, id_gen, external, condition);
            append_rebuilt(
                store,
                NodeSnapshot::IfThenElse(condition, then_node, else_node),
            )
        }
        NodeSnapshot::Sequence(first, second) => {
            let second = simplify(store, metadata, id_gen, external, second);
            let first = simplify(store, metadata, id_gen, external, first);
            append_rebuilt(store, NodeSnapshot::Sequence(first, second))
        }
        NodeSnapshot::While(condition, body) => {
            let body = simplify(store, metadata, id_gen, external, body);
            let condition = simplify(store, metadata, id_gen, external, condition);
            append_rebuilt(store, NodeSnapshot::While(condition, body))
        }
        NodeSnapshot::For(id, from, to, direction, body) => {
            let body = simplify(store, metadata, id_gen, external, body);
            let to = simplify(store, metadata, id_gen, external, to);
            let from = simplify(store, metadata, id_gen, external, from);
            append_rebuilt(store, NodeSnapshot::For(id, from, to, direction, body))
        }
        NodeSnapshot::ForOf(id, iterable, body) => {
            let body = simplify(store, metadata, id_gen, external, body);
            let iterable = simplify(store, metadata, id_gen, external, iterable);
            append_rebuilt(store, NodeSnapshot::ForOf(id, iterable, body))
        }
        NodeSnapshot::ForAwaitOf(id, iterable, body) => {
            let body = simplify(store, metadata, id_gen, external, body);
            let iterable = simplify(store, metadata, id_gen, external, iterable);
            append_rebuilt(store, NodeSnapshot::ForAwaitOf(id, iterable, body))
        }
        NodeSnapshot::Assign(id, value) => {
            let value = simplify(store, metadata, id_gen, external, value);
            append_rebuilt(store, NodeSnapshot::Assign(id, value))
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
            let (store, metadata) = self.parts_mut();
            simplify(store, metadata, id_gen, external, root)
        };
        self.replace_root(root);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ident::Ident;
    use crate::ident::IdentFlags;
    use crate::lambda::lam_compile_context::ExternalArityInfo;
    use crate::lambda::{Apply, Constant, Lambda};
    use crate::location::Location;

    fn id(name: &str, stamp: i32) -> Ident {
        Ident::new(name, stamp, IdentFlags::NONE)
    }
    fn info(status: ApplyStatus) -> ApInfo {
        ApInfo {
            loc: Location::none(),
            status,
        }
    }
    fn apply(function: Lambda, args: Vec<Lambda>, status: ApplyStatus) -> Lambda {
        Lambda::Lapply(Box::new(Apply {
            ap_func: Box::new(function),
            ap_args: args,
            ap_info: info(status),
        }))
    }
    fn run(input: Lambda, start: i32) -> (Lambda, i32) {
        let generator = IdGenerator::with_start_stamp(start);
        let mut context = IndexedLambdaContext::from_lambda(input, []);
        context.collect_info();
        let mut external = |_: &Ident, _: &str| None;
        context.alpha_conversion_with_external_arity(&generator, &mut external);
        (context.materialize(), generator.current_stamp())
    }

    #[test]
    fn external_arity_queries_follow_edge_order_and_preserve_location() {
        let module = id("External", 0);
        let location = Location::new_for_error("alpha.res", 10, 20);
        let access = |name: &str| {
            Lambda::prim(
                Primitive::Pfield(0, FieldDbgInfo::Module { name: name.into() }),
                vec![Lambda::LglobalModule(module)],
                location,
            )
        };
        let call = |function, argument| {
            Lambda::Lapply(Box::new(Apply {
                ap_func: Box::new(function),
                ap_args: vec![Lambda::const_(Constant::int(argument))],
                ap_info: ApInfo {
                    loc: location,
                    status: ApplyStatus::Na,
                },
            }))
        };
        let input = Lambda::seq(call(access("first"), 1), call(access("second"), 2));
        let generator = IdGenerator::with_start_stamp(10);
        let mut context = IndexedLambdaContext::from_lambda(input, []);
        context.collect_info();
        let mut calls = Vec::new();
        let mut external = |module: &Ident, field: &str| {
            calls.push((module.name().to_string(), field.to_string()));
            Some(ExternalArityInfo::Single(
                crate::lambda::lam_arity::Arity::info(vec![1], false),
            ))
        };
        context.alpha_conversion_with_external_arity(&generator, &mut external);
        assert_eq!(
            calls,
            vec![
                ("External".into(), "second".into()),
                ("External".into(), "first".into())
            ]
        );
        let Lambda::Lsequence(first, second) = context.materialize() else {
            panic!("expected sequence")
        };
        for node in [*first, *second] {
            let Lambda::Lapply(call) = node else {
                panic!("expected call")
            };
            assert_eq!(call.ap_info.status, ApplyStatus::InferFull);
            assert_eq!(call.ap_info.loc, location);
        }
        assert_eq!(generator.current_stamp(), 10);
    }

    fn function_definition(arity: i32, stamp: i32) -> Lambda {
        Lambda::function_(
            arity,
            (0..arity)
                .map(|index| id(&format!("p{index}"), stamp + index))
                .collect(),
            Lambda::const_(Constant::int(0)),
            FunctionAttribute::default(),
            crate::location::Location::none(),
        )
    }

    fn under_call(function: &Ident) -> Lambda {
        apply(
            Lambda::var(*function),
            vec![Lambda::const_(Constant::int(1))],
            ApplyStatus::Na,
        )
    }

    fn eta_stamp(lambda: &Lambda) -> i32 {
        let Lambda::Lfunction(function) = lambda else {
            panic!("expected eta function")
        };
        assert_eq!(function.params.len(), 1);
        function.params[0].stamp()
    }

    #[test]
    fn equal_apply_maps_arguments_left_to_right_before_function() {
        let outer = id("outer", 1);
        let inner = id("inner", 2);
        let function_expression = Lambda::let_(
            LetKind::Strict,
            id("side", 3),
            under_call(&inner),
            Lambda::var(outer),
        );
        let input = Lambda::let_(
            LetKind::Strict,
            outer,
            function_definition(1, 10),
            Lambda::let_(
                LetKind::Strict,
                inner,
                function_definition(2, 20),
                apply(
                    function_expression,
                    vec![under_call(&inner)],
                    ApplyStatus::Na,
                ),
            ),
        );
        let (actual, frontier) = run(input, 50);
        assert_eq!(frontier, 52);
        let Lambda::Llet(_, _, _, body) = actual else {
            panic!("expected outer let")
        };
        let Lambda::Llet(_, _, _, body) = *body else {
            panic!("expected inner let")
        };
        let Lambda::Lapply(call) = *body else {
            panic!("expected equal apply")
        };
        assert_eq!(eta_stamp(&call.ap_args[0]), 51);
        let Lambda::Llet(_, _, value, _) = *call.ap_func else {
            panic!("expected function let")
        };
        assert_eq!(eta_stamp(&value), 52);
    }

    #[test]
    fn equal_apply_argument_list_map_is_left_to_right() {
        let outer = id("outer", 1);
        let inner = id("inner", 2);
        let input = Lambda::let_(
            LetKind::Strict,
            outer,
            function_definition(2, 10),
            Lambda::let_(
                LetKind::Strict,
                inner,
                function_definition(2, 20),
                apply(
                    Lambda::var(outer),
                    vec![under_call(&inner), under_call(&inner)],
                    ApplyStatus::Na,
                ),
            ),
        );
        let (actual, frontier) = run(input, 50);
        assert_eq!(frontier, 52);
        let Lambda::Llet(_, _, _, body) = actual else {
            panic!("expected outer let")
        };
        let Lambda::Llet(_, _, _, body) = *body else {
            panic!("expected inner let")
        };
        let Lambda::Lapply(call) = *body else {
            panic!("expected equal apply")
        };
        assert_eq!(eta_stamp(&call.ap_args[0]), 51);
        assert_eq!(eta_stamp(&call.ap_args[1]), 52);
    }

    #[test]
    fn under_apply_simplifies_function_then_argument_before_eta() {
        let outer = id("outer", 1);
        let inner = id("inner", 2);
        let function_expression = Lambda::let_(
            LetKind::Strict,
            id("side", 3),
            under_call(&inner),
            Lambda::var(outer),
        );
        let input = Lambda::let_(
            LetKind::Strict,
            outer,
            function_definition(3, 10),
            Lambda::let_(
                LetKind::Strict,
                inner,
                function_definition(2, 20),
                apply(
                    function_expression,
                    vec![under_call(&inner)],
                    ApplyStatus::Na,
                ),
            ),
        );
        let (actual, frontier) = run(input, 50);
        assert_eq!(frontier, 55);
        let Lambda::Llet(_, _, _, body) = actual else {
            panic!("expected outer let")
        };
        let Lambda::Llet(_, _, _, body) = *body else {
            panic!("expected inner let")
        };
        let Lambda::Llet(LetKind::Strict, partial, partial_value, eta) = *body else {
            panic!("expected partial function")
        };
        assert_eq!(
            (partial.name(), partial.stamp(), partial.flags()),
            ("partial_arg", 55, IdentFlags::NONE)
        );
        let Lambda::Llet(_, _, nested_function, _) = *partial_value else {
            panic!("expected simplified function expression")
        };
        assert_eq!(eta_stamp(&nested_function), 51);
        let Lambda::Lfunction(eta) = *eta else {
            panic!("expected outer eta")
        };
        assert_eq!(eta.params.len(), 2);
        assert_eq!(eta.params[0].stamp(), 53);
        assert_eq!(eta.params[1].stamp(), 54);
        let Lambda::Lapply(call) = *eta.body else {
            panic!("expected eta call")
        };
        assert_eq!(eta_stamp(&call.ap_args[0]), 52);
    }

    #[test]
    fn letrec_explicit_binding_map_precedes_body() {
        let inner = id("inner", 1);
        let recursive = id("recursive", 2);
        let input = Lambda::let_(
            LetKind::Strict,
            inner,
            function_definition(2, 10),
            Lambda::letrec(vec![(recursive, under_call(&inner))], under_call(&inner)),
        );
        let (actual, frontier) = run(input, 50);
        assert_eq!(frontier, 52);
        let Lambda::Llet(_, _, _, body) = actual else {
            panic!("expected let")
        };
        let Lambda::Lletrec(bindings, body) = *body else {
            panic!("expected letrec")
        };
        assert_eq!(eta_stamp(&bindings[0].1), 51);
        assert_eq!(eta_stamp(&body), 52);
    }

    #[test]
    fn switch_children_follow_native_record_and_call_order() {
        let module = id("External", 0);
        let call = |name: &str| {
            apply(
                Lambda::prim(
                    Primitive::Pfield(0, FieldDbgInfo::Module { name: name.into() }),
                    vec![Lambda::LglobalModule(module)],
                    Location::none(),
                ),
                vec![Lambda::const_(Constant::int(0))],
                ApplyStatus::Na,
            )
        };
        let input = Lambda::Lswitch(
            Box::new(call("scrutinee")),
            Box::new(crate::lambda::LambdaSwitch {
                sw_consts_full: false,
                sw_consts: vec![(crate::lambda::SwitchKey::Int(0), call("constant"))],
                sw_blocks_full: false,
                sw_blocks: vec![(crate::lambda::SwitchKey::Int(0), call("block"))],
                sw_failaction: Some(Box::new(call("failure"))),
                sw_dispatch: crate::lambda::SwitchDispatch::Direct,
            }),
        );
        let generator = IdGenerator::new();
        let mut context = IndexedLambdaContext::from_lambda(input, []);
        let mut calls = Vec::new();
        let mut external = |_: &Ident, field: &str| {
            calls.push(field.to_string());
            Some(ExternalArityInfo::Single(
                crate::lambda::lam_arity::Arity::info(vec![1], false),
            ))
        };
        context.alpha_conversion_with_external_arity(&generator, &mut external);
        assert_eq!(calls, vec!["failure", "block", "constant", "scrutinee"]);
    }

    #[test]
    fn over_application_freshens_rest_before_first_group() {
        let outer = id("outer", 1);
        let inner = id("inner", 2);
        let input = Lambda::let_(
            LetKind::Strict,
            outer,
            Lambda::function_(
                1,
                vec![id("x", 3)],
                Lambda::const_(Constant::int(0)),
                FunctionAttribute::default(),
                crate::location::Location::none(),
            ),
            Lambda::let_(
                LetKind::Strict,
                inner,
                Lambda::function_(
                    2,
                    vec![id("a", 4), id("b", 5)],
                    Lambda::const_(Constant::int(0)),
                    FunctionAttribute::default(),
                    crate::location::Location::none(),
                ),
                apply(
                    Lambda::var(outer),
                    vec![
                        apply(
                            Lambda::var(inner),
                            vec![Lambda::const_(Constant::int(1))],
                            ApplyStatus::Na,
                        ),
                        apply(
                            Lambda::var(inner),
                            vec![Lambda::const_(Constant::int(2))],
                            ApplyStatus::Na,
                        ),
                    ],
                    ApplyStatus::Na,
                ),
            ),
        );
        let (actual, frontier) = run(input, 50);
        assert_eq!(frontier, 52);
        let Lambda::Llet(_, _, _, body) = actual else {
            panic!("expected outer let")
        };
        let Lambda::Llet(_, _, _, body) = *body else {
            panic!("expected inner let")
        };
        let Lambda::Lapply(outer_call) = *body else {
            panic!("expected outer apply")
        };
        let Lambda::Lapply(first_group) = *outer_call.ap_func else {
            panic!("expected first group")
        };
        let Lambda::Lfunction(first_eta) = &first_group.ap_args[0] else {
            panic!("expected first eta")
        };
        let Lambda::Lfunction(rest_eta) = &outer_call.ap_args[0] else {
            panic!("expected rest eta")
        };
        assert_eq!(
            (
                first_eta.params[0].name(),
                first_eta.params[0].stamp(),
                first_eta.params[0].flags()
            ),
            ("param", 52, IdentFlags::NONE)
        );
        assert_eq!(
            (
                rest_eta.params[0].name(),
                rest_eta.params[0].stamp(),
                rest_eta.params[0].flags()
            ),
            ("param", 51, IdentFlags::NONE)
        );
    }

    #[test]
    fn exact_and_over_application_preserve_status_jsx_and_location() {
        let function = id("function", 1);
        let p = id("p", 2);
        let q = id("q", 3);
        let definition = Lambda::function_(
            2,
            vec![p, q],
            Lambda::var(p),
            FunctionAttribute::default(),
            crate::location::Location::none(),
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
                function,
                definition.clone(),
                apply(Lambda::var(function), args, ApplyStatus::Na),
            );
            let (actual, frontier) = run(input, 20);
            let Lambda::Llet(_, _, _, body) = actual else {
                panic!("expected let")
            };
            if over {
                let Lambda::Lapply(outer) = *body else {
                    panic!("expected outer apply")
                };
                assert_eq!(outer.ap_info.status, ApplyStatus::Na);
                let Lambda::Lapply(inner) = *outer.ap_func else {
                    panic!("expected inner apply")
                };
                assert_eq!(inner.ap_info.status, ApplyStatus::InferFull);
            } else {
                let Lambda::Lapply(call) = *body else {
                    panic!("expected apply")
                };
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
                    ffi: Box::new(crate::lambda::lam_primitive::ExternalDecl::test_val("", 0)),
                },
                vec![],
                Location::none(),
            )
        };
        let function_expression = Lambda::let_(
            LetKind::Strict,
            id("side", 2),
            effect("callee"),
            Lambda::var(known),
        );
        let input = Lambda::let_(
            LetKind::Strict,
            known,
            Lambda::function_(
                4,
                vec![id("a", 3), id("b", 4), id("c", 5), id("d", 6)],
                Lambda::const_(Constant::int(0)),
                FunctionAttribute::default(),
                crate::location::Location::none(),
            ),
            apply(
                function_expression,
                vec![effect("argument1"), effect("argument2")],
                ApplyStatus::Na,
            ),
        );
        let (actual, frontier) = run(input, 100);
        assert_eq!(frontier, 105);
        let Lambda::Llet(_, _, _, body) = actual else {
            panic!("expected definition")
        };
        let Lambda::Llet(LetKind::Strict, outer, outer_value, inner) = *body else {
            panic!("expected outer argument binding")
        };
        assert_eq!(
            (outer.name(), outer.stamp(), outer.flags()),
            ("partial_arg", 103, IdentFlags::NONE)
        );
        assert!(
            matches!(&*outer_value, Lambda::Lprim(info) if matches!(&info.primitive, Primitive::PjsCall { prim_name, .. } if prim_name == "argument2"))
        );
        let Lambda::Llet(LetKind::Strict, middle_id, middle_value, inner) = *inner else {
            panic!("expected middle argument binding")
        };
        assert_eq!(
            (middle_id.name(), middle_id.stamp(), middle_id.flags()),
            ("partial_arg", 104, IdentFlags::NONE)
        );
        assert!(
            matches!(&*middle_value, Lambda::Lprim(info) if matches!(&info.primitive, Primitive::PjsCall { prim_name, .. } if prim_name == "argument1"))
        );
        let Lambda::Llet(LetKind::Strict, inner_id, inner_value, eta) = *inner else {
            panic!("expected inner function binding")
        };
        assert_eq!(
            (inner_id.name(), inner_id.stamp(), inner_id.flags()),
            ("partial_arg", 105, IdentFlags::NONE)
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
        assert_eq!(call.ap_info.status, ApplyStatus::InferFull);
    }

    #[test]
    fn shared_under_application_freshens_each_semantic_edge() {
        let function = id("function", 1);
        let input = Lambda::let_(
            LetKind::Strict,
            function,
            Lambda::function_(
                2,
                vec![id("a", 2), id("b", 3)],
                Lambda::const_(Constant::int(0)),
                FunctionAttribute::default(),
                crate::location::Location::none(),
            ),
            apply(
                Lambda::var(function),
                vec![Lambda::const_(Constant::int(1))],
                ApplyStatus::Na,
            ),
        );
        let generator = IdGenerator::with_start_stamp(50);
        let mut context = IndexedLambdaContext::from_lambda(input, []);
        context.collect_info();
        let original = context.current_root();
        let NodeView::Let(kind, id, value, call) = context.store().view(original) else {
            panic!("expected input let")
        };
        let (kind, id, value, call) = (kind, *id, value, call);
        let shared_body = context.store_mut().append_sequence(call, call);
        let root = context
            .store_mut()
            .append(NodeSnapshot::Let(kind, id, value, shared_body));
        context.replace_root(root);
        let mut external = |_: &Ident, _: &str| None;
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
            ("param", 52, IdentFlags::NONE)
        );
        assert_eq!(
            (
                second.params[0].name(),
                second.params[0].stamp(),
                second.params[0].flags()
            ),
            ("param", 51, IdentFlags::NONE)
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
            function,
            Lambda::function_(
                2,
                vec![id("a", 2), id("b", 3)],
                Lambda::const_(Constant::int(0)),
                attr.clone(),
                crate::location::Location::none(),
            ),
            apply(
                Lambda::var(function),
                vec![Lambda::const_(Constant::int(1))],
                ApplyStatus::Na,
            ),
        );
        let generator = IdGenerator::with_start_stamp(70);
        let mut context = IndexedLambdaContext::from_lambda(input, []);
        context.collect_info();
        let mut external = |_: &Ident, _: &str| None;
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
                    ffi: Box::new(crate::lambda::lam_primitive::ExternalDecl::test_val("", 0)),
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
            known,
            Lambda::function_(
                2,
                vec![id("x", 10), id("y", 11)],
                Lambda::const_(Constant::int(0)),
                FunctionAttribute::default(),
                crate::location::Location::none(),
            ),
            apply(
                Lambda::var(known),
                vec![effect("argument")],
                ApplyStatus::Na,
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
        assert_eq!(call.ap_info.status, ApplyStatus::InferFull);
    }
}
