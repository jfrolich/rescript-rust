use super::*;
use crate::ident::IdentFlags;
use crate::js_ir::printer::{print_block, print_expression};
use crate::lambda::FieldDbgInfo;

// A closed test continuation for the families moved so far. There is no
// production catch-all or compatibility fallback. Every recursive edge in
// these fixtures (including imported beta results) goes through this function.
fn expression(owner: &mut IndexedJsConsumer<'_>, node: NodeId) -> Compiled {
    match owner.context.store().view(node) {
        NodeView::Const(value) => Compiled {
            prelude: vec![],
            expr: LambdaCompiler::compile_constant(value),
        },
        NodeView::Var(id) => Compiled {
            prelude: vec![],
            expr: Expression::var(id.clone()),
        },
        NodeView::GlobalModule(id, dynamic_import) => Compiled {
            prelude: vec![],
            expr: Expression::qualified(
                ModuleId {
                    id: id.clone(),
                    kind: Kind::Ml,
                    dynamic_import,
                },
                None,
            ),
        },
        NodeView::Apply(..) => owner.application(node, &mut expression),
        NodeView::Prim(..) => owner.primitive(node, &mut expression),
        NodeView::TryWith(..) => owner.try_with(node, &mut assign),
        NodeView::Function(..) => owner.function(node, &mut return_body),
        NodeView::While(..) => owner.while_loop(node, &mut expression, &mut effect),
        NodeView::For(..) => owner.for_loop(node, &mut expression, &mut effect),
        NodeView::ForOf(..) | NodeView::ForAwaitOf(..) => {
            owner.for_of(node, &mut expression, &mut effect)
        }
        NodeView::Break | NodeView::Continue => owner.loop_exit(node),
        NodeView::Assign(..) => owner.assign(node, &mut expression),
        _ => panic!("fixture uses a family outside this closed continuation"),
    }
}

fn assign(owner: &mut IndexedJsConsumer<'_>, id: &Ident, node: NodeId) -> Block {
    let compiled = expression(owner, node);
    let mut block = compiled.prelude;
    if !block_terminates(&block) {
        block.push(Statement::exp(Expression::bin(
            BinOp::Eq,
            Expression::var(id.clone()),
            compiled.expr,
        )));
    }
    block
}

fn external_application(args: Vec<Lambda>, status: ApplyStatus, jsx: bool) -> Lambda {
    Lambda::Lapply(Box::new(Apply {
        ap_func: Box::new(Lambda::prim(
            Primitive::Pfield(0, FieldDbgInfo::Module { name: "run".into() }),
            vec![Lambda::global_module(
                Ident::create_persistent("External"),
                false,
            )],
            Location::none(),
        )),
        ap_args: args,
        ap_info: ApInfo {
            loc: Location::new_for_error("caller.res", 10, 20),
            inlined: InlineAttribute::Default,
            status,
        },
        ap_transformed_jsx: jsx,
    }))
}

#[test]
fn cmj_reduced_original_argument_reenters_the_indexed_js_continuation() {
    let generator = Arc::new(IdGenerator::new());
    generator.set_current_stamp(700);
    let mut compiler = LambdaCompiler::with_shared_generator_and_options(
        Arc::clone(&generator),
        None,
        false,
        true,
        true,
    );
    compiler.set_source_map_enabled(true);
    let param = Ident::new("value", 40, IdentFlags::NONE);
    compiler.cmj_lambda_cache.insert(
        "External".into(),
        Some(Arc::new(AHashMap::from_iter([(
            "run".into(),
            Lambda::function_(
                1,
                vec![param.clone()],
                Lambda::var(param),
                FunctionAttribute::default(),
            ),
        )]))),
    );
    let mut context = IndexedLambdaContext::from_lambda(
        external_application(
            vec![Lambda::const_(Constant::int(7))],
            ApplyStatus::Na,
            true,
        ),
        [],
    );
    let root = context.current_root();
    let argument = match context.store().view(root) {
        NodeView::Apply(_, args, _, _) => args[0],
        _ => unreachable!(),
    };
    context.register_backend_roots([root]);
    let mut owner = IndexedJsConsumer::new(&mut compiler, &mut context);
    let mut visited = vec![];
    let compiled = owner.application(root, &mut |owner, child| {
        visited.push(child);
        expression(owner, child)
    });
    assert_eq!(visited, [argument]);
    assert_eq!(print_expression(&compiled.expr), "7");
    // Native successful beta returns compile_lambda(reduced) directly, without
    // attaching the eliminated caller's location (lam_compile.ml:349-357).
    assert_eq!(compiled.expr.source_loc, None);
    assert!(compiled.prelude.is_empty());
    assert!(owner.compiler.cmj_arity_cache.is_empty());
    assert_eq!(generator.current_stamp(), 700);
    assert_eq!(owner.context.backend_roots(), &[root]);
}

#[test]
fn cmj_reduced_try_reaches_actual_js_with_shared_beta_and_js_allocations() {
    let generator = Arc::new(IdGenerator::new());
    generator.set_current_stamp(800);
    let mut compiler = LambdaCompiler::with_shared_generator_and_options(
        Arc::clone(&generator),
        None,
        false,
        true,
        true,
    );
    let param = Ident::new("value", 40, IdentFlags::NONE);
    let exception = Ident::new("exn", 41, IdentFlags::from_bits_truncate(0x2b));
    compiler.cmj_lambda_cache.insert(
        "External".into(),
        Some(Arc::new(AHashMap::from_iter([(
            "run".into(),
            Lambda::function_(
                1,
                vec![param.clone()],
                Lambda::LtryWith(
                    Box::new(Lambda::var(param)),
                    exception.clone(),
                    Box::new(Lambda::unit()),
                ),
                FunctionAttribute::default(),
            ),
        )]))),
    );
    let mut context = IndexedLambdaContext::from_lambda(
        external_application(
            vec![Lambda::const_(Constant::int(42))],
            ApplyStatus::Na,
            false,
        ),
        [],
    );
    let root = context.current_root();
    context.register_backend_roots([root]);
    let mut owner = IndexedJsConsumer::new(&mut compiler, &mut context);
    let compiled = expression(&mut owner, root);
    let js = print_block(&compiled.prelude);
    assert!(js.contains("try"), "{js}");
    assert!(js.contains("42"), "{js}");
    let StatementDesc::Try(_, Some((actual_exception, _)), _) = &compiled.prelude[1].desc else {
        panic!("try statement")
    };
    assert_eq!(actual_exception.name(), exception.name());
    assert_eq!(actual_exception.stamp(), 801);
    assert_eq!(actual_exception.flags(), exception.flags());
    let ExpressionDesc::Var(VIdent::Id(result)) = &compiled.expr.desc else {
        panic!("result")
    };
    assert_eq!(result.stamp(), 802);
    assert_eq!(result.flags(), IdentFlags::NONE);
    assert_eq!(generator.current_stamp(), 802);
    assert!(owner.compiler.cmj_arity_cache.is_empty());
    match &owner.compiler.id_gen {
        LambdaIdGenerator::Shared(actual) => assert!(Arc::ptr_eq(actual, &generator)),
        LambdaIdGenerator::Owned(_) => panic!("generator replaced"),
    }
}

#[test]
fn rejected_cmj_does_not_import_and_lowers_arguments_after_arity_query_rtl() {
    let generator = Arc::new(IdGenerator::new());
    let mut compiler =
        LambdaCompiler::with_shared_generator_and_options(generator, None, false, true, true);
    let attr = FunctionAttribute {
        async_: true,
        ..FunctionAttribute::default()
    };
    compiler.cmj_lambda_cache.insert(
        "External".into(),
        Some(Arc::new(AHashMap::from_iter([(
            "run".into(),
            Lambda::function_(
                2,
                vec![Ident::create_persistent("a"), Ident::create_persistent("b")],
                Lambda::unit(),
                attr,
            ),
        )]))),
    );
    let mut context = IndexedLambdaContext::from_lambda(
        external_application(
            vec![
                Lambda::const_(Constant::int(1)),
                Lambda::const_(Constant::int(2)),
            ],
            ApplyStatus::Uncurry,
            true,
        ),
        [],
    );
    let root = context.current_root();
    let count = context.node_count();
    let args = match context.store().view(root) {
        NodeView::Apply(_, args, _, _) => args.to_vec(),
        _ => unreachable!(),
    };
    let mut owner = IndexedJsConsumer::new(&mut compiler, &mut context);
    let mut seen = vec![];
    let compiled = owner.application(root, &mut |owner, child| {
        assert!(owner.compiler.cmj_arity_cache.contains_key("External"));
        assert_eq!(owner.context.node_count(), count);
        seen.push(child);
        expression(owner, child)
    });
    assert_eq!(seen, [args[1], args[0]]);
    assert_eq!(print_expression(&compiled.expr), "External.run(1, 2)");
    let ExpressionDesc::Call(_, _, info) = &compiled.expr.desc else {
        panic!("call")
    };
    assert!(info.call_transformed_jsx);
    assert_eq!(info.arity, CallArity::Full);
    assert_eq!(info.kind, CallKind::Na);
}

#[test]
fn normal_calls_visit_arguments_then_function_rtl_but_emit_source_order() {
    let generator = Arc::new(IdGenerator::new());
    let mut compiler =
        LambdaCompiler::with_shared_generator_and_options(generator, None, false, true, false);
    let mut context = IndexedLambdaContext::from_lambda(
        Lambda::Lapply(Box::new(Apply {
            ap_func: Box::new(Lambda::var(Ident::new("f", 41, IdentFlags::NONE))),
            ap_args: vec![
                Lambda::const_(Constant::int(1)),
                Lambda::const_(Constant::int(2)),
            ],
            ap_info: ApInfo {
                loc: Location::none(),
                status: ApplyStatus::Uncurry,
                inlined: InlineAttribute::Default,
            },
            ap_transformed_jsx: false,
        })),
        [],
    );
    let root = context.current_root();
    let (function, args) = match context.store().view(root) {
        NodeView::Apply(f, args, _, _) => (f, args.to_vec()),
        _ => unreachable!(),
    };
    let mut owner = IndexedJsConsumer::new(&mut compiler, &mut context);
    let mut seen = vec![];
    let compiled = owner.application(root, &mut |owner, child| {
        seen.push(child);
        expression(owner, child)
    });
    assert_eq!(seen, [args[1], args[0], function]);
    assert_eq!(print_expression(&compiled.expr), "f(1, 2)");
}

fn effect(owner: &mut IndexedJsConsumer<'_>, node: NodeId) -> Block {
    let compiled = expression(owner, node);
    let mut block = compiled.prelude;
    if !block_terminates(&block) {
        crate::lambda::lam_coercion::push_s_exp(&mut block, compiled.expr);
    }
    block
}

fn return_body(owner: &mut IndexedJsConsumer<'_>, node: NodeId) -> Block {
    let compiled = expression(owner, node);
    let mut block = compiled.prelude;
    if !block_terminates(&block) {
        block.push(Statement::return_(compiled.expr));
    }
    block
}

#[test]
fn indexed_for_of_uses_full_flag_membership_and_allocates_before_iterable() {
    for await_ in [false, true] {
        for same_flags in [false, true] {
            let generator = Arc::new(IdGenerator::new());
            generator.set_current_stamp(600);
            let mut compiler = LambdaCompiler::with_shared_generator_and_options(
                Arc::clone(&generator),
                None,
                false,
                true,
                false,
            );
            let id = Ident::new("element", 50, IdentFlags::JS_OBJECT);
            let use_id = Ident::new(
                "element",
                50,
                if same_flags {
                    IdentFlags::JS_OBJECT
                } else {
                    IdentFlags::NONE
                },
            );
            let iterable = Box::new(Lambda::LtryWith(
                Box::new(Lambda::var(Ident::new("items", 51, IdentFlags::NONE))),
                Ident::new("exn", 52, IdentFlags::NONE),
                Box::new(Lambda::unit()),
            ));
            let lambda = if await_ {
                Lambda::Lfor_await_of(id.clone(), iterable, Box::new(Lambda::var(use_id)))
            } else {
                Lambda::Lfor_of(id.clone(), iterable, Box::new(Lambda::var(use_id)))
            };
            let mut context = IndexedLambdaContext::from_lambda(lambda, []);
            let root = context.current_root();
            let count = context.node_count();
            let mut owner = IndexedJsConsumer::new(&mut compiler, &mut context);
            let compiled = expression(&mut owner, root);
            let actual = match (&compiled.prelude.last().unwrap().desc, await_) {
                (StatementDesc::ForOf(None, id, _, _), false) => id,
                (StatementDesc::ForAwaitOf(None, id, _, _), true) => id,
                other => panic!("wrong loop: {other:?}"),
            };
            if same_flags {
                assert_eq!(actual.name(), id.name());
                assert_eq!(actual.stamp(), id.stamp());
                assert_eq!(actual.flags(), id.flags());
                assert_eq!(generator.current_stamp(), 601);
            } else {
                assert_eq!(
                    actual.name(),
                    if await_ { "_for_await_of" } else { "_for_of" }
                );
                assert_eq!(actual.stamp(), 601);
                assert_eq!(actual.flags(), IdentFlags::NONE);
                assert_eq!(generator.current_stamp(), 602);
            }
            assert!(matches!(
                compiled.expr.desc,
                ExpressionDesc::Undefined { is_unit: true }
            ));
            assert_eq!(owner.context.node_count(), count);
            assert!(owner.compiler.loop_stack.is_empty());
            let js = print_block(&compiled.prelude);
            assert!(
                js.contains(if await_ { "for await" } else { "for (" }),
                "{js}"
            );
        }
    }
}

#[test]
fn indexed_for_compiles_finish_then_start_and_removes_native_minus_one_shape() {
    let mut compiler = LambdaCompiler::new();
    let finish = Lambda::Lprim(Box::new(PrimInfo {
        primitive: Primitive::Poffsetint(-1),
        args: vec![Lambda::var(Ident::new("finish", 42, IdentFlags::NONE))],
        loc: Location::none(),
    }));
    let mut context = IndexedLambdaContext::from_lambda(
        Lambda::Lfor(
            Ident::new("i", 43, IdentFlags::NONE),
            Box::new(Lambda::var(Ident::new("start", 41, IdentFlags::NONE))),
            Box::new(finish),
            crate::lambda::DirectionFlag::Upto,
            Box::new(Lambda::Lbreak),
        ),
        [],
    );
    let root = context.current_root();
    let (start, finish) = match context.store().view(root) {
        NodeView::For(_, start, finish, _, _) => {
            let NodeView::Prim(_, [finish], _) = context.store().view(finish) else {
                unreachable!()
            };
            (start, *finish)
        }
        _ => unreachable!(),
    };
    let mut owner = IndexedJsConsumer::new(&mut compiler, &mut context);
    let mut seen = vec![];
    let compiled = owner.for_loop(
        root,
        &mut |owner, child| {
            seen.push(child);
            expression(owner, child)
        },
        &mut effect,
    );
    assert_eq!(seen, [finish, start]);
    let StatementDesc::ForRange(None, Some(_), _, _, ForDirection::Up, block) =
        &compiled.prelude[0].desc
    else {
        panic!("range")
    };
    assert!(matches!(block[0].desc, StatementDesc::Break(None)));
    let js = print_block(&compiled.prelude);
    assert!(js.contains("i < finish"), "{js}");
}

#[test]
fn indexed_while_exit_labels_are_lazy_and_shared_by_the_current_loop() {
    for is_break in [true, false] {
        let mut compiler = LambdaCompiler::new();
        let mut context = IndexedLambdaContext::from_lambda(
            Lambda::Lwhile(
                Box::new(Lambda::true_()),
                Box::new(if is_break {
                    Lambda::Lbreak
                } else {
                    Lambda::Lcontinue
                }),
            ),
            [],
        );
        let root = context.current_root();
        let mut owner = IndexedJsConsumer::new(&mut compiler, &mut context);
        let compiled = owner.while_loop(root, &mut expression, &mut |owner, child| {
            assert!(owner.compiler.loop_stack[0].label().is_none());
            owner.compiler.switch_depth += 1;
            let first = owner.loop_exit(child);
            let second = owner.loop_exit(child);
            owner.compiler.switch_depth -= 1;
            assert_eq!(print_block(&first.prelude), print_block(&second.prelude));
            first.prelude
        });
        let StatementDesc::While(Some(label), _, body) = &compiled.prelude[0].desc else {
            panic!("labelled while")
        };
        assert_eq!(label, "loop_0");
        match (&body[0].desc, is_break) {
            (StatementDesc::Break(Some(actual)), true)
            | (StatementDesc::Continue(Some(actual)), false) => assert_eq!(actual, label),
            other => panic!("exit: {other:?}"),
        }
        assert!(owner.compiler.loop_stack.is_empty());
        assert_eq!(owner.compiler.switch_depth, 0);
        assert_eq!(owner.compiler.loop_label_counter.get(), 1);
    }
}

#[test]
fn indexed_function_keeps_attributes_and_restores_outer_control_state() {
    let generator = Arc::new(IdGenerator::new());
    generator.set_current_stamp(900);
    let mut compiler = LambdaCompiler::with_shared_generator_and_options(
        Arc::clone(&generator),
        None,
        false,
        true,
        false,
    );
    compiler.switch_depth = 3;
    compiler.try_body_depth = 4;
    let outer_frame = compiler.push_loop();
    let id = Ident::new("arg", 41, IdentFlags::from_bits_truncate(0x2b));
    let mut context = IndexedLambdaContext::from_lambda(
        Lambda::function_(
            1,
            vec![id.clone()],
            Lambda::var(id.clone()),
            FunctionAttribute {
                async_: true,
                directive: Some("use server".into()),
                return_unit: true,
                ..FunctionAttribute::default()
            },
        ),
        [],
    );
    let root = context.current_root();
    let mut owner = IndexedJsConsumer::new(&mut compiler, &mut context);
    let compiled = owner.function(root, &mut |owner, body| {
        assert_eq!(owner.compiler.switch_depth, 0);
        assert_eq!(owner.compiler.try_body_depth, 0);
        assert!(owner.compiler.loop_stack.is_empty());
        assert_eq!(owner.compiler.return_unit_stack.last(), Some(&true));
        return_body(owner, body)
    });
    let ExpressionDesc::Fun {
        params,
        return_unit: true,
        async_: true,
        directive,
        ..
    } = &compiled.expr.desc
    else {
        panic!("function")
    };
    assert_eq!(directive.as_deref().map(String::as_str), Some("use server"));
    assert_eq!(params[0].name(), id.name());
    assert_eq!(params[0].stamp(), id.stamp());
    assert_eq!(params[0].flags(), id.flags());
    assert_eq!(owner.compiler.switch_depth, 3);
    assert_eq!(owner.compiler.try_body_depth, 4);
    assert!(owner.compiler.return_unit_stack.is_empty());
    owner.compiler.ensure_loop_label(&outer_frame);
    assert_eq!(
        owner.compiler.loop_stack[0].label().as_deref(),
        Some("loop_0")
    );
    assert_eq!(generator.current_stamp(), 900);
    let js = print_expression(&compiled.expr);
    assert!(js.contains("async"), "{js}");
    assert!(js.contains("use server"), "{js}");
}

#[test]
fn indexed_assign_offset_takes_reference_fast_path_without_child_lowering() {
    let mut compiler = LambdaCompiler::new();
    let id = Ident::new("counter", 41, IdentFlags::JS_OBJECT);
    let mut context = IndexedLambdaContext::from_lambda(
        Lambda::Lassign(
            id.clone(),
            Box::new(Lambda::prim(
                Primitive::Poffsetint(1),
                vec![Lambda::var(id)],
                Location::none(),
            )),
        ),
        [],
    );
    let root = context.current_root();
    let mut owner = IndexedJsConsumer::new(&mut compiler, &mut context);
    let compiled = owner.assign(root, &mut |_, _| panic!("offset fast path visited child"));
    assert!(matches!(
        compiled.expr.desc,
        ExpressionDesc::Undefined { is_unit: true }
    ));
    let js = print_block(&compiled.prelude);
    assert!(js.contains("counter = counter + 1 | 0"), "{js}");
}

#[test]
fn indexed_short_circuit_preserves_distinct_native_nonreturn_continuations() {
    use super::context::{Continuation, TailType};
    for and in [true, false] {
        for mode in 0..4 {
            let generator = Arc::new(IdGenerator::new());
            generator.set_current_stamp(1000);
            let mut compiler = LambdaCompiler::with_shared_generator_and_options(
                Arc::clone(&generator),
                None,
                false,
                true,
                false,
            );
            let branch = |name| {
                Lambda::LtryWith(
                    Box::new(Lambda::var(Ident::new(
                        name,
                        if name == "left" { 51 } else { 52 },
                        IdentFlags::NONE,
                    ))),
                    Ident::new("exn", 53, IdentFlags::NONE),
                    Box::new(Lambda::false_()),
                )
            };
            let mut context = IndexedLambdaContext::from_lambda(
                Lambda::Lprim(Box::new(PrimInfo {
                    primitive: if and {
                        Primitive::Psequand
                    } else {
                        Primitive::Psequor
                    },
                    args: vec![branch("left"), branch("right")],
                    loc: Location::none(),
                })),
                [],
            );
            let root = context.current_root();
            let target = Ident::new("result", 54, IdentFlags::JS_OBJECT);
            let continuation = match mode {
                0 => Continuation::NeedValue(TailType::NotTail),
                1 => Continuation::EffectCall(TailType::NotTail),
                2 => Continuation::Declare(LetKind::Alias, target.clone()),
                _ => Continuation::Assign(target.clone()),
            };
            let mut owner = IndexedJsConsumer::new(&mut compiler, &mut context);
            let output = owner.short_circuit_nonreturn(root, &continuation, &mut expression);
            assert_eq!(output.finished, super::output::Finished::False);
            assert_eq!(output.value.is_some(), mode < 2);
            assert_eq!(
                generator.current_stamp(),
                if mode < 2 { 1003 } else { 1002 }
            );
            if mode < 3 {
                let declaration_index = if mode < 2 && and { 0 } else { 2 };
                let StatementDesc::Variable(decl) = &output.block[declaration_index].desc else {
                    panic!("declaration")
                };
                assert_eq!(decl.property, LetKind::Variable);
                if mode < 2 {
                    assert_eq!(decl.ident.stamp(), 1003);
                } else {
                    assert_eq!(decl.ident.stamp(), target.stamp());
                    assert_eq!(decl.ident.flags(), target.flags());
                }
            }
            let js = print_block(&output.block);
            assert!(js.contains("if"), "{js}");
            if mode == 3 {
                assert!(js.contains("else"), "{js}");
            }
        }
    }
}

#[test]
fn indexed_short_circuit_return_rewrites_once_and_keeps_the_same_continuation() {
    use super::output::Output;
    for and in [true, false] {
        let mut compiler = LambdaCompiler::new();
        let mut context = IndexedLambdaContext::from_lambda(
            Lambda::Lprim(Box::new(PrimInfo {
                primitive: if and {
                    Primitive::Psequand
                } else {
                    Primitive::Psequor
                },
                args: vec![
                    Lambda::var(Ident::new("left", 41, IdentFlags::NONE)),
                    Lambda::var(Ident::new("right", 42, IdentFlags::NONE)),
                ],
                loc: Location::none(),
            })),
            [],
        );
        let root = context.current_root();
        let (left, right) = match context.store().view(root) {
            NodeView::Prim(_, [left, right], _) => (*left, *right),
            _ => unreachable!(),
        };
        let mut owner = IndexedJsConsumer::new(&mut compiler, &mut context);
        let mut visits = 0;
        let output = owner.short_circuit_return(root, &mut |owner, rewritten| {
            visits += 1;
            let NodeView::IfThenElse(condition, then_, else_) =
                owner.context.store().view(rewritten)
            else {
                panic!("native Lam.if_")
            };
            assert_eq!(condition, left);
            assert_eq!(if and { then_ } else { else_ }, right);
            let default = if and { else_ } else { then_ };
            assert!(
                matches!(
                    owner.context.store().view(default),
                    NodeView::Const(Constant::JsFalse)
                ) == and
            );
            // This fixture's return continuation deliberately has no tail-call
            // target. It emits JS from indexed children, never recursive Lambda.
            let cond = expression(owner, condition).expr;
            let then_ = expression(owner, then_).expr;
            let else_ = expression(owner, else_).expr;
            Output {
                block: vec![Statement::return_(Expression::cond(cond, then_, else_))],
                value: None,
                finished: super::output::Finished::True,
            }
        });
        assert_eq!(visits, 1);
        assert_eq!(output.finished, super::output::Finished::True);
        assert!(print_block(&output.block).contains("return"));
    }
}

#[test]
fn indexed_output_keeps_native_finished_and_dummy_append_protocol() {
    use super::output::{Finished, Output};
    use super::context::{Continuation, TailType};
    let first = Output {
        block: vec![Statement::break_()],
        value: Some(Expression::call(
            Expression::var(Ident::create_persistent("unreachable")),
            vec![],
            CallInfo::default(),
        )),
        finished: Finished::True,
    };
    let second = Output::of_block_and_expression(
        &Continuation::NeedValue(TailType::NotTail),
        vec![],
        Expression::string("tail"),
    );
    let joined = first.append(second);
    let (block, should_break) = joined.into_break_block();
    assert!(!should_break);
    assert_eq!(block.len(), 1);
    assert!(matches!(block[0].desc, StatementDesc::Break(None)));
    let mut forced = false;
    let effect = Output::of_expression(
        &Continuation::EffectCall(TailType::NotTail),
        Expression::bool(true),
        || {
            forced = true;
            true
        },
    );
    assert!(forced);
    assert_eq!(effect.finished, Finished::Dummy);
    let value = Output::of_expression(
        &Continuation::NeedValue(TailType::NotTail),
        Expression::bool(true),
        || panic!("forced lazy purity outside EffectCall"),
    );
    assert_eq!(value.append(effect).finished, Finished::False);
}
