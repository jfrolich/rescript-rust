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
    Lambda::Lapply(Apply {
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
    })
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
    assert_eq!(
        compiled.expr.source_loc,
        Some(Location::new_for_error("caller.res", 10, 20))
    );
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
        Lambda::Lapply(Apply {
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
        }),
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
