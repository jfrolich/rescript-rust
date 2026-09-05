use super::*;

#[test]
fn shared_generator_is_the_actual_js_temporary_allocator() {
    let generator = Arc::new(IdGenerator::new());
    generator.set_current_stamp(700);
    let mut compiler = LambdaCompiler::with_shared_generator_and_options(
        Arc::clone(&generator),
        None,
        false,
        true,
        false,
    );

    match &compiler.id_gen {
        LambdaIdGenerator::Shared(actual) => assert!(Arc::ptr_eq(actual, &generator)),
        LambdaIdGenerator::Owned(_) => panic!("indexed JS compiler replaced the shared generator"),
    }

    let exception = Ident::new("exn", 12, crate::ident::IdentFlags::JS_OBJECT);
    let lambda = Lambda::LtryWith(
        Box::new(Lambda::unit()),
        exception,
        Box::new(Lambda::unit()),
    );
    let _ = compiler.compile_expr(&lambda);

    assert_eq!(generator.current_stamp(), 701);
    let next = generator.create("after_js");
    assert_eq!(next.name(), "after_js");
    assert_eq!(next.stamp(), 702);
    assert_eq!(next.flags(), crate::ident::IdentFlags::NONE);
}

#[test]
fn indexed_cmj_beta_imports_into_owner_store_and_reuses_argument_ids() {
    let generator = Arc::new(IdGenerator::new());
    generator.set_current_stamp(700);
    let mut compiler = LambdaCompiler::with_shared_generator_and_options(
        Arc::clone(&generator),
        None,
        false,
        true,
        true,
    );

    let argument = Lambda::const_(Constant::int(42));
    let mut context = IndexedLambdaContext::from_lambda(argument, []);
    let argument_root = context.current_root();
    context.register_backend_roots([argument_root]);

    let parameter = Ident::new("cmjArg", 40, crate::ident::IdentFlags::NONE);
    let exception = Ident::new("cmjExn", 41, crate::ident::IdentFlags::JS_OBJECT);
    let function = LFunction {
        arity: 1,
        params: vec![parameter.clone()],
        body: Box::new(Lambda::LtryWith(
            Box::new(Lambda::var(parameter)),
            exception,
            Box::new(Lambda::unit()),
        )),
        attr: FunctionAttribute::default(),
    };

    let before_import = context.node_count();
    let reduced =
        compiler.import_and_beta_indexed_cmj_function(&mut context, function, &[argument_root]);
    assert!(context.node_count() > before_import);
    let NodeSnapshot::TryWith(body, _, _) = context.store().snapshot(reduced) else {
        panic!("expected beta-reduced CMJ try body")
    };
    assert_eq!(body, argument_root, "beta did not reuse the indexed call argument");
    assert_eq!(
        generator.current_stamp(),
        701,
        "consumer beta did not use the shared compilation generator"
    );

    // The compatibility materialization here is test-only. It checks that the
    // reduced root remains compilable while the common indexed consumer is
    // being wired to this owner-private mutation boundary.
    let reduced = context.store().materialize_node(reduced);
    let _ = compiler.compile_expr(&reduced);
    assert_eq!(generator.current_stamp(), 702);
    let next = generator.create("after_cmj_js");
    assert_eq!(next.stamp(), 703);
    assert_eq!(next.flags(), crate::ident::IdentFlags::NONE);
}

#[test]
fn legacy_compiler_keeps_its_generator_stack_owned() {
    let compiler = LambdaCompiler::new();
    assert!(matches!(compiler.id_gen, LambdaIdGenerator::Owned(_)));
}
