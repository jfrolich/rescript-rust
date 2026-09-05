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
fn legacy_compiler_keeps_its_generator_stack_owned() {
    let compiler = LambdaCompiler::new();
    assert!(matches!(compiler.id_gen, LambdaIdGenerator::Owned(_)));
}
