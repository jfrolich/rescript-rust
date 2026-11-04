use super::*;
use crate::lambda::LamLoc;
use crate::lambda::{FunctionAttribute, InlineAttribute};

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
        loc: LamLoc::NONE,
        arity: 1,
        params: vec![parameter],
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
    assert_eq!(
        body, argument_root,
        "beta did not reuse the indexed call argument"
    );
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
fn indexed_external_apply_queries_then_beta_reduces_in_the_owner_store() {
    let generator = Arc::new(IdGenerator::new());
    generator.set_current_stamp(900);
    let mut compiler = LambdaCompiler::with_shared_generator_and_options(
        Arc::clone(&generator),
        None,
        false,
        true,
        true,
    );
    let module = Ident::new("External", 1, crate::ident::IdentFlags::GLOBAL);
    let argument = Lambda::const_(Constant::int(7));
    let application = Lambda::apply(
        Lambda::prim(
            Primitive::Pfield(
                0,
                crate::lambda::FieldDbgInfo::Module { name: "run".into() },
            ),
            vec![Lambda::global_module(module)],
            LamLoc::NONE,
        ),
        vec![argument],
        ApInfo {
            loc: LamLoc::for_test(13),
            inlined: InlineAttribute::Default,
            status: ApplyStatus::Na,
        },
        true,
    );
    let mut context = IndexedLambdaContext::from_lambda(application, []);
    let application_root = context.current_root();
    let argument_root = match context.store().snapshot(application_root) {
        NodeSnapshot::Apply(_, args, _, _) => args[0],
        _ => unreachable!(),
    };
    context.register_backend_roots([application_root]);

    let parameter = Ident::new("value", 2, crate::ident::IdentFlags::NONE);
    let external = Lambda::function_(
        1,
        vec![parameter],
        Lambda::var(parameter),
        FunctionAttribute::default(),
        LamLoc::NONE,
    );
    compiler.cmj_lambda_cache.insert(
        module.name().to_string(),
        Some(Arc::new(AHashMap::from_iter([(
            "run".to_string(),
            external,
        )]))),
    );

    let prepared = compiler
        .prepare_indexed_external_field_apply(&mut context, application_root)
        .expect("external application");
    let PreparedIndexedExternalApply::Reduced(reduced) = prepared else {
        panic!("eligible CMJ function was not beta-reduced")
    };
    assert_eq!(reduced, argument_root);
    assert!(
        compiler.cmj_arity_cache.is_empty(),
        "arity was queried after successful CMJ beta"
    );
    assert_eq!(generator.current_stamp(), 900);
}

#[test]
fn indexed_external_apply_rejection_defers_to_arity_after_lambda_query() {
    let generator = Arc::new(IdGenerator::new());
    let mut compiler =
        LambdaCompiler::with_shared_generator_and_options(generator, None, false, true, true);
    let module = Ident::new("External", 1, crate::ident::IdentFlags::GLOBAL);
    let application = Lambda::apply(
        Lambda::prim(
            Primitive::Pfield(
                0,
                crate::lambda::FieldDbgInfo::Module { name: "run".into() },
            ),
            vec![Lambda::global_module(module)],
            LamLoc::NONE,
        ),
        vec![Lambda::unit()],
        ApInfo {
            loc: LamLoc::NONE,
            inlined: InlineAttribute::Default,
            status: ApplyStatus::Na,
        },
        false,
    );
    let mut context = IndexedLambdaContext::from_lambda(application, []);
    let application_root = context.current_root();
    context.register_backend_roots([application_root]);
    let parameter = Ident::new("value", 2, crate::ident::IdentFlags::NONE);
    let mut attr = FunctionAttribute::default();
    attr.async_ = true;
    compiler.cmj_lambda_cache.insert(
        module.name().to_string(),
        Some(Arc::new(AHashMap::from_iter([(
            "run".to_string(),
            Lambda::function_(
                1,
                vec![parameter],
                Lambda::var(parameter),
                attr,
                LamLoc::NONE,
            ),
        )]))),
    );

    let prepared = compiler
        .prepare_indexed_external_field_apply(&mut context, application_root)
        .expect("external application");
    let PreparedIndexedExternalApply::Call {
        module: prepared_module,
        field_name,
        args,
        info,
        transformed_jsx,
        known_arity,
    } = prepared
    else {
        panic!("async CMJ function was incorrectly beta-reduced")
    };
    assert!(prepared_module.id.same(&module));
    assert_eq!(field_name, "run");
    assert_eq!(args.len(), 1);
    assert_eq!(info.status, ApplyStatus::Na);
    assert!(!transformed_jsx);
    assert!(known_arity.is_none());
    assert!(
        compiler.cmj_arity_cache.contains_key(module.name()),
        "fallback arity query did not run after lambda rejection"
    );
}

#[test]
fn legacy_compiler_keeps_its_generator_stack_owned() {
    let compiler = LambdaCompiler::new();
    assert!(matches!(compiler.id_gen, LambdaIdGenerator::Owned(_)));
}
