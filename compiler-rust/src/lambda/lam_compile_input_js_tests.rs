//! Direct JS helper tests. These do not claim full indexed-consumer coverage.
use super::*;
use crate::js_ir::printer::{print_block, print_expression};
use crate::lambda::lam_compile_input::{LambdaInput, LambdaInputView};
use crate::lambda::lam_primitive::Mutable;

#[test]
fn indexed_identity_module_emits_original_identifier_with_all_flags() {
    let flags = crate::ident::IdentFlags::from_bits_truncate(0x2b);
    let target = Ident::new("Input", 211, flags);
    let alias = Ident::new("value", 212, crate::ident::IdentFlags::NONE);
    let field = |target| {
        Lambda::prim(
            Primitive::Pfield(
                0,
                crate::lambda::FieldDbgInfo::Module {
                    name: "value".into(),
                },
            ),
            vec![target],
            Location::none(),
        )
    };
    for inline in [false, true] {
        for dynamic in [None, Some(false), Some(true)] {
            let base = match dynamic {
                None => Lambda::var(target.clone()),
                Some(dynamic) => Lambda::LglobalModule(target.clone(), dynamic),
            };
            // Exercise the consumer shape without the producer smart constructor
            // collapsing the inlined module wrapper first.
            let body = Lambda::Lprim(PrimInfo {
                primitive: Primitive::Pmakeblock(
                    crate::lambda::TagInfo::Module(vec!["value".into()]),
                    Mutable::Immutable,
                ),
                args: vec![if inline {
                    field(base.clone())
                } else {
                    Lambda::var(alias.clone())
                }],
                loc: Location::none(),
            });
            let body = if inline {
                body
            } else {
                Lambda::let_(LetKind::Alias, alias.clone(), field(base), body)
            };
            let context = IndexedLambdaContext::from_lambda(body, []);
            let count = context.node_count();
            let mut compiler = LambdaCompiler::new();
            let expr = compiler
                .try_compile_identity_module_return_input(LambdaInput::indexed(
                    context.store(),
                    context.current_root(),
                ))
                .expect("identity module");
            let actual = match &expr.desc {
                ExpressionDesc::Var(VIdent::Id(id)) if dynamic.is_none() => id,
                ExpressionDesc::Var(VIdent::Qualified(module, None)) => {
                    assert_eq!(Some(module.dynamic_import), dynamic);
                    &module.id
                }
                other => panic!("unexpected expression: {other:?}"),
            };
            assert_eq!(actual.name(), target.name());
            assert_eq!(actual.stamp(), target.stamp());
            assert_eq!(actual.flags(), flags);
            assert!(!print_expression(&expr).is_empty());
            assert_eq!(context.node_count(), count);
        }
    }
}

#[test]
fn indexed_eta_emits_runtime_js_and_honors_function_guards() {
    let left = Ident::new("left", 301, crate::ident::IdentFlags::JS_OBJECT);
    let right = Ident::new("right", 302, crate::ident::IdentFlags::NONE);
    for guard in 0..5 {
        let mut attr = crate::lambda::FunctionAttribute::default();
        attr.one_unit_arg = guard == 1;
        attr.async_ = guard == 2;
        attr.directive = (guard == 3).then(|| "use server".to_owned());
        let args = if guard == 4 {
            vec![Lambda::var(right.clone()), Lambda::var(left.clone())]
        } else {
            vec![Lambda::var(left.clone()), Lambda::var(right.clone())]
        };
        let context = IndexedLambdaContext::from_lambda(
            Lambda::function_(
                2,
                vec![left.clone(), right.clone()],
                Lambda::prim(Primitive::Pobjorder, args, Location::none()),
                attr,
            ),
            [],
        );
        let LambdaInputView::Function(function) =
            LambdaInput::indexed(context.store(), context.current_root()).view()
        else {
            panic!("function")
        };
        let expr = LambdaCompiler::new().compile_eta_wrapped_runtime_alias_input(function);
        if guard == 0 {
            assert_eq!(
                print_expression(&expr.expect("runtime alias")),
                "Primitive_object.compare"
            );
        } else {
            assert!(expr.is_none());
        }
    }
}

#[test]
fn primitive_js_boundary_preserves_prelude_and_shared_dynamic_import_allocator() {
    let generator = Arc::new(IdGenerator::new());
    generator.set_current_stamp(900);
    let mut compiler = LambdaCompiler::with_shared_generator_and_options(
        Arc::clone(&generator),
        None,
        false,
        true,
        false,
    );
    let module = ModuleId {
        id: Ident::new("External", 411, crate::ident::IdentFlags::JS_OBJECT),
        kind: Kind::External {
            name: "external-package".into(),
            default: false,
            import_attributes: None,
        },
        dynamic_import: true,
    };
    let before = Statement::exp(Expression::call(
        Expression::var(Ident::create_persistent("before")),
        vec![],
        CallInfo::default(),
    ));
    let prelude_text = print_block(&vec![before.clone()]);
    let compiled = compiler.compile_primitive_js(
        &Primitive::Pimport,
        vec![Expression::qualified(module, Some("value".into()))],
        vec![before],
        &Location::none(),
    );
    assert_eq!(print_block(&compiled.prelude), prelude_text);
    let js = print_expression(&compiled.expr);
    assert!(js.contains("import(\"external-package\")"), "{js}");
    assert!(js.contains(".then("), "{js}");
    assert_eq!(generator.current_stamp(), 901);
    match &compiler.id_gen {
        LambdaIdGenerator::Shared(actual) => assert!(Arc::ptr_eq(actual, &generator)),
        LambdaIdGenerator::Owned(_) => panic!("generator replaced"),
    }
}
