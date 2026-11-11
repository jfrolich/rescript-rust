use super::*;
use crate::expect_dump;
use crate::js_ir::dump;
use crate::js_ir::test_util::test_fun;
use crate::lambda::lam_coercion::{ExtractedExports, resolve_export_aliases};

#[test]
fn coerce_toplevel_exports_reuses_existing_undefined_binding() {
    let mut compiler = LambdaCompiler::new();
    let alias = Ident::create_local("VS");
    let other = Ident::create_local("y");
    let mut block = vec![
        JS::variable(
            VarDecl {
                ident: alias,
                value: Some(JE::undefined(false, &mut compiler.j)),
                property: LetKind::Strict,
                ident_info: IdentInfo::default(),
            },
            &mut compiler.j,
        ),
        JS::variable(
            VarDecl {
                ident: other,
                value: Some(JE::number(Number::int(13), &mut compiler.j)),
                property: LetKind::Strict,
                ident_info: IdentInfo::default(),
            },
            &mut compiler.j,
        ),
    ];

    let exports = {
        let a0 = &mut block;
        let a1 = ExtractedExports {
            exports: vec![alias, other],
            values: vec![
                JE::undefined(false, &mut compiler.j),
                JE::var(other, &mut compiler.j),
            ],
        };
        compiler.coerce_toplevel_exports_lam(
            a0,
            a1,
            crate::lambda::lam_compile::OutputFinished::False,
        )
    };

    assert_eq!(exports, vec![alias, other]);
    expect_dump!(
        dump::block(&compiler.j, &block),
        "let[Strict] VS = undefined; let[Strict] y = 13"
    );
}

#[test]
fn coerce_toplevel_exports_keeps_undefined_rebound_after_later_effects() {
    let mut compiler = LambdaCompiler::new();
    let alias = Ident::create_local("MyURL");
    let callback = Ident::create_persistent("callback");
    let mut block = vec![
        JS::variable(
            VarDecl {
                ident: alias,
                value: Some(JE::undefined(false, &mut compiler.j)),
                property: LetKind::Strict,
                ident_info: IdentInfo::default(),
            },
            &mut compiler.j,
        ),
        JS::exp(
            JE::call(
                JE::var(callback, &mut compiler.j),
                &[],
                CallInfo::default(),
                &mut compiler.j,
            ),
            &mut compiler.j,
        ),
    ];

    let exports = {
        let a0 = &mut block;
        let a1 = ExtractedExports {
            exports: vec![alias],
            values: vec![JE::undefined(false, &mut compiler.j)],
        };
        compiler.coerce_toplevel_exports_lam(
            a0,
            a1,
            crate::lambda::lam_compile::OutputFinished::False,
        )
    };

    expect_dump!(
        dump::block(&compiler.j, &block),
        "let[Strict] MyURL = undefined; Exp(Call[Na](callback; )); let[Strict] MyURL#1 = undefined"
    );
    let [rebound] = exports.as_slice() else {
        panic!("expected one export, got {exports:?}");
    };
    assert!(!rebound.same(&alias));
    assert_eq!(rebound.name(), alias.name());
}

#[test]
fn coerce_toplevel_exports_skips_unreachable_undefined_placeholder_after_throw() {
    let mut compiler = LambdaCompiler::new();
    let exported = Ident::create_local("u");
    let mut block = vec![JS::throw(
        JE::string("boom", &mut compiler.j),
        &mut compiler.j,
    )];

    let exports = {
        let a0 = &mut block;
        let a1 = ExtractedExports {
            exports: vec![exported],
            values: vec![JE::undefined(false, &mut compiler.j)],
        };
        compiler.coerce_toplevel_exports_lam(
            a0,
            a1,
            crate::lambda::lam_compile::OutputFinished::True,
        )
    };

    assert_eq!(exports, vec![exported]);
    expect_dump!(dump::block(&compiler.j, &block), "Throw(\"boom\")");
}

#[test]
fn coerce_and_resolve_keep_declared_same_name_function_export_aliases_with_multiple_materialized_roots()
 {
    let mut compiler = LambdaCompiler::new();
    let source_level_broken = Ident::create_local("broken");
    let target = Ident::create_local("broken");
    let exported = Ident::create_local("broken");
    let do_something_async = Ident::create_local("doSomethingAsync");
    let param = Ident::create_local("param");
    let mut block = vec![
        JS::variable(
            VarDecl {
                ident: source_level_broken,
                value: Some(JE::var(do_something_async, &mut compiler.j)),
                property: LetKind::Alias,
                ident_info: IdentInfo::default(),
            },
            &mut compiler.j,
        ),
        JS::variable(
            VarDecl {
                ident: target,
                value: Some(test_fun(
                    false,
                    &[param],
                    &[JS::return_(
                        JE::undefined(false, &mut compiler.j),
                        &mut compiler.j,
                    )],
                    false,
                    true,
                    None,
                    &mut compiler.j,
                )),
                property: LetKind::Strict,
                ident_info: IdentInfo::default(),
            },
            &mut compiler.j,
        ),
        JS::variable(
            VarDecl {
                ident: exported,
                value: Some(JE::var(target, &mut compiler.j)),
                property: LetKind::Alias,
                ident_info: IdentInfo::default(),
            },
            &mut compiler.j,
        ),
    ];

    let exports = {
        let a0 = &mut block;
        let a1 = ExtractedExports {
            exports: vec![exported],
            values: vec![JE::var(target, &mut compiler.j)],
        };
        compiler.coerce_toplevel_exports_lam(
            a0,
            a1,
            crate::lambda::lam_compile::OutputFinished::False,
        )
    };
    let exports = resolve_export_aliases(&mut compiler.j, &block, exports);

    assert_eq!(exports, vec![exported]);
    expect_dump!(
        dump::block(&compiler.j, &block),
        "let[Alias] broken = doSomethingAsync; let[Strict] broken#1 = Fun[async](param){Return(undefined)}; let[Alias] broken#2 = broken#1"
    );
}

#[test]
fn coerce_toplevel_exports_reuses_existing_same_name_alias_binding_for_matching_var_value() {
    let mut compiler = LambdaCompiler::new();
    let target = Ident::create_persistent("tToJs");
    let declared_alias = Ident::create_local("v");
    let exported = Ident::create_local("v");
    let mut block = vec![JS::variable(
        VarDecl {
            ident: declared_alias,
            value: Some(JE::var(target, &mut compiler.j)),
            property: LetKind::Alias,
            ident_info: IdentInfo::default(),
        },
        &mut compiler.j,
    )];

    let exports = {
        let a0 = &mut block;
        let a1 = ExtractedExports {
            exports: vec![exported],
            values: vec![JE::var(target, &mut compiler.j)],
        };
        compiler.coerce_toplevel_exports_lam(
            a0,
            a1,
            crate::lambda::lam_compile::OutputFinished::False,
        )
    };
    let exports = resolve_export_aliases(&mut compiler.j, &block, exports);

    assert_eq!(exports, vec![declared_alias]);
    expect_dump!(dump::block(&compiler.j, &block), "let[Alias] v = tToJs");
}

#[test]
fn coerce_toplevel_exports_moves_same_name_recursive_function_alias_to_tail_without_remaining_use()
{
    let mut compiler = LambdaCompiler::new();
    let fib = Ident::create_local("fib");
    let exported = Ident::create_local("b");
    let n = Ident::create_local("n");
    let sink = Ident::create_persistent("sink");
    let mut block = vec![
        JS::variable(
            VarDecl {
                ident: fib,
                value: Some(test_fun(
                    false,
                    &[n],
                    &[JS::return_(
                        JE::call(
                            JE::var(fib, &mut compiler.j),
                            &[JE::var(n, &mut compiler.j)],
                            CallInfo::default(),
                            &mut compiler.j,
                        ),
                        &mut compiler.j,
                    )],
                    false,
                    false,
                    None,
                    &mut compiler.j,
                )),
                property: LetKind::Strict,
                ident_info: IdentInfo::default(),
            },
            &mut compiler.j,
        ),
        JS::variable(
            VarDecl {
                ident: exported,
                value: Some(JE::var(fib, &mut compiler.j)),
                property: LetKind::Alias,
                ident_info: IdentInfo::default(),
            },
            &mut compiler.j,
        ),
        JS::exp(
            JE::call(
                JE::var(sink, &mut compiler.j),
                &[],
                CallInfo::default(),
                &mut compiler.j,
            ),
            &mut compiler.j,
        ),
    ];

    let exports = {
        let a0 = &mut block;
        let a1 = ExtractedExports {
            exports: vec![exported],
            values: vec![JE::var(fib, &mut compiler.j)],
        };
        compiler.coerce_toplevel_exports_lam(
            a0,
            a1,
            crate::lambda::lam_compile::OutputFinished::False,
        )
    };
    let exports = resolve_export_aliases(&mut compiler.j, &block, exports);

    assert_eq!(exports.len(), 1);
    assert_eq!(exports[0].name(), exported.name());
    expect_dump!(
        dump::block(&compiler.j, &block),
        "let[Strict] fib = Fun(n){Return(Call[Na](fib; n))}; Exp(Call[Na](sink; )); let[Alias] b = fib"
    );
}

#[test]
fn resolve_export_aliases_prefers_underlying_declared_same_name_target_over_self_alias() {
    let mut j = JsArena::new();
    let target = Ident::create_local("tToJs");
    let exported = Ident::create_local("tToJs");
    let param = Ident::create_local("param");
    let block = vec![
        JS::variable(
            VarDecl {
                ident: target,
                value: Some(test_fun(
                    false,
                    &[param],
                    &[JS::return_(JE::undefined(false, &mut j), &mut j)],
                    false,
                    false,
                    None,
                    &mut j,
                )),
                property: LetKind::Strict,
                ident_info: IdentInfo::default(),
            },
            &mut j,
        ),
        JS::variable(
            VarDecl {
                ident: exported,
                value: Some(JE::var(target, &mut j)),
                property: LetKind::Alias,
                ident_info: IdentInfo::default(),
            },
            &mut j,
        ),
    ];

    assert_eq!(
        resolve_export_aliases(&mut j, &block, vec![exported]),
        vec![target]
    );
}

#[test]
fn coerce_toplevel_exports_moves_same_name_export_strict_module_field_binding_to_tail_when_reused()
{
    let mut compiler = LambdaCompiler::new();
    let set_gen = ModuleId {
        id: Ident::create_persistent("Set_gen"),
        kind: Kind::Ml,
        dynamic_import: false,
    };
    let declared_alias = Ident::create_local("empty");
    let exported = Ident::create_local("empty");
    let mut block = vec![
        JS::variable(
            VarDecl {
                ident: declared_alias,
                value: Some(JE::qualified(
                    set_gen.clone(),
                    Some("empty".to_string()),
                    &mut compiler.j,
                )),
                property: LetKind::Strict,
                ident_info: IdentInfo::default(),
            },
            &mut compiler.j,
        ),
        JS::exp(
            JE::call(
                JE::var(declared_alias, &mut compiler.j),
                &[],
                CallInfo::default(),
                &mut compiler.j,
            ),
            &mut compiler.j,
        ),
    ];

    let exports = {
        let a0 = &mut block;
        let a1 = ExtractedExports {
            exports: vec![exported],
            values: vec![JE::var(declared_alias, &mut compiler.j)],
        };
        compiler.coerce_toplevel_exports_lam(
            a0,
            a1,
            crate::lambda::lam_compile::OutputFinished::False,
        )
    };
    let exports = resolve_export_aliases(&mut compiler.j, &block, exports);

    assert_eq!(exports, vec![exported]);
    expect_dump!(
        dump::block(&compiler.j, &block),
        "Exp(Call[Na](Set_gen.empty<Ml>; )); let[Strict] empty = Set_gen.empty<Ml>"
    );
}

#[test]
fn coerce_toplevel_exports_keeps_same_name_literal_binding_used_by_later_function_body() {
    let mut compiler = LambdaCompiler::new();
    let exported = Ident::create_local("bla2");
    let concat = Ident::create_local("concat");
    let mut block = vec![
        JS::variable(
            VarDecl {
                ident: exported,
                value: Some(JE::string("", &mut compiler.j)),
                property: LetKind::Alias,
                ident_info: IdentInfo::default(),
            },
            &mut compiler.j,
        ),
        JS::variable(
            VarDecl {
                ident: concat,
                value: Some(test_fun(
                    false,
                    &[],
                    &[JS::return_(
                        JE::var(exported, &mut compiler.j),
                        &mut compiler.j,
                    )],
                    false,
                    false,
                    None,
                    &mut compiler.j,
                )),
                property: LetKind::Strict,
                ident_info: IdentInfo::default(),
            },
            &mut compiler.j,
        ),
    ];

    let exports = {
        let a0 = &mut block;
        let a1 = ExtractedExports {
            exports: vec![exported],
            values: vec![JE::var(exported, &mut compiler.j)],
        };
        compiler.coerce_toplevel_exports_lam(
            a0,
            a1,
            crate::lambda::lam_compile::OutputFinished::False,
        )
    };
    let exports = resolve_export_aliases(&mut compiler.j, &block, exports);

    assert_eq!(exports, vec![exported]);
    expect_dump!(
        dump::block(&compiler.j, &block),
        "let[Alias] bla2 = \"\"; let[Strict] concat = Fun(){Return(bla2)}"
    );
}

#[test]
fn coerce_toplevel_exports_keeps_same_name_qualified_alias_before_later_function_binding() {
    let mut compiler = LambdaCompiler::new();
    let stdlib_lazy = ModuleId {
        id: Ident::create_persistent("Stdlib_Lazy"),
        kind: Kind::Ml,
        dynamic_import: false,
    };
    let exported = Ident::create_local("is_lazy_force");
    let fib = Ident::create_local("fib");
    let n = Ident::create_local("n");
    let mut block = vec![
        JS::variable(
            VarDecl {
                ident: exported,
                value: Some(JE::qualified(
                    stdlib_lazy,
                    Some("get".to_string()),
                    &mut compiler.j,
                )),
                property: LetKind::Alias,
                ident_info: IdentInfo::default(),
            },
            &mut compiler.j,
        ),
        JS::variable(
            VarDecl {
                ident: fib,
                value: Some(test_fun(
                    false,
                    &[n],
                    &[JS::return_(JE::var(n, &mut compiler.j), &mut compiler.j)],
                    false,
                    false,
                    None,
                    &mut compiler.j,
                )),
                property: LetKind::Strict,
                ident_info: IdentInfo::default(),
            },
            &mut compiler.j,
        ),
    ];

    let exports = {
        let a0 = &mut block;
        let a1 = ExtractedExports {
            exports: vec![exported],
            values: vec![JE::var(exported, &mut compiler.j)],
        };
        compiler.coerce_toplevel_exports_lam(
            a0,
            a1,
            crate::lambda::lam_compile::OutputFinished::False,
        )
    };
    let exports = resolve_export_aliases(&mut compiler.j, &block, exports);

    assert_eq!(exports, vec![exported]);
    expect_dump!(
        dump::block(&compiler.j, &block),
        "let[Alias] is_lazy_force = Stdlib_Lazy.get<Ml>; let[Strict] fib = Fun(n){Return(n)}"
    );
}

#[test]
fn coerce_toplevel_exports_keeps_same_name_module_field_binding_before_later_effects() {
    let mut compiler = LambdaCompiler::new();
    let set_gen = ModuleId {
        id: Ident::create_persistent("Set_gen"),
        kind: Kind::Ml,
        dynamic_import: false,
    };
    let declared = Ident::create_local("empty");
    let exported = Ident::create_local("empty");
    let effect = Ident::create_local("effect");
    let mut block = vec![
        JS::variable(
            VarDecl {
                ident: declared,
                value: Some(JE::qualified(
                    set_gen,
                    Some("empty".to_string()),
                    &mut compiler.j,
                )),
                property: LetKind::Strict,
                ident_info: IdentInfo::default(),
            },
            &mut compiler.j,
        ),
        JS::exp(
            JE::call(
                JE::var(effect, &mut compiler.j),
                &[],
                CallInfo::default(),
                &mut compiler.j,
            ),
            &mut compiler.j,
        ),
    ];

    let exports = {
        let a0 = &mut block;
        let a1 = ExtractedExports {
            exports: vec![exported],
            values: vec![JE::var(declared, &mut compiler.j)],
        };
        compiler.coerce_toplevel_exports_lam(
            a0,
            a1,
            crate::lambda::lam_compile::OutputFinished::False,
        )
    };
    let exports = resolve_export_aliases(&mut compiler.j, &block, exports);

    assert_eq!(exports.len(), 1);
    assert_eq!(exports[0].name(), exported.name());
    expect_dump!(
        dump::block(&compiler.j, &block),
        "let[Strict] empty = Set_gen.empty<Ml>; Exp(Call[Na](effect; ))"
    );
}

#[test]
fn coerce_toplevel_exports_keeps_same_name_runtime_module_field_alias_before_unused_later_effect() {
    let mut compiler = LambdaCompiler::new();
    let belt_mutable_set_int = ModuleId {
        id: Ident::create_persistent("Belt_MutableSetInt"),
        kind: Kind::Runtime,
        dynamic_import: false,
    };
    let exported = Ident::create_local("fromArray");
    let effect = Ident::create_local("effect");
    let mut block = vec![
        JS::variable(
            VarDecl {
                ident: exported,
                value: Some(JE::qualified(
                    belt_mutable_set_int.clone(),
                    Some("fromArray".to_string()),
                    &mut compiler.j,
                )),
                property: LetKind::Alias,
                ident_info: IdentInfo::default(),
            },
            &mut compiler.j,
        ),
        JS::exp(
            JE::call(
                JE::var(effect, &mut compiler.j),
                &[],
                CallInfo::default(),
                &mut compiler.j,
            ),
            &mut compiler.j,
        ),
    ];

    let exports = {
        let a0 = &mut block;
        let a1 = ExtractedExports {
            exports: vec![exported],
            values: vec![JE::var(exported, &mut compiler.j)],
        };
        compiler.coerce_toplevel_exports_lam(
            a0,
            a1,
            crate::lambda::lam_compile::OutputFinished::False,
        )
    };
    let exports = resolve_export_aliases(&mut compiler.j, &block, exports);

    assert_eq!(exports, vec![exported]);
    expect_dump!(
        dump::block(&compiler.j, &block),
        "let[Alias] fromArray = Belt_MutableSetInt.fromArray<Runtime>; Exp(Call[Na](effect; ))"
    );
}

#[test]
fn coerce_toplevel_exports_keeps_distinct_import_alias_for_late_export_tail() {
    let mut compiler = LambdaCompiler::new();
    let file_js = ModuleId {
        id: Ident::create_persistent("FileJs"),
        kind: Kind::External {
            name: "./File.js".to_string(),
            default: false,
            import_attributes: None,
        },
        dynamic_import: false,
    };
    let foo = Ident::create_local("foo");
    let bar = Ident::create_local("bar");
    let exported = Ident::create_local("bar");
    let mut block = vec![
        JS::variable(
            VarDecl {
                ident: foo,
                value: Some(JE::qualified(
                    file_js,
                    Some("foo".to_string()),
                    &mut compiler.j,
                )),
                property: LetKind::Alias,
                ident_info: IdentInfo::default(),
            },
            &mut compiler.j,
        ),
        JS::variable(
            VarDecl {
                ident: bar,
                value: Some(JE::var(foo, &mut compiler.j)),
                property: LetKind::Alias,
                ident_info: IdentInfo::default(),
            },
            &mut compiler.j,
        ),
    ];

    let exports = {
        let a0 = &mut block;
        let a1 = ExtractedExports {
            exports: vec![exported],
            values: vec![JE::var(bar, &mut compiler.j)],
        };
        compiler.coerce_toplevel_exports_lam(
            a0,
            a1,
            crate::lambda::lam_compile::OutputFinished::False,
        )
    };
    let exports = resolve_export_aliases(&mut compiler.j, &block, exports);

    assert_eq!(exports, vec![exported]);
    expect_dump!(
        dump::block(&compiler.j, &block),
        "let[Alias] foo = FileJs.foo<External { name: \"./File.js\", default: false, import_attributes: None }>; let[Alias] bar = foo"
    );
}

#[test]
fn coerce_toplevel_exports_keeps_same_name_export_alias_binding_used_by_later_top_level_initializer()
 {
    let mut compiler = LambdaCompiler::new();
    let hash_utils = ModuleId {
        id: Ident::create_persistent("Hash_utils"),
        kind: Kind::Ml,
        dynamic_import: false,
    };
    let belt_id = ModuleId {
        id: Ident::create_persistent("Belt_Id"),
        kind: Kind::Ml,
        dynamic_import: false,
    };
    let int_hash = Ident::create_local("intHash");
    let int_eq = Ident::create_local("intEq");
    let y = Ident::create_local("Y");
    let mut block = vec![
        JS::variable(
            VarDecl {
                ident: int_hash,
                value: Some(JE::qualified(
                    hash_utils,
                    Some("hash".to_string()),
                    &mut compiler.j,
                )),
                property: LetKind::Alias,
                ident_info: IdentInfo::default(),
            },
            &mut compiler.j,
        ),
        JS::variable(
            VarDecl {
                ident: y,
                value: Some(JE::call(
                    JE::qualified(belt_id, Some("hashable".to_string()), &mut compiler.j),
                    &[
                        JE::var(int_hash, &mut compiler.j),
                        JE::var(int_eq, &mut compiler.j),
                    ],
                    CallInfo::default(),
                    &mut compiler.j,
                )),
                property: LetKind::Strict,
                ident_info: IdentInfo::default(),
            },
            &mut compiler.j,
        ),
    ];

    let exports = {
        let a0 = &mut block;
        let a1 = ExtractedExports {
            exports: vec![int_hash, y],
            values: vec![
                JE::var(int_hash, &mut compiler.j),
                JE::var(y, &mut compiler.j),
            ],
        };
        compiler.coerce_toplevel_exports_lam(
            a0,
            a1,
            crate::lambda::lam_compile::OutputFinished::False,
        )
    };
    let exports = resolve_export_aliases(&mut compiler.j, &block, exports);

    assert_eq!(exports, vec![int_hash, y]);
    expect_dump!(
        dump::block(&compiler.j, &block),
        "let[Alias] intHash = Hash_utils.hash<Ml>; let[Strict] Y = Call[Na](Belt_Id.hashable<Ml>; intHash, intEq)"
    );
}

#[test]
fn coerce_toplevel_exports_keeps_same_name_import_alias_binding_before_top_level_effect() {
    let mut compiler = LambdaCompiler::new();
    let imported = Ident::create_persistent("MyJsonJson");
    let sink = Ident::create_persistent("sink");
    let exported = Ident::create_local("myJson");
    let mut block = vec![
        JS::variable(
            VarDecl {
                ident: exported,
                value: Some(JE::var(imported, &mut compiler.j)),
                property: LetKind::Alias,
                ident_info: IdentInfo::default(),
            },
            &mut compiler.j,
        ),
        JS::exp(
            JE::call(
                JE::var(sink, &mut compiler.j),
                &[JE::var(exported, &mut compiler.j)],
                CallInfo::default(),
                &mut compiler.j,
            ),
            &mut compiler.j,
        ),
    ];

    let exports = {
        let a0 = &mut block;
        let a1 = ExtractedExports {
            exports: vec![exported],
            values: vec![JE::var(exported, &mut compiler.j)],
        };
        compiler.coerce_toplevel_exports_lam(
            a0,
            a1,
            crate::lambda::lam_compile::OutputFinished::False,
        )
    };
    let exports = resolve_export_aliases(&mut compiler.j, &block, exports);

    assert_eq!(exports, vec![exported]);
    expect_dump!(
        dump::block(&compiler.j, &block),
        "let[Alias] myJson = MyJsonJson; Exp(Call[Na](sink; myJson))"
    );
}

#[test]
fn coerce_toplevel_exports_keeps_same_name_local_value_alias_binding_for_non_function_target() {
    let mut compiler = LambdaCompiler::new();
    let process = Ident::create_local("process");
    let exported = Ident::create_local("proc");
    let global_this = Ident::create_persistent("globalThis");
    let mut block = vec![
        JS::variable(
            VarDecl {
                ident: process,
                value: Some(JE::new(
                    ExprKind::StaticIndex(
                        JE::var(global_this, &mut compiler.j),
                        JE::str_id("process", &mut compiler.j),
                        crate::js_ir::arena::FieldPos::new(None),
                    ),
                    &mut compiler.j,
                )),
                property: LetKind::Alias,
                ident_info: IdentInfo::default(),
            },
            &mut compiler.j,
        ),
        JS::variable(
            VarDecl {
                ident: exported,
                value: Some(JE::var(process, &mut compiler.j)),
                property: LetKind::Alias,
                ident_info: IdentInfo::default(),
            },
            &mut compiler.j,
        ),
    ];

    let exports = {
        let a0 = &mut block;
        let a1 = ExtractedExports {
            exports: vec![exported],
            values: vec![JE::var(exported, &mut compiler.j)],
        };
        compiler.coerce_toplevel_exports_lam(
            a0,
            a1,
            crate::lambda::lam_compile::OutputFinished::False,
        )
    };
    let exports = resolve_export_aliases(&mut compiler.j, &block, exports);

    assert_eq!(exports, vec![exported]);
    expect_dump!(
        dump::block(&compiler.j, &block),
        "let[Alias] process = globalThis.process; let[Alias] proc = process"
    );
}

#[test]
fn coerce_toplevel_exports_keeps_same_name_qualified_value_alias_binding_before_value_effect() {
    let mut compiler = LambdaCompiler::new();
    let module = ModuleId {
        id: Ident::create_persistent("MyJsonJson"),
        kind: Kind::External {
            name: "./myJson.json".to_string(),
            default: true,
            import_attributes: Some(JsImportAttributes {
                entries: vec![
                    ("type".to_string(), "json".to_string()),
                    ("some-identifier".to_string(), "yep".to_string()),
                ],
            }),
        },
        dynamic_import: false,
    };
    let exported = Ident::create_local("myJson");
    let sink = Ident::create_persistent("sink");
    let mut block = vec![
        JS::variable(
            VarDecl {
                ident: exported,
                value: Some(JE::qualified(
                    module.clone(),
                    Some("default".to_string()),
                    &mut compiler.j,
                )),
                property: LetKind::Alias,
                ident_info: IdentInfo::default(),
            },
            &mut compiler.j,
        ),
        JS::exp(
            JE::call(
                JE::var(sink, &mut compiler.j),
                &[JE::var(exported, &mut compiler.j)],
                CallInfo::default(),
                &mut compiler.j,
            ),
            &mut compiler.j,
        ),
    ];

    let exports = {
        let a0 = &mut block;
        let a1 = ExtractedExports {
            exports: vec![exported],
            values: vec![JE::qualified(
                module,
                Some("default".to_string()),
                &mut compiler.j,
            )],
        };
        compiler.coerce_toplevel_exports_lam(
            a0,
            a1,
            crate::lambda::lam_compile::OutputFinished::False,
        )
    };
    let exports = resolve_export_aliases(&mut compiler.j, &block, exports);

    assert_eq!(exports, vec![exported]);
    expect_dump!(
        dump::block(&compiler.j, &block),
        "let[Alias] myJson = MyJsonJson.default<External { name: \"./myJson.json\", default: true, import_attributes: Some(ImportAttributes { entries: [(\"type\", \"json\"), (\"some-identifier\", \"yep\")] }) }>; Exp(Call[Na](sink; myJson))"
    );
}
