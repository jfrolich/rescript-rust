use super::*;
use crate::cmi::persistent_env::PersistentEnv;
use crate::js_ir::printer::print_deps_program_with_directives;
use crate::js_ir::{ModulePathResolver, print_block, print_deps_program, print_expression};
use crate::lambda::constant::{Constant, ConstructorRuntimeTag, ConstructorTag, PointerInfo};
use crate::lambda::primitive::{
    ExternalArgAttr, ExternalArgConst, ExternalArgDelim, ExternalArgLabel, ExternalArgSpec,
    ExternalFfiKind, ExternalFfiSpec, ExternalModuleBindName, ExternalModuleName,
    ExternalObjLabel, ExternalObjSpec, ExternalReturnWrapper, ExternalSpec, JsRawInfo,
    Primitive,
};
use crate::lambda::{
    ApInfo, Apply, ApplyStatus, FunctionAttribute, InlineAttribute, Lambda, SwitchBlock,
    SwitchNames, SwitchTag,
};
use crate::location::Location;
use std::fs;
use std::path::PathBuf;
use tempfile::tempdir;

fn write_ast_source_stub(ast_path: &std::path::Path, source_path: &std::path::Path) {
    let mut bytes = Vec::new();
    bytes.extend_from_slice(&0u32.to_be_bytes());
    bytes.extend_from_slice(source_path.to_string_lossy().as_bytes());
    bytes.push(b'\n');
    fs::write(ast_path, bytes).expect("failed to write ast source stub");
}

fn compile_checked_in_test_file_to_js(module_name: &str) -> String {
    let repo_root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("repo root")
        .to_path_buf();
    let source_path = repo_root
        .join("tests")
        .join("tests")
        .join("src")
        .join(format!("{module_name}.res"));
    let output_path = repo_root
        .join("tests")
        .join("tests")
        .join("src")
        .join(format!("{module_name}.mjs"));
    let options = crate::driver::CompilerOptions {
        include_paths: vec![
            repo_root
                .join("tests")
                .join("tests")
                .join("lib")
                .join("ocaml"),
        ],
        runtime_path: Some(
            repo_root
                .join("node_modules")
                .join("@rescript")
                .join("runtime"),
        ),
        source_filename: Some(source_path.to_string_lossy().into_owned()),
        output_path: Some(output_path),
        ..crate::driver::CompilerOptions::default()
    };

    crate::driver::compile_file_to_js_with_options(&source_path, &options)
        .unwrap_or_else(|err| panic!("failed to compile {module_name}.res: {err:#}"))
}

fn find_variable_initializer<'a>(block: &'a Block, ident: &Ident) -> Option<&'a Expression> {
    block.iter().find_map(|stmt| match &stmt.desc {
        StatementDesc::Variable(VariableDeclaration {
            ident: binding,
            value: Some(value),
            ..
        }) if binding.same(ident) => Some(value),
        _ => None,
    })
}

#[test]
fn gpr_1760_test_keeps_checked_division_and_mod_effects_like_ocaml() {
    let output = compile_checked_in_test_file_to_js("gpr_1760_test");
    assert!(
        output.contains("Primitive_int.div(0, 0);"),
        "expected the checked fixture to keep Primitive_int.div(0, 0), got:\n{output}"
    );
    assert!(
        output.contains("Primitive_int.mod_(0, 0);"),
        "expected the checked fixture to keep Primitive_int.mod_(0, 0), got:\n{output}"
    );
}

#[test]
fn div_by_zero_test_keeps_checked_throw_helpers_like_ocaml() {
    let output = compile_checked_in_test_file_to_js("div_by_zero_test");
    assert!(
        output.contains("Primitive_int.div(3, 0);"),
        "expected the checked fixture to call Primitive_int.div(3, 0), got:\n{output}"
    );
    assert!(
        output.contains("Primitive_int.mod_(3, 0);"),
        "expected the checked fixture to call Primitive_int.mod_(3, 0), got:\n{output}"
    );
}

fn external_module(bundle: &str) -> ExternalModuleName {
    ExternalModuleName {
        bundle: bundle.to_string(),
        module_bind_name: ExternalModuleBindName::Nothing,
        import_attributes: None,
    }
}

fn external_module_with_attrs(
    bundle: &str,
    hint: &str,
    attrs: &[(&str, &str)],
) -> ExternalModuleName {
    ExternalModuleName {
        bundle: bundle.to_string(),
        module_bind_name: ExternalModuleBindName::HintName(hint.to_string()),
        import_attributes: Some(
            attrs.iter()
                .map(|(key, value)| (key.to_string(), value.to_string()))
                .collect(),
        ),
    }
}

fn js_var_external(name: &str, external_module_name: Option<ExternalModuleName>) -> Lambda {
    Lambda::prim(
        Primitive::PjsCall {
            prim_name: name.to_string(),
            arg_types: vec![],
            ffi: ExternalFfiSpec {
                kind: ExternalFfiKind::Default,
                spec: Some(ExternalSpec::JsVar {
                    name: name.to_string(),
                    external_module_name,
                    scopes: vec![],
                }),
                obj_params: None,
                return_wrapper: ExternalReturnWrapper::Identity,
                inline_constant: None,
            },
            dynamic_import: false,
            transformed_jsx: false,
        },
        vec![],
        Location::none(),
    )
}

fn console_log_effect(arg: Lambda) -> Lambda {
    Lambda::seq(
        Lambda::prim(
            Primitive::PjsCall {
                prim_name: "console.log".to_string(),
                arg_types: vec![],
                ffi: ExternalFfiSpec {
                    kind: ExternalFfiKind::Default,
                    spec: None,
                    obj_params: None,
                    return_wrapper: ExternalReturnWrapper::Identity,
                    inline_constant: None,
                },
                dynamic_import: false,
                transformed_jsx: false,
            },
            vec![arg],
            Location::none(),
        ),
        Lambda::const_(Constant::JsUndefined { is_unit: true }),
    )
}

fn import_attributes_lowered_lambda() -> Lambda {
    let include_json = Ident::create_local("include");
    let my_json = Ident::create_local("myJson");
    let include_css = Ident::create_local("include");
    let button_css = Ident::create_local("buttonCss");

    let json_module = external_module_with_attrs(
        "./myJson.json",
        "MyJsonJson",
        &[("type", "json"), ("some-identifier", "yep")],
    );
    let css_module = external_module_with_attrs(
        "./myCss.css",
        "MyCssCss",
        &[("type", "css"), ("some-identifier", "yep")],
    );

    Lambda::let_(
        LetKind::Strict,
        include_json.clone(),
        Lambda::prim(
            Primitive::Pmakeblock(
                0,
                TagInfo::Module(vec!["myJson".to_string()]),
                Mutable::Immutable,
            ),
            vec![js_var_external("default", Some(json_module))],
            Location::none(),
        ),
        Lambda::let_(
            LetKind::Alias,
            my_json.clone(),
            Lambda::prim(
                Primitive::Pfield(
                    0,
                    FieldDbgInfo::Module {
                        name: "myJson".to_string(),
                    },
                ),
                vec![Lambda::var(include_json.clone())],
                Location::none(),
            ),
            Lambda::seq(
                console_log_effect(Lambda::var(my_json.clone())),
                Lambda::let_(
                    LetKind::Strict,
                    include_css.clone(),
                    Lambda::prim(
                        Primitive::Pmakeblock(
                            0,
                            TagInfo::Module(vec!["buttonCss".to_string()]),
                            Mutable::Immutable,
                        ),
                        vec![js_var_external("button", Some(css_module))],
                        Location::none(),
                    ),
                    Lambda::let_(
                        LetKind::Alias,
                        button_css.clone(),
                        Lambda::prim(
                            Primitive::Pfield(
                                0,
                                FieldDbgInfo::Module {
                                    name: "buttonCss".to_string(),
                                },
                            ),
                            vec![Lambda::var(include_css)],
                            Location::none(),
                        ),
                        Lambda::seq(
                            console_log_effect(Lambda::var(button_css.clone())),
                            Lambda::prim(
                                Primitive::Pmakeblock(
                                    0,
                                    TagInfo::ModuleExport(vec![
                                        my_json.clone(),
                                        button_css.clone(),
                                    ]),
                                    Mutable::Immutable,
                                ),
                                vec![
                                    Lambda::var(my_json.clone()),
                                    Lambda::var(button_css.clone()),
                                ],
                                Location::none(),
                            ),
                        ),
                    ),
                ),
            ),
        ),
    )
}

fn assert_import_attributes_alias_block_shape(block: &Block, stage: &str) {
    let rendered = print_block(block);
    assert!(
        rendered.contains("let myJson = MyJsonJson;\n\nconsole.log(myJson);"),
        "expected {stage} to keep the exported JSON alias before the log call, got:\n{rendered}"
    );
    assert!(
        rendered.contains("let buttonCss = MyCssCss.button;\n\nconsole.log(buttonCss);"),
        "expected {stage} to keep the exported CSS alias before the log call, got:\n{rendered}"
    );
    assert!(
        !rendered.contains("console.log(MyJsonJson);")
            && !rendered.contains("console.log(MyCssCss.button);"),
        "unexpected direct imported-value logging remained at {stage}:\n{rendered}"
    );
}

fn resolver_with_checked_in_cmj() -> ModulePathResolver {
    let mut persistent_env = PersistentEnv::new();
    persistent_env.add_load_path(
        PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .expect("repo root")
            .join("tests")
            .join("tests")
            .join("lib")
            .join("ocaml"),
    );
    persistent_env.add_load_path(
        PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .expect("repo root")
            .join("packages")
            .join("@rescript")
            .join("runtime")
            .join("lib")
            .join("ocaml"),
    );
    ModulePathResolver::from_compile_options(
        None,
        Some(std::path::Path::new("/tmp/Effect.mjs")),
        None,
        Some(persistent_env),
    )
}

#[test]
fn test_compile_constant_int() {
    let mut compiler = LambdaCompiler::new();
    let lam = Lambda::const_(Constant::int(7));
    let program = compiler.compile_program(&lam);
    assert!(!program.block.is_empty());
}

#[test]
fn lowers_upto_subint_one_finish_to_ocaml_exclusive_for_range() {
    let mut compiler = LambdaCompiler::new();
    let i = Ident::create_local("i");
    let xs = Ident::create_local("xs");
    let lam = Lambda::for_(
        i,
        Lambda::const_(Constant::int(0)),
        Lambda::prim(
            Primitive::Psubint,
            vec![Lambda::var(xs), Lambda::const_(Constant::int(1))],
            Location::none(),
        ),
        crate::lambda::DirectionFlag::Upto,
        Lambda::unit(),
    );

    let compiled = compiler.compile_expr(&lam);
    let rendered = print_block(&compiled.prelude);

    assert_eq!(rendered.trim(), "for (let i = 0; i < xs; ++i) {}");
}

#[test]
fn lowers_upto_predint_finish_to_ocaml_exclusive_for_range() {
    let mut compiler = LambdaCompiler::new();
    let i = Ident::create_local("i");
    let xs = Ident::create_local("xs");
    let lam = Lambda::for_(
        i,
        Lambda::const_(Constant::int(0)),
        Lambda::prim(
            Primitive::Poffsetint(-1),
            vec![Lambda::var(xs)],
            Location::none(),
        ),
        crate::lambda::DirectionFlag::Upto,
        Lambda::unit(),
    );

    let compiled = compiler.compile_expr(&lam);
    let rendered = print_block(&compiled.prelude);

    assert_eq!(rendered.trim(), "for (let i = 0; i < xs; ++i) {}");
}

#[test]
fn lowers_for_bounds_preludes_in_ocaml_order_when_start_expr_is_pure() {
    let mut compiler = LambdaCompiler::new();
    let i = Ident::create_local("i");
    let probe = Ident::create_local("probe");
    let probe_finish = Ident::create_local("probe_finish");
    let lam = Lambda::for_(
        i,
        Lambda::seq(
            Lambda::assign(probe, Lambda::const_(Constant::int(1))),
            Lambda::const_(Constant::int(0)),
        ),
        Lambda::seq(
            Lambda::assign(probe_finish, Lambda::const_(Constant::int(2))),
            Lambda::const_(Constant::int(1)),
        ),
        crate::lambda::DirectionFlag::Upto,
        Lambda::unit(),
    );

    let compiled = compiler.compile_expr(&lam);
    let rendered = print_block(&compiled.prelude);

    assert_eq!(
        rendered.trim(),
        "probe = 1;\n\nprobe_finish = 2;\n\nfor (let i = 0; i <= 1; ++i) {}"
    );
}

#[test]
fn lowers_effectful_for_start_out_of_initializer_when_finish_has_prelude() {
    let mut compiler = LambdaCompiler::new();
    let i = Ident::create_local("i");
    let probe_finish = Ident::create_local("probe_finish");
    let lam = Lambda::for_(
        i,
        Lambda::prim(
            Primitive::PrawJsCode(JsRawInfo {
                code: "start()".to_string(),
                is_stmt: false,
            }),
            vec![],
            Location::none(),
        ),
        Lambda::seq(
            Lambda::assign(probe_finish, Lambda::const_(Constant::int(2))),
            Lambda::const_(Constant::int(1)),
        ),
        crate::lambda::DirectionFlag::Upto,
        Lambda::unit(),
    );

    let compiled = compiler.compile_expr(&lam);
    let rendered = print_block(&compiled.prelude);

    assert_eq!(
        rendered.trim(),
        "let i = (start());\n\nprobe_finish = 2;\n\nfor (; i <= 1; ++i) {}"
    );
}

#[test]
fn compile_raw_js_trims_outer_whitespace_before_js_ir_printing() {
    let mut compiler = LambdaCompiler::new();
    let lam = Lambda::prim(
        Primitive::PrawJsCode(JsRawInfo {
            code: "\nif (import.meta.hot){\n  console.log('es6')\n}\n".to_string(),
            is_stmt: true,
        }),
        vec![],
        Location::none(),
    );

    let program = compiler.compile_program(&lam);
    let raw_code = program
        .block
        .iter()
        .find_map(|stmt| match &stmt.desc {
            StatementDesc::Exp(Expression {
                desc: ExpressionDesc::RawJsCode(info),
                ..
            }) => Some(info.code.as_str()),
            _ => None,
        })
        .expect("compiled raw js statement");

    assert_eq!(raw_code, "if (import.meta.hot){\n  console.log('es6')\n}");
}

#[test]
fn compile_constant_named_constructor_uses_string_runtime_name() {
    let compiled = LambdaCompiler::compile_constant(&Constant::Int {
        i: 0,
        comment: Some(PointerInfo::Constructor(ConstructorTag {
            name: "NoParam".to_string(),
            const_: 1,
            non_const: 2,
            runtime_tag: None,
        })),
    });

    assert!(matches!(
        compiled,
        Expression {
            desc: ExpressionDesc::Str { ref txt, .. },
            ..
        } if txt == "NoParam"
    ));
}

#[test]
fn compile_constant_constructor_runtime_tag_uses_runtime_literal() {
    let compiled = LambdaCompiler::compile_constant(&Constant::Int {
        i: 0,
        comment: Some(PointerInfo::Constructor(ConstructorTag {
            name: "Three".to_string(),
            const_: 1,
            non_const: 0,
            runtime_tag: Some(ConstructorRuntimeTag::String("three".to_string())),
        })),
    });

    assert!(matches!(
        compiled,
        Expression {
            desc: ExpressionDesc::Str { ref txt, .. },
            ..
        } if txt == "three"
    ));
}

#[test]
fn compile_constant_empty_list_keeps_numeric_zero_with_pointer_comment() {
    let compiled = LambdaCompiler::compile_constant(&Constant::Int {
        i: 0,
        comment: Some(PointerInfo::Constructor(ConstructorTag {
            name: "[]".to_string(),
            const_: 1,
            non_const: 1,
            runtime_tag: None,
        })),
    });

    assert!(matches!(
        compiled,
        Expression {
            desc: ExpressionDesc::Number(Number::Int { i: 0, .. }),
            comment: Some(ref comment),
        }
        if comment == "[]"
    ));
    assert_eq!(print_expression(&compiled), "/* [] */0");
}

#[test]
fn compile_constant_some_unit_boxes_undefined_none_encoding() {
    let compiled =
        LambdaCompiler::compile_constant(&Constant::Some(Box::new(Constant::JsUndefined {
            is_unit: true,
        })));

    assert!(matches!(
        compiled,
        Expression {
            desc: ExpressionDesc::OptionalBlock(ref inner, false),
            ..
        } if matches!(
            inner.as_ref(),
            Expression {
                desc: ExpressionDesc::Undefined { is_unit: false },
                ..
            }
        )
    ));
    assert_eq!(
        print_expression(&compiled),
        "Primitive_option.some(undefined)"
    );
}

#[test]
fn compile_constant_preserves_marshaled_starj_strings() {
    let compiled = LambdaCompiler::compile_constant(&Constant::String {
        s: "\\\"".to_string(),
        delim: Some(StringDelim::StarJ),
    });

    assert!(matches!(
        compiled,
        Expression {
            desc: ExpressionDesc::Str {
                delim: Delim::StarJ,
                ref txt,
            },
            ..
        } if txt == "\\\""
    ));
    assert_eq!(print_expression(&compiled), "\"\\\"\"");
}

#[test]
fn compile_constant_quotes_noquote_delim_strings_like_ocaml() {
    let compiled = LambdaCompiler::compile_constant(&Constant::String {
        s: "{foo:true}".to_string(),
        delim: Some(StringDelim::NoQuotes),
    });

    assert!(matches!(
        compiled,
        Expression {
            desc: ExpressionDesc::Str {
                delim: Delim::None,
                ref txt,
            },
            ..
        } if txt == "{foo:true}"
    ));
    assert_eq!(print_expression(&compiled), "\"{foo:true}\"");
}

#[test]
fn switch_case_expr_preserves_marshaled_string_tags() {
    let compiled = LambdaCompiler::switch_case_expr(&SwitchCaseTag::String("\\\"".to_string()));

    assert!(matches!(
        compiled,
        Expression {
            desc: ExpressionDesc::Str {
                delim: Delim::StarJ,
                ref txt,
            },
            ..
        } if txt == "\\\""
    ));
    assert_eq!(print_expression(&compiled), "\"\\\"\"");
}

#[test]
fn compile_constant_nested_some_none_preserves_nested_optional_boxes() {
    let compiled = LambdaCompiler::compile_constant(&Constant::Some(Box::new(Constant::Some(
        Box::new(Constant::JsUndefined { is_unit: false }),
    ))));

    assert_eq!(
        print_expression(&compiled),
        "Primitive_option.some(Primitive_option.some(undefined))"
    );
}

#[test]
fn compile_float_pow_uses_js_exponentiation_operator() {
    let mut compiler = LambdaCompiler::new();
    let compiled = compiler.compile_expr(&Lambda::prim(
        Primitive::Ppowfloat,
        vec![
            Lambda::const_(Constant::float("2.")),
            Lambda::const_(Constant::float("3.")),
        ],
        Location::none(),
    ));

    assert!(compiled.prelude.is_empty());
    assert!(matches!(
        &compiled.expr,
        Expression {
            desc: ExpressionDesc::Bin(BinOp::Pow, left, right),
            ..
        } if matches!(
            left.as_ref(),
            Expression {
                desc: ExpressionDesc::Number(Number::Float(_)),
                ..
            }
        ) && matches!(
            right.as_ref(),
            Expression {
                desc: ExpressionDesc::Number(Number::Float(_)),
                ..
            }
        )
    ));
    let printed = print_expression(&compiled.expr);
    assert!(
        printed.contains("**"),
        "expected exponentiation operator, got {printed}"
    );
    assert!(
        !printed.contains("Math.pow"),
        "expected float pow lowering to avoid Math.pow, got {printed}"
    );
}

#[test]
fn compile_int_pow_folds_small_int_literals_like_ocaml_ext_int() {
    let mut compiler = LambdaCompiler::new();
    let compiled = compiler.compile_expr(&Lambda::prim(
        Primitive::Ppowint,
        vec![
            Lambda::const_(Constant::int(2)),
            Lambda::const_(Constant::int(2)),
        ],
        Location::none(),
    ));

    assert!(compiled.prelude.is_empty());
    assert_int_expr(&compiled.expr, 4);
}

#[test]
fn compile_int_pow_folds_overflowing_int_literals_like_ocaml_ext_int() {
    let mut compiler = LambdaCompiler::new();
    let compiled = compiler.compile_expr(&Lambda::prim(
        Primitive::Ppowint,
        vec![
            Lambda::const_(Constant::int(2_147_483_647)),
            Lambda::const_(Constant::int(2)),
        ],
        Location::none(),
    ));

    assert!(compiled.prelude.is_empty());
    assert_int_expr(&compiled.expr, 0);
}

#[test]
fn compile_create_extension_uses_primitive_exceptions_create() {
    let mut compiler = LambdaCompiler::new();
    let compiled = compiler.compile_expr(&Lambda::prim(
        Primitive::PcreateExtension("Local_exception_test.A".to_string()),
        vec![],
        Location::none(),
    ));

    assert!(compiled.prelude.is_empty());
    let ExpressionDesc::Call(func, args, _) = &compiled.expr.desc else {
        panic!("expected extension constructors to lower to a runtime call");
    };
    assert!(matches!(
        func.as_ref(),
        Expression {
            desc: ExpressionDesc::Var(crate::js_ir::VIdent::Qualified(module, Some(member))),
            ..
        } if module.id.name() == "Primitive_exceptions" && member == "create"
    ));
    assert!(matches!(
        args.as_slice(),
        [Expression {
            desc: ExpressionDesc::Str { txt, .. },
            ..
        }] if txt == "Local_exception_test.A"
    ));
    assert_eq!(compiled.expr.comment.as_deref(), Some("@__PURE__"));
    assert_eq!(
        print_expression(&compiled.expr),
        "/* @__PURE__ */Primitive_exceptions.create(\"Local_exception_test.A\")"
    );
}

#[test]
fn compile_wrap_exn_uses_primitive_exceptions_internal_to_exception() {
    let mut compiler = LambdaCompiler::new();
    let exn = Ident::create_local("exn");
    let compiled = compiler.compile_expr(&Lambda::prim(
        Primitive::PwrapExn,
        vec![Lambda::var(exn.clone())],
        Location::none(),
    ));

    assert!(compiled.prelude.is_empty());
    let ExpressionDesc::Call(func, args, _) = &compiled.expr.desc else {
        panic!("expected exception wrapping to lower to a runtime call");
    };
    assert!(matches!(
        func.as_ref(),
        Expression {
            desc: ExpressionDesc::Var(crate::js_ir::VIdent::Qualified(module, Some(member))),
            ..
        } if module.id.name() == "Primitive_exceptions" && member == "internalToException"
    ));
    assert!(matches!(
        args.as_slice(),
        [Expression {
            desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
            ..
        }] if id.same(&exn)
    ));
}

#[test]
fn compile_module_primitives_lower_to_primitive_module_runtime_calls_like_ocaml() {
    let mut compiler = LambdaCompiler::new();
    let loc = Location::none();
    let init = compiler.compile_expr(&Lambda::prim(
        Primitive::PinitMod,
        vec![
            Lambda::const_(Constant::int(1)),
            Lambda::var(Ident::create_local("shape")),
        ],
        loc.clone(),
    ));
    assert!(init.prelude.is_empty());
    assert_eq!(
        print_expression(&init.expr),
        "Primitive_module.init(1, shape)"
    );

    let update = compiler.compile_expr(&Lambda::prim(
        Primitive::PupdateMod,
        vec![
            Lambda::var(Ident::create_local("shape")),
            Lambda::var(Ident::create_local("point")),
            Lambda::var(Ident::create_local("value")),
        ],
        loc,
    ));
    assert!(update.prelude.is_empty());
    assert_eq!(
        print_expression(&update.expr),
        "Primitive_module.update(shape, point, value)"
    );
}

#[test]
fn compile_module_primitives_require_primitive_module_runtime_import() {
    let mut compiler = LambdaCompiler::new();
    let module_slot = Ident::create_local("point");
    let lam = Lambda::let_(
        LetKind::Strict,
        module_slot.clone(),
        Lambda::prim(
            Primitive::PinitMod,
            vec![
                Lambda::const_(Constant::int(1)),
                Lambda::const_(Constant::string("shape")),
            ],
            Location::none(),
        ),
        Lambda::seq(
            Lambda::unit(),
            Lambda::prim(
                Primitive::PupdateMod,
                vec![
                    Lambda::const_(Constant::string("shape")),
                    Lambda::var(module_slot),
                    Lambda::const_(Constant::string("value")),
                ],
                Location::none(),
            ),
        ),
    );

    let deps = compiler.compile_deps_program(&lam);
    assert!(deps.modules.iter().any(|module| {
        module.kind == Kind::Runtime && module.id.name() == "Primitive_module"
    }));

    let resolver = ModulePathResolver::from_compile_options(
        None,
        Some(std::path::Path::new("/tmp/module_primitive.mjs")),
        None,
        None,
    );
    let rendered = print_deps_program(&deps, Some(&resolver));
    assert!(rendered.contains(
        "import * as Primitive_module from \"@rescript/runtime/lib/es6/Primitive_module.js\";"
    ));
    assert!(rendered.contains("let point = Primitive_module.init(1, \"shape\");"));
    assert!(rendered.contains("Primitive_module.update(\"shape\", point, \"value\");"));
}

#[test]
fn compile_int_order_uses_primitive_int_compare() {
    let mut compiler = LambdaCompiler::new();
    let left = Ident::create_local("left");
    let right = Ident::create_local("right");
    let compiled = compiler.compile_expr(&Lambda::prim(
        Primitive::Pintorder,
        vec![Lambda::var(left), Lambda::var(right)],
        Location::none(),
    ));

    assert!(compiled.prelude.is_empty());
    assert_eq!(
        print_expression(&compiled.expr),
        "Primitive_int.compare(left, right)"
    );
}

#[test]
fn compile_checked_int_div_uses_primitive_int_runtime_call_like_ocaml() {
    let mut compiler = LambdaCompiler::new();
    let left = Ident::create_local("left");
    let compiled = compiler.compile_expr(&Lambda::prim(
        Primitive::Pdivint,
        vec![Lambda::var(left), Lambda::const_(Constant::int(0))],
        Location::none(),
    ));

    assert!(compiled.prelude.is_empty());
    assert_eq!(
        print_expression(&compiled.expr),
        "Primitive_int.div(left, 0)"
    );
}

#[test]
fn compile_checked_int_mod_uses_primitive_int_runtime_call_like_ocaml() {
    let mut compiler = LambdaCompiler::new();
    let left = Ident::create_local("left");
    let compiled = compiler.compile_expr(&Lambda::prim(
        Primitive::Pmodint,
        vec![Lambda::var(left), Lambda::const_(Constant::int(0))],
        Location::none(),
    ));

    assert!(compiled.prelude.is_empty());
    assert_eq!(
        print_expression(&compiled.expr),
        "Primitive_int.mod_(left, 0)"
    );
}

#[test]
fn compile_checked_bigint_div_uses_primitive_bigint_runtime_call_like_ocaml() {
    let mut compiler = LambdaCompiler::new();
    let left = Ident::create_local("left");
    let compiled = compiler.compile_expr(&Lambda::prim(
        Primitive::Pdivbigint,
        vec![
            Lambda::var(left),
            Lambda::const_(Constant::bigint(false, "0")),
        ],
        Location::none(),
    ));

    assert!(compiled.prelude.is_empty());
    assert_eq!(
        print_expression(&compiled.expr),
        "Primitive_bigint.div(left, 0n)"
    );
}

#[test]
fn compile_checked_bigint_mod_uses_primitive_bigint_runtime_call_like_ocaml() {
    let mut compiler = LambdaCompiler::new();
    let left = Ident::create_local("left");
    let compiled = compiler.compile_expr(&Lambda::prim(
        Primitive::Pmodbigint,
        vec![
            Lambda::var(left),
            Lambda::const_(Constant::bigint(false, "0")),
        ],
        Location::none(),
    ));

    assert!(compiled.prelude.is_empty());
    assert_eq!(
        print_expression(&compiled.expr),
        "Primitive_bigint.mod_(left, 0n)"
    );
}

#[test]
fn compile_string_order_uses_primitive_string_compare() {
    let mut compiler = LambdaCompiler::new();
    let left = Ident::create_local("left");
    let right = Ident::create_local("right");
    let compiled = compiler.compile_expr(&Lambda::prim(
        Primitive::Pstringorder,
        vec![Lambda::var(left), Lambda::var(right)],
        Location::none(),
    ));

    assert!(compiled.prelude.is_empty());
    assert_eq!(
        print_expression(&compiled.expr),
        "Primitive_string.compare(left, right)"
    );
}

#[test]
fn compile_arrayrefu_uses_direct_array_index() {
    let mut compiler = LambdaCompiler::new();
    let array = Ident::create_local("arr");
    let index = Ident::create_local("i");
    let compiled = compiler.compile_expr(&Lambda::prim(
        Primitive::Parrayrefu,
        vec![Lambda::var(array), Lambda::var(index)],
        Location::none(),
    ));

    assert!(compiled.prelude.is_empty());
    assert_eq!(print_expression(&compiled.expr), "arr[i]");
}

#[test]
fn compile_arrayrefs_uses_primitive_array_get() {
    let mut compiler = LambdaCompiler::new();
    let array = Ident::create_local("arr");
    let index = Ident::create_local("i");
    let compiled = compiler.compile_expr(&Lambda::prim(
        Primitive::Parrayrefs,
        vec![Lambda::var(array), Lambda::var(index)],
        Location::none(),
    ));

    assert!(compiled.prelude.is_empty());
    assert_eq!(
        print_expression(&compiled.expr),
        "Primitive_array.get(arr, i)"
    );
}

#[test]
fn compile_arraysetu_sequences_assignment_to_unit() {
    let mut compiler = LambdaCompiler::new();
    let array = Ident::create_local("arr");
    let index = Ident::create_local("i");
    let value = Ident::create_local("value");
    let compiled = compiler.compile_expr(&Lambda::prim(
        Primitive::Parraysetu,
        vec![
            Lambda::var(array.clone()),
            Lambda::var(index.clone()),
            Lambda::var(value.clone()),
        ],
        Location::none(),
    ));

    assert!(compiled.prelude.is_empty());
    let ExpressionDesc::Seq(assign, tail) = &compiled.expr.desc else {
        panic!("expected array set to lower to a seq");
    };
    let ExpressionDesc::Bin(BinOp::Eq, lhs, rhs) = &assign.desc else {
        panic!("expected array set seq head to be an assignment");
    };
    let ExpressionDesc::ArrayIndex(target, position) = &lhs.desc else {
        panic!("expected array set assignment lhs to be an array index");
    };
    assert!(matches!(
        target.as_ref(),
        Expression {
            desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
            ..
        } if id.same(&array)
    ));
    assert!(matches!(
        position.as_ref(),
        Expression {
            desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
            ..
        } if id.same(&index)
    ));
    assert!(matches!(
        rhs.as_ref(),
        Expression {
            desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
            ..
        } if id.same(&value)
    ));
    assert!(matches!(
        tail.as_ref(),
        Expression {
            desc: ExpressionDesc::Undefined { is_unit: false },
            ..
        }
    ));
}

#[test]
fn compile_arraysets_uses_primitive_array_set() {
    let mut compiler = LambdaCompiler::new();
    let array = Ident::create_local("arr");
    let index = Ident::create_local("i");
    let value = Ident::create_local("value");
    let compiled = compiler.compile_expr(&Lambda::prim(
        Primitive::Parraysets,
        vec![Lambda::var(array), Lambda::var(index), Lambda::var(value)],
        Location::none(),
    ));

    assert!(compiled.prelude.is_empty());
    assert_eq!(
        print_expression(&compiled.expr),
        "Primitive_array.set(arr, i, value)"
    );
}

#[test]
fn compile_string_refs_use_primitive_string_get_char() {
    let mut compiler = LambdaCompiler::new();
    let string = Ident::create_local("str");
    let index = Ident::create_local("i");
    let compiled = compiler.compile_expr(&Lambda::prim(
        Primitive::Pstringrefs,
        vec![Lambda::var(string), Lambda::var(index)],
        Location::none(),
    ));

    assert!(compiled.prelude.is_empty());
    assert_eq!(
        print_expression(&compiled.expr),
        "Primitive_string.getChar(str, i)"
    );
}

#[test]
fn compile_obj_compare_against_null_uses_strict_equality() {
    let mut compiler = LambdaCompiler::new();
    let value = Ident::create_local("value");
    let compiled = compiler.compile_expr(&Lambda::prim(
        Primitive::Pobjcomp(Comparison::Eq),
        vec![Lambda::const_(Constant::JsNull), Lambda::var(value)],
        Location::none(),
    ));

    assert!(compiled.prelude.is_empty());
    assert_eq!(print_expression(&compiled.expr), "null === value");
}

#[test]
fn compile_obj_compare_null_against_number_literal_folds_false() {
    let mut compiler = LambdaCompiler::new();
    let compiled = compiler.compile_expr(&Lambda::prim(
        Primitive::Pobjcomp(Comparison::Eq),
        vec![
            Lambda::const_(Constant::JsNull),
            Lambda::const_(Constant::int(5)),
        ],
        Location::none(),
    ));

    assert!(compiled.prelude.is_empty());
    assert_eq!(print_expression(&compiled.expr), "false");
}

#[test]
fn compile_obj_notequal_undefined_against_number_literal_folds_true() {
    let mut compiler = LambdaCompiler::new();
    let compiled = compiler.compile_expr(&Lambda::prim(
        Primitive::Pobjcomp(Comparison::Neq),
        vec![
            Lambda::const_(Constant::JsUndefined { is_unit: false }),
            Lambda::const_(Constant::int(5)),
        ],
        Location::none(),
    ));

    assert!(compiled.prelude.is_empty());
    assert_eq!(print_expression(&compiled.expr), "true");
}

#[test]
fn compile_obj_order_uses_primitive_object_compare() {
    let mut compiler = LambdaCompiler::new();
    let left = Ident::create_local("left");
    let right = Ident::create_local("right");
    let compiled = compiler.compile_expr(&Lambda::prim(
        Primitive::Pobjorder,
        vec![Lambda::var(left), Lambda::var(right)],
        Location::none(),
    ));

    assert!(compiled.prelude.is_empty());
    assert_eq!(
        print_expression(&compiled.expr),
        "Primitive_object.compare(left, right)"
    );
}

#[test]
fn compile_eta_wrapped_object_compare_function_aliases_runtime_member() {
    let mut compiler = LambdaCompiler::new();
    let left = Ident::create_local("left");
    let right = Ident::create_local("right");
    let compiled = compiler.compile_expr(&Lambda::function_(
        2,
        vec![left.clone(), right.clone()],
        Lambda::prim(
            Primitive::Pobjorder,
            vec![Lambda::var(left), Lambda::var(right)],
            Location::none(),
        ),
        Default::default(),
    ));

    assert!(compiled.prelude.is_empty());
    assert_eq!(print_expression(&compiled.expr), "Primitive_object.compare");
}

#[test]
fn compile_obj_tag_uses_caml_block_tag_access_like_ocaml() {
    let mut compiler = LambdaCompiler::new();
    let value = Ident::create_local("value");
    let compiled = compiler.compile_expr(&Lambda::prim(
        Primitive::Pobjtag,
        vec![Lambda::var(value.clone())],
        Location::none(),
    ));

    assert!(compiled.prelude.is_empty());
    assert_eq!(print_expression(&compiled.expr), "value.TAG");
}

#[test]
fn compile_obj_size_uses_caml_block_length_like_ocaml() {
    let mut compiler = LambdaCompiler::new();
    let value = Ident::create_local("value");
    let compiled = compiler.compile_expr(&Lambda::prim(
        Primitive::Pobjsize,
        vec![Lambda::var(value.clone())],
        Location::none(),
    ));

    assert!(compiled.prelude.is_empty());
    assert_eq!(print_expression(&compiled.expr), "value.length");
}

#[test]
fn compile_eta_wrapped_float_compare_function_aliases_runtime_member() {
    let mut compiler = LambdaCompiler::new();
    let left = Ident::create_local("x");
    let right = Ident::create_local("y");
    let compiled = compiler.compile_expr(&Lambda::function_(
        2,
        vec![left.clone(), right.clone()],
        Lambda::prim(
            Primitive::Pfloatorder,
            vec![Lambda::var(left), Lambda::var(right)],
            Location::none(),
        ),
        Default::default(),
    ));

    assert!(compiled.prelude.is_empty());
    assert_eq!(print_expression(&compiled.expr), "Primitive_float.compare");
}

#[test]
fn compile_expr_keeps_forwarded_module_call_params_like_ocaml() {
    let mut compiler = LambdaCompiler::new();
    let none = Ident::create_local("none");
    let icmp = Ident::create_persistent("Icmp");
    let belt_map = Ident::create_persistent("Belt_Map");

    let compiled = compiler.compile_expr(&Lambda::function_(
        1,
        vec![none.clone()],
        Lambda::Lapply(Apply {
            ap_func: Box::new(Lambda::prim(
                Primitive::Pfield(
                    23,
                    FieldDbgInfo::Module {
                        name: "fromArray".to_string(),
                    },
                ),
                vec![Lambda::LglobalModule(belt_map, false)],
                Location::none(),
            )),
            ap_args: vec![Lambda::var(none.clone()), Lambda::var(icmp.clone())],
            ap_info: ApInfo {
                loc: Location::none(),
                inlined: InlineAttribute::Default,
                status: ApplyStatus::Uncurry,
            },
            ap_transformed_jsx: false,
        }),
        Default::default(),
    ));

    let rendered = print_expression(&compiled.expr);
    assert!(
        compiled.prelude.is_empty(),
        "expected the forwarding wrapper to compile as a pure expression, got prelude:\n{}",
        print_block(&compiled.prelude)
    );
    assert!(
        rendered.contains("fromArray(none, Icmp)"),
        "expected forwarded wrapper parameter to survive in the lowered call, got:\n{rendered}"
    );
    assert!(
        !rendered.contains("fromArray(undefined, Icmp)"),
        "unexpected forwarded parameter loss in lowered call:\n{rendered}"
    );
}

#[test]
fn compile_expr_keeps_forwarded_nested_wrapper_params_like_ocaml() {
    let mut compiler = LambdaCompiler::new();
    let a = Ident::create_local("a");
    let b = Ident::create_local("b");
    let extra = Ident::create_local("extra");
    let belt_map = Ident::create_persistent("Belt_Map");

    let compiled = compiler.compile_expr(&Lambda::function_(
        2,
        vec![a.clone(), b.clone()],
        Lambda::function_(
            1,
            vec![extra.clone()],
            Lambda::Lapply(Apply {
                ap_func: Box::new(Lambda::prim(
                    Primitive::Pfield(
                        9,
                        FieldDbgInfo::Module {
                            name: "eq".to_string(),
                        },
                    ),
                    vec![Lambda::LglobalModule(belt_map, false)],
                    Location::none(),
                )),
                ap_args: vec![
                    Lambda::var(a.clone()),
                    Lambda::var(b.clone()),
                    Lambda::var(extra.clone()),
                ],
                ap_info: ApInfo {
                    loc: Location::none(),
                    inlined: InlineAttribute::Default,
                    status: ApplyStatus::Uncurry,
                },
                ap_transformed_jsx: false,
            }),
            Default::default(),
        ),
        Default::default(),
    ));

    let rendered = print_expression(&compiled.expr);
    assert!(
        compiled.prelude.is_empty(),
        "expected the nested forwarding wrapper to compile as a pure expression, got prelude:\n{}",
        print_block(&compiled.prelude)
    );
    assert!(
        rendered.contains("eq(a, b, extra)"),
        "expected nested wrapper parameter to survive in the lowered call, got:\n{rendered}"
    );
    assert!(
        !rendered.contains("eq(a, b, undefined)"),
        "unexpected nested wrapper parameter loss in lowered call:\n{rendered}"
    );
}

#[test]
fn compile_effectful_underscore_binding_from_nested_js_function_calls_survives_shake() {
    let mut compiler = LambdaCompiler::new();
    let outer_fn_param = Ident::create_local("x");
    let inner_true_param = Ident::create_local("f");
    let inner_zero_param = Ident::create_local("f");
    let unused = Ident::create_local("_s");
    let always_true = Ident::create_local("h");
    let also_true = Ident::create_local("j");
    let loc = Location::none();
    let starj_empty = Lambda::const_(Constant::String {
        s: "".to_string(),
        delim: Some(StringDelim::StarJ),
    });

    let outer_value = Lambda::let_(
        LetKind::Strict,
        always_true,
        Lambda::true_(),
        Lambda::prim(
            Primitive::PjsFnMake(1),
            vec![Lambda::function_(
                1,
                vec![outer_fn_param.clone()],
                Lambda::let_(
                    LetKind::Strict,
                    also_true,
                    Lambda::prim(
                        Primitive::PjsFnMake(1),
                        vec![Lambda::function_(
                            1,
                            vec![inner_true_param],
                            Lambda::true_(),
                            FunctionAttribute::default(),
                        )],
                        loc.clone(),
                    ),
                    Lambda::prim(
                        Primitive::PjsFnMake(1),
                        vec![Lambda::function_(
                            1,
                            vec![inner_zero_param],
                            Lambda::const_(Constant::int(0)),
                            FunctionAttribute::default(),
                        )],
                        loc.clone(),
                    ),
                ),
                FunctionAttribute::default(),
            )],
            loc.clone(),
        ),
    );
    let nested_call = Lambda::Lapply(Apply {
        ap_func: Box::new(Lambda::Lapply(Apply {
            ap_func: Box::new(outer_value),
            ap_args: vec![starj_empty.clone()],
            ap_info: ApInfo {
                loc: loc.clone(),
                inlined: InlineAttribute::Default,
                status: ApplyStatus::Uncurry,
            },
            ap_transformed_jsx: false,
        })),
        ap_args: vec![starj_empty],
        ap_info: ApInfo {
            loc: loc.clone(),
            inlined: InlineAttribute::Default,
            status: ApplyStatus::Uncurry,
        },
        ap_transformed_jsx: false,
    });
    let program = compiler.compile_program(&Lambda::let_(
        LetKind::Strict,
        unused,
        nested_call,
        Lambda::unit(),
    ));

    let rendered = print_block(&program.block);
    assert!(
        rendered.contains("(f => 0)(\"\")"),
        "expected the top-level call to survive, got:\n{rendered}"
    );
}

#[test]
fn compile_hash_primitives_lower_to_primitive_hash_runtime_calls_like_ocaml() {
    let mut compiler = LambdaCompiler::new();
    let x = Ident::create_local("x");
    let seed = Ident::create_local("seed");
    let value = Ident::create_local("value");

    let hash = compiler.compile_expr(&Lambda::prim(
        Primitive::Phash,
        vec![
            Lambda::const_(Constant::int(10)),
            Lambda::const_(Constant::int(100)),
            Lambda::const_(Constant::int(0)),
            Lambda::var(x.clone()),
        ],
        Location::none(),
    ));
    assert!(hash.prelude.is_empty());
    assert_eq!(
        print_expression(&hash.expr),
        "Primitive_hash.hash(10, 100, 0, x)"
    );

    let hash_mix_int = compiler.compile_expr(&Lambda::prim(
        Primitive::PhashMixint,
        vec![Lambda::var(seed.clone()), Lambda::var(value.clone())],
        Location::none(),
    ));
    assert!(hash_mix_int.prelude.is_empty());
    assert_eq!(
        print_expression(&hash_mix_int.expr),
        "Primitive_hash.hash_mix_int(seed, value)"
    );

    let hash_mix_string = compiler.compile_expr(&Lambda::prim(
        Primitive::PhashMixstring,
        vec![Lambda::var(seed.clone()), Lambda::var(value.clone())],
        Location::none(),
    ));
    assert!(hash_mix_string.prelude.is_empty());
    assert_eq!(
        print_expression(&hash_mix_string.expr),
        "Primitive_hash.hash_mix_string(seed, value)"
    );

    let hash_final_mix = compiler.compile_expr(&Lambda::prim(
        Primitive::PhashFinalmix,
        vec![Lambda::var(seed)],
        Location::none(),
    ));
    assert!(hash_final_mix.prelude.is_empty());
    assert_eq!(
        print_expression(&hash_final_mix.expr),
        "Primitive_hash.hash_final_mix(seed)"
    );
}

#[test]
fn compile_eta_wrapped_hash_function_aliases_runtime_member() {
    let mut compiler = LambdaCompiler::new();
    let hash_limit = Ident::create_local("hash_limit");
    let hash_count = Ident::create_local("hash_count");
    let hash_acc = Ident::create_local("hash_acc");
    let value = Ident::create_local("value");
    let compiled = compiler.compile_expr(&Lambda::function_(
        4,
        vec![
            hash_limit.clone(),
            hash_count.clone(),
            hash_acc.clone(),
            value.clone(),
        ],
        Lambda::prim(
            Primitive::Phash,
            vec![
                Lambda::var(hash_limit),
                Lambda::var(hash_count),
                Lambda::var(hash_acc),
                Lambda::var(value),
            ],
            Location::none(),
        ),
        Default::default(),
    ));

    assert!(compiled.prelude.is_empty());
    assert_eq!(print_expression(&compiled.expr), "Primitive_hash.hash");
}

#[test]
fn compile_compare_against_zero_elides_runtime_compare_call_like_ocaml() {
    let mut compiler = LambdaCompiler::new();
    let left = Ident::create_local("x");
    let right = Ident::create_local("y");
    let compiled = compiler.compile_expr(&Lambda::prim(
        Primitive::Pintcomp(Comparison::Gt),
        vec![
            Lambda::prim(
                Primitive::Pfloatorder,
                vec![Lambda::var(left.clone()), Lambda::var(right.clone())],
                Location::none(),
            ),
            Lambda::const_(Constant::int(0)),
        ],
        Location::none(),
    ));

    assert!(compiled.prelude.is_empty());
    assert_eq!(print_expression(&compiled.expr), "x > y");
}

#[test]
fn compile_bigint_compare_against_zero_elides_runtime_compare_call_like_ocaml() {
    let mut compiler = LambdaCompiler::new();
    let compiled = compiler.compile_expr(&Lambda::prim(
        Primitive::Pintcomp(Comparison::Lt),
        vec![
            Lambda::prim(
                Primitive::Pfloatorder,
                vec![
                    Lambda::const_(Constant::BigInt {
                        negative: false,
                        value: "123".to_string(),
                    }),
                    Lambda::const_(Constant::BigInt {
                        negative: false,
                        value: "555555".to_string(),
                    }),
                ],
                Location::none(),
            ),
            Lambda::const_(Constant::int(0)),
        ],
        Location::none(),
    ));

    assert!(compiled.prelude.is_empty());
    assert_eq!(print_expression(&compiled.expr), "123n < 555555n");
}

#[test]
fn compile_bigint_literal_equality_folds_like_ocaml() {
    let mut compiler = LambdaCompiler::new();
    let compiled = compiler.compile_expr(&Lambda::prim(
        Primitive::Pbigintcomp(Comparison::Eq),
        vec![
            Lambda::const_(Constant::BigInt {
                negative: false,
                value: "001000".to_string(),
            }),
            Lambda::const_(Constant::BigInt {
                negative: false,
                value: "1000".to_string(),
            }),
        ],
        Location::none(),
    ));

    assert!(compiled.prelude.is_empty());
    assert_eq!(print_expression(&compiled.expr), "true");
}

#[test]
fn compile_eta_wrapped_float_equality_stays_as_function() {
    let mut compiler = LambdaCompiler::new();
    let left = Ident::create_local("x");
    let right = Ident::create_local("y");
    let compiled = compiler.compile_expr(&Lambda::function_(
        2,
        vec![left.clone(), right.clone()],
        Lambda::prim(
            Primitive::Pfloatcomp(Comparison::Eq),
            vec![Lambda::var(left), Lambda::var(right)],
            Location::none(),
        ),
        Default::default(),
    ));

    assert!(compiled.prelude.is_empty());
    assert!(matches!(compiled.expr.desc, ExpressionDesc::Fun { .. }));
}

#[test]
fn compile_bigint_min_literals_use_conditional_fast_path() {
    let mut compiler = LambdaCompiler::new();
    let compiled = compiler.compile_expr(&Lambda::prim(
        Primitive::Pbigintmin,
        vec![
            Lambda::const_(Constant::BigInt {
                negative: false,
                value: "9".to_string(),
            }),
            Lambda::const_(Constant::BigInt {
                negative: false,
                value: "1".to_string(),
            }),
        ],
        Location::none(),
    ));

    assert!(compiled.prelude.is_empty());
    assert_eq!(print_expression(&compiled.expr), "9n < 1n ? 9n : 1n");
}

#[test]
fn compile_bigint_arithmetic_primitives_use_raw_js_bigint_ops_like_ocaml() {
    let mut compiler = LambdaCompiler::new();
    let lhs = Lambda::const_(Constant::BigInt {
        negative: false,
        value: "9".to_string(),
    });
    let rhs = Lambda::const_(Constant::BigInt {
        negative: false,
        value: "1".to_string(),
    });

    let add = compiler.compile_expr(&Lambda::prim(
        Primitive::Paddbigint,
        vec![lhs.clone(), rhs.clone()],
        Location::none(),
    ));
    assert!(add.prelude.is_empty());
    assert_eq!(print_expression(&add.expr), "9n + 1n");

    let pow = compiler.compile_expr(&Lambda::prim(
        Primitive::Ppowbigint,
        vec![lhs.clone(), rhs.clone()],
        Location::none(),
    ));
    assert!(pow.prelude.is_empty());
    assert_eq!(print_expression(&pow.expr), "9n ** 1n");

    let neg = compiler.compile_expr(&Lambda::prim(
        Primitive::Pnegbigint,
        vec![lhs],
        Location::none(),
    ));
    assert!(neg.prelude.is_empty());
    assert_eq!(print_expression(&neg.expr), "0n - 9n");
}

#[test]
fn compile_bigint_bitwise_primitives_use_raw_js_bigint_ops_like_ocaml() {
    let mut compiler = LambdaCompiler::new();
    let lhs = Lambda::const_(Constant::BigInt {
        negative: false,
        value: "9".to_string(),
    });
    let rhs = Lambda::const_(Constant::BigInt {
        negative: false,
        value: "1".to_string(),
    });

    let land = compiler.compile_expr(&Lambda::prim(
        Primitive::Pandbigint,
        vec![lhs.clone(), rhs.clone()],
        Location::none(),
    ));
    assert!(land.prelude.is_empty());
    assert_eq!(print_expression(&land.expr), "9n & 1n");

    let lsl = compiler.compile_expr(&Lambda::prim(
        Primitive::Plslbigint,
        vec![lhs.clone(), rhs.clone()],
        Location::none(),
    ));
    assert!(lsl.prelude.is_empty());
    assert_eq!(print_expression(&lsl.expr), "(9n << 1n)");

    let lnot = compiler.compile_expr(&Lambda::prim(
        Primitive::Pnotbigint,
        vec![lhs],
        Location::none(),
    ));
    assert!(lnot.prelude.is_empty());
    assert_eq!(print_expression(&lnot.expr), "~9n");
}

#[test]
fn compile_duprecord_lowers_to_object_spread_like_ocaml() {
    let mut compiler = LambdaCompiler::new();
    let source = Ident::create_local("source");
    let compiled = compiler.compile_expr(&Lambda::prim(
        Primitive::Pduprecord,
        vec![Lambda::var(source)],
        Location::none(),
    ));

    assert!(compiled.prelude.is_empty());
    assert_eq!(print_expression(&compiled.expr), "{...source}");
}

#[test]
fn compile_deps_program_reuses_same_name_export_targets() {
    let mut compiler = LambdaCompiler::new();
    let source = Ident::create_local("value");
    let rebound_export = Ident::create_local("value");
    let param = Ident::create_local("arg");
    let lam = Lambda::let_(
        LetKind::Strict,
        source.clone(),
        Lambda::function_(
            1,
            vec![param.clone()],
            Lambda::var(param),
            crate::lambda::FunctionAttribute::default(),
        ),
        Lambda::let_(
            LetKind::Alias,
            rebound_export.clone(),
            Lambda::var(source.clone()),
            Lambda::prim(
                Primitive::Pmakeblock(
                    0,
                    TagInfo::ModuleExport(vec![rebound_export]),
                    Mutable::Immutable,
                ),
                vec![Lambda::var(source.clone())],
                Location::none(),
            ),
        ),
    );

    let deps = compiler.compile_deps_program(&lam);

    let [exported] = deps.program.exports.as_slice() else {
        panic!("expected a single export");
    };
    assert!(
        exported.same(&source),
        "expected export {:?}, got {:?}",
        source,
        exported
    );

    let [stmt] = deps.program.block.as_slice() else {
        panic!("expected the rebound export alias to be shaken away");
    };
    match &stmt.desc {
        StatementDesc::Variable(VariableDeclaration { ident, .. }) => {
            assert!(ident.same(&source))
        }
        other => panic!("expected only the original exported binding to remain, got {other:?}"),
    }
}

#[test]
fn coerce_toplevel_exports_reuses_existing_undefined_binding() {
    let mut compiler = LambdaCompiler::new();
    let alias = Ident::create_local("VS");
    let other = Ident::create_local("y");
    let mut block = vec![
        Statement::variable(VariableDeclaration {
            ident: alias.clone(),
            value: Some(Expression::undefined(false)),
            property: LetKind::Strict,
            ident_info: IdentInfo::default(),
        }),
        Statement::variable(VariableDeclaration {
            ident: other.clone(),
            value: Some(Expression::number(Number::int(13))),
            property: LetKind::Strict,
            ident_info: IdentInfo::default(),
        }),
    ];

    let exports = compiler.coerce_toplevel_exports(
        &mut block,
        ExtractedExports {
            exports: vec![alias.clone(), other.clone()],
            values: vec![Expression::undefined(false), Expression::var(other.clone())],
        },
    );

    assert_eq!(exports, vec![alias.clone(), other.clone()]);
    let [first, second] = block.as_slice() else {
        panic!("expected the existing bindings to be reused without rebound placeholders");
    };
    match &first.desc {
        StatementDesc::Variable(VariableDeclaration { ident, .. }) => {
            assert!(ident.same(&alias))
        }
        other => panic!("expected the original alias binding first, got {other:?}"),
    }
    match &second.desc {
        StatementDesc::Variable(VariableDeclaration { ident, .. }) => {
            assert!(ident.same(&other))
        }
        other => panic!("expected the later binding second, got {other:?}"),
    }
}

#[test]
fn coerce_toplevel_exports_keeps_undefined_rebound_after_later_effects() {
    let mut compiler = LambdaCompiler::new();
    let alias = Ident::create_local("MyURL");
    let callback = Ident::create_persistent("callback");
    let mut block = vec![
        Statement::variable(VariableDeclaration {
            ident: alias.clone(),
            value: Some(Expression::undefined(false)),
            property: LetKind::Strict,
            ident_info: IdentInfo::default(),
        }),
        Statement::exp(Expression::call(
            Expression::var(callback),
            vec![],
            CallInfo::default(),
        )),
    ];

    let exports = compiler.coerce_toplevel_exports(
        &mut block,
        ExtractedExports {
            exports: vec![alias.clone()],
            values: vec![Expression::undefined(false)],
        },
    );

    let [decl, effect, rebound] = block.as_slice() else {
        panic!("expected the later effect to force a trailing rebound placeholder");
    };
    match &decl.desc {
        StatementDesc::Variable(VariableDeclaration { ident, .. }) => {
            assert!(ident.same(&alias))
        }
        other => panic!("expected the original alias binding first, got {other:?}"),
    }
    assert!(matches!(effect.desc, StatementDesc::Exp(_)));
    match &rebound.desc {
        StatementDesc::Variable(VariableDeclaration { ident, .. }) => {
            assert!(
                !ident.same(&alias),
                "expected a rebound export placeholder at the tail"
            );
            assert_eq!(ident.name(), alias.name());
            assert_eq!(exports, vec![ident.clone()]);
        }
        other => panic!("expected the trailing rebound export placeholder, got {other:?}"),
    }
}

#[test]
fn coerce_toplevel_exports_skips_unreachable_undefined_placeholder_after_throw() {
    let mut compiler = LambdaCompiler::new();
    let exported = Ident::create_local("u");
    let mut block = vec![Statement::throw(Expression::string("boom".to_string()))];

    let exports = compiler.coerce_toplevel_exports(
        &mut block,
        ExtractedExports {
            exports: vec![exported.clone()],
            values: vec![Expression::undefined(false)],
        },
    );

    assert_eq!(exports, vec![exported.clone()]);
    let [stmt] = block.as_slice() else {
        panic!("expected the terminating effect to stay alone in the block");
    };
    assert!(matches!(
        stmt.desc,
        StatementDesc::Throw(Expression {
            desc: ExpressionDesc::Str { .. },
            ..
        })
    ));
}

#[test]
fn compile_deps_program_preserves_toplevel_binding_order_during_shake() {
    let mut compiler = LambdaCompiler::new();
    let first = Ident::create_local("first");
    let second = Ident::create_local("second");
    let lam = Lambda::let_(
        LetKind::Strict,
        first.clone(),
        Lambda::const_(Constant::int(3)),
        Lambda::let_(
            LetKind::Strict,
            second.clone(),
            Lambda::const_(Constant::int(4)),
            Lambda::prim(
                Primitive::Pmakeblock(
                    0,
                    TagInfo::ModuleExport(vec![first.clone(), second.clone()]),
                    Mutable::Immutable,
                ),
                vec![Lambda::var(first.clone()), Lambda::var(second.clone())],
                Location::none(),
            ),
        ),
    );

    let deps = compiler.compile_deps_program(&lam);

    let [first_export, second_export] = deps.program.exports.as_slice() else {
        panic!("expected two exports");
    };
    assert!(first_export.same(&first));
    assert!(second_export.same(&second));

    let [first_stmt, second_stmt] = deps.program.block.as_slice() else {
        panic!("expected the retained bindings to stay in the OCaml shake order");
    };

    match &first_stmt.desc {
        StatementDesc::Variable(VariableDeclaration {
            ident,
            value:
                Some(Expression {
                    desc: ExpressionDesc::Number(Number::Int { i: 3, .. }),
                    ..
                }),
            ..
        }) => assert!(ident.same(&first)),
        other => panic!("expected the earlier retained binding first, got {other:?}"),
    }

    match &second_stmt.desc {
        StatementDesc::Variable(VariableDeclaration {
            ident,
            value:
                Some(Expression {
                    desc: ExpressionDesc::Number(Number::Int { i: 4, .. }),
                    ..
                }),
            ..
        }) => assert!(ident.same(&second)),
        other => panic!("expected the later retained binding second, got {other:?}"),
    }
}

#[test]
fn compile_deps_program_keeps_exported_constant_binding_before_exported_alias_of_same_constant_like_test_small()
 {
    let mut compiler = LambdaCompiler::new();
    let fib = Ident::create_local("fib");
    let u = Ident::create_local("u");
    let lam = Lambda::let_(
        LetKind::Strict,
        fib.clone(),
        Lambda::const_(Constant::int(3)),
        Lambda::let_(
            LetKind::Strict,
            u.clone(),
            Lambda::var(fib.clone()),
            Lambda::prim(
                Primitive::Pmakeblock(
                    0,
                    TagInfo::ModuleExport(vec![fib.clone(), u.clone()]),
                    Mutable::Immutable,
                ),
                vec![Lambda::var(fib.clone()), Lambda::var(u.clone())],
                Location::none(),
            ),
        ),
    );

    let deps = compiler.compile_deps_program(&lam);

    let rendered = print_deps_program(&deps, None);

    let [first_export, second_export] = deps.program.exports.as_slice() else {
        panic!("expected two exports");
    };
    assert!(
        first_export.same(&fib),
        "expected fib to remain the first export, exports={:?}\n{rendered}",
        deps.program.exports
    );
    assert!(
        second_export.same(&u),
        "expected u to remain the second export, exports={:?}\n{rendered}",
        deps.program.exports
    );

    let [first_stmt, second_stmt] = deps.program.block.as_slice() else {
        panic!("expected the preserved constant binding plus its exported alias");
    };

    match &first_stmt.desc {
        StatementDesc::Variable(VariableDeclaration {
            ident,
            value:
                Some(Expression {
                    desc: ExpressionDesc::Number(Number::Int { i: 3, .. }),
                    ..
                }),
            ..
        }) => assert!(ident.same(&fib)),
        other => panic!("expected fib = 3 to remain first, got {other:?}\n{rendered}"),
    }

    match &second_stmt.desc {
        StatementDesc::Variable(VariableDeclaration {
            ident,
            value:
                Some(Expression {
                    desc: ExpressionDesc::Number(Number::Int { i: 3, .. }),
                    ..
                }),
            ..
        }) => assert!(ident.same(&u)),
        other => panic!("expected u = 3 to remain second, got {other:?}\n{rendered}"),
    }
}

#[test]
fn compile_deps_program_keeps_exported_call_result_before_rebound_constant_block_export() {
    let mut compiler = LambdaCompiler::new();
    let f = Ident::create_local("f");
    let v = Ident::create_local("v");
    let res = Ident::create_local("res");
    let param = Ident::create_local("v");
    let export_block = Lambda::prim(
        Primitive::Pmakeblock(
            0,
            TagInfo::ModuleExport(vec![v.clone(), res.clone()]),
            Mutable::Immutable,
        ),
        vec![Lambda::var(v.clone()), Lambda::var(res.clone())],
        Location::none(),
    );
    let lam = Lambda::let_(
        LetKind::Strict,
        f.clone(),
        Lambda::prim(
            Primitive::PjsFnMake(1),
            vec![Lambda::function_(
                1,
                vec![param.clone()],
                Lambda::prim(
                    Primitive::Pfield(
                        0,
                        crate::lambda::compat::FieldDbgInfo::Record {
                            name: "x".to_string(),
                            mutable_flag: crate::parser::ast::MutableFlag::Immutable,
                        },
                    ),
                    vec![Lambda::var(param)],
                    Location::none(),
                ),
                FunctionAttribute::default(),
            )],
            Location::none(),
        ),
        Lambda::let_(
            LetKind::Strict,
            v.clone(),
            Lambda::const_(Constant::Block {
                tag: 0,
                tag_info: TagInfo::record(
                    vec![
                        ("x".to_string(), false),
                        ("y".to_string(), false),
                        ("z".to_string(), false),
                    ],
                    crate::parser::ast::MutableFlag::Immutable,
                ),
                elements: vec![
                    Constant::int(3),
                    Constant::int(4),
                    Constant::JsUndefined { is_unit: false },
                ],
            }),
            Lambda::let_(
                LetKind::Strict,
                res.clone(),
                Lambda::Lapply(Apply {
                    ap_func: Box::new(Lambda::var(f)),
                    ap_args: vec![Lambda::var(v.clone())],
                    ap_info: ApInfo {
                        loc: Location::none(),
                        inlined: InlineAttribute::Default,
                        status: ApplyStatus::Uncurry,
                    },
                    ap_transformed_jsx: false,
                }),
                export_block,
            ),
        ),
    );

    let deps = compiler.compile_deps_program(&lam);
    let rendered = print_deps_program(&deps, None);
    let res_idx = rendered
        .find("let res = 3;")
        .expect("expected the reduced exported call result binding");
    let v_idx = rendered
        .find("let v = {\n  x: 3,")
        .expect("expected the rebound constant-block export binding");
    assert!(
        res_idx < v_idx,
        "expected the preserved exported call result before the rebound block export:\n{rendered}"
    );
}

#[test]
fn compile_deps_program_rebinds_different_name_exports_after_effects() {
    let mut compiler = LambdaCompiler::new();
    let original_export = Ident::create_local("MyURL");
    let export_block = Lambda::prim(
        Primitive::Pmakeblock(
            0,
            TagInfo::ModuleExport(vec![original_export.clone()]),
            Mutable::Immutable,
        ),
        vec![Lambda::unit()],
        Location::none(),
    );
    let lam = Lambda::let_(
        LetKind::Alias,
        original_export.clone(),
        Lambda::unit(),
        Lambda::seq(
            Lambda::prim(Primitive::Pdebugger, vec![], Location::none()),
            export_block,
        ),
    );

    let deps = compiler.compile_deps_program(&lam);

    let [exported] = deps.program.exports.as_slice() else {
        panic!("expected a single export");
    };
    assert_eq!(exported.name(), "MyURL");
    assert!(
        !exported.same(&original_export),
        "expected export coercion to rename the trailing export binding"
    );

    let [debugger, rebound] = deps.program.block.as_slice() else {
        panic!(
            "expected the original placeholder to shake away and the rebound export to remain"
        );
    };
    assert!(matches!(debugger.desc, StatementDesc::Debugger));
    match &rebound.desc {
        StatementDesc::Variable(VariableDeclaration {
            ident,
            value:
                Some(Expression {
                    desc: ExpressionDesc::Undefined { is_unit: true },
                    ..
                }),
            ..
        }) => assert!(ident.same(exported)),
        other => panic!("expected trailing undefined export placeholder, got {other:?}"),
    }
}

#[test]
fn compile_deps_program_rebinds_exported_constants_after_surviving_function_bindings() {
    let mut compiler = LambdaCompiler::new();
    let x = Ident::create_local("x");
    let xx = Ident::create_local("xx");
    let foo = Ident::create_local("foo");
    let param = Ident::create_local("x");
    let export_block = Lambda::prim(
        Primitive::Pmakeblock(
            0,
            TagInfo::ModuleExport(vec![x.clone(), xx.clone(), foo.clone()]),
            Mutable::Immutable,
        ),
        vec![
            Lambda::var(x.clone()),
            Lambda::var(xx.clone()),
            Lambda::var(foo.clone()),
        ],
        Location::none(),
    );
    let lam = Lambda::let_(
        LetKind::Strict,
        x.clone(),
        Lambda::const_(Constant::int(1)),
        Lambda::let_(
            LetKind::Strict,
            xx.clone(),
            Lambda::var(x),
            Lambda::let_(
                LetKind::Strict,
                foo.clone(),
                Lambda::prim(
                    Primitive::PjsFnMake(1),
                    vec![Lambda::function_(
                        1,
                        vec![param.clone()],
                        Lambda::var(param),
                        FunctionAttribute::default(),
                    )],
                    Location::none(),
                ),
                export_block,
            ),
        ),
    );

    let deps = compiler.compile_deps_program(&lam);

    assert_eq!(
        deps.program
            .exports
            .iter()
            .map(|ident| ident.name())
            .collect::<Vec<_>>(),
        vec!["x", "xx", "foo"]
    );

    let [first, second, third] = deps.program.block.as_slice() else {
        panic!("expected function binding followed by two rebound constant exports");
    };
    match &first.desc {
        StatementDesc::Variable(VariableDeclaration {
            ident,
            value:
                Some(Expression {
                    desc: ExpressionDesc::Fun { .. },
                    ..
                }),
            ..
        }) => assert!(ident.same(&foo)),
        other => panic!("expected the surviving function binding first, got {other:?}"),
    }
    match &second.desc {
        StatementDesc::Variable(VariableDeclaration { ident, .. }) => {
            assert_eq!(ident.name(), "x");
        }
        other => panic!("expected the rebound x export second, got {other:?}"),
    }
    match &third.desc {
        StatementDesc::Variable(VariableDeclaration { ident, .. }) => {
            assert_eq!(ident.name(), "xx");
        }
        other => panic!("expected the rebound xx export third, got {other:?}"),
    }

    let rendered = print_deps_program(&deps, None);
    let foo_idx = rendered.find("function foo").unwrap();
    let x_idx = rendered.find("let x = 1;").unwrap();
    let xx_idx = rendered.find("let xx = 1;").unwrap();
    assert!(foo_idx < x_idx);
    assert!(x_idx < xx_idx);
}

#[test]
fn compile_deps_program_rebinds_marshaled_string_exports_after_surviving_function_bindings() {
    let mut compiler = LambdaCompiler::new();
    let foo = Ident::create_local("foo");
    let s = Ident::create_local("s");
    let bar = Ident::create_local("bar");
    let foo_param = Ident::create_local("x");
    let bar_param = Ident::create_local("x");
    let export_block = Lambda::prim(
        Primitive::Pmakeblock(
            0,
            TagInfo::ModuleExport(vec![foo.clone(), s.clone(), bar.clone()]),
            Mutable::Immutable,
        ),
        vec![
            Lambda::var(foo.clone()),
            Lambda::var(s.clone()),
            Lambda::var(bar.clone()),
        ],
        Location::none(),
    );
    let lam = Lambda::let_(
        LetKind::Strict,
        foo.clone(),
        Lambda::prim(
            Primitive::PjsFnMake(1),
            vec![Lambda::function_(
                1,
                vec![foo_param.clone()],
                Lambda::var(foo_param),
                FunctionAttribute::default(),
            )],
            Location::none(),
        ),
        Lambda::let_(
            LetKind::Strict,
            s.clone(),
            Lambda::const_(Constant::String {
                s: "😀".to_string(),
                delim: Some(StringDelim::StarJ),
            }),
            Lambda::let_(
                LetKind::Strict,
                bar.clone(),
                Lambda::prim(
                    Primitive::PjsFnMake(1),
                    vec![Lambda::function_(
                        1,
                        vec![bar_param.clone()],
                        Lambda::var(bar_param),
                        FunctionAttribute::default(),
                    )],
                    Location::none(),
                ),
                export_block,
            ),
        ),
    );

    let deps = compiler.compile_deps_program(&lam);

    assert_eq!(
        deps.program
            .exports
            .iter()
            .map(|ident| ident.name())
            .collect::<Vec<_>>(),
        vec!["foo", "s", "bar"]
    );

    let rendered = print_deps_program(&deps, None);
    let foo_idx = rendered.find("function foo").unwrap();
    let bar_idx = rendered.find("function bar").unwrap();
    let s_idx = rendered.find("let s = \"😀\";").unwrap();
    assert!(foo_idx < bar_idx);
    assert!(bar_idx < s_idx);
}

#[test]
fn compile_deps_program_keeps_same_name_export_aliases_for_unbound_globals() {
    let mut compiler = LambdaCompiler::new();
    let global = Ident::create_persistent("parseInt");
    let rebound_export = Ident::create_local("parseInt");
    let lam = Lambda::let_(
        LetKind::Alias,
        rebound_export.clone(),
        Lambda::var(global.clone()),
        Lambda::prim(
            Primitive::Pmakeblock(
                0,
                TagInfo::ModuleExport(vec![rebound_export.clone()]),
                Mutable::Immutable,
            ),
            vec![Lambda::var(rebound_export.clone())],
            Location::none(),
        ),
    );

    let deps = compiler.compile_deps_program(&lam);

    let [exported] = deps.program.exports.as_slice() else {
        panic!("expected a single export");
    };
    assert_eq!(exported.name(), rebound_export.name());

    let [stmt] = deps.program.block.as_slice() else {
        panic!("expected the rebound alias to stay as a real binding");
    };
    match &stmt.desc {
        StatementDesc::Variable(VariableDeclaration {
            ident,
            value:
                Some(Expression {
                    desc: ExpressionDesc::Var(VIdent::Id(target)),
                    ..
                }),
            ..
        }) => {
            assert_eq!(ident.name(), rebound_export.name());
            assert!(target.same(&global));
        }
        other => panic!("expected the rebound export binding to remain, got {other:?}"),
    }
}

#[test]
fn coerce_and_resolve_keep_declared_same_name_export_aliases() {
    let mut compiler = LambdaCompiler::new();
    let target = Ident::create_local("broken");
    let exported = Ident::create_local("broken");
    let mut block = vec![
        Statement::variable(VariableDeclaration {
            ident: target.clone(),
            value: Some(Expression::number(Number::int(1))),
            property: LetKind::Strict,
            ident_info: IdentInfo::default(),
        }),
        Statement::variable(VariableDeclaration {
            ident: exported.clone(),
            value: Some(Expression::var(target.clone())),
            property: LetKind::Alias,
            ident_info: IdentInfo::default(),
        }),
    ];

    let exports = compiler.coerce_toplevel_exports(
        &mut block,
        ExtractedExports {
            exports: vec![exported.clone()],
            values: vec![Expression::var(target.clone())],
        },
    );
    let exports = resolve_export_aliases(&block, exports);

    assert_eq!(exports, vec![exported.clone()]);

    let [first, second] = block.as_slice() else {
        panic!("expected the original target and alias bindings to remain");
    };
    match &first.desc {
        StatementDesc::Variable(VariableDeclaration { ident, .. }) => {
            assert!(ident.same(&target));
        }
        other => panic!("expected the original target binding first, got {other:?}"),
    }
    match &second.desc {
        StatementDesc::Variable(VariableDeclaration { ident, .. }) => {
            assert!(ident.same(&exported));
        }
        other => panic!("expected the exported alias binding second, got {other:?}"),
    }
}

#[test]
fn coerce_and_resolve_keep_declared_same_name_function_export_aliases_with_multiple_materialized_roots(
) {
    let mut compiler = LambdaCompiler::new();
    let source_level_broken = Ident::create_local("broken");
    let target = Ident::create_local("broken");
    let exported = Ident::create_local("broken");
    let do_something_async = Ident::create_local("doSomethingAsync");
    let param = Ident::create_local("param");
    let mut block = vec![
        Statement::variable(VariableDeclaration {
            ident: source_level_broken.clone(),
            value: Some(Expression::var(do_something_async.clone())),
            property: LetKind::Alias,
            ident_info: IdentInfo::default(),
        }),
        Statement::variable(VariableDeclaration {
            ident: target.clone(),
            value: Some(Expression::new(ExpressionDesc::Fun {
                is_method: false,
                params: vec![param],
                body: vec![Statement::return_(Expression::undefined(false))],
                env: Default::default(),
                return_unit: false,
                async_: true,
                directive: None,
            })),
            property: LetKind::Strict,
            ident_info: IdentInfo::default(),
        }),
        Statement::variable(VariableDeclaration {
            ident: exported.clone(),
            value: Some(Expression::var(target.clone())),
            property: LetKind::Alias,
            ident_info: IdentInfo::default(),
        }),
    ];

    let exports = compiler.coerce_toplevel_exports(
        &mut block,
        ExtractedExports {
            exports: vec![exported.clone()],
            values: vec![Expression::var(target.clone())],
        },
    );
    let exports = resolve_export_aliases(&block, exports);

    assert_eq!(exports, vec![exported.clone()]);
    let [first, second, third] = block.as_slice() else {
        panic!("expected the earlier same-name binding, async target, and alias bindings to remain");
    };
    match &first.desc {
        StatementDesc::Variable(VariableDeclaration {
            ident,
            value:
                Some(Expression {
                    desc: ExpressionDesc::Var(VIdent::Id(alias_target)),
                    ..
                }),
            property,
            ..
        }) => {
            assert!(ident.same(&source_level_broken));
            assert!(alias_target.same(&do_something_async));
            assert_eq!(*property, LetKind::Alias);
        }
        other => panic!(
            "expected the earlier source-level same-name binding first, got {other:?}"
        ),
    };
    match &second.desc {
        StatementDesc::Variable(VariableDeclaration {
            ident,
            value:
                Some(Expression {
                    desc: ExpressionDesc::Fun { async_, .. },
                    ..
                }),
            ..
        }) => {
            assert!(ident.same(&target));
            assert!(*async_);
        }
        other => panic!("expected the original async function binding first, got {other:?}"),
    }
    match &third.desc {
        StatementDesc::Variable(VariableDeclaration {
            ident,
            value:
                Some(Expression {
                    desc: ExpressionDesc::Var(VIdent::Id(alias_target)),
                    ..
                }),
            property,
            ..
        }) => {
            assert!(ident.same(&exported));
            assert!(alias_target.same(&target));
            assert_eq!(*property, LetKind::Alias);
        }
        other => panic!("expected the exported async alias binding second, got {other:?}"),
    }
}

#[test]
fn coerce_toplevel_exports_reuses_existing_same_name_alias_binding_for_matching_var_value() {
    let mut compiler = LambdaCompiler::new();
    let target = Ident::create_persistent("tToJs");
    let declared_alias = Ident::create_local("v");
    let exported = Ident::create_local("v");
    let mut block = vec![Statement::variable(VariableDeclaration {
        ident: declared_alias.clone(),
        value: Some(Expression::var(target.clone())),
        property: LetKind::Alias,
        ident_info: IdentInfo::default(),
    })];

    let exports = compiler.coerce_toplevel_exports(
        &mut block,
        ExtractedExports {
            exports: vec![exported],
            values: vec![Expression::var(target)],
        },
    );
    let exports = resolve_export_aliases(&block, exports);

    assert_eq!(exports, vec![declared_alias.clone()]);
    let [stmt] = block.as_slice() else {
        panic!("expected the existing same-name alias binding to be reused");
    };
    match &stmt.desc {
        StatementDesc::Variable(VariableDeclaration { ident, .. }) => {
            assert!(ident.same(&declared_alias));
        }
        other => panic!("expected the original same-name alias binding, got {other:?}"),
    }
}

#[test]
fn coerce_toplevel_exports_reuses_existing_same_name_alias_binding_for_matching_module_field() {
    let mut compiler = LambdaCompiler::new();
    let set_gen = ModuleId {
        id: Ident::create_persistent("Set_gen"),
        kind: Kind::Ml,
        dynamic_import: false,
    };
    let declared_alias = Ident::create_local("empty");
    let exported = Ident::create_local("empty");
    let mut block = vec![Statement::variable(VariableDeclaration {
        ident: declared_alias.clone(),
        value: Some(Expression::qualified(
            set_gen.clone(),
            Some("empty".to_string()),
        )),
        property: LetKind::Alias,
        ident_info: IdentInfo::default(),
    })];

    let exports = compiler.coerce_toplevel_exports(
        &mut block,
        ExtractedExports {
            exports: vec![exported],
            values: vec![Expression::qualified(set_gen, Some("empty".to_string()))],
        },
    );
    let exports = resolve_export_aliases(&block, exports);

    assert_eq!(exports, vec![declared_alias.clone()]);
    let [stmt] = block.as_slice() else {
        panic!("expected the existing same-name module field alias to be reused");
    };
    match &stmt.desc {
        StatementDesc::Variable(VariableDeclaration { ident, .. }) => {
            assert!(ident.same(&declared_alias));
        }
        other => panic!("expected the original same-name alias binding, got {other:?}"),
    }
}

#[test]
fn coerce_toplevel_exports_keeps_same_name_function_alias_binding_before_later_effect_when_reused(
) {
    let mut compiler = LambdaCompiler::new();
    let target = Ident::create_local("tToJs");
    let declared_alias = Ident::create_local("v");
    let exported = Ident::create_local("v");
    let param = Ident::create_local("param");
    let mut block = vec![
        Statement::variable(VariableDeclaration {
            ident: target.clone(),
            value: Some(Expression::new(ExpressionDesc::Fun {
                is_method: false,
                params: vec![param],
                body: vec![Statement::return_(Expression::undefined(false))],
                env: Default::default(),
                return_unit: false,
                async_: false,
                directive: None,
            })),
            property: LetKind::Strict,
            ident_info: IdentInfo::default(),
        }),
        Statement::variable(VariableDeclaration {
            ident: declared_alias.clone(),
            value: Some(Expression::var(target.clone())),
            property: LetKind::Alias,
            ident_info: IdentInfo::default(),
        }),
        Statement::exp(Expression::call(
            Expression::var(declared_alias.clone()),
            vec![Expression::string("a")],
            CallInfo::default(),
        )),
    ];

    let exports = compiler.coerce_toplevel_exports(
        &mut block,
        ExtractedExports {
            exports: vec![exported.clone()],
            values: vec![Expression::var(declared_alias.clone())],
        },
    );
    let exports = resolve_export_aliases(&block, exports);

    assert_eq!(exports, vec![declared_alias.clone()]);
    let [first, second, third] = block.as_slice() else {
        panic!("expected the function binding, preserved alias, and later top-level effect");
    };
    match &first.desc {
        StatementDesc::Variable(VariableDeclaration {
            ident,
            value:
                Some(Expression {
                    desc: ExpressionDesc::Fun { .. },
                    ..
                }),
            ..
        }) => {
            assert!(ident.same(&target));
        }
        other => panic!("expected the function binding to remain first, got {other:?}"),
    };
    match &second.desc {
        StatementDesc::Variable(VariableDeclaration {
            ident,
            value:
                Some(Expression {
                    desc: ExpressionDesc::Var(VIdent::Id(rebound_target)),
                    ..
                }),
            property,
            ..
        }) => {
            assert!(ident.same(&declared_alias));
            assert!(rebound_target.same(&target));
            assert_eq!(*property, LetKind::Alias);
        }
        other => panic!("expected the preserved alias binding second, got {other:?}"),
    }
    match &third.desc {
        StatementDesc::Exp(Expression {
            desc: ExpressionDesc::Call(func, args, _),
            ..
        }) => {
            let [arg] = args.as_slice() else {
                panic!("expected the later top-level call to keep a single argument");
            };
            match &arg.desc {
                ExpressionDesc::Str { txt, .. } => assert_eq!(txt, "a"),
                other => panic!(
                    "expected the later top-level call argument to stay as \"a\", got {other:?}"
                ),
            }
            match &func.desc {
                ExpressionDesc::Var(VIdent::Id(ident)) => assert!(ident.same(&declared_alias)),
                other => panic!(
                    "expected the later top-level call to keep using the preserved alias, got {other:?}"
                ),
            }
        }
        other => panic!("expected the later top-level call third, got {other:?}"),
    }
}

#[test]
fn coerce_toplevel_exports_keeps_same_name_function_alias_chain_before_later_effect()
{
    let mut compiler = LambdaCompiler::new();
    let target = Ident::create_local("tToJs");
    let renamed_same_name = Ident::create_local("tToJs");
    let declared_alias = Ident::create_local("v");
    let exported = Ident::create_local("v");
    let param = Ident::create_local("param");
    let mut block = vec![
        Statement::variable(VariableDeclaration {
            ident: target.clone(),
            value: Some(Expression::new(ExpressionDesc::Fun {
                is_method: false,
                params: vec![param],
                body: vec![Statement::return_(Expression::undefined(false))],
                env: Default::default(),
                return_unit: false,
                async_: false,
                directive: None,
            })),
            property: LetKind::Strict,
            ident_info: IdentInfo::default(),
        }),
        Statement::variable(VariableDeclaration {
            ident: renamed_same_name.clone(),
            value: Some(Expression::var(target.clone())),
            property: LetKind::Alias,
            ident_info: IdentInfo::default(),
        }),
        Statement::variable(VariableDeclaration {
            ident: declared_alias.clone(),
            value: Some(Expression::var(renamed_same_name)),
            property: LetKind::Alias,
            ident_info: IdentInfo::default(),
        }),
        Statement::exp(Expression::call(
            Expression::var(declared_alias.clone()),
            vec![Expression::string("a")],
            CallInfo::default(),
        )),
    ];

    let exports = compiler.coerce_toplevel_exports(
        &mut block,
        ExtractedExports {
            exports: vec![exported.clone()],
            values: vec![Expression::var(declared_alias.clone())],
        },
    );
    let exports = resolve_export_aliases(&block, exports);

    assert_eq!(exports, vec![declared_alias.clone()]);
    let [first, second, third, fourth] = block.as_slice() else {
        panic!(
            "expected the original function, renamed alias chain, preserved same-name alias, and later top-level effect"
        );
    };
    match &first.desc {
        StatementDesc::Variable(VariableDeclaration {
            ident,
            value:
                Some(Expression {
                    desc: ExpressionDesc::Fun { .. },
                    ..
                }),
            ..
        }) => assert!(ident.same(&target)),
        other => panic!("expected the underlying function binding first, got {other:?}"),
    }
    match &second.desc {
        StatementDesc::Variable(VariableDeclaration {
            ident,
            value:
                Some(Expression {
                    desc: ExpressionDesc::Var(VIdent::Id(rebound_target)),
                    ..
                }),
            ..
        }) => {
            assert!(ident.name() == target.name());
            assert!(rebound_target.same(&target));
        }
        other => panic!("expected the renamed same-name alias second, got {other:?}"),
    }
    match &third.desc {
        StatementDesc::Variable(VariableDeclaration {
            ident,
            value:
                Some(Expression {
                    desc: ExpressionDesc::Var(VIdent::Id(rebound_target)),
                    ..
                }),
            property,
            ..
        }) => {
            assert!(ident.same(&declared_alias));
            assert!(rebound_target.name() == target.name());
            assert_eq!(*property, LetKind::Alias);
        }
        other => panic!("expected the preserved same-name alias third, got {other:?}"),
    }
    match &fourth.desc {
        StatementDesc::Exp(Expression {
            desc: ExpressionDesc::Call(func, args, _),
            ..
        }) => {
            let [arg] = args.as_slice() else {
                panic!("expected the later top-level call to keep one argument");
            };
            match &arg.desc {
                ExpressionDesc::Str { txt, .. } => assert_eq!(txt, "a"),
                other => panic!(
                    "expected the later top-level call arg to stay as \"a\", got {other:?}"
                ),
            }
            match &func.desc {
                ExpressionDesc::Var(VIdent::Id(ident)) => {
                    assert!(ident.same(&declared_alias))
                }
                other => panic!(
                    "expected the later top-level call to keep using the preserved alias chain, got {other:?}"
                ),
            }
        }
        other => panic!("expected the later top-level call fourth, got {other:?}"),
    }
}

#[test]
fn coerce_toplevel_exports_moves_same_name_recursive_function_alias_to_tail_without_remaining_use(
) {
    let mut compiler = LambdaCompiler::new();
    let fib = Ident::create_local("fib");
    let exported = Ident::create_local("b");
    let n = Ident::create_local("n");
    let sink = Ident::create_persistent("sink");
    let mut block = vec![
        Statement::variable(VariableDeclaration {
            ident: fib.clone(),
            value: Some(Expression::new(ExpressionDesc::Fun {
                is_method: false,
                params: vec![n.clone()],
                body: vec![Statement::return_(Expression::call(
                    Expression::var(fib.clone()),
                    vec![Expression::var(n)],
                    CallInfo::default(),
                ))],
                env: Default::default(),
                return_unit: false,
                async_: false,
                directive: None,
            })),
            property: LetKind::Strict,
            ident_info: IdentInfo::default(),
        }),
        Statement::variable(VariableDeclaration {
            ident: exported.clone(),
            value: Some(Expression::var(fib.clone())),
            property: LetKind::Alias,
            ident_info: IdentInfo::default(),
        }),
        Statement::exp(Expression::call(
            Expression::var(sink.clone()),
            vec![],
            CallInfo::default(),
        )),
    ];

    let exports = compiler.coerce_toplevel_exports(
        &mut block,
        ExtractedExports {
            exports: vec![exported.clone()],
            values: vec![Expression::var(fib.clone())],
        },
    );
    let exports = resolve_export_aliases(&block, exports);

    assert_eq!(exports.len(), 1);
    assert_eq!(exports[0].name(), exported.name());
    let [first, second, third] = block.as_slice() else {
        panic!("expected the recursive function, later effect, and late export alias");
    };
    match &first.desc {
        StatementDesc::Variable(VariableDeclaration {
            ident,
            value:
                Some(Expression {
                    desc: ExpressionDesc::Fun { .. },
                    ..
                }),
            ..
        }) => assert!(ident.same(&fib)),
        other => panic!("expected the recursive function binding first, got {other:?}"),
    }
    match &second.desc {
        StatementDesc::Exp(Expression {
            desc: ExpressionDesc::Call(func, args, _),
            ..
        }) => {
            assert!(args.is_empty());
            match &func.desc {
                ExpressionDesc::Var(VIdent::Id(ident)) => assert!(ident.same(&sink)),
                other => panic!("expected the later effect call second, got {other:?}"),
            }
        }
        other => panic!("expected the later effect second, got {other:?}"),
    }
    match &third.desc {
        StatementDesc::Variable(VariableDeclaration {
            ident,
            value:
                Some(Expression {
                    desc: ExpressionDesc::Var(VIdent::Id(target)),
                    ..
                }),
            property,
            ..
        }) => {
            assert!(ident.same(&exported));
            assert!(target.same(&fib));
            assert_eq!(*property, LetKind::Alias);
        }
        other => panic!("expected the late recursive export alias third, got {other:?}"),
    }
}

#[test]
fn later_toplevel_effect_blocks_tail_move_for_non_recursive_function_without_remaining_use() {
    let target = Ident::create_local("abc_u");
    let replacement = Expression::var(Ident::create_local("abc"));
    let sink = Ident::create_persistent("sink");
    let remaining = vec![
        Statement::exp(Expression::call(
            Expression::var(sink.clone()),
            vec![],
            CallInfo::default(),
        )),
    ];

    assert!(!later_toplevel_effect_allows_tail_move(
        &remaining,
        &target,
        TailMoveInitializerKind::Function,
        &replacement,
        false,
    ));
}

#[test]
fn resolve_export_aliases_prefers_underlying_declared_same_name_target_over_self_alias() {
    let target = Ident::create_local("tToJs");
    let exported = Ident::create_local("tToJs");
    let param = Ident::create_local("param");
    let block = vec![
        Statement::variable(VariableDeclaration {
            ident: target.clone(),
            value: Some(Expression::new(ExpressionDesc::Fun {
                is_method: false,
                params: vec![param],
                body: vec![Statement::return_(Expression::undefined(false))],
                env: Default::default(),
                return_unit: false,
                async_: false,
                directive: None,
            })),
            property: LetKind::Strict,
            ident_info: IdentInfo::default(),
        }),
        Statement::variable(VariableDeclaration {
            ident: exported.clone(),
            value: Some(Expression::var(target.clone())),
            property: LetKind::Alias,
            ident_info: IdentInfo::default(),
        }),
    ];

    assert_eq!(resolve_export_aliases(&block, vec![exported]), vec![target]);
}

#[test]
fn coerce_toplevel_exports_moves_same_name_export_strict_module_field_binding_to_tail_when_reused(
) {
    let mut compiler = LambdaCompiler::new();
    let set_gen = ModuleId {
        id: Ident::create_persistent("Set_gen"),
        kind: Kind::Ml,
        dynamic_import: false,
    };
    let declared_alias = Ident::create_local("empty");
    let exported = Ident::create_local("empty");
    let mut block = vec![
        Statement::variable(VariableDeclaration {
            ident: declared_alias.clone(),
            value: Some(Expression::qualified(
                set_gen.clone(),
                Some("empty".to_string()),
            )),
            property: LetKind::Strict,
            ident_info: IdentInfo::default(),
        }),
        Statement::exp(Expression::call(
            Expression::var(declared_alias.clone()),
            vec![],
            CallInfo::default(),
        )),
    ];

    let exports = compiler.coerce_toplevel_exports(
        &mut block,
        ExtractedExports {
            exports: vec![exported.clone()],
            values: vec![Expression::var(declared_alias)],
        },
    );
    let exports = resolve_export_aliases(&block, exports);

    assert_eq!(exports, vec![exported.clone()]);
    let [first, second] = block.as_slice() else {
        panic!("expected the internal use plus the late export binding");
    };
    match &first.desc {
        StatementDesc::Exp(Expression {
            desc: ExpressionDesc::Call(func, args, _),
            ..
        }) => {
            assert!(args.is_empty());
            match &func.desc {
                ExpressionDesc::Var(VIdent::Qualified(module, Some(field))) => {
                    assert_eq!(module.id.name(), "Set_gen");
                    assert_eq!(field, "empty");
                }
                other => panic!(
                    "expected the internal call to use the underlying module field directly, got {other:?}"
                ),
            }
        }
        other => panic!("expected the internal call to remain first, got {other:?}"),
    }
    match &second.desc {
        StatementDesc::Variable(VariableDeclaration {
            ident,
            value:
                Some(Expression {
                    desc: ExpressionDesc::Var(VIdent::Qualified(module, Some(field))),
                    ..
                }),
            property,
            ..
        }) => {
            assert!(ident.same(&exported));
            assert_eq!(module.id.name(), "Set_gen");
            assert_eq!(field, "empty");
            assert_eq!(*property, LetKind::Strict);
        }
        other => panic!("expected the late export binding second, got {other:?}"),
    }
}

#[test]
fn coerce_toplevel_exports_moves_same_name_literal_binding_to_tail_when_reused() {
    let mut compiler = LambdaCompiler::new();
    let declared = Ident::create_local("noParam");
    let exported = Ident::create_local("noParam");
    let compose = Ident::create_local("compose");
    let a = Ident::create_local("a");
    let accessor = Ident::create_local("accessor");
    let mut block = vec![
        Statement::variable(VariableDeclaration {
            ident: declared.clone(),
            value: Some(Expression::string("NoParam")),
            property: LetKind::Alias,
            ident_info: IdentInfo::default(),
        }),
        Statement::variable(VariableDeclaration {
            ident: compose.clone(),
            value: Some(Expression::new(ExpressionDesc::Fun {
                is_method: false,
                params: vec![a.clone(), accessor.clone()],
                body: vec![Statement::return_(Expression::call(
                    Expression::var(accessor),
                    vec![Expression::var(a)],
                    CallInfo::default(),
                ))],
                env: Default::default(),
                return_unit: false,
                async_: false,
                directive: None,
            })),
            property: LetKind::Strict,
            ident_info: IdentInfo::default(),
        }),
    ];

    let exports = compiler.coerce_toplevel_exports(
        &mut block,
        ExtractedExports {
            exports: vec![exported.clone()],
            values: vec![Expression::var(declared.clone())],
        },
    );
    let exports = resolve_export_aliases(&block, exports);

    assert_eq!(exports.len(), 1);
    assert_eq!(exports[0].name(), exported.name());
    let [first, second] = block.as_slice() else {
        panic!("expected the surviving function binding plus the late literal export");
    };
    match &first.desc {
        StatementDesc::Variable(VariableDeclaration {
            ident,
            value:
                Some(Expression {
                    desc: ExpressionDesc::Fun { .. },
                    ..
                }),
            ..
        }) => assert!(ident.same(&compose)),
        other => panic!("expected the function binding first, got {other:?}"),
    }
    match &second.desc {
        StatementDesc::Variable(VariableDeclaration {
            ident,
            value:
                Some(Expression {
                    desc: ExpressionDesc::Str { txt, .. },
                    ..
                }),
            property,
            ..
        }) => {
            assert!(ident.same(&exported));
            assert_eq!(txt, "NoParam");
            assert_eq!(*property, LetKind::Alias);
        }
        other => panic!("expected the late literal export binding second, got {other:?}"),
    }
}

#[test]
fn coerce_toplevel_exports_keeps_same_name_literal_binding_used_by_later_function_body() {
    let mut compiler = LambdaCompiler::new();
    let exported = Ident::create_local("bla2");
    let concat = Ident::create_local("concat");
    let mut block = vec![
        Statement::variable(VariableDeclaration {
            ident: exported.clone(),
            value: Some(Expression::string("")),
            property: LetKind::Alias,
            ident_info: IdentInfo::default(),
        }),
        Statement::variable(VariableDeclaration {
            ident: concat.clone(),
            value: Some(Expression::new(ExpressionDesc::Fun {
                is_method: false,
                params: vec![],
                body: vec![Statement::return_(Expression::var(exported.clone()))],
                env: Default::default(),
                return_unit: false,
                async_: false,
                directive: None,
            })),
            property: LetKind::Strict,
            ident_info: IdentInfo::default(),
        }),
    ];

    let exports = compiler.coerce_toplevel_exports(
        &mut block,
        ExtractedExports {
            exports: vec![exported.clone()],
            values: vec![Expression::var(exported.clone())],
        },
    );
    let exports = resolve_export_aliases(&block, exports);

    assert_eq!(exports, vec![exported.clone()]);
    let [first, second] = block.as_slice() else {
        panic!("expected the literal export plus the later function binding");
    };
    match &first.desc {
        StatementDesc::Variable(VariableDeclaration {
            ident,
            value:
                Some(Expression {
                    desc: ExpressionDesc::Str { txt, .. },
                    ..
                }),
            property,
            ..
        }) => {
            assert!(ident.same(&exported));
            assert_eq!(txt, "");
            assert_eq!(*property, LetKind::Alias);
        }
        other => panic!("expected the exported literal binding first, got {other:?}"),
    }
    match &second.desc {
        StatementDesc::Variable(VariableDeclaration {
            ident,
            value:
                Some(Expression {
                    desc: ExpressionDesc::Fun { body, .. },
                    ..
                }),
            ..
        }) => {
            assert!(ident.same(&concat));
            let [Statement {
                desc:
                    StatementDesc::Return(Expression {
                        desc: ExpressionDesc::Var(VIdent::Id(target)),
                        ..
                    }),
                ..
            }] = body.as_slice()
            else {
                panic!("expected the later function body to return the shared binding");
            };
            assert!(target.same(&exported));
        }
        other => panic!("expected the later function binding second, got {other:?}"),
    }
}

#[test]
fn coerce_toplevel_exports_moves_same_name_literal_binding_to_tail_across_later_initializer_use()
 {
    let mut compiler = LambdaCompiler::new();
    let exported = Ident::create_local("a15");
    let derived = Ident::create_local("a20");
    let ff = Ident::create_local("ff");
    let mut block = vec![
        Statement::variable(VariableDeclaration {
            ident: exported.clone(),
            value: Some(Expression::string("hello world")),
            property: LetKind::Alias,
            ident_info: IdentInfo::default(),
        }),
        Statement::variable(VariableDeclaration {
            ident: derived.clone(),
            value: Some(Expression::new(ExpressionDesc::StringAppend(
                Box::new(Expression::var(exported.clone())),
                Box::new(Expression::string("not")),
            ))),
            property: LetKind::Strict,
            ident_info: IdentInfo::default(),
        }),
        Statement::variable(VariableDeclaration {
            ident: ff.clone(),
            value: Some(Expression::new(ExpressionDesc::Fun {
                is_method: false,
                params: vec![],
                body: vec![Statement::return_(Expression::var(derived.clone()))],
                env: Default::default(),
                return_unit: false,
                async_: false,
                directive: None,
            })),
            property: LetKind::Strict,
            ident_info: IdentInfo::default(),
        }),
    ];

    let exports = compiler.coerce_toplevel_exports(
        &mut block,
        ExtractedExports {
            exports: vec![exported.clone()],
            values: vec![Expression::var(exported.clone())],
        },
    );
    let exports = resolve_export_aliases(&block, exports);

    assert_eq!(exports, vec![exported.clone()]);
    let [first, second, third] = block.as_slice() else {
        panic!("expected the rewritten initializer, function binding, and late export");
    };
    match &first.desc {
        StatementDesc::Variable(VariableDeclaration {
            ident,
            value:
                Some(Expression {
                    desc: ExpressionDesc::StringAppend(left, right),
                    ..
                }),
            ..
        }) => {
            assert!(ident.same(&derived));
            assert!(matches!(
                left.as_ref(),
                Expression {
                    desc: ExpressionDesc::Str { txt, .. },
                    ..
                } if txt == "hello world"
            ));
            assert!(matches!(
                right.as_ref(),
                Expression {
                    desc: ExpressionDesc::Str { txt, .. },
                    ..
                } if txt == "not"
            ));
        }
        other => panic!("expected the rewritten derived binding first, got {other:?}"),
    }
    match &second.desc {
        StatementDesc::Variable(VariableDeclaration { ident, .. }) => {
            assert!(ident.same(&ff));
        }
        other => panic!("expected the function binding second, got {other:?}"),
    }
    match &third.desc {
        StatementDesc::Variable(VariableDeclaration {
            ident,
            value:
                Some(Expression {
                    desc: ExpressionDesc::Str { txt, .. },
                    ..
                }),
            property,
            ..
        }) => {
            assert!(ident.same(&exported));
            assert_eq!(txt, "hello world");
            assert_eq!(*property, LetKind::Alias);
        }
        other => panic!("expected the late literal export binding third, got {other:?}"),
    }
}

#[test]
fn coerce_toplevel_exports_rewrites_later_initializers_through_materialized_root_for_same_name_literal_alias_chain(
) {
    let mut compiler = LambdaCompiler::new();
    let root = Ident::create_local("a10");
    let exported = Ident::create_local("a15");
    let derived = Ident::create_local("a20");
    let ff = Ident::create_local("ff");
    let mut block = vec![
        Statement::variable(VariableDeclaration {
            ident: root.clone(),
            value: Some(Expression::string("hello world")),
            property: LetKind::Alias,
            ident_info: IdentInfo::default(),
        }),
        Statement::variable(VariableDeclaration {
            ident: exported.clone(),
            value: Some(Expression::var(root.clone())),
            property: LetKind::Alias,
            ident_info: IdentInfo::default(),
        }),
        Statement::variable(VariableDeclaration {
            ident: derived.clone(),
            value: Some(Expression::new(ExpressionDesc::StringAppend(
                Box::new(Expression::var(exported.clone())),
                Box::new(Expression::string("not")),
            ))),
            property: LetKind::Strict,
            ident_info: IdentInfo::default(),
        }),
        Statement::variable(VariableDeclaration {
            ident: ff.clone(),
            value: Some(Expression::new(ExpressionDesc::Fun {
                is_method: false,
                params: vec![],
                body: vec![Statement::return_(Expression::var(derived.clone()))],
                env: Default::default(),
                return_unit: false,
                async_: false,
                directive: None,
            })),
            property: LetKind::Strict,
            ident_info: IdentInfo::default(),
        }),
    ];

    let exports = compiler.coerce_toplevel_exports(
        &mut block,
        ExtractedExports {
            exports: vec![exported.clone()],
            values: vec![Expression::var(exported.clone())],
        },
    );
    let exports = resolve_export_aliases(&block, exports);

    assert_eq!(exports, vec![exported.clone()]);
    let [first, second, third, fourth] = block.as_slice() else {
        panic!("expected the root binding, rewritten initializer, function binding, and late export");
    };
    match &first.desc {
        StatementDesc::Variable(VariableDeclaration {
            ident,
            value:
                Some(Expression {
                    desc: ExpressionDesc::Str { txt, .. },
                    ..
                }),
            property,
            ..
        }) => {
            assert!(ident.same(&root));
            assert_eq!(txt, "hello world");
            assert_eq!(*property, LetKind::Alias);
        }
        other => panic!("expected the materialized root binding first, got {other:?}"),
    }
    match &second.desc {
        StatementDesc::Variable(VariableDeclaration {
            ident,
            value:
                Some(Expression {
                    desc: ExpressionDesc::StringAppend(left, right),
                    ..
                }),
            ..
        }) => {
            assert!(ident.same(&derived));
            assert!(matches!(
                left.as_ref(),
                Expression {
                    desc: ExpressionDesc::Var(VIdent::Id(target)),
                    ..
                } if target.same(&root)
            ));
            assert!(matches!(
                right.as_ref(),
                Expression {
                    desc: ExpressionDesc::Str { txt, .. },
                    ..
                } if txt == "not"
            ));
        }
        other => panic!("expected the rewritten derived binding second, got {other:?}"),
    }
    match &third.desc {
        StatementDesc::Variable(VariableDeclaration { ident, .. }) => {
            assert!(ident.same(&ff));
        }
        other => panic!("expected the function binding third, got {other:?}"),
    }
    match &fourth.desc {
        StatementDesc::Variable(VariableDeclaration {
            ident,
            value:
                Some(Expression {
                    desc: ExpressionDesc::Var(VIdent::Id(target)),
                    ..
                }),
            property,
            ..
        }) => {
            assert!(ident.same(&exported));
            assert!(target.same(&root));
            assert_eq!(*property, LetKind::Alias);
        }
        other => panic!("expected the late export binding to reuse the materialized root, got {other:?}"),
    }
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
        Statement::variable(VariableDeclaration {
            ident: exported.clone(),
            value: Some(Expression::qualified(stdlib_lazy, Some("get".to_string()))),
            property: LetKind::Alias,
            ident_info: IdentInfo::default(),
        }),
        Statement::variable(VariableDeclaration {
            ident: fib.clone(),
            value: Some(Expression::new(ExpressionDesc::Fun {
                is_method: false,
                params: vec![n.clone()],
                body: vec![Statement::return_(Expression::var(n))],
                env: Default::default(),
                return_unit: false,
                async_: false,
                directive: None,
            })),
            property: LetKind::Strict,
            ident_info: IdentInfo::default(),
        }),
    ];

    let exports = compiler.coerce_toplevel_exports(
        &mut block,
        ExtractedExports {
            exports: vec![exported.clone()],
            values: vec![Expression::var(exported.clone())],
        },
    );
    let exports = resolve_export_aliases(&block, exports);

    assert_eq!(exports, vec![exported.clone()]);
    let [first, second] = block.as_slice() else {
        panic!("expected the qualified alias plus the later function binding");
    };
    match &first.desc {
        StatementDesc::Variable(VariableDeclaration {
            ident,
            value:
                Some(Expression {
                    desc: ExpressionDesc::Var(VIdent::Qualified(module, Some(field))),
                    ..
                }),
            property,
            ..
        }) => {
            assert!(ident.same(&exported));
            assert_eq!(module.id.name(), "Stdlib_Lazy");
            assert_eq!(field, "get");
            assert_eq!(*property, LetKind::Alias);
        }
        other => panic!("expected the qualified alias binding first, got {other:?}"),
    }
    match &second.desc {
        StatementDesc::Variable(VariableDeclaration {
            ident,
            value:
                Some(Expression {
                    desc: ExpressionDesc::Fun { .. },
                    ..
                }),
            ..
        }) => assert!(ident.same(&fib)),
        other => panic!("expected the later function binding second, got {other:?}"),
    }
}

fn coerce_toplevel_exports_moves_same_name_literal_binding_to_tail_across_later_effect_without_remaining_use()
 {
    let mut compiler = LambdaCompiler::new();
    let exported = Ident::create_local("b");
    let helper = Ident::create_local("f1");
    let sink = Ident::create_persistent("sink");
    let mut block = vec![
        Statement::variable(VariableDeclaration {
            ident: exported.clone(),
            value: Some(Expression::string("Three")),
            property: LetKind::Alias,
            ident_info: IdentInfo::default(),
        }),
        Statement::variable(VariableDeclaration {
            ident: helper.clone(),
            value: Some(Expression::new(ExpressionDesc::Fun {
                is_method: false,
                params: vec![],
                body: vec![Statement::return_(Expression::string("b"))],
                env: Default::default(),
                return_unit: false,
                async_: false,
                directive: None,
            })),
            property: LetKind::Strict,
            ident_info: IdentInfo::default(),
        }),
        Statement::exp(Expression::call(
            Expression::var(sink),
            vec![Expression::number(Number::int(1))],
            CallInfo::default(),
        )),
    ];

    let exports = compiler.coerce_toplevel_exports(
        &mut block,
        ExtractedExports {
            exports: vec![exported.clone()],
            values: vec![Expression::var(exported.clone())],
        },
    );
    let exports = resolve_export_aliases(&block, exports);

    assert_eq!(exports, vec![exported.clone()]);
    let [first, second, third] = block.as_slice() else {
        panic!("expected the function binding, effect, and late export");
    };
    match &first.desc {
        StatementDesc::Variable(VariableDeclaration { ident, .. }) => {
            assert!(ident.same(&helper));
        }
        other => panic!("expected the function binding first, got {other:?}"),
    }
    match &second.desc {
        StatementDesc::Exp(Expression {
            desc: ExpressionDesc::Call(_, args, _),
            ..
        }) => {
            assert!(matches!(
                args.as_slice(),
                [Expression {
                    desc: ExpressionDesc::Number(Number::Int { i: 1, .. }),
                    ..
                }]
            ));
        }
        other => panic!("expected the later effect second, got {other:?}"),
    }
    match &third.desc {
        StatementDesc::Variable(VariableDeclaration {
            ident,
            value:
                Some(Expression {
                    desc: ExpressionDesc::Str { txt, .. },
                    ..
                }),
            property,
            ..
        }) => {
            assert!(ident.same(&exported));
            assert_eq!(txt, "Three");
            assert_eq!(*property, LetKind::Alias);
        }
        other => panic!("expected the late literal export binding third, got {other:?}"),
    }
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
        Statement::variable(VariableDeclaration {
            ident: declared.clone(),
            value: Some(Expression::qualified(
                set_gen,
                Some("empty".to_string()),
            )),
            property: LetKind::Strict,
            ident_info: IdentInfo::default(),
        }),
        Statement::exp(Expression::call(
            Expression::var(effect.clone()),
            vec![],
            CallInfo::default(),
        )),
    ];

    let exports = compiler.coerce_toplevel_exports(
        &mut block,
        ExtractedExports {
            exports: vec![exported.clone()],
            values: vec![Expression::var(declared.clone())],
        },
    );
    let exports = resolve_export_aliases(&block, exports);

    assert_eq!(exports.len(), 1);
    assert_eq!(exports[0].name(), exported.name());
    let [first, second] = block.as_slice() else {
        panic!("expected the original binding to stay ahead of the later effect");
    };
    match &first.desc {
        StatementDesc::Variable(VariableDeclaration {
            ident,
            value:
                Some(Expression {
                    desc: ExpressionDesc::Var(VIdent::Qualified(module, Some(field))),
                    ..
                }),
            property,
            ..
        }) => {
            assert!(ident.same(&declared));
            assert_eq!(module.id.name(), "Set_gen");
            assert_eq!(field, "empty");
            assert_eq!(*property, LetKind::Strict);
        }
        other => panic!("expected the module-field binding first, got {other:?}"),
    }
    match &second.desc {
        StatementDesc::Exp(Expression {
            desc: ExpressionDesc::Call(func, args, _),
            ..
        }) => {
            assert!(args.is_empty());
            match &func.desc {
                ExpressionDesc::Var(VIdent::Id(ident)) => assert!(ident.same(&effect)),
                other => panic!("expected the later effect call to stay second, got {other:?}"),
            }
        }
        other => panic!("expected the later effect statement second, got {other:?}"),
    }
}

#[test]
fn coerce_toplevel_exports_keeps_same_name_runtime_module_field_alias_before_unused_later_effect(
) {
    let mut compiler = LambdaCompiler::new();
    let belt_mutable_set_int = ModuleId {
        id: Ident::create_persistent("Belt_MutableSetInt"),
        kind: Kind::Runtime,
        dynamic_import: false,
    };
    let exported = Ident::create_local("fromArray");
    let effect = Ident::create_local("effect");
    let mut block = vec![
        Statement::variable(VariableDeclaration {
            ident: exported.clone(),
            value: Some(Expression::qualified(
                belt_mutable_set_int.clone(),
                Some("fromArray".to_string()),
            )),
            property: LetKind::Alias,
            ident_info: IdentInfo::default(),
        }),
        Statement::exp(Expression::call(
            Expression::var(effect.clone()),
            vec![],
            CallInfo::default(),
        )),
    ];

    let exports = compiler.coerce_toplevel_exports(
        &mut block,
        ExtractedExports {
            exports: vec![exported.clone()],
            values: vec![Expression::var(exported.clone())],
        },
    );
    let exports = resolve_export_aliases(&block, exports);

    assert_eq!(exports, vec![exported.clone()]);
    let [first, second] = block.as_slice() else {
        panic!("expected the runtime alias binding to remain ahead of the later effect");
    };
    match &first.desc {
        StatementDesc::Variable(VariableDeclaration {
            ident,
            value:
                Some(Expression {
                    desc: ExpressionDesc::Var(VIdent::Qualified(module, Some(field))),
                    ..
                }),
            property,
            ..
        }) => {
            assert!(ident.same(&exported));
            assert_eq!(module.id.name(), "Belt_MutableSetInt");
            assert_eq!(field, "fromArray");
            assert_eq!(*property, LetKind::Alias);
        }
        other => panic!("expected the runtime module-field alias first, got {other:?}"),
    }
    match &second.desc {
        StatementDesc::Exp(Expression {
            desc: ExpressionDesc::Call(func, args, _),
            ..
        }) => {
            assert!(args.is_empty());
            match &func.desc {
                ExpressionDesc::Var(VIdent::Id(ident)) => assert!(ident.same(&effect)),
                other => panic!("expected the later effect call second, got {other:?}"),
            }
        }
        other => panic!("expected the later effect statement second, got {other:?}"),
    }
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
        Statement::variable(VariableDeclaration {
            ident: foo.clone(),
            value: Some(Expression::qualified(
                file_js,
                Some("foo".to_string()),
            )),
            property: LetKind::Alias,
            ident_info: IdentInfo::default(),
        }),
        Statement::variable(VariableDeclaration {
            ident: bar.clone(),
            value: Some(Expression::var(foo.clone())),
            property: LetKind::Alias,
            ident_info: IdentInfo::default(),
        }),
    ];

    let exports = compiler.coerce_toplevel_exports(
        &mut block,
        ExtractedExports {
            exports: vec![exported.clone()],
            values: vec![Expression::var(bar)],
        },
    );
    let exports = resolve_export_aliases(&block, exports);

    assert_eq!(exports, vec![exported.clone()]);
    let [first, second] = block.as_slice() else {
        panic!("expected the imported alias plus the late export alias");
    };
    match &first.desc {
        StatementDesc::Variable(VariableDeclaration {
            ident,
            value:
                Some(Expression {
                    desc: ExpressionDesc::Var(VIdent::Qualified(_, Some(field))),
                    ..
                }),
            ..
        }) => {
            assert!(ident.same(&foo));
            assert_eq!(field, "foo");
        }
        other => panic!("expected the imported alias binding first, got {other:?}"),
    }
    match &second.desc {
        StatementDesc::Variable(VariableDeclaration {
            ident,
            value:
                Some(Expression {
                    desc: ExpressionDesc::Var(VIdent::Id(target)),
                    ..
                }),
            property,
            ..
        }) => {
            assert!(ident.same(&exported));
            assert!(target.same(&foo));
            assert_eq!(*property, LetKind::Alias);
        }
        other => panic!("expected the late export alias to reuse foo, got {other:?}"),
    }
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
        Statement::variable(VariableDeclaration {
            ident: int_hash.clone(),
            value: Some(Expression::qualified(hash_utils, Some("hash".to_string()))),
            property: LetKind::Alias,
            ident_info: IdentInfo::default(),
        }),
        Statement::variable(VariableDeclaration {
            ident: y.clone(),
            value: Some(Expression::call(
                Expression::qualified(belt_id, Some("hashable".to_string())),
                vec![
                    Expression::var(int_hash.clone()),
                    Expression::var(int_eq.clone()),
                ],
                CallInfo::default(),
            )),
            property: LetKind::Strict,
            ident_info: IdentInfo::default(),
        }),
    ];

    let exports = compiler.coerce_toplevel_exports(
        &mut block,
        ExtractedExports {
            exports: vec![int_hash.clone(), y.clone()],
            values: vec![
                Expression::var(int_hash.clone()),
                Expression::var(y.clone()),
            ],
        },
    );
    let exports = resolve_export_aliases(&block, exports);

    assert_eq!(exports, vec![int_hash.clone(), y.clone()]);
    let [first, second] = block.as_slice() else {
        panic!("expected the alias binding plus the dependent top-level initializer");
    };
    match &first.desc {
        StatementDesc::Variable(VariableDeclaration { ident, .. }) => {
            assert!(ident.same(&int_hash));
        }
        other => panic!("expected intHash to stay materialized, got {other:?}"),
    }
    match &second.desc {
        StatementDesc::Variable(VariableDeclaration {
            ident,
            value:
                Some(Expression {
                    desc: ExpressionDesc::Call(_, args, _),
                    ..
                }),
            ..
        }) => {
            assert!(ident.same(&y));
            let [hash_arg, eq_arg] = args.as_slice() else {
                panic!("expected the dependent initializer to keep two call arguments");
            };
            match &hash_arg.desc {
                ExpressionDesc::Var(VIdent::Id(ident)) => assert!(ident.same(&int_hash)),
                other => {
                    panic!("expected the first call arg to stay as intHash, got {other:?}")
                }
            }
            match &eq_arg.desc {
                ExpressionDesc::Var(VIdent::Id(ident)) => assert!(ident.same(&int_eq)),
                other => panic!("expected the second call arg to stay as intEq, got {other:?}"),
            }
        }
        other => panic!("expected the Y initializer to stay intact, got {other:?}"),
    }
}

#[test]
fn coerce_toplevel_exports_keeps_same_name_import_alias_binding_before_top_level_effect() {
    let mut compiler = LambdaCompiler::new();
    let imported = Ident::create_persistent("MyJsonJson");
    let sink = Ident::create_persistent("sink");
    let exported = Ident::create_local("myJson");
    let mut block = vec![
        Statement::variable(VariableDeclaration {
            ident: exported.clone(),
            value: Some(Expression::var(imported.clone())),
            property: LetKind::Alias,
            ident_info: IdentInfo::default(),
        }),
        Statement::exp(Expression::call(
            Expression::var(sink),
            vec![Expression::var(exported.clone())],
            CallInfo::default(),
        )),
    ];

    let exports = compiler.coerce_toplevel_exports(
        &mut block,
        ExtractedExports {
            exports: vec![exported.clone()],
            values: vec![Expression::var(exported.clone())],
        },
    );
    let exports = resolve_export_aliases(&block, exports);

    assert_eq!(exports, vec![exported.clone()]);
    let [first, second] = block.as_slice() else {
        panic!("expected the alias binding to stay ahead of the top-level effect");
    };
    match &first.desc {
        StatementDesc::Variable(VariableDeclaration {
            ident,
            value:
                Some(Expression {
                    desc: ExpressionDesc::Var(VIdent::Id(target)),
                    ..
                }),
            ..
        }) => {
            assert!(ident.same(&exported));
            assert!(target.same(&imported));
        }
        other => panic!("expected the imported alias binding to remain first, got {other:?}"),
    }
    match &second.desc {
        StatementDesc::Exp(Expression {
            desc: ExpressionDesc::Call(_, args, _),
            ..
        }) => {
            let [arg] = args.as_slice() else {
                panic!("expected the top-level effect to keep one argument");
            };
            match &arg.desc {
                ExpressionDesc::Var(VIdent::Id(ident)) => assert!(ident.same(&exported)),
                other => panic!(
                    "expected the top-level effect to keep using the alias binding, got {other:?}"
                ),
            }
        }
        other => panic!("expected the effect statement to remain second, got {other:?}"),
    }
}

#[test]
fn coerce_toplevel_exports_moves_function_alias_binding_to_tail_when_later_effect_only_calls_it()
{
    let mut compiler = LambdaCompiler::new();
    let converter = Ident::create_local("tToJs");
    let exported = Ident::create_local("v");
    let sink = Ident::create_persistent("sink");
    let param = Ident::create_local("param");
    let arg = Ident::create_local("arg");
    let mut block = vec![
        Statement::variable(VariableDeclaration {
            ident: converter.clone(),
            value: Some(Expression::new(ExpressionDesc::Fun {
                is_method: false,
                params: vec![param.clone()],
                body: vec![Statement::return_(Expression::var(param))],
                env: Default::default(),
                return_unit: false,
                async_: false,
                directive: None,
            })),
            property: LetKind::Strict,
            ident_info: IdentInfo::default(),
        }),
        Statement::variable(VariableDeclaration {
            ident: exported.clone(),
            value: Some(Expression::var(converter.clone())),
            property: LetKind::Alias,
            ident_info: IdentInfo::default(),
        }),
        Statement::exp(Expression::call(
            Expression::var(sink),
            vec![Expression::new(ExpressionDesc::Fun {
                is_method: false,
                params: vec![arg.clone()],
                body: vec![Statement::return_(Expression::call(
                    Expression::var(exported.clone()),
                    vec![Expression::var(arg)],
                    CallInfo::default(),
                ))],
                env: Default::default(),
                return_unit: false,
                async_: false,
                directive: None,
            })],
            CallInfo::default(),
        )),
    ];

    let exports = compiler.coerce_toplevel_exports(
        &mut block,
        ExtractedExports {
            exports: vec![exported.clone()],
            values: vec![Expression::var(exported.clone())],
        },
    );
    let exports = resolve_export_aliases(&block, exports);

    assert_eq!(exports, vec![exported.clone()]);
    let [first, second, third] = block.as_slice() else {
        panic!("expected the function binding, later effect, and late export alias");
    };
    match &first.desc {
        StatementDesc::Variable(VariableDeclaration { ident, .. }) => {
            assert!(ident.same(&converter));
        }
        other => panic!("expected the underlying function binding first, got {other:?}"),
    }
    match &second.desc {
        StatementDesc::Exp(Expression {
            desc: ExpressionDesc::Call(_, args, _),
            ..
        }) => {
            let [effect_closure] = args.as_slice() else {
                panic!("expected the later effect to keep one closure argument");
            };
            match &effect_closure.desc {
                ExpressionDesc::Fun { body, .. } => {
                    let [Statement {
                        desc:
                            StatementDesc::Return(Expression {
                                desc: ExpressionDesc::Call(func, _, _),
                                ..
                            }),
                        ..
                    }] = body.as_slice()
                    else {
                        panic!("expected the closure body to stay a direct function call");
                    };
                    match &func.desc {
                        ExpressionDesc::Var(VIdent::Id(ident)) => {
                            assert!(ident.same(&converter));
                        }
                        other => panic!(
                            "expected the closure call to inline back to the underlying function, got {other:?}"
                        ),
                    }
                }
                other => panic!("expected the later effect arg to stay a closure, got {other:?}"),
            }
        }
        other => panic!("expected the later effect second, got {other:?}"),
    }
    match &third.desc {
        StatementDesc::Variable(VariableDeclaration {
            ident,
            value:
                Some(Expression {
                    desc: ExpressionDesc::Var(VIdent::Id(target)),
                    ..
                }),
            property,
            ..
        }) => {
            assert!(ident.same(&exported));
            assert!(target.same(&converter));
            assert_eq!(*property, LetKind::Alias);
        }
        other => panic!("expected the late export alias binding third, got {other:?}"),
    }
}

#[test]
fn coerce_toplevel_exports_keeps_same_name_local_value_alias_binding_for_non_function_target() {
    let mut compiler = LambdaCompiler::new();
    let process = Ident::create_local("process");
    let exported = Ident::create_local("proc");
    let global_this = Ident::create_persistent("globalThis");
    let mut block = vec![
        Statement::variable(VariableDeclaration {
            ident: process.clone(),
            value: Some(Expression::new(ExpressionDesc::StaticIndex(
                Box::new(Expression::var(global_this)),
                "process".to_string(),
                None,
            ))),
            property: LetKind::Alias,
            ident_info: IdentInfo::default(),
        }),
        Statement::variable(VariableDeclaration {
            ident: exported.clone(),
            value: Some(Expression::var(process.clone())),
            property: LetKind::Alias,
            ident_info: IdentInfo::default(),
        }),
    ];

    let exports = compiler.coerce_toplevel_exports(
        &mut block,
        ExtractedExports {
            exports: vec![exported.clone()],
            values: vec![Expression::var(exported.clone())],
        },
    );
    let exports = resolve_export_aliases(&block, exports);

    assert_eq!(exports, vec![exported.clone()]);
    let [first, second] = block.as_slice() else {
        panic!("expected both non-function aliases to stay materialized");
    };
    match &first.desc {
        StatementDesc::Variable(VariableDeclaration { ident, .. }) => {
            assert!(ident.same(&process));
        }
        other => panic!("expected the source alias binding first, got {other:?}"),
    }
    match &second.desc {
        StatementDesc::Variable(VariableDeclaration {
            ident,
            value:
                Some(Expression {
                    desc: ExpressionDesc::Var(VIdent::Id(target)),
                    ..
                }),
            ..
        }) => {
            assert!(ident.same(&exported));
            assert!(target.same(&process));
        }
        other => panic!("expected the exported alias binding second, got {other:?}"),
    }
}

#[test]
fn coerce_toplevel_exports_moves_same_name_ml_module_field_alias_to_tail_across_value_effect()
{
    let mut compiler = LambdaCompiler::new();
    let module = ModuleId {
        id: Ident::create_persistent("A3_a4"),
        kind: Kind::Ml,
        dynamic_import: false,
    };
    let exported = Ident::create_local("v");
    let sink = Ident::create_persistent("sink");
    let qualified = Expression::qualified(module.clone(), Some("v".to_string()));
    let mut block = vec![
        Statement::variable(VariableDeclaration {
            ident: exported.clone(),
            value: Some(qualified.clone()),
            property: LetKind::Alias,
            ident_info: IdentInfo::default(),
        }),
        Statement::exp(Expression::call(
            Expression::var(sink),
            vec![Expression::var(exported.clone())],
            CallInfo::default(),
        )),
    ];

    let exports = compiler.coerce_toplevel_exports(
        &mut block,
        ExtractedExports {
            exports: vec![exported.clone()],
            values: vec![Expression::var(exported.clone())],
        },
    );
    let exports = resolve_export_aliases(&block, exports);

    assert_eq!(exports, vec![exported.clone()]);
    let [first, second] = block.as_slice() else {
        panic!("expected the rewritten later effect plus the late export alias");
    };
    match &first.desc {
        StatementDesc::Exp(Expression {
            desc: ExpressionDesc::Call(_, args, _),
            ..
        }) => {
            let [arg] = args.as_slice() else {
                panic!("expected the later effect to keep one argument");
            };
            match &arg.desc {
                ExpressionDesc::Var(VIdent::Qualified(module_id, Some(field))) => {
                    assert_eq!(field, "v");
                    assert_eq!(module_id, &module);
                }
                other => panic!(
                    "expected the later effect to inline to the module field access, got {other:?}"
                ),
            }
        }
        other => panic!("expected the later effect first, got {other:?}"),
    }
    match &second.desc {
        StatementDesc::Variable(VariableDeclaration {
            ident,
            value:
                Some(Expression {
                    desc: ExpressionDesc::Var(VIdent::Qualified(module_id, Some(field))),
                    ..
                }),
            property,
            ..
        }) => {
            assert!(ident.same(&exported));
            assert_eq!(field, "v");
            assert_eq!(module_id, &module);
            assert_eq!(*property, LetKind::Alias);
        }
        other => panic!("expected the late same-name module-field alias second, got {other:?}"),
    }
}

#[test]
fn coerce_toplevel_exports_moves_same_name_ml_module_field_alias_with_different_field_name_to_tail_after_unused_later_effect(
) {
    let mut compiler = LambdaCompiler::new();
    let module = ModuleId {
        id: Ident::create_persistent("Belt_MutableSetInt"),
        kind: Kind::Ml,
        dynamic_import: false,
    };
    let exported = Ident::create_local("empty");
    let effect = Ident::create_persistent("effect");
    let mut block = vec![
        Statement::variable(VariableDeclaration {
            ident: exported.clone(),
            value: Some(Expression::qualified(module.clone(), Some("make".to_string()))),
            property: LetKind::Alias,
            ident_info: IdentInfo::default(),
        }),
        Statement::exp(Expression::call(
            Expression::var(effect.clone()),
            vec![],
            CallInfo::default(),
        )),
    ];

    let exports = compiler.coerce_toplevel_exports(
        &mut block,
        ExtractedExports {
            exports: vec![exported.clone()],
            values: vec![Expression::var(exported.clone())],
        },
    );
    let exports = resolve_export_aliases(&block, exports);

    assert_eq!(exports, vec![exported.clone()]);
    let [first, second] = block.as_slice() else {
        panic!("expected the later effect followed by the late ML export alias");
    };
    match &first.desc {
        StatementDesc::Exp(Expression {
            desc: ExpressionDesc::Call(func, args, _),
            ..
        }) => {
            assert!(args.is_empty());
            match &func.desc {
                ExpressionDesc::Var(VIdent::Id(ident)) => assert!(ident.same(&effect)),
                other => panic!("expected the later effect call first, got {other:?}"),
            }
        }
        other => panic!("expected the later effect statement first, got {other:?}"),
    }
    match &second.desc {
        StatementDesc::Variable(VariableDeclaration {
            ident,
            value:
                Some(Expression {
                    desc: ExpressionDesc::Var(VIdent::Qualified(module_id, Some(field))),
                    ..
                }),
            property,
            ..
        }) => {
            assert!(ident.same(&exported));
            assert_eq!(module_id, &module);
            assert_eq!(field, "make");
            assert_eq!(*property, LetKind::Alias);
        }
        other => panic!("expected the late ML module-field alias second, got {other:?}"),
    }
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
        Statement::variable(VariableDeclaration {
            ident: exported.clone(),
            value: Some(Expression::qualified(
                module.clone(),
                Some("default".to_string()),
            )),
            property: LetKind::Alias,
            ident_info: IdentInfo::default(),
        }),
        Statement::exp(Expression::call(
            Expression::var(sink),
            vec![Expression::var(exported.clone())],
            CallInfo::default(),
        )),
    ];

    let exports = compiler.coerce_toplevel_exports(
        &mut block,
        ExtractedExports {
            exports: vec![exported.clone()],
            values: vec![Expression::qualified(module, Some("default".to_string()))],
        },
    );
    let exports = resolve_export_aliases(&block, exports);

    assert_eq!(exports, vec![exported.clone()]);
    let [first, second] = block.as_slice() else {
        panic!("expected the qualified alias binding to remain ahead of the value-position effect");
    };
    match &first.desc {
        StatementDesc::Variable(VariableDeclaration { ident, .. }) => {
            assert!(ident.same(&exported));
        }
        other => panic!("expected the qualified alias binding first, got {other:?}"),
    }
    match &second.desc {
        StatementDesc::Exp(Expression {
            desc: ExpressionDesc::Call(_, args, _),
            ..
        }) => {
            let [arg] = args.as_slice() else {
                panic!("expected the later effect to keep one argument");
            };
            match &arg.desc {
                ExpressionDesc::Var(VIdent::Id(ident)) => assert!(ident.same(&exported)),
                other => panic!(
                    "expected the later effect to keep using the alias binding, got {other:?}"
                ),
            }
        }
        other => panic!("expected the effect statement second, got {other:?}"),
    }
}

#[test]
fn rewrite_toplevel_variable_initializers_through_rewriteable_aliases_rewrites_function_and_literal_aliases(
) {
    let target = Ident::create_local("myField");
    let exported_same_name_alias = Ident::create_local("myField");
    let no_param = Ident::create_local("noParam");
    let field_alias = Ident::create_local("_myFieldAlias");
    let no_param_alias = Ident::create_local("_noParamAlias");
    let param = Ident::create_local("param");
    let mut block = vec![
        Statement::variable(VariableDeclaration {
            ident: target.clone(),
            value: Some(Expression::new(ExpressionDesc::Fun {
                is_method: false,
                params: vec![param],
                body: vec![Statement::return_(Expression::undefined(false))],
                env: Default::default(),
                return_unit: false,
                async_: false,
                directive: None,
            })),
            property: LetKind::Strict,
            ident_info: IdentInfo::default(),
        }),
        Statement::variable(VariableDeclaration {
            ident: exported_same_name_alias.clone(),
            value: Some(Expression::var(target.clone())),
            property: LetKind::Alias,
            ident_info: IdentInfo::default(),
        }),
        Statement::variable(VariableDeclaration {
            ident: no_param.clone(),
            value: Some(Expression::string("NoParam")),
            property: LetKind::Strict,
            ident_info: IdentInfo::default(),
        }),
        Statement::variable(VariableDeclaration {
            ident: field_alias.clone(),
            value: Some(Expression::var(exported_same_name_alias)),
            property: LetKind::Alias,
            ident_info: IdentInfo::default(),
        }),
        Statement::variable(VariableDeclaration {
            ident: no_param_alias.clone(),
            value: Some(Expression::var(no_param)),
            property: LetKind::Alias,
            ident_info: IdentInfo::default(),
        }),
    ];

    rewrite_toplevel_variable_initializers_through_rewriteable_aliases(
        &mut block,
        &[field_alias.clone(), no_param_alias.clone()],
    );

    let Some(field_alias_value) = find_variable_initializer(&block, &field_alias) else {
        panic!("expected the field alias binding to remain");
    };
    match &field_alias_value.desc {
        ExpressionDesc::Var(VIdent::Id(ident)) => assert!(ident.same(&target)),
        other => panic!("expected _myFieldAlias to rewrite to myField, got {other:?}"),
    }

    let Some(no_param_alias_value) = find_variable_initializer(&block, &no_param_alias) else {
        panic!("expected the noParam alias binding to remain");
    };
    match &no_param_alias_value.desc {
        ExpressionDesc::Str { txt, .. } => assert_eq!(txt, "NoParam"),
        other => panic!("expected _noParamAlias to inline the literal, got {other:?}"),
    }
}

#[test]
fn rewrite_toplevel_variable_initializers_through_rewriteable_aliases_skips_non_export_aliases(
) {
    let target = Ident::create_local("myField");
    let exported_same_name_alias = Ident::create_local("myField");
    let non_export_alias = Ident::create_local("_myFieldAlias");
    let param = Ident::create_local("param");
    let mut block = vec![
        Statement::variable(VariableDeclaration {
            ident: target.clone(),
            value: Some(Expression::new(ExpressionDesc::Fun {
                is_method: false,
                params: vec![param],
                body: vec![Statement::return_(Expression::undefined(false))],
                env: Default::default(),
                return_unit: false,
                async_: false,
                directive: None,
            })),
            property: LetKind::Strict,
            ident_info: IdentInfo::default(),
        }),
        Statement::variable(VariableDeclaration {
            ident: exported_same_name_alias.clone(),
            value: Some(Expression::var(target)),
            property: LetKind::Alias,
            ident_info: IdentInfo::default(),
        }),
        Statement::variable(VariableDeclaration {
            ident: non_export_alias.clone(),
            value: Some(Expression::var(exported_same_name_alias.clone())),
            property: LetKind::Alias,
            ident_info: IdentInfo::default(),
        }),
    ];

    rewrite_toplevel_variable_initializers_through_rewriteable_aliases(
        &mut block,
        &[exported_same_name_alias.clone()],
    );

    let Some(non_export_alias_value) = find_variable_initializer(&block, &non_export_alias)
    else {
        panic!("expected the non-export alias binding to remain");
    };
    match &non_export_alias_value.desc {
        ExpressionDesc::Var(VIdent::Id(ident)) => assert!(ident.same(&exported_same_name_alias)),
        other => panic!("expected non-export alias to stay as a variable alias, got {other:?}"),
    }
}

#[test]
fn rewrite_toplevel_variable_initializers_through_rewriteable_aliases_keeps_shared_literal_roots_materialized(
) {
    let shared_root = Ident::create_local("a10");
    let shared_use = Ident::create_local("a20");
    let exported_alias = Ident::create_local("a15");
    let mut block = vec![
        Statement::variable(VariableDeclaration {
            ident: shared_root.clone(),
            value: Some(Expression::string("hello world")),
            property: LetKind::Strict,
            ident_info: IdentInfo::default(),
        }),
        Statement::variable(VariableDeclaration {
            ident: shared_use,
            value: Some(Expression::var(shared_root.clone())),
            property: LetKind::Alias,
            ident_info: IdentInfo::default(),
        }),
        Statement::variable(VariableDeclaration {
            ident: exported_alias.clone(),
            value: Some(Expression::var(shared_root.clone())),
            property: LetKind::Alias,
            ident_info: IdentInfo::default(),
        }),
    ];

    rewrite_toplevel_variable_initializers_through_rewriteable_aliases(
        &mut block,
        std::slice::from_ref(&exported_alias),
    );

    let Some(exported_alias_value) = find_variable_initializer(&block, &exported_alias) else {
        panic!("expected the exported alias binding to remain");
    };
    match &exported_alias_value.desc {
        ExpressionDesc::Var(VIdent::Id(ident)) => assert!(ident.same(&shared_root)),
        other => panic!(
            "expected the shared literal root to stay materialized, got {other:?}"
        ),
    }
}

#[test]
fn compile_deps_program_keeps_exports_after_trailing_effect_sequence() {
    let mut compiler = LambdaCompiler::new();
    let exported = Ident::create_local("foo");
    let export_block = Lambda::prim(
        Primitive::Pmakeblock(
            0,
            TagInfo::ModuleExport(vec![exported.clone()]),
            Mutable::Immutable,
        ),
        vec![Lambda::var(exported.clone())],
        Location::none(),
    );
    let lam = Lambda::let_(
        LetKind::Strict,
        exported.clone(),
        Lambda::const_(Constant::int(1)),
        Lambda::seq(
            Lambda::assign(exported.clone(), Lambda::const_(Constant::int(2))),
            export_block,
        ),
    );

    let deps = compiler.compile_deps_program(&lam);

    let [exported_ident] = deps.program.exports.as_slice() else {
        panic!("expected a single export after the trailing effect");
    };
    assert!(exported_ident.same(&exported));

    assert!(
        deps.program.block.iter().any(|stmt| matches!(
            &stmt.desc,
            StatementDesc::Exp(Expression {
                desc: ExpressionDesc::Bin(
                    BinOp::Eq,
                    left,
                    right,
                ),
                ..
            }) if matches!(
                left.as_ref(),
                Expression {
                    desc: ExpressionDesc::Var(VIdent::Id(id)),
                    ..
                } if id.same(&exported)
            ) && matches!(
                right.as_ref(),
                Expression {
                    desc: ExpressionDesc::Number(Number::Int { i: 2, .. }),
                    ..
                }
            )
        )),
        "expected the trailing assignment effect to remain in the program block"
    );
}

#[test]
fn compile_deps_program_skips_unreachable_throwing_export_binding_declaration() {
    let mut compiler = LambdaCompiler::new();
    let exported = Ident::create_local("u");
    let export_block = Lambda::prim(
        Primitive::Pmakeblock(
            0,
            TagInfo::ModuleExport(vec![exported.clone()]),
            Mutable::Immutable,
        ),
        vec![Lambda::var(exported.clone())],
        Location::none(),
    );
    let lam = Lambda::let_(
        LetKind::Strict,
        exported.clone(),
        Lambda::prim(
            Primitive::Praise,
            vec![Lambda::const_(Constant::string("boom"))],
            Location::none(),
        ),
        export_block,
    );

    let deps = compiler.compile_deps_program(&lam);

    assert_eq!(deps.program.exports, vec![exported.clone()]);
    let [stmt] = deps.program.block.as_slice() else {
        panic!(
            "expected the terminating throw to stay as the only statement, got {:?}",
            deps.program.block
        );
    };
    assert!(matches!(
        stmt,
        Statement {
            desc: StatementDesc::Throw(Expression {
                desc: ExpressionDesc::Str { txt, .. },
                ..
            }),
            ..
        } if txt == "boom"
    ));
}

#[test]
fn compile_deps_program_skips_unreachable_nested_throwing_export_binding_declaration() {
    let mut compiler = LambdaCompiler::new();
    let exported = Ident::create_local("A");
    let nested = Ident::create_local("u");
    let export_block = Lambda::prim(
        Primitive::Pmakeblock(
            0,
            TagInfo::ModuleExport(vec![exported.clone()]),
            Mutable::Immutable,
        ),
        vec![Lambda::var(exported.clone())],
        Location::none(),
    );
    let lam = Lambda::let_(
        LetKind::Strict,
        exported.clone(),
        Lambda::let_(
            LetKind::Strict,
            nested.clone(),
            Lambda::prim(
                Primitive::Praise,
                vec![Lambda::const_(Constant::string("boom"))],
                Location::none(),
            ),
            Lambda::prim(
                Primitive::Pmakeblock(
                    0,
                    TagInfo::record(
                        vec![(nested.name().to_string(), false)],
                        crate::parser::ast::MutableFlag::Immutable,
                    ),
                    Mutable::Immutable,
                ),
                vec![Lambda::var(nested)],
                Location::none(),
            ),
        ),
        export_block,
    );

    let deps = compiler.compile_deps_program(&lam);

    assert_eq!(deps.program.exports, vec![exported.clone()]);
    let [stmt] = deps.program.block.as_slice() else {
        panic!(
            "expected the terminating throw to stay as the only statement, got {:?}",
            deps.program.block
        );
    };
    assert!(
        matches!(
            stmt,
            Statement {
                desc: StatementDesc::Throw(Expression {
                    desc: ExpressionDesc::Str { txt, .. },
                    ..
                }),
                ..
            } if txt == "boom"
        ),
        "expected a terminating throw, got {:?}",
        stmt
    );
}

#[test]
fn compile_return_block_skips_unreachable_sequence_after_throw() {
    let mut compiler = LambdaCompiler::new();
    let block = compiler.compile_return_block(&Lambda::seq(
        Lambda::prim(
            Primitive::Praise,
            vec![Lambda::const_(Constant::string("boom"))],
            Location::none(),
        ),
        Lambda::const_(Constant::int(12)),
    ));

    let [stmt] = block.as_slice() else {
        panic!("expected only the terminating throw, got {:?}", block);
    };
    assert!(matches!(
        stmt,
        Statement {
            desc: StatementDesc::Throw(Expression {
                desc: ExpressionDesc::Str { txt, .. },
                ..
            }),
            ..
        } if txt == "boom"
    ));
}

#[test]
fn compile_return_block_lowers_trywith_in_return_position() {
    let mut compiler = LambdaCompiler::new();
    let callee = Ident::create_local("g");
    let exn = Ident::create_local("exn");
    let block = compiler.compile_return_block(&Lambda::LtryWith(
        Box::new(Lambda::Lapply(Apply {
            ap_func: Box::new(Lambda::var(callee)),
            ap_args: vec![],
            ap_info: ApInfo {
                loc: Location::none(),
                inlined: InlineAttribute::Default,
                status: ApplyStatus::Na,
            },
            ap_transformed_jsx: false,
        })),
        exn.clone(),
        Box::new(Lambda::const_(Constant::int(0))),
    ));

    let [stmt] = block.as_slice() else {
        panic!("expected a single try statement, got {:?}", block);
    };
    let StatementDesc::Try(body, Some((caught, handler)), None) = &stmt.desc else {
        panic!("expected a try statement, got {:?}", stmt);
    };

    assert!(caught.same(&exn));
    assert!(matches!(
        body.as_slice(),
        [Statement {
            desc: StatementDesc::Return(_),
            ..
        }]
    ));
    assert!(matches!(
        handler.as_slice(),
        [Statement {
            desc: StatementDesc::Return(Expression {
                desc: ExpressionDesc::Number(Number::Int { i: 0, .. }),
                ..
            }),
            ..
        }]
    ));
}

#[test]
fn trywith_expression_result_temp_uses_tmp_name_like_ocaml() {
    let mut compiler = LambdaCompiler::new();
    let exn = Ident::create_local("exn");
    let compiled = compiler.compile_expr(&Lambda::LtryWith(
        Box::new(Lambda::const_(Constant::int(1))),
        exn.clone(),
        Box::new(Lambda::const_(Constant::int(2))),
    ));

    let [declare, try_stmt] = compiled.prelude.as_slice() else {
        panic!("expected a declaration followed by a try statement");
    };
    let StatementDesc::Variable(VariableDeclaration { ident: result, .. }) = &declare.desc
    else {
        panic!("expected the trywith result temp declaration");
    };
    assert_eq!(result.name(), "tmp");
    let StatementDesc::Try(body, Some((caught, handler)), None) = &try_stmt.desc else {
        panic!("expected a try statement");
    };
    assert!(caught.same(&exn));
    assert!(matches!(
        body.as_slice(),
        [Statement {
            desc: StatementDesc::Exp(Expression {
                desc: ExpressionDesc::Bin(BinOp::Eq, lhs, rhs),
                ..
            }),
            ..
        }] if matches!(
            (&lhs.desc, &rhs.desc),
            (
                ExpressionDesc::Var(crate::js_ir::VIdent::Id(lhs_id)),
                ExpressionDesc::Number(Number::Int { i: 1, .. })
            ) if lhs_id.same(result)
        )
    ));
    assert!(matches!(
        handler.as_slice(),
        [Statement {
            desc: StatementDesc::Exp(Expression {
                desc: ExpressionDesc::Bin(BinOp::Eq, lhs, rhs),
                ..
            }),
            ..
        }] if matches!(
            (&lhs.desc, &rhs.desc),
            (
                ExpressionDesc::Var(crate::js_ir::VIdent::Id(lhs_id)),
                ExpressionDesc::Number(Number::Int { i: 2, .. })
            ) if lhs_id.same(result)
        )
    ));
    assert!(matches!(
        compiled.expr,
        Expression {
            desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
            ..
        } if id.same(result)
    ));
}

#[test]
fn staticcatch_trywith_return_keeps_bound_exit_effects_outside_try_like_ocaml() {
    let mut compiler = LambdaCompiler::new();
    let x = Ident::create_local("x");
    let g = Ident::create_local("g");
    let exn = Ident::create_local("exn");
    let val = Ident::create_local("val");
    let block = compiler.compile_return_block(&Lambda::LstaticCatch(
        Box::new(Lambda::LtryWith(
            Box::new(Lambda::LstaticRaise(
                -2,
                vec![Lambda::Lapply(Apply {
                    ap_func: Box::new(Lambda::var(x.clone())),
                    ap_args: vec![],
                    ap_info: ApInfo {
                        loc: Location::none(),
                        inlined: InlineAttribute::Default,
                        status: ApplyStatus::Na,
                    },
                    ap_transformed_jsx: false,
                })],
            )),
            exn.clone(),
            Box::new(Lambda::const_(Constant::int(1))),
        )),
        (-2, vec![val.clone()]),
        Box::new(Lambda::Lapply(Apply {
            ap_func: Box::new(Lambda::var(g.clone())),
            ap_args: vec![],
            ap_info: ApInfo {
                loc: Location::none(),
                inlined: InlineAttribute::Default,
                status: ApplyStatus::Na,
            },
            ap_transformed_jsx: false,
        })),
    ));

    let [declare, try_stmt, ret] = block.as_slice() else {
        panic!("expected binding decl, try, and trailing return, got {block:?}");
    };

    assert!(matches!(
        &declare.desc,
        StatementDesc::Variable(VariableDeclaration { ident, value, .. })
            if ident.same(&val) && value.is_none()
    ));

    let StatementDesc::Try(body, Some((caught, handler)), None) = &try_stmt.desc else {
        panic!("expected a try statement, got {try_stmt:?}");
    };
    assert!(caught.same(&exn));
    assert!(matches!(
        body.as_slice(),
        [Statement {
            desc: StatementDesc::Exp(Expression {
                desc: ExpressionDesc::Bin(BinOp::Eq, lhs, rhs),
                ..
            }),
            ..
        }] if matches!(
            (&lhs.as_ref().desc, &rhs.as_ref().desc),
            (
                ExpressionDesc::Var(crate::js_ir::VIdent::Id(lhs_id)),
                ExpressionDesc::Call(func, args, _)
            ) if lhs_id.same(&val)
                && args.is_empty()
                && matches!(
                    func.as_ref(),
                    Expression {
                        desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(func_id)),
                        ..
                    } if func_id.same(&x)
                )
        )
    ));
    assert!(matches!(
        handler.as_slice(),
        [Statement {
            desc: StatementDesc::Return(Expression {
                desc: ExpressionDesc::Number(Number::Int { i: 1, .. }),
                ..
            }),
            ..
        }]
    ));

    assert!(matches!(
        &ret.desc,
        StatementDesc::Return(Expression {
            desc: ExpressionDesc::Call(func, args, _),
            ..
        }) if args.is_empty()
            && matches!(
                func.as_ref(),
                Expression {
                    desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(func_id)),
                    ..
                } if func_id.same(&g)
            )
    ));
}

#[test]
fn staticcatch_wrapped_trywith_identity_handler_returns_directly_like_ocaml() {
    let mut compiler = LambdaCompiler::new();
    let g = Ident::create_local("g");
    let x = Ident::create_local("x");
    let exn = Ident::create_local("exn");
    let y = Ident::create_local("y");
    let block = compiler.compile_return_block(&Lambda::LstaticCatch(
        Box::new(Lambda::LtryWith(
            Box::new(Lambda::LstaticRaise(
                -1,
                vec![Lambda::Lapply(Apply {
                    ap_func: Box::new(Lambda::var(g.clone())),
                    ap_args: vec![Lambda::var(x.clone())],
                    ap_info: ApInfo {
                        loc: Location::none(),
                        inlined: InlineAttribute::Default,
                        status: ApplyStatus::Na,
                    },
                    ap_transformed_jsx: false,
                })],
            )),
            exn.clone(),
            Box::new(Lambda::const_(Constant::int(3))),
        )),
        (-1, vec![y.clone()]),
        Box::new(Lambda::var(y)),
    ));

    let [try_stmt] = block.as_slice() else {
        panic!(
            "expected the identity staticcatch wrapper to collapse to one try statement, got {block:?}"
        );
    };
    let StatementDesc::Try(body, Some((caught, handler)), None) = &try_stmt.desc else {
        panic!("expected the collapsed block to stay a try statement, got {try_stmt:?}");
    };
    assert!(caught.same(&exn));
    assert!(matches!(
        body.as_slice(),
        [Statement {
            desc: StatementDesc::Return(Expression {
                desc: ExpressionDesc::Call(func, args, _),
                ..
            }),
            ..
        }] if args.len() == 1
            && matches!(
                func.as_ref(),
                Expression {
                    desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                    ..
                } if id.same(&g)
            )
            && matches!(
                args.as_slice(),
                [Expression {
                    desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                    ..
                }] if id.same(&x)
            )
    ));
    assert!(matches!(
        handler.as_slice(),
        [Statement {
            desc: StatementDesc::Return(Expression {
                desc: ExpressionDesc::Number(Number::Int { i: 3, .. }),
                ..
            }),
            ..
        }]
    ));
}

#[test]
fn staticcatch_trywith_tail_loop_keeps_bound_exit_effects_outside_try_like_ocaml() {
    let mut compiler = LambdaCompiler::new();
    let loop_ = Ident::create_local("loop");
    let acc = Ident::create_local("acc");
    let read = Ident::create_local("read");
    let next_acc = Ident::create_local("nextAcc");
    let exn = Ident::create_local("exn");
    let lam = Lambda::letrec(
        vec![(
            loop_.clone(),
            Lambda::function_(
                1,
                vec![acc.clone()],
                Lambda::LstaticCatch(
                    Box::new(Lambda::LtryWith(
                        Box::new(Lambda::LstaticRaise(
                            -1,
                            vec![Lambda::Lapply(Apply {
                                ap_func: Box::new(Lambda::var(read.clone())),
                                ap_args: vec![Lambda::var(acc.clone())],
                                ap_info: ApInfo {
                                    loc: Location::none(),
                                    inlined: InlineAttribute::Default,
                                    status: ApplyStatus::Na,
                                },
                                ap_transformed_jsx: false,
                            })],
                        )),
                        exn.clone(),
                        Box::new(Lambda::const_(Constant::int(0))),
                    )),
                    (-1, vec![next_acc.clone()]),
                    Box::new(Lambda::Lapply(Apply {
                        ap_func: Box::new(Lambda::var(loop_.clone())),
                        ap_args: vec![Lambda::var(next_acc.clone())],
                        ap_info: ApInfo {
                            loc: Location::none(),
                            inlined: InlineAttribute::Default,
                            status: ApplyStatus::Na,
                        },
                        ap_transformed_jsx: false,
                    })),
                ),
                FunctionAttribute::default(),
            ),
        )],
        Lambda::unit(),
    );

    let compiled = compiler.compile_expr(&lam);
    let rendered = print_block(&compiled.prelude);

    assert!(
        rendered.contains("while (true)"),
        "expected staticcatch trywith lowering to stay on the tail loop path:\n{rendered}"
    );
    assert!(
        rendered.contains("let nextAcc;"),
        "expected the bound staticcatch value to be declared outside the try:\n{rendered}"
    );
    assert!(
        rendered.contains("try {"),
        "expected the bound exit effect to stay inside the try body:\n{rendered}"
    );
    assert!(
        rendered.contains("nextAcc = read(")
            || rendered.contains("nextAcc = read(acc)")
            || rendered.contains("nextAcc = _read(")
            || rendered.contains("nextAcc = _read(acc)"),
        "expected the fallthrough exit value to be assigned before the loop continue:\n{rendered}"
    );
    assert!(
        rendered.contains("continue;"),
        "expected the recursive handler to stay as a loop continue:\n{rendered}"
    );
    assert!(
        !rendered.contains("return loop("),
        "unexpected direct recursive return remained after the staticcatch handler:\n{rendered}"
    );
}

#[test]
fn direct_recursive_trywith_self_calls_do_not_lower_to_loops_like_ocaml() {
    let mut compiler = LambdaCompiler::new();
    let loop_ = Ident::create_local("loop");
    let acc = Ident::create_local("acc");
    let exn = Ident::create_local("exn");
    let lam = Lambda::letrec(
        vec![(
            loop_.clone(),
            Lambda::function_(
                1,
                vec![acc.clone()],
                Lambda::LtryWith(
                    Box::new(Lambda::Lapply(Apply {
                        ap_func: Box::new(Lambda::var(loop_.clone())),
                        ap_args: vec![Lambda::var(acc.clone())],
                        ap_info: ApInfo {
                            loc: Location::none(),
                            inlined: InlineAttribute::Default,
                            status: ApplyStatus::Na,
                        },
                        ap_transformed_jsx: false,
                    })),
                    exn,
                    Box::new(Lambda::const_(Constant::int(0))),
                ),
                FunctionAttribute::default(),
            ),
        )],
        Lambda::unit(),
    );

    let compiled = compiler.compile_expr(&lam);
    let rendered = print_block(&compiled.prelude);

    assert!(
        !rendered.contains("while (true)"),
        "expected direct recursive trywith lowering to stay as a recursive call:\n{rendered}"
    );
    assert!(
        rendered.contains("try {"),
        "expected the recursive self-call to stay inside the try body:\n{rendered}"
    );
    assert!(
        rendered.contains("return loop(acc)")
            || rendered.contains("return loop(_acc)")
            || rendered.contains("return loop("),
        "expected the direct recursive return to remain in the emitted body:\n{rendered}"
    );
}

#[test]
fn nested_wrapped_staticcatch_trywith_tail_loops_lower_like_gpr_1701() {
    let mut compiler = LambdaCompiler::new();
    let outer = Ident::create_local("readLines");
    let inc = Ident::create_local("inc");
    let loop_ = Ident::create_local("loop");
    let acc = Ident::create_local("acc");
    let read = Ident::create_local("read");
    let next_acc = Ident::create_local("nextAcc");
    let exn = Ident::create_local("exn");
    let raw_exn = Ident::create_local("rawExn");
    let reverse = Ident::create_local("reverse");
    let eof = Ident::create_local("End_of_file");
    let cons = Lambda::prim(
        Primitive::Pmakeblock(
            0,
            TagInfo::Constructor {
                name: "::".to_string(),
                num_nonconst: 1,
                tag: 0,
                attrs: vec![],
            },
            Mutable::Immutable,
        ),
        vec![Lambda::var(next_acc.clone()), Lambda::var(acc.clone())],
        Location::none(),
    );

    let lam = Lambda::letrec(
        vec![(
            outer.clone(),
            Lambda::prim(
                Primitive::PjsFnMake(1),
                vec![Lambda::function_(
                    1,
                    vec![inc.clone()],
                    Lambda::letrec(
                        vec![(
                            loop_.clone(),
                            Lambda::prim(
                                Primitive::PjsFnMake(1),
                                vec![Lambda::function_(
                                    1,
                                    vec![acc.clone()],
                                    Lambda::LstaticCatch(
                                        Box::new(Lambda::LtryWith(
                                            Box::new(Lambda::LstaticRaise(
                                                -1,
                                                vec![Lambda::Lapply(Apply {
                                                    ap_func: Box::new(Lambda::var(
                                                        read.clone(),
                                                    )),
                                                    ap_args: vec![Lambda::var(inc.clone())],
                                                    ap_info: ApInfo {
                                                        loc: Location::none(),
                                                        inlined: InlineAttribute::Default,
                                                        status: ApplyStatus::Na,
                                                    },
                                                    ap_transformed_jsx: false,
                                                })],
                                            )),
                                            raw_exn.clone(),
                                            Box::new(Lambda::let_(
                                                LetKind::StrictOpt,
                                                exn.clone(),
                                                Lambda::prim(
                                                    Primitive::PwrapExn,
                                                    vec![Lambda::var(raw_exn.clone())],
                                                    Location::none(),
                                                ),
                                                Lambda::LstaticCatch(
                                                    Box::new(Lambda::if_(
                                                        Lambda::prim(
                                                            Primitive::Pstringcomp(
                                                                Comparison::Eq,
                                                            ),
                                                            vec![
                                                                Lambda::prim(
                                                                    Primitive::Pfield(
                                                                        0,
                                                                        crate::lambda::compat::FieldDbgInfo::Record {
                                                                            name: "RE_EXN_ID".to_string(),
                                                                            mutable_flag: crate::parser::ast::MutableFlag::Immutable,
                                                                        },
                                                                    ),
                                                                    vec![Lambda::var(exn.clone())],
                                                                    Location::none(),
                                                                ),
                                                                Lambda::var(eof.clone()),
                                                            ],
                                                            Location::none(),
                                                        ),
                                                        Lambda::Lapply(Apply {
                                                            ap_func: Box::new(Lambda::var(
                                                                reverse.clone(),
                                                            )),
                                                            ap_args: vec![Lambda::var(
                                                                acc.clone(),
                                                            )],
                                                            ap_info: ApInfo {
                                                                loc: Location::none(),
                                                                inlined:
                                                                    InlineAttribute::Default,
                                                                status: ApplyStatus::Na,
                                                            },
                                                            ap_transformed_jsx: false,
                                                        }),
                                                        Lambda::LstaticRaise(3, vec![]),
                                                    )),
                                                    (3, vec![]),
                                                    Box::new(Lambda::prim(
                                                        Primitive::Praise,
                                                        vec![Lambda::var(exn.clone())],
                                                        Location::none(),
                                                    )),
                                                ),
                                            )),
                                        )),
                                        (-1, vec![next_acc.clone()]),
                                        Box::new(Lambda::Lapply(Apply {
                                            ap_func: Box::new(Lambda::var(loop_.clone())),
                                            ap_args: vec![cons],
                                            ap_info: ApInfo {
                                                loc: Location::none(),
                                                inlined: InlineAttribute::Default,
                                                status: ApplyStatus::Na,
                                            },
                                            ap_transformed_jsx: false,
                                        })),
                                    ),
                                    FunctionAttribute::default(),
                                )],
                                Location::none(),
                            ),
                        )],
                        Lambda::Lapply(Apply {
                            ap_func: Box::new(Lambda::var(loop_.clone())),
                            ap_args: vec![Lambda::const_(Constant::int(0))],
                            ap_info: ApInfo {
                                loc: Location::none(),
                                inlined: InlineAttribute::Default,
                                status: ApplyStatus::Na,
                            },
                            ap_transformed_jsx: false,
                        }),
                    ),
                    FunctionAttribute::default(),
                )],
                Location::none(),
            ),
        )],
        Lambda::prim(
            Primitive::Pmakeblock(
                0,
                TagInfo::ModuleExport(vec![outer.clone()]),
                Mutable::Immutable,
            ),
            vec![Lambda::var(outer.clone())],
            Location::none(),
        ),
    );

    let deps = compiler.compile_deps_program(&lam);
    let rendered = print_deps_program(&deps, None);

    assert!(
        rendered.contains("while (true)"),
        "expected nested wrapped staticcatch tail recursion to emit a loop:\n{rendered}"
    );
    assert!(
        rendered.contains("continue;"),
        "expected nested wrapped staticcatch tail recursion to continue the loop:\n{rendered}"
    );
    assert!(
        !rendered.contains("return loop({") && !rendered.contains("return loop(nextAcc)"),
        "unexpected direct recursive return remained in the wrapped staticcatch path:\n{rendered}"
    );
}

#[test]
fn nested_static_raises_in_return_position_keep_the_return_continuation() {
    let mut compiler = LambdaCompiler::new();
    let cond_a = Ident::create_local("condA");
    let cond_b = Ident::create_local("condB");
    let block = compiler.compile_return_block(&Lambda::LstaticCatch(
        Box::new(Lambda::LstaticCatch(
            Box::new(Lambda::if_(
                Lambda::var(cond_a),
                Lambda::const_(Constant::int(1)),
                Lambda::static_raise(2, Vec::new()),
            )),
            (2, vec![]),
            Box::new(Lambda::if_(
                Lambda::var(cond_b),
                Lambda::const_(Constant::int(2)),
                Lambda::static_raise(1, Vec::new()),
            )),
        )),
        (1, vec![]),
        Box::new(Lambda::prim(
            Primitive::Praise,
            vec![Lambda::const_(Constant::string("boom"))],
            Location::none(),
        )),
    ));

    let rendered = print_block(&block);
    assert!(
        !rendered.contains("let ifres"),
        "nested static raises lost the return continuation and reintroduced ifres temps:\n{rendered}"
    );
    assert!(
        rendered.contains("if (condA)") && rendered.contains("return 1;"),
        "expected the first static-raise branch to stay in return position:\n{rendered}"
    );
    assert!(
        rendered.contains("if (condB)") && rendered.contains("return 2;"),
        "expected the nested handler to stay in return position:\n{rendered}"
    );
    assert!(
        rendered.contains("throw \"boom\";"),
        "expected the final handler to stay as the fallthrough throw:\n{rendered}"
    );
}

#[test]
fn block_finishes_output_ignores_switch_case_breaks() {
    let block = vec![Statement::new(StatementDesc::StringSwitch(
        Expression::bool(true),
        vec![StringClause {
            tag_type: crate::lambda::SwitchCaseTag::String("a".to_string()),
            clause: CaseClause {
                body: vec![
                    Statement::exp(Expression::string("a".to_string())),
                    Statement::break_(),
                ],
                should_break: false,
                comment: None,
            },
        }],
        Some(vec![Statement::throw(Expression::string(
            "boom".to_string(),
        ))]),
    ))];

    assert!(block_terminates(&block));
    assert!(!block_finishes_output(&block));
}

#[test]
fn lowers_expression_sequences_to_js_comma_expressions() {
    let mut compiler = LambdaCompiler::new();
    let callback = Ident::create_local("callback");
    let sequence = Lambda::Lsequence(
        Box::new(Lambda::Lapply(Apply {
            ap_func: Box::new(Lambda::var(callback.clone())),
            ap_args: vec![],
            ap_info: ApInfo {
                loc: Location::none(),
                inlined: InlineAttribute::Default,
                status: ApplyStatus::Na,
            },
            ap_transformed_jsx: false,
        })),
        Box::new(Lambda::const_(Constant::none())),
    );
    let program = compiler.compile_program(&Lambda::prim(
        Primitive::Pmakearray,
        vec![sequence],
        Location::none(),
    ));

    let [stmt] = program.block.as_slice() else {
        panic!("expected a single expression statement");
    };
    match &stmt.desc {
        StatementDesc::Exp(Expression {
            desc: ExpressionDesc::Array(items, _),
            ..
        }) => {
            let [item] = items.as_slice() else {
                panic!("expected a single array element");
            };
            match &item.desc {
                ExpressionDesc::Seq(first, second) => {
                    assert!(matches!(
                        first.as_ref(),
                        Expression {
                            desc: ExpressionDesc::Call(func, args, _),
                            ..
                        } if args.is_empty() && matches!(
                            func.as_ref(),
                            Expression {
                                desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                                ..
                            } if id.same(&callback)
                        )
                    ));
                    assert!(matches!(
                        second.as_ref(),
                        Expression {
                            desc: ExpressionDesc::Undefined { is_unit: false },
                            ..
                        }
                    ));
                }
                other => panic!("expected comma expression inside array, got {other:?}"),
            }
        }
        other => panic!("expected array literal output, got {other:?}"),
    }
}

#[test]
fn nested_effect_sequences_drop_intermediate_pignore_suffixes_when_appended_to_values() {
    let mut compiler = LambdaCompiler::new();
    let callback = Ident::create_local("callback");
    let value = Ident::create_local("value");
    let call = Lambda::Lapply(Apply {
        ap_func: Box::new(Lambda::var(callback.clone())),
        ap_args: vec![],
        ap_info: ApInfo {
            loc: Location::none(),
            inlined: InlineAttribute::Default,
            status: ApplyStatus::Na,
        },
        ap_transformed_jsx: false,
    });
    let sequence = Lambda::Lsequence(
        Box::new(Lambda::Lsequence(
            Box::new(call),
            Box::new(Lambda::prim(
                Primitive::Pignore,
                vec![Lambda::const_(Constant::int(3))],
                Location::none(),
            )),
        )),
        Box::new(Lambda::var(value.clone())),
    );

    let compiled = compiler.compile_expr(&sequence);

    assert!(
        compiled.prelude.is_empty(),
        "nested effect/value sequence unexpectedly produced prelude statements"
    );
    match &compiled.expr.desc {
        ExpressionDesc::Seq(first, second) => {
            assert!(matches!(
                first.as_ref(),
                Expression {
                    desc: ExpressionDesc::Call(func, args, _),
                    ..
                } if args.is_empty() && matches!(
                    func.as_ref(),
                    Expression {
                        desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                        ..
                    } if id.same(&callback)
                )
            ));
            assert!(matches!(
                second.as_ref(),
                Expression {
                    desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                    ..
                } if id.same(&value)
            ));
        }
        other => panic!("expected cleaned sequence expression, got {other:?}"),
    }
}

#[test]
fn int_switch_expressions_assign_branch_values_into_the_result_temp() {
    let mut compiler = LambdaCompiler::new();
    let scrutinee = Ident::create_local("scrutinee");
    let compiled = compiler.compile_expr(&Lambda::Lswitch(
        Box::new(Lambda::var(scrutinee.clone())),
        LambdaSwitch {
            sw_consts_full: true,
            sw_consts: vec![
                (0, Lambda::const_(Constant::int(1))),
                (1, Lambda::const_(Constant::int(2))),
            ],
            sw_blocks_full: false,
            sw_blocks: vec![],
            sw_failaction: Some(Box::new(Lambda::const_(Constant::int(3)))),
            sw_names: None,
        },
    ));

    let [declare, switch_stmt] = compiled.prelude.as_slice() else {
        panic!("expected a declaration and switch statement");
    };
    let StatementDesc::Variable(VariableDeclaration { ident: result, .. }) = &declare.desc
    else {
        panic!("expected the switch temporary declaration");
    };
    assert_eq!(result.name(), "tmp");
    let StatementDesc::IntSwitch(test, clauses, Some(default_block)) = &switch_stmt.desc else {
        panic!("expected an integer switch with a default block");
    };
    assert!(matches!(
        test,
        Expression {
            desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
            ..
        } if id.same(&scrutinee)
    ));
    assert!(matches!(
        compiled.expr,
        Expression {
            desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
            ..
        } if id.same(result)
    ));

    let expected_cases = [(0, 1_i32), (1, 2_i32)];
    for ((tag, clause), (expected_tag, expected_value)) in clauses.iter().zip(expected_cases) {
        assert_eq!(*tag, expected_tag);
        assert_switch_case_assigns_int_result(&clause.body, result, expected_value);
    }
    assert_switch_case_assigns_int_result(default_block, result, 3);
}

#[test]
fn string_switch_expressions_assign_branch_values_into_the_result_temp() {
    let mut compiler = LambdaCompiler::new();
    let scrutinee = Ident::create_local("scrutinee");
    let compiled = compiler.compile_expr(&Lambda::LstringSwitch(
        Box::new(Lambda::var(scrutinee.clone())),
        vec![
            ("linux".to_string(), Lambda::const_(Constant::int(1))),
            ("darwin".to_string(), Lambda::const_(Constant::int(2))),
        ],
        Some(Box::new(Lambda::const_(Constant::int(3)))),
    ));

    let [declare, switch_stmt] = compiled.prelude.as_slice() else {
        panic!("expected a declaration and string switch statement");
    };
    let StatementDesc::Variable(VariableDeclaration { ident: result, .. }) = &declare.desc
    else {
        panic!("expected the string switch temporary declaration");
    };
    assert_eq!(result.name(), "tmp");
    let StatementDesc::StringSwitch(test, clauses, Some(default_block)) = &switch_stmt.desc
    else {
        panic!("expected a string switch with a default block");
    };
    assert!(matches!(
        test,
        Expression {
            desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
            ..
        } if id.same(&scrutinee)
    ));
    assert!(matches!(
        compiled.expr,
        Expression {
            desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
            ..
        } if id.same(result)
    ));

    let expected_cases = [("linux", 1_i32), ("darwin", 2_i32)];
    for (clause, (expected_tag, expected_value)) in clauses.iter().zip(expected_cases) {
        assert_eq!(
            clause.tag_type,
            SwitchCaseTag::String(expected_tag.to_string())
        );
        assert_switch_case_assigns_int_result(&clause.clause.body, result, expected_value);
    }
    assert_switch_case_assigns_int_result(default_block, result, 3);
}

#[test]
fn int_switch_expressions_group_adjacent_equal_cases_and_drop_default_duplicates() {
    let mut compiler = LambdaCompiler::new();
    let scrutinee = Ident::create_local("scrutinee");
    let compiled = compiler.compile_expr(&Lambda::Lswitch(
        Box::new(Lambda::var(scrutinee.clone())),
        LambdaSwitch {
            sw_consts_full: false,
            sw_consts: vec![
                (0, Lambda::const_(Constant::int(1))),
                (1, Lambda::const_(Constant::int(1))),
                (2, Lambda::const_(Constant::int(2))),
            ],
            sw_blocks_full: false,
            sw_blocks: vec![],
            sw_failaction: Some(Box::new(Lambda::const_(Constant::int(2)))),
            sw_names: None,
        },
    ));

    let [declare, switch_stmt] = compiled.prelude.as_slice() else {
        panic!("expected a declaration and switch statement");
    };
    let StatementDesc::Variable(VariableDeclaration { ident: result, .. }) = &declare.desc
    else {
        panic!("expected the switch temporary declaration");
    };
    let StatementDesc::IntSwitch(test, clauses, Some(default_block)) = &switch_stmt.desc else {
        panic!("expected an integer switch with a default block");
    };
    assert!(matches!(
        test,
        Expression {
            desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
            ..
        } if id.same(&scrutinee)
    ));
    assert_eq!(
        clauses.len(),
        2,
        "expected the default-duplicate case to be filtered"
    );
    assert_eq!(clauses[0].0, 0);
    assert!(
        clauses[0].1.body.is_empty(),
        "expected the first grouped case to fall through"
    );
    assert!(!clauses[0].1.should_break);
    assert_eq!(clauses[1].0, 1);
    assert_switch_case_assigns_int_result(&clauses[1].1.body, result, 1);
    assert_switch_case_assigns_int_result(default_block, result, 2);
}

#[test]
fn int_switch_expressions_group_non_adjacent_equal_cases_like_ocaml_stable_group() {
    let mut compiler = LambdaCompiler::new();
    let scrutinee = Ident::create_local("scrutinee");
    let compiled = compiler.compile_expr(&Lambda::Lswitch(
        Box::new(Lambda::var(scrutinee.clone())),
        LambdaSwitch {
            sw_consts_full: true,
            sw_consts: vec![
                (0, Lambda::const_(Constant::int(2))),
                (1, Lambda::const_(Constant::int(1))),
                (2, Lambda::const_(Constant::int(2))),
            ],
            sw_blocks_full: false,
            sw_blocks: vec![],
            sw_failaction: None,
            sw_names: None,
        },
    ));

    let [declare, switch_stmt] = compiled.prelude.as_slice() else {
        panic!("expected a declaration and switch statement");
    };
    let StatementDesc::Variable(VariableDeclaration { ident: result, .. }) = &declare.desc
    else {
        panic!("expected the switch temporary declaration");
    };
    let StatementDesc::IntSwitch(_, clauses, None) = &switch_stmt.desc else {
        panic!("expected an exhaustive integer switch");
    };

    assert_eq!(
        clauses.len(),
        3,
        "expected OCaml-style stable grouping to keep all tags while reordering groups"
    );
    assert_eq!(clauses[0].0, 1);
    assert_switch_case_assigns_int_result(&clauses[0].1.body, result, 1);
    assert_eq!(clauses[1].0, 0);
    assert!(
        clauses[1].1.body.is_empty(),
        "expected the first equal-body case to fall through after stable grouping"
    );
    assert!(!clauses[1].1.should_break);
    assert_eq!(clauses[2].0, 2);
    assert_switch_case_assigns_int_result(&clauses[2].1.body, result, 2);
}

#[test]
fn runtime_test_return_bodies_share_trailing_return_outside_inner_test() {
    let mut compiler = LambdaCompiler::new();
    let value = Ident::create_local("value");
    let yes_seen = Ident::create_local("yes_seen");
    let no_seen = Ident::create_local("no_seen");
    let yes_branch = Lambda::seq(
        Lambda::Lassign(yes_seen.clone(), Box::new(Lambda::const_(Constant::int(1)))),
        Lambda::unit(),
    );
    let no_branch = Lambda::seq(
        Lambda::Lassign(no_seen.clone(), Box::new(Lambda::const_(Constant::int(0)))),
        Lambda::unit(),
    );
    let block = LambdaCompiler::normalize_runtime_test_return_body(
        compiler
            .compile_small_string_switch_return(
                Expression::var(value.clone()),
                &[(SwitchCaseTag::Int(10), &yes_branch)],
                Some(&no_branch),
                false,
            )
            .expect("expected the small switch fast path"),
    );

    let [ret] = block.as_slice() else {
        panic!("expected one conditional return");
    };
    let StatementDesc::Return(Expression {
        desc: ExpressionDesc::Cond(test, then_expr, else_expr),
        ..
    }) = &ret.desc
    else {
        panic!("expected the runtime-test body to use one conditional return");
    };
    assert!(matches!(
        &test.as_ref().desc,
        ExpressionDesc::Bin(op, left, right)
            if matches!(
                op,
                BinOp::EqEqEq | BinOp::NotEqEq
            ) && matches!(
                left.as_ref(),
                Expression {
                    desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                    ..
                } if id.same(&value)
            ) && matches!(
                right.as_ref(),
                Expression {
                    desc: ExpressionDesc::Number(Number::Int { i: 10, .. }),
                    ..
                }
            )
    ));
    assert!(matches!(
        &then_expr.as_ref().desc,
        ExpressionDesc::Seq(first, second)
            if matches!(
                first.as_ref(),
                Expression {
                    desc: ExpressionDesc::Bin(BinOp::Eq, _, _),
                    ..
                }
            ) && matches!(
                second.as_ref(),
                Expression {
                    desc: ExpressionDesc::Undefined { is_unit: true },
                    ..
                }
            )
    ));
    assert!(matches!(
        &else_expr.as_ref().desc,
        ExpressionDesc::Seq(first, second)
            if matches!(
                first.as_ref(),
                Expression {
                    desc: ExpressionDesc::Bin(BinOp::Eq, _, _),
                    ..
                }
            ) && matches!(
                second.as_ref(),
                Expression {
                    desc: ExpressionDesc::Undefined { is_unit: true },
                    ..
                }
            )
    ));
}

#[test]
fn string_switch_effects_group_adjacent_equal_cases_and_drop_default_duplicates() {
    let mut compiler = LambdaCompiler::new();
    let scrutinee = Ident::create_local("scrutinee");
    let captured = Ident::create_local("captured");
    let block = compiler.compile_effect_block(&Lambda::LstringSwitch(
        Box::new(Lambda::var(scrutinee.clone())),
        vec![
            (
                "A".to_string(),
                Lambda::Lassign(captured.clone(), Box::new(Lambda::const_(Constant::int(1)))),
            ),
            (
                "B".to_string(),
                Lambda::Lassign(captured.clone(), Box::new(Lambda::const_(Constant::int(1)))),
            ),
            (
                "C".to_string(),
                Lambda::Lassign(captured.clone(), Box::new(Lambda::const_(Constant::int(2)))),
            ),
        ],
        Some(Box::new(Lambda::Lassign(
            captured.clone(),
            Box::new(Lambda::const_(Constant::int(2))),
        ))),
    ));

    let [switch_stmt] = block.as_slice() else {
        panic!("expected a single string switch");
    };
    let StatementDesc::StringSwitch(test, clauses, Some(default_block)) = &switch_stmt.desc
    else {
        panic!("expected a string switch with a default block");
    };
    assert!(matches!(
        test,
        Expression {
            desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
            ..
        } if id.same(&scrutinee)
    ));
    assert_eq!(
        clauses.len(),
        2,
        "expected the default-duplicate case to be filtered"
    );
    assert_eq!(clauses[0].tag_type, SwitchCaseTag::String("A".to_string()));
    assert!(
        clauses[0].clause.body.is_empty(),
        "expected the first grouped case to fall through"
    );
    assert!(!clauses[0].clause.should_break);
    assert_eq!(clauses[1].tag_type, SwitchCaseTag::String("B".to_string()));
    assert!(clauses[1].clause.should_break);
    assert_effect_assignment_writes_int(&clauses[1].clause.body, &captured, 1);
    assert_effect_assignment_writes_int(default_block, &captured, 2);
}

#[test]
fn string_switch_effects_group_non_adjacent_equal_cases_like_ocaml_stable_group() {
    let mut compiler = LambdaCompiler::new();
    let scrutinee = Ident::create_local("scrutinee");
    let captured = Ident::create_local("captured");
    let block = compiler.compile_effect_block(&Lambda::LstringSwitch(
        Box::new(Lambda::var(scrutinee.clone())),
        vec![
            (
                "A".to_string(),
                Lambda::Lassign(captured.clone(), Box::new(Lambda::const_(Constant::int(2)))),
            ),
            (
                "B".to_string(),
                Lambda::Lassign(captured.clone(), Box::new(Lambda::const_(Constant::int(1)))),
            ),
            (
                "C".to_string(),
                Lambda::Lassign(captured.clone(), Box::new(Lambda::const_(Constant::int(2)))),
            ),
        ],
        None,
    ));

    let [switch_stmt] = block.as_slice() else {
        panic!("expected a single string switch");
    };
    let StatementDesc::StringSwitch(_, clauses, None) = &switch_stmt.desc else {
        panic!("expected an exhaustive string switch");
    };

    assert_eq!(clauses.len(), 3);
    assert_eq!(clauses[0].tag_type, SwitchCaseTag::String("B".to_string()));
    assert_effect_assignment_writes_int(&clauses[0].clause.body, &captured, 1);
    assert_eq!(clauses[1].tag_type, SwitchCaseTag::String("A".to_string()));
    assert!(
        clauses[1].clause.body.is_empty(),
        "expected the first equal-body case to fall through after stable grouping"
    );
    assert!(!clauses[1].clause.should_break);
    assert_eq!(clauses[2].tag_type, SwitchCaseTag::String("C".to_string()));
    assert_effect_assignment_writes_int(&clauses[2].clause.body, &captured, 2);
}

#[test]
fn fallthrough_handlers_do_not_reorder_grouped_named_string_return_cases() {
    let mut compiler = LambdaCompiler::new();
    let scrutinee = Ident::create_local("scrutinee");
    let case_a = Lambda::const_(Constant::int(2));
    let case_b = Lambda::const_(Constant::int(1));
    let case_c = Lambda::const_(Constant::int(2));
    let cases = vec![
        (SwitchCaseTag::String("A".to_string()), &case_a),
        (SwitchCaseTag::String("B".to_string()), &case_b),
        (SwitchCaseTag::String("C".to_string()), &case_c),
    ];

    let block = compiler.with_fallthrough_return_handler(1, &[], |this| {
        this.compile_named_string_switch_return(
            Expression::var(scrutinee.clone()),
            &cases,
            None,
            true,
        )
    });

    let [switch_stmt] = block.as_slice() else {
        panic!("expected a single string switch");
    };
    let StatementDesc::StringSwitch(test, clauses, None) = &switch_stmt.desc else {
        panic!("expected an exhaustive string switch");
    };
    assert!(matches!(
        test,
        Expression {
            desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
            ..
        } if id.same(&scrutinee)
    ));

    assert_eq!(clauses.len(), 3);
    assert_eq!(clauses[0].tag_type, SwitchCaseTag::String("B".to_string()));
    assert_switch_case_returns_int_result(&clauses[0].clause.body, 1);
    assert_eq!(clauses[1].tag_type, SwitchCaseTag::String("A".to_string()));
    assert!(clauses[1].clause.body.is_empty());
    assert_eq!(clauses[2].tag_type, SwitchCaseTag::String("C".to_string()));
    assert_switch_case_returns_int_result(&clauses[2].clause.body, 2);
}

#[test]
fn fallthrough_handlers_do_not_reorder_grouped_string_switch_return_blocks() {
    let mut compiler = LambdaCompiler::new();
    let scrutinee = Ident::create_local("scrutinee");
    let block = compiler.with_fallthrough_return_handler(1, &[], |this| {
        this.compile_string_switch_return_block(
            &Lambda::var(scrutinee.clone()),
            &[
                ("A".to_string(), Lambda::const_(Constant::int(2))),
                ("B".to_string(), Lambda::const_(Constant::int(1))),
                ("C".to_string(), Lambda::const_(Constant::int(2))),
            ],
            None,
        )
    });

    let [switch_stmt] = block.as_slice() else {
        panic!("expected a single string switch");
    };
    let StatementDesc::StringSwitch(test, clauses, None) = &switch_stmt.desc else {
        panic!("expected an exhaustive string switch");
    };
    assert!(matches!(
        test,
        Expression {
            desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
            ..
        } if id.same(&scrutinee)
    ));

    assert_eq!(clauses.len(), 3);
    assert_eq!(clauses[0].tag_type, SwitchCaseTag::String("B".to_string()));
    assert_switch_case_returns_int_result(&clauses[0].clause.body, 1);
    assert_eq!(clauses[1].tag_type, SwitchCaseTag::String("A".to_string()));
    assert!(clauses[1].clause.body.is_empty());
    assert_eq!(clauses[2].tag_type, SwitchCaseTag::String("C".to_string()));
    assert_switch_case_returns_int_result(&clauses[2].clause.body, 2);
}

#[test]
fn let_bindings_lower_string_switches_directly_into_the_declared_binding() {
    let mut compiler = LambdaCompiler::new();
    let version = Ident::create_local("version");
    let scrutinee = Ident::create_local("platform");
    let program = compiler.compile_program(&Lambda::Llet(
        LetKind::Strict,
        version.clone(),
        Box::new(Lambda::LstringSwitch(
            Box::new(Lambda::var(scrutinee.clone())),
            vec![
                ("linux".to_string(), Lambda::const_(Constant::int(1))),
                ("darwin".to_string(), Lambda::const_(Constant::int(2))),
            ],
            Some(Box::new(Lambda::const_(Constant::int(3)))),
        )),
        Box::new(Lambda::var(version.clone())),
    ));

    let [declare, switch_stmt] = program.block.as_slice() else {
        panic!("expected a declaration followed by a string switch");
    };
    let StatementDesc::Variable(VariableDeclaration {
        ident, value: None, ..
    }) = &declare.desc
    else {
        panic!("expected an uninitialized binding declaration");
    };
    assert!(ident.same(&version));

    let StatementDesc::StringSwitch(test, clauses, Some(default_block)) = &switch_stmt.desc
    else {
        panic!("expected a direct string switch statement");
    };
    assert!(matches!(
        test,
        Expression {
            desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
            ..
        } if id.same(&scrutinee)
    ));

    let expected_cases = [("linux", 1_i32), ("darwin", 2_i32)];
    for (clause, (expected_tag, expected_value)) in clauses.iter().zip(expected_cases) {
        assert_eq!(
            clause.tag_type,
            SwitchCaseTag::String(expected_tag.to_string())
        );
        assert_switch_case_assigns_int_result(&clause.clause.body, &version, expected_value);
    }
    assert_switch_default_assigns_int_result(default_block, &version, 3);
}

#[test]
fn single_case_string_switches_with_default_lower_to_conditional_assignment() {
    let mut compiler = LambdaCompiler::new();
    let scrutinee = Ident::create_local("platform");
    let compiled = compiler.compile_expr(&Lambda::LstringSwitch(
        Box::new(Lambda::var(scrutinee.clone())),
        vec![("linux".to_string(), Lambda::const_(Constant::int(1)))],
        Some(Box::new(Lambda::const_(Constant::int(2)))),
    ));

    let [declare, assign] = compiled.prelude.as_slice() else {
        panic!("expected a declaration followed by one assignment");
    };
    let StatementDesc::Variable(VariableDeclaration { ident: result, .. }) = &declare.desc
    else {
        panic!("expected the string switch temporary declaration");
    };
    let StatementDesc::Exp(Expression {
        desc: ExpressionDesc::Bin(BinOp::Eq, left, right),
        ..
    }) = &assign.desc
    else {
        panic!("expected the lowered switch to assign into the result temp");
    };
    assert!(matches!(
        left.as_ref(),
        Expression {
            desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
            ..
        } if id.same(result)
    ));
    let ExpressionDesc::Cond(cond, then_expr, else_expr) = &right.as_ref().desc else {
        panic!("expected the assignment RHS to be a conditional expression");
    };
    assert_string_equality_check(cond, Some(&scrutinee), None, "linux");
    assert_int_expr(then_expr, 1);
    assert_int_expr(else_expr, 2);
}

#[test]
fn staticcatch_wrapped_string_switches_use_the_handler_as_the_default_value() {
    let mut compiler = LambdaCompiler::new();
    let version = Ident::create_local("version");
    let scrutinee = Ident::create_local("platform");
    let program = compiler.compile_program(&Lambda::Llet(
        LetKind::Strict,
        version.clone(),
        Box::new(Lambda::LstaticCatch(
            Box::new(Lambda::LstringSwitch(
                Box::new(Lambda::var(scrutinee.clone())),
                vec![
                    ("linux".to_string(), Lambda::const_(Constant::int(1))),
                    ("darwin".to_string(), Lambda::const_(Constant::int(2))),
                ],
                Some(Box::new(Lambda::static_raise(1, Vec::new()))),
            )),
            (1, vec![]),
            Box::new(Lambda::const_(Constant::int(3))),
        )),
        Box::new(Lambda::var(version.clone())),
    ));

    let [declare, switch_stmt] = program.block.as_slice() else {
        panic!("expected a declaration followed by a string switch");
    };
    let StatementDesc::Variable(VariableDeclaration {
        ident, value: None, ..
    }) = &declare.desc
    else {
        panic!("expected an uninitialized binding declaration");
    };
    assert!(ident.same(&version));

    let StatementDesc::StringSwitch(_, clauses, Some(default_block)) = &switch_stmt.desc else {
        panic!("expected a direct string switch statement");
    };
    let expected_cases = [("linux", 1_i32), ("darwin", 2_i32)];
    for (clause, (expected_tag, expected_value)) in clauses.iter().zip(expected_cases) {
        assert_eq!(
            clause.tag_type,
            SwitchCaseTag::String(expected_tag.to_string())
        );
        assert_switch_case_assigns_int_result(&clause.clause.body, &version, expected_value);
    }
    assert_switch_default_assigns_int_result(default_block, &version, 3);
}

#[test]
fn staticcatch_wrapped_int_return_switches_omit_empty_default_arms() {
    let mut compiler = LambdaCompiler::new();
    let action = Ident::create_local("action");
    let block = compiler.compile_return_block(&Lambda::LstaticCatch(
        Box::new(Lambda::LstaticCatch(
            Box::new(Lambda::Lswitch(
                Box::new(Lambda::var(action.clone())),
                LambdaSwitch {
                    sw_consts_full: false,
                    sw_consts: vec![
                        (1, Lambda::const_(Constant::int(10))),
                        (2, Lambda::const_(Constant::int(20))),
                    ],
                    sw_blocks_full: true,
                    sw_blocks: vec![],
                    sw_failaction: Some(Box::new(Lambda::static_raise(2, Vec::new()))),
                    sw_names: None,
                },
            )),
            (2, vec![]),
            Box::new(Lambda::static_raise(1, Vec::new())),
        )),
        (1, vec![]),
        Box::new(Lambda::const_(Constant::int(30))),
    ));

    let [switch_stmt, handler_return] = block.as_slice() else {
        panic!("expected a switch followed by the outer handler return");
    };
    let StatementDesc::IntSwitch(test, clauses, None) = &switch_stmt.desc else {
        panic!("expected the fallthrough default to stay outside the switch");
    };
    assert!(matches!(
        test,
        Expression {
            desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
            ..
        } if id.same(&action)
    ));

    let expected_cases = [(1, 10_i32), (2, 20_i32)];
    for ((tag, clause), (expected_tag, expected_value)) in clauses.iter().zip(expected_cases) {
        assert_eq!(*tag, expected_tag);
        assert_switch_case_returns_int_result(&clause.body, expected_value);
    }
    match &handler_return.desc {
        StatementDesc::Return(expr) => assert_int_expr(expr, 30),
        other => panic!("expected the outer handler return, got {other:?}"),
    }
}

#[test]
fn partial_int_return_switch_cases_break_to_shared_handler_like_test_set() {
    let mut compiler = LambdaCompiler::new();
    let action = Ident::create_local("action");
    let cond = Ident::create_local("cond");
    let block = compiler.compile_return_block(&Lambda::LstaticCatch(
        Box::new(Lambda::Lswitch(
            Box::new(Lambda::var(action.clone())),
            LambdaSwitch {
                sw_consts_full: false,
                sw_consts: vec![
                    (
                        1,
                        Lambda::if_(
                            Lambda::var(cond.clone()),
                            Lambda::const_(Constant::int(10)),
                            Lambda::static_raise(1, Vec::new()),
                        ),
                    ),
                    (2, Lambda::const_(Constant::int(20))),
                ],
                sw_blocks_full: true,
                sw_blocks: vec![],
                sw_failaction: None,
                sw_names: None,
            },
        )),
        (1, vec![]),
        Box::new(Lambda::const_(Constant::int(30))),
    ));

    let [switch_stmt, handler_return] = block.as_slice() else {
        panic!("expected a switch followed by the shared handler return");
    };
    let StatementDesc::IntSwitch(test, clauses, None) = &switch_stmt.desc else {
        panic!("expected the shared handler to stay outside the switch");
    };
    assert!(matches!(
        test,
        Expression {
            desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
            ..
        } if id.same(&action)
    ));
    assert_eq!(clauses.len(), 2);
    assert_eq!(clauses[0].0, 1);
    assert!(
        clauses[0].1.should_break,
        "expected the partial case to break to the shared handler"
    );
    assert_eq!(clauses[1].0, 2);
    assert_switch_case_returns_int_result(&clauses[1].1.body, 20);
    assert!(
        !clauses[1].1.should_break,
        "expected the fully returning case to omit break"
    );

    let rendered = print_block(&block);
    assert_eq!(
        rendered,
        "switch (action) {\n  case 1 :\n    if (cond) {\n      return 10;\n    }\n    break;\n  case 2 :\n    return 20;\n}\n\nreturn 30;"
    );

    match &handler_return.desc {
        StatementDesc::Return(expr) => assert_int_expr(expr, 30),
        other => panic!("expected the shared handler return, got {other:?}"),
    }
}

#[test]
fn direct_return_switch_cases_with_shared_plain_handlers_fall_through_like_ocaml() {
    let mut compiler = LambdaCompiler::new();
    let action = Ident::create_local("action");
    let block = compiler.compile_return_block(&Lambda::LstaticCatch(
        Box::new(Lambda::Lswitch(
            Box::new(Lambda::var(action.clone())),
            LambdaSwitch {
                sw_consts_full: false,
                sw_consts: vec![
                    (1, Lambda::static_raise(1, Vec::new())),
                    (2, Lambda::static_raise(1, Vec::new())),
                    (3, Lambda::const_(Constant::int(40))),
                ],
                sw_blocks_full: true,
                sw_blocks: vec![],
                sw_failaction: None,
                sw_names: None,
            },
        )),
        (1, vec![]),
        Box::new(Lambda::const_(Constant::int(30))),
    ));

    let [switch_stmt, handler_return] = block.as_slice() else {
        panic!("expected the shared plain handler to fall through after the switch");
    };
    let StatementDesc::IntSwitch(test, clauses, None) = &switch_stmt.desc else {
        panic!("expected the shared plain handler to leave the switch default empty");
    };
    assert!(matches!(
        test,
        Expression {
            desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
            ..
        } if id.same(&action)
    ));
    assert_eq!(clauses.len(), 3);
    assert_eq!(
        print_block(&block),
        "switch (action) {\n  case 3 :\n    return 40;\n  case 1 :\n  case 2 :\n}\n\nreturn 30;"
    );
    match &handler_return.desc {
        StatementDesc::Return(expr) => assert_int_expr(expr, 30),
        other => panic!("expected the shared plain handler return, got {other:?}"),
    }
}

#[test]
fn staticcatch_wrapped_multi_case_string_return_switches_omit_empty_default_arms() {
    let mut compiler = LambdaCompiler::new();
    let platform = Ident::create_local("platform");
    let block = compiler.compile_return_block(&Lambda::LstaticCatch(
        Box::new(Lambda::LstaticCatch(
            Box::new(Lambda::LstringSwitch(
                Box::new(Lambda::var(platform.clone())),
                vec![
                    ("linux".to_string(), Lambda::const_(Constant::int(1))),
                    ("darwin".to_string(), Lambda::const_(Constant::int(2))),
                ],
                Some(Box::new(Lambda::static_raise(2, Vec::new()))),
            )),
            (2, vec![]),
            Box::new(Lambda::static_raise(1, Vec::new())),
        )),
        (1, vec![]),
        Box::new(Lambda::const_(Constant::int(3))),
    ));

    let [switch_stmt, handler_return] = block.as_slice() else {
        panic!("expected a switch followed by the outer handler return");
    };
    let StatementDesc::StringSwitch(test, clauses, None) = &switch_stmt.desc else {
        panic!("expected the fallthrough default to stay outside the string switch");
    };
    assert!(matches!(
        test,
        Expression {
            desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
            ..
        } if id.same(&platform)
    ));

    let expected_cases = [("linux", 1_i32), ("darwin", 2_i32)];
    for (clause, (expected_tag, expected_value)) in clauses.iter().zip(expected_cases) {
        assert_eq!(
            clause.tag_type,
            SwitchCaseTag::String(expected_tag.to_string())
        );
        assert_switch_case_returns_int_result(&clause.clause.body, expected_value);
    }
    match &handler_return.desc {
        StatementDesc::Return(expr) => assert_int_expr(expr, 3),
        other => panic!("expected the outer handler return, got {other:?}"),
    }
}

#[test]
fn staticcatch_wrapped_int_return_switches_keep_single_handlers_as_default_arms() {
    let mut compiler = LambdaCompiler::new();
    let action = Ident::create_local("action");
    let block = compiler.compile_return_block(&Lambda::LstaticCatch(
        Box::new(Lambda::Lswitch(
            Box::new(Lambda::var(action.clone())),
            LambdaSwitch {
                sw_consts_full: false,
                sw_consts: vec![
                    (1, Lambda::const_(Constant::int(10))),
                    (2, Lambda::const_(Constant::int(20))),
                ],
                sw_blocks_full: true,
                sw_blocks: vec![],
                sw_failaction: Some(Box::new(Lambda::static_raise(2, Vec::new()))),
                sw_names: None,
            },
        )),
        (2, vec![]),
        Box::new(Lambda::const_(Constant::int(30))),
    ));

    let [switch_stmt] = block.as_slice() else {
        panic!("expected a single switch statement");
    };
    let StatementDesc::IntSwitch(test, clauses, Some(default_block)) = &switch_stmt.desc else {
        panic!("expected the single handler to stay as the default arm");
    };
    assert!(matches!(
        test,
        Expression {
            desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
            ..
        } if id.same(&action)
    ));

    let expected_cases = [(1, 10_i32), (2, 20_i32)];
    for ((tag, clause), (expected_tag, expected_value)) in clauses.iter().zip(expected_cases) {
        assert_eq!(*tag, expected_tag);
        assert_switch_case_returns_int_result(&clause.body, expected_value);
    }
    let [default_return] = default_block.as_slice() else {
        panic!("expected one default return statement");
    };
    match &default_return.desc {
        StatementDesc::Return(expr) => assert_int_expr(expr, 30),
        other => panic!("expected the default return, got {other:?}"),
    }
}

#[test]
fn staticcatch_wrapped_string_return_switches_keep_single_handlers_as_default_arms() {
    let mut compiler = LambdaCompiler::new();
    let platform = Ident::create_local("platform");
    let block = compiler.compile_return_block(&Lambda::LstaticCatch(
        Box::new(Lambda::LstringSwitch(
            Box::new(Lambda::var(platform.clone())),
            vec![
                ("linux".to_string(), Lambda::const_(Constant::int(1))),
                ("darwin".to_string(), Lambda::const_(Constant::int(2))),
            ],
            Some(Box::new(Lambda::static_raise(2, Vec::new()))),
        )),
        (2, vec![]),
        Box::new(Lambda::const_(Constant::int(3))),
    ));

    let [switch_stmt] = block.as_slice() else {
        panic!("expected a single string switch statement");
    };
    let StatementDesc::StringSwitch(test, clauses, Some(default_block)) = &switch_stmt.desc
    else {
        panic!("expected the single handler to stay as the string-switch default arm");
    };
    assert!(matches!(
        test,
        Expression {
            desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
            ..
        } if id.same(&platform)
    ));

    let expected_cases = [("linux", 1_i32), ("darwin", 2_i32)];
    for (clause, (expected_tag, expected_value)) in clauses.iter().zip(expected_cases) {
        assert_eq!(
            clause.tag_type,
            SwitchCaseTag::String(expected_tag.to_string())
        );
        assert_switch_case_returns_int_result(&clause.clause.body, expected_value);
    }
    let [default_return] = default_block.as_slice() else {
        panic!("expected one default return statement");
    };
    match &default_return.desc {
        StatementDesc::Return(expr) => assert_int_expr(expr, 3),
        other => panic!("expected the default return, got {other:?}"),
    }
}

#[test]
fn nested_staticcatch_binding_handlers_that_raise_outward_avoid_exit_temps() {
    let mut compiler = LambdaCompiler::new();
    let cond = Ident::create_local("cond");
    let carried = Ident::create_local("carried");
    let block = compiler.compile_return_block(&Lambda::LstaticCatch(
        Box::new(Lambda::LstaticCatch(
            Box::new(Lambda::if_(
                Lambda::var(cond.clone()),
                Lambda::const_(Constant::int(0)),
                Lambda::static_raise(2, Vec::new()),
            )),
            (2, vec![]),
            Box::new(Lambda::static_raise(
                1,
                vec![Lambda::const_(Constant::int(1))],
            )),
        )),
        (1, vec![carried.clone()]),
        Box::new(Lambda::var(carried.clone())),
    ));

    let rendered = print_block(&block);
    assert!(
        !rendered.contains("let exit ="),
        "nested binding handlers reintroduced an explicit staticcatch jump temp:\n{rendered}"
    );
    assert!(
        !rendered.contains("if (exit ==="),
        "nested binding handlers still guard the handler behind an exit sentinel:\n{rendered}"
    );
    assert!(
        rendered.contains("return cond ? 0 : 1;")
            || (rendered.contains("if (cond)")
                && rendered.contains("return 0;")
                && rendered.contains("return 1;")),
        "expected the outward handler raise to lower directly instead of through an exit temp:\n{rendered}"
    );
}

#[test]
fn nested_staticcatch_switch_forwarders_to_outer_handlers_avoid_exit_temps_like_gpr_3609() {
    let mut compiler = LambdaCompiler::new();
    let state = Ident::create_local("state");
    let int_value = Ident::create_local("intValue");
    let int_func = Ident::create_local("intFunc");
    let int_param = Ident::create_local("intParam");
    let block = compiler.compile_return_block(&Lambda::LstaticCatch(
        Box::new(Lambda::LstaticCatch(
            Box::new(Lambda::Lswitch(
                Box::new(Lambda::var(state.clone())),
                LambdaSwitch {
                    sw_consts_full: true,
                    sw_consts: vec![(0, Lambda::const_(Constant::int(0)))],
                    sw_blocks_full: true,
                    sw_blocks: vec![
                        (0, Lambda::static_raise(2, Vec::new())),
                        (1, Lambda::static_raise(2, Vec::new())),
                    ],
                    sw_failaction: None,
                    sw_names: Some(SwitchNames {
                        consts: vec![crate::lambda::SwitchTag::named("Empty")],
                        blocks: vec![
                            crate::lambda::SwitchBlock::named("Int1"),
                            crate::lambda::SwitchBlock::named("Int2"),
                        ],
                    }),
                },
            )),
            (2, vec![]),
            Box::new(Lambda::let_(
                LetKind::Alias,
                int_value.clone(),
                Lambda::prim(
                    Primitive::Pfield(0, FieldDbgInfo::Variant),
                    vec![Lambda::var(state.clone())],
                    Location::none(),
                ),
                Lambda::static_raise(1, vec![Lambda::var(int_value.clone())]),
            )),
        )),
        (1, vec![int_value.clone()]),
        Box::new(Lambda::let_(
            LetKind::Strict,
            int_func.clone(),
            Lambda::prim(
                Primitive::PjsFnMake(1),
                vec![Lambda::function_(
                    1,
                    vec![int_param.clone()],
                    Lambda::prim(
                        Primitive::Paddint,
                        vec![Lambda::var(int_param), Lambda::var(int_value.clone())],
                        Location::none(),
                    ),
                    FunctionAttribute::default(),
                )],
                Location::none(),
            ),
            Lambda::apply(
                Lambda::var(int_func),
                vec![Lambda::const_(Constant::int(0))],
                ApInfo {
                    loc: Location::none(),
                    inlined: InlineAttribute::Default,
                    status: ApplyStatus::Uncurry,
                },
                false,
            ),
        )),
    ));

    let rendered = print_block(&block);
    assert!(
        !rendered.contains("let exit ="),
        "gpr_3609-style nested switch forwarding reintroduced an exit temp:\n{rendered}"
    );
    assert!(
        !rendered.contains("if (exit ==="),
        "gpr_3609-style nested switch forwarding still guards the shared tail behind an exit sentinel:\n{rendered}"
    );
}

#[test]
fn nested_staticcatch_switch_forwarders_keep_collapsed_shared_return_like_gpr_3609() {
    let mut compiler = LambdaCompiler::new();
    let state = Ident::create_local("state");
    let int_value = Ident::create_local("intValue");
    let int_func = Ident::create_local("intFunc");
    let int_param = Ident::create_local("intParam");
    let block = compiler.compile_return_block(&Lambda::LstaticCatch(
        Box::new(Lambda::LstaticCatch(
            Box::new(Lambda::Lswitch(
                Box::new(Lambda::var(state.clone())),
                LambdaSwitch {
                    sw_consts_full: true,
                    sw_consts: vec![(0, Lambda::const_(Constant::int(0)))],
                    sw_blocks_full: true,
                    sw_blocks: vec![
                        (0, Lambda::static_raise(2, Vec::new())),
                        (1, Lambda::static_raise(2, Vec::new())),
                    ],
                    sw_failaction: None,
                    sw_names: Some(SwitchNames {
                        consts: vec![crate::lambda::SwitchTag::named("Empty")],
                        blocks: vec![
                            crate::lambda::SwitchBlock::named("Int1"),
                            crate::lambda::SwitchBlock::named("Int2"),
                        ],
                    }),
                },
            )),
            (2, vec![]),
            Box::new(Lambda::let_(
                LetKind::Alias,
                int_value.clone(),
                Lambda::prim(
                    Primitive::Pfield(0, FieldDbgInfo::Variant),
                    vec![Lambda::var(state.clone())],
                    Location::none(),
                ),
                Lambda::static_raise(1, vec![Lambda::var(int_value.clone())]),
            )),
        )),
        (1, vec![int_value.clone()]),
        Box::new(Lambda::let_(
            LetKind::Strict,
            int_func.clone(),
            Lambda::prim(
                Primitive::PjsFnMake(1),
                vec![Lambda::function_(
                    1,
                    vec![int_param.clone()],
                    Lambda::prim(
                        Primitive::Paddint,
                        vec![Lambda::var(int_param), Lambda::var(int_value.clone())],
                        Location::none(),
                    ),
                    FunctionAttribute::default(),
                )],
                Location::none(),
            ),
            Lambda::apply(
                Lambda::var(int_func),
                vec![Lambda::const_(Constant::int(0))],
                ApInfo {
                    loc: Location::none(),
                    inlined: InlineAttribute::Default,
                    status: ApplyStatus::Uncurry,
                },
                false,
            ),
        )),
    ));

    let rendered = print_block(&block);
    assert!(
        rendered.contains("if (typeof state !== \"object\") {"),
        "expected the outer object split to stay materialized:\n{rendered}"
    );
    assert!(
        !rendered.contains("state.TAG ==="),
        "gpr_3609-style shared payload handlers should not reintroduce a tag split:\n{rendered}"
    );
    assert!(
        rendered.contains("return intFunc(0);"),
        "expected the shared payload tail to stay forwarded through the outer handler:\n{rendered}"
    );
}

#[test]
fn unit_return_staticcatch_bindings_without_handler_exits_share_fallthrough_tail() {
    let mut compiler = LambdaCompiler::new();
    let cond1 = Ident::create_local("cond1");
    let cond2 = Ident::create_local("cond2");
    let first = Ident::create_local("first");
    let second = Ident::create_local("second");
    let carried = Ident::create_local("carried");
    let seen = Ident::create_local("seen");
    let block = compiler.with_return_unit_context(true, |compiler| {
        compiler.compile_return_block(&Lambda::LstaticCatch(
            Box::new(Lambda::if_(
                Lambda::var(cond1.clone()),
                Lambda::static_raise(1, vec![Lambda::var(first.clone())]),
                Lambda::LifThenElse(
                    Box::new(Lambda::var(cond2.clone())),
                    Box::new(Lambda::static_raise(1, vec![Lambda::var(second.clone())])),
                    Box::new(Lambda::const_(Constant::JsUndefined { is_unit: true })),
                ),
            )),
            (1, vec![carried.clone()]),
            Box::new(Lambda::Lsequence(
                Box::new(Lambda::Lassign(
                    seen.clone(),
                    Box::new(Lambda::var(carried.clone())),
                )),
                Box::new(Lambda::const_(Constant::JsUndefined { is_unit: true })),
            )),
        ))
    });

    let rendered = print_block(&block);
    assert!(
        !rendered.contains("let exit ="),
        "single-handler unit-return staticcatch bindings reintroduced an exit temp:\n{rendered}"
    );
    assert!(
        rendered.contains("let carried;"),
        "expected the carried binding to stay declared ahead of the shared tail:\n{rendered}"
    );
    assert_eq!(
        rendered.matches("seen = carried;").count(),
        1,
        "expected the handler tail to stay shared exactly once:\n{rendered}"
    );
    assert!(
        rendered.contains("return;"),
        "expected the non-matching branch to keep its early return:\n{rendered}"
    );
}

#[test]
fn return_staticcatchs_share_nontrivial_handlers_across_multiple_exit_sites() {
    let mut compiler = LambdaCompiler::new();
    let cond = Ident::create_local("cond");
    let kind = Ident::create_local("kind");
    let block = compiler.compile_return_block(&Lambda::LstaticCatch(
        Box::new(Lambda::LstaticCatch(
            Box::new(Lambda::if_(
                Lambda::var(cond.clone()),
                Lambda::static_raise(2, Vec::new()),
                Lambda::LstringSwitch(
                    Box::new(Lambda::var(kind.clone())),
                    vec![("e".to_string(), Lambda::const_(Constant::int(4)))],
                    Some(Box::new(Lambda::static_raise(2, Vec::new()))),
                ),
            )),
            (2, vec![]),
            Box::new(Lambda::LstringSwitch(
                Box::new(Lambda::var(kind.clone())),
                vec![("f".to_string(), Lambda::const_(Constant::int(5)))],
                Some(Box::new(Lambda::static_raise(1, Vec::new()))),
            )),
        )),
        (1, vec![]),
        Box::new(Lambda::const_(Constant::int(6))),
    ));

    let rendered = print_block(&block);
    assert!(
        rendered.contains("let exit = 0;"),
        "expected repeated exits to share the handler behind an exit temp:\n{rendered}"
    );
    assert!(
        rendered.contains("if (exit ==="),
        "expected the shared handler to stay after an explicit exit test:\n{rendered}"
    );
    assert_eq!(
        rendered.matches("=== \"f\"").count(),
        1,
        "expected the nontrivial handler to be emitted once:\n{rendered}"
    );
}

#[test]
fn nested_return_handler_staticcatchs_lower_without_forcing_outer_exit_temp() {
    let mut compiler = LambdaCompiler::new();
    let first = Ident::create_local("first");
    let second = Ident::create_local("second");
    let block = compiler.compile_return_block(&Lambda::LstaticCatch(
        Box::new(Lambda::if_(
            Lambda::var(first.clone()),
            Lambda::const_(Constant::int(0)),
            Lambda::static_raise(1, Vec::new()),
        )),
        (1, vec![]),
        Box::new(Lambda::LstaticCatch(
            Box::new(Lambda::if_(
                Lambda::var(second.clone()),
                Lambda::const_(Constant::int(1)),
                Lambda::static_raise(2, Vec::new()),
            )),
            (2, vec![]),
            Box::new(Lambda::const_(Constant::int(2))),
        )),
    ));

    let rendered = print_block(&block);
    assert!(
        !rendered.contains("let exit ="),
        "nested return-handler staticcatchs should stay inline without an outer exit temp:\n{rendered}"
    );
    assert!(
        (rendered.contains("if (first)") && rendered.contains("if (second)"))
            || rendered.contains("return first ? 0 : (\n    second ? 1 : 2\n  );"),
        "expected the nested handler guards to stay inline without an outer exit temp:\n{rendered}"
    );
    assert!(
        (rendered.contains("return 0;")
            && rendered.contains("return 1;")
            && rendered.contains("return 2;"))
            || rendered.contains("return first ? 0 : (\n    second ? 1 : 2\n  );"),
        "expected the nested handler to lower into direct returns:\n{rendered}"
    );
}

#[test]
fn return_staticcatchs_keep_plain_handlers_inline_across_multiple_exit_sites() {
    let mut compiler = LambdaCompiler::new();
    let kind = Ident::create_local("kind");
    let do_with_b = Ident::create_local("doWithB");
    let block = compiler.compile_return_block(&Lambda::LstaticCatch(
        Box::new(Lambda::LstringSwitch(
            Box::new(Lambda::var(kind.clone())),
            vec![
                ("four".to_string(), Lambda::static_raise(2, Vec::new())),
                ("five".to_string(), Lambda::static_raise(2, Vec::new())),
                ("six".to_string(), Lambda::const_(Constant::int(6))),
            ],
            Some(Box::new(Lambda::const_(Constant::int(7)))),
        )),
        (2, vec![]),
        Box::new(Lambda::apply(
            Lambda::var(do_with_b.clone()),
            vec![Lambda::var(kind.clone())],
            ApInfo {
                loc: Location::none(),
                inlined: InlineAttribute::Default,
                status: ApplyStatus::Na,
            },
            false,
        )),
    ));

    let rendered = print_block(&block);
    assert!(
        !rendered.contains("let exit ="),
        "plain multi-exit handlers should stay inline without an exit temp:\n{rendered}"
    );
    assert!(
        rendered.contains("case \"four\" :") && rendered.contains("case \"five\" :"),
        "expected grouped inline cases for the shared handler:\n{rendered}"
    );
    assert_eq!(
        rendered.matches("return doWithB(kind);").count(),
        1,
        "expected the shared plain handler to stay inline in the switch:\n{rendered}"
    );
}

#[test]
fn untagged_object_return_switches_keep_outer_plain_handler_inside_the_switch() {
    let mut compiler = LambdaCompiler::new();
    let value = Ident::create_local("value");
    let body_id = Ident::create_local("body");
    let block = compiler.compile_return_block(&Lambda::LstaticCatch(
        Box::new(Lambda::Lswitch(
            Box::new(Lambda::var(value.clone())),
            LambdaSwitch {
                sw_consts_full: false,
                sw_consts: vec![],
                sw_blocks_full: false,
                sw_blocks: vec![(
                    0,
                    Lambda::LstaticCatch(
                        Box::new(Lambda::static_raise(2, Vec::new())),
                        (2, vec![]),
                        Box::new(Lambda::let_(
                            LetKind::Strict,
                            body_id.clone(),
                            Lambda::const_(Constant::int(1)),
                            Lambda::var(body_id.clone()),
                        )),
                    ),
                )],
                sw_failaction: Some(Box::new(Lambda::static_raise(1, Vec::new()))),
                sw_names: Some(SwitchNames {
                    consts: vec![
                        crate::lambda::SwitchTag {
                            name: "Null".to_string(),
                            tag_type: Some(crate::lambda::SwitchCaseTag::Null),
                        },
                        crate::lambda::SwitchTag {
                            name: "String".to_string(),
                            tag_type: Some(crate::lambda::SwitchCaseTag::String(
                                "string".to_string(),
                            )),
                        },
                    ],
                    blocks: vec![
                        crate::lambda::SwitchBlock {
                            tag: crate::lambda::SwitchTag::named("Object"),
                            tag_name: None,
                            block_type: Some(crate::lambda::SwitchBlockType::Object),
                        },
                        crate::lambda::SwitchBlock {
                            tag: crate::lambda::SwitchTag::named("Array"),
                            tag_name: None,
                            block_type: Some(crate::lambda::SwitchBlockType::Instance(
                                "Array".to_string(),
                            )),
                        },
                    ],
                }),
            },
        )),
        (1, vec![]),
        Box::new(Lambda::const_(Constant::int(0))),
    ));

    let rendered = print_block(&block);
    assert!(
        rendered.contains(
            "if (typeof value !== \"object\" || value === null || Array.isArray(value))"
        ),
        "expected the outer handler to stay as the literal-side guard:\n{rendered}"
    );
    assert!(
        !rendered.ends_with("return 0;"),
        "expected the outer handler not to be peeled out as a trailing fallthrough:\n{rendered}"
    );
    assert!(
        rendered.contains("let body = 1;") && rendered.contains("return body;"),
        "expected the object branch to stay inline after the guard:\n{rendered}"
    );
}

#[test]
fn single_case_staticcatch_wrapped_named_variant_return_switch_falls_through_to_handler() {
    let mut compiler = LambdaCompiler::new();
    let action = Ident::create_local("action");
    let block = compiler.with_return_unit_context(true, |compiler| {
        compiler.compile_return_block(&Lambda::LstaticCatch(
            Box::new(Lambda::Lswitch(
                Box::new(Lambda::var(action.clone())),
                LambdaSwitch {
                    sw_consts_full: false,
                    sw_consts: vec![(0, Lambda::const_(Constant::int(1)))],
                    sw_blocks_full: true,
                    sw_blocks: vec![],
                    sw_failaction: Some(Box::new(Lambda::static_raise(7, Vec::new()))),
                    sw_names: Some(SwitchNames {
                        consts: vec![crate::lambda::SwitchTag::named("One")],
                        blocks: vec![],
                    }),
                },
            )),
            (7, vec![]),
            Box::new(Lambda::const_(Constant::int(2))),
        ))
    });

    let [if_stmt, handler_return] = block.as_slice() else {
        panic!("expected an if statement followed by the handler return");
    };
    let (cond, then_block, else_block) = match &if_stmt.desc {
        StatementDesc::If(cond, then_block, else_block) => (cond, then_block, else_block),
        StatementDesc::Block(inner) => {
            let [inner_if] = inner.as_slice() else {
                panic!("expected the staticcatch wrapper block to contain a single if");
            };
            let StatementDesc::If(cond, then_block, else_block) = &inner_if.desc else {
                panic!(
                    "expected the single-case staticcatch switch to lower to if/fallthrough"
                );
            };
            (cond, then_block, else_block)
        }
        other => panic!(
            "expected the single-case staticcatch switch to lower to if/fallthrough, got {other:?}"
        ),
    };
    assert_string_equality_check(cond, Some(&action), None, "One");
    assert!(
        else_block.is_empty(),
        "unexpected else block: {else_block:?}"
    );
    assert_switch_case_returns_int_result(then_block, 1);
    match &handler_return.desc {
        StatementDesc::Return(expr) => assert_int_expr(expr, 2),
        other => panic!("expected the fallthrough handler return, got {other:?}"),
    }
}

#[test]
fn single_case_staticcatch_wrapped_named_variant_unit_handler_falls_through_like_variant_pattern_matching_spreads()
 {
    let mut compiler = LambdaCompiler::new();
    let action = Ident::create_local("action");
    let then_seen = Ident::create_local("then_seen");
    let else_seen = Ident::create_local("else_seen");
    let block = compiler.with_return_unit_context(true, |compiler| {
        compiler.compile_return_block(&Lambda::LstaticCatch(
            Box::new(Lambda::Lswitch(
                Box::new(Lambda::var(action.clone())),
                LambdaSwitch {
                    sw_consts_full: false,
                    sw_consts: vec![(
                        0,
                        Lambda::Lassign(
                            then_seen.clone(),
                            Box::new(Lambda::const_(Constant::int(1))),
                        ),
                    )],
                    sw_blocks_full: true,
                    sw_blocks: vec![],
                    sw_failaction: Some(Box::new(Lambda::static_raise(7, Vec::new()))),
                    sw_names: Some(SwitchNames {
                        consts: vec![crate::lambda::SwitchTag::named("One")],
                        blocks: vec![],
                    }),
                },
            )),
            (7, vec![]),
            Box::new(Lambda::Lassign(
                else_seen.clone(),
                Box::new(Lambda::const_(Constant::int(2))),
            )),
        ))
    });

    let rendered = print_block(&block);
    assert!(
        rendered.contains("if (action === \"One\") {"),
        "expected the single-case handler to stay as a positive guard:\n{rendered}"
    );
    assert!(
        rendered.contains("then_seen = 1;"),
        "expected the matching branch effect to stay inside the guard:\n{rendered}"
    );
    assert!(
        rendered.contains("else_seen = 2;"),
        "expected the non-matching handler to fall through after the guard:\n{rendered}"
    );
    assert!(
        rendered.contains("return;"),
        "expected the matching branch to keep its explicit unit return:\n{rendered}"
    );
    assert!(
        !rendered.contains("} else {"),
        "unexpected explicit else around the fallthrough handler:\n{rendered}"
    );
}

#[test]
fn js_pipeline_keeps_single_case_staticcatch_unit_handler_as_fallthrough_guard() {
    let mut compiler = LambdaCompiler::new();
    let run = Ident::create_local("run");
    let action = Ident::create_local("action");
    let then_seen = Ident::create_local("then_seen");
    let else_seen = Ident::create_local("else_seen");
    let lam = Lambda::let_(
        LetKind::Strict,
        run.clone(),
        Lambda::function_(
            1,
            vec![action.clone()],
            Lambda::LstaticCatch(
                Box::new(Lambda::Lswitch(
                    Box::new(Lambda::var(action.clone())),
                    LambdaSwitch {
                        sw_consts_full: false,
                        sw_consts: vec![(
                            0,
                            Lambda::Lassign(
                                then_seen.clone(),
                                Box::new(Lambda::const_(Constant::int(1))),
                            ),
                        )],
                        sw_blocks_full: true,
                        sw_blocks: vec![],
                        sw_failaction: Some(Box::new(Lambda::static_raise(7, Vec::new()))),
                        sw_names: Some(SwitchNames {
                            consts: vec![crate::lambda::SwitchTag::named("One")],
                            blocks: vec![],
                        }),
                    },
                )),
                (7, vec![]),
                Box::new(Lambda::Lassign(
                    else_seen.clone(),
                    Box::new(Lambda::const_(Constant::int(2))),
                )),
            ),
            crate::lambda::FunctionAttribute {
                return_unit: true,
                ..Default::default()
            },
        ),
        Lambda::prim(
            Primitive::Pmakeblock(
                0,
                TagInfo::ModuleExport(vec![run.clone()]),
                Mutable::Immutable,
            ),
            vec![Lambda::var(run.clone())],
            Location::none(),
        ),
    );

    let deps = compiler.compile_deps_program(&lam);
    let rendered = print_deps_program(&deps, None);
    assert!(
        rendered.contains("if (action === \"One\") {"),
        "expected the final JS pipeline to keep the positive guard:\n{rendered}"
    );
    assert!(
        rendered.contains("then_seen = 1;"),
        "expected the matching branch effect to stay materialized:\n{rendered}"
    );
    assert!(
        rendered.contains("else_seen = 2;"),
        "expected the handler effect to stay after the guard:\n{rendered}"
    );
    assert!(
        rendered.contains("return;"),
        "expected the matching branch to keep its explicit unit return:\n{rendered}"
    );
    assert!(
        !rendered.contains("} else {"),
        "unexpected explicit else around the final JS pipeline output:\n{rendered}"
    );
}

#[test]
fn single_case_staticcatch_wrapped_untagged_object_unit_handler_keeps_negative_guard() {
    let mut compiler = LambdaCompiler::new();
    let json = Ident::create_local("json");
    let seen = Ident::create_local("seen");
    let block = compiler.with_return_unit_context(true, |compiler| {
        compiler.compile_return_block(&Lambda::LstaticCatch(
            Box::new(Lambda::Lswitch(
                Box::new(Lambda::var(json.clone())),
                LambdaSwitch {
                    sw_consts_full: false,
                    sw_consts: vec![],
                    sw_blocks_full: false,
                    sw_blocks: vec![(
                        0,
                        Lambda::Lassign(
                            seen.clone(),
                            Box::new(Lambda::const_(Constant::int(1))),
                        ),
                    )],
                    sw_failaction: Some(Box::new(Lambda::static_raise(9, Vec::new()))),
                    sw_names: Some(SwitchNames {
                        consts: vec![crate::lambda::SwitchTag {
                            name: "Null".to_string(),
                            tag_type: Some(crate::lambda::SwitchCaseTag::Null),
                        }],
                        blocks: vec![
                            crate::lambda::SwitchBlock {
                                tag: crate::lambda::SwitchTag::named("Object"),
                                tag_name: None,
                                block_type: Some(crate::lambda::SwitchBlockType::Object),
                            },
                            crate::lambda::SwitchBlock {
                                tag: crate::lambda::SwitchTag::named("Array"),
                                tag_name: None,
                                block_type: Some(crate::lambda::SwitchBlockType::Instance(
                                    "Array".to_string(),
                                )),
                            },
                        ],
                    }),
                },
            )),
            (9, vec![]),
            Box::new(Lambda::const_(Constant::JsUndefined { is_unit: true })),
        ))
    });

    let rendered = print_block(&block);
    assert!(
        rendered.contains(
            "if (typeof json !== \"object\" || json === null || Array.isArray(json)) {"
        ),
        "expected the unit handler to stay as the negative guard default:\n{rendered}"
    );
    assert!(
        rendered.contains("return;"),
        "expected the negative guard to keep an explicit early return:\n{rendered}"
    );
    assert!(
        rendered.contains("seen = 1;"),
        "expected the object branch effect to remain after the guard:\n{rendered}"
    );
}

#[test]
fn effectful_unit_staticcatch_handlers_keep_fail_first_guards() {
    let mut compiler = LambdaCompiler::new();
    let s = Ident::create_local("s");
    let len = Ident::create_local("len");
    let match_ = Ident::create_local("match");
    let seen = Ident::create_local("seen");
    let failed = Ident::create_local("failed");
    let block = compiler.with_return_unit_context(true, |compiler| {
        compiler.compile_return_block(&Lambda::LstaticCatch(
            Box::new(Lambda::Lswitch(
                Box::new(Lambda::var(s.clone())),
                LambdaSwitch {
                    sw_consts_full: false,
                    sw_consts: vec![],
                    sw_blocks_full: false,
                    sw_blocks: vec![(
                        0,
                        Lambda::let_(
                            LetKind::Alias,
                            len.clone(),
                            Lambda::prim(
                                Primitive::Parraylength,
                                vec![Lambda::var(s.clone())],
                                Location::none(),
                            ),
                            Lambda::LifThenElse(
                                Box::new(Lambda::prim(
                                    Primitive::Pintcomp(Comparison::Neq),
                                    vec![
                                        Lambda::var(len.clone()),
                                        Lambda::const_(Constant::int(3)),
                                    ],
                                    Location::none(),
                                )),
                                Box::new(Lambda::static_raise(11, Vec::new())),
                                Box::new(Lambda::let_(
                                    LetKind::StrictOpt,
                                    match_.clone(),
                                    Lambda::prim(
                                        Primitive::Parrayrefu,
                                        vec![
                                            Lambda::var(s.clone()),
                                            Lambda::const_(Constant::int(0)),
                                        ],
                                        Location::none(),
                                    ),
                                    Lambda::Lswitch(
                                        Box::new(Lambda::var(match_.clone())),
                                        LambdaSwitch {
                                            sw_consts_full: false,
                                            sw_consts: vec![(
                                                2,
                                                Lambda::Lassign(
                                                    seen.clone(),
                                                    Box::new(Lambda::const_(Constant::int(1))),
                                                ),
                                            )],
                                            sw_blocks_full: false,
                                            sw_blocks: vec![],
                                            sw_failaction: Some(Box::new(
                                                Lambda::static_raise(11, Vec::new()),
                                            )),
                                            sw_names: Some(SwitchNames {
                                                consts: vec![
                                                    crate::lambda::SwitchTag {
                                                        name: "Missing".to_string(),
                                                        tag_type: Some(
                                                            crate::lambda::SwitchCaseTag::Undefined,
                                                        ),
                                                    },
                                                    crate::lambda::SwitchTag {
                                                        name: "False".to_string(),
                                                        tag_type: Some(
                                                            crate::lambda::SwitchCaseTag::Bool(false),
                                                        ),
                                                    },
                                                    crate::lambda::SwitchTag {
                                                        name: "True".to_string(),
                                                        tag_type: Some(
                                                            crate::lambda::SwitchCaseTag::Bool(true),
                                                        ),
                                                    },
                                                    crate::lambda::SwitchTag {
                                                        name: "Null".to_string(),
                                                        tag_type: Some(
                                                            crate::lambda::SwitchCaseTag::Null,
                                                        ),
                                                    },
                                                ],
                                                blocks: vec![
                                                    crate::lambda::SwitchBlock {
                                                        tag: crate::lambda::SwitchTag::named(
                                                            "String",
                                                        ),
                                                        tag_name: None,
                                                        block_type: Some(
                                                            crate::lambda::SwitchBlockType::String,
                                                        ),
                                                    },
                                                    crate::lambda::SwitchBlock {
                                                        tag: crate::lambda::SwitchTag::named(
                                                            "Number",
                                                        ),
                                                        tag_name: None,
                                                        block_type: Some(
                                                            crate::lambda::SwitchBlockType::Float,
                                                        ),
                                                    },
                                                    crate::lambda::SwitchBlock {
                                                        tag: crate::lambda::SwitchTag::named(
                                                            "Object",
                                                        ),
                                                        tag_name: None,
                                                        block_type: Some(
                                                            crate::lambda::SwitchBlockType::Object,
                                                        ),
                                                    },
                                                    crate::lambda::SwitchBlock {
                                                        tag: crate::lambda::SwitchTag::named(
                                                            "Array",
                                                        ),
                                                        tag_name: None,
                                                        block_type: Some(
                                                            crate::lambda::SwitchBlockType::Instance(
                                                                "Array".to_string(),
                                                            ),
                                                        ),
                                                    },
                                                ],
                                            }),
                                        },
                                    ),
                                )),
                            ),
                        ),
                    )],
                    sw_failaction: Some(Box::new(Lambda::static_raise(11, Vec::new()))),
                    sw_names: Some(SwitchNames {
                        consts: vec![],
                        blocks: vec![crate::lambda::SwitchBlock {
                            tag: crate::lambda::SwitchTag::named("Array"),
                            tag_name: None,
                            block_type: Some(crate::lambda::SwitchBlockType::Instance(
                                "Array".to_string(),
                            )),
                        }],
                    }),
                },
            )),
            (11, vec![]),
            Box::new(Lambda::Lsequence(
                Box::new(Lambda::Lassign(
                    failed.clone(),
                    Box::new(Lambda::const_(Constant::int(1))),
                )),
                Box::new(Lambda::const_(Constant::JsUndefined { is_unit: true })),
            )),
        ))
    });

    let rendered = print_block(&block);
    assert!(
        rendered.contains("if (len !== 3) {"),
        "expected the length mismatch to stay as a fail-first guard:\n{rendered}"
    );
    assert!(
        !rendered.contains("if (len === 3) {"),
        "expected the success-first length nest to be gone:\n{rendered}"
    );
    assert!(
        rendered.contains("failed = 1;"),
        "expected the effectful unit handler to stay explicit in the lowered guard chain:\n{rendered}"
    );
}

#[test]
fn multi_case_staticcatch_wrapped_named_variant_return_switch_moves_fallthrough_cases_last() {
    let mut compiler = LambdaCompiler::new();
    let action = Ident::create_local("action");
    let block = compiler.compile_return_block(&Lambda::LstaticCatch(
        Box::new(Lambda::LstaticCatch(
            Box::new(Lambda::LstaticCatch(
                Box::new(Lambda::Lswitch(
                    Box::new(Lambda::var(action.clone())),
                    LambdaSwitch {
                        sw_consts_full: true,
                        sw_consts: vec![
                            (0, Lambda::static_raise(4, Vec::new())),
                            (1, Lambda::static_raise(1, Vec::new())),
                            (2, Lambda::static_raise(4, Vec::new())),
                        ],
                        sw_blocks_full: true,
                        sw_blocks: vec![],
                        sw_failaction: None,
                        sw_names: Some(SwitchNames {
                            consts: vec![
                                crate::lambda::SwitchTag::named("A"),
                                crate::lambda::SwitchTag::named("B"),
                                crate::lambda::SwitchTag::named("C"),
                            ],
                            blocks: vec![],
                        }),
                    },
                )),
                (4, vec![]),
                Box::new(Lambda::static_raise(2, Vec::new())),
            )),
            (2, vec![]),
            Box::new(Lambda::const_(Constant::JsFalse)),
        )),
        (1, vec![]),
        Box::new(Lambda::const_(Constant::JsTrue)),
    ));

    let [switch_stmt, handler_return] = block.as_slice() else {
        panic!("expected a switch followed by the fallthrough handler return");
    };
    let StatementDesc::StringSwitch(test, clauses, None) = &switch_stmt.desc else {
        panic!("expected a named-constructor string switch");
    };
    assert!(matches!(
        test,
        Expression {
            desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
            ..
        } if id.same(&action)
    ));

    let expected_tags = ["B", "A", "C"];
    assert_eq!(clauses.len(), expected_tags.len());
    for (clause, expected_tag) in clauses.iter().zip(expected_tags) {
        assert_eq!(
            clause.tag_type,
            SwitchCaseTag::String(expected_tag.to_string())
        );
    }
    assert_switch_case_returns_bool_result(&clauses[0].clause.body, true);
    assert!(clauses[1].clause.body.is_empty());
    assert!(clauses[2].clause.body.is_empty());
    match &handler_return.desc {
        StatementDesc::Return(Expression {
            desc: ExpressionDesc::Bool(value),
            ..
        }) => assert!(!value),
        other => panic!("expected the fallthrough handler return, got {other:?}"),
    }
}

#[test]
fn nested_named_variant_return_switches_keep_plain_inner_handlers_as_default_arms() {
    let mut compiler = LambdaCompiler::new();
    let action = Ident::create_local("action");
    let block = compiler.compile_return_block(&Lambda::LstaticCatch(
        Box::new(Lambda::LstaticCatch(
            Box::new(Lambda::LstaticCatch(
                Box::new(Lambda::Lswitch(
                    Box::new(Lambda::var(action.clone())),
                    LambdaSwitch {
                        sw_consts_full: false,
                        sw_consts: vec![
                            (0, Lambda::static_raise(4, Vec::new())),
                            (1, Lambda::static_raise(4, Vec::new())),
                            (2, Lambda::static_raise(5, Vec::new())),
                            (3, Lambda::static_raise(5, Vec::new())),
                        ],
                        sw_blocks_full: true,
                        sw_blocks: vec![],
                        sw_failaction: Some(Box::new(Lambda::static_raise(3, Vec::new()))),
                        sw_names: Some(SwitchNames {
                            consts: vec![
                                crate::lambda::SwitchTag::named("Four"),
                                crate::lambda::SwitchTag::named("Five"),
                                crate::lambda::SwitchTag::named("Six"),
                                crate::lambda::SwitchTag::named("Seven"),
                            ],
                            blocks: vec![],
                        }),
                    },
                )),
                (3, vec![]),
                Box::new(Lambda::const_(Constant::int(10))),
            )),
            (4, vec![]),
            Box::new(Lambda::const_(Constant::int(20))),
        )),
        (5, vec![]),
        Box::new(Lambda::const_(Constant::int(30))),
    ));
    let rendered = print_block(&block);

    let [switch_stmt] = block.as_slice() else {
        panic!(
            "expected a single switch with the plain handler kept as the default arm:\n{rendered}"
        );
    };
    let StatementDesc::StringSwitch(test, clauses, Some(default_block)) = &switch_stmt.desc
    else {
        panic!(
            "expected the innermost plain handler to stay in the switch default:\n{rendered}"
        );
    };
    assert!(matches!(
        test,
        Expression {
            desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
            ..
        } if id.same(&action)
    ));

    let expected_tags = ["Four", "Five", "Six", "Seven"];
    assert_eq!(clauses.len(), expected_tags.len());
    for (clause, expected_tag) in clauses.iter().zip(expected_tags) {
        assert_eq!(
            clause.tag_type,
            SwitchCaseTag::String(expected_tag.to_string())
        );
    }
    assert!(clauses[0].clause.body.is_empty());
    assert_switch_case_returns_int_result(&clauses[1].clause.body, 20);
    assert!(clauses[2].clause.body.is_empty());
    assert_switch_case_returns_int_result(&clauses[3].clause.body, 30);
    assert_switch_default_returns_int_result(default_block, 10);
}

fn gpr_1438_switch_cases(b: &Ident, c: &Ident, d: &Ident, e: &Ident) -> Vec<(i32, Lambda)> {
    vec![
        (98, Lambda::var(c.clone())),
        (99, Lambda::static_raise(1, Vec::new())),
        (100, Lambda::static_raise(2, Vec::new())),
        (101, Lambda::static_raise(2, Vec::new())),
        (102, Lambda::static_raise(2, Vec::new())),
        (103, Lambda::static_raise(2, Vec::new())),
        (104, Lambda::static_raise(2, Vec::new())),
        (105, Lambda::static_raise(2, Vec::new())),
        (106, Lambda::var(d.clone())),
        (107, Lambda::var(e.clone())),
        (108, Lambda::static_raise(2, Vec::new())),
        (109, Lambda::static_raise(2, Vec::new())),
        (110, Lambda::static_raise(2, Vec::new())),
        (111, Lambda::static_raise(2, Vec::new())),
        (112, Lambda::static_raise(2, Vec::new())),
        (113, Lambda::static_raise(2, Vec::new())),
        (114, Lambda::static_raise(2, Vec::new())),
        (115, Lambda::static_raise(2, Vec::new())),
        (116, Lambda::var(b.clone())),
        (117, Lambda::static_raise(2, Vec::new())),
        (118, Lambda::static_raise(1, Vec::new())),
    ]
}

fn gpr_1438_fallthrough_handler() -> Lambda {
    let param = Ident::create_local("param");
    Lambda::prim(
        Primitive::PjsFnMake(1),
        vec![Lambda::function_(
            1,
            vec![param],
            Lambda::const_(Constant::JsUndefined { is_unit: true }),
            FunctionAttribute {
                return_unit: true,
                ..FunctionAttribute::default()
            },
        )],
        Location::none(),
    )
}

#[test]
fn nested_plain_int_return_switches_can_fall_through_like_gpr_1438() {
    let mut compiler = LambdaCompiler::new();
    let key = Ident::create_local("key");
    let a = Ident::create_local("a");
    let b = Ident::create_local("b");
    let c = Ident::create_local("c");
    let d = Ident::create_local("d");
    let e = Ident::create_local("e");
    let block = compiler.compile_return_block(&Lambda::LstaticCatch(
        Box::new(Lambda::LstaticCatch(
            Box::new(Lambda::Lswitch(
                Box::new(Lambda::var(key.clone())),
                LambdaSwitch {
                    sw_consts_full: false,
                    sw_consts: gpr_1438_switch_cases(&b, &c, &d, &e),
                    sw_blocks_full: true,
                    sw_blocks: vec![],
                    sw_failaction: Some(Box::new(Lambda::static_raise(2, Vec::new()))),
                    sw_names: None,
                },
            )),
            (2, vec![]),
            Box::new(gpr_1438_fallthrough_handler()),
        )),
        (1, vec![]),
        Box::new(Lambda::var(a.clone())),
    ));

    let [switch_stmt, handler_return] = block.as_slice() else {
        panic!("expected a switch followed by the outer fallthrough handler");
    };
    let StatementDesc::IntSwitch(test, clauses, None) = &switch_stmt.desc else {
        panic!("expected the inner plain handler to stay outside the switch");
    };
    assert!(matches!(
        test,
        Expression {
            desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
            ..
        } if id.same(&key)
    ));
    assert_eq!(clauses.len(), 6);

    let rendered = print_block(&block);
    assert_eq!(
        rendered,
        "switch (key) {\n  case 98 :\n    return c;\n  case 106 :\n    return d;\n  case 107 :\n    return e;\n  case 116 :\n    return b;\n  case 99 :\n  case 118 :\n    return a;\n}\n\nreturn param => {};"
    );

    match &handler_return.desc {
        StatementDesc::Return(_) => {}
        other => panic!("expected the outer handler return, got {other:?}"),
    }
}

#[test]
fn compile_deps_program_keeps_gpr_1438_fallthrough_return_outside_switch() {
    let mut compiler = LambdaCompiler::new();
    let action_key = Ident::create_local("actionKey");
    let key = Ident::create_local("key");
    let a = Ident::create_local("a");
    let b = Ident::create_local("b");
    let c = Ident::create_local("c");
    let d = Ident::create_local("d");
    let e = Ident::create_local("e");
    let function = Lambda::function_(
        6,
        vec![
            key.clone(),
            a.clone(),
            b.clone(),
            c.clone(),
            d.clone(),
            e.clone(),
        ],
        Lambda::LstaticCatch(
            Box::new(Lambda::LstaticCatch(
                Box::new(Lambda::Lswitch(
                    Box::new(Lambda::var(key.clone())),
                    LambdaSwitch {
                        sw_consts_full: false,
                        sw_consts: gpr_1438_switch_cases(&b, &c, &d, &e),
                        sw_blocks_full: true,
                        sw_blocks: vec![],
                        sw_failaction: Some(Box::new(Lambda::static_raise(2, Vec::new()))),
                        sw_names: None,
                    },
                )),
                (2, vec![]),
                Box::new(gpr_1438_fallthrough_handler()),
            )),
            (1, vec![]),
            Box::new(Lambda::var(a.clone())),
        ),
        FunctionAttribute::default(),
    );
    let lam = Lambda::let_(
        LetKind::Strict,
        action_key.clone(),
        Lambda::prim(Primitive::PjsFnMake(6), vec![function], Location::none()),
        Lambda::prim(
            Primitive::Pmakeblock(
                0,
                TagInfo::ModuleExport(vec![action_key.clone()]),
                Mutable::Immutable,
            ),
            vec![Lambda::var(action_key.clone())],
            Location::none(),
        ),
    );

    let simplified =
        crate::lambda::simplify::simplify_for_js_backend_with_jsx_preserve(&lam, false);
    let mut direct_compiler = LambdaCompiler::new();
    let direct_body =
        direct_compiler.compile_return_block(extract_first_function_body(&simplified));
    assert_fallthrough_return_outside_switch_body(
        &direct_body,
        "after simplify + direct compile_return_block",
    );

    let compiled = compiler.compile_expr(&simplified);
    let mut block = compiled.prelude;
    assert_first_function_body_keeps_fallthrough_return_outside_switch(
        &block,
        "after compile_expr",
    );

    let exports = if let Some(mut exports) = extract_toplevel_exports(compiled.expr, &mut block)
    {
        if block_terminates(&block) {
            for value in &mut exports.values {
                *value = Expression::undefined(false);
            }
        }
        compiler.coerce_toplevel_exports(&mut block, exports)
    } else {
        vec![]
    };
    let program = Program::new(block, exports);
    assert_first_function_body_keeps_fallthrough_return_outside_switch(
        &program.block,
        "after export extraction",
    );

    let deps = apply_js_flatten_pass(DepsProgram {
        program,
        modules: vec![],
        side_effect: module_side_effect_reason(&simplified),
    });
    assert_first_function_body_keeps_fallthrough_return_outside_switch(
        &deps.program.block,
        "after js_flatten",
    );

    let deps = apply_external_shadow_pass(deps);
    assert_first_function_body_keeps_fallthrough_return_outside_switch(
        &deps.program.block,
        "after external_shadow",
    );

    let deps = apply_js_tailcall_inline_pass(deps);
    assert_first_function_body_keeps_fallthrough_return_outside_switch(
        &deps.program.block,
        "after tailcall_inline",
    );

    let deps = apply_js_flatten_and_mark_dead_pass(deps, false);
    assert_first_function_body_keeps_fallthrough_return_outside_switch(
        &deps.program.block,
        "after flatten_and_mark_dead",
    );

    let deps = apply_js_shake_pass(deps);
    assert_first_function_body_keeps_fallthrough_return_outside_switch(
        &deps.program.block,
        "after js_shake",
    );
    let rendered = print_deps_program(&deps, None);
    assert_eq!(
        rendered,
        "// Generated by ReScript, PLEASE EDIT WITH CARE\n\n\nfunction actionKey(key, a, b, c, d, e) {\n  switch (key) {\n    case 98 :\n      return c;\n    case 106 :\n      return d;\n    case 107 :\n      return e;\n    case 116 :\n      return b;\n    case 99 :\n    case 118 :\n      return a;\n  }\n  return param => {};\n}\n\nexport {\n  actionKey,\n}\n/* No side effect */\n"
    );
}

#[test]
fn nested_let_values_preserve_declaration_context_for_wrapped_string_switches() {
    let mut compiler = LambdaCompiler::new();
    let version = Ident::create_local("version");
    let match_id = Ident::create_local("match");
    let scrutinee = Ident::create_local("platform");
    let program = compiler.compile_program(&Lambda::Llet(
        LetKind::Strict,
        version.clone(),
        Box::new(Lambda::let_(
            LetKind::Strict,
            match_id.clone(),
            Lambda::var(scrutinee.clone()),
            Lambda::LstaticCatch(
                Box::new(Lambda::LstringSwitch(
                    Box::new(Lambda::var(match_id.clone())),
                    vec![
                        ("linux".to_string(), Lambda::const_(Constant::int(1))),
                        ("darwin".to_string(), Lambda::const_(Constant::int(2))),
                    ],
                    Some(Box::new(Lambda::static_raise(1, Vec::new()))),
                )),
                (1, vec![]),
                Box::new(Lambda::const_(Constant::int(3))),
            ),
        )),
        Box::new(Lambda::var(version.clone())),
    ));

    let [version_decl, switch_stmt] = program.block.as_slice() else {
        panic!(
            "expected simplification to inline the nested binding into a declaration and switch"
        );
    };

    let StatementDesc::Variable(VariableDeclaration {
        ident, value: None, ..
    }) = &version_decl.desc
    else {
        panic!("expected an uninitialized declaration for the outer binding");
    };
    assert!(ident.same(&version));

    let StatementDesc::StringSwitch(test, clauses, Some(default_block)) = &switch_stmt.desc
    else {
        panic!("expected the outer declaration context to reach the string switch");
    };
    assert!(matches!(
        test,
        Expression {
            desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
            ..
        } if id.same(&scrutinee)
    ));

    let expected_cases = [("linux", 1_i32), ("darwin", 2_i32)];
    for (clause, (expected_tag, expected_value)) in clauses.iter().zip(expected_cases) {
        assert_eq!(
            clause.tag_type,
            SwitchCaseTag::String(expected_tag.to_string())
        );
        assert_switch_case_assigns_int_result(&clause.clause.body, &version, expected_value);
    }
    assert_switch_default_assigns_int_result(default_block, &version, 3);
}

#[test]
fn function_return_blocks_lower_switches_without_a_result_temp() {
    let mut compiler = LambdaCompiler::new();
    let scrutinee = Ident::create_local("scrutinee");
    let compiled = compiler.compile_expr(&Lambda::Lfunction(crate::lambda::LFunction {
        arity: 1,
        params: vec![scrutinee.clone()],
        body: Box::new(Lambda::Lswitch(
            Box::new(Lambda::var(scrutinee.clone())),
            LambdaSwitch {
                sw_consts_full: true,
                sw_consts: vec![
                    (0, Lambda::const_(Constant::int(1))),
                    (1, Lambda::const_(Constant::int(2))),
                ],
                sw_blocks_full: false,
                sw_blocks: vec![],
                sw_failaction: Some(Box::new(Lambda::const_(Constant::int(3)))),
                sw_names: None,
            },
        )),
        attr: crate::lambda::FunctionAttribute::default(),
    }));

    let Expression {
        desc: ExpressionDesc::Fun { body, .. },
        ..
    } = compiled.expr
    else {
        panic!("expected a function expression");
    };

    let [switch_stmt] = body.as_slice() else {
        panic!("expected a single switch statement in the function body");
    };
    let StatementDesc::IntSwitch(test, clauses, Some(default_block)) = &switch_stmt.desc else {
        panic!("expected a direct integer switch in the function body");
    };
    assert!(matches!(
        test,
        Expression {
            desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
            ..
        } if id.same(&scrutinee)
    ));

    let expected_cases = [(0, 1_i32), (1, 2_i32)];
    for ((tag, clause), (expected_tag, expected_value)) in clauses.iter().zip(expected_cases) {
        assert_eq!(*tag, expected_tag);
        assert_switch_case_returns_int_result(&clause.body, expected_value);
    }
    assert_switch_default_returns_int_result(default_block, 3);
}

#[test]
fn function_return_blocks_lower_ifs_without_a_result_temp() {
    let mut compiler = LambdaCompiler::new();
    let cond = Ident::create_local("cond");
    let branch = Ident::create_local("branch");
    let compiled = compiler.compile_expr(&Lambda::Lfunction(crate::lambda::LFunction {
        arity: 1,
        params: vec![cond.clone()],
        body: Box::new(Lambda::LifThenElse(
            Box::new(Lambda::var(cond.clone())),
            Box::new(Lambda::let_(
                LetKind::Strict,
                branch.clone(),
                Lambda::const_(Constant::int(1)),
                Lambda::var(branch.clone()),
            )),
            Box::new(Lambda::const_(Constant::int(0))),
        )),
        attr: crate::lambda::FunctionAttribute::default(),
    }));

    let Expression {
        desc: ExpressionDesc::Fun { body, .. },
        ..
    } = compiled.expr
    else {
        panic!("expected a function expression");
    };

    match body.as_slice() {
        [if_stmt] => {
            let (test, then_block, else_block) = match &if_stmt.desc {
                StatementDesc::If(test, then_block, else_block) => {
                    (test, then_block, else_block)
                }
                StatementDesc::Block(inner) => match inner.as_slice() {
                    [inner_if] => {
                        let StatementDesc::If(test, then_block, else_block) = &inner_if.desc
                        else {
                            panic!("expected the wrapper block to contain an if");
                        };
                        (test, then_block, else_block)
                    }
                    [guard_stmt, branch_decl, branch_return] => {
                        let (test, then_block, else_block) = match &guard_stmt.desc {
                            StatementDesc::If(test, then_block, else_block) => {
                                (test, then_block, else_block)
                            }
                            other => panic!("expected a guard if, got {other:?}"),
                        };
                        assert!(matches!(
                            test,
                            Expression {
                                desc: ExpressionDesc::JsNot(inner),
                                ..
                            } if matches!(
                                &inner.desc,
                                ExpressionDesc::Var(crate::js_ir::VIdent::Id(id))
                                    if id.same(&cond)
                            )
                        ));
                        assert!(else_block.is_empty());
                        assert_switch_case_returns_int_result(then_block, 0);

                        let StatementDesc::Variable(VariableDeclaration {
                            ident,
                            value:
                                Some(Expression {
                                    desc: ExpressionDesc::Number(Number::Int { i: 1, .. }),
                                    ..
                                }),
                            ..
                        }) = &branch_decl.desc
                        else {
                            panic!("expected the then-branch declaration");
                        };
                        assert!(ident.same(&branch));
                        assert!(matches!(
                            branch_return,
                            Statement {
                                desc: StatementDesc::Return(Expression {
                                    desc: ExpressionDesc::Var(
                                        crate::js_ir::VIdent::Id(id)
                                    ),
                                    ..
                                }),
                                ..
                            } if id.same(&branch)
                        ));
                        return;
                    }
                    _ => panic!("expected a single wrapped if statement"),
                },
                other => panic!("expected direct return-position if lowering, got {other:?}"),
            };
            assert!(matches!(
                test,
                Expression {
                    desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                    ..
                } if id.same(&cond)
            ));

            let [branch_decl, branch_return] = then_block.as_slice() else {
                panic!("expected the let-binding branch to stay inline in the then block");
            };
            let StatementDesc::Variable(VariableDeclaration {
                ident,
                value:
                    Some(Expression {
                        desc: ExpressionDesc::Number(Number::Int { i: 1, .. }),
                        ..
                    }),
                ..
            }) = &branch_decl.desc
            else {
                panic!("expected the then branch local declaration");
            };
            assert!(ident.same(&branch));
            assert!(matches!(
                branch_return,
                Statement {
                    desc: StatementDesc::Return(Expression {
                        desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                        ..
                    }),
                    ..
                } if id.same(&branch)
            ));

            let [else_return] = else_block.as_slice() else {
                panic!("expected a single return in the else branch");
            };
            assert!(matches!(
                else_return,
                Statement {
                    desc: StatementDesc::Return(Expression {
                        desc: ExpressionDesc::Number(Number::Int { i: 0, .. }),
                        ..
                    }),
                    ..
                }
            ));
        }
        [guard_stmt, branch_decl, branch_return] => {
            let (test, then_block, else_block) = match &guard_stmt.desc {
                StatementDesc::If(test, then_block, else_block) => {
                    (test, then_block, else_block)
                }
                StatementDesc::Block(inner) => {
                    let [inner_if] = inner.as_slice() else {
                        panic!("expected a single guard if inside the wrapper block");
                    };
                    let StatementDesc::If(test, then_block, else_block) = &inner_if.desc else {
                        panic!("expected the wrapper block to contain an if");
                    };
                    (test, then_block, else_block)
                }
                other => panic!("expected a guard if, got {other:?}"),
            };
            assert!(matches!(
                test,
                Expression {
                    desc: ExpressionDesc::JsNot(inner),
                    ..
                } if matches!(
                    &inner.desc,
                    ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)) if id.same(&cond)
                )
            ));
            assert!(else_block.is_empty());
            assert_switch_case_returns_int_result(then_block, 0);

            let StatementDesc::Variable(VariableDeclaration {
                ident,
                value:
                    Some(Expression {
                        desc: ExpressionDesc::Number(Number::Int { i: 1, .. }),
                        ..
                    }),
                ..
            }) = &branch_decl.desc
            else {
                panic!("expected the then-branch declaration");
            };
            assert!(ident.same(&branch));
            assert!(matches!(
                branch_return,
                Statement {
                    desc: StatementDesc::Return(Expression {
                        desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                        ..
                    }),
                    ..
                } if id.same(&branch)
            ));
        }
        _ => panic!("expected either a direct if or a guard-fallthrough lowering"),
    }
}

#[test]
fn unit_return_function_body_keeps_positive_effect_guard_before_js_passes() {
    let mut compiler = LambdaCompiler::new();
    let cond = Ident::create_local("cond");
    let seen = Ident::create_local("seen");
    let body = Lambda::LifThenElse(
        Box::new(Lambda::var(cond.clone())),
        Box::new(Lambda::Lassign(
            seen.clone(),
            Box::new(Lambda::const_(Constant::int(1))),
        )),
        Box::new(Lambda::const_(Constant::JsUndefined { is_unit: true })),
    );
    let compiled = compiler.compile_expr(&Lambda::Lfunction(crate::lambda::LFunction {
        arity: 2,
        params: vec![cond.clone(), seen.clone()],
        body: Box::new(body),
        attr: crate::lambda::FunctionAttribute {
            return_unit: true,
            ..Default::default()
        },
    }));

    let Expression {
        desc: ExpressionDesc::Fun { body, .. },
        ..
    } = compiled.expr
    else {
        panic!("expected a function expression");
    };

    let [if_stmt] = body.as_slice() else {
        panic!("expected a single if statement in the function body");
    };
    let StatementDesc::If(_, then_block, else_block) = &if_stmt.desc else {
        panic!("expected a direct positive guard, got {if_stmt:#?}");
    };
    assert!(matches!(
        then_block.as_slice(),
        [
            Statement {
                desc: StatementDesc::Exp(Expression {
                    desc: ExpressionDesc::Bin(BinOp::Eq, _, _),
                    ..
                }),
                ..
            },
            Statement {
                desc: StatementDesc::Return(Expression {
                    desc: ExpressionDesc::Undefined { .. },
                    ..
                }),
                ..
            }
        ]
    ));
    assert!(else_block.is_empty());
}

#[test]
fn unit_return_function_with_trivial_if_branches_keeps_condition_effect_only() {
    let mut compiler = LambdaCompiler::new();
    let effect = Ident::create_local("effect");
    let body = Lambda::LifThenElse(
        Box::new(Lambda::apply(
            Lambda::var(effect.clone()),
            vec![],
            ApInfo {
                loc: Location::none(),
                inlined: InlineAttribute::Default,
                status: ApplyStatus::Na,
            },
            false,
        )),
        Box::new(Lambda::const_(Constant::JsUndefined { is_unit: true })),
        Box::new(Lambda::const_(Constant::JsUndefined { is_unit: true })),
    );
    let compiled = compiler.compile_expr(&Lambda::Lfunction(crate::lambda::LFunction {
        arity: 1,
        params: vec![effect.clone()],
        body: Box::new(body),
        attr: crate::lambda::FunctionAttribute {
            return_unit: true,
            ..Default::default()
        },
    }));

    let Expression {
        desc: ExpressionDesc::Fun { body, .. },
        ..
    } = compiled.expr
    else {
        panic!("expected a function expression");
    };

    let [stmt] = body.as_slice() else {
        panic!("expected a single expression statement in the function body");
    };
    assert!(matches!(
        stmt,
        Statement {
            desc: StatementDesc::Exp(Expression {
                desc: ExpressionDesc::Call(
                    func,
                    args,
                    _
                ),
                ..
            }),
            ..
        } if matches!(
            &func.as_ref().desc,
            ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)) if id.same(&effect)
        ) && args.is_empty()
    ));
}

#[test]
fn unit_return_function_keeps_positive_effect_guard_through_js_pipeline() {
    let mut compiler = LambdaCompiler::new();
    let run = Ident::create_local("run");
    let cond = Ident::create_local("cond");
    let seen = Ident::create_local("seen");
    let lam = Lambda::let_(
        LetKind::Strict,
        run.clone(),
        Lambda::function_(
            2,
            vec![cond.clone(), seen.clone()],
            Lambda::LifThenElse(
                Box::new(Lambda::var(cond.clone())),
                Box::new(Lambda::Lassign(
                    seen.clone(),
                    Box::new(Lambda::const_(Constant::int(1))),
                )),
                Box::new(Lambda::const_(Constant::JsUndefined { is_unit: true })),
            ),
            crate::lambda::FunctionAttribute {
                return_unit: true,
                ..Default::default()
            },
        ),
        Lambda::prim(
            Primitive::Pmakeblock(
                0,
                TagInfo::ModuleExport(vec![run.clone()]),
                Mutable::Immutable,
            ),
            vec![Lambda::var(run.clone())],
            Location::none(),
        ),
    );

    let deps = compiler.compile_deps_program(&lam);
    let rendered = print_deps_program(&deps, None);
    assert!(
        rendered.contains("if (cond) {"),
        "expected the unit-return function to keep a positive guard, got:\n{rendered}"
    );
    assert!(
        rendered.contains("seen = 1;"),
        "expected the effectful branch to stay inside the positive guard, got:\n{rendered}"
    );
    assert!(
        rendered.contains("return;"),
        "expected the unit-return branch to keep its tail return, got:\n{rendered}"
    );
    assert!(
        !rendered.contains("if (!cond) {"),
        "unexpected negative guard in final JS pipeline output:\n{rendered}"
    );
}

#[test]
fn array_subtle_tail_guard_keeps_positive_if_shape() {
    let output = compile_checked_in_test_file_to_js("array_subtle_test");
    assert!(
        output.contains("if (x.length >= 10) {"),
        "expected the checked-in fixture to keep the positive array-length guard, got:\n{output}"
    );
    assert!(
        output.contains("console.log(\"hi\");"),
        "expected the guarded effect to stay inside the positive branch, got:\n{output}"
    );
    assert!(
        output.contains("return;"),
        "expected the positive tail branch to keep its explicit return, got:\n{output}"
    );
    assert!(
        !output.contains("if (x.length < 10) {"),
        "unexpected negative early-return guard in checked-in fixture output:\n{output}"
    );
}

#[test]
fn test_primitive_keeps_positive_effectful_if_else_return_shape() {
    let output = compile_checked_in_test_file_to_js("test_primitive");
    assert!(
        output.contains("function u(b) {\n  if (b) {"),
        "expected test_primitive.u to keep OCaml's positive if/else guard, got:\n{output}"
    );
    assert!(
        output.contains("console.log(1);"),
        "expected the effectful success branch to stay inside the positive guard, got:\n{output}"
    );
    assert!(
        output.contains("} else {\n    return 7;\n  }"),
        "expected the fallback return to stay in an explicit else branch, got:\n{output}"
    );
    assert!(
        !output.contains("function u(b) {\n  if (!b) {"),
        "unexpected negative early-return guard for test_primitive.u:\n{output}"
    );
}

#[test]
fn pr6726_keeps_local_module_wrapper_call_materialized_like_ocaml() {
    let output = compile_checked_in_test_file_to_js("pr6726");
    assert!(
        output.contains("let v = test_endian_string(1);"),
        "expected pr6726 to keep the local module wrapper call materialized, got:\n{output}"
    );
    assert!(
        output.contains("v: v"),
        "expected the local module block to reference the call-result binding, got:\n{output}"
    );
    assert!(
        output.contains("/* v Not a pure module */"),
        "expected pr6726 to preserve OCaml's module-side-effect reason, got:\n{output}"
    );
    assert!(
        !output.contains("v: 33"),
        "unexpected inlined local-module wrapper call result in pr6726:\n{output}"
    );
}

#[test]
fn variant_drops_pure_local_module_wrapper_call_outside_materialized_block_like_ocaml() {
    let output = compile_checked_in_test_file_to_js("variant");
    assert!(
        !output.contains("find(p);"),
        "unexpected retained pure local-module wrapper call in variant:\n{output}"
    );
    assert!(
        output.contains("function rollback_path(subst, p) {\n  try {"),
        "expected variant.rollback_path to start directly with the try block, got:\n{output}"
    );
}

#[test]
fn a_drops_dead_functor_argument_wrapper_call_like_ocaml() {
    let output = compile_checked_in_test_file_to_js("a");
    assert!(
        !output.contains("function add(x, y) {") && !output.contains("add(1, 2);"),
        "unexpected retained dead functor-argument wrapper or call in a:\n{output}"
    );
    assert!(
        output.contains("/* No side effect */"),
        "expected a to recover OCaml's pure-module comment after dropping the dead call, got:\n{output}"
    );
}

#[test]
fn test_match_exception_keeps_direct_try_return_like_ocaml() {
    let output = compile_checked_in_test_file_to_js("test_match_exception");
    assert!(
        output.contains("function f(g, x) {\n  try {\n    return g(x);"),
        "expected test_match_exception to keep the try body in direct return position, got:\n{output}"
    );
    assert!(
        output.contains("if (exn.RE_EXN_ID === \"Not_found\") {\n      return 3;\n    }"),
        "expected test_match_exception to keep the catch return shape, got:\n{output}"
    );
    assert!(
        !output.contains("let y;")
            && !output.contains("y = g(x);")
            && !output.contains("return y;"),
        "unexpected staticcatch temp assignment shape remained in test_match_exception:\n{output}"
    );
}

#[test]
fn uncurried_always_keeps_non_module_field_partial_calls_inlineable() {
    let output = compile_checked_in_test_file_to_js("UncurriedAlways");
    assert!(
        output.contains("let a1 = [\n  \"x\",\n  \"y\",\n  \"z\"\n];"),
        "expected UncurriedAlways.AllLabels.a1 to stay inlined to the tuple literal, got:\n{output}"
    );
    assert!(
        !output.contains("let a1 = ptl$1(\"x\", \"z\");"),
        "unexpected preserved partial-wrapper call in UncurriedAlways:\n{output}"
    );
}

#[test]
fn gpr_1728_unit_if_tail_stays_as_condition_effect() {
    let output = compile_checked_in_test_file_to_js("gpr_1728_test");
    assert!(
        output.contains("Number.parseInt(x) !== 3;"),
        "expected the checked-in fixture to keep the condition as an effect statement, got:\n{output}"
    );
    assert!(
        !output.contains("if (Number.parseInt(x) !== 3) {"),
        "unexpected unit-return guard for the checked-in fixture:\n{output}"
    );
}

#[test]
fn gpr_1891_keeps_unit_polyvariant_guard_flattened_like_ocaml() {
    let output = compile_checked_in_test_file_to_js("gpr_1891_test");
    assert!(
        output.contains("if (typeof x === \"object\" && x.NAME === \"Foo\" && x.VAL === 3) {"),
        "expected gpr_1891_test.foo4 to keep the flattened payload guard, got:\n{output}"
    );
    assert!(
        output.contains("return h();"),
        "expected gpr_1891_test.foo4 to keep the guarded call in the body, got:\n{output}"
    );
    assert!(
        !output.contains(
            "if (typeof x === \"object\" && x.NAME === \"Foo\") {\n    if (x.VAL !== 3) {"
        ),
        "unexpected nested negative payload guard in gpr_1891_test.foo4:\n{output}"
    );
}

#[test]
fn gpr_3154_keeps_none_guard_chain_conjoined_like_ocaml() {
    let output = compile_checked_in_test_file_to_js("gpr_3154_test");
    assert!(
        output.contains(
            "if (match !== undefined && Primitive_option.valFromOption(match) === undefined) {"
        ),
        "expected gpr_3154_test to keep the shared fallback guard chain collapsed into one positive conjunction, got:\n{output}"
    );
    assert!(
        !output.contains("if (match === undefined) {\n      return Test_utils.ok("),
        "unexpected standalone negative guard on the option match in gpr_3154_test:\n{output}"
    );
    assert!(
        !output.contains("if (Primitive_option.valFromOption(match) !== undefined) {"),
        "unexpected nested negative payload guard in gpr_3154_test:\n{output}"
    );
}

#[test]
fn gpr_3609_keeps_explicit_else_tail_like_ocaml() {
    let output = compile_checked_in_test_file_to_js("gpr_3609_test");
    assert!(
        output.contains("if (typeof state !== \"object\") {"),
        "expected gpr_3609_test.func to keep the outer object guard, got:\n{output}"
    );
    assert!(
        output.contains("  } else {\n    return 0 + state._0 | 0;\n  }"),
        "expected gpr_3609_test.func to keep the explicit else tail, got:\n{output}"
    );
    assert!(
        !output.contains(
            "if (typeof state !== \"object\") {\n    return 0;\n  }\n  return 0 + state._0 | 0;"
        ),
        "unexpected fallthrough tail in gpr_3609_test.func:\n{output}"
    );
}

#[test]
fn gpr_3770_keeps_all_zero_guard_conjoined_like_ocaml() {
    let output = compile_checked_in_test_file_to_js("gpr_3770_test");
    assert!(
        output.contains("if (a === 0 && x._1 === 0 && x._2 === 0) {"),
        "expected gpr_3770_test.show to keep the all-zero guard collapsed into one positive conjunction, got:\n{output}"
    );
    assert!(
        output.contains("return \"zeroes\";"),
        "expected gpr_3770_test.show to keep the zero case in the guarded branch, got:\n{output}"
    );
    assert!(
        output.contains("return a.toString() + x._1.toString();"),
        "expected gpr_3770_test.show to keep the non-zero fallback return after the guard, got:\n{output}"
    );
    assert!(
        !output.contains("if (a !== 0) {"),
        "unexpected leading negative guard in gpr_3770_test.show:\n{output}"
    );
    assert!(
        !output.contains("else if (x._1 !== 0) {")
            && !output.contains("else if (x._2 !== 0) {"),
        "unexpected nested negative guard chain in gpr_3770_test.show:\n{output}"
    );
    assert!(
        !output.contains("  } else {\n    return a.toString() + x._1.toString();\n  }"),
        "unexpected explicit else tail in gpr_3770_test.show:\n{output}"
    );
}

#[test]
fn bal_set_mini_unwraps_terminal_return_blocks_before_if_fallthrough_flattening() {
    let output = compile_checked_in_test_file_to_js("bal_set_mini");
    assert!(
        output.contains("  }\n  if (hr <= (hl + 2 | 0)) {"),
        "expected the checked-in fixture to keep the right-balance guard as fallthrough after the left branch, got:\n{output}"
    );
    assert!(
        !output.contains("    } else {\n    if (hr <= (hl + 2 | 0)) {")
            && !output.contains("    } else {\n      if (hr <= (hl + 2 | 0)) {"),
        "unexpected nested else-wrapper around the right-balance guard in the checked-in fixture:\n{output}"
    );
}

#[test]
fn bal_set_mini_binds_named_variant_switch_scrutinee_once_like_ocaml() {
    let output = compile_checked_in_test_file_to_js("bal_set_mini");
    assert!(
        output.contains("let match = v;\n\nif (typeof match === \"object\") {"),
        "expected bal_set_mini to bind the shared named-variant scrutinee before the final switch dispatch, got:\n{output}"
    );
    assert!(
        !output.contains("if (typeof v === \"object\") {"),
        "unexpected direct final dispatch on v in bal_set_mini; OCaml binds the shared scrutinee first:\n{output}"
    );
}

#[test]
fn let_unwrap_keeps_declared_switch_binding_shape_like_ocaml() {
    let output = compile_checked_in_test_file_to_js("LetUnwrap");
    assert!(
        output.contains("let someResult;\n\nsomeResult = x.TAG === \"Ok\" ? x._0 : ("),
        "expected LetUnwrap to keep the declared result binding before the switch assignment, got:\n{output}"
    );
    assert!(
        !output.contains("let someResult = x.TAG === \"Ok\" ? x._0 : ("),
        "unexpected initialized declaration for LetUnwrap's switch-bound result:\n{output}"
    );
}

#[test]
fn gpr_2608_test_keeps_declared_short_circuit_binding_shape_like_snapshot() {
    let output = compile_checked_in_test_file_to_js("gpr_2608_test");
    assert!(
        output.contains("let huntGrootCondition = false;")
            && output.contains("let huntGrootCondition2 = true;"),
        "expected gpr_2608_test to keep the declared short-circuit bindings, got:\n{output}"
    );
    assert!(
        !output.contains("let tmp = false;")
            && !output.contains("let tmp$1 = true;")
            && !output.contains("let huntGrootCondition = tmp;")
            && !output.contains("let huntGrootCondition2 = tmp$1;"),
        "unexpected temporary alias binding remained in gpr_2608_test:\n{output}"
    );
}

#[test]
fn variant_pattern_matching_spreads_keeps_positive_unit_fallthrough_guards_like_ocaml() {
    let output = compile_checked_in_test_file_to_js("VariantPatternMatchingSpreads");
    assert!(
        output.contains(
            "function doWithB(b) {\n  if (b === \"One\") {\n    console.log(\"aaa\");\n    return;\n  }\n  console.log(\"twwwoooo\");"
        ),
        "expected doWithB to keep the positive-guard fallthrough shape, got:\n{output}"
    );
    assert!(
        output.contains("function lookupOpt(b) {\n  if (b !== undefined) {"),
        "expected lookupOpt to keep the positive option guard, got:\n{output}"
    );
    assert!(
        output.contains(
            "function doWithZ(z) {\n  if (z === \"First\") {\n    console.log(\"First\");\n    return;\n  }\n  console.log(\"Second\");"
        ),
        "expected doWithZ to keep the positive-guard fallthrough shape, got:\n{output}"
    );
}

#[test]
fn variant_pattern_matching_spreads_with_payloads_keeps_nested_handlers_inline_like_ocaml() {
    let output = compile_checked_in_test_file_to_js("VariantPatternMatchingSpreadsWithPayloads");
    assert!(
        output.contains(
            "function lookup2(d) {\n  if (typeof d !== \"object\") {\n    switch (d) {\n      case \"Four\" :\n      case \"Five\" :\n        return doWithB(d);\n      case \"Six\" :\n        console.log(\"Got rest of d\");\n        return;\n      default:\n        return doWithA(d);\n    }\n  } else {"
        ),
        "expected lookup2 to keep the shared const-side handler inline inside the switch, got:\n{output}"
    );
    assert!(
        output.contains(
            "  } else {\n    if (d.TAG !== \"Seven\") {\n      return doWithA(d);\n    }\n    console.log(\"Got rest of d\");\n    return;\n  }\n}"
        ),
        "expected lookup2 to keep the payload-side handler inline inside the outer else branch, got:\n{output}"
    );
    assert!(
        !output.contains("  doWithB(d);\n}"),
        "unexpected nested fallthrough handler escaped after lookup2's switch:\n{output}"
    );
}

#[test]
fn inline_record_test_keeps_positive_exception_fallthrough_guard_like_ocaml() {
    let output = compile_checked_in_test_file_to_js("inline_record_test");
    assert!(
        output.contains(
            "function ff0(x) {\n  if (x.RE_EXN_ID === A4) {\n    x.x = x.x + 1 | 0;\n    x.z = x.z + 1 | 0;\n    return;\n  }\n}"
        ),
        "expected inline_record_test.ff0 to keep the positive exception guard with guarded fallthrough, got:\n{output}"
    );
    assert!(
        !output.contains("if (x.RE_EXN_ID !== A4) {"),
        "unexpected negative early-return guard in inline_record_test.ff0:\n{output}"
    );
}

#[test]
fn json_decorders_keeps_needvalue_if_temp_declared_like_ocaml() {
    let output = compile_checked_in_test_file_to_js("json_decorders");
    assert!(
        output.contains("let tmp;\n  tmp = typeof email === \"string\" ? email : undefined;"),
        "expected json_decorders to keep the declared conditional temp before assignment, got:\n{output}"
    );
    assert!(
        !output.contains("let tmp = typeof email === \"string\" ? email : undefined;"),
        "unexpected initialized conditional temp in json_decorders:\n{output}"
    );
}

#[test]
fn res_debug_materializes_two_field_record_payload_bindings_like_ocaml() {
    let output = compile_checked_in_test_file_to_js("res_debug");
    assert!(
        output.contains("let ok_name = optionMap(undefined, x => x);")
            && output.contains("let bad_name = optionMap(undefined, x => x);"),
        "expected res_debug to materialize the optional record payload temps, got:\n{output}"
    );
    assert!(
        output.contains("let ok = {\n  name: ok_name\n};")
            && output.contains("let bad = {\n  name: bad_name\n};"),
        "expected res_debug to reuse the materialized record payload temps, got:\n{output}"
    );
}

#[test]
fn record_coercion_materializes_nested_two_field_record_blocks_like_ocaml() {
    let output = compile_checked_in_test_file_to_js("RecordCoercion");
    assert!(
        output.contains("let TestInlining_a = {\n  number: 42,\n  name: \"a\"\n};"),
        "expected RecordCoercion to keep the nested record payload materialized, got:\n{output}"
    );
    assert!(
        output.contains("let TestInlining = {\n  a: TestInlining_a,\n  name: \"a\"\n};"),
        "expected RecordCoercion to reuse the nested record temp in the module block, got:\n{output}"
    );
}

#[test]
fn record_debug_test_keeps_record_update_projection_materialized_like_ocaml() {
    let output = compile_checked_in_test_file_to_js("record_debug_test");
    assert!(
        output.contains("let u_a = 2;")
            && output.contains("let u_b = v.b;")
            && output.contains("let u = {\n  a: u_a,\n  b: u_b\n};"),
        "expected record_debug_test to keep the record-update projection materialized, got:\n{output}"
    );
    assert!(
        !output.contains("let v_b = {\n  xx: 2,\n  yy: 3\n};")
            && !output.contains("let u_b = {\n  xx: 2,\n  yy: 3\n};"),
        "did not expect record_debug_test to inline the nested allocating record field, got:\n{output}"
    );
}

#[test]
fn gpr_2503_test_keeps_obj_external_accumulator_before_optional_value_temp_like_snapshot() {
    let output = compile_checked_in_test_file_to_js("gpr_2503_test");
    assert!(
        output.contains(
            "function makeWrapper4(foo, param) {\n  console.log(2);\n  let tmp = {};\n  let tmp$1 = foo > 100 ? undefined : ("
        ),
        "expected gpr_2503_test to materialize the object accumulator before the complex optional value temp, got:\n{output}"
    );
    assert!(
        output.contains(
            "function makeWrapper3(foo, param) {\n  console.log(2);\n  let tmp = {};\n  if (foo !== undefined) {"
        ),
        "expected gpr_2503_test to keep the simple optional wrapper on the same tmp accumulator naming path, got:\n{output}"
    );
    assert!(
        !output.contains("let obj = foo > 100 ? undefined")
            && !output.contains("let obj$1 = {};"),
        "unexpected Rust-only object-temp ordering remained in gpr_2503_test:\n{output}"
    );
}

#[test]
fn derive_projector_test_collapses_pure_record_projection_like_ocaml() {
    let output = compile_checked_in_test_file_to_js("derive_projector_test");
    assert!(
        output.contains("let v = {\n  TAG: \"D_int\",\n  _0: 3\n};"),
        "expected the checked-in fixture to collapse the pure record projection to the payload value, got:\n{output}"
    );
    assert!(
        !output.contains("let v = ({") && !output.contains("}).d;"),
        "unexpected materialized fresh-record projection remained in checked-in fixture output:\n{output}"
    );
}

#[test]
fn deriving_accessors_curried_rewrites_alias_initializers_through_exported_bindings_like_snapshot(
) {
    let output = compile_checked_in_test_file_to_js("DerivingAccessorsCurried");
    assert!(
        output.contains("let _myFieldAlias = myField;")
            && output.contains("let _noParamAlias = \"NoParam\";")
            && output.contains("let _numAlias = num;")
            && output.contains("let _doubleNumAlias = doubleNum;"),
        "expected DerivingAccessorsCurried to reuse the underlying exported bindings in later alias initializers, got:\n{output}"
    );
    assert!(
        !output.contains("let myField$1 = myField;")
            && !output.contains("let num$1 = num;")
            && !output.contains("let doubleNum$1 = doubleNum;")
            && !output.contains("let _noParamAlias = noParam;"),
        "unexpected redundant same-name export aliases remained in DerivingAccessorsCurried:\n{output}"
    );
    let compose_idx = output.find("function compose").unwrap();
    let no_param_idx = output.find("let noParam = \"NoParam\";").unwrap();
    assert!(
        compose_idx < no_param_idx,
        "expected compose to remain before the rebound literal export in DerivingAccessorsCurried, got:\n{output}"
    );
}

#[test]
fn deriving_accessors_uncurried_rewrites_alias_initializers_through_exported_bindings_like_snapshot(
) {
    let output = compile_checked_in_test_file_to_js("DerivingAccessorsUncurried");
    assert!(
        output.contains("let _myFieldAlias = myField;")
            && output.contains("let _noParamAlias = \"NoParam\";")
            && output.contains("let _numAlias = num;")
            && output.contains("let _doubleNumAlias = doubleNum;"),
        "expected DerivingAccessorsUncurried to reuse the underlying exported bindings in later alias initializers, got:\n{output}"
    );
    assert!(
        !output.contains("let myField$1 = myField;")
            && !output.contains("let num$1 = num;")
            && !output.contains("let doubleNum$1 = doubleNum;")
            && !output.contains("let _noParamAlias = noParam;"),
        "unexpected redundant same-name export aliases remained in DerivingAccessorsUncurried:\n{output}"
    );
    let compose_idx = output.find("function compose").unwrap();
    let no_param_idx = output.find("let noParam = \"NoParam\";").unwrap();
    assert!(
        compose_idx < no_param_idx,
        "expected compose to remain before the rebound literal export in DerivingAccessorsUncurried, got:\n{output}"
    );
}

#[test]
fn coercion_rebinds_same_name_literal_exports_after_surviving_function_binding_like_snapshot() {
    let output = compile_checked_in_test_file_to_js("Coercion");
    let foo_idx = output.find("function foo").unwrap();
    let x_idx = output.find("let x = 1;").unwrap();
    let xx_idx = output.find("let xx = 1;").unwrap();
    assert!(
        foo_idx < x_idx && x_idx < xx_idx,
        "expected Coercion to keep the surviving function binding before the rebound literal exports, got:\n{output}"
    );
}

#[test]
fn block_alias_test_keeps_exported_alias_before_mocha_effects_like_snapshot() {
    let output = compile_checked_in_test_file_to_js("block_alias_test");
    let alias_idx = output.find("let f = Primitive_object.equal;").unwrap();
    let describe_idx = output.find("Mocha.describe(").unwrap();
    assert!(
        alias_idx < describe_idx,
        "expected block_alias_test to keep the exported alias before Mocha.describe, got:\n{output}"
    );
}

#[test]
fn ffi_arity_test_keeps_exported_alias_before_later_effects_like_snapshot() {
    let output = compile_checked_in_test_file_to_js("ffi_arity_test");
    let alias_idx = output.find("let abc_u = abc;").unwrap();
    let call_idx = output
        .rfind("((function(){console.log(\"forgiving arity\")})());")
        .unwrap();
    assert!(
        alias_idx < call_idx,
        "expected ffi_arity_test to keep abc_u before the later top-level effects, got:\n{output}"
    );
}

#[test]
fn module_parameter_test_keeps_local_module_alias_binding_materialized_like_ocaml() {
    let output = compile_checked_in_test_file_to_js("module_parameter_test");
    assert!(
        output.contains("let s = Stdlib_String;\n\nlet N = {\n  s: s\n};"),
        "expected module_parameter_test to keep the local module alias binding materialized, got:\n{output}"
    );
    assert!(
        output.contains("3, \"abc\".length"),
        "expected module_parameter_test to match current OCaml by reducing the exported wrapper call at the checked site, got:\n{output}"
    );
    assert!(
        !output.contains("s: Stdlib_String") && !output.contains("3, v(\"abc\")"),
        "unexpected inlined local-module field or stale snapshot-era wrapper call remained in module_parameter_test:\n{output}"
    );
}

#[test]
fn import_keeps_nested_module_field_alias_binding_materialized_like_snapshot() {
    let output = compile_checked_in_test_file_to_js("Import");
    assert!(
        output.contains("let N1_each = O.forEach;\n\nlet N1 = {\n  O: O,\n  each: N1_each\n};"),
        "expected Import to keep the nested module-field alias binding materialized, got:\n{output}"
    );
    assert!(
        output.contains("let N_each = N2.forEach;\n\nlet N = {\n  N0: N0,\n  N1: N1,\n  N2: N2,\n  each: N_each\n};"),
        "expected Import to keep the outer module-field alias binding materialized with the module-prefixed name, got:\n{output}"
    );
    assert!(
        !output.contains("each: O.forEach") && !output.contains("each: each$1"),
        "unexpected inlined nested module-field alias remained in Import:\n{output}"
    );
}

#[test]
fn relative_path_keeps_exported_import_alias_chain_materialized_like_snapshot() {
    let output = compile_checked_in_test_file_to_js("relative_path");
    assert!(
        output.contains("let foo = FileJs.foo;\n")
            && output.contains("let bar = foo;\n"),
        "expected relative_path to keep the exported import alias chain materialized, got:\n{output}"
    );
    assert!(
        !output.contains("let bar = FileJs.foo;"),
        "unexpected direct qualified import rebound remained in relative_path:\n{output}"
    );
}

#[test]
fn import_attributes_exact_lowered_lambda_keeps_aliases_before_logs_through_js_pipeline() {
    let lam = import_attributes_lowered_lambda();
    let simplified = crate::lambda::simplify::simplify_for_js_backend_with_jsx_preserve(
        &lam, false,
    );
    let mut compiler = LambdaCompiler::new();
    let compiled = compiler.compile_expr(&simplified);
    let mut block = compiled.prelude;
    let exports = extract_toplevel_exports(compiled.expr, &mut block)
        .expect("expected ImportAttributes-style lambda to end in a module export block");
    assert_import_attributes_alias_block_shape(&block, "after export extraction");

    let exports = compiler.coerce_toplevel_exports(&mut block, exports);
    let exports = resolve_export_aliases(&block, exports);
    let program = Program::new(block, exports);
    assert_import_attributes_alias_block_shape(&program.block, "after top-level export coercion");

    let deps = apply_js_flatten_pass(DepsProgram {
        program,
        modules: vec![],
        side_effect: module_side_effect_reason(&simplified),
    });
    assert_import_attributes_alias_block_shape(&deps.program.block, "after js_flatten");

    let deps = apply_external_shadow_pass(deps);
    assert_import_attributes_alias_block_shape(&deps.program.block, "after external_shadow");

    let deps = apply_js_tailcall_inline_pass(deps);
    assert_import_attributes_alias_block_shape(&deps.program.block, "after tailcall_inline");

    let deps = apply_js_flatten_and_mark_dead_pass(deps, false);
    assert_import_attributes_alias_block_shape(&deps.program.block, "after flatten_and_mark_dead");

    let deps = apply_js_shake_pass(deps);
    assert_import_attributes_alias_block_shape(&deps.program.block, "after js_shake");
}

#[test]
fn import_attributes_keeps_exported_alias_bindings_before_log_calls_like_snapshot() {
    let output = compile_checked_in_test_file_to_js("ImportAttributes");
    assert!(
        output.contains("let myJson = MyJsonJson;\n\nconsole.log(myJson);"),
        "expected ImportAttributes to keep the exported JSON alias binding ahead of the log call, got:\n{output}"
    );
    assert!(
        output.contains("let buttonCss = MyCssCss.button;\n\nconsole.log(buttonCss);"),
        "expected ImportAttributes to keep the exported CSS alias binding ahead of the log call, got:\n{output}"
    );
    assert!(
        !output.contains("console.log(MyJsonJson);")
            && !output.contains("console.log(MyCssCss.button);"),
        "unexpected direct imported-value logging remained in ImportAttributes:\n{output}"
    );
}

#[test]
fn bs_mutable_set_test_inlines_inner_fromarray_alias_calls_like_snapshot() {
    let output = compile_checked_in_test_file_to_js("bs_mutable_set_test");
    assert!(
        output.contains(
            "Belt_MutableSetInt.eq(cc, Belt_MutableSetInt.fromArray(Array_data_util.randomRange(0, 120)))"
        ),
        "expected bs_mutable_set_test to call Belt_MutableSetInt.fromArray directly at the checked site, got:\n{output}"
    );
    assert!(
        !output.contains("let f = Belt_MutableSetInt.fromArray;"),
        "unexpected callee alias binding remained in bs_mutable_set_test:\n{output}"
    );
}

#[test]
fn bs_mutable_set_test_keeps_exported_module_field_aliases_only_in_late_export_section() {
    let output = compile_checked_in_test_file_to_js("bs_mutable_set_test");
    assert!(
        output.find("Mocha.describe(\"Bs_mutable_set_test\"").is_some()
            && output.find("let empty = Belt_MutableSetInt.make;").is_some()
            && output.find("let fromArray = Belt_MutableSetInt.fromArray;").is_some()
            && output.find("Mocha.describe(\"Bs_mutable_set_test\"").unwrap()
                < output.find("let empty = Belt_MutableSetInt.make;").unwrap()
            && output.find("Mocha.describe(\"Bs_mutable_set_test\"").unwrap()
                < output.find("let fromArray = Belt_MutableSetInt.fromArray;").unwrap(),
        "expected bs_mutable_set_test to keep the exported module-field aliases only in the late export section, got:\n{output}"
    );
}

#[test]
fn inline_string_test_keeps_alias_materialized_named_matcher_like_snapshot() {
    let output = compile_checked_in_test_file_to_js("inline_string_test");
    assert!(
        output.contains("function f(x) {\n  if (x !== undefined) {\n    return \"Some\";\n  } else {\n    return \"None\";\n  }\n}"),
        "expected inline_string_test to keep the named matcher function materialized, got:\n{output}"
    );
    assert!(
        output.contains("console.log([\n  f(3),\n  \"None\",\n  \"Some\"\n]);"),
        "expected inline_string_test to keep the alias-substituted `f(3)` call while inlining only the direct constant cases, got:\n{output}"
    );
    assert!(
        !output.contains("console.log([\n  \"Some\",\n  \"None\",\n  \"Some\"\n]);"),
        "unexpected full constant inlining remained in inline_string_test:\n{output}"
    );
}

#[test]
fn gpr_3142_test_reuses_same_name_export_alias_bindings_like_snapshot() {
    let output = compile_checked_in_test_file_to_js("gpr_3142_test");
    assert!(
        output.contains("Test_utils.eq(\"File \\\"gpr_3142_test.res\\\", line 18, characters 7-14\", tToJs(\"a\"), \"x\")")
            && output.contains("Test_utils.eq(\"File \\\"gpr_3142_test.res\\\", line 23, characters 7-14\", tFromJs(\"x\"), \"a\")"),
        "expected gpr_3142_test to inline the exported aliases back to direct converter calls at the checked internal sites, got:\n{output}"
    );
    assert!(
        output.contains("let v = tToJs;\n\nlet u = tFromJs;"),
        "expected gpr_3142_test to keep the exported alias bindings materialized for the final export payload, got:\n{output}"
    );
    assert!(
        output.contains("export {\n  tToJs,\n  tFromJs,\n  v,\n  u,\n}")
            && output.find("Mocha.describe(\"Gpr_3142_test\"").is_some()
            && output.find("let v = tToJs;").is_some()
            && output.find("Mocha.describe(\"Gpr_3142_test\"").unwrap()
                < output.find("let v = tToJs;").unwrap()
            && !output.contains("v$1 as v")
            && !output.contains("u$1 as u"),
        "expected gpr_3142_test to keep the aliases only as late export bindings with no rebound export aliases, got:\n{output}"
    );
}

#[test]
fn string_set_reuses_same_name_export_aliases_for_module_fields_like_snapshot() {
    let output = compile_checked_in_test_file_to_js("string_set");
    assert!(
        output.contains("return Set_gen.empty;")
            && output.contains("return Set_gen.singleton(x0);")
            && output
                .contains("return Set_gen.of_sorted_list(Belt_List.sort(l, compare_elt));"),
        "expected string_set to inline exported module-field aliases at ordinary internal call sites like OCaml, got:\n{output}"
    );
    assert!(
        output.contains("let empty = Set_gen.empty;")
            && output.contains("let singleton = Set_gen.singleton;")
            && output.contains("let of_sorted_list = Set_gen.of_sorted_list;")
            && output.find("function invariant(t)").is_some()
            && output.find("let empty = Set_gen.empty;").is_some()
            && output.find("function invariant(t)").unwrap()
                < output.find("let empty = Set_gen.empty;").unwrap(),
        "expected string_set to keep those alias bindings only in the later export section, got:\n{output}"
    );
    assert!(
        output.contains("export {\n  compare_elt,\n  empty,")
            && output.contains("  singleton,")
            && output.contains("  of_sorted_list,")
            && !output.contains("empty$1 as empty")
            && !output.contains("singleton$1 as singleton")
            && !output.contains("of_sorted_list$1 as of_sorted_list"),
        "unexpected rebound export aliases remained in string_set:\n{output}"
    );
}

#[test]
fn string_bound_get_test_keeps_direct_literal_export_binding_before_internal_uses_like_snapshot(
) {
    let output = compile_checked_in_test_file_to_js("string_bound_get_test");
    assert!(
        output.contains("let v = \"ghos\";\n\nlet u_a = v[0];")
            && output.contains("function u_b() {\n  return v[-1];\n}")
            && output.find("let v = \"ghos\";").is_some()
            && output.find("let u_a = v[0];").is_some()
            && output.find("let v = \"ghos\";").unwrap()
                < output.find("let u_a = v[0];").unwrap(),
        "expected string_bound_get_test to keep the direct literal export binding ahead of later internal uses like OCaml, got:\n{output}"
    );
    assert!(
        !output.contains("function u_b() {\n  return \"ghos\"[-1];\n}"),
        "unexpected literal inlining of the exported binding into string_bound_get_test.u_b:\n{output}"
    );
}

#[test]
fn external_shadow_keeps_new_wrapper_after_new_module_binding_like_snapshot() {
    let output = compile_checked_in_test_file_to_js("ExternalShadow");
    assert!(
        output.contains("let New = {};\n\nfunction url(prim) {\n  return new URL(prim);\n}\n\nlet Global = {};"),
        "expected ExternalShadow to keep the @new wrapper after the New module binding and before Global, got:\n{output}"
    );
    assert!(
        output.find("let X = {};").is_some()
            && output.find("function url(prim) {").is_some()
            && output.find("let X = {};").unwrap()
                < output.find("function url(prim) {").unwrap(),
        "expected ExternalShadow to keep earlier module/value bindings ahead of the @new wrapper, got:\n{output}"
    );
}

#[test]
fn forward_ref_regress_keeps_props_ref_wrapper_materialized_like_snapshot() {
    let output = compile_checked_in_test_file_to_js("forwardRef_regress");
    assert!(
        output.contains("let make = React.forwardRef((props, ref) => props.children);"),
        "expected forwardRef_regress to keep the OCaml-style props/ref wrapper materialized, got:\n{output}"
    );
    assert!(
        !output.contains("function make(")
            && !output.contains("React.forwardRef(make)")
            && !output.contains("make$1 as make"),
        "unexpected helper hoist or rebound export alias remained in forwardRef_regress:\n{output}"
    );
}

#[test]
fn belt_hashmap_test_keeps_exported_hash_alias_materialized_like_snapshot() {
    let output = compile_checked_in_test_file_to_js("belt_hashmap_test");
    assert!(
        output.contains("let intHash = Hash_utils.hash;")
            && output.contains("let Y = Belt_Id.hashable(intHash, intEq);"),
        "expected belt_hashmap_test to keep the exported hash alias materialized at its internal higher-order use site, got:\n{output}"
    );
    assert!(
        !output.contains("Belt_Id.hashable(Hash_utils.hash, intEq)")
            && output.find("let intHash = Hash_utils.hash;").is_some()
            && output.find("let cmp = Primitive_int.compare;").is_some()
            && output.find("let intHash = Hash_utils.hash;").unwrap()
                < output.find("let cmp = Primitive_int.compare;").unwrap(),
        "unexpected inlined hash alias or late export-tail-only binding remained in belt_hashmap_test:\n{output}"
    );
}

#[test]
fn offset_keeps_exported_module_alias_placeholder_before_local_module_block_like_snapshot() {
    let output = compile_checked_in_test_file_to_js("offset");
    assert!(
        output.contains("let $$Set;\n\nlet M = {\n  x: 1,\n  $$Set: $$Set\n};"),
        "expected offset to keep the exported module alias placeholder before M, got:\n{output}"
    );
    assert!(
        !output.contains("$$Set: undefined")
            && !output.contains("let $$Set$1 = $$Set;")
            && !output.contains("$$Set$1 as $$Set"),
        "unexpected placeholder-field inlining or rebound export alias remained in offset:\n{output}"
    );
}

#[test]
fn gpr_977_keeps_exported_constant_name_while_inlining_non_export_uses_like_snapshot() {
    let output = compile_checked_in_test_file_to_js("gpr_977_test");
    assert!(
        output.contains("let u = f(-2147483648);"),
        "expected gpr_977_test to inline the non-export call argument to the literal, got:\n{output}"
    );
    assert!(
        output.contains("Test_utils.eq(\"File \\\"gpr_977_test.res\\\", line 15, characters 39-46\", -2147483648, u)")
            && output.contains("let min_32_int = -2147483648;"),
        "expected gpr_977_test to keep the exported constant name only at the export binding site, got:\n{output}"
    );
    assert!(
        !output.contains("let min_32_int$1 = -2147483648;")
            && !output.contains("f(min_32_int)")
            && !output.contains("Test_utils.eq(\"File \\\"gpr_977_test.res\\\", line 15, characters 39-46\", min_32_int, u)"),
        "unexpected retained internal exported-constant alias uses remained in gpr_977_test:\n{output}"
    );
}

#[test]
fn async_await_inlines_exported_wrapped_named_helper_calls_like_snapshot() {
    let output = compile_checked_in_test_file_to_js("async_await");
    assert!(
        output.contains("function next(n) {\n  return n + 1 | 0;\n}\n\nasync function useNext() {\n  return 4;\n}"),
        "expected async_await to inline the exported wrapped helper call to the constant result, got:\n{output}"
    );
    assert!(
        !output.contains("async function useNext() {\n  return next(3);\n}"),
        "unexpected retained wrapped helper call remained in async_await:\n{output}"
    );
}

#[test]
fn async_inline_keeps_same_name_export_alias_for_eta_reduced_async_wrapper_like_snapshot() {
    let output = compile_checked_in_test_file_to_js("async_inline");
    assert!(
        output.contains("let broken$2 = broken$1;"),
        "expected async_inline to keep the eta-reduced async wrapper export alias binding, got:\n{output}"
    );
    assert!(
        output.contains("broken$2 as broken,"),
        "expected async_inline to export the preserved alias binding, got:\n{output}"
    );
    assert!(
        !output.contains("broken$1 as broken,"),
        "unexpected direct export of the underlying async helper in async_inline:\n{output}"
    );
}

#[test]
fn gpr_4900_inlines_local_matcher_calls_to_constants_like_ocaml() {
    let output = compile_checked_in_test_file_to_js("gpr_4900_test");
    assert!(
        output.contains(
            "Test_utils.eq(\"File \\\"gpr_4900_test.res\\\", line 14, characters 7-14\", true, true);"
        ) && output.contains(
            "Test_utils.eq(\"File \\\"gpr_4900_test.res\\\", line 15, characters 7-14\", false, false);"
        ) && output.contains(
            "Test_utils.eq(\"File \\\"gpr_4900_test.res\\\", line 16, characters 7-14\", true, true);"
        ),
        "expected gpr_4900_test to inline the local matcher calls to constants, got:\n{output}"
    );
    assert!(
        !output.contains("let showToJs = x =>"),
        "unexpected retained local matcher helper in gpr_4900_test:\n{output}"
    );
}

#[test]
fn gpr_4924_inlines_local_variant_matcher_calls_to_constants_like_ocaml() {
    let output = compile_checked_in_test_file_to_js("gpr_4924_test");
    assert!(
        output.contains(
            "Test_utils.eq(\"File \\\"gpr_4924_test.res\\\", line 29, characters 7-14\", false, false);"
        ) && output.contains(
            "Test_utils.eq(\"File \\\"gpr_4924_test.res\\\", line 30, characters 7-14\", true, true);"
        ) && output.contains(
            "Test_utils.eq(\"File \\\"gpr_4924_test.res\\\", line 31, characters 7-14\", true, true);"
        ),
        "expected gpr_4924_test to inline the local matcher calls to constants, got:\n{output}"
    );
    assert!(
        !output.contains("let u2 = b =>"),
        "unexpected retained local matcher helper in gpr_4924_test:\n{output}"
    );
}

#[test]
fn uncurried_cast_keeps_local_module_field_alias_binding_materialized_like_ocaml() {
    let output = compile_checked_in_test_file_to_js("uncurried_cast");
    assert!(
        output.contains("let map = Belt_List.map;\n\nlet List = {\n  map: map\n};"),
        "expected uncurried_cast to keep the eta-reduced module field alias materialized in List, got:\n{output}"
    );
    assert!(
        output.contains("let l = Belt_List.map({")
            && output.contains("function partial(x) {\n  return Belt_List.map({")
            && output.contains("let l$1 = Belt_List.map({")
            && output.contains("function partial$1(extra) {\n  return Belt_List.map({"),
        "expected uncurried_cast to rewrite map call sites back to Belt_List.map like OCaml, got:\n{output}"
    );
    assert!(
        !output.contains("let List = {\n  map: Belt_List.map\n};"),
        "unexpected inlined Belt_List.map inside the local module block for uncurried_cast:\n{output}"
    );
    assert!(
        !output.contains("let l = map({")
            && !output.contains("function partial(x) {\n  return map({")
            && !output.contains("let l$1 = map({")
            && !output.contains("function partial$1(extra) {\n  return map({"),
        "unexpected residual local alias calls remained in uncurried_cast:\n{output}"
    );
}

#[test]
fn recursive_module_test_keeps_include_field_alias_binding_materialized_like_ocaml() {
    let output = compile_checked_in_test_file_to_js("recursive_module_test");
    assert!(
        output.contains("let fact$1 = M.fact;\n\nlet Fact = {\n  M: M,\n  fact: fact$1\n};"),
        "expected recursive_module_test to keep the included module field alias materialized, got:\n{output}"
    );
    assert!(
        output.contains("120, fact$1(5)"),
        "expected recursive_module_test to keep the fact$1 call shape, got:\n{output}"
    );
    assert!(
        !output.contains("let Fact_fact = M.fact;") && !output.contains("120, M.fact(5)"),
        "unexpected renamed or inlined recursive module field alias in recursive_module_test:\n{output}"
    );
}

#[test]
fn complex_while_loop_keeps_effectful_condition_blocks_inside_iifes() {
    let output = compile_checked_in_test_file_to_js("complex_while_loop");
    assert!(
        output.contains("while ((() => {")
            && output.contains("let fib = x => {")
            && output.contains("return fib(n) > 10;"),
        "expected complex_while_loop to keep the recursive condition binding scoped inside the while predicate IIFE, got:\n{output}"
    );
    assert!(
        output.contains("let b = 9;") && output.contains("return (3 + b | 0) > 10;"),
        "expected complex_while_loop's second predicate to stay as an IIFE-wrapped block, got:\n{output}"
    );
    assert!(
        !output.contains("while (fib(n) > 10)") && !output.contains("while ((3 + b | 0) > 10)"),
        "unexpected dropped predicate-prelude scope in complex_while_loop:\n{output}"
    );
}

#[test]
fn test_while_side_effect_keeps_local_condition_bindings_in_iifes() {
    let output = compile_checked_in_test_file_to_js("test_while_side_effect");
    assert!(
        output.contains("while ((() => {")
            && output.contains("let y = 3;")
            && output.contains("console.log(x.contents.toString());")
            && output.contains("y = y + 1 | 0;")
            && output.contains("x.contents = x.contents + 1 | 0;")
            && output.contains("return (fib(x.contents) + fib(x.contents) | 0) < 20;"),
        "expected test_while_side_effect to keep the local binding and side effects inside the predicate IIFE, got:\n{output}"
    );
    assert!(
        !output.contains("while (x.contents = x.contents + 1 | 0, (fib(x.contents) + fib(x.contents) | 0) < 20)"),
        "unexpected flattened predicate sequence lost the local binding scope in test_while_side_effect:\n{output}"
    );
}

#[test]
fn unit_return_function_with_for_loop_tail_keeps_negative_guard() {
    let mut compiler = LambdaCompiler::new();
    let run = Ident::create_local("run");
    let cond = Ident::create_local("cond");
    let seen = Ident::create_local("seen");
    let index = Ident::create_local("i");
    let lam = Lambda::let_(
        LetKind::Strict,
        run.clone(),
        Lambda::function_(
            2,
            vec![cond.clone(), seen.clone()],
            Lambda::LifThenElse(
                Box::new(Lambda::var(cond.clone())),
                Box::new(Lambda::for_(
                    index,
                    Lambda::const_(Constant::int(0)),
                    Lambda::const_(Constant::int(1)),
                    crate::lambda::DirectionFlag::Upto,
                    Lambda::Lassign(seen.clone(), Box::new(Lambda::const_(Constant::int(1)))),
                )),
                Box::new(Lambda::const_(Constant::JsUndefined { is_unit: true })),
            ),
            crate::lambda::FunctionAttribute {
                return_unit: true,
                ..Default::default()
            },
        ),
        Lambda::prim(
            Primitive::Pmakeblock(
                0,
                TagInfo::ModuleExport(vec![run.clone()]),
                Mutable::Immutable,
            ),
            vec![Lambda::var(run.clone())],
            Location::none(),
        ),
    );

    let deps = compiler.compile_deps_program(&lam);
    let rendered = print_deps_program(&deps, None);
    assert!(
        rendered.contains("if (!cond) {"),
        "expected the loop tail to stay as a negative guard, got:\n{rendered}"
    );
    assert!(
        !rendered.contains("if (cond) {"),
        "unexpected positive guard for loop-shaped unit tail:\n{rendered}"
    );
}

#[test]
fn unit_return_function_with_else_for_loop_tail_keeps_negative_guard() {
    let mut compiler = LambdaCompiler::new();
    let run = Ident::create_local("run");
    let cond = Ident::create_local("cond");
    let seen = Ident::create_local("seen");
    let index = Ident::create_local("i");
    let lam = Lambda::let_(
        LetKind::Strict,
        run.clone(),
        Lambda::function_(
            2,
            vec![cond.clone(), seen.clone()],
            Lambda::LifThenElse(
                Box::new(Lambda::var(cond.clone())),
                Box::new(Lambda::const_(Constant::JsUndefined { is_unit: true })),
                Box::new(Lambda::for_(
                    index,
                    Lambda::const_(Constant::int(0)),
                    Lambda::const_(Constant::int(1)),
                    crate::lambda::DirectionFlag::Upto,
                    Lambda::Lassign(seen.clone(), Box::new(Lambda::const_(Constant::int(1)))),
                )),
            ),
            crate::lambda::FunctionAttribute {
                return_unit: true,
                ..Default::default()
            },
        ),
        Lambda::prim(
            Primitive::Pmakeblock(
                0,
                TagInfo::ModuleExport(vec![run.clone()]),
                Mutable::Immutable,
            ),
            vec![Lambda::var(run.clone())],
            Location::none(),
        ),
    );

    let deps = compiler.compile_deps_program(&lam);
    let rendered = print_deps_program(&deps, None);
    assert!(
        rendered.contains("if (cond) {"),
        "expected the unit branch to stay as the explicit negative-guard source, got:\n{rendered}"
    );
    assert!(
        rendered.contains("return;"),
        "expected the unit branch to keep its explicit early return, got:\n{rendered}"
    );
    assert!(
        !rendered.contains("if (!cond) {"),
        "unexpected inverted positive guard for else-loop unit tail:\n{rendered}"
    );
}

#[test]
fn unit_return_function_with_local_while_tail_keeps_negative_guard() {
    let mut compiler = LambdaCompiler::new();
    let run = Ident::create_local("run");
    let cond = Ident::create_local("cond");
    let seen = Ident::create_local("seen");
    let loop_cond = Ident::create_local("loopCond");
    let cell = Ident::create_local("cell");
    let lam = Lambda::let_(
        LetKind::Strict,
        run.clone(),
        Lambda::function_(
            3,
            vec![cond.clone(), seen.clone(), loop_cond.clone()],
            Lambda::LifThenElse(
                Box::new(Lambda::var(cond.clone())),
                Box::new(Lambda::let_(
                    LetKind::Strict,
                    cell,
                    Lambda::const_(Constant::int(0)),
                    Lambda::while_(
                        Lambda::var(loop_cond.clone()),
                        Lambda::Lassign(
                            seen.clone(),
                            Box::new(Lambda::const_(Constant::int(1))),
                        ),
                    ),
                )),
                Box::new(Lambda::const_(Constant::JsUndefined { is_unit: true })),
            ),
            crate::lambda::FunctionAttribute {
                return_unit: true,
                ..Default::default()
            },
        ),
        Lambda::prim(
            Primitive::Pmakeblock(
                0,
                TagInfo::ModuleExport(vec![run.clone()]),
                Mutable::Immutable,
            ),
            vec![Lambda::var(run.clone())],
            Location::none(),
        ),
    );

    let deps = compiler.compile_deps_program(&lam);
    let rendered = print_deps_program(&deps, None);
    assert!(
        rendered.contains("if (!cond) {"),
        "expected the local/while tail to stay as a negative guard, got:\n{rendered}"
    );
    assert!(
        !rendered.contains("if (cond) {"),
        "unexpected positive guard for local/while unit tail:\n{rendered}"
    );
}

#[test]
fn function_return_blocks_lower_effectful_sequands_without_a_result_temp() {
    let mut compiler = LambdaCompiler::new();
    let cond = Ident::create_local("cond");
    let branch = Ident::create_local("branch");
    let compiled = compiler.compile_expr(&Lambda::Lfunction(crate::lambda::LFunction {
        arity: 1,
        params: vec![cond.clone()],
        body: Box::new(Lambda::prim(
            Primitive::Psequand,
            vec![
                Lambda::var(cond.clone()),
                Lambda::let_(
                    LetKind::Strict,
                    branch.clone(),
                    Lambda::const_(Constant::int(1)),
                    Lambda::var(branch.clone()),
                ),
            ],
            Location::none(),
        )),
        attr: crate::lambda::FunctionAttribute::default(),
    }));

    let Expression {
        desc: ExpressionDesc::Fun { body, .. },
        ..
    } = compiled.expr
    else {
        panic!("expected a function expression");
    };

    let [stmt] = body.as_slice() else {
        panic!("expected a single short-circuit lowering statement");
    };
    match &stmt.desc {
        StatementDesc::If(test, then_block, else_block) => {
            assert!(matches!(
                test,
                Expression {
                    desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                    ..
                } if id.same(&cond)
            ));

            let [branch_decl, branch_return] = then_block.as_slice() else {
                panic!("expected the right-hand branch declaration and return");
            };
            let StatementDesc::Variable(VariableDeclaration {
                ident,
                value:
                    Some(Expression {
                        desc: ExpressionDesc::Number(Number::Int { i: 1, .. }),
                        ..
                    }),
                ..
            }) = &branch_decl.desc
            else {
                panic!("expected the right-hand branch local declaration");
            };
            assert!(ident.same(&branch));
            assert!(matches!(
                branch_return,
                Statement {
                    desc: StatementDesc::Return(Expression {
                        desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                        ..
                    }),
                    ..
                } if id.same(&branch)
            ));

            let [else_return] = else_block.as_slice() else {
                panic!("expected a single false return in the else branch");
            };
            assert!(matches!(
                else_return,
                Statement {
                    desc: StatementDesc::Return(Expression {
                        desc: ExpressionDesc::Bool(false),
                        ..
                    }),
                    ..
                }
            ));
        }
        StatementDesc::Block(block) => {
            let [guard_if, branch_decl, branch_return] = block.as_slice() else {
                panic!("expected a guarded false-return plus the right-hand branch");
            };
            let StatementDesc::If(test, then_block, else_block) = &guard_if.desc else {
                panic!("expected the short-circuit false-return guard");
            };
            assert!(matches!(
                test,
                Expression {
                    desc: ExpressionDesc::JsNot(inner),
                    ..
                } if matches!(
                    &inner.desc,
                    ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)) if id.same(&cond)
                )
            ));
            assert!(else_block.is_empty());
            let [guard_return] = then_block.as_slice() else {
                panic!("expected the false-return guard body");
            };
            assert!(matches!(
                guard_return,
                Statement {
                    desc: StatementDesc::Return(Expression {
                        desc: ExpressionDesc::Bool(false),
                        ..
                    }),
                    ..
                }
            ));

            let StatementDesc::Variable(VariableDeclaration {
                ident,
                value:
                    Some(Expression {
                        desc: ExpressionDesc::Number(Number::Int { i: 1, .. }),
                        ..
                    }),
                ..
            }) = &branch_decl.desc
            else {
                panic!("expected the right-hand branch local declaration");
            };
            assert!(ident.same(&branch));
            assert!(matches!(
                branch_return,
                Statement {
                    desc: StatementDesc::Return(Expression {
                        desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                        ..
                    }),
                    ..
                } if id.same(&branch)
            ));
        }
        _ => panic!("expected direct return-position short-circuit lowering"),
    }
}

#[test]
fn let_bindings_lower_ifs_without_a_result_temp() {
    let mut compiler = LambdaCompiler::new();
    let cond = Ident::create_local("cond");
    let result = Ident::create_local("result");
    let branch = Ident::create_local("branch");
    let compiled = compiler.compile_expr(&Lambda::Llet(
        LetKind::Strict,
        result.clone(),
        Box::new(Lambda::LifThenElse(
            Box::new(Lambda::var(cond.clone())),
            Box::new(Lambda::let_(
                LetKind::Strict,
                branch.clone(),
                Lambda::const_(Constant::int(1)),
                Lambda::var(branch.clone()),
            )),
            Box::new(Lambda::const_(Constant::int(0))),
        )),
        Box::new(Lambda::var(result.clone())),
    ));

    let [result_decl, if_stmt] = compiled.prelude.as_slice() else {
        panic!("expected a declaration followed by direct if assignment");
    };
    let StatementDesc::Variable(VariableDeclaration {
        ident, value: None, ..
    }) = &result_decl.desc
    else {
        panic!("expected an uninitialized declaration for the let-bound result");
    };
    assert!(ident.same(&result));

    let StatementDesc::If(test, then_block, else_block) = &if_stmt.desc else {
        panic!("expected the let-bound if to lower directly into branch assignments");
    };
    assert!(matches!(
        test,
        Expression {
            desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
            ..
        } if id.same(&cond)
    ));

    let [branch_decl, branch_assign] = then_block.as_slice() else {
        panic!("expected the then branch declaration and assignment");
    };
    let StatementDesc::Variable(VariableDeclaration {
        ident,
        value:
            Some(Expression {
                desc: ExpressionDesc::Number(Number::Int { i: 1, .. }),
                ..
            }),
        ..
    }) = &branch_decl.desc
    else {
        panic!("expected the then branch local declaration");
    };
    assert!(ident.same(&branch));
    assert!(matches!(
        branch_assign,
        Statement {
            desc: StatementDesc::Exp(Expression {
                desc: ExpressionDesc::Bin(
                    BinOp::Eq,
                    lhs,
                    rhs
                ),
                ..
            }),
            ..
        } if matches!(
            (&lhs.desc, &rhs.desc),
            (
                ExpressionDesc::Var(crate::js_ir::VIdent::Id(lhs_id)),
                ExpressionDesc::Var(crate::js_ir::VIdent::Id(rhs_id))
            ) if lhs_id.same(&result) && rhs_id.same(&branch)
        )
    ));

    let [else_assign] = else_block.as_slice() else {
        panic!("expected a single assignment in the else branch");
    };
    assert!(matches!(
        else_assign,
        Statement {
            desc: StatementDesc::Exp(Expression {
                desc: ExpressionDesc::Bin(
                    BinOp::Eq,
                    lhs,
                    rhs
                ),
                ..
            }),
            ..
        } if matches!(
            (&lhs.desc, &rhs.desc),
            (
                ExpressionDesc::Var(crate::js_ir::VIdent::Id(lhs_id)),
                ExpressionDesc::Number(Number::Int { i: 0, .. })
            ) if lhs_id.same(&result)
        )
    ));
}

#[test]
fn let_bindings_lower_effectful_short_circuits_without_a_result_alias_temp() {
    let mut compiler = LambdaCompiler::new();
    let cond = Ident::create_local("cond");
    let result = Ident::create_local("result");
    let branch = Ident::create_local("branch");
    let compiled = compiler.compile_expr(&Lambda::Llet(
        LetKind::Strict,
        result.clone(),
        Box::new(Lambda::prim(
            Primitive::Psequand,
            vec![
                Lambda::var(cond.clone()),
                Lambda::let_(
                    LetKind::Strict,
                    branch.clone(),
                    Lambda::const_(Constant::int(1)),
                    Lambda::var(branch.clone()),
                ),
            ],
            Location::none(),
        )),
        Box::new(Lambda::var(result.clone())),
    ));

    let [result_decl, if_stmt] = compiled.prelude.as_slice() else {
        panic!("expected a declaration followed by direct short-circuit assignment");
    };
    let StatementDesc::Variable(VariableDeclaration {
        ident,
        value:
            Some(Expression {
                desc: ExpressionDesc::Bool(false),
                ..
            }),
        ..
    }) = &result_decl.desc
    else {
        panic!("expected the short-circuit target declaration");
    };
    assert!(ident.same(&result));

    let StatementDesc::If(test, then_block, else_block) = &if_stmt.desc else {
        panic!("expected the short-circuit binding to lower directly into an if");
    };
    assert!(matches!(
        test,
        Expression {
            desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
            ..
        } if id.same(&cond)
    ));
    assert!(else_block.is_empty());

    let [branch_decl, branch_assign] = then_block.as_slice() else {
        panic!("expected the right-hand branch declaration and assignment");
    };
    let StatementDesc::Variable(VariableDeclaration {
        ident,
        value:
            Some(Expression {
                desc: ExpressionDesc::Number(Number::Int { i: 1, .. }),
                ..
            }),
        ..
    }) = &branch_decl.desc
    else {
        panic!("expected the right-hand branch local declaration");
    };
    assert!(ident.same(&branch));
    assert!(matches!(
        branch_assign,
        Statement {
            desc: StatementDesc::Exp(Expression {
                desc: ExpressionDesc::Bin(BinOp::Eq, lhs, rhs),
                ..
            }),
            ..
        } if matches!(
            (&lhs.desc, &rhs.desc),
            (
                ExpressionDesc::Var(crate::js_ir::VIdent::Id(lhs_id)),
                ExpressionDesc::Var(crate::js_ir::VIdent::Id(rhs_id))
            ) if lhs_id.same(&result) && rhs_id.same(&branch)
        )
    ));
    assert!(
        !print_block(&compiled.prelude).contains("tmp"),
        "unexpected result-alias temp remained in short-circuit binding lowering"
    );
}

#[test]
fn let_bindings_merge_direct_if_assignments_into_initialized_declarations() {
    let mut compiler = LambdaCompiler::new();
    let cond = Ident::create_local("cond");
    let result = Ident::create_local("result");
    let compiled = compiler.compile_expr(&Lambda::Llet(
        LetKind::Strict,
        result.clone(),
        Box::new(Lambda::LifThenElse(
            Box::new(Lambda::var(cond.clone())),
            Box::new(Lambda::const_(Constant::int(1))),
            Box::new(Lambda::const_(Constant::int(0))),
        )),
        Box::new(Lambda::var(result.clone())),
    ));

    let [result_decl] = compiled.prelude.as_slice() else {
        panic!("expected the let-bound if to collapse into one initialized declaration");
    };
    let StatementDesc::Variable(VariableDeclaration {
        ident,
        value:
            Some(Expression {
                desc: ExpressionDesc::Cond(test, then_expr, else_expr),
                ..
            }),
        ..
    }) = &result_decl.desc
    else {
        panic!("expected a single initialized declaration for the let-bound result");
    };
    assert!(ident.same(&result));
    assert!(matches!(
        test.as_ref(),
        Expression {
            desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
            ..
        } if id.same(&cond)
    ));
    assert!(matches!(
        then_expr.as_ref(),
        Expression {
            desc: ExpressionDesc::Number(Number::Int { i: 1, .. }),
            ..
        }
    ));
    assert!(matches!(
        else_expr.as_ref(),
        Expression {
            desc: ExpressionDesc::Number(Number::Int { i: 0, .. }),
            ..
        }
    ));
}

#[test]
fn effect_blocks_lower_ifs_without_a_result_temp() {
    let mut compiler = LambdaCompiler::new();
    let cond = Ident::create_local("cond");
    let slot = Ident::create_local("slot");
    let block = compiler.compile_effect_block(&Lambda::LifThenElse(
        Box::new(Lambda::var(cond.clone())),
        Box::new(Lambda::Lsequence(
            Box::new(Lambda::Lassign(
                slot.clone(),
                Box::new(Lambda::const_(Constant::int(1))),
            )),
            Box::new(Lambda::const_(Constant::int(42))),
        )),
        Box::new(Lambda::const_(Constant::int(0))),
    ));

    let [if_stmt] = block.as_slice() else {
        panic!("expected a single direct if statement in effect context");
    };
    let StatementDesc::If(test, then_block, else_block) = &if_stmt.desc else {
        panic!("expected effect-position if lowering");
    };
    assert!(matches!(
        test,
        Expression {
            desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
            ..
        } if id.same(&cond)
    ));
    assert!(else_block.is_empty());

    let [assign_stmt] = then_block.as_slice() else {
        panic!("expected the pure branch value to be dropped");
    };
    assert!(matches!(
        assign_stmt,
        Statement {
            desc: StatementDesc::Exp(Expression {
                desc: ExpressionDesc::Bin(
                    BinOp::Eq,
                    lhs,
                    rhs
                ),
                ..
            }),
            ..
        } if matches!(
            (&lhs.desc, &rhs.desc),
            (
                ExpressionDesc::Var(crate::js_ir::VIdent::Id(lhs_id)),
                ExpressionDesc::Number(Number::Int { i: 1, .. })
            ) if lhs_id.same(&slot)
        )
    ));
}

#[test]
fn effect_blocks_keep_nested_effect_ifs_out_of_value_temps() {
    let mut compiler = LambdaCompiler::new();
    let outer = Ident::create_local("outer");
    let inner = Ident::create_local("inner");
    let lhs = Ident::create_local("lhs");
    let rhs = Ident::create_local("rhs");
    let fallback = Ident::create_local("fallback");
    let block = compiler.compile_effect_block(&Lambda::LifThenElse(
        Box::new(Lambda::var(outer.clone())),
        Box::new(Lambda::Lassign(
            lhs.clone(),
            Box::new(Lambda::const_(Constant::int(1))),
        )),
        Box::new(Lambda::LifThenElse(
            Box::new(Lambda::var(inner.clone())),
            Box::new(Lambda::Lassign(
                rhs.clone(),
                Box::new(Lambda::const_(Constant::int(2))),
            )),
            Box::new(Lambda::Lassign(
                fallback.clone(),
                Box::new(Lambda::const_(Constant::int(3))),
            )),
        )),
    ));

    let rendered = print_block(&block);
    assert!(
        !rendered.contains("let tmp"),
        "nested effect-position ifs reintroduced a value temp:\n{rendered}"
    );
    assert!(
        rendered.contains("lhs = 1"),
        "expected the outer branch assignment to remain visible:\n{rendered}"
    );
    assert!(
        rendered.contains("rhs = 2"),
        "expected the inner branch assignment to remain visible:\n{rendered}"
    );
    assert!(
        rendered.contains("fallback = 3"),
        "expected the inner fallback assignment to remain visible:\n{rendered}"
    );
}

#[test]
fn effect_blocks_keep_allocating_branches_inside_conditional_expressions_like_ocaml() {
    let mut compiler = LambdaCompiler::new();
    let cond = Ident::create_local("cond");
    let effect = Ident::create_local("effect");
    let allocating_block = Lambda::const_(Constant::Block {
        tag: 0,
        tag_info: TagInfo::tuple(),
        elements: vec![Constant::int(1), Constant::int(2)],
    });

    let block = compiler.compile_effect_block(&Lambda::LifThenElse(
        Box::new(Lambda::var(cond.clone())),
        Box::new(Lambda::Lsequence(
            Box::new(Lambda::apply(
                Lambda::var(effect.clone()),
                vec![],
                ApInfo {
                    loc: Location::none(),
                    inlined: InlineAttribute::Default,
                    status: ApplyStatus::Na,
                },
                false,
            )),
            Box::new(allocating_block.clone()),
        )),
        Box::new(allocating_block),
    ));

    let [stmt] = block.as_slice() else {
        panic!("expected the allocating branches to stay as one conditional expression");
    };
    let StatementDesc::Exp(Expression {
        desc: ExpressionDesc::Cond(test, then_expr, else_expr),
        ..
    }) = &stmt.desc
    else {
        panic!("expected effect-position if lowering to keep the conditional expression");
    };
    assert!(matches!(
        test.as_ref(),
        Expression {
            desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
            ..
        } if id.same(&cond)
    ));
    assert!(matches!(
        then_expr.as_ref(),
        Expression {
            desc: ExpressionDesc::Seq(left, right),
            ..
        } if matches!(
            (&left.as_ref().desc, &right.as_ref().desc),
            (
                ExpressionDesc::Call(func, args, _),
                ExpressionDesc::CamlBlock(_, _, _, _)
            ) if matches!(
                func.as_ref(),
                Expression {
                    desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                    ..
                } if id.same(&effect)
            )
            && args.is_empty()
        )
    ));
    assert!(matches!(
        else_expr.as_ref(),
        Expression {
            desc: ExpressionDesc::CamlBlock(_, _, _, _),
            ..
        }
    ));
}

#[test]
fn effect_blocks_keep_conditional_expressions_when_both_branches_are_effectful() {
    let mut compiler = LambdaCompiler::new();
    let cond = Ident::create_local("cond");
    let lhs = Ident::create_local("lhs");
    let rhs = Ident::create_local("rhs");
    let block = compiler.compile_effect_block(&Lambda::LifThenElse(
        Box::new(Lambda::var(cond.clone())),
        Box::new(Lambda::Lassign(
            lhs.clone(),
            Box::new(Lambda::const_(Constant::int(1))),
        )),
        Box::new(Lambda::Lassign(
            rhs.clone(),
            Box::new(Lambda::const_(Constant::int(2))),
        )),
    ));

    let [stmt] = block.as_slice() else {
        panic!("expected a single expression statement");
    };
    let StatementDesc::Exp(Expression {
        desc: ExpressionDesc::Cond(test, then_expr, else_expr),
        ..
    }) = &stmt.desc
    else {
        panic!("expected an effectful conditional expression");
    };
    assert!(matches!(
        test.as_ref(),
        Expression {
            desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
            ..
        } if id.same(&cond)
    ));
    assert!(matches!(
        (&then_expr.desc, &else_expr.desc),
        (
            ExpressionDesc::Bin(
                BinOp::Eq,
                then_lhs,
                then_rhs
            ),
            ExpressionDesc::Bin(
                BinOp::Eq,
                else_lhs,
                else_rhs
            )
        ) if matches!(
            (&then_lhs.desc, &then_rhs.desc),
            (
                ExpressionDesc::Var(crate::js_ir::VIdent::Id(lhs_id)),
                ExpressionDesc::Number(Number::Int { i: 1, .. })
            ) if lhs_id.same(&lhs)
        ) && matches!(
            (&else_lhs.desc, &else_rhs.desc),
            (
                ExpressionDesc::Var(crate::js_ir::VIdent::Id(rhs_id)),
                ExpressionDesc::Number(Number::Int { i: 2, .. })
            ) if rhs_id.same(&rhs)
        )
    ));
}

#[test]
fn sequence_prefix_ifs_use_effect_lowering_without_result_temps() {
    let mut compiler = LambdaCompiler::new();
    let cond = Ident::create_local("cond");
    let value = Ident::create_local("value");
    let compiled = compiler.compile_expr(&Lambda::Lsequence(
        Box::new(Lambda::LifThenElse(
            Box::new(Lambda::var(cond.clone())),
            Box::new(Lambda::const_(Constant::int(0))),
            Box::new(Lambda::LstaticRaise(
                1,
                vec![Lambda::const_(Constant::string("boom"))],
            )),
        )),
        Box::new(Lambda::var(value.clone())),
    ));

    assert!(
        compiled
            .prelude
            .iter()
            .all(|stmt| !matches!(stmt.desc, StatementDesc::Variable(_))),
        "effect-lowered sequence prefixes should not allocate result temps"
    );

    let [if_stmt] = compiled.prelude.as_slice() else {
        panic!("expected a single effect-position if prelude");
    };
    let StatementDesc::If(_, then_block, else_block) = &if_stmt.desc else {
        panic!("expected an effect-lowered if statement");
    };
    assert!(
        matches!(
            then_block.as_slice(),
            [Statement {
                desc: StatementDesc::Throw(_),
                ..
            }]
        ) || matches!(
            else_block.as_slice(),
            [Statement {
                desc: StatementDesc::Throw(_),
                ..
            }]
        ),
        "expected the lowered branch to throw directly"
    );
    assert!(matches!(
        compiled.expr,
        Expression {
            desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
            ..
        } if id.same(&value)
    ));
}

#[test]
fn if_value_branches_keep_assignment_continuation_through_let_bindings() {
    let mut compiler = LambdaCompiler::new();
    let outer_cond = Ident::create_local("outerCond");
    let inner_cond = Ident::create_local("innerCond");
    let alias = Ident::create_local("alias");
    let compiled = compiler.compile_expr(&Lambda::LifThenElse(
        Box::new(Lambda::var(outer_cond.clone())),
        Box::new(Lambda::Llet(
            LetKind::Strict,
            alias.clone(),
            Box::new(Lambda::const_(Constant::int(1))),
            Box::new(Lambda::LifThenElse(
                Box::new(Lambda::var(inner_cond.clone())),
                Box::new(Lambda::const_(Constant::int(2))),
                Box::new(Lambda::const_(Constant::int(3))),
            )),
        )),
        Box::new(Lambda::const_(Constant::int(4))),
    ));

    let [result_decl, if_stmt] = compiled.prelude.as_slice() else {
        panic!("expected a temp declaration and one if statement");
    };

    let result = match &result_decl.desc {
        StatementDesc::Variable(VariableDeclaration { ident, .. }) => ident.clone(),
        _ => panic!("expected a result temp declaration"),
    };
    assert_eq!(result.name(), "tmp");
    let StatementDesc::If(_, then_block, else_block) = &if_stmt.desc else {
        panic!("expected an if statement");
    };

    let [alias_decl, then_assign] = then_block.as_slice() else {
        panic!("expected the then branch to bind the alias then assign");
    };
    assert!(matches!(
        alias_decl,
        Statement {
            desc: StatementDesc::Variable(VariableDeclaration { ident, .. }),
            ..
        } if ident.same(&alias)
    ));
    assert!(matches!(
        then_assign,
        Statement {
            desc: StatementDesc::Exp(Expression {
                desc: ExpressionDesc::Bin(
                    BinOp::Eq,
                    lhs,
                    rhs
                ),
                ..
            }),
            ..
        } if matches!(
            (&lhs.desc, &rhs.desc),
            (
                ExpressionDesc::Var(crate::js_ir::VIdent::Id(lhs_id)),
                ExpressionDesc::Cond(test, consequent, alternate)
            ) if lhs_id.same(&result)
                && matches!(
                    test.as_ref(),
                    Expression {
                        desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(test_id)),
                        ..
                    } if test_id.same(&inner_cond)
                )
                && matches!(consequent.desc, ExpressionDesc::Number(Number::Int { i: 2, .. }))
                && matches!(alternate.desc, ExpressionDesc::Number(Number::Int { i: 3, .. }))
        )
    ));
    assert!(matches!(
        else_block.as_slice(),
        [Statement {
            desc: StatementDesc::Exp(Expression {
                desc: ExpressionDesc::Bin(
                    BinOp::Eq,
                    lhs,
                    rhs
                ),
                ..
            }),
            ..
        }] if matches!(
            (&lhs.desc, &rhs.desc),
            (
                ExpressionDesc::Var(crate::js_ir::VIdent::Id(lhs_id)),
                ExpressionDesc::Number(Number::Int { i: 4, .. })
            ) if lhs_id.same(&result)
        )
    ));
    assert!(matches!(
        compiled.expr,
        Expression {
            desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
            ..
        } if id.same(&result)
    ));
}

#[test]
fn if_expression_result_temp_uses_tmp_name_like_ocaml() {
    let mut compiler = LambdaCompiler::new();
    let cond = Ident::create_local("cond");
    let alias = Ident::create_local("alias");
    let compiled = compiler.compile_expr(&Lambda::LifThenElse(
        Box::new(Lambda::var(cond)),
        Box::new(Lambda::Llet(
            LetKind::Strict,
            alias.clone(),
            Box::new(Lambda::const_(Constant::int(1))),
            Box::new(Lambda::var(alias.clone())),
        )),
        Box::new(Lambda::const_(Constant::int(0))),
    ));

    let [result_decl, if_stmt] = compiled.prelude.as_slice() else {
        panic!("expected a result declaration followed by the lowered if");
    };
    let result = match &result_decl.desc {
        StatementDesc::Variable(VariableDeclaration {
            ident, value: None, ..
        }) => ident.clone(),
        _ => panic!("expected an uninitialized result temp"),
    };
    assert_eq!(result.name(), "tmp");

    let StatementDesc::If(_, then_block, else_block) = &if_stmt.desc else {
        panic!("expected an if statement assigning into the result temp");
    };
    assert!(matches!(
        then_block.as_slice(),
        [
            Statement {
                desc: StatementDesc::Variable(VariableDeclaration { ident, .. }),
                ..
            },
            Statement {
                desc: StatementDesc::Exp(Expression {
                    desc: ExpressionDesc::Bin(
                        BinOp::Eq,
                        lhs,
                        rhs
                    ),
                    ..
                }),
                ..
            }
        ] if ident.same(&alias)
            && matches!(
                (&lhs.desc, &rhs.desc),
                (
                    ExpressionDesc::Var(crate::js_ir::VIdent::Id(lhs_id)),
                    ExpressionDesc::Var(crate::js_ir::VIdent::Id(rhs_id))
                ) if lhs_id.same(&result) && rhs_id.same(&alias)
            )
    ));
    assert!(matches!(
        else_block.as_slice(),
        [Statement {
            desc: StatementDesc::Exp(Expression {
                desc: ExpressionDesc::Bin(
                    BinOp::Eq,
                    lhs,
                    rhs
                ),
                ..
            }),
            ..
        }] if matches!(
            (&lhs.desc, &rhs.desc),
            (
                ExpressionDesc::Var(crate::js_ir::VIdent::Id(lhs_id)),
                ExpressionDesc::Number(Number::Int { i: 0, .. })
            ) if lhs_id.same(&result)
        )
    ));
    assert!(matches!(
        compiled.expr,
        Expression {
            desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
            ..
        } if id.same(&result)
    ));
}

#[test]
fn named_variant_switch_expressions_split_const_and_block_dispatch() {
    let mut compiler = LambdaCompiler::new();
    let scrutinee = Ident::create_local("scrutinee");
    let compiled = compiler.compile_expr(&Lambda::Lswitch(
        Box::new(Lambda::var(scrutinee.clone())),
        LambdaSwitch {
            sw_consts_full: false,
            sw_consts: vec![(0, Lambda::const_(Constant::int(1)))],
            sw_blocks_full: false,
            sw_blocks: vec![(0, Lambda::const_(Constant::int(2)))],
            sw_failaction: Some(Box::new(Lambda::const_(Constant::int(3)))),
            sw_names: Some(SwitchNames {
                consts: vec![crate::lambda::SwitchTag::named("A")],
                blocks: vec![crate::lambda::SwitchBlock::named("B")],
            }),
        },
    ));

    let rendered = print_block(&compiled.prelude);
    assert!(
        rendered.contains("typeof scrutinee !== \"object\" ?"),
        "expected the mixed named-variant dispatch to test the const side first:\n{rendered}"
    );
    assert!(
        rendered.contains("scrutinee === \"A\" ? 1 : 3"),
        "expected the const-side conditional to stay materialized:\n{rendered}"
    );
    assert!(
        rendered.contains("scrutinee.TAG === \"B\" ? 2 : 3"),
        "expected the payload-side conditional to stay materialized:\n{rendered}"
    );
    assert!(matches!(
        compiled.expr,
        Expression {
            desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(_)),
            ..
        }
    ));
}

#[test]
fn named_variant_constant_return_switch_skips_redundant_match_temp() {
    let mut compiler = LambdaCompiler::new();
    let block = compiler.compile_return_block(&Lambda::Lswitch(
        Box::new(Lambda::const_(Constant::int(2))),
        LambdaSwitch {
            sw_consts_full: true,
            sw_consts: vec![
                (0, Lambda::const_(Constant::string("a"))),
                (1, Lambda::const_(Constant::string("b"))),
            ],
            sw_blocks_full: true,
            sw_blocks: vec![],
            sw_failaction: None,
            sw_names: Some(SwitchNames {
                consts: vec![
                    crate::lambda::SwitchTag {
                        name: "A".to_string(),
                        tag_type: Some(SwitchCaseTag::Int(0)),
                    },
                    crate::lambda::SwitchTag {
                        name: "B".to_string(),
                        tag_type: Some(SwitchCaseTag::Int(2)),
                    },
                ],
                blocks: vec![],
            }),
        },
    ));

    let [stmt] = block.as_slice() else {
        panic!("expected a single simplified return statement");
    };
    match &stmt.desc {
        StatementDesc::Return(Expression {
            desc: ExpressionDesc::Str { txt, .. },
            ..
        }) => assert_eq!(txt, "b"),
        StatementDesc::Block(inner) => {
            let [inner_stmt] = inner.as_slice() else {
                panic!("expected the simplified block to contain one return");
            };
            assert!(matches!(
                &inner_stmt.desc,
                StatementDesc::Return(Expression {
                    desc: ExpressionDesc::Str { txt, .. },
                    ..
                }) if txt == "b"
            ));
        }
        other => panic!("expected the switch to collapse to the taken branch, got {other:?}"),
    }
}

#[test]
fn named_variant_effect_switches_keep_payload_cases() {
    let mut compiler = LambdaCompiler::new();
    let action = Ident::create_local("action");
    let captured = Ident::create_local("captured");
    let block = compiler.compile_effect_block(&Lambda::Lswitch(
        Box::new(Lambda::var(action.clone())),
        LambdaSwitch {
            sw_consts_full: false,
            sw_consts: vec![(0, Lambda::unit())],
            sw_blocks_full: false,
            sw_blocks: vec![(
                0,
                Lambda::Lassign(captured.clone(), Box::new(Lambda::const_(Constant::int(1)))),
            )],
            sw_failaction: Some(Box::new(Lambda::unit())),
            sw_names: Some(SwitchNames {
                consts: vec![crate::lambda::SwitchTag::named("WithoutPayload")],
                blocks: vec![crate::lambda::SwitchBlock::named("WithPayload")],
            }),
        },
    ));

    let rendered = print_block(&block);
    assert!(
        rendered
            .contains("if (typeof action === \"object\" && action.TAG === \"WithPayload\") {"),
        "expected the payload-effect switch to stay guarded by the object/tag check:\n{rendered}"
    );
    assert!(
        rendered.contains("captured = 1;"),
        "expected the payload-effect branch to keep the assignment:\n{rendered}"
    );
}

#[test]
fn named_variant_return_switches_with_only_payload_cases_skip_object_split() {
    let mut compiler = LambdaCompiler::new();
    let action = Ident::create_local("action");
    let block = compiler.compile_return_block(&Lambda::Lswitch(
        Box::new(Lambda::var(action.clone())),
        LambdaSwitch {
            sw_consts_full: true,
            sw_consts: vec![],
            sw_blocks_full: true,
            sw_blocks: vec![
                (0, Lambda::const_(Constant::int(1))),
                (1, Lambda::const_(Constant::int(2))),
            ],
            sw_failaction: None,
            sw_names: Some(SwitchNames {
                consts: vec![],
                blocks: vec![
                    crate::lambda::SwitchBlock::named("Ok"),
                    crate::lambda::SwitchBlock::named("Error"),
                ],
            }),
        },
    ));

    let rendered = print_block(&block);
    assert!(
        rendered.contains("return action.TAG === \"Ok\" ? 1 : 2;"),
        "expected the all-payload switch to lower directly over TAG without an object split:\n{rendered}"
    );
}

#[test]
fn named_variant_mixed_const_and_identical_payload_return_cases_drop_redundant_tag_split_like_gpr_3609()
 {
    let mut compiler = LambdaCompiler::new();
    let state = Ident::create_local("state");
    let payload = Lambda::prim(
        Primitive::Paddint,
        vec![
            Lambda::const_(Constant::int(0)),
            Lambda::prim(
                Primitive::Pfield(0, FieldDbgInfo::Variant),
                vec![Lambda::var(state.clone())],
                Location::none(),
            ),
        ],
        Location::none(),
    );
    let block = compiler.compile_return_block(&Lambda::Lswitch(
        Box::new(Lambda::var(state.clone())),
        LambdaSwitch {
            sw_consts_full: true,
            sw_consts: vec![(0, Lambda::const_(Constant::int(0)))],
            sw_blocks_full: true,
            sw_blocks: vec![(0, payload.clone()), (1, payload)],
            sw_failaction: None,
            sw_names: Some(SwitchNames {
                consts: vec![crate::lambda::SwitchTag::named("Empty")],
                blocks: vec![
                    crate::lambda::SwitchBlock::named("Int1"),
                    crate::lambda::SwitchBlock::named("Int2"),
                ],
            }),
        },
    ));

    assert_eq!(
        print_block(&block),
        "return typeof state !== \"object\" ? 0 : 0 + state._0 | 0;"
    );
}

#[test]
fn named_variant_incomplete_payload_only_return_switches_keep_default_as_negated_guard() {
    let mut compiler = LambdaCompiler::new();
    let action = Ident::create_local("action");
    let block = compiler.compile_return_block(&Lambda::Lswitch(
        Box::new(Lambda::var(action.clone())),
        LambdaSwitch {
            sw_consts_full: false,
            sw_consts: vec![],
            sw_blocks_full: false,
            sw_blocks: vec![(1, Lambda::const_(Constant::int(7)))],
            sw_failaction: Some(Box::new(Lambda::const_(Constant::int(42)))),
            sw_names: Some(SwitchNames {
                consts: vec![
                    crate::lambda::SwitchTag::named("A1"),
                    crate::lambda::SwitchTag::named("A2"),
                ],
                blocks: vec![
                    crate::lambda::SwitchBlock::named("B"),
                    crate::lambda::SwitchBlock::named("C"),
                    crate::lambda::SwitchBlock::named("D"),
                ],
            }),
        },
    ));

    let rendered = print_block(&block);
    assert!(
        rendered
            .contains("return typeof action !== \"object\" || action.TAG !== \"C\" ? 42 : 7;"),
        "expected the incomplete payload-only dispatch to keep OCaml's negated default guard:\n{rendered}"
    );
}

#[test]
fn named_variant_incomplete_const_only_return_switches_keep_literal_guard() {
    let mut compiler = LambdaCompiler::new();
    let action = Ident::create_local("action");
    let block = compiler.compile_return_block(&Lambda::Lswitch(
        Box::new(Lambda::var(action.clone())),
        LambdaSwitch {
            sw_consts_full: false,
            sw_consts: vec![(0, Lambda::const_(Constant::int(1)))],
            sw_blocks_full: false,
            sw_blocks: vec![],
            sw_failaction: Some(Box::new(Lambda::const_(Constant::int(42)))),
            sw_names: Some(SwitchNames {
                consts: vec![
                    crate::lambda::SwitchTag::named("A1"),
                    crate::lambda::SwitchTag::named("A2"),
                ],
                blocks: vec![crate::lambda::SwitchBlock::named("C")],
            }),
        },
    ));

    let rendered = print_block(&block);
    assert!(
        rendered.contains("return typeof action !== \"object\" && action === \"A1\" ? 1 : 42;"),
        "expected the incomplete const-only dispatch to keep the literal-side guard:\n{rendered}"
    );
}

#[test]
fn named_variant_return_switches_keep_default_only_const_side_inside_outer_else_like_typeof_test()
 {
    let mut compiler = LambdaCompiler::new();
    let action = Ident::create_local("action");
    let block = compiler.compile_named_variant_switch_return_statements(
        Expression::var(action.clone()),
        &LambdaSwitch {
            sw_consts_full: false,
            sw_consts: vec![
                (0, Lambda::const_(Constant::int(0))),
                (1, Lambda::const_(Constant::int(0))),
                (2, Lambda::const_(Constant::int(0))),
            ],
            sw_blocks_full: false,
            sw_blocks: vec![
                (0, Lambda::const_(Constant::int(1))),
                (1, Lambda::const_(Constant::int(2))),
                (2, Lambda::const_(Constant::int(3))),
            ],
            sw_failaction: Some(Box::new(Lambda::const_(Constant::int(0)))),
            sw_names: Some(SwitchNames {
                consts: vec![
                    crate::lambda::SwitchTag::named("A"),
                    crate::lambda::SwitchTag::named("B"),
                    crate::lambda::SwitchTag::named("C"),
                ],
                blocks: vec![
                    crate::lambda::SwitchBlock::named("WithPayloadA"),
                    crate::lambda::SwitchBlock::named("WithPayloadB"),
                    crate::lambda::SwitchBlock::named("WithPayloadC"),
                ],
            }),
        },
    );

    let [dispatch] = block.as_slice() else {
        panic!("expected a single outer named-variant dispatch");
    };
    let StatementDesc::If(test, then_block, else_block) = &dispatch.desc else {
        panic!(
            "expected the mixed named-variant return dispatch to stay as an explicit if/else:\n{}",
            print_block(&block)
        );
    };
    assert!(
        matches!(
            &test.desc,
            ExpressionDesc::Bin(BinOp::NotEqEq, left, right)
                if matches!(
                    (&left.as_ref().desc, &right.as_ref().desc),
                    (
                        ExpressionDesc::Typeof(inner),
                        ExpressionDesc::Str { txt, .. }
                    ) if matches!(
                        inner.as_ref(),
                        Expression {
                            desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                            ..
                        } if id.same(&action)
                    ) && txt == "object"
                )
        ),
        "unexpected outer literal-vs-payload dispatch test:\n{}",
        print_block(&block)
    );

    let [const_switch] = then_block.as_slice() else {
        panic!(
            "expected the const branch to stay wrapped in a switch default:\n{}",
            print_block(&block)
        );
    };
    let StatementDesc::StringSwitch(const_test, const_clauses, Some(const_default)) =
        &const_switch.desc
    else {
        panic!(
            "expected the const branch to stay as a string switch with a default arm:\n{}",
            print_block(&block)
        );
    };
    assert!(
        matches!(
            &const_test.desc,
            ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)) if id.same(&action)
        ),
        "unexpected const-side switch test:\n{}",
        print_block(&block)
    );
    assert!(
        const_clauses.is_empty(),
        "expected default-duplicate const cases to filter away while keeping the switch:\n{}",
        print_block(&block)
    );
    assert_switch_default_returns_int_result(const_default, 0);

    let [payload_switch] = else_block.as_slice() else {
        panic!(
            "expected the payload branch to stay attached as the outer else block:\n{}",
            print_block(&block)
        );
    };
    let StatementDesc::StringSwitch(payload_test, payload_clauses, Some(payload_default)) =
        &payload_switch.desc
    else {
        panic!(
            "expected the payload branch to stay as a tag switch:\n{}",
            print_block(&block)
        );
    };
    assert!(
        matches!(
            &payload_test.desc,
            ExpressionDesc::StaticIndex(inner, field, _)
                if matches!(
                    inner.as_ref(),
                    Expression {
                        desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                        ..
                    } if id.same(&action)
                ) && field == "TAG"
        ),
        "expected the payload branch to switch on the variant TAG field:\n{}",
        print_block(&block)
    );
    assert_eq!(
        payload_clauses
            .iter()
            .map(|clause| clause.tag_type.clone())
            .collect::<Vec<_>>(),
        vec![
            SwitchCaseTag::String("WithPayloadA".to_string()),
            SwitchCaseTag::String("WithPayloadB".to_string()),
            SwitchCaseTag::String("WithPayloadC".to_string()),
        ]
    );
    assert_switch_case_returns_int_result(&payload_clauses[0].clause.body, 1);
    assert_switch_case_returns_int_result(&payload_clauses[1].clause.body, 2);
    assert_switch_case_returns_int_result(&payload_clauses[2].clause.body, 3);
    assert_switch_default_returns_int_result(payload_default, 0);
}

#[test]
fn named_variant_return_switches_keep_shared_final_groups_inside_the_switch_without_exits() {
    let mut compiler = LambdaCompiler::new();
    let action = Ident::create_local("action");
    let block = compiler.compile_return_block(&Lambda::Lswitch(
        Box::new(Lambda::var(action.clone())),
        LambdaSwitch {
            sw_consts_full: true,
            sw_consts: vec![],
            sw_blocks_full: true,
            sw_blocks: vec![
                (0, Lambda::const_(Constant::int(1))),
                (1, Lambda::const_(Constant::int(2))),
                (2, Lambda::const_(Constant::int(2))),
            ],
            sw_failaction: None,
            sw_names: Some(SwitchNames {
                consts: vec![],
                blocks: vec![
                    crate::lambda::SwitchBlock::named("A"),
                    crate::lambda::SwitchBlock::named("B"),
                    crate::lambda::SwitchBlock::named("C"),
                ],
            }),
        },
    ));

    let [switch_stmt] = block.as_slice() else {
        panic!("expected a single payload tag switch");
    };
    let StatementDesc::StringSwitch(test, clauses, None) = &switch_stmt.desc else {
        panic!("expected a direct payload tag switch without a default arm");
    };
    assert_tag_field_access(test, &action);
    assert_eq!(clauses.len(), 3);
    assert_eq!(clauses[0].tag_type, SwitchCaseTag::String("A".to_string()));
    assert_switch_case_returns_int_result(&clauses[0].clause.body, 1);
    assert_eq!(clauses[1].tag_type, SwitchCaseTag::String("B".to_string()));
    assert!(
        clauses[1].clause.body.is_empty(),
        "expected the first shared case to keep falling through"
    );
    assert!(!clauses[1].clause.should_break);
    assert_eq!(clauses[2].tag_type, SwitchCaseTag::String("C".to_string()));
    assert_switch_case_returns_int_result(&clauses[2].clause.body, 2);
    assert!(
        !clauses[2].clause.should_break,
        "plain shared return groups should stay in the switch without an exit-driven break"
    );
}

#[test]
fn nested_named_variant_complete_return_switches_keep_plain_handlers_inside_switch_like_test_incomplete()
 {
    let mut compiler = LambdaCompiler::new();
    let action = Ident::create_local("action");
    let action_field = || {
        Lambda::prim(
            Primitive::Pfield(0, FieldDbgInfo::Variant),
            vec![Lambda::var(action.clone())],
            Location::none(),
        )
    };
    let block = compiler.compile_return_block(&Lambda::LstaticCatch(
        Box::new(Lambda::LstaticCatch(
            Box::new(Lambda::Lswitch(
                Box::new(Lambda::var(action.clone())),
                LambdaSwitch {
                    sw_consts_full: true,
                    sw_consts: vec![],
                    sw_blocks_full: true,
                    sw_blocks: vec![
                        (0, Lambda::static_raise(1, Vec::new())),
                        (1, Lambda::static_raise(2, Vec::new())),
                        (2, Lambda::static_raise(1, Vec::new())),
                        (3, Lambda::static_raise(2, Vec::new())),
                    ],
                    sw_failaction: None,
                    sw_names: Some(SwitchNames {
                        consts: vec![],
                        blocks: vec![
                            crate::lambda::SwitchBlock::named("A"),
                            crate::lambda::SwitchBlock::named("B"),
                            crate::lambda::SwitchBlock::named("C"),
                            crate::lambda::SwitchBlock::named("D"),
                        ],
                    }),
                },
            )),
            (1, vec![]),
            Box::new(Lambda::prim(
                Primitive::Paddint,
                vec![action_field(), Lambda::const_(Constant::int(1))],
                Location::none(),
            )),
        )),
        (2, vec![]),
        Box::new(Lambda::prim(
            Primitive::Paddint,
            vec![action_field(), Lambda::const_(Constant::int(2))],
            Location::none(),
        )),
    ));
    let rendered = print_block(&block);

    let [switch_stmt] = block.as_slice() else {
        panic!(
            "expected the complete named-variant handlers to stay inside one switch:\n{rendered}"
        );
    };
    let StatementDesc::StringSwitch(test, clauses, None) = &switch_stmt.desc else {
        panic!(
            "expected a complete named-variant string switch without a trailing handler:\n{rendered}"
        );
    };
    assert_tag_field_access(test, &action);
    assert_eq!(clauses.len(), 4);
    assert_eq!(clauses[0].tag_type, SwitchCaseTag::String("A".to_string()));
    assert!(clauses[0].clause.body.is_empty());
    assert_eq!(clauses[1].tag_type, SwitchCaseTag::String("C".to_string()));
    assert_eq!(clauses[2].tag_type, SwitchCaseTag::String("B".to_string()));
    assert!(clauses[2].clause.body.is_empty());
    assert_eq!(clauses[3].tag_type, SwitchCaseTag::String("D".to_string()));

    assert_eq!(
        rendered,
        "switch (action.TAG) {\n  case \"A\" :\n  case \"C\" :\n    return action._0 + 1 | 0;\n  case \"B\" :\n  case \"D\" :\n    return action._0 + 2 | 0;\n}"
    );
}

#[test]
fn named_variant_return_switches_inline_resolved_static_handler_values_inside_the_switch() {
    let mut compiler = LambdaCompiler::new();
    let action = Ident::create_local("action");
    let block = compiler.compile_return_block(&Lambda::LstaticCatch(
        Box::new(Lambda::Lswitch(
            Box::new(Lambda::var(action.clone())),
            LambdaSwitch {
                sw_consts_full: true,
                sw_consts: vec![
                    (0, Lambda::const_(Constant::int(1))),
                    (1, Lambda::static_raise(7, Vec::new())),
                    (2, Lambda::static_raise(7, Vec::new())),
                ],
                sw_blocks_full: true,
                sw_blocks: vec![],
                sw_failaction: None,
                sw_names: Some(SwitchNames {
                    consts: vec![
                        crate::lambda::SwitchTag::named("A"),
                        crate::lambda::SwitchTag::named("B"),
                        crate::lambda::SwitchTag::named("C"),
                    ],
                    blocks: vec![],
                }),
            },
        )),
        (7, vec![]),
        Box::new(Lambda::const_(Constant::int(2))),
    ));

    let [switch_stmt] = block.as_slice() else {
        panic!("expected a single switch with the resolved handler inlined");
    };
    let StatementDesc::StringSwitch(test, clauses, None) = &switch_stmt.desc else {
        panic!("expected a named-constructor string switch without a trailing handler block");
    };
    assert!(matches!(
        test,
        Expression {
            desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
            ..
        } if id.same(&action)
    ));
    assert_eq!(clauses.len(), 3);
    assert_eq!(clauses[0].tag_type, SwitchCaseTag::String("A".to_string()));
    assert_switch_case_returns_int_result(&clauses[0].clause.body, 1);
    assert_eq!(clauses[1].tag_type, SwitchCaseTag::String("B".to_string()));
    assert!(clauses[1].clause.body.is_empty());
    assert!(!clauses[1].clause.should_break);
    assert_eq!(clauses[2].tag_type, SwitchCaseTag::String("C".to_string()));
    assert_switch_case_returns_int_result(&clauses[2].clause.body, 2);
    assert!(!clauses[2].clause.should_break);
}

#[test]
fn nested_named_variant_return_switches_keep_complete_payload_handlers_inline() {
    let mut compiler = LambdaCompiler::new();
    let action = Ident::create_local("action");
    let block = compiler.compile_return_block(&Lambda::LstaticCatch(
        Box::new(Lambda::LstaticCatch(
            Box::new(Lambda::Lswitch(
                Box::new(Lambda::var(action.clone())),
                LambdaSwitch {
                    sw_consts_full: true,
                    sw_consts: vec![
                        (0, Lambda::const_(Constant::int(1))),
                        (1, Lambda::const_(Constant::int(3))),
                        (2, Lambda::const_(Constant::int(4))),
                    ],
                    sw_blocks_full: true,
                    sw_blocks: vec![
                        (0, Lambda::static_raise(18, Vec::new())),
                        (1, Lambda::static_raise(18, Vec::new())),
                        (2, Lambda::static_raise(19, Vec::new())),
                    ],
                    sw_failaction: None,
                    sw_names: Some(SwitchNames {
                        consts: vec![
                            crate::lambda::SwitchTag::named("A"),
                            crate::lambda::SwitchTag::named("B"),
                            crate::lambda::SwitchTag::named("F"),
                        ],
                        blocks: vec![
                            crate::lambda::SwitchBlock::named("C"),
                            crate::lambda::SwitchBlock::named("D"),
                            crate::lambda::SwitchBlock::named("E"),
                        ],
                    }),
                },
            )),
            (19, vec![]),
            Box::new(Lambda::const_(Constant::int(2))),
        )),
        (18, vec![]),
        Box::new(Lambda::const_(Constant::int(1))),
    ));

    let [if_stmt] = block.as_slice() else {
        panic!("expected a single const/payload dispatch statement");
    };
    let StatementDesc::If(_, _, else_block) = &if_stmt.desc else {
        panic!("expected the named variant lowering to stay as an if dispatch");
    };
    let [switch_stmt] = else_block.as_slice() else {
        panic!("expected the payload branch to stay inside one switch");
    };
    let StatementDesc::StringSwitch(test, clauses, None) = &switch_stmt.desc else {
        panic!("expected the complete payload branch to compile without a default arm");
    };
    assert_tag_field_access(test, &action);
    assert_eq!(clauses.len(), 3);
    assert_eq!(clauses[0].tag_type, SwitchCaseTag::String("C".to_string()));
    assert!(clauses[0].clause.body.is_empty());
    assert_eq!(clauses[1].tag_type, SwitchCaseTag::String("D".to_string()));
    assert_switch_case_returns_int_result(&clauses[1].clause.body, 1);
    assert_eq!(clauses[2].tag_type, SwitchCaseTag::String("E".to_string()));
    assert_switch_case_returns_int_result(&clauses[2].clause.body, 2);
}

#[test]
fn named_variant_return_switches_preserve_binding_temps_in_hoisted_shared_tails() {
    let mut compiler = LambdaCompiler::new();
    let action = Ident::create_local("action");
    let inner = Ident::create_local("inner");
    let carried = Ident::create_local("carried");
    let block = compiler.compile_return_block(&Lambda::LstaticCatch(
        Box::new(Lambda::LstaticCatch(
            Box::new(Lambda::Lswitch(
                Box::new(Lambda::var(action.clone())),
                LambdaSwitch {
                    sw_consts_full: true,
                    sw_consts: vec![
                        (0, Lambda::const_(Constant::int(1))),
                        (1, Lambda::static_raise(3, Vec::new())),
                        (2, Lambda::static_raise(3, Vec::new())),
                    ],
                    sw_blocks_full: true,
                    sw_blocks: vec![],
                    sw_failaction: None,
                    sw_names: Some(SwitchNames {
                        consts: vec![
                            crate::lambda::SwitchTag::named("A"),
                            crate::lambda::SwitchTag::named("B"),
                            crate::lambda::SwitchTag::named("C"),
                        ],
                        blocks: vec![],
                    }),
                },
            )),
            (3, vec![]),
            Box::new(Lambda::let_(
                LetKind::Strict,
                inner.clone(),
                Lambda::const_(Constant::int(5)),
                Lambda::static_raise(2, vec![Lambda::var(inner.clone())]),
            )),
        )),
        (2, vec![carried.clone()]),
        Box::new(Lambda::prim(
            Primitive::Pmulint,
            vec![Lambda::var(carried.clone()), Lambda::var(carried.clone())],
            Location::none(),
        )),
    ));

    let rendered = print_block(&block);
    assert!(
        rendered.contains("case \"B\" :\n  case \"C\" :\n    break;"),
        "expected the grouped shared tail to stay after the switch:\n{rendered}"
    );
    assert!(
        rendered.contains("let carried = inner;"),
        "expected the outer staticcatch binding to stay materialized as a temp:\n{rendered}"
    );
    assert!(
        rendered.contains("return carried * carried | 0;"),
        "expected the hoisted tail to return through the bound temp:\n{rendered}"
    );
}

#[test]
fn builtin_untagged_block_switch_expressions_dispatch_on_object_runtime_shape() {
    let mut compiler = LambdaCompiler::new();
    let value = Ident::create_local("value");
    let body_id = Ident::create_local("body");
    let compiled = compiler.compile_expr(&Lambda::Lswitch(
        Box::new(Lambda::var(value.clone())),
        LambdaSwitch {
            sw_consts_full: false,
            sw_consts: vec![],
            sw_blocks_full: false,
            sw_blocks: vec![(
                0,
                Lambda::let_(
                    LetKind::Strict,
                    body_id.clone(),
                    Lambda::const_(Constant::int(1)),
                    Lambda::var(body_id.clone()),
                ),
            )],
            sw_failaction: Some(Box::new(Lambda::const_(Constant::int(0)))),
            sw_names: Some(SwitchNames {
                consts: vec![],
                blocks: vec![crate::lambda::SwitchBlock {
                    tag: crate::lambda::SwitchTag::named("Object"),
                    tag_name: None,
                    block_type: Some(crate::lambda::SwitchBlockType::Object),
                }],
            }),
        },
    ));

    let [declare, dispatch] = compiled.prelude.as_slice() else {
        panic!("expected a result declaration followed by object dispatch");
    };
    let StatementDesc::Variable(VariableDeclaration { ident: result, .. }) = &declare.desc
    else {
        panic!("expected the switch result declaration");
    };
    let StatementDesc::If(cond, then_block, else_block) = &dispatch.desc else {
        panic!("expected an object runtime check around the block case");
    };

    assert_typeof_object_check(cond, &value, true);
    assert!(matches!(
        then_block.as_slice(),
        [
            Statement {
                desc: StatementDesc::Variable(VariableDeclaration {
                    ident,
                    value: Some(Expression {
                        desc: ExpressionDesc::Number(Number::Int { i, .. }),
                        ..
                    }),
                    ..
                }),
                ..
            },
            Statement {
                desc: StatementDesc::Exp(Expression {
                    desc: ExpressionDesc::Bin(BinOp::Eq, left, right),
                    ..
                }),
                ..
            }
        ] if ident.same(&body_id)
            && *i == 1
            && matches!(
                left.as_ref(),
                Expression {
                    desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                    ..
                } if id.same(result)
            )
            && matches!(
                right.as_ref(),
                Expression {
                    desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                    ..
                } if id.same(&body_id)
            )
    ));
    assert_switch_default_assigns_int_result(else_block, result, 0);
}

#[test]
fn builtin_untagged_object_switches_use_plain_object_check_after_array_split() {
    let mut compiler = LambdaCompiler::new();
    let value = Ident::create_local("value");
    let array_seen = Ident::create_local("array_seen");
    let object_seen = Ident::create_local("object_seen");
    let block = compiler.compile_effect_block(&Lambda::Lswitch(
        Box::new(Lambda::var(value.clone())),
        LambdaSwitch {
            sw_consts_full: false,
            sw_consts: vec![],
            sw_blocks_full: false,
            sw_blocks: vec![
                (
                    0,
                    Lambda::Lassign(
                        array_seen.clone(),
                        Box::new(Lambda::const_(Constant::int(1))),
                    ),
                ),
                (
                    1,
                    Lambda::Lassign(
                        object_seen.clone(),
                        Box::new(Lambda::const_(Constant::int(2))),
                    ),
                ),
            ],
            sw_failaction: Some(Box::new(Lambda::unit())),
            sw_names: Some(SwitchNames {
                consts: vec![],
                blocks: vec![
                    crate::lambda::SwitchBlock {
                        tag: crate::lambda::SwitchTag::named("Array"),
                        tag_name: None,
                        block_type: Some(crate::lambda::SwitchBlockType::Instance(
                            "Array".to_string(),
                        )),
                    },
                    crate::lambda::SwitchBlock {
                        tag: crate::lambda::SwitchTag::named("Object"),
                        tag_name: None,
                        block_type: Some(crate::lambda::SwitchBlockType::Object),
                    },
                ],
            }),
        },
    ));

    let [dispatch] = block.as_slice() else {
        panic!("expected an array/object dispatch chain");
    };
    let StatementDesc::If(array_cond, _, else_block) = &dispatch.desc else {
        panic!("expected the array case to lower to a runtime if-check");
    };
    assert_array_is_array_call(array_cond, &value);

    let [object_dispatch] = else_block.as_slice() else {
        panic!("expected an object fallback after the array case");
    };
    let StatementDesc::If(object_cond, _, _) = &object_dispatch.desc else {
        panic!("expected the object fallback to be another runtime if-check");
    };
    assert_typeof_object_check(object_cond, &value, true);
}

#[test]
fn object_and_array_untagged_return_switches_keep_object_inside_typeof_switch_like_ocaml() {
    let mut compiler = LambdaCompiler::new();
    let value = Ident::create_local("value");
    let block = compiler.compile_untagged_variant_switch_return_statements(
        Expression::var(value.clone()),
        &LambdaSwitch {
            sw_consts_full: true,
            sw_consts: vec![],
            sw_blocks_full: true,
            sw_blocks: vec![
                (0, Lambda::const_(Constant::int(1))),
                (1, Lambda::const_(Constant::int(2))),
                (2, Lambda::const_(Constant::int(3))),
                (3, Lambda::const_(Constant::int(4))),
            ],
            sw_failaction: None,
            sw_names: Some(SwitchNames {
                consts: vec![],
                blocks: vec![
                    crate::lambda::SwitchBlock {
                        tag: crate::lambda::SwitchTag::named("String"),
                        tag_name: None,
                        block_type: Some(crate::lambda::SwitchBlockType::String),
                    },
                    crate::lambda::SwitchBlock {
                        tag: crate::lambda::SwitchTag::named("Number"),
                        tag_name: None,
                        block_type: Some(crate::lambda::SwitchBlockType::Int),
                    },
                    crate::lambda::SwitchBlock {
                        tag: crate::lambda::SwitchTag::named("Object"),
                        tag_name: None,
                        block_type: Some(crate::lambda::SwitchBlockType::Object),
                    },
                    crate::lambda::SwitchBlock {
                        tag: crate::lambda::SwitchTag::named("Array"),
                        tag_name: None,
                        block_type: Some(crate::lambda::SwitchBlockType::Instance(
                            "Array".to_string(),
                        )),
                    },
                ],
            }),
        },
    );
    let statements = match block.as_slice() {
        [
            Statement {
                desc: StatementDesc::Block(inner),
                ..
            },
        ] => inner.as_slice(),
        other => other,
    };

    let [dispatch, typeof_switch] = statements else {
        panic!("expected an Array runtime split followed by a typeof switch");
    };
    let StatementDesc::If(array_cond, then_block, else_block) = &dispatch.desc else {
        panic!("expected the Array case to lower to a runtime if-check");
    };
    assert_array_is_array_call(array_cond, &value);
    assert_switch_case_returns_int_result(then_block, 4);
    assert!(else_block.is_empty());

    let StatementDesc::StringSwitch(test, clauses, None) = &typeof_switch.desc else {
        panic!("expected the remaining block cases to stay inside a typeof switch");
    };
    assert!(matches!(
        test,
        Expression {
            desc: ExpressionDesc::Typeof(inner),
            ..
        } if matches!(
            inner.as_ref(),
            Expression {
                desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                ..
            } if id.same(&value)
        )
    ));
    assert_eq!(
        clauses
            .iter()
            .map(|clause| clause.tag_type.clone())
            .collect::<Vec<_>>(),
        vec![
            SwitchCaseTag::String("string".to_string()),
            SwitchCaseTag::String("number".to_string()),
            SwitchCaseTag::String("object".to_string()),
        ]
    );
    assert_switch_case_returns_int_result(&clauses[2].clause.body, 3);
}

#[test]
fn mixed_array_object_function_untagged_return_switches_keep_typeof_tail_as_switch() {
    let mut compiler = LambdaCompiler::new();
    let value = Ident::create_local("value");
    let block = compiler.compile_untagged_variant_switch_return_statements(
        Expression::var(value.clone()),
        &LambdaSwitch {
            sw_consts_full: true,
            sw_consts: vec![],
            sw_blocks_full: true,
            sw_blocks: vec![
                (0, Lambda::const_(Constant::int(1))),
                (1, Lambda::const_(Constant::int(2))),
                (2, Lambda::const_(Constant::int(3))),
            ],
            sw_failaction: None,
            sw_names: Some(SwitchNames {
                consts: vec![],
                blocks: vec![
                    crate::lambda::SwitchBlock {
                        tag: crate::lambda::SwitchTag::named("Array"),
                        tag_name: None,
                        block_type: Some(crate::lambda::SwitchBlockType::Instance(
                            "Array".to_string(),
                        )),
                    },
                    crate::lambda::SwitchBlock {
                        tag: crate::lambda::SwitchTag::named("Object"),
                        tag_name: None,
                        block_type: Some(crate::lambda::SwitchBlockType::Object),
                    },
                    crate::lambda::SwitchBlock {
                        tag: crate::lambda::SwitchTag::named("Function"),
                        tag_name: None,
                        block_type: Some(crate::lambda::SwitchBlockType::Function),
                    },
                ],
            }),
        },
    );
    let statements = match block.as_slice() {
        [
            Statement {
                desc: StatementDesc::Block(inner),
                ..
            },
        ] => inner.as_slice(),
        other => other,
    };

    let [dispatch, typeof_switch] = statements else {
        panic!("expected an Array runtime split followed by a typeof switch");
    };
    let StatementDesc::If(array_cond, then_block, else_block) = &dispatch.desc else {
        panic!("expected the Array case to lower to a runtime if-check");
    };
    assert_array_is_array_call(array_cond, &value);
    assert_switch_case_returns_int_result(then_block, 1);
    assert!(else_block.is_empty());

    let StatementDesc::StringSwitch(test, clauses, None) = &typeof_switch.desc else {
        panic!("expected the remaining object/function cases to stay in a typeof switch");
    };
    assert!(matches!(
        test,
        Expression {
            desc: ExpressionDesc::Typeof(inner),
            ..
        } if matches!(
            inner.as_ref(),
            Expression {
                desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                ..
            } if id.same(&value)
        )
    ));
    assert_eq!(
        clauses
            .iter()
            .map(|clause| clause.tag_type.clone())
            .collect::<Vec<_>>(),
        vec![
            SwitchCaseTag::String("object".to_string()),
            SwitchCaseTag::String("function".to_string()),
        ]
    );
    assert_switch_case_returns_int_result(&clauses[0].clause.body, 2);
    assert_switch_case_returns_int_result(&clauses[1].clause.body, 3);
}

#[test]
fn mixed_literal_and_block_untagged_return_dispatch_keeps_outer_else_block() {
    let mut compiler = LambdaCompiler::new();
    let value = Ident::create_local("value");
    let string_seen = Ident::create_local("string_seen");
    let int_seen = Ident::create_local("int_seen");
    let array_seen = Ident::create_local("array_seen");
    let object_seen = Ident::create_local("object_seen");
    let mark = |slot: &Ident, value| {
        Lambda::seq(
            Lambda::Lassign(slot.clone(), Box::new(Lambda::const_(Constant::int(value)))),
            Lambda::unit(),
        )
    };
    let block = compiler.compile_untagged_variant_switch_return_statements(
        Expression::var(value.clone()),
        &LambdaSwitch {
            sw_consts_full: true,
            sw_consts: vec![(0, mark(&string_seen, 1)), (1, mark(&int_seen, 2))],
            sw_blocks_full: true,
            sw_blocks: vec![(0, mark(&array_seen, 3)), (1, mark(&object_seen, 4))],
            sw_failaction: None,
            sw_names: Some(SwitchNames {
                consts: vec![
                    crate::lambda::SwitchTag {
                        name: "test".to_string(),
                        tag_type: Some(SwitchCaseTag::String("test".to_string())),
                    },
                    crate::lambda::SwitchTag {
                        name: "Twelve".to_string(),
                        tag_type: Some(SwitchCaseTag::Int(12)),
                    },
                ],
                blocks: vec![
                    crate::lambda::SwitchBlock {
                        tag: crate::lambda::SwitchTag::named("Array"),
                        tag_name: None,
                        block_type: Some(crate::lambda::SwitchBlockType::Instance(
                            "Array".to_string(),
                        )),
                    },
                    crate::lambda::SwitchBlock {
                        tag: crate::lambda::SwitchTag::named("Object"),
                        tag_name: None,
                        block_type: Some(crate::lambda::SwitchBlockType::Object),
                    },
                ],
            }),
        },
    );

    let [dispatch] = block.as_slice() else {
        panic!("expected a single outer literal-vs-block dispatch");
    };
    let StatementDesc::If(_, then_block, else_block) = &dispatch.desc else {
        panic!("expected the mixed dispatch to stay as an explicit if/else");
    };
    assert!(
        matches!(
            then_block.as_slice(),
            [Statement {
                desc: StatementDesc::Block(_),
                ..
            }]
        ),
        "expected the small literal return switch to stay wrapped inside the outer dispatch:\n{}",
        print_block(&block)
    );
    assert!(
        !else_block.is_empty(),
        "expected the block branch to stay attached as an else block:\n{}",
        print_block(&block)
    );
}

#[test]
fn mixed_array_object_function_untagged_effect_switches_keep_typeof_tail_as_switch() {
    let mut compiler = LambdaCompiler::new();
    let value = Ident::create_local("value");
    let array_seen = Ident::create_local("array_seen");
    let object_seen = Ident::create_local("object_seen");
    let function_seen = Ident::create_local("function_seen");
    let block = compiler.compile_effect_block(&Lambda::Lswitch(
        Box::new(Lambda::var(value.clone())),
        LambdaSwitch {
            sw_consts_full: true,
            sw_consts: vec![],
            sw_blocks_full: true,
            sw_blocks: vec![
                (
                    0,
                    Lambda::Lassign(
                        array_seen.clone(),
                        Box::new(Lambda::const_(Constant::int(1))),
                    ),
                ),
                (
                    1,
                    Lambda::Lassign(
                        object_seen.clone(),
                        Box::new(Lambda::const_(Constant::int(2))),
                    ),
                ),
                (
                    2,
                    Lambda::Lassign(
                        function_seen.clone(),
                        Box::new(Lambda::const_(Constant::int(3))),
                    ),
                ),
            ],
            sw_failaction: None,
            sw_names: Some(SwitchNames {
                consts: vec![],
                blocks: vec![
                    crate::lambda::SwitchBlock {
                        tag: crate::lambda::SwitchTag::named("Array"),
                        tag_name: None,
                        block_type: Some(crate::lambda::SwitchBlockType::Instance(
                            "Array".to_string(),
                        )),
                    },
                    crate::lambda::SwitchBlock {
                        tag: crate::lambda::SwitchTag::named("Object"),
                        tag_name: None,
                        block_type: Some(crate::lambda::SwitchBlockType::Object),
                    },
                    crate::lambda::SwitchBlock {
                        tag: crate::lambda::SwitchTag::named("Function"),
                        tag_name: None,
                        block_type: Some(crate::lambda::SwitchBlockType::Function),
                    },
                ],
            }),
        },
    ));
    let statements = match block.as_slice() {
        [
            Statement {
                desc: StatementDesc::Block(inner),
                ..
            },
        ] => inner.as_slice(),
        other => other,
    };

    let [dispatch] = statements else {
        panic!("expected an Array runtime split with a typeof-switch fallback");
    };
    let StatementDesc::If(array_cond, then_block, else_block) = &dispatch.desc else {
        panic!("expected the Array case to lower to a runtime if-check");
    };
    assert_array_is_array_call(array_cond, &value);
    assert_eq!(then_block.len(), 1);
    let StatementDesc::Exp(expr) = &then_block[0].desc else {
        panic!("expected the Array branch to contain the assignment effect");
    };
    assert_assignment_to_int(expr, &array_seen, 1);
    let [typeof_switch] = else_block.as_slice() else {
        panic!("expected the object/function fallback to stay inside a typeof switch");
    };

    let StatementDesc::StringSwitch(test, clauses, None) = &typeof_switch.desc else {
        panic!("expected the remaining object/function cases to stay in a typeof switch");
    };
    assert!(matches!(
        test,
        Expression {
            desc: ExpressionDesc::Typeof(inner),
            ..
        } if matches!(
            inner.as_ref(),
            Expression {
                desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                ..
            } if id.same(&value)
        )
    ));
    assert_eq!(
        clauses
            .iter()
            .map(|clause| clause.tag_type.clone())
            .collect::<Vec<_>>(),
        vec![
            SwitchCaseTag::String("object".to_string()),
            SwitchCaseTag::String("function".to_string()),
        ]
    );
    assert_eq!(clauses[0].clause.body.len(), 1);
    let StatementDesc::Exp(expr) = &clauses[0].clause.body[0].desc else {
        panic!("expected the object clause to contain the assignment effect");
    };
    assert_assignment_to_int(expr, &object_seen, 2);
    assert_eq!(clauses[1].clause.body.len(), 1);
    let StatementDesc::Exp(expr) = &clauses[1].clause.body[0].desc else {
        panic!("expected the function clause to contain the assignment effect");
    };
    assert_assignment_to_int(expr, &function_seen, 3);
}

#[test]
fn untagged_literal_dispatch_keeps_ocaml_case_order() {
    let mut compiler = LambdaCompiler::new();
    let value = Ident::create_local("value");
    let block = compiler.compile_untagged_variant_switch_return_statements(
        Expression::var(value.clone()),
        &LambdaSwitch {
            sw_consts_full: true,
            sw_consts: vec![
                (0, Lambda::const_(Constant::int(1))),
                (1, Lambda::const_(Constant::int(2))),
                (2, Lambda::const_(Constant::int(3))),
            ],
            sw_blocks_full: true,
            sw_blocks: vec![(0, Lambda::const_(Constant::int(4)))],
            sw_failaction: None,
            sw_names: Some(SwitchNames {
                consts: vec![
                    crate::lambda::SwitchTag::named("One"),
                    crate::lambda::SwitchTag::named("Two"),
                    crate::lambda::SwitchTag::named("Three"),
                ],
                blocks: vec![crate::lambda::SwitchBlock {
                    tag: crate::lambda::SwitchTag::named("FutureAddedValue"),
                    tag_name: None,
                    block_type: Some(crate::lambda::SwitchBlockType::String),
                }],
            }),
        },
    );

    let rendered = print_block(&block);
    assert!(
        rendered.contains("value !== \"One\" && value !== \"Three\" && value !== \"Two\""),
        "expected OCaml-style literal dispatch order from switch names:\n{rendered}"
    );
}

#[test]
fn mixed_untagged_literal_dispatch_keeps_ocaml_block_overlap_order() {
    let mut compiler = LambdaCompiler::new();
    let value = Ident::create_local("value");
    let block = compiler.compile_untagged_variant_switch_return_statements(
        Expression::var(value.clone()),
        &LambdaSwitch {
            sw_consts_full: true,
            sw_consts: vec![
                (0, Lambda::const_(Constant::int(1))),
                (1, Lambda::const_(Constant::int(2))),
                (2, Lambda::const_(Constant::int(3))),
                (3, Lambda::const_(Constant::int(4))),
            ],
            sw_blocks_full: true,
            sw_blocks: vec![
                (0, Lambda::const_(Constant::int(5))),
                (1, Lambda::const_(Constant::int(6))),
                (2, Lambda::const_(Constant::int(7))),
            ],
            sw_failaction: None,
            sw_names: Some(SwitchNames {
                consts: vec![
                    crate::lambda::SwitchTag::named("A"),
                    crate::lambda::SwitchTag::named("B"),
                    crate::lambda::SwitchTag::named("C"),
                    crate::lambda::SwitchTag::named("D"),
                ],
                blocks: vec![
                    crate::lambda::SwitchBlock {
                        tag: crate::lambda::SwitchTag::named("String"),
                        tag_name: None,
                        block_type: Some(crate::lambda::SwitchBlockType::String),
                    },
                    crate::lambda::SwitchBlock {
                        tag: crate::lambda::SwitchTag::named("Int"),
                        tag_name: None,
                        block_type: Some(crate::lambda::SwitchBlockType::Int),
                    },
                    crate::lambda::SwitchBlock {
                        tag: crate::lambda::SwitchTag::named("Object"),
                        tag_name: None,
                        block_type: Some(crate::lambda::SwitchBlockType::Object),
                    },
                ],
            }),
        },
    );

    let rendered = print_block(&block);
    assert!(
        rendered.contains(
            "value === \"A\" || value === \"D\" || value === \"B\" || value === \"C\""
        ),
        "expected OCaml-style literal dispatch order across overlapping block kinds:\n{rendered}"
    );
}

#[test]
fn named_string_effect_switches_filter_default_duplicates_before_small_lowering() {
    let mut compiler = LambdaCompiler::new();
    let key = Ident::create_local("key");
    let seen = Ident::create_local("seen");
    let literal_tag = |txt: &str| crate::lambda::SwitchTag {
        name: txt.to_string(),
        tag_type: Some(crate::lambda::SwitchCaseTag::String(txt.to_string())),
    };
    let unit = Lambda::const_(Constant::JsUndefined { is_unit: true });
    let effect = Lambda::Lassign(seen.clone(), Box::new(Lambda::const_(Constant::int(1))));
    let cases = vec![
        (literal_tag("a").tag_type.unwrap(), &unit),
        (literal_tag("b").tag_type.unwrap(), &unit),
        (literal_tag("c").tag_type.unwrap(), &unit),
        (literal_tag("d").tag_type.unwrap(), &unit),
        (literal_tag("e").tag_type.unwrap(), &unit),
        (literal_tag("f").tag_type.unwrap(), &unit),
        (literal_tag("g").tag_type.unwrap(), &unit),
        (literal_tag("h").tag_type.unwrap(), &unit),
        (literal_tag("i").tag_type.unwrap(), &unit),
        (literal_tag("j").tag_type.unwrap(), &unit),
        (literal_tag("k").tag_type.unwrap(), &unit),
        (literal_tag("l").tag_type.unwrap(), &unit),
        (literal_tag("m").tag_type.unwrap(), &unit),
        (literal_tag("n").tag_type.unwrap(), &unit),
        (literal_tag("o").tag_type.unwrap(), &unit),
        (literal_tag("p").tag_type.unwrap(), &unit),
        (literal_tag("q").tag_type.unwrap(), &unit),
        (literal_tag("r").tag_type.unwrap(), &unit),
        (literal_tag("s").tag_type.unwrap(), &unit),
        (literal_tag("t").tag_type.unwrap(), &unit),
        (literal_tag("u").tag_type.unwrap(), &unit),
        (literal_tag("v").tag_type.unwrap(), &unit),
        (literal_tag("w").tag_type.unwrap(), &unit),
        (literal_tag("x").tag_type.unwrap(), &unit),
        (literal_tag("y").tag_type.unwrap(), &unit),
        (literal_tag("z").tag_type.unwrap(), &unit),
        (literal_tag("space").tag_type.unwrap(), &effect),
    ];
    let block = compiler.compile_named_string_switch_effect_with_strategy(
        Expression::var(key.clone()),
        &cases,
        Some(&unit),
        false,
        true,
    );
    let rendered = print_block(&block);
    assert!(
        rendered.contains("if (key === \"space\") {"),
        "expected default-duplicate string cases to filter before the small lowering:\n{rendered}"
    );
    assert!(
        !rendered.contains("key !== \"a\""),
        "expected the broad literal-membership guard to disappear after filtering:\n{rendered}"
    );
}

fn mixed_untagged_string_overlap_switch(
    space_body: Lambda,
    default_body: Lambda,
) -> LambdaSwitch {
    let literal_tag = |txt: &str| crate::lambda::SwitchTag {
        name: txt.to_string(),
        tag_type: Some(crate::lambda::SwitchCaseTag::String(txt.to_string())),
    };

    LambdaSwitch {
        sw_consts_full: false,
        sw_consts: vec![
            (0, default_body.clone()),
            (1, default_body.clone()),
            (2, space_body),
        ],
        sw_blocks_full: false,
        sw_blocks: vec![],
        sw_failaction: Some(Box::new(default_body)),
        sw_names: Some(SwitchNames {
            consts: vec![literal_tag("a"), literal_tag("b"), literal_tag("space")],
            blocks: vec![crate::lambda::SwitchBlock {
                tag: crate::lambda::SwitchTag::named("String"),
                tag_name: None,
                block_type: Some(crate::lambda::SwitchBlockType::String),
            }],
        }),
    }
}

#[test]
fn mixed_untagged_string_effect_switches_filter_default_duplicates_before_small_lowering() {
    let mut compiler = LambdaCompiler::new();
    let key = Ident::create_local("key");
    let seen = Ident::create_local("seen");
    let unit = Lambda::const_(Constant::JsUndefined { is_unit: true });
    let block = compiler.compile_untagged_variant_switch_effect_statements(
        Expression::var(key.clone()),
        &mixed_untagged_string_overlap_switch(
            Lambda::Lassign(seen.clone(), Box::new(Lambda::const_(Constant::int(1)))),
            unit,
        ),
    );
    let rendered = print_block(&block);
    assert!(
        rendered.contains("if (key === \"space\") {"),
        "expected the mixed untagged const branch to reach the OCaml small-case path:\n{rendered}"
    );
    assert!(
        !rendered.contains("key === \"a\" ||")
            && !rendered.contains("key !== \"a\"")
            && !rendered.contains("typeof key === \"string\""),
        "expected the mixed untagged literal-membership residue to disappear:\n{rendered}"
    );
}

#[test]
fn small_untagged_object_value_switches_keep_ocaml_runtime_guards() {
    let mut compiler = LambdaCompiler::new();
    let value = Ident::create_local("value");
    let compiled = compiler.compile_expr(&Lambda::Lswitch(
        Box::new(Lambda::var(value.clone())),
        LambdaSwitch {
            sw_consts_full: false,
            sw_consts: vec![],
            sw_blocks_full: false,
            sw_blocks: vec![(0, Lambda::const_(Constant::int(1)))],
            sw_failaction: Some(Box::new(Lambda::const_(Constant::int(0)))),
            sw_names: Some(SwitchNames {
                consts: vec![crate::lambda::SwitchTag {
                    name: "Null".to_string(),
                    tag_type: Some(crate::lambda::SwitchCaseTag::Null),
                }],
                blocks: vec![
                    crate::lambda::SwitchBlock {
                        tag: crate::lambda::SwitchTag::named("Object"),
                        tag_name: None,
                        block_type: Some(crate::lambda::SwitchBlockType::Object),
                    },
                    crate::lambda::SwitchBlock {
                        tag: crate::lambda::SwitchTag::named("Array"),
                        tag_name: None,
                        block_type: Some(crate::lambda::SwitchBlockType::Instance(
                            "Array".to_string(),
                        )),
                    },
                ],
            }),
        },
    ));

    let rendered = print_block(&compiled.prelude);
    assert!(
        rendered
            .contains("typeof value === \"object\" && value !== null && !Array.isArray(value)"),
        "expected the small object switch to keep OCaml's object/null/array runtime guard:\n{rendered}"
    );
}

#[test]
fn complete_object_then_array_untagged_return_switches_preserve_case_order() {
    let mut compiler = LambdaCompiler::new();
    let value = Ident::create_local("value");
    let block = compiler.compile_untagged_variant_switch_return_statements(
        Expression::var(value.clone()),
        &LambdaSwitch {
            sw_consts_full: true,
            sw_consts: vec![],
            sw_blocks_full: true,
            sw_blocks: vec![
                (0, Lambda::const_(Constant::int(1))),
                (1, Lambda::const_(Constant::int(2))),
            ],
            sw_failaction: None,
            sw_names: Some(SwitchNames {
                consts: vec![],
                blocks: vec![
                    crate::lambda::SwitchBlock {
                        tag: crate::lambda::SwitchTag::named("Object"),
                        tag_name: None,
                        block_type: Some(crate::lambda::SwitchBlockType::Object),
                    },
                    crate::lambda::SwitchBlock {
                        tag: crate::lambda::SwitchTag::named("Array"),
                        tag_name: None,
                        block_type: Some(crate::lambda::SwitchBlockType::Instance(
                            "Array".to_string(),
                        )),
                    },
                ],
            }),
        },
    );

    let rendered = print_block(&block);
    assert!(
        rendered.contains("typeof value === \"object\" && !Array.isArray(value)"),
        "expected the object-first two-case switch to keep the first case test:\n{rendered}"
    );
    assert!(
        !rendered.contains("if (Array.isArray(value))"),
        "expected the object-first two-case switch not to flip to an Array-first split:\n{rendered}"
    );
}

fn single_complete_array_block_switch(
    array_body: Lambda,
    undefined_body: Lambda,
) -> LambdaSwitch {
    LambdaSwitch {
        sw_consts_full: true,
        sw_consts: vec![(0, undefined_body)],
        sw_blocks_full: true,
        sw_blocks: vec![(0, array_body)],
        sw_failaction: None,
        sw_names: Some(SwitchNames {
            consts: vec![crate::lambda::SwitchTag {
                name: "Empty".to_string(),
                tag_type: Some(crate::lambda::SwitchCaseTag::Undefined),
            }],
            blocks: vec![crate::lambda::SwitchBlock {
                tag: crate::lambda::SwitchTag::named("Cons"),
                tag_name: None,
                block_type: Some(crate::lambda::SwitchBlockType::Instance(
                    "Array".to_string(),
                )),
            }],
        }),
    }
}

fn default_only_untagged_boolean_switch(
    boolean_body: Lambda,
    default_body: Lambda,
) -> LambdaSwitch {
    LambdaSwitch {
        sw_consts_full: false,
        sw_consts: vec![],
        sw_blocks_full: false,
        sw_blocks: vec![(0, boolean_body)],
        sw_failaction: Some(Box::new(default_body)),
        sw_names: Some(SwitchNames {
            consts: vec![
                crate::lambda::SwitchTag {
                    name: "Null".to_string(),
                    tag_type: Some(crate::lambda::SwitchCaseTag::Null),
                },
                crate::lambda::SwitchTag {
                    name: "Undefined".to_string(),
                    tag_type: Some(crate::lambda::SwitchCaseTag::Undefined),
                },
            ],
            blocks: vec![
                crate::lambda::SwitchBlock {
                    tag: crate::lambda::SwitchTag::named("B"),
                    tag_name: None,
                    block_type: Some(crate::lambda::SwitchBlockType::Boolean),
                },
                crate::lambda::SwitchBlock {
                    tag: crate::lambda::SwitchTag::named("S"),
                    tag_name: None,
                    block_type: Some(crate::lambda::SwitchBlockType::String),
                },
                crate::lambda::SwitchBlock {
                    tag: crate::lambda::SwitchTag::named("I"),
                    tag_name: None,
                    block_type: Some(crate::lambda::SwitchBlockType::Int),
                },
            ],
        }),
    }
}

#[test]
fn complete_single_untagged_array_value_branch_skips_redundant_instance_guard() {
    let mut compiler = LambdaCompiler::new();
    let value = Ident::create_local("value");
    let result = Ident::create_local("result");
    let block = compiler.compile_untagged_variant_switch_assignment_statements(
        &result,
        Expression::var(value.clone()),
        &single_complete_array_block_switch(
            Lambda::const_(Constant::int(1)),
            Lambda::const_(Constant::int(0)),
        ),
    );

    let [dispatch] = block.as_slice() else {
        panic!("expected a single literal-vs-block dispatch");
    };
    let StatementDesc::Exp(Expression {
        desc: ExpressionDesc::Bin(BinOp::Eq, left, right),
        ..
    }) = &dispatch.desc
    else {
        panic!("expected the direct switch assignment");
    };
    assert!(matches!(
        left.as_ref(),
        Expression {
            desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
            ..
        } if id.same(&result)
    ));
    let ExpressionDesc::Cond(cond, then_expr, else_expr) = &right.as_ref().desc else {
        panic!("expected a conditional expression on the assignment RHS");
    };
    assert_is_undefined_equality_check(cond, &value);
    assert_int_expr(then_expr, 0);
    assert_int_expr(else_expr, 1);
}

#[test]
fn complete_single_untagged_array_return_branch_skips_redundant_instance_guard() {
    let mut compiler = LambdaCompiler::new();
    let value = Ident::create_local("value");
    let block = compiler.compile_untagged_variant_switch_return_statements(
        Expression::var(value.clone()),
        &single_complete_array_block_switch(
            Lambda::const_(Constant::int(1)),
            Lambda::const_(Constant::int(0)),
        ),
    );

    let [dispatch] = block.as_slice() else {
        panic!("expected a single literal dispatch");
    };
    let StatementDesc::Return(Expression {
        desc: ExpressionDesc::Cond(cond, then_expr, else_expr),
        ..
    }) = &dispatch.desc
    else {
        panic!("expected the direct switch return");
    };
    assert_is_undefined_equality_check(cond, &value);
    assert_int_expr(then_expr, 0);
    assert_int_expr(else_expr, 1);
}

#[test]
fn complete_single_untagged_array_effect_branch_skips_redundant_instance_guard() {
    let mut compiler = LambdaCompiler::new();
    let value = Ident::create_local("value");
    let empty_seen = Ident::create_local("empty_seen");
    let cons_seen = Ident::create_local("cons_seen");
    let block = compiler.compile_untagged_variant_switch_effect_statements(
        Expression::var(value.clone()),
        &single_complete_array_block_switch(
            Lambda::Lassign(
                cons_seen.clone(),
                Box::new(Lambda::const_(Constant::int(1))),
            ),
            Lambda::Lassign(
                empty_seen.clone(),
                Box::new(Lambda::const_(Constant::int(0))),
            ),
        ),
    );

    let [dispatch] = block.as_slice() else {
        panic!("expected a single literal dispatch");
    };
    let StatementDesc::Exp(Expression {
        desc: ExpressionDesc::Cond(cond, then_expr, else_expr),
        ..
    }) = &dispatch.desc
    else {
        panic!("expected the direct switch effect expression");
    };
    assert_is_undefined_equality_check(cond, &value);
    assert_assignment_to_int(then_expr, &empty_seen, 0);
    assert_assignment_to_int(else_expr, &cons_seen, 1);
}

#[test]
fn default_only_untagged_boolean_assignment_skips_literal_dispatch_when_defaults_match() {
    let mut compiler = LambdaCompiler::new();
    let value = Ident::create_local("value");
    let result = Ident::create_local("result");
    let block = compiler.compile_untagged_variant_switch_assignment_statements(
        &result,
        Expression::var(value.clone()),
        &default_only_untagged_boolean_switch(
            Lambda::const_(Constant::int(1)),
            Lambda::const_(Constant::int(0)),
        ),
    );

    let [assign] = block.as_slice() else {
        panic!("expected a single direct switch assignment");
    };
    let StatementDesc::Exp(Expression {
        desc: ExpressionDesc::Bin(BinOp::Eq, left, right),
        ..
    }) = &assign.desc
    else {
        panic!("expected the switch assignment");
    };
    assert!(matches!(
        left.as_ref(),
        Expression {
            desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
            ..
        } if id.same(&result)
    ));
    let ExpressionDesc::Cond(cond, then_expr, else_expr) = &right.as_ref().desc else {
        panic!("expected the assignment RHS to be a conditional expression");
    };
    assert_typeof_check(cond, &value, "boolean", BinOp::EqEqEq);
    assert_int_expr(then_expr, 1);
    assert_int_expr(else_expr, 0);
}

#[test]
fn default_only_untagged_boolean_return_skips_literal_dispatch_when_defaults_match() {
    let mut compiler = LambdaCompiler::new();
    let value = Ident::create_local("value");
    let block = compiler.compile_untagged_variant_switch_return_statements(
        Expression::var(value.clone()),
        &default_only_untagged_boolean_switch(
            Lambda::const_(Constant::int(1)),
            Lambda::const_(Constant::int(0)),
        ),
    );

    let [dispatch] = block.as_slice() else {
        panic!("expected a single direct switch return");
    };
    let StatementDesc::Return(Expression {
        desc: ExpressionDesc::Cond(cond, then_expr, else_expr),
        ..
    }) = &dispatch.desc
    else {
        panic!("expected the switch return to be a conditional expression");
    };
    assert_typeof_check(cond, &value, "boolean", BinOp::EqEqEq);
    assert_int_expr(then_expr, 1);
    assert_int_expr(else_expr, 0);
}

#[test]
fn default_only_untagged_object_return_keeps_literal_default_branch_outside_object_chain() {
    let mut compiler = LambdaCompiler::new();
    let value = Ident::create_local("value");
    let body_id = Ident::create_local("body");
    let block = compiler.compile_untagged_variant_switch_return_statements(
        Expression::var(value.clone()),
        &LambdaSwitch {
            sw_consts_full: false,
            sw_consts: vec![],
            sw_blocks_full: false,
            sw_blocks: vec![(
                0,
                Lambda::let_(
                    LetKind::Strict,
                    body_id.clone(),
                    Lambda::const_(Constant::int(1)),
                    Lambda::var(body_id.clone()),
                ),
            )],
            sw_failaction: Some(Box::new(Lambda::const_(Constant::int(0)))),
            sw_names: Some(SwitchNames {
                consts: vec![
                    crate::lambda::SwitchTag {
                        name: "Null".to_string(),
                        tag_type: Some(crate::lambda::SwitchCaseTag::Null),
                    },
                    crate::lambda::SwitchTag {
                        name: "String".to_string(),
                        tag_type: Some(crate::lambda::SwitchCaseTag::String(
                            "string".to_string(),
                        )),
                    },
                ],
                blocks: vec![
                    crate::lambda::SwitchBlock {
                        tag: crate::lambda::SwitchTag::named("Object"),
                        tag_name: None,
                        block_type: Some(crate::lambda::SwitchBlockType::Object),
                    },
                    crate::lambda::SwitchBlock {
                        tag: crate::lambda::SwitchTag::named("Array"),
                        tag_name: None,
                        block_type: Some(crate::lambda::SwitchBlockType::Instance(
                            "Array".to_string(),
                        )),
                    },
                ],
            }),
        },
    );

    let rendered = print_block(&block);
    assert!(
        rendered.contains(
            "if (typeof value !== \"object\" || value === null || Array.isArray(value))"
        ),
        "expected the literal/default side to stay outside the object chain:\n{rendered}"
    );
    assert!(
        rendered.contains("return 0;"),
        "expected the literal/default branch to return the fallback:\n{rendered}"
    );
    assert!(
        rendered.contains("let body = 1;") && rendered.contains("return body;"),
        "expected the object branch to stay inside the guarded path:\n{rendered}"
    );
}

fn assert_switch_case_assigns_int_result(block: &Block, result: &Ident, expected: i32) {
    let [assign, break_stmt] = block.as_slice() else {
        panic!("expected an assignment followed by break");
    };
    match &assign.desc {
        StatementDesc::Exp(Expression {
            desc: ExpressionDesc::Bin(BinOp::Eq, left, right),
            ..
        }) => {
            assert!(matches!(
                left.as_ref(),
                Expression {
                    desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                    ..
                } if id.same(result)
            ));
            assert!(matches!(
                right.as_ref(),
                Expression {
                    desc: ExpressionDesc::Number(Number::Int { i, .. }),
                    ..
                } if *i == expected
            ));
        }
        other => panic!("expected a result assignment, got {other:?}"),
    }
    assert!(matches!(break_stmt.desc, StatementDesc::Break));
}

fn assert_switch_default_assigns_int_result(block: &Block, result: &Ident, expected: i32) {
    let assign = match block.as_slice() {
        [assign] => assign,
        [assign, break_stmt] if matches!(break_stmt.desc, StatementDesc::Break) => assign,
        _ => panic!("expected a default assignment with an optional break"),
    };
    match &assign.desc {
        StatementDesc::Exp(Expression {
            desc: ExpressionDesc::Bin(BinOp::Eq, left, right),
            ..
        }) => {
            assert!(matches!(
                left.as_ref(),
                Expression {
                    desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                    ..
                } if id.same(result)
            ));
            assert!(matches!(
                right.as_ref(),
                Expression {
                    desc: ExpressionDesc::Number(Number::Int { i, .. }),
                    ..
                } if *i == expected
            ));
        }
        other => panic!("expected a default assignment, got {other:?}"),
    }
}

fn assert_is_undefined_equality_check(expr: &Expression, ident: &Ident) {
    match &expr.desc {
        ExpressionDesc::Bin(BinOp::EqEqEq, left, right) => {
            assert!(matches!(
                left.as_ref(),
                Expression {
                    desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                    ..
                } if id.same(ident)
            ));
            assert!(matches!(
                right.as_ref(),
                Expression {
                    desc: ExpressionDesc::Undefined { .. },
                    ..
                }
            ));
        }
        other => panic!("expected an undefined equality dispatch, got {other:?}"),
    }
}

fn assert_int_expr(expr: &Expression, expected: i32) {
    assert!(matches!(
        expr,
        Expression {
            desc: ExpressionDesc::Number(Number::Int { i, .. }),
            ..
        } if *i == expected
    ));
}

fn assert_assignment_to_int(expr: &Expression, ident: &Ident, expected: i32) {
    match &expr.desc {
        ExpressionDesc::Bin(BinOp::Eq, left, right) => {
            assert!(matches!(
                left.as_ref(),
                Expression {
                    desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                    ..
                } if id.same(ident)
            ));
            assert_int_expr(right, expected);
        }
        other => panic!("expected an assignment expression, got {other:?}"),
    }
}

fn assert_effect_assignment_writes_int(block: &Block, ident: &Ident, expected: i32) {
    let [assign] = block.as_slice() else {
        panic!("expected a single effect assignment");
    };
    match &assign.desc {
        StatementDesc::Exp(Expression {
            desc: ExpressionDesc::Bin(BinOp::Eq, left, right),
            ..
        }) => {
            assert!(matches!(
                left.as_ref(),
                Expression {
                    desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                    ..
                } if id.same(ident)
            ));
            assert!(matches!(
                right.as_ref(),
                Expression {
                    desc: ExpressionDesc::Number(Number::Int { i, .. }),
                    ..
                } if *i == expected
            ));
        }
        other => panic!("expected an effect assignment, got {other:?}"),
    }
}

fn assert_switch_case_returns_int_result(block: &Block, expected: i32) {
    let [ret] = block.as_slice() else {
        panic!("expected a single return statement");
    };
    match &ret.desc {
        StatementDesc::Return(Expression {
            desc: ExpressionDesc::Number(Number::Int { i, .. }),
            ..
        }) if *i == expected => {}
        other => panic!("expected a return of {expected}, got {other:?}"),
    }
}

fn assert_switch_default_returns_int_result(block: &Block, expected: i32) {
    assert_switch_case_returns_int_result(block, expected);
}

fn assert_switch_case_returns_bool_result(block: &Block, expected: bool) {
    let [ret] = block.as_slice() else {
        panic!("expected a single return statement");
    };
    match &ret.desc {
        StatementDesc::Return(Expression {
            desc: ExpressionDesc::Bool(value),
            ..
        }) if *value == expected => {}
        other => panic!("expected a return of {expected}, got {other:?}"),
    }
}

fn assert_first_function_body_keeps_fallthrough_return_outside_switch(
    block: &Block,
    stage: &str,
) {
    let [function_decl, ..] = block.as_slice() else {
        panic!("{stage}: expected the compiled program to start with the function binding");
    };
    let StatementDesc::Variable(VariableDeclaration {
        value:
            Some(Expression {
                desc: ExpressionDesc::Fun { body, .. },
                ..
            }),
        ..
    }) = &function_decl.desc
    else {
        panic!("{stage}: expected the first top-level statement to be the function binding");
    };

    let [switch_stmt, handler_return] = body.as_slice() else {
        panic!(
            "{stage}: expected the function body to keep the fallthrough tail after the switch"
        );
    };
    let StatementDesc::IntSwitch(_, _, None) = &switch_stmt.desc else {
        panic!("{stage}: expected the fallthrough default to stay outside the switch");
    };
    assert!(
        matches!(handler_return.desc, StatementDesc::Return(_)),
        "{stage}: expected the fallthrough handler to stay as a trailing return"
    );
}

fn assert_fallthrough_return_outside_switch_body(body: &Block, stage: &str) {
    let [switch_stmt, handler_return] = body.as_slice() else {
        panic!(
            "{stage}: expected the function body to keep the fallthrough tail after the switch"
        );
    };
    let StatementDesc::IntSwitch(_, _, None) = &switch_stmt.desc else {
        panic!("{stage}: expected the fallthrough default to stay outside the switch");
    };
    assert!(
        matches!(handler_return.desc, StatementDesc::Return(_)),
        "{stage}: expected the fallthrough handler to stay as a trailing return"
    );
}

fn extract_first_function_body(lam: &Lambda) -> &Lambda {
    let Lambda::Llet(_, _, value, _) = lam else {
        panic!("expected the top-level lambda to bind the function export");
    };
    match value.as_ref() {
        Lambda::Lfunction(func) => &func.body,
        Lambda::Lprim(crate::lambda::PrimInfo {
            primitive: Primitive::PjsFnMake(_),
            args,
            ..
        }) => {
            let [Lambda::Lfunction(func)] = args.as_slice() else {
                panic!("expected a single lowered function body in the JS function primitive");
            };
            &func.body
        }
        other => {
            panic!("expected the top-level binding to stay function-shaped, got {other:?}")
        }
    }
}

fn assert_typeof_check(
    expr: &Expression,
    ident: &Ident,
    expected_type: &str,
    expected_op: BinOp,
) {
    match &expr.desc {
        ExpressionDesc::Bin(op, left, right) if *op == expected_op => {
            assert!(matches!(
                left.as_ref(),
                Expression {
                    desc: ExpressionDesc::Typeof(inner),
                    ..
                } if matches!(
                    inner.as_ref(),
                    Expression {
                        desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                        ..
                    } if id.same(ident)
                )
            ));
            assert!(matches!(
                right.as_ref(),
                Expression {
                    desc: ExpressionDesc::Str { txt, .. },
                    ..
                } if txt == expected_type
            ));
        }
        other => panic!("expected a typeof check, got {other:?}"),
    }
}

fn assert_typeof_object_check(expr: &Expression, ident: &Ident, expect_object: bool) {
    let expected_op = if expect_object {
        BinOp::EqEqEq
    } else {
        BinOp::NotEqEq
    };
    assert_typeof_check(expr, ident, "object", expected_op);
}

fn assert_array_is_array_call(expr: &Expression, ident: &Ident) {
    match &expr.desc {
        ExpressionDesc::Call(func, args, _) => {
            assert!(matches!(
                func.as_ref(),
                Expression {
                    desc: ExpressionDesc::StaticIndex(target, field, _),
                    ..
                } if field == "isArray"
                    && matches!(
                        target.as_ref(),
                        Expression {
                            desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(array_ident)),
                            ..
                        } if array_ident.name() == "Array"
                    )
            ));
            assert!(matches!(
                args.as_slice(),
                [Expression {
                    desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                    ..
                }] if id.same(ident)
            ));
        }
        other => panic!("expected Array.isArray call, got {other:?}"),
    }
}

fn assert_string_equality_check(
    expr: &Expression,
    ident: Option<&Ident>,
    tag_ident: Option<&Ident>,
    expected_tag: &str,
) {
    match &expr.desc {
        ExpressionDesc::Bin(BinOp::EqEqEq, left, right) => {
            match (ident, tag_ident) {
                (Some(ident), None) => {
                    assert!(matches!(
                        left.as_ref(),
                        Expression {
                            desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                            ..
                        } if id.same(ident)
                    ));
                }
                (None, Some(tag_ident)) => assert_tag_field_access(left, tag_ident),
                _ => panic!("expected exactly one string-equality input shape"),
            }
            assert!(matches!(
                right.as_ref(),
                Expression {
                    desc: ExpressionDesc::Str { txt, .. },
                    ..
                } if txt == expected_tag
            ));
        }
        other => panic!("expected a string equality check, got {other:?}"),
    }
}

fn assert_tag_field_access(expr: &Expression, ident: &Ident) {
    match &expr.desc {
        ExpressionDesc::StaticIndex(target, field, _) if field == "TAG" => {
            assert!(matches!(
                target.as_ref(),
                Expression {
                    desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                    ..
                } if id.same(ident)
            ));
        }
        other => panic!("expected a TAG field access, got {other:?}"),
    }
}

#[test]
fn drops_pure_sequence_prefixes_in_effect_contexts() {
    let mut compiler = LambdaCompiler::new();
    let value = Ident::create_local("value");
    let lam = Lambda::Lsequence(
        Box::new(Lambda::const_(Constant::int(1))),
        Box::new(Lambda::var(value.clone())),
    );
    let program = compiler.compile_program(&lam);

    let [stmt] = program.block.as_slice() else {
        panic!("expected a single expression statement");
    };
    match &stmt.desc {
        StatementDesc::Exp(Expression {
            desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
            ..
        }) => assert!(id.same(&value)),
        other => panic!("expected pure sequence prefix to be removed, got {other:?}"),
    }
}

#[test]
fn flattens_value_sequences_back_to_effect_statements_at_toplevel() {
    let mut compiler = LambdaCompiler::new();
    let callback = Ident::create_local("callback");
    let lam = Lambda::Lsequence(
        Box::new(Lambda::Lapply(Apply {
            ap_func: Box::new(Lambda::var(callback.clone())),
            ap_args: vec![],
            ap_info: ApInfo {
                loc: Location::none(),
                inlined: InlineAttribute::Default,
                status: ApplyStatus::Na,
            },
            ap_transformed_jsx: false,
        })),
        Box::new(Lambda::const_(Constant::none())),
    );
    let program = compiler.compile_program(&lam);

    let [stmt] = program.block.as_slice() else {
        panic!("expected a single expression statement");
    };
    match &stmt.desc {
        StatementDesc::Exp(Expression {
            desc: ExpressionDesc::Call(func, args, _),
            ..
        }) => {
            assert!(args.is_empty());
            assert!(matches!(
                func.as_ref(),
                Expression {
                    desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                    ..
                } if id.same(&callback)
            ));
        }
        other => {
            panic!("expected top-level sequence to flatten to a call statement, got {other:?}")
        }
    }
}

#[test]
fn effect_context_calls_with_arg_preludes_skip_intermediate_call_temps() {
    let mut compiler = LambdaCompiler::new();
    let before = Ident::create_local("before");
    let after = Ident::create_local("after");
    let then_fn = Ident::create_local("thenFn");
    let else_fn = Ident::create_local("elseFn");
    let lam = Lambda::Lapply(Apply {
        ap_func: Box::new(Lambda::LifThenElse(
            Box::new(Lambda::const_(Constant::JsTrue)),
            Box::new(Lambda::Lsequence(
                Box::new(Lambda::Lapply(Apply {
                    ap_func: Box::new(Lambda::var(before.clone())),
                    ap_args: vec![],
                    ap_info: ApInfo {
                        loc: Location::none(),
                        inlined: InlineAttribute::Default,
                        status: ApplyStatus::Na,
                    },
                    ap_transformed_jsx: false,
                })),
                Box::new(Lambda::var(then_fn.clone())),
            )),
            Box::new(Lambda::Lsequence(
                Box::new(Lambda::Lapply(Apply {
                    ap_func: Box::new(Lambda::var(after.clone())),
                    ap_args: vec![],
                    ap_info: ApInfo {
                        loc: Location::none(),
                        inlined: InlineAttribute::Default,
                        status: ApplyStatus::Na,
                    },
                    ap_transformed_jsx: false,
                })),
                Box::new(Lambda::var(else_fn.clone())),
            )),
        )),
        ap_args: vec![Lambda::const_(Constant::int(1))],
        ap_info: ApInfo {
            loc: Location::none(),
            inlined: InlineAttribute::Default,
            status: ApplyStatus::Na,
        },
        ap_transformed_jsx: false,
    });

    let program = compiler.compile_program(&lam);
    let rendered = print_block(&program.block);
    assert!(
        !rendered.contains("let call ="),
        "effect-context apply reintroduced a call temp:\n{rendered}"
    );
    assert!(
        rendered.contains("(1);"),
        "effect-context apply lost the direct call:\n{rendered}"
    );
}

#[test]
fn value_context_direct_calls_stay_as_call_expressions() {
    let mut compiler = LambdaCompiler::new();
    let callback = Ident::create_local("callback");
    let compiled = compiler.compile_expr(&Lambda::Lapply(Apply {
        ap_func: Box::new(Lambda::var(callback.clone())),
        ap_args: vec![Lambda::const_(Constant::int(1))],
        ap_info: ApInfo {
            loc: Location::none(),
            inlined: InlineAttribute::Default,
            status: ApplyStatus::Na,
        },
        ap_transformed_jsx: false,
    }));

    assert!(
        compiled.prelude.is_empty(),
        "value-context call unexpectedly emitted a prelude: {:?}",
        compiled.prelude
    );
    assert!(matches!(
        compiled.expr,
        Expression {
            desc: ExpressionDesc::Call(func, args, _),
            ..
        } if matches!(
            func.as_ref(),
            Expression {
                desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                ..
            } if id.same(&callback)
        ) && matches!(
            args.as_slice(),
            [Expression {
                desc: ExpressionDesc::Number(Number::Int { i: 1, .. }),
                ..
            }]
        )
    ));
}

#[test]
fn nested_app_na_calls_reassociate_through_lam_apply_for_ari_regress_shape() {
    let mut compiler = LambdaCompiler::new();
    let gg = Ident::create_local("gg");
    let x = Ident::create_local("x");
    let y = Ident::create_local("y");
    let u = Ident::create_local("u");
    let z = Ident::create_local("z");
    let result = Ident::create_local("result");
    let loc = Location::none();

    let lam = Lambda::let_(
        LetKind::Alias,
        gg.clone(),
        Lambda::prim(
            Primitive::PjsFnMake(2),
            vec![Lambda::function_(
                2,
                vec![x.clone(), y.clone()],
                Lambda::let_(
                    LetKind::Strict,
                    u.clone(),
                    Lambda::prim(
                        Primitive::Paddint,
                        vec![Lambda::var(x), Lambda::var(y)],
                        loc.clone(),
                    ),
                    Lambda::prim(
                        Primitive::PjsFnMake(1),
                        vec![Lambda::function_(
                            1,
                            vec![z.clone()],
                            Lambda::prim(
                                Primitive::Paddint,
                                vec![Lambda::var(u.clone()), Lambda::var(z)],
                                loc.clone(),
                            ),
                            crate::lambda::FunctionAttribute::default(),
                        )],
                        loc.clone(),
                    ),
                ),
                crate::lambda::FunctionAttribute::default(),
            )],
            loc.clone(),
        ),
        Lambda::let_(
            LetKind::Strict,
            result.clone(),
            Lambda::Lapply(Apply {
                ap_func: Box::new(Lambda::Lapply(Apply {
                    ap_func: Box::new(Lambda::var(gg)),
                    ap_args: vec![
                        Lambda::const_(Constant::int(3)),
                        Lambda::const_(Constant::int(5)),
                    ],
                    ap_info: ApInfo {
                        loc: loc.clone(),
                        inlined: InlineAttribute::Default,
                        status: ApplyStatus::Na,
                    },
                    ap_transformed_jsx: false,
                })),
                ap_args: vec![Lambda::const_(Constant::int(6))],
                ap_info: ApInfo {
                    loc: loc.clone(),
                    inlined: InlineAttribute::Default,
                    status: ApplyStatus::Na,
                },
                ap_transformed_jsx: false,
            }),
            Lambda::var(result.clone()),
        ),
    );

    let simplified = crate::lambda::simplify::simplify_for_js_backend(&lam);
    let compiled = compiler.compile_expr(&simplified);
    let rendered = format!(
        "{}\n{}",
        print_block(&compiled.prelude),
        print_expression(&compiled.expr)
    );
    assert!(
        rendered.contains("u + 6 | 0"),
        "expected Ari_regress-style nested apply to collapse to a direct add, got:\n{rendered}"
    );
    assert!(
        !rendered.contains("(z => u + z | 0)(6)"),
        "expected Ari_regress-style nested apply to avoid an emitted IIFE, got:\n{rendered}"
    );
}

#[test]
fn nested_app_na_calls_reassociate_multi_arg_returned_functions_for_test_demo_shape() {
    let mut compiler = LambdaCompiler::new();
    let g1 = Ident::create_local("g1");
    let x = Ident::create_local("x");
    let y = Ident::create_local("y");
    let u = Ident::create_local("u");
    let xx = Ident::create_local("xx");
    let yy = Ident::create_local("yy");
    let extra = Ident::create_local("extra");
    let result = Ident::create_local("result");
    let loc = Location::none();

    let lam = Lambda::let_(
        LetKind::Alias,
        g1.clone(),
        Lambda::prim(
            Primitive::PjsFnMake(2),
            vec![Lambda::function_(
                2,
                vec![x.clone(), y.clone()],
                Lambda::let_(
                    LetKind::Strict,
                    u.clone(),
                    Lambda::prim(
                        Primitive::Paddint,
                        vec![Lambda::var(x), Lambda::var(y)],
                        loc.clone(),
                    ),
                    Lambda::prim(
                        Primitive::PjsFnMake(2),
                        vec![Lambda::function_(
                            2,
                            vec![xx.clone(), yy.clone()],
                            Lambda::prim(
                                Primitive::Paddint,
                                vec![
                                    Lambda::prim(
                                        Primitive::Paddint,
                                        vec![Lambda::var(xx), Lambda::var(yy)],
                                        loc.clone(),
                                    ),
                                    Lambda::var(u.clone()),
                                ],
                                loc.clone(),
                            ),
                            crate::lambda::FunctionAttribute::default(),
                        )],
                        loc.clone(),
                    ),
                ),
                crate::lambda::FunctionAttribute::default(),
            )],
            loc.clone(),
        ),
        Lambda::let_(
            LetKind::Strict,
            result.clone(),
            Lambda::function_(
                1,
                vec![extra.clone()],
                Lambda::Lapply(Apply {
                    ap_func: Box::new(Lambda::Lapply(Apply {
                        ap_func: Box::new(Lambda::var(g1)),
                        ap_args: vec![
                            Lambda::const_(Constant::int(3)),
                            Lambda::const_(Constant::int(4)),
                        ],
                        ap_info: ApInfo {
                            loc: loc.clone(),
                            inlined: InlineAttribute::Default,
                            status: ApplyStatus::Na,
                        },
                        ap_transformed_jsx: false,
                    })),
                    ap_args: vec![Lambda::const_(Constant::int(6)), Lambda::var(extra.clone())],
                    ap_info: ApInfo {
                        loc: loc.clone(),
                        inlined: InlineAttribute::Default,
                        status: ApplyStatus::Na,
                    },
                    ap_transformed_jsx: false,
                }),
                crate::lambda::FunctionAttribute::default(),
            ),
            Lambda::var(result),
        ),
    );

    let simplified = crate::lambda::simplify::simplify_for_js_backend(&lam);
    let compiled = compiler.compile_expr(&simplified);
    let rendered = print_expression(&compiled.expr);
    assert!(
        rendered.contains("(6 + extra | 0) + u | 0"),
        "expected test_demo-style nested apply to collapse to a direct returned add, got:\n{rendered}"
    );
    assert!(
        !rendered.contains("((xx, yy) => (xx + yy | 0) + u | 0)(6, extra)"),
        "expected test_demo-style nested apply to avoid an emitted multi-arg IIFE, got:\n{rendered}"
    );
}

#[test]
fn let_bound_direct_calls_skip_intermediate_call_aliases() {
    let mut compiler = LambdaCompiler::new();
    let callback = Ident::create_local("callback");
    let x = Ident::create_local("x");
    let compiled = compiler.compile_expr(&Lambda::Llet(
        LetKind::Strict,
        x.clone(),
        Box::new(Lambda::Lapply(Apply {
            ap_func: Box::new(Lambda::var(callback)),
            ap_args: vec![Lambda::const_(Constant::int(1))],
            ap_info: ApInfo {
                loc: Location::none(),
                inlined: InlineAttribute::Default,
                status: ApplyStatus::Na,
            },
            ap_transformed_jsx: false,
        })),
        Box::new(Lambda::var(x.clone())),
    ));

    let [decl] = compiled.prelude.as_slice() else {
        panic!("expected one initialized declaration for the let-bound call");
    };
    assert!(matches!(
        decl,
        Statement {
            desc: StatementDesc::Variable(VariableDeclaration {
                ident,
                value:
                    Some(Expression {
                        desc: ExpressionDesc::Call(func, args, _),
                        ..
                    }),
                ..
            }),
            ..
        } if ident.same(&x)
            && matches!(
                func.as_ref(),
                Expression {
                    desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                    ..
                } if id.name() == "callback"
            )
            && matches!(
                args.as_slice(),
                [Expression {
                    desc: ExpressionDesc::Number(Number::Int { i: 1, .. }),
                    ..
                }]
            )
    ));
    assert!(matches!(
        compiled.expr,
        Expression {
            desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
            ..
        } if id.same(&x)
    ));
}

#[test]
fn return_context_calls_with_arg_preludes_skip_intermediate_call_temps() {
    let mut compiler = LambdaCompiler::new();
    let before = Ident::create_local("before");
    let after = Ident::create_local("after");
    let then_fn = Ident::create_local("thenFn");
    let else_fn = Ident::create_local("elseFn");
    let lam = Lambda::Lapply(Apply {
        ap_func: Box::new(Lambda::LifThenElse(
            Box::new(Lambda::const_(Constant::JsTrue)),
            Box::new(Lambda::Lsequence(
                Box::new(Lambda::Lapply(Apply {
                    ap_func: Box::new(Lambda::var(before.clone())),
                    ap_args: vec![],
                    ap_info: ApInfo {
                        loc: Location::none(),
                        inlined: InlineAttribute::Default,
                        status: ApplyStatus::Na,
                    },
                    ap_transformed_jsx: false,
                })),
                Box::new(Lambda::var(then_fn.clone())),
            )),
            Box::new(Lambda::Lsequence(
                Box::new(Lambda::Lapply(Apply {
                    ap_func: Box::new(Lambda::var(after.clone())),
                    ap_args: vec![],
                    ap_info: ApInfo {
                        loc: Location::none(),
                        inlined: InlineAttribute::Default,
                        status: ApplyStatus::Na,
                    },
                    ap_transformed_jsx: false,
                })),
                Box::new(Lambda::var(else_fn.clone())),
            )),
        )),
        ap_args: vec![Lambda::const_(Constant::int(1))],
        ap_info: ApInfo {
            loc: Location::none(),
            inlined: InlineAttribute::Default,
            status: ApplyStatus::Na,
        },
        ap_transformed_jsx: false,
    });

    let block = compiler.compile_return_block(&lam);
    let rendered = print_block(&block);
    assert!(
        !rendered.contains("let call ="),
        "return-context apply reintroduced a call temp:\n{rendered}"
    );
    assert!(
        !rendered.contains("return call;"),
        "return-context apply still returns the call temp:\n{rendered}"
    );
    assert!(
        rendered.contains("return ") && rendered.contains("(1);"),
        "return-context apply lost the direct return call:\n{rendered}"
    );
}

#[test]
fn assignment_context_calls_with_arg_preludes_skip_intermediate_call_temps() {
    let mut compiler = LambdaCompiler::new();
    let before = Ident::create_local("before");
    let after = Ident::create_local("after");
    let then_fn = Ident::create_local("thenFn");
    let else_fn = Ident::create_local("elseFn");
    let result = Ident::create_local("result");
    let lam = Lambda::Lapply(Apply {
        ap_func: Box::new(Lambda::LifThenElse(
            Box::new(Lambda::const_(Constant::JsTrue)),
            Box::new(Lambda::Lsequence(
                Box::new(Lambda::Lapply(Apply {
                    ap_func: Box::new(Lambda::var(before.clone())),
                    ap_args: vec![],
                    ap_info: ApInfo {
                        loc: Location::none(),
                        inlined: InlineAttribute::Default,
                        status: ApplyStatus::Na,
                    },
                    ap_transformed_jsx: false,
                })),
                Box::new(Lambda::var(then_fn.clone())),
            )),
            Box::new(Lambda::Lsequence(
                Box::new(Lambda::Lapply(Apply {
                    ap_func: Box::new(Lambda::var(after.clone())),
                    ap_args: vec![],
                    ap_info: ApInfo {
                        loc: Location::none(),
                        inlined: InlineAttribute::Default,
                        status: ApplyStatus::Na,
                    },
                    ap_transformed_jsx: false,
                })),
                Box::new(Lambda::var(else_fn.clone())),
            )),
        )),
        ap_args: vec![Lambda::const_(Constant::int(1))],
        ap_info: ApInfo {
            loc: Location::none(),
            inlined: InlineAttribute::Default,
            status: ApplyStatus::Na,
        },
        ap_transformed_jsx: false,
    });

    let block = compiler.compile_assign_to_target_block(&result, &lam);
    let rendered = print_block(&block);
    assert!(
        !rendered.contains("let call ="),
        "assignment-context apply reintroduced a call temp:\n{rendered}"
    );
    assert!(
        !rendered.contains("= call;"),
        "assignment-context apply still assigns from the call temp:\n{rendered}"
    );
    assert!(
        rendered.contains("result = ") && rendered.contains("(1);"),
        "assignment-context apply lost the direct assignment call:\n{rendered}"
    );
}

#[test]
fn function_bodies_drop_pure_undefined_sequence_suffixes() {
    let mut compiler = LambdaCompiler::new();
    let callback = Ident::create_local("callback");
    let value = Ident::create_local("value");
    let call = || {
        Lambda::Lapply(Apply {
            ap_func: Box::new(Lambda::var(callback.clone())),
            ap_args: vec![],
            ap_info: ApInfo {
                loc: Location::none(),
                inlined: InlineAttribute::Default,
                status: ApplyStatus::Na,
            },
            ap_transformed_jsx: false,
        })
    };
    let body = Lambda::Lsequence(
        Box::new(Lambda::Lsequence(
            Box::new(call()),
            Box::new(Lambda::const_(Constant::none())),
        )),
        Box::new(Lambda::Lsequence(
            Box::new(Lambda::Lsequence(
                Box::new(call()),
                Box::new(Lambda::const_(Constant::none())),
            )),
            Box::new(Lambda::var(value.clone())),
        )),
    );
    let compiled = compiler.compile_expr(&Lambda::Lfunction(crate::lambda::LFunction {
        arity: 1,
        params: vec![value.clone()],
        body: Box::new(body),
        attr: crate::lambda::FunctionAttribute::default(),
    }));

    let Expression {
        desc: ExpressionDesc::Fun { body, .. },
        ..
    } = compiled.expr
    else {
        panic!("expected a function expression");
    };

    let [first, second, third] = body.as_slice() else {
        panic!("expected two effect statements followed by a return");
    };

    for stmt in [first, second] {
        match &stmt.desc {
            StatementDesc::Exp(Expression {
                desc: ExpressionDesc::Call(func, args, _),
                ..
            }) => {
                assert!(args.is_empty());
                assert!(matches!(
                    func.as_ref(),
                    Expression {
                        desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                        ..
                    } if id.same(&callback)
                ));
            }
            other => panic!("expected a callback call statement, got {other:?}"),
        }
    }

    match &third.desc {
        StatementDesc::Return(Expression {
            desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
            ..
        }) => assert!(id.same(&value)),
        other => panic!("expected a return of the original value, got {other:?}"),
    }
}

#[test]
fn top_level_if_effects_drop_trailing_pure_undefined_branch_suffixes() {
    let mut compiler = LambdaCompiler::new();
    let cond = Ident::create_local("cond");
    let then_callback = Ident::create_local("thenCallback");
    let else_callback = Ident::create_local("elseCallback");
    let call = |id: &Ident| {
        Lambda::Lapply(Apply {
            ap_func: Box::new(Lambda::var(id.clone())),
            ap_args: vec![],
            ap_info: ApInfo {
                loc: Location::none(),
                inlined: InlineAttribute::Default,
                status: ApplyStatus::Na,
            },
            ap_transformed_jsx: false,
        })
    };
    let lam = Lambda::LifThenElse(
        Box::new(Lambda::var(cond)),
        Box::new(Lambda::Lsequence(
            Box::new(call(&then_callback)),
            Box::new(Lambda::const_(Constant::none())),
        )),
        Box::new(Lambda::Lsequence(
            Box::new(call(&else_callback)),
            Box::new(Lambda::const_(Constant::none())),
        )),
    );

    let program = compiler.compile_program(&lam);
    let rendered = print_block(&program.block);
    assert!(
        !rendered.contains("undefined;"),
        "top-level if effect branch kept a pure undefined suffix:\n{rendered}"
    );
}

#[test]
fn js_flatten_pass_splits_function_return_sequences_into_statements() {
    let function_ident = Ident::create_local("run");
    let callback = Ident::create_local("callback");
    let deps = apply_js_flatten_pass(DepsProgram {
        program: Program::new(
            vec![Statement::variable(VariableDeclaration {
                ident: function_ident,
                value: Some(Expression::new(ExpressionDesc::Fun {
                    is_method: false,
                    params: vec![],
                    body: vec![Statement::return_(Expression::new(ExpressionDesc::Seq(
                        Box::new(Expression::call(
                            Expression::var(callback.clone()),
                            vec![],
                            CallInfo::default(),
                        )),
                        Box::new(Expression::undefined(false)),
                    )))],
                    env: Default::default(),
                    return_unit: false,
                    async_: false,
                    directive: None,
                })),
                property: LetKind::Strict,
                ident_info: IdentInfo::default(),
            })],
            vec![],
        ),
        modules: vec![],
        side_effect: None,
    });

    let [stmt] = deps.program.block.as_slice() else {
        panic!("expected one top-level statement");
    };
    let StatementDesc::Variable(VariableDeclaration {
        value:
            Some(Expression {
                desc: ExpressionDesc::Fun { body, .. },
                ..
            }),
        ..
    }) = &stmt.desc
    else {
        panic!("expected a function-valued variable declaration");
    };

    let [first, second] = body.as_slice() else {
        panic!("expected flattened function body");
    };
    match &first.desc {
        StatementDesc::Exp(Expression {
            desc: ExpressionDesc::Call(func, args, _),
            ..
        }) => {
            assert!(args.is_empty());
            assert!(matches!(
                func.as_ref(),
                Expression {
                    desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                    ..
                } if id.same(&callback)
            ));
        }
        other => panic!("expected callback expression statement, got {other:?}"),
    }
    match &second.desc {
        StatementDesc::Return(Expression {
            desc: ExpressionDesc::Undefined { is_unit: false },
            ..
        }) => {}
        other => panic!("expected return undefined after flattening, got {other:?}"),
    }
}

#[test]
fn js_flatten_pass_turns_conditional_effects_into_if_statements() {
    let then_callback = Ident::create_local("thenCallback");
    let else_callback = Ident::create_local("elseCallback");
    let deps = apply_js_flatten_pass(DepsProgram {
        program: Program::new(
            vec![Statement::exp(Expression::cond(
                Expression::bool(true),
                Expression::call(
                    Expression::var(then_callback.clone()),
                    vec![],
                    CallInfo::default(),
                ),
                Expression::call(
                    Expression::var(else_callback.clone()),
                    vec![],
                    CallInfo::default(),
                ),
            ))],
            vec![],
        ),
        modules: vec![],
        side_effect: None,
    });

    let [stmt] = deps.program.block.as_slice() else {
        panic!("expected one top-level statement");
    };
    let StatementDesc::If(test, then_block, else_block) = &stmt.desc else {
        panic!("expected conditional effect to lower to an if statement");
    };
    assert!(matches!(test.desc, ExpressionDesc::Bool(true)));

    let [then_stmt] = then_block.as_slice() else {
        panic!("expected one statement in then branch");
    };
    let [else_stmt] = else_block.as_slice() else {
        panic!("expected one statement in else branch");
    };

    match &then_stmt.desc {
        StatementDesc::Exp(Expression {
            desc: ExpressionDesc::Call(func, args, _),
            ..
        }) => {
            assert!(args.is_empty());
            assert!(matches!(
                func.as_ref(),
                Expression {
                    desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                    ..
                } if id.same(&then_callback)
            ));
        }
        other => panic!("expected then branch effect call, got {other:?}"),
    }
    match &else_stmt.desc {
        StatementDesc::Exp(Expression {
            desc: ExpressionDesc::Call(func, args, _),
            ..
        }) => {
            assert!(args.is_empty());
            assert!(matches!(
                func.as_ref(),
                Expression {
                    desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                    ..
                } if id.same(&else_callback)
            ));
        }
        other => panic!("expected else branch effect call, got {other:?}"),
    }
}

#[test]
fn js_tailcall_inline_inlines_once_pure_named_calls() {
    let helper = Ident::create_local("helper");
    let arg = Ident::create_local("arg");
    let run = Ident::create_local("run");
    let value = Ident::create_local("value");
    let deps = apply_js_tailcall_inline_pass(DepsProgram {
        program: Program::new(
            vec![
                Statement::variable(VariableDeclaration {
                    ident: helper.clone(),
                    value: Some(Expression::new(ExpressionDesc::Fun {
                        is_method: false,
                        params: vec![arg.clone()],
                        body: vec![Statement::return_(Expression::var(arg.clone()))],
                        env: Default::default(),
                        return_unit: false,
                        async_: false,
                        directive: None,
                    })),
                    property: LetKind::Strict,
                    ident_info: IdentInfo::default(),
                }),
                Statement::variable(VariableDeclaration {
                    ident: run.clone(),
                    value: Some(Expression::new(ExpressionDesc::Fun {
                        is_method: false,
                        params: vec![value.clone()],
                        body: vec![Statement::return_(Expression::call(
                            Expression::var(helper.clone()),
                            vec![Expression::var(value.clone())],
                            CallInfo::default(),
                        ))],
                        env: Default::default(),
                        return_unit: false,
                        async_: false,
                        directive: None,
                    })),
                    property: LetKind::Strict,
                    ident_info: IdentInfo::default(),
                }),
            ],
            vec![run.clone()],
        ),
        modules: vec![],
        side_effect: None,
    });

    let [helper_stmt, run_stmt] = deps.program.block.as_slice() else {
        panic!("expected helper and run bindings");
    };

    match &helper_stmt.desc {
        StatementDesc::Variable(VariableDeclaration { ident_info, .. }) => {
            assert_eq!(ident_info.used_stats, UsedStats::DeadPure);
        }
        other => {
            panic!("expected helper to remain marked dead for the next pass, got {other:?}")
        }
    }

    let StatementDesc::Variable(VariableDeclaration {
        ident,
        ident_info,
        value:
            Some(Expression {
                desc: ExpressionDesc::Fun { body, .. },
                ..
            }),
        ..
    }) = &run_stmt.desc
    else {
        panic!("expected run to remain a function binding");
    };
    assert!(ident.same(&run));
    assert_eq!(ident_info.used_stats, UsedStats::Exported);

    let [stmt] = body.as_slice() else {
        panic!("expected the inlined body to contain a single return");
    };
    match &stmt.desc {
        StatementDesc::Return(Expression {
            desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
            ..
        }) => assert!(id.same(&value)),
        other => panic!("expected the named call to inline to `return value`, got {other:?}"),
    }
}

#[test]
fn js_tailcall_inline_inlines_suffix_named_calls_after_prefix_statements() {
    let helper = Ident::create_local("helper");
    let arg = Ident::create_local("arg");
    let run = Ident::create_local("run");
    let value = Ident::create_local("value");
    let guard = Ident::create_local("guard");
    let deps = apply_js_tailcall_inline_pass(DepsProgram {
        program: Program::new(
            vec![
                Statement::variable(VariableDeclaration {
                    ident: helper.clone(),
                    value: Some(Expression::new(ExpressionDesc::Fun {
                        is_method: false,
                        params: vec![arg.clone()],
                        body: vec![Statement::return_(Expression::var(arg.clone()))],
                        env: Default::default(),
                        return_unit: false,
                        async_: false,
                        directive: None,
                    })),
                    property: LetKind::Strict,
                    ident_info: IdentInfo::default(),
                }),
                Statement::variable(VariableDeclaration {
                    ident: run.clone(),
                    value: Some(Expression::new(ExpressionDesc::Fun {
                        is_method: false,
                        params: vec![guard.clone(), value.clone()],
                        body: vec![
                            Statement::if_(
                                Expression::var(guard.clone()),
                                vec![Statement::return_(Expression::number(Number::int(0)))],
                                vec![],
                            ),
                            Statement::return_(Expression::call(
                                Expression::var(helper.clone()),
                                vec![Expression::var(value.clone())],
                                CallInfo::default(),
                            )),
                        ],
                        env: Default::default(),
                        return_unit: false,
                        async_: false,
                        directive: None,
                    })),
                    property: LetKind::Strict,
                    ident_info: IdentInfo::default(),
                }),
            ],
            vec![run.clone()],
        ),
        modules: vec![],
        side_effect: None,
    });

    let [helper_stmt, run_stmt] = deps.program.block.as_slice() else {
        panic!("expected helper and run bindings");
    };

    match &helper_stmt.desc {
        StatementDesc::Variable(VariableDeclaration { ident_info, .. }) => {
            assert_eq!(ident_info.used_stats, UsedStats::DeadPure);
        }
        other => {
            panic!("expected helper to remain marked dead for the next pass, got {other:?}")
        }
    }

    let StatementDesc::Variable(VariableDeclaration {
        value:
            Some(Expression {
                desc: ExpressionDesc::Fun { body, .. },
                ..
            }),
        ..
    }) = &run_stmt.desc
    else {
        panic!("expected run to remain a function binding");
    };

    let [prefix, suffix] = body.as_slice() else {
        panic!("expected the guard to remain ahead of the inlined suffix call");
    };
    assert!(match &prefix.desc {
        StatementDesc::If(_, _, _) => true,
        StatementDesc::Block(block) => matches!(
            block.as_slice(),
            [Statement {
                desc: StatementDesc::If(_, _, _),
                ..
            }]
        ),
        _ => false,
    });
    match &suffix.desc {
        StatementDesc::Return(Expression {
            desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
            ..
        }) => assert!(id.same(&value)),
        other => {
            panic!("expected the suffix named call to inline to `return value`, got {other:?}")
        }
    }
}

#[test]
fn js_tailcall_inline_inlines_direct_return_iifes() {
    let run = Ident::create_local("run");
    let value = Ident::create_local("value");
    let param = Ident::create_local("param");
    let deps = apply_js_tailcall_inline_pass(DepsProgram {
        program: Program::new(
            vec![Statement::variable(VariableDeclaration {
                ident: run.clone(),
                value: Some(Expression::new(ExpressionDesc::Fun {
                    is_method: false,
                    params: vec![value.clone()],
                    body: vec![Statement::return_(Expression::call(
                        Expression::new(ExpressionDesc::Fun {
                            is_method: false,
                            params: vec![param.clone()],
                            body: vec![Statement::return_(Expression::var(param.clone()))],
                            env: Default::default(),
                            return_unit: false,
                            async_: false,
                            directive: None,
                        }),
                        vec![Expression::var(value.clone())],
                        CallInfo::default(),
                    ))],
                    env: Default::default(),
                    return_unit: false,
                    async_: false,
                    directive: None,
                })),
                property: LetKind::Strict,
                ident_info: IdentInfo::default(),
            })],
            vec![run.clone()],
        ),
        modules: vec![],
        side_effect: None,
    });

    let [stmt] = deps.program.block.as_slice() else {
        panic!("expected one top-level binding");
    };
    let StatementDesc::Variable(VariableDeclaration {
        value:
            Some(Expression {
                desc: ExpressionDesc::Fun { body, .. },
                ..
            }),
        ..
    }) = &stmt.desc
    else {
        panic!("expected run to remain a function binding");
    };

    let [stmt] = body.as_slice() else {
        panic!("expected the direct IIFE to inline to one return statement");
    };
    match &stmt.desc {
        StatementDesc::Return(Expression {
            desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
            ..
        }) => assert!(id.same(&value)),
        other => panic!("expected the direct IIFE to inline to `return value`, got {other:?}"),
    }
}

#[test]
fn js_tailcall_inline_preserves_shadowed_returned_function_params() {
    let run = Ident::create_local("run");
    let outer_param = Ident::create_local("extra");
    let inner_param = Ident::create_local("extra");
    let deps = apply_js_tailcall_inline_pass(DepsProgram {
        program: Program::new(
            vec![Statement::variable(VariableDeclaration {
                ident: run.clone(),
                value: Some(Expression::new(ExpressionDesc::Fun {
                    is_method: false,
                    params: vec![],
                    body: vec![Statement::return_(Expression::call(
                        Expression::new(ExpressionDesc::Fun {
                            is_method: false,
                            params: vec![outer_param.clone()],
                            body: vec![Statement::return_(Expression::new(
                                ExpressionDesc::Fun {
                                    is_method: false,
                                    params: vec![inner_param.clone()],
                                    body: vec![Statement::return_(Expression::var(
                                        inner_param.clone(),
                                    ))],
                                    env: Default::default(),
                                    return_unit: false,
                                    async_: false,
                                    directive: None,
                                },
                            ))],
                            env: Default::default(),
                            return_unit: false,
                            async_: false,
                            directive: None,
                        }),
                        vec![Expression::undefined(false)],
                        CallInfo::default(),
                    ))],
                    env: Default::default(),
                    return_unit: false,
                    async_: false,
                    directive: None,
                })),
                property: LetKind::Strict,
                ident_info: IdentInfo::default(),
            })],
            vec![run.clone()],
        ),
        modules: vec![],
        side_effect: None,
    });
    let rendered = print_block(&deps.program.block);
    assert!(
        rendered.contains("return extra => extra;"),
        "expected the returned function parameter to survive tailcall inlining, got:\n{rendered}"
    );
    assert!(
        !rendered.contains("return extra => undefined;"),
        "unexpected shadowed-parameter rewrite during tailcall inlining:\n{rendered}"
    );
}

#[test]
fn js_tailcall_inline_preserves_shadowed_block_bindings() {
    let run = Ident::create_local("run");
    let outer_param = Ident::create_local("value");
    let inner_binding = Ident::create_local("value");
    let deps = apply_js_tailcall_inline_pass(DepsProgram {
        program: Program::new(
            vec![Statement::variable(VariableDeclaration {
                ident: run.clone(),
                value: Some(Expression::new(ExpressionDesc::Fun {
                    is_method: false,
                    params: vec![],
                    body: vec![Statement::return_(Expression::call(
                        Expression::new(ExpressionDesc::Fun {
                            is_method: false,
                            params: vec![outer_param.clone()],
                            body: vec![
                                Statement::variable(VariableDeclaration {
                                    ident: inner_binding.clone(),
                                    value: Some(Expression::number(Number::int(1))),
                                    property: LetKind::Strict,
                                    ident_info: IdentInfo::default(),
                                }),
                                Statement::return_(Expression::var(inner_binding.clone())),
                            ],
                            env: Default::default(),
                            return_unit: false,
                            async_: false,
                            directive: None,
                        }),
                        vec![Expression::undefined(false)],
                        CallInfo::default(),
                    ))],
                    env: Default::default(),
                    return_unit: false,
                    async_: false,
                    directive: None,
                })),
                property: LetKind::Strict,
                ident_info: IdentInfo::default(),
            })],
            vec![run.clone()],
        ),
        modules: vec![],
        side_effect: None,
    });
    let rendered = print_block(&deps.program.block);
    assert!(
        rendered.contains("let value$1 = 1;"),
        "expected the shadowing binding to stay intact after inlining, got:\n{rendered}"
    );
    assert!(
        rendered.contains("return value$1;"),
        "expected the shadowing binding to stay visible after inlining, got:\n{rendered}"
    );
    assert!(
        !rendered.contains("return undefined;"),
        "unexpected shadowed-block rewrite during tailcall inlining:\n{rendered}"
    );
}

#[test]
fn function_return_blocks_collapse_identity_module_wrapper_to_parameter() {
    let mut compiler = LambdaCompiler::new();
    let module_param = Ident::create_local("U");
    let field_alias = Ident::create_local("x");
    let loc = crate::location::Location::none();

    let compiled = compiler.compile_expr(&Lambda::Lfunction(crate::lambda::LFunction {
        arity: 1,
        params: vec![module_param.clone()],
        body: Box::new(Lambda::let_(
            LetKind::Alias,
            field_alias.clone(),
            Lambda::prim(
                Primitive::Pfield(
                    0,
                    FieldDbgInfo::Module {
                        name: "x".to_string(),
                    },
                ),
                vec![Lambda::var(module_param.clone())],
                loc.clone(),
            ),
            Lambda::prim(
                Primitive::Pmakeblock(
                    0,
                    TagInfo::Module(vec!["x".to_string()]),
                    Mutable::Immutable,
                ),
                vec![Lambda::var(field_alias)],
                loc,
            ),
        )),
        attr: crate::lambda::FunctionAttribute::default(),
    }));

    let Expression {
        desc: ExpressionDesc::Fun { body, .. },
        ..
    } = compiled.expr
    else {
        panic!("expected a function expression");
    };

    let [stmt] = body.as_slice() else {
        panic!("expected the identity module wrapper to collapse to one return statement");
    };
    match &stmt.desc {
        StatementDesc::Return(Expression {
            desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
            ..
        }) if id.same(&module_param) => {}
        other => panic!("expected `return U`, got {other:?}"),
    }
}

#[test]
fn function_return_blocks_collapse_inlined_identity_module_wrapper_to_parameter() {
    let mut compiler = LambdaCompiler::new();
    let module_param = Ident::create_local("U");
    let loc = crate::location::Location::none();

    let compiled = compiler.compile_expr(&Lambda::Lfunction(crate::lambda::LFunction {
        arity: 1,
        params: vec![module_param.clone()],
        body: Box::new(Lambda::prim(
            Primitive::Pmakeblock(
                0,
                TagInfo::Module(vec!["x".to_string()]),
                Mutable::Immutable,
            ),
            vec![Lambda::prim(
                Primitive::Pfield(
                    0,
                    FieldDbgInfo::Module {
                        name: "x".to_string(),
                    },
                ),
                vec![Lambda::var(module_param.clone())],
                loc,
            )],
            crate::location::Location::none(),
        )),
        attr: crate::lambda::FunctionAttribute::default(),
    }));

    let Expression {
        desc: ExpressionDesc::Fun { body, .. },
        ..
    } = compiled.expr
    else {
        panic!("expected a function expression");
    };

    let [stmt] = body.as_slice() else {
        panic!("expected the inlined identity module wrapper to collapse to one return");
    };
    match &stmt.desc {
        StatementDesc::Return(Expression {
            desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
            ..
        }) if id.same(&module_param) => {}
        other => panic!("expected `return U`, got {other:?}"),
    }
}

#[test]
fn function_return_blocks_keep_non_identity_module_wrapper() {
    let mut compiler = LambdaCompiler::new();
    let left = Ident::create_local("Left");
    let right = Ident::create_local("Right");
    let left_alias = Ident::create_local("x");
    let right_alias = Ident::create_local("y");
    let loc = crate::location::Location::none();

    let compiled = compiler.compile_expr(&Lambda::Lfunction(crate::lambda::LFunction {
        arity: 2,
        params: vec![left.clone(), right.clone()],
        body: Box::new(Lambda::let_(
            LetKind::Alias,
            left_alias.clone(),
            Lambda::prim(
                Primitive::Pfield(
                    0,
                    FieldDbgInfo::Module {
                        name: "x".to_string(),
                    },
                ),
                vec![Lambda::var(left.clone())],
                loc.clone(),
            ),
            Lambda::let_(
                LetKind::Alias,
                right_alias.clone(),
                Lambda::prim(
                    Primitive::Pfield(
                        1,
                        FieldDbgInfo::Module {
                            name: "y".to_string(),
                        },
                    ),
                    vec![Lambda::var(right.clone())],
                    loc.clone(),
                ),
                Lambda::prim(
                    Primitive::Pmakeblock(
                        0,
                        TagInfo::Module(vec!["x".to_string(), "y".to_string()]),
                        Mutable::Immutable,
                    ),
                    vec![Lambda::var(left_alias), Lambda::var(right_alias)],
                    loc,
                ),
            ),
        )),
        attr: crate::lambda::FunctionAttribute::default(),
    }));

    let Expression {
        desc: ExpressionDesc::Fun { body, .. },
        ..
    } = compiled.expr
    else {
        panic!("expected a function expression");
    };

    assert_eq!(
        body.len(),
        3,
        "expected the mixed-target module wrapper to keep its alias bindings"
    );
}

#[test]
fn js_flatten_and_mark_dead_rewrites_pre_marked_dead_bindings() {
    let dead_pure = Ident::create_local("deadPure");
    let dead_non_pure = Ident::create_local("deadNonPure");
    let callback = Ident::create_local("callback");
    let deps = apply_js_flatten_and_mark_dead_pass(
        DepsProgram {
            program: Program::new(
                vec![
                    Statement::variable(VariableDeclaration {
                        ident: dead_pure,
                        value: Some(Expression::number(Number::int(1))),
                        property: LetKind::Strict,
                        ident_info: IdentInfo {
                            used_stats: UsedStats::DeadPure,
                        },
                    }),
                    Statement::variable(VariableDeclaration {
                        ident: dead_non_pure,
                        value: Some(Expression::call(
                            Expression::var(callback.clone()),
                            vec![],
                            CallInfo::default(),
                        )),
                        property: LetKind::Strict,
                        ident_info: IdentInfo {
                            used_stats: UsedStats::DeadNonPure,
                        },
                    }),
                ],
                vec![],
            ),
            modules: vec![],
            side_effect: None,
        },
        false,
    );

    let [first, second] = deps.program.block.as_slice() else {
        panic!("expected two rewritten statements");
    };
    match &first.desc {
        StatementDesc::Block(block) => assert!(block.is_empty()),
        other => {
            panic!("expected the dead pure binding to become an empty block, got {other:?}")
        }
    }
    match &second.desc {
        StatementDesc::Exp(Expression {
            desc: ExpressionDesc::Call(func, args, _),
            ..
        }) => {
            assert!(args.is_empty());
            assert!(matches!(
                func.as_ref(),
                Expression {
                    desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                    ..
                } if id.same(&callback)
            ));
        }
        other => panic!(
            "expected the dead impure binding to become an effect statement, got {other:?}"
        ),
    }
}

#[test]
fn js_flatten_and_mark_dead_substitutes_immutable_caml_block_index_reads() {
    let tuple = Ident::create_local("tuple");
    let field = Ident::create_local("field");
    let callback = Ident::create_local("callback");
    let deps = apply_js_flatten_and_mark_dead_pass(
        DepsProgram {
            program: Program::new(
                vec![
                    Statement::variable(VariableDeclaration {
                        ident: tuple.clone(),
                        value: Some(Expression::new(ExpressionDesc::CamlBlock(
                            vec![
                                Expression::call(
                                    Expression::var(callback.clone()),
                                    vec![],
                                    CallInfo::default(),
                                ),
                                Expression::number(Number::int(2)),
                                Expression::number(Number::int(3)),
                            ],
                            MutableFlag::Immutable,
                            Box::new(Expression::number(Number::int(0))),
                            TagInfo::tuple(),
                        ))),
                        property: LetKind::Strict,
                        ident_info: IdentInfo::default(),
                    }),
                    Statement::variable(VariableDeclaration {
                        ident: field,
                        value: Some(Expression::new(ExpressionDesc::ArrayIndex(
                            Box::new(Expression::var(tuple.clone())),
                            Box::new(Expression::number(Number::int(1))),
                        ))),
                        property: LetKind::Strict,
                        ident_info: IdentInfo::default(),
                    }),
                ],
                vec![],
            ),
            modules: vec![],
            side_effect: None,
        },
        false,
    );

    let [tuple_stmt, field_stmt] = deps.program.block.as_slice() else {
        panic!("expected the tuple binding and the rewritten projection");
    };

    let StatementDesc::Block(bindings) = &tuple_stmt.desc else {
        panic!("expected the tuple binding to expand into helper bindings");
    };
    let [helper_stmt, original_stmt] = bindings.as_slice() else {
        panic!("expected one helper binding plus the original tuple binding");
    };

    match &helper_stmt.desc {
        StatementDesc::Variable(VariableDeclaration {
            value:
                Some(Expression {
                    desc: ExpressionDesc::Call(func, args, _),
                    ..
                }),
            ..
        }) => {
            assert!(args.is_empty());
            assert!(matches!(
                func.as_ref(),
                Expression {
                    desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                    ..
                } if id.same(&callback)
            ));
        }
        other => {
            panic!("expected the complex tuple field to become a helper binding, got {other:?}")
        }
    }
    match &original_stmt.desc {
        StatementDesc::Variable(VariableDeclaration {
            ident,
            value:
                Some(Expression {
                    desc: ExpressionDesc::CamlBlock(items, MutableFlag::Immutable, _, _),
                    ..
                }),
            ..
        }) => {
            assert!(ident.same(&tuple));
            assert!(matches!(
                items.as_slice(),
                [
                    Expression {
                        desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(_)),
                        ..
                    },
                    Expression {
                        desc: ExpressionDesc::Number(Number::Int { i: 2, .. }),
                        ..
                    },
                    Expression {
                        desc: ExpressionDesc::Number(Number::Int { i: 3, .. }),
                        ..
                    }
                ]
            ));
        }
        other => panic!(
            "expected the original tuple binding to remain as a rewritten Caml block, got {other:?}"
        ),
    }
    match &field_stmt.desc {
        StatementDesc::Variable(VariableDeclaration {
            value:
                Some(Expression {
                    desc: ExpressionDesc::Number(Number::Int { i: 2, .. }),
                    ..
                }),
            ..
        }) => {}
        other => panic!(
            "expected the tuple projection to inline to the selected field, got {other:?}"
        ),
    }
}

#[test]
fn js_flatten_and_mark_dead_keeps_direct_object_property_reads_materialized_like_ocaml() {
    let value = Ident::create_local("value");
    let deps = apply_js_flatten_and_mark_dead_pass(
        DepsProgram {
            program: Program::new(
                vec![Statement::variable(VariableDeclaration {
                    ident: Ident::create_local("projected"),
                    value: Some(Expression::new(ExpressionDesc::StaticIndex(
                        Box::new(Expression::new(ExpressionDesc::Object(
                            None,
                            vec![(PropertyName::lit("d"), Expression::var(value.clone()))],
                        ))),
                        "d".to_string(),
                        None,
                    ))),
                    property: LetKind::Strict,
                    ident_info: IdentInfo::default(),
                })],
                vec![],
            ),
            modules: vec![],
            side_effect: None,
        },
        false,
    );

    let [stmt] = deps.program.block.as_slice() else {
        panic!("expected one projected binding");
    };
    match &stmt.desc {
        StatementDesc::Variable(VariableDeclaration {
            value:
                Some(Expression {
                    desc: ExpressionDesc::StaticIndex(target, field, None),
                    ..
                }),
            ..
        }) if field == "d"
            && matches!(
                target.as_ref(),
                Expression {
                    desc: ExpressionDesc::Object(
                        None,
                        props
                    ),
                    ..
                } if matches!(
                    props.as_slice(),
                    [(PropertyName::Lit(name), Expression {
                        desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                        ..
                    })] if name == "d" && id.same(&value)
                )
            ) => {}
        other => panic!(
            "expected the direct object property projection to stay materialized, got {other:?}"
        ),
    }
}

#[test]
fn js_flatten_and_mark_dead_keeps_pure_nested_immutable_caml_blocks_inline() {
    let list = Ident::create_local("list");
    let deps = apply_js_flatten_and_mark_dead_pass(
        DepsProgram {
            program: Program::new(
                vec![Statement::variable(VariableDeclaration {
                    ident: list.clone(),
                    value: Some(Expression::new(ExpressionDesc::CamlBlock(
                        vec![
                            Expression::number(Number::int(2)),
                            Expression::new(ExpressionDesc::CamlBlock(
                                vec![
                                    Expression::number(Number::int(3)),
                                    Expression::number(Number::int(0)),
                                ],
                                MutableFlag::Immutable,
                                Box::new(Expression::number(Number::int(0))),
                                TagInfo::Constructor {
                                    name: "::".to_string(),
                                    num_nonconst: 1,
                                    tag: 0,
                                    attrs: vec![],
                                },
                            )),
                        ],
                        MutableFlag::Immutable,
                        Box::new(Expression::number(Number::int(0))),
                        TagInfo::Constructor {
                            name: "::".to_string(),
                            num_nonconst: 1,
                            tag: 0,
                            attrs: vec![],
                        },
                    ))),
                    property: LetKind::Strict,
                    ident_info: IdentInfo::default(),
                })],
                vec![],
            ),
            modules: vec![],
            side_effect: None,
        },
        false,
    );

    let [stmt] = deps.program.block.as_slice() else {
        panic!("expected the list binding to remain");
    };

    let StatementDesc::Variable(VariableDeclaration {
        ident,
        value:
            Some(Expression {
                desc: ExpressionDesc::CamlBlock(items, MutableFlag::Immutable, _, _),
                ..
            }),
        ..
    }) = &stmt.desc
    else {
        panic!("expected the pure nested list binding to stay inline");
    };
    assert!(ident.same(&list));
    assert!(matches!(
        items.as_slice(),
        [
            Expression {
                desc: ExpressionDesc::Number(Number::Int { i: 2, .. }),
                ..
            },
            Expression {
                desc: ExpressionDesc::CamlBlock(inner, MutableFlag::Immutable, _, _),
                ..
            }
        ] if matches!(
            inner.as_slice(),
            [
                Expression {
                    desc: ExpressionDesc::Number(Number::Int { i: 3, .. }),
                    ..
                },
                Expression {
                    desc: ExpressionDesc::Number(Number::Int { i: 0, .. }),
                    ..
                }
            ]
        )
    ));
}

#[test]
fn js_flatten_and_mark_dead_keeps_single_field_module_reads_materialized_like_ocaml() {
    let module = Ident::create_local("M");
    let eq = Ident::create_local("Eq");
    let projected = Ident::create_local("EQ");
    let deps = apply_js_flatten_and_mark_dead_pass(
        DepsProgram {
            program: Program::new(
                vec![
                    Statement::variable(VariableDeclaration {
                        ident: module.clone(),
                        value: Some(Expression::new(ExpressionDesc::CamlBlock(
                            vec![Expression::var(eq.clone())],
                            MutableFlag::Immutable,
                            Box::new(Expression::number(Number::int(0))),
                            TagInfo::Module(vec!["Eq".to_string()]),
                        ))),
                        property: LetKind::Strict,
                        ident_info: IdentInfo::default(),
                    }),
                    Statement::variable(VariableDeclaration {
                        ident: projected,
                        value: Some(Expression::new(ExpressionDesc::StaticIndex(
                            Box::new(Expression::var(module.clone())),
                            "Eq".to_string(),
                            Some(0),
                        ))),
                        property: LetKind::Strict,
                        ident_info: IdentInfo::default(),
                    }),
                ],
                vec![],
            ),
            modules: vec![],
            side_effect: None,
        },
        false,
    );

    let [module_stmt, projected_stmt] = deps.program.block.as_slice() else {
        panic!("expected the module binding and the rewritten projection");
    };
    match &module_stmt.desc {
        StatementDesc::Variable(VariableDeclaration {
            ident,
            value:
                Some(Expression {
                    desc: ExpressionDesc::CamlBlock(items, MutableFlag::Immutable, _, _),
                    ..
                }),
            ..
        }) => {
            assert!(ident.same(&module));
            assert!(matches!(
                items.as_slice(),
                [Expression {
                    desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                    ..
                }] if id.same(&eq)
            ));
        }
        other => {
            panic!("expected the single-field module binding to remain intact, got {other:?}")
        }
    }
    match &projected_stmt.desc {
        StatementDesc::Variable(VariableDeclaration {
            value:
                Some(Expression {
                    desc: ExpressionDesc::StaticIndex(target, field, Some(index)),
                    ..
                }),
            ..
        }) if matches!(
            &target.as_ref().desc,
            ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)) if id.same(&module)
        ) && field == "Eq"
            && *index == 0 => {}
        other => panic!(
            "expected the single-field module projection to stay materialized, got {other:?}"
        ),
    }
}

#[test]
fn js_flatten_and_mark_dead_preserves_transformed_jsx_component_make_reads() {
    let module = Ident::create_local("Foo");
    let component = Ident::create_local("Async_jsx$Foo");
    let rendered = print_deps_program_with_directives(
        &apply_js_flatten_and_mark_dead_pass(
            DepsProgram {
                program: Program::new(
                    vec![
                        Statement::variable(VariableDeclaration {
                            ident: module.clone(),
                            value: Some(Expression::new(ExpressionDesc::CamlBlock(
                                vec![Expression::var(component.clone())],
                                MutableFlag::Immutable,
                                Box::new(Expression::number(Number::int(0))),
                                TagInfo::Module(vec!["make".to_string()]),
                            ))),
                            property: LetKind::Strict,
                            ident_info: IdentInfo::default(),
                        }),
                        Statement::exp(Expression::call(
                            Expression::qualified(
                                ModuleId {
                                    id: Ident::create_persistent("JsxRuntime"),
                                    kind: Kind::External {
                                        name: "react/jsx-runtime".to_string(),
                                        default: false,
                                        import_attributes: None,
                                    },
                                    dynamic_import: false,
                                },
                                Some("jsx".to_string()),
                            ),
                            vec![
                                Expression::new(ExpressionDesc::StaticIndex(
                                    Box::new(Expression::var(module.clone())),
                                    "make".to_string(),
                                    Some(0),
                                )),
                                Expression::new(ExpressionDesc::CamlBlock(
                                    vec![],
                                    MutableFlag::Immutable,
                                    Box::new(Expression::number(Number::int(0))),
                                    TagInfo::record(
                                        vec![],
                                        crate::parser::ast::MutableFlag::Immutable,
                                    ),
                                )),
                            ],
                            CallInfo {
                                call_transformed_jsx: true,
                                ..CallInfo::default()
                            },
                        )),
                    ],
                    vec![],
                ),
                modules: vec![],
                side_effect: None,
            },
            true,
        ),
        None,
        &[],
        false,
        true,
    );

    assert!(
        rendered.contains("<Foo.make />"),
        "expected transformed JSX preserve mode to keep Foo.make visible:\n{rendered}"
    );
    assert!(
        !rendered.contains("<Async_jsx$Foo />"),
        "transformed JSX tag regressed to the component function value:\n{rendered}"
    );
}

#[test]
fn js_flatten_and_mark_dead_keeps_single_field_component_make_reads_without_jsx_preserve_like_ocaml()
 {
    let module = Ident::create_local("Foo");
    let component = Ident::create_local("Async_jsx$Foo");
    let rendered = print_deps_program(
        &apply_js_flatten_and_mark_dead_pass(
            DepsProgram {
                program: Program::new(
                    vec![
                        Statement::variable(VariableDeclaration {
                            ident: module.clone(),
                            value: Some(Expression::new(ExpressionDesc::CamlBlock(
                                vec![Expression::var(component.clone())],
                                MutableFlag::Immutable,
                                Box::new(Expression::number(Number::int(0))),
                                TagInfo::Module(vec!["make".to_string()]),
                            ))),
                            property: LetKind::Strict,
                            ident_info: IdentInfo::default(),
                        }),
                        Statement::exp(Expression::call(
                            Expression::qualified(
                                ModuleId {
                                    id: Ident::create_persistent("JsxRuntime"),
                                    kind: Kind::External {
                                        name: "react/jsx-runtime".to_string(),
                                        default: false,
                                        import_attributes: None,
                                    },
                                    dynamic_import: false,
                                },
                                Some("jsx".to_string()),
                            ),
                            vec![
                                Expression::new(ExpressionDesc::StaticIndex(
                                    Box::new(Expression::var(module.clone())),
                                    "make".to_string(),
                                    Some(0),
                                )),
                                Expression::new(ExpressionDesc::CamlBlock(
                                    vec![],
                                    MutableFlag::Immutable,
                                    Box::new(Expression::number(Number::int(0))),
                                    TagInfo::record(
                                        vec![],
                                        crate::parser::ast::MutableFlag::Immutable,
                                    ),
                                )),
                            ],
                            CallInfo {
                                call_transformed_jsx: true,
                                ..CallInfo::default()
                            },
                        )),
                    ],
                    vec![],
                ),
                modules: vec![],
                side_effect: None,
            },
            false,
        ),
        None,
    );

    assert!(
        rendered.contains("JsxRuntime.jsx(Foo.make, {})"),
        "without jsx preserve the single-field module projection should stay materialized:\n{rendered}"
    );
    assert!(
        !rendered.contains("JsxRuntime.jsx(Async_jsx$Foo, {})"),
        "single-field component .make reads should not inline in this pass:\n{rendered}"
    );
}

#[test]
fn js_flatten_and_mark_dead_rebinds_sync_component_make_aliases_to_descriptive_names() {
    let make = Ident::create_local("make");
    let component = Ident::create_local("Jsx_preserve_test$B");
    let module = Ident::create_local("B");
    let props = Ident::create_local("props");
    let rendered = print_deps_program(
        &apply_js_flatten_and_mark_dead_pass(
            DepsProgram {
                program: Program::new(
                    vec![
                        Statement::variable(VariableDeclaration {
                            ident: make.clone(),
                            value: Some(Expression::new(ExpressionDesc::Fun {
                                is_method: false,
                                params: vec![props],
                                body: vec![Statement::return_(Expression::null())],
                                env: Default::default(),
                                return_unit: false,
                                async_: false,
                                directive: None,
                            })),
                            property: LetKind::Strict,
                            ident_info: IdentInfo::default(),
                        }),
                        Statement::variable(VariableDeclaration {
                            ident: component.clone(),
                            value: Some(Expression::var(make.clone())),
                            property: LetKind::Alias,
                            ident_info: IdentInfo::default(),
                        }),
                        Statement::variable(VariableDeclaration {
                            ident: module.clone(),
                            value: Some(Expression::new(ExpressionDesc::CamlBlock(
                                vec![Expression::var(component.clone())],
                                MutableFlag::Immutable,
                                Box::new(Expression::number(Number::int(0))),
                                TagInfo::Module(vec!["make".to_string()]),
                            ))),
                            property: LetKind::Strict,
                            ident_info: IdentInfo::default(),
                        }),
                    ],
                    vec![],
                ),
                modules: vec![],
                side_effect: None,
            },
            true,
        ),
        None,
    );

    assert!(
        rendered.contains("function Jsx_preserve_test$B(props)"),
        "expected the descriptive component binding to own the function:\n{rendered}"
    );
    assert!(
        !rendered.contains("let Jsx_preserve_test$B = make;"),
        "component alias should collapse into the function declaration:\n{rendered}"
    );
    assert!(
        !rendered.contains("function make(props)"),
        "generic make binding should not survive for sync component aliases:\n{rendered}"
    );
}

#[test]
fn js_flatten_and_mark_dead_rebinds_duplicate_local_module_field_aliases_to_module_names() {
    let imported = Ident::create_local("O");
    let each = Ident::create_local("each");
    let module = Ident::create_local("N1");
    let import_fn = Ident::create_persistent("import");
    let rendered = print_deps_program(
        &DepsProgram {
            program: Program::new(
                rebind_materialized_local_module_field_aliases(vec![
                    Statement::variable(VariableDeclaration {
                        ident: imported.clone(),
                        value: Some(Expression::new(ExpressionDesc::Await(Box::new(
                            Expression::call(
                                Expression::var(import_fn),
                                vec![Expression::string("belt-list")],
                                CallInfo::default(),
                            ),
                        )))),
                        property: LetKind::Strict,
                        ident_info: IdentInfo::default(),
                    }),
                    Statement::variable(VariableDeclaration {
                        ident: each.clone(),
                        value: Some(Expression::new(ExpressionDesc::StaticIndex(
                            Box::new(Expression::var(imported.clone())),
                            "forEach".to_string(),
                            None,
                        ))),
                        property: LetKind::Strict,
                        ident_info: IdentInfo::default(),
                    }),
                    Statement::variable(VariableDeclaration {
                        ident: module.clone(),
                        value: Some(Expression::new(ExpressionDesc::CamlBlock(
                            vec![Expression::var(imported), Expression::var(each.clone())],
                            MutableFlag::Immutable,
                            Box::new(Expression::number(Number::int(0))),
                            TagInfo::Module(vec!["O".to_string(), "each".to_string()]),
                        ))),
                        property: LetKind::Strict,
                        ident_info: IdentInfo::default(),
                    }),
                    Statement::variable(VariableDeclaration {
                        ident: Ident::create_local("each"),
                        value: Some(Expression::number(Number::int(1))),
                        property: LetKind::Strict,
                        ident_info: IdentInfo::default(),
                    }),
                ]),
                vec![],
            ),
            modules: vec![],
            side_effect: None,
        },
        None,
    );

    assert!(
        rendered.contains("let N1_each = O.forEach;"),
        "expected the duplicate module-field alias binding to get the module-prefixed name:\n{rendered}"
    );
    assert!(
        rendered.contains("let N1 = {\n  O: O,\n  each: N1_each\n};"),
        "expected the module block to reference the rebound alias name:\n{rendered}"
    );
}

#[test]
fn js_flatten_and_mark_dead_keeps_async_component_make_aliases_materialized() {
    let make = Ident::create_local("make");
    let component = Ident::create_local("Async_jsx$Foo");
    let module = Ident::create_local("Foo");
    let param = Ident::create_local("param");
    let rendered = print_deps_program(
        &apply_js_flatten_and_mark_dead_pass(
            DepsProgram {
                program: Program::new(
                    vec![
                        Statement::variable(VariableDeclaration {
                            ident: make.clone(),
                            value: Some(Expression::new(ExpressionDesc::Fun {
                                is_method: false,
                                params: vec![param],
                                body: vec![Statement::return_(Expression::null())],
                                env: Default::default(),
                                return_unit: false,
                                async_: true,
                                directive: None,
                            })),
                            property: LetKind::Strict,
                            ident_info: IdentInfo::default(),
                        }),
                        Statement::variable(VariableDeclaration {
                            ident: component.clone(),
                            value: Some(Expression::var(make.clone())),
                            property: LetKind::Alias,
                            ident_info: IdentInfo::default(),
                        }),
                        Statement::variable(VariableDeclaration {
                            ident: module,
                            value: Some(Expression::new(ExpressionDesc::CamlBlock(
                                vec![Expression::var(component.clone())],
                                MutableFlag::Immutable,
                                Box::new(Expression::number(Number::int(0))),
                                TagInfo::Module(vec!["make".to_string()]),
                            ))),
                            property: LetKind::Strict,
                            ident_info: IdentInfo::default(),
                        }),
                    ],
                    vec![],
                ),
                modules: vec![],
                side_effect: None,
            },
            true,
        ),
        None,
    );

    assert!(
        rendered.contains("async function make(param)"),
        "async component binding should keep the original make function:\n{rendered}"
    );
    assert!(
        rendered.contains("let Async_jsx$Foo = make;"),
        "async component alias should remain materialized:\n{rendered}"
    );
    assert!(
        !rendered.contains("async function Async_jsx$Foo(param)"),
        "async component function should not be rebound to the descriptive alias:\n{rendered}"
    );
}

#[test]
fn js_flatten_and_mark_dead_materializes_strictopt_identity_optional_record_fields_like_ocaml()
{
    let record = Ident::create_local("x");
    let deps = apply_js_flatten_and_mark_dead_pass(
        DepsProgram {
            program: Program::new(
                vec![Statement::variable(VariableDeclaration {
                    ident: record.clone(),
                    value: Some(Expression::new(ExpressionDesc::CamlBlock(
                        vec![
                            Expression::undefined(false),
                            Expression::new(ExpressionDesc::OptionalBlock(
                                Box::new(Expression::string("test".to_string())),
                                true,
                            )),
                            Expression::undefined(false),
                            Expression::undefined(false),
                            Expression::new(ExpressionDesc::OptionalBlock(
                                Box::new(Expression::string("test".to_string())),
                                true,
                            )),
                            Expression::undefined(false),
                        ],
                        MutableFlag::Immutable,
                        Box::new(Expression::number(Number::int(0))),
                        TagInfo::Record {
                            fields: vec![
                                ("id".to_string(), true),
                                ("name".to_string(), true),
                                ("title".to_string(), true),
                                ("className".to_string(), true),
                                ("x".to_string(), true),
                                ("y".to_string(), true),
                            ],
                            mutable_flag: crate::parser::ast::MutableFlag::Immutable,
                        },
                    ))),
                    property: LetKind::StrictOpt,
                    ident_info: IdentInfo::default(),
                })],
                vec![],
            ),
            modules: vec![],
            side_effect: None,
        },
        false,
    );

    let [record_stmt] = deps.program.block.as_slice() else {
        panic!("expected the pass to return a single transparent block");
    };
    match &record_stmt.desc {
        StatementDesc::Block(bindings) => {
            let [name_stmt, x_stmt, record_stmt] = bindings.as_slice() else {
                panic!("expected the hoisted optional bindings plus the record binding");
            };
            match &name_stmt.desc {
                StatementDesc::Variable(VariableDeclaration {
                    ident,
                    value:
                        Some(Expression {
                            desc: ExpressionDesc::OptionalBlock(_, true),
                            ..
                        }),
                    ..
                }) => assert_eq!(ident.name(), "x_name"),
                other => panic!(
                    "expected the first hoisted optional binding, got {other:?}"
                ),
            }
            match &x_stmt.desc {
                StatementDesc::Variable(VariableDeclaration {
                    ident,
                    value:
                        Some(Expression {
                            desc: ExpressionDesc::OptionalBlock(_, true),
                            ..
                        }),
                    ..
                }) => assert_eq!(ident.name(), "x_x"),
                other => panic!(
                    "expected the second hoisted optional binding, got {other:?}"
                ),
            }
            match &record_stmt.desc {
                StatementDesc::Variable(VariableDeclaration {
                    ident,
                    value:
                        Some(Expression {
                            desc: ExpressionDesc::CamlBlock(items, MutableFlag::Immutable, _, _),
                            ..
                        }),
                    ..
                }) => {
                    assert!(ident.same(&record));
                    assert!(matches!(
                        items.as_slice(),
                        [
                            Expression {
                                desc: ExpressionDesc::Undefined { .. },
                                ..
                            },
                            Expression {
                                desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(name)),
                                ..
                            },
                            Expression {
                                desc: ExpressionDesc::Undefined { .. },
                                ..
                            },
                            Expression {
                                desc: ExpressionDesc::Undefined { .. },
                                ..
                            },
                            Expression {
                                desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(x_value)),
                                ..
                            },
                            Expression {
                                desc: ExpressionDesc::Undefined { .. },
                                ..
                            }
                        ] if name.name() == "x_name" && x_value.name() == "x_x"
                    ));
                }
                other => panic!(
                    "expected the rewritten record binding to reference the hoisted optionals, got {other:?}"
                ),
            }
        }
        other => panic!("expected the optional record binding block, got {other:?}"),
    }
}

#[test]
fn js_flatten_and_mark_dead_keeps_alias_bound_deep_constant_records_inline_like_ocaml() {
    let record = Ident::create_local("v");
    let deps = apply_js_flatten_and_mark_dead_pass(
        DepsProgram {
            program: Program::new(
                vec![Statement::variable(VariableDeclaration {
                    ident: record.clone(),
                    value: Some(Expression::new(ExpressionDesc::CamlBlock(
                        vec![
                            Expression::new(ExpressionDesc::OptionalBlock(
                                Box::new(Expression::number(Number::int(3))),
                                true,
                            )),
                            Expression::new(ExpressionDesc::CamlBlock(
                                vec![
                                    Expression::number(Number::int(2)),
                                    Expression::number(Number::int(3)),
                                ],
                                MutableFlag::Immutable,
                                Box::new(Expression::number(Number::int(0))),
                                TagInfo::Record {
                                    fields: vec![
                                        ("xx".to_string(), false),
                                        ("yy".to_string(), false),
                                    ],
                                    mutable_flag: crate::parser::ast::MutableFlag::Immutable,
                                },
                            )),
                        ],
                        MutableFlag::Immutable,
                        Box::new(Expression::number(Number::int(0))),
                        TagInfo::Record {
                            fields: vec![
                                ("a".to_string(), false),
                                ("b".to_string(), false),
                            ],
                            mutable_flag: crate::parser::ast::MutableFlag::Immutable,
                        },
                    ))),
                    property: LetKind::Alias,
                    ident_info: IdentInfo::default(),
                })],
                vec![],
            ),
            modules: vec![],
            side_effect: None,
        },
        false,
    );

    let [stmt] = deps.program.block.as_slice() else {
        panic!("expected the alias-bound constant record to stay as one binding");
    };
    match &stmt.desc {
        StatementDesc::Variable(VariableDeclaration {
            ident,
            value:
                Some(Expression {
                    desc: ExpressionDesc::CamlBlock(items, MutableFlag::Immutable, _, _),
                    ..
                }),
            property,
            ..
        }) => {
            assert!(ident.same(&record));
            assert_eq!(*property, LetKind::Alias);
            assert!(matches!(
                items.as_slice(),
                [
                    Expression {
                        desc: ExpressionDesc::OptionalBlock(_, true),
                        ..
                    },
                    Expression {
                        desc: ExpressionDesc::CamlBlock(inner, MutableFlag::Immutable, _, _),
                        ..
                    }
                ] if matches!(
                    inner.as_slice(),
                    [
                        Expression {
                            desc: ExpressionDesc::Number(Number::Int { i: 2, .. }),
                            ..
                        },
                        Expression {
                            desc: ExpressionDesc::Number(Number::Int { i: 3, .. }),
                            ..
                        }
                    ]
                )
            ));
        }
        other => panic!(
            "expected the alias-bound deep-constant record to stay inline, got {other:?}"
        ),
    }
}

#[test]
fn js_flatten_and_mark_dead_marks_unused_nested_pure_bindings() {
    let run = Ident::create_local("run");
    let unused = Ident::create_local("unused");
    let used = Ident::create_local("used");
    let deps = apply_js_flatten_and_mark_dead_pass(
        DepsProgram {
            program: Program::new(
                vec![Statement::variable(VariableDeclaration {
                    ident: run,
                    value: Some(Expression::new(ExpressionDesc::Fun {
                        is_method: false,
                        params: vec![],
                        body: vec![
                            Statement::variable(VariableDeclaration {
                                ident: unused.clone(),
                                value: Some(Expression::number(Number::int(1))),
                                property: LetKind::Strict,
                                ident_info: IdentInfo::default(),
                            }),
                            Statement::variable(VariableDeclaration {
                                ident: used.clone(),
                                value: Some(Expression::number(Number::int(2))),
                                property: LetKind::Strict,
                                ident_info: IdentInfo::default(),
                            }),
                            Statement::return_(Expression::var(used.clone())),
                        ],
                        env: Default::default(),
                        return_unit: false,
                        async_: false,
                        directive: None,
                    })),
                    property: LetKind::Strict,
                    ident_info: IdentInfo::default(),
                })],
                vec![],
            ),
            modules: vec![],
            side_effect: None,
        },
        false,
    );

    let [stmt] = deps.program.block.as_slice() else {
        panic!("expected one top-level function binding");
    };
    let StatementDesc::Variable(VariableDeclaration {
        value:
            Some(Expression {
                desc: ExpressionDesc::Fun { body, .. },
                ..
            }),
        ..
    }) = &stmt.desc
    else {
        panic!("expected a function-valued binding");
    };
    let [unused_stmt, used_stmt, _] = body.as_slice() else {
        panic!("expected two nested bindings followed by a return");
    };
    match &unused_stmt.desc {
        StatementDesc::Variable(VariableDeclaration { ident_info, .. }) => {
            assert_eq!(ident_info.used_stats, UsedStats::DeadPure);
        }
        other => panic!(
            "expected the first nested binding to remain a variable declaration, got {other:?}"
        ),
    }
    match &used_stmt.desc {
        StatementDesc::Variable(VariableDeclaration { ident_info, .. }) => {
            assert_eq!(ident_info.used_stats, UsedStats::Used);
        }
        other => panic!(
            "expected the used nested binding to remain a variable declaration, got {other:?}"
        ),
    }
}

#[test]
fn lowers_js_var_without_args_to_a_value() {
    let mut compiler = LambdaCompiler::new();
    let lam = Lambda::prim(
        Primitive::PjsCall {
            prim_name: "process".to_string(),
            arg_types: vec![],
            ffi: ExternalFfiSpec {
                kind: ExternalFfiKind::Default,
                spec: Some(ExternalSpec::JsVar {
                    name: "process".to_string(),
                    external_module_name: None,
                    scopes: vec![],
                }),
                obj_params: None,
                return_wrapper: ExternalReturnWrapper::Identity,
                inline_constant: None,
            },
            dynamic_import: false,
            transformed_jsx: false,
        },
        vec![],
        Location::none(),
    );

    let compiled = compiler.compile_expr(&lam);
    assert!(compiled.prelude.is_empty());
    assert!(matches!(
        compiled.expr,
        Expression {
            desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(ref id)),
            ..
        } if id.name() == "process"
    ));
}

#[test]
fn lowers_js_var_calls_with_runtime_args_even_without_external_arg_metadata() {
    let mut compiler = LambdaCompiler::new();
    let lam = Lambda::prim(
        Primitive::PjsCall {
            prim_name: "foo1".to_string(),
            arg_types: vec![],
            ffi: ExternalFfiSpec {
                kind: ExternalFfiKind::Default,
                spec: Some(ExternalSpec::JsVar {
                    name: "foo1".to_string(),
                    external_module_name: None,
                    scopes: vec![],
                }),
                obj_params: None,
                return_wrapper: ExternalReturnWrapper::Identity,
                inline_constant: None,
            },
            dynamic_import: false,
            transformed_jsx: false,
        },
        vec![Lambda::Lconst(Constant::Int {
            i: 10,
            comment: None,
        })],
        Location::none(),
    );

    let program = compiler.compile_program(&lam);
    let [stmt] = program.block.as_slice() else {
        panic!("expected a single expression statement");
    };
    match &stmt.desc {
        StatementDesc::Exp(Expression {
            desc: ExpressionDesc::Call(func, args, _),
            ..
        }) => {
            assert_eq!(args.len(), 1);
            assert!(matches!(
                func.as_ref(),
                Expression {
                    desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                    ..
                } if id.name() == "foo1"
            ));
            assert!(matches!(
                args[0],
                Expression {
                    desc: ExpressionDesc::Number(Number::Int { i: 10, .. }),
                    ..
                }
            ));
        }
        other => panic!("expected a direct js-var call, got {other:?}"),
    }
}

#[test]
fn lowers_module_external_calls_to_namespace_imports() {
    let mut compiler = LambdaCompiler::new();
    let lam = Lambda::prim(
        Primitive::PjsCall {
            prim_name: "describe".to_string(),
            arg_types: vec![],
            ffi: ExternalFfiSpec {
                kind: ExternalFfiKind::Default,
                spec: Some(ExternalSpec::JsCall {
                    name: "describe".to_string(),
                    external_module_name: Some(external_module("mocha")),
                    splice: false,
                    scopes: vec![],
                    tagged_template: false,
                }),
                obj_params: None,
                return_wrapper: ExternalReturnWrapper::Identity,
                inline_constant: None,
            },
            dynamic_import: false,
            transformed_jsx: false,
        },
        vec![],
        Location::none(),
    );

    let deps = compiler.compile_deps_program(&lam);
    assert!(matches!(
        deps.modules.as_slice(),
        [ModuleId {
            kind: Kind::External { name, default, .. },
            ..
        }] if name == "mocha" && !default
    ));

    let [stmt] = deps.program.block.as_slice() else {
        panic!("expected a single expression statement");
    };
    match &stmt.desc {
        StatementDesc::Exp(Expression {
            desc: ExpressionDesc::Call(func, args, _),
            ..
        }) => {
            assert!(args.is_empty());
            assert!(matches!(
                func.as_ref(),
                Expression {
                    desc: ExpressionDesc::Var(crate::js_ir::VIdent::Qualified(
                        ModuleId {
                            kind: Kind::External { name, default, .. },
                            ..
                        },
                        Some(field),
                    )),
                    ..
                } if field == "describe" && name == "mocha" && !default
            ));
        }
        other => panic!("expected external module call, got {other:?}"),
    }
}

#[test]
fn translates_external_module_values_to_qualified_members_like_ocaml() {
    let mut compiler = LambdaCompiler::new();
    let expr = compiler.translate_scoped_module_value(
        Some(&external_module("react/jsx-runtime")),
        "jsx",
        &[],
        false,
    );

    assert!(matches!(
        expr,
        Expression {
            desc: ExpressionDesc::Var(crate::js_ir::VIdent::Qualified(
                ModuleId {
                    kind: Kind::External {
                        name: ref name,
                        default,
                        ..
                    },
                    ..
                },
                Some(ref member),
            )),
            ..
        } if name == "react/jsx-runtime" && !default && member == "jsx"
    ));
    assert_eq!(print_expression(&expr), "JsxRuntime.jsx");
}

#[test]
fn lowers_pjs_unsafe_downgrade_getters_to_method_calls() {
    let mut compiler = LambdaCompiler::new();
    let john = Ident::create_persistent("john");
    let lam = Lambda::Lapply(Apply {
        ap_func: Box::new(Lambda::prim(
            Primitive::PjsUnsafeDowngrade {
                name: "say".to_string(),
                setter: false,
            },
            vec![Lambda::var(john.clone())],
            Location::none(),
        )),
        ap_args: vec![
            Lambda::const_(Constant::String {
                s: "hey".to_string(),
                delim: None,
            }),
            Lambda::const_(Constant::String {
                s: "jude".to_string(),
                delim: None,
            }),
        ],
        ap_info: ApInfo {
            loc: Location::none(),
            inlined: InlineAttribute::Default,
            status: ApplyStatus::Uncurry,
        },
        ap_transformed_jsx: false,
    });

    let program = compiler.compile_program(&lam);
    let rendered = print_block(&program.block);
    assert_eq!(rendered, "john.say(\"hey\", \"jude\");");
}

#[test]
fn lowers_pjs_unsafe_downgrade_setters_to_property_assignments() {
    let mut compiler = LambdaCompiler::new();
    let student = Ident::create_persistent("student1");
    let lam = Lambda::prim(
        Primitive::PjsUnsafeDowngrade {
            name: "name".to_string(),
            setter: true,
        },
        vec![
            Lambda::var(student),
            Lambda::const_(Constant::String {
                s: "Mary".to_string(),
                delim: None,
            }),
        ],
        Location::none(),
    );

    let program = compiler.compile_program(&lam);
    let rendered = print_block(&program.block);
    assert_eq!(rendered, "student1.name = \"Mary\";");
}

#[test]
fn top_level_record_field_assignments_on_pure_fresh_literals_collapse_to_rhs_effects() {
    let mut compiler = LambdaCompiler::new();
    let lam = Lambda::seq(
        Lambda::prim(
            Primitive::Psetfield(0, SetFieldDbgInfo::RecordSet("x".to_string())),
            vec![
                Lambda::prim(
                    Primitive::Pmakeblock(
                        0,
                        TagInfo::Record {
                            fields: vec![("x".to_string(), false)],
                            mutable_flag: crate::parser::ast::MutableFlag::Mutable,
                        },
                        Mutable::Immutable,
                    ),
                    vec![Lambda::const_(Constant::int(3))],
                    Location::none(),
                ),
                Lambda::Lsequence(
                    Box::new(Lambda::prim(
                        Primitive::PrawJsCode(crate::lambda::primitive::JsRawInfo {
                            code: "console.log(\"hi\")".to_string(),
                            is_stmt: true,
                        }),
                        vec![],
                        Location::none(),
                    )),
                    Box::new(Lambda::const_(Constant::int(2))),
                ),
            ],
            Location::none(),
        ),
        Lambda::unit(),
    );

    let rendered = print_block(&compiler.compile_program(&lam).block);
    assert!(
        rendered.contains("console.log(\"hi\")"),
        "expected the sequenced logging effect to remain, got:\n{rendered}"
    );
    assert!(
        !rendered.contains(".x = 2;"),
        "did not expect a dead assignment to a pure fresh record literal, got:\n{rendered}"
    );
}

#[test]
fn source_record_field_assignments_on_pure_fresh_literals_collapse_to_rhs_effects() {
    let source = r#"
@val external log: string => unit = "console.log"
type u = {mutable x: int}

{x: 3}.x = {
  log("hi")
  2
}
"#;

    let output = crate::driver::compile_source_to_js(source, "fresh_record_set.res").unwrap();
    assert!(
        output.contains("console.log(\"hi\");"),
        "expected the RHS effect to survive source compilation, got:\n{output}"
    );
    assert!(
        !output.contains("}).x = 2;"),
        "did not expect a dead assignment to a pure fresh record literal, got:\n{output}"
    );
}

#[test]
fn source_record_field_assignments_on_impure_fresh_literals_keep_the_assignment() {
    let source = r#"
@val external log: string => unit = "console.log"
type u = {mutable x: int}

let f = x =>
  {
x: {
  log("hi")
  x
},
  }.x = x + 1
"#;

    let output =
        crate::driver::compile_source_to_js(source, "fresh_record_set_impure.res").unwrap();
    assert!(
        output.contains("console.log(\"hi\")"),
        "expected the impure target initializer to stay visible, got:\n{output}"
    );
    assert!(
        output.contains("}).x = x + 1 | 0;"),
        "expected impure fresh-record assignments to stay materialized, got:\n{output}"
    );
}

#[test]
fn lowers_spliced_js_calls_by_flattening_literal_variadic_arrays() {
    let mut compiler = LambdaCompiler::new();
    let lam = Lambda::prim(
        Primitive::PjsCall {
            prim_name: "join".to_string(),
            arg_types: vec![ExternalArgSpec::dummy()],
            ffi: ExternalFfiSpec {
                kind: ExternalFfiKind::Default,
                spec: Some(ExternalSpec::JsCall {
                    name: "join".to_string(),
                    external_module_name: Some(external_module("path")),
                    splice: true,
                    scopes: vec![],
                    tagged_template: false,
                }),
                obj_params: None,
                return_wrapper: ExternalReturnWrapper::Identity,
                inline_constant: None,
            },
            dynamic_import: false,
            transformed_jsx: false,
        },
        vec![Lambda::prim(
            Primitive::Pmakearray,
            vec![
                Lambda::const_(Constant::String {
                    s: ".".to_string(),
                    delim: None,
                }),
                Lambda::const_(Constant::String {
                    s: "Node_path_test".to_string(),
                    delim: None,
                }),
            ],
            Location::none(),
        )],
        Location::none(),
    );

    let program = compiler.compile_program(&lam);
    let rendered = print_block(&program.block);
    assert_eq!(rendered, "Path.join(\".\", \"Node_path_test\");");
}

#[test]
fn lowers_default_module_values_in_dynamic_imports() {
    let mut compiler = LambdaCompiler::new();
    let external_value = Lambda::prim(
        Primitive::PjsCall {
            prim_name: "default".to_string(),
            arg_types: vec![],
            ffi: ExternalFfiSpec {
                kind: ExternalFfiKind::Default,
                spec: Some(ExternalSpec::JsVar {
                    name: "default".to_string(),
                    external_module_name: Some(external_module("a")),
                    scopes: vec![],
                }),
                obj_params: None,
                return_wrapper: ExternalReturnWrapper::Identity,
                inline_constant: None,
            },
            dynamic_import: false,
            transformed_jsx: false,
        },
        vec![],
        Location::none(),
    );
    let program = compiler.compile_program(&Lambda::prim(
        Primitive::Pimport,
        vec![external_value],
        Location::none(),
    ));
    let rendered = print_block(&program.block);
    assert_eq!(rendered, "import(\"a\").then(m => m.default);");
}

#[test]
fn lowers_unit_returning_default_module_functions_in_dynamic_imports() {
    let mut compiler = LambdaCompiler::new();
    let param = Ident::create_local("prim");
    let eta_expanded_default = Lambda::Lfunction(crate::lambda::LFunction {
        arity: 1,
        params: vec![param.clone()],
        body: Box::new(Lambda::seq(
            Lambda::prim(
                Primitive::PjsCall {
                    prim_name: "default".to_string(),
                    arg_types: vec![ExternalArgSpec::dummy()],
                    ffi: ExternalFfiSpec {
                        kind: ExternalFfiKind::Default,
                        spec: Some(ExternalSpec::JsVar {
                            name: "default".to_string(),
                            external_module_name: Some(external_module("b")),
                            scopes: vec![],
                        }),
                        obj_params: None,
                        return_wrapper: ExternalReturnWrapper::Identity,
                        inline_constant: None,
                    },
                    dynamic_import: false,
                    transformed_jsx: false,
                },
                vec![Lambda::var(param)],
                Location::none(),
            ),
            Lambda::const_(Constant::JsUndefined { is_unit: true }),
        )),
        attr: crate::lambda::FunctionAttribute::default(),
    });
    let program = compiler.compile_program(&Lambda::prim(
        Primitive::Pimport,
        vec![eta_expanded_default],
        Location::none(),
    ));

    let rendered = print_block(&program.block);
    assert_eq!(rendered, "import(\"b\").then(m => m.default);");
}

#[test]
fn lowers_js_new_to_new_expression() {
    let mut compiler = LambdaCompiler::new();
    let arg = Ident::create_local("prim");
    let lam = Lambda::prim(
        Primitive::PjsCall {
            prim_name: "URL".to_string(),
            arg_types: vec![],
            ffi: ExternalFfiSpec {
                kind: ExternalFfiKind::Default,
                spec: Some(ExternalSpec::JsNew {
                    name: "URL".to_string(),
                    external_module_name: None,
                    splice: false,
                    scopes: vec![],
                }),
                obj_params: None,
                return_wrapper: ExternalReturnWrapper::Identity,
                inline_constant: None,
            },
            dynamic_import: false,
            transformed_jsx: false,
        },
        vec![Lambda::var(arg.clone())],
        Location::none(),
    );

    let program = compiler.compile_program(&lam);
    let [stmt] = program.block.as_slice() else {
        panic!("expected a single expression statement");
    };
    match &stmt.desc {
        StatementDesc::Exp(Expression {
            desc: ExpressionDesc::New(ctor, Some(args)),
            ..
        }) => {
            assert!(matches!(
                ctor.desc,
                ExpressionDesc::Var(crate::js_ir::VIdent::Id(ref id)) if id.name() == "URL"
            ));
            assert!(matches!(
                args.as_slice(),
                [Expression {
                    desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                    ..
                }] if id.same(&arg)
            ));
        }
        other => panic!("expected a new expression, got {other:?}"),
    }
}

#[test]
fn lowers_js_call_omits_trailing_optional_undefined_args_like_ocaml() {
    let mut compiler = LambdaCompiler::new();
    let date = Ident::create_local("date");
    let lam = Lambda::prim(
        Primitive::PjsCall {
            prim_name: "formatDate".to_string(),
            arg_types: vec![
                ExternalArgSpec {
                    arg_type: ExternalArgAttr::Nothing,
                    arg_label: ExternalArgLabel::Empty,
                },
                ExternalArgSpec {
                    arg_type: ExternalArgAttr::Nothing,
                    arg_label: ExternalArgLabel::Optional,
                },
                ExternalArgSpec {
                    arg_type: ExternalArgAttr::Nothing,
                    arg_label: ExternalArgLabel::Optional,
                },
            ],
            ffi: ExternalFfiSpec {
                kind: ExternalFfiKind::Default,
                spec: Some(ExternalSpec::JsCall {
                    name: "formatDate".to_string(),
                    external_module_name: Some(external_module("SomeModule")),
                    splice: false,
                    scopes: vec![],
                    tagged_template: false,
                }),
                obj_params: None,
                return_wrapper: ExternalReturnWrapper::Identity,
                inline_constant: None,
            },
            dynamic_import: false,
            transformed_jsx: false,
        },
        vec![
            Lambda::var(date.clone()),
            Lambda::const_(Constant::JsUndefined { is_unit: false }),
            Lambda::const_(Constant::JsUndefined { is_unit: false }),
        ],
        Location::none(),
    );

    let simplified = crate::lambda::simplify::simplify_for_js_backend(&lam);
    let compiled = compiler.compile_expr(&simplified);
    let rendered = if compiled.prelude.is_empty() {
        print_expression(&compiled.expr)
    } else {
        print_block(&compiled.prelude)
    };
    assert_eq!(rendered, "SomeModule.formatDate(date);");
}

#[test]
fn lowers_js_send_omits_trailing_optional_undefined_args_like_ocaml() {
    let mut compiler = LambdaCompiler::new();
    let lam = Lambda::prim(
        Primitive::PjsCall {
            prim_name: "toString".to_string(),
            arg_types: vec![
                ExternalArgSpec {
                    arg_type: ExternalArgAttr::Nothing,
                    arg_label: ExternalArgLabel::Empty,
                },
                ExternalArgSpec {
                    arg_type: ExternalArgAttr::Nothing,
                    arg_label: ExternalArgLabel::Optional,
                },
            ],
            ffi: ExternalFfiSpec {
                kind: ExternalFfiKind::Default,
                spec: Some(ExternalSpec::JsSend {
                    name: "toString".to_string(),
                    splice: false,
                    js_send_scopes: vec![],
                }),
                obj_params: None,
                return_wrapper: ExternalReturnWrapper::Identity,
                inline_constant: None,
            },
            dynamic_import: false,
            transformed_jsx: false,
        },
        vec![
            Lambda::const_(Constant::Float("42.".to_string())),
            Lambda::const_(Constant::JsUndefined { is_unit: false }),
        ],
        Location::none(),
    );

    let rendered = print_block(&compiler.compile_program(&lam).block);
    assert_eq!(rendered, "(42).toString();");
}

#[test]
fn lowers_js_new_omits_trailing_optional_undefined_args_like_ocaml() {
    let mut compiler = LambdaCompiler::new();
    let lam = Lambda::prim(
        Primitive::PjsCall {
            prim_name: "RegExp".to_string(),
            arg_types: vec![
                ExternalArgSpec {
                    arg_type: ExternalArgAttr::Nothing,
                    arg_label: ExternalArgLabel::Empty,
                },
                ExternalArgSpec {
                    arg_type: ExternalArgAttr::Nothing,
                    arg_label: ExternalArgLabel::Optional,
                },
            ],
            ffi: ExternalFfiSpec {
                kind: ExternalFfiKind::Default,
                spec: Some(ExternalSpec::JsNew {
                    name: "RegExp".to_string(),
                    external_module_name: None,
                    splice: false,
                    scopes: vec![],
                }),
                obj_params: None,
                return_wrapper: ExternalReturnWrapper::Identity,
                inline_constant: None,
            },
            dynamic_import: false,
            transformed_jsx: false,
        },
        vec![
            Lambda::const_(Constant::String {
                s: "ab+c".to_string(),
                delim: None,
            }),
            Lambda::const_(Constant::JsUndefined { is_unit: false }),
        ],
        Location::none(),
    );

    let rendered = print_block(&compiler.compile_program(&lam).block);
    assert_eq!(rendered, "new RegExp(\"ab+c\");");
}

#[test]
fn lowers_external_polyvar_string_and_int_args_like_ocaml() {
    let mut compiler = LambdaCompiler::new();
    let lam = Lambda::prim(
        Primitive::PjsCall {
            prim_name: "consume".to_string(),
            arg_types: vec![
                ExternalArgSpec {
                    arg_type: ExternalArgAttr::PolyVarString {
                        descr: vec![
                            ("on_closed".to_string(), "on_closed".to_string()),
                            ("on_open".to_string(), "on_open".to_string()),
                            ("in_".to_string(), "in".to_string()),
                        ],
                    },
                    arg_label: ExternalArgLabel::Empty,
                },
                ExternalArgSpec {
                    arg_type: ExternalArgAttr::Int(vec![
                        ("on_closed".to_string(), 0),
                        ("on_open".to_string(), 3),
                        ("in_".to_string(), 4),
                    ]),
                    arg_label: ExternalArgLabel::Empty,
                },
            ],
            ffi: ExternalFfiSpec {
                kind: ExternalFfiKind::Default,
                spec: Some(ExternalSpec::JsCall {
                    name: "consume".to_string(),
                    external_module_name: None,
                    splice: false,
                    scopes: vec![],
                    tagged_template: false,
                }),
                obj_params: None,
                return_wrapper: ExternalReturnWrapper::Identity,
                inline_constant: None,
            },
            dynamic_import: false,
            transformed_jsx: false,
        },
        vec![
            Lambda::const_(Constant::Pointer("in_".to_string())),
            Lambda::const_(Constant::Pointer("on_open".to_string())),
        ],
        Location::none(),
    );

    let rendered = print_block(&compiler.compile_program(&lam).block);
    assert_eq!(rendered, "consume(\"in\", 3);");
}

#[test]
fn lowers_external_polyvar_payload_args_to_two_js_args_like_ocaml() {
    let mut compiler = LambdaCompiler::new();
    let lam = Lambda::prim(
        Primitive::PjsCall {
            prim_name: "handle".to_string(),
            arg_types: vec![ExternalArgSpec {
                arg_type: ExternalArgAttr::PolyVar {
                    descr: Some(vec![("b".to_string(), "renamed".to_string())]),
                },
                arg_label: ExternalArgLabel::Empty,
            }],
            ffi: ExternalFfiSpec {
                kind: ExternalFfiKind::Default,
                spec: Some(ExternalSpec::JsCall {
                    name: "handle".to_string(),
                    external_module_name: None,
                    splice: false,
                    scopes: vec![],
                    tagged_template: false,
                }),
                obj_params: None,
                return_wrapper: ExternalReturnWrapper::Identity,
                inline_constant: None,
            },
            dynamic_import: false,
            transformed_jsx: false,
        },
        vec![Lambda::const_(Constant::Block {
            tag: 0,
            tag_info: TagInfo::PolyVar("b".to_string()),
            elements: vec![Constant::Pointer("b".to_string()), Constant::int(2)],
        })],
        Location::none(),
    );

    let rendered = print_block(&compiler.compile_program(&lam).block);
    assert_eq!(rendered, "handle(\"renamed\", 2);");
}

#[test]
fn bs_unwrap_keeps_exported_polyvar_wrappers_materialized_like_snapshot() {
    let source = r#"
@val
external log1: @unwrap
[
  | #Pair(string, int)
  | #Int(int)
  | #String(string)
] => unit = "console.log"

let arg_string = #String("hi runtime")
let _ = log1(arg_string)

let arg_pair = #Pair("hi", 1)
let _ = log1(arg_pair)
"#;

    let output =
        crate::driver::compile_source_to_js(source, "bs_unwrap_exported_polyvars.res").unwrap();

    assert!(
        output.contains("console.log(arg_string.VAL);"),
        "expected the exported string polyvar wrapper to stay materialized, got:\n{output}"
    );
    assert!(
        output.contains("console.log(arg_pair.VAL);"),
        "expected the exported pair polyvar wrapper to stay materialized, got:\n{output}"
    );
    assert!(
        !output.contains("console.log(\"hi runtime\");"),
        "did not expect the exported string polyvar wrapper to unwrap to a raw payload:\n{output}"
    );
    assert!(
        !output.contains("let arg_pair_1 = ["),
        "did not expect the exported pair payload to be split into a separate temp:\n{output}"
    );
}

#[test]
fn source_json_template_falls_back_to_regular_string_interpolation_like_ocaml() {
    let source = r#"
let x = json`some random ${"string"}`
"#;

    let output = crate::driver::compile_source_to_js(source, "json_template_test.res").unwrap();

    assert!(
        output.contains("let x = \"some random \" + \"string\";"),
        "expected ordinary string interpolation fallback, got:\n{output}"
    );
}

#[test]
fn source_ref_aliases_survive_later_mutation_like_ocaml() {
    let source = r#"
let fib3 = n => {
  let a = ref(1)
  let b = ref(1)
  for i in 1 to n {
let tmp = a.contents
a := b.contents
b := b.contents + tmp
  }
  a.contents
}
"#;

    let output = crate::driver::compile_source_to_js(source, "fib_ref_alias_test.res").unwrap();

    assert!(
        output.contains("let tmp = a;"),
        "expected the loop alias to remain materialized, got:\n{output}"
    );
    assert!(
        output.contains("b = b + tmp | 0;"),
        "expected the carried temp to feed the second assignment, got:\n{output}"
    );
    assert!(
        !output.contains("b = b + a | 0;"),
        "did not expect the carried temp to collapse to the reassigned binding:\n{output}"
    );
}

#[test]
fn lowers_marshaled_constant_args_in_js_call() {
    let mut compiler = LambdaCompiler::new();
    let lam = Lambda::prim(
        Primitive::PjsCall {
            prim_name: "somefn".to_string(),
            arg_types: vec![ExternalArgSpec {
                arg_type: ExternalArgAttr::ArgCst(ExternalArgConst::StringLit(
                    "{foo:true}".to_string(),
                    ExternalArgDelim::NoQuotes,
                )),
                arg_label: ExternalArgLabel::Empty,
            }],
            ffi: ExternalFfiSpec {
                kind: ExternalFfiKind::Default,
                spec: Some(ExternalSpec::JsCall {
                    name: "somefn".to_string(),
                    external_module_name: None,
                    splice: false,
                    scopes: vec!["somescope".to_string()],
                    tagged_template: false,
                }),
                obj_params: None,
                return_wrapper: ExternalReturnWrapper::Identity,
                inline_constant: None,
            },
            dynamic_import: false,
            transformed_jsx: false,
        },
        vec![],
        Location::none(),
    );

    let program = compiler.compile_program(&lam);
    let [stmt] = program.block.as_slice() else {
        panic!("expected a single expression statement");
    };
    match &stmt.desc {
        StatementDesc::Exp(Expression {
            desc: ExpressionDesc::Call(func, args, _),
            ..
        }) => {
            assert!(matches!(
                func.desc,
                ExpressionDesc::StaticIndex(_, ref field, _)
                if field == "somefn"
            ));
            assert!(matches!(
                args.as_slice(),
                [Expression {
                    desc: ExpressionDesc::Str {
                        delim: Delim::NoQuotes,
                        txt,
                    },
                    ..
                }] if txt == "{foo:true}"
            ));
        }
        other => panic!("expected a JS call, got {other:?}"),
    }
}

#[test]
fn lowers_js_object_create_with_marshaled_fields() {
    let mut compiler = LambdaCompiler::new();
    let name_ident = Ident::create_local("name");
    let compiled = compiler.compile_expr(&Lambda::prim(
        Primitive::PjsObjectCreate(vec![
            ExternalObjSpec {
                obj_arg_type: ExternalArgAttr::ArgCst(ExternalArgConst::StringLit(
                    "false".to_string(),
                    ExternalArgDelim::NoQuotes,
                )),
                obj_arg_label: ExternalObjLabel::Label {
                    name: "objectMode".to_string(),
                },
            },
            ExternalObjSpec {
                obj_arg_type: ExternalArgAttr::Nothing,
                obj_arg_label: ExternalObjLabel::Label {
                    name: "name".to_string(),
                },
            },
            ExternalObjSpec {
                obj_arg_type: ExternalArgAttr::ArgCst(ExternalArgConst::StringLit(
                    "true".to_string(),
                    ExternalArgDelim::NoQuotes,
                )),
                obj_arg_label: ExternalObjLabel::Label {
                    name: "someOther".to_string(),
                },
            },
            ExternalObjSpec {
                obj_arg_type: ExternalArgAttr::ExternUnit,
                obj_arg_label: ExternalObjLabel::Empty,
            },
        ]),
        vec![
            Lambda::var(name_ident.clone()),
            Lambda::const_(Constant::JsUndefined { is_unit: true }),
        ],
        Location::none(),
    ));

    assert!(compiled.prelude.is_empty());
    match &compiled.expr.desc {
        ExpressionDesc::Object(_, props) => {
            assert_eq!(props.len(), 3);
            assert!(matches!(
                &props[0],
                (
                    PropertyName::Lit(name),
                    Expression {
                        desc: ExpressionDesc::Str {
                            delim: Delim::NoQuotes,
                            txt,
                        },
                        ..
                    },
                ) if name == "objectMode" && txt == "false"
            ));
            assert!(matches!(
                &props[1],
                (
                    PropertyName::Lit(name),
                    Expression {
                        desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                        ..
                    },
                ) if name == "name" && id.same(&name_ident)
            ));
            assert!(matches!(
                &props[2],
                (
                    PropertyName::Lit(name),
                    Expression {
                        desc: ExpressionDesc::Str {
                            delim: Delim::NoQuotes,
                            txt,
                        },
                        ..
                    },
                ) if name == "someOther" && txt == "true"
            ));
        }
        other => panic!("expected an object literal expression, got {other:?}"),
    }
}

#[test]
fn lowers_js_object_create_with_polyvar_string_field_like_ocaml() {
    let mut compiler = LambdaCompiler::new();
    let compiled = compiler.compile_expr(&Lambda::prim(
        Primitive::PjsObjectCreate(vec![ExternalObjSpec {
            obj_arg_type: ExternalArgAttr::PolyVarString {
                descr: vec![
                    ("lookup".to_string(), "lookup".to_string()),
                    ("best_fit".to_string(), "best fit".to_string()),
                ],
            },
            obj_arg_label: ExternalObjLabel::Label {
                name: "localeMatcher".to_string(),
            },
        }]),
        vec![Lambda::const_(Constant::Pointer("best_fit".to_string()))],
        Location::none(),
    ));

    assert!(compiled.prelude.is_empty());
    match &compiled.expr.desc {
        ExpressionDesc::Object(_, props) => {
            assert_eq!(props.len(), 1);
            assert!(matches!(
                &props[0],
                (
                    PropertyName::Lit(name),
                    Expression {
                        desc: ExpressionDesc::Str { txt, .. },
                        ..
                    },
                ) if name == "localeMatcher" && txt == "best fit"
            ));
        }
        other => panic!("expected an object literal expression, got {other:?}"),
    }
}

#[test]
fn lowers_js_object_create_with_optional_polyvar_string_field_inline_like_ocaml() {
    let mut compiler = LambdaCompiler::new();
    let compiled = compiler.compile_expr(&Lambda::prim(
        Primitive::PjsObjectCreate(vec![ExternalObjSpec {
            obj_arg_type: ExternalArgAttr::PolyVarString {
                descr: vec![
                    ("numeric".to_string(), "numeric".to_string()),
                    ("two_digit".to_string(), "2-digit".to_string()),
                ],
            },
            obj_arg_label: ExternalObjLabel::Optional {
                name: "day".to_string(),
                for_sure_no_nested_option: false,
            },
        }]),
        vec![Lambda::prim(
            Primitive::Psome,
            vec![Lambda::const_(Constant::Pointer("two_digit".to_string()))],
            Location::none(),
        )],
        Location::none(),
    ));

    assert!(compiled.prelude.is_empty());
    match &compiled.expr.desc {
        ExpressionDesc::Object(_, props) => {
            assert_eq!(props.len(), 1);
            assert!(matches!(
                &props[0],
                (
                    PropertyName::Lit(name),
                    Expression {
                        desc: ExpressionDesc::Str { txt, .. },
                        ..
                    },
                ) if name == "day" && txt == "2-digit"
            ));
        }
        other => panic!("expected an object literal expression, got {other:?}"),
    }
}

#[test]
fn bind_switch_scrutinee_once_uses_tmp_name_like_ocaml() {
    let mut compiler = LambdaCompiler::new();
    let (prelude, expr) = compiler.bind_switch_scrutinee_once(
        vec![],
        Expression::call(
            Expression::var(Ident::create_local("compute")),
            vec![Expression::number(Number::int(1))],
            CallInfo::default(),
        ),
    );

    let ExpressionDesc::Var(crate::js_ir::VIdent::Id(tmp_ident)) = &expr.desc else {
        panic!("expected the bound scrutinee expression to become a temp variable");
    };
    assert_eq!(tmp_ident.name(), "tmp");

    let [stmt] = prelude.as_slice() else {
        panic!("expected a single temp binding statement");
    };
    match &stmt.desc {
        StatementDesc::Variable(VariableDeclaration { ident, value, .. }) => {
            assert!(ident.same(tmp_ident));
            assert!(matches!(
                value,
                Some(Expression {
                    desc: ExpressionDesc::Call(_, _, _),
                    ..
                })
            ));
        }
        other => panic!("expected a temp variable declaration, got {other:?}"),
    }
}

#[test]
fn lowers_js_object_create_with_statically_present_optional_field_inline_like_ocaml() {
    let mut compiler = LambdaCompiler::new();
    let compiled = compiler.compile_expr(&Lambda::prim(
        Primitive::PjsObjectCreate(vec![ExternalObjSpec {
            obj_arg_type: ExternalArgAttr::Nothing,
            obj_arg_label: ExternalObjLabel::Optional {
                name: "alt".to_string(),
                for_sure_no_nested_option: false,
            },
        }]),
        vec![Lambda::prim(
            Primitive::Psome,
            vec![Lambda::const_(Constant::string("pic"))],
            Location::none(),
        )],
        Location::none(),
    ));

    assert!(compiled.prelude.is_empty());
    match &compiled.expr.desc {
        ExpressionDesc::Object(_, props) => {
            assert_eq!(props.len(), 1);
            assert!(matches!(
                &props[0],
                (
                    PropertyName::Lit(name),
                    Expression {
                        desc: ExpressionDesc::Str { txt, .. },
                        ..
                    },
                ) if name == "alt" && txt == "pic"
            ));
        }
        other => panic!("expected an inline object literal expression, got {other:?}"),
    }
}

#[test]
fn lowers_js_object_create_with_unknown_optional_field_to_conditional_assignment_like_ocaml() {
    let mut compiler = LambdaCompiler::new();
    let opt = Ident::create_local("opt");
    let compiled = compiler.compile_expr(&Lambda::prim(
        Primitive::PjsObjectCreate(vec![ExternalObjSpec {
            obj_arg_type: ExternalArgAttr::Nothing,
            obj_arg_label: ExternalObjLabel::Optional {
                name: "alt".to_string(),
                for_sure_no_nested_option: false,
            },
        }]),
        vec![Lambda::var(opt.clone())],
        Location::none(),
    ));

    let ExpressionDesc::Var(crate::js_ir::VIdent::Id(obj)) = &compiled.expr.desc else {
        panic!("expected the conditional path to return the temp object");
    };

    let [init_stmt, if_stmt] = compiled.prelude.as_slice() else {
        panic!("expected object init plus one conditional assignment");
    };

    match &init_stmt.desc {
        StatementDesc::Variable(VariableDeclaration {
            ident,
            value:
                Some(Expression {
                    desc: ExpressionDesc::Object(_, props),
                    ..
                }),
            ..
        }) => {
            assert!(ident.same(obj));
            assert!(props.is_empty());
        }
        other => panic!("expected an empty object temp, got {other:?}"),
    }

    match &if_stmt.desc {
        StatementDesc::If(cond, then_block, else_block) => {
            assert!(else_block.is_empty());
            assert!(matches!(
                &cond.desc,
                ExpressionDesc::Bin(
                    BinOp::NotEqEq,
                    left,
                    right,
                ) if matches!(
                    left.as_ref(),
                    Expression {
                        desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                        ..
                    } if id.same(&opt)
                ) && matches!(
                    right.as_ref(),
                    Expression {
                        desc: ExpressionDesc::Undefined { is_unit: false },
                        ..
                    }
                )
            ));

            let [assign_stmt] = then_block.as_slice() else {
                panic!("expected one conditional assignment");
            };
            match &assign_stmt.desc {
                StatementDesc::Exp(Expression {
                    desc: ExpressionDesc::Bin(BinOp::Eq, target, value),
                    ..
                }) => {
                    assert!(matches!(
                        target.as_ref(),
                        Expression {
                            desc: ExpressionDesc::StaticIndex(target_obj, field, _),
                            ..
                        } if field == "alt"
                            && matches!(
                                target_obj.as_ref(),
                                Expression {
                                    desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                                    ..
                                } if id.same(obj)
                            )
                    ));
                    assert_eq!(
                        print_expression(value),
                        "Primitive_option.valFromOption(opt)"
                    );
                }
                other => panic!("expected an object-field assignment, got {other:?}"),
            }
        }
        other => panic!("expected a conditional optional assignment, got {other:?}"),
    }
}

#[test]
fn lowers_js_object_create_with_nonduplicable_optional_field_after_object_temp_like_ocaml() {
    let mut compiler = LambdaCompiler::new();
    let compiled = compiler.compile_expr(&Lambda::prim(
        Primitive::PjsObjectCreate(vec![ExternalObjSpec {
            obj_arg_type: ExternalArgAttr::Nothing,
            obj_arg_label: ExternalObjLabel::Optional {
                name: "alt".to_string(),
                for_sure_no_nested_option: false,
            },
        }]),
        vec![Lambda::prim(
            Primitive::PrawJsCode(JsRawInfo {
                code: "computeOption()".to_string(),
                is_stmt: false,
            }),
            vec![],
            Location::none(),
        )],
        Location::none(),
    ));

    let ExpressionDesc::Var(crate::js_ir::VIdent::Id(obj)) = &compiled.expr.desc else {
        panic!("expected the conditional path to return the temp object");
    };
    assert_eq!(obj.name(), "tmp");

    let [init_stmt, arg_stmt, if_stmt] = compiled.prelude.as_slice() else {
        panic!("expected object init, prepared arg temp, and one conditional assignment");
    };

    match &init_stmt.desc {
        StatementDesc::Variable(VariableDeclaration {
            ident,
            value:
                Some(Expression {
                    desc: ExpressionDesc::Object(_, props),
                    ..
                }),
            property,
            ..
        }) => {
            assert!(ident.same(obj));
            assert_eq!(*property, LetKind::Variable);
            assert!(props.is_empty());
        }
        other => panic!("expected an empty object temp, got {other:?}"),
    }

    let prepared = match &arg_stmt.desc {
        StatementDesc::Variable(VariableDeclaration {
            ident,
            value:
                Some(Expression {
                    desc:
                        ExpressionDesc::RawJsCode(crate::js_ir::JsRawInfo {
                            code,
                            is_stmt: false,
                        }),
                    ..
                }),
            property,
            ..
        }) => {
            assert_eq!(code, "computeOption()");
            assert_eq!(*property, LetKind::Strict);
            assert!(!ident.same(obj));
            ident.clone()
        }
        other => panic!("expected the prepared optional-value temp, got {other:?}"),
    };

    match &if_stmt.desc {
        StatementDesc::If(cond, then_block, else_block) => {
            assert!(else_block.is_empty());
            assert!(matches!(
                &cond.desc,
                ExpressionDesc::Bin(
                    BinOp::NotEqEq,
                    left,
                    right,
                ) if matches!(
                    left.as_ref(),
                    Expression {
                        desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                        ..
                    } if id.same(&prepared)
                ) && matches!(
                    right.as_ref(),
                    Expression {
                        desc: ExpressionDesc::Undefined { is_unit: false },
                        ..
                    }
                )
            ));

            let [assign_stmt] = then_block.as_slice() else {
                panic!("expected one conditional assignment");
            };
            match &assign_stmt.desc {
                StatementDesc::Exp(Expression {
                    desc: ExpressionDesc::Bin(BinOp::Eq, target, _value),
                    ..
                }) => {
                    assert!(matches!(
                        target.as_ref(),
                        Expression {
                            desc: ExpressionDesc::StaticIndex(target_obj, field, _),
                            ..
                        } if field == "alt"
                            && matches!(
                                target_obj.as_ref(),
                                Expression {
                                    desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                                    ..
                                } if id.same(obj)
                            )
                    ));
                }
                other => panic!("expected an object-field assignment, got {other:?}"),
            }
        }
        other => panic!("expected a conditional optional assignment, got {other:?}"),
    }
}

#[test]
fn lowers_ignored_js_call_args_to_ocaml_sequence_effects() {
    let mut compiler = LambdaCompiler::new();
    let lam = Lambda::prim(
        Primitive::PjsCall {
            prim_name: "somefn".to_string(),
            arg_types: vec![
                ExternalArgSpec {
                    arg_type: ExternalArgAttr::Ignore,
                    arg_label: ExternalArgLabel::Empty,
                },
                ExternalArgSpec {
                    arg_type: ExternalArgAttr::Nothing,
                    arg_label: ExternalArgLabel::Empty,
                },
            ],
            ffi: ExternalFfiSpec {
                kind: ExternalFfiKind::Default,
                spec: Some(ExternalSpec::JsCall {
                    name: "somefn".to_string(),
                    external_module_name: None,
                    splice: false,
                    scopes: vec![],
                    tagged_template: false,
                }),
                obj_params: None,
                return_wrapper: ExternalReturnWrapper::Identity,
                inline_constant: None,
            },
            dynamic_import: false,
            transformed_jsx: false,
        },
        vec![
            Lambda::Lsequence(
                Box::new(Lambda::prim(
                    Primitive::PrawJsCode(JsRawInfo {
                        code: "sideEffect()".to_string(),
                        is_stmt: false,
                    }),
                    vec![],
                    Location::none(),
                )),
                Box::new(Lambda::const_(Constant::string("Float"))),
            ),
            Lambda::const_(Constant::int(3)),
        ],
        Location::none(),
    );

    let compiled = compiler.compile_expr(&lam);
    assert!(
        compiled.prelude.is_empty(),
        "expected ignored-call effects to stay in the expression, got {:?}",
        compiled.prelude
    );
    let ExpressionDesc::Seq(left, call) = &compiled.expr.desc else {
        panic!("expected outer effect sequence, got {:?}", compiled.expr);
    };
    let ExpressionDesc::Seq(effect, kind) = &left.as_ref().desc else {
        panic!("expected nested ignored-arg sequence, got {:?}", left);
    };
    assert!(matches!(
        effect.as_ref(),
        Expression {
            desc: ExpressionDesc::RawJsCode(crate::js_ir::JsRawInfo {
                code,
                is_stmt: false,
            }),
            ..
        } if code == "sideEffect()"
    ));
    assert!(matches!(
        kind.as_ref(),
        Expression {
            desc: ExpressionDesc::Str { txt, .. },
            ..
        } if txt == "Float"
    ));
    match &call.as_ref().desc {
        ExpressionDesc::Call(func, args, _) => {
            assert!(matches!(func.as_ref().desc, ExpressionDesc::Var(_)));
            assert!(matches!(
                args.as_slice(),
                [Expression {
                    desc: ExpressionDesc::Number(Number::Int { i: 3, .. }),
                    ..
                }]
            ));
        }
        other => panic!("expected a call expression, got {other:?}"),
    };
}

#[test]
fn lowers_ignored_js_object_fields_to_ocaml_sequence_effects() {
    let mut compiler = LambdaCompiler::new();
    let lam = Lambda::prim(
        Primitive::PjsObjectCreate(vec![
            ExternalObjSpec {
                obj_arg_type: ExternalArgAttr::Ignore,
                obj_arg_label: ExternalObjLabel::Label {
                    name: "kind".to_string(),
                },
            },
            ExternalObjSpec {
                obj_arg_type: ExternalArgAttr::Nothing,
                obj_arg_label: ExternalObjLabel::Label {
                    name: "hi".to_string(),
                },
            },
        ]),
        vec![
            Lambda::Lsequence(
                Box::new(Lambda::prim(
                    Primitive::PrawJsCode(JsRawInfo {
                        code: "sideEffect()".to_string(),
                        is_stmt: false,
                    }),
                    vec![],
                    Location::none(),
                )),
                Box::new(Lambda::const_(Constant::string("Float"))),
            ),
            Lambda::const_(Constant::int(3)),
        ],
        Location::none(),
    );

    let compiled = compiler.compile_expr(&lam);
    assert!(
        compiled.prelude.is_empty(),
        "expected ignored-object effects to stay in the expression, got {:?}",
        compiled.prelude
    );
    let ExpressionDesc::Seq(left, object) = &compiled.expr.desc else {
        panic!("expected outer effect sequence, got {:?}", compiled.expr);
    };
    assert!(matches!(
        left.as_ref(),
        Expression {
            desc: ExpressionDesc::Seq(effect, kind),
            ..
        } if matches!(
            effect.as_ref(),
            Expression {
                desc: ExpressionDesc::RawJsCode(crate::js_ir::JsRawInfo {
                    code,
                    is_stmt: false,
                }),
                ..
            } if code == "sideEffect()"
        ) && matches!(
            kind.as_ref(),
            Expression {
                desc: ExpressionDesc::Str { txt, .. },
                ..
            } if txt == "Float"
        )
    ));
    match &object.as_ref().desc {
        ExpressionDesc::Object(_, props) => {
            assert_eq!(props.len(), 1);
            assert!(matches!(
                &props[0],
                (
                    PropertyName::Lit(name),
                    Expression {
                        desc: ExpressionDesc::Number(Number::Int { i: 3, .. }),
                        ..
                    },
                ) if name == "hi"
            ));
        }
        other => panic!("expected an object literal expression, got {other:?}"),
    };
}

#[test]
fn compile_deps_program_keeps_exported_dict_initializer_object_literals() {
    let mut compiler = LambdaCompiler::new();
    let dict_ident = Ident::create_local("stringDict");
    let dict_value = Lambda::prim(
        Primitive::Pmakedict,
        vec![Lambda::prim(
            Primitive::Pmakearray,
            vec![Lambda::prim(
                Primitive::Pmakeblock(0, TagInfo::Tuple, Mutable::Immutable),
                vec![
                    Lambda::const_(Constant::string("first")),
                    Lambda::const_(Constant::string("hello")),
                ],
                Location::none(),
            )],
            Location::none(),
        )],
        Location::none(),
    );
    let lam = Lambda::let_(
        LetKind::Strict,
        dict_ident.clone(),
        dict_value,
        Lambda::prim(
            Primitive::Pmakeblock(
                0,
                TagInfo::ModuleExport(vec![dict_ident.clone()]),
                Mutable::Immutable,
            ),
            vec![Lambda::var(dict_ident.clone())],
            Location::none(),
        ),
    );

    let deps = compiler.compile_deps_program(&lam);

    let [stmt] = deps.program.block.as_slice() else {
        panic!("expected one exported dict binding");
    };
    match &stmt.desc {
        StatementDesc::Variable(VariableDeclaration {
            ident,
            value:
                Some(Expression {
                    desc: ExpressionDesc::Object(_, props),
                    ..
                }),
            ..
        }) => {
            assert!(ident.same(&dict_ident));
            assert_eq!(props.len(), 1);
            assert!(matches!(
                &props[0],
                (
                    PropertyName::Lit(name),
                    Expression {
                        desc: ExpressionDesc::Str { txt, .. },
                        ..
                    },
                ) if name == "first" && txt == "hello"
            ));
        }
        other => panic!("expected exported dict object literal, got {other:?}"),
    }
}

#[test]
fn compile_dict_has_primitive_emits_in_operator_like_ocaml() {
    let mut compiler = LambdaCompiler::new();
    let dict = Ident::create_local("dict");
    let compiled = compiler.compile_expr(&Lambda::prim(
        Primitive::PdictHas,
        vec![
            Lambda::var(dict.clone()),
            Lambda::const_(Constant::string("key1")),
        ],
        Location::none(),
    ));

    assert!(compiled.prelude.is_empty());
    assert_eq!(print_expression(&compiled.expr), "\"key1\" in dict");
}

#[test]
fn js_pass_pipeline_preserves_dict_has_in_operator_through_typeof() {
    let dict = Ident::create_local("dict");
    let result = Ident::create_local("result");
    let deps = apply_js_shake_pass(apply_js_flatten_and_mark_dead_pass(
        apply_js_tailcall_inline_pass(apply_external_shadow_pass(apply_js_flatten_pass(
            DepsProgram {
                program: Program::new(
                    vec![
                        Statement::variable(VariableDeclaration {
                            ident: dict.clone(),
                            value: Some(Expression::new(ExpressionDesc::Object(None, vec![]))),
                            property: LetKind::Strict,
                            ident_info: IdentInfo::default(),
                        }),
                        Statement::variable(VariableDeclaration {
                            ident: result.clone(),
                            value: Some(Expression::new(ExpressionDesc::Typeof(Box::new(
                                Expression::new(ExpressionDesc::In(
                                    Box::new(Expression::string("key1")),
                                    Box::new(Expression::var(dict.clone())),
                                )),
                            )))),
                            property: LetKind::Strict,
                            ident_info: IdentInfo::default(),
                        }),
                    ],
                    vec![result.clone()],
                ),
                modules: vec![],
                side_effect: None,
            },
        ))),
        false,
    ));
    let rendered = print_deps_program(&deps, None);
    assert!(
        rendered.contains("typeof (\"key1\" in dict)"),
        "expected the JS pass pipeline to preserve the Dict.has `in` operator, got:\n{rendered}"
    );
    assert!(
        !rendered.contains("typeof undefined"),
        "unexpected dropped Dict.has `in` operator after the JS passes:\n{rendered}"
    );
}

#[test]
fn collects_static_module_dependencies() {
    let mut compiler = LambdaCompiler::new();
    let deps = compiler.compile_deps_program(&Lambda::global_module(
        Ident::create_persistent("Belt_List"),
        false,
    ));

    assert_eq!(deps.modules.len(), 1);
    assert_eq!(deps.modules[0].id.name(), "Belt_List");
    assert!(!deps.modules[0].dynamic_import);
}

#[test]
fn external_module_import_attributes_preserve_all_fields() {
    let module = ExternalModuleName {
        bundle: "./myJson.json".to_string(),
        module_bind_name: ExternalModuleBindName::Nothing,
        import_attributes: Some(vec![
            ("type".to_string(), "json".to_string()),
            ("some-identifier".to_string(), "yep".to_string()),
        ]),
    };

    let attrs = external_module_import_attributes(&module).expect("expected import attributes");

    assert_eq!(
        attrs.entries,
        vec![
            ("type".to_string(), "json".to_string()),
            ("some-identifier".to_string(), "yep".to_string()),
        ]
    );
}

#[test]
fn skips_dynamic_import_only_possible_required_modules() {
    let mut compiler = LambdaCompiler::new();
    let extras = std::collections::HashSet::from([ModuleId {
        id: Ident::create_persistent("Side_effect"),
        kind: Kind::Ml,
        dynamic_import: true,
    }]);
    let deps =
        compiler.compile_deps_program_with_possible_required_modules(&Lambda::unit(), &extras);

    assert!(deps.modules.is_empty());
}

#[test]
fn required_modules_skip_dead_pure_external_bindings_like_printer() {
    let compiler = LambdaCompiler::new();
    let mut dead_info = IdentInfo::default();
    dead_info.used_stats = UsedStats::DeadPure;
    let block = vec![Statement::variable(VariableDeclaration {
        ident: Ident::create_local("dead_external"),
        value: Some(Expression::qualified(
            ModuleId {
                id: Ident::create_local("X"),
                kind: Kind::External {
                    name: "./x".to_string(),
                    default: false,
                    import_attributes: None,
                },
                dynamic_import: false,
            },
            Some("x".to_string()),
        )),
        property: LetKind::StrictOpt,
        ident_info: dead_info,
    })];

    let modules = compiler.collect_required_modules(&block);

    assert!(
        modules.is_empty(),
        "dead pure bindings are omitted by the printer, so they must not keep module deps"
    );
}

#[test]
fn internal_unused_test_omits_dead_private_relative_external_import_like_ocaml() {
    let output = compile_checked_in_test_file_to_js("internal_unused_test");

    assert!(
        !output.contains("import * as X from \"./x\";"),
        "expected dead private relative external import to be omitted, got:\n{output}"
    );
    assert!(
        output.contains(
            "import * as Primitive_exceptions from \"@rescript/runtime/lib/es6/Primitive_exceptions.js\";"
        ),
        "expected checked-in runtime import to remain, got:\n{output}"
    );
}

#[test]
fn sorts_external_module_dependencies_by_module_name() {
    let compiler = LambdaCompiler::new();
    let block = vec![
        Statement::exp(Expression::qualified(
            ModuleId {
                id: Ident::create_persistent("JsxRuntime"),
                kind: Kind::External {
                    name: "react/jsx-runtime".to_string(),
                    default: false,
                    import_attributes: None,
                },
                dynamic_import: false,
            },
            None,
        )),
        Statement::exp(Expression::qualified(
            ModuleId {
                id: Ident::create_persistent("ReactIntl"),
                kind: Kind::External {
                    name: "react-intl".to_string(),
                    default: false,
                    import_attributes: None,
                },
                dynamic_import: false,
            },
            None,
        )),
    ];

    let modules = compiler.collect_required_modules(&block);

    assert_eq!(modules.len(), 2);
    assert_eq!(module_sort_name(&modules[0]), "react-intl");
    assert_eq!(module_sort_name(&modules[1]), "react/jsx-runtime");
}

#[test]
fn sorts_required_modules_by_length_before_bytes() {
    let compiler = LambdaCompiler::new();
    let block = vec![
        Statement::exp(Expression::qualified(
            ModuleId {
                id: Ident::create_persistent("Test_utils"),
                kind: Kind::Ml,
                dynamic_import: false,
            },
            None,
        )),
        Statement::exp(Expression::qualified(
            ModuleId {
                id: Ident::create_persistent("Mocha"),
                kind: Kind::External {
                    name: "mocha".to_string(),
                    default: false,
                    import_attributes: None,
                },
                dynamic_import: false,
            },
            None,
        )),
    ];

    let modules = compiler.collect_required_modules(&block);

    assert_eq!(modules.len(), 2);
    assert_eq!(module_sort_name(&modules[0]), "mocha");
    assert_eq!(module_sort_name(&modules[1]), "Test_utils");
}

#[test]
fn required_modules_match_ocaml_sort_across_same_name_import_pairs() {
    let compiler = LambdaCompiler::new();
    let some_default = ModuleId {
        id: Ident::create_local("SomeEs6Module"),
        kind: Kind::External {
            name: "some-es6-module".to_string(),
            default: true,
            import_attributes: None,
        },
        dynamic_import: false,
    };
    let some_namespace = ModuleId {
        id: Ident::create_local("SomeEs6Module"),
        kind: Kind::External {
            name: "some-es6-module".to_string(),
            default: false,
            import_attributes: None,
        },
        dynamic_import: false,
    };
    let ome_default = ModuleId {
        id: Ident::create_local("OmeEs6Module"),
        kind: Kind::External {
            name: "./ome-es6-module".to_string(),
            default: true,
            import_attributes: None,
        },
        dynamic_import: false,
    };
    let ome_namespace = ModuleId {
        id: Ident::create_local("OmeEs6Module"),
        kind: Kind::External {
            name: "./ome-es6-module".to_string(),
            default: false,
            import_attributes: None,
        },
        dynamic_import: false,
    };
    let vscode = ModuleId {
        id: Ident::create_local("Vscode"),
        kind: Kind::External {
            name: "vscode".to_string(),
            default: false,
            import_attributes: None,
        },
        dynamic_import: false,
    };
    let block = vec![
        Statement::exp(Expression::qualified(some_default.clone(), None)),
        Statement::exp(Expression::qualified(
            some_namespace.clone(),
            Some("default2".to_string()),
        )),
        Statement::exp(Expression::qualified(ome_default.clone(), None)),
        Statement::exp(Expression::qualified(
            ome_namespace.clone(),
            Some("default2".to_string()),
        )),
        Statement::exp(Expression::qualified(
            vscode.clone(),
            Some("window".to_string()),
        )),
    ];

    let modules = compiler.collect_required_modules(&block);

    assert_eq!(
        modules,
        vec![
            vscode,
            some_namespace,
            some_default,
            ome_default,
            ome_namespace,
        ]
    );
}

#[test]
fn required_module_effect_reason_uses_external_module_name() {
    let reason = required_module_side_effect_reason(
        None,
        &[ModuleId {
            id: Ident::create_persistent("GentTypeReTestGen"),
            kind: Kind::External {
                name: "./gentTypeReTest.gen".to_string(),
                default: false,
                import_attributes: None,
            },
            dynamic_import: false,
        }],
    );

    assert_eq!(reason.as_deref(), Some("./gentTypeReTest.gen"));
}

#[test]
fn pure_ml_dependencies_do_not_mark_module_impure() {
    let resolver = resolver_with_checked_in_cmj();
    let reason = required_module_side_effect_reason(
        Some(&resolver),
        &[ModuleId {
            id: Ident::create_persistent("Side_effect_free"),
            kind: Kind::Ml,
            dynamic_import: false,
        }],
    );

    assert_eq!(reason, None);
}

#[test]
fn preserves_impure_side_effect_only_ml_dependencies_from_lambda() {
    let resolver = resolver_with_checked_in_cmj();
    let side_effect = Ident::create_persistent("Side_effect");
    let include_binding = Ident::create_local("include");
    let mut compiler = LambdaCompiler::with_module_path_resolver(Some(resolver));
    let deps = compiler.compile_deps_program(&Lambda::let_(
        LetKind::Alias,
        include_binding,
        Lambda::global_module(side_effect.clone(), false),
        Lambda::unit(),
    ));

    assert!(deps.program.block.is_empty());
    assert!(deps.program.exports.is_empty());
    assert_eq!(deps.modules.len(), 1);
    assert_eq!(deps.modules[0].id.name(), side_effect.name());
    assert_eq!(deps.modules[0].kind, Kind::Ml);
    assert_eq!(deps.side_effect.as_deref(), Some("Side_effect"));
}

#[test]
fn impure_ml_dependencies_use_module_name_as_effect_reason() {
    let resolver = resolver_with_checked_in_cmj();
    let reason = required_module_side_effect_reason(
        Some(&resolver),
        &[ModuleId {
            id: Ident::create_persistent("Test_utils"),
            kind: Kind::Ml,
            dynamic_import: false,
        }],
    );

    assert_eq!(reason.as_deref(), Some("Test_utils"));
}

#[test]
fn module_side_effect_reason_uses_first_impure_group_in_final_order_like_ocaml() {
    let first = Ident::create_local("first");
    let second = Ident::create_local("second");
    let lam = Lambda::let_(
        LetKind::Strict,
        first,
        Lambda::prim(Primitive::Pdebugger, vec![], Location::none()),
        Lambda::let_(
            LetKind::Strict,
            second.clone(),
            Lambda::prim(Primitive::Pdebugger, vec![], Location::none()),
            Lambda::unit(),
        ),
    );

    assert_eq!(module_side_effect_reason(&lam).as_deref(), Some("first"));
}

#[test]
fn module_side_effect_reason_uses_binding_name_for_impure_group_bodies() {
    let match_id = Ident::create_local("match");
    let lam = Lambda::seq(
        Lambda::let_(
            LetKind::Strict,
            match_id.clone(),
            Lambda::prim(Primitive::Pdebugger, vec![], Location::none()),
            Lambda::unit(),
        ),
        Lambda::unit(),
    );

    assert_eq!(module_side_effect_reason(&lam).as_deref(), Some("match"));
}

#[test]
fn module_side_effect_reason_keeps_empty_reason_for_impure_nops() {
    let lam = Lambda::seq(
        Lambda::prim(Primitive::Pdebugger, vec![], Location::none()),
        Lambda::unit(),
    );

    assert_eq!(module_side_effect_reason(&lam).as_deref(), Some(""));
}

#[test]
fn resolves_runtime_dynamic_import_to_string_path() {
    let runtime = tempdir().expect("failed to create runtime tempdir");
    let runtime_ocaml = runtime.path().join("lib").join("ocaml");
    fs::create_dir_all(&runtime_ocaml).expect("failed to create runtime ocaml dir");
    fs::write(runtime_ocaml.join("Belt_List.cmi"), []).expect("failed to stub runtime cmi");

    let project = tempdir().expect("failed to create project tempdir");
    let source = project.path().join("src").join("Import.res");
    let output = project.path().join("src").join("Import.mjs");

    let resolver = ModulePathResolver::from_compile_options(
        Some(source.to_str().expect("utf8 source path")),
        Some(output.as_path()),
        Some(runtime.path()),
        None,
    );
    let mut compiler = LambdaCompiler::with_module_path_resolver(Some(resolver));
    let program = compiler.compile_program(&Lambda::prim(
        Primitive::Pimport,
        vec![Lambda::global_module(
            Ident::create_persistent("Belt_List"),
            true,
        )],
        Location::none(),
    ));

    let [stmt] = program.block.as_slice() else {
        panic!("expected a single import expression statement");
    };
    match &stmt.desc {
        StatementDesc::Exp(Expression {
            desc: ExpressionDesc::Call(func, args, _),
            ..
        }) => {
            assert!(matches!(
                func.desc,
                ExpressionDesc::Var(crate::js_ir::VIdent::Id(ref id)) if id.name() == "import"
            ));
            assert!(matches!(
                args.as_slice(),
                [Expression {
                    desc: ExpressionDesc::Str { txt, .. },
                    ..
                }] if txt == "@rescript/runtime/lib/es6/Belt_List.js"
            ));
        }
        other => panic!("expected import(\"...\") call, got {other:?}"),
    }
}

#[test]
fn resolves_local_module_paths_from_ast_metadata() {
    let project = tempdir().expect("failed to create project tempdir");
    let source_dir = project.path().join("src");
    let build_dir = project.path().join("lib").join("bs").join("src");
    fs::create_dir_all(&source_dir).expect("failed to create source dir");
    fs::create_dir_all(&build_dir).expect("failed to create build dir");

    let current_source = source_dir.join("Current.res");
    let target_source = source_dir.join("ModuleWithAlias.res");
    fs::write(&current_source, "").expect("failed to stub current source");
    fs::write(&target_source, "").expect("failed to stub target source");
    write_ast_source_stub(&build_dir.join("ModuleWithAlias.ast"), &target_source);

    let mut pers = PersistentEnv::new();
    pers.set_load_path(vec![build_dir]);

    let resolver = ModulePathResolver::from_compile_options(
        Some(current_source.to_str().expect("utf8 current source path")),
        Some(source_dir.join("Current.mjs").as_path()),
        None,
        Some(pers),
    );
    let module = ModuleId {
        id: Ident::create_persistent("ModuleWithAlias"),
        kind: Kind::Ml,
        dynamic_import: true,
    };

    assert_eq!(
        resolver.resolve_module_path(&module).as_deref(),
        Some("./ModuleWithAlias.mjs")
    );
}

#[test]
fn lowers_paddint_with_int32_coercion() {
    let mut compiler = LambdaCompiler::new();
    let lhs = Ident::create_local("lhs");
    let rhs = Ident::create_local("rhs");
    let program = compiler.compile_program(&Lambda::prim(
        Primitive::Paddint,
        vec![Lambda::var(lhs.clone()), Lambda::var(rhs.clone())],
        Location::none(),
    ));

    let [stmt] = program.block.as_slice() else {
        panic!("expected a single expression statement");
    };
    match &stmt.desc {
        StatementDesc::Exp(Expression {
            desc: ExpressionDesc::Bin(BinOp::Bor, left, right),
            ..
        }) => {
            assert!(matches!(
                right.as_ref(),
                Expression {
                    desc: ExpressionDesc::Number(Number::Int { i: 0, .. }),
                    ..
                }
            ));
            assert!(matches!(
                left.as_ref(),
                Expression {
                    desc: ExpressionDesc::Bin(BinOp::Plus, lhs_expr, rhs_expr),
                    ..
                }
                if matches!(
                    lhs_expr.as_ref(),
                    Expression {
                        desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                        ..
                    } if id.same(&lhs)
                ) && matches!(
                    rhs_expr.as_ref(),
                    Expression {
                        desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                        ..
                    } if id.same(&rhs)
                )
            ));
        }
        other => panic!("expected `lhs + rhs | 0`, got {other:?}"),
    }
}

#[test]
fn lowers_poffsetref_to_ref_contents_update() {
    let mut compiler = LambdaCompiler::new();
    let cell = Ident::create_local("cell");
    let program = compiler.compile_program(&Lambda::prim(
        Primitive::Poffsetref(1),
        vec![Lambda::var(cell.clone())],
        Location::none(),
    ));

    let [stmt] = program.block.as_slice() else {
        panic!("expected a single effect statement");
    };
    match &stmt.desc {
        StatementDesc::Exp(Expression {
            desc: ExpressionDesc::Bin(BinOp::Eq, left, right),
            ..
        }) => {
            assert!(matches!(
                left.as_ref(),
                Expression {
                    desc: ExpressionDesc::StaticIndex(target, field, None),
                    ..
                } if field == "contents"
                    && matches!(
                        target.as_ref(),
                        Expression {
                            desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                            ..
                        } if id.same(&cell)
                    )
            ));
            assert!(matches!(
                right.as_ref(),
                Expression {
                    desc: ExpressionDesc::Bin(BinOp::Bor, offset_inner, truncation),
                    ..
                }
                if matches!(
                    truncation.as_ref(),
                    Expression {
                        desc: ExpressionDesc::Number(Number::Int { i: 0, .. }),
                        ..
                    }
                ) && matches!(
                    offset_inner.as_ref(),
                    Expression {
                        desc: ExpressionDesc::Bin(BinOp::Plus, read_back, delta),
                        ..
                    }
                    if matches!(
                        read_back.as_ref(),
                        Expression {
                            desc: ExpressionDesc::StaticIndex(target, field, None),
                            ..
                        } if field == "contents"
                            && matches!(
                                target.as_ref(),
                                Expression {
                                    desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                                    ..
                                } if id.same(&cell)
                            )
                    ) && matches!(
                        delta.as_ref(),
                        Expression {
                            desc: ExpressionDesc::Number(Number::Int { i: 1, .. }),
                            ..
                        }
                    )
                )
            ));
        }
        other => panic!("expected `cell.contents = cell.contents + 1 | 0`, got {other:?}"),
    }
}

#[test]
fn lassign_expression_lowers_to_statement_prelude_and_unit_value() {
    let mut compiler = LambdaCompiler::new();
    let cell = Ident::create_local("cell");
    let compiled = compiler.compile_expr(&Lambda::Lassign(
        cell.clone(),
        Box::new(Lambda::prim(
            Primitive::Poffsetint(1),
            vec![Lambda::var(cell.clone())],
            Location::none(),
        )),
    ));

    assert_eq!(print_block(&compiled.prelude), "cell = cell + 1 | 0;");
    assert!(matches!(
        compiled.expr,
        Expression {
            desc: ExpressionDesc::Undefined { is_unit: false },
            ..
        }
    ));
}

#[test]
fn let_bindings_of_unit_lassigns_emit_effects_before_undefined_declarations() {
    let mut compiler = LambdaCompiler::new();
    let u = Ident::create_local("u");
    let v = Ident::create_local("v");
    let block = compiler.compile_let_binding(
        LetKind::Strict,
        &v,
        &Lambda::Lassign(
            u.clone(),
            Box::new(Lambda::prim(
                Primitive::Poffsetint(1),
                vec![Lambda::var(u.clone())],
                Location::none(),
            )),
        ),
    );
    assert_eq!(print_block(&block), "u = u + 1 | 0;\n\nlet v;");
}

#[test]
fn lowers_pis_poly_var_block_to_typeof_object_check() {
    let mut compiler = LambdaCompiler::new();
    let value = Ident::create_local("value");
    let compiled = compiler.compile_expr(&Lambda::prim(
        Primitive::PisPolyVarBlock,
        vec![Lambda::var(value)],
        Location::none(),
    ));

    assert!(
        compiled.prelude.is_empty(),
        "unexpected prelude:\n{}",
        print_block(&compiled.prelude)
    );
    assert!(
        print_expression(&compiled.expr) == "typeof value === \"object\"",
        "rendered expression was:\n{}",
        print_expression(&compiled.expr)
    );
}

#[test]
fn lowers_pisint_to_typeof_number_check() {
    let mut compiler = LambdaCompiler::new();
    let value = Ident::create_local("value");
    let compiled = compiler.compile_expr(&Lambda::prim(
        Primitive::Pisint,
        vec![Lambda::var(value)],
        Location::none(),
    ));

    assert!(
        compiled.prelude.is_empty(),
        "unexpected prelude:\n{}",
        print_block(&compiled.prelude)
    );
    assert!(
        print_expression(&compiled.expr) == "typeof value === \"number\"",
        "rendered expression was:\n{}",
        print_expression(&compiled.expr)
    );
}

#[test]
fn typeof_folding_matches_ocaml_js_exp_make_for_supported_literals() {
    assert_eq!(
        print_expression(&ocaml_typeof_expr(Expression::number(Number::int(3)))),
        "\"number\""
    );
    assert_eq!(
        print_expression(&ocaml_typeof_expr(Expression::string("x"))),
        "\"string\""
    );
    assert_eq!(
        print_expression(&ocaml_typeof_expr(Expression::bool(true))),
        "\"boolean\""
    );
    assert_eq!(
        print_expression(&ocaml_typeof_expr(Expression::array(
            vec![],
            MutableFlag::Immutable,
        ))),
        "\"object\""
    );
}

#[test]
fn typeof_literal_comparisons_fold_like_ocaml_string_equal() {
    assert_eq!(
        print_expression(&raw_typeof_comparison(
            Expression::number(Number::int(3)),
            BinOp::NotEqEq,
            "number",
        )),
        "false"
    );
    assert_eq!(
        print_expression(&raw_typeof_comparison(
            Expression::string("x"),
            BinOp::EqEqEq,
            "object",
        )),
        "false"
    );
}

#[test]
fn lowers_pisout_to_ocaml_range_check_shapes() {
    let mut compiler = LambdaCompiler::new();
    let value = Ident::create_local("value");
    let zero_offset = compiler.compile_expr(&Lambda::prim(
        Primitive::Pisout(0),
        vec![Lambda::const_(Constant::int(1)), Lambda::var(value.clone())],
        Location::none(),
    ));
    let one_offset = compiler.compile_expr(&Lambda::prim(
        Primitive::Pisout(1),
        vec![Lambda::const_(Constant::int(1)), Lambda::var(value)],
        Location::none(),
    ));

    assert!(
        zero_offset.prelude.is_empty(),
        "unexpected prelude:\n{}",
        print_block(&zero_offset.prelude)
    );
    assert!(
        one_offset.prelude.is_empty(),
        "unexpected prelude:\n{}",
        print_block(&one_offset.prelude)
    );
    assert!(
        print_expression(&zero_offset.expr) == "value !== 0 && value !== 1",
        "rendered expression was:\n{}",
        print_expression(&zero_offset.expr)
    );
    assert!(
        print_expression(&one_offset.expr) == "value !== -1 && value !== 0",
        "rendered expression was:\n{}",
        print_expression(&one_offset.expr)
    );
}

#[test]
fn lowers_plsrint_with_int32_coercion() {
    let mut compiler = LambdaCompiler::new();
    let value = Ident::create_local("value");
    let shift = Ident::create_local("shift");
    let program = compiler.compile_program(&Lambda::prim(
        Primitive::Plsrint,
        vec![Lambda::var(value.clone()), Lambda::var(shift.clone())],
        Location::none(),
    ));

    let [stmt] = program.block.as_slice() else {
        panic!("expected a single expression statement");
    };
    match &stmt.desc {
        StatementDesc::Exp(Expression {
            desc: ExpressionDesc::Bin(BinOp::Bor, left, right),
            ..
        }) => {
            assert!(matches!(
                right.as_ref(),
                Expression {
                    desc: ExpressionDesc::Number(Number::Int { i: 0, .. }),
                    ..
                }
            ));
            assert!(matches!(
                left.as_ref(),
                Expression {
                    desc: ExpressionDesc::Bin(BinOp::Lsr, value_expr, shift_expr),
                    ..
                }
                if matches!(
                    value_expr.as_ref(),
                    Expression {
                        desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                        ..
                    } if id.same(&value)
                ) && matches!(
                    shift_expr.as_ref(),
                    Expression {
                        desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                        ..
                    } if id.same(&shift)
                )
            ));
        }
        other => panic!("expected `value >>> shift | 0`, got {other:?}"),
    }
}

#[test]
fn lowers_pmulint_by_positive_power_of_two_to_shift() {
    let value = Ident::create_local("value");
    let expr = int32_mul(Expression::var(value.clone()), int_expr(2));

    match expr.desc {
        ExpressionDesc::Bin(BinOp::Lsl, left, right) => {
            assert!(matches!(
                left.as_ref(),
                Expression {
                    desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                    ..
                } if id.same(&value)
            ));
            assert!(matches!(
                right.as_ref(),
                Expression {
                    desc: ExpressionDesc::Number(Number::Int { i: 1, .. }),
                    ..
                }
            ));
        }
        other => panic!("expected `value << 1`, got {other:?}"),
    }
}

#[test]
fn lowers_pxorint_literal_operands_to_folded_constant() {
    let expr = int32_bxor(int_expr(2), int_expr(-3));

    match expr.desc {
        ExpressionDesc::Number(Number::Int { i: -1, .. }) => {}
        other => panic!("expected folded `-1`, got {other:?}"),
    }
}

#[test]
fn to_int32_drops_redundant_bor_after_logical_shift() {
    let value = Ident::create_local("value");
    let expr = to_int32(Expression::bin(
        BinOp::Lsr,
        Expression::var(value.clone()),
        int_expr(3),
    ));

    match expr.desc {
        ExpressionDesc::Bin(BinOp::Lsr, left, right) => {
            assert!(matches!(
                left.as_ref(),
                Expression {
                    desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                    ..
                } if id.same(&value)
            ));
            assert!(matches!(
                right.as_ref(),
                Expression {
                    desc: ExpressionDesc::Number(Number::Int { i: 3, .. }),
                    ..
                }
            ));
        }
        other => panic!("expected bare logical shift, got {other:?}"),
    }
}

#[test]
fn int32_band_drops_redundant_bor_on_left_operand() {
    let value = Ident::create_local("value");
    let expr = int32_band(
        to_int32(Expression::bin(
            BinOp::Plus,
            Expression::var(value),
            int_expr(1),
        )),
        int_expr(0x7fff_ffff),
    );

    assert_eq!(print_expression(&expr), "value + 1 & 2147483647");
}

#[test]
fn lowers_psome_not_nest_to_identity_optional_block() {
    let mut compiler = LambdaCompiler::new();
    let value = Ident::create_local("value");
    let compiled = compiler.compile_expr(&Lambda::prim(
        Primitive::PsomeNotNest,
        vec![Lambda::var(value.clone())],
        Location::none(),
    ));

    assert!(compiled.prelude.is_empty());
    match &compiled.expr.desc {
        ExpressionDesc::OptionalBlock(inner, true) => {
            assert!(matches!(
                inner.as_ref(),
                Expression {
                    desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                    ..
                } if id.same(&value)
            ));
        }
        other => panic!("expected identity optional block, got {other:?}"),
    }
}

#[test]
fn lowers_psome_immediates_to_identity_optional_block_like_ocaml() {
    let mut compiler = LambdaCompiler::new();
    let compiled = compiler.compile_expr(&Lambda::prim(
        Primitive::Psome,
        vec![Lambda::const_(Constant::int(3))],
        Location::none(),
    ));

    assert!(compiled.prelude.is_empty());
    match &compiled.expr.desc {
        ExpressionDesc::OptionalBlock(inner, true) => {
            assert!(matches!(
                inner.as_ref(),
                Expression {
                    desc: ExpressionDesc::Number(Number::Int { i: 3, .. }),
                    ..
                }
            ));
        }
        other => panic!("expected identity optional block for an immediate, got {other:?}"),
    }
}

fn lowers_pval_from_option_optional_block_to_inner_value() {
    let mut compiler = LambdaCompiler::new();
    let value = Ident::create_local("value");
    let program = compiler.compile_program(&Lambda::prim(
        Primitive::PvalFromOption,
        vec![Lambda::prim(
            Primitive::PsomeNotNest,
            vec![Lambda::var(value.clone())],
            Location::none(),
        )],
        Location::none(),
    ));

    let [stmt] = program.block.as_slice() else {
        panic!("expected a single expression statement");
    };
    match &stmt.desc {
        StatementDesc::Exp(Expression {
            desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
            ..
        }) => assert!(id.same(&value)),
        other => panic!("expected optional unwrap to lower to the inner value, got {other:?}"),
    }
}

#[test]
fn lowers_pval_from_option_to_primitive_option_runtime_call() {
    let mut compiler = LambdaCompiler::new();
    let value = Ident::create_local("value");
    let compiled = compiler.compile_expr(&Lambda::prim(
        Primitive::PvalFromOption,
        vec![Lambda::var(value.clone())],
        Location::none(),
    ));

    assert!(compiled.prelude.is_empty());
    let ExpressionDesc::Call(func, args, _) = &compiled.expr.desc else {
        panic!("expected option unwrap to lower to a runtime call");
    };
    assert!(matches!(
        func.as_ref(),
        Expression {
            desc: ExpressionDesc::Var(crate::js_ir::VIdent::Qualified(module, Some(member))),
            ..
        } if module.id.name() == "Primitive_option" && member == "valFromOption"
    ));
    assert!(matches!(
        args.as_slice(),
        [Expression {
            desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
            ..
        }] if id.same(&value)
    ));
    assert_eq!(
        print_expression(&compiled.expr),
        "Primitive_option.valFromOption(value)"
    );
}

#[test]
fn lowers_pnull_to_opt_non_inline_operand_to_primitive_option_from_null() {
    let mut compiler = LambdaCompiler::new();
    let compiled = compiler.compile_expr(&Lambda::prim(
        Primitive::PnullToOpt,
        vec![Lambda::const_(Constant::string("value"))],
        Location::none(),
    ));

    assert!(compiled.prelude.is_empty());
    let ExpressionDesc::Call(func, args, _) = &compiled.expr.desc else {
        panic!("expected null-to-option lowering to use the runtime helper");
    };
    assert!(matches!(
        func.as_ref(),
        Expression {
            desc: ExpressionDesc::Var(crate::js_ir::VIdent::Qualified(module, Some(member))),
            ..
        } if module.id.name() == "Primitive_option" && member == "fromNull"
    ));
    assert!(matches!(
        args.as_slice(),
        [Expression {
            desc: ExpressionDesc::Str { txt, .. },
            ..
        }] if txt == "value"
    ));
    assert_eq!(
        print_expression(&compiled.expr),
        "Primitive_option.fromNull(\"value\")"
    );
}

#[test]
fn lowers_pnull_undefined_to_opt_non_inline_operand_to_primitive_option_from_nullable() {
    let mut compiler = LambdaCompiler::new();
    let compiled = compiler.compile_expr(&Lambda::prim(
        Primitive::PnullUndefinedToOpt,
        vec![Lambda::const_(Constant::string("value"))],
        Location::none(),
    ));

    assert!(compiled.prelude.is_empty());
    let ExpressionDesc::Call(func, args, _) = &compiled.expr.desc else {
        panic!("expected nullable-to-option lowering to use the runtime helper");
    };
    assert!(matches!(
        func.as_ref(),
        Expression {
            desc: ExpressionDesc::Var(crate::js_ir::VIdent::Qualified(module, Some(member))),
            ..
        } if module.id.name() == "Primitive_option" && member == "fromNullable"
    ));
    assert!(matches!(
        args.as_slice(),
        [Expression {
            desc: ExpressionDesc::Str { txt, .. },
            ..
        }] if txt == "value"
    ));
    assert_eq!(
        print_expression(&compiled.expr),
        "Primitive_option.fromNullable(\"value\")"
    );
}

#[test]
fn compile_deps_program_imports_primitive_option_for_non_identity_optional_block() {
    let mut compiler = LambdaCompiler::new();
    let global = Ident::create_persistent("value");
    let exported = Ident::create_local("wrapped");
    let lam = Lambda::let_(
        LetKind::Strict,
        exported.clone(),
        Lambda::prim(
            Primitive::Psome,
            vec![Lambda::var(global.clone())],
            Location::none(),
        ),
        Lambda::prim(
            Primitive::Pmakeblock(
                0,
                TagInfo::ModuleExport(vec![exported.clone()]),
                Mutable::Immutable,
            ),
            vec![Lambda::var(exported.clone())],
            Location::none(),
        ),
    );

    let deps = compiler.compile_deps_program(&lam);
    assert!(deps.modules.iter().any(|module| {
        module.kind == Kind::Runtime && module.id.name() == "Primitive_option"
    }));

    let resolver = ModulePathResolver::from_compile_options(
        None,
        Some(std::path::Path::new("/tmp/wrapped.mjs")),
        None,
        None,
    );
    let rendered = print_deps_program(&deps, Some(&resolver));
    assert!(rendered.contains(
        "import * as Primitive_option from \"@rescript/runtime/lib/es6/Primitive_option.js\";"
    ));
    assert!(rendered.contains("let wrapped = Primitive_option.some(value);"));
}

#[test]
fn external_module_ids_reuse_first_binding_for_same_bundle_and_default() {
    let mut compiler = LambdaCompiler::new();
    let plain = ExternalModuleName {
        bundle: "x".to_string(),
        module_bind_name: ExternalModuleBindName::Nothing,
        import_attributes: None,
    };
    let hinted = ExternalModuleName {
        bundle: "x".to_string(),
        module_bind_name: ExternalModuleBindName::HintName("U".to_string()),
        import_attributes: None,
    };

    let plain_module = compiler.external_module_id(&plain, false, false);
    let hinted_module = compiler.external_module_id(&hinted, false, false);
    let default_module = compiler.external_module_id(&plain, true, false);
    let dynamic_plain_module = compiler.external_module_id(&plain, false, true);

    assert_eq!(plain_module, hinted_module);
    assert_eq!(plain_module.id.name(), "X");
    assert!(!plain_module.id.same(&default_module.id));
    assert!(plain_module.id.same(&dynamic_plain_module.id));
    assert!(!plain_module.dynamic_import);
    assert!(dynamic_plain_module.dynamic_import);
}

#[test]
fn lowers_nullable_predicates_to_js_null_checks() {
    let mut compiler = LambdaCompiler::new();
    let value = Ident::create_local("value");

    let null_compiled = compiler.compile_expr(&Lambda::prim(
        Primitive::PisNull,
        vec![Lambda::var(value.clone())],
        Location::none(),
    ));
    let undefined_compiled = compiler.compile_expr(&Lambda::prim(
        Primitive::PisUndefined,
        vec![Lambda::var(value.clone())],
        Location::none(),
    ));
    let nullable_compiled = compiler.compile_expr(&Lambda::prim(
        Primitive::PisNullUndefined,
        vec![Lambda::var(value.clone())],
        Location::none(),
    ));

    assert!(null_compiled.prelude.is_empty());
    match &null_compiled.expr.desc {
        ExpressionDesc::Bin(BinOp::EqEqEq, left, right) => {
            assert!(matches!(
                left.as_ref(),
                Expression {
                    desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                    ..
                } if id.same(&value)
            ));
            assert!(matches!(
                right.as_ref(),
                Expression {
                    desc: ExpressionDesc::Null,
                    ..
                }
            ));
        }
        other => panic!("expected `value === null`, got {other:?}"),
    }

    assert!(undefined_compiled.prelude.is_empty());
    match &undefined_compiled.expr.desc {
        ExpressionDesc::Bin(BinOp::EqEqEq, left, right) => {
            assert!(matches!(
                left.as_ref(),
                Expression {
                    desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                    ..
                } if id.same(&value)
            ));
            assert!(matches!(
                right.as_ref(),
                Expression {
                    desc: ExpressionDesc::Undefined { .. },
                    ..
                }
            ));
        }
        other => panic!("expected `value === undefined`, got {other:?}"),
    }

    assert!(nullable_compiled.prelude.is_empty());
    match &nullable_compiled.expr.desc {
        ExpressionDesc::IsNullOrUndefined(inner) => {
            assert!(matches!(
                inner.as_ref(),
                Expression {
                    desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                    ..
                } if id.same(&value)
            ));
        }
        other => panic!("expected `value == null`, got {other:?}"),
    }
}

#[test]
fn lowers_pfield_cons_to_hd_tl_properties() {
    let mut compiler = LambdaCompiler::new();
    let list = Ident::create_local("list");
    let head_program = compiler.compile_program(&Lambda::prim(
        Primitive::Pfield(0, FieldDbgInfo::Cons),
        vec![Lambda::var(list.clone())],
        Location::none(),
    ));
    let tail_program = compiler.compile_program(&Lambda::prim(
        Primitive::Pfield(1, FieldDbgInfo::Cons),
        vec![Lambda::var(list.clone())],
        Location::none(),
    ));

    let [head_stmt] = head_program.block.as_slice() else {
        panic!("expected a single expression statement for head");
    };
    let [tail_stmt] = tail_program.block.as_slice() else {
        panic!("expected a single expression statement for tail");
    };

    match &head_stmt.desc {
        StatementDesc::Exp(Expression {
            desc: ExpressionDesc::StaticIndex(target, field, _),
            ..
        }) => {
            assert_eq!(field, "hd");
            assert!(matches!(
                target.as_ref(),
                Expression {
                    desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                    ..
                } if id.same(&list)
            ));
        }
        other => panic!("expected head access to lower to `.hd`, got {other:?}"),
    }

    match &tail_stmt.desc {
        StatementDesc::Exp(Expression {
            desc: ExpressionDesc::StaticIndex(target, field, _),
            ..
        }) => {
            assert_eq!(field, "tl");
            assert!(matches!(
                target.as_ref(),
                Expression {
                    desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                    ..
                } if id.same(&list)
            ));
        }
        other => panic!("expected tail access to lower to `.tl`, got {other:?}"),
    }
}

#[test]
fn lowers_module_pfield_with_ocaml_identifier_conversion() {
    let mut compiler = LambdaCompiler::new();
    let module_value = Ident::create_local("Js_promise2");
    let expr = compiler.compile_field_access(
        3,
        &FieldDbgInfo::Module {
            name: "catch".to_string(),
        },
        &Expression::var(module_value.clone()),
    );

    match &expr.desc {
        ExpressionDesc::StaticIndex(target, field, Some(index)) => {
            assert_eq!(field, "$$catch");
            assert_eq!(*index, 3);
            assert!(matches!(
                target.as_ref(),
                Expression {
                    desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                    ..
                } if id.same(&module_value)
            ));
        }
        other => panic!(
            "expected module field access to lower to converted static index, got {other:?}"
        ),
    }

    assert_eq!(print_expression(&expr), "Js_promise2.$$catch");
}

#[test]
fn lowers_extension_pfield_to_named_payload_property_like_ocaml() {
    let mut compiler = LambdaCompiler::new();
    let exn = Ident::create_local("exn");
    let expr = compiler.compile_field_access(
        1,
        &FieldDbgInfo::Extension,
        &Expression::var(exn.clone()),
    );

    match &expr.desc {
        ExpressionDesc::StaticIndex(target, field, Some(index)) => {
            assert_eq!(field, "_1");
            assert_eq!(*index, 1);
            assert!(matches!(
                target.as_ref(),
                Expression {
                    desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                    ..
                } if id.same(&exn)
            ));
        }
        other => panic!(
            "expected extension field access to lower to a named static index, got {other:?}"
        ),
    }

    assert_eq!(print_expression(&expr), "exn._1");
}

#[test]
fn lowers_module_pfield_from_pure_caml_block_directly_like_ocaml() {
    let mut compiler = LambdaCompiler::new();
    let eq = Ident::create_local("Eq");
    let expr = compiler.compile_field_access(
        0,
        &FieldDbgInfo::Module {
            name: "Eq".to_string(),
        },
        &Expression::new(ExpressionDesc::CamlBlock(
            vec![Expression::var(eq.clone())],
            MutableFlag::Immutable,
            Box::new(Expression::number(Number::int(0))),
            TagInfo::Module(vec!["Eq".to_string()]),
        )),
    );

    assert!(matches!(
        &expr,
        Expression {
            desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
            ..
        } if id.same(&eq)
    ));
    assert_eq!(print_expression(&expr), "Eq");
}

#[test]
fn lowers_record_pfield_from_pure_caml_block_directly_like_ocaml() {
    let mut compiler = LambdaCompiler::new();
    let value = Ident::create_local("value");
    let expr = compiler.compile_field_access(
        0,
        &FieldDbgInfo::Record {
            name: "d".to_string(),
            mutable_flag: crate::parser::ast::MutableFlag::Immutable,
        },
        &Expression::new(ExpressionDesc::CamlBlock(
            vec![Expression::var(value.clone())],
            MutableFlag::Immutable,
            Box::new(Expression::number(Number::int(0))),
            TagInfo::Record {
                fields: vec![("d".to_string(), false)],
                mutable_flag: crate::parser::ast::MutableFlag::Immutable,
            },
        )),
    );

    assert!(matches!(
        &expr,
        Expression {
            desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
            ..
        } if id.same(&value)
    ));
    assert_eq!(print_expression(&expr), "value");
}

#[test]
fn lowers_cons_pfield_from_pure_caml_block_directly_like_ocaml() {
    let mut compiler = LambdaCompiler::new();
    let head = Ident::create_local("head");
    let tail = Ident::create_local("tail");
    let head_expr = compiler.compile_field_access(
        0,
        &FieldDbgInfo::Cons,
        &Expression::new(ExpressionDesc::CamlBlock(
            vec![Expression::var(head.clone()), Expression::var(tail.clone())],
            MutableFlag::Immutable,
            Box::new(Expression::number(Number::int(0))),
            TagInfo::Constructor {
                name: "::".to_string(),
                num_nonconst: 1,
                tag: 0,
                attrs: vec![],
            },
        )),
    );
    let tail_expr = compiler.compile_field_access(
        1,
        &FieldDbgInfo::Cons,
        &Expression::new(ExpressionDesc::CamlBlock(
            vec![Expression::var(head.clone()), Expression::var(tail.clone())],
            MutableFlag::Immutable,
            Box::new(Expression::number(Number::int(0))),
            TagInfo::Constructor {
                name: "::".to_string(),
                num_nonconst: 1,
                tag: 0,
                attrs: vec![],
            },
        )),
    );

    assert!(matches!(
        &head_expr,
        Expression {
            desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
            ..
        } if id.same(&head)
    ));
    assert!(matches!(
        &tail_expr,
        Expression {
            desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
            ..
        } if id.same(&tail)
    ));
}

#[test]
fn lowers_extension_pfield_from_pure_caml_block_directly_like_ocaml() {
    let mut compiler = LambdaCompiler::new();
    let payload = Ident::create_local("payload");
    let expr = compiler.compile_field_access(
        1,
        &FieldDbgInfo::Extension,
        &Expression::new(ExpressionDesc::CamlBlock(
            vec![
                Expression::string("Exn".to_string()),
                Expression::var(payload.clone()),
            ],
            MutableFlag::Immutable,
            Box::new(Expression::number(Number::int(0))),
            TagInfo::Extension,
        )),
    );

    assert!(matches!(
        &expr,
        Expression {
            desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
            ..
        } if id.same(&payload)
    ));
    assert_eq!(print_expression(&expr), "payload");
}

#[test]
fn lowers_polyvar_pfield_to_named_static_access_like_ocaml() {
    let mut compiler = LambdaCompiler::new();
    let variant = Ident::create_local("variant");
    let tag = compiler.compile_field_access(
        0,
        &FieldDbgInfo::PolyVarTag,
        &Expression::var(variant.clone()),
    );
    let value = compiler.compile_field_access(
        1,
        &FieldDbgInfo::PolyVarContent,
        &Expression::var(variant.clone()),
    );

    match &tag.desc {
        ExpressionDesc::StaticIndex(target, field, Some(index)) => {
            assert_eq!(field, "NAME");
            assert_eq!(*index, 0);
            assert!(matches!(
                target.as_ref(),
                Expression {
                    desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                    ..
                } if id.same(&variant)
            ));
        }
        other => panic!("expected polyvariant tag access to lower to `.NAME`, got {other:?}"),
    }

    match &value.desc {
        ExpressionDesc::StaticIndex(target, field, Some(index)) => {
            assert_eq!(field, "VAL");
            assert_eq!(*index, 1);
            assert!(matches!(
                target.as_ref(),
                Expression {
                    desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                    ..
                } if id.same(&variant)
            ));
        }
        other => {
            panic!("expected polyvariant payload access to lower to `.VAL`, got {other:?}")
        }
    }

    assert_eq!(print_expression(&tag), "variant.NAME");
    assert_eq!(print_expression(&value), "variant.VAL");
}

#[test]
fn lowers_polyvar_pfield_from_pure_caml_block_directly_like_ocaml() {
    let mut compiler = LambdaCompiler::new();
    let payload = Ident::create_local("payload");
    let block = Expression::new(ExpressionDesc::CamlBlock(
        vec![Expression::string("Tag"), Expression::var(payload.clone())],
        MutableFlag::Immutable,
        Box::new(Expression::number(Number::int(0))),
        TagInfo::PolyVar("Tag".to_string()),
    ));
    let tag = compiler.compile_field_access(0, &FieldDbgInfo::PolyVarTag, &block);
    let value = compiler.compile_field_access(1, &FieldDbgInfo::PolyVarContent, &block);

    assert_eq!(print_expression(&tag), "\"Tag\"");
    assert!(matches!(
        &value,
        Expression {
            desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
            ..
        } if id.same(&payload)
    ));
    assert_eq!(print_expression(&value), "payload");
}

#[test]
fn lowers_qualified_ml_module_default_field_without_preconverting_the_member_name() {
    let mut compiler = LambdaCompiler::new();
    let expr = compiler.compile_field_access(
        0,
        &FieldDbgInfo::Module {
            name: "default".to_string(),
        },
        &Expression::qualified(
            ModuleId {
                id: Ident::create_persistent("Es6_export"),
                kind: Kind::Ml,
                dynamic_import: false,
            },
            None,
        ),
    );

    match &expr.desc {
        ExpressionDesc::Var(crate::js_ir::VIdent::Qualified(module, Some(member))) => {
            assert_eq!(module.id.name(), "Es6_export");
            assert!(matches!(module.kind, Kind::Ml));
            assert_eq!(member, "default");
        }
        other => {
            panic!("expected qualified ml-module access for default export, got {other:?}")
        }
    }

    assert_eq!(print_expression(&expr), "Es6_export.default");
}

#[test]
fn lowers_qualified_ml_module_reserved_fields_through_vident_printing() {
    let mut compiler = LambdaCompiler::new();
    let expr = compiler.compile_field_access(
        3,
        &FieldDbgInfo::Module {
            name: "catch".to_string(),
        },
        &Expression::qualified(
            ModuleId {
                id: Ident::create_persistent("Js_promise2"),
                kind: Kind::Ml,
                dynamic_import: false,
            },
            None,
        ),
    );

    match &expr.desc {
        ExpressionDesc::Var(crate::js_ir::VIdent::Qualified(module, Some(member))) => {
            assert_eq!(module.id.name(), "Js_promise2");
            assert!(matches!(module.kind, Kind::Ml));
            assert_eq!(member, "catch");
        }
        other => {
            panic!("expected qualified ml-module access for reserved field, got {other:?}")
        }
    }

    assert_eq!(print_expression(&expr), "Js_promise2.$$catch");
}

#[test]
fn lowers_qualified_ml_module_closed_undefined_constant_from_cmj() {
    let resolver = resolver_with_checked_in_cmj();
    let mut compiler = LambdaCompiler::with_module_path_resolver(Some(resolver));
    let expr = compiler.compile_field_access(
        0,
        &FieldDbgInfo::Module {
            name: "empty".to_string(),
        },
        &Expression::qualified(
            ModuleId {
                id: Ident::create_persistent("Belt_MapString"),
                kind: Kind::Ml,
                dynamic_import: false,
            },
            None,
        ),
    );

    assert!(matches!(
        expr.desc,
        ExpressionDesc::Undefined { is_unit: false }
    ));
    assert_eq!(print_expression(&expr), "undefined");
}

#[test]
fn external_shadow_pass_rewrites_only_shadowed_initializer_reads() {
    let process = Ident::create_local("process");
    let proc = Ident::create_local("proc");
    let global_process = Ident::create_persistent("process");
    let deps = DepsProgram {
        program: Program::new(
            vec![
                Statement::variable(VariableDeclaration {
                    ident: process.clone(),
                    value: Some(Expression::var(global_process.clone())),
                    property: LetKind::Strict,
                    ident_info: IdentInfo::default(),
                }),
                Statement::variable(VariableDeclaration {
                    ident: proc,
                    value: Some(Expression::var(global_process.clone())),
                    property: LetKind::Strict,
                    ident_info: IdentInfo::default(),
                }),
            ],
            vec![],
        ),
        modules: vec![],
        side_effect: None,
    };

    let rewritten = apply_external_shadow_pass(deps);
    let [first, second] = rewritten.program.block.as_slice() else {
        panic!("expected two variable declarations");
    };

    match &first.desc {
        StatementDesc::Variable(VariableDeclaration {
            value:
                Some(Expression {
                    desc: ExpressionDesc::StaticIndex(target, field, _),
                    ..
                }),
            ..
        }) => {
            assert_eq!(field, "process");
            assert!(matches!(
                target.desc,
                ExpressionDesc::Var(crate::js_ir::VIdent::Id(ref id)) if id.name() == "globalThis"
            ));
        }
        other => panic!("expected first initializer to read globalThis.process, got {other:?}"),
    }

    match &second.desc {
        StatementDesc::Variable(VariableDeclaration {
            value:
                Some(Expression {
                    desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                    ..
                }),
            ..
        }) => assert_eq!(id.name(), "process"),
        other => {
            panic!("expected second initializer to remain a plain process read, got {other:?}")
        }
    }
}

#[test]
fn js_shake_pass_removes_unused_pure_toplevel_bindings_and_statements() {
    let exported = Ident::create_local("exported");
    let unused = Ident::create_local("unused");
    let deps = apply_js_shake_pass(DepsProgram {
        program: Program::new(
            vec![
                Statement::exp(Expression::undefined(false)),
                Statement::variable(VariableDeclaration {
                    ident: unused,
                    value: Some(Expression::number(Number::int(1))),
                    property: LetKind::Strict,
                    ident_info: IdentInfo::default(),
                }),
                Statement::variable(VariableDeclaration {
                    ident: exported.clone(),
                    value: Some(Expression::number(Number::int(2))),
                    property: LetKind::Strict,
                    ident_info: IdentInfo::default(),
                }),
            ],
            vec![exported.clone()],
        ),
        modules: vec![],
        side_effect: None,
    });

    let [stmt] = deps.program.block.as_slice() else {
        panic!("expected only the exported binding to remain");
    };

    match &stmt.desc {
        StatementDesc::Variable(VariableDeclaration {
            ident,
            value:
                Some(Expression {
                    desc: ExpressionDesc::Number(Number::Int { i: 2, .. }),
                    ..
                }),
            ..
        }) => assert!(ident.same(&exported)),
        other => panic!("expected exported number binding, got {other:?}"),
    }
}

#[test]
fn js_shake_pass_keeps_export_dependencies_and_impure_bindings() {
    let dep = Ident::create_local("dep");
    let exported = Ident::create_local("exported");
    let callback = Ident::create_local("callback");
    let side = Ident::create_local("side");
    let deps = apply_js_shake_pass(DepsProgram {
        program: Program::new(
            vec![
                Statement::variable(VariableDeclaration {
                    ident: dep.clone(),
                    value: Some(Expression::number(Number::int(1))),
                    property: LetKind::Strict,
                    ident_info: IdentInfo::default(),
                }),
                Statement::variable(VariableDeclaration {
                    ident: exported.clone(),
                    value: Some(Expression::var(dep.clone())),
                    property: LetKind::Strict,
                    ident_info: IdentInfo::default(),
                }),
                Statement::variable(VariableDeclaration {
                    ident: side.clone(),
                    value: Some(Expression::call(
                        Expression::var(callback.clone()),
                        vec![],
                        CallInfo::default(),
                    )),
                    property: LetKind::Strict,
                    ident_info: IdentInfo::default(),
                }),
            ],
            vec![exported.clone()],
        ),
        modules: vec![],
        side_effect: None,
    });

    let [side_stmt, exported_stmt, dep_stmt] = deps.program.block.as_slice() else {
        panic!("expected the dependency chain and impure binding to remain");
    };

    match &side_stmt.desc {
        StatementDesc::Variable(VariableDeclaration {
            ident,
            value:
                Some(Expression {
                    desc: ExpressionDesc::Call(func, args, _),
                    ..
                }),
            ..
        }) => {
            assert!(ident.same(&side));
            assert!(args.is_empty());
            assert!(matches!(
                func.as_ref(),
                Expression {
                    desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                    ..
                } if id.same(&callback)
            ));
        }
        other => panic!("expected the impure binding to remain first, got {other:?}"),
    }
    match &exported_stmt.desc {
        StatementDesc::Variable(VariableDeclaration { ident, .. }) => {
            assert!(ident.same(&exported));
        }
        other => panic!("expected the exported binding to remain in the middle, got {other:?}"),
    }
    match &dep_stmt.desc {
        StatementDesc::Variable(VariableDeclaration { ident, .. }) => {
            assert!(ident.same(&dep));
        }
        other => panic!("expected the dependency binding to remain last, got {other:?}"),
    }
}

#[test]
fn one_unit_arg_functions_lower_to_zero_arg_js_functions() {
    let mut compiler = LambdaCompiler::new();
    let compiled = compiler.compile_expr(&Lambda::function_(
        1,
        vec![Ident::create_local("param")],
        Lambda::unit(),
        FunctionAttribute {
            one_unit_arg: true,
            ..FunctionAttribute::default()
        },
    ));

    assert!(compiled.prelude.is_empty());
    match compiled.expr.desc {
        ExpressionDesc::Fun { params, .. } => assert!(params.is_empty()),
        other => panic!("expected lowered JS function, got {other:?}"),
    }
}

#[test]
fn recursive_function_bindings_lower_directly_without_placeholder_assignments() {
    let mut compiler = LambdaCompiler::new();
    let func = Ident::create_local("u");
    let param = Ident::create_local("param");
    let lam = Lambda::letrec(
        vec![(
            func.clone(),
            Lambda::function_(
                1,
                vec![param],
                Lambda::var(func.clone()),
                FunctionAttribute::default(),
            ),
        )],
        Lambda::unit(),
    );

    let compiled = compiler.compile_expr(&lam);
    let rendered = print_block(&compiled.prelude);

    assert!(
        rendered.contains("function u(param)"),
        "expected a direct recursive function declaration:\n{rendered}"
    );
    assert!(
        !rendered.contains("let u;"),
        "unexpected recursive placeholder declaration:\n{rendered}"
    );
    assert!(
        !rendered.contains("u ="),
        "unexpected recursive assignment fallback:\n{rendered}"
    );
}

#[test]
fn mutually_recursive_function_bindings_lower_without_placeholder_assignments() {
    let mut compiler = LambdaCompiler::new();
    let even = Ident::create_local("even");
    let odd = Ident::create_local("odd");
    let n = Ident::create_local("n");
    let lam = Lambda::letrec(
        vec![
            (
                even.clone(),
                Lambda::function_(
                    1,
                    vec![n.clone()],
                    Lambda::var(odd.clone()),
                    FunctionAttribute::default(),
                ),
            ),
            (
                odd.clone(),
                Lambda::function_(
                    1,
                    vec![n],
                    Lambda::var(even.clone()),
                    FunctionAttribute::default(),
                ),
            ),
        ],
        Lambda::unit(),
    );

    let compiled = compiler.compile_expr(&lam);
    let rendered = print_block(&compiled.prelude);

    assert!(
        rendered.contains("function even(n)"),
        "expected the first recursive function to lower directly:\n{rendered}"
    );
    assert!(
        rendered.contains("function odd(n)"),
        "expected the second recursive function to lower directly:\n{rendered}"
    );
    assert!(
        !rendered.contains("let even;") && !rendered.contains("let odd;"),
        "unexpected recursive placeholders remained:\n{rendered}"
    );
}

#[test]
fn recursive_singleton_nested_let_function_bindings_avoid_placeholder_assignments() {
    let mut compiler = LambdaCompiler::new();
    let make = Ident::create_local("make");
    let make_internal = Ident::create_local("make$Internal");
    let make_alias = Ident::create_local("make$1");
    let component = Ident::create_local("Recursive_react_component");
    let param = Ident::create_local("param");
    let props = Ident::create_local("props");
    let lam = Lambda::letrec(
        vec![(
            make.clone(),
            Lambda::let_(
                LetKind::Strict,
                make_internal.clone(),
                Lambda::prim(
                    Primitive::PjsFnMake(1),
                    vec![Lambda::function_(
                        1,
                        vec![param],
                        Lambda::var(make.clone()),
                        FunctionAttribute::default(),
                    )],
                    Location::none(),
                ),
                Lambda::let_(
                    LetKind::Strict,
                    make_alias.clone(),
                    Lambda::let_(
                        LetKind::Strict,
                        component.clone(),
                        Lambda::prim(
                            Primitive::PjsFnMake(1),
                            vec![Lambda::function_(
                                1,
                                vec![props.clone()],
                                Lambda::apply(
                                    Lambda::var(make_internal.clone()),
                                    vec![Lambda::var(props)],
                                    ApInfo {
                                        loc: Location::none(),
                                        inlined: InlineAttribute::Default,
                                        status: ApplyStatus::Na,
                                    },
                                    false,
                                ),
                                FunctionAttribute::default(),
                            )],
                            Location::none(),
                        ),
                        Lambda::var(component),
                    ),
                    Lambda::var(make_alias),
                ),
            ),
        )],
        Lambda::unit(),
    );

    let compiled = compiler.compile_expr(&lam);
    let rendered = print_block(&compiled.prelude);
    let make_decl = compiled.prelude.iter().find_map(|stmt| match &stmt.desc {
        StatementDesc::Variable(VariableDeclaration { ident, value, .. })
            if ident.same(&make) =>
        {
            Some(value)
        }
        _ => None,
    });

    assert!(
        matches!(make_decl, Some(Some(_))),
        "expected the recursive wrapper binding to produce an initialized declaration:\n{rendered}"
    );
    assert!(
        !rendered.contains("let make;"),
        "unexpected recursive placeholder declaration remained:\n{rendered}"
    );
}

#[test]
fn recursive_self_referential_record_bindings_lower_to_dummy_object_updates_like_ocaml() {
    let mut compiler = LambdaCompiler::new();
    let xx = Ident::create_local("xx");
    let lam = Lambda::letrec(
        vec![(
            xx.clone(),
            Lambda::prim(
                Primitive::Pmakeblock(
                    0,
                    TagInfo::record(
                        vec![("xx".to_string(), false)],
                        crate::parser::ast::MutableFlag::Immutable,
                    ),
                    Mutable::Immutable,
                ),
                vec![Lambda::var(xx.clone())],
                Location::none(),
            ),
        )],
        Lambda::unit(),
    );

    let compiled = compiler.compile_expr(&lam);
    let [declare, assign] = compiled.prelude.as_slice() else {
        panic!("expected a dummy-object declaration followed by a field update");
    };

    let StatementDesc::Variable(VariableDeclaration {
        ident,
        value:
            Some(Expression {
                desc: ExpressionDesc::Object(None, props),
                ..
            }),
        property: LetKind::Variable,
        ..
    }) = &declare.desc
    else {
        panic!("expected an initialized dummy-object declaration");
    };
    assert!(ident.same(&xx));
    assert!(props.is_empty(), "expected an empty dummy object");

    let StatementDesc::Exp(Expression {
        desc: ExpressionDesc::Bin(BinOp::Eq, left, right),
        ..
    }) = &assign.desc
    else {
        panic!("expected the recursive record field assignment");
    };
    assert!(matches!(
        left.as_ref(),
        Expression {
            desc: ExpressionDesc::StaticIndex(target, field, None),
            ..
        } if field == "xx"
            && matches!(
                target.as_ref(),
                Expression {
                    desc: ExpressionDesc::Var(VIdent::Id(id)),
                    ..
                } if id.same(&xx)
            )
    ));
    assert!(matches!(
        right.as_ref(),
        Expression {
            desc: ExpressionDesc::Var(VIdent::Id(id)),
            ..
        } if id.same(&xx)
    ));
}

#[test]
fn acyclic_letrec_singletons_lower_like_lam_scc_plain_lets() {
    let mut compiler = LambdaCompiler::new();
    let a = Ident::create_local("a");
    let b = Ident::create_local("b");
    let lam = Lambda::letrec(
        vec![
            (
                a.clone(),
                Lambda::prim(
                    Primitive::Pmakeblock(
                        0,
                        TagInfo::record(
                            vec![("inner".to_string(), false)],
                            crate::parser::ast::MutableFlag::Immutable,
                        ),
                        Mutable::Immutable,
                    ),
                    vec![Lambda::prim(
                        Primitive::Pmakeblock(
                            0,
                            TagInfo::record(
                                vec![("value".to_string(), false)],
                                crate::parser::ast::MutableFlag::Immutable,
                            ),
                            Mutable::Immutable,
                        ),
                        vec![Lambda::const_(Constant::int(1))],
                        Location::none(),
                    )],
                    Location::none(),
                ),
            ),
            (
                b.clone(),
                Lambda::prim(
                    Primitive::Pmakeblock(
                        0,
                        TagInfo::record(
                            vec![("next".to_string(), false)],
                            crate::parser::ast::MutableFlag::Immutable,
                        ),
                        Mutable::Immutable,
                    ),
                    vec![Lambda::var(a.clone())],
                    Location::none(),
                ),
            ),
        ],
        Lambda::unit(),
    );

    let rendered = print_block(&compiler.compile_expr(&lam).prelude);

    assert!(
        rendered.contains("let a = {"),
        "expected the non-recursive singleton to lower as a plain let:\n{rendered}"
    );
    assert!(
        rendered.contains("let b = {"),
        "expected the dependent singleton to lower as a plain let:\n{rendered}"
    );
    assert!(
        !rendered.contains("let a;") && !rendered.contains("let b;"),
        "unexpected recursive placeholder declaration remained:\n{rendered}"
    );
    assert!(
        !rendered.contains("Primitive_object.updateDummy"),
        "acyclic singletons should not go through dummy-object updates:\n{rendered}"
    );
}

#[test]
fn mutually_recursive_record_bindings_lower_to_runtime_update_dummy_calls() {
    let mut compiler = LambdaCompiler::new();
    let a = Ident::create_local("a");
    let b = Ident::create_local("b");
    let lam = Lambda::letrec(
        vec![
            (
                a.clone(),
                Lambda::prim(
                    Primitive::Pmakeblock(
                        0,
                        TagInfo::record(
                            vec![("b".to_string(), false)],
                            crate::parser::ast::MutableFlag::Immutable,
                        ),
                        Mutable::Immutable,
                    ),
                    vec![Lambda::var(b.clone())],
                    Location::none(),
                ),
            ),
            (
                b.clone(),
                Lambda::prim(
                    Primitive::Pmakeblock(
                        0,
                        TagInfo::record(
                            vec![("a".to_string(), false)],
                            crate::parser::ast::MutableFlag::Immutable,
                        ),
                        Mutable::Immutable,
                    ),
                    vec![Lambda::var(a.clone())],
                    Location::none(),
                ),
            ),
        ],
        Lambda::unit(),
    );

    let rendered = print_block(&compiler.compile_expr(&lam).prelude);

    assert!(
        rendered.contains("let a = {};") && rendered.contains("let b = {};"),
        "expected dummy-object declarations for mutually recursive records:\n{rendered}"
    );
    assert!(
        rendered.contains("Primitive_object.updateDummy(a, {")
            && rendered.contains("Primitive_object.updateDummy(b, {"),
        "expected runtime dummy-object updates for mutually recursive records:\n{rendered}"
    );
    assert!(
        !rendered.contains("let a;") && !rendered.contains("let b;"),
        "unexpected placeholder assignments remained:\n{rendered}"
    );
}

#[test]
fn recursive_self_tailcalls_lower_to_looping_while_bodies() {
    let mut compiler = LambdaCompiler::new();
    let loop_ = Ident::create_local("loop");
    let flag = Ident::create_local("flag");
    let acc = Ident::create_local("acc");
    let next = Ident::create_local("next");
    let tailcall = Lambda::Lapply(Apply {
        ap_func: Box::new(Lambda::var(loop_.clone())),
        ap_args: vec![
            Lambda::const_(Constant::JsFalse),
            Lambda::var(next.clone()),
            Lambda::var(next.clone()),
        ],
        ap_info: ApInfo {
            loc: Location::none(),
            inlined: InlineAttribute::Default,
            status: ApplyStatus::Na,
        },
        ap_transformed_jsx: false,
    });
    let lam = Lambda::letrec(
        vec![(
            loop_.clone(),
            Lambda::function_(
                3,
                vec![flag.clone(), acc.clone(), next],
                Lambda::if_(Lambda::var(flag), tailcall, Lambda::var(acc)),
                FunctionAttribute::default(),
            ),
        )],
        Lambda::unit(),
    );

    let compiled = compiler.compile_expr(&lam);
    let rendered = print_block(&compiled.prelude);

    assert!(
        rendered.contains("while (true)"),
        "expected recursive self-tailcall lowering to emit a loop:\n{rendered}"
    );
    assert!(
        rendered.contains("continue;"),
        "expected recursive self-tailcall lowering to continue the loop:\n{rendered}"
    );
    assert!(
        !rendered.contains("return loop("),
        "unexpected recursive return call remained:\n{rendered}"
    );
}

#[test]
fn recursive_self_tailcalls_lower_sequands_to_looping_while_bodies() {
    let mut compiler = LambdaCompiler::new();
    let loop_ = Ident::create_local("loop");
    let flag = Ident::create_local("flag");
    let tailcall = Lambda::Lapply(Apply {
        ap_func: Box::new(Lambda::var(loop_.clone())),
        ap_args: vec![Lambda::const_(Constant::JsFalse)],
        ap_info: ApInfo {
            loc: Location::none(),
            inlined: InlineAttribute::Default,
            status: ApplyStatus::Na,
        },
        ap_transformed_jsx: false,
    });
    let lam = Lambda::letrec(
        vec![(
            loop_.clone(),
            Lambda::function_(
                1,
                vec![flag.clone()],
                Lambda::prim(
                    Primitive::Psequand,
                    vec![Lambda::var(flag), tailcall],
                    Location::none(),
                ),
                FunctionAttribute::default(),
            ),
        )],
        Lambda::unit(),
    );

    let compiled = compiler.compile_expr(&lam);
    let rendered = print_block(&compiled.prelude);

    assert!(
        rendered.contains("while (true)"),
        "expected recursive sequand lowering to emit a loop:\n{rendered}"
    );
    assert!(
        rendered.contains("continue;"),
        "expected recursive sequand lowering to continue the loop:\n{rendered}"
    );
    assert!(
        !rendered.contains("return loop("),
        "unexpected recursive return call remained:\n{rendered}"
    );
}

#[test]
fn recursive_self_tailcalls_lower_sequors_to_looping_while_bodies() {
    let mut compiler = LambdaCompiler::new();
    let loop_ = Ident::create_local("loop");
    let flag = Ident::create_local("flag");
    let tailcall = Lambda::Lapply(Apply {
        ap_func: Box::new(Lambda::var(loop_.clone())),
        ap_args: vec![Lambda::const_(Constant::JsFalse)],
        ap_info: ApInfo {
            loc: Location::none(),
            inlined: InlineAttribute::Default,
            status: ApplyStatus::Na,
        },
        ap_transformed_jsx: false,
    });
    let lam = Lambda::letrec(
        vec![(
            loop_.clone(),
            Lambda::function_(
                1,
                vec![flag.clone()],
                Lambda::prim(
                    Primitive::Psequor,
                    vec![Lambda::var(flag), tailcall],
                    Location::none(),
                ),
                FunctionAttribute::default(),
            ),
        )],
        Lambda::unit(),
    );

    let compiled = compiler.compile_expr(&lam);
    let rendered = print_block(&compiled.prelude);

    assert!(
        rendered.contains("while (true)"),
        "expected recursive sequor lowering to emit a loop:\n{rendered}"
    );
    assert!(
        rendered.contains("continue;"),
        "expected recursive sequor lowering to continue the loop:\n{rendered}"
    );
    assert!(
        !rendered.contains("return loop("),
        "unexpected recursive return call remained:\n{rendered}"
    );
}

#[test]
fn recursive_self_tailcalls_rename_params_before_loop_assignments() {
    let mut compiler = LambdaCompiler::new();
    let loop_ = Ident::create_local("loop");
    let a = Ident::create_local("a");
    let b = Ident::create_local("b");
    let flag = Ident::create_local("flag");
    let tailcall = Lambda::Lapply(Apply {
        ap_func: Box::new(Lambda::var(loop_.clone())),
        ap_args: vec![
            Lambda::var(b.clone()),
            Lambda::var(a.clone()),
            Lambda::const_(Constant::JsFalse),
        ],
        ap_info: ApInfo {
            loc: Location::none(),
            inlined: InlineAttribute::Default,
            status: ApplyStatus::Na,
        },
        ap_transformed_jsx: false,
    });
    let lam = Lambda::letrec(
        vec![(
            loop_.clone(),
            Lambda::function_(
                3,
                vec![a.clone(), b.clone(), flag.clone()],
                Lambda::if_(Lambda::var(flag), tailcall, Lambda::var(a)),
                FunctionAttribute::default(),
            ),
        )],
        Lambda::unit(),
    );

    let compiled = compiler.compile_expr(&lam);
    let rendered = print_block(&compiled.prelude);

    assert!(
        rendered.contains("function loop(_a, _b, _flag)"),
        "expected loop parameters to be renamed before tailcall assignments:\n{rendered}"
    );
    assert!(
        rendered.contains("let a = _a;")
            && rendered.contains("let b = _b;")
            && rendered.contains("let flag = _flag;"),
        "expected original parameter aliases inside the loop body:\n{rendered}"
    );
    assert!(
        rendered.contains("_a = b;")
            && rendered.contains("_b = a;")
            && rendered.contains("_flag = false;"),
        "expected assignments to target renamed loop params:\n{rendered}"
    );
}

#[test]
fn recursive_self_tailcalls_preserve_ocaml_loop_ordering() {
    let mut compiler = LambdaCompiler::new();
    let f = Ident::create_local("f");
    let n = Ident::create_local("n");
    let acc = Ident::create_local("acc");
    let body = Lambda::if_(
        Lambda::var(n.clone()),
        Lambda::Lapply(Apply {
            ap_func: Box::new(Lambda::var(f.clone())),
            ap_args: vec![
                Lambda::prim(
                    Primitive::Psubint,
                    vec![Lambda::var(n.clone()), Lambda::const_(Constant::int(1))],
                    Location::none(),
                ),
                Lambda::function_(
                    1,
                    vec![Ident::create_local("param")],
                    Lambda::var(acc.clone()),
                    FunctionAttribute::default(),
                ),
            ],
            ap_info: ApInfo {
                loc: Location::none(),
                inlined: InlineAttribute::Default,
                status: ApplyStatus::Na,
            },
            ap_transformed_jsx: false,
        }),
        Lambda::var(acc.clone()),
    );
    let lam = Lambda::letrec(
        vec![(
            f.clone(),
            Lambda::function_(
                2,
                vec![n.clone(), acc.clone()],
                body,
                FunctionAttribute::default(),
            ),
        )],
        Lambda::unit(),
    );

    let compiled = compiler.compile_expr(&lam);
    let rendered = print_block(&compiled.prelude);
    let alias_start = rendered
        .find("let acc = _acc;")
        .expect("expected acc alias in loop body");
    let alias_next = rendered
        .find("let n = _n;")
        .expect("expected n alias in loop body");
    let assign_start = rendered
        .find("_acc =")
        .expect("expected acc reassignment in loop body");
    let assign_next = rendered
        .find("_n =")
        .expect("expected n reassignment in loop body");

    assert!(
        alias_start < alias_next,
        "expected acc alias before n alias:\n{rendered}"
    );
    assert!(
        assign_start < assign_next,
        "expected acc reassignment before n reassignment:\n{rendered}"
    );
}

#[test]
fn recursive_wrapped_js_fn_make_bindings_lower_to_looping_while_bodies() {
    let mut compiler = LambdaCompiler::new();
    let loop_ = Ident::create_local("loop");
    let flag = Ident::create_local("flag");
    let acc = Ident::create_local("acc");
    let next = Ident::create_local("next");
    let tailcall = Lambda::Lapply(Apply {
        ap_func: Box::new(Lambda::var(loop_.clone())),
        ap_args: vec![
            Lambda::const_(Constant::JsFalse),
            Lambda::var(next.clone()),
            Lambda::var(next.clone()),
        ],
        ap_info: ApInfo {
            loc: Location::none(),
            inlined: InlineAttribute::Default,
            status: ApplyStatus::Na,
        },
        ap_transformed_jsx: false,
    });
    let lam = Lambda::letrec(
        vec![(
            loop_.clone(),
            Lambda::prim(
                Primitive::PjsFnMake(3),
                vec![Lambda::function_(
                    3,
                    vec![flag.clone(), acc.clone(), next],
                    Lambda::if_(Lambda::var(flag), tailcall, Lambda::var(acc)),
                    FunctionAttribute::default(),
                )],
                Location::none(),
            ),
        )],
        Lambda::var(loop_.clone()),
    );

    let simplified = crate::lambda::simplify::simplify_for_js_backend(&lam);
    let compiled = compiler.compile_expr(&simplified);
    let rendered = if compiled.prelude.is_empty() {
        print_expression(&compiled.expr)
    } else {
        print_block(&compiled.prelude)
    };

    assert!(
        rendered.contains("while (true)"),
        "expected wrapped recursive self-tailcall lowering to emit a loop:\n{rendered}"
    );
    assert!(
        rendered.contains("continue;"),
        "expected wrapped recursive self-tailcall lowering to continue the loop:\n{rendered}"
    );
    assert!(
        !rendered.contains("return loop("),
        "unexpected wrapped recursive return call remained:\n{rendered}"
    );
}

#[test]
fn recursive_named_variant_block_cases_reenter_tail_loops() {
    let mut compiler = LambdaCompiler::new();
    let loop_ = Ident::create_local("loop");
    let value = Ident::create_local("value");
    let tailcall = Lambda::Lapply(Apply {
        ap_func: Box::new(Lambda::var(loop_.clone())),
        ap_args: vec![Lambda::var(value.clone())],
        ap_info: ApInfo {
            loc: Location::none(),
            inlined: InlineAttribute::Default,
            status: ApplyStatus::Na,
        },
        ap_transformed_jsx: false,
    });
    let body = Lambda::Lswitch(
        Box::new(Lambda::var(value.clone())),
        LambdaSwitch {
            sw_consts_full: true,
            sw_consts: vec![(0, Lambda::const_(Constant::int(0)))],
            sw_blocks_full: true,
            sw_blocks: vec![(0, tailcall)],
            sw_failaction: None,
            sw_names: Some(SwitchNames {
                consts: vec![SwitchTag::named("Empty")],
                blocks: vec![SwitchBlock::named("Node")],
            }),
        },
    );
    let lam = Lambda::letrec(
        vec![(
            loop_.clone(),
            Lambda::function_(1, vec![value], body, FunctionAttribute::default()),
        )],
        Lambda::unit(),
    );

    let compiled = compiler.compile_expr(&lam);
    let rendered = print_block(&compiled.prelude);

    assert!(
        rendered.contains("while (true)"),
        "expected named-variant tail recursion to lower to a loop:\n{rendered}"
    );
    assert!(
        rendered.contains("continue;"),
        "expected the block case to continue the loop instead of returning recursively:\n{rendered}"
    );
    assert!(
        !rendered.contains("return loop("),
        "unexpected recursive call remained in named-variant switch lowering:\n{rendered}"
    );
}

#[test]
fn recursive_function_aliases_reenter_the_same_tail_loop_like_a_scope_bug() {
    let mut compiler = LambdaCompiler::new();
    let odd = Ident::create_local("odd");
    let even = Ident::create_local("even");
    let z = Ident::create_local("z");
    let y = Ident::create_local("y");
    let lam = Lambda::letrec(
        vec![
            (
                odd.clone(),
                Lambda::prim(
                    Primitive::PjsFnMake(1),
                    vec![Lambda::function_(
                        1,
                        vec![z],
                        Lambda::Lapply(Apply {
                            ap_func: Box::new(Lambda::var(even.clone())),
                            ap_args: vec![Lambda::const_(Constant::int(32))],
                            ap_info: ApInfo {
                                loc: Location::none(),
                                inlined: InlineAttribute::Default,
                                status: ApplyStatus::Na,
                            },
                            ap_transformed_jsx: false,
                        }),
                        FunctionAttribute::default(),
                    )],
                    Location::none(),
                ),
            ),
            (
                even.clone(),
                Lambda::prim(
                    Primitive::PjsFnMake(1),
                    vec![Lambda::function_(
                        1,
                        vec![y.clone()],
                        Lambda::Lapply(Apply {
                            ap_func: Box::new(Lambda::var(odd.clone())),
                            ap_args: vec![Lambda::var(y)],
                            ap_info: ApInfo {
                                loc: Location::none(),
                                inlined: InlineAttribute::Default,
                                status: ApplyStatus::Na,
                            },
                            ap_transformed_jsx: false,
                        }),
                        FunctionAttribute::default(),
                    )],
                    Location::none(),
                ),
            ),
        ],
        Lambda::var(odd.clone()),
    );

    let simplified = crate::lambda::simplify::simplify_for_js_backend(&lam);
    let Lambda::Lletrec(bindings, _) = &simplified else {
        panic!("expected simplified alias test to stay a letrec, got {simplified:?}");
    };
    let tail_targets = direct_recursive_function_tail_targets(bindings);
    let odd_targets = tail_targets
        .get(&odd)
        .cloned()
        .unwrap_or_else(|| panic!("expected tail targets for odd, got {tail_targets:?}"));
    assert!(
        odd_targets.iter().any(|target| target.same(&odd))
            && odd_targets.iter().any(|target| target.same(&even)),
        "expected odd tail targets to include the same-group alias, got {odd_targets:?}\nsimplified:\n{}",
        crate::lambda::print::lambda_to_string(&simplified)
    );
    let compiled = compiler.compile_expr(&simplified);
    let rendered = if compiled.prelude.is_empty() {
        print_expression(&compiled.expr)
    } else {
        print_block(&compiled.prelude)
    };

    assert!(
        rendered.contains("while (true)"),
        "expected same-group function aliases to lower through the tail loop:\n{rendered}"
    );
    assert!(
        rendered.contains("let even = odd;"),
        "expected the recursive alias binding to collapse to a direct alias:\n{rendered}"
    );
    assert!(
        !rendered.contains("return even("),
        "unexpected recursive alias call remained in the emitted JS:\n{rendered}"
    );
}
