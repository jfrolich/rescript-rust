pub(super) use super::test_support::*;
use super::*;
pub(super) use crate::cmi::persistent_env::PersistentEnv;
pub(super) use crate::js_ir::op::{ImportAttributes as JsImportAttributes, PropertyName};
pub(super) use crate::js_ir::{
    ModulePathResolver, print_block, print_deps_program, print_deps_program_with_directives,
    print_expression,
};
pub(super) use crate::lambda::LamLoc;
pub(super) use crate::lambda::LambdaSwitch;
pub(super) use crate::lambda::js_exp_make::{int32_band, int32_bxor, int32_mul, ocaml_typeof_expr};
pub(super) use crate::lambda::lam_coercion::resolve_export_aliases;
pub(super) use crate::lambda::lam_compile_external::external_module_import_attributes;
pub(super) use crate::lambda::lam_constant::{
    Constant, ConstructorRuntimeTag, ConstructorTag, PointerInfo,
};
pub(super) use crate::lambda::lam_primitive::{
    Attr, Cst, DeclKind, ExternalDecl, ExternalModuleName, ImportSource, JsRawInfo, Label,
    LabelNoname, ModuleBindName, ModuleSource, Mutable, ObjParam, Param, Primitive,
};
pub(super) use crate::lambda::{
    ApInfo, Apply, ApplyStatus, Comparison, FieldDbgInfo, FunctionAttribute, Lambda,
};
use std::fs;
pub(super) use std::path::PathBuf;
pub(super) use tempfile::tempdir;

pub(super) fn write_ast_source_stub(ast_path: &std::path::Path, source_path: &std::path::Path) {
    let mut bytes = Vec::new();
    bytes.extend_from_slice(&0u32.to_be_bytes());
    bytes.extend_from_slice(source_path.to_string_lossy().as_bytes());
    bytes.push(b'\n');
    fs::write(ast_path, bytes).expect("failed to write ast source stub");
}

fn repo_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("repo root")
        .to_path_buf()
}

/// Compiler options resolving against the checked-in test package and runtime.
fn test_compiler_options(repo_root: &std::path::Path) -> crate::driver::CompilerOptions {
    crate::driver::CompilerOptions {
        include_paths: vec![
            repo_root
                .join("tests")
                .join("tests")
                .join("lib")
                .join("ocaml"),
            repo_root
                .join("tests")
                .join("dependencies")
                .join("rescript-react")
                .join("lib")
                .join("ocaml"),
        ],
        runtime_path: Some(
            repo_root
                .join("node_modules")
                .join("@rescript")
                .join("runtime"),
        ),
        ..crate::driver::CompilerOptions::default()
    }
}

/// Run `f` on a thread with a 32 MiB stack, as deep fixtures need it.
fn on_big_stack<T: Send + 'static>(name: String, f: impl FnOnce() -> T + Send + 'static) -> T {
    std::thread::Builder::new()
        .name(name)
        .stack_size(32 * 1024 * 1024)
        .spawn(f)
        .expect("failed to spawn compiler test thread")
        .join()
        .expect("compiler test thread panicked")
}

fn compile_checked_in_test_file_to_js_inner(module_name: &str) -> String {
    let repo_root = repo_root();
    let src_dir = repo_root.join("tests").join("tests").join("src");
    let source_path = src_dir.join(format!("{module_name}.res"));
    let output_path = src_dir.join(format!("{module_name}.mjs"));
    let options = crate::driver::CompilerOptions {
        source_filename: Some(source_path.to_string_lossy().into_owned()),
        output_path: Some(output_path),
        ..test_compiler_options(&repo_root)
    };

    crate::driver::compile_file_to_js_with_options(&source_path, &options)
        .unwrap_or_else(|err| panic!("failed to compile {module_name}.res: {err:#}"))
}

pub(super) fn compile_checked_in_test_file_to_js(module_name: &str) -> String {
    let module_name = module_name.to_string();
    on_big_stack(
        format!("compile_checked_in_test_file_to_js:{module_name}"),
        move || compile_checked_in_test_file_to_js_inner(&module_name),
    )
}

pub(super) fn compile_test_source_to_js(source: &str, filename: &str) -> anyhow::Result<String> {
    let source = source.to_string();
    let filename = filename.to_string();
    on_big_stack(format!("compile_test_source_to_js:{filename}"), move || {
        crate::driver::compile_source_to_js_with_options(
            &source,
            &filename,
            &test_compiler_options(&repo_root()),
        )
    })
}

pub(super) fn find_variable_initializer<'a>(
    block: &'a Block,
    ident: &Ident,
) -> Option<&'a Expression> {
    block.iter().find_map(|stmt| match &stmt.desc {
        StatementDesc::Variable(VariableDeclaration {
            ident: binding,
            value: Some(value),
            ..
        }) if binding.same(ident) => Some(value),
        _ => None,
    })
}

pub(super) fn external_module(bundle: &str) -> ExternalModuleName {
    ExternalModuleName {
        bundle: bundle.to_string(),
        module_bind_name: ModuleBindName::PhintNothing,
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
        module_bind_name: ModuleBindName::PhintName(hint.to_string()),
        import_attributes: Some(
            attrs
                .iter()
                .map(|(key, value)| (key.to_string(), value.to_string()))
                .collect(),
        ),
    }
}

fn js_var_external(name: &str, external_module_name: Option<ExternalModuleName>) -> Lambda {
    Lambda::prim(
        Primitive::PjsCall(Box::new(crate::lambda::lam_primitive::JsCall {
            prim_name: name.to_string(),
            arg_types: vec![],
            ffi: ExternalDecl {
                kind: DeclKind::DeclVal {
                    name: name.to_string(),
                },
                module_: external_module_name.map(ModuleSource::ModuleNamed),
                scopes: vec![],
                variadic: false,
                effective_arity: 0,
            },
        })),
        vec![],
        LamLoc::NONE,
    )
}

fn test_apply_info() -> ApInfo {
    ApInfo {
        loc: LamLoc::NONE,
        status: ApplyStatus::Na,
    }
}

fn test_function_calling(ident: Ident, target: &Ident) -> (Ident, Lambda) {
    let param = Ident::create_local("param");
    (
        ident,
        Lambda::function_(
            1,
            vec![param],
            Lambda::Lapply(Box::new(Apply {
                ap_func: Box::new(Lambda::var(*target)),
                ap_args: vec![],
                ap_info: test_apply_info(),
            })),
            FunctionAttribute::default(),
            LamLoc::NONE,
        ),
    )
}

fn test_apply(target: &Ident) -> Lambda {
    Lambda::Lapply(Box::new(Apply {
        ap_func: Box::new(Lambda::var(*target)),
        ap_args: vec![],
        ap_info: test_apply_info(),
    }))
}

fn test_function_calling_two(ident: Ident, first: &Ident, second: &Ident) -> (Ident, Lambda) {
    let param = Ident::create_local("param");
    (
        ident,
        Lambda::function_(
            1,
            vec![param],
            Lambda::seq(test_apply(first), test_apply(second)),
            FunctionAttribute::default(),
            LamLoc::NONE,
        ),
    )
}

fn test_unit_function(ident: Ident) -> (Ident, Lambda) {
    let param = Ident::create_local("param");
    (
        ident,
        Lambda::function_(
            1,
            vec![param],
            Lambda::const_(Constant::JsUndefined { is_unit: true }),
            FunctionAttribute::default(),
            LamLoc::NONE,
        ),
    )
}

fn console_log_effect(arg: Lambda) -> Lambda {
    Lambda::seq(
        Lambda::prim(
            Primitive::PjsCall(Box::new(crate::lambda::lam_primitive::JsCall {
                prim_name: "console.log".to_string(),
                arg_types: vec![],
                ffi: crate::lambda::lam_primitive::ExternalDecl::test_val("", 0),
            })),
            vec![arg],
            LamLoc::NONE,
        ),
        Lambda::const_(Constant::JsUndefined { is_unit: true }),
    )
}

pub(super) fn import_attributes_lowered_lambda() -> Lambda {
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
        include_json,
        Lambda::prim(
            Primitive::Pmakeblock(
                TagInfo::Module(vec!["myJson".to_string()]),
                Mutable::Immutable,
            ),
            vec![js_var_external("default", Some(json_module))],
            LamLoc::NONE,
        ),
        Lambda::let_(
            LetKind::Alias,
            my_json,
            Lambda::prim(
                Primitive::Pfield(
                    0,
                    FieldDbgInfo::Module {
                        name: "myJson".to_string(),
                    },
                ),
                vec![Lambda::var(include_json)],
                LamLoc::NONE,
            ),
            Lambda::seq(
                console_log_effect(Lambda::var(my_json)),
                Lambda::let_(
                    LetKind::Strict,
                    include_css,
                    Lambda::prim(
                        Primitive::Pmakeblock(
                            TagInfo::Module(vec!["buttonCss".to_string()]),
                            Mutable::Immutable,
                        ),
                        vec![js_var_external("button", Some(css_module))],
                        LamLoc::NONE,
                    ),
                    Lambda::let_(
                        LetKind::Alias,
                        button_css,
                        Lambda::prim(
                            Primitive::Pfield(
                                0,
                                FieldDbgInfo::Module {
                                    name: "buttonCss".to_string(),
                                },
                            ),
                            vec![Lambda::var(include_css)],
                            LamLoc::NONE,
                        ),
                        Lambda::seq(
                            console_log_effect(Lambda::var(button_css)),
                            Lambda::prim(
                                Primitive::Pmakeblock(
                                    TagInfo::ModuleExport(vec![my_json, button_css]),
                                    Mutable::Immutable,
                                ),
                                vec![Lambda::var(my_json), Lambda::var(button_css)],
                                LamLoc::NONE,
                            ),
                        ),
                    ),
                ),
            ),
        ),
    )
}

pub(super) fn assert_import_attributes_alias_block_shape(block: &Block, stage: &str) {
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

pub(super) fn resolver_with_checked_in_cmj() -> ModulePathResolver {
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
    let mut belt_constants = ahash::AHashMap::new();
    belt_constants.insert(
        "empty".to_string(),
        crate::cmi::persistent_env::CmjExportConstant::Undefined { is_unit: false },
    );
    persistent_env.register_in_memory_module(
        "Belt_MapString",
        crate::cmi::persistent_env::InMemoryModuleInfo::new(
            PathBuf::from("Belt_MapString.res"),
            true,
            belt_constants,
            false,
        ),
    );
    ModulePathResolver::from_compile_options(
        None,
        Some(std::path::Path::new("/tmp/Effect.mjs")),
        None,
        None,
        None,
        Some(persistent_env),
        false,
    )
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
        LamLoc::NONE,
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
        comment: Some(Box::new(PointerInfo::Constructor(ConstructorTag {
            name: "NoParam".to_string(),
            const_: 1,
            non_const: 2,
            runtime_tag: None,
        }))),
    });

    assert!(matches!(
        compiled,
        Expression {
            desc: ExpressionDesc::Str(ref txt),
            ..
        } if txt == "NoParam"
    ));
}

#[test]
fn compile_constant_constructor_runtime_tag_uses_runtime_literal() {
    let compiled = LambdaCompiler::compile_constant(&Constant::Int {
        i: 0,
        comment: Some(Box::new(PointerInfo::Constructor(ConstructorTag {
            name: "Three".to_string(),
            const_: 1,
            non_const: 0,
            runtime_tag: Some(ConstructorRuntimeTag::String("three".to_string())),
        }))),
    });

    assert!(matches!(
        compiled,
        Expression {
            desc: ExpressionDesc::Str(ref txt),
            ..
        } if txt == "three"
    ));
}

#[test]
fn compile_constant_empty_list_keeps_numeric_zero_with_pointer_comment() {
    let compiled = LambdaCompiler::compile_constant(&Constant::Int {
        i: 0,
        comment: Some(Box::new(PointerInfo::Constructor(ConstructorTag {
            name: "[]".to_string(),
            const_: 1,
            non_const: 1,
            runtime_tag: None,
        }))),
    });

    assert!(matches!(
        compiled,
        Expression {
            desc: ExpressionDesc::Number(Number::Int { i: 0, .. }),
            comment: Some(ref comment),
            ..
        }
        if **comment == "[]"
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
fn compile_constant_escapes_semantic_strings() {
    // lam_compile_const.ml: `Const_string s -> E.str s`, printed by
    // `Js_dump_string.pp_string`.
    let compiled = LambdaCompiler::compile_constant(&Constant::String("\\\"".to_string()));

    assert!(matches!(
        compiled,
        Expression {
            desc: ExpressionDesc::Str(ref txt),
            ..
        } if txt == "\\\""
    ));
    assert_eq!(print_expression(&compiled), "\"\\\\\\\"\"");
}

#[test]
fn switch_case_expr_escapes_string_tags() {
    // js_exp_make.ml `tag_type`: `String s -> str s`.
    let compiled = LambdaCompiler::switch_case_expr(&SwitchCaseTag::String("\\\"".to_string()));

    assert!(matches!(
        compiled,
        Expression {
            desc: ExpressionDesc::Str(ref txt),
            ..
        } if txt == "\\\""
    ));
    assert_eq!(print_expression(&compiled), "\"\\\\\\\"\"");
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
    let compiled = compiler.compile_expr_tree(&Lambda::prim(
        Primitive::Ppowfloat,
        vec![
            Lambda::const_(Constant::float("2.")),
            Lambda::const_(Constant::float("3.")),
        ],
        LamLoc::NONE,
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
    let compiled = compiler.compile_expr_tree(&Lambda::prim(
        Primitive::Ppowint,
        vec![
            Lambda::const_(Constant::int(2)),
            Lambda::const_(Constant::int(2)),
        ],
        LamLoc::NONE,
    ));

    assert!(compiled.prelude.is_empty());
    assert_int_expr(&compiled.expr, 4);
}

#[test]
fn compile_int_pow_folds_overflowing_int_literals_like_ocaml_ext_int() {
    let mut compiler = LambdaCompiler::new();
    let compiled = compiler.compile_expr_tree(&Lambda::prim(
        Primitive::Ppowint,
        vec![
            Lambda::const_(Constant::int(2_147_483_647)),
            Lambda::const_(Constant::int(2)),
        ],
        LamLoc::NONE,
    ));

    assert!(compiled.prelude.is_empty());
    assert_int_expr(&compiled.expr, 0);
}

#[test]
fn compile_create_extension_uses_primitive_exceptions_create() {
    let mut compiler = LambdaCompiler::new();
    let compiled = compiler.compile_expr_tree(&Lambda::prim(
        Primitive::PcreateExtension("Local_exception_test.A".to_string()),
        vec![],
        LamLoc::NONE,
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
            desc: ExpressionDesc::Str(txt),
            ..
        }] if txt == "Local_exception_test.A"
    ));
    assert_eq!(
        compiled.expr.comment.as_deref().map(String::as_str),
        Some("@__PURE__")
    );
    assert_eq!(
        print_expression(&compiled.expr),
        "/* @__PURE__ */Primitive_exceptions.create(\"Local_exception_test.A\")"
    );
}

#[test]
fn compile_wrap_exn_uses_primitive_exceptions_internal_to_exception() {
    let mut compiler = LambdaCompiler::new();
    let exn = Ident::create_local("exn");
    let compiled = compiler.compile_expr_tree(&crate::raw_lambda::lower::wrap_exn(
        LamLoc::NONE,
        Lambda::var(exn),
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
fn compile_integer_inequality_preserves_typeof_string_comparison_like_ocaml() {
    let mut compiler = LambdaCompiler::new();
    let compiled = compiler.compile_expr_tree(&Lambda::prim(
        Primitive::Pintcomp(Comparison::Neq),
        vec![
            Lambda::prim(
                Primitive::Ptypeof,
                vec![Lambda::const_(Constant::int(3))],
                LamLoc::NONE,
            ),
            Lambda::const_(Constant::String("number".to_string())),
        ],
        LamLoc::NONE,
    ));

    assert!(compiled.prelude.is_empty());
    assert!(matches!(
        compiled.expr.desc,
        ExpressionDesc::Bin(BinOp::NotEqEq, _, _)
    ));
    assert_eq!(
        print_expression(&compiled.expr),
        "\"number\" !== \"number\""
    );
}

#[test]
fn compile_module_primitives_lower_to_primitive_module_runtime_calls_like_ocaml() {
    let mut compiler = LambdaCompiler::new();
    let loc = LamLoc::NONE;
    let init = compiler.compile_expr_tree(&Lambda::prim(
        Primitive::PinitMod,
        vec![
            Lambda::const_(Constant::int(1)),
            Lambda::var(Ident::create_local("shape")),
        ],
        loc,
    ));
    assert!(init.prelude.is_empty());
    assert_eq!(
        print_expression(&init.expr),
        "Primitive_module.init(1, shape)"
    );

    let update = compiler.compile_expr_tree(&Lambda::prim(
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
fn compile_int_order_uses_primitive_int_compare() {
    let mut compiler = LambdaCompiler::new();
    let left = Ident::create_local("left");
    let right = Ident::create_local("right");
    let compiled = compiler.compile_expr_tree(&Lambda::prim(
        Primitive::Pintorder,
        vec![Lambda::var(left), Lambda::var(right)],
        LamLoc::NONE,
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
    let compiled = compiler.compile_expr_tree(&Lambda::prim(
        Primitive::Pdivint,
        vec![Lambda::var(left), Lambda::const_(Constant::int(0))],
        LamLoc::NONE,
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
    let compiled = compiler.compile_expr_tree(&Lambda::prim(
        Primitive::Pmodint,
        vec![Lambda::var(left), Lambda::const_(Constant::int(0))],
        LamLoc::NONE,
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
    let compiled = compiler.compile_expr_tree(&Lambda::prim(
        Primitive::Pdivbigint,
        vec![
            Lambda::var(left),
            Lambda::const_(Constant::bigint(false, "0")),
        ],
        LamLoc::NONE,
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
    let compiled = compiler.compile_expr_tree(&Lambda::prim(
        Primitive::Pmodbigint,
        vec![
            Lambda::var(left),
            Lambda::const_(Constant::bigint(false, "0")),
        ],
        LamLoc::NONE,
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
    let compiled = compiler.compile_expr_tree(&Lambda::prim(
        Primitive::Pstringorder,
        vec![Lambda::var(left), Lambda::var(right)],
        LamLoc::NONE,
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
    let compiled = compiler.compile_expr_tree(&Lambda::prim(
        Primitive::Parrayrefu,
        vec![Lambda::var(array), Lambda::var(index)],
        LamLoc::NONE,
    ));

    assert!(compiled.prelude.is_empty());
    assert_eq!(print_expression(&compiled.expr), "arr[i]");
}

#[test]
fn compile_arrayrefs_uses_primitive_array_get() {
    let mut compiler = LambdaCompiler::new();
    let array = Ident::create_local("arr");
    let index = Ident::create_local("i");
    let compiled = compiler.compile_expr_tree(&Lambda::prim(
        Primitive::Parrayrefs,
        vec![Lambda::var(array), Lambda::var(index)],
        LamLoc::NONE,
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
    let compiled = compiler.compile_expr_tree(&Lambda::prim(
        Primitive::Parraysetu,
        vec![Lambda::var(array), Lambda::var(index), Lambda::var(value)],
        LamLoc::NONE,
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
fn compile_string_refs_use_primitive_string_get_char() {
    let mut compiler = LambdaCompiler::new();
    let string = Ident::create_local("str");
    let index = Ident::create_local("i");
    let compiled = compiler.compile_expr_tree(&Lambda::prim(
        Primitive::Pstringrefs,
        vec![Lambda::var(string), Lambda::var(index)],
        LamLoc::NONE,
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
    let compiled = compiler.compile_expr_tree(&Lambda::prim(
        Primitive::Pobjcomp(Comparison::Eq),
        vec![Lambda::const_(Constant::JsNull), Lambda::var(value)],
        LamLoc::NONE,
    ));

    assert!(compiled.prelude.is_empty());
    assert_eq!(print_expression(&compiled.expr), "null === value");
}

#[test]
fn compile_obj_compare_null_against_number_literal_folds_false() {
    let mut compiler = LambdaCompiler::new();
    let compiled = compiler.compile_expr_tree(&Lambda::prim(
        Primitive::Pobjcomp(Comparison::Eq),
        vec![
            Lambda::const_(Constant::JsNull),
            Lambda::const_(Constant::int(5)),
        ],
        LamLoc::NONE,
    ));

    assert!(compiled.prelude.is_empty());
    assert_eq!(print_expression(&compiled.expr), "false");
}

#[test]
fn compile_obj_notequal_undefined_against_number_literal_folds_true() {
    let mut compiler = LambdaCompiler::new();
    let compiled = compiler.compile_expr_tree(&Lambda::prim(
        Primitive::Pobjcomp(Comparison::Neq),
        vec![
            Lambda::const_(Constant::JsUndefined { is_unit: false }),
            Lambda::const_(Constant::int(5)),
        ],
        LamLoc::NONE,
    ));

    assert!(compiled.prelude.is_empty());
    assert_eq!(print_expression(&compiled.expr), "true");
}

#[test]
fn compile_obj_order_uses_primitive_object_compare() {
    let mut compiler = LambdaCompiler::new();
    let left = Ident::create_local("left");
    let right = Ident::create_local("right");
    let compiled = compiler.compile_expr_tree(&Lambda::prim(
        Primitive::Pobjorder,
        vec![Lambda::var(left), Lambda::var(right)],
        LamLoc::NONE,
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
    let compiled = compiler.compile_expr_tree(&Lambda::function_(
        2,
        vec![left, right],
        Lambda::prim(
            Primitive::Pobjorder,
            vec![Lambda::var(left), Lambda::var(right)],
            LamLoc::NONE,
        ),
        Default::default(),
        LamLoc::NONE,
    ));

    assert!(compiled.prelude.is_empty());
    assert_eq!(print_expression(&compiled.expr), "Primitive_object.compare");
}

#[test]
fn compile_obj_tag_uses_caml_block_tag_access_like_ocaml() {
    let mut compiler = LambdaCompiler::new();
    let value = Ident::create_local("value");
    let compiled = compiler.compile_expr_tree(&Lambda::prim(
        Primitive::Pobjtag,
        vec![Lambda::var(value)],
        LamLoc::NONE,
    ));

    assert!(compiled.prelude.is_empty());
    assert_eq!(print_expression(&compiled.expr), "value.TAG");
}

#[test]
fn compile_eta_wrapped_float_compare_function_aliases_runtime_member() {
    let mut compiler = LambdaCompiler::new();
    let left = Ident::create_local("x");
    let right = Ident::create_local("y");
    let compiled = compiler.compile_expr_tree(&Lambda::function_(
        2,
        vec![left, right],
        Lambda::prim(
            Primitive::Pfloatorder,
            vec![Lambda::var(left), Lambda::var(right)],
            LamLoc::NONE,
        ),
        Default::default(),
        LamLoc::NONE,
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

    let compiled = compiler.compile_expr_tree(&Lambda::function_(
        1,
        vec![none],
        Lambda::Lapply(Box::new(Apply {
            ap_func: Box::new(Lambda::prim(
                Primitive::Pfield(
                    23,
                    FieldDbgInfo::Module {
                        name: "fromArray".to_string(),
                    },
                ),
                vec![Lambda::LglobalModule(belt_map)],
                LamLoc::NONE,
            )),
            ap_args: vec![Lambda::var(none), Lambda::var(icmp)],
            ap_info: ApInfo {
                loc: LamLoc::NONE,
                status: ApplyStatus::Uncurry,
            },
        })),
        Default::default(),
        LamLoc::NONE,
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

    let compiled = compiler.compile_expr_tree(&Lambda::function_(
        2,
        vec![a, b],
        Lambda::function_(
            1,
            vec![extra],
            Lambda::Lapply(Box::new(Apply {
                ap_func: Box::new(Lambda::prim(
                    Primitive::Pfield(
                        9,
                        FieldDbgInfo::Module {
                            name: "eq".to_string(),
                        },
                    ),
                    vec![Lambda::LglobalModule(belt_map)],
                    LamLoc::NONE,
                )),
                ap_args: vec![Lambda::var(a), Lambda::var(b), Lambda::var(extra)],
                ap_info: ApInfo {
                    loc: LamLoc::NONE,
                    status: ApplyStatus::Uncurry,
                },
            })),
            Default::default(),
            LamLoc::NONE,
        ),
        Default::default(),
        LamLoc::NONE,
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
    let loc = LamLoc::NONE;
    let starj_empty = Lambda::const_(Constant::String("".to_string()));

    let outer_value = Lambda::let_(
        LetKind::Strict,
        always_true,
        Lambda::true_(),
        Lambda::function_(
            1,
            vec![outer_fn_param],
            Lambda::let_(
                LetKind::Strict,
                also_true,
                Lambda::function_(
                    1,
                    vec![inner_true_param],
                    Lambda::true_(),
                    FunctionAttribute::default(),
                    LamLoc::NONE,
                ),
                Lambda::function_(
                    1,
                    vec![inner_zero_param],
                    Lambda::const_(Constant::int(0)),
                    FunctionAttribute::default(),
                    LamLoc::NONE,
                ),
            ),
            FunctionAttribute::default(),
            LamLoc::NONE,
        ),
    );
    let nested_call = Lambda::Lapply(Box::new(Apply {
        ap_func: Box::new(Lambda::Lapply(Box::new(Apply {
            ap_func: Box::new(outer_value),
            ap_args: vec![starj_empty.clone()],
            ap_info: ApInfo {
                loc: loc,
                status: ApplyStatus::Uncurry,
            },
        }))),
        ap_args: vec![starj_empty],
        ap_info: ApInfo {
            loc: loc,
            status: ApplyStatus::Uncurry,
        },
    }));
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

    let hash = compiler.compile_expr_tree(&Lambda::prim(
        Primitive::Phash,
        vec![
            Lambda::const_(Constant::int(10)),
            Lambda::const_(Constant::int(100)),
            Lambda::const_(Constant::int(0)),
            Lambda::var(x),
        ],
        LamLoc::NONE,
    ));
    assert!(hash.prelude.is_empty());
    assert_eq!(
        print_expression(&hash.expr),
        "Primitive_hash.hash(10, 100, 0, x)"
    );

    let hash_mix_int = compiler.compile_expr_tree(&Lambda::prim(
        Primitive::PhashMixint,
        vec![Lambda::var(seed), Lambda::var(value)],
        LamLoc::NONE,
    ));
    assert!(hash_mix_int.prelude.is_empty());
    assert_eq!(
        print_expression(&hash_mix_int.expr),
        "Primitive_hash.hash_mix_int(seed, value)"
    );

    let hash_mix_string = compiler.compile_expr_tree(&Lambda::prim(
        Primitive::PhashMixstring,
        vec![Lambda::var(seed), Lambda::var(value)],
        LamLoc::NONE,
    ));
    assert!(hash_mix_string.prelude.is_empty());
    assert_eq!(
        print_expression(&hash_mix_string.expr),
        "Primitive_hash.hash_mix_string(seed, value)"
    );

    let hash_final_mix = compiler.compile_expr_tree(&Lambda::prim(
        Primitive::PhashFinalmix,
        vec![Lambda::var(seed)],
        LamLoc::NONE,
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
    let compiled = compiler.compile_expr_tree(&Lambda::function_(
        4,
        vec![hash_limit, hash_count, hash_acc, value],
        Lambda::prim(
            Primitive::Phash,
            vec![
                Lambda::var(hash_limit),
                Lambda::var(hash_count),
                Lambda::var(hash_acc),
                Lambda::var(value),
            ],
            LamLoc::NONE,
        ),
        Default::default(),
        LamLoc::NONE,
    ));

    assert!(compiled.prelude.is_empty());
    assert_eq!(print_expression(&compiled.expr), "Primitive_hash.hash");
}

#[test]
fn compile_compare_against_zero_elides_runtime_compare_call_like_ocaml() {
    let mut compiler = LambdaCompiler::new();
    let left = Ident::create_local("x");
    let right = Ident::create_local("y");
    let compiled = compiler.compile_expr_tree(&Lambda::prim(
        Primitive::Pintcomp(Comparison::Gt),
        vec![
            Lambda::prim(
                Primitive::Pfloatorder,
                vec![Lambda::var(left), Lambda::var(right)],
                LamLoc::NONE,
            ),
            Lambda::const_(Constant::int(0)),
        ],
        LamLoc::NONE,
    ));

    assert!(compiled.prelude.is_empty());
    assert_eq!(print_expression(&compiled.expr), "x > y");
}

#[test]
fn compile_bigint_compare_against_zero_elides_runtime_compare_call_like_ocaml() {
    let mut compiler = LambdaCompiler::new();
    let compiled = compiler.compile_expr_tree(&Lambda::prim(
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
                LamLoc::NONE,
            ),
            Lambda::const_(Constant::int(0)),
        ],
        LamLoc::NONE,
    ));

    assert!(compiled.prelude.is_empty());
    assert_eq!(print_expression(&compiled.expr), "123n < 555555n");
}

#[test]
fn compile_bigint_literal_equality_folds_like_ocaml() {
    let mut compiler = LambdaCompiler::new();
    let compiled = compiler.compile_expr_tree(&Lambda::prim(
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
        LamLoc::NONE,
    ));

    assert!(compiled.prelude.is_empty());
    assert_eq!(print_expression(&compiled.expr), "true");
}

#[test]
fn compile_eta_wrapped_float_equality_stays_as_function() {
    let mut compiler = LambdaCompiler::new();
    let left = Ident::create_local("x");
    let right = Ident::create_local("y");
    let compiled = compiler.compile_expr_tree(&Lambda::function_(
        2,
        vec![left, right],
        Lambda::prim(
            Primitive::Pfloatcomp(Comparison::Eq),
            vec![Lambda::var(left), Lambda::var(right)],
            LamLoc::NONE,
        ),
        Default::default(),
        LamLoc::NONE,
    ));

    assert!(compiled.prelude.is_empty());
    assert!(matches!(compiled.expr.desc, ExpressionDesc::Fun { .. }));
}

#[test]
fn compile_bigint_min_literals_use_conditional_fast_path() {
    let mut compiler = LambdaCompiler::new();
    let compiled = compiler.compile_expr_tree(&Lambda::prim(
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
        LamLoc::NONE,
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

    let add = compiler.compile_expr_tree(&Lambda::prim(
        Primitive::Paddbigint,
        vec![lhs.clone(), rhs.clone()],
        LamLoc::NONE,
    ));
    assert!(add.prelude.is_empty());
    assert_eq!(print_expression(&add.expr), "9n + 1n");

    let pow = compiler.compile_expr_tree(&Lambda::prim(
        Primitive::Ppowbigint,
        vec![lhs.clone(), rhs.clone()],
        LamLoc::NONE,
    ));
    assert!(pow.prelude.is_empty());
    assert_eq!(print_expression(&pow.expr), "9n ** 1n");

    let neg = compiler.compile_expr_tree(&Lambda::prim(
        Primitive::Pnegbigint,
        vec![lhs],
        LamLoc::NONE,
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

    let land = compiler.compile_expr_tree(&Lambda::prim(
        Primitive::Pandbigint,
        vec![lhs.clone(), rhs.clone()],
        LamLoc::NONE,
    ));
    assert!(land.prelude.is_empty());
    assert_eq!(print_expression(&land.expr), "9n & 1n");

    let lsl = compiler.compile_expr_tree(&Lambda::prim(
        Primitive::Plslbigint,
        vec![lhs.clone(), rhs.clone()],
        LamLoc::NONE,
    ));
    assert!(lsl.prelude.is_empty());
    assert_eq!(print_expression(&lsl.expr), "(9n << 1n)");

    let lnot = compiler.compile_expr_tree(&Lambda::prim(
        Primitive::Pnotbigint,
        vec![lhs],
        LamLoc::NONE,
    ));
    assert!(lnot.prelude.is_empty());
    assert_eq!(print_expression(&lnot.expr), "~9n");
}

#[test]
fn compile_duprecord_lowers_to_object_spread_like_ocaml() {
    let mut compiler = LambdaCompiler::new();
    let source = Ident::create_local("source");
    let compiled = compiler.compile_expr_tree(&Lambda::prim(
        Primitive::Pduprecord,
        vec![Lambda::var(source)],
        LamLoc::NONE,
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
        source,
        Lambda::function_(
            1,
            vec![param],
            Lambda::var(param),
            crate::lambda::FunctionAttribute::default(),
            LamLoc::NONE,
        ),
        Lambda::let_(
            LetKind::Alias,
            rebound_export,
            Lambda::var(source),
            Lambda::prim(
                Primitive::Pmakeblock(
                    TagInfo::ModuleExport(vec![rebound_export]),
                    Mutable::Immutable,
                ),
                vec![Lambda::var(source)],
                LamLoc::NONE,
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
fn compile_deps_program_keeps_exported_call_result_before_rebound_constant_block_export() {
    let mut compiler = LambdaCompiler::new();
    let f = Ident::create_local("f");
    let v = Ident::create_local("v");
    let res = Ident::create_local("res");
    let param = Ident::create_local("v");
    let export_block = Lambda::prim(
        Primitive::Pmakeblock(TagInfo::ModuleExport(vec![v, res]), Mutable::Immutable),
        vec![Lambda::var(v), Lambda::var(res)],
        LamLoc::NONE,
    );
    let lam = Lambda::let_(
        LetKind::Strict,
        f,
        Lambda::function_(
            1,
            vec![param],
            Lambda::prim(
                Primitive::Pfield(
                    0,
                    crate::lambda::lam_compat::FieldDbgInfo::Record {
                        name: "x".to_string(),
                    },
                ),
                vec![Lambda::var(param)],
                LamLoc::NONE,
            ),
            FunctionAttribute::default(),
            LamLoc::NONE,
        ),
        Lambda::let_(
            LetKind::Strict,
            v,
            Lambda::const_(Constant::Block {
                tag_info: Box::new(TagInfo::record(
                    vec![
                        ("x".to_string(), false),
                        ("y".to_string(), false),
                        ("z".to_string(), false),
                    ],
                    crate::parser::ast::MutableFlag::Immutable,
                )),
                elements: vec![
                    Constant::int(3),
                    Constant::int(4),
                    Constant::JsUndefined { is_unit: false },
                ],
            }),
            Lambda::let_(
                LetKind::Strict,
                res,
                Lambda::Lapply(Box::new(Apply {
                    ap_func: Box::new(Lambda::var(f)),
                    ap_args: vec![Lambda::var(v)],
                    ap_info: ApInfo {
                        loc: LamLoc::NONE,
                        status: ApplyStatus::Uncurry,
                    },
                })),
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
        v_idx < res_idx,
        "expected the rebound block export before its reduced projected result like current OCaml:\n{rendered}"
    );
}

#[test]
fn compile_deps_program_rebinds_different_name_exports_after_effects() {
    let mut compiler = LambdaCompiler::new();
    let original_export = Ident::create_local("MyURL");
    let export_block = Lambda::prim(
        Primitive::Pmakeblock(
            TagInfo::ModuleExport(vec![original_export]),
            Mutable::Immutable,
        ),
        vec![Lambda::unit()],
        LamLoc::NONE,
    );
    let lam = Lambda::let_(
        LetKind::Alias,
        original_export,
        Lambda::unit(),
        Lambda::seq(
            Lambda::prim(Primitive::Pdebugger, vec![], LamLoc::NONE),
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
        panic!("expected the original placeholder to shake away and the rebound export to remain");
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
        Primitive::Pmakeblock(TagInfo::ModuleExport(vec![x, xx, foo]), Mutable::Immutable),
        vec![Lambda::var(x), Lambda::var(xx), Lambda::var(foo)],
        LamLoc::NONE,
    );
    let lam = Lambda::let_(
        LetKind::Strict,
        x,
        Lambda::const_(Constant::int(1)),
        Lambda::let_(
            LetKind::Strict,
            xx,
            Lambda::var(x),
            Lambda::let_(
                LetKind::Strict,
                foo,
                Lambda::function_(
                    1,
                    vec![param],
                    Lambda::var(param),
                    FunctionAttribute::default(),
                    LamLoc::NONE,
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
        Primitive::Pmakeblock(TagInfo::ModuleExport(vec![foo, s, bar]), Mutable::Immutable),
        vec![Lambda::var(foo), Lambda::var(s), Lambda::var(bar)],
        LamLoc::NONE,
    );
    let lam = Lambda::let_(
        LetKind::Strict,
        foo,
        Lambda::function_(
            1,
            vec![foo_param],
            Lambda::var(foo_param),
            FunctionAttribute::default(),
            LamLoc::NONE,
        ),
        Lambda::let_(
            LetKind::Strict,
            s,
            Lambda::const_(Constant::String("😀".to_string())),
            Lambda::let_(
                LetKind::Strict,
                bar,
                Lambda::function_(
                    1,
                    vec![bar_param],
                    Lambda::var(bar_param),
                    FunctionAttribute::default(),
                    LamLoc::NONE,
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
        rebound_export,
        Lambda::var(global),
        Lambda::prim(
            Primitive::Pmakeblock(
                TagInfo::ModuleExport(vec![rebound_export]),
                Mutable::Immutable,
            ),
            vec![Lambda::var(rebound_export)],
            LamLoc::NONE,
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

fn coerce_toplevel_exports_moves_same_name_literal_binding_to_tail_across_later_effect_without_remaining_use()
 {
    let mut compiler = LambdaCompiler::new();
    let exported = Ident::create_local("b");
    let helper = Ident::create_local("f1");
    let sink = Ident::create_persistent("sink");
    let mut block = vec![
        Statement::variable(VariableDeclaration {
            ident: exported,
            value: Some(Expression::string("Three")),
            property: LetKind::Alias,
            ident_info: IdentInfo::default(),
        }),
        Statement::variable(VariableDeclaration {
            ident: helper,
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
            exports: vec![exported],
            values: vec![Expression::var(exported)],
        },
        OutputFinished::False,
    );
    let exports = resolve_export_aliases(&block, exports);

    assert_eq!(exports, vec![exported]);
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
                    desc: ExpressionDesc::Str(txt),
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
fn compile_deps_program_declares_export_left_unbound_by_throwing_binding() {
    let mut compiler = LambdaCompiler::new();
    let exported = Ident::create_local("u");
    let export_block = Lambda::prim(
        Primitive::Pmakeblock(TagInfo::ModuleExport(vec![exported]), Mutable::Immutable),
        vec![Lambda::var(exported)],
        LamLoc::NONE,
    );
    let lam = Lambda::let_(
        LetKind::Strict,
        exported,
        Lambda::prim(
            Primitive::Praise,
            vec![Lambda::const_(Constant::string("boom"))],
            LamLoc::NONE,
        ),
        export_block,
    );

    let deps = compiler.compile_deps_program(&lam);

    assert_eq!(deps.program.exports, vec![exported]);
    // lam_compile_main.ml `declare_undeclared_exports`: the export the
    // throw left unbound is declared after it.
    let [stmt, declared] = deps.program.block.as_slice() else {
        panic!(
            "expected the terminating throw followed by the export declaration, got {:?}",
            deps.program.block
        );
    };
    assert!(matches!(
        declared,
        Statement {
            desc: StatementDesc::Variable(VariableDeclaration { ident, value: None, .. }),
            ..
        } if ident.same(&exported)
    ));
    assert!(matches!(
        stmt,
        Statement {
            desc: StatementDesc::Throw(Expression {
                desc: ExpressionDesc::Str(txt),
                ..
            }),
            ..
        } if txt == "boom"
    ));
}

#[test]
fn compile_deps_program_declares_export_left_unbound_by_nested_throwing_binding() {
    let mut compiler = LambdaCompiler::new();
    let exported = Ident::create_local("A");
    let nested = Ident::create_local("u");
    let export_block = Lambda::prim(
        Primitive::Pmakeblock(TagInfo::ModuleExport(vec![exported]), Mutable::Immutable),
        vec![Lambda::var(exported)],
        LamLoc::NONE,
    );
    let lam = Lambda::let_(
        LetKind::Strict,
        exported,
        Lambda::let_(
            LetKind::Strict,
            nested,
            Lambda::prim(
                Primitive::Praise,
                vec![Lambda::const_(Constant::string("boom"))],
                LamLoc::NONE,
            ),
            Lambda::prim(
                Primitive::Pmakeblock(
                    TagInfo::record(
                        vec![(nested.name().to_string(), false)],
                        crate::parser::ast::MutableFlag::Immutable,
                    ),
                    Mutable::Immutable,
                ),
                vec![Lambda::var(nested)],
                LamLoc::NONE,
            ),
        ),
        export_block,
    );

    let deps = compiler.compile_deps_program(&lam);

    assert_eq!(deps.program.exports, vec![exported]);
    // lam_compile_main.ml `declare_undeclared_exports`: the export the
    // throw left unbound is declared after it.
    let [stmt, declared] = deps.program.block.as_slice() else {
        panic!(
            "expected the terminating throw followed by the export declaration, got {:?}",
            deps.program.block
        );
    };
    assert!(matches!(
        declared,
        Statement {
            desc: StatementDesc::Variable(VariableDeclaration { ident, value: None, .. }),
            ..
        } if ident.same(&exported)
    ));
    assert!(
        matches!(
            stmt,
            Statement {
                desc: StatementDesc::Throw(Expression {
                    desc: ExpressionDesc::Str(txt),
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
    let block = compiler.compile_return_block_tree(&Lambda::seq(
        Lambda::prim(
            Primitive::Praise,
            vec![Lambda::const_(Constant::string("boom"))],
            LamLoc::NONE,
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
                desc: ExpressionDesc::Str(txt),
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
    let block = compiler.compile_return_block_tree(&Lambda::LtryWith(
        Box::new(Lambda::Lapply(Box::new(Apply {
            ap_func: Box::new(Lambda::var(callee)),
            ap_args: vec![],
            ap_info: ApInfo {
                loc: LamLoc::NONE,
                status: ApplyStatus::Na,
            },
        }))),
        exn,
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
    let compiled = compiler.compile_expr_tree(&Lambda::LtryWith(
        Box::new(Lambda::const_(Constant::int(1))),
        exn,
        Box::new(Lambda::const_(Constant::int(2))),
    ));

    let [declare, try_stmt] = compiled.prelude.as_slice() else {
        panic!("expected a declaration followed by a try statement");
    };
    let StatementDesc::Variable(VariableDeclaration { ident: result, .. }) = &declare.desc else {
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
fn direct_recursive_trywith_self_calls_do_not_lower_to_loops_like_ocaml() {
    let mut compiler = LambdaCompiler::new();
    let loop_ = Ident::create_local("loop");
    let acc = Ident::create_local("acc");
    let exn = Ident::create_local("exn");
    let lam = Lambda::letrec(
        vec![(
            loop_,
            Lambda::function_(
                1,
                vec![acc],
                Lambda::LtryWith(
                    Box::new(Lambda::Lapply(Box::new(Apply {
                        ap_func: Box::new(Lambda::var(loop_)),
                        ap_args: vec![Lambda::var(acc)],
                        ap_info: ApInfo {
                            loc: LamLoc::NONE,
                            status: ApplyStatus::Na,
                        },
                    }))),
                    exn,
                    Box::new(Lambda::const_(Constant::int(0))),
                ),
                FunctionAttribute::default(),
                LamLoc::NONE,
            ),
        )],
        Lambda::unit(),
    );

    let compiled = compiler.compile_expr_tree(&lam);
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
fn recursive_trywith_handler_self_calls_lower_to_loops_like_ocaml() {
    let mut compiler = LambdaCompiler::new();
    let loop_ = Ident::create_local("loop");
    let read = Ident::create_local("read");
    let acc = Ident::create_local("acc");
    let exn = Ident::create_local("exn");
    let tailcall = Lambda::Lapply(Box::new(Apply {
        ap_func: Box::new(Lambda::var(loop_)),
        ap_args: vec![Lambda::var(acc)],
        ap_info: ApInfo {
            loc: LamLoc::NONE,
            status: ApplyStatus::Na,
        },
    }));
    let lam = Lambda::letrec(
        vec![(
            loop_,
            Lambda::function_(
                1,
                vec![acc],
                Lambda::LtryWith(
                    Box::new(Lambda::Lapply(Box::new(Apply {
                        ap_func: Box::new(Lambda::var(read)),
                        ap_args: vec![Lambda::var(acc)],
                        ap_info: ApInfo {
                            loc: LamLoc::NONE,
                            status: ApplyStatus::Na,
                        },
                    }))),
                    exn,
                    Box::new(tailcall),
                ),
                FunctionAttribute::default(),
                LamLoc::NONE,
            ),
        )],
        Lambda::unit(),
    );

    let compiled = compiler.compile_expr_tree(&lam);
    let rendered = print_block(&compiled.prelude);

    assert!(
        rendered.contains("while (true)"),
        "expected handler self-tailcall lowering to emit a loop:\n{rendered}"
    );
    assert!(
        rendered.contains("try {"),
        "expected the non-tail try body to stay under try:\n{rendered}"
    );
    assert!(
        rendered.contains("continue;"),
        "expected the handler self-tailcall to continue the loop:\n{rendered}"
    );
    assert!(
        !rendered.contains("return loop("),
        "unexpected recursive return call remained in handler tail position:\n{rendered}"
    );
}

#[test]
fn block_finishes_output_ignores_switch_case_breaks() {
    let block = vec![Statement::new(StatementDesc::StringSwitch(
        Expression::bool(true),
        vec![StringClause {
            tag_type: crate::lambda::SwitchCaseTag::String("a".to_string()),
            clause: CaseClause {
                source_loc: None,
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
        Box::new(Lambda::Lapply(Box::new(Apply {
            ap_func: Box::new(Lambda::var(callback)),
            ap_args: vec![],
            ap_info: ApInfo {
                loc: LamLoc::NONE,
                status: ApplyStatus::Na,
            },
        }))),
        Box::new(Lambda::const_(Constant::none())),
    );
    let program = compiler.compile_program(&Lambda::prim(
        Primitive::Pmakearray,
        vec![sequence],
        LamLoc::NONE,
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
    let call = Lambda::Lapply(Box::new(Apply {
        ap_func: Box::new(Lambda::var(callback)),
        ap_args: vec![],
        ap_info: ApInfo {
            loc: LamLoc::NONE,
            status: ApplyStatus::Na,
        },
    }));
    let sequence = Lambda::Lsequence(
        Box::new(Lambda::Lsequence(
            Box::new(call),
            Box::new(Lambda::prim(
                Primitive::Pignore,
                vec![Lambda::const_(Constant::int(3))],
                LamLoc::NONE,
            )),
        )),
        Box::new(Lambda::var(value)),
    );

    let compiled = compiler.compile_expr_tree(&sequence);

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
fn int_switch_expressions_group_non_adjacent_equal_cases_like_ocaml_stable_group() {
    let mut compiler = LambdaCompiler::new();
    let scrutinee = Ident::create_local("scrutinee");
    let compiled = compiler.compile_expr_tree(&Lambda::Lswitch(
        Box::new(Lambda::var(scrutinee)),
        Box::new(LambdaSwitch {
            sw_consts_full: true,
            sw_consts: vec![
                (
                    crate::lambda::SwitchKey::Int(0),
                    Lambda::const_(Constant::int(2)),
                ),
                (
                    crate::lambda::SwitchKey::Int(1),
                    Lambda::const_(Constant::int(1)),
                ),
                (
                    crate::lambda::SwitchKey::Int(2),
                    Lambda::const_(Constant::int(2)),
                ),
            ],
            sw_blocks_full: false,
            sw_blocks: vec![],
            sw_failaction: None,
            sw_dispatch: crate::lambda::SwitchDispatch::Direct,
        }),
    ));

    let [declare, switch_stmt] = compiled.prelude.as_slice() else {
        panic!("expected a declaration and switch statement");
    };
    let StatementDesc::Variable(VariableDeclaration { ident: result, .. }) = &declare.desc else {
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
fn string_switch_effects_group_adjacent_equal_cases_and_drop_default_duplicates() {
    let mut compiler = LambdaCompiler::new();
    let scrutinee = Ident::create_local("scrutinee");
    let captured = Ident::create_local("captured");
    let block = compiler.compile_effect_block_tree(&Lambda::LstringSwitch(
        Box::new(Lambda::var(scrutinee)),
        vec![
            (
                "A".to_string(),
                Lambda::Lassign(captured, Box::new(Lambda::const_(Constant::int(1)))),
            ),
            (
                "B".to_string(),
                Lambda::Lassign(captured, Box::new(Lambda::const_(Constant::int(1)))),
            ),
            (
                "C".to_string(),
                Lambda::Lassign(captured, Box::new(Lambda::const_(Constant::int(2)))),
            ),
        ],
        Some(Box::new(Lambda::Lassign(
            captured,
            Box::new(Lambda::const_(Constant::int(2))),
        ))),
    ));

    let [switch_stmt] = block.as_slice() else {
        panic!("expected a single string switch");
    };
    let StatementDesc::StringSwitch(test, clauses, Some(default_block)) = &switch_stmt.desc else {
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
    let block = compiler.compile_effect_block_tree(&Lambda::LstringSwitch(
        Box::new(Lambda::var(scrutinee)),
        vec![
            (
                "A".to_string(),
                Lambda::Lassign(captured, Box::new(Lambda::const_(Constant::int(2)))),
            ),
            (
                "B".to_string(),
                Lambda::Lassign(captured, Box::new(Lambda::const_(Constant::int(1)))),
            ),
            (
                "C".to_string(),
                Lambda::Lassign(captured, Box::new(Lambda::const_(Constant::int(2)))),
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

pub(super) fn gpr_1438_switch_cases(
    b: &Ident,
    c: &Ident,
    d: &Ident,
    e: &Ident,
) -> Vec<(crate::lambda::SwitchKey, Lambda)> {
    vec![
        (98, Lambda::var(*c)),
        (99, Lambda::static_raise(1, Vec::new())),
        (100, Lambda::static_raise(2, Vec::new())),
        (101, Lambda::static_raise(2, Vec::new())),
        (102, Lambda::static_raise(2, Vec::new())),
        (103, Lambda::static_raise(2, Vec::new())),
        (104, Lambda::static_raise(2, Vec::new())),
        (105, Lambda::static_raise(2, Vec::new())),
        (106, Lambda::var(*d)),
        (107, Lambda::var(*e)),
        (108, Lambda::static_raise(2, Vec::new())),
        (109, Lambda::static_raise(2, Vec::new())),
        (110, Lambda::static_raise(2, Vec::new())),
        (111, Lambda::static_raise(2, Vec::new())),
        (112, Lambda::static_raise(2, Vec::new())),
        (113, Lambda::static_raise(2, Vec::new())),
        (114, Lambda::static_raise(2, Vec::new())),
        (115, Lambda::static_raise(2, Vec::new())),
        (116, Lambda::var(*b)),
        (117, Lambda::static_raise(2, Vec::new())),
        (118, Lambda::static_raise(1, Vec::new())),
    ]
    .into_iter()
    .map(|(key, action)| (crate::lambda::SwitchKey::Int(key), action))
    .collect()
}

pub(super) fn gpr_1438_fallthrough_handler() -> Lambda {
    let param = Ident::create_local("param");
    Lambda::function_(
        1,
        vec![param],
        Lambda::const_(Constant::JsUndefined { is_unit: true }),
        FunctionAttribute {
            return_unit: true,
            ..FunctionAttribute::default()
        },
        LamLoc::NONE,
    )
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
        vec![key, a, b, c, d, e],
        Lambda::LstaticCatch(
            Box::new(Lambda::LstaticCatch(
                Box::new(Lambda::Lswitch(
                    Box::new(Lambda::var(key)),
                    Box::new(LambdaSwitch {
                        sw_consts_full: false,
                        sw_consts: gpr_1438_switch_cases(&b, &c, &d, &e),
                        sw_blocks_full: true,
                        sw_blocks: vec![],
                        sw_failaction: Some(Box::new(Lambda::static_raise(2, Vec::new()))),
                        sw_dispatch: crate::lambda::SwitchDispatch::Direct,
                    }),
                )),
                (2, vec![]),
                Box::new(gpr_1438_fallthrough_handler()),
            )),
            (1, vec![]),
            Box::new(Lambda::var(a)),
        ),
        FunctionAttribute::default(),
        LamLoc::NONE,
    );
    let lam = Lambda::let_(
        LetKind::Strict,
        action_key,
        function,
        Lambda::prim(
            Primitive::Pmakeblock(TagInfo::ModuleExport(vec![action_key]), Mutable::Immutable),
            vec![Lambda::var(action_key)],
            LamLoc::NONE,
        ),
    );

    let simplified = simplify_tree_for_js_backend(&lam);
    let mut direct_compiler = LambdaCompiler::new();
    let direct_body =
        direct_compiler.compile_return_block_tree(extract_first_function_body(&simplified));
    assert_fallthrough_return_outside_switch_body(
        &direct_body,
        "after simplify + direct compile_return_block",
    );

    let compiled = compiler.compile_expr_tree(&simplified);
    let mut block = compiled.prelude;
    assert_first_function_body_keeps_fallthrough_return_outside_switch(
        &block,
        "after compile_expr",
    );

    let exports = if let Some(mut exports) = extract_toplevel_exports(compiled.expr, &mut block) {
        if compiled.finished == OutputFinished::True {
            for value in &mut exports.values {
                *value = Expression::undefined(false);
            }
        }
        compiler.coerce_toplevel_exports(&mut block, exports, compiled.finished)
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
        side_effect: module_side_effect_reason_tree(&simplified),
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
fn function_return_blocks_lower_switches_without_a_result_temp() {
    let mut compiler = LambdaCompiler::new();
    let scrutinee = Ident::create_local("scrutinee");
    let compiled =
        compiler.compile_expr_tree(&Lambda::Lfunction(Box::new(crate::lambda::LFunction {
            loc: LamLoc::NONE,
            arity: 1,
            params: vec![scrutinee],
            body: Box::new(Lambda::Lswitch(
                Box::new(Lambda::var(scrutinee)),
                Box::new(LambdaSwitch {
                    sw_consts_full: true,
                    sw_consts: vec![
                        (
                            crate::lambda::SwitchKey::Int(0),
                            Lambda::const_(Constant::int(1)),
                        ),
                        (
                            crate::lambda::SwitchKey::Int(1),
                            Lambda::const_(Constant::int(2)),
                        ),
                    ],
                    sw_blocks_full: false,
                    sw_blocks: vec![],
                    sw_failaction: Some(Box::new(Lambda::const_(Constant::int(3)))),
                    sw_dispatch: crate::lambda::SwitchDispatch::Direct,
                }),
            )),
            attr: crate::lambda::FunctionAttribute::default(),
        })));

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
    let compiled =
        compiler.compile_expr_tree(&Lambda::Lfunction(Box::new(crate::lambda::LFunction {
            loc: LamLoc::NONE,
            arity: 1,
            params: vec![cond],
            body: Box::new(Lambda::LifThenElse(
                Box::new(Lambda::var(cond)),
                Box::new(Lambda::let_(
                    LetKind::Strict,
                    branch,
                    Lambda::const_(Constant::int(1)),
                    Lambda::var(branch),
                )),
                Box::new(Lambda::const_(Constant::int(0))),
            )),
            attr: crate::lambda::FunctionAttribute::default(),
        })));

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
                StatementDesc::If(test, then_block, else_block) => (test, then_block, else_block),
                StatementDesc::Block(inner) => match inner.as_slice() {
                    [inner_if] => {
                        let StatementDesc::If(test, then_block, else_block) = &inner_if.desc else {
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
                StatementDesc::If(test, then_block, else_block) => (test, then_block, else_block),
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
fn unit_return_function_with_trivial_if_branches_keeps_condition_effect_only() {
    let mut compiler = LambdaCompiler::new();
    let effect = Ident::create_local("effect");
    let body = Lambda::LifThenElse(
        Box::new(Lambda::apply(
            Lambda::var(effect),
            vec![],
            ApInfo {
                loc: LamLoc::NONE,
                status: ApplyStatus::Na,
            },
        )),
        Box::new(Lambda::const_(Constant::JsUndefined { is_unit: true })),
        Box::new(Lambda::const_(Constant::JsUndefined { is_unit: true })),
    );
    let compiled =
        compiler.compile_expr_tree(&Lambda::Lfunction(Box::new(crate::lambda::LFunction {
            loc: LamLoc::NONE,
            arity: 1,
            params: vec![effect],
            body: Box::new(body),
            attr: crate::lambda::FunctionAttribute {
                return_unit: true,
                ..Default::default()
            },
        })));

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
fn unit_return_function_flips_effect_guard_into_early_return() {
    let mut compiler = LambdaCompiler::new();
    let run = Ident::create_local("run");
    let cond = Ident::create_local("cond");
    let seen = Ident::create_local("seen");
    let lam = Lambda::let_(
        LetKind::Strict,
        run,
        Lambda::function_(
            2,
            vec![cond, seen],
            Lambda::LifThenElse(
                Box::new(Lambda::var(cond)),
                Box::new(Lambda::Lassign(
                    seen,
                    Box::new(Lambda::const_(Constant::int(1))),
                )),
                Box::new(Lambda::const_(Constant::JsUndefined { is_unit: true })),
            ),
            crate::lambda::FunctionAttribute {
                return_unit: true,
                ..Default::default()
            },
            LamLoc::NONE,
        ),
        Lambda::prim(
            Primitive::Pmakeblock(TagInfo::ModuleExport(vec![run]), Mutable::Immutable),
            vec![Lambda::var(run)],
            LamLoc::NONE,
        ),
    );

    let deps = compiler.compile_deps_program(&lam);
    let rendered = print_deps_program(&deps, None);
    // OCaml compiles the assignment as a statement whatever the
    // continuation (`compile_assign`), so the tail `else` is
    // `[Return undefined]` and `Js_stmt_make.if_` flips the guard into an
    // early return.
    assert!(
        rendered.contains("  if (!cond) {\n    return;\n  }\n  seen = 1;\n}"),
        "expected the guard to flip into an early return, got:\n{rendered}"
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
        run,
        Lambda::function_(
            2,
            vec![cond, seen],
            Lambda::LifThenElse(
                Box::new(Lambda::var(cond)),
                Box::new(Lambda::for_(
                    index,
                    Lambda::const_(Constant::int(0)),
                    Lambda::const_(Constant::int(1)),
                    crate::lambda::DirectionFlag::Upto,
                    Lambda::Lassign(seen, Box::new(Lambda::const_(Constant::int(1)))),
                )),
                Box::new(Lambda::const_(Constant::JsUndefined { is_unit: true })),
            ),
            crate::lambda::FunctionAttribute {
                return_unit: true,
                ..Default::default()
            },
            LamLoc::NONE,
        ),
        Lambda::prim(
            Primitive::Pmakeblock(TagInfo::ModuleExport(vec![run]), Mutable::Immutable),
            vec![Lambda::var(run)],
            LamLoc::NONE,
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
        run,
        Lambda::function_(
            2,
            vec![cond, seen],
            Lambda::LifThenElse(
                Box::new(Lambda::var(cond)),
                Box::new(Lambda::const_(Constant::JsUndefined { is_unit: true })),
                Box::new(Lambda::for_(
                    index,
                    Lambda::const_(Constant::int(0)),
                    Lambda::const_(Constant::int(1)),
                    crate::lambda::DirectionFlag::Upto,
                    Lambda::Lassign(seen, Box::new(Lambda::const_(Constant::int(1)))),
                )),
            ),
            crate::lambda::FunctionAttribute {
                return_unit: true,
                ..Default::default()
            },
            LamLoc::NONE,
        ),
        Lambda::prim(
            Primitive::Pmakeblock(TagInfo::ModuleExport(vec![run]), Mutable::Immutable),
            vec![Lambda::var(run)],
            LamLoc::NONE,
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
        run,
        Lambda::function_(
            3,
            vec![cond, seen, loop_cond],
            Lambda::LifThenElse(
                Box::new(Lambda::var(cond)),
                Box::new(Lambda::let_(
                    LetKind::Strict,
                    cell,
                    Lambda::const_(Constant::int(0)),
                    Lambda::while_(
                        Lambda::var(loop_cond),
                        Lambda::Lassign(seen, Box::new(Lambda::const_(Constant::int(1)))),
                    ),
                )),
                Box::new(Lambda::const_(Constant::JsUndefined { is_unit: true })),
            ),
            crate::lambda::FunctionAttribute {
                return_unit: true,
                ..Default::default()
            },
            LamLoc::NONE,
        ),
        Lambda::prim(
            Primitive::Pmakeblock(TagInfo::ModuleExport(vec![run]), Mutable::Immutable),
            vec![Lambda::var(run)],
            LamLoc::NONE,
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
fn let_bindings_lower_ifs_without_a_result_temp() {
    let mut compiler = LambdaCompiler::new();
    let cond = Ident::create_local("cond");
    let result = Ident::create_local("result");
    let branch = Ident::create_local("branch");
    let compiled = compiler.compile_expr_tree(&Lambda::Llet(
        LetKind::Strict,
        result,
        Box::new(Lambda::LifThenElse(
            Box::new(Lambda::var(cond)),
            Box::new(Lambda::let_(
                LetKind::Strict,
                branch,
                Lambda::const_(Constant::int(1)),
                Lambda::var(branch),
            )),
            Box::new(Lambda::const_(Constant::int(0))),
        )),
        Box::new(Lambda::var(result)),
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
    let compiled = compiler.compile_expr_tree(&Lambda::Llet(
        LetKind::Strict,
        result,
        Box::new(Lambda::prim(
            Primitive::Psequand,
            vec![
                Lambda::var(cond),
                Lambda::let_(
                    LetKind::Strict,
                    branch,
                    Lambda::const_(Constant::int(1)),
                    Lambda::var(branch),
                ),
            ],
            LamLoc::NONE,
        )),
        Box::new(Lambda::var(result)),
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
    let compiled = compiler.compile_expr_tree(&Lambda::Llet(
        LetKind::Strict,
        result,
        Box::new(Lambda::LifThenElse(
            Box::new(Lambda::var(cond)),
            Box::new(Lambda::const_(Constant::int(1))),
            Box::new(Lambda::const_(Constant::int(0))),
        )),
        Box::new(Lambda::var(result)),
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
    let block = compiler.compile_effect_block_tree(&Lambda::LifThenElse(
        Box::new(Lambda::var(cond)),
        Box::new(Lambda::Lsequence(
            Box::new(Lambda::Lassign(
                slot,
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
    let block = compiler.compile_effect_block_tree(&Lambda::LifThenElse(
        Box::new(Lambda::var(outer)),
        Box::new(Lambda::Lassign(
            lhs,
            Box::new(Lambda::const_(Constant::int(1))),
        )),
        Box::new(Lambda::LifThenElse(
            Box::new(Lambda::var(inner)),
            Box::new(Lambda::Lassign(
                rhs,
                Box::new(Lambda::const_(Constant::int(2))),
            )),
            Box::new(Lambda::Lassign(
                fallback,
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
        tag_info: Box::new(TagInfo::tuple()),
        elements: vec![Constant::int(1), Constant::int(2)],
    });

    let block = compiler.compile_effect_block_tree(&Lambda::LifThenElse(
        Box::new(Lambda::var(cond)),
        Box::new(Lambda::Lsequence(
            Box::new(Lambda::apply(
                Lambda::var(effect),
                vec![],
                ApInfo {
                    loc: LamLoc::NONE,
                    status: ApplyStatus::Na,
                },
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
                ExpressionDesc::CamlBlock(_, _, _)
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
            desc: ExpressionDesc::CamlBlock(_, _, _),
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
    let block = compiler.compile_effect_block_tree(&Lambda::LifThenElse(
        Box::new(Lambda::var(cond)),
        Box::new(Lambda::Lassign(
            lhs,
            Box::new(Lambda::const_(Constant::int(1))),
        )),
        Box::new(Lambda::Lassign(
            rhs,
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
    let compiled = compiler.compile_expr_tree(&Lambda::Lsequence(
        Box::new(Lambda::LifThenElse(
            Box::new(Lambda::var(cond)),
            Box::new(Lambda::const_(Constant::int(0))),
            Box::new(Lambda::LstaticRaise(
                1,
                vec![Lambda::const_(Constant::string("boom"))],
            )),
        )),
        Box::new(Lambda::var(value)),
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
    let compiled = compiler.compile_expr_tree(&Lambda::LifThenElse(
        Box::new(Lambda::var(outer_cond)),
        Box::new(Lambda::Llet(
            LetKind::Strict,
            alias,
            Box::new(Lambda::const_(Constant::int(1))),
            Box::new(Lambda::LifThenElse(
                Box::new(Lambda::var(inner_cond)),
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
        StatementDesc::Variable(VariableDeclaration { ident, .. }) => *ident,
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
fn assignment_merge_applies_js_not_swap_before_conditional_like_ocaml() {
    let compiler = LambdaCompiler::new();
    let result = Ident::create_local("result");
    let value = Ident::create_local("value");
    let cond = Expression::not(Expression::is_null_or_undefined(Expression::var(value)));
    let then_block = vec![Statement::exp(Expression::bin(
        BinOp::Eq,
        Expression::var(result),
        Expression::number(Number::int(1)),
    ))];
    let else_block = vec![Statement::exp(Expression::bin(
        BinOp::Eq,
        Expression::var(result),
        Expression::undefined(false),
    ))];

    let block = compiler.compile_test_assignment_block(&result, cond, then_block, else_block);

    assert!(matches!(
        block.as_slice(),
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
                ExpressionDesc::Cond(test, consequent, alternate),
            ) if lhs_id.same(&result)
                && matches!(
                    test.as_ref(),
                    Expression {
                        desc: ExpressionDesc::IsNullOrUndefined(inner),
                        ..
                    } if matches!(
                        inner.as_ref(),
                        Expression {
                            desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                            ..
                        } if id.same(&value)
                    )
                )
                && matches!(consequent.desc, ExpressionDesc::Undefined { .. })
                && matches!(alternate.desc, ExpressionDesc::Number(Number::Int { i: 1, .. }))
        )
    ));
}

#[test]
fn if_expression_result_temp_uses_tmp_name_like_ocaml() {
    let mut compiler = LambdaCompiler::new();
    let cond = Ident::create_local("cond");
    let alias = Ident::create_local("alias");
    let compiled = compiler.compile_expr_tree(&Lambda::LifThenElse(
        Box::new(Lambda::var(cond)),
        Box::new(Lambda::Llet(
            LetKind::Strict,
            alias,
            Box::new(Lambda::const_(Constant::int(1))),
            Box::new(Lambda::var(alias)),
        )),
        Box::new(Lambda::const_(Constant::int(0))),
    ));

    let [result_decl, if_stmt] = compiled.prelude.as_slice() else {
        panic!("expected a result declaration followed by the lowered if");
    };
    let result = match &result_decl.desc {
        StatementDesc::Variable(VariableDeclaration {
            ident, value: None, ..
        }) => *ident,
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

pub(super) fn mixed_untagged_string_overlap_switch(
    space_body: Lambda,
    default_body: Lambda,
) -> LambdaSwitch {
    LambdaSwitch {
        sw_consts_full: false,
        sw_consts: vec![
            (
                crate::lambda::SwitchKey::Constructor(
                    crate::types::VariantConstructorCase::Constant(crate::types::VariantTag {
                        name: "a".to_string(),
                        literal: crate::types::VariantLiteralTag::String("a".to_string()),
                    }),
                ),
                default_body.clone(),
            ),
            (
                crate::lambda::SwitchKey::Constructor(
                    crate::types::VariantConstructorCase::Constant(crate::types::VariantTag {
                        name: "b".to_string(),
                        literal: crate::types::VariantLiteralTag::String("b".to_string()),
                    }),
                ),
                default_body.clone(),
            ),
            (
                crate::lambda::SwitchKey::Constructor(
                    crate::types::VariantConstructorCase::Constant(crate::types::VariantTag {
                        name: "space".to_string(),
                        literal: crate::types::VariantLiteralTag::String("space".to_string()),
                    }),
                ),
                space_body,
            ),
        ],
        sw_blocks_full: false,
        sw_blocks: vec![],
        sw_failaction: Some(Box::new(default_body)),
        sw_dispatch: crate::lambda::SwitchDispatch::Variant(crate::types::VariantMatchingFacts {
            tag_name: None,
            block_types: vec![crate::types::VariantBlockType::String],
            literal_tags: vec![
                crate::types::VariantLiteralTag::String("space".to_string()),
                crate::types::VariantLiteralTag::String("b".to_string()),
                crate::types::VariantLiteralTag::String("a".to_string()),
            ],
        }),
    }
}

pub(super) fn single_complete_array_block_switch(
    array_body: Lambda,
    undefined_body: Lambda,
) -> LambdaSwitch {
    LambdaSwitch {
        sw_consts_full: true,
        sw_consts: vec![(
            crate::lambda::SwitchKey::Constructor(crate::types::VariantConstructorCase::Constant(
                crate::types::VariantTag {
                    name: "Empty".to_string(),
                    literal: crate::types::VariantLiteralTag::Undefined,
                },
            )),
            undefined_body,
        )],
        sw_blocks_full: true,
        sw_blocks: vec![(
            crate::lambda::SwitchKey::Constructor(crate::types::VariantConstructorCase::Block(
                crate::types::VariantBlock::Untagged {
                    tag: crate::types::VariantTag {
                        name: "Cons".to_string(),
                        literal: crate::types::VariantLiteralTag::String("Cons".to_string()),
                    },
                    block_type: crate::types::VariantBlockType::Instance(
                        crate::types::VariantInstance::Array(crate::types::ShapeAllocation::fresh()),
                    ),
                },
            )),
            array_body,
        )],
        sw_failaction: None,
        sw_dispatch: crate::lambda::SwitchDispatch::Variant(crate::types::VariantMatchingFacts {
            tag_name: None,
            block_types: vec![crate::types::VariantBlockType::Instance(
                crate::types::VariantInstance::Array(crate::types::ShapeAllocation::fresh()),
            )],
            literal_tags: vec![crate::types::VariantLiteralTag::Undefined],
        }),
    }
}

pub(super) fn default_only_untagged_boolean_switch(
    boolean_body: Lambda,
    default_body: Lambda,
) -> LambdaSwitch {
    LambdaSwitch {
        sw_consts_full: false,
        sw_consts: vec![],
        sw_blocks_full: false,
        sw_blocks: vec![(
            crate::lambda::SwitchKey::Constructor(crate::types::VariantConstructorCase::Block(
                crate::types::VariantBlock::Untagged {
                    tag: crate::types::VariantTag {
                        name: "B".to_string(),
                        literal: crate::types::VariantLiteralTag::String("B".to_string()),
                    },
                    block_type: crate::types::VariantBlockType::Boolean,
                },
            )),
            boolean_body,
        )],
        sw_failaction: Some(Box::new(default_body)),
        sw_dispatch: crate::lambda::SwitchDispatch::Variant(crate::types::VariantMatchingFacts {
            tag_name: None,
            block_types: vec![
                crate::types::VariantBlockType::Number,
                crate::types::VariantBlockType::String,
                crate::types::VariantBlockType::Boolean,
            ],
            literal_tags: vec![
                crate::types::VariantLiteralTag::Undefined,
                crate::types::VariantLiteralTag::Null,
            ],
        }),
    }
}

pub(super) fn assert_switch_case_assigns_int_result(block: &Block, result: &Ident, expected: i32) {
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
    assert!(matches!(break_stmt.desc, StatementDesc::Break(_)));
}

pub(super) fn assert_switch_default_assigns_int_result(
    block: &Block,
    result: &Ident,
    expected: i32,
) {
    let assign = match block.as_slice() {
        [assign] => assign,
        [assign, break_stmt] if matches!(break_stmt.desc, StatementDesc::Break(_)) => assign,
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

pub(super) fn assert_is_undefined_equality_check(expr: &Expression, ident: &Ident) {
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

pub(super) fn assert_int_expr(expr: &Expression, expected: i32) {
    assert!(matches!(
        expr,
        Expression {
            desc: ExpressionDesc::Number(Number::Int { i, .. }),
            ..
        } if *i == expected
    ));
}

pub(super) fn assert_assignment_to_int(expr: &Expression, ident: &Ident, expected: i32) {
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

pub(super) fn assert_switch_case_returns_int_result(block: &Block, expected: i32) {
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

pub(super) fn assert_switch_default_returns_int_result(block: &Block, expected: i32) {
    assert_switch_case_returns_int_result(block, expected);
}

pub(super) fn assert_switch_case_returns_bool_result(block: &Block, expected: bool) {
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

fn assert_first_function_body_keeps_fallthrough_return_outside_switch(block: &Block, stage: &str) {
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
        panic!("{stage}: expected the function body to keep the fallthrough tail after the switch");
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
        panic!("{stage}: expected the function body to keep the fallthrough tail after the switch");
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
        other => {
            panic!("expected the top-level binding to stay function-shaped, got {other:?}")
        }
    }
}

pub(super) fn assert_typeof_check(
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
                    desc: ExpressionDesc::Str(txt),
                    ..
                } if txt == expected_type
            ));
        }
        other => panic!("expected a typeof check, got {other:?}"),
    }
}

pub(super) fn assert_typeof_object_check(expr: &Expression, ident: &Ident, expect_object: bool) {
    let expected_op = if expect_object {
        BinOp::EqEqEq
    } else {
        BinOp::NotEqEq
    };
    assert_typeof_check(expr, ident, "object", expected_op);
}

pub(super) fn assert_array_is_array_call(expr: &Expression, ident: &Ident) {
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

pub(super) fn assert_string_equality_check(
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
                    desc: ExpressionDesc::Str(txt),
                    ..
                } if txt == expected_tag
            ));
        }
        other => panic!("expected a string equality check, got {other:?}"),
    }
}

pub(super) fn assert_tag_field_access(expr: &Expression, ident: &Ident) {
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
fn flattens_value_sequences_back_to_effect_statements_at_toplevel() {
    let mut compiler = LambdaCompiler::new();
    let callback = Ident::create_local("callback");
    let lam = Lambda::Lsequence(
        Box::new(Lambda::Lapply(Box::new(Apply {
            ap_func: Box::new(Lambda::var(callback)),
            ap_args: vec![],
            ap_info: ApInfo {
                loc: LamLoc::NONE,
                status: ApplyStatus::Na,
            },
        }))),
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
    let lam = Lambda::Lapply(Box::new(Apply {
        ap_func: Box::new(Lambda::LifThenElse(
            Box::new(Lambda::const_(Constant::JsTrue)),
            Box::new(Lambda::Lsequence(
                Box::new(Lambda::Lapply(Box::new(Apply {
                    ap_func: Box::new(Lambda::var(before)),
                    ap_args: vec![],
                    ap_info: ApInfo {
                        loc: LamLoc::NONE,
                        status: ApplyStatus::Na,
                    },
                }))),
                Box::new(Lambda::var(then_fn)),
            )),
            Box::new(Lambda::Lsequence(
                Box::new(Lambda::Lapply(Box::new(Apply {
                    ap_func: Box::new(Lambda::var(after)),
                    ap_args: vec![],
                    ap_info: ApInfo {
                        loc: LamLoc::NONE,
                        status: ApplyStatus::Na,
                    },
                }))),
                Box::new(Lambda::var(else_fn)),
            )),
        )),
        ap_args: vec![Lambda::const_(Constant::int(1))],
        ap_info: ApInfo {
            loc: LamLoc::NONE,
            status: ApplyStatus::Na,
        },
    }));

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
    let compiled = compiler.compile_expr_tree(&Lambda::Lapply(Box::new(Apply {
        ap_func: Box::new(Lambda::var(callback)),
        ap_args: vec![Lambda::const_(Constant::int(1))],
        ap_info: ApInfo {
            loc: LamLoc::NONE,
            status: ApplyStatus::Na,
        },
    })));

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
    let loc = LamLoc::NONE;

    let lam = Lambda::let_(
        LetKind::Alias,
        gg,
        Lambda::function_(
            2,
            vec![x, y],
            Lambda::let_(
                LetKind::Strict,
                u,
                Lambda::prim(
                    Primitive::Paddint,
                    vec![Lambda::var(x), Lambda::var(y)],
                    loc,
                ),
                Lambda::function_(
                    1,
                    vec![z],
                    Lambda::prim(
                        Primitive::Paddint,
                        vec![Lambda::var(u), Lambda::var(z)],
                        loc,
                    ),
                    crate::lambda::FunctionAttribute::default(),
                    LamLoc::NONE,
                ),
            ),
            crate::lambda::FunctionAttribute::default(),
            LamLoc::NONE,
        ),
        Lambda::let_(
            LetKind::Strict,
            result,
            Lambda::Lapply(Box::new(Apply {
                ap_func: Box::new(Lambda::Lapply(Box::new(Apply {
                    ap_func: Box::new(Lambda::var(gg)),
                    ap_args: vec![
                        Lambda::const_(Constant::int(3)),
                        Lambda::const_(Constant::int(5)),
                    ],
                    ap_info: ApInfo {
                        loc: loc,
                        status: ApplyStatus::Na,
                    },
                }))),
                ap_args: vec![Lambda::const_(Constant::int(6))],
                ap_info: ApInfo {
                    loc: loc,
                    status: ApplyStatus::Na,
                },
            })),
            Lambda::var(result),
        ),
    );

    let simplified = simplify_tree_for_js_backend(&lam);
    let compiled = compiler.compile_expr_tree(&simplified);
    let rendered = format!(
        "{}\n{}",
        print_block(&compiled.prelude),
        print_expression(&compiled.expr)
    );
    assert_eq!(
        rendered.trim(),
        "14",
        "expected Ari_regress-style nested apply to fully reduce, got:\n{rendered}"
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
    let loc = LamLoc::NONE;

    let lam = Lambda::let_(
        LetKind::Alias,
        g1,
        Lambda::function_(
            2,
            vec![x, y],
            Lambda::let_(
                LetKind::Strict,
                u,
                Lambda::prim(
                    Primitive::Paddint,
                    vec![Lambda::var(x), Lambda::var(y)],
                    loc,
                ),
                Lambda::function_(
                    2,
                    vec![xx, yy],
                    Lambda::prim(
                        Primitive::Paddint,
                        vec![
                            Lambda::prim(
                                Primitive::Paddint,
                                vec![Lambda::var(xx), Lambda::var(yy)],
                                loc,
                            ),
                            Lambda::var(u),
                        ],
                        loc,
                    ),
                    crate::lambda::FunctionAttribute::default(),
                    LamLoc::NONE,
                ),
            ),
            crate::lambda::FunctionAttribute::default(),
            LamLoc::NONE,
        ),
        Lambda::let_(
            LetKind::Strict,
            result,
            Lambda::function_(
                1,
                vec![extra],
                Lambda::Lapply(Box::new(Apply {
                    ap_func: Box::new(Lambda::Lapply(Box::new(Apply {
                        ap_func: Box::new(Lambda::var(g1)),
                        ap_args: vec![
                            Lambda::const_(Constant::int(3)),
                            Lambda::const_(Constant::int(4)),
                        ],
                        ap_info: ApInfo {
                            loc: loc,
                            status: ApplyStatus::Na,
                        },
                    }))),
                    ap_args: vec![Lambda::const_(Constant::int(6)), Lambda::var(extra)],
                    ap_info: ApInfo {
                        loc: loc,
                        status: ApplyStatus::Na,
                    },
                })),
                crate::lambda::FunctionAttribute::default(),
                LamLoc::NONE,
            ),
            Lambda::var(result),
        ),
    );

    let simplified = simplify_tree_for_js_backend(&lam);
    let compiled = compiler.compile_expr_tree(&simplified);
    let rendered = print_expression(&compiled.expr);
    assert_eq!(
        rendered.trim(),
        "extra => (6 + extra | 0) + 7 | 0",
        "expected test_demo-style nested apply to reduce captured constants, got:\n{rendered}"
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
    let compiled = compiler.compile_expr_tree(&Lambda::Llet(
        LetKind::Strict,
        x,
        Box::new(Lambda::Lapply(Box::new(Apply {
            ap_func: Box::new(Lambda::var(callback)),
            ap_args: vec![Lambda::const_(Constant::int(1))],
            ap_info: ApInfo {
                loc: LamLoc::NONE,
                status: ApplyStatus::Na,
            },
        }))),
        Box::new(Lambda::var(x)),
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
    let lam = Lambda::Lapply(Box::new(Apply {
        ap_func: Box::new(Lambda::LifThenElse(
            Box::new(Lambda::const_(Constant::JsTrue)),
            Box::new(Lambda::Lsequence(
                Box::new(Lambda::Lapply(Box::new(Apply {
                    ap_func: Box::new(Lambda::var(before)),
                    ap_args: vec![],
                    ap_info: ApInfo {
                        loc: LamLoc::NONE,
                        status: ApplyStatus::Na,
                    },
                }))),
                Box::new(Lambda::var(then_fn)),
            )),
            Box::new(Lambda::Lsequence(
                Box::new(Lambda::Lapply(Box::new(Apply {
                    ap_func: Box::new(Lambda::var(after)),
                    ap_args: vec![],
                    ap_info: ApInfo {
                        loc: LamLoc::NONE,
                        status: ApplyStatus::Na,
                    },
                }))),
                Box::new(Lambda::var(else_fn)),
            )),
        )),
        ap_args: vec![Lambda::const_(Constant::int(1))],
        ap_info: ApInfo {
            loc: LamLoc::NONE,
            status: ApplyStatus::Na,
        },
    }));

    let block = compiler.compile_return_block_tree(&lam);
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
    let lam = Lambda::Lapply(Box::new(Apply {
        ap_func: Box::new(Lambda::LifThenElse(
            Box::new(Lambda::const_(Constant::JsTrue)),
            Box::new(Lambda::Lsequence(
                Box::new(Lambda::Lapply(Box::new(Apply {
                    ap_func: Box::new(Lambda::var(before)),
                    ap_args: vec![],
                    ap_info: ApInfo {
                        loc: LamLoc::NONE,
                        status: ApplyStatus::Na,
                    },
                }))),
                Box::new(Lambda::var(then_fn)),
            )),
            Box::new(Lambda::Lsequence(
                Box::new(Lambda::Lapply(Box::new(Apply {
                    ap_func: Box::new(Lambda::var(after)),
                    ap_args: vec![],
                    ap_info: ApInfo {
                        loc: LamLoc::NONE,
                        status: ApplyStatus::Na,
                    },
                }))),
                Box::new(Lambda::var(else_fn)),
            )),
        )),
        ap_args: vec![Lambda::const_(Constant::int(1))],
        ap_info: ApInfo {
            loc: LamLoc::NONE,
            status: ApplyStatus::Na,
        },
    }));

    let block = compiler.compile_assign_to_target_block_tree(&result, &lam);
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
        Lambda::Lapply(Box::new(Apply {
            ap_func: Box::new(Lambda::var(callback)),
            ap_args: vec![],
            ap_info: ApInfo {
                loc: LamLoc::NONE,
                status: ApplyStatus::Na,
            },
        }))
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
            Box::new(Lambda::var(value)),
        )),
    );
    let compiled =
        compiler.compile_expr_tree(&Lambda::Lfunction(Box::new(crate::lambda::LFunction {
            loc: LamLoc::NONE,
            arity: 1,
            params: vec![value],
            body: Box::new(body),
            attr: crate::lambda::FunctionAttribute::default(),
        })));

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
        Lambda::Lapply(Box::new(Apply {
            ap_func: Box::new(Lambda::var(*id)),
            ap_args: vec![],
            ap_info: ApInfo {
                loc: LamLoc::NONE,
                status: ApplyStatus::Na,
            },
        }))
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
                            Expression::var(callback),
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
fn js_tailcall_inline_inlines_once_pure_named_calls() {
    let helper = Ident::create_local("helper");
    let arg = Ident::create_local("arg");
    let run = Ident::create_local("run");
    let value = Ident::create_local("value");
    let deps = apply_js_tailcall_inline_pass(DepsProgram {
        program: Program::new(
            vec![
                Statement::variable(VariableDeclaration {
                    ident: helper,
                    value: Some(Expression::new(ExpressionDesc::Fun {
                        is_method: false,
                        params: vec![arg],
                        body: vec![Statement::return_(Expression::var(arg))],
                        env: Default::default(),
                        return_unit: false,
                        async_: false,
                        directive: None,
                    })),
                    property: LetKind::Strict,
                    ident_info: IdentInfo::default(),
                }),
                Statement::variable(VariableDeclaration {
                    ident: run,
                    value: Some(Expression::new(ExpressionDesc::Fun {
                        is_method: false,
                        params: vec![value],
                        body: vec![Statement::return_(Expression::call(
                            Expression::var(helper),
                            vec![Expression::var(value)],
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
            vec![run],
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
                    ident: helper,
                    value: Some(Expression::new(ExpressionDesc::Fun {
                        is_method: false,
                        params: vec![arg],
                        body: vec![Statement::return_(Expression::var(arg))],
                        env: Default::default(),
                        return_unit: false,
                        async_: false,
                        directive: None,
                    })),
                    property: LetKind::Strict,
                    ident_info: IdentInfo::default(),
                }),
                Statement::variable(VariableDeclaration {
                    ident: run,
                    value: Some(Expression::new(ExpressionDesc::Fun {
                        is_method: false,
                        params: vec![guard, value],
                        body: vec![
                            Statement::if_(
                                Expression::var(guard),
                                vec![Statement::return_(Expression::number(Number::int(0)))],
                                vec![],
                            ),
                            Statement::return_(Expression::call(
                                Expression::var(helper),
                                vec![Expression::var(value)],
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
            vec![run],
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
                ident: run,
                value: Some(Expression::new(ExpressionDesc::Fun {
                    is_method: false,
                    params: vec![value],
                    body: vec![Statement::return_(Expression::call(
                        Expression::new(ExpressionDesc::Fun {
                            is_method: false,
                            params: vec![param],
                            body: vec![Statement::return_(Expression::var(param))],
                            env: Default::default(),
                            return_unit: false,
                            async_: false,
                            directive: None,
                        }),
                        vec![Expression::var(value)],
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
            vec![run],
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
                ident: run,
                value: Some(Expression::new(ExpressionDesc::Fun {
                    is_method: false,
                    params: vec![],
                    body: vec![Statement::return_(Expression::call(
                        Expression::new(ExpressionDesc::Fun {
                            is_method: false,
                            params: vec![outer_param],
                            body: vec![Statement::return_(Expression::new(ExpressionDesc::Fun {
                                is_method: false,
                                params: vec![inner_param],
                                body: vec![Statement::return_(Expression::var(inner_param))],
                                env: Default::default(),
                                return_unit: false,
                                async_: false,
                                directive: None,
                            }))],
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
            vec![run],
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
                ident: run,
                value: Some(Expression::new(ExpressionDesc::Fun {
                    is_method: false,
                    params: vec![],
                    body: vec![Statement::return_(Expression::call(
                        Expression::new(ExpressionDesc::Fun {
                            is_method: false,
                            params: vec![outer_param],
                            body: vec![
                                Statement::variable(VariableDeclaration {
                                    ident: inner_binding,
                                    value: Some(Expression::number(Number::int(1))),
                                    property: LetKind::Strict,
                                    ident_info: IdentInfo::default(),
                                }),
                                Statement::return_(Expression::var(inner_binding)),
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
            vec![run],
        ),
        modules: vec![],
        side_effect: None,
    });
    let rendered = print_block(&deps.program.block);
    // The constant argument replaces the parameter (js_pass_tailcall_inline.ml
    // `substitute_arguments`), so no outer `value` is declared; the inner
    // binding that shadows it must keep its own value.
    assert!(
        rendered.contains("let value = 1;"),
        "expected the shadowing binding to stay intact after inlining, got:\n{rendered}"
    );
    assert!(
        rendered.contains("return value;"),
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
    let loc = LamLoc::NONE;

    let compiled =
        compiler.compile_expr_tree(&Lambda::Lfunction(Box::new(crate::lambda::LFunction {
            loc: LamLoc::NONE,
            arity: 1,
            params: vec![module_param],
            body: Box::new(Lambda::let_(
                LetKind::Alias,
                field_alias,
                Lambda::prim(
                    Primitive::Pfield(
                        0,
                        FieldDbgInfo::Module {
                            name: "x".to_string(),
                        },
                    ),
                    vec![Lambda::var(module_param)],
                    loc,
                ),
                Lambda::prim(
                    Primitive::Pmakeblock(
                        TagInfo::Module(vec!["x".to_string()]),
                        Mutable::Immutable,
                    ),
                    vec![Lambda::var(field_alias)],
                    loc,
                ),
            )),
            attr: crate::lambda::FunctionAttribute::default(),
        })));

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
    let loc = LamLoc::NONE;

    let compiled =
        compiler.compile_expr_tree(&Lambda::Lfunction(Box::new(crate::lambda::LFunction {
            loc: LamLoc::NONE,
            arity: 1,
            params: vec![module_param],
            body: Box::new(Lambda::prim(
                Primitive::Pmakeblock(TagInfo::Module(vec!["x".to_string()]), Mutable::Immutable),
                vec![Lambda::prim(
                    Primitive::Pfield(
                        0,
                        FieldDbgInfo::Module {
                            name: "x".to_string(),
                        },
                    ),
                    vec![Lambda::var(module_param)],
                    loc,
                )],
                LamLoc::NONE,
            )),
            attr: crate::lambda::FunctionAttribute::default(),
        })));

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
    let loc = LamLoc::NONE;

    let compiled =
        compiler.compile_expr_tree(&Lambda::Lfunction(Box::new(crate::lambda::LFunction {
            loc: LamLoc::NONE,
            arity: 2,
            params: vec![left, right],
            body: Box::new(Lambda::let_(
                LetKind::Alias,
                left_alias,
                Lambda::prim(
                    Primitive::Pfield(
                        0,
                        FieldDbgInfo::Module {
                            name: "x".to_string(),
                        },
                    ),
                    vec![Lambda::var(left)],
                    loc,
                ),
                Lambda::let_(
                    LetKind::Alias,
                    right_alias,
                    Lambda::prim(
                        Primitive::Pfield(
                            1,
                            FieldDbgInfo::Module {
                                name: "y".to_string(),
                            },
                        ),
                        vec![Lambda::var(right)],
                        loc,
                    ),
                    Lambda::prim(
                        Primitive::Pmakeblock(
                            TagInfo::Module(vec!["x".to_string(), "y".to_string()]),
                            Mutable::Immutable,
                        ),
                        vec![Lambda::var(left_alias), Lambda::var(right_alias)],
                        loc,
                    ),
                ),
            )),
            attr: crate::lambda::FunctionAttribute::default(),
        })));

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
                            Expression::var(callback),
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
        other => {
            panic!("expected the dead impure binding to become an effect statement, got {other:?}")
        }
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
                        ident: tuple,
                        value: Some(Expression::new(ExpressionDesc::CamlBlock(
                            vec![
                                Expression::call(
                                    Expression::var(callback),
                                    vec![],
                                    CallInfo::default(),
                                ),
                                Expression::number(Number::int(2)),
                                Expression::number(Number::int(3)),
                            ],
                            MutableFlag::Immutable,
                            Box::new(TagInfo::tuple()),
                        ))),
                        property: LetKind::Strict,
                        ident_info: IdentInfo::default(),
                    }),
                    Statement::variable(VariableDeclaration {
                        ident: field,
                        value: Some(Expression::new(ExpressionDesc::ArrayIndex(
                            Box::new(Expression::var(tuple)),
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
                    desc: ExpressionDesc::CamlBlock(items, MutableFlag::Immutable, _),
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
        other => {
            panic!("expected the tuple projection to inline to the selected field, got {other:?}")
        }
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
                        Box::new(Expression::new(ExpressionDesc::object(vec![(
                            PropertyName::lit("d"),
                            Expression::var(value),
                        )]))),
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
                    desc: ExpressionDesc::Object(props),
                    ..
                } if matches!(
                    props.as_slice(),
                    [crate::js_ir::ObjectEntry::Property(PropertyName::Lit(name), Expression {
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
fn js_flatten_and_mark_dead_keeps_single_field_module_reads_materialized_like_ocaml() {
    let module = Ident::create_local("M");
    let eq = Ident::create_local("Eq");
    let projected = Ident::create_local("EQ");
    let deps = apply_js_flatten_and_mark_dead_pass(
        DepsProgram {
            program: Program::new(
                vec![
                    Statement::variable(VariableDeclaration {
                        ident: module,
                        value: Some(Expression::new(ExpressionDesc::CamlBlock(
                            vec![Expression::var(eq)],
                            MutableFlag::Immutable,
                            Box::new(TagInfo::Module(vec!["Eq".to_string()])),
                        ))),
                        property: LetKind::Strict,
                        ident_info: IdentInfo::default(),
                    }),
                    Statement::variable(VariableDeclaration {
                        ident: projected,
                        value: Some(Expression::new(ExpressionDesc::StaticIndex(
                            Box::new(Expression::var(module)),
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
                    desc: ExpressionDesc::CamlBlock(items, MutableFlag::Immutable, _),
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
fn js_flatten_and_mark_dead_keeps_jsx_component_tag_projection() {
    let module = Ident::create_local("Foo");
    let component = Ident::create_local("Async_jsx$Foo");
    let rendered = print_deps_program_with_directives(
        &apply_js_flatten_and_mark_dead_pass(
            DepsProgram {
                program: Program::new(
                    vec![
                        Statement::variable(VariableDeclaration {
                            ident: module,
                            value: Some(Expression::new(ExpressionDesc::CamlBlock(
                                vec![Expression::var(component)],
                                MutableFlag::Immutable,
                                Box::new(TagInfo::Module(vec!["make".to_string()])),
                            ))),
                            property: LetKind::Strict,
                            ident_info: IdentInfo::default(),
                        }),
                        Statement::exp(Expression::new(ExpressionDesc::Jsx(Box::new(
                            crate::js_ir::JsxExpression {
                                callee: Expression::qualified(
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
                                tag: Expression::new(ExpressionDesc::StaticIndex(
                                    Box::new(Expression::var(module)),
                                    "make".to_string(),
                                    Some(0),
                                )),
                                spread: None,
                                props: vec![],
                                children: None,
                                key: None,
                                multi: false,
                                fragment: false,
                            },
                        )))),
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
        "expected JSX preserve mode to keep Foo.make visible:\n{rendered}"
    );
    assert!(
        !rendered.contains("<Async_jsx$Foo />"),
        "JSX tag regressed to the component function value:\n{rendered}"
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
                            ident: module,
                            value: Some(Expression::new(ExpressionDesc::CamlBlock(
                                vec![Expression::var(component)],
                                MutableFlag::Immutable,
                                Box::new(TagInfo::Module(vec!["make".to_string()])),
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
                                    Box::new(Expression::var(module)),
                                    "make".to_string(),
                                    Some(0),
                                )),
                                Expression::new(ExpressionDesc::CamlBlock(
                                    vec![],
                                    MutableFlag::Immutable,
                                    Box::new(TagInfo::record(
                                        vec![],
                                        crate::parser::ast::MutableFlag::Immutable,
                                    )),
                                )),
                            ],
                            CallInfo {
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
                            ident: make,
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
                            ident: component,
                            value: Some(Expression::var(make)),
                            property: LetKind::Alias,
                            ident_info: IdentInfo::default(),
                        }),
                        Statement::variable(VariableDeclaration {
                            ident: module,
                            value: Some(Expression::new(ExpressionDesc::CamlBlock(
                                vec![Expression::var(component)],
                                MutableFlag::Immutable,
                                Box::new(TagInfo::Module(vec!["make".to_string()])),
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
fn js_flatten_and_mark_dead_materializes_strictopt_identity_optional_record_fields_like_ocaml() {
    let record = Ident::create_local("x");
    let deps = apply_js_flatten_and_mark_dead_pass(
        DepsProgram {
            program: Program::new(
                vec![Statement::variable(VariableDeclaration {
                    ident: record,
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
                        Box::new(TagInfo::Record(Box::new(
                            crate::lambda::lam_tag_info::RecordTag {
                                fields: vec![
                                    ("id".to_string(), true),
                                    ("name".to_string(), true),
                                    ("title".to_string(), true),
                                    ("className".to_string(), true),
                                    ("x".to_string(), true),
                                    ("y".to_string(), true),
                                ],
                                logical_field_count: None,
                                mutable_flag: crate::parser::ast::MutableFlag::Immutable,
                            },
                        ))),
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
                other => panic!("expected the first hoisted optional binding, got {other:?}"),
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
                other => panic!("expected the second hoisted optional binding, got {other:?}"),
            }
            match &record_stmt.desc {
                StatementDesc::Variable(VariableDeclaration {
                    ident,
                    value:
                        Some(Expression {
                            desc: ExpressionDesc::CamlBlock(items, MutableFlag::Immutable, _),
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
fn js_flatten_and_mark_dead_materializes_strict_identity_optional_record_fields_like_ocaml() {
    let record = Ident::create_local("story");
    let deps = apply_js_flatten_and_mark_dead_pass(
        DepsProgram {
            program: Program::new(
                vec![Statement::variable(VariableDeclaration {
                    ident: record,
                    value: Some(Expression::new(ExpressionDesc::CamlBlock(
                        vec![
                            Expression::string("STORY#id"),
                            Expression::new(ExpressionDesc::OptionalBlock(
                                Box::new(Expression::string("IDLE")),
                                true,
                            )),
                            Expression::new(ExpressionDesc::OptionalBlock(
                                Box::new(Expression::bool(true)),
                                true,
                            )),
                        ],
                        MutableFlag::Immutable,
                        Box::new(TagInfo::Record(Box::new(
                            crate::lambda::lam_tag_info::RecordTag {
                                fields: vec![
                                    ("pk".to_string(), false),
                                    ("exportStatus".to_string(), true),
                                    ("instantPlayerEligible".to_string(), true),
                                ],
                                logical_field_count: None,
                                mutable_flag: crate::parser::ast::MutableFlag::Immutable,
                            },
                        ))),
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

    let [record_stmt] = deps.program.block.as_slice() else {
        panic!("expected the pass to return a single transparent block");
    };
    match &record_stmt.desc {
        StatementDesc::Block(bindings) => {
            let [export_status_stmt, instant_player_stmt, record_stmt] = bindings.as_slice() else {
                panic!("expected the hoisted optional bindings plus the record binding");
            };
            match &export_status_stmt.desc {
                StatementDesc::Variable(VariableDeclaration {
                    ident,
                    value:
                        Some(Expression {
                            desc: ExpressionDesc::OptionalBlock(_, true),
                            ..
                        }),
                    ..
                }) => assert_eq!(ident.name(), "story_exportStatus"),
                other => panic!("expected the exportStatus hoist, got {other:?}"),
            }
            match &instant_player_stmt.desc {
                StatementDesc::Variable(VariableDeclaration {
                    ident,
                    value:
                        Some(Expression {
                            desc: ExpressionDesc::OptionalBlock(_, true),
                            ..
                        }),
                    ..
                }) => assert_eq!(ident.name(), "story_instantPlayerEligible"),
                other => panic!("expected the instantPlayerEligible hoist, got {other:?}"),
            }
            match &record_stmt.desc {
                StatementDesc::Variable(VariableDeclaration {
                    ident,
                    value:
                        Some(Expression {
                            desc: ExpressionDesc::CamlBlock(items, MutableFlag::Immutable, _),
                            ..
                        }),
                    ..
                }) => {
                    assert!(ident.same(&record));
                    assert!(matches!(
                        items.as_slice(),
                        [
                            Expression {
                                desc: ExpressionDesc::Str(_),
                                ..
                            },
                            Expression {
                                desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(export_status)),
                                ..
                            },
                            Expression {
                                desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(instant_player)),
                                ..
                            }
                        ] if export_status.name() == "story_exportStatus"
                            && instant_player.name() == "story_instantPlayerEligible"
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
                    ident: record,
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
                                Box::new(TagInfo::Record(Box::new(
                                    crate::lambda::lam_tag_info::RecordTag {
                                        fields: vec![
                                            ("xx".to_string(), false),
                                            ("yy".to_string(), false),
                                        ],
                                        logical_field_count: None,
                                        mutable_flag: crate::parser::ast::MutableFlag::Immutable,
                                    },
                                ))),
                            )),
                        ],
                        MutableFlag::Immutable,
                        Box::new(TagInfo::Record(Box::new(
                            crate::lambda::lam_tag_info::RecordTag {
                                fields: vec![("a".to_string(), false), ("b".to_string(), false)],
                                logical_field_count: None,
                                mutable_flag: crate::parser::ast::MutableFlag::Immutable,
                            },
                        ))),
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
                    desc: ExpressionDesc::CamlBlock(items, MutableFlag::Immutable, _),
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
                        desc: ExpressionDesc::CamlBlock(inner, MutableFlag::Immutable, _),
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
        other => {
            panic!("expected the alias-bound deep-constant record to stay inline, got {other:?}")
        }
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
                                ident: unused,
                                value: Some(Expression::number(Number::int(1))),
                                property: LetKind::Strict,
                                ident_info: IdentInfo::default(),
                            }),
                            Statement::variable(VariableDeclaration {
                                ident: used,
                                value: Some(Expression::number(Number::int(2))),
                                property: LetKind::Strict,
                                ident_info: IdentInfo::default(),
                            }),
                            Statement::return_(Expression::var(used)),
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
fn top_level_record_field_assignments_on_pure_fresh_literals_collapse_to_rhs_effects() {
    let mut compiler = LambdaCompiler::new();
    let lam = Lambda::seq(
        Lambda::prim(
            Primitive::Psetfield(0, SetFieldDbgInfo::RecordSet("x".to_string())),
            vec![
                Lambda::prim(
                    Primitive::Pmakeblock(
                        TagInfo::Record(Box::new(crate::lambda::lam_tag_info::RecordTag {
                            fields: vec![("x".to_string(), false)],
                            logical_field_count: None,
                            mutable_flag: crate::parser::ast::MutableFlag::Mutable,
                        })),
                        Mutable::Immutable,
                    ),
                    vec![Lambda::const_(Constant::int(3))],
                    LamLoc::NONE,
                ),
                Lambda::Lsequence(
                    Box::new(Lambda::prim(
                        Primitive::PrawJsCode(crate::lambda::lam_primitive::JsRawInfo {
                            code: "console.log(\"hi\")".to_string(),
                            is_stmt: true,
                        }),
                        vec![],
                        LamLoc::NONE,
                    )),
                    Box::new(Lambda::const_(Constant::int(2))),
                ),
            ],
            LamLoc::NONE,
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

    let output = compile_test_source_to_js(source, "fresh_record_set.res").unwrap();
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

    let output = compile_test_source_to_js(source, "fresh_record_set_impure.res").unwrap();
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
fn source_json_template_with_interpolation_is_a_plain_tagged_template_like_ocaml() {
    let source = r#"
let x = json`some random ${"string"}`
"#;

    let error = compile_test_source_to_js(source, "json_template_test.res")
        .unwrap_err()
        .to_string();

    // Upstream #8875: `json` is no longer a literal, so an interpolated
    // `json` template is an ordinary tagged template call
    // (super_errors/expected/syntaxErrors_json_interpolation.res.expected).
    assert!(
        error.contains("The value json can't be found"),
        "expected an unbound `json` tag, got:\n{error}"
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

    let output = compile_test_source_to_js(source, "fib_ref_alias_test.res").unwrap();

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
fn lassign_expression_lowers_to_statement_prelude_and_unit_value() {
    let mut compiler = LambdaCompiler::new();
    let cell = Ident::create_local("cell");
    let compiled = compiler.compile_expr_tree(&Lambda::Lassign(
        cell,
        Box::new(Lambda::prim(
            Primitive::Paddint,
            vec![Lambda::var(cell), Lambda::const_(Constant::int(1))],
            LamLoc::NONE,
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
    let block = compiler.compile_let_binding_tree(
        LetKind::Strict,
        &v,
        &Lambda::Lassign(
            u,
            Box::new(Lambda::prim(
                Primitive::Paddint,
                vec![Lambda::var(u), Lambda::const_(Constant::int(1))],
                LamLoc::NONE,
            )),
        ),
    );
    assert_eq!(print_block(&block), "u = u + 1 | 0;\n\nlet v;");
}

#[test]
fn lowers_pis_poly_var_block_to_typeof_object_check() {
    let mut compiler = LambdaCompiler::new();
    let value = Ident::create_local("value");
    let compiled = compiler.compile_expr_tree(&Lambda::prim(
        Primitive::PisPolyVarBlock,
        vec![Lambda::var(value)],
        LamLoc::NONE,
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
fn lowers_pmulint_by_positive_power_of_two_to_shift() {
    let value = Ident::create_local("value");
    let expr = int32_mul(Expression::var(value), int_expr(2));

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
        Expression::var(value),
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
    let compiled = compiler.compile_expr_tree(&Lambda::prim(
        Primitive::PsomeNotNest,
        vec![Lambda::var(value)],
        LamLoc::NONE,
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
    let compiled = compiler.compile_expr_tree(&Lambda::prim(
        Primitive::Psome,
        vec![Lambda::const_(Constant::int(3))],
        LamLoc::NONE,
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
            vec![Lambda::var(value)],
            LamLoc::NONE,
        )],
        LamLoc::NONE,
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
    let compiled = compiler.compile_expr_tree(&Lambda::prim(
        Primitive::PvalFromOption,
        vec![Lambda::var(value)],
        LamLoc::NONE,
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
    let compiled = compiler.compile_expr_tree(&Lambda::prim(
        Primitive::PnullToOpt,
        vec![Lambda::const_(Constant::string("value"))],
        LamLoc::NONE,
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
            desc: ExpressionDesc::Str(txt),
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
    let compiled = compiler.compile_expr_tree(&Lambda::prim(
        Primitive::PnullUndefinedToOpt,
        vec![Lambda::const_(Constant::string("value"))],
        LamLoc::NONE,
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
            desc: ExpressionDesc::Str(txt),
            ..
        }] if txt == "value"
    ));
    assert_eq!(
        print_expression(&compiled.expr),
        "Primitive_option.fromNullable(\"value\")"
    );
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
        &Expression::var(module_value),
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
        other => {
            panic!("expected module field access to lower to converted static index, got {other:?}")
        }
    }

    assert_eq!(print_expression(&expr), "Js_promise2.$$catch");
}

#[test]
fn lowers_record_pfield_to_positioned_static_access_like_ocaml() {
    let mut compiler = LambdaCompiler::new();
    let record = Ident::create_local("record");
    let expr = compiler.compile_field_access(
        2,
        &FieldDbgInfo::Record {
            name: "field".to_string(),
        },
        &Expression::var(record),
    );

    match &expr.desc {
        ExpressionDesc::StaticIndex(target, field, Some(index)) => {
            assert_eq!(field, "field");
            assert_eq!(*index, 2);
            assert!(matches!(
                target.as_ref(),
                Expression {
                    desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                    ..
                } if id.same(&record)
            ));
        }
        other => panic!("expected record field access to keep field position, got {other:?}"),
    }

    assert_eq!(print_expression(&expr), "record.field");
}

#[test]
fn lowers_extension_pfield_to_named_payload_property_like_ocaml() {
    let mut compiler = LambdaCompiler::new();
    let exn = Ident::create_local("exn");
    let expr = compiler.compile_field_access(1, &FieldDbgInfo::Extension, &Expression::var(exn));

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
            vec![Expression::var(eq)],
            MutableFlag::Immutable,
            Box::new(TagInfo::Module(vec!["Eq".to_string()])),
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
        },
        &Expression::new(ExpressionDesc::CamlBlock(
            vec![Expression::var(value)],
            MutableFlag::Immutable,
            Box::new(TagInfo::Record(Box::new(
                crate::lambda::lam_tag_info::RecordTag {
                    fields: vec![("d".to_string(), false)],
                    logical_field_count: None,
                    mutable_flag: crate::parser::ast::MutableFlag::Immutable,
                },
            ))),
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
            vec![Expression::var(head), Expression::var(tail)],
            MutableFlag::Immutable,
            Box::new(TagInfo::Constructor(Box::new(
                crate::lambda::lam_tag_info::ConstructorTag {
                    name: "::".to_string(),
                    num_nonconst: 1,
                    runtime: Box::new(crate::types::TaggedBlock {
                        tag: crate::types::VariantTag {
                            name: "::".to_string(),
                            literal: crate::types::VariantLiteralTag::String("::".to_string()),
                        },
                        tag_name: None,
                    }),
                },
            ))),
        )),
    );
    let tail_expr = compiler.compile_field_access(
        1,
        &FieldDbgInfo::Cons,
        &Expression::new(ExpressionDesc::CamlBlock(
            vec![Expression::var(head), Expression::var(tail)],
            MutableFlag::Immutable,
            Box::new(TagInfo::Constructor(Box::new(
                crate::lambda::lam_tag_info::ConstructorTag {
                    name: "::".to_string(),
                    num_nonconst: 1,
                    runtime: Box::new(crate::types::TaggedBlock {
                        tag: crate::types::VariantTag {
                            name: "::".to_string(),
                            literal: crate::types::VariantLiteralTag::String("::".to_string()),
                        },
                        tag_name: None,
                    }),
                },
            ))),
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
                Expression::var(payload),
            ],
            MutableFlag::Immutable,
            Box::new(TagInfo::Extension),
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
    let tag =
        compiler.compile_field_access(0, &FieldDbgInfo::PolyVarTag, &Expression::var(variant));
    let value =
        compiler.compile_field_access(1, &FieldDbgInfo::PolyVarContent, &Expression::var(variant));

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
        vec![Expression::string("Tag"), Expression::var(payload)],
        MutableFlag::Immutable,
        Box::new(TagInfo::PolyVar("Tag".to_string())),
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
fn external_shadow_pass_reads_global_through_global_this_where_binding_is_in_scope() {
    let process = Ident::create_local("process");
    let proc = Ident::create_local("proc");
    let global_process = Ident::create_persistent("process");
    let deps = DepsProgram {
        program: Program::new(
            vec![
                Statement::variable(VariableDeclaration {
                    ident: process,
                    value: Some(Expression::var(global_process)),
                    property: LetKind::Strict,
                    ident_info: IdentInfo::default(),
                }),
                Statement::variable(VariableDeclaration {
                    ident: proc,
                    value: Some(Expression::var(global_process)),
                    property: LetKind::Strict,
                    ident_info: IdentInfo::default(),
                }),
            ],
            vec![],
        ),
        modules: vec![],
        side_effect: None,
    };

    // A toplevel `let process` is in scope in its whole block, so both
    // reads of the global go through `globalThis`.
    let rewritten = apply_external_shadow_pass(deps);
    let [first, second] = rewritten.program.block.as_slice() else {
        panic!("expected two variable declarations");
    };
    for stmt in [first, second] {
        match &stmt.desc {
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
            other => panic!("expected the initializer to read globalThis.process, got {other:?}"),
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
                    ident: exported,
                    value: Some(Expression::number(Number::int(2))),
                    property: LetKind::Strict,
                    ident_info: IdentInfo::default(),
                }),
            ],
            vec![exported],
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
fn one_unit_arg_functions_lower_to_zero_arg_js_functions() {
    let mut compiler = LambdaCompiler::new();
    let compiled = compiler.compile_expr_tree(&Lambda::function_(
        1,
        vec![Ident::create_local("param")],
        Lambda::unit(),
        FunctionAttribute {
            one_unit_arg: true,
            ..FunctionAttribute::default()
        },
        LamLoc::NONE,
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
            func,
            Lambda::function_(
                1,
                vec![param],
                Lambda::var(func),
                FunctionAttribute::default(),
                LamLoc::NONE,
            ),
        )],
        Lambda::unit(),
    );

    let compiled = compiler.compile_expr_tree(&lam);
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
                even,
                Lambda::function_(
                    1,
                    vec![n],
                    Lambda::var(odd),
                    FunctionAttribute::default(),
                    LamLoc::NONE,
                ),
            ),
            (
                odd,
                Lambda::function_(
                    1,
                    vec![n],
                    Lambda::var(even),
                    FunctionAttribute::default(),
                    LamLoc::NONE,
                ),
            ),
        ],
        Lambda::unit(),
    );

    let compiled = compiler.compile_expr_tree(&lam);
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
            make,
            Lambda::let_(
                LetKind::Strict,
                make_internal,
                Lambda::function_(
                    1,
                    vec![param],
                    Lambda::var(make),
                    FunctionAttribute::default(),
                    LamLoc::NONE,
                ),
                Lambda::let_(
                    LetKind::Strict,
                    make_alias,
                    Lambda::let_(
                        LetKind::Strict,
                        component,
                        Lambda::function_(
                            1,
                            vec![props],
                            Lambda::apply(
                                Lambda::var(make_internal),
                                vec![Lambda::var(props)],
                                ApInfo {
                                    loc: LamLoc::NONE,
                                    status: ApplyStatus::Na,
                                },
                            ),
                            FunctionAttribute::default(),
                            LamLoc::NONE,
                        ),
                        Lambda::var(component),
                    ),
                    Lambda::var(make_alias),
                ),
            ),
        )],
        Lambda::unit(),
    );

    let compiled = compiler.compile_expr_tree(&lam);
    let rendered = print_block(&compiled.prelude);
    let make_decl = compiled.prelude.iter().find_map(|stmt| match &stmt.desc {
        StatementDesc::Variable(VariableDeclaration { ident, value, .. }) if ident.same(&make) => {
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
            xx,
            Lambda::prim(
                Primitive::Pmakeblock(
                    TagInfo::record(
                        vec![("xx".to_string(), false)],
                        crate::parser::ast::MutableFlag::Immutable,
                    ),
                    Mutable::Immutable,
                ),
                vec![Lambda::var(xx)],
                LamLoc::NONE,
            ),
        )],
        Lambda::unit(),
    );

    let compiled = compiler.compile_expr_tree(&lam);
    let [declare, assign] = compiled.prelude.as_slice() else {
        panic!("expected a dummy-object declaration followed by a field update");
    };

    let StatementDesc::Variable(VariableDeclaration {
        ident,
        value:
            Some(Expression {
                desc: ExpressionDesc::Object(props),
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
            desc: ExpressionDesc::StaticIndex(target, field, Some(index)),
            ..
        } if field == "xx"
            && *index == 0
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
fn mutually_recursive_record_bindings_lower_to_runtime_update_dummy_calls() {
    let mut compiler = LambdaCompiler::new();
    let a = Ident::create_local("a");
    let b = Ident::create_local("b");
    let lam = Lambda::letrec(
        vec![
            (
                a,
                Lambda::prim(
                    Primitive::Pmakeblock(
                        TagInfo::record(
                            vec![("b".to_string(), false)],
                            crate::parser::ast::MutableFlag::Immutable,
                        ),
                        Mutable::Immutable,
                    ),
                    vec![Lambda::var(b)],
                    LamLoc::NONE,
                ),
            ),
            (
                b,
                Lambda::prim(
                    Primitive::Pmakeblock(
                        TagInfo::record(
                            vec![("a".to_string(), false)],
                            crate::parser::ast::MutableFlag::Immutable,
                        ),
                        Mutable::Immutable,
                    ),
                    vec![Lambda::var(a)],
                    LamLoc::NONE,
                ),
            ),
        ],
        Lambda::unit(),
    );

    let rendered = print_block(&compiler.compile_expr_tree(&lam).prelude);

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
    let tailcall = Lambda::Lapply(Box::new(Apply {
        ap_func: Box::new(Lambda::var(loop_)),
        ap_args: vec![
            Lambda::const_(Constant::JsFalse),
            Lambda::var(next),
            Lambda::var(next),
        ],
        ap_info: ApInfo {
            loc: LamLoc::NONE,
            status: ApplyStatus::Na,
        },
    }));
    let lam = Lambda::letrec(
        vec![(
            loop_,
            Lambda::function_(
                3,
                vec![flag, acc, next],
                Lambda::if_(Lambda::var(flag), tailcall, Lambda::var(acc)),
                FunctionAttribute::default(),
                LamLoc::NONE,
            ),
        )],
        Lambda::unit(),
    );

    let compiled = compiler.compile_expr_tree(&lam);
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
fn recursive_int_switch_fallthrough_handler_breaks_before_tail_loop_continue() {
    let mut compiler = LambdaCompiler::new();
    let loop_ = Ident::create_local("loop");
    let tag = Ident::create_local("tag");
    let next = Ident::create_local("next");
    let tailcall = Lambda::Lapply(Box::new(Apply {
        ap_func: Box::new(Lambda::var(loop_)),
        ap_args: vec![Lambda::var(next), Lambda::var(next)],
        ap_info: ApInfo {
            loc: LamLoc::NONE,
            status: ApplyStatus::Na,
        },
    }));
    let body = Lambda::LstaticCatch(
        Box::new(Lambda::Lswitch(
            Box::new(Lambda::var(tag)),
            Box::new(LambdaSwitch {
                sw_consts_full: false,
                sw_consts: vec![
                    (
                        crate::lambda::SwitchKey::Int(1),
                        Lambda::static_raise(1, Vec::new()),
                    ),
                    (
                        crate::lambda::SwitchKey::Int(2),
                        Lambda::static_raise(1, Vec::new()),
                    ),
                ],
                sw_blocks_full: true,
                sw_blocks: vec![],
                sw_failaction: Some(Box::new(Lambda::var(tag))),
                sw_dispatch: crate::lambda::SwitchDispatch::Direct,
            }),
        )),
        (1, vec![]),
        Box::new(tailcall),
    );
    let lam = Lambda::letrec(
        vec![(
            loop_,
            Lambda::function_(
                2,
                vec![tag, next],
                body,
                FunctionAttribute::default(),
                LamLoc::NONE,
            ),
        )],
        Lambda::unit(),
    );

    let rendered = print_block(&compiler.compile_expr_tree(&lam).prelude);

    assert!(
        rendered.contains("case 2 :\n        break;\n      default:"),
        "expected OCaml-style break before the shared tail-loop handler:\n{rendered}"
    );
}

#[test]
fn recursive_string_switch_fallthrough_handler_breaks_before_tail_loop_continue() {
    let mut compiler = LambdaCompiler::new();
    let strip = Ident::create_local("strip");
    let ch = Ident::create_local("ch");
    let next = Ident::create_local("next");
    let tailcall = Lambda::Lapply(Box::new(Apply {
        ap_func: Box::new(Lambda::var(strip)),
        ap_args: vec![Lambda::var(next), Lambda::var(next)],
        ap_info: ApInfo {
            loc: LamLoc::NONE,
            status: ApplyStatus::Na,
        },
    }));
    let body = Lambda::LstaticCatch(
        Box::new(Lambda::LstringSwitch(
            Box::new(Lambda::var(ch)),
            vec![
                ("!".to_string(), Lambda::static_raise(1, Vec::new())),
                ("?".to_string(), Lambda::static_raise(1, Vec::new())),
            ],
            Some(Box::new(Lambda::var(ch))),
        )),
        (1, vec![]),
        Box::new(tailcall),
    );
    let lam = Lambda::letrec(
        vec![(
            strip,
            Lambda::function_(
                2,
                vec![ch, next],
                body,
                FunctionAttribute::default(),
                LamLoc::NONE,
            ),
        )],
        Lambda::unit(),
    );

    let rendered = print_block(&compiler.compile_expr_tree(&lam).prelude);

    assert!(
        rendered.contains("case \"?\" :\n        break;\n      default:"),
        "expected OCaml-style break before the shared tail-loop handler:\n{rendered}"
    );
}

#[test]
fn recursive_self_tailcalls_lower_sequands_to_looping_while_bodies() {
    let mut compiler = LambdaCompiler::new();
    let loop_ = Ident::create_local("loop");
    let flag = Ident::create_local("flag");
    let tailcall = Lambda::Lapply(Box::new(Apply {
        ap_func: Box::new(Lambda::var(loop_)),
        ap_args: vec![Lambda::const_(Constant::JsFalse)],
        ap_info: ApInfo {
            loc: LamLoc::NONE,
            status: ApplyStatus::Na,
        },
    }));
    let lam = Lambda::letrec(
        vec![(
            loop_,
            Lambda::function_(
                1,
                vec![flag],
                Lambda::prim(
                    Primitive::Psequand,
                    vec![Lambda::var(flag), tailcall],
                    LamLoc::NONE,
                ),
                FunctionAttribute::default(),
                LamLoc::NONE,
            ),
        )],
        Lambda::unit(),
    );

    let compiled = compiler.compile_expr_tree(&lam);
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
    let tailcall = Lambda::Lapply(Box::new(Apply {
        ap_func: Box::new(Lambda::var(loop_)),
        ap_args: vec![Lambda::const_(Constant::JsFalse)],
        ap_info: ApInfo {
            loc: LamLoc::NONE,
            status: ApplyStatus::Na,
        },
    }));
    let lam = Lambda::letrec(
        vec![(
            loop_,
            Lambda::function_(
                1,
                vec![flag],
                Lambda::prim(
                    Primitive::Psequor,
                    vec![Lambda::var(flag), tailcall],
                    LamLoc::NONE,
                ),
                FunctionAttribute::default(),
                LamLoc::NONE,
            ),
        )],
        Lambda::unit(),
    );

    let compiled = compiler.compile_expr_tree(&lam);
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
    // Allocate from the compiler's generator so the stamps cannot collide
    // with the loop parameters it creates, whatever ran before on this thread.
    let loop_ = compiler.id_gen.create("loop");
    let a = compiler.id_gen.create("a");
    let b = compiler.id_gen.create("b");
    let flag = compiler.id_gen.create("flag");
    let tailcall = Lambda::Lapply(Box::new(Apply {
        ap_func: Box::new(Lambda::var(loop_)),
        ap_args: vec![
            Lambda::var(b),
            Lambda::var(a),
            Lambda::const_(Constant::JsFalse),
        ],
        ap_info: ApInfo {
            loc: LamLoc::NONE,
            status: ApplyStatus::Na,
        },
    }));
    let lam = Lambda::letrec(
        vec![(
            loop_,
            Lambda::function_(
                3,
                vec![a, b, flag],
                Lambda::if_(Lambda::var(flag), tailcall, Lambda::var(a)),
                FunctionAttribute::default(),
                LamLoc::NONE,
            ),
        )],
        Lambda::unit(),
    );

    let compiled = compiler.compile_expr_tree(&lam);
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
    let f = compiler.id_gen.create("f");
    let n = compiler.id_gen.create("n");
    let acc = compiler.id_gen.create("acc");
    let body = Lambda::if_(
        Lambda::var(n),
        Lambda::Lapply(Box::new(Apply {
            ap_func: Box::new(Lambda::var(f)),
            ap_args: vec![
                Lambda::prim(
                    Primitive::Psubint,
                    vec![Lambda::var(n), Lambda::const_(Constant::int(1))],
                    LamLoc::NONE,
                ),
                Lambda::function_(
                    1,
                    vec![compiler.id_gen.create("param")],
                    Lambda::var(acc),
                    FunctionAttribute::default(),
                    LamLoc::NONE,
                ),
            ],
            ap_info: ApInfo {
                loc: LamLoc::NONE,
                status: ApplyStatus::Na,
            },
        })),
        Lambda::var(acc),
    );
    let lam = Lambda::letrec(
        vec![(
            f,
            Lambda::function_(
                2,
                vec![n, acc],
                body,
                FunctionAttribute::default(),
                LamLoc::NONE,
            ),
        )],
        Lambda::unit(),
    );

    // compile_expr is an internal entry point: unlike compile_program, it
    // does not seed the lowering generator from the input Lambda. Construct
    // this fixture with that same generator, as OCaml's Ext_ident.create does.
    assert!(
        compiler.id_gen.current_stamp() >= {
            let mut a = LamArena::new();
            let l = a.import(&lam);
            crate::lambda::lam_beta_reduce::max_ident_stamp_in_lambda(&a, l)
        }
    );
    let compiled = compiler.compile_expr_tree(&lam);
    let rendered = print_block(&compiled.prelude);
    let alias_start = rendered
        .find("let acc = _acc;")
        .unwrap_or_else(|| panic!("expected acc alias in loop body:\n{rendered}"));
    let alias_next = rendered
        .find("let n = _n;")
        .unwrap_or_else(|| panic!("expected n alias in loop body:\n{rendered}"));
    let assign_start = rendered
        .find("_acc =")
        .unwrap_or_else(|| panic!("expected acc reassignment in loop body:\n{rendered}"));
    let assign_next = rendered
        .find("_n =")
        .unwrap_or_else(|| panic!("expected n reassignment in loop body:\n{rendered}"));

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
fn recursive_function_bindings_lower_to_looping_while_bodies() {
    let mut compiler = LambdaCompiler::new();
    let loop_ = Ident::create_local("loop");
    let flag = Ident::create_local("flag");
    let acc = Ident::create_local("acc");
    let next = Ident::create_local("next");
    let tailcall = Lambda::Lapply(Box::new(Apply {
        ap_func: Box::new(Lambda::var(loop_)),
        ap_args: vec![
            Lambda::const_(Constant::JsFalse),
            Lambda::var(next),
            Lambda::var(next),
        ],
        ap_info: ApInfo {
            loc: LamLoc::NONE,
            status: ApplyStatus::Na,
        },
    }));
    let lam = Lambda::letrec(
        vec![(
            loop_,
            Lambda::function_(
                3,
                vec![flag, acc, next],
                Lambda::if_(Lambda::var(flag), tailcall, Lambda::var(acc)),
                FunctionAttribute::default(),
                LamLoc::NONE,
            ),
        )],
        Lambda::var(loop_),
    );

    let simplified = simplify_tree_for_js_backend(&lam);
    let compiled = compiler.compile_expr_tree(&simplified);
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
    let tailcall = Lambda::Lapply(Box::new(Apply {
        ap_func: Box::new(Lambda::var(loop_)),
        ap_args: vec![Lambda::var(value)],
        ap_info: ApInfo {
            loc: LamLoc::NONE,
            status: ApplyStatus::Na,
        },
    }));
    let body = Lambda::Lswitch(
        Box::new(Lambda::var(value)),
        Box::new(LambdaSwitch {
            sw_consts_full: true,
            sw_consts: vec![(
                crate::lambda::SwitchKey::Constructor(
                    crate::types::VariantConstructorCase::Constant(crate::types::VariantTag {
                        name: "Empty".to_string(),
                        literal: crate::types::VariantLiteralTag::String("Empty".to_string()),
                    }),
                ),
                Lambda::const_(Constant::int(0)),
            )],
            sw_blocks_full: true,
            sw_blocks: vec![(
                crate::lambda::SwitchKey::Constructor(crate::types::VariantConstructorCase::Block(
                    crate::types::VariantBlock::Tagged(crate::types::TaggedBlock {
                        tag: crate::types::VariantTag {
                            name: "Node".to_string(),
                            literal: crate::types::VariantLiteralTag::String("Node".to_string()),
                        },
                        tag_name: None,
                    }),
                )),
                tailcall,
            )],
            sw_failaction: None,
            sw_dispatch: crate::lambda::SwitchDispatch::Variant(
                crate::types::VariantMatchingFacts {
                    tag_name: None,
                    block_types: vec![],
                    literal_tags: vec![crate::types::VariantLiteralTag::String(
                        "Empty".to_string().clone(),
                    )],
                },
            ),
        }),
    );
    let lam = Lambda::letrec(
        vec![(
            loop_,
            Lambda::function_(
                1,
                vec![value],
                body,
                FunctionAttribute::default(),
                LamLoc::NONE,
            ),
        )],
        Lambda::unit(),
    );

    let compiled = compiler.compile_expr_tree(&lam);
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

mod lam_coercion_tests;
mod lam_compile_external_tests;
mod lam_compile_integration_tests;
mod lam_compile_staticcatch_tests;
mod lam_compile_switch_tests;

fn raise_boom() -> Lambda {
    Lambda::prim(
        Primitive::Praise,
        vec![Lambda::const_(Constant::string("boom"))],
        LamLoc::NONE,
    )
}

/// A static catch, which allocates an `exit` identifier when compiled.
fn allocating_catch() -> Lambda {
    Lambda::LstaticCatch(
        Box::new(Lambda::LstaticRaise(7, vec![])),
        (7, vec![]),
        Box::new(Lambda::const_(Constant::int(1))),
    )
}

/// The stamp the next fresh identifier gets after compiling `compile`.
fn next_stamp_after(compile: impl FnOnce(&mut LambdaCompiler)) -> i32 {
    let mut compiler = LambdaCompiler::new();
    compile(&mut compiler);
    compiler.fresh_ident("probe").stamp()
}

/// js_output.ml:118-138 `append_output`, through lam_compile.ml:1867-1877
/// (`Llet`) and 1905-1910 (`Lsequence`): a raise finishes the output in an
/// `Assign`, `Declare` or `EffectCall` continuation, and what follows is
/// dropped from the JavaScript but still compiled, so it allocates the
/// identifiers it would have allocated.
#[test]
fn finished_output_drops_but_compiles_what_follows() {
    let result = Ident::create_local("result");
    let bound = Ident::create_local("bound");
    let seq = Lambda::seq(raise_boom(), allocating_catch());
    let let_ = Lambda::let_(LetKind::Strict, bound, raise_boom(), allocating_catch());

    for lam in [&seq, &let_] {
        let mut compiler = LambdaCompiler::new();
        let assign = compiler.compile_assign_to_target_output_tree(&result, lam);
        assert_eq!(assign.finished, OutputFinished::True);
        let [stmt] = assign.block.as_slice() else {
            panic!("expected only the throw, got {:?}", assign.block);
        };
        assert!(matches!(stmt.desc, StatementDesc::Throw(_)));

        let effect = LambdaCompiler::new().compile_effect_block_output_tree(lam);
        assert_eq!(effect.finished, OutputFinished::True);
        assert_eq!(effect.block.len(), 1);

        let declare =
            LambdaCompiler::new().compile_let_binding_output_tree(LetKind::Strict, &result, lam);
        assert_eq!(declare.finished, OutputFinished::True);
        assert_eq!(declare.block.len(), 1);

        let compiled = LambdaCompiler::new().compile_expr_tree(lam);
        assert_eq!(compiled.finished, OutputFinished::True);
    }

    // The dropped catch still allocated its `exit` identifier.
    let raise_only = next_stamp_after(|c| {
        c.compile_assign_to_target_output_tree(&result, &raise_boom());
    });
    let raise_then_catch = next_stamp_after(|c| {
        c.compile_assign_to_target_output_tree(&result, &seq);
    });
    assert!(raise_then_catch > raise_only);
}

/// lam_compile.ml:1063-1101: a static catch is `append_output (make
/// declares) (append_output lbody (make cases))`, so a body that raises
/// finishes the catch, and its handler is compiled and dropped.
#[test]
fn static_catch_carries_its_body_finished_flag() {
    let result = Ident::create_local("result");
    let catch = Lambda::LstaticCatch(
        Box::new(raise_boom()),
        (3, vec![]),
        Box::new(allocating_catch()),
    );
    let mut compiler = LambdaCompiler::new();
    let output = compiler.compile_assign_to_target_output_tree(&result, &catch);
    assert_eq!(output.finished, OutputFinished::True);
    assert!(
        !output
            .block
            .iter()
            .any(|stmt| matches!(stmt.desc, StatementDesc::If(..))),
        "the handler dispatch is dropped: {:?}",
        output.block
    );
    let without_handler_allocation = next_stamp_after(|c| {
        c.compile_assign_to_target_output_tree(
            &result,
            &Lambda::LstaticCatch(
                Box::new(raise_boom()),
                (3, vec![]),
                Box::new(Lambda::const_(Constant::int(1))),
            ),
        );
    });
    let with_handler_allocation = next_stamp_after(|c| {
        c.compile_assign_to_target_output_tree(&result, &catch);
    });
    assert!(with_handler_allocation > without_handler_allocation);
}

/// Only `Praise`, `Lbreak` and `Lcontinue` finish an output outside a return
/// (lam_compile.ml:1682, 1934, 1949): an `if` whose branches both raise is
/// a plain `make`, so what follows it is kept.
#[test]
fn conditional_of_raises_is_not_finished() {
    let result = Ident::create_local("result");
    let cond = Ident::create_local("cond");
    let lam = Lambda::seq(
        Lambda::if_(Lambda::var(cond), raise_boom(), raise_boom()),
        Lambda::const_(Constant::int(2)),
    );
    let output = LambdaCompiler::new().compile_assign_to_target_output_tree(&result, &lam);
    assert_eq!(output.finished, OutputFinished::False);
    assert!(
        output.block.len() >= 2,
        "the assignment is kept: {:?}",
        output.block
    );
}

fn declared_exit_stamps(block: &Block) -> Vec<i32> {
    let mut stamps = vec![];
    for stmt in block {
        if let StatementDesc::Variable(declaration) = &stmt.desc {
            if declaration.ident.name() == "exit" {
                stamps.push(declaration.ident.stamp());
            }
        }
    }
    stamps
}

/// lam_compile.ml:521-539 `compile_recursive_lets_aux` folds the bindings
/// with `Ext_list.fold_right`, so the last binding is compiled first, and
/// joins the outputs with `append_output`.
#[test]
fn recursive_lets_compile_last_binding_first() {
    let first = Ident::create_local("first");
    let second = Ident::create_local("second");
    let lam = Lambda::Lletrec(
        vec![(first, allocating_catch()), (second, allocating_catch())],
        Box::new(Lambda::const_(Constant::int(0))),
    );
    let output = LambdaCompiler::new().compile_effect_block_output_tree(&lam);
    let stamps = declared_exit_stamps(&output.block);
    let [first_exit, second_exit] = stamps.as_slice() else {
        panic!("expected two exit declarations, got {:?}", output.block);
    };
    assert!(
        first_exit > second_exit,
        "the second binding allocates first: {stamps:?}"
    );
}

/// A recursive binding whose value raises finishes the group's output, and
/// `append_output` drops the bindings after it and the body, all of which
/// are still compiled.
#[test]
fn recursive_lets_carry_a_raising_binding_flag() {
    let first = Ident::create_local("first");
    let second = Ident::create_local("second");
    let lam = Lambda::Lletrec(
        vec![(first, raise_boom()), (second, allocating_catch())],
        Box::new(allocating_catch()),
    );
    let mut compiler = LambdaCompiler::new();
    let output = compiler.compile_effect_block_output_tree(&lam);
    assert_eq!(output.finished, OutputFinished::True);
    let [stmt] = output.block.as_slice() else {
        panic!("expected only the throw, got {:?}", output.block);
    };
    assert!(matches!(stmt.desc, StatementDesc::Throw(_)));
    let compiled = LambdaCompiler::new().compile_expr_tree(&lam);
    assert_eq!(compiled.finished, OutputFinished::True);
    let raise_only = next_stamp_after(|c| {
        c.compile_effect_block_output_tree(&Lambda::Lletrec(
            vec![(first, raise_boom())],
            Box::new(Lambda::const_(Constant::int(0))),
        ));
    });
    let with_dropped = next_stamp_after(|c| {
        c.compile_effect_block_output_tree(&lam);
    });
    assert!(with_dropped > raise_only);
}

fn call_of(callee: Ident) -> Lambda {
    Lambda::apply(Lambda::var(callee), vec![], test_apply_info())
}

/// lam_compile.ml:1533-1537: in a return continuation, an `if` whose
/// branches are plain values is `return e ? a : b`, which is finished; the
/// `S.if_` fallback is a `Js_output.make`, which is not, even when every
/// branch returns.
#[test]
fn return_if_is_finished_only_as_a_conditional_return() {
    let cond = Ident::create_local("cond");
    let callee = Ident::create_local("callee");
    let values = Lambda::if_(
        Lambda::var(cond),
        Lambda::const_(Constant::int(1)),
        Lambda::const_(Constant::int(2)),
    );
    let output = LambdaCompiler::new().compile_return_output_tree(&values);
    assert_eq!(output.finished, OutputFinished::True);

    // A static catch needs statements under `NeedValue`.
    let statements = Lambda::if_(
        Lambda::var(cond),
        allocating_catch(),
        Lambda::seq(call_of(callee), allocating_catch()),
    );
    let output = LambdaCompiler::new().compile_return_output_tree(&statements);
    assert_eq!(output.finished, OutputFinished::False);
}

/// A `return` finishes the output (js_output.ml:57-59), so a static catch
/// whose body returns drops its handler dispatch after compiling it
/// (lam_compile.ml:1063-1101).
#[test]
fn return_static_catch_drops_the_handler_of_a_returning_body() {
    let callee = Ident::create_local("callee");
    let catch = |handler: Lambda| {
        Lambda::LstaticCatch(
            Box::new(Lambda::seq(
                Lambda::if_(
                    Lambda::var(callee),
                    Lambda::LstaticRaise(5, vec![]),
                    Lambda::const_(Constant::int(0)),
                ),
                call_of(callee),
            )),
            (5, vec![]),
            Box::new(handler),
        )
    };
    let lam = catch(allocating_catch());
    let output = LambdaCompiler::new().compile_return_output_tree(&lam);
    assert_eq!(output.finished, OutputFinished::True);
    assert!(
        matches!(
            output.block.last().map(|stmt| &stmt.desc),
            Some(StatementDesc::Return(_))
        ),
        "the body's return ends the output: {:?}",
        output.block
    );
    let plain = next_stamp_after(|c| {
        c.compile_return_output_tree(&catch(Lambda::const_(Constant::int(1))));
    });
    let allocating = next_stamp_after(|c| {
        c.compile_return_output_tree(&lam);
    });
    assert!(allocating > plain, "the dropped handler is compiled");
}

/// lam_compile.ml:1320-1334 `compile_assign` appends the assignment to the
/// value's block without asking whether it ends in a `throw`; its output is
/// a plain `make`, so it does not finish what follows.
#[test]
fn assign_of_a_raise_keeps_its_assignment() {
    let target = Ident::create_local("target");
    let compiled =
        LambdaCompiler::new().compile_expr_tree(&Lambda::Lassign(target, Box::new(raise_boom())));
    assert_eq!(compiled.finished, OutputFinished::False);
    let [throw, assign] = compiled.prelude.as_slice() else {
        panic!(
            "expected the throw and the assignment, got {:?}",
            compiled.prelude
        );
    };
    assert!(matches!(throw.desc, StatementDesc::Throw(_)));
    assert!(matches!(assign.desc, StatementDesc::Exp(_)));
}

/// lam_compile.ml:222-238, 535-539: a `let rec` group is compiled as
/// `Lambda_scc.bind_rec` left it, with functions before values, and is not
/// split again.
#[test]
fn recursive_lets_put_functions_before_values_without_resplitting() {
    let value = Ident::create_local("value");
    let first = Ident::create_local("first");
    let second = Ident::create_local("second");
    let (first, first_lam) = test_function_calling(first, &first);
    let (second, second_lam) = test_function_calling(second, &second);
    let lam = Lambda::Lletrec(
        vec![
            (value, Lambda::const_(Constant::int(3))),
            (second, second_lam),
            (first, first_lam),
        ],
        Box::new(Lambda::const_(Constant::int(0))),
    );
    let output = LambdaCompiler::new().compile_effect_block_output_tree(&lam);
    let names: Vec<_> = output
        .block
        .iter()
        .filter_map(|stmt| match &stmt.desc {
            StatementDesc::Variable(declaration) => Some(declaration.ident.name().to_string()),
            _ => None,
        })
        .collect();
    assert_eq!(names, ["second", "first", "value"]);
}

/// lam_compile.ml:1232: compile_for builds the tuple `(compile_lambda
/// new_cxt start, compile_lambda new_cxt finish)`, which OCaml evaluates
/// right to left, so the finish bound allocates first; the emitted block
/// still puts the start bound's statements first (lines 1256-1270).
#[test]
fn for_loop_compiles_its_finish_bound_before_its_start_bound() {
    let index = Ident::create_local("i");
    let lam = Lambda::Lfor(
        index,
        Box::new(allocating_catch()),
        Box::new(allocating_catch()),
        crate::lambda::DirectionFlag::Upto,
        Box::new(Lambda::const_(Constant::JsUndefined { is_unit: true })),
    );
    let compiled = LambdaCompiler::new().compile_expr_tree(&lam);
    let stamps = declared_exit_stamps(&compiled.prelude);
    let [start_exit, finish_exit] = stamps.as_slice() else {
        panic!("expected two exit declarations, got {:?}", compiled.prelude);
    };
    assert!(
        start_exit > finish_exit,
        "the finish bound allocates first: {stamps:?}"
    );
}

/// lam_compile.ml:375-388 and 1581-1587: a recursive function's body is
/// compiled with `ret.id` set to the function itself, and only a call with
/// `Ident.same ret.id fn_id` becomes the loop; a call through an alias in
/// the same group stays a call.
#[test]
fn recursive_function_loops_only_on_calls_to_itself() {
    let compile = |callee_is_alias: bool| {
        let function = Ident::create_local("f");
        let alias = Ident::create_local("g");
        let target = if callee_is_alias { alias } else { function };
        let (function, function_lam) = test_function_calling(function, &target);
        let lam = Lambda::Lletrec(
            vec![(function, function_lam), (alias, Lambda::var(function))],
            Box::new(Lambda::const_(Constant::int(0))),
        );
        print_block(
            &LambdaCompiler::new()
                .compile_effect_block_output_tree(&lam)
                .block,
        )
    };
    assert!(compile(false).contains("while"), "{}", compile(false));
    let through_alias = compile(true);
    assert!(!through_alias.contains("while"), "{through_alias}");
}

/// compile_sequand / compile_sequor in a `Declare (_kind, v)` continuation
/// declare the target with `~kind:Variable` when the right side needs
/// statements (lam_compile.ml:1128-1135, 1168-1175).
#[test]
fn short_circuit_declaration_with_statements_is_a_variable() {
    let flag = Ident::create_local("flag");
    let target = Ident::create_local("target");
    let output = LambdaCompiler::new().compile_let_binding_output_tree(
        LetKind::Strict,
        &target,
        &Lambda::prim(
            Primitive::Psequand,
            vec![Lambda::var(flag), allocating_catch()],
            LamLoc::NONE,
        ),
    );
    let declaration = output
        .block
        .iter()
        .find_map(|stmt| match &stmt.desc {
            StatementDesc::Variable(declaration) if declaration.ident.same(&target) => {
                Some(declaration)
            }
            _ => None,
        })
        .expect("the target is declared");
    assert_eq!(declaration.property, LetKind::Variable);
}

/// lam_compile.ml:1689-1704: the arguments of `Pdebugger` are compiled in
/// `EffectCall Not_tail` before the statement (a literal unit compiles to
/// nothing), and the primitive's value is unit in every continuation.
#[test]
fn debugger_compiles_its_arguments_for_effect_before_the_statement() {
    let log = Ident::create_local("log");
    let effect = || {
        Lambda::apply(
            Lambda::var(log),
            vec![Lambda::const_(Constant::string("before"))],
            test_apply_info(),
        )
    };
    let debugger = |args| Lambda::prim(Primitive::Pdebugger, args, LamLoc::NONE);
    // One printed statement per element, so the layout between statements
    // (the JS printer's business) does not matter here.
    let statements = |block: &Block| -> Vec<String> {
        block
            .iter()
            .map(|statement| print_block(&vec![statement.clone()]).trim().to_string())
            .collect()
    };

    let mut compiler = LambdaCompiler::new();
    let block = compiler.compile_effect_block_tree(&debugger(vec![Lambda::unit()]));
    assert_eq!(statements(&block), ["debugger;"]);

    let mut compiler = LambdaCompiler::new();
    let block = compiler.compile_effect_block_tree(&debugger(vec![effect()]));
    assert_eq!(statements(&block), ["log(\"before\");", "debugger;"]);

    // NeedValue: the argument and the statement form the prelude, the value
    // is unit.
    let mut compiler = LambdaCompiler::new();
    let compiled = compiler.compile_expr_tree(&debugger(vec![effect()]));
    assert_eq!(
        statements(&compiled.prelude),
        ["log(\"before\");", "debugger;"]
    );
    assert!(matches!(
        compiled.expr.desc,
        ExpressionDesc::Undefined { is_unit: true }
    ));
    assert_eq!(compiled.finished, OutputFinished::False);

    // A control-flow argument is compiled exactly as it is for effect on its
    // own (`EffectCall Not_tail`), not as a value, then the statement follows.
    let cond = Ident::create_local("cond");
    let conditional = || Lambda::if_(Lambda::var(cond), effect(), Lambda::unit());
    let mut compiler = LambdaCompiler::new();
    let mut expected = statements(&compiler.compile_effect_block_tree(&conditional()));
    expected.push("debugger;".to_string());
    let mut compiler = LambdaCompiler::new();
    let block = compiler.compile_effect_block_tree(&debugger(vec![conditional()]));
    assert_eq!(statements(&block), expected);
}
