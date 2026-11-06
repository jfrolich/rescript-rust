// Port of compiler/gentype/TranslateTypeExprFromTypes.ml:1-761.

use crate::gentype::gen_type_common::{
    ArgType, Case as VariantCase, ClosedFlag, Dep, Field, Function, Ident, Label, LabelJs, Mutable,
    Optional, Payload, Type, create_variant, dep_to_string, ident, ident_with, is_number, unknown,
};
use crate::types::path::PathView;
use crate::types::asttypes::ArgLabel;
use crate::types::context::TypeContext;
use crate::types::path::Path;
use crate::types::type_expr::{RowDesc, RowField, TypeDesc, TypeExprRef};

#[derive(Debug, Clone)]
pub struct Translation {
    pub dependencies: Vec<Dep>,
    pub type_: Type,
}

fn type_expr_desc(ctx: &TypeContext, type_expr: &TypeExprRef) -> TypeDesc {
    // Mirrors direct `type_expr.desc` reads throughout
    // compiler/gentype/TranslateTypeExprFromTypes.ml. Rust stores type nodes in
    // TypeContext's arena, so descriptor access is explicit while preserving the
    // OCaml traversal order.
    let desc = ctx.get_desc(*type_expr);
    (*desc).clone()
}

pub fn remove_option(
    ctx: &TypeContext,
    label: &ArgLabel,
    type_expr: &TypeExprRef,
) -> Option<(String, TypeExprRef)> {
    // Mirrors compiler/gentype/TranslateTypeExprFromTypes.ml:5-12.
    match (type_expr_desc(ctx, type_expr), label) {
        (TypeDesc::Tconstr { path, args, .. }, ArgLabel::Optional(lbl))
            if matches!(path.view(), PathView::Pident(id) if id.name() == "option") && args.len() == 1 =>
        {
            Some((lbl.txt.clone(), args[0]))
        }
        (TypeDesc::Tlink(t), _) => remove_option(ctx, label, &t),
        _ => None,
    }
}

pub fn path_to_list(path: &Path) -> Vec<String> {
    // Mirrors compiler/gentype/TranslateTypeExprFromTypes.ml:14-22.
    match path.view() {
        PathView::Pident(id) if id.name().starts_with("Stdlib_") => {
            let name = id.name();
            vec![name[7..].to_string(), "Stdlib".to_string()]
        }
        PathView::Pident(id) => vec![id.name().to_string()],
        PathView::Pdot(p, s, _) => {
            let mut out = vec![s.to_string()];
            out.extend(path_to_list(p));
            out
        }
        PathView::Papply(_, _) => vec![],
    }
}

pub fn translate_obj_type(
    closed_flag: ClosedFlag,
    fields_translations: Vec<(String, Mutable, Translation)>,
) -> Translation {
    // Mirrors compiler/gentype/translate_type_expr_from_types.ml
    // `translate_obj_type`.
    let dependencies = fields_translations
        .iter()
        .flat_map(|(_, _, translation)| translation.dependencies.clone())
        .collect::<Vec<_>>();
    let fields = fields_translations
        .into_iter()
        .map(|(name, mutable_, translation)| {
            let t = translation.type_;
            let (optional, type_) = match t {
                Type::Option(type_) => (Optional::Optional, *type_),
                _ => (Optional::Mandatory, t),
            };
            Field {
                mutable_,
                name_js: name,
                optional,
                type_,
                doc_string: crate::gentype::gen_type_common::doc_string::empty,
            }
        })
        .collect::<Vec<_>>();

    Translation {
        dependencies,
        type_: Type::Object(closed_flag, fields),
    }
}

pub fn translate_constr(
    config: &crate::gentype::config::T,
    params_translation: &[Translation],
    path: &Path,
    type_env: &crate::gentype::type_env::T,
) -> Translation {
    // Mirrors compiler/gentype/translate_type_expr_from_types.ml:48-423.
    let stripped_path = crate::gentype::type_env::strip_current_module_prefix(path, type_env);
    let path = stripped_path.as_ref().unwrap_or(path);
    let mut path_list = path_to_list(path);
    path_list.reverse();
    let path_list: Vec<&str> = path_list.iter().map(String::as_str).collect();
    let builtin = |type_args: Vec<Type>, name: &str| ident_with(true, type_args, name);
    let with_type = |param: &Translation, type_: Type| Translation {
        dependencies: param.dependencies.clone(),
        type_,
    };
    use crate::gentype::gen_type_common as common;

    match (path_list.as_slice(), params_translation) {
        (["bool"], []) => tr(common::boolean_t()),
        (["int"] | ["float"], []) => tr(common::number_t()),
        (["string"] | ["Stdlib", "String", "t"], []) => tr(common::string_t()),
        (["Stdlib", "BigInt", "t"], []) => tr(common::bigint_t()),
        (["Stdlib", "Date", "t"], []) => tr(common::date_t()),
        (["Map", "t"] | ["Stdlib", "Map", "t"], [key, value]) => Translation {
            dependencies: concat_deps(&[key, value]),
            type_: common::map_t(key.type_.clone(), value.type_.clone()),
        },
        (["WeakMap", "t"] | ["Stdlib", "WeakMap", "t"], [key, value]) => Translation {
            dependencies: concat_deps(&[key, value]),
            type_: common::weakmap_t(key.type_.clone(), value.type_.clone()),
        },
        (["Set", "t"] | ["Stdlib", "Set", "t"], [param]) => {
            with_type(param, common::set_t(param.type_.clone()))
        }
        (["WeakSet", "t"] | ["Stdlib", "WeakSet", "t"], [param]) => {
            with_type(param, common::weakset_t(param.type_.clone()))
        }
        (["Stdlib", "RegExp", "t"], []) => tr(common::regexp_t()),
        (
            [
                "Stdlib",
                name @ ("ArrayBuffer" | "DataView" | "Int8Array" | "Uint8Array"
                | "Uint8ClampedArray" | "Int16Array" | "Uint16Array" | "Int32Array"
                | "Uint32Array" | "Float32Array" | "Float64Array" | "BigInt64Array"
                | "BigUint64Array"),
                "t",
            ],
            [],
        ) => tr(ident(name)),
        (["Stdlib", "Symbol", "t"], []) => tr(ident("symbol")),
        (["Stdlib", "Intl", intl_module, "t"], []) => tr(ident(&format!("Intl.{intl_module}"))),
        (["Stdlib", "Error", "t"] | ["Stdlib", "JsError", "t"], []) => tr(ident("Error")),
        (["Stdlib", "Iterable", "t"] | ["iterable"], [param]) => {
            with_type(param, builtin(vec![param.type_.clone()], "Iterable"))
        }
        (
            [
                "Stdlib",
                name @ ("Iterator"
                | "IteratorObject"
                | "IterableIterator"
                | "Generator"
                | "AsyncIterator"
                | "AsyncIterableIterator"
                | "AsyncGenerator"),
                "t",
            ],
            [yield_t, return_t, next_t],
        ) => Translation {
            dependencies: concat_deps(&[yield_t, return_t, next_t]),
            type_: builtin(
                vec![
                    yield_t.type_.clone(),
                    return_t.type_.clone(),
                    next_t.type_.clone(),
                ],
                name,
            ),
        },
        (["Stdlib", "AsyncIterable", "t"] | ["asyncIterable"], [param]) => {
            with_type(param, builtin(vec![param.type_.clone()], "AsyncIterable"))
        }
        (["Stdlib", "Ordering", "t"], []) => tr(common::number_t()),
        (["unit"], []) => tr(common::unit_t()),
        (["array"] | ["Stdlib", "Array", "t"], [param]) => with_type(
            param,
            Type::Array(Box::new(param.type_.clone()), Mutable::Mutable),
        ),
        (["ImmutableArray", "t"], [param]) => with_type(
            param,
            Type::Array(Box::new(param.type_.clone()), Mutable::Immutable),
        ),
        (["Pervasives", "ref"], [param]) => with_type(
            param,
            Type::Object(
                ClosedFlag::Closed,
                vec![Field {
                    mutable_: Mutable::Mutable,
                    name_js: "contents".to_string(),
                    optional: Optional::Mandatory,
                    type_: param.type_.clone(),
                    doc_string: common::doc_string::empty,
                }],
            ),
        ),
        (
            ["Pervasives", "result"]
            | ["Belt", "Result", "t"]
            | ["result"]
            | ["Stdlib", "Result", "t"],
            [ok_t, error_t],
        ) => result_translation(ok_t, error_t),
        (["React", "callback"], [from_t, to_t]) => function_translation(from_t, to_t),
        (["React", "componentLike"], [props_t, ret_t]) => function_translation(props_t, ret_t),
        (["React", "component"], [props_t]) => with_type(
            props_t,
            Type::Function(Function {
                arg_types: vec![ArgType {
                    a_name: String::new(),
                    a_type: props_t.type_.clone(),
                }],
                ret_type: Box::new(crate::gentype::emit_type::type_react_element()),
                type_vars: vec![],
            }),
        ),
        (["React", "Context", "t"], [param]) => with_type(
            param,
            crate::gentype::emit_type::type_react_context(param.type_.clone()),
        ),
        (["React", "Ref", "t"] | ["React", "ref"], [param]) => with_type(
            param,
            crate::gentype::emit_type::type_react_ref(param.type_.clone()),
        ),
        (["ReactDOM", "domRef"] | ["ReactDOM", "Ref", "t"], []) => {
            tr(crate::gentype::emit_type::type_react_d_o_m_re_dom_ref())
        }
        (["ReactDOM", "Ref", "currentDomRef"], []) => tr(crate::gentype::emit_type::type_any()),
        (["ReactDOMRe", "domRef"], []) => {
            tr(crate::gentype::emit_type::type_react_d_o_m_re_dom_ref())
        }
        (["ReactDOMRe", "Ref", "currentDomRef"], []) => tr(crate::gentype::emit_type::type_any()),
        (["ReactEvent", "Mouse", "t"], []) => {
            tr(crate::gentype::emit_type::type_react_event_mouse_t())
        }
        (
            ["React", "element"]
            | ["ReasonReact", "reactElement"]
            | ["Pervasives", "Jsx", "element"]
            | ["Jsx", "element"],
            [],
        ) => tr(crate::gentype::emit_type::type_react_element()),
        (["option"], [param]) => with_type(param, Type::Option(Box::new(param.type_.clone()))),
        (["Stdlib", "undefined"], [param]) => {
            with_type(param, Type::Option(Box::new(param.type_.clone())))
        }
        (["Stdlib", "Null", "t"] | ["Stdlib", "null"], [param]) => {
            with_type(param, Type::Null(Box::new(param.type_.clone())))
        }
        (["Stdlib", "Nullable", "t"] | ["Stdlib", "nullable"], [param]) => {
            with_type(param, Type::Nullable(Box::new(param.type_.clone())))
        }
        (["promise"] | ["Stdlib", "Promise", "t"], [param]) => {
            with_type(param, Type::Promise(Box::new(param.type_.clone())))
        }
        (["dict"] | ["Stdlib", "Dict", "t"], [param]) => {
            with_type(param, Type::Dict(Box::new(param.type_.clone())))
        }
        (["Stdlib", "JSON", "t"], []) => tr(unknown()),
        // A tagged-template tag is a variadic function usable with backtick
        // syntax: (strings: TemplateStringsArray, ...values: 'param[]) =>
        // 'output. The spread is encoded in the parameter name, which is
        // emitted verbatim before the type.
        (["taggedTemplate"] | ["Stdlib", "TaggedTemplate", "t"], [param, output]) => Translation {
            dependencies: concat_deps(&[param, output]),
            type_: Type::Function(Function {
                arg_types: vec![
                    ArgType {
                        a_name: "strings".to_string(),
                        a_type: ident("TemplateStringsArray"),
                    },
                    ArgType {
                        a_name: "...values".to_string(),
                        a_type: Type::Array(Box::new(param.type_.clone()), Mutable::Mutable),
                    },
                ],
                ret_type: Box::new(output.type_.clone()),
                type_vars: vec![],
            }),
        },
        _ => default_case(config, params_translation, path, type_env),
    }
}

#[derive(Debug, Clone)]
pub struct ProcessVariant {
    pub no_payloads: Vec<String>,
    pub payloads: Vec<(String, TypeExprRef)>,
    pub unknowns: Vec<String>,
}

pub fn process_variant(row_fields: &[(crate::types::asttypes::Label, RowField)]) -> ProcessVariant {
    // Mirrors compiler/gentype/TranslateTypeExprFromTypes.ml:441-468.
    let mut no_payloads = Vec::new();
    let mut payloads = Vec::new();
    let mut unknowns = Vec::new();

    for (label, row_field) in row_fields {
        match row_field {
            RowField::Rpresent(None) => no_payloads.push(label.to_string()),
            RowField::Reither { constant: true, .. } => no_payloads.push(label.to_string()),
            RowField::Rpresent(Some(payload)) => payloads.push((label.to_string(), *payload)),
            RowField::Rabsent
            | RowField::Reither {
                constant: false, ..
            } => unknowns.push(label.to_string()),
        }
    }

    ProcessVariant {
        no_payloads,
        payloads,
        unknowns,
    }
}

#[allow(non_snake_case)]
pub fn translate_arrow_type(
    ctx: &TypeContext,
    config: &crate::gentype::config::T,
    type_vars_gen: &crate::gentype::gen_ident::TypeVarsGen,
    type_env: &crate::gentype::type_env::T,
    args: &[crate::types::type_expr::TypeArg],
    ret: &TypeExprRef,
) -> Translation {
    // Mirrors compiler/gentype/translate_type_expr_from_types.ml:454-490: one
    // n-ary arrow is one function; a function-typed result stays nested.
    let mut arg_deps = Vec::new();
    let mut labeled_convertable_types = Vec::with_capacity(args.len());
    for arg in args {
        let (label, typ) = match arg.label() {
            ArgLabel::Nolabel => (Label::Nolabel, arg.typ),
            label => match remove_option(ctx, label, &arg.typ) {
                Some((lbl, typ)) => (Label::OptLabel(lbl), typ),
                None => (Label::Label(label_name(label)), arg.typ),
            },
        };
        let Translation {
            dependencies,
            type_,
        } = translateTypeExprFromTypes_(ctx, config, type_vars_gen, type_env, &typ);
        arg_deps.extend(dependencies);
        labeled_convertable_types.push((label, type_));
    }
    let Translation {
        dependencies,
        type_: ret_type,
    } = translateTypeExprFromTypes_(ctx, config, type_vars_gen, type_env, ret);
    arg_deps.extend(dependencies);
    let arg_types = crate::gentype::named_args::group(labeled_convertable_types);
    Translation {
        dependencies: arg_deps,
        type_: Type::Function(Function {
            arg_types,
            ret_type: Box::new(ret_type),
            type_vars: vec![],
        }),
    }
}

#[allow(non_snake_case)]
pub fn translateTypeExprFromTypes_(
    ctx: &TypeContext,
    config: &crate::gentype::config::T,
    type_vars_gen: &crate::gentype::gen_ident::TypeVarsGen,
    type_env: &crate::gentype::type_env::T,
    type_expr: &TypeExprRef,
) -> Translation {
    // Mirrors compiler/gentype/TranslateTypeExprFromTypes.ml:526-672.
    match type_expr_desc(ctx, type_expr) {
        TypeDesc::Tvar(None) => Translation {
            dependencies: vec![],
            type_: Type::TypeVar(
                crate::gentype::gen_ident::js_type_name_for_anonymous_type_id(
                    type_vars_gen,
                    type_expr.0 as i32,
                ),
            ),
        },
        TypeDesc::Tvar(Some(s)) => Translation {
            dependencies: vec![],
            type_: Type::TypeVar(s),
        },
        TypeDesc::Tconstr { path, args, .. }
            if path.name() == "Js.t" && args.len() == 1 && is_js_t_preserved(ctx, &args[0]) =>
        {
            translate_obj_type(ClosedFlag::Closed, vec![])
        }
        TypeDesc::Tconstr { path, args, .. } if path.name() == "Js.t" && args.len() == 1 => {
            translateTypeExprFromTypes_(ctx, config, type_vars_gen, type_env, &args[0])
        }
        TypeDesc::Tobject { fields, .. } => {
            let (closed_flag, fields_translations) =
                get_field_types(ctx, config, type_vars_gen, type_env, &fields);
            translate_obj_type(closed_flag, fields_translations)
        }
        TypeDesc::Tconstr { path, args, .. } => {
            // OCaml TranslateTypeExprFromTypes.ml:560-565 has a dedicated
            // `{type_expr with desc = Tconstr(path, [te], r)}` branch when the
            // single argument is Tlink. Rust still needs that exact branch; for
            // now the argument translation follows Tlink through the same
            // TypeContext-backed descriptor reads.
            let params_translation =
                translateTypeExprsFromTypes_(ctx, config, type_vars_gen, type_env, &args);
            translate_constr(config, &params_translation, &path, type_env)
        }
        TypeDesc::Tpoly { body, vars } if vars.is_empty() => {
            translateTypeExprFromTypes_(ctx, config, type_vars_gen, type_env, &body)
        }
        TypeDesc::Tarrow { args, ret } => {
            translate_arrow_type(ctx, config, type_vars_gen, type_env, &args, &ret)
        }
        TypeDesc::Ttuple(list_exp) => {
            let inner_types_translation =
                translateTypeExprsFromTypes_(ctx, config, type_vars_gen, type_env, &list_exp);
            Translation {
                dependencies: inner_types_translation
                    .iter()
                    .flat_map(|translation| translation.dependencies.clone())
                    .collect(),
                type_: Type::Tuple(
                    inner_types_translation
                        .into_iter()
                        .map(|translation| translation.type_)
                        .collect(),
                ),
            }
        }
        TypeDesc::Tlink(t) => translateTypeExprFromTypes_(ctx, config, type_vars_gen, type_env, &t),
        TypeDesc::Tvariant(row_desc) => {
            translate_variant(ctx, config, type_vars_gen, type_env, &row_desc)
        }
        TypeDesc::Tpackage {
            path,
            lids,
            args: types,
        } => {
            // Mirrors compiler/gentype/TranslateTypeExprFromTypes.ml:639-670:
            // `Tpackage(path, ids, types)` translates package constraints by
            // pairing the stored Longident list with the stored type list before
            // calling `TypeEnv.add_type_equations`.
            let ids = lids
                .iter()
                .map(|lid| longident_to_strings(ctx, lid))
                .collect::<Vec<_>>();
            translate_package(ctx, config, type_vars_gen, type_env, &path, &ids, &types)
        }
        TypeDesc::Tfield { .. }
        | TypeDesc::Tnil
        | TypeDesc::Tpoly { .. }
        | TypeDesc::Tsubst(_)
        | TypeDesc::Tunivar(_) => Translation {
            dependencies: vec![],
            type_: unknown(),
        },
    }
}

#[allow(non_snake_case)]
pub fn translateTypeExprsFromTypes_(
    ctx: &TypeContext,
    config: &crate::gentype::config::T,
    type_vars_gen: &crate::gentype::gen_ident::TypeVarsGen,
    type_env: &crate::gentype::type_env::T,
    type_exprs: &[TypeExprRef],
) -> Vec<Translation> {
    // Mirrors compiler/gentype/TranslateTypeExprFromTypes.ml:674-677.
    type_exprs
        .iter()
        .map(|type_expr| {
            translateTypeExprFromTypes_(ctx, config, type_vars_gen, type_env, type_expr)
        })
        .collect()
}

pub fn signature_to_module_runtime_representation(
    ctx: &TypeContext,
    config: &crate::gentype::config::T,
    type_vars_gen: &crate::gentype::gen_ident::TypeVarsGen,
    type_env: &crate::gentype::type_env::T,
    signature: &[crate::types::decl::SignatureItem],
) -> (Vec<Dep>, Type) {
    // Mirrors compiler/gentype/TranslateTypeExprFromTypes.ml:679-737.
    let mut dependencies = Vec::new();
    let mut fields = Vec::new();

    for signature_item in signature {
        match signature_item {
            crate::types::decl::SignatureItem::SigValue(_id, value_description)
                if matches!(
                    value_description.val_kind,
                    crate::types::decl::ValueKind::ValPrim(_)
                ) => {}
            crate::types::decl::SignatureItem::SigValue(id, value_description) => {
                let translation = translateTypeExprFromTypes_(
                    ctx,
                    config,
                    type_vars_gen,
                    type_env,
                    &value_description.val_type,
                );
                dependencies.extend(translation.dependencies);
                fields.push(Field {
                    mutable_: Mutable::Immutable,
                    name_js: id.name().to_string(),
                    optional: Optional::Mandatory,
                    type_: translation.type_,
                    doc_string: crate::gentype::gen_type_common::doc_string::empty,
                });
            }
            crate::types::decl::SignatureItem::SigModule(id, module_declaration, _) => {
                let type_env1 = match crate::gentype::type_env::get_module(id.name(), type_env) {
                    Some(type_env1) => type_env1,
                    None => type_env.clone(),
                };
                let (module_dependencies, type_) = match &module_declaration.md_type {
                    crate::types::decl::ModuleType::MtySignature(signature) => {
                        signature_to_module_runtime_representation(
                            ctx,
                            config,
                            type_vars_gen,
                            &type_env1,
                            signature,
                        )
                    }
                    crate::types::decl::ModuleType::MtyIdent(_)
                    | crate::types::decl::ModuleType::MtyFunctor { .. }
                    | crate::types::decl::ModuleType::MtyAlias(_, _) => (vec![], unknown()),
                };
                dependencies.extend(module_dependencies);
                fields.push(Field {
                    mutable_: Mutable::Immutable,
                    name_js: id.name().to_string(),
                    optional: Optional::Mandatory,
                    type_,
                    doc_string: crate::gentype::gen_type_common::doc_string::empty,
                });
            }
            crate::types::decl::SignatureItem::SigType(_, _, _)
            | crate::types::decl::SignatureItem::SigTypext(_, _, _)
            | crate::types::decl::SignatureItem::SigModtype(_, _)
            | crate::types::decl::SignatureItem::SigClass
            | crate::types::decl::SignatureItem::SigClassType => {}
        }
    }

    (dependencies, Type::Object(ClosedFlag::Closed, fields))
}

pub fn translate_type_expr_from_types(
    ctx: &TypeContext,
    config: &crate::gentype::config::T,
    type_env: &crate::gentype::type_env::T,
    type_expr: &TypeExprRef,
) -> Translation {
    // Mirrors compiler/gentype/TranslateTypeExprFromTypes.ml:739-748.
    let type_vars_gen = crate::gentype::gen_ident::create_type_vars_gen();
    let translation = translateTypeExprFromTypes_(ctx, config, &type_vars_gen, type_env, type_expr);
    log_dependencies(&translation);
    translation
}

pub fn translate_type_exprs_from_types(
    ctx: &TypeContext,
    config: &crate::gentype::config::T,
    type_env: &crate::gentype::type_env::T,
    type_exprs: &[TypeExprRef],
) -> Vec<Translation> {
    // Mirrors compiler/gentype/TranslateTypeExprFromTypes.ml:750-761.
    let type_vars_gen = crate::gentype::gen_ident::create_type_vars_gen();
    let translations =
        translateTypeExprsFromTypes_(ctx, config, &type_vars_gen, type_env, type_exprs);
    for translation in &translations {
        log_dependencies(translation);
    }
    translations
}

fn tr(type_: Type) -> Translation {
    Translation {
        dependencies: vec![],
        type_,
    }
}

fn default_case(
    config: &crate::gentype::config::T,
    params_translation: &[Translation],
    path: &Path,
    type_env: &crate::gentype::type_env::T,
) -> Translation {
    let type_args = params_translation
        .iter()
        .map(|translation| translation.type_.clone())
        .collect::<Vec<_>>();
    let type_param_deps = params_translation
        .iter()
        .flat_map(|translation| translation.dependencies.clone())
        .collect::<Vec<_>>();

    match crate::gentype::type_env::apply_type_equations(config, path, type_env) {
        Some(type_) => Translation {
            dependencies: type_param_deps,
            type_,
        },
        None => {
            let dep = crate::gentype::dependencies::from_path(config, type_env, path);
            let mut dependencies = vec![dep.clone()];
            dependencies.extend(type_param_deps);
            Translation {
                dependencies,
                type_: Type::Ident(Ident {
                    builtin: false,
                    name: dep_to_string(&dep),
                    type_args,
                }),
            }
        }
    }
}

fn concat_deps(translations: &[&Translation]) -> Vec<Dep> {
    translations
        .iter()
        .flat_map(|translation| translation.dependencies.clone())
        .collect()
}

fn result_translation(ok_t: &Translation, error_t: &Translation) -> Translation {
    let case = |name: &str, type_: Type| Payload {
        case: VariantCase {
            label_js: LabelJs::StringLabel(name.to_string()),
        },
        t: type_,
    };
    Translation {
        dependencies: concat_deps(&[ok_t, error_t]),
        type_: create_variant(
            vec![],
            vec![],
            vec![
                case("Ok", ok_t.type_.clone()),
                case("Error", error_t.type_.clone()),
            ],
            false,
            None,
            false,
        ),
    }
}

fn function_translation(from_t: &Translation, to_t: &Translation) -> Translation {
    Translation {
        dependencies: concat_deps(&[from_t, to_t]),
        type_: Type::Function(Function {
            arg_types: vec![ArgType {
                a_name: String::new(),
                a_type: from_t.type_.clone(),
            }],
            ret_type: Box::new(to_t.type_.clone()),
            type_vars: vec![],
        }),
    }
}

fn label_name(label: &ArgLabel) -> String {
    match label {
        ArgLabel::Nolabel => String::new(),
        ArgLabel::Labelled(loc) | ArgLabel::Optional(loc) => loc.txt.clone(),
    }
}

fn is_js_t_preserved(ctx: &TypeContext, type_expr: &TypeExprRef) -> bool {
    matches!(
        type_expr_desc(ctx, type_expr),
        TypeDesc::Tvar(_) | TypeDesc::Tconstr { .. }
    )
}

fn get_field_types(
    ctx: &TypeContext,
    config: &crate::gentype::config::T,
    type_vars_gen: &crate::gentype::gen_ident::TypeVarsGen,
    type_env: &crate::gentype::type_env::T,
    type_expr: &TypeExprRef,
) -> (ClosedFlag, Vec<(String, Mutable, Translation)>) {
    // Mirrors compiler/gentype/translate_type_expr_from_types.ml:502-517:
    // each field's rest is translated before the field itself. Fields are
    // pushed innermost-first, so the list is reversed once at the end.
    fn go(
        ctx: &TypeContext,
        config: &crate::gentype::config::T,
        type_vars_gen: &crate::gentype::gen_ident::TypeVarsGen,
        type_env: &crate::gentype::type_env::T,
        type_expr: &TypeExprRef,
        fields: &mut Vec<(String, Mutable, Translation)>,
    ) -> ClosedFlag {
        match type_expr_desc(ctx, type_expr) {
            TypeDesc::Tfield {
                name,
                mutability,
                typ,
                rest,
            } => {
                let closed_flag = go(ctx, config, type_vars_gen, type_env, &rest, fields);
                let mutable_ = match ctx.mutability_repr(mutability) {
                    crate::types::asttypes::MutableFlag::Mutable => Mutable::Mutable,
                    crate::types::asttypes::MutableFlag::Immutable => Mutable::Immutable,
                };
                let translation =
                    translateTypeExprFromTypes_(ctx, config, type_vars_gen, type_env, &typ);
                fields.push((name, mutable_, translation));
                closed_flag
            }
            TypeDesc::Tlink(te) => go(ctx, config, type_vars_gen, type_env, &te, fields),
            TypeDesc::Tvar(None) => ClosedFlag::Open,
            _ => ClosedFlag::Closed,
        }
    }

    let mut fields = Vec::new();
    let closed_flag = go(ctx, config, type_vars_gen, type_env, type_expr, &mut fields);
    fields.reverse();
    (closed_flag, fields)
}

fn translate_variant(
    ctx: &TypeContext,
    config: &crate::gentype::config::T,
    type_vars_gen: &crate::gentype::gen_ident::TypeVarsGen,
    type_env: &crate::gentype::type_env::T,
    row_desc: &RowDesc,
) -> Translation {
    match process_variant(&row_desc.row_fields) {
        ProcessVariant {
            no_payloads,
            payloads,
            unknowns,
        } if payloads.is_empty() && unknowns.is_empty() => Translation {
            dependencies: vec![],
            type_: create_variant(
                vec![],
                no_payloads
                    .into_iter()
                    .map(|label| VariantCase {
                        label_js: if is_number(&label) {
                            LabelJs::IntLabel(label)
                        } else {
                            LabelJs::StringLabel(label)
                        },
                    })
                    .collect(),
                vec![],
                true,
                None,
                false,
            ),
        },
        ProcessVariant {
            no_payloads,
            payloads,
            unknowns,
        } if no_payloads.is_empty() && payloads.len() == 1 && unknowns.is_empty() => {
            translateTypeExprFromTypes_(ctx, config, type_vars_gen, type_env, &payloads[0].1)
        }
        ProcessVariant {
            no_payloads,
            payloads,
            unknowns,
        } if unknowns.is_empty() => {
            let no_payloads = no_payloads
                .into_iter()
                .map(|label| VariantCase {
                    label_js: LabelJs::StringLabel(label),
                })
                .collect::<Vec<_>>();
            let payload_translations = payloads
                .iter()
                .map(|(label, payload)| {
                    (
                        label.clone(),
                        translateTypeExprFromTypes_(ctx, config, type_vars_gen, type_env, payload),
                    )
                })
                .collect::<Vec<_>>();
            let dependencies = payload_translations
                .iter()
                .flat_map(|(_, translation)| translation.dependencies.clone())
                .collect();
            let payloads = payload_translations
                .into_iter()
                .map(|(label, translation)| Payload {
                    case: VariantCase {
                        label_js: LabelJs::StringLabel(label),
                    },
                    t: translation.type_,
                })
                .collect();
            Translation {
                dependencies,
                type_: create_variant(vec![], no_payloads, payloads, true, None, false),
            }
        }
        ProcessVariant { unknowns, .. } if !unknowns.is_empty() => tr(unknown()),
        _ => tr(unknown()),
    }
}

fn longident_to_strings(
    ctx: &TypeContext,
    longident: &crate::parser::longident::Longident,
) -> Vec<String> {
    // OCaml compiler/gentype/TypeEnv.ml:96-104 calls `Longident.flatten` for
    // package type equations. Rust stores arena-backed Longident components in
    // `TypeDesc::Tpackage`; TypeCheckContext::new registers the arena names on
    // TypeContext so this Types-based translator can flatten them after typing.
    longident
        .flatten_idx()
        .into_iter()
        .map(|idx| {
            ctx.resolve_any_longident_component(idx)
                .expect("package Longident component should be registered on TypeContext")
        })
        .collect()
}

fn translate_package(
    ctx: &TypeContext,
    config: &crate::gentype::config::T,
    type_vars_gen: &crate::gentype::gen_ident::TypeVarsGen,
    type_env: &crate::gentype::type_env::T,
    path: &Path,
    ids: &[Vec<String>],
    types: &[TypeExprRef],
) -> Translation {
    match crate::gentype::type_env::lookup_module_type_signature(path, type_env) {
        Some((_, signature, type_env)) => {
            let type_equations_translation = ids
                .iter()
                .zip(types.iter())
                .map(|(x, t)| {
                    (
                        x.clone(),
                        translateTypeExprFromTypes_(ctx, config, type_vars_gen, &type_env, t),
                    )
                })
                .collect::<Vec<_>>();
            let type_equations = type_equations_translation
                .iter()
                .map(|(x, translation)| (x.clone(), translation.type_.clone()))
                .collect::<Vec<_>>();
            let dependencies_from_type_equations = type_equations_translation
                .iter()
                .flat_map(|(_, translation)| translation.dependencies.clone())
                .collect::<Vec<_>>();
            let type_env1 =
                crate::gentype::type_env::add_type_equations(&type_equations, &type_env);
            let (mut dependencies_from_record_type, type_) =
                signature_to_module_runtime_representation(
                    ctx,
                    config,
                    type_vars_gen,
                    &type_env1,
                    &signature,
                );
            let mut dependencies = dependencies_from_type_equations;
            dependencies.append(&mut dependencies_from_record_type);
            Translation {
                dependencies,
                type_,
            }
        }
        None => tr(unknown()),
    }
}

fn log_dependencies(translation: &Translation) {
    if crate::gentype::debug::dependencies.load(std::sync::atomic::Ordering::Relaxed) {
        for dep in &translation.dependencies {
            crate::gentype::log_::item(&format!("Dependency: {}\n", dep_to_string(dep)));
        }
    }
}
