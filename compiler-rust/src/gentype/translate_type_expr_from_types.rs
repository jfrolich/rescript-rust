// Port of compiler/gentype/TranslateTypeExprFromTypes.ml:1-761.
// This Stage 3 GenType port is intentionally not wired into the crate yet.

use crate::gentype::gen_type_common::{
    ArgType, Case as VariantCase, ClosedFlag, Dep, Field, Function, Ident, Label, LabelJs, Mutable,
    Optional, Payload, Type, create_variant, dep_to_string, ident, ident_with, is_number, unknown,
};
use crate::types::asttypes::ArgLabel;
use crate::types::path::Path;
use crate::types::type_expr::{RowDesc, RowField, TypeDesc, TypeExprRef};

#[derive(Debug, Clone)]
pub struct Translation {
    pub dependencies: Vec<Dep>,
    pub type_: Type,
}

fn type_expr_desc(_type_expr: &TypeExprRef) -> TypeDesc {
    // Temporary Phase 0 adapter for compiler/ml/types.ml:type_expr.desc access.
    // The integrated port must read through the Rust TypeContext arena while
    // preserving OCaml TranslateTypeExprFromTypes.ml traversal order.
    unimplemented!("TypeExprRef descriptor access is wired in Phase 5")
}

pub fn remove_option(label: &ArgLabel, type_expr: &TypeExprRef) -> Option<(String, TypeExprRef)> {
    // Mirrors compiler/gentype/TranslateTypeExprFromTypes.ml:5-12.
    match (type_expr_desc(type_expr), label) {
        (TypeDesc::Tconstr { path, args, .. }, ArgLabel::Optional(lbl))
            if matches!(&path, Path::Pident(id) if id.name() == "option") && args.len() == 1 =>
        {
            Some((lbl.txt.clone(), args[0]))
        }
        (TypeDesc::Tlink(t), _) => remove_option(label, &t),
        _ => None,
    }
}

pub fn path_to_list(path: &Path) -> Vec<String> {
    // Mirrors compiler/gentype/TranslateTypeExprFromTypes.ml:14-22.
    match path {
        Path::Pident(id) if id.name().starts_with("Stdlib_") => {
            let name = id.name();
            vec![name[7..].to_string(), "Stdlib".to_string()]
        }
        Path::Pident(id) => vec![id.name().to_string()],
        Path::Pdot(p, s, _) => {
            let mut out = vec![s.clone()];
            out.extend(path_to_list(p));
            out
        }
        Path::Papply(_, _) => vec![],
    }
}

pub fn translate_obj_type(
    closed_flag: ClosedFlag,
    fields_translations: Vec<(String, Translation)>,
) -> Translation {
    // Mirrors compiler/gentype/TranslateTypeExprFromTypes.ml:24-57.
    let dependencies = fields_translations
        .iter()
        .flat_map(|(_, translation)| translation.dependencies.clone())
        .collect::<Vec<_>>();

    fn check_mutable_field(
        fields: &[(String, Translation)],
        acc: &mut Vec<(String, Type, Mutable)>,
    ) {
        match fields {
            [(previous_name, _), (name, translation), rest @ ..]
                if crate::gentype::runtime::check_mutable_object_field(previous_name, name) =>
            {
                acc.push((name.clone(), translation.type_.clone(), Mutable::Mutable));
                check_mutable_field(rest, acc);
            }
            [(name, translation), rest @ ..] => {
                acc.push((name.clone(), translation.type_.clone(), Mutable::Immutable));
                check_mutable_field(rest, acc);
            }
            [] => {}
        }
    }

    let mut mutable_checked = Vec::new();
    check_mutable_field(&fields_translations, &mut mutable_checked);
    let fields = mutable_checked
        .into_iter()
        .map(|(name, t, mutable_)| {
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
    // Mirrors compiler/gentype/TranslateTypeExprFromTypes.ml:59-439.
    let mut path_list = path_to_list(path);
    path_list.reverse();

    if params_translation.is_empty() {
        match path_list.as_slice() {
            [s] if s == "bool" => return tr(crate::gentype::gen_type_common::boolean_t()),
            [s] if s == "int" || s == "float" => {
                return tr(crate::gentype::gen_type_common::number_t());
            }
            [s] if s == "unit" => return tr(crate::gentype::gen_type_common::unit_t()),
            [s] if s == "string" => return tr(crate::gentype::gen_type_common::string_t()),
            [a, b] if a == "String" && b == "t" => {
                return tr(crate::gentype::gen_type_common::string_t());
            }
            [a, b, c]
                if (a == "Stdlib" && b == "String" && c == "t")
                    || (a == "Js" && (b == "String" || b == "String2") && c == "t") =>
            {
                return tr(crate::gentype::gen_type_common::string_t());
            }
            [a, b] if a == "BigInt" && b == "t" => {
                return tr(crate::gentype::gen_type_common::bigint_t());
            }
            [a, b, c]
                if (a == "Js" && b == "Types" && c == "bigint_val")
                    || (a == "Stdlib" && b == "BigInt" && c == "t") =>
            {
                return tr(crate::gentype::gen_type_common::bigint_t());
            }
            [a, b] if (a == "Date" || a == "RegExp") && b == "t" => {
                return tr(match a.as_str() {
                    "Date" => crate::gentype::gen_type_common::date_t(),
                    _ => crate::gentype::gen_type_common::regexp_t(),
                });
            }
            [a, b, c]
                if (a == "Js" && b == "Date" && c == "t")
                    || (a == "Stdlib" && b == "Date" && c == "t") =>
            {
                return tr(crate::gentype::gen_type_common::date_t());
            }
            [a, b, c]
                if (a == "Js" && b == "Re" && c == "t")
                    || (a == "Stdlib" && b == "RegExp" && c == "t") =>
            {
                return tr(crate::gentype::gen_type_common::regexp_t());
            }
            [a, b, c] if a == "Stdlib" && c == "t" => {
                return match b.as_str() {
                    "ArrayBuffer" | "DataView" | "Int8Array" | "Uint8Array"
                    | "Uint8ClampedArray" | "Int16Array" | "Uint16Array" | "Int32Array"
                    | "Uint32Array" | "Float32Array" | "Float64Array" | "BigInt64Array"
                    | "BigUint64Array" => tr(ident(b)),
                    "Symbol" => tr(ident("symbol")),
                    "Error" | "JsError" => tr(ident("Error")),
                    "Ordering" => tr(crate::gentype::gen_type_common::number_t()),
                    "JSON" => tr(unknown()),
                    _ => default_case(config, params_translation, path, type_env),
                };
            }
            [a, b, c, d] if a == "Stdlib" && b == "Intl" && d == "t" => {
                return tr(ident(&format!("Intl.{c}")));
            }
            [a, b] if a == "ReactDOM" && b == "domRef" => {
                return tr(crate::gentype::emit_type::type_react_d_o_m_re_dom_ref());
            }
            [a, b, c] if a == "ReactDOM" && b == "Ref" && c == "currentDomRef" => {
                return tr(crate::gentype::emit_type::type_any());
            }
            [a, b] if a == "ReactDOMRe" && b == "domRef" => {
                return tr(crate::gentype::emit_type::type_react_d_o_m_re_dom_ref());
            }
            [a, b, c] if a == "ReactDOMRe" && b == "Ref" && c == "currentDomRef" => {
                return tr(crate::gentype::emit_type::type_any());
            }
            [a, b, c] if a == "ReactEvent" && b == "Mouse" && c == "t" => {
                return tr(crate::gentype::emit_type::type_react_event_mouse_t());
            }
            [a, b]
                if (a == "React" && b == "element")
                    || (a == "ReasonReact" && b == "reactElement")
                    || (a == "Jsx" && b == "element") =>
            {
                return tr(crate::gentype::emit_type::type_react_element());
            }
            [a, b, c] if a == "Pervasives" && b == "Jsx" && c == "element" => {
                return tr(crate::gentype::emit_type::type_react_element());
            }
            _ => {}
        }
    }

    match (path_list.as_slice(), params_translation) {
        ([a, b], [param1, param2]) if (a == "Map" || a == "WeakMap") && b == "t" => {
            let type_ = match a.as_str() {
                "Map" => crate::gentype::gen_type_common::map_t(
                    param1.type_.clone(),
                    param2.type_.clone(),
                ),
                _ => crate::gentype::gen_type_common::weakmap_t(
                    param1.type_.clone(),
                    param2.type_.clone(),
                ),
            };
            Translation {
                dependencies: concat_deps(&[param1, param2]),
                type_,
            }
        }
        ([a, b, c], [param1, param2])
            if a == "Stdlib" && (b == "Map" || b == "WeakMap") && c == "t" =>
        {
            let type_ = match b.as_str() {
                "Map" => crate::gentype::gen_type_common::map_t(
                    param1.type_.clone(),
                    param2.type_.clone(),
                ),
                _ => crate::gentype::gen_type_common::weakmap_t(
                    param1.type_.clone(),
                    param2.type_.clone(),
                ),
            };
            Translation {
                dependencies: concat_deps(&[param1, param2]),
                type_,
            }
        }
        ([a, b], [param]) if (a == "Set" || a == "WeakSet") && b == "t" => Translation {
            dependencies: param.dependencies.clone(),
            type_: match a.as_str() {
                "Set" => crate::gentype::gen_type_common::set_t(param.type_.clone()),
                _ => crate::gentype::gen_type_common::weakset_t(param.type_.clone()),
            },
        },
        ([a, b, c], [param]) if a == "Stdlib" && (b == "Set" || b == "WeakSet") && c == "t" => {
            Translation {
                dependencies: param.dependencies.clone(),
                type_: match b.as_str() {
                    "Set" => crate::gentype::gen_type_common::set_t(param.type_.clone()),
                    _ => crate::gentype::gen_type_common::weakset_t(param.type_.clone()),
                },
            }
        }
        ([a, b], [param]) if (a == "array" || a == "ImmutableArray") && b == "t" => Translation {
            dependencies: param.dependencies.clone(),
            type_: Type::Array(
                Box::new(param.type_.clone()),
                match a.as_str() {
                    "ImmutableArray" => Mutable::Immutable,
                    _ => Mutable::Mutable,
                },
            ),
        },
        ([a], [param]) if a == "array" => Translation {
            dependencies: param.dependencies.clone(),
            type_: Type::Array(Box::new(param.type_.clone()), Mutable::Mutable),
        },
        ([a, b, c], [param]) if a == "Js" && (b == "Array" || b == "Array2") && c == "t" => {
            Translation {
                dependencies: param.dependencies.clone(),
                type_: Type::Array(Box::new(param.type_.clone()), Mutable::Mutable),
            }
        }
        ([a, b], [param]) if a == "Pervasives" && b == "ref" => Translation {
            dependencies: param.dependencies.clone(),
            type_: Type::Object(
                ClosedFlag::Closed,
                vec![Field {
                    mutable_: Mutable::Mutable,
                    name_js: "contents".to_string(),
                    optional: Optional::Mandatory,
                    type_: param.type_.clone(),
                    doc_string: crate::gentype::gen_type_common::doc_string::empty,
                }],
            ),
        },
        ([a], [param]) if a == "option" => Translation {
            dependencies: param.dependencies.clone(),
            type_: Type::Option(Box::new(param.type_.clone())),
        },
        ([a], [ok_t, error_t]) if a == "result" => result_translation(ok_t, error_t),
        ([a, b], [ok_t, error_t]) if a == "Pervasives" && b == "result" => {
            result_translation(ok_t, error_t)
        }
        ([a, b, c], [ok_t, error_t])
            if (a == "Belt" && b == "Result" && c == "t")
                || (a == "Stdlib" && b == "Result" && c == "t") =>
        {
            result_translation(ok_t, error_t)
        }
        ([a, b], [param])
            if (a == "Js" && (b == "undefined" || b == "null" || b == "nullable"))
                || (a == "Stdlib" && (b == "undefined" || b == "null" || b == "nullable")) =>
        {
            wrap_builtin_nullable(b, param)
        }
        ([a, b, c], [param])
            if (a == "Js"
                && (b == "Undefined"
                    || b == "Null"
                    || b == "Nullable"
                    || b == "Promise"
                    || b == "Dict")
                && c == "t")
                || (a == "Stdlib"
                    && (b == "Null" || b == "Nullable" || b == "Promise" || b == "Dict")
                    && c == "t") =>
        {
            wrap_builtin_nullable(b, param)
        }
        ([a, b], [param])
            if (a == "Undefined" && b == "t")
                || (a == "Null" && b == "t")
                || (a == "Nullable" && b == "t")
                || (a == "Promise" && b == "t")
                || (a == "Dict" && b == "t") =>
        {
            wrap_builtin_nullable(a, param)
        }
        ([a], [param]) if a == "promise" || a == "dict" => wrap_builtin_nullable(a, param),
        ([a, b, c], [param])
            if a == "Stdlib" && (b == "Iterable" || b == "AsyncIterable") && c == "t" =>
        {
            Translation {
                dependencies: param.dependencies.clone(),
                type_: ident_with(true, vec![param.type_.clone()], b),
            }
        }
        ([a], [param]) if a == "iterable" || a == "asyncIterable" => Translation {
            dependencies: param.dependencies.clone(),
            type_: ident_with(
                false,
                vec![param.type_.clone()],
                match a.as_str() {
                    "iterable" => "Iterable",
                    _ => "AsyncIterable",
                },
            ),
        },
        ([a, b, c], [yield_t, return_t, next_t])
            if a == "Stdlib"
                && matches!(
                    b.as_str(),
                    "Iterator"
                        | "IteratorObject"
                        | "IterableIterator"
                        | "Generator"
                        | "AsyncIterator"
                        | "AsyncIterableIterator"
                        | "AsyncGenerator"
                )
                && c == "t" =>
        {
            Translation {
                dependencies: concat_deps(&[yield_t, return_t, next_t]),
                type_: ident_with(
                    false,
                    vec![
                        yield_t.type_.clone(),
                        return_t.type_.clone(),
                        next_t.type_.clone(),
                    ],
                    b,
                ),
            }
        }
        ([a, b], [from_t, to_t]) if a == "React" && b == "callback" => {
            function_translation(from_t, to_t)
        }
        ([a, b], [props_t, ret_t]) if a == "React" && b == "componentLike" => {
            function_translation(props_t, ret_t)
        }
        ([a, b], [props_t]) if a == "React" && b == "component" => Translation {
            dependencies: props_t.dependencies.clone(),
            type_: Type::Function(Function {
                arg_types: vec![ArgType {
                    a_name: String::new(),
                    a_type: props_t.type_.clone(),
                }],
                ret_type: Box::new(crate::gentype::emit_type::type_react_element()),
                type_vars: vec![],
            }),
        },
        ([a, b, c], [param]) if a == "React" && b == "Context" && c == "t" => Translation {
            dependencies: param.dependencies.clone(),
            type_: crate::gentype::emit_type::type_react_context(param.type_.clone()),
        },
        ([a, b, c], [param]) if a == "React" && b == "Ref" && c == "t" => Translation {
            dependencies: param.dependencies.clone(),
            type_: crate::gentype::emit_type::type_react_ref(param.type_.clone()),
        },
        ([a, b], [param]) if a == "React" && b == "ref" => Translation {
            dependencies: param.dependencies.clone(),
            type_: crate::gentype::emit_type::type_react_ref(param.type_.clone()),
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
    config: &crate::gentype::config::T,
    type_vars_gen: &crate::gentype::gen_ident::TypeVarsGen,
    type_env: &crate::gentype::type_env::T,
    rev_arg_deps: Vec<Dep>,
    rev_args: Vec<(Label, Type)>,
    type_expr: &TypeExprRef,
) -> Translation {
    // Mirrors compiler/gentype/TranslateTypeExprFromTypes.ml:470-524.
    match type_expr_desc(type_expr) {
        TypeDesc::Tlink(t) => {
            translate_arrow_type(config, type_vars_gen, type_env, rev_arg_deps, rev_args, &t)
        }
        TypeDesc::Tarrow {
            arg, ret, arity, ..
        } if matches!(arg.lbl, ArgLabel::Nolabel) && (arity.is_none() || rev_args.is_empty()) => {
            let Translation {
                dependencies,
                type_,
            } = translateTypeExprFromTypes_(config, type_vars_gen, type_env, &arg.typ);
            let mut next_rev_deps = dependencies;
            next_rev_deps.extend(rev_arg_deps);
            let mut next_rev_args = vec![(Label::Nolabel, type_)];
            next_rev_args.extend(rev_args);
            translate_arrow_type(
                config,
                type_vars_gen,
                type_env,
                next_rev_deps,
                next_rev_args,
                &ret,
            )
        }
        TypeDesc::Tarrow {
            arg, ret, arity, ..
        } if !matches!(arg.lbl, ArgLabel::Nolabel) && (arity.is_none() || rev_args.is_empty()) => {
            match remove_option(&arg.lbl, &arg.typ) {
                None => {
                    let Translation {
                        dependencies,
                        type_: type1,
                    } = translateTypeExprFromTypes_(config, type_vars_gen, type_env, &arg.typ);
                    let mut next_rev_deps = dependencies;
                    next_rev_deps.extend(rev_arg_deps);
                    let mut next_rev_args = vec![(Label::Label(label_name(&arg.lbl)), type1)];
                    next_rev_args.extend(rev_args);
                    translate_arrow_type(
                        config,
                        type_vars_gen,
                        type_env,
                        next_rev_deps,
                        next_rev_args,
                        &ret,
                    )
                }
                Some((lbl, t1)) => {
                    let Translation {
                        dependencies,
                        type_: type1,
                    } = translateTypeExprFromTypes_(config, type_vars_gen, type_env, &t1);
                    let mut next_rev_deps = dependencies;
                    next_rev_deps.extend(rev_arg_deps);
                    let mut next_rev_args = vec![(Label::OptLabel(lbl), type1)];
                    next_rev_args.extend(rev_args);
                    translate_arrow_type(
                        config,
                        type_vars_gen,
                        type_env,
                        next_rev_deps,
                        next_rev_args,
                        &ret,
                    )
                }
            }
        }
        _ => {
            let Translation {
                dependencies,
                type_: ret_type,
            } = translateTypeExprFromTypes_(config, type_vars_gen, type_env, type_expr);
            let mut all_deps = rev_arg_deps;
            all_deps.extend(dependencies);
            let mut labeled_convertable_types = rev_args;
            labeled_convertable_types.reverse();
            let arg_types = crate::gentype::named_args::group(labeled_convertable_types);
            Translation {
                dependencies: all_deps,
                type_: Type::Function(Function {
                    arg_types,
                    ret_type: Box::new(ret_type),
                    type_vars: vec![],
                }),
            }
        }
    }
}

#[allow(non_snake_case)]
pub fn translateTypeExprFromTypes_(
    config: &crate::gentype::config::T,
    type_vars_gen: &crate::gentype::gen_ident::TypeVarsGen,
    type_env: &crate::gentype::type_env::T,
    type_expr: &TypeExprRef,
) -> Translation {
    // Mirrors compiler/gentype/TranslateTypeExprFromTypes.ml:526-672.
    match type_expr_desc(type_expr) {
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
            if path.name() == "Js.t" && args.len() == 1 && is_js_t_preserved(&args[0]) =>
        {
            translate_obj_type(ClosedFlag::Closed, vec![])
        }
        TypeDesc::Tconstr { path, args, .. } if path.name() == "Js.t" && args.len() == 1 => {
            translateTypeExprFromTypes_(config, type_vars_gen, type_env, &args[0])
        }
        TypeDesc::Tobject { fields, .. } => {
            let (closed_flag, fields_translations) =
                get_field_types(config, type_vars_gen, type_env, &fields);
            translate_obj_type(closed_flag, fields_translations)
        }
        TypeDesc::Tconstr { path, args, .. } => {
            // OCaml TranslateTypeExprFromTypes.ml:560-565 has a dedicated
            // `{type_expr with desc = Tconstr(path, [te], r)}` branch when the
            // single argument is Tlink. Rust Phase 5 must reproduce that
            // record-copy shape once TypeContext-backed descriptor access is
            // threaded here; until then the argument translation follows Tlink.
            let params_translation =
                translateTypeExprsFromTypes_(config, type_vars_gen, type_env, &args);
            translate_constr(config, &params_translation, &path, type_env)
        }
        TypeDesc::Tpoly { body, vars } if vars.is_empty() => {
            translateTypeExprFromTypes_(config, type_vars_gen, type_env, &body)
        }
        TypeDesc::Tarrow { .. } => {
            translate_arrow_type(config, type_vars_gen, type_env, vec![], vec![], type_expr)
        }
        TypeDesc::Ttuple(list_exp) => {
            let inner_types_translation =
                translateTypeExprsFromTypes_(config, type_vars_gen, type_env, &list_exp);
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
        TypeDesc::Tlink(t) => translateTypeExprFromTypes_(config, type_vars_gen, type_env, &t),
        TypeDesc::Tvariant(row_desc) => {
            translate_variant(config, type_vars_gen, type_env, &row_desc)
        }
        TypeDesc::Tpackage {
            path,
            lids: _,
            args: types,
        } => {
            // OCaml TranslateTypeExprFromTypes.ml:639-670 uses package
            // constraint longidents here. Rust Phase 5 must thread the
            // ParseArena so those Longident indices can be flattened to names.
            translate_package(config, type_vars_gen, type_env, &path, &[], &types)
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
    config: &crate::gentype::config::T,
    type_vars_gen: &crate::gentype::gen_ident::TypeVarsGen,
    type_env: &crate::gentype::type_env::T,
    type_exprs: &[TypeExprRef],
) -> Vec<Translation> {
    // Mirrors compiler/gentype/TranslateTypeExprFromTypes.ml:674-677.
    type_exprs
        .iter()
        .map(|type_expr| translateTypeExprFromTypes_(config, type_vars_gen, type_env, type_expr))
        .collect()
}

pub fn signature_to_module_runtime_representation(
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
    config: &crate::gentype::config::T,
    type_env: &crate::gentype::type_env::T,
    type_expr: &TypeExprRef,
) -> Translation {
    // Mirrors compiler/gentype/TranslateTypeExprFromTypes.ml:739-748.
    let type_vars_gen = crate::gentype::gen_ident::create_type_vars_gen();
    let translation = translateTypeExprFromTypes_(config, &type_vars_gen, type_env, type_expr);
    log_dependencies(&translation);
    translation
}

pub fn translate_type_exprs_from_types(
    config: &crate::gentype::config::T,
    type_env: &crate::gentype::type_env::T,
    type_exprs: &[TypeExprRef],
) -> Vec<Translation> {
    // Mirrors compiler/gentype/TranslateTypeExprFromTypes.ml:750-761.
    let type_vars_gen = crate::gentype::gen_ident::create_type_vars_gen();
    let translations = translateTypeExprsFromTypes_(config, &type_vars_gen, type_env, type_exprs);
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

fn wrap_builtin_nullable(name: &str, param: &Translation) -> Translation {
    let type_ = match name {
        "Undefined" | "undefined" => Type::Option(Box::new(param.type_.clone())),
        "Null" | "null" => Type::Null(Box::new(param.type_.clone())),
        "Nullable" | "nullable" => Type::Nullable(Box::new(param.type_.clone())),
        "Promise" | "promise" => Type::Promise(Box::new(param.type_.clone())),
        "Dict" | "dict" => Type::Dict(Box::new(param.type_.clone())),
        _ => param.type_.clone(),
    };
    Translation {
        dependencies: param.dependencies.clone(),
        type_,
    }
}

fn label_name(label: &ArgLabel) -> String {
    match label {
        ArgLabel::Nolabel => String::new(),
        ArgLabel::Labelled(loc) | ArgLabel::Optional(loc) => loc.txt.clone(),
    }
}

fn is_js_t_preserved(type_expr: &TypeExprRef) -> bool {
    matches!(
        type_expr_desc(type_expr),
        TypeDesc::Tvar(_) | TypeDesc::Tconstr { .. }
    )
}

fn get_field_types(
    config: &crate::gentype::config::T,
    type_vars_gen: &crate::gentype::gen_ident::TypeVarsGen,
    type_env: &crate::gentype::type_env::T,
    type_expr: &TypeExprRef,
) -> (ClosedFlag, Vec<(String, Translation)>) {
    match type_expr_desc(type_expr) {
        TypeDesc::Tfield {
            name, typ, rest, ..
        } => {
            let (closed_flag, mut fields) = get_field_types(config, type_vars_gen, type_env, &rest);
            let translation = match crate::gentype::runtime::is_mutable_object_field(&name) {
                true => tr(ident("")),
                false => translateTypeExprFromTypes_(config, type_vars_gen, type_env, &typ),
            };
            fields.insert(0, (name, translation));
            (closed_flag, fields)
        }
        TypeDesc::Tlink(te) => get_field_types(config, type_vars_gen, type_env, &te),
        TypeDesc::Tvar(None) => (ClosedFlag::Open, vec![]),
        _ => (ClosedFlag::Closed, vec![]),
    }
}

fn translate_variant(
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
            translateTypeExprFromTypes_(config, type_vars_gen, type_env, &payloads[0].1)
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
                        translateTypeExprFromTypes_(config, type_vars_gen, type_env, payload),
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

fn translate_package(
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
                        translateTypeExprFromTypes_(config, type_vars_gen, &type_env, t),
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
