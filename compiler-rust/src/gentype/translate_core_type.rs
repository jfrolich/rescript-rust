// Port of compiler/gentype/TranslateCoreType.ml:1-295.
// This Stage 3 GenType port is intentionally not wired into the crate yet.

use crate::gentype::gen_type_common::{
    Case as VariantCase, ClosedFlag as GenClosedFlag, Function, Label, LabelJs, Payload, Type,
    create_variant, dep_to_string, is_number, unknown,
};
use crate::parse_arena::ParseArena;
use crate::parser::ast::ClosedFlag as AstClosedFlag;
use crate::parser::longident::Longident;
use crate::types::asttypes::ArgLabel;
use crate::types::context::TypeContext;
use crate::types::path::Path;
use crate::types::typedtree::{
    ObjectField, ObjectFieldDesc, RowFieldDesc, RowFieldType, TypedCoreType, TypedCoreTypeDesc,
};

pub fn remove_option(
    label: &ArgLabel,
    core_type: &TypedCoreType,
) -> Option<(String, TypedCoreType)> {
    // Mirrors compiler/gentype/TranslateCoreType.ml:4-15.
    match (&core_type.ctyp_desc, label) {
        (TypedCoreTypeDesc::Ttyp_constr(Path::Pident(id), _, args), ArgLabel::Optional(lbl))
            if id.name() == "option" && args.len() == 1 =>
        {
            Some((lbl.txt.clone(), args[0].clone()))
        }
        (
            TypedCoreTypeDesc::Ttyp_constr(Path::Pdot(name_space, id, _), _, args),
            ArgLabel::Optional(lbl),
        ) if matches!(name_space.as_ref(), Path::Pident(ns) if ns.name() == "FB")
            && id == "option"
            && args.len() == 1 =>
        {
            Some((lbl.txt.clone(), args[0].clone()))
        }
        _ => None,
    }
}

#[derive(Debug, Clone)]
pub struct ProcessVariant {
    pub no_payloads: Vec<(String, crate::parser::ast::Attributes)>,
    pub payloads: Vec<(String, crate::parser::ast::Attributes, TypedCoreType)>,
    pub inherits: Vec<TypedCoreType>,
}

pub fn process_variant(row_fields: &[RowFieldType]) -> ProcessVariant {
    // Mirrors compiler/gentype/TranslateCoreType.ml:17-50.
    let mut no_payloads = Vec::new();
    let mut payloads = Vec::new();
    let mut inherits = Vec::new();

    for row_field in row_fields {
        match &row_field.rf_desc {
            RowFieldDesc::Rtag(label, _, payload) if payload.is_empty() => {
                no_payloads.push((label.txt.clone(), row_field.rf_attributes.clone()));
            }
            RowFieldDesc::Rtag(label, _, payload) if payload.len() == 1 => {
                payloads.push((
                    label.txt.clone(),
                    row_field.rf_attributes.clone(),
                    payload[0].clone(),
                ));
            }
            RowFieldDesc::Rtag(_, _, _) => {}
            RowFieldDesc::Rinherit(t) => inherits.push(t.clone()),
        }
    }

    ProcessVariant {
        no_payloads,
        payloads,
        inherits,
    }
}

pub fn translate_arrow_type(
    ctx: &TypeContext,
    arena: &ParseArena,
    config: &crate::gentype::config::T,
    type_vars_gen: &crate::gentype::gen_ident::TypeVarsGen,
    no_function_return_dependencies: bool,
    type_env: &crate::gentype::type_env::T,
    args: &[crate::types::typedtree::ArrowArg],
    ret: &TypedCoreType,
) -> crate::gentype::translate_type_expr_from_types::Translation {
    // Mirrors compiler/gentype/translate_core_type.ml:52-103: one n-ary arrow
    // is one function, and `@genType.as` renames come from each argument.
    let mut all_deps = Vec::new();
    let mut labeled_convertable_types = Vec::with_capacity(args.len());
    for arg in args {
        let (label, typ) = match &arg.lbl {
            ArgLabel::Nolabel => (Label::Nolabel, &*arg.typ),
            label => {
                let as_label =
                    crate::gentype::annotation::get_gentype_as_renaming(arena, &arg.attrs)
                        .unwrap_or_default();
                match remove_option(label, &arg.typ) {
                    None => {
                        let label = if as_label.is_empty() {
                            label_name(label)
                        } else {
                            as_label
                        };
                        (Label::Label(label), &*arg.typ)
                    }
                    Some((lbl, typ)) => {
                        let translation = translateCoreType_(
                            ctx,
                            arena,
                            config,
                            type_vars_gen,
                            false,
                            type_env,
                            &typ,
                        );
                        all_deps.extend(translation.dependencies);
                        labeled_convertable_types.push((Label::OptLabel(lbl), translation.type_));
                        continue;
                    }
                }
            }
        };
        let translation =
            translateCoreType_(ctx, arena, config, type_vars_gen, false, type_env, typ);
        all_deps.extend(translation.dependencies);
        labeled_convertable_types.push((label, translation.type_));
    }
    let translation = translateCoreType_(ctx, arena, config, type_vars_gen, false, type_env, ret);
    if !no_function_return_dependencies {
        all_deps.extend(translation.dependencies);
    }
    let arg_types = crate::gentype::named_args::group(labeled_convertable_types);
    crate::gentype::translate_type_expr_from_types::Translation {
        dependencies: all_deps,
        type_: Type::Function(Function {
            arg_types,
            ret_type: Box::new(translation.type_),
            type_vars: vec![],
        }),
    }
}

#[allow(non_snake_case)]
pub fn translateCoreType_(
    ctx: &TypeContext,
    arena: &ParseArena,
    config: &crate::gentype::config::T,
    type_vars_gen: &crate::gentype::gen_ident::TypeVarsGen,
    no_function_return_dependencies: bool,
    type_env: &crate::gentype::type_env::T,
    core_type: &TypedCoreType,
) -> crate::gentype::translate_type_expr_from_types::Translation {
    // Mirrors compiler/gentype/TranslateCoreType.ml:122-280.
    match &core_type.ctyp_desc {
        TypedCoreTypeDesc::Ttyp_alias(ct, _) => {
            translateCoreType_(ctx, arena, config, type_vars_gen, false, type_env, ct)
        }
        TypedCoreTypeDesc::Ttyp_object(t_obj, closed_flag) => {
            let fields_translations = t_obj
                .iter()
                .map(|object_field| {
                    get_field_type(ctx, arena, config, type_vars_gen, type_env, object_field)
                })
                .collect::<Vec<_>>();
            crate::gentype::translate_type_expr_from_types::translate_obj_type(
                match closed_flag {
                    AstClosedFlag::Closed => GenClosedFlag::Closed,
                    _ => GenClosedFlag::Open,
                },
                fields_translations,
            )
        }
        TypedCoreTypeDesc::Ttyp_constr(path, _, type_params) => {
            let params_translation =
                translateCoreTypes_(ctx, arena, config, type_vars_gen, type_env, type_params);
            crate::gentype::translate_type_expr_from_types::translate_constr(
                config,
                &params_translation,
                path,
                type_env,
            )
        }
        TypedCoreTypeDesc::Ttyp_poly(_, t) => translateCoreType_(
            ctx,
            arena,
            config,
            type_vars_gen,
            no_function_return_dependencies,
            type_env,
            t,
        ),
        TypedCoreTypeDesc::Ttyp_arrow(args, ret) => translate_arrow_type(
            ctx,
            arena,
            config,
            type_vars_gen,
            no_function_return_dependencies,
            type_env,
            args,
            ret,
        ),
        TypedCoreTypeDesc::Ttyp_tuple(list_exp) => {
            let inner_types_translation =
                translateCoreTypes_(ctx, arena, config, type_vars_gen, type_env, list_exp);
            crate::gentype::translate_type_expr_from_types::Translation {
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
        TypedCoreTypeDesc::Ttyp_var(Some(s)) => {
            crate::gentype::translate_type_expr_from_types::Translation {
                dependencies: vec![],
                type_: Type::TypeVar(s.clone()),
            }
        }
        TypedCoreTypeDesc::Ttyp_var(None) => {
            crate::gentype::translate_type_expr_from_types::Translation {
                dependencies: vec![],
                type_: unknown(),
            }
        }
        TypedCoreTypeDesc::Ttyp_variant(row_fields, _, _) => translate_variant(
            ctx,
            arena,
            config,
            type_vars_gen,
            type_env,
            core_type,
            row_fields,
        ),
        TypedCoreTypeDesc::Ttyp_package(package) => {
            translate_package(ctx, arena, config, type_vars_gen, type_env, package)
        }
    }
}

#[allow(non_snake_case)]
pub fn translateCoreTypes_(
    ctx: &TypeContext,
    arena: &ParseArena,
    config: &crate::gentype::config::T,
    type_vars_gen: &crate::gentype::gen_ident::TypeVarsGen,
    type_env: &crate::gentype::type_env::T,
    type_exprs: &[TypedCoreType],
) -> Vec<crate::gentype::translate_type_expr_from_types::Translation> {
    // Mirrors compiler/gentype/TranslateCoreType.ml:282-284.
    type_exprs
        .iter()
        .map(|core_type| {
            translateCoreType_(
                ctx,
                arena,
                config,
                type_vars_gen,
                false,
                type_env,
                core_type,
            )
        })
        .collect()
}

pub fn translate_core_type(
    ctx: &TypeContext,
    arena: &ParseArena,
    config: &crate::gentype::config::T,
    type_env: &crate::gentype::type_env::T,
    core_type: &TypedCoreType,
) -> crate::gentype::translate_type_expr_from_types::Translation {
    // Mirrors compiler/gentype/TranslateCoreType.ml:286-295.
    let type_vars_gen = crate::gentype::gen_ident::create_type_vars_gen();
    let translation = translateCoreType_(
        ctx,
        arena,
        config,
        &type_vars_gen,
        false,
        type_env,
        core_type,
    );
    if crate::gentype::debug::dependencies.load(std::sync::atomic::Ordering::Relaxed) {
        for dep in &translation.dependencies {
            crate::gentype::log_::item(&format!("Dependency: {}\n", dep_to_string(dep)));
        }
    }
    translation
}

fn get_field_type(
    ctx: &TypeContext,
    arena: &ParseArena,
    config: &crate::gentype::config::T,
    type_vars_gen: &crate::gentype::gen_ident::TypeVarsGen,
    type_env: &crate::gentype::type_env::T,
    object_field: &ObjectField,
) -> (
    String,
    crate::gentype::gen_type_common::Mutable,
    crate::gentype::translate_type_expr_from_types::Translation,
) {
    match &object_field.of_desc {
        ObjectFieldDesc::OTtag(name, t) => {
            let mutable_ = if object_field.of_attributes.iter().any(|(attr_name, payload)| {
                arena.get_string(attr_name.txt) == "set"
                    && matches!(payload, crate::parser::ast::Payload::PStr(items) if items.is_empty())
            }) {
                crate::gentype::gen_type_common::Mutable::Mutable
            } else {
                crate::gentype::gen_type_common::Mutable::Immutable
            };
            (
                name.txt.clone(),
                mutable_,
                translateCoreType_(ctx, arena, config, type_vars_gen, false, type_env, t),
            )
        }
        ObjectFieldDesc::OTinherit(t) => (
            "Inherit".to_string(),
            crate::gentype::gen_type_common::Mutable::Immutable,
            translateCoreType_(ctx, arena, config, type_vars_gen, false, type_env, t),
        ),
    }
}

fn translate_variant(
    ctx: &TypeContext,
    arena: &ParseArena,
    config: &crate::gentype::config::T,
    type_vars_gen: &crate::gentype::gen_ident::TypeVarsGen,
    type_env: &crate::gentype::type_env::T,
    core_type: &TypedCoreType,
    row_fields: &[RowFieldType],
) -> crate::gentype::translate_type_expr_from_types::Translation {
    match process_variant(row_fields) {
        ProcessVariant {
            no_payloads,
            payloads,
            inherits,
        } => {
            let as_string = crate::gentype::annotation::has_attribute(
                arena,
                crate::gentype::annotation::tag_is_string,
                &core_type.ctyp_attributes,
            );
            let as_int = crate::gentype::annotation::has_attribute(
                arena,
                crate::gentype::annotation::tag_is_int,
                &core_type.ctyp_attributes,
            );
            let mut last_bs_int = -1;
            let no_payloads = no_payloads
                .into_iter()
                .map(|(label, attributes)| {
                    let label_js = if as_string {
                        match crate::gentype::annotation::get_as_string(arena, &attributes) {
                            Some(label_renamed) => LabelJs::StringLabel(
                                crate::gentype::emit_text::escape_string_contents(&label_renamed),
                            ),
                            None if is_number(&label) => LabelJs::IntLabel(label),
                            None => LabelJs::StringLabel(label),
                        }
                    } else if as_int {
                        match crate::gentype::annotation::get_as_int(arena, &attributes) {
                            Some(n) => {
                                last_bs_int = n;
                                LabelJs::IntLabel(n.to_string())
                            }
                            None => {
                                last_bs_int += 1;
                                LabelJs::IntLabel(last_bs_int.to_string())
                            }
                        }
                    } else if is_number(&label) {
                        LabelJs::IntLabel(label)
                    } else {
                        LabelJs::StringLabel(label)
                    };
                    VariantCase { label_js }
                })
                .collect::<Vec<_>>();

            let payloads_translations = payloads
                .iter()
                .map(|(label, attributes, payload)| {
                    (
                        label.clone(),
                        attributes.clone(),
                        translateCoreType_(
                            ctx,
                            arena,
                            config,
                            type_vars_gen,
                            false,
                            type_env,
                            payload,
                        ),
                    )
                })
                .collect::<Vec<_>>();
            let payloads = payloads_translations
                .iter()
                .map(|(label, _, translation)| Payload {
                    case: VariantCase {
                        label_js: if is_number(label) {
                            LabelJs::IntLabel(label.clone())
                        } else {
                            LabelJs::StringLabel(label.clone())
                        },
                    },
                    t: translation.type_.clone(),
                })
                .collect::<Vec<_>>();
            let inherits_translations =
                translateCoreTypes_(ctx, arena, config, type_vars_gen, type_env, &inherits);
            let inherits = inherits_translations
                .iter()
                .map(|translation| translation.type_.clone())
                .collect::<Vec<_>>();
            let mut dependencies = inherits_translations
                .iter()
                .flat_map(|translation| translation.dependencies.clone())
                .collect::<Vec<_>>();
            dependencies.extend(
                payloads_translations
                    .iter()
                    .flat_map(|(_, _, translation)| translation.dependencies.clone()),
            );
            crate::gentype::translate_type_expr_from_types::Translation {
                dependencies,
                type_: create_variant(inherits, no_payloads, payloads, true, None, false),
            }
        }
    }
}

fn translate_package(
    ctx: &TypeContext,
    arena: &ParseArena,
    config: &crate::gentype::config::T,
    type_vars_gen: &crate::gentype::gen_ident::TypeVarsGen,
    type_env: &crate::gentype::type_env::T,
    package: &crate::types::typedtree::PackageType,
) -> crate::gentype::translate_type_expr_from_types::Translation {
    match crate::gentype::type_env::lookup_module_type_signature(&package.pack_path, type_env) {
        Some((_, signature, type_env)) => {
            let type_equations_translation = package
                .pack_fields
                .iter()
                .map(|(x, t)| {
                    (
                        longident_to_strings(arena, arena.get_longident(x.txt)),
                        translateCoreType_(ctx, arena, config, type_vars_gen, false, &type_env, t),
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
                crate::gentype::translate_type_expr_from_types::signature_to_module_runtime_representation(
                    ctx,
                    config,
                    type_vars_gen,
                    &type_env1,
                    &signature,
                );
            let mut dependencies = dependencies_from_type_equations;
            dependencies.append(&mut dependencies_from_record_type);
            crate::gentype::translate_type_expr_from_types::Translation {
                dependencies,
                type_,
            }
        }
        None => crate::gentype::translate_type_expr_from_types::Translation {
            dependencies: vec![],
            type_: unknown(),
        },
    }
}

fn label_name(label: &ArgLabel) -> String {
    match label {
        ArgLabel::Nolabel => String::new(),
        ArgLabel::Labelled(loc) | ArgLabel::Optional(loc) => loc.txt.clone(),
    }
}

fn longident_to_strings(arena: &ParseArena, longident: &Longident) -> Vec<String> {
    match longident {
        Longident::Lident(s) => vec![arena.get_string(*s).to_string()],
        Longident::Ldot(prefix, s) => {
            let mut out = longident_to_strings(arena, prefix);
            out.push(arena.get_string(*s).to_string());
            out
        }
        Longident::Lapply(prefix, _) => longident_to_strings(arena, prefix),
    }
}
