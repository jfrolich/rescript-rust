// Port of compiler/gentype/Translation.ml:1-217.
// This Stage 1 GenType port is intentionally not wired into the crate yet.

use crate::gentype::code_item;
use crate::gentype::gen_type_common::{Dep, Type, dep_to_string, ident_with};
use crate::parse_arena::ParseArena;
use crate::parser::ast::Attributes;
use crate::types::typedtree::TypedValueDescription;

pub type T = code_item::Translation;

pub fn empty() -> T {
    T {
        import_types: vec![],
        code_items: vec![],
        type_declarations: vec![],
    }
}

pub fn get_import_type_unique_name(import_type: &code_item::ImportType) -> String {
    let code_item::ImportType {
        type_name,
        as_type_name,
        ..
    } = import_type;
    format!(
        "{}{}",
        type_name,
        match as_type_name {
            None => String::new(),
            Some(s) => format!("_as_{s}"),
        }
    )
}

pub fn import_type_compare(
    i1: &code_item::ImportType,
    i2: &code_item::ImportType,
) -> std::cmp::Ordering {
    get_import_type_unique_name(i1).cmp(&get_import_type_unique_name(i2))
}

pub fn combine(translations: &[T]) -> T {
    let mut import_types = Vec::new();
    let mut code_items = Vec::new();
    let mut type_declarations = Vec::new();

    for code_item::Translation {
        import_types: item_import_types,
        code_items: item_code_items,
        type_declarations: item_type_declarations,
    } in translations
    {
        import_types.extend(item_import_types.clone());
        code_items.extend(item_code_items.clone());
        type_declarations.extend(item_type_declarations.clone());
    }

    T {
        import_types,
        code_items,
        type_declarations,
    }
}

/// Applies type parameters to types (for all).
pub fn abstract_the_type_parameters(type_vars: Vec<String>, type_: Type) -> Type {
    match type_ {
        Type::Function(mut function_) => {
            function_.type_vars = type_vars;
            Type::Function(function_)
        }
        _ => type_,
    }
}

pub fn dep_to_import_type(
    config: &crate::gentype::config::T,
    output_file_relative: &str,
    resolver: &crate::gentype::module_resolver::Resolver,
    dep: &Dep,
) -> Vec<code_item::ImportType> {
    match dep {
        _ if crate::gentype::dependencies::is_internal(dep) => vec![],
        Dep::External(name) if name == "list" => vec![code_item::ImportType {
            type_name: "list".to_string(),
            as_type_name: None,
            import_path: crate::gentype::module_resolver::import_path_for_reason_module_name(
                config,
                output_file_relative,
                resolver,
                &crate::gentype::module_name::rescript_pervasives.to_string(),
            ),
        }],
        Dep::External(_) => vec![],
        Dep::Internal(_) => vec![],
        Dep::Dot(_, _) => {
            let module_name = crate::gentype::dependencies::get_outer_module_name(dep);
            let type_name = dep_to_string(
                &crate::gentype::dependencies::remove_external_outer_module(dep),
            );
            let as_type_name = match crate::gentype::dependencies::is_internal(dep) {
                true => None,
                false => Some(dep_to_string(dep)),
            };
            let import_path = crate::gentype::module_resolver::import_path_for_reason_module_name(
                config,
                output_file_relative,
                resolver,
                &module_name,
            );
            vec![code_item::ImportType {
                type_name,
                as_type_name,
                import_path,
            }]
        }
    }
}

pub fn translate_dependencies(
    config: &crate::gentype::config::T,
    output_file_relative: &str,
    resolver: &crate::gentype::module_resolver::Resolver,
    dependencies: &[Dep],
) -> Vec<code_item::ImportType> {
    dependencies
        .iter()
        .flat_map(|dep| dep_to_import_type(config, output_file_relative, resolver, dep))
        .collect()
}

pub fn translate_value<F>(
    ctx: &crate::types::context::TypeContext,
    arena: &ParseArena,
    attributes: &Attributes,
    config: &crate::gentype::config::T,
    doc_string: crate::gentype::gen_type_common::doc_string::T,
    output_file_relative: &str,
    resolver: &crate::gentype::module_resolver::Resolver,
    type_env: &crate::gentype::type_env::T,
    type_expr: crate::types::type_expr::TypeExprRef,
    add_annotations_to_function: F,
    name: &str,
) -> T
where
    F: Fn(Type) -> Type,
{
    let name_as = match crate::gentype::annotation::get_gentype_as_renaming(arena, attributes) {
        Some(s) => s,
        _ => name.to_string(),
    };
    translate_value_with_name_as(
        ctx,
        Some(name_as),
        config,
        doc_string,
        output_file_relative,
        resolver,
        type_env,
        type_expr,
        add_annotations_to_function,
        name,
    )
}

pub fn translate_value_with_name_as<F>(
    ctx: &crate::types::context::TypeContext,
    name_as: Option<String>,
    config: &crate::gentype::config::T,
    doc_string: crate::gentype::gen_type_common::doc_string::T,
    output_file_relative: &str,
    resolver: &crate::gentype::module_resolver::Resolver,
    type_env: &crate::gentype::type_env::T,
    type_expr: crate::types::type_expr::TypeExprRef,
    add_annotations_to_function: F,
    name: &str,
) -> T
where
    F: Fn(Type) -> Type,
{
    // Mirrors compiler/gentype/Translation.ml:80-112. This entry is used by
    // Types.signature callers after Annotation.ml-equivalent decl attribute
    // scanning has already recovered `name_as`.
    let name_as = name_as.unwrap_or_else(|| name.to_string());
    let type_expr_translation =
        crate::gentype::translate_type_expr_from_types::translate_type_expr_from_types(
            ctx, config, type_env, &type_expr,
        );
    let type_vars = crate::gentype::type_vars::free(&type_expr_translation.type_);
    let type_ = add_annotations_to_function(abstract_the_type_parameters(
        type_vars,
        type_expr_translation.type_,
    ));
    let resolved_name_original = crate::gentype::resolved_name::to_string(
        &crate::gentype::type_env::add_module_path(type_env, name),
    );
    let resolved_name = crate::gentype::type_env::add_module_path(type_env, &name_as);
    let module_access_path =
        crate::gentype::type_env::get_module_access_path(&resolved_name_original, type_env);
    let code_items = vec![code_item::T::ExportValue(code_item::ExportValue {
        doc_string,
        module_access_path,
        original_name: name.to_string(),
        resolved_name,
        type_,
    })];

    T {
        import_types: translate_dependencies(
            config,
            output_file_relative,
            resolver,
            &type_expr_translation.dependencies,
        ),
        code_items,
        type_declarations: vec![],
    }
}

/// [@genType]
/// [@module] external myBanner : ReasonReact.reactClass = "./MyBanner";
pub fn translate_primitive(
    ctx: &crate::types::context::TypeContext,
    arena: &ParseArena,
    config: &crate::gentype::config::T,
    output_file_relative: &str,
    resolver: &crate::gentype::module_resolver::Resolver,
    type_env: &crate::gentype::type_env::T,
    value_description: &TypedValueDescription,
) -> T {
    if crate::gentype::debug::translation.load(std::sync::atomic::Ordering::Relaxed) {
        crate::gentype::log_::item("Translate Primitive\n");
    }

    let value_name = match value_description.val_prim.as_slice() {
        [] => value_description.val_id.name().to_string(),
        [first, ..] if first.is_empty() => value_description.val_id.name().to_string(),
        [name_of_extern, ..] => name_of_extern.clone(),
    };

    let type_expr_translation = crate::gentype::translate_core_type::translate_core_type(
        ctx,
        arena,
        config,
        type_env,
        &value_description.val_desc,
    );
    let (attribute_import, attribute_renaming) =
        crate::gentype::annotation::get_attribute_import_renaming(
            arena,
            &value_description.val_attributes,
        );

    match attribute_import {
        Some(import_string) => {
            let as_path = match attribute_renaming {
                Some(as_path) => as_path,
                None => value_name.clone(),
            };
            let type_vars = crate::gentype::type_vars::free(&type_expr_translation.type_);
            let type_ = abstract_the_type_parameters(type_vars, type_expr_translation.type_);
            T {
                import_types: translate_dependencies(
                    config,
                    output_file_relative,
                    resolver,
                    &type_expr_translation.dependencies,
                ),
                code_items: vec![code_item::T::ImportValue(code_item::ImportValue {
                    as_path,
                    import_annotation: crate::gentype::annotation::import_from_string(
                        &import_string,
                    ),
                    type_,
                    value_name,
                })],
                type_declarations: vec![],
            }
        }
        None => T {
            import_types: vec![],
            code_items: vec![],
            type_declarations: vec![],
        },
    }
}

pub fn add_type_declarations_from_module_equations(
    type_env: &crate::gentype::type_env::T,
    translation: T,
) -> T {
    let eqs = crate::gentype::type_env::get_module_equations(type_env);
    let new_type_declarations = translation
        .type_declarations
        .iter()
        .flat_map(|type_declaration| {
            let export_type = &type_declaration.export_from_type_declaration.export_type;
            let equations = crate::gentype::resolved_name::apply_equations(
                &eqs,
                &export_type.resolved_type_name,
            );

            equations
                .into_iter()
                .map(|(x, y)| {
                    let mut new_export_type = export_type.clone();
                    new_export_type.name_as = None;
                    new_export_type.type_ = ident_with(
                        false,
                        export_type
                            .type_vars
                            .iter()
                            .map(|s| Type::TypeVar(s.clone()))
                            .collect(),
                        &crate::gentype::resolved_name::to_string(&y),
                    );
                    new_export_type.resolved_type_name = x;
                    code_item::TypeDeclaration {
                        export_from_type_declaration: code_item::ExportFromTypeDeclaration {
                            export_type: new_export_type,
                            annotation: type_declaration
                                .export_from_type_declaration
                                .annotation
                                .clone(),
                        },
                        import_types: vec![],
                    }
                })
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();

    match new_type_declarations.is_empty() {
        true => translation,
        false => {
            let mut translation = translation;
            translation.type_declarations.extend(new_type_declarations);
            translation
        }
    }
}
