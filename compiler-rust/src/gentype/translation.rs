// Port of compiler/gentype/Translation.ml:1-217.

use crate::gentype::code_item;
use crate::gentype::gen_type_common::{Dep, Type, dep_to_string, ident_with};
use crate::parse_arena::ParseArena;
use crate::parser::ast::Attributes;
use crate::types::typedtree::TypedValueDescription;

/// What translating a module produces.
pub type T = code_item::Translation;

/// What every translation of one typed artifact reads: the trees the
/// artifact is made of, and the generated file and resolver that imports
/// are resolved with. The configuration is passed separately, as module
/// attributes can change it for the items they enclose.
#[derive(Clone, Copy)]
pub struct Input<'a> {
    /// Node storage of the artifact's typed tree.
    pub ta: &'a crate::types::typedtree::TypedArena,
    /// The type state the typed tree's type expressions live in.
    pub ctx: &'a crate::types::context::TypeContext,
    /// The parse arena holding the tree's attributes, strings and locations.
    pub arena: &'a ParseArena,
    /// The generated file's path, relative to the project root.
    pub output_file_relative: &'a str,
    /// Finds the source directories of the modules the translation imports.
    pub resolver: &'a crate::gentype::module_resolver::Resolver,
}

/// An empty translation.
pub fn empty() -> T {
    T {
        import_types: vec![],
        code_items: vec![],
        type_declarations: vec![],
    }
}

/// The name an import is deduplicated by: its type name and alias.
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

/// The translations' imports, code items and type declarations, each in order.
pub fn combine(translations: Vec<T>) -> T {
    let mut import_types = Vec::new();
    let mut code_items = Vec::new();
    let mut type_declarations = Vec::new();

    for code_item::Translation {
        import_types: item_import_types,
        code_items: item_code_items,
        type_declarations: item_type_declarations,
    } in translations
    {
        import_types.extend(item_import_types);
        code_items.extend(item_code_items);
        type_declarations.extend(item_type_declarations);
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

/// The imports a dependency needs: ReScript's `list` from the pervasives
/// module, and a type of another module from that module's generated file;
/// none for this module's types.
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
                &crate::gentype::module_name::RESCRIPT_PERVASIVES.to_string(),
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

/// The imports `dependencies` need.
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

/// How a value is exported: its ReScript name, the name it is exported
/// under when `@genType.as` renames it, and its doc comment.
pub struct ValueExport<'n> {
    /// The value's name in the ReScript source.
    pub name: &'n str,
    /// The exported name, when it differs from `name`.
    pub name_as: Option<String>,
    /// The doc comment emitted above the export.
    pub doc_string: crate::gentype::gen_type_common::doc_string::T,
}

/// `Translation.translateValue`: the export of a value annotated with
/// `@genType`, renamed and documented by its `attributes`.
pub fn translate_value<F>(
    input: Input<'_>,
    attributes: &Attributes,
    config: &crate::gentype::config::T,
    type_env: &crate::gentype::type_env::T,
    type_expr: crate::types::type_expr::TypeExprRef,
    add_annotations_to_function: F,
    name: &str,
) -> T
where
    F: Fn(Type) -> Type,
{
    let arena = input.arena;
    let name_as = match crate::gentype::annotation::get_gentype_as_renaming(arena, attributes) {
        Some(s) => s,
        _ => name.to_string(),
    };
    translate_value_with_name_as(
        input,
        config,
        type_env,
        type_expr,
        add_annotations_to_function,
        ValueExport {
            name,
            name_as: Some(name_as),
            doc_string: crate::gentype::annotation::doc_string_from_attrs(arena, attributes),
        },
    )
}

/// The export of a value of type `type_expr` whose name and renaming are
/// already known; `add_annotations_to_function` adjusts the translated type.
pub fn translate_value_with_name_as<F>(
    input: Input<'_>,
    config: &crate::gentype::config::T,
    type_env: &crate::gentype::type_env::T,
    type_expr: crate::types::type_expr::TypeExprRef,
    add_annotations_to_function: F,
    value: ValueExport<'_>,
) -> T
where
    F: Fn(Type) -> Type,
{
    // Mirrors compiler/gentype/Translation.ml:80-112. This entry is used by
    // Types.signature callers after Annotation.ml-equivalent decl attribute
    // scanning has already recovered `name_as`.
    let Input {
        ctx,
        output_file_relative,
        resolver,
        ..
    } = input;
    let ValueExport {
        name,
        name_as,
        doc_string,
    } = value;
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

/// `Translation.translatePrimitive`: translate an `external`. One annotated
/// with `@genType.import` becomes an import of the value it names; others
/// translate to nothing.
pub fn translate_primitive(
    input: Input<'_>,
    config: &crate::gentype::config::T,
    type_env: &crate::gentype::type_env::T,
    value_description: &TypedValueDescription,
) -> T {
    let Input {
        ta,
        ctx,
        arena,
        output_file_relative,
        resolver,
        ..
    } = input;
    if crate::gentype::debug::translation.load(std::sync::atomic::Ordering::Relaxed) {
        crate::gentype::log_::item("Translate Primitive\n");
    }

    // external foo : someType = "abc" -- the extern name is "abc"
    let name_of_extern = match &value_description.val_prim {
        Some(crate::parser::ast::PrimitiveRepr::PrimName(name)) => arena.get_string(*name),
        Some(crate::parser::ast::PrimitiveRepr::PrimFfi { name, .. }) => name.as_str(),
        _ => "",
    };
    let value_name = if name_of_extern.is_empty() {
        value_description.val_id.name().to_string()
    } else {
        name_of_extern.to_string()
    };

    let type_expr_translation = crate::gentype::translate_core_type::translate_core_type(
        ta,
        ctx,
        arena,
        config,
        type_env,
        ta.core_type(value_description.val_desc),
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

/// Add, for each type declaration, an alias under each name that module
/// aliases make it available as.
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
                            annotation: type_declaration.export_from_type_declaration.annotation,
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
