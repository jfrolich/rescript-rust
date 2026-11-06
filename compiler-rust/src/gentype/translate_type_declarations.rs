// Port of compiler/gentype/TranslateTypeDeclarations.ml:1-373.

use crate::gentype::code_item;
use crate::gentype::gen_type_common::{
    Case as VariantCase, ClosedFlag, Field, LabelJs, Mutable, Optional, Payload, Type,
    create_variant, ident_with, sanitize_type_name, unknown,
};
use crate::location::Location;
use crate::parse_arena::{LocIdx, ParseArena};
use crate::parser::ast::Attributes;
use crate::parser::longident::Longident;
use crate::types::asttypes::MutableFlag;
use crate::types::decl::{
    Attribute as DeclAttribute, ConstructorArguments, ConstructorDeclaration, LabelDeclaration,
    RecordRepresentation, TypeKind, TypeRepresentation,
};
use crate::types::type_expr::TypeExprRef;
use crate::types::typedtree::{TypedCoreType, TypedTypeDeclaration};

#[derive(Debug, Clone)]
pub enum DeclarationKind {
    RecordDeclarationFromTypes(Vec<LabelDeclaration>, RecordRepresentation),
    GeneralDeclaration(Option<TypedCoreType>),
    GeneralDeclarationFromTypes(Option<TypeExprRef>),
    VariantDeclarationFromTypes(
        Vec<ConstructorDeclaration>,
        crate::types::VariantLayout,
        TypeRepresentation,
    ),
    NoDeclaration,
}

struct DeclarationAttributeInfo {
    doc_string: crate::gentype::gen_type_common::doc_string::T,
    annotation: crate::gentype::annotation::T,
    opaque: Option<bool>,
    import_string_opt: Option<String>,
    name_as: Option<String>,
}

pub fn create_export_type_from_type_declaration(
    annotation: crate::gentype::annotation::T,
    loc: crate::types::DeclLoc,
    name_as: Option<String>,
    opaque: Option<bool>,
    type_: Type,
    type_env: &crate::gentype::type_env::T,
    doc_string: crate::gentype::gen_type_common::doc_string::T,
    type_name: &str,
    type_vars: Vec<String>,
) -> code_item::ExportFromTypeDeclaration {
    // Mirrors compiler/gentype/TranslateTypeDeclarations.ml:11-21.
    let resolved_type_name =
        crate::gentype::type_env::add_module_path(type_env, &sanitize_type_name(type_name));
    code_item::ExportFromTypeDeclaration {
        export_type: code_item::ExportType {
            loc,
            name_as,
            opaque,
            type_,
            type_vars,
            resolved_type_name,
            doc_string,
        },
        annotation,
    }
}

pub fn create_case(
    arena: &ParseArena,
    label: &str,
    attributes: &Attributes,
    poly: bool,
) -> VariantCase {
    // Mirrors compiler/gentype/TranslateTypeDeclarations.ml:23-37.
    let label_js = match crate::gentype::annotation::get_attribute_payload(
        arena,
        crate::gentype::annotation::tag_is_as,
        attributes,
    ) {
        Some((_, crate::gentype::annotation::AttributePayload::IdentPayload(lid)))
            if longident_is_lident(arena, &lid, "null") =>
        {
            LabelJs::NullLabel
        }
        Some((_, crate::gentype::annotation::AttributePayload::IdentPayload(lid)))
            if longident_is_lident(arena, &lid, "undefined") =>
        {
            LabelJs::UndefinedLabel
        }
        Some((_, crate::gentype::annotation::AttributePayload::BoolPayload(b))) => {
            LabelJs::BoolLabel(b)
        }
        Some((_, crate::gentype::annotation::AttributePayload::FloatPayload(s))) => {
            LabelJs::FloatLabel(s)
        }
        Some((_, crate::gentype::annotation::AttributePayload::IntPayload(i))) => {
            LabelJs::IntLabel(i)
        }
        Some((_, crate::gentype::annotation::AttributePayload::StringPayload(as_label))) => {
            LabelJs::StringLabel(crate::gentype::emit_text::escape_string_contents(&as_label))
        }
        _ if poly && crate::gentype::gen_type_common::is_number(label) => {
            LabelJs::IntLabel(label.to_string())
        }
        _ => LabelJs::StringLabel(label.to_string()),
    };
    VariantCase { label_js }
}

fn create_variant_case(label: &str, tag: &Option<crate::types::VariantLiteralTag>) -> VariantCase {
    let label_js = match tag {
        Some(crate::types::VariantLiteralTag::String(value)) => {
            LabelJs::StringLabel(crate::gentype::emit_text::escape_string_contents(value))
        }
        Some(crate::types::VariantLiteralTag::Int(value)) => LabelJs::IntLabel(value.to_string()),
        Some(crate::types::VariantLiteralTag::Float(value)) => LabelJs::FloatLabel(value.clone()),
        Some(crate::types::VariantLiteralTag::BigInt(value)) => LabelJs::IntLabel(value.clone()),
        Some(crate::types::VariantLiteralTag::Bool(value)) => LabelJs::BoolLabel(*value),
        Some(crate::types::VariantLiteralTag::Null) => LabelJs::NullLabel,
        Some(crate::types::VariantLiteralTag::Undefined) => LabelJs::UndefinedLabel,
        None => LabelJs::StringLabel(label.to_string()),
    };
    VariantCase { label_js }
}

pub fn rename_record_field(arena: &ParseArena, attributes: &Attributes, name: &str) -> String {
    // Mirrors compiler/gentype/TranslateTypeDeclarations.ml:39-53.
    crate::gentype::annotation::check_unsupported_gentype_as_renaming(arena, attributes);
    match crate::gentype::annotation::get_as_string(arena, attributes) {
        Some(s) => crate::string_literal::ocaml_escaped(&s),
        None => unwrap_uppercase_exotic(name).to_string(),
    }
}

/// OCaml `Translate_type_declarations.declared_field_name`: a declared field
/// carries its runtime name; only the renaming that reaches gentype through
/// an expression's attributes still has to be read off one.
pub fn declared_field_name(locs: &dyn crate::types::DeclLocs, ld: &LabelDeclaration) -> String {
    crate::gentype::annotation::check_unsupported_decl_gentype_as_renaming(locs, &ld.ld_attributes);
    match &ld.ld_runtime_name {
        Some(s) => crate::string_literal::ocaml_escaped(s),
        None => unwrap_uppercase_exotic(ld.ld_id.name()).to_string(),
    }
}

#[allow(non_snake_case)]
pub fn traslate_declaration_kind(
    ctx: &crate::types::context::TypeContext,
    arena: &ParseArena,
    config: &crate::gentype::config::T,
    loc: Location,
    loc_idx: LocIdx,
    output_file_relative: &str,
    resolver: &crate::gentype::module_resolver::Resolver,
    type_attributes: &Attributes,
    type_env: &crate::gentype::type_env::T,
    type_name: &str,
    type_vars: Vec<String>,
    declaration_kind: DeclarationKind,
) -> Vec<code_item::TypeDeclaration> {
    // Mirrors compiler/gentype/TranslateTypeDeclarations.ml:54-321.
    let doc_string = crate::gentype::annotation::doc_string_from_attrs(arena, type_attributes);
    let annotation =
        crate::gentype::annotation::from_attributes(arena, config, loc_idx, type_attributes);
    let opaque = match annotation == crate::gentype::annotation::T::GenTypeOpaque {
        true => Some(true),
        false => None,
    };
    let (import_string_opt, name_as) =
        crate::gentype::annotation::get_attribute_import_renaming(arena, type_attributes);
    let attribute_info = DeclarationAttributeInfo {
        doc_string,
        annotation,
        opaque,
        import_string_opt,
        name_as,
    };
    traslate_declaration_kind_with_attribute_info(
        ctx,
        arena,
        config,
        loc,
        output_file_relative,
        resolver,
        attribute_info,
        type_env,
        type_name,
        type_vars,
        declaration_kind,
    )
}

#[allow(non_snake_case)]
pub fn traslate_declaration_kind_from_decl_attributes(
    ctx: &crate::types::context::TypeContext,
    arena: &ParseArena,
    config: &crate::gentype::config::T,
    loc: Location,
    output_file_relative: &str,
    resolver: &crate::gentype::module_resolver::Resolver,
    type_attributes: &[DeclAttribute],
    type_env: &crate::gentype::type_env::T,
    type_name: &str,
    type_vars: Vec<String>,
    declaration_kind: DeclarationKind,
) -> Vec<code_item::TypeDeclaration> {
    // OCaml TranslateSignatureFromTypes.ml:3-29 passes
    // Types.type_declaration.type_attributes through to
    // TranslateTypeDeclarations.ml:54-321. Rust decl attributes have already
    // been converted out of parser payloads, so compute the same annotation
    // facts from decl::Attribute instead of using an empty parser attribute set.
    let doc_string = crate::gentype::annotation::doc_string_from_decl_attrs(type_attributes);
    let annotation =
        crate::gentype::annotation::from_decl_attributes(config, &loc, type_attributes);
    let opaque = match annotation == crate::gentype::annotation::T::GenTypeOpaque {
        true => Some(true),
        false => None,
    };
    let (import_string_opt, name_as) =
        crate::gentype::annotation::get_decl_attribute_import_renaming(type_attributes);
    let attribute_info = DeclarationAttributeInfo {
        doc_string,
        annotation,
        opaque,
        import_string_opt,
        name_as,
    };
    traslate_declaration_kind_with_attribute_info(
        ctx,
        arena,
        config,
        loc,
        output_file_relative,
        resolver,
        attribute_info,
        type_env,
        type_name,
        type_vars,
        declaration_kind,
    )
}

fn traslate_declaration_kind_with_attribute_info(
    ctx: &crate::types::context::TypeContext,
    arena: &ParseArena,
    config: &crate::gentype::config::T,
    loc: Location,
    output_file_relative: &str,
    resolver: &crate::gentype::module_resolver::Resolver,
    attribute_info: DeclarationAttributeInfo,
    type_env: &crate::gentype::type_env::T,
    type_name: &str,
    type_vars: Vec<String>,
    declaration_kind: DeclarationKind,
) -> Vec<code_item::TypeDeclaration> {
    let DeclarationAttributeInfo {
        doc_string,
        annotation,
        opaque,
        import_string_opt,
        name_as,
    } = attribute_info;

    let return_type_declaration =
        |mut type_declaration: code_item::TypeDeclaration| -> Vec<code_item::TypeDeclaration> {
            if opaque == Some(true) {
                type_declaration.import_types.clear();
            }
            vec![type_declaration]
        };

    let handle_general_declaration =
        |translation: crate::gentype::translate_type_expr_from_types::Translation| {
            let export_from_type_declaration = create_export_type_from_type_declaration(
                annotation,
                ctx.intern_loc(loc),
                name_as.clone(),
                opaque,
                translation.type_,
                type_env,
                doc_string.clone(),
                type_name,
                type_vars.clone(),
            );
            let import_types = crate::gentype::translation::translate_dependencies(
                config,
                output_file_relative,
                resolver,
                &translation.dependencies,
            );
            code_item::TypeDeclaration {
                import_types,
                export_from_type_declaration,
            }
        };

    match (declaration_kind, import_string_opt) {
        (_, Some(import_string)) => {
            let type_name_original = type_name.to_string();
            let name_with_module_path = crate::gentype::resolved_name::to_string(
                &crate::gentype::type_env::add_module_path(type_env, &type_name_original),
            );
            let (type_name_imported, as_type_name) = match name_as.clone() {
                Some(as_string) => (as_string, format!("$${name_with_module_path}")),
                None => (
                    name_with_module_path.clone(),
                    format!("$${name_with_module_path}"),
                ),
            };
            let import_types = vec![code_item::ImportType {
                type_name: type_name_imported,
                as_type_name: Some(as_type_name.clone()),
                import_path: crate::gentype::import_path::from_string_unsafe(&import_string),
            }];
            let export_from_type_declaration = create_export_type_from_type_declaration(
                crate::gentype::annotation::T::GenType,
                ctx.intern_loc(loc),
                None,
                Some(false),
                ident_with(
                    true,
                    type_vars.iter().map(|s| Type::TypeVar(s.clone())).collect(),
                    &as_type_name,
                ),
                type_env,
                doc_string,
                &type_name_original,
                type_vars,
            );
            vec![code_item::TypeDeclaration {
                import_types,
                export_from_type_declaration,
            }]
        }
        (
            DeclarationKind::GeneralDeclarationFromTypes(None)
            | DeclarationKind::GeneralDeclaration(None),
            None,
        ) => return_type_declaration(code_item::TypeDeclaration {
            import_types: vec![],
            export_from_type_declaration: create_export_type_from_type_declaration(
                annotation,
                ctx.intern_loc(loc),
                name_as,
                Some(true),
                unknown(),
                type_env,
                doc_string,
                type_name,
                type_vars,
            ),
        }),
        (DeclarationKind::GeneralDeclarationFromTypes(Some(type_expr)), None) => {
            let translation =
                crate::gentype::translate_type_expr_from_types::translate_type_expr_from_types(
                    ctx, config, type_env, &type_expr,
                );
            return_type_declaration(handle_general_declaration(translation))
        }
        (DeclarationKind::GeneralDeclaration(Some(core_type)), None) => {
            let translation = crate::gentype::translate_core_type::translate_core_type(
                ctx, arena, config, type_env, &core_type,
            );
            let type_ = match (&core_type.ctyp_desc, translation.type_.clone()) {
                (
                    crate::types::typedtree::TypedCoreTypeDesc::Ttyp_variant(row_fields, _, _),
                    Type::Variant(mut variant),
                ) => {
                    let row_fields_variants =
                        crate::gentype::translate_core_type::process_variant(row_fields);
                    variant.no_payloads = row_fields_variants
                        .no_payloads
                        .iter()
                        .map(|(label, attributes)| create_case(arena, label, attributes, true))
                        .collect();
                    if variant.payloads.len() == row_fields_variants.payloads.len() {
                        variant.payloads = variant
                            .payloads
                            .into_iter()
                            .zip(row_fields_variants.payloads.iter())
                            .map(|(mut payload, (label, attributes, _))| {
                                payload.case = create_case(arena, label, attributes, true);
                                payload
                            })
                            .collect();
                    }
                    Type::Variant(variant)
                }
                _ => translation.type_,
            };
            return_type_declaration(handle_general_declaration(
                crate::gentype::translate_type_expr_from_types::Translation {
                    type_,
                    ..translation
                },
            ))
        }
        (DeclarationKind::RecordDeclarationFromTypes(label_declarations, representation), None) => {
            let unboxed = matches!(representation, RecordRepresentation::RecordUnboxed(_));
            let translation = translate_label_declarations(
                ctx,
                arena,
                config,
                type_env,
                false,
                unboxed,
                &label_declarations,
            );
            let import_types = crate::gentype::translation::translate_dependencies(
                config,
                output_file_relative,
                resolver,
                &translation.dependencies,
            );
            return_type_declaration(code_item::TypeDeclaration {
                import_types,
                export_from_type_declaration: create_export_type_from_type_declaration(
                    annotation,
                    ctx.intern_loc(loc),
                    name_as,
                    opaque,
                    translation.type_,
                    type_env,
                    doc_string,
                    type_name,
                    type_vars,
                ),
            })
        }
        (
            DeclarationKind::VariantDeclarationFromTypes(
                constructor_declarations,
                layout,
                type_representation,
            ),
            None,
        ) => {
            let tag_annotation = layout.matching_facts.tag_name.clone();
            let variants = constructor_declarations
                .iter()
                .enumerate()
                .map(|(position, constructor_declaration)| {
                    let case = &layout.constructors[position];
                    let tag = match case {
                        crate::types::VariantConstructorCase::Constant(tag) => &tag.literal,
                        crate::types::VariantConstructorCase::Block(block) => {
                            &block.tag().literal
                        }
                    };
                    let tag = tag.clone();
                    let name = constructor_declaration.cd_id.name().to_string();
                    let args_translation = match &constructor_declaration.cd_args {
                        ConstructorArguments::CstrTuple(type_exprs) => {
                            crate::gentype::translate_type_expr_from_types::translate_type_exprs_from_types(
                                ctx,
                                config,
                                type_env,
                                type_exprs,
                            )
                        }
                        ConstructorArguments::CstrRecord(label_declarations) => vec![
                            translate_label_declarations(
                                ctx,
                                arena,
                                config,
                                type_env,
                                true,
                                type_representation == TypeRepresentation::Unboxed,
                                label_declarations,
                            ),
                        ],
                    };
                    let arg_types = args_translation
                        .iter()
                        .map(|translation| translation.type_.clone())
                        .collect::<Vec<_>>();
                    let import_types = crate::gentype::translation::translate_dependencies(
                        config,
                        output_file_relative,
                        resolver,
                        &args_translation
                            .iter()
                            .flat_map(|translation| translation.dependencies.clone())
                            .collect::<Vec<_>>(),
                    );
                    (name, tag, arg_types, import_types)
                })
                .collect::<Vec<_>>();

            let no_payloads = variants
                .iter()
                .filter(|(_, _, arg_types, _)| arg_types.is_empty())
                .map(|(name, tag, _, _)| create_variant_case(name, tag))
                .collect::<Vec<_>>();
            let payloads = variants
                .iter()
                .filter(|(_, _, arg_types, _)| !arg_types.is_empty())
                .map(|(name, tag, arg_types, _)| {
                    let type_ = match arg_types.as_slice() {
                        [type_] => type_.clone(),
                        _ => Type::Tuple(arg_types.clone()),
                    };
                    Payload {
                        case: create_variant_case(name, tag),
                        t: type_,
                    }
                })
                .collect::<Vec<_>>();
            let variant_typ = create_variant(
                vec![],
                no_payloads,
                payloads,
                false,
                tag_annotation,
                type_representation == TypeRepresentation::Unboxed
                    || layout.configuration().unboxed,
            );
            let resolved_type_name =
                crate::gentype::type_env::add_module_path(type_env, &sanitize_type_name(type_name));
            let export_from_type_declaration = code_item::ExportFromTypeDeclaration {
                export_type: code_item::ExportType {
                    loc: ctx.intern_loc(loc),
                    name_as,
                    opaque,
                    type_: variant_typ,
                    type_vars,
                    resolved_type_name,
                    doc_string,
                },
                annotation,
            };
            let import_types = variants
                .into_iter()
                .flat_map(|(_, _, _, import_types)| import_types)
                .collect();
            return_type_declaration(code_item::TypeDeclaration {
                export_from_type_declaration,
                import_types,
            })
        }
        (DeclarationKind::NoDeclaration, None) => vec![],
    }
}

pub fn has_some_gadt_leaf(constructor_declarations: &[ConstructorDeclaration]) -> bool {
    // Mirrors compiler/gentype/TranslateTypeDeclarations.ml:323-326.
    constructor_declarations
        .iter()
        .any(|declaration| declaration.cd_res.is_some())
}

pub fn translate_type_declaration(
    ctx: &crate::types::context::TypeContext,
    arena: &ParseArena,
    config: &crate::gentype::config::T,
    output_file_relative: &str,
    resolver: &crate::gentype::module_resolver::Resolver,
    type_env: &crate::gentype::type_env::T,
    type_declaration: &TypedTypeDeclaration,
) -> Vec<code_item::TypeDeclaration> {
    // Mirrors compiler/gentype/TranslateTypeDeclarations.ml:328-351.
    if crate::gentype::debug::translation.load(std::sync::atomic::Ordering::Relaxed) {
        crate::gentype::log_::item(&format!(
            "Translate Type Declaration {}\n",
            type_declaration.typ_id.name()
        ));
    }
    let type_name = type_declaration.typ_id.name().to_string();
    let type_params = type_declaration
        .typ_params
        .iter()
        .map(|(core_type, _)| core_type.clone())
        .collect::<Vec<_>>();
    let type_vars = crate::gentype::type_vars::extract_from_core_type(&type_params);
    let declaration_kind = match &type_declaration.typ_type.type_kind {
        TypeKind::TypeRecord(label_declarations, representation) => {
            DeclarationKind::RecordDeclarationFromTypes(
                label_declarations.to_vec(),
                representation.clone(),
            )
        }
        TypeKind::TypeVariant(constructor_declarations, layout_ref) => {
            DeclarationKind::VariantDeclarationFromTypes(
                constructor_declarations.to_vec(),
                ctx.variant_layout(*layout_ref),
                type_declaration.typ_type.type_representation,
            )
        }
        TypeKind::TypeAbstract => {
            DeclarationKind::GeneralDeclaration(type_declaration.typ_manifest.clone())
        }
        _ => DeclarationKind::NoDeclaration,
    };
    traslate_declaration_kind(
        ctx,
        arena,
        config,
        arena.to_location(type_declaration.typ_loc),
        type_declaration.typ_loc,
        output_file_relative,
        resolver,
        &type_declaration.typ_attributes,
        type_env,
        &type_name,
        type_vars,
        declaration_kind,
    )
}

pub fn add_type_declaration_id_to_type_env(
    type_env: &crate::gentype::type_env::T,
    type_declaration: &TypedTypeDeclaration,
) {
    // Mirrors compiler/gentype/TranslateTypeDeclarations.ml:353-355.
    crate::gentype::type_env::new_type(type_declaration.typ_id.name(), type_env);
}

pub fn translate_type_declarations(
    ctx: &crate::types::context::TypeContext,
    arena: &ParseArena,
    config: &crate::gentype::config::T,
    output_file_relative: &str,
    recursive: bool,
    resolver: &crate::gentype::module_resolver::Resolver,
    type_env: &crate::gentype::type_env::T,
    type_declarations: &[TypedTypeDeclaration],
) -> Vec<code_item::TypeDeclaration> {
    // Mirrors compiler/gentype/TranslateTypeDeclarations.ml:357-373.
    if recursive {
        for type_declaration in type_declarations {
            add_type_declaration_id_to_type_env(type_env, type_declaration);
        }
    }
    type_declarations
        .iter()
        .flat_map(|type_declaration| {
            let res = translate_type_declaration(
                ctx,
                arena,
                config,
                output_file_relative,
                resolver,
                type_env,
                type_declaration,
            );
            if !recursive {
                add_type_declaration_id_to_type_env(type_env, type_declaration);
            }
            res
        })
        .collect()
}

fn translate_label_declarations(
    ctx: &crate::types::context::TypeContext,
    _arena: &ParseArena,
    config: &crate::gentype::config::T,
    type_env: &crate::gentype::type_env::T,
    inline: bool,
    unboxed_annotation: bool,
    label_declarations: &[LabelDeclaration],
) -> crate::gentype::translate_type_expr_from_types::Translation {
    // Mirrors compiler/gentype/TranslateTypeDeclarations.ml:91-143.
    let field_translations = label_declarations
        .iter()
        .map(|label_declaration| {
            let attributes = &label_declaration.ld_attributes;
            let name = declared_field_name(ctx, label_declaration);
            let mutable_ = match label_declaration.ld_mutable {
                MutableFlag::Mutable => Mutable::Mutable,
                MutableFlag::Immutable => Mutable::Immutable,
            };
            (
                name,
                mutable_,
                label_declaration.ld_optional,
                crate::gentype::translate_type_expr_from_types::translate_type_expr_from_types(
                    ctx,
                    config,
                    type_env,
                    &label_declaration.ld_type,
                ),
                crate::gentype::annotation::doc_string_from_decl_attrs(attributes),
            )
        })
        .collect::<Vec<_>>();

    let dependencies = field_translations
        .iter()
        .flat_map(|(_, _, _, translation, _)| translation.dependencies.clone())
        .collect::<Vec<_>>();
    let fields = field_translations
        .into_iter()
        .map(|(name, mutable_, optional_, translation, doc_string)| {
            let (optional, type_) = match translation.type_ {
                Type::Option(type1) if optional_ => (Optional::Optional, *type1),
                type_ => (Optional::Mandatory, type_),
            };
            Field {
                mutable_,
                name_js: name,
                optional,
                type_,
                doc_string,
            }
        })
        .collect::<Vec<_>>();
    let type_ = match fields.as_slice() {
        [field] if unboxed_annotation => field.type_.clone(),
        _ => Type::Object(
            match inline {
                true => ClosedFlag::Inline,
                false => ClosedFlag::Closed,
            },
            fields,
        ),
    };
    crate::gentype::translate_type_expr_from_types::Translation {
        dependencies,
        type_,
    }
}

fn longident_is_lident(arena: &ParseArena, longident: &Longident, expected: &str) -> bool {
    match longident {
        Longident::Lident(s) => arena.get_string(*s) == expected,
        _ => false,
    }
}

fn unwrap_uppercase_exotic(name: &str) -> &str {
    let bytes = name.as_bytes();
    if bytes.len() >= 3 && bytes[0] == b'\\' && bytes[1] == b'"' && bytes[bytes.len() - 1] == b'"' {
        &name[2..name.len() - 1]
    } else {
        name
    }
}
