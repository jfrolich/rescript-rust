// Port of compiler/gentype/TranslateTypeDeclarations.ml:1-373.

use crate::gentype::code_item;
use crate::gentype::gen_type_common::{
    Case as VariantCase, ClosedFlag, Field, LabelJs, Mutable, Optional, Payload, Type,
    create_variant, ident_with, sanitize_type_name, unknown,
};
use crate::gentype::translation::Input;
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
use crate::types::typedtree::TypedTypeDeclaration;

/// What a type declaration defines, in the form it is translated from.
#[derive(Debug, Clone)]
pub enum DeclarationKind {
    /// A record type, with its fields and representation.
    RecordDeclarationFromTypes(Vec<LabelDeclaration>, RecordRepresentation),
    /// An abstract type or an abbreviation, with the manifest as written.
    GeneralDeclaration(Option<crate::types::typedtree::TCoreTypeIdx>),
    /// An abstract type or an abbreviation, with its inferred manifest.
    GeneralDeclarationFromTypes(Option<TypeExprRef>),
    /// A variant type, with its constructors, layout and representation.
    VariantDeclarationFromTypes(
        Vec<ConstructorDeclaration>,
        crate::types::VariantLayout,
        TypeRepresentation,
    ),
    /// A declaration gentype does not translate, such as a GADT.
    NoDeclaration,
}

/// A type declaration to translate: where it is, its name, the names of its
/// type parameters, and what it declares.
pub struct Declaration<'a> {
    /// The declaration's location.
    pub loc: Location,
    /// The declared type's name.
    pub type_name: &'a str,
    /// The names of the declaration's type parameters.
    pub type_vars: Vec<String>,
    /// What the declaration declares.
    pub kind: DeclarationKind,
}

struct DeclarationAttributeInfo {
    doc_string: crate::gentype::gen_type_common::doc_string::T,
    annotation: crate::gentype::annotation::T,
    opaque: Option<bool>,
    import_string_opt: Option<String>,
    name_as: Option<String>,
}

/// What every export of one type declaration shares: the type environment
/// its name is resolved in, its doc comment, its name and its type
/// parameters.
pub struct ExportTypeHeader<'a> {
    /// The environment of the module declaring the type.
    pub type_env: &'a crate::gentype::type_env::T,
    /// The declaration's doc comment.
    pub doc_string: crate::gentype::gen_type_common::doc_string::T,
    /// The declared type's name.
    pub type_name: &'a str,
    /// The names of the declaration's type parameters.
    pub type_vars: Vec<String>,
}

/// `createExportTypeFromTypeDeclaration`: the export of the declaration
/// described by `header` as `type_`.
pub fn create_export_type_from_type_declaration(
    header: &ExportTypeHeader<'_>,
    annotation: crate::gentype::annotation::T,
    loc: crate::types::DeclLoc,
    name_as: Option<String>,
    opaque: Option<bool>,
    type_: Type,
) -> code_item::ExportFromTypeDeclaration {
    // Mirrors compiler/gentype/TranslateTypeDeclarations.ml:11-21.
    let ExportTypeHeader {
        type_env,
        doc_string,
        type_name,
        type_vars,
    } = header;
    let doc_string = doc_string.clone();
    let type_vars = type_vars.clone();
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

/// The variant case of `label`, with the runtime value its `@as` attribute
/// gives, or else the label; `poly` makes numeric labels numbers.
pub fn create_case(
    arena: &ParseArena,
    label: &str,
    attributes: &Attributes,
    poly: bool,
) -> crate::gentype::annotation::Read<VariantCase> {
    // Mirrors compiler/gentype/TranslateTypeDeclarations.ml:23-37.
    let label_js = match crate::gentype::annotation::get_attribute_payload(
        arena,
        crate::gentype::annotation::tag_is_as,
        attributes,
    )? {
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
    Ok(VariantCase { label_js })
}

/// translate_type_declarations.ml `create_variant_case`: the case's runtime
/// literal, which is its name when it has no `@as`.
fn create_variant_case(tag: &crate::types::VariantLiteralTag) -> VariantCase {
    let label_js = match tag {
        crate::types::VariantLiteralTag::String(value) => {
            LabelJs::StringLabel(crate::gentype::emit_text::escape_string_contents(value))
        }
        crate::types::VariantLiteralTag::Int(value) => LabelJs::IntLabel(value.to_string()),
        crate::types::VariantLiteralTag::Float(value) => LabelJs::FloatLabel(value.clone()),
        crate::types::VariantLiteralTag::BigInt(value) => LabelJs::IntLabel(value.clone()),
        crate::types::VariantLiteralTag::Bool(value) => LabelJs::BoolLabel(*value),
        crate::types::VariantLiteralTag::Null => LabelJs::NullLabel,
        crate::types::VariantLiteralTag::Undefined => LabelJs::UndefinedLabel,
    };
    VariantCase { label_js }
}

/// The JavaScript name of a record field: its `@as` name, or else its own.
pub fn rename_record_field(
    arena: &ParseArena,
    notes: &crate::gentype::log_::Notes,
    attributes: &Attributes,
    name: &str,
) -> crate::gentype::annotation::Read<String> {
    // Mirrors compiler/gentype/TranslateTypeDeclarations.ml:39-53.
    crate::gentype::annotation::check_unsupported_gentype_as_renaming(arena, notes, attributes)?;
    Ok(
        match crate::gentype::annotation::get_as_string(arena, attributes)? {
            Some(s) => crate::string_literal::ocaml_escaped(&s),
            None => unwrap_uppercase_exotic(name).to_string(),
        },
    )
}

/// OCaml `Translate_type_declarations.declared_field_name`: a declared field
/// carries its runtime name; only the renaming that reaches gentype through
/// an expression's attributes still has to be read off one.
pub fn declared_field_name(
    ctx: &crate::types::context::TypeContext,
    arena: &ParseArena,
    notes: &crate::gentype::log_::Notes,
    ld: &LabelDeclaration,
) -> crate::gentype::annotation::Read<String> {
    crate::gentype::annotation::check_unsupported_decl_gentype_as_renaming(
        ctx,
        arena,
        notes,
        &ld.ld_attributes,
    )?;
    Ok(match &ld.ld_runtime_name {
        Some(s) => crate::string_literal::ocaml_escaped(s),
        None => unwrap_uppercase_exotic(ld.ld_id.name()).to_string(),
    })
}

/// `TranslateTypeDeclarations.traslateDeclarationKind`: translate a type
/// declaration with the parse-tree `type_attributes` at `loc_idx`.
#[allow(non_snake_case)]
pub fn traslate_declaration_kind(
    input: Input<'_>,
    config: &crate::gentype::config::T,
    type_env: &crate::gentype::type_env::T,
    loc_idx: LocIdx,
    type_attributes: &Attributes,
    declaration: Declaration<'_>,
) -> crate::gentype::annotation::Read<Vec<code_item::TypeDeclaration>> {
    // Mirrors compiler/gentype/TranslateTypeDeclarations.ml:54-321.
    let Input { arena, .. } = input;
    let doc_string = crate::gentype::annotation::doc_string_from_attrs(arena, type_attributes)?;
    let annotation = crate::gentype::annotation::from_attributes(
        arena,
        config,
        &crate::gentype::type_env::notes(type_env),
        loc_idx,
        type_attributes,
    )?;
    let opaque = match annotation == crate::gentype::annotation::T::GenTypeOpaque {
        true => Some(true),
        false => None,
    };
    let (import_string_opt, name_as) =
        crate::gentype::annotation::get_attribute_import_renaming(arena, type_attributes)?;
    let attribute_info = DeclarationAttributeInfo {
        doc_string,
        annotation,
        opaque,
        import_string_opt,
        name_as,
    };
    traslate_declaration_kind_with_attribute_info(
        input,
        config,
        type_env,
        attribute_info,
        declaration,
    )
}

/// Translate a type declaration whose attributes are declaration
/// attributes, as found in signature types.
#[allow(non_snake_case)]
pub fn traslate_declaration_kind_from_decl_attributes(
    input: Input<'_>,
    config: &crate::gentype::config::T,
    type_env: &crate::gentype::type_env::T,
    loc_file: &dyn Fn() -> String,
    type_attributes: &[DeclAttribute],
    declaration: Declaration<'_>,
) -> crate::gentype::annotation::Read<Vec<code_item::TypeDeclaration>> {
    // OCaml TranslateSignatureFromTypes.ml:3-29 passes
    // Types.type_declaration.type_attributes through to
    // TranslateTypeDeclarations.ml:54-321. Rust decl attributes have already
    // been converted out of parser payloads, so compute the same annotation
    // facts from decl::Attribute instead of using an empty parser attribute set.
    let doc_string = crate::gentype::annotation::doc_string_from_decl_attrs(type_attributes)?;
    let annotation = crate::gentype::annotation::from_decl_attributes(
        config,
        &crate::gentype::type_env::notes(type_env),
        loc_file,
        &declaration.loc,
        type_attributes,
    )?;
    let opaque = match annotation == crate::gentype::annotation::T::GenTypeOpaque {
        true => Some(true),
        false => None,
    };
    let (import_string_opt, name_as) =
        crate::gentype::annotation::get_decl_attribute_import_renaming(type_attributes)?;
    let attribute_info = DeclarationAttributeInfo {
        doc_string,
        annotation,
        opaque,
        import_string_opt,
        name_as,
    };
    traslate_declaration_kind_with_attribute_info(
        input,
        config,
        type_env,
        attribute_info,
        declaration,
    )
}

fn traslate_declaration_kind_with_attribute_info(
    input: Input<'_>,
    config: &crate::gentype::config::T,
    type_env: &crate::gentype::type_env::T,
    attribute_info: DeclarationAttributeInfo,
    declaration: Declaration<'_>,
) -> crate::gentype::annotation::Read<Vec<code_item::TypeDeclaration>> {
    let Input {
        ta,
        ctx,
        arena,
        output_file_relative,
        resolver,
    } = input;
    let DeclarationAttributeInfo {
        doc_string,
        annotation,
        opaque,
        import_string_opt,
        name_as,
    } = attribute_info;
    let Declaration {
        loc,
        type_name,
        type_vars,
        kind: declaration_kind,
    } = declaration;
    let header = ExportTypeHeader {
        type_env,
        doc_string,
        type_name,
        type_vars,
    };

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
                &header,
                annotation,
                ctx.intern_loc(loc),
                name_as.clone(),
                opaque,
                translation.type_,
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

    Ok(match (declaration_kind, import_string_opt) {
        (_, Some(import_string)) => {
            let type_name_original = header.type_name.to_string();
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
                &header,
                crate::gentype::annotation::T::GenType,
                ctx.intern_loc(loc),
                None,
                Some(false),
                ident_with(
                    true,
                    header
                        .type_vars
                        .iter()
                        .map(|s| Type::TypeVar(s.clone()))
                        .collect(),
                    &as_type_name,
                ),
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
                &header,
                annotation,
                ctx.intern_loc(loc),
                name_as,
                Some(true),
                unknown(),
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
            let core_type = ta.core_type(core_type);
            let translation = crate::gentype::translate_core_type::translate_core_type(
                ta, ctx, arena, config, type_env, core_type,
            )?;
            let type_ = match (&core_type.ctyp_desc, translation.type_.clone()) {
                (
                    crate::types::typedtree::TypedCoreTypeDesc::Ttyp_variant(row_fields, _, _),
                    Type::Variant(mut variant),
                ) => {
                    let row_fields_variants =
                        crate::gentype::translate_core_type::process_variant(ta, row_fields);
                    variant.no_payloads = row_fields_variants
                        .no_payloads
                        .iter()
                        .map(|(label, attributes)| create_case(arena, label, attributes, true))
                        .collect::<crate::gentype::annotation::Read<_>>()?;
                    if variant.payloads.len() == row_fields_variants.payloads.len() {
                        variant.payloads = variant
                            .payloads
                            .into_iter()
                            .zip(row_fields_variants.payloads.iter())
                            .map(|(mut payload, (label, attributes, _))| {
                                payload.case = create_case(arena, label, attributes, true)?;
                                Ok(payload)
                            })
                            .collect::<crate::gentype::annotation::Read<_>>()?;
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
            )?;
            let import_types = crate::gentype::translation::translate_dependencies(
                config,
                output_file_relative,
                resolver,
                &translation.dependencies,
            );
            return_type_declaration(code_item::TypeDeclaration {
                import_types,
                export_from_type_declaration: create_export_type_from_type_declaration(
                    &header,
                    annotation,
                    ctx.intern_loc(loc),
                    name_as,
                    opaque,
                    translation.type_,
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
                            )?,
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
                    Ok((tag, arg_types, import_types))
                })
                .collect::<crate::gentype::annotation::Read<Vec<_>>>()?;

            let no_payloads = variants
                .iter()
                .filter(|(_, arg_types, _)| arg_types.is_empty())
                .map(|(tag, _, _)| create_variant_case(tag))
                .collect::<Vec<_>>();
            let payloads = variants
                .iter()
                .filter(|(_, arg_types, _)| !arg_types.is_empty())
                .map(|(tag, arg_types, _)| {
                    let type_ = match arg_types.as_slice() {
                        [type_] => type_.clone(),
                        _ => Type::Tuple(arg_types.clone()),
                    };
                    Payload {
                        case: create_variant_case(tag),
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
            let resolved_type_name = crate::gentype::type_env::add_module_path(
                type_env,
                &sanitize_type_name(header.type_name),
            );
            let export_from_type_declaration = code_item::ExportFromTypeDeclaration {
                export_type: code_item::ExportType {
                    loc: ctx.intern_loc(loc),
                    name_as,
                    opaque,
                    type_: variant_typ,
                    type_vars: header.type_vars,
                    resolved_type_name,
                    doc_string: header.doc_string,
                },
                annotation,
            };
            let import_types = variants
                .into_iter()
                .flat_map(|(_, _, import_types)| import_types)
                .collect();
            return_type_declaration(code_item::TypeDeclaration {
                export_from_type_declaration,
                import_types,
            })
        }
        (DeclarationKind::NoDeclaration, None) => vec![],
    })
}

/// Whether a constructor has its own result type, making the type a GADT.
pub fn has_some_gadt_leaf(constructor_declarations: &[ConstructorDeclaration]) -> bool {
    // Mirrors compiler/gentype/TranslateTypeDeclarations.ml:323-326.
    constructor_declarations
        .iter()
        .any(|declaration| declaration.cd_res.is_some())
}

/// Translate a typed type declaration.
pub fn translate_type_declaration(
    input: Input<'_>,
    config: &crate::gentype::config::T,
    type_env: &crate::gentype::type_env::T,
    type_declaration: &TypedTypeDeclaration,
) -> crate::gentype::annotation::Read<Vec<code_item::TypeDeclaration>> {
    // Mirrors compiler/gentype/TranslateTypeDeclarations.ml:328-351.
    let Input { ta, ctx, arena, .. } = input;
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
        .map(|(core_type, _)| ta.core_type(*core_type))
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
            DeclarationKind::GeneralDeclaration(type_declaration.typ_manifest)
        }
        _ => DeclarationKind::NoDeclaration,
    };
    traslate_declaration_kind(
        input,
        config,
        type_env,
        type_declaration.typ_loc,
        &type_declaration.typ_attributes,
        Declaration {
            loc: arena.to_location(type_declaration.typ_loc),
            type_name: &type_name,
            type_vars,
            kind: declaration_kind,
        },
    )
}

/// Declare the type of a type declaration in `type_env`.
pub fn add_type_declaration_id_to_type_env(
    type_env: &crate::gentype::type_env::T,
    type_declaration: &TypedTypeDeclaration,
) {
    // Mirrors compiler/gentype/TranslateTypeDeclarations.ml:353-355.
    crate::gentype::type_env::new_type(type_declaration.typ_id.name(), type_env);
}

/// `TranslateTypeDeclarations.translateTypeDeclarations`: translate the
/// declarations of one `type` item, declaring all of their names first when
/// it is recursive.
pub fn translate_type_declarations(
    input: Input<'_>,
    config: &crate::gentype::config::T,
    recursive: bool,
    type_env: &crate::gentype::type_env::T,
    type_declarations: &[TypedTypeDeclaration],
) -> crate::gentype::annotation::Read<Vec<code_item::TypeDeclaration>> {
    // Mirrors compiler/gentype/TranslateTypeDeclarations.ml:357-373.
    if recursive {
        for type_declaration in type_declarations {
            add_type_declaration_id_to_type_env(type_env, type_declaration);
        }
    }
    let mut translations = Vec::new();
    for type_declaration in type_declarations {
        let res = translate_type_declaration(input, config, type_env, type_declaration)?;
        if !recursive {
            add_type_declaration_id_to_type_env(type_env, type_declaration);
        }
        translations.extend(res);
    }
    Ok(translations)
}

fn translate_label_declarations(
    ctx: &crate::types::context::TypeContext,
    arena: &ParseArena,
    config: &crate::gentype::config::T,
    type_env: &crate::gentype::type_env::T,
    inline: bool,
    unboxed_annotation: bool,
    label_declarations: &[LabelDeclaration],
) -> crate::gentype::annotation::Read<crate::gentype::translate_type_expr_from_types::Translation> {
    // Mirrors compiler/gentype/TranslateTypeDeclarations.ml:91-143.
    let notes = crate::gentype::type_env::notes(type_env);
    let field_translations = label_declarations
        .iter()
        .map(|label_declaration| {
            let attributes = &label_declaration.ld_attributes;
            let name = declared_field_name(ctx, arena, &notes, label_declaration)?;
            let mutable_ = match label_declaration.ld_mutable {
                MutableFlag::Mutable => Mutable::Mutable,
                MutableFlag::Immutable => Mutable::Immutable,
            };
            Ok((
                name,
                mutable_,
                label_declaration.ld_optional,
                crate::gentype::translate_type_expr_from_types::translate_type_expr_from_types(
                    ctx,
                    config,
                    type_env,
                    &label_declaration.ld_type,
                ),
                crate::gentype::annotation::doc_string_from_decl_attrs(attributes)?,
            ))
        })
        .collect::<crate::gentype::annotation::Read<Vec<_>>>()?;

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
    Ok(
        crate::gentype::translate_type_expr_from_types::Translation {
            dependencies,
            type_,
        },
    )
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
