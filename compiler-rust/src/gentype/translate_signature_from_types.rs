// Port of compiler/gentype/TranslateSignatureFromTypes.ml:1-110.
// This Stage 3 GenType port is intentionally not wired into the crate yet.

use crate::parse_arena::{LocIdx, ParseArena};
use crate::parser::ast::Attributes;
use crate::types::decl::{ModuleType, SignatureItem, TypeKind};

pub fn translate_type_declaration_from_types(
    arena: &ParseArena,
    config: &crate::gentype::config::T,
    output_file_relative: &str,
    resolver: &crate::gentype::module_resolver::Resolver,
    type_env: &crate::gentype::type_env::T,
    id: &crate::ident::Ident,
    type_declaration: &crate::types::decl::TypeDeclaration,
) -> Vec<crate::gentype::code_item::TypeDeclaration> {
    // Mirrors compiler/gentype/TranslateSignatureFromTypes.ml:3-29.
    crate::gentype::type_env::new_type(id.name(), type_env);
    let type_name = id.name().to_string();
    let type_vars =
        crate::gentype::type_vars::extract_from_type_expr_refs(&type_declaration.type_params);
    if crate::gentype::debug::translation.load(std::sync::atomic::Ordering::Relaxed) {
        crate::gentype::log_::item(&format!("Translate Types.type_declaration {type_name}\n"));
    }
    let declaration_kind = match &type_declaration.type_kind {
        TypeKind::TypeRecord(label_declarations, _) => {
            crate::gentype::translate_type_declarations::DeclarationKind::RecordDeclarationFromTypes(
                label_declarations.clone(),
            )
        }
        TypeKind::TypeVariant(constructor_declarations)
            if !crate::gentype::translate_type_declarations::has_some_gadt_leaf(
                constructor_declarations,
            ) =>
        {
            crate::gentype::translate_type_declarations::DeclarationKind::VariantDeclarationFromTypes(
                constructor_declarations.clone(),
            )
        }
        TypeKind::TypeAbstract => {
            crate::gentype::translate_type_declarations::DeclarationKind::GeneralDeclarationFromTypes(
                type_declaration.type_manifest,
            )
        }
        _ => crate::gentype::translate_type_declarations::DeclarationKind::NoDeclaration,
    };
    let empty_attributes = Attributes::new();
    crate::gentype::translate_type_declarations::traslate_declaration_kind(
        arena,
        config,
        type_declaration.type_loc.clone(),
        LocIdx::default(),
        output_file_relative,
        resolver,
        &empty_attributes,
        type_env,
        &type_name,
        type_vars,
        declaration_kind,
    )
}

pub fn translate_module_declaration_from_types(
    arena: &ParseArena,
    config: &crate::gentype::config::T,
    output_file_relative: &str,
    resolver: &crate::gentype::module_resolver::Resolver,
    type_env: &crate::gentype::type_env::T,
    id: &crate::ident::Ident,
    module_declaration: &crate::types::decl::ModuleDeclaration,
) -> crate::gentype::translation::T {
    // Mirrors compiler/gentype/TranslateSignatureFromTypes.ml:30-49.
    match &module_declaration.md_type {
        ModuleType::MtySignature(signature) => {
            let name = id.name();
            crate::gentype::translation::combine(&translate_signature_from_types(
                arena,
                config,
                output_file_relative,
                resolver,
                &crate::gentype::type_env::new_module(name, type_env),
                signature,
            ))
        }
        ModuleType::MtyIdent(_) => {
            crate::gentype::gen_type_common::log_not_implemented(
                "Mty_ident compiler/gentype/TranslateSignatureFromTypes.ml:41",
            );
            crate::gentype::translation::empty()
        }
        ModuleType::MtyFunctor { .. } => {
            crate::gentype::gen_type_common::log_not_implemented(
                "Mty_functor compiler/gentype/TranslateSignatureFromTypes.ml:44",
            );
            crate::gentype::translation::empty()
        }
        ModuleType::MtyAlias(_, _) => {
            crate::gentype::gen_type_common::log_not_implemented(
                "Mty_alias compiler/gentype/TranslateSignatureFromTypes.ml:47",
            );
            crate::gentype::translation::empty()
        }
    }
}

pub fn translate_signature_item_from_types(
    arena: &ParseArena,
    config: &crate::gentype::config::T,
    output_file_relative: &str,
    resolver: &crate::gentype::module_resolver::Resolver,
    type_env: &crate::gentype::type_env::T,
    signature_item: &SignatureItem,
) -> crate::gentype::translation::T {
    // Mirrors compiler/gentype/TranslateSignatureFromTypes.ml:51-101.
    match signature_item {
        SignatureItem::SigType(id, type_declaration, _) => crate::gentype::translation::T {
            import_types: vec![],
            code_items: vec![],
            type_declarations: translate_type_declaration_from_types(
                arena,
                config,
                output_file_relative,
                resolver,
                type_env,
                id,
                type_declaration,
            ),
        },
        SignatureItem::SigModule(id, module_declaration, _) => {
            let module_item = crate::gentype::runtime::new_module_item(id.name());
            let config = crate::gentype::annotation::update_config_for_decl_module(
                config,
                &module_declaration.md_attributes,
            );
            crate::gentype::type_env::update_module_item(module_item, type_env);
            translate_module_declaration_from_types(
                arena,
                &config,
                output_file_relative,
                resolver,
                type_env,
                id,
                module_declaration,
            )
        }
        SignatureItem::SigValue(id, value_description) => {
            let name = unwrap_uppercase_exotic(id.name()).to_string();
            if crate::gentype::debug::translation.load(std::sync::atomic::Ordering::Relaxed) {
                crate::gentype::log_::item(&format!("Translate Sig Value {name}\n"));
            }
            let module_item = crate::gentype::runtime::new_module_item(&name);
            crate::gentype::type_env::update_module_item(module_item, type_env);
            if crate::gentype::annotation::from_decl_attributes(
                config,
                &value_description.val_loc,
                &value_description.val_attributes,
            ) == crate::gentype::annotation::T::GenType
            {
                crate::gentype::translation::translate_value_with_name_as(
                    crate::gentype::annotation::get_decl_gentype_as_renaming(
                        &value_description.val_attributes,
                    ),
                    config,
                    crate::gentype::annotation::doc_string_from_decl_attrs(
                        &value_description.val_attributes,
                    ),
                    output_file_relative,
                    resolver,
                    type_env,
                    value_description.val_type,
                    |t| t,
                    &name,
                )
            } else {
                crate::gentype::translation::empty()
            }
        }
        SignatureItem::SigTypext(_, _, _) => not_implemented("Sig_typext"),
        SignatureItem::SigModtype(_, _) => not_implemented("Sig_modtype"),
        SignatureItem::SigClass => not_implemented("Sig_class"),
        SignatureItem::SigClassType => not_implemented("Sig_class_type"),
    }
}

pub fn translate_signature_from_types(
    arena: &ParseArena,
    config: &crate::gentype::config::T,
    output_file_relative: &str,
    resolver: &crate::gentype::module_resolver::Resolver,
    type_env: &crate::gentype::type_env::T,
    signature: &[SignatureItem],
) -> Vec<crate::gentype::translation::T> {
    // Mirrors compiler/gentype/TranslateSignatureFromTypes.ml:103-110.
    if crate::gentype::debug::translation.load(std::sync::atomic::Ordering::Relaxed) {
        crate::gentype::log_::item("Translate Types.signature\n");
    }
    signature
        .iter()
        .map(|signature_item| {
            translate_signature_item_from_types(
                arena,
                config,
                output_file_relative,
                resolver,
                type_env,
                signature_item,
            )
        })
        .collect()
}

fn not_implemented(name: &str) -> crate::gentype::translation::T {
    crate::gentype::gen_type_common::log_not_implemented(&format!(
        "{name} compiler/gentype/TranslateSignatureFromTypes.ml"
    ));
    crate::gentype::translation::empty()
}

fn attributes_from_vec(attributes: &[crate::parser::ast::Attribute]) -> Attributes {
    Attributes::from_vec(attributes.to_vec())
}

fn unwrap_uppercase_exotic(name: &str) -> &str {
    let bytes = name.as_bytes();
    if bytes.len() >= 3 && bytes[0] == b'\\' && bytes[1] == b'"' && bytes[bytes.len() - 1] == b'"' {
        &name[2..name.len() - 1]
    } else {
        name
    }
}
