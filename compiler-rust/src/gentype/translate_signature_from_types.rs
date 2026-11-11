// Port of compiler/gentype/TranslateSignatureFromTypes.ml:1-110.

use crate::gentype::translation::Input;
use crate::types::decl::{ModuleType, SignatureItem, TypeKind};

/// Translate a type declaration found in a signature type.
pub fn translate_type_declaration_from_types(
    input: Input<'_>,
    config: &crate::gentype::config::T,
    type_env: &crate::gentype::type_env::T,
    id: &crate::ident::Ident,
    type_declaration: &crate::types::decl::TypeDeclaration,
) -> Vec<crate::gentype::code_item::TypeDeclaration> {
    // Mirrors compiler/gentype/TranslateSignatureFromTypes.ml:3-29.
    let Input { ctx, .. } = input;
    crate::gentype::type_env::new_type(id.name(), type_env);
    let type_name = id.name().to_string();
    let type_vars =
        crate::gentype::type_vars::extract_from_type_expr_refs(ctx, &type_declaration.type_params);
    if crate::gentype::debug::translation.load(std::sync::atomic::Ordering::Relaxed) {
        crate::gentype::log_::item(&format!("Translate Types.type_declaration {type_name}\n"));
    }
    let declaration_kind = match &type_declaration.type_kind {
        TypeKind::TypeRecord(label_declarations, representation) => {
            crate::gentype::translate_type_declarations::DeclarationKind::RecordDeclarationFromTypes(
                label_declarations.to_vec(),
                representation.clone(),
            )
        }
        TypeKind::TypeVariant(constructor_declarations, layout_ref)
            if !crate::gentype::translate_type_declarations::has_some_gadt_leaf(
                constructor_declarations,
            ) =>
        {
            crate::gentype::translate_type_declarations::DeclarationKind::VariantDeclarationFromTypes(
                constructor_declarations.to_vec(),
                ctx.variant_layout(*layout_ref),
                type_declaration.type_representation,
            )
        }
        TypeKind::TypeAbstract => {
            crate::gentype::translate_type_declarations::DeclarationKind::GeneralDeclarationFromTypes(
                type_declaration.type_manifest,
            )
        }
        _ => crate::gentype::translate_type_declarations::DeclarationKind::NoDeclaration,
    };
    crate::gentype::translate_type_declarations::traslate_declaration_kind_from_decl_attributes(
        input,
        config,
        type_env,
        &type_declaration.type_attributes,
        crate::gentype::translate_type_declarations::Declaration {
            loc: ctx.resolve_loc(type_declaration.type_loc),
            type_name: &type_name,
            type_vars,
            kind: declaration_kind,
        },
    )
}

/// Translate a submodule found in a signature type.
pub fn translate_module_declaration_from_types(
    input: Input<'_>,
    config: &crate::gentype::config::T,
    type_env: &crate::gentype::type_env::T,
    id: &crate::ident::Ident,
    module_declaration: &crate::types::decl::ModuleDeclaration,
) -> crate::gentype::translation::T {
    // Mirrors compiler/gentype/TranslateSignatureFromTypes.ml:30-49.
    match &module_declaration.md_type {
        ModuleType::MtySignature(signature) => {
            let name = id.name();
            crate::gentype::translation::combine(translate_signature_from_types(
                input,
                config,
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

/// Translate one item of a signature type.
pub fn translate_signature_item_from_types(
    input: Input<'_>,
    config: &crate::gentype::config::T,
    type_env: &crate::gentype::type_env::T,
    signature_item: &SignatureItem,
) -> crate::gentype::translation::T {
    // Mirrors compiler/gentype/TranslateSignatureFromTypes.ml:51-101.
    let Input { ctx, .. } = input;
    match signature_item {
        SignatureItem::SigType(id, type_declaration, _) => crate::gentype::translation::T {
            import_types: vec![],
            code_items: vec![],
            type_declarations: translate_type_declaration_from_types(
                input,
                config,
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
                input,
                &config,
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
                &ctx.resolve_loc(value_description.val_loc),
                &value_description.val_attributes,
            ) == crate::gentype::annotation::T::GenType
            {
                crate::gentype::translation::translate_value_with_name_as(
                    input,
                    config,
                    type_env,
                    value_description.val_type,
                    |t| t,
                    crate::gentype::translation::ValueExport {
                        name: &name,
                        name_as: crate::gentype::annotation::get_decl_gentype_as_renaming(
                            &value_description.val_attributes,
                        ),
                        doc_string: crate::gentype::annotation::doc_string_from_decl_attrs(
                            &value_description.val_attributes,
                        ),
                    },
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

/// `TranslateSignatureFromTypes.translateSignatureFromTypes`: translate
/// each item of a signature type.
pub fn translate_signature_from_types(
    input: Input<'_>,
    config: &crate::gentype::config::T,
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
            translate_signature_item_from_types(input, config, type_env, signature_item)
        })
        .collect()
}

fn not_implemented(name: &str) -> crate::gentype::translation::T {
    crate::gentype::gen_type_common::log_not_implemented(&format!(
        "{name} compiler/gentype/TranslateSignatureFromTypes.ml"
    ));
    crate::gentype::translation::empty()
}

fn unwrap_uppercase_exotic(name: &str) -> &str {
    let bytes = name.as_bytes();
    if bytes.len() >= 3 && bytes[0] == b'\\' && bytes[1] == b'"' && bytes[bytes.len() - 1] == b'"' {
        &name[2..name.len() - 1]
    } else {
        name
    }
}
