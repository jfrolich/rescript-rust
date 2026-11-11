// Port of compiler/gentype/TranslateSignature.ml:1-169.

use crate::gentype::translation::Input;
use crate::types::typedtree::{
    ModuleTypeDeclaration, ModuleTypeDesc, TypedModuleDeclaration, TypedSignatureItem,
    TypedSignatureItemDesc,
};

/// Translate a value declared in a signature, when it is exported.
pub fn translate_signature_value(
    input: Input<'_>,
    config: &crate::gentype::config::T,
    type_env: &crate::gentype::type_env::T,
    value_description: &crate::types::typedtree::TypedValueDescription,
) -> crate::gentype::translation::T {
    // Mirrors compiler/gentype/TranslateSignature.ml:3-21.
    let Input { ta, arena, .. } = input;
    if crate::gentype::debug::translation.load(std::sync::atomic::Ordering::Relaxed) {
        crate::gentype::log_::item(&format!(
            "Translate Signature Value {}\n",
            value_description.val_id.name()
        ));
    }
    let type_expr = ta.core_type(value_description.val_desc).ctyp_type;
    match crate::gentype::annotation::from_attributes(
        arena,
        config,
        value_description.val_loc,
        &value_description.val_attributes,
    ) {
        crate::gentype::annotation::T::GenType => {
            let name = unwrap_uppercase_exotic(value_description.val_id.name()).to_string();
            crate::gentype::translation::translate_value(
                input,
                &value_description.val_attributes,
                config,
                type_env,
                type_expr,
                |t| t,
                &name,
            )
        }
        _ => crate::gentype::translation::empty(),
    }
}

/// Translate a submodule declared in a signature.
pub fn translate_module_declaration(
    input: Input<'_>,
    config: &crate::gentype::config::T,
    type_env: &crate::gentype::type_env::T,
    module_declaration: &TypedModuleDeclaration,
) -> crate::gentype::translation::T {
    // Mirrors compiler/gentype/TranslateSignature.ml:23-52.
    let Input { ta, .. } = input;
    let name = module_declaration.md_id.name();
    if crate::gentype::debug::translation.load(std::sync::atomic::Ordering::Relaxed) {
        crate::gentype::log_::item(&format!("Translate Module Declaration {name}\n"));
    }
    let type_env = crate::gentype::type_env::new_module(name, type_env);
    match &ta.module_type(module_declaration.md_type).mty_desc {
        ModuleTypeDesc::Tmty_signature(signature) => {
            crate::gentype::translation::combine(translate_signature(
                input,
                config,
                &type_env,
                ta.signature_items(signature.sig_items),
            ))
        }
        ModuleTypeDesc::Tmty_ident(path, _) => {
            match crate::gentype::type_env::lookup_module_type_signature(path, &type_env) {
                None => crate::gentype::translation::empty(),
                Some((signature, _, type_env)) => {
                    crate::gentype::translation::combine(translate_signature(
                        input,
                        config,
                        &type_env,
                        ta.signature_items(signature.sig_items),
                    ))
                }
            }
        }
        ModuleTypeDesc::Tmty_functor(_, _, _, _) => not_implemented("Tmty_functor"),
        ModuleTypeDesc::Tmty_with(_, _) => not_implemented("Tmty_with"),
        ModuleTypeDesc::Tmty_typeof(_) => not_implemented("Tmty_typeof"),
        ModuleTypeDesc::Tmty_alias(_, _) => not_implemented("Tmty_alias"),
    }
}

/// Translate a module type declaration's types; its values are not
/// exported.
pub fn translate_module_type_declaration(
    input: Input<'_>,
    config: &crate::gentype::config::T,
    type_env: &crate::gentype::type_env::T,
    module_type_declaration: &ModuleTypeDeclaration,
) -> crate::gentype::translation::T {
    // Mirrors compiler/gentype/TranslateSignature.ml:53-95.
    let Input { ctx, arena, ta, .. } = input;
    if crate::gentype::debug::translation.load(std::sync::atomic::Ordering::Relaxed) {
        crate::gentype::log_::item(&format!(
            "Translate Module Type Declaration {}\n",
            module_type_declaration.mtd_id.name()
        ));
    }
    match &module_type_declaration.mtd_type {
        None => crate::gentype::translation::empty(),
        Some(mtd_type) => match &ta.module_type(*mtd_type).mty_desc {
            ModuleTypeDesc::Tmty_signature(signature) => {
                let name = module_type_declaration.mtd_id.name();
                let signature_without_values = ta
                    .signature_items(signature.sig_items)
                    .iter()
                    .filter(|item| !matches!(item.sig_desc, TypedSignatureItemDesc::Tsig_value(_)));
                crate::gentype::translation::combine(translate_signature(
                    input,
                    config,
                    &crate::gentype::type_env::new_module_type(
                        name,
                        signature.clone(),
                        crate::types::typemod::decl_signature_from_typed_signature(
                            ta, signature, arena, ctx,
                        ),
                        type_env,
                    ),
                    signature_without_values,
                ))
            }
            ModuleTypeDesc::Tmty_ident(_, _) => not_implemented("Tmty_ident"),
            ModuleTypeDesc::Tmty_functor(_, _, _, _) => not_implemented("Tmty_functor"),
            ModuleTypeDesc::Tmty_with(_, _) => not_implemented("Tmty_with"),
            ModuleTypeDesc::Tmty_typeof(_) => not_implemented("Tmty_typeof"),
            ModuleTypeDesc::Tmty_alias(_, _) => not_implemented("Tmty_alias"),
        },
    }
}

/// Translate one signature item.
pub fn translate_signature_item(
    input: Input<'_>,
    config: &crate::gentype::config::T,
    type_env: &crate::gentype::type_env::T,
    signature_item: &TypedSignatureItem,
) -> crate::gentype::translation::T {
    // Mirrors compiler/gentype/TranslateSignature.ml:97-161.
    let Input { arena, ta, .. } = input;
    match &signature_item.sig_desc {
        TypedSignatureItemDesc::Tsig_type(rec_flag, type_declarations) => {
            crate::gentype::translation::T {
                import_types: vec![],
                code_items: vec![],
                type_declarations:
                    crate::gentype::translate_type_declarations::translate_type_declarations(
                        input,
                        config,
                        matches!(rec_flag, crate::parser::ast::RecFlag::Recursive),
                        type_env,
                        type_declarations,
                    ),
            }
        }
        TypedSignatureItemDesc::Tsig_value(value_description) => {
            let is_import = crate::gentype::annotation::has_attribute(
                arena,
                crate::gentype::annotation::tag_is_gentype_import,
                &ta.value_description(*value_description).val_attributes,
            );
            if ta.value_description(*value_description).val_prim.is_some() || is_import {
                crate::gentype::translation::translate_primitive(
                    input,
                    config,
                    type_env,
                    ta.value_description(*value_description),
                )
            } else {
                let module_item = crate::gentype::runtime::new_module_item(
                    ta.value_description(*value_description).val_id.name(),
                );
                crate::gentype::type_env::update_module_item(module_item, type_env);
                translate_signature_value(
                    input,
                    config,
                    type_env,
                    ta.value_description(*value_description),
                )
            }
        }
        TypedSignatureItemDesc::Tsig_module(module_declaration) => {
            translate_module_declaration(input, config, type_env, module_declaration)
        }
        TypedSignatureItemDesc::Tsig_modtype(module_type_declaration) => {
            let module_item =
                crate::gentype::runtime::new_module_item(module_type_declaration.mtd_id.name());
            let config = crate::gentype::annotation::update_config_for_module(
                arena,
                config,
                &module_type_declaration.mtd_attributes,
            );
            crate::gentype::type_env::update_module_item(module_item, type_env);
            translate_module_type_declaration(input, &config, type_env, module_type_declaration)
        }
        TypedSignatureItemDesc::Tsig_typext(_) => not_implemented("Tsig_typext"),
        TypedSignatureItemDesc::Tsig_exception(_) => not_implemented("Tsig_exception"),
        TypedSignatureItemDesc::Tsig_recmodule(_) => not_implemented("Tsig_recmodule"),
        TypedSignatureItemDesc::Tsig_open(_) => not_implemented("Tsig_open"),
        TypedSignatureItemDesc::Tsig_include(_) => not_implemented("Tsig_include"),
        TypedSignatureItemDesc::Tsig_attribute(_) => not_implemented("Tsig_attribute"),
    }
}

/// `TranslateSignature.translateSignature`: translate each signature item.
pub fn translate_signature<'s>(
    input: Input<'_>,
    config: &crate::gentype::config::T,
    type_env: &crate::gentype::type_env::T,
    signature_items: impl IntoIterator<Item = &'s crate::types::typedtree::TypedSignatureItem>,
) -> Vec<crate::gentype::translation::T> {
    // Mirrors compiler/gentype/TranslateSignature.ml:163-169.
    if crate::gentype::debug::translation.load(std::sync::atomic::Ordering::Relaxed) {
        crate::gentype::log_::item("Translate Signature\n");
    }
    signature_items
        .into_iter()
        .map(|signature_item| translate_signature_item(input, config, type_env, signature_item))
        .collect()
}

fn not_implemented(name: &str) -> crate::gentype::translation::T {
    crate::gentype::gen_type_common::log_not_implemented(&format!(
        "{name} compiler/gentype/TranslateSignature.ml"
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
