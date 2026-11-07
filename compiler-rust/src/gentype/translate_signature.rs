// Port of compiler/gentype/TranslateSignature.ml:1-169.

use crate::parse_arena::ParseArena;
use crate::types::typedtree::{
    ModuleTypeDeclaration, ModuleTypeDesc, TypedModuleDeclaration, TypedSignature,
    TypedSignatureItem, TypedSignatureItemDesc,
};

pub fn translate_signature_value(
    ctx: &crate::types::context::TypeContext,
    arena: &ParseArena,
    config: &crate::gentype::config::T,
    output_file_relative: &str,
    resolver: &crate::gentype::module_resolver::Resolver,
    type_env: &crate::gentype::type_env::T,
    value_description: &crate::types::typedtree::TypedValueDescription,
) -> crate::gentype::annotation::Read<crate::gentype::translation::T> {
    // Mirrors compiler/gentype/TranslateSignature.ml:3-21.
    if crate::gentype::debug::translation.load(std::sync::atomic::Ordering::Relaxed) {
        crate::gentype::log_::item(&format!(
            "Translate Signature Value {}\n",
            value_description.val_id.name()
        ));
    }
    let type_expr = value_description.val_desc.ctyp_type;
    Ok(
        match crate::gentype::annotation::from_attributes(
            arena,
            config,
            &crate::gentype::type_env::notes(type_env),
            value_description.val_loc,
            &value_description.val_attributes,
        )? {
            crate::gentype::annotation::T::GenType => {
                let name = unwrap_uppercase_exotic(value_description.val_id.name()).to_string();
                crate::gentype::translation::translate_value(
                    ctx,
                    arena,
                    &value_description.val_attributes,
                    config,
                    crate::gentype::annotation::doc_string_from_attrs(
                        arena,
                        &value_description.val_attributes,
                    )?,
                    output_file_relative,
                    resolver,
                    type_env,
                    type_expr,
                    |t| t,
                    &name,
                )?
            }
            _ => crate::gentype::translation::empty(),
        },
    )
}

pub fn translate_module_declaration(
    ctx: &crate::types::context::TypeContext,
    arena: &ParseArena,
    config: &crate::gentype::config::T,
    output_file_relative: &str,
    resolver: &crate::gentype::module_resolver::Resolver,
    type_env: &crate::gentype::type_env::T,
    module_declaration: &TypedModuleDeclaration,
) -> crate::gentype::annotation::Read<crate::gentype::translation::T> {
    // Mirrors compiler/gentype/TranslateSignature.ml:23-52.
    let name = module_declaration.md_id.name();
    if crate::gentype::debug::translation.load(std::sync::atomic::Ordering::Relaxed) {
        crate::gentype::log_::item(&format!("Translate Module Declaration {name}\n"));
    }
    let type_env = crate::gentype::type_env::new_module(name, type_env);
    Ok(match &module_declaration.md_type.mty_desc {
        ModuleTypeDesc::Tmty_signature(signature) => {
            crate::gentype::translation::combine(translate_signature(
                ctx,
                arena,
                config,
                output_file_relative,
                resolver,
                &type_env,
                signature,
            )?)
        }
        ModuleTypeDesc::Tmty_ident(path, _) => {
            match crate::gentype::type_env::lookup_module_type_signature(path, &type_env) {
                None => crate::gentype::translation::empty(),
                Some((signature, _, type_env)) => {
                    crate::gentype::translation::combine(translate_signature(
                        ctx,
                        arena,
                        config,
                        output_file_relative,
                        resolver,
                        &type_env,
                        &signature,
                    )?)
                }
            }
        }
        ModuleTypeDesc::Tmty_functor(_, _, _, _) => not_implemented("Tmty_functor"),
        ModuleTypeDesc::Tmty_with(_, _) => not_implemented("Tmty_with"),
        ModuleTypeDesc::Tmty_typeof(_) => not_implemented("Tmty_typeof"),
        ModuleTypeDesc::Tmty_alias(_, _) => not_implemented("Tmty_alias"),
    })
}

pub fn translate_module_type_declaration(
    ctx: &crate::types::context::TypeContext,
    arena: &ParseArena,
    config: &crate::gentype::config::T,
    output_file_relative: &str,
    resolver: &crate::gentype::module_resolver::Resolver,
    type_env: &crate::gentype::type_env::T,
    module_type_declaration: &ModuleTypeDeclaration,
) -> crate::gentype::annotation::Read<crate::gentype::translation::T> {
    // Mirrors compiler/gentype/TranslateSignature.ml:53-95.
    if crate::gentype::debug::translation.load(std::sync::atomic::Ordering::Relaxed) {
        crate::gentype::log_::item(&format!(
            "Translate Module Type Declaration {}\n",
            module_type_declaration.mtd_id.name()
        ));
    }
    Ok(match &module_type_declaration.mtd_type {
        None => crate::gentype::translation::empty(),
        Some(mtd_type) => match &mtd_type.mty_desc {
            ModuleTypeDesc::Tmty_signature(signature) => {
                let name = module_type_declaration.mtd_id.name();
                let mut signature_without_values = signature.clone();
                signature_without_values
                    .sig_items
                    .retain(|item| !matches!(item.sig_desc, TypedSignatureItemDesc::Tsig_value(_)));
                crate::gentype::translation::combine(translate_signature(
                    ctx,
                    arena,
                    config,
                    output_file_relative,
                    resolver,
                    &crate::gentype::type_env::new_module_type(
                        name,
                        signature.clone(),
                        crate::types::typemod::decl_signature_from_typed_signature(
                            signature, arena, ctx,
                        ),
                        type_env,
                    ),
                    &signature_without_values,
                )?)
            }
            ModuleTypeDesc::Tmty_ident(_, _) => not_implemented("Tmty_ident"),
            ModuleTypeDesc::Tmty_functor(_, _, _, _) => not_implemented("Tmty_functor"),
            ModuleTypeDesc::Tmty_with(_, _) => not_implemented("Tmty_with"),
            ModuleTypeDesc::Tmty_typeof(_) => not_implemented("Tmty_typeof"),
            ModuleTypeDesc::Tmty_alias(_, _) => not_implemented("Tmty_alias"),
        },
    })
}

pub fn translate_signature_item(
    ctx: &crate::types::context::TypeContext,
    arena: &ParseArena,
    config: &crate::gentype::config::T,
    output_file_relative: &str,
    resolver: &crate::gentype::module_resolver::Resolver,
    type_env: &crate::gentype::type_env::T,
    signature_item: &TypedSignatureItem,
) -> crate::gentype::annotation::Read<crate::gentype::translation::T> {
    // Mirrors compiler/gentype/TranslateSignature.ml:97-161.
    Ok(match &signature_item.sig_desc {
        TypedSignatureItemDesc::Tsig_type(rec_flag, type_declarations) => {
            crate::gentype::translation::T {
                import_types: vec![],
                code_items: vec![],
                type_declarations:
                    crate::gentype::translate_type_declarations::translate_type_declarations(
                        ctx,
                        arena,
                        config,
                        output_file_relative,
                        matches!(rec_flag, crate::parser::ast::RecFlag::Recursive),
                        resolver,
                        type_env,
                        type_declarations,
                    )?,
            }
        }
        TypedSignatureItemDesc::Tsig_value(value_description) => {
            let is_import = crate::gentype::annotation::has_attribute(
                arena,
                crate::gentype::annotation::tag_is_gentype_import,
                &value_description.val_attributes,
            )?;
            if value_description.val_prim.is_some() || is_import {
                crate::gentype::translation::translate_primitive(
                    ctx,
                    arena,
                    config,
                    output_file_relative,
                    resolver,
                    type_env,
                    value_description,
                )?
            } else {
                let module_item =
                    crate::gentype::runtime::new_module_item(value_description.val_id.name());
                crate::gentype::type_env::update_module_item(module_item, type_env);
                translate_signature_value(
                    ctx,
                    arena,
                    config,
                    output_file_relative,
                    resolver,
                    type_env,
                    value_description,
                )?
            }
        }
        TypedSignatureItemDesc::Tsig_module(module_declaration) => translate_module_declaration(
            ctx,
            arena,
            config,
            output_file_relative,
            resolver,
            type_env,
            module_declaration,
        )?,
        TypedSignatureItemDesc::Tsig_modtype(module_type_declaration) => {
            let module_item =
                crate::gentype::runtime::new_module_item(module_type_declaration.mtd_id.name());
            let config = crate::gentype::annotation::update_config_for_module(
                arena,
                config,
                &module_type_declaration.mtd_attributes,
            )?;
            crate::gentype::type_env::update_module_item(module_item, type_env);
            translate_module_type_declaration(
                ctx,
                arena,
                &config,
                output_file_relative,
                resolver,
                type_env,
                module_type_declaration,
            )?
        }
        TypedSignatureItemDesc::Tsig_typext(_) => not_implemented("Tsig_typext"),
        TypedSignatureItemDesc::Tsig_exception(_) => not_implemented("Tsig_exception"),
        TypedSignatureItemDesc::Tsig_recmodule(_) => not_implemented("Tsig_recmodule"),
        TypedSignatureItemDesc::Tsig_open(_) => not_implemented("Tsig_open"),
        TypedSignatureItemDesc::Tsig_include(_) => not_implemented("Tsig_include"),
        TypedSignatureItemDesc::Tsig_attribute(_) => not_implemented("Tsig_attribute"),
    })
}

pub fn translate_signature(
    ctx: &crate::types::context::TypeContext,
    arena: &ParseArena,
    config: &crate::gentype::config::T,
    output_file_relative: &str,
    resolver: &crate::gentype::module_resolver::Resolver,
    type_env: &crate::gentype::type_env::T,
    signature: &TypedSignature,
) -> crate::gentype::annotation::Read<Vec<crate::gentype::translation::T>> {
    // Mirrors compiler/gentype/TranslateSignature.ml:163-169.
    if crate::gentype::debug::translation.load(std::sync::atomic::Ordering::Relaxed) {
        crate::gentype::log_::item("Translate Signature\n");
    }
    signature
        .sig_items
        .iter()
        .map(|signature_item| {
            translate_signature_item(
                ctx,
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
