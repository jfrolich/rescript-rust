// Port of compiler/gentype/Annotation.ml:1-295.
// This Stage 3 GenType port is intentionally not wired into the crate yet.

use crate::location::Location;
use crate::parse_arena::{LocIdx, ParseArena};
use crate::parser::ast::{Attribute, Attributes, Constant, Expression, ExpressionDesc, Payload};
use crate::parser::longident::Longident;
use crate::types::typedtree::{
    ModuleExpr, ModuleExprDesc, ModuleType, ModuleTypeConstraint, ModuleTypeDeclaration,
    ModuleTypeDesc, Structure, StructureItem, StructureItemDesc, TypedModuleDeclaration,
    TypedSignature, TypedSignatureItem, TypedSignatureItemDesc,
};

#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct Import {
    pub import_path: crate::gentype::import_path::T,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AttributePayload {
    BoolPayload(bool),
    FloatPayload(String),
    IdentPayload(Longident),
    IntPayload(String),
    StringPayload(String),
    TuplePayload(Vec<AttributePayload>),
    UnrecognizedPayload,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum T {
    GenType,
    GenTypeOpaque,
    NoGenType,
}

pub fn to_string(annotation: T) -> &'static str {
    match annotation {
        T::GenType => "GenType",
        T::GenTypeOpaque => "GenTypeOpaque",
        T::NoGenType => "NoGenType",
    }
}

pub fn tag_is_gentype(s: &str) -> bool {
    s == "genType" || s == "gentype"
}

pub fn tag_is_gentype_as(s: &str) -> bool {
    s == "genType.as" || s == "gentype.as"
}

pub fn tag_is_as(s: &str) -> bool {
    s == "as"
}

pub fn tag_is_int(s: &str) -> bool {
    s == "int"
}

pub fn tag_is_string(s: &str) -> bool {
    s == "string"
}

pub fn tag_is_gentype_import(s: &str) -> bool {
    s == "genType.import" || s == "gentype.import"
}

pub fn tag_is_gentype_opaque(s: &str) -> bool {
    s == "genType.opaque" || s == "gentype.opaque"
}

pub fn tag_is_one_of_the_gentype_annotations(s: &str) -> bool {
    tag_is_gentype(s)
        || tag_is_gentype_as(s)
        || tag_is_gentype_import(s)
        || tag_is_gentype_opaque(s)
}

pub fn tag_is_gentype_ignore_interface(s: &str) -> bool {
    s == "genType.ignoreInterface" || s == "gentype.ignoreInterface"
}

pub fn tag_is_doc(s: &str) -> bool {
    s == "res.doc"
}

pub fn tag_is_intern_local(s: &str) -> bool {
    s == "internal.local"
}

fn from_expr(arena: &ParseArena, expr: &Expression) -> Option<AttributePayload> {
    // Mirrors compiler/gentype/Annotation.ml:43-68.
    if let Some(s) = crate::ast_payload::semantic_string_of_expression(arena, expr).ok().flatten() {
        return Some(AttributePayload::StringPayload(s));
    }
    match expr.pexp_desc.as_ref() {
        ExpressionDesc::Pexp_constant(constant) => match constant.as_ref() {
            Constant::Integer(n, _) => Some(AttributePayload::IntPayload(n.to_string())),
            Constant::Float(s, _) => Some(AttributePayload::FloatPayload(s.to_string())),
            _ => None,
        },
        ExpressionDesc::Pexp_construct(lid, _) => match arena.get_longident(lid.txt) {
            Longident::Lident(name) => match arena.get_string(*name) {
                "true" => Some(AttributePayload::BoolPayload(true)),
                "false" => Some(AttributePayload::BoolPayload(false)),
                _ => None,
            },
            _ => None,
        },
        ExpressionDesc::Pexp_tuple(exprs) => {
            let payloads = exprs
                .iter()
                .filter_map(|expr_idx| from_expr(arena, arena.get_expr(*expr_idx)))
                .collect();
            Some(AttributePayload::TuplePayload(payloads))
        }
        ExpressionDesc::Pexp_ident(lid) => Some(AttributePayload::IdentPayload(
            arena.get_longident(lid.txt).clone(),
        )),
        _ => None,
    }
}

pub fn get_attribute_payload(
    arena: &ParseArena,
    check_text: impl Fn(&str) -> bool + Copy,
    attributes: &Attributes,
) -> Option<(LocIdx, AttributePayload)> {
    // Mirrors compiler/gentype/Annotation.ml:69-95: inspect attributes in
    // source order and stop at the first matching tag.
    for (txt, payload) in attributes.iter() {
        if check_text(arena.get_string(txt.txt)) {
            let payload = match payload {
                Payload::PStr(items) => match items.first() {
                    None => Some(AttributePayload::UnrecognizedPayload),
                    Some(structure_item) => match structure_item.pstr_desc.as_ref() {
                        crate::parser::ast::StructureItemDesc::Pstr_eval(eval) => {
                            Some(from_expr(arena, arena.get_expr(eval.0))?)
                        }
                        _ => Some(AttributePayload::UnrecognizedPayload),
                    },
                },
                Payload::PPat(_) | Payload::PSig(_) | Payload::PTyp(_) => {
                    Some(AttributePayload::UnrecognizedPayload)
                }
            };
            return payload.map(|payload| (txt.loc, payload));
        }
    }
    None
}

pub fn get_gentype_as_renaming(arena: &ParseArena, attributes: &Attributes) -> Option<String> {
    match get_attribute_payload(arena, tag_is_gentype_as, attributes) {
        Some((_, AttributePayload::StringPayload(s))) => Some(s),
        None => match get_attribute_payload(arena, tag_is_gentype, attributes) {
            Some((_, AttributePayload::StringPayload(s))) => Some(s),
            _ => None,
        },
        _ => None,
    }
}

fn warn_gentype_as_renaming(loc: &Location) {
    // Mirrors compiler/gentype/Annotation.ml:106-121.
    crate::gentype::log_::color::setup();
    crate::gentype::log_::info(
        || {
            "\n@genType.as is not supported anymore in type definitions. Use @as from the language."
                .to_string()
        },
        loc,
        "Warning genType",
    );
}

pub fn check_unsupported_gentype_as_renaming(arena: &ParseArena, attributes: &Attributes) {
    match get_attribute_payload(arena, tag_is_gentype_as, attributes) {
        Some((loc, _)) => warn_gentype_as_renaming(&arena.to_location(loc)),
        None => {
            if let Some((loc, _)) = get_attribute_payload(arena, tag_is_gentype, attributes) {
                warn_gentype_as_renaming(&arena.to_location(loc));
            }
        }
    }
}

pub fn get_as_string(arena: &ParseArena, attributes: &Attributes) -> Option<String> {
    match get_attribute_payload(arena, tag_is_as, attributes) {
        Some((_, AttributePayload::StringPayload(s))) => Some(s),
        _ => None,
    }
}

pub fn get_as_int(arena: &ParseArena, attributes: &Attributes) -> Option<i32> {
    match get_attribute_payload(arena, tag_is_as, attributes) {
        Some((_, AttributePayload::IntPayload(s))) => s.parse().ok(),
        _ => None,
    }
}

pub fn get_attribute_import_renaming(
    arena: &ParseArena,
    attributes: &Attributes,
) -> (Option<String>, Option<String>) {
    let attribute_import = get_attribute_payload(arena, tag_is_gentype_import, attributes);
    let gentype_as_renaming = get_gentype_as_renaming(arena, attributes);
    match attribute_import {
        Some((_, AttributePayload::StringPayload(import_string))) => {
            (Some(import_string), gentype_as_renaming)
        }
        Some((_, AttributePayload::TuplePayload(payloads))) => match payloads.as_slice() {
            [
                AttributePayload::StringPayload(import_string),
                AttributePayload::StringPayload(rename_string),
            ] => (Some(import_string.clone()), Some(rename_string.clone())),
            _ => (None, gentype_as_renaming),
        },
        _ => (None, gentype_as_renaming),
    }
}

pub fn get_doc_payload(arena: &ParseArena, attributes: &Attributes) -> Option<String> {
    match get_attribute_payload(arena, tag_is_doc, attributes) {
        Some((_, AttributePayload::StringPayload(doc_string))) if !doc_string.is_empty() => {
            Some(doc_string)
        }
        _ => None,
    }
}

pub fn doc_string_from_attrs(
    arena: &ParseArena,
    attributes: &Attributes,
) -> crate::gentype::gen_type_common::doc_string::T {
    get_doc_payload(arena, attributes)
}

pub fn has_attribute(
    arena: &ParseArena,
    check_text: impl Fn(&str) -> bool + Copy,
    attributes: &Attributes,
) -> bool {
    get_attribute_payload(arena, check_text, attributes).is_some()
}

pub fn from_attributes(
    arena: &ParseArena,
    config: &crate::gentype::config::T,
    loc: LocIdx,
    attributes: &Attributes,
) -> T {
    // Mirrors compiler/gentype/Annotation.ml:166-181.
    let default = match config.everything {
        true => T::GenType,
        false => T::NoGenType,
    };
    if has_attribute(arena, tag_is_gentype_opaque, attributes) {
        T::GenTypeOpaque
    } else if has_attribute(
        arena,
        |s| tag_is_gentype(s) || tag_is_gentype_as(s),
        attributes,
    ) {
        match get_attribute_payload(arena, tag_is_gentype, attributes) {
            Some((_, AttributePayload::UnrecognizedPayload)) | None => {}
            Some(_) => {
                crate::gentype::log_::color::setup();
                let location = arena.to_location(loc);
                crate::gentype::log_::info(
                    || "Annotation payload is ignored".to_string(),
                    &location,
                    "Warning genType",
                );
            }
        }
        T::GenType
    } else {
        default
    }
}

pub fn module_type_check_annotation(
    arena: &ParseArena,
    check_annotation: &impl Fn(LocIdx, &Attributes) -> bool,
    module_type: &ModuleType,
) -> bool {
    // Mirrors compiler/gentype/Annotation.ml:183-190.
    match &module_type.mty_desc {
        ModuleTypeDesc::Tmty_signature(signature) => {
            signature_check_annotation(arena, check_annotation, signature)
        }
        ModuleTypeDesc::Tmty_ident(_, _)
        | ModuleTypeDesc::Tmty_functor(_, _, _, _)
        | ModuleTypeDesc::Tmty_with(_, _)
        | ModuleTypeDesc::Tmty_typeof(_)
        | ModuleTypeDesc::Tmty_alias(_, _)
        | ModuleTypeDesc::Tmty_placeholder => false,
    }
}

pub fn module_type_declaration_check_annotation(
    arena: &ParseArena,
    check_annotation: &impl Fn(LocIdx, &Attributes) -> bool,
    module_type_declaration: &ModuleTypeDeclaration,
) -> bool {
    // Mirrors compiler/gentype/Annotation.ml:192-200.
    check_annotation(
        module_type_declaration.mtd_loc,
        &module_type_declaration.mtd_attributes,
    ) || match module_type_declaration.mtd_type.as_ref() {
        None => false,
        Some(module_type) => module_type_check_annotation(arena, check_annotation, module_type),
    }
}

pub fn module_declaration_check_annotation(
    arena: &ParseArena,
    check_annotation: &impl Fn(LocIdx, &Attributes) -> bool,
    module_declaration: &TypedModuleDeclaration,
) -> bool {
    // Mirrors compiler/gentype/Annotation.ml:202-205.
    check_annotation(module_declaration.md_loc, &module_declaration.md_attributes)
        || module_type_check_annotation(arena, check_annotation, &module_declaration.md_type)
}

pub fn signature_item_check_annotation(
    arena: &ParseArena,
    check_annotation: &impl Fn(LocIdx, &Attributes) -> bool,
    signature_item: &TypedSignatureItem,
) -> bool {
    // Mirrors compiler/gentype/Annotation.ml:207-226.
    match &signature_item.sig_desc {
        TypedSignatureItemDesc::Tsig_type(_, type_declarations) => {
            type_declarations.iter().any(|type_declaration| {
                check_annotation(type_declaration.typ_loc, &type_declaration.typ_attributes)
            })
        }
        TypedSignatureItemDesc::Tsig_value(value_description) => {
            check_annotation(value_description.val_loc, &value_description.val_attributes)
        }
        TypedSignatureItemDesc::Tsig_module(module_declaration) => {
            module_declaration_check_annotation(arena, check_annotation, module_declaration)
        }
        TypedSignatureItemDesc::Tsig_attribute(attribute) => {
            let attributes = singleton_attribute(attribute);
            check_annotation(signature_item.sig_loc, &attributes)
        }
        TypedSignatureItemDesc::Tsig_modtype(module_type_declaration) => {
            module_type_declaration_check_annotation(
                arena,
                check_annotation,
                module_type_declaration,
            )
        }
        TypedSignatureItemDesc::Tsig_typext(_)
        | TypedSignatureItemDesc::Tsig_exception(_)
        | TypedSignatureItemDesc::Tsig_recmodule(_)
        | TypedSignatureItemDesc::Tsig_open(_)
        | TypedSignatureItemDesc::Tsig_include(_) => false,
    }
}

pub fn signature_check_annotation(
    arena: &ParseArena,
    check_annotation: &impl Fn(LocIdx, &Attributes) -> bool,
    signature: &TypedSignature,
) -> bool {
    // Mirrors compiler/gentype/Annotation.ml:228-231.
    signature.sig_items.iter().any(|signature_item| {
        signature_item_check_annotation(arena, check_annotation, signature_item)
    })
}

pub fn structure_item_check_annotation(
    arena: &ParseArena,
    check_annotation: &impl Fn(LocIdx, &Attributes) -> bool,
    structure_item: &StructureItem,
) -> bool {
    // Mirrors compiler/gentype/Annotation.ml:233-261.
    match &structure_item.str_desc {
        StructureItemDesc::Tstr_type(_, type_declarations) => {
            type_declarations.iter().any(|type_declaration| {
                check_annotation(type_declaration.typ_loc, &type_declaration.typ_attributes)
            })
        }
        StructureItemDesc::Tstr_value(_, value_bindings) => value_bindings
            .iter()
            .any(|vb| check_annotation(vb.vb_loc, &vb.vb_attributes)),
        StructureItemDesc::Tstr_primitive(value_description) => {
            check_annotation(value_description.val_loc, &value_description.val_attributes)
        }
        StructureItemDesc::Tstr_module(module_binding) => {
            module_binding_check_annotation(arena, check_annotation, module_binding)
        }
        StructureItemDesc::Tstr_recmodule(module_bindings) => {
            module_bindings.iter().any(|module_binding| {
                module_binding_check_annotation(arena, check_annotation, module_binding)
            })
        }
        StructureItemDesc::Tstr_include(include_declaration) => {
            check_annotation(
                include_declaration.incl_loc,
                &include_declaration.incl_attributes,
            ) || module_expr_check_annotation(
                arena,
                check_annotation,
                &include_declaration.incl_mod,
            )
        }
        StructureItemDesc::Tstr_modtype(module_type_declaration) => {
            module_type_declaration_check_annotation(
                arena,
                check_annotation,
                module_type_declaration,
            )
        }
        StructureItemDesc::Tstr_attribute(attribute) => {
            let attributes = singleton_attribute(attribute);
            check_annotation(structure_item.str_loc, &attributes)
        }
        StructureItemDesc::Tstr_eval(_, _)
        | StructureItemDesc::Tstr_typext(_)
        | StructureItemDesc::Tstr_exception(_)
        | StructureItemDesc::Tstr_open(_) => false,
    }
}

pub fn module_expr_check_annotation(
    arena: &ParseArena,
    check_annotation: &impl Fn(LocIdx, &Attributes) -> bool,
    module_expr: &ModuleExpr,
) -> bool {
    // Mirrors compiler/gentype/Annotation.ml:263-276.
    match &module_expr.mod_desc {
        ModuleExprDesc::Tmod_structure(structure) => {
            structure_check_annotation(arena, check_annotation, structure)
        }
        ModuleExprDesc::Tmod_constraint(module_expr, _, module_type_constraint, _) => {
            module_expr_check_annotation(arena, check_annotation, module_expr)
                || match module_type_constraint {
                    ModuleTypeConstraint::Tmodtype_explicit(module_type) => {
                        module_type_check_annotation(arena, check_annotation, module_type)
                    }
                    ModuleTypeConstraint::Tmodtype_implicit => false,
                }
        }
        ModuleExprDesc::Tmod_ident(_, _)
        | ModuleExprDesc::Tmod_functor(_, _, _, _)
        | ModuleExprDesc::Tmod_apply(_, _, _)
        | ModuleExprDesc::Tmod_unpack(_, _) => false,
    }
}

pub fn module_binding_check_annotation(
    arena: &ParseArena,
    check_annotation: &impl Fn(LocIdx, &Attributes) -> bool,
    module_binding: &crate::types::typedtree::ModuleBinding,
) -> bool {
    // Mirrors compiler/gentype/Annotation.ml:278-281.
    check_annotation(module_binding.mb_loc, &module_binding.mb_attributes)
        || module_expr_check_annotation(arena, check_annotation, &module_binding.mb_expr)
}

pub fn structure_check_annotation(
    arena: &ParseArena,
    check_annotation: &impl Fn(LocIdx, &Attributes) -> bool,
    structure: &Structure,
) -> bool {
    // Mirrors compiler/gentype/Annotation.ml:283-286.
    structure.str_items.iter().any(|structure_item| {
        structure_item_check_annotation(arena, check_annotation, structure_item)
    })
}

pub fn import_from_string(import_string: &str) -> Import {
    // Mirrors compiler/gentype/Annotation.ml:288-290.
    Import {
        import_path: crate::gentype::import_path::from_string_unsafe(import_string),
    }
}

pub fn update_config_for_module<'c>(
    arena: &ParseArena,
    config: &'c crate::gentype::config::T,
    attributes: &Attributes,
) -> std::borrow::Cow<'c, crate::gentype::config::T> {
    // Mirrors compiler/gentype/Annotation.ml:292-295.
    if has_attribute(arena, tag_is_gentype, attributes) {
        let mut config = config.clone();
        config.everything = true;
        std::borrow::Cow::Owned(config)
    } else {
        std::borrow::Cow::Borrowed(config)
    }
}

fn decl_attribute_payload_is_empty(payload: &crate::types::decl::AttributePayload) -> bool {
    matches!(
        payload,
        crate::types::decl::AttributePayload::Empty
            | crate::types::decl::AttributePayload::Structure(_)
    )
}

fn decl_attribute_payload_as_string(
    payload: &crate::types::decl::AttributePayload,
) -> Option<String> {
    match payload {
        crate::types::decl::AttributePayload::Str(s) => Some(s.clone()),
        _ => None,
    }
}

fn decl_attribute_payload_as_int(payload: &crate::types::decl::AttributePayload) -> Option<i32> {
    match payload {
        crate::types::decl::AttributePayload::Int(n) => i32::try_from(*n).ok(),
        crate::types::decl::AttributePayload::IntLiteral(s) => s.parse().ok(),
        _ => None,
    }
}

pub fn get_decl_attribute_payload<'a>(
    check_text: impl Fn(&str) -> bool + Copy,
    attributes: &'a [crate::types::decl::Attribute],
) -> Option<&'a crate::types::decl::AttributePayload> {
    // Mirrors compiler/gentype/Annotation.ml:69-95 for Types.signature
    // attributes. Rust stores these payloads in decl::Attribute instead of
    // parser::Payload after typemod conversion.
    attributes
        .iter()
        .find(|attribute| check_text(&attribute.attr_name.txt))
        .map(|attribute| &attribute.attr_payload)
}

pub fn get_decl_gentype_as_renaming(
    attributes: &[crate::types::decl::Attribute],
) -> Option<String> {
    match get_decl_attribute_payload(tag_is_gentype_as, attributes)
        .and_then(decl_attribute_payload_as_string)
    {
        Some(s) => Some(s),
        None => get_decl_attribute_payload(tag_is_gentype, attributes)
            .and_then(decl_attribute_payload_as_string),
    }
}

pub fn get_decl_as_string(attributes: &[crate::types::decl::Attribute]) -> Option<String> {
    get_decl_attribute_payload(tag_is_as, attributes).and_then(decl_attribute_payload_as_string)
}

pub fn get_decl_as_int(attributes: &[crate::types::decl::Attribute]) -> Option<i32> {
    get_decl_attribute_payload(tag_is_as, attributes).and_then(decl_attribute_payload_as_int)
}

pub fn get_decl_doc_payload(attributes: &[crate::types::decl::Attribute]) -> Option<String> {
    get_decl_attribute_payload(tag_is_doc, attributes)
        .and_then(decl_attribute_payload_as_string)
        .filter(|doc_string| !doc_string.is_empty())
}

pub fn doc_string_from_decl_attrs(
    attributes: &[crate::types::decl::Attribute],
) -> crate::gentype::gen_type_common::doc_string::T {
    get_decl_doc_payload(attributes)
}

pub fn has_decl_attribute(
    check_text: impl Fn(&str) -> bool + Copy,
    attributes: &[crate::types::decl::Attribute],
) -> bool {
    get_decl_attribute_payload(check_text, attributes).is_some()
}

pub fn get_decl_attribute_import_renaming(
    attributes: &[crate::types::decl::Attribute],
) -> (Option<String>, Option<String>) {
    // Mirrors compiler/gentype/Annotation.ml:136-148. The Rust decl attribute
    // payload currently preserves the common string import payload; tuple import
    // payloads need a typedtree payload-preservation pass before final parity.
    let attribute_import = get_decl_attribute_payload(tag_is_gentype_import, attributes);
    let gentype_as_renaming = get_decl_gentype_as_renaming(attributes);
    match attribute_import.and_then(decl_attribute_payload_as_string) {
        Some(import_string) => (Some(import_string), gentype_as_renaming),
        None => (None, gentype_as_renaming),
    }
}

fn warn_gentype_as_renaming_decl(loc: &Location) {
    crate::gentype::log_::color::setup();
    crate::gentype::log_::info(
        || {
            "\n@genType.as is not supported anymore in type definitions. Use @as from the language."
                .to_string()
        },
        loc,
        "Warning genType",
    );
}

pub fn check_unsupported_decl_gentype_as_renaming(attributes: &[crate::types::decl::Attribute]) {
    if let Some(attribute) = attributes
        .iter()
        .find(|attribute| tag_is_gentype_as(&attribute.attr_name.txt))
        .or_else(|| {
            attributes
                .iter()
                .find(|attribute| tag_is_gentype(&attribute.attr_name.txt))
        })
    {
        warn_gentype_as_renaming_decl(&attribute.attr_loc);
    }
}

pub fn from_decl_attributes(
    config: &crate::gentype::config::T,
    loc: &Location,
    attributes: &[crate::types::decl::Attribute],
) -> T {
    // Mirrors compiler/gentype/Annotation.ml:166-181 for Types.signature
    // attributes, whose locations are already materialized as Location values.
    let default = match config.everything {
        true => T::GenType,
        false => T::NoGenType,
    };
    if has_decl_attribute(tag_is_gentype_opaque, attributes) {
        T::GenTypeOpaque
    } else if has_decl_attribute(|s| tag_is_gentype(s) || tag_is_gentype_as(s), attributes) {
        if let Some(payload) = get_decl_attribute_payload(tag_is_gentype, attributes)
            && !decl_attribute_payload_is_empty(payload)
        {
            crate::gentype::log_::color::setup();
            crate::gentype::log_::info(
                || "Annotation payload is ignored".to_string(),
                loc,
                "Warning genType",
            );
        }
        T::GenType
    } else {
        default
    }
}

pub fn update_config_for_decl_module(
    config: &crate::gentype::config::T,
    attributes: &[crate::types::decl::Attribute],
) -> crate::gentype::config::T {
    // Mirrors compiler/gentype/Annotation.ml:292-295 for Types.signature
    // attributes.
    if has_decl_attribute(tag_is_gentype, attributes) {
        let mut config = config.clone();
        config.everything = true;
        config
    } else {
        config.clone()
    }
}

fn singleton_attribute(attribute: &Attribute) -> Attributes {
    Attributes::from_vec(vec![attribute.clone()])
}
