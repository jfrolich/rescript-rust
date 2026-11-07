// Port of compiler/gentype/Annotation.ml:1-295.

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

/// The template with an invalid escape (only a PPX makes one) where
/// `Ast_payload.semantic_string_of_expression` raises (ast_payload.ml:39-51),
/// in the artifact's parse tree or a declaration's attribute. Nothing in
/// genType catches the raise: it ends genType and fails the compile.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InvalidEscape {
    Parsed(LocIdx),
    Decl(crate::types::DeclLoc),
}

/// A genType reader's result: `Err` where the OCaml reader raises.
pub type Read<T> = Result<T, InvalidEscape>;

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

fn from_expr(arena: &ParseArena, expr: &Expression) -> Read<Option<AttributePayload>> {
    // Mirrors compiler/gentype/Annotation.ml:43-68.
    if let Some(s) = crate::ast_payload::semantic_string_of_expression(arena, expr)
        .map_err(|error| InvalidEscape::Parsed(error.loc))?
    {
        return Ok(Some(AttributePayload::StringPayload(s)));
    }
    Ok(
        match &crate::ast_payload::unwrap_braces(arena, expr).pexp_desc {
            ExpressionDesc::Pexp_constant(constant) => match constant {
                Constant::Integer(n, _) => Some(AttributePayload::IntPayload(
                    arena.get_string(*n).to_string(),
                )),
                Constant::Float(s, _) => Some(AttributePayload::FloatPayload(
                    arena.get_string(*s).to_string(),
                )),
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
                // Annotation.ml:54-62 folds over the reversed elements: the last
                // is read first.
                let mut payloads = Vec::new();
                for expr_idx in arena.expr_list(*exprs).iter().rev() {
                    if let Some(payload) = from_expr(arena, arena.get_expr(*expr_idx))? {
                        payloads.push(payload);
                    }
                }
                payloads.reverse();
                Some(AttributePayload::TuplePayload(payloads))
            }
            ExpressionDesc::Pexp_ident(lid) => Some(AttributePayload::IdentPayload(
                arena.get_longident(lid.txt).clone(),
            )),
            _ => None,
        },
    )
}

pub fn get_attribute_payload(
    arena: &ParseArena,
    check_text: impl Fn(&str) -> bool + Copy,
    attributes: &Attributes,
) -> Read<Option<(LocIdx, AttributePayload)>> {
    // Mirrors compiler/gentype/Annotation.ml:69-95: inspect attributes in
    // source order and stop at the first matching tag.
    for (txt, payload) in attributes.iter() {
        if check_text(arena.get_string(txt.txt)) {
            let payload = match payload {
                Payload::PStr(items) => match items.first() {
                    None => Some(AttributePayload::UnrecognizedPayload),
                    Some(structure_item) => match &structure_item.pstr_desc {
                        crate::parser::ast::StructureItemDesc::Pstr_eval(eval) => {
                            from_expr(arena, arena.get_expr(eval.0))?
                        }
                        _ => Some(AttributePayload::UnrecognizedPayload),
                    },
                },
                Payload::PPat(_) | Payload::PSig(_) | Payload::PTyp(_) => {
                    Some(AttributePayload::UnrecognizedPayload)
                }
            };
            return Ok(payload.map(|payload| (txt.loc, payload)));
        }
    }
    Ok(None)
}

pub fn get_gentype_as_renaming(
    arena: &ParseArena,
    attributes: &Attributes,
) -> Read<Option<String>> {
    Ok(
        match get_attribute_payload(arena, tag_is_gentype_as, attributes)? {
            Some((_, AttributePayload::StringPayload(s))) => Some(s),
            None => match get_attribute_payload(arena, tag_is_gentype, attributes)? {
                Some((_, AttributePayload::StringPayload(s))) => Some(s),
                _ => None,
            },
            _ => None,
        },
    )
}

const GENTYPE_AS_RENAMING: &str =
    "\n@genType.as is not supported anymore in type definitions. Use @as from the language.";

/// The file a parsed location is in, as Location.get_pos_info names it.
/// A location-free parse has none: a compile whose GenType prints a note
/// from one is retried with locations (`Outcome::needs_locations`).
pub fn parsed_file(arena: &ParseArena, loc: &Location) -> String {
    if !arena.stores_locations() {
        return String::new();
    }
    arena.get_string(loc.loc_start.file_name).to_string()
}

/// The file a declaration location is in. The handle's kind does not say
/// which unit it came from (an imported declaration keeps a source handle),
/// so the file index's owner does: importing a declaration renames its file
/// into the context's file table (`DeclLocImport::files`, interned by
/// `TypeContext::intern_cmi_longident_name` or the shared pool), and any
/// other file is one of the compiling unit's own, named by its parse arena.
pub fn decl_file(
    ctx: &crate::types::context::TypeContext,
    arena: &ParseArena,
    loc: crate::types::DeclLoc,
) -> String {
    let resolved = ctx.resolve_loc(loc);
    if resolved.is_none() {
        return String::new();
    }
    let file = resolved.loc_start.file_name;
    match ctx.resolve_cmi_longident_component(file) {
        Some(imported) => imported,
        None => arena
            .own_file_name(file)
            .unwrap_or_else(|| panic!("declaration location in an unknown file {file:?}"))
            .to_string(),
    }
}

fn warn_gentype_as_renaming(notes: &crate::gentype::log_::Notes, arena: &ParseArena, loc: LocIdx) {
    // Mirrors compiler/gentype/Annotation.ml:106-121.
    let loc = arena.to_location(loc);
    notes.info(
        &parsed_file(arena, &loc),
        &loc,
        "Warning genType",
        GENTYPE_AS_RENAMING,
    );
}

pub fn check_unsupported_gentype_as_renaming(
    arena: &ParseArena,
    notes: &crate::gentype::log_::Notes,
    attributes: &Attributes,
) -> Read<()> {
    match get_attribute_payload(arena, tag_is_gentype_as, attributes)? {
        Some((loc, _)) => warn_gentype_as_renaming(notes, arena, loc),
        None => {
            if let Some((loc, _)) = get_attribute_payload(arena, tag_is_gentype, attributes)? {
                warn_gentype_as_renaming(notes, arena, loc);
            }
        }
    }
    Ok(())
}

pub fn get_as_string(arena: &ParseArena, attributes: &Attributes) -> Read<Option<String>> {
    Ok(match get_attribute_payload(arena, tag_is_as, attributes)? {
        Some((_, AttributePayload::StringPayload(s))) => Some(s),
        _ => None,
    })
}

pub fn get_as_int(arena: &ParseArena, attributes: &Attributes) -> Read<Option<i32>> {
    Ok(match get_attribute_payload(arena, tag_is_as, attributes)? {
        Some((_, AttributePayload::IntPayload(s))) => s.parse().ok(),
        _ => None,
    })
}

pub fn get_attribute_import_renaming(
    arena: &ParseArena,
    attributes: &Attributes,
) -> Read<(Option<String>, Option<String>)> {
    // Annotation.ml:136-139: the import, then the renaming.
    let attribute_import = get_attribute_payload(arena, tag_is_gentype_import, attributes)?;
    let gentype_as_renaming = get_gentype_as_renaming(arena, attributes)?;
    Ok(match attribute_import {
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
    })
}

pub fn get_doc_payload(arena: &ParseArena, attributes: &Attributes) -> Read<Option<String>> {
    Ok(
        match get_attribute_payload(arena, tag_is_doc, attributes)? {
            Some((_, AttributePayload::StringPayload(doc_string))) if !doc_string.is_empty() => {
                Some(doc_string)
            }
            _ => None,
        },
    )
}

pub fn doc_string_from_attrs(
    arena: &ParseArena,
    attributes: &Attributes,
) -> Read<crate::gentype::gen_type_common::doc_string::T> {
    get_doc_payload(arena, attributes)
}

pub fn has_attribute(
    arena: &ParseArena,
    check_text: impl Fn(&str) -> bool + Copy,
    attributes: &Attributes,
) -> Read<bool> {
    Ok(get_attribute_payload(arena, check_text, attributes)?.is_some())
}

pub fn from_attributes(
    arena: &ParseArena,
    config: &crate::gentype::config::T,
    notes: &crate::gentype::log_::Notes,
    loc: LocIdx,
    attributes: &Attributes,
) -> Read<T> {
    // Mirrors compiler/gentype/Annotation.ml:166-181.
    let default = match config.everything {
        true => T::GenType,
        false => T::NoGenType,
    };
    Ok(
        if has_attribute(arena, tag_is_gentype_opaque, attributes)? {
            T::GenTypeOpaque
        } else if has_attribute(
            arena,
            |s| tag_is_gentype(s) || tag_is_gentype_as(s),
            attributes,
        )? {
            match get_attribute_payload(arena, tag_is_gentype, attributes)? {
                Some((_, AttributePayload::UnrecognizedPayload)) | None => {}
                Some(_) => {
                    let location = arena.to_location(loc);
                    notes.info(
                        &parsed_file(arena, &location),
                        &location,
                        "Warning genType",
                        "Annotation payload is ignored",
                    );
                }
            }
            T::GenType
        } else {
            default
        },
    )
}

/// `List.exists` over a reader that may raise: the first true stops, a raise
/// propagates.
fn exists<I>(items: I, mut f: impl FnMut(I::Item) -> Read<bool>) -> Read<bool>
where
    I: IntoIterator,
{
    for item in items {
        if f(item)? {
            return Ok(true);
        }
    }
    Ok(false)
}

pub fn module_type_check_annotation(
    arena: &ParseArena,
    check_annotation: &impl Fn(LocIdx, &Attributes) -> Read<bool>,
    module_type: &ModuleType,
) -> Read<bool> {
    // Mirrors compiler/gentype/Annotation.ml:183-190.
    match &module_type.mty_desc {
        ModuleTypeDesc::Tmty_signature(signature) => {
            signature_check_annotation(arena, check_annotation, signature)
        }
        ModuleTypeDesc::Tmty_ident(_, _)
        | ModuleTypeDesc::Tmty_functor(_, _, _, _)
        | ModuleTypeDesc::Tmty_with(_, _)
        | ModuleTypeDesc::Tmty_typeof(_)
        | ModuleTypeDesc::Tmty_alias(_, _) => Ok(false),
    }
}

pub fn module_type_declaration_check_annotation(
    arena: &ParseArena,
    check_annotation: &impl Fn(LocIdx, &Attributes) -> Read<bool>,
    module_type_declaration: &ModuleTypeDeclaration,
) -> Read<bool> {
    // Mirrors compiler/gentype/Annotation.ml:192-200.
    Ok(check_annotation(
        module_type_declaration.mtd_loc,
        &module_type_declaration.mtd_attributes,
    )? || match module_type_declaration.mtd_type.as_ref() {
        None => false,
        Some(module_type) => module_type_check_annotation(arena, check_annotation, module_type)?,
    })
}

pub fn module_declaration_check_annotation(
    arena: &ParseArena,
    check_annotation: &impl Fn(LocIdx, &Attributes) -> Read<bool>,
    module_declaration: &TypedModuleDeclaration,
) -> Read<bool> {
    // Mirrors compiler/gentype/Annotation.ml:202-205.
    Ok(
        check_annotation(module_declaration.md_loc, &module_declaration.md_attributes)?
            || module_type_check_annotation(arena, check_annotation, &module_declaration.md_type)?,
    )
}

pub fn signature_item_check_annotation(
    arena: &ParseArena,
    check_annotation: &impl Fn(LocIdx, &Attributes) -> Read<bool>,
    signature_item: &TypedSignatureItem,
) -> Read<bool> {
    // Mirrors compiler/gentype/Annotation.ml:207-226.
    match &signature_item.sig_desc {
        TypedSignatureItemDesc::Tsig_type(_, type_declarations) => {
            exists(type_declarations, |type_declaration| {
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
        | TypedSignatureItemDesc::Tsig_include(_) => Ok(false),
    }
}

pub fn signature_check_annotation(
    arena: &ParseArena,
    check_annotation: &impl Fn(LocIdx, &Attributes) -> Read<bool>,
    signature: &TypedSignature,
) -> Read<bool> {
    // Mirrors compiler/gentype/Annotation.ml:228-231.
    exists(&signature.sig_items, |signature_item| {
        signature_item_check_annotation(arena, check_annotation, signature_item)
    })
}

pub fn structure_item_check_annotation(
    arena: &ParseArena,
    check_annotation: &impl Fn(LocIdx, &Attributes) -> Read<bool>,
    structure_item: &StructureItem,
) -> Read<bool> {
    // Mirrors compiler/gentype/Annotation.ml:233-261.
    match &structure_item.str_desc {
        StructureItemDesc::Tstr_type(_, type_declarations) => {
            exists(type_declarations, |type_declaration| {
                check_annotation(type_declaration.typ_loc, &type_declaration.typ_attributes)
            })
        }
        StructureItemDesc::Tstr_value(_, value_bindings) => exists(value_bindings, |vb| {
            check_annotation(vb.vb_loc, &vb.vb_attributes)
        }),
        StructureItemDesc::Tstr_primitive(value_description) => {
            check_annotation(value_description.val_loc, &value_description.val_attributes)
        }
        StructureItemDesc::Tstr_module(module_binding) => {
            module_binding_check_annotation(arena, check_annotation, module_binding)
        }
        StructureItemDesc::Tstr_recmodule(module_bindings) => {
            exists(module_bindings, |module_binding| {
                module_binding_check_annotation(arena, check_annotation, module_binding)
            })
        }
        StructureItemDesc::Tstr_include(include_declaration) => Ok(check_annotation(
            include_declaration.incl_loc,
            &include_declaration.incl_attributes,
        )?
            || module_expr_check_annotation(
                arena,
                check_annotation,
                &include_declaration.incl_mod,
            )?),
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
        | StructureItemDesc::Tstr_open(_) => Ok(false),
    }
}

pub fn module_expr_check_annotation(
    arena: &ParseArena,
    check_annotation: &impl Fn(LocIdx, &Attributes) -> Read<bool>,
    module_expr: &ModuleExpr,
) -> Read<bool> {
    // Mirrors compiler/gentype/Annotation.ml:263-276.
    match &module_expr.mod_desc {
        ModuleExprDesc::Tmod_structure(structure) => {
            structure_check_annotation(arena, check_annotation, structure)
        }
        ModuleExprDesc::Tmod_constraint(module_expr, _, module_type_constraint, _) => Ok(
            module_expr_check_annotation(arena, check_annotation, module_expr)?
                || match module_type_constraint {
                    ModuleTypeConstraint::Tmodtype_explicit(module_type) => {
                        module_type_check_annotation(arena, check_annotation, module_type)?
                    }
                    ModuleTypeConstraint::Tmodtype_implicit => false,
                },
        ),
        ModuleExprDesc::Tmod_ident(_, _)
        | ModuleExprDesc::Tmod_functor(_, _, _, _)
        | ModuleExprDesc::Tmod_apply(_, _, _)
        | ModuleExprDesc::Tmod_unpack(_, _) => Ok(false),
    }
}

pub fn module_binding_check_annotation(
    arena: &ParseArena,
    check_annotation: &impl Fn(LocIdx, &Attributes) -> Read<bool>,
    module_binding: &crate::types::typedtree::ModuleBinding,
) -> Read<bool> {
    // Mirrors compiler/gentype/Annotation.ml:278-281.
    Ok(
        check_annotation(module_binding.mb_loc, &module_binding.mb_attributes)?
            || module_expr_check_annotation(arena, check_annotation, &module_binding.mb_expr)?,
    )
}

pub fn structure_check_annotation(
    arena: &ParseArena,
    check_annotation: &impl Fn(LocIdx, &Attributes) -> Read<bool>,
    structure: &Structure,
) -> Read<bool> {
    // Mirrors compiler/gentype/Annotation.ml:283-286.
    exists(&structure.str_items, |structure_item| {
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
) -> Read<std::borrow::Cow<'c, crate::gentype::config::T>> {
    // Mirrors compiler/gentype/Annotation.ml:292-295.
    Ok(if has_attribute(arena, tag_is_gentype, attributes)? {
        let mut config = config.clone();
        config.everything = true;
        std::borrow::Cow::Owned(config)
    } else {
        std::borrow::Cow::Borrowed(config)
    })
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
    // Read after `get_decl_attribute_payload` decoded the payload, which
    // raised on a template it cannot read.
    payload.semantic_string().ok().flatten().map(str::to_string)
}

fn decl_attribute_payload_as_int(payload: &crate::types::decl::AttributePayload) -> Option<i32> {
    match payload {
        crate::types::decl::AttributePayload::Int(n) => i32::try_from(*n).ok(),
        crate::types::decl::AttributePayload::IntLiteral(s) => s.parse().ok(),
        _ => None,
    }
}

/// The first attribute `check_text` accepts, as `get_attribute_payload`
/// finds it (Annotation.ml:69-95), with its payload decoded:
/// `semantic_string_of_expression` raises on a template it cannot read.
fn find_decl_attribute(
    check_text: impl Fn(&str) -> bool + Copy,
    attributes: &[crate::types::decl::Attribute],
) -> Read<Option<&crate::types::decl::Attribute>> {
    let Some(attribute) = attributes
        .iter()
        .find(|attribute| check_text(&attribute.attr_name.txt))
    else {
        return Ok(None);
    };
    attribute
        .attr_payload
        .semantic_string()
        .map_err(InvalidEscape::Decl)?;
    Ok(Some(attribute))
}

pub fn get_decl_attribute_payload(
    check_text: impl Fn(&str) -> bool + Copy,
    attributes: &[crate::types::decl::Attribute],
) -> Read<Option<&crate::types::decl::AttributePayload>> {
    // Mirrors compiler/gentype/Annotation.ml:69-95 for Types.signature
    // attributes. Rust stores these payloads in decl::Attribute instead of
    // parser::Payload after typemod conversion.
    Ok(find_decl_attribute(check_text, attributes)?.map(|attribute| &attribute.attr_payload))
}

pub fn get_decl_gentype_as_renaming(
    attributes: &[crate::types::decl::Attribute],
) -> Read<Option<String>> {
    Ok(
        match get_decl_attribute_payload(tag_is_gentype_as, attributes)?
            .and_then(decl_attribute_payload_as_string)
        {
            Some(s) => Some(s),
            None => get_decl_attribute_payload(tag_is_gentype, attributes)?
                .and_then(decl_attribute_payload_as_string),
        },
    )
}

pub fn get_decl_as_string(attributes: &[crate::types::decl::Attribute]) -> Read<Option<String>> {
    Ok(get_decl_attribute_payload(tag_is_as, attributes)?
        .and_then(decl_attribute_payload_as_string))
}

pub fn get_decl_as_int(attributes: &[crate::types::decl::Attribute]) -> Read<Option<i32>> {
    Ok(get_decl_attribute_payload(tag_is_as, attributes)?.and_then(decl_attribute_payload_as_int))
}

pub fn get_decl_doc_payload(attributes: &[crate::types::decl::Attribute]) -> Read<Option<String>> {
    Ok(get_decl_attribute_payload(tag_is_doc, attributes)?
        .and_then(decl_attribute_payload_as_string)
        .filter(|doc_string| !doc_string.is_empty()))
}

pub fn doc_string_from_decl_attrs(
    attributes: &[crate::types::decl::Attribute],
) -> Read<crate::gentype::gen_type_common::doc_string::T> {
    get_decl_doc_payload(attributes)
}

pub fn has_decl_attribute(
    check_text: impl Fn(&str) -> bool + Copy,
    attributes: &[crate::types::decl::Attribute],
) -> Read<bool> {
    Ok(get_decl_attribute_payload(check_text, attributes)?.is_some())
}

pub fn get_decl_attribute_import_renaming(
    attributes: &[crate::types::decl::Attribute],
) -> Read<(Option<String>, Option<String>)> {
    // Mirrors compiler/gentype/Annotation.ml:136-148.
    let attribute_import = get_decl_attribute_payload(tag_is_gentype_import, attributes)?;
    let gentype_as_renaming = get_decl_gentype_as_renaming(attributes)?;
    Ok(match attribute_import {
        Some(payload) if decl_attribute_payload_as_string(payload).is_some() => (
            decl_attribute_payload_as_string(payload),
            gentype_as_renaming,
        ),
        Some(crate::types::decl::AttributePayload::StrTuple(strings)) => match strings.as_slice() {
            [import_string, rename_string] => {
                (Some(import_string.clone()), Some(rename_string.clone()))
            }
            _ => (None, gentype_as_renaming),
        },
        _ => (None, gentype_as_renaming),
    })
}

pub fn check_unsupported_decl_gentype_as_renaming(
    ctx: &crate::types::context::TypeContext,
    arena: &ParseArena,
    notes: &crate::gentype::log_::Notes,
    attributes: &[crate::types::decl::Attribute],
) -> Read<()> {
    // Annotation.ml:107-121: `get_attribute_payload tag_is_gentype_as`, then
    // `tag_is_gentype`.
    let attribute = match find_decl_attribute(tag_is_gentype_as, attributes)? {
        Some(attribute) => Some(attribute),
        None => find_decl_attribute(tag_is_gentype, attributes)?,
    };
    if let Some(attribute) = attribute {
        let loc = ctx.resolve_loc(attribute.attr_loc);
        notes.info(
            &decl_file(ctx, arena, attribute.attr_loc),
            &loc,
            "Warning genType",
            GENTYPE_AS_RENAMING,
        );
    }
    Ok(())
}

pub fn from_decl_attributes(
    config: &crate::gentype::config::T,
    notes: &crate::gentype::log_::Notes,
    file: &dyn Fn() -> String,
    loc: &Location,
    attributes: &[crate::types::decl::Attribute],
) -> Read<T> {
    // Mirrors compiler/gentype/Annotation.ml:166-181 for Types.signature
    // attributes, whose locations are already materialized as Location values.
    let default = match config.everything {
        true => T::GenType,
        false => T::NoGenType,
    };
    Ok(if has_decl_attribute(tag_is_gentype_opaque, attributes)? {
        T::GenTypeOpaque
    } else if has_decl_attribute(|s| tag_is_gentype(s) || tag_is_gentype_as(s), attributes)? {
        if let Some(payload) = get_decl_attribute_payload(tag_is_gentype, attributes)?
            && !decl_attribute_payload_is_empty(payload)
        {
            notes.info(
                &file(),
                loc,
                "Warning genType",
                "Annotation payload is ignored",
            );
        }
        T::GenType
    } else {
        default
    })
}

pub fn update_config_for_decl_module(
    config: &crate::gentype::config::T,
    attributes: &[crate::types::decl::Attribute],
) -> Read<crate::gentype::config::T> {
    // Mirrors compiler/gentype/Annotation.ml:292-295 for Types.signature
    // attributes.
    Ok(if has_decl_attribute(tag_is_gentype, attributes)? {
        let mut config = config.clone();
        config.everything = true;
        config
    } else {
        config.clone()
    })
}

fn singleton_attribute(attribute: &Attribute) -> Attributes {
    Attributes::from_vec(vec![attribute.clone()])
}

#[cfg(test)]
mod tests {
    use crate::location::{Location, LocationOrigin, Position};

    fn source_handle(file: crate::intern::StrIdx) -> crate::types::DeclLoc {
        let pos = Position::new(file, 0, 0, 0);
        crate::types::DeclLoc::source(&Location {
            loc_start: pos,
            loc_end: pos,
            loc_ghost: false,
            origin: LocationOrigin::default(),
        })
        .expect("a coordinate-free location")
    }

    /// A declaration imported from another unit keeps a source handle, its
    /// file renamed into the context's file table: its notes name that file,
    /// whether or not the compiling unit's parse stores locations.
    #[test]
    fn decl_file_names_the_unit_a_declaration_came_from() {
        for store_locations in [true, false] {
            let parser = crate::parser::Parser::with_locations(
                "src/B.res".to_string(),
                "module M = A\n",
                store_locations,
            );
            let arena = parser.into_arena();
            let ctx = crate::types::context::TypeContext::new(std::sync::Arc::new(
                crate::context::IdGenerator::new(),
            ));
            let imported = ctx.intern_cmi_longident_name("src/A.res");
            assert_eq!(
                super::decl_file(&ctx, &arena, source_handle(imported)),
                "src/A.res"
            );
            let own = arena.source_file();
            assert_eq!(
                super::decl_file(&ctx, &arena, source_handle(own)),
                "src/B.res"
            );
        }
    }
}
