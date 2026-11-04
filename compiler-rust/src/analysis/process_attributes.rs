//! A port of analysis/src/process_attributes.ml.
//!
//! OCaml reads `Parsetree.attributes` everywhere. Rust has two forms: the
//! parse tree's (resolved through its arena) and the portable copies type
//! declarations carry (`types::decl::Attribute`); [`Attrs`] reads either.

use super::shared_types::{Declared, Loc, Located, ModulePath, ModulePathList};
use crate::ast_payload::payload_expression;
use crate::parse_arena::{ExprIdx, ParseArena};
use crate::parser::ast::{Attribute, ExpressionDesc, Payload};
use crate::parser::longident::Longident;
use crate::types::decl;

/// Attributes in either of their Rust forms.
#[derive(Clone, Copy)]
pub enum Attrs<'a> {
    Parsed(&'a [Attribute], &'a ParseArena),
    Decl(&'a [decl::Attribute]),
}

/// `Ast_payload.semantic_string_of_expression`. OCaml raises on an invalid
/// escape; the compiler has already rejected such a file.
fn string_constant(arena: &ParseArena, e: ExprIdx) -> Option<String> {
    crate::ast_payload::semantic_string_of_expression(arena, arena.get_expr(e))
        .ok()
        .flatten()
}

/// `Utils.flatten_long_ident` without its options.
pub fn flatten_long_ident(arena: &ParseArena, lid: &Longident) -> ModulePathList {
    match lid {
        Longident::Lident(txt) => vec![arena.get_string(*txt).to_string()],
        Longident::Ldot(lid, txt) => {
            let mut path = flatten_long_ident(arena, lid);
            path.push(arena.get_string(*txt).to_string());
            path
        }
        Longident::Lapply(..) => Vec::new(),
    }
}

fn is_doc_name(name: &str) -> bool {
    matches!(name, "ocaml.doc" | "ocaml.text" | "ns.doc" | "res.doc")
}

/// `find_doc_attribute`.
pub fn find_doc_attribute(attrs: Attrs<'_>) -> Option<String> {
    match attrs {
        Attrs::Parsed(attrs, arena) => attrs.iter().find_map(|(name, payload)| {
            if !is_doc_name(arena.get_string(name.txt)) {
                return None;
            }
            crate::ast_payload::semantic_string_of_payload(arena, payload)
                .ok()
                .flatten()
        }),
        Attrs::Decl(attrs) => attrs.iter().find_map(|attr| {
            if !is_doc_name(&attr.attr_name.txt) {
                return None;
            }
            match &attr.attr_payload {
                decl::AttributePayload::Str(s) => Some(s.clone()),
                _ => None,
            }
        }),
    }
}

/// `find_deprecated_attribute`.
pub fn find_deprecated_attribute(attrs: Attrs<'_>) -> Option<String> {
    match attrs {
        Attrs::Parsed(attrs, arena) => {
            let (_, payload) = attrs
                .iter()
                .find(|attr| is_parsed_deprecated(arena, attr))?;
            parsed_deprecated_reason(arena, payload)
        }
        Attrs::Decl(attrs) => decl_deprecated_reason(attrs.iter().find(|a| is_decl_deprecated(a))?),
    }
}

fn is_parsed_deprecated(arena: &ParseArena, (name, _): &Attribute) -> bool {
    arena.get_string(name.txt) == "deprecated"
}

fn is_decl_deprecated(attr: &decl::Attribute) -> bool {
    attr.attr_name.txt == "deprecated"
}

/// The reason of a found `@deprecated` attribute.
fn parsed_deprecated_reason(arena: &ParseArena, payload: &Payload) -> Option<String> {
    let Some(e) = payload_expression(payload) else {
        return Some(String::new());
    };
    if let Some(msg) = string_constant(arena, e) {
        return Some(msg);
    }
    match &arena.get_expr(e).pexp_desc {
        ExpressionDesc::Pexp_record(record) => {
            let mut reason = String::new();
            for field in &record.0 {
                if let Longident::Lident(txt) = arena.get_longident(field.lid.txt)
                    && arena.get_string(*txt) == "reason"
                    && let Some(msg) = string_constant(arena, field.expr)
                {
                    reason = msg;
                }
            }
            Some(reason)
        }
        _ => None,
    }
}

/// The reason of a found `@deprecated` declaration attribute.
fn decl_deprecated_reason(attr: &decl::Attribute) -> Option<String> {
    match &attr.attr_payload {
        decl::AttributePayload::Str(msg) => Some(msg.clone()),
        decl::AttributePayload::Deprecated { reason, .. } => Some(reason.clone()),
        decl::AttributePayload::Empty => Some(String::new()),
        _ => None,
    }
}

/// `find_editor_complete_from_attribute`.
pub fn find_editor_complete_from_attribute(attrs: Attrs<'_>) -> Vec<ModulePathList> {
    let mut module_paths: Vec<ModulePathList> = Vec::new();
    match attrs {
        Attrs::Parsed(attrs, arena) => {
            for (name, payload) in attrs {
                if arena.get_string(name.txt) != "editor.completeFrom" {
                    continue;
                }
                let Some(e) = payload_expression(payload) else {
                    continue;
                };
                let items: Vec<ExprIdx> = match &arena.get_expr(e).pexp_desc {
                    ExpressionDesc::Pexp_array(items) => arena.expr_list(*items).to_vec(),
                    _ => vec![e],
                };
                let mut from_array: Vec<ModulePathList> = items
                    .iter()
                    .filter_map(|item| match &arena.get_expr(*item).pexp_desc {
                        ExpressionDesc::Pexp_construct(lid, args) if args.txt.is_empty() => {
                            Some(flatten_long_ident(arena, arena.get_longident(lid.txt)))
                        }
                        _ => None,
                    })
                    .collect();
                from_array.append(&mut module_paths);
                module_paths = from_array;
            }
        }
        Attrs::Decl(attrs) => {
            for attr in attrs {
                if attr.attr_name.txt != "editor.completeFrom" {
                    continue;
                }
                if let decl::AttributePayload::Ident(path) = &attr.attr_payload {
                    let mut from_array = vec![path.split('.').map(str::to_string).collect()];
                    from_array.append(&mut module_paths);
                    module_paths = from_array;
                }
            }
        }
    }
    module_paths
}

/// `find_deprecated_attribute (List.rev attributes)`.
fn reversed_deprecated(attrs: Attrs<'_>) -> Option<String> {
    match attrs {
        Attrs::Parsed(attrs, arena) => {
            let (_, payload) = attrs
                .iter()
                .rev()
                .find(|attr| is_parsed_deprecated(arena, attr))?;
            parsed_deprecated_reason(arena, payload)
        }
        Attrs::Decl(attrs) => {
            decl_deprecated_reason(attrs.iter().rev().find(|a| is_decl_deprecated(a))?)
        }
    }
}

/// `new_declared`.
pub fn new_declared<T>(
    item: T,
    extent: Loc,
    name: Located<String>,
    stamp: i32,
    module_path: ModulePath,
    is_exported: bool,
    attributes: Attrs<'_>,
) -> Declared<T> {
    Declared {
        name,
        stamp,
        extent_loc: extent,
        is_exported,
        module_path,
        deprecated: reversed_deprecated(attributes),
        docstring: find_doc_attribute(attributes).into_iter().collect(),
        item,
    }
}
