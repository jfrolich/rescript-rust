//! Attribute payloads as the analyses read them
//! (analysis/reanalyze/src/annotation.ml).

use crate::parse_arena::ParseArena;
use crate::parser::ast::{Attribute, Constant, Expression, ExpressionDesc, Payload};
use crate::parser::longident::Longident;

/// `Annotation.attribute_payload`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AttributePayload {
    /// A boolean.
    Bool(bool),
    /// A constructor, as its dotted name.
    Construct(String),
    /// A number literal, as written.
    Float(String),
    /// An identifier, as its dotted name.
    Ident(String),
    /// An integer literal, as written.
    Int(String),
    /// A string.
    String(String),
    /// A tuple, an array or a list of payloads.
    Tuple(Vec<AttributePayload>),
    /// Any other payload, or none.
    Unrecognized,
}

fn longident_string(arena: &ParseArena, lid: &Longident) -> String {
    lid.flatten_idx()
        .into_iter()
        .map(|s| arena.get_string(s))
        .collect::<Vec<_>>()
        .join(".")
}

/// The payloads of `exprs`, which `Annotation.from_expr` reads last first.
fn tuple_payload<'a>(
    arena: &'a ParseArena,
    exprs: impl DoubleEndedIterator<Item = &'a Expression>,
) -> AttributePayload {
    let mut payloads: Vec<AttributePayload> = exprs
        .rev()
        .filter_map(|expr| from_expr(arena, expr))
        .collect();
    payloads.reverse();
    AttributePayload::Tuple(payloads)
}

fn from_expr(arena: &ParseArena, expr: &Expression) -> Option<AttributePayload> {
    // A template with an invalid escape raises in OCaml; only a PPX makes one.
    if let Ok(Some(s)) = crate::ast_payload::semantic_string_of_expression(arena, expr) {
        return Some(AttributePayload::String(s));
    }
    match &crate::ast_payload::unwrap_braces(arena, expr).pexp_desc {
        ExpressionDesc::Pexp_constant(Constant::Integer(n, _)) => {
            Some(AttributePayload::Int(arena.get_string(*n).to_string()))
        }
        ExpressionDesc::Pexp_constant(Constant::Float(s, _)) => {
            Some(AttributePayload::Float(arena.get_string(*s).to_string()))
        }
        ExpressionDesc::Pexp_construct(lid, args) => {
            let lid = arena.get_longident(lid.txt);
            let args = arena.expr_list(args.txt);
            if let Longident::Lident(name) = lid {
                match (arena.get_string(*name), args) {
                    ("true", _) => return Some(AttributePayload::Bool(true)),
                    ("false", _) => return Some(AttributePayload::Bool(false)),
                    ("[]", []) => return None,
                    ("::", [head, tail]) => {
                        return Some(tuple_payload(
                            arena,
                            [arena.get_expr(*head), arena.get_expr(*tail)].into_iter(),
                        ));
                    }
                    _ => {}
                }
            }
            Some(AttributePayload::Construct(longident_string(arena, lid)))
        }
        ExpressionDesc::Pexp_tuple(exprs) | ExpressionDesc::Pexp_array(exprs) => {
            Some(tuple_payload(
                arena,
                arena.expr_list(*exprs).iter().map(|e| arena.get_expr(*e)),
            ))
        }
        ExpressionDesc::Pexp_ident(lid) => Some(AttributePayload::Ident(longident_string(
            arena,
            arena.get_longident(lid.txt),
        ))),
        _ => None,
    }
}

/// `Annotation.get_attribute_payload`: the payload of the first of
/// `attributes` whose name `check_text` accepts.
pub fn get_attribute_payload<'a>(
    arena: &ParseArena,
    check_text: impl Fn(&str) -> bool,
    attributes: impl IntoIterator<Item = &'a Attribute>,
) -> Option<AttributePayload> {
    for (txt, payload) in attributes {
        if check_text(arena.get_string(txt.txt)) {
            return match payload {
                Payload::PStr(items) => match items.first() {
                    None => Some(AttributePayload::Unrecognized),
                    Some(item) => match &item.pstr_desc {
                        crate::parser::ast::StructureItemDesc::Pstr_eval(eval) => {
                            from_expr(arena, arena.get_expr(arena.expanded(eval.0)))
                        }
                        _ => Some(AttributePayload::Unrecognized),
                    },
                },
                Payload::PPat(_) | Payload::PSig(_) | Payload::PTyp(_) => {
                    Some(AttributePayload::Unrecognized)
                }
            };
        }
    }
    None
}

/// `Annotation.has_attribute`.
pub fn has_attribute<'a>(
    arena: &ParseArena,
    check_text: impl Fn(&str) -> bool,
    attributes: impl IntoIterator<Item = &'a Attribute>,
) -> bool {
    get_attribute_payload(arena, check_text, attributes).is_some()
}

/// `Annotation.tag_is_one_of_the_gentype_annotations`.
pub fn tag_is_one_of_the_gentype_annotations(s: &str) -> bool {
    matches!(
        s,
        "genType"
            | "gentype"
            | "genType.import"
            | "gentype.import"
            | "genType.opaque"
            | "gentype.opaque"
    )
}

/// `Annotation.is_ocaml_suppress_dead_warning`.
pub fn is_ocaml_suppress_dead_warning<'a>(
    arena: &ParseArena,
    attributes: impl IntoIterator<Item = &'a Attribute>,
) -> bool {
    match get_attribute_payload(arena, |x| x == "warning", attributes) {
        Some(AttributePayload::String(s)) => {
            s.contains("-32") || s.contains("-unused-value-declaration")
        }
        _ => false,
    }
}
