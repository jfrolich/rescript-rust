//! Port of the string-literal helpers of `compiler/ml/ast_payload.ml`.

use crate::parse_arena::{ExprIdx, LocIdx, ParseArena};
use crate::parser::ast::{Constant, Expression, ExpressionDesc, Payload, StructureItemDesc};

/// OCaml `Ast_payload.unwrap_braces`: the expression under any explicit
/// braces, each read as the compiler reads it (`ParseArena::expanded`; the
/// tree as written before the built-in rewrites have run).
///
/// Cost: one read and one bit test per brace level.
pub fn unwrap_braces<'a>(arena: &'a ParseArena, expression: &'a Expression) -> &'a Expression {
    let mut expression = expression;
    while let ExpressionDesc::Pexp_braces(braces) = &expression.pexp_desc {
        expression = arena.get_expr(arena.expanded(braces.expr));
    }
    expression
}

/// The expression of a single-expression payload `PStr [Pstr_eval (e, _)]`,
/// braces kept.
pub fn payload_expression(payload: &Payload) -> Option<ExprIdx> {
    if let Payload::PStr(items) = payload
        && let [item] = items.as_slice()
        && let StructureItemDesc::Pstr_eval(eval) = &item.pstr_desc
    {
        return Some(eval.0);
    }
    None
}

/// The expression of a single-expression payload `PStr [Pstr_eval (e, _)]`,
/// under any explicit braces (OCaml `Ast_payload.unwrap_payload_expression`).
pub fn unwrapped_payload_expression<'a>(
    arena: &'a ParseArena,
    payload: &Payload,
) -> Option<&'a Expression> {
    payload_expression(payload).map(|e| unwrap_braces(arena, arena.get_expr(e)))
}

/// An error raised by these helpers (OCaml `Location.raise_errorf ~loc`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PayloadError {
    /// Source span of the invalid payload.
    pub loc: LocIdx,
    /// Diagnostic explaining why the payload was rejected.
    pub message: &'static str,
}

/// OCaml `Ast_payload.semantic_string_of_expression`: the decoded value of an
/// ordinary string or a non-interpolated backquoted string.
pub fn semantic_string_of_expression(
    arena: &ParseArena,
    expression: &Expression,
) -> Result<Option<String>, PayloadError> {
    let expression = unwrap_braces(arena, expression);
    match &expression.pexp_desc {
        ExpressionDesc::Pexp_constant(Constant::String(payload)) => {
            Ok(Some(payload.semantic(arena).to_string()))
        }
        ExpressionDesc::Pexp_template(_) => template_semantic(arena, expression),
        _ => Ok(None),
    }
}

/// The decoded value of a non-interpolated backquoted string; `Ok(None)`
/// for any other template.
fn template_semantic(
    arena: &ParseArena,
    expression: &Expression,
) -> Result<Option<String>, PayloadError> {
    let ExpressionDesc::Pexp_template(template) = &expression.pexp_desc else {
        return Ok(None);
    };
    if template.source_segments.len() != 1 || !template.values.is_empty() {
        return Ok(None);
    }
    let source = arena.get_string(template.source_segments[0].txt);
    match crate::string_literal::decode_js_template_escapes(source) {
        Some(semantic) => Ok(Some(semantic)),
        None => Err(PayloadError {
            loc: expression.pexp_loc,
            message: "Invalid string escape sequence",
        }),
    }
}

/// OCaml `Ast_payload.semantic_string_of_payload`.
pub fn semantic_string_of_payload(
    arena: &ParseArena,
    payload: &Payload,
) -> Result<Option<String>, PayloadError> {
    match payload_expression(payload) {
        Some(e) => semantic_string_of_expression(arena, arena.get_expr(e)),
        None => Ok(None),
    }
}

/// OCaml `Ast_payload.string_literal_of_expression`: the string literal an
/// expression denotes, keeping its source spelling. A non-interpolated
/// backquoted string gets canonical quoted spelling.
pub fn string_literal_of_expression(
    arena: &ParseArena,
    expression: &Expression,
) -> Result<Option<crate::string_literal::StringLiteral>, PayloadError> {
    let expression = unwrap_braces(arena, expression);
    match &expression.pexp_desc {
        ExpressionDesc::Pexp_constant(Constant::String(payload)) => {
            Ok(Some(payload.to_literal(arena)))
        }
        ExpressionDesc::Pexp_template(_) => Ok(template_semantic(arena, expression)?
            .map(|semantic| crate::string_literal::string_from_semantic(&semantic))),
        _ => Ok(None),
    }
}

/// OCaml `Ast_payload.string_literal_of_payload`.
pub fn string_literal_of_payload(
    arena: &ParseArena,
    payload: &Payload,
) -> Result<Option<crate::string_literal::StringLiteral>, PayloadError> {
    match unwrapped_payload_expression(arena, payload) {
        Some(expression) => string_literal_of_expression(arena, expression),
        None => Ok(None),
    }
}

fn single_constant<'a>(arena: &'a ParseArena, payload: &Payload) -> Option<&'a Constant> {
    match &unwrapped_payload_expression(arena, payload)?.pexp_desc {
        ExpressionDesc::Pexp_constant(constant) => Some(constant),
        _ => None,
    }
}

/// OCaml `Ast_payload.single_int_source`: the source of an integer payload
/// without the bigint suffix.
pub fn single_int_source(arena: &ParseArena, payload: &Payload) -> Option<String> {
    match single_constant(arena, payload)? {
        Constant::Integer(name, suffix) if *suffix != Some('n') => {
            Some(arena.get_string(*name).to_string())
        }
        _ => None,
    }
}

/// OCaml `Ast_payload.is_single_bool`.
fn is_single_bool(arena: &ParseArena, payload: &Payload) -> Option<bool> {
    match &unwrapped_payload_expression(arena, payload)?.pexp_desc {
        ExpressionDesc::Pexp_construct(lid, _) => match arena.get_longident(lid.txt) {
            crate::parser::longident::Longident::Lident(name) => match arena.get_string(*name) {
                "true" => Some(true),
                "false" => Some(false),
                _ => None,
            },
            _ => None,
        },
        _ => None,
    }
}

/// OCaml `Ast_payload.is_single_ident`, as the name of a simple identifier
/// (`Some(None)` for any other identifier path).
fn is_single_ident<'a>(arena: &'a ParseArena, payload: &Payload) -> Option<Option<&'a str>> {
    match &unwrapped_payload_expression(arena, payload)?.pexp_desc {
        ExpressionDesc::Pexp_ident(lid) => match arena.get_longident(lid.txt) {
            crate::parser::longident::Longident::Lident(name) => {
                Some(Some(arena.get_string(*name)))
            }
            _ => Some(None),
        },
        _ => None,
    }
}

/// `string_literal_of_payload` with the literal stored in `arena`. A quoted
/// string constant keeps its interned spellings; a backquoted string gets
/// canonical quoted spelling, interned here.
pub fn string_const_of_payload(
    arena: &mut ParseArena,
    payload: &Payload,
) -> Result<Option<crate::parser::ast::StringConst>, PayloadError> {
    let Some(expression) = unwrapped_payload_expression(arena, payload) else {
        return Ok(None);
    };
    let expression = unwrap_braces(arena, expression);
    match &expression.pexp_desc {
        ExpressionDesc::Pexp_constant(Constant::String(payload)) => Ok(Some(*payload)),
        ExpressionDesc::Pexp_template(_) => match template_semantic(arena, expression)? {
            Some(semantic) => {
                let literal = crate::string_literal::string_from_semantic(&semantic);
                Ok(Some(arena.push_string_literal(&literal)))
            }
            None => Ok(None),
        },
        _ => Ok(None),
    }
}

/// OCaml `Ast_payload.constructor_tag_of_payload`: the literal denoted by a
/// valid variant-constructor `@as` payload. Number tags keep the payload
/// constant's interned spelling.
pub fn constructor_tag_of_payload(
    arena: &mut ParseArena,
    payload: &Payload,
) -> Result<Option<crate::parser::ast::ConstructorTag>, PayloadError> {
    use crate::parser::ast::ConstructorTag;
    if let Some(s) = string_const_of_payload(arena, payload)? {
        return Ok(Some(ConstructorTag::Pct_string(s)));
    }
    match single_constant(arena, payload) {
        Some(Constant::Integer(i, suffix)) if *suffix != Some('n') => {
            return Ok(Some(ConstructorTag::Pct_int(*i)));
        }
        Some(Constant::Float(f, _)) => return Ok(Some(ConstructorTag::Pct_float(*f))),
        Some(Constant::Integer(i, Some('n'))) => {
            return Ok(Some(ConstructorTag::Pct_bigint(*i)));
        }
        _ => {}
    }
    if let Some(b) = is_single_bool(arena, payload) {
        return Ok(Some(ConstructorTag::Pct_bool(b)));
    }
    Ok(match is_single_ident(arena, payload) {
        Some(Some("null")) => Some(ConstructorTag::Pct_null),
        Some(Some("undefined")) => Some(ConstructorTag::Pct_undefined),
        Some(_) | None => None,
    })
}
