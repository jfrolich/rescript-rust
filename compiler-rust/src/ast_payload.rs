//! Port of the string-literal helpers of `compiler/ml/ast_payload.ml`.

use crate::parse_arena::{LocIdx, ParseArena};
use crate::parser::ast::{Constant, Expression, ExpressionDesc, Payload, StructureItemDesc};

/// OCaml `Ast_payload.json_literal_outside_external_message`.
pub const JSON_LITERAL_OUTSIDE_EXTERNAL_MESSAGE: &str =
    "A `json` literal can only be used in an external attribute such as `@as`";

/// An error raised by these helpers (OCaml `Location.raise_errorf ~loc`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PayloadError {
    pub loc: LocIdx,
    pub message: &'static str,
}

/// OCaml `Ast_payload.reject_json_literal_payload`: the location of a payload
/// that is a single `json` literal, which callers must reject.
pub fn reject_json_literal_payload(arena: &ParseArena, payload: &Payload) -> Result<(), PayloadError> {
    if let Payload::PStr(items) = payload
        && let [item] = items.as_slice()
        && let StructureItemDesc::Pstr_eval(eval) = &*item.pstr_desc
    {
        let expression = arena.get_expr(eval.0);
        if let ExpressionDesc::Pexp_constant(constant) = &*expression.pexp_desc
            && let Constant::Json(_) = &**constant
        {
            return Err(PayloadError {
                loc: expression.pexp_loc,
                message: JSON_LITERAL_OUTSIDE_EXTERNAL_MESSAGE,
            });
        }
    }
    Ok(())
}

/// OCaml `Ast_payload.semantic_string_of_expression`: the decoded value of an
/// ordinary string or a non-interpolated backquoted string.
pub fn semantic_string_of_expression(
    arena: &ParseArena,
    expression: &Expression,
) -> Result<Option<String>, PayloadError> {
    match &*expression.pexp_desc {
        ExpressionDesc::Pexp_constant(constant) => match &**constant {
            Constant::String(payload) => Ok(Some(payload.semantic().to_string())),
            _ => Ok(None),
        },
        ExpressionDesc::Pexp_template(template)
            if template.source_segments.len() == 1 && template.values.is_empty() =>
        {
            let source = arena.get_string(template.source_segments[0].txt);
            match crate::string_literal::decode_js_template_escapes(source) {
                Some(semantic) => Ok(Some(semantic)),
                None => Err(PayloadError {
                    loc: expression.pexp_loc,
                    message: "Invalid string escape sequence",
                }),
            }
        }
        _ => Ok(None),
    }
}

/// OCaml `Ast_payload.semantic_string_of_payload`.
pub fn semantic_string_of_payload(arena: &ParseArena, payload: &Payload) -> Result<Option<String>, PayloadError> {
    if let Payload::PStr(items) = payload
        && let [item] = items.as_slice()
        && let StructureItemDesc::Pstr_eval(eval) = &*item.pstr_desc
    {
        return semantic_string_of_expression(arena, arena.get_expr(eval.0));
    }
    Ok(None)
}
