//! Port of `compiler/ml/ast_todo.ml`: `%todo`.

use crate::parse_arena::{ExprIdx, LocIdx, Located, ParseArena};
use crate::parser::ast::{
    Constant, ExpressionDesc, Extension, Payload, StructureItem, StructureItemDesc,
};

/// OCaml `Ast_todo.name`.
pub const NAME: &str = "todo";

/// OCaml `Ast_todo.is_message`: a string literal or a template without
/// interpolations, without attributes.
fn is_message(arena: &ParseArena, message: ExprIdx) -> bool {
    let expr = arena.get_expr(message);
    if !expr.pexp_attributes.is_empty() {
        return false;
    }
    match &expr.pexp_desc {
        ExpressionDesc::Pexp_constant(Constant::String(_)) => true,
        ExpressionDesc::Pexp_template(template) => {
            template.source_segments.len() == 1 && template.values.is_empty()
        }
        _ => false,
    }
}

/// OCaml `Ast_todo.of_payload`: the message of a parsed `%todo` payload,
/// `Some(None)` for no payload, `Some(Some(message))` for a string literal or
/// a template without interpolations, `None` for any other payload, which
/// stays an extension.
pub fn of_payload(arena: &ParseArena, payload: &Payload) -> Option<Option<ExprIdx>> {
    let Payload::PStr(items) = payload else {
        return None;
    };
    match items.as_slice() {
        [] => Some(None),
        [item] => match &item.pstr_desc {
            StructureItemDesc::Pstr_eval(eval) => {
                let (message, attrs) = &**eval;
                if attrs.is_empty() && is_message(arena, *message) {
                    Some(Some(*message))
                } else {
                    None
                }
            }
            _ => None,
        },
        _ => None,
    }
}

/// OCaml `Ast_todo.to_extension`: the extension as parsed. Built through a
/// shared arena, so printers can call it.
pub fn to_extension(arena: &ParseArena, name_loc: LocIdx, message: Option<ExprIdx>) -> Extension {
    let payload = match message {
        None => vec![],
        // `Ast_helper.Str.eval ~loc:message.pexp_loc message`.
        Some(message) => vec![StructureItem {
            pstr_desc: StructureItemDesc::Pstr_eval(Box::new((
                message,
                crate::parser::ast::Attributes::new(),
            ))),
            pstr_loc: arena.get_expr(message).pexp_loc,
        }],
    };
    (
        Located {
            txt: arena.push_shared_string(NAME.to_string()),
            loc: name_loc,
        },
        Payload::PStr(Box::new(payload)),
    )
}
