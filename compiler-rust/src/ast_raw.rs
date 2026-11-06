//! Port of `compiler/ml/ast_raw.ml`: `%raw`, `%ffi` and `%%raw`.

use crate::parse_arena::{LocIdx, Located, ParseArena};
use crate::parser::ast::{
    Attributes, Constant, Expression, ExpressionDesc, Extension, Payload, PexpTemplate, RawKind,
    RawSource, StringLoc, StructureItem, StructureItemDesc,
};

/// OCaml `Ast_raw.extension_name`: `"raw"` or `"ffi"`.
pub fn extension_name(kind: RawKind) -> &'static str {
    match kind {
        RawKind::Expression => "raw",
        RawKind::Function => "ffi",
    }
}

/// OCaml `Ast_raw.source_loc`.
pub fn source_loc(source: &RawSource) -> LocIdx {
    match source {
        RawSource::String(s) | RawSource::Template(s) => s.loc,
    }
}

fn source_text(source: &RawSource) -> &StringLoc {
    match source {
        RawSource::String(s) | RawSource::Template(s) => s,
    }
}

/// OCaml `Ast_raw.js_source`: the JavaScript source that a raw node stands
/// for.
pub fn js_source(arena: &ParseArena, source: &RawSource) -> String {
    match source {
        RawSource::String(s) => arena.get_string(s.txt).to_string(),
        RawSource::Template(s) => {
            crate::string_literal::decode_raw_template_source(arena.get_string(s.txt))
        }
    }
}

/// The location `Ast_raw.payload_loc` computes, as a full location: for a
/// template, the source ends before the closing backquote.
fn payload_location(arena: &ParseArena, source: &RawSource) -> Option<crate::location::Location> {
    match source {
        RawSource::String(_) => None,
        RawSource::Template(s) => {
            if arena.loc_ghost(s.loc) {
                return None;
            }
            let mut loc = arena.to_location(s.loc);
            loc.loc_end.cnum += 1;
            Some(loc)
        }
    }
}

/// OCaml `Ast_raw.payload_loc`: the location of the string or template
/// literal holding the source.
pub fn payload_loc(arena: &mut ParseArena, source: &RawSource) -> LocIdx {
    match payload_location(arena, source) {
        None => source_loc(source),
        Some(loc) => arena.mk_loc_from_positions(&loc.loc_start, &loc.loc_end),
    }
}

/// [`payload_loc`] through a shared arena.
pub fn payload_loc_shared(arena: &ParseArena, source: &RawSource) -> LocIdx {
    match payload_location(arena, source) {
        None => source_loc(source),
        Some(loc) => arena.push_typecheck_location(&loc, &|_| None),
    }
}

/// OCaml `Ast_raw.kind_of_name`: the kind of `%raw` or `%ffi`.
pub fn kind_of_name(name: &str) -> Option<RawKind> {
    match name {
        "raw" => Some(RawKind::Expression),
        "ffi" => Some(RawKind::Function),
        _ => None,
    }
}

/// OCaml `Ast_raw.of_payload`: the source in a parsed `%raw`, `%ffi` or
/// `%%raw` payload, if it is a plain string or template.
pub fn of_payload(arena: &mut ParseArena, payload: &Payload) -> Option<RawSource> {
    let Payload::PStr(items) = payload else {
        return None;
    };
    let [item] = items.as_slice() else {
        return None;
    };
    let StructureItemDesc::Pstr_eval(eval) = &item.pstr_desc else {
        return None;
    };
    let (expr_idx, eval_attrs) = &**eval;
    if !eval_attrs.is_empty() {
        return None;
    }
    let expr = arena.get_expr(*expr_idx);
    if !expr.pexp_attributes.is_empty() {
        return None;
    }
    let pexp_loc = expr.pexp_loc;
    match &expr.pexp_desc {
        ExpressionDesc::Pexp_constant(constant) => match *constant {
            Constant::String(payload) => {
                let source = payload.source(arena).to_string();
                Some(RawSource::String(Located {
                    txt: arena.intern(&source),
                    loc: pexp_loc,
                }))
            }
            _ => None,
        },
        ExpressionDesc::Pexp_template(template) => match template.source_segments.as_slice() {
            [source] if template.values.is_empty() => Some(RawSource::Template(source.clone())),
            _ => None,
        },
        _ => None,
    }
}

/// OCaml `Ast_raw.fits_double_quotes`: whether `source` can be written
/// between double quotes as it is, i.e. it has no unescaped double quote.
pub fn fits_double_quotes(source: &str) -> bool {
    let bytes = source.as_bytes();
    let mut index = 0;
    while index < bytes.len() {
        match bytes[index] {
            b'"' => return false,
            b'\\' => {
                if index + 1 >= bytes.len() {
                    return false;
                }
                index += 2;
            }
            _ => index += 1,
        }
    }
    true
}

/// OCaml `Ast_raw.to_extension`: the extension as parsed, for passes that
/// treat raw JavaScript like the extension it is written as. Built through a
/// shared arena, so printers can call it.
pub fn to_extension(
    arena: &ParseArena,
    name: &str,
    name_loc: LocIdx,
    source: &RawSource,
) -> Extension {
    let loc = payload_loc_shared(arena, source);
    let expression = |desc| Expression {
        pexp_desc: desc,
        pexp_loc: loc,
        pexp_attributes: Attributes::new(),
    };
    let template = |segment: StringLoc| {
        ExpressionDesc::Pexp_template(Box::new(PexpTemplate {
            source_segments: vec![segment],
            values: vec![],
        }))
    };
    let desc = match source {
        RawSource::String(s) => {
            let txt = arena.get_string(s.txt);
            let payload = if fits_double_quotes(txt) {
                crate::string_literal::string_from_source(txt)
            } else {
                None
            };
            match payload {
                Some(payload) => ExpressionDesc::Pexp_constant(Constant::String(
                    arena.push_shared_string_literal(&payload),
                )),
                None => template(Located {
                    txt: arena
                        .push_shared_string(crate::string_literal::encode_raw_template_source(txt)),
                    loc: s.loc,
                }),
            }
        }
        RawSource::Template(s) => template(s.clone()),
    };
    let expr = arena.push_shared_expr(expression(desc));
    (
        Located {
            txt: arena.push_shared_string(name.to_string()),
            loc: name_loc,
        },
        Payload::PStr(Box::new(vec![StructureItem {
            pstr_desc: StructureItemDesc::Pstr_eval(Box::new((expr, Attributes::new()))),
            pstr_loc: loc,
        }])),
    )
}

/// The text of a raw source as written.
pub fn source_as_written<'a>(arena: &'a ParseArena, source: &RawSource) -> &'a str {
    arena.get_string(source_text(source).txt)
}
