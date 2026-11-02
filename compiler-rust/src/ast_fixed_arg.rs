//! Port of `compiler/ml/ast_fixed_arg.ml`: fixed external arguments, written
//! `@as(value) _`.

use crate::parse_arena::Located;
use crate::parse_arena::{LocIdx, ParseArena};
use crate::parser::ast::{
    Attribute, Attributes, Constant, CoreType, CoreTypeDesc, Expression, ExpressionDesc, FixedArg,
    FixedValue, Payload, PexpTaggedTemplate, PexpTemplate, StructureItem, StructureItemDesc,
    TypeArg,
};

/// OCaml `Ast_fixed_arg.of_payload`: the fixed value denoted by an `@as`
/// payload (an integer, a string, a non-interpolated backquoted string, or a
/// `json` literal) and the payload's location.
pub fn of_payload(arena: &mut ParseArena, payload: &Payload) -> Option<(FixedValue, LocIdx)> {
    let Payload::PStr(items) = payload else {
        return None;
    };
    // A payload with attributes stays an attribute, which keeps them.
    let [item] = items.as_slice() else {
        return None;
    };
    let StructureItemDesc::Pstr_eval(eval) = &*item.pstr_desc else {
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
    let value = match &*expr.pexp_desc {
        ExpressionDesc::Pexp_constant(constant) => match &**constant {
            Constant::Integer(source, None) => {
                let source = source.clone();
                FixedValue::Int(Located {
                    txt: arena.intern(&source),
                    loc: pexp_loc,
                })
            }
            Constant::String(payload) => FixedValue::String(payload.clone()),
            _ => return None,
        },
        ExpressionDesc::Pexp_template(template) => match template.source_segments.as_slice() {
            [source] if template.values.is_empty() => FixedValue::Template(*source),
            _ => return None,
        },
        ExpressionDesc::Pexp_tagged_template(template) => {
            let tag = arena.get_expr(template.tag);
            let is_json = tag.pexp_attributes.is_empty()
                && matches!(&*tag.pexp_desc,
                    ExpressionDesc::Pexp_ident(lid) if arena.is_lident(lid.txt, "json"));
            match template.raw_sources.as_slice() {
                [source] if is_json && template.values.is_empty() => FixedValue::Json(*source),
                _ => return None,
            }
        }
        _ => return None,
    };
    Some((value, item.pstr_loc))
}

/// OCaml `Ast_fixed_arg.to_expression`: the payload expression that spells
/// `value`.
pub fn to_expression(arena: &mut ParseArena, value: &FixedValue, loc: LocIdx) -> Expression {
    let constant = |desc, loc| Expression {
        pexp_desc: Box::new(desc),
        pexp_loc: loc,
        pexp_attributes: Attributes::new(),
    };
    match value {
        FixedValue::Int(source) => constant(
            ExpressionDesc::Pexp_constant(Box::new(Constant::Integer(
                arena.get_string(source.txt).to_string().into(),
                None,
            ))),
            source.loc,
        ),
        FixedValue::String(payload) => constant(
            ExpressionDesc::Pexp_constant(Box::new(Constant::String(payload.clone()))),
            loc,
        ),
        FixedValue::Template(source) => constant(
            ExpressionDesc::Pexp_template(Box::new(PexpTemplate {
                source_segments: vec![*source],
                values: vec![],
            })),
            loc,
        ),
        FixedValue::Json(source) => {
            let lid = arena.push_lident_static("json");
            let tag = arena.push_expr(constant(
                ExpressionDesc::Pexp_ident(Located { txt: lid, loc }),
                loc,
            ));
            constant(
                ExpressionDesc::Pexp_tagged_template(Box::new(PexpTaggedTemplate {
                    tag,
                    raw_sources: vec![*source],
                    values: vec![],
                })),
                loc,
            )
        }
    }
}

/// OCaml `Ast_fixed_arg.to_attribute`: the `@as` attribute that spells
/// `value` (located at `value_loc`), with its name located at `loc`.
pub fn to_attribute(
    arena: &mut ParseArena,
    value: &FixedValue,
    value_loc: LocIdx,
    loc: LocIdx,
) -> Attribute {
    let expr = to_expression(arena, value, value_loc);
    let expr = arena.push_expr(expr);
    let name = arena.intern("as");
    (
        Located { txt: name, loc },
        Payload::PStr(Box::new(vec![StructureItem {
            pstr_desc: Box::new(StructureItemDesc::Pstr_eval(Box::new((
                expr,
                Attributes::new(),
            )))),
            pstr_loc: value_loc,
        }])),
    )
}

/// OCaml `Ast_fixed_arg.underscore_loc`: the location of the `_` that ends a
/// fixed argument located at `loc`.
pub fn underscore_loc(arena: &mut ParseArena, loc: LocIdx) -> LocIdx {
    if arena.loc_ghost(loc) {
        return loc;
    }
    let end = *arena.loc_end(loc);
    let end_idx = arena.loc_end_idx(loc);
    let start = arena.push_position(crate::location::Position {
        cnum: end.cnum - 1,
        ..end
    });
    arena.mk_loc(start, end_idx)
}

/// OCaml `Ast_fixed_arg.as_name_loc`: the location of the `@as` that starts a
/// fixed argument located at `loc`.
pub fn as_name_loc(arena: &mut ParseArena, loc: LocIdx) -> LocIdx {
    if arena.loc_ghost(loc) {
        return loc;
    }
    let start = *arena.loc_start(loc);
    let start_idx = arena.loc_start_idx(loc);
    let end = arena.push_position(crate::location::Position {
        cnum: start.cnum + 3,
        ..start
    });
    arena.mk_loc(start_idx, end)
}

/// OCaml `loc = Location.none`, compared structurally.
fn is_none_location(arena: &ParseArena, loc: LocIdx) -> bool {
    let none = LocIdx::none();
    loc.is_none()
        || (arena.loc_start(loc) == arena.loc_start(none)
            && arena.loc_end(loc) == arena.loc_end(none)
            && arena.loc_ghost(loc) == arena.loc_ghost(none))
}

/// OCaml `Ast_fixed_arg.normalize_arg`: `@as(value) _` on a direct argument
/// becomes a fixed argument. An argument with an invalid payload stays as
/// written, so external processing reports it as before. So do the rare
/// arguments that a fixed argument could not print back as written: a `_`
/// with other attributes too, and a braced payload such as `@as({1})`.
///
/// The argument keeps its `_` as `typ`, now without the attribute and located
/// at the underscore (`underscore_loc`).
fn normalize_arg(arena: &mut ParseArena, arg: &mut TypeArg) {
    if arg.fixed.is_some() {
        return;
    }
    let typ = arena.get_core_type(arg.typ);
    if !matches!(&*typ.ptyp_desc, CoreTypeDesc::Ptyp_any) {
        return;
    }
    let [(name, payload)] = typ.ptyp_attributes.as_slice() else {
        return;
    };
    if arena.get_string(name.txt) != "as" {
        return;
    }
    let as_loc = name.loc;
    let ptyp_loc = typ.ptyp_loc;
    let payload = payload.clone();
    let Some((value, value_loc)) = of_payload(arena, &payload) else {
        return;
    };
    let loc = if is_none_location(arena, as_loc) {
        ptyp_loc
    } else {
        let start = arena.loc_start_idx(as_loc);
        let end = arena.loc_end_idx(ptyp_loc);
        let ghost = arena.loc_ghost(as_loc);
        arena.push_loc(start, end, ghost)
    };
    let underscore = underscore_loc(arena, loc);
    let typ = arena.get_core_type_mut(arg.typ);
    typ.ptyp_attributes = Attributes::new();
    typ.ptyp_loc = underscore;
    arg.fixed = Some(Box::new(FixedArg {
        value,
        value_loc,
        loc,
    }));
}

/// OCaml `Ast_fixed_arg.normalize_external_type`: turn the `@as(value) _`
/// arguments of an external's type into fixed arguments.
pub fn normalize_external_type(arena: &mut ParseArena, typ: &mut CoreType) {
    let CoreTypeDesc::Ptyp_arrow(inner) = &mut *typ.ptyp_desc else {
        return;
    };
    let first = &mut inner.0;
    let first_typ = first.typ;
    if let Some(mut args) = arena.take_nary_arrow_args(first_typ) {
        for arg in args.iter_mut() {
            normalize_arg(arena, arg);
        }
        **first = args[0].clone();
        arena.restore_nary_arrow_args(first_typ, args);
    } else {
        normalize_arg(arena, first);
    }
}
