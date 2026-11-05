//! Port of the declaration builders of OCaml `Ast_helper.Type`
//! (`compiler/ml/ast_helper.ml`): `constructor` and `field` take a valid
//! `@as` out of the attributes into `pcd_runtime_tag` / `pld_runtime_name`,
//! and `constructor_attributes` / `field_attributes` put it back for
//! printers and mappers.

use crate::ast_payload::{self, PayloadError};
use crate::binary_ast::ppx::PpxError;
use crate::parse_arena::{CoreTypeIdx, LocIdx, Located, ParseArena, StrIdx};
use crate::parser::ast::{
    Attribute, Attributes, Constant, ConstructorArguments, ConstructorDeclaration, ConstructorTag,
    Expression, ExpressionDesc, LabelDeclaration, MutableFlag, Payload, StructureItem,
    StructureItemDesc,
};

/// OCaml raises from inside `Type.field`/`Type.constructor` when a backquoted
/// payload holds an invalid escape; the error surfaces with the next ppx
/// error check.
fn defer(arena: &mut ParseArena, error: PayloadError) {
    arena.defer_ppx_error(PpxError::at_loc(error.loc, error.message));
}

fn is_as(arena: &ParseArena, attr: &Attribute) -> bool {
    arena.get_string(attr.0.txt) == "as"
}

/// Take out the first `@as` that `decode` accepts. `stop_at_invalid` follows
/// `Type.constructor`, which leaves an invalid first `@as` (and everything
/// after it) in place; `Type.field` skips over payloads that are not names.
fn take_as<T>(
    arena: &mut ParseArena,
    attrs: Attributes,
    stop_at_invalid: bool,
    decode: fn(&mut ParseArena, &Payload) -> Result<Option<T>, PayloadError>,
) -> (Option<Located<T>>, Attributes) {
    let attrs = attrs.into_vec();
    let mut found = None;
    for (index, attr) in attrs.iter().enumerate() {
        if !is_as(arena, attr) {
            continue;
        }
        match decode(arena, &attr.1) {
            Ok(Some(txt)) => {
                found = Some((index, Located::new(txt, attr.0.loc)));
                break;
            }
            Ok(None) => {
                if stop_at_invalid {
                    break;
                }
            }
            Err(error) => {
                defer(arena, error);
                break;
            }
        }
    }
    match found {
        None => (None, Attributes::from_vec(attrs)),
        Some((index, txt)) => {
            let mut attrs = attrs;
            attrs.remove(index);
            (Some(txt), Attributes::from_vec(attrs))
        }
    }
}

/// OCaml `Ast_helper.Type.constructor`.
pub fn constructor(
    arena: &mut ParseArena,
    loc: LocIdx,
    attrs: Attributes,
    args: ConstructorArguments,
    res: Option<CoreTypeIdx>,
    runtime_tag: Option<ConstructorTag>,
    name: Located<StrIdx>,
) -> ConstructorDeclaration {
    let (pcd_runtime_tag, pcd_attributes) = match runtime_tag {
        Some(tag) => (Some(Located::new(tag, name.loc)), attrs),
        None => take_as(arena, attrs, true, ast_payload::constructor_tag_of_payload),
    };
    ConstructorDeclaration {
        pcd_name: name,
        pcd_runtime_tag,
        pcd_args: args,
        pcd_res: res,
        pcd_loc: loc,
        pcd_attributes,
    }
}

/// OCaml `Ast_helper.Type.field`.
#[allow(clippy::too_many_arguments)]
pub fn field(
    arena: &mut ParseArena,
    loc: LocIdx,
    attrs: Attributes,
    mutable: MutableFlag,
    optional: bool,
    runtime_name: Option<&str>,
    name: Located<StrIdx>,
    typ: CoreTypeIdx,
) -> LabelDeclaration {
    let (pld_runtime_name, pld_attributes) = match runtime_name {
        Some(txt) => {
            let literal = crate::string_literal::string_from_semantic(txt);
            (
                Some(Located::new(arena.push_string_literal(&literal), name.loc)),
                attrs,
            )
        }
        None => take_as(arena, attrs, false, ast_payload::string_const_of_payload),
    };
    LabelDeclaration {
        pld_name: name,
        pld_runtime_name,
        pld_mutable: mutable,
        pld_type: typ,
        pld_loc: loc,
        pld_attributes,
        pld_optional: optional,
    }
}

fn constant_expression(loc: LocIdx, constant: Constant) -> Expression {
    Expression {
        pexp_desc: ExpressionDesc::Pexp_constant(constant),
        pexp_loc: loc,
        pexp_attributes: Attributes::new(),
    }
}

/// Where the rebuilt `@as` payload expression is stored: printers only hold
/// a shared arena, while attributes that become part of the AST go into the
/// ordinary expression storage.
pub enum PayloadArena<'a> {
    Shared(&'a ParseArena),
    Owned(&'a mut ParseArena),
}

impl PayloadArena<'_> {
    fn arena(&self) -> &ParseArena {
        match self {
            PayloadArena::Shared(arena) => arena,
            PayloadArena::Owned(arena) => arena,
        }
    }

    fn push_expr(&mut self, expression: Expression) -> crate::parse_arena::ExprIdx {
        match self {
            PayloadArena::Shared(arena) => arena.push_shared_expr(expression),
            PayloadArena::Owned(arena) => arena.push_expr(expression),
        }
    }
}

/// `(Location.mkloc "as" loc, PStr [Str.eval ~loc expression])`, put back
/// among `attrs` after every attribute written no later than it.
fn put_back_as(
    mut target: PayloadArena<'_>,
    attrs: &Attributes,
    loc: LocIdx,
    expression: Expression,
) -> Attributes {
    let expression = target.push_expr(expression);
    let arena = target.arena();
    let item = StructureItem {
        pstr_desc: StructureItemDesc::Pstr_eval(Box::new((expression, Attributes::new()))),
        pstr_loc: loc,
    };
    let name = arena.as_attribute_name();
    let attr: Attribute = (Located::new(name, loc), Payload::PStr(Box::new(vec![item])));
    let cnum = |arena: &ParseArena, loc: LocIdx| {
        arena.get_position(arena.get_location(loc).loc_start).cnum
    };
    let pos = cnum(arena, loc);
    let (mut earlier, later): (Vec<Attribute>, Vec<Attribute>) = attrs
        .iter()
        .cloned()
        .partition(|other| cnum(arena, other.0.loc) <= pos);
    earlier.push(attr);
    earlier.extend(later);
    Attributes::from_vec(earlier)
}

/// OCaml `Ast_helper.Type.constructor_attributes`: the attributes as
/// written, with the constructor `@as` put back.
pub fn constructor_attributes(arena: &ParseArena, cd: &ConstructorDeclaration) -> Attributes {
    constructor_attributes_in(PayloadArena::Shared(arena), cd)
}

/// [`constructor_attributes`] for attributes that become part of the AST.
pub fn constructor_attributes_owned(
    arena: &mut ParseArena,
    cd: &ConstructorDeclaration,
) -> Attributes {
    constructor_attributes_in(PayloadArena::Owned(arena), cd)
}

fn constructor_attributes_in(target: PayloadArena<'_>, cd: &ConstructorDeclaration) -> Attributes {
    let Some(tag) = &cd.pcd_runtime_tag else {
        return cd.pcd_attributes.clone();
    };
    let loc = tag.loc;
    let expression = match tag.txt {
        ConstructorTag::Pct_string(s) => constant_expression(loc, Constant::String(s)),
        ConstructorTag::Pct_int(i) => constant_expression(loc, Constant::Integer(i, None)),
        ConstructorTag::Pct_float(f) => constant_expression(loc, Constant::Float(f, None)),
        ConstructorTag::Pct_bigint(i) => constant_expression(loc, Constant::Integer(i, Some('n'))),
        ConstructorTag::Pct_bool(b) => {
            let lid = target
                .arena()
                .runtime_tag_lident(if b { "true" } else { "false" });
            Expression {
                pexp_desc: ExpressionDesc::Pexp_construct(
                    Located::new(lid, loc),
                    Located::new(crate::parse_arena::ExprList::EMPTY, loc),
                ),
                pexp_loc: loc,
                pexp_attributes: Attributes::new(),
            }
        }
        ConstructorTag::Pct_null | ConstructorTag::Pct_undefined => {
            let lid =
                target
                    .arena()
                    .runtime_tag_lident(if matches!(tag.txt, ConstructorTag::Pct_null) {
                        "null"
                    } else {
                        "undefined"
                    });
            Expression {
                pexp_desc: ExpressionDesc::Pexp_ident(Located::new(lid, loc)),
                pexp_loc: loc,
                pexp_attributes: Attributes::new(),
            }
        }
    };
    put_back_as(target, &cd.pcd_attributes, loc, expression)
}

/// OCaml `Ast_helper.Type.field_attributes`: the attributes as written,
/// with the `@as` taken out by [`field`] put back.
pub fn field_attributes(arena: &ParseArena, ld: &LabelDeclaration) -> Attributes {
    field_attributes_in(PayloadArena::Shared(arena), ld)
}

/// [`field_attributes`] for attributes that become part of the AST.
pub fn field_attributes_owned(arena: &mut ParseArena, ld: &LabelDeclaration) -> Attributes {
    field_attributes_in(PayloadArena::Owned(arena), ld)
}

fn field_attributes_in(target: PayloadArena<'_>, ld: &LabelDeclaration) -> Attributes {
    let Some(name) = &ld.pld_runtime_name else {
        return ld.pld_attributes.clone();
    };
    let loc = name.loc;
    let expression = constant_expression(loc, Constant::String(name.txt));
    put_back_as(target, &ld.pld_attributes, loc, expression)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::ast::{StructureItemDesc, TypeKind};

    /// The `@as` string a rebuilt attribute list carries, read from a shared
    /// arena as printers and mappers do before type checking.
    fn as_payload_string(arena: &ParseArena, attrs: &Attributes) -> Option<String> {
        attrs.iter().find_map(|(name, payload)| {
            if arena.get_string(name.txt) != "as" {
                return None;
            }
            let Payload::PStr(items) = payload else {
                return None;
            };
            let StructureItemDesc::Pstr_eval(eval) = &items.first()?.pstr_desc else {
                return None;
            };
            match arena.get_expr(eval.0).pexp_desc {
                ExpressionDesc::Pexp_constant(Constant::String(s)) => {
                    Some(s.semantic(arena).to_string())
                }
                ExpressionDesc::Pexp_constant(Constant::Integer(i, _)) => {
                    Some(arena.get_string(i).to_string())
                }
                _ => None,
            }
        })
    }

    #[test]
    fn as_attributes_put_back_before_type_checking_keep_their_strings() {
        let source = "type r = {@as(\"x-real-ip\") ip: string}\n\
                      type v = | @as(\"seedance-2.0\") A | @as(42) B\n";
        let mut parser = crate::parser::Parser::new("test.res", source);
        let structure = crate::parser::module::parse_structure(&mut parser);
        let arena = parser.into_arena();
        let mut seen = Vec::new();
        for item in &structure {
            let StructureItemDesc::Pstr_type(decls) = &item.pstr_desc else {
                continue;
            };
            for decl in &decls.1 {
                match &decl.ptype_kind {
                    TypeKind::Ptype_record(labels) => {
                        for label in labels {
                            seen.push(as_payload_string(&arena, &field_attributes(&arena, label)));
                        }
                    }
                    TypeKind::Ptype_variant(constructors) => {
                        for cd in constructors {
                            seen.push(as_payload_string(
                                &arena,
                                &constructor_attributes(&arena, cd),
                            ));
                        }
                    }
                    _ => {}
                }
            }
        }
        assert_eq!(
            seen,
            [
                Some("x-real-ip".to_string()),
                Some("seedance-2.0".to_string()),
                Some("42".to_string()),
            ]
        );
    }
}
