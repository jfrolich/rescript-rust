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
use crate::string_literal::StringLiteral;

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
    decode: fn(&ParseArena, &Payload) -> Result<Option<T>, PayloadError>,
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
        Some(txt) => (
            Some(Located::new(crate::string_literal::string_from_semantic(txt), name.loc)),
            attrs,
        ),
        None => take_as(arena, attrs, false, ast_payload::string_literal_of_payload),
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
        pexp_desc: Box::new(ExpressionDesc::Pexp_constant(Box::new(constant))),
        pexp_loc: loc,
        pexp_attributes: Attributes::new(),
    }
}

/// `(Location.mkloc "as" loc, PStr [Str.eval ~loc expression])`, put back
/// among `attrs` after every attribute written no later than it.
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

fn put_back_as(
    mut target: PayloadArena<'_>,
    attrs: &Attributes,
    loc: LocIdx,
    expression: Expression,
) -> Attributes {
    let expression = target.push_expr(expression);
    let arena = target.arena();
    let item = StructureItem {
        pstr_desc: Box::new(StructureItemDesc::Pstr_eval(Box::new((expression, Attributes::new())))),
        pstr_loc: loc,
    };
    let name = arena.as_attribute_name();
    let attr: Attribute = (Located::new(name, loc), Payload::PStr(Box::new(vec![item])));
    let cnum = |arena: &ParseArena, loc: LocIdx| arena.get_position(arena.get_location(loc).loc_start).cnum;
    let pos = cnum(arena, loc);
    let (mut earlier, later): (Vec<Attribute>, Vec<Attribute>) =
        attrs.iter().cloned().partition(|other| cnum(arena, other.0.loc) <= pos);
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
pub fn constructor_attributes_owned(arena: &mut ParseArena, cd: &ConstructorDeclaration) -> Attributes {
    constructor_attributes_in(PayloadArena::Owned(arena), cd)
}

fn constructor_attributes_in(target: PayloadArena<'_>, cd: &ConstructorDeclaration) -> Attributes {
    let arena = target.arena();
    let Some(tag) = &cd.pcd_runtime_tag else {
        return cd.pcd_attributes.clone();
    };
    let loc = tag.loc;
    let expression = match &tag.txt {
        ConstructorTag::Pct_string(s) => constant_expression(loc, Constant::String(s.clone())),
        ConstructorTag::Pct_int(i) => {
            constant_expression(loc, Constant::Integer(i.clone().into(), None))
        }
        ConstructorTag::Pct_float(f) => {
            constant_expression(loc, Constant::Float(f.clone().into(), None))
        }
        ConstructorTag::Pct_bigint(i) => {
            constant_expression(loc, Constant::Integer(i.clone().into(), Some('n')))
        }
        ConstructorTag::Pct_bool(b) => {
            let lid = arena.runtime_tag_lident(if *b { "true" } else { "false" });
            Expression {
                pexp_desc: Box::new(ExpressionDesc::Pexp_construct(
                    Located::new(lid, loc),
                    Box::new(Located::new(Vec::new(), loc)),
                )),
                pexp_loc: loc,
                pexp_attributes: Attributes::new(),
            }
        }
        ConstructorTag::Pct_null | ConstructorTag::Pct_undefined => {
            let lid = arena.runtime_tag_lident(if matches!(tag.txt, ConstructorTag::Pct_null) {
                "null"
            } else {
                "undefined"
            });
            Expression {
                pexp_desc: Box::new(ExpressionDesc::Pexp_ident(Located::new(lid, loc))),
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
    let expression = constant_expression(loc, Constant::String(name.txt.clone()));
    put_back_as(target, &ld.pld_attributes, loc, expression)
}

/// The semantic value of a field's runtime name
/// (`String_literal.string_semantic`).
pub fn runtime_name_semantic(name: &Located<StringLiteral>) -> &str {
    name.txt.semantic()
}
