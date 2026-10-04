//! Internal Spice PPX implementation.
//!
//! This is a direct port of the OCaml ppx_spice implementation, adapted to
//! ReScript's current AST representation (arity fields, partial flags, etc.).

use std::borrow::Cow;

use crate::parse_arena::{
    CoreTypeIdx, ExprIdx, LidentIdx, LocIdx, Located, ModExprIdx, ModTypeIdx, ParseArena, PatIdx,
    PosIdx, StrIdx,
};
use crate::parser::ast::{
    ArgLabel, Attribute, Attributes, Case, ClosedFlag, Constant, ConstructorArguments,
    ConstructorDeclaration, CoreType, CoreTypeDesc, Expression, ExpressionDesc,
    ExpressionRecordField, Extension, ExtensionConstructor, ExtensionConstructorKind,
    IncludeDeclaration, IncludeDescription, JsxClosingTag, JsxContainerElement, JsxElement,
    JsxFragment, JsxProp, JsxUnaryElement, LabelDeclaration, ModuleBinding, ModuleDeclaration,
    ModuleExpr, ModuleExprDesc, ModuleType, ModuleTypeDeclaration, ModuleTypeDesc, ObjectField,
    OpenDescription, PackageType, Pattern, PatternDesc, PatternRecordField, Payload, PexpApply,
    PexpFun, RecFlag, RowField, SignatureItem, SignatureItemDesc, StructureItem, StructureItemDesc,
    TypeArg, TypeDeclaration, TypeExtension, TypeKind, ValueBinding, ValueDescription,
    WithConstraint, extend_cow_lifetime,
};
use crate::parser::longident::Longident;

const ANNOTATION_NAME: &str = "spice";
const ENCODER_FUNC_SUFFIX: &str = "_encode";
const VALUE_ENCODER_FUNC_SUFFIX: &str = "_encodeJson";
const DECODER_FUNC_SUFFIX: &str = "_decode";
const ENCODER_VAR_PREFIX: &str = "encoder_";
const DECODER_VAR_PREFIX: &str = "decoder_";

#[derive(Clone, Copy, Debug)]
struct GeneratorSettings {
    do_encode: bool,
    do_decode: bool,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum EncodeContext {
    Optional,
    Value,
}

#[derive(Clone, Debug)]
struct ParsedRecordField {
    name: StrIdx,
    key: Expression,
    key_identity: Option<StrIdx>,
    codecs: (Option<Expression>, Option<Expression>),
    default: Option<Expression>,
    is_optional: bool,
    is_option: bool,
}

#[derive(Clone, Debug)]
struct ParsedVariantDecl {
    name: StrIdx,
    name_literal: StrIdx,
    alias: Expression,
    has_attr_as: bool,
    constr_decl: crate::parser::ast::ConstructorDeclaration,
}

#[derive(Clone, Debug)]
struct ParsedPolyvariantField {
    name: Cow<'static, str>,
    alias: Expression,
    has_attr_as: bool,
    row_field: crate::parser::ast::RowField,
}

type SpiceResult<T> = Result<T, String>;

fn spice_error(message: impl Into<String>) -> String {
    message.into()
}

fn require_encoder(encoder: Option<Expression>) -> SpiceResult<Expression> {
    encoder.ok_or_else(|| spice_error("Internal spice error: missing encoder"))
}

fn require_decoder(decoder: Option<Expression>) -> SpiceResult<Expression> {
    decoder.ok_or_else(|| spice_error("Internal spice error: missing decoder"))
}

fn lident_path_static(arena: &mut ParseArena, parts: &[&str]) -> LidentIdx {
    if parts.is_empty() {
        return {
            let lident_name = arena.intern_string("");
            arena.push_lident_from_idx(lident_name)
        };
    }
    if parts.len() == 1 {
        if parts[0] == "v" {
            let idx = arena.spice_runtime_v();
            return arena.push_lident_from_idx(idx);
        }
        return {
            let lident_name = arena.intern_string(parts[0]);
            arena.push_lident_from_idx(lident_name)
        };
    }
    let first = match parts[0] {
        "JSON" => arena.spice_json_str(),
        "Option" => arena.spice_option_str(),
        "Dict" => arena.spice_dict_str(),
        "Result" => arena.spice_result_str(),
        "Array" => arena.spice_array_str(),
        _ => arena.intern_string(parts[0]),
    };
    let mut lid = Longident::Lident(first);
    for part in &parts[1..] {
        lid = Longident::Ldot(Box::new(lid), arena.intern_string(part));
    }
    arena.push_longident(lid)
}

fn lident_path_parse(arena: &mut ParseArena, parts: &[&str]) -> LidentIdx {
    if parts.is_empty() {
        return {
            let lident_name = arena.intern_string("");
            arena.push_lident_from_idx(lident_name)
        };
    }
    let mut lid = Longident::Lident(arena.push_string(parts[0].to_string()));
    for part in &parts[1..] {
        lid = Longident::Ldot(Box::new(lid), arena.push_string(part.to_string()));
    }
    arena.push_longident(lid)
}

fn lident_path_from_parts(arena: &mut ParseArena, parts: &[StrIdx]) -> LidentIdx {
    if parts.is_empty() {
        return {
            let lident_name = arena.intern_string("");
            arena.push_lident_from_idx(lident_name)
        };
    }
    let mut lid = Longident::Lident(parts[0]);
    for part in &parts[1..] {
        lid = Longident::Ldot(Box::new(lid), *part);
    }
    arena.push_longident(lid)
}

fn lident_path_spice_prefix(arena: &mut ParseArena, prefix: StrIdx, suffix: &str) -> LidentIdx {
    let suffix_idx = arena.intern_string(suffix);
    lident_path_from_parts(arena, &[prefix, suffix_idx])
}

fn longident_matches(arena: &ParseArena, lid_idx: LidentIdx, parts: &[&str]) -> bool {
    fn collect<'a>(arena: &'a ParseArena, lid: &Longident, out: &mut Vec<&'a str>) {
        match lid {
            Longident::Lident(idx) => out.push(arena.get_string(*idx)),
            Longident::Ldot(prefix, idx) => {
                collect(arena, prefix, out);
                out.push(arena.get_string(*idx));
            }
            Longident::Lapply(_, _) => {}
        }
    }

    let lid = arena.get_longident(lid_idx);
    let mut segs = Vec::new();
    collect(arena, lid, &mut segs);
    if segs.len() != parts.len() {
        return false;
    }
    segs.iter().zip(parts.iter()).all(|(a, b)| *a == *b)
}

fn expr_ident_with_loc(lid_idx: LidentIdx, ident_loc: LocIdx, expr_loc: LocIdx) -> Expression {
    Expression {
        pexp_desc: Box::new(ExpressionDesc::Pexp_ident(Located::new(lid_idx, ident_loc))),
        pexp_loc: expr_loc,
        pexp_attributes: Attributes::new(),
    }
}

fn expr_ident_path(arena: &mut ParseArena, parts: &[&str]) -> Expression {
    let lid_idx = lident_path_static(arena, parts);
    expr_ident_with_loc(lid_idx, arena.dummy_loc(), arena.dummy_loc())
}

fn expr_ident_spice_prefix(arena: &mut ParseArena, prefix: StrIdx, suffix: &str) -> Expression {
    let lid_idx = lident_path_spice_prefix(arena, prefix, suffix);
    expr_ident_with_loc(lid_idx, arena.dummy_loc(), arena.dummy_loc())
}

fn expr_ident_spice_codecs_with_loc(
    arena: &mut ParseArena,
    suffix: &str,
    lid_loc: LocIdx,
) -> Expression {
    let prefix = arena.spice_codecs_str();
    let lid_idx = lident_path_spice_prefix(arena, prefix, suffix);
    expr_ident_with_loc(lid_idx, lid_loc, lid_loc)
}

fn expr_ident_spice_records(arena: &mut ParseArena, suffix: &str) -> Expression {
    let prefix = arena.spice_records_str();
    expr_ident_spice_prefix(arena, prefix, suffix)
}

fn expr_ident_spice_variants(arena: &mut ParseArena, suffix: &str) -> Expression {
    let prefix = arena.spice_variants_str();
    expr_ident_spice_prefix(arena, prefix, suffix)
}

fn expr_ident_spice_polyvars(arena: &mut ParseArena, suffix: &str) -> Expression {
    let prefix = arena.spice_polyvars_str();
    expr_ident_spice_prefix(arena, prefix, suffix)
}

fn expr_ident_spice_tuple(arena: &mut ParseArena, suffix: &str) -> Expression {
    let prefix = arena.spice_tuple_str();
    expr_ident_spice_prefix(arena, prefix, suffix)
}

fn expr_ident_path_mknoloc(arena: &mut ParseArena, parts: &[&str]) -> Expression {
    let lid_idx = lident_path_static(arena, parts);
    expr_ident_with_loc(lid_idx, arena.none_loc(), arena.dummy_loc())
}

fn expr_ident_path_with_lid_loc(
    arena: &mut ParseArena,
    parts: &[&str],
    lid_loc: LocIdx,
) -> Expression {
    let lid_idx = lident_path_static(arena, parts);
    expr_ident_with_loc(lid_idx, lid_loc, lid_loc)
}

fn expr_ident_path_dynamic(
    arena: &mut ParseArena,
    parts: &[&str],
    ident_loc: LocIdx,
) -> Expression {
    let lid_idx = lident_path_parse(arena, parts);
    expr_ident_with_loc(lid_idx, ident_loc, arena.dummy_loc())
}

fn expr_ident_path_dynamic_mknoloc(arena: &mut ParseArena, parts: &[&str]) -> Expression {
    expr_ident_path_dynamic(arena, parts, arena.none_loc())
}

fn expr_ident_from_str_idx(arena: &mut ParseArena, idx: StrIdx, ident_loc: LocIdx) -> Expression {
    let lid_idx = arena.push_lident_from_idx(idx);
    expr_ident_with_loc(lid_idx, ident_loc, arena.dummy_loc())
}

fn expr_ident_dynamic(arena: &mut ParseArena, name: String) -> Expression {
    let idx = arena.push_string(name);
    expr_ident_from_str_idx(arena, idx, arena.none_loc())
}

fn expr_constant(constant: Constant, arena: &mut ParseArena) -> Expression {
    Expression {
        pexp_desc: Box::new(ExpressionDesc::Pexp_constant(Box::new(constant))),
        pexp_loc: arena.dummy_loc(),
        pexp_attributes: Attributes::new(),
    }
}

fn expr_constant_literal(arena: &mut ParseArena, value: &str) -> Expression {
    arena.register_shareable_literal(value);
    expr_constant(Constant::string(value), arena)
}

fn expr_apply(
    funct: Expression,
    args: Vec<(ArgLabel, Expression)>,
    partial: bool,
    loc: LocIdx,
    arena: &mut ParseArena,
) -> Expression {
    let funct_idx = arena.push_expr(funct);
    let args_idx: Vec<(ArgLabel, ExprIdx)> = args
        .into_iter()
        .map(|(lbl, e)| (lbl, arena.push_expr(e)))
        .collect();
    Expression {
        pexp_desc: Box::new(ExpressionDesc::Pexp_apply(Box::new(PexpApply {
            funct: funct_idx,
            args: args_idx,
            partial,
            transformed_jsx: false,
        }))),
        pexp_loc: loc,
        pexp_attributes: Attributes::new(),
    }
}

fn expr_fun(
    arg_label: ArgLabel,
    lhs: Pattern,
    rhs: Expression,
    arity: Option<i32>,
    arena: &mut ParseArena,
) -> Expression {
    let arity_idx = arena.push_arity(arity);
    let rhs_idx = arena.push_expr(rhs);
    let lhs_idx = arena.push_pat(lhs);
    Expression {
        pexp_desc: Box::new(ExpressionDesc::Pexp_fun(Box::new(PexpFun {
            arg_label,
            default: None,
            lhs: lhs_idx,
            rhs: rhs_idx,
            arity: arity_idx,
            is_async: false,
        }))),
        pexp_loc: arena.dummy_loc(),
        pexp_attributes: Attributes::new(),
    }
}

fn expr_fun_with_loc(
    arg_label: ArgLabel,
    lhs: Pattern,
    rhs: Expression,
    arity: Option<i32>,
    loc: LocIdx,
    arena: &mut ParseArena,
) -> Expression {
    let arity_idx = arena.push_arity(arity);
    let rhs_idx = arena.push_expr(rhs);
    let lhs_idx = arena.push_pat(lhs);
    Expression {
        pexp_desc: Box::new(ExpressionDesc::Pexp_fun(Box::new(PexpFun {
            arg_label,
            default: None,
            lhs: lhs_idx,
            rhs: rhs_idx,
            arity: arity_idx,
            is_async: false,
        }))),
        pexp_loc: loc,
        pexp_attributes: Attributes::new(),
    }
}

fn expr_tuple(items: Vec<Expression>, arena: &mut ParseArena) -> Expression {
    let items_idx: Vec<ExprIdx> = items.into_iter().map(|e| arena.push_expr(e)).collect();
    Expression {
        pexp_desc: Box::new(ExpressionDesc::Pexp_tuple(Box::new(items_idx))),
        pexp_loc: arena.dummy_loc(),
        pexp_attributes: Attributes::new(),
    }
}

fn expr_array(items: Vec<Expression>, arena: &mut ParseArena) -> Expression {
    let items_idx: Vec<ExprIdx> = items.into_iter().map(|e| arena.push_expr(e)).collect();
    Expression {
        pexp_desc: Box::new(ExpressionDesc::Pexp_array(Box::new(items_idx))),
        pexp_loc: arena.dummy_loc(),
        pexp_attributes: Attributes::new(),
    }
}

/// The constructor argument list the upstream PPX bridge
/// (`Ast_mapper_from0.decode_args`) builds from this PPX's single v0
/// payload: a tuple splits into arguments only for `::`; anything else is
/// the one argument. The list is located at the payload, or at the node
/// when there is none.
fn bridge_expr_args(
    split_tuple: bool,
    arg: Option<Expression>,
    node_loc: LocIdx,
    arena: &mut ParseArena,
) -> Located<Vec<ExprIdx>> {
    match arg {
        None => Located::new(Vec::new(), node_loc),
        Some(arg) => {
            let loc = arg.pexp_loc;
            match &*arg.pexp_desc {
                ExpressionDesc::Pexp_tuple(items) if split_tuple && arg.pexp_attributes.is_empty() => {
                    Located::new(items.to_vec(), loc)
                }
                _ => Located::new(vec![arena.push_expr(arg)], loc),
            }
        }
    }
}

/// `bridge_expr_args` for patterns.
fn bridge_pat_args(
    split_tuple: bool,
    arg: Option<Pattern>,
    node_loc: LocIdx,
    arena: &mut ParseArena,
) -> Located<Vec<PatIdx>> {
    match arg {
        None => Located::new(Vec::new(), node_loc),
        Some(arg) => {
            let loc = arg.ppat_loc;
            match &*arg.ppat_desc {
                PatternDesc::Ppat_tuple(items) if split_tuple && arg.ppat_attributes.is_empty() => {
                    Located::new(items.to_vec(), loc)
                }
                _ => Located::new(vec![arena.push_pat(arg)], loc),
            }
        }
    }
}

fn expr_construct(
    lid_idx: LidentIdx,
    arg: Option<Expression>,
    arena: &mut ParseArena,
) -> Expression {
    expr_construct_with_loc(lid_idx, arg, arena.none_loc(), arena)
}

fn expr_construct_with_loc(
    lid_idx: LidentIdx,
    arg: Option<Expression>,
    lid_loc: LocIdx,
    arena: &mut ParseArena,
) -> Expression {
    let expr_loc = arena.dummy_loc();
    expr_construct_with_locs(lid_idx, arg, lid_loc, expr_loc, arena)
}

fn expr_construct_with_locs(
    lid_idx: LidentIdx,
    arg: Option<Expression>,
    lid_loc: LocIdx,
    expr_loc: LocIdx,
    arena: &mut ParseArena,
) -> Expression {
    let split_tuple = arena.is_lident(lid_idx, "::");
    let args = bridge_expr_args(split_tuple, arg, expr_loc, arena);
    Expression {
        pexp_desc: Box::new(ExpressionDesc::Pexp_construct(
            Located::new(lid_idx, lid_loc),
            Box::new(args),
        )),
        pexp_loc: expr_loc,
        pexp_attributes: Attributes::new(),
    }
}

fn expr_variant(
    label: Cow<'static, str>,
    arg: Option<Expression>,
    arena: &mut ParseArena,
) -> Expression {
    let loc = arena.dummy_loc();
    let args = bridge_expr_args(false, arg, loc, arena);
    Expression {
        pexp_desc: Box::new(ExpressionDesc::Pexp_variant(Box::new((label, args)))),
        pexp_loc: loc,
        pexp_attributes: Attributes::new(),
    }
}

fn expr_match(expr: Expression, cases: Vec<Case>, arena: &mut ParseArena) -> Expression {
    let expr_idx = arena.push_expr(expr);
    Expression {
        pexp_desc: Box::new(ExpressionDesc::Pexp_match(Box::new((expr_idx, cases)))),
        pexp_loc: arena.dummy_loc(),
        pexp_attributes: Attributes::new(),
    }
}

fn expr_ifthenelse(
    cond: Expression,
    then_expr: Expression,
    else_expr: Option<Expression>,
    arena: &mut ParseArena,
) -> Expression {
    let cond_idx = arena.push_expr(cond);
    let then_idx = arena.push_expr(then_expr);
    let else_idx = else_expr.map(|e| arena.push_expr(e));
    Expression {
        pexp_desc: Box::new(ExpressionDesc::Pexp_ifthenelse(Box::new((
            cond_idx, then_idx, else_idx,
        )))),
        pexp_loc: arena.dummy_loc(),
        pexp_attributes: Attributes::new(),
    }
}

fn expr_let(
    rec_flag: RecFlag,
    bindings: Vec<ValueBinding>,
    body: Expression,
    arena: &mut ParseArena,
) -> Expression {
    let body_idx = arena.push_expr(body);
    Expression {
        pexp_desc: Box::new(ExpressionDesc::Pexp_let(Box::new((
            rec_flag, bindings, body_idx,
        )))),
        pexp_loc: arena.dummy_loc(),
        pexp_attributes: Attributes::new(),
    }
}

fn expr_constraint(expr: Expression, typ: CoreType, arena: &mut ParseArena) -> Expression {
    let expr_idx = arena.push_expr(expr);
    let typ_idx = arena.push_core_type(typ);
    Expression {
        pexp_desc: Box::new(ExpressionDesc::Pexp_constraint(Box::new((
            expr_idx, typ_idx,
        )))),
        pexp_loc: arena.dummy_loc(),
        pexp_attributes: Attributes::new(),
    }
}

fn expr_field_with_loc(
    expr: Expression,
    lid_idx: LidentIdx,
    lid_loc: LocIdx,
    arena: &mut ParseArena,
) -> Expression {
    let expr_idx = arena.push_expr(expr);
    Expression {
        pexp_desc: Box::new(ExpressionDesc::Pexp_field(
            expr_idx,
            Located::new(lid_idx, lid_loc),
        )),
        pexp_loc: arena.dummy_loc(),
        pexp_attributes: Attributes::new(),
    }
}

fn expr_field(expr: Expression, lid_idx: LidentIdx, arena: &mut ParseArena) -> Expression {
    expr_field_with_loc(expr, lid_idx, arena.none_loc(), arena)
}

fn expr_field_default_loc(
    expr: Expression,
    lid_idx: LidentIdx,
    arena: &mut ParseArena,
) -> Expression {
    expr_field_with_loc(expr, lid_idx, arena.none_loc(), arena)
}

fn expr_record(
    fields: Vec<ExpressionRecordField>,
    base: Option<Expression>,
    arena: &mut ParseArena,
) -> Expression {
    let base_idx = base.map(|b| arena.push_expr(b));
    Expression {
        pexp_desc: Box::new(ExpressionDesc::Pexp_record(Box::new((fields, base_idx)))),
        pexp_loc: arena.dummy_loc(),
        pexp_attributes: Attributes::new(),
    }
}

fn pat_any(arena: &mut ParseArena) -> Pattern {
    Pattern {
        ppat_desc: Box::new(PatternDesc::Ppat_any),
        ppat_loc: arena.dummy_loc(),
        ppat_attributes: Attributes::new(),
    }
}

fn pat_var_idx(arena: &mut ParseArena, idx: StrIdx, loc: LocIdx) -> Pattern {
    Pattern {
        ppat_desc: Box::new(PatternDesc::Ppat_var(Located::new(idx, loc))),
        ppat_loc: arena.dummy_loc(),
        ppat_attributes: Attributes::new(),
    }
}

fn pat_var_idx_with_loc(arena: &mut ParseArena, idx: StrIdx, loc: LocIdx) -> Pattern {
    Pattern {
        ppat_desc: Box::new(PatternDesc::Ppat_var(Located::new(idx, loc))),
        ppat_loc: loc,
        ppat_attributes: Attributes::new(),
    }
}

fn pat_var(arena: &mut ParseArena, name: &str, loc: LocIdx) -> Pattern {
    let idx = if name == "v" {
        arena.spice_pat_v()
    } else {
        arena.intern_string(name)
    };
    pat_var_idx(arena, idx, loc)
}

fn pat_var_with_loc(arena: &mut ParseArena, name: &str, loc: LocIdx) -> Pattern {
    let idx = if name == "v" {
        arena.spice_pat_v()
    } else {
        arena.intern_string(name)
    };
    pat_var_idx_with_loc(arena, idx, loc)
}

fn pat_var_dynamic(arena: &mut ParseArena, name: &str, loc: LocIdx) -> Pattern {
    let idx = arena.push_string(name.to_string());
    pat_var_idx(arena, idx, loc)
}

fn pat_var_none(arena: &mut ParseArena, name: &str) -> Pattern {
    pat_var(arena, name, arena.none_loc())
}

fn pat_var_dummy(arena: &mut ParseArena, name: &str) -> Pattern {
    pat_var(arena, name, arena.dummy_loc())
}

fn pat_tuple(items: Vec<Pattern>, arena: &mut ParseArena) -> Pattern {
    let items_idx: Vec<PatIdx> = items.into_iter().map(|p| arena.push_pat(p)).collect();
    Pattern {
        ppat_desc: Box::new(PatternDesc::Ppat_tuple(Box::new(items_idx))),
        ppat_loc: arena.dummy_loc(),
        ppat_attributes: Attributes::new(),
    }
}

fn pat_array(items: Vec<Pattern>, arena: &mut ParseArena) -> Pattern {
    let items_idx: Vec<PatIdx> = items.into_iter().map(|p| arena.push_pat(p)).collect();
    Pattern {
        ppat_desc: Box::new(PatternDesc::Ppat_array(Box::new(items_idx))),
        ppat_loc: arena.dummy_loc(),
        ppat_attributes: Attributes::new(),
    }
}

fn pat_construct(lid_idx: LidentIdx, arg: Option<Pattern>, arena: &mut ParseArena) -> Pattern {
    let loc = arena.none_loc();
    pat_construct_with_loc(lid_idx, arg, loc, arena)
}

fn pat_construct_with_loc(
    lid_idx: LidentIdx,
    arg: Option<Pattern>,
    loc: LocIdx,
    arena: &mut ParseArena,
) -> Pattern {
    let pat_loc = arena.dummy_loc();
    let split_tuple = arena.is_lident(lid_idx, "::");
    let args = bridge_pat_args(split_tuple, arg, pat_loc, arena);
    Pattern {
        ppat_desc: Box::new(PatternDesc::Ppat_construct(Located::new(lid_idx, loc), Box::new(args))),
        ppat_loc: pat_loc,
        ppat_attributes: Attributes::new(),
    }
}

fn pat_variant(label: Cow<'static, str>, arg: Option<Pattern>, arena: &mut ParseArena) -> Pattern {
    let loc = arena.dummy_loc();
    let args = bridge_pat_args(false, arg, loc, arena);
    Pattern {
        ppat_desc: Box::new(PatternDesc::Ppat_variant(Box::new((label, args)))),
        ppat_loc: loc,
        ppat_attributes: Attributes::new(),
    }
}

fn pat_constraint(pat: Pattern, typ: CoreType, arena: &mut ParseArena) -> Pattern {
    let pat_idx = arena.push_pat(pat);
    let typ_idx = arena.push_core_type(typ);
    Pattern {
        ppat_desc: Box::new(PatternDesc::Ppat_constraint(Box::new((pat_idx, typ_idx)))),
        ppat_loc: arena.dummy_loc(),
        ppat_attributes: Attributes::new(),
    }
}

fn case(pat: Pattern, rhs: Expression, arena: &mut ParseArena) -> Case {
    let pat_idx = arena.push_pat(pat);
    let rhs_idx = arena.push_expr(rhs);
    Case {
        pc_bar: None,
        pc_lhs: pat_idx,
        pc_guard: None,
        pc_rhs: rhs_idx,
    }
}

fn tuple_expr_or_singleton(items: Vec<Expression>, arena: &mut ParseArena) -> Expression {
    if items.len() == 1 {
        items.into_iter().next().unwrap()
    } else {
        expr_tuple(items, arena)
    }
}

fn tuple_pat_or_singleton(items: Vec<Pattern>, arena: &mut ParseArena) -> Pattern {
    if items.len() == 1 {
        items.into_iter().next().unwrap()
    } else {
        pat_tuple(items, arena)
    }
}

fn mk_type_constr_with_lid_loc(
    lid_idx: LidentIdx,
    lid_loc: LocIdx,
    args: Vec<CoreType>,
    arena: &mut ParseArena,
) -> CoreType {
    let args_idx: Vec<CoreTypeIdx> = args
        .into_iter()
        .map(|ct| arena.push_core_type(ct))
        .collect();
    CoreType {
        ptyp_desc: Box::new(CoreTypeDesc::Ptyp_constr(Box::new((
            Located::new(lid_idx, lid_loc),
            args_idx,
        )))),
        ptyp_loc: arena.dummy_loc(),
        ptyp_attributes: Attributes::new(),
    }
}

fn mk_type_constr(lid_idx: LidentIdx, args: Vec<CoreType>, arena: &mut ParseArena) -> CoreType {
    mk_type_constr_with_lid_loc(lid_idx, arena.none_loc(), args, arena)
}

fn mk_type_var(name: &str, arena: &mut ParseArena) -> CoreType {
    CoreType {
        ptyp_desc: Box::new(CoreTypeDesc::Ptyp_var(Box::new(Cow::Owned(
            name.to_string(),
        )))),
        ptyp_loc: arena.dummy_loc(),
        ptyp_attributes: Attributes::new(),
    }
}

fn mk_type_arrow(arg_type: CoreType, ret_type: CoreType, arena: &mut ParseArena) -> CoreType {
    let arg_type_idx = arena.push_core_type(arg_type);
    let arg = TypeArg {
        attrs: Attributes::new(),
        lbl: ArgLabel::Nolabel,
        typ: arg_type_idx,
    };
    let ret_idx = arena.push_core_type(ret_type);
    CoreType {
        ptyp_desc: Box::new(CoreTypeDesc::Ptyp_arrow(Box::new((
            Box::new(arg),
            ret_idx,
            arena.push_arity(Some(1)),
        )))),
        ptyp_loc: arena.dummy_loc(),
        ptyp_attributes: Attributes::new(),
    }
}

fn mk_type_arrow_no_arity(
    arg_type: CoreType,
    ret_type: CoreType,
    arena: &mut ParseArena,
) -> CoreType {
    let arg_type_idx = arena.push_core_type(arg_type);
    let arg = TypeArg {
        attrs: Attributes::new(),
        lbl: ArgLabel::Nolabel,
        typ: arg_type_idx,
    };
    let ret_idx = arena.push_core_type(ret_type);
    CoreType {
        ptyp_desc: Box::new(CoreTypeDesc::Ptyp_arrow(Box::new((
            Box::new(arg),
            ret_idx,
            arena.push_arity(None),
        )))),
        ptyp_loc: arena.dummy_loc(),
        ptyp_attributes: Attributes::new(),
    }
}

fn ctyp_json_t(arena: &mut ParseArena) -> CoreType {
    let json_idx = arena.spice_json_str();
    let t_idx = arena.spice_json_t_str();
    let json_lid = lident_path_from_parts(arena, &[json_idx, t_idx]);
    mk_type_constr_with_lid_loc(json_lid, arena.dummy_loc(), vec![], arena)
}

fn ctyp_json_t_const(arena: &mut ParseArena) -> CoreType {
    let json_lid = arena.spice_json_ctyp_lident();
    mk_type_constr(json_lid, vec![], arena)
}

fn make_ident_expr(arena: &mut ParseArena, name: &str) -> Expression {
    let lid_idx = lident_path_parse(arena, &[name]);
    expr_ident_with_loc(lid_idx, arena.dummy_loc(), arena.dummy_loc())
}

fn get_attribute_by_name<'a>(
    attrs: &'a [Attribute],
    name: &str,
    arena: &ParseArena,
) -> Result<Option<&'a Attribute>, String> {
    let mut found: Option<&Attribute> = None;
    for attr in attrs {
        let attr_name = arena.get_string(attr.0.txt);
        if attr_name == name {
            if found.is_some() {
                return Err(format!("Too many occurrences of \"{}\" attribute", name));
            }
            found = Some(attr);
        }
    }
    Ok(found)
}

fn get_generator_settings_from_attributes(
    attrs: &[Attribute],
    arena: &ParseArena,
) -> Result<Option<GeneratorSettings>, String> {
    match get_attribute_by_name(attrs, ANNOTATION_NAME, arena)? {
        Some(_) => Ok(Some(GeneratorSettings {
            do_encode: true,
            do_decode: true,
        })),
        None => {
            let decode = get_attribute_by_name(attrs, "spice.decode", arena)?;
            let encode = get_attribute_by_name(attrs, "spice.encode", arena)?;
            match (decode, encode) {
                (Some(_), Some(_)) => Ok(Some(GeneratorSettings {
                    do_encode: true,
                    do_decode: true,
                })),
                (Some(_), None) => Ok(Some(GeneratorSettings {
                    do_encode: false,
                    do_decode: true,
                })),
                (None, Some(_)) => Ok(Some(GeneratorSettings {
                    do_encode: true,
                    do_decode: false,
                })),
                (None, None) => Ok(None),
            }
        }
    }
}

fn get_expression_from_payload(attr: &Attribute, arena: &ParseArena) -> Result<Expression, String> {
    let payload = &attr.1;
    match payload {
        Payload::PStr(items) => {
            if items.len() != 1 {
                return Err("Expected expression as attribute payload".to_string());
            }
            match &*items[0].pstr_desc {
                StructureItemDesc::Pstr_eval(inner) => {
                    let (ref expr_idx, _) = **inner;
                    Ok(arena.get_expr(*expr_idx).clone())
                }
                _ => Err("Expected expression as attribute payload".to_string()),
            }
        }
        _ => Err("Expected expression as attribute payload".to_string()),
    }
}

fn get_param_names(
    params: &[(CoreTypeIdx, crate::parser::ast::Variance)],
    arena: &ParseArena,
) -> Result<Vec<String>, String> {
    let mut names = Vec::with_capacity(params.len());
    for (typ_idx, _) in params {
        let typ = arena.get_core_type(*typ_idx);
        match &*typ.ptyp_desc {
            CoreTypeDesc::Ptyp_var(name) => names.push(name.to_string()),
            _ => return Err("Unhandled param type".to_string()),
        }
    }
    Ok(names)
}

fn get_string_from_expression(expr: &Expression) -> Result<Option<Constant>, String> {
    match &*expr.pexp_desc {
        ExpressionDesc::Pexp_constant(constant) => match &**constant {
            Constant::String(_) => Ok(Some((**constant).clone())),
            Constant::Float(_, _) => Ok(None),
            _ => Err("cannot find a name??".to_string()),
        },
        _ => Err("cannot find a name??".to_string()),
    }
}

fn get_float_from_expression(expr: &Expression) -> Result<Option<Constant>, String> {
    match &*expr.pexp_desc {
        ExpressionDesc::Pexp_constant(constant) => match &**constant {
            Constant::String(_) => Ok(None),
            Constant::Float(_, _) => Ok(Some((**constant).clone())),
            _ => Err("cannot find a name??".to_string()),
        },
        _ => Err("cannot find a name??".to_string()),
    }
}

fn index_const(i: usize, arena: &mut ParseArena) -> Expression {
    let value = format!("[{}]", i);
    expr_constant(
        Constant::string(&value),
        arena,
    )
}

fn check_option_type(typ_idx: &CoreTypeIdx, arena: &ParseArena) -> bool {
    let typ = arena.get_core_type(*typ_idx);
    match &*typ.ptyp_desc {
        CoreTypeDesc::Ptyp_constr(inner) => {
            let (ref lid, ref args) = **inner;
            longident_matches(arena, lid.txt, &["option"]) && args.len() == 1
        }
        _ => false,
    }
}

fn expr_spice_error_with_prefix(
    arena: &mut ParseArena,
    prefix: StrIdx,
    message: Expression,
    value: Expression,
    path: Option<Expression>,
) -> Expression {
    let func = expr_ident_spice_prefix(arena, prefix, "error");
    let mut args: Vec<(ArgLabel, Expression)> = Vec::new();
    if let Some(path_expr) = path {
        arena.register_shareable_literal("path");
        let label_idx = arena.intern_string("path");
        args.push((
            ArgLabel::Labelled(Located::new(label_idx, arena.none_loc())),
            path_expr,
        ));
    }
    args.push((ArgLabel::Nolabel, message));
    args.push((ArgLabel::Nolabel, value));
    expr_apply(func, args, false, arena.dummy_loc(), arena)
}

fn expr_spice_error_records(
    arena: &mut ParseArena,
    message: Expression,
    value: Expression,
    path: Option<Expression>,
) -> Expression {
    let prefix = arena.spice_records_str();
    expr_spice_error_with_prefix(arena, prefix, message, value, path)
}

fn expr_spice_error_variants(
    arena: &mut ParseArena,
    message: Expression,
    value: Expression,
    path: Option<Expression>,
) -> Expression {
    let prefix = arena.spice_variants_str();
    expr_spice_error_with_prefix(arena, prefix, message, value, path)
}

fn expr_spice_error_polyvars(
    arena: &mut ParseArena,
    message: Expression,
    value: Expression,
    path: Option<Expression>,
) -> Expression {
    let prefix = arena.spice_polyvars_str();
    expr_spice_error_with_prefix(arena, prefix, message, value, path)
}

fn expr_spice_error_tuple(
    arena: &mut ParseArena,
    message: Expression,
    value: Expression,
    path: Option<Expression>,
) -> Expression {
    let prefix = arena.spice_tuple_str();
    expr_spice_error_with_prefix(arena, prefix, message, value, path)
}

fn expr_concat(arena: &mut ParseArena, left: Expression, right: Expression) -> Expression {
    let op = expr_ident_path(arena, &["++"]);
    expr_apply(
        op,
        vec![(ArgLabel::Nolabel, left), (ArgLabel::Nolabel, right)],
        false,
        arena.dummy_loc(),
        arena,
    )
}

fn expr_equal(arena: &mut ParseArena, left: Expression, right: Expression) -> Expression {
    let lid_idx = lident_path_static(arena, &["=="]);
    let op = expr_ident_with_loc(lid_idx, arena.none_loc(), arena.dummy_loc());
    expr_apply(
        op,
        vec![(ArgLabel::Nolabel, left), (ArgLabel::Nolabel, right)],
        false,
        arena.dummy_loc(),
        arena,
    )
}

fn expr_not_equal(arena: &mut ParseArena, left: Expression, right: Expression) -> Expression {
    let lid_idx = lident_path_static(arena, &["!="]);
    let op = expr_ident_with_loc(lid_idx, arena.dummy_loc(), arena.dummy_loc());
    expr_apply(
        op,
        vec![(ArgLabel::Nolabel, left), (ArgLabel::Nolabel, right)],
        false,
        arena.dummy_loc(),
        arena,
    )
}

fn expr_not_equal_strict(
    arena: &mut ParseArena,
    left: Expression,
    right: Expression,
) -> Expression {
    let lid_idx = lident_path_static(arena, &["!=="]);
    let op = expr_ident_with_loc(lid_idx, arena.dummy_loc(), arena.dummy_loc());
    expr_apply(
        op,
        vec![(ArgLabel::Nolabel, left), (ArgLabel::Nolabel, right)],
        false,
        arena.dummy_loc(),
        arena,
    )
}

fn build_ifthenelse_with_prefix(
    arena: &mut ParseArena,
    cases: Vec<(Expression, Expression)>,
    prefix: StrIdx,
) -> Expression {
    let mut iter = cases.into_iter().rev();
    let v_expr = expr_ident_path(arena, &["v"]);
    let not_matched = expr_constant_literal(arena, "Not matched");
    let mut acc = expr_spice_error_with_prefix(arena, prefix, not_matched, v_expr, None);
    while let Some((if_expr, then_expr)) = iter.next() {
        acc = expr_ifthenelse(if_expr, then_expr, Some(acc), arena);
    }
    acc
}

fn tuple_or_singleton_expr(items: Vec<Expression>, arena: &mut ParseArena) -> Expression {
    tuple_expr_or_singleton(items, arena)
}

fn tuple_or_singleton_pat(items: Vec<Pattern>, arena: &mut ParseArena) -> Pattern {
    tuple_pat_or_singleton(items, arena)
}

fn generate_error_case(
    num_args: usize,
    index: usize,
    has_type_offset: bool,
    arena: &mut ParseArena,
) -> Case {
    let mut pats = Vec::with_capacity(num_args);
    for which in 0..num_args {
        if which == index {
            let e_loc = arena.dummy_loc();
            let e_pat = pat_var(arena, "e", e_loc);
            let decode_error_type = mk_type_constr_with_lid_loc(
                lident_path_parse(arena, &["Spice", "decodeError"]),
                arena.dummy_loc(),
                vec![],
                arena,
            );
            let err_pat = pat_constraint(e_pat, decode_error_type, arena);
            let error_lid = {
                let lident_name = arena.intern_string("Error");
                arena.push_lident_from_idx(lident_name)
            };
            pats.push(pat_construct_with_loc(
                error_lid,
                Some(err_pat),
                arena.dummy_loc(),
                arena,
            ));
        } else {
            pats.push(pat_any(arena));
        }
    }
    let lhs = tuple_or_singleton_pat(pats, arena);

    let e_expr = expr_ident_path(arena, &["e"]);
    let path_field = expr_field_with_loc(
        e_expr.clone(),
        {
            let lident_name = arena.intern_string("path");
            arena.push_lident_from_idx(lident_name)
        },
        arena.dummy_loc(),
        arena,
    );
    let index_expr = index_const(index + usize::from(has_type_offset), arena);
    let new_path = expr_concat(arena, index_expr, path_field);

    let record_field = ExpressionRecordField {
        lid: Located::new(
            {
                let lident_name = arena.intern_string("path");
                arena.push_lident_from_idx(lident_name)
            },
            arena.dummy_loc(),
        ),
        expr: arena.push_expr(new_path),
        opt: false,
    };
    let record_expr = expr_record(vec![record_field], Some(e_expr), arena);
    let error_expr = expr_construct_with_loc(
        {
            let lident_name = arena.intern_string("Error");
            arena.push_lident_from_idx(lident_name)
        },
        Some(record_expr),
        arena.dummy_loc(),
        arena,
    );

    let lhs_idx = arena.push_pat(lhs);
    let rhs_idx = arena.push_expr(error_expr);
    Case {
        pc_bar: None,
        pc_lhs: lhs_idx,
        pc_guard: None,
        pc_rhs: rhs_idx,
    }
}

fn tuple_generate_encoder(
    composite_encoders: Vec<Expression>,
    arena: &mut ParseArena,
) -> Expression {
    let mut arr_items = Vec::with_capacity(composite_encoders.len());
    for (i, encoder) in composite_encoders.iter().enumerate() {
        let v_expr = expr_ident_dynamic(arena, format!("v{}", i));
        let applied = expr_apply(
            encoder.clone(),
            vec![(ArgLabel::Nolabel, v_expr)],
            false,
            arena.dummy_loc(),
            arena,
        );
        arr_items.push(applied);
    }

    let arr_expr = expr_array(arr_items, arena);
    let json_array = expr_construct_with_loc(
        lident_path_static(arena, &["JSON", "Array"]),
        Some(arr_expr),
        arena.dummy_loc(),
        arena,
    );
    let json_t = ctyp_json_t_const(arena);
    let constrained = expr_constraint(json_array, json_t, arena);

    let mut pat_vars = Vec::with_capacity(composite_encoders.len());
    for i in 0..composite_encoders.len() {
        let v_loc = arena.none_loc();
        pat_vars.push(pat_var_dynamic(arena, &format!("v{}", i), v_loc));
    }
    let deconstructor = pat_tuple(pat_vars, arena);

    let fun_expr = expr_fun(
        ArgLabel::Nolabel,
        deconstructor,
        constrained,
        Some(1),
        arena,
    );
    fun_expr
}

fn tuple_generate_decode_success_case(num_args: usize, arena: &mut ParseArena) -> Case {
    let mut pats = Vec::with_capacity(num_args);
    for i in 0..num_args {
        let v_loc = arena.none_loc();
        let v_pat = pat_var_dynamic(arena, &format!("v{}", i), v_loc);
        let ok_lid = {
            let lident_name = arena.intern_string("Ok");
            arena.push_lident_from_idx(lident_name)
        };
        pats.push(pat_construct_with_loc(
            ok_lid,
            Some(v_pat),
            arena.dummy_loc(),
            arena,
        ));
    }
    let lhs = tuple_or_singleton_pat(pats, arena);

    let mut exprs = Vec::with_capacity(num_args);
    for i in 0..num_args {
        exprs.push(expr_ident_dynamic(arena, format!("v{}", i)));
    }
    let tuple = tuple_or_singleton_expr(exprs, arena);
    let ok_expr = expr_construct_with_loc(
        {
            let lident_name = arena.intern_string("Ok");
            arena.push_lident_from_idx(lident_name)
        },
        Some(tuple),
        arena.dummy_loc(),
        arena,
    );

    case(lhs, ok_expr, arena)
}

fn tuple_generate_decode_switch(
    composite_decoders: Vec<Expression>,
    arena: &mut ParseArena,
) -> Expression {
    let num_args = composite_decoders.len();
    let mut decode_exprs = Vec::with_capacity(num_args);
    for (i, decoder) in composite_decoders.iter().enumerate() {
        let v_expr = expr_ident_dynamic(arena, format!("v{}", i));
        let applied = expr_apply(
            decoder.clone(),
            vec![(ArgLabel::Nolabel, v_expr)],
            false,
            arena.dummy_loc(),
            arena,
        );
        decode_exprs.push(applied);
    }
    let tuple_expr = tuple_or_singleton_expr(decode_exprs, arena);

    let mut cases = Vec::new();
    cases.push(tuple_generate_decode_success_case(num_args, arena));
    for i in 0..num_args {
        cases.push(generate_error_case(num_args, i, false, arena));
    }

    expr_match(tuple_expr, cases, arena)
}

fn tuple_generate_decoder(
    composite_decoders: Vec<Expression>,
    arena: &mut ParseArena,
) -> Expression {
    let mut match_arr_vars = Vec::with_capacity(composite_decoders.len());
    for i in 0..composite_decoders.len() {
        let v_loc = arena.none_loc();
        match_arr_vars.push(pat_var_dynamic(arena, &format!("v{}", i), v_loc));
    }
    let array_pat = pat_array(match_arr_vars, arena);

    let json_array_pat = pat_construct_with_loc(
        lident_path_static(arena, &["JSON", "Array"]),
        Some(array_pat),
        arena.dummy_loc(),
        arena,
    );
    let json_array_any = pat_construct_with_loc(
        lident_path_static(arena, &["JSON", "Array"]),
        Some(pat_any(arena)),
        arena.dummy_loc(),
        arena,
    );

    let json_expr = expr_ident_path(arena, &["json"]);
    let constrained = expr_constraint(json_expr.clone(), ctyp_json_t_const(arena), arena);

    let mut cases = Vec::new();
    cases.push(case(
        json_array_pat,
        tuple_generate_decode_switch(composite_decoders, arena),
        arena,
    ));
    let incorrect_msg = expr_constant_literal(arena, "Incorrect cardinality");
    cases.push(case(
        json_array_any,
        expr_spice_error_tuple(arena, incorrect_msg, json_expr.clone(), None),
        arena,
    ));
    let not_tuple_msg = expr_constant_literal(arena, "Not a tuple");
    cases.push(case(
        pat_any(arena),
        expr_spice_error_tuple(arena, not_tuple_msg, json_expr, None),
        arena,
    ));

    let match_expr = expr_match(constrained, cases, arena);
    let json_loc = arena.dummy_loc();
    let fun_pat = pat_var(arena, "json", json_loc);
    expr_fun(ArgLabel::Nolabel, fun_pat, match_expr, Some(1), arena)
}

fn codecs_generate_constr_codecs(
    context: EncodeContext,
    settings: GeneratorSettings,
    lid: &Located<LidentIdx>,
    arena: &mut ParseArena,
) -> (Option<Expression>, Option<Expression>) {
    let do_encode = settings.do_encode;
    let do_decode = settings.do_decode;
    let lid_loc = lid.loc;

    let lid_idx = lid.txt;
    let encode = if do_encode {
        if longident_matches(arena, lid_idx, &["string"]) {
            Some(expr_ident_spice_codecs_with_loc(
                arena,
                "stringToJson",
                lid_loc,
            ))
        } else if longident_matches(arena, lid_idx, &["int"]) {
            Some(expr_ident_spice_codecs_with_loc(
                arena,
                "intToJson",
                lid_loc,
            ))
        } else if longident_matches(arena, lid_idx, &["bigint"]) {
            Some(expr_ident_spice_codecs_with_loc(
                arena,
                "bigintToJson",
                lid_loc,
            ))
        } else if longident_matches(arena, lid_idx, &["float"]) {
            Some(expr_ident_spice_codecs_with_loc(
                arena,
                "floatToJson",
                lid_loc,
            ))
        } else if longident_matches(arena, lid_idx, &["bool"]) {
            Some(expr_ident_spice_codecs_with_loc(
                arena,
                "boolToJson",
                lid_loc,
            ))
        } else if longident_matches(arena, lid_idx, &["unit"]) {
            Some(expr_ident_spice_codecs_with_loc(
                arena,
                "unitToJson",
                lid_loc,
            ))
        } else if longident_matches(arena, lid_idx, &["array"]) {
            Some(expr_ident_spice_codecs_with_loc(
                arena,
                "arrayToJson",
                lid_loc,
            ))
        } else if longident_matches(arena, lid_idx, &["list"]) {
            Some(expr_ident_spice_codecs_with_loc(
                arena,
                "listToJson",
                lid_loc,
            ))
        } else if longident_matches(arena, lid_idx, &["option"]) {
            let codec = match context {
                EncodeContext::Optional => "optionToJson",
                EncodeContext::Value => "optionToNullableJson",
            };
            Some(expr_ident_spice_codecs_with_loc(arena, codec, lid_loc))
        } else if longident_matches(arena, lid_idx, &["Js", "null"])
            || longident_matches(arena, lid_idx, &["Js", "Null", "t"])
            || longident_matches(arena, lid_idx, &["Null", "t"])
        {
            Some(expr_ident_spice_codecs_with_loc(
                arena,
                "nullToJson",
                lid_loc,
            ))
        } else if longident_matches(arena, lid_idx, &["result"])
            || longident_matches(arena, lid_idx, &["Result", "t"])
            || longident_matches(arena, lid_idx, &["Belt", "Result", "t"])
        {
            Some(expr_ident_spice_codecs_with_loc(
                arena,
                "resultToJson",
                lid_loc,
            ))
        } else if longident_matches(arena, lid_idx, &["dict"])
            || longident_matches(arena, lid_idx, &["Js", "Dict", "t"])
            || longident_matches(arena, lid_idx, &["Dict", "t"])
        {
            Some(expr_ident_spice_codecs_with_loc(
                arena,
                "dictToJson",
                lid_loc,
            ))
        } else if longident_matches(arena, lid_idx, &["Js", "Json", "t"])
            || longident_matches(arena, lid_idx, &["JSON", "t"])
        {
            let v_loc = lid_loc;
            let v_pat = pat_var_with_loc(arena, "v", v_loc);
            let v_expr = expr_ident_path_with_lid_loc(arena, &["v"], v_loc);
            Some(expr_fun_with_loc(
                ArgLabel::Nolabel,
                v_pat,
                v_expr,
                Some(1),
                v_loc,
                arena,
            ))
        } else {
            let lid = arena.get_longident(lid_idx).clone();
            match lid {
                Longident::Lident(s) => {
                    let name = arena.get_string(s);
                    let suffix = match context {
                        EncodeContext::Optional => ENCODER_FUNC_SUFFIX,
                        EncodeContext::Value => VALUE_ENCODER_FUNC_SUFFIX,
                    };
                    let new_name = format!("{}{}", name, suffix);
                    let idx = arena.push_string(new_name);
                    Some(expr_ident_from_str_idx(arena, idx, arena.none_loc()))
                }
                Longident::Ldot(prefix, right) => {
                    let right_name = arena.get_string(right);
                    let suffix = match context {
                        EncodeContext::Optional => ENCODER_FUNC_SUFFIX,
                        EncodeContext::Value => VALUE_ENCODER_FUNC_SUFFIX,
                    };
                    let new_name = format!("{}{}", right_name, suffix);
                    let new_idx = arena.push_string(new_name);
                    let new_lid = Longident::Ldot(prefix.clone(), new_idx);
                    let lid_idx = arena.push_longident(new_lid);
                    Some(expr_ident_with_loc(
                        lid_idx,
                        arena.none_loc(),
                        arena.dummy_loc(),
                    ))
                }
                Longident::Lapply(_, _) => None,
            }
        }
    } else {
        None
    };

    let decode = if do_decode {
        if longident_matches(arena, lid_idx, &["string"]) {
            Some(expr_ident_spice_codecs_with_loc(
                arena,
                "stringFromJson",
                lid_loc,
            ))
        } else if longident_matches(arena, lid_idx, &["int"]) {
            Some(expr_ident_spice_codecs_with_loc(
                arena,
                "intFromJson",
                lid_loc,
            ))
        } else if longident_matches(arena, lid_idx, &["bigint"]) {
            Some(expr_ident_spice_codecs_with_loc(
                arena,
                "bigintFromJson",
                lid_loc,
            ))
        } else if longident_matches(arena, lid_idx, &["float"]) {
            Some(expr_ident_spice_codecs_with_loc(
                arena,
                "floatFromJson",
                lid_loc,
            ))
        } else if longident_matches(arena, lid_idx, &["bool"]) {
            Some(expr_ident_spice_codecs_with_loc(
                arena,
                "boolFromJson",
                lid_loc,
            ))
        } else if longident_matches(arena, lid_idx, &["unit"]) {
            Some(expr_ident_spice_codecs_with_loc(
                arena,
                "unitFromJson",
                lid_loc,
            ))
        } else if longident_matches(arena, lid_idx, &["array"]) {
            Some(expr_ident_spice_codecs_with_loc(
                arena,
                "arrayFromJson",
                lid_loc,
            ))
        } else if longident_matches(arena, lid_idx, &["list"]) {
            Some(expr_ident_spice_codecs_with_loc(
                arena,
                "listFromJson",
                lid_loc,
            ))
        } else if longident_matches(arena, lid_idx, &["option"]) {
            Some(expr_ident_spice_codecs_with_loc(
                arena,
                "optionFromJson",
                lid_loc,
            ))
        } else if longident_matches(arena, lid_idx, &["Js", "null"])
            || longident_matches(arena, lid_idx, &["Js", "Null", "t"])
            || longident_matches(arena, lid_idx, &["Null", "t"])
        {
            Some(expr_ident_spice_codecs_with_loc(
                arena,
                "nullFromJson",
                lid_loc,
            ))
        } else if longident_matches(arena, lid_idx, &["result"])
            || longident_matches(arena, lid_idx, &["Result", "t"])
            || longident_matches(arena, lid_idx, &["Belt", "Result", "t"])
        {
            Some(expr_ident_spice_codecs_with_loc(
                arena,
                "resultFromJson",
                lid_loc,
            ))
        } else if longident_matches(arena, lid_idx, &["dict"])
            || longident_matches(arena, lid_idx, &["Js", "Dict", "t"])
            || longident_matches(arena, lid_idx, &["Dict", "t"])
        {
            Some(expr_ident_spice_codecs_with_loc(
                arena,
                "dictFromJson",
                lid_loc,
            ))
        } else if longident_matches(arena, lid_idx, &["Js", "Json", "t"])
            || longident_matches(arena, lid_idx, &["JSON", "t"])
        {
            let v_loc = lid_loc;
            let v_pat = pat_var_with_loc(arena, "v", v_loc);
            let v_expr = expr_ident_path_with_lid_loc(arena, &["v"], v_loc);
            let ok_expr = expr_construct_with_locs(
                {
                    let lident_name = arena.intern_string("Ok");
                    arena.push_lident_from_idx(lident_name)
                },
                Some(v_expr),
                v_loc,
                v_loc,
                arena,
            );
            Some(expr_fun_with_loc(
                ArgLabel::Nolabel,
                v_pat,
                ok_expr,
                Some(1),
                v_loc,
                arena,
            ))
        } else {
            let lid = arena.get_longident(lid_idx).clone();
            match lid {
                Longident::Lident(s) => {
                    let name = arena.get_string(s);
                    let new_name = format!("{}{}", name, DECODER_FUNC_SUFFIX);
                    let idx = arena.push_string(new_name);
                    Some(expr_ident_from_str_idx(arena, idx, arena.none_loc()))
                }
                Longident::Ldot(prefix, right) => {
                    let right_name = arena.get_string(right);
                    let new_name = format!("{}{}", right_name, DECODER_FUNC_SUFFIX);
                    let new_idx = arena.push_string(new_name);
                    let new_lid = Longident::Ldot(prefix.clone(), new_idx);
                    let lid_idx = arena.push_longident(new_lid);
                    Some(expr_ident_with_loc(
                        lid_idx,
                        arena.none_loc(),
                        arena.dummy_loc(),
                    ))
                }
                Longident::Lapply(_, _) => None,
            }
        }
    } else {
        None
    };

    (encode, decode)
}

fn codecs_parameterize_codecs(
    type_args: &[CoreTypeIdx],
    encoder_func: Option<Expression>,
    decoder_func: Option<Expression>,
    settings: GeneratorSettings,
    arena: &mut ParseArena,
) -> SpiceResult<(Option<Expression>, Option<Expression>)> {
    let type_args_resolved: Vec<CoreType> = type_args
        .iter()
        .map(|idx| arena.get_core_type(*idx).clone())
        .collect();
    let mut sub_encoders = Vec::new();
    let mut sub_decoders = Vec::new();
    for typ in type_args_resolved.iter() {
        let (enc, dec) = codecs_generate_codecs_for(EncodeContext::Value, settings, typ, arena)?;
        sub_encoders.push(enc);
        sub_decoders.push(dec);
    }

    let encoder = match encoder_func {
        None => None,
        Some(func) => {
            let mut args = Vec::new();
            for e in sub_encoders.into_iter() {
                let enc = require_encoder(e)?;
                args.push((ArgLabel::Nolabel, enc));
            }
            Some(expr_apply(func, args, true, arena.dummy_loc(), arena))
        }
    };

    let decoder = match decoder_func {
        None => None,
        Some(func) => {
            let mut args = Vec::new();
            for d in sub_decoders.into_iter() {
                let dec = require_decoder(d)?;
                args.push((ArgLabel::Nolabel, dec));
            }
            Some(expr_apply(func, args, true, arena.dummy_loc(), arena))
        }
    };

    Ok((encoder, decoder))
}

fn codecs_generate_codecs_for(
    context: EncodeContext,
    settings: GeneratorSettings,
    typ_ref: &CoreType,
    arena: &mut ParseArena,
) -> SpiceResult<(Option<Expression>, Option<Expression>)> {
    // Note: typ_ref may be either a directly-passed CoreType or one obtained from the arena.
    // All sub-types inside it that are indices need to be resolved through the arena.
    let typ = typ_ref;
    match &*typ.ptyp_desc {
        CoreTypeDesc::Ptyp_any => Err(spice_error("Can't generate codecs for `any` type")),
        CoreTypeDesc::Ptyp_arrow(inner) => {
            let (..) = **inner;
            Err(spice_error("Can't generate codecs for function type"))
        }
        CoreTypeDesc::Ptyp_package(_) => Err(spice_error("Can't generate codecs for module type")),
        CoreTypeDesc::Ptyp_tuple(types) => {
            let types_vec: Vec<CoreType> = types
                .iter()
                .map(|t| arena.get_core_type(*t).clone())
                .collect();
            let mut encoders = Vec::new();
            let mut decoders = Vec::new();
            for t in types_vec.iter() {
                let (enc, dec) =
                    codecs_generate_codecs_for(EncodeContext::Value, settings, t, arena)?;
                if settings.do_encode {
                    encoders.push(require_encoder(enc)?);
                }
                if settings.do_decode {
                    decoders.push(require_decoder(dec)?);
                }
            }
            let encoder = if settings.do_encode {
                Some(tuple_generate_encoder(encoders, arena))
            } else {
                None
            };
            let decoder = if settings.do_decode {
                Some(tuple_generate_decoder(decoders, arena))
            } else {
                None
            };
            Ok((encoder, decoder))
        }
        CoreTypeDesc::Ptyp_var(name) => Ok((
            if settings.do_encode {
                Some(expr_ident_dynamic(
                    arena,
                    format!("{}{}", ENCODER_VAR_PREFIX, name),
                ))
            } else {
                None
            },
            if settings.do_decode {
                Some(expr_ident_dynamic(
                    arena,
                    format!("{}{}", DECODER_VAR_PREFIX, name),
                ))
            } else {
                None
            },
        )),
        CoreTypeDesc::Ptyp_constr(inner) => {
            let (ref constr, ref type_args) = **inner;
            let custom_codec = get_attribute_by_name(&typ.ptyp_attributes, "spice.codec", arena);
            let (encode, decode) = match custom_codec {
                Ok(Some(attr)) => {
                    let expr = get_expression_from_payload(attr, arena)?;
                    let encode_expr = if settings.do_encode {
                        let e_loc = arena.dummy_loc();
                        let e_pat = pat_var(arena, "e", e_loc);
                        let pat = pat_tuple(vec![e_pat, pat_any(arena)], arena);
                        let vb = ValueBinding {
                            pvb_pat: arena.push_pat(pat),
                            pvb_expr: arena.push_expr(expr.clone()),
                            pvb_attributes: Attributes::new(),
                            pvb_loc: arena.dummy_loc(),
                        };
                        let body = expr_ident_path(arena, &["e"]);
                        Some(expr_let(RecFlag::Nonrecursive, vec![vb], body, arena))
                    } else {
                        None
                    };
                    let decode_expr = if settings.do_decode {
                        let d_loc = arena.dummy_loc();
                        let d_pat = pat_var(arena, "d", d_loc);
                        let pat = pat_tuple(vec![pat_any(arena), d_pat], arena);
                        let vb = ValueBinding {
                            pvb_pat: arena.push_pat(pat),
                            pvb_expr: arena.push_expr(expr),
                            pvb_attributes: Attributes::new(),
                            pvb_loc: arena.dummy_loc(),
                        };
                        let body = expr_ident_path(arena, &["d"]);
                        Some(expr_let(RecFlag::Nonrecursive, vec![vb], body, arena))
                    } else {
                        None
                    };
                    (encode_expr, decode_expr)
                }
                Ok(None) => codecs_generate_constr_codecs(context, settings, constr, arena),
                Err(e) => return Err(e),
            };

            if type_args.is_empty() {
                Ok((encode, decode))
            } else {
                codecs_parameterize_codecs(type_args, encode, decode, settings, arena)
            }
        }
        _ => Err(spice_error("This syntax is not yet handled by spice")),
    }
}

fn codecs_generate_codecs(
    settings: GeneratorSettings,
    typ: &CoreType,
    arena: &mut ParseArena,
) -> SpiceResult<(Option<Expression>, Option<Expression>)> {
    codecs_generate_codecs_for(EncodeContext::Optional, settings, typ, arena)
}

fn codecs_generate_value_codecs(
    settings: GeneratorSettings,
    typ: &CoreType,
    arena: &mut ParseArena,
) -> SpiceResult<(Option<Expression>, Option<Expression>)> {
    codecs_generate_codecs_for(EncodeContext::Value, settings, typ, arena)
}

fn records_make_omittable_codecs(
    codecs: (Option<Expression>, Option<Expression>),
    arena: &mut ParseArena,
) -> (Option<Expression>, Option<Expression>) {
    let encode = codecs.0.map(|encoder| {
        expr_apply(
            expr_ident_spice_records(arena, "optionToJson"),
            vec![(ArgLabel::Nolabel, encoder)],
            true,
            arena.dummy_loc(),
            arena,
        )
    });
    let decode = codecs.1.map(|decoder| {
        expr_apply(
            expr_ident_spice_records(arena, "optionalFieldFromJson"),
            vec![(ArgLabel::Nolabel, decoder)],
            true,
            arena.dummy_loc(),
            arena,
        )
    });
    (encode, decode)
}

fn records_parse_decl(
    settings: GeneratorSettings,
    decl: &LabelDeclaration,
    arena: &mut ParseArena,
) -> SpiceResult<ParsedRecordField> {
    let default = match get_attribute_by_name(&decl.pld_attributes, "spice.default", arena) {
        Ok(Some(attr)) => Some(get_expression_from_payload(attr, arena)?),
        Ok(None) => None,
        Err(e) => return Err(e),
    };

    let (key, key_identity) = match get_attribute_by_name(&decl.pld_attributes, "spice.key", arena)
    {
        Ok(Some(attr)) => (get_expression_from_payload(attr, arena)?, None),
        Ok(None) => {
            let name_idx = decl.pld_name.txt;
            let name = extend_cow_lifetime(Cow::Borrowed(arena.get_string(name_idx)));
            arena.register_shareable_literal(name.as_ref());
            arena.register_constant_string_identity(name.as_ref(), name_idx);
            (
                expr_constant(Constant::string(&name), arena),
                Some(name_idx),
            )
        }
        Err(e) => return Err(e),
    };

    let optional_attr_names = ["ns.optional", "res.optional"];
    let mut is_optional = decl.pld_optional;
    if !is_optional {
        for attr_name in &optional_attr_names {
            if get_attribute_by_name(&decl.pld_attributes, attr_name, arena)?.is_some() {
                is_optional = true;
                break;
            }
        }
    }

    let is_option = check_option_type(&decl.pld_type, arena);

    let pld_type = arena.get_core_type(decl.pld_type).clone();
    let codecs = if is_optional {
        let codecs = codecs_generate_value_codecs(settings, &pld_type, arena)?;
        records_make_omittable_codecs(codecs, arena)
    } else if is_option {
        match &*pld_type.ptyp_desc {
            CoreTypeDesc::Ptyp_constr(inner) => {
                let (_, args) = &**inner;
                let inner_type = arena.get_core_type(args[0]).clone();
                let codecs = codecs_generate_value_codecs(settings, &inner_type, arena)?;
                records_make_omittable_codecs(codecs, arena)
            }
            _ => unreachable!("option type must be a type constructor"),
        }
    } else {
        codecs_generate_value_codecs(settings, &pld_type, arena)?
    };

    Ok(ParsedRecordField {
        name: decl.pld_name.txt,
        key,
        key_identity,
        codecs,
        default,
        is_optional,
        is_option,
    })
}

fn clone_record_key(field: &ParsedRecordField, arena: &mut ParseArena) -> Expression {
    let key = field.key.clone();
    if let (Some(identity), ExpressionDesc::Pexp_constant(constant)) =
        (field.key_identity, &*key.pexp_desc)
        && let Constant::String(value) = &**constant
    {
        arena.register_constant_string_identity(value.semantic(), identity);
    }
    key
}

fn records_generate_encoder(
    fields: &[ParsedRecordField],
    unboxed: bool,
    arena: &mut ParseArena,
) -> SpiceResult<Expression> {
    let field_v_idx = arena.spice_field_v();
    let field_v_loc = arena.dummy_loc();
    let v_pat = pat_var_idx(arena, field_v_idx, field_v_loc);

    if unboxed {
        let field = fields
            .first()
            .ok_or_else(|| spice_error("Internal spice error: missing field"))?;
        let encoder = require_encoder(field.codecs.0.clone())?;
        let name_str = arena.get_string(field.name).to_string();
        let name_slice = [name_str.as_str()];
        let field_lid = lident_path_parse(arena, &name_slice);
        let field_v_expr = expr_ident_from_str_idx(arena, field_v_idx, field_v_loc);
        let field_expr = expr_field(field_v_expr, field_lid, arena);
        let applied = expr_apply(
            encoder,
            vec![(ArgLabel::Nolabel, field_expr)],
            false,
            arena.dummy_loc(),
            arena,
        );
        return Ok(expr_fun(ArgLabel::Nolabel, v_pat, applied, Some(1), arena));
    }

    let mut arr_items = Vec::with_capacity(fields.len());
    for field in fields {
        let encoder = require_encoder(field.codecs.0.clone())?;
        let name_str = arena.get_string(field.name).to_string();
        let name_slice = [name_str.as_str()];
        let field_lid = lident_path_parse(arena, &name_slice);
        let field_v_expr = expr_ident_from_str_idx(arena, field_v_idx, field_v_loc);
        let field_expr = expr_field(field_v_expr, field_lid, arena);
        let encoded = expr_apply(
            encoder,
            vec![(ArgLabel::Nolabel, field_expr)],
            false,
            arena.dummy_loc(),
            arena,
        );
        let tuple_expr = if field.is_optional || field.is_option {
            expr_tuple(vec![clone_record_key(field, arena), encoded], arena)
        } else {
            let some_expr = expr_construct_with_loc(
                {
                    let lident_name = arena.intern_string("Some");
                    arena.push_lident_from_idx(lident_name)
                },
                Some(encoded),
                arena.dummy_loc(),
                arena,
            );
            expr_tuple(vec![clone_record_key(field, arena), some_expr], arena)
        };
        arr_items.push(tuple_expr);
    }

    let arr_expr = expr_array(arr_items, arena);
    let filtered = expr_apply(
        expr_ident_spice_records(arena, "filterOptional"),
        vec![(ArgLabel::Nolabel, arr_expr)],
        false,
        arena.dummy_loc(),
        arena,
    );
    let dict_from_array = expr_apply(
        expr_ident_path(arena, &["Dict", "fromArray"]),
        vec![(ArgLabel::Nolabel, filtered)],
        false,
        arena.dummy_loc(),
        arena,
    );
    let json_object = expr_construct_with_loc(
        lident_path_static(arena, &["JSON", "Object"]),
        Some(dict_from_array),
        arena.dummy_loc(),
        arena,
    );
    let constrained = expr_constraint(json_object, ctyp_json_t_const(arena), arena);

    Ok(expr_fun(
        ArgLabel::Nolabel,
        v_pat,
        constrained,
        Some(1),
        arena,
    ))
}

fn records_generate_flat_decoder_expr(
    fields: &[ParsedRecordField],
    constructor_name: Option<StrIdx>,
    arena: &mut ParseArena,
) -> Expression {
    let dict_expr = expr_ident_path_mknoloc(arena, &["dict"]);
    let v_idx = arena.spice_field_v();
    arena.register_shareable_literal(" missing");

    let mut decode_exprs: Vec<Expression> = Vec::with_capacity(fields.len());

    for field in fields {
        let decode_expr = match &field.codecs.1 {
            Some(decode) => {
                let get_expr = expr_apply(
                    expr_ident_path(arena, &["Dict", "get"]),
                    vec![
                        (ArgLabel::Nolabel, dict_expr.clone()),
                        (ArgLabel::Nolabel, clone_record_key(field, arena)),
                    ],
                    false,
                    arena.dummy_loc(),
                    arena,
                );
                let decode_applied = decode.clone();
                let opt_map = expr_apply(
                    expr_ident_path(arena, &["Option", "map"]),
                    vec![
                        (ArgLabel::Nolabel, get_expr),
                        (ArgLabel::Nolabel, decode_applied),
                    ],
                    false,
                    arena.dummy_loc(),
                    arena,
                );

                let default_expr = if field.is_optional {
                    match &field.default {
                        Some(d) => expr_apply(
                            expr_ident_path(arena, &["Option", "getOr"]),
                            vec![
                                (ArgLabel::Nolabel, opt_map.clone()),
                                (
                                    ArgLabel::Nolabel,
                                    expr_construct_with_loc(
                                        {
                                            let lident_name = arena.intern_string("Ok");
                                            arena.push_lident_from_idx(lident_name)
                                        },
                                        Some(d.clone()),
                                        arena.dummy_loc(),
                                        arena,
                                    ),
                                ),
                            ],
                            false,
                            arena.dummy_loc(),
                            arena,
                        ),
                        None => {
                            let ok_none = expr_construct_with_loc(
                                {
                                    let lident_name = arena.intern_string("Ok");
                                    arena.push_lident_from_idx(lident_name)
                                },
                                Some(expr_construct_with_loc(
                                    {
                                        let lident_name = arena.intern_string("None");
                                        arena.push_lident_from_idx(lident_name)
                                    },
                                    None,
                                    arena.dummy_loc(),
                                    arena,
                                )),
                                arena.dummy_loc(),
                                arena,
                            );
                            expr_apply(
                                expr_ident_path(arena, &["Option", "getOr"]),
                                vec![
                                    (ArgLabel::Nolabel, opt_map.clone()),
                                    (ArgLabel::Nolabel, ok_none),
                                ],
                                false,
                                arena.dummy_loc(),
                                arena,
                            )
                        }
                    }
                } else if field.is_option {
                    let fallback = match &field.default {
                        Some(d) => d.clone(),
                        None => expr_construct_with_loc(
                            {
                                let lident_name = arena.intern_string("None");
                                arena.push_lident_from_idx(lident_name)
                            },
                            None,
                            arena.dummy_loc(),
                            arena,
                        ),
                    };
                    let ok_default = expr_construct_with_loc(
                        {
                            let lident_name = arena.intern_string("Ok");
                            arena.push_lident_from_idx(lident_name)
                        },
                        Some(fallback),
                        arena.dummy_loc(),
                        arena,
                    );
                    expr_apply(
                        expr_ident_path(arena, &["Option", "getOr"]),
                        vec![
                            (ArgLabel::Nolabel, opt_map.clone()),
                            (ArgLabel::Nolabel, ok_default),
                        ],
                        false,
                        arena.dummy_loc(),
                        arena,
                    )
                } else if let Some(d) = &field.default {
                    let ok_default = expr_construct_with_loc(
                        {
                            let lident_name = arena.intern_string("Ok");
                            arena.push_lident_from_idx(lident_name)
                        },
                        Some(d.clone()),
                        arena.dummy_loc(),
                        arena,
                    );
                    expr_apply(
                        expr_ident_path(arena, &["Option", "getOr"]),
                        vec![
                            (ArgLabel::Nolabel, opt_map.clone()),
                            (ArgLabel::Nolabel, ok_default),
                        ],
                        false,
                        arena.dummy_loc(),
                        arena,
                    )
                } else {
                    let missing =
                        expr_constant(Constant::string(" missing"), arena);
                    let key = clone_record_key(field, arena);
                    let msg = expr_concat(arena, key, missing);
                    let v_loc = arena.dummy_loc();
                    let v_expr = expr_ident_from_str_idx(arena, v_idx, v_loc);
                    let err_expr = expr_spice_error_records(arena, msg, v_expr, None);
                    expr_apply(
                        expr_ident_path(arena, &["Option", "getOr"]),
                        vec![
                            (ArgLabel::Nolabel, opt_map.clone()),
                            (ArgLabel::Nolabel, err_expr),
                        ],
                        false,
                        arena.dummy_loc(),
                        arena,
                    )
                };

                default_expr
            }
            None => {
                let missing =
                    expr_constant(Constant::string(" missing"), arena);
                let key = clone_record_key(field, arena);
                let msg = expr_concat(arena, key, missing);
                let v_loc = arena.dummy_loc();
                let v_expr = expr_ident_from_str_idx(arena, v_idx, v_loc);
                expr_spice_error_records(arena, msg, v_expr, None)
            }
        };

        decode_exprs.push(decode_expr);
    }

    let mut record_fields = Vec::with_capacity(fields.len());
    for field in fields {
        let name_str = arena.get_string(field.name).to_string();
        let name_slice = [name_str.as_str()];
        let lid = lident_path_parse(arena, &name_slice);
        let expr = expr_ident_path_dynamic_mknoloc(arena, &name_slice);
        record_fields.push(ExpressionRecordField {
            lid: Located::new(lid, arena.none_loc()),
            expr: arena.push_expr(expr),
            opt: field.is_optional,
        });
    }
    let record = expr_record(record_fields, None, arena);
    let decoded = match constructor_name {
        Some(name) => expr_construct(arena.push_lident_from_idx(name), Some(record), arena),
        None => record,
    };
    let ok_expr = expr_construct_with_loc(
        {
            let lident_name = arena.intern_string("Ok");
            arena.push_lident_from_idx(lident_name)
        },
        Some(decoded),
        arena.dummy_loc(),
        arena,
    );
    let mut acc = ok_expr;
    for (field, decode_expr) in fields.iter().zip(decode_exprs.into_iter()).rev() {
        let ok_pat = pat_construct_with_loc(
            {
                let lident_name = arena.intern_string("Ok");
                arena.push_lident_from_idx(lident_name)
            },
            Some(pat_var_idx(arena, field.name, arena.none_loc())),
            arena.none_loc(),
            arena,
        );
        let e_pat = pat_var(arena, "e", arena.none_loc());
        let decode_error_type = mk_type_constr(
            lident_path_parse(arena, &["Spice", "decodeError"]),
            vec![],
            arena,
        );
        let err_pat = pat_constraint(e_pat, decode_error_type, arena);
        let err_pat = pat_construct_with_loc(
            {
                let lident_name = arena.intern_string("Error");
                arena.push_lident_from_idx(lident_name)
            },
            Some(err_pat),
            arena.none_loc(),
            arena,
        );

        let e_expr = expr_ident_path(arena, &["e"]);
        let msg_expr = expr_field_with_loc(
            e_expr.clone(),
            {
                let lident_name = arena.intern_string("message");
                arena.push_lident_from_idx(lident_name)
            },
            arena.dummy_loc(),
            arena,
        );
        let val_expr = expr_field_with_loc(
            e_expr.clone(),
            {
                let lident_name = arena.intern_string("value");
                arena.push_lident_from_idx(lident_name)
            },
            arena.dummy_loc(),
            arena,
        );
        let field_key = clone_record_key(field, arena);
        let error_path = expr_field_with_loc(
            e_expr,
            {
                let lident_name = arena.intern_string("path");
                arena.push_lident_from_idx(lident_name)
            },
            arena.dummy_loc(),
            arena,
        );
        let nested_path = expr_concat(arena, field_key, error_path);
        let dot = expr_constant_literal(arena, ".");
        let error_path = expr_concat(arena, dot, nested_path);
        let err_rhs = expr_spice_error_records(arena, msg_expr, val_expr, Some(error_path));

        acc = expr_match(
            decode_expr,
            vec![case(ok_pat, acc, arena), case(err_pat, err_rhs, arena)],
            arena,
        );
    }

    acc
}

fn records_generate_decoder(
    fields: &[ParsedRecordField],
    unboxed: bool,
    arena: &mut ParseArena,
) -> SpiceResult<Expression> {
    if unboxed {
        let field = fields
            .first()
            .ok_or_else(|| spice_error("Internal spice error: missing field"))?;
        let decoder = require_decoder(field.codecs.1.clone())?;

        let map_v_idx = arena.spice_field_v();
        let map_v_loc = arena.dummy_loc();
        let map_v_pat = pat_var_idx(arena, map_v_idx, map_v_loc);

        let name_str = arena.get_string(field.name).to_string();
        let name_slice = [name_str.as_str()];
        let field_lid = lident_path_parse(arena, &name_slice);
        let v_expr = make_ident_expr(arena, "v");
        let record_fields = vec![ExpressionRecordField {
            lid: Located::new(field_lid, arena.none_loc()),
            expr: arena.push_expr(v_expr),
            opt: field.is_optional,
        }];
        let record_expr = expr_record(record_fields, None, arena);

        let inner_fun = expr_fun(ArgLabel::Nolabel, map_v_pat, record_expr, Some(1), arena);
        let map_expr = expr_apply(
            expr_ident_path(arena, &["Result", "map"]),
            vec![
                (
                    ArgLabel::Nolabel,
                    expr_apply(
                        decoder,
                        vec![(
                            ArgLabel::Nolabel,
                            expr_ident_from_str_idx(arena, map_v_idx, map_v_loc),
                        )],
                        false,
                        arena.dummy_loc(),
                        arena,
                    ),
                ),
                (ArgLabel::Nolabel, inner_fun),
            ],
            false,
            arena.dummy_loc(),
            arena,
        );
        return Ok(expr_fun(
            ArgLabel::Nolabel,
            pat_var_idx(arena, map_v_idx, map_v_loc),
            map_expr,
            Some(1),
            arena,
        ));
    }

    let v_idx = arena.spice_field_v();
    let v_loc = arena.dummy_loc();
    let v_pat = pat_var_idx(arena, v_idx, v_loc);
    let json_expr = expr_ident_from_str_idx(arena, v_idx, v_loc);
    let json_obj_pat = pat_construct_with_loc(
        lident_path_static(arena, &["JSON", "Object"]),
        Some(pat_var_dummy(arena, "dict")),
        arena.dummy_loc(),
        arena,
    );
    let not_object = expr_constant_literal(arena, "Not an object");
    let error_expr = expr_spice_error_records(arena, not_object, json_expr.clone(), None);

    let match_expr = expr_match(
        expr_constraint(json_expr.clone(), ctyp_json_t(arena), arena),
        vec![
            case(
                json_obj_pat,
                records_generate_flat_decoder_expr(fields, None, arena),
                arena,
            ),
            case(pat_any(arena), error_expr, arena),
        ],
        arena,
    );

    Ok(expr_fun(
        ArgLabel::Nolabel,
        v_pat,
        match_expr,
        Some(1),
        arena,
    ))
}

fn records_generate_codecs(
    settings: GeneratorSettings,
    decls: &[LabelDeclaration],
    unboxed: bool,
    arena: &mut ParseArena,
) -> SpiceResult<(Option<Expression>, Option<Expression>)> {
    let parsed: Vec<ParsedRecordField> = decls
        .iter()
        .map(|d| records_parse_decl(settings, d, arena))
        .collect::<Result<Vec<_>, _>>()?;

    let encoder = if settings.do_encode {
        Some(records_generate_encoder(&parsed, unboxed, arena)?)
    } else {
        None
    };
    let decoder = if settings.do_decode {
        Some(records_generate_decoder(&parsed, unboxed, arena)?)
    } else {
        None
    };
    Ok((encoder, decoder))
}

fn records_generate_inline_encoder_expr(
    settings: GeneratorSettings,
    decls: &[LabelDeclaration],
    arena: &mut ParseArena,
) -> SpiceResult<Expression> {
    let fields = decls
        .iter()
        .map(|decl| records_parse_decl(settings, decl, arena))
        .collect::<Result<Vec<_>, _>>()?;
    let mut arr_items = Vec::with_capacity(fields.len());
    for field in &fields {
        let encoder = require_encoder(field.codecs.0.clone())?;
        let field_expr = expr_ident_from_str_idx(arena, field.name, arena.dummy_loc());
        let encoded = expr_apply(
            encoder,
            vec![(ArgLabel::Nolabel, field_expr)],
            false,
            arena.dummy_loc(),
            arena,
        );
        let value = if field.is_optional || field.is_option {
            encoded
        } else {
            expr_construct_with_loc(
                {
                    let lident_name = arena.intern_string("Some");
                    arena.push_lident_from_idx(lident_name)
                },
                Some(encoded),
                arena.dummy_loc(),
                arena,
            )
        };
        let key = clone_record_key(field, arena);
        arr_items.push(expr_tuple(vec![key, value], arena));
    }

    let arr_expr = expr_array(arr_items, arena);
    let filtered = expr_apply(
        expr_ident_spice_records(arena, "filterOptional"),
        vec![(ArgLabel::Nolabel, arr_expr)],
        false,
        arena.dummy_loc(),
        arena,
    );
    let dict = expr_apply(
        expr_ident_path(arena, &["Dict", "fromArray"]),
        vec![(ArgLabel::Nolabel, filtered)],
        false,
        arena.dummy_loc(),
        arena,
    );
    let object = expr_construct_with_loc(
        lident_path_static(arena, &["JSON", "Object"]),
        Some(dict),
        arena.dummy_loc(),
        arena,
    );
    Ok(expr_constraint(object, ctyp_json_t_const(arena), arena))
}

fn records_generate_inline_decoder_expr(
    settings: GeneratorSettings,
    decls: &[LabelDeclaration],
    constructor_name: StrIdx,
    arena: &mut ParseArena,
) -> SpiceResult<Expression> {
    let fields = decls
        .iter()
        .map(|decl| records_parse_decl(settings, decl, arena))
        .collect::<Result<Vec<_>, _>>()?;
    Ok(records_generate_flat_decoder_expr(
        &fields,
        Some(constructor_name),
        arena,
    ))
}

fn variants_prefix_inline_payload_error(decoded: Expression, arena: &mut ParseArena) -> Expression {
    let ok_pattern = pat_construct_with_loc(
        {
            let name = arena.intern_string("Ok");
            arena.push_lident_from_idx(name)
        },
        Some(pat_var_dummy(arena, "v")),
        arena.dummy_loc(),
        arena,
    );
    let ok_value = expr_construct_with_loc(
        {
            let name = arena.intern_string("Ok");
            arena.push_lident_from_idx(name)
        },
        Some(expr_ident_path(arena, &["v"])),
        arena.dummy_loc(),
        arena,
    );

    let error_pattern = pat_constraint(
        pat_var_dummy(arena, "e"),
        mk_type_constr(
            lident_path_parse(arena, &["Spice", "decodeError"]),
            vec![],
            arena,
        ),
        arena,
    );
    let error_pattern = pat_construct_with_loc(
        {
            let name = arena.intern_string("Error");
            arena.push_lident_from_idx(name)
        },
        Some(error_pattern),
        arena.dummy_loc(),
        arena,
    );
    let e_value = expr_ident_path(arena, &["e"]);
    let previous_path = expr_field_with_loc(
        e_value.clone(),
        {
            let name = arena.intern_string("path");
            arena.push_lident_from_idx(name)
        },
        arena.dummy_loc(),
        arena,
    );
    arena.register_shareable_literal("[1]");
    let index = expr_constant(
        Constant::string("[1]"),
        arena,
    );
    let path = expr_concat(arena, index, previous_path);
    let path_lid = {
        let name = arena.intern_string("path");
        arena.push_lident_from_idx(name)
    };
    let error_record = expr_record(
        vec![ExpressionRecordField {
            lid: Located::new(path_lid, arena.none_loc()),
            expr: arena.push_expr(path),
            opt: false,
        }],
        Some(e_value),
        arena,
    );
    let error_value = expr_construct_with_loc(
        {
            let name = arena.intern_string("Error");
            arena.push_lident_from_idx(name)
        },
        Some(error_record),
        arena.dummy_loc(),
        arena,
    );

    expr_match(
        decoded,
        vec![
            case(ok_pattern, ok_value, arena),
            case(error_pattern, error_value, arena),
        ],
        arena,
    )
}

fn variants_parse_decl(
    decl: &crate::parser::ast::ConstructorDeclaration,
    arena: &mut ParseArena,
) -> SpiceResult<ParsedVariantDecl> {
    let name = decl.pcd_name.txt;
    let name_literal = name;
    let (alias, has_attr_as) = match get_attribute_by_name(&decl.pcd_attributes, "spice.as", arena)
    {
        Ok(Some(attr)) => (get_expression_from_payload(attr, arena)?, true),
        Ok(None) => {
            let name_str = extend_cow_lifetime(Cow::Borrowed(arena.get_string(name_literal)));
            arena.register_constant_string_identity(name_str.as_ref(), name_literal);
            (
                expr_constant(Constant::string(&name_str), arena),
                false,
            )
        }
        Err(e) => return Err(e),
    };

    Ok(ParsedVariantDecl {
        name,
        name_literal,
        alias,
        has_attr_as,
        constr_decl: decl.clone(),
    })
}

fn variants_generate_encoder_case(
    settings: GeneratorSettings,
    unboxed: bool,
    has_attr_as: bool,
    decl: &ParsedVariantDecl,
    arena: &mut ParseArena,
) -> SpiceResult<Case> {
    let pcd_loc = arena.clone_loc(decl.constr_decl.pcd_loc);

    let json_expr = match &*decl.alias.pexp_desc {
        ExpressionDesc::Pexp_constant(constant) => match &**constant {
            Constant::String(_) => expr_construct_with_loc(
                lident_path_static(arena, &["JSON", "String"]),
                Some(decl.alias.clone()),
                arena.dummy_loc(),
                arena,
            ),
            Constant::Float(_, _) | Constant::Integer(_, _) => expr_construct_with_loc(
                lident_path_static(arena, &["JSON", "Number"]),
                Some(decl.alias.clone()),
                arena.dummy_loc(),
                arena,
            ),
            _ => return Err(spice_error("cannot find a name??!")),
        },
        _ => return Err(spice_error("cannot find a name???")),
    };

    let (lhs_vars, rhs) = match &decl.constr_decl.pcd_args {
        crate::parser::ast::ConstructorArguments::Pcstr_tuple(args) => {
            let lhs_vars = match args.len() {
                0 => None,
                1 => Some(pat_var_none(arena, "v0")),
                _ => {
                    let mut vars = Vec::with_capacity(args.len());
                    for i in 0..args.len() {
                        vars.push(pat_var_dynamic(arena, &format!("v{}", i), pcd_loc));
                    }
                    Some(pat_tuple(vars, arena))
                }
            };

            let args_resolved: Vec<CoreType> = args
                .iter()
                .map(|idx| arena.get_core_type(*idx).clone())
                .collect();
            let mut rhs_list = Vec::new();
            rhs_list.push(json_expr.clone());
            for (i, arg) in args_resolved.iter().enumerate() {
                let (enc, _) = codecs_generate_value_codecs(settings, arg, arena)?;
                let encoder = require_encoder(enc)?;
                let v_expr = expr_ident_dynamic(arena, format!("v{}", i));
                let applied = expr_apply(
                    encoder,
                    vec![(ArgLabel::Nolabel, v_expr)],
                    false,
                    pcd_loc,
                    arena,
                );
                rhs_list.push(applied);
            }

            let rhs = if unboxed {
                rhs_list
                    .get(1)
                    .cloned()
                    .unwrap_or_else(|| json_expr.clone())
            } else if has_attr_as {
                json_expr.clone()
            } else {
                let arr = expr_array(rhs_list, arena);
                expr_construct_with_loc(
                    lident_path_static(arena, &["JSON", "Array"]),
                    Some(arr),
                    arena.dummy_loc(),
                    arena,
                )
            };
            (lhs_vars, rhs)
        }
        crate::parser::ast::ConstructorArguments::Pcstr_record(fields) => {
            let mut pattern_fields = Vec::with_capacity(fields.len());
            for field in fields {
                let field_name = field.pld_name.txt;
                let variable = pat_var_idx(arena, field_name, field.pld_name.loc);
                pattern_fields.push(PatternRecordField {
                    lid: Located::new(arena.push_lident_from_idx(field_name), field.pld_name.loc),
                    pat: arena.push_pat(variable),
                    opt: field.pld_optional,
                });
            }
            let payload_pattern = Pattern {
                ppat_desc: Box::new(PatternDesc::Ppat_record(Box::new((
                    pattern_fields,
                    ClosedFlag::Closed,
                    None,
                )))),
                ppat_loc: pcd_loc,
                ppat_attributes: Attributes::new(),
            };
            let payload = records_generate_inline_encoder_expr(settings, fields, arena)?;
            let rhs = if unboxed {
                payload.clone()
            } else if has_attr_as {
                json_expr.clone()
            } else {
                let arr = expr_array(vec![json_expr.clone(), payload], arena);
                expr_construct_with_loc(
                    lident_path_static(arena, &["JSON", "Array"]),
                    Some(arr),
                    arena.dummy_loc(),
                    arena,
                )
            };
            (Some(payload_pattern), rhs)
        }
    };

    let constructor_name = arena.get_string(decl.constr_decl.pcd_name.txt).to_string();
    let constructor_name_idx = arena.push_string(constructor_name);
    let pat = pat_construct(
        arena.push_lident_from_idx(constructor_name_idx),
        lhs_vars,
        arena,
    );

    Ok(Case {
        pc_bar: None,
        pc_lhs: arena.push_pat(pat),
        pc_guard: None,
        pc_rhs: arena.push_expr(rhs),
    })
}

fn variants_generate_decode_success_case(
    num_args: usize,
    constructor_name: StrIdx,
    arena: &mut ParseArena,
) -> Case {
    let mut pats = Vec::with_capacity(num_args);
    for i in 0..num_args {
        let v_pat = pat_var_dynamic(arena, &format!("v{}", i), arena.none_loc());
        pats.push(pat_construct_with_loc(
            {
                let lident_name = arena.intern_string("Ok");
                arena.push_lident_from_idx(lident_name)
            },
            Some(v_pat),
            arena.dummy_loc(),
            arena,
        ));
    }
    let lhs = tuple_or_singleton_pat(pats, arena);

    let mut exprs = Vec::with_capacity(num_args);
    for i in 0..num_args {
        exprs.push(expr_ident_dynamic(arena, format!("v{}", i)));
    }
    let payload = tuple_or_singleton_expr(exprs, arena);
    let constructor_name = arena.get_string(constructor_name).to_string();
    let constructor_name_idx = arena.push_string(constructor_name);
    let ctor = expr_construct(
        arena.push_lident_from_idx(constructor_name_idx),
        Some(payload),
        arena,
    );
    let ok_expr = expr_construct_with_loc(
        {
            let lident_name = arena.intern_string("Ok");
            arena.push_lident_from_idx(lident_name)
        },
        Some(ctor),
        arena.dummy_loc(),
        arena,
    );

    case(lhs, ok_expr, arena)
}

fn variants_generate_arg_decoder(
    settings: GeneratorSettings,
    args: &[CoreTypeIdx],
    constructor_name: StrIdx,
    arena: &mut ParseArena,
) -> SpiceResult<Expression> {
    let args_resolved: Vec<CoreType> = args
        .iter()
        .map(|idx| arena.get_core_type(*idx).clone())
        .collect();
    let num_args = args_resolved.len();

    let mut decode_exprs = Vec::with_capacity(num_args);
    for (i, arg) in args_resolved.iter().enumerate() {
        let (_, dec) = codecs_generate_value_codecs(settings, arg, arena)?;
        let decoder = require_decoder(dec)?;
        let idx_expr = expr_constant(
            Constant::Integer(Cow::Owned((i + 1).to_string()), None),
            arena,
        );
        let arg_expr = expr_apply(
            expr_ident_path(arena, &["Array", "getUnsafe"]),
            vec![
                (ArgLabel::Nolabel, expr_ident_path(arena, &["json_arr"])),
                (ArgLabel::Nolabel, idx_expr),
            ],
            false,
            arena.dummy_loc(),
            arena,
        );
        let applied = expr_apply(
            decoder,
            vec![(ArgLabel::Nolabel, arg_expr)],
            false,
            arena.dummy_loc(),
            arena,
        );
        decode_exprs.push(applied);
    }

    let tuple_expr = tuple_or_singleton_expr(decode_exprs, arena);

    let mut cases = Vec::new();
    cases.push(variants_generate_decode_success_case(
        num_args,
        constructor_name,
        arena,
    ));
    for i in 0..num_args {
        cases.push(generate_error_case(num_args, i, true, arena));
    }

    Ok(expr_match(tuple_expr, cases, arena))
}

fn variants_generate_decoder_case(
    settings: GeneratorSettings,
    decl: &ParsedVariantDecl,
    arena: &mut ParseArena,
) -> SpiceResult<Case> {
    let name_idx = decl.name;
    let name_literal_idx = decl.name_literal;
    match &decl.constr_decl.pcd_args {
        crate::parser::ast::ConstructorArguments::Pcstr_tuple(args) => {
            let arg_len = expr_constant(
                Constant::Integer(Cow::Owned((args.len() + 1).to_string()), None),
                arena,
            );
            let decoded = if args.is_empty() {
                let constructor_name = arena.get_string(name_idx).to_string();
                let constructor_name_idx = arena.push_string(constructor_name);
                let ctor = expr_construct(
                    arena.push_lident_from_idx(constructor_name_idx),
                    None,
                    arena,
                );
                expr_construct_with_loc(
                    {
                        let lident_name = arena.intern_string("Ok");
                        arena.push_lident_from_idx(lident_name)
                    },
                    Some(ctor),
                    arena.dummy_loc(),
                    arena,
                )
            } else {
                variants_generate_arg_decoder(settings, args, name_idx, arena)?
            };

            let name_const = extend_cow_lifetime(Cow::Borrowed(arena.get_string(name_literal_idx)));
            arena.register_constant_string_identity(name_const.as_ref(), name_literal_idx);
            let json_str_pat = pat_construct_with_loc(
                lident_path_static(arena, &["JSON", "String"]),
                Some(Pattern {
                    ppat_desc: Box::new(PatternDesc::Ppat_constant(Box::new(Constant::string(&name_const)))),
                    ppat_loc: arena.dummy_loc(),
                    ppat_attributes: Attributes::new(),
                }),
                arena.none_loc(),
                arena,
            );

            let json_arr_expr = expr_ident_path(arena, &["json_arr"]);
            let len_expr = expr_apply(
                expr_ident_path(arena, &["Array", "length"]),
                vec![(ArgLabel::Nolabel, json_arr_expr)],
                false,
                arena.dummy_loc(),
                arena,
            );
            let cond = expr_not_equal(arena, len_expr, arg_len);

            let v_expr = expr_ident_path(arena, &["v"]);
            let invalid_msg =
                expr_constant_literal(arena, "Invalid number of arguments to variant constructor");
            let err_expr = expr_spice_error_variants(arena, invalid_msg, v_expr, None);
            let rhs = expr_ifthenelse(cond, err_expr, Some(decoded), arena);

            Ok(case(json_str_pat, rhs, arena))
        }
        crate::parser::ast::ConstructorArguments::Pcstr_record(fields) => {
            let arg_len = expr_constant(Constant::Integer(Cow::Borrowed("2"), None), arena);
            let payload_value = expr_apply(
                expr_ident_path(arena, &["Array", "getUnsafe"]),
                vec![
                    (ArgLabel::Nolabel, expr_ident_path(arena, &["json_arr"])),
                    (
                        ArgLabel::Nolabel,
                        expr_constant(Constant::Integer(Cow::Borrowed("1"), None), arena),
                    ),
                ],
                false,
                arena.dummy_loc(),
                arena,
            );
            let payload_expr = expr_ident_path(arena, &["v"]);
            let object_pattern = pat_construct_with_loc(
                lident_path_static(arena, &["JSON", "Object"]),
                Some(pat_var_dummy(arena, "dict")),
                arena.dummy_loc(),
                arena,
            );
            let decoded = records_generate_inline_decoder_expr(settings, fields, decl.name, arena)?;
            let not_object_message = expr_constant_literal(arena, "Not an object");
            let not_object =
                expr_spice_error_variants(arena, not_object_message, payload_expr.clone(), None);
            let payload_match = expr_match(
                expr_constraint(payload_expr, ctyp_json_t(arena), arena),
                vec![
                    case(object_pattern, decoded, arena),
                    case(pat_any(arena), not_object, arena),
                ],
                arena,
            );
            let payload_pattern = pat_var_dummy(arena, "v");
            let payload_pattern = arena.push_pat(payload_pattern);
            let decoded = expr_let(
                RecFlag::Nonrecursive,
                vec![ValueBinding {
                    pvb_pat: payload_pattern,
                    pvb_expr: arena.push_expr(payload_value),
                    pvb_attributes: Attributes::new(),
                    pvb_loc: arena.dummy_loc(),
                }],
                payload_match,
                arena,
            );
            let decoded = variants_prefix_inline_payload_error(decoded, arena);

            let name_const = extend_cow_lifetime(Cow::Borrowed(arena.get_string(name_literal_idx)));
            arena.register_constant_string_identity(name_const.as_ref(), name_literal_idx);
            let json_str_pat = pat_construct_with_loc(
                lident_path_static(arena, &["JSON", "String"]),
                Some(Pattern {
                    ppat_desc: Box::new(PatternDesc::Ppat_constant(Box::new(Constant::string(&name_const)))),
                    ppat_loc: arena.dummy_loc(),
                    ppat_attributes: Attributes::new(),
                }),
                arena.none_loc(),
                arena,
            );
            let len_expr = expr_apply(
                expr_ident_path(arena, &["Array", "length"]),
                vec![(ArgLabel::Nolabel, expr_ident_path(arena, &["json_arr"]))],
                false,
                arena.dummy_loc(),
                arena,
            );
            let cond = expr_not_equal(arena, len_expr, arg_len);
            let invalid_message =
                expr_constant_literal(arena, "Invalid number of arguments to variant constructor");
            let whole_value = expr_ident_path(arena, &["v"]);
            let err_expr = expr_spice_error_variants(arena, invalid_message, whole_value, None);
            Ok(case(
                json_str_pat,
                expr_ifthenelse(cond, err_expr, Some(decoded), arena),
                arena,
            ))
        }
    }
}

fn variants_generate_decoder_case_attr(
    is_string: bool,
    settings: GeneratorSettings,
    decl: &ParsedVariantDecl,
    arena: &mut ParseArena,
) -> SpiceResult<Option<(Expression, Expression)>> {
    match &decl.constr_decl.pcd_args {
        crate::parser::ast::ConstructorArguments::Pcstr_tuple(args) => {
            let const_opt = if is_string {
                get_string_from_expression(&decl.alias)?
            } else {
                get_float_from_expression(&decl.alias)?
            };
            let const_value = match const_opt {
                Some(c) => c,
                None => return Ok(None),
            };

            let decoded = if args.is_empty() {
                let constructor_name = arena.get_string(decl.name).to_string();
                let constructor_name_idx = arena.push_string(constructor_name);
                let ctor = expr_construct(
                    arena.push_lident_from_idx(constructor_name_idx),
                    None,
                    arena,
                );
                expr_construct_with_loc(
                    {
                        let lident_name = arena.intern_string("Ok");
                        arena.push_lident_from_idx(lident_name)
                    },
                    Some(ctor),
                    arena.dummy_loc(),
                    arena,
                )
            } else {
                variants_generate_arg_decoder(settings, args, decl.name, arena)?
            };

            let const_expr = expr_constant(const_value, arena);
            let str_expr = expr_ident_path(arena, &["str_or_num"]);
            let if_expr = expr_equal(arena, const_expr, str_expr);
            Ok(Some((if_expr, decoded)))
        }
        crate::parser::ast::ConstructorArguments::Pcstr_record(_) => {
            Err(spice_error("This syntax is not yet implemented by spice"))
        }
    }
}

fn variants_generate_unboxed_decode(
    settings: GeneratorSettings,
    decl: &crate::parser::ast::ConstructorDeclaration,
    arena: &mut ParseArena,
) -> SpiceResult<Option<Expression>> {
    match &decl.pcd_args {
        crate::parser::ast::ConstructorArguments::Pcstr_tuple(args) => {
            if args.len() != 1 {
                return Err(spice_error("Expected exactly one type argument"));
            }
            let arg0 = arena.get_core_type(args[0]).clone();
            let (_, dec) = codecs_generate_value_codecs(settings, &arg0, arena)?;
            let decoder = match dec {
                Some(decoder) => decoder,
                None => return Ok(None),
            };
            let map_v_idx = arena.spice_runtime_v();
            let map_v_loc = arena.dummy_loc();
            let map_v_expr = expr_ident_from_str_idx(arena, map_v_idx, map_v_loc);
            let map_v_pat = pat_var_idx(arena, map_v_idx, map_v_loc);
            let ctor_name = decl.pcd_name.txt;
            let ctor_name = arena.get_string(ctor_name).to_string();
            let ctor_name_idx = arena.push_string(ctor_name);
            let ctor_expr = expr_construct(
                arena.push_lident_from_idx(ctor_name_idx),
                Some(map_v_expr),
                arena,
            );
            let inner_fun = expr_fun(ArgLabel::Nolabel, map_v_pat, ctor_expr, Some(1), arena);
            let map_expr = expr_apply(
                expr_ident_path(arena, &["Result", "map"]),
                vec![
                    (
                        ArgLabel::Nolabel,
                        expr_apply(
                            decoder,
                            vec![(ArgLabel::Nolabel, expr_ident_path(arena, &["v"]))],
                            false,
                            arena.dummy_loc(),
                            arena,
                        ),
                    ),
                    (ArgLabel::Nolabel, inner_fun),
                ],
                false,
                arena.dummy_loc(),
                arena,
            );
            Ok(Some(expr_fun(
                ArgLabel::Nolabel,
                pat_var_dummy(arena, "v"),
                map_expr,
                Some(1),
                arena,
            )))
        }
        crate::parser::ast::ConstructorArguments::Pcstr_record(_) => {
            Err(spice_error("This syntax is not yet implemented by spice"))
        }
    }
}

fn variants_generate_codecs(
    settings: GeneratorSettings,
    constr_decls: &[crate::parser::ast::ConstructorDeclaration],
    unboxed: bool,
    arena: &mut ParseArena,
) -> SpiceResult<(Option<Expression>, Option<Expression>)> {
    let parsed: Vec<ParsedVariantDecl> = constr_decls
        .iter()
        .map(|d| variants_parse_decl(d, arena))
        .collect::<Result<Vec<_>, _>>()?;
    let count_has_attr = parsed.iter().filter(|v| v.has_attr_as).count();
    let has_attr_as = if count_has_attr > 0 {
        if count_has_attr == parsed.len() {
            true
        } else {
            return Err(spice_error("Partial @spice.as usage is not allowed"));
        }
    } else {
        false
    };

    let encoder = if settings.do_encode {
        let mut cases = Vec::new();
        for decl in &parsed {
            cases.push(variants_generate_encoder_case(
                settings,
                unboxed,
                has_attr_as,
                decl,
                arena,
            )?);
        }
        let match_expr = expr_match(expr_ident_path(arena, &["v"]), cases, arena);
        let constrained = expr_constraint(match_expr, ctyp_json_t_const(arena), arena);
        Some(expr_fun(
            ArgLabel::Nolabel,
            pat_var_dummy(arena, "v"),
            constrained,
            Some(1),
            arena,
        ))
    } else {
        None
    };

    let decoder = if settings.do_decode {
        if unboxed {
            let first_decl = constr_decls
                .first()
                .ok_or_else(|| spice_error("Internal spice error: missing constructor"))?;
            variants_generate_unboxed_decode(settings, first_decl, arena)?
        } else if has_attr_as {
            let mut string_cases = Vec::new();
            let mut number_cases = Vec::new();
            for decl in &parsed {
                if let Some(pair) =
                    variants_generate_decoder_case_attr(true, settings, decl, arena)?
                {
                    string_cases.push(pair);
                }
                if let Some(pair) =
                    variants_generate_decoder_case_attr(false, settings, decl, arena)?
                {
                    number_cases.push(pair);
                }
            }

            let spice_prefix = arena.spice_variants_str();
            let decoder_switch = build_ifthenelse_with_prefix(arena, string_cases, spice_prefix);
            let decoder_switch_num =
                build_ifthenelse_with_prefix(arena, number_cases, spice_prefix);

            let json_expr = expr_ident_path(arena, &["v"]);
            let match_expr = expr_match(
                expr_constraint(json_expr.clone(), ctyp_json_t(arena), arena),
                vec![
                    case(
                        pat_construct_with_loc(
                            lident_path_static(arena, &["JSON", "String"]),
                            Some(pat_var_dummy(arena, "str_or_num")),
                            arena.dummy_loc(),
                            arena,
                        ),
                        decoder_switch,
                        arena,
                    ),
                    case(
                        pat_construct_with_loc(
                            lident_path_static(arena, &["JSON", "Number"]),
                            Some(pat_var_dummy(arena, "str_or_num")),
                            arena.dummy_loc(),
                            arena,
                        ),
                        decoder_switch_num,
                        arena,
                    ),
                    case(
                        pat_any(arena),
                        {
                            let not_string = expr_constant_literal(arena, "Not a JSONString");
                            expr_spice_error_variants(arena, not_string, json_expr, None)
                        },
                        arena,
                    ),
                ],
                arena,
            );
            Some(expr_fun(
                ArgLabel::Nolabel,
                pat_var_dummy(arena, "v"),
                match_expr,
                Some(1),
                arena,
            ))
        } else {
            let mut cases = Vec::new();
            for decl in &parsed {
                cases.push(variants_generate_decoder_case(settings, decl, arena)?);
            }
            let json_arr_expr = expr_ident_path(arena, &["json_arr"]);
            let head_expr = expr_apply(
                expr_ident_path(arena, &["Array", "getUnsafe"]),
                vec![
                    (ArgLabel::Nolabel, json_arr_expr.clone()),
                    (
                        ArgLabel::Nolabel,
                        expr_constant(Constant::Integer(Cow::Borrowed("0"), None), arena),
                    ),
                ],
                false,
                arena.dummy_loc(),
                arena,
            );
            let default_case = case(
                pat_any(arena),
                {
                    let invalid_ctor = expr_constant_literal(arena, "Invalid variant constructor");
                    expr_spice_error_variants(arena, invalid_ctor, head_expr.clone(), None)
                },
                arena,
            );
            cases.push(default_case);

            let decoder_switch = expr_match(head_expr, cases, arena);

            let json_expr = expr_ident_path(arena, &["v"]);
            let match_expr = expr_match(
                expr_constraint(json_expr.clone(), ctyp_json_t(arena), arena),
                vec![
                    case(
                        pat_construct_with_loc(
                            lident_path_static(arena, &["JSON", "Array"]),
                            Some(pat_array(vec![], arena)),
                            arena.dummy_loc(),
                            arena,
                        ),
                        {
                            let empty_array =
                                expr_constant_literal(arena, "Expected variant, found empty array");
                            expr_spice_error_variants(arena, empty_array, json_expr.clone(), None)
                        },
                        arena,
                    ),
                    case(
                        pat_construct_with_loc(
                            lident_path_static(arena, &["JSON", "Array"]),
                            Some(pat_var_dummy(arena, "json_arr")),
                            arena.dummy_loc(),
                            arena,
                        ),
                        decoder_switch,
                        arena,
                    ),
                    case(
                        pat_any(arena),
                        {
                            let not_variant = expr_constant_literal(arena, "Not a variant");
                            expr_spice_error_variants(arena, not_variant, json_expr, None)
                        },
                        arena,
                    ),
                ],
                arena,
            );
            Some(expr_fun(
                ArgLabel::Nolabel,
                pat_var_dummy(arena, "v"),
                match_expr,
                Some(1),
                arena,
            ))
        }
    } else {
        None
    };

    Ok((encoder, decoder))
}

/// A tag's payload groups as the v0 PPX bridge (`Ast_mapper_to0`) hands
/// them to this PPX: a single type stays itself, several become a tuple.
fn bridge_rtag_types(groups: &[crate::parser::ast::VariantTypeArgs], arena: &ParseArena) -> Vec<CoreType> {
    groups
        .iter()
        .map(|group| match group.txt.as_slice() {
            [typ] => arena.get_core_type(*typ).clone(),
            types => CoreType {
                ptyp_desc: Box::new(CoreTypeDesc::Ptyp_tuple(Box::new(types.to_vec()))),
                ptyp_loc: group.loc,
                ptyp_attributes: Attributes::new(),
            },
        })
        .collect()
}

fn polyvars_get_args(
    _loc: LocIdx,
    groups: &[crate::parser::ast::VariantTypeArgs],
    arena: &ParseArena,
) -> SpiceResult<Vec<CoreType>> {
    let core_types = bridge_rtag_types(groups, arena);
    match core_types.len() {
        0 => Ok(vec![]),
        1 => {
            let ct = &core_types[0];
            match &*ct.ptyp_desc {
                CoreTypeDesc::Ptyp_tuple(types) => Ok(types
                    .iter()
                    .map(|idx| arena.get_core_type(*idx).clone())
                    .collect()),
                _ => Ok(vec![ct.clone()]),
            }
        }
        _ => Err(spice_error(
            "This error shoudn't happen, means that the AST of your polyvariant is wrong",
        )),
    }
}

fn polyvars_parse_decl(
    row_field: &RowField,
    arena: &mut ParseArena,
) -> SpiceResult<ParsedPolyvariantField> {
    let name = match row_field {
        RowField::Rtag(tag, _, _, _) => tag.txt.clone(),
        _ => return Err(spice_error("cannot get polymorphic variant constructor")),
    };

    let (alias, has_attr_as) = match row_field {
        RowField::Rtag(_, attrs, _, _) => match get_attribute_by_name(attrs, "spice.as", arena) {
            Ok(Some(attr)) => (get_expression_from_payload(attr, arena)?, true),
            Ok(None) => (
                expr_constant(
                    Constant::string(&name),
                    arena,
                ),
                false,
            ),
            Err(e) => return Err(e),
        },
        RowField::Rinherit(_) => {
            return Err(spice_error("This syntax is not yet implemented by spice"));
        }
    };

    Ok(ParsedPolyvariantField {
        name,
        alias,
        has_attr_as,
        row_field: row_field.clone(),
    })
}

fn polyvars_generate_encoder_case(
    settings: GeneratorSettings,
    unboxed: bool,
    has_attr_as: bool,
    row: &ParsedPolyvariantField,
    arena: &mut ParseArena,
) -> SpiceResult<Case> {
    let (json_expr, args) = match &row.row_field {
        RowField::Rtag(_, _, _, core_types) => {
            let json_expr = match &*row.alias.pexp_desc {
                ExpressionDesc::Pexp_constant(constant) => match &**constant {
                    Constant::String(_) => expr_construct_with_loc(
                        lident_path_static(arena, &["JSON", "String"]),
                        Some(row.alias.clone()),
                        arena.dummy_loc(),
                        arena,
                    ),
                    Constant::Float(_, _) => expr_construct_with_loc(
                        lident_path_static(arena, &["JSON", "Number"]),
                        Some(row.alias.clone()),
                        arena.dummy_loc(),
                        arena,
                    ),
                    _ => return Err(spice_error("cannot find a name??")),
                },
                _ => return Err(spice_error("cannot find a name??")),
            };
            let args = polyvars_get_args(arena.dummy_loc(), core_types, arena)?;
            (json_expr, args)
        }
        RowField::Rinherit(_arg) => {
            return Err(spice_error("This syntax is not yet implemented by spice"));
        }
    };

    let lhs_vars = match args.len() {
        0 => None,
        1 => Some(pat_var_none(arena, "v0")),
        _ => {
            let mut vars = Vec::with_capacity(args.len());
            for i in 0..args.len() {
                vars.push(pat_var_dynamic(
                    arena,
                    &format!("v{}", i),
                    arena.dummy_loc(),
                ));
            }
            Some(pat_tuple(vars, arena))
        }
    };

    let mut rhs_list = Vec::new();
    rhs_list.push(json_expr.clone());
    for (i, arg) in args.iter().enumerate() {
        let (enc, _) = codecs_generate_value_codecs(settings, arg, arena)?;
        let encoder = require_encoder(enc)?;
        let v_expr = expr_ident_dynamic(arena, format!("v{}", i));
        let applied = expr_apply(
            encoder,
            vec![(ArgLabel::Nolabel, v_expr)],
            false,
            arena.dummy_loc(),
            arena,
        );
        rhs_list.push(applied);
    }

    let rhs = if unboxed {
        rhs_list
            .get(1)
            .cloned()
            .unwrap_or_else(|| json_expr.clone())
    } else if has_attr_as {
        json_expr
    } else {
        let arr = expr_array(rhs_list, arena);
        expr_construct_with_loc(
            lident_path_static(arena, &["JSON", "Array"]),
            Some(arr),
            arena.dummy_loc(),
            arena,
        )
    };

    let pat = pat_variant(row.name.clone(), lhs_vars, arena);

    Ok(Case {
        pc_bar: None,
        pc_lhs: arena.push_pat(pat),
        pc_guard: None,
        pc_rhs: arena.push_expr(rhs),
    })
}

fn polyvars_generate_decode_success_case(
    num_args: usize,
    constructor_name: &str,
    arena: &mut ParseArena,
) -> Case {
    let mut pats = Vec::with_capacity(num_args);
    for i in 0..num_args {
        let v_pat = pat_var_dynamic(arena, &format!("v{}", i), arena.none_loc());
        pats.push(pat_construct_with_loc(
            {
                let lident_name = arena.intern_string("Ok");
                arena.push_lident_from_idx(lident_name)
            },
            Some(v_pat),
            arena.dummy_loc(),
            arena,
        ));
    }
    let lhs = tuple_or_singleton_pat(pats, arena);

    let mut exprs = Vec::with_capacity(num_args);
    for i in 0..num_args {
        exprs.push(expr_ident_dynamic(arena, format!("v{}", i)));
    }
    let payload = tuple_or_singleton_expr(exprs, arena);
    let ctor = expr_variant(
        Cow::Owned(constructor_name.to_string()),
        Some(payload),
        arena,
    );
    let ok_expr = expr_construct_with_loc(
        {
            let lident_name = arena.intern_string("Ok");
            arena.push_lident_from_idx(lident_name)
        },
        Some(ctor),
        arena.dummy_loc(),
        arena,
    );

    case(lhs, ok_expr, arena)
}

fn polyvars_generate_arg_decoder(
    settings: GeneratorSettings,
    args: &[CoreType],
    constructor_name: &str,
    arena: &mut ParseArena,
) -> SpiceResult<Expression> {
    let num_args = args.len();

    let mut decode_exprs = Vec::with_capacity(num_args);
    for (i, arg) in args.iter().enumerate() {
        let (_, dec) = codecs_generate_value_codecs(settings, arg, arena)?;
        let decoder = require_decoder(dec)?;
        let idx_expr = expr_constant(
            Constant::Integer(Cow::Owned((i + 1).to_string()), None),
            arena,
        );
        let arg_expr = expr_apply(
            expr_ident_path(arena, &["Array", "getUnsafe"]),
            vec![
                (ArgLabel::Nolabel, expr_ident_path(arena, &["json_arr"])),
                (ArgLabel::Nolabel, idx_expr),
            ],
            false,
            arena.dummy_loc(),
            arena,
        );
        let applied = expr_apply(
            decoder,
            vec![(ArgLabel::Nolabel, arg_expr)],
            false,
            arena.dummy_loc(),
            arena,
        );
        decode_exprs.push(applied);
    }

    let tuple_expr = tuple_or_singleton_expr(decode_exprs, arena);

    let mut cases = Vec::new();
    cases.push(polyvars_generate_decode_success_case(
        num_args,
        constructor_name,
        arena,
    ));
    for i in 0..num_args {
        cases.push(generate_error_case(num_args, i, true, arena));
    }

    Ok(expr_match(tuple_expr, cases, arena))
}

fn polyvars_generate_decoder_case(
    settings: GeneratorSettings,
    row_field: &RowField,
    arena: &mut ParseArena,
) -> SpiceResult<Case> {
    match row_field {
        RowField::Rtag(tag, _, _, core_types) => {
            let args = polyvars_get_args(arena.dummy_loc(), core_types, arena)?;
            let arg_len = expr_constant(
                Constant::Integer(Cow::Owned((args.len() + 1).to_string()), None),
                arena,
            );
            let decoded = if args.is_empty() {
                let ctor = expr_variant(tag.txt.clone(), None, arena);
                expr_construct_with_loc(
                    {
                        let lident_name = arena.intern_string("Ok");
                        arena.push_lident_from_idx(lident_name)
                    },
                    Some(ctor),
                    arena.dummy_loc(),
                    arena,
                )
            } else {
                polyvars_generate_arg_decoder(settings, &args, &tag.txt, arena)?
            };

            let tag_name = tag.txt.clone();
            let json_str_pat = pat_construct_with_loc(
                lident_path_static(arena, &["JSON", "String"]),
                Some(Pattern {
                    ppat_desc: Box::new(PatternDesc::Ppat_constant(Box::new(Constant::string(&tag_name)))),
                    ppat_loc: arena.dummy_loc(),
                    ppat_attributes: Attributes::new(),
                }),
                arena.none_loc(),
                arena,
            );

            let json_arr_expr = expr_ident_path(arena, &["json_arr"]);
            let len_expr = expr_apply(
                expr_ident_path(arena, &["Array", "length"]),
                vec![(ArgLabel::Nolabel, json_arr_expr)],
                false,
                arena.dummy_loc(),
                arena,
            );
            let cond = expr_not_equal_strict(arena, len_expr, arg_len);

            let v_expr = expr_ident_path(arena, &["v"]);
            let invalid_msg = expr_constant_literal(
                arena,
                "Invalid number of arguments to polyvariant constructor",
            );
            let err_expr = expr_spice_error_polyvars(arena, invalid_msg, v_expr, None);
            let rhs = expr_ifthenelse(cond, err_expr, Some(decoded), arena);
            Ok(case(json_str_pat, rhs, arena))
        }
        RowField::Rinherit(_core_type) => {
            Err(spice_error("This syntax is not yet implemented by spice"))
        }
    }
}

fn polyvars_generate_decoder_case_attr(
    is_string: bool,
    settings: GeneratorSettings,
    row: &ParsedPolyvariantField,
    arena: &mut ParseArena,
) -> SpiceResult<Option<(Expression, Expression)>> {
    match &row.row_field {
        RowField::Rtag(tag, _, _, core_types) => {
            let args = polyvars_get_args(arena.dummy_loc(), core_types, arena)?;
            let const_opt = if is_string {
                get_string_from_expression(&row.alias)?
            } else {
                get_float_from_expression(&row.alias)?
            };
            let const_value = match const_opt {
                Some(c) => c,
                None => return Ok(None),
            };

            let decoded = if args.is_empty() {
                let ctor = expr_variant(tag.txt.clone(), None, arena);
                expr_construct_with_loc(
                    {
                        let lident_name = arena.intern_string("Ok");
                        arena.push_lident_from_idx(lident_name)
                    },
                    Some(ctor),
                    arena.dummy_loc(),
                    arena,
                )
            } else {
                polyvars_generate_arg_decoder(settings, &args, &tag.txt, arena)?
            };

            let const_expr = expr_constant(const_value, arena);
            let str_expr = expr_ident_path(arena, &["str_or_num"]);
            let if_expr = expr_equal(arena, const_expr, str_expr);
            Ok(Some((if_expr, decoded)))
        }
        RowField::Rinherit(_) => Err(spice_error("This syntax is not yet implemented by spice")),
    }
}

fn polyvars_generate_unboxed_decode(
    settings: GeneratorSettings,
    row_field: &RowField,
    arena: &mut ParseArena,
) -> SpiceResult<Option<Expression>> {
    match row_field {
        RowField::Rtag(tag, _, _, args) => {
            let mut args = bridge_rtag_types(args, arena);
            if args.len() != 1 {
                return Err(spice_error("Expected exactly one type argument"));
            }
            let arg0 = args.pop().expect("one type argument");
            let (_, dec) = codecs_generate_value_codecs(settings, &arg0, arena)?;
            let decoder = match dec {
                Some(decoder) => decoder,
                None => return Ok(None),
            };
            let map_v_idx = arena.spice_runtime_v();
            let map_v_loc = arena.dummy_loc();
            let map_v_expr = expr_ident_from_str_idx(arena, map_v_idx, map_v_loc);
            let map_v_pat = pat_var_idx(arena, map_v_idx, map_v_loc);
            let ctor_expr = expr_construct(
                {
                    let lident_name = arena.intern_string(&tag.txt);
                    arena.push_lident_from_idx(lident_name)
                },
                Some(map_v_expr),
                arena,
            );
            let inner_fun = expr_fun(ArgLabel::Nolabel, map_v_pat, ctor_expr, Some(1), arena);
            let map_expr = expr_apply(
                expr_ident_path(arena, &["Result", "map"]),
                vec![
                    (
                        ArgLabel::Nolabel,
                        expr_apply(
                            decoder,
                            vec![(ArgLabel::Nolabel, expr_ident_path(arena, &["v"]))],
                            false,
                            arena.dummy_loc(),
                            arena,
                        ),
                    ),
                    (ArgLabel::Nolabel, inner_fun),
                ],
                false,
                arena.dummy_loc(),
                arena,
            );
            Ok(Some(expr_fun(
                ArgLabel::Nolabel,
                pat_var_dummy(arena, "v"),
                map_expr,
                Some(1),
                arena,
            )))
        }
        RowField::Rinherit(_core_type) => {
            Err(spice_error("This syntax is not yet implemented by spice"))
        }
    }
}

fn polyvars_generate_codecs(
    settings: GeneratorSettings,
    row_fields: &[RowField],
    unboxed: bool,
    arena: &mut ParseArena,
) -> SpiceResult<(Option<Expression>, Option<Expression>)> {
    let parsed: Vec<ParsedPolyvariantField> = row_fields
        .iter()
        .map(|r| polyvars_parse_decl(r, arena))
        .collect::<Result<Vec<_>, _>>()?;
    let count_has_attr = parsed.iter().filter(|v| v.has_attr_as).count();
    let has_attr_as = if count_has_attr > 0 {
        if count_has_attr == parsed.len() {
            true
        } else {
            return Err(spice_error("Partial @spice.as usage is not allowed"));
        }
    } else {
        false
    };

    let encoder = if settings.do_encode {
        let mut cases = Vec::new();
        for row in &parsed {
            cases.push(polyvars_generate_encoder_case(
                settings,
                unboxed,
                has_attr_as,
                row,
                arena,
            )?);
        }
        let match_expr = expr_match(expr_ident_path(arena, &["v"]), cases, arena);
        Some(expr_fun(
            ArgLabel::Nolabel,
            pat_var_dummy(arena, "v"),
            match_expr,
            Some(1),
            arena,
        ))
    } else {
        None
    };

    let decoder = if settings.do_decode {
        if unboxed {
            let first_row = row_fields
                .first()
                .ok_or_else(|| spice_error("Internal spice error: missing row field"))?;
            polyvars_generate_unboxed_decode(settings, first_row, arena)?
        } else if has_attr_as {
            let mut string_cases = Vec::new();
            let mut number_cases = Vec::new();
            for row in &parsed {
                if let Some(pair) = polyvars_generate_decoder_case_attr(true, settings, row, arena)?
                {
                    string_cases.push(pair);
                }
                if let Some(pair) =
                    polyvars_generate_decoder_case_attr(false, settings, row, arena)?
                {
                    number_cases.push(pair);
                }
            }

            let spice_prefix = arena.spice_polyvars_str();
            let decoder_switch = build_ifthenelse_with_prefix(arena, string_cases, spice_prefix);
            let decoder_switch_num =
                build_ifthenelse_with_prefix(arena, number_cases, spice_prefix);

            let json_expr = expr_ident_path(arena, &["v"]);
            let match_expr = expr_match(
                expr_constraint(json_expr.clone(), ctyp_json_t(arena), arena),
                vec![
                    case(
                        pat_construct_with_loc(
                            lident_path_static(arena, &["JSON", "String"]),
                            Some(pat_var_dummy(arena, "str_or_num")),
                            arena.dummy_loc(),
                            arena,
                        ),
                        decoder_switch,
                        arena,
                    ),
                    case(
                        pat_construct_with_loc(
                            lident_path_static(arena, &["JSON", "Number"]),
                            Some(pat_var_dummy(arena, "str_or_num")),
                            arena.dummy_loc(),
                            arena,
                        ),
                        decoder_switch_num,
                        arena,
                    ),
                    case(
                        pat_any(arena),
                        {
                            let not_string = expr_constant_literal(arena, "Not a JSONString");
                            expr_spice_error_polyvars(arena, not_string, json_expr, None)
                        },
                        arena,
                    ),
                ],
                arena,
            );
            Some(expr_fun(
                ArgLabel::Nolabel,
                pat_var_dummy(arena, "v"),
                match_expr,
                Some(1),
                arena,
            ))
        } else {
            let mut cases = Vec::new();
            for row in row_fields {
                cases.push(polyvars_generate_decoder_case(settings, row, arena)?);
            }
            let json_arr_expr = expr_ident_path(arena, &["json_arr"]);
            let head_expr = expr_apply(
                expr_ident_path(arena, &["Array", "getUnsafe"]),
                vec![
                    (ArgLabel::Nolabel, json_arr_expr.clone()),
                    (
                        ArgLabel::Nolabel,
                        expr_constant(Constant::Integer(Cow::Borrowed("0"), None), arena),
                    ),
                ],
                false,
                arena.dummy_loc(),
                arena,
            );
            let default_case = case(
                pat_any(arena),
                {
                    let invalid_ctor =
                        expr_constant_literal(arena, "Invalid polymorphic variant constructor");
                    expr_spice_error_polyvars(arena, invalid_ctor, head_expr.clone(), None)
                },
                arena,
            );
            cases.push(default_case);

            let decoder_switch = expr_match(head_expr, cases, arena);

            let json_expr = expr_ident_path(arena, &["v"]);
            let match_expr = expr_match(
                expr_constraint(json_expr.clone(), ctyp_json_t(arena), arena),
                vec![
                    case(
                        pat_construct_with_loc(
                            lident_path_static(arena, &["JSON", "Array"]),
                            Some(pat_array(vec![], arena)),
                            arena.dummy_loc(),
                            arena,
                        ),
                        {
                            let empty_array = expr_constant_literal(
                                arena,
                                "Expected polyvariant, found empty array",
                            );
                            expr_spice_error_polyvars(arena, empty_array, json_expr.clone(), None)
                        },
                        arena,
                    ),
                    case(
                        pat_construct_with_loc(
                            lident_path_static(arena, &["JSON", "Array"]),
                            Some(pat_var_dummy(arena, "json_arr")),
                            arena.dummy_loc(),
                            arena,
                        ),
                        decoder_switch,
                        arena,
                    ),
                    case(
                        pat_any(arena),
                        {
                            let not_poly = expr_constant_literal(arena, "Not a polyvariant");
                            expr_spice_error_polyvars(arena, not_poly, json_expr, None)
                        },
                        arena,
                    ),
                ],
                arena,
            );
            Some(expr_fun(
                ArgLabel::Nolabel,
                pat_var_dummy(arena, "v"),
                match_expr,
                Some(1),
                arena,
            ))
        }
    } else {
        None
    };

    Ok((encoder, decoder))
}

fn unused_value_warning_attribute(arena: &mut ParseArena) -> Attribute {
    let warning = expr_constant_literal(arena, "-32");
    let item = StructureItem {
        pstr_desc: Box::new(StructureItemDesc::Pstr_eval(Box::new((
            arena.push_expr(warning),
            Attributes::new(),
        )))),
        pstr_loc: arena.dummy_loc(),
    };
    (
        Located::new(arena.intern_string("ocaml.warning"), arena.dummy_loc()),
        Payload::PStr(Box::new(vec![item])),
    )
}

fn generate_codec_decls(
    type_name: &str,
    param_names: &[String],
    value_encoder: Option<Expression>,
    codecs: (Option<Expression>, Option<Expression>),
    arena: &mut ParseArena,
) -> Vec<ValueBinding> {
    let mut vbs = Vec::new();

    if let Some(encoder) = codecs.0 {
        for suffix in [ENCODER_FUNC_SUFFIX, VALUE_ENCODER_FUNC_SUFFIX] {
            let runtime_v_idx = arena.spice_runtime_v();
            let selected_encoder = if suffix == VALUE_ENCODER_FUNC_SUFFIX {
                value_encoder.clone().unwrap_or_else(|| encoder.clone())
            } else {
                encoder.clone()
            };
            let applied = expr_apply(
                selected_encoder,
                vec![(ArgLabel::Nolabel, expr_ident_path(arena, &["v"]))],
                false,
                arena.dummy_loc(),
                arena,
            );
            let mut expr = expr_fun(
                ArgLabel::Nolabel,
                pat_var_idx(arena, runtime_v_idx, arena.dummy_loc()),
                applied,
                Some(1),
                arena,
            );
            for param in param_names.iter().rev() {
                let name = format!("{}{}", ENCODER_VAR_PREFIX, param);
                expr = expr_fun(
                    ArgLabel::Nolabel,
                    pat_var_dynamic(arena, &name, arena.none_loc()),
                    expr,
                    None,
                    arena,
                );
            }

            let name = format!("{}{}", type_name, suffix);
            let pat = pat_var_dynamic(arena, &name, arena.none_loc());
            let attributes = if suffix == VALUE_ENCODER_FUNC_SUFFIX {
                vec![unused_value_warning_attribute(arena)].into()
            } else {
                Attributes::new()
            };
            vbs.push(ValueBinding {
                pvb_pat: arena.push_pat(pat),
                pvb_expr: arena.push_expr(expr),
                pvb_attributes: attributes,
                pvb_loc: arena.dummy_loc(),
            });
        }
    }

    if let Some(decoder) = codecs.1 {
        let runtime_v_idx = arena.spice_runtime_v();
        let mut expr = expr_fun(
            ArgLabel::Nolabel,
            pat_var_idx(arena, runtime_v_idx, arena.dummy_loc()),
            expr_apply(
                decoder,
                vec![(ArgLabel::Nolabel, expr_ident_path(arena, &["v"]))],
                false,
                arena.dummy_loc(),
                arena,
            ),
            Some(1),
            arena,
        );
        for param in param_names.iter().rev() {
            let name = format!("{}{}", DECODER_VAR_PREFIX, param);
            expr = expr_fun(
                ArgLabel::Nolabel,
                pat_var_dynamic(arena, &name, arena.none_loc()),
                expr,
                None,
                arena,
            );
        }

        let name = format!("{}{}", type_name, DECODER_FUNC_SUFFIX);
        let pat = pat_var_dynamic(arena, &name, arena.none_loc());
        vbs.push(ValueBinding {
            pvb_pat: arena.push_pat(pat),
            pvb_expr: arena.push_expr(expr),
            pvb_attributes: Attributes::new(),
            pvb_loc: arena.dummy_loc(),
        });
    }

    vbs
}

fn manifest_value_encoder(
    settings: GeneratorSettings,
    manifest: &CoreType,
    arena: &mut ParseArena,
) -> SpiceResult<Option<Expression>> {
    if get_attribute_by_name(&manifest.ptyp_attributes, "spice.codec", arena)?.is_some() {
        return Ok(None);
    }
    let CoreTypeDesc::Ptyp_constr(inner) = &*manifest.ptyp_desc else {
        return Ok(None);
    };
    let (constructor, args) = &**inner;
    if !longident_matches(arena, constructor.txt, &["option"]) || args.len() != 1 {
        return Ok(None);
    }
    Ok(codecs_generate_value_codecs(settings, manifest, arena)?.0)
}

fn map_type_decl_structure(
    decl: &TypeDeclaration,
    arena: &mut ParseArena,
) -> SpiceResult<Vec<ValueBinding>> {
    let type_name = arena.get_string(decl.ptype_name.txt).to_string();

    let is_unboxed = match get_attribute_by_name(&decl.ptype_attributes, "unboxed", arena) {
        Ok(Some(_)) => true,
        _ => false,
    };

    let generator_settings =
        match get_generator_settings_from_attributes(&decl.ptype_attributes, arena) {
            Ok(v) => v,
            Err(e) => return Err(e),
        };

    let settings = match generator_settings {
        None => return Ok(vec![]),
        Some(v) => v,
    };

    let param_names = get_param_names(&decl.ptype_params, arena)?;

    match (&decl.ptype_manifest, &decl.ptype_kind) {
        (None, TypeKind::Ptype_abstract) => {
            Err(spice_error("Can't generate codecs for unspecified type"))
        }
        (Some(manifest_idx), TypeKind::Ptype_abstract) => {
            let manifest = arena.get_core_type(*manifest_idx).clone();
            match &*manifest.ptyp_desc {
                CoreTypeDesc::Ptyp_variant(inner) => {
                    let (ref row_fields, _, _) = **inner;
                    let codecs = polyvars_generate_codecs(settings, row_fields, is_unboxed, arena)?;
                    Ok(generate_codec_decls(
                        &type_name,
                        &param_names,
                        None,
                        codecs,
                        arena,
                    ))
                }
                _ => {
                    let value_encoder = manifest_value_encoder(settings, &manifest, arena)?;
                    let codecs = codecs_generate_codecs(settings, &manifest, arena)?;
                    Ok(generate_codec_decls(
                        &type_name,
                        &param_names,
                        value_encoder,
                        codecs,
                        arena,
                    ))
                }
            }
        }
        (Some(manifest_idx), _) => {
            let manifest = arena.get_core_type(*manifest_idx).clone();
            let value_encoder = manifest_value_encoder(settings, &manifest, arena)?;
            let codecs = codecs_generate_codecs(settings, &manifest, arena)?;
            Ok(generate_codec_decls(
                &type_name,
                &param_names,
                value_encoder,
                codecs,
                arena,
            ))
        }
        (None, TypeKind::Ptype_variant(constructors)) => {
            let codecs = variants_generate_codecs(settings, constructors, is_unboxed, arena)?;
            Ok(generate_codec_decls(
                &type_name,
                &param_names,
                None,
                codecs,
                arena,
            ))
        }
        (None, TypeKind::Ptype_record(labels)) => {
            let codecs = records_generate_codecs(settings, labels, is_unboxed, arena)?;
            Ok(generate_codec_decls(
                &type_name,
                &param_names,
                None,
                codecs,
                arena,
            ))
        }
        _ => Err(spice_error("This type is not handled by spice")),
    }
}

fn attribute_is_spice(attr: &Attribute, arena: &ParseArena) -> bool {
    let name = arena.get_string(attr.0.txt);
    name == ANNOTATION_NAME || name.starts_with("spice.")
}

fn type_declaration_has_spice_attr(decl: &TypeDeclaration, arena: &ParseArena) -> bool {
    decl.ptype_attributes
        .iter()
        .any(|attr| attribute_is_spice(attr, arena))
}

fn module_type_contains_spice_type_decl(mod_type: &ModuleType, arena: &ParseArena) -> bool {
    match &*mod_type.pmty_desc {
        ModuleTypeDesc::Pmty_signature(items) => items
            .iter()
            .any(|item| signature_item_contains_spice_type_decl(item, arena)),
        ModuleTypeDesc::Pmty_functor(inner) => {
            let (_, arg, body) = &**inner;
            arg.map(|arg_idx| {
                let arg_type = arena.get_mod_type(arg_idx);
                module_type_contains_spice_type_decl(arg_type, arena)
            })
            .unwrap_or(false)
                || module_type_contains_spice_type_decl(arena.get_mod_type(*body), arena)
        }
        ModuleTypeDesc::Pmty_with(inner) => {
            let (base, constraints) = &**inner;
            module_type_contains_spice_type_decl(arena.get_mod_type(*base), arena)
                || constraints.iter().any(|constraint| match constraint {
                    WithConstraint::Pwith_type(_, decl)
                    | WithConstraint::Pwith_typesubst(_, decl) => {
                        type_declaration_has_spice_attr(decl, arena)
                    }
                    WithConstraint::Pwith_module(_, _) | WithConstraint::Pwith_modsubst(_, _) => {
                        false
                    }
                })
        }
        ModuleTypeDesc::Pmty_typeof(expr_idx) => {
            module_expr_contains_spice_type_decl(arena.get_mod_expr(*expr_idx), arena)
        }
        ModuleTypeDesc::Pmty_ident(_)
        | ModuleTypeDesc::Pmty_alias(_)
        | ModuleTypeDesc::Pmty_extension(_) => false,
    }
}

fn module_expr_contains_spice_type_decl(mod_expr: &ModuleExpr, arena: &ParseArena) -> bool {
    match &*mod_expr.pmod_desc {
        ModuleExprDesc::Pmod_structure(items) => items
            .iter()
            .any(|item| structure_item_contains_spice_type_decl(item, arena)),
        ModuleExprDesc::Pmod_functor(inner) => {
            let (_, arg, body) = &**inner;
            arg.map(|arg_idx| {
                let arg_type = arena.get_mod_type(arg_idx);
                module_type_contains_spice_type_decl(arg_type, arena)
            })
            .unwrap_or(false)
                || module_expr_contains_spice_type_decl(arena.get_mod_expr(*body), arena)
        }
        ModuleExprDesc::Pmod_apply(lhs, rhs) => {
            module_expr_contains_spice_type_decl(arena.get_mod_expr(*lhs), arena)
                || module_expr_contains_spice_type_decl(arena.get_mod_expr(*rhs), arena)
        }
        ModuleExprDesc::Pmod_constraint(lhs, mty) => {
            module_expr_contains_spice_type_decl(arena.get_mod_expr(*lhs), arena)
                || module_type_contains_spice_type_decl(arena.get_mod_type(*mty), arena)
        }
        ModuleExprDesc::Pmod_ident(_)
        | ModuleExprDesc::Pmod_unpack(_)
        | ModuleExprDesc::Pmod_extension(_) => false,
    }
}

fn signature_item_contains_spice_type_decl(item: &SignatureItem, arena: &ParseArena) -> bool {
    match &*item.psig_desc {
        SignatureItemDesc::Psig_type(inner) => {
            let (_, decls) = &**inner;
            decls
                .iter()
                .any(|decl| type_declaration_has_spice_attr(decl, arena))
        }
        SignatureItemDesc::Psig_module(md) => {
            module_type_contains_spice_type_decl(arena.get_mod_type(md.pmd_type), arena)
        }
        SignatureItemDesc::Psig_recmodule(mds) => mds
            .iter()
            .any(|md| module_type_contains_spice_type_decl(arena.get_mod_type(md.pmd_type), arena)),
        SignatureItemDesc::Psig_modtype(mtd) => mtd
            .pmtd_type
            .map(|mod_type| {
                module_type_contains_spice_type_decl(arena.get_mod_type(mod_type), arena)
            })
            .unwrap_or(false),
        SignatureItemDesc::Psig_include(incl) => {
            module_type_contains_spice_type_decl(arena.get_mod_type(incl.pincl_mod), arena)
        }
        SignatureItemDesc::Psig_value(_)
        | SignatureItemDesc::Psig_typext(_)
        | SignatureItemDesc::Psig_exception(_)
        | SignatureItemDesc::Psig_open(_)
        | SignatureItemDesc::Psig_attribute(_)
        | SignatureItemDesc::Psig_extension(_) => false,
    }
}

fn structure_item_contains_spice_type_decl(item: &StructureItem, arena: &ParseArena) -> bool {
    match &*item.pstr_desc {
        StructureItemDesc::Pstr_type(inner) => {
            let (_, decls) = &**inner;
            decls
                .iter()
                .any(|decl| type_declaration_has_spice_attr(decl, arena))
        }
        StructureItemDesc::Pstr_module(mb) => {
            module_expr_contains_spice_type_decl(arena.get_mod_expr(mb.pmb_expr), arena)
        }
        StructureItemDesc::Pstr_recmodule(mbs) => mbs
            .iter()
            .any(|mb| module_expr_contains_spice_type_decl(arena.get_mod_expr(mb.pmb_expr), arena)),
        StructureItemDesc::Pstr_modtype(mtd) => mtd
            .pmtd_type
            .map(|mod_type| {
                module_type_contains_spice_type_decl(arena.get_mod_type(mod_type), arena)
            })
            .unwrap_or(false),
        StructureItemDesc::Pstr_include(incl) => {
            module_expr_contains_spice_type_decl(arena.get_mod_expr(incl.pincl_mod), arena)
        }
        StructureItemDesc::Pstr_eval(_)
        | StructureItemDesc::Pstr_value(_)
        | StructureItemDesc::Pstr_primitive(_)
        | StructureItemDesc::Pstr_typext(_)
        | StructureItemDesc::Pstr_exception(_)
        | StructureItemDesc::Pstr_open(_)
        | StructureItemDesc::Pstr_attribute(_)
        | StructureItemDesc::Pstr_extension(_) => false,
    }
}

struct LocCloner<'a> {
    arena: &'a mut ParseArena,
    error: Option<String>,
}

impl<'a> LocCloner<'a> {
    fn new(arena: &'a mut ParseArena) -> Self {
        Self { arena, error: None }
    }

    fn finish(self) -> SpiceResult<()> {
        match self.error {
            Some(error) => Err(error),
            None => Ok(()),
        }
    }

    fn expression_idx(&mut self, idx: &mut ExprIdx) {
        let mut expr = self.arena.get_expr(*idx).clone();
        self.expression(&mut expr);
        *idx = self.arena.push_expr(expr);
    }

    fn pattern_idx(&mut self, idx: &mut PatIdx) {
        let mut pat = self.arena.get_pat(*idx).clone();
        self.pattern(&mut pat);
        *idx = self.arena.push_pat(pat);
    }

    fn core_type_idx(&mut self, idx: &mut CoreTypeIdx) {
        let mut typ = self.arena.get_core_type(*idx).clone();
        self.core_type(&mut typ);
        *idx = self.arena.push_core_type(typ);
    }

    fn mod_expr_idx(&mut self, idx: &mut ModExprIdx) {
        let mut me = self.arena.get_mod_expr(*idx).clone();
        self.module_expr(&mut me);
        *idx = self.arena.push_mod_expr(me);
    }

    fn mod_type_idx(&mut self, idx: &mut ModTypeIdx) {
        let mut mt = self.arena.get_mod_type(*idx).clone();
        self.module_type(&mut mt);
        *idx = self.arena.push_mod_type(mt);
    }

    fn loc(&mut self, loc: &mut LocIdx) {
        if loc.is_none() || *loc == self.arena.dummy_loc() {
            return;
        }
        *loc = self.arena.clone_loc(*loc);
    }

    fn pos(&mut self, pos: &mut PosIdx) {
        if *pos == self.arena.none_pos() {
            return;
        }
        let position = *self.arena.get_position(*pos);
        *pos = self.arena.push_position(position);
    }

    fn located<T>(&mut self, loc: &mut Located<T>) {
        self.loc(&mut loc.loc);
    }

    fn arg_label(&mut self, label: &mut ArgLabel) {
        match label {
            ArgLabel::Labelled(loc) | ArgLabel::Optional(loc) => {
                // External spice PPX path does not preserve argument-label locations.
                // Keep labels but normalize their location to none.
                loc.loc = self.arena.none_loc();
            }
            ArgLabel::Nolabel => {}
        }
    }

    fn attributes(&mut self, attrs: &mut Attributes) {
        for attr in attrs {
            self.attribute(attr);
        }
    }

    fn attribute(&mut self, attr: &mut Attribute) {
        self.located(&mut attr.0);
        self.payload(&mut attr.1);
    }

    fn remove_res_async_attr(&mut self, attrs: &mut Attributes) {
        *attrs = attrs
            .iter()
            .filter(|attr| self.arena.get_string(attr.0.txt) != "res.async")
            .cloned()
            .collect::<Vec<_>>()
            .into();
    }

    fn normalize_jsx_fragment_expr_loc(&mut self, expr: &mut Expression) {
        let (opening, closing) = match &*expr.pexp_desc {
            ExpressionDesc::Pexp_jsx_element(jsx) => match jsx.as_ref() {
                JsxElement::Fragment(frag) => (frag.opening, frag.closing),
                _ => return,
            },
            _ => return,
        };
        if opening == self.arena.none_pos() || closing == self.arena.none_pos() {
            return;
        }

        let mut start = *self.arena.get_position(opening);
        let mut end = *self.arena.get_position(closing);
        if start.cnum < start.bol || end.cnum < end.bol {
            return;
        }

        // External spice PPX mapper keeps fragment loc from opening to closing
        // fragment positions.
        let start_idx = self.arena.push_position(start);
        let end_idx = self.arena.push_position(end);
        let ghost = self.arena.get_location(expr.pexp_loc).loc_ghost;
        expr.pexp_loc = self.arena.push_loc(start_idx, end_idx, ghost);
    }

    fn extension(&mut self, ext: &mut Extension) {
        self.located(&mut ext.0);
        self.payload(&mut ext.1);
    }

    fn payload(&mut self, payload: &mut Payload) {
        match payload {
            Payload::PStr(items) => {
                for item in items.iter_mut() {
                    self.structure_item(item);
                }
            }
            Payload::PSig(items) => {
                for item in items.iter_mut() {
                    self.signature_item(item);
                }
            }
            Payload::PTyp(typ) => self.core_type_idx(typ),
            Payload::PPat(inner) => {
                let (ref mut pat, ref mut guard) = **inner;
                self.pattern_idx(pat);
                if let Some(expr) = guard {
                    self.expression_idx(expr);
                }
            }
        }
    }

    fn core_type(&mut self, typ: &mut CoreType) {
        self.loc(&mut typ.ptyp_loc);
        self.attributes(&mut typ.ptyp_attributes);
        self.core_type_desc(&mut typ.ptyp_desc);
    }

    fn type_arg(&mut self, arg: &mut TypeArg) {
        self.attributes(&mut arg.attrs);
        self.arg_label(&mut arg.lbl);
        self.core_type_idx(&mut arg.typ);
    }

    fn package_type(&mut self, pkg: &mut PackageType) {
        self.located(&mut pkg.0);
        for (lid, typ) in pkg.1.iter_mut() {
            self.located(lid);
            self.core_type_idx(typ);
        }
    }

    fn row_field(&mut self, row: &mut RowField) {
        match row {
            RowField::Rtag(label, attrs, _, types) => {
                self.located(label);
                self.attributes(attrs);
                for group in types {
                    self.located(group);
                    for typ in group.txt.iter_mut() {
                        self.core_type_idx(typ);
                    }
                }
            }
            RowField::Rinherit(typ) => self.core_type_idx(typ),
        }
    }

    fn object_field(&mut self, field: &mut ObjectField) {
        match field {
            ObjectField::Otag(name, attrs, typ) => {
                self.located(name);
                self.attributes(attrs);
                self.core_type_idx(typ);
            }
            ObjectField::Oinherit(typ) => self.core_type_idx(typ),
        }
    }

    fn core_type_desc(&mut self, desc: &mut CoreTypeDesc) {
        match desc {
            CoreTypeDesc::Ptyp_any | CoreTypeDesc::Ptyp_var(_) => {}
            CoreTypeDesc::Ptyp_arrow(inner) => {
                let (ref mut arg, ref mut ret, arity) = **inner;
                let mut args = self.arena.nary_arrow_args(arg, arity).into_owned();
                for arg in &mut args {
                    self.type_arg(arg);
                }
                self.core_type_idx(ret);
                if args.len() > 1 {
                    self.arena.set_nary_arrow_args(arity, args.clone());
                }
                *arg = Box::new(args.remove(0));
            }
            CoreTypeDesc::Ptyp_tuple(types) => {
                for typ in types.iter_mut() {
                    self.core_type_idx(typ);
                }
            }
            CoreTypeDesc::Ptyp_constr(inner) => {
                let (ref mut lid, ref mut args) = **inner;
                self.located(lid);
                for typ in args.iter_mut() {
                    self.core_type_idx(typ);
                }
            }
            CoreTypeDesc::Ptyp_object(inner) => {
                let (ref mut fields, _) = **inner;
                for field in fields.iter_mut() {
                    self.object_field(field);
                }
            }
            CoreTypeDesc::Ptyp_alias(inner) => {
                let (ref mut typ, _) = **inner;
                self.core_type_idx(typ);
            }
            CoreTypeDesc::Ptyp_variant(inner) => {
                let (ref mut rows, _, ref labels) = **inner;
                for row in rows.iter_mut() {
                    self.row_field(row);
                }
                if let Some(labels) = labels {
                    let _ = labels;
                }
            }
            CoreTypeDesc::Ptyp_poly(inner) => {
                let (ref mut vars, ref mut typ) = **inner;
                for var in vars.iter_mut() {
                    self.located(var);
                }
                self.core_type_idx(typ);
            }
            CoreTypeDesc::Ptyp_package(pkg) => self.package_type(pkg),
            CoreTypeDesc::Ptyp_extension(ext) => self.extension(ext),
        }
    }

    fn pattern_record_field(&mut self, field: &mut PatternRecordField) {
        self.located(&mut field.lid);
        self.pattern_idx(&mut field.pat);
    }

    fn pattern(&mut self, pat: &mut Pattern) {
        self.loc(&mut pat.ppat_loc);
        self.attributes(&mut pat.ppat_attributes);
        self.pattern_desc(&mut pat.ppat_desc);
    }

    fn pattern_desc(&mut self, desc: &mut PatternDesc) {
        match desc {
            PatternDesc::Ppat_any
            | PatternDesc::Ppat_constant(_)
            | PatternDesc::Ppat_interval(_) => {}
            PatternDesc::Ppat_var(name) => self.located(name),
            PatternDesc::Ppat_alias(pat, name) => {
                self.pattern_idx(pat);
                self.located(name);
            }
            PatternDesc::Ppat_tuple(items) | PatternDesc::Ppat_array(items) => {
                for item in items.iter_mut() {
                    self.pattern_idx(item);
                }
            }
            PatternDesc::Ppat_construct(lid, args) => {
                self.located(lid);
                self.located(&mut **args);
                for arg in args.txt.iter_mut() {
                    self.pattern_idx(arg);
                }
            }
            PatternDesc::Ppat_variant(inner) => {
                let (_, ref mut args) = **inner;
                self.located(args);
                for arg in args.txt.iter_mut() {
                    self.pattern_idx(arg);
                }
            }
            PatternDesc::Ppat_record(inner) => {
                let (ref mut fields, _, ref mut record_rest) = **inner;
                for field in fields.iter_mut() {
                    self.pattern_record_field(field);
                }
                if let Some(rest) = record_rest {
                    self.loc(&mut rest.rest_loc);
                    self.located(&mut rest.rest_name);
                    if let Some(typ) = &mut rest.rest_type {
                        self.core_type_idx(typ);
                    }
                }
            }
            PatternDesc::Ppat_or(lhs, rhs) => {
                self.pattern_idx(lhs);
                self.pattern_idx(rhs);
            }
            PatternDesc::Ppat_constraint(inner) => {
                let (ref mut pat, ref mut typ) = **inner;
                self.pattern_idx(pat);
                self.core_type_idx(typ);
            }
            PatternDesc::Ppat_type(lid) => self.located(lid),
            PatternDesc::Ppat_unpack(name) => self.located(name),
            PatternDesc::Ppat_exception(pat) => self.pattern_idx(pat),
            PatternDesc::Ppat_extension(ext) => self.extension(ext),
        }
    }

    fn expression_record_field(&mut self, field: &mut ExpressionRecordField) {
        self.located(&mut field.lid);
        self.expression_idx(&mut field.expr);
    }

    fn case(&mut self, case: &mut Case) {
        // External spice PPX path drops bar positions in mapped cases.
        case.pc_bar = None;
        self.pattern_idx(&mut case.pc_lhs);
        if let Some(expr) = &mut case.pc_guard {
            self.expression_idx(expr);
        }
        self.expression_idx(&mut case.pc_rhs);
    }

    fn value_binding(&mut self, vb: &mut ValueBinding) {
        let value_constraint = self.arena.value_constraint(vb.pvb_pat).cloned();
        self.pattern_idx(&mut vb.pvb_pat);
        self.expression_idx(&mut vb.pvb_expr);
        self.attributes(&mut vb.pvb_attributes);
        self.loc(&mut vb.pvb_loc);
        if let Some(mut constraint) = value_constraint {
            for newtype in &mut constraint.pvc_newtypes {
                self.located(newtype);
            }
            self.core_type_idx(&mut constraint.pvc_type);
            self.arena
                .set_value_constraint(vb.pvb_pat, constraint, vb.pvb_expr, vb.pvb_loc);
        }
    }

    fn value_description(&mut self, vd: &mut ValueDescription) {
        self.located(&mut vd.pval_name);
        self.core_type_idx(&mut vd.pval_type);
        self.attributes(&mut vd.pval_attributes);
        self.loc(&mut vd.pval_loc);
    }

    fn jsx_element(&mut self, element: &mut JsxElement) {
        if let JsxElement::Unary(unary) = element {
            // External spice PPX path normalizes unary JSX nodes into container
            // nodes with empty children.
            let props = std::mem::take(&mut unary.props);
            let mut container = JsxContainerElement {
                tag_name_start: unary.tag_name.clone(),
                opening_end: self.arena.none_pos(),
                props,
                children: vec![],
                closing_tag: None,
            };
            self.jsx_container_element(&mut container);
            *element = JsxElement::Container(container);
            return;
        }
        match element {
            JsxElement::Fragment(fragment) => self.jsx_fragment(fragment),
            JsxElement::Container(container) => self.jsx_container_element(container),
            JsxElement::Unary(_) => {}
        }
    }

    fn jsx_fragment(&mut self, fragment: &mut JsxFragment) {
        self.pos(&mut fragment.opening);
        for child in fragment.children.iter_mut() {
            self.expression_idx(child);
        }
        self.pos(&mut fragment.closing);
    }

    fn jsx_unary_element(&mut self, element: &mut JsxUnaryElement) {
        self.located(&mut element.tag_name);
        for prop in element.props.iter_mut() {
            self.jsx_prop(prop);
        }
    }

    fn jsx_container_element(&mut self, element: &mut JsxContainerElement) {
        self.located(&mut element.tag_name_start);
        self.pos(&mut element.opening_end);
        for prop in element.props.iter_mut() {
            self.jsx_prop(prop);
        }
        for child in element.children.iter_mut() {
            self.expression_idx(child);
        }
        if let Some(tag) = &mut element.closing_tag {
            self.jsx_closing_tag(tag);
        }
    }

    fn jsx_closing_tag(&mut self, tag: &mut JsxClosingTag) {
        self.pos(&mut tag.start);
        self.located(&mut tag.name);
        self.pos(&mut tag.end);
    }

    fn jsx_prop(&mut self, prop: &mut JsxProp) {
        match prop {
            JsxProp::Punning { name, .. } => self.located(name),
            JsxProp::Value { name, value, .. } => {
                self.located(name);
                self.expression_idx(value);
            }
            JsxProp::Spreading { loc, expr } => {
                self.loc(loc);
                self.expression_idx(expr);
            }
        }
    }

    fn expression(&mut self, expr: &mut Expression) {
        self.loc(&mut expr.pexp_loc);
        self.attributes(&mut expr.pexp_attributes);
        self.expression_desc(&mut expr.pexp_desc);
        self.normalize_jsx_fragment_expr_loc(expr);
        let is_async_fun = matches!(
            &*expr.pexp_desc,
            ExpressionDesc::Pexp_fun(inner) if inner.is_async
        );
        if is_async_fun {
            self.remove_res_async_attr(&mut expr.pexp_attributes);
        }
    }

    fn expression_desc(&mut self, desc: &mut ExpressionDesc) {
        match desc {
            ExpressionDesc::Pexp_ident(lid) => self.located(lid),
            ExpressionDesc::Pexp_constant(_) => {}
            ExpressionDesc::Pexp_break | ExpressionDesc::Pexp_continue => {}
            ExpressionDesc::Pexp_template(template) => {
                for segment in &mut template.source_segments {
                    self.located(segment);
                }
                for value in &mut template.values {
                    self.expression_idx(value);
                }
            }
            ExpressionDesc::Pexp_tagged_template(template) => {
                self.expression_idx(&mut template.tag);
                for segment in &mut template.raw_sources {
                    self.located(segment);
                }
                for value in &mut template.values {
                    self.expression_idx(value);
                }
            }
            ExpressionDesc::Pexp_let(inner) => {
                let (_, ref mut bindings, ref mut body) = **inner;
                for binding in bindings.iter_mut() {
                    self.value_binding(binding);
                }
                self.expression_idx(body);
            }
            ExpressionDesc::Pexp_fun(inner) => {
                let mut params = self.arena.nary_fun_params(inner).into_owned();
                let mut newtypes = self.arena.nary_fun_newtypes(inner).to_vec();
                let unknown_arity = self.arena.nary_fun_unknown_arity(inner);
                for (newtype, attrs) in &mut newtypes {
                    self.located(newtype);
                    self.attributes(attrs);
                }
                for param in &mut params {
                    self.attributes(&mut param.p_attrs);
                    self.arg_label(&mut param.p_lbl);
                    if let Some(default) = &mut param.p_default {
                        self.expression_idx(default);
                    }
                    self.pattern_idx(&mut param.p_pat);
                }
                self.expression_idx(&mut inner.rhs);
                let first = params
                    .first()
                    .expect("Pexp_fun must contain at least one parameter")
                    .clone();
                inner.arg_label = first.p_lbl;
                inner.default = first.p_default;
                inner.lhs = first.p_pat;
                if params.len() > 1 {
                    self.arena
                        .set_nary_fun_params(inner.arity, params, unknown_arity);
                }
                if !newtypes.is_empty() {
                    self.arena.set_nary_fun_newtypes(inner.lhs, newtypes);
                }
            }
            ExpressionDesc::Pexp_apply(inner) => {
                let PexpApply {
                    ref mut funct,
                    ref mut args,
                    ..
                } = **inner;
                self.expression_idx(funct);
                for (label, arg) in args.iter_mut() {
                    self.arg_label(label);
                    self.expression_idx(arg);
                }
            }
            ExpressionDesc::Pexp_match(inner) | ExpressionDesc::Pexp_try(inner) => {
                let (ref mut expr, ref mut cases) = **inner;
                self.expression_idx(expr);
                for case in cases.iter_mut() {
                    self.case(case);
                }
            }
            ExpressionDesc::Pexp_tuple(items) | ExpressionDesc::Pexp_array(items) => {
                for item in items.iter_mut() {
                    self.expression_idx(item);
                }
            }
            ExpressionDesc::Pexp_construct(lid, args) => {
                self.located(lid);
                self.located(&mut **args);
                for expr in args.txt.iter_mut() {
                    self.expression_idx(expr);
                }
            }
            ExpressionDesc::Pexp_variant(inner) => {
                let (_, ref mut args) = **inner;
                self.located(args);
                for expr in args.txt.iter_mut() {
                    self.expression_idx(expr);
                }
            }
            ExpressionDesc::Pexp_record(inner) => {
                let (ref mut fields, ref mut base) = **inner;
                for field in fields.iter_mut() {
                    self.expression_record_field(field);
                }
                if let Some(expr) = base {
                    self.expression_idx(expr);
                }
            }
            ExpressionDesc::Pexp_field(expr, lid) => {
                self.expression_idx(expr);
                self.located(lid);
            }
            ExpressionDesc::Pexp_setfield(inner) => {
                let (ref mut expr, ref mut lid, ref mut rhs) = **inner;
                self.expression_idx(expr);
                self.located(lid);
                self.expression_idx(rhs);
            }
            ExpressionDesc::Pexp_ifthenelse(inner) => {
                let (ref mut cond, ref mut then_expr, ref mut else_expr) = **inner;
                self.expression_idx(cond);
                self.expression_idx(then_expr);
                if let Some(expr) = else_expr {
                    self.expression_idx(expr);
                }
            }
            ExpressionDesc::Pexp_ternary(inner) => {
                let (ref mut cond, ref mut consequent, ref mut alternate) = **inner;
                self.expression_idx(cond);
                self.expression_idx(consequent);
                self.expression_idx(alternate);
            }
            ExpressionDesc::Pexp_braces(braces) => {
                self.loc(&mut braces.braces_loc);
                self.expression_idx(&mut braces.expr);
            }
            ExpressionDesc::Pexp_regexp(_) => {}
            ExpressionDesc::Pexp_sequence(first, second)
            | ExpressionDesc::Pexp_while(first, second) => {
                self.expression_idx(first);
                self.expression_idx(second);
            }
            ExpressionDesc::Pexp_for(inner) => {
                let (ref mut pat, ref mut start, ref mut end, _, ref mut body) = **inner;
                self.pattern_idx(pat);
                self.expression_idx(start);
                self.expression_idx(end);
                self.expression_idx(body);
            }
            ExpressionDesc::Pexp_for_of(inner) | ExpressionDesc::Pexp_for_await_of(inner) => {
                let (ref mut pat, ref mut iterable, ref mut body) = **inner;
                self.pattern_idx(pat);
                self.expression_idx(iterable);
                self.expression_idx(body);
            }
            ExpressionDesc::Pexp_constraint(inner) => {
                let (ref mut expr, ref mut typ) = **inner;
                self.expression_idx(expr);
                self.core_type_idx(typ);
            }
            ExpressionDesc::Pexp_coerce(inner) => {
                let (ref mut expr, ref mut from, ref mut to) = **inner;
                self.expression_idx(expr);
                if let Some(from) = from {
                    self.core_type_idx(from);
                }
                self.core_type_idx(to);
            }
            ExpressionDesc::Pexp_object_get(inner) => {
                let (ref mut expr, ref mut method) = **inner;
                self.expression_idx(expr);
                self.located(method);
            }
            ExpressionDesc::Pexp_object_set(inner) => {
                let (ref mut expr, ref mut name, ref mut value) = **inner;
                self.expression_idx(expr);
                self.located(name);
                self.expression_idx(value);
            }
            ExpressionDesc::Pexp_object_literal(fields) => {
                for (name, expr) in fields.iter_mut() {
                    self.located(name);
                    self.expression_idx(expr);
                }
            }
            ExpressionDesc::Pexp_letmodule(inner) => {
                let (ref mut name, ref mut module_expr, ref mut body) = **inner;
                self.located(name);
                self.mod_expr_idx(module_expr);
                self.expression_idx(body);
            }
            ExpressionDesc::Pexp_letexception(inner) => {
                let (ref mut ext, ref mut body) = **inner;
                self.extension_constructor(ext);
                self.expression_idx(body);
            }
            ExpressionDesc::Pexp_assert(expr) => self.expression_idx(expr),
            ExpressionDesc::Pexp_newtype(inner) => {
                let (ref mut name, ref mut expr) = **inner;
                self.located(name);
                self.expression_idx(expr);
            }
            ExpressionDesc::Pexp_pack(module_expr) => self.mod_expr_idx(module_expr),
            ExpressionDesc::Pexp_open(inner) => {
                let (_, ref mut lid, ref mut expr) = **inner;
                self.located(lid);
                self.expression_idx(expr);
            }
            ExpressionDesc::Pexp_extension(ext) => self.extension(ext),
            ExpressionDesc::Pexp_await(expr) => self.expression_idx(expr),
            ExpressionDesc::Pexp_jsx_element(element) => self.jsx_element(element),
            ExpressionDesc::Pexp_inline_for(inner) => {
                let (ref mut _pat, ref mut collection, ref mut body) = **inner;
                self.expression_idx(collection);
                self.expression_idx(body);
            }
            ExpressionDesc::Pexp_comptime_typeinfo(_)
            | ExpressionDesc::Pexp_comptime_typename(_) => {
                // No sub-expressions to walk
            }
            ExpressionDesc::Pexp_comptime_field(inner) => {
                let (ref mut value, ref mut field) = **inner;
                self.expression_idx(value);
                self.expression_idx(field);
            }
            ExpressionDesc::Pexp_comptime_compile_error(expr) => {
                self.expression_idx(expr);
            }
            ExpressionDesc::Pexp_comptime_record(inner) => {
                let (ref _ct, ref mut fields_expr) = **inner;
                self.expression_idx(fields_expr);
            }
            ExpressionDesc::Pexp_comptime_variant(inner) => {
                let (ref _ct, ref mut expr, ref mut opt_expr) = **inner;
                self.expression_idx(expr);
                if let Some(e) = opt_expr {
                    self.expression_idx(e);
                }
            }
            ExpressionDesc::Pexp_comptime_build_variant(e) => {
                self.expression_idx(e);
            }
            ExpressionDesc::Pexp_comptime_variant_case(e) => {
                self.expression_idx(e);
            }
            ExpressionDesc::Pexp_comptime_build_record(e) => {
                self.expression_idx(e);
            }
            ExpressionDesc::Pexp_comptime_record_field(e) => {
                self.expression_idx(e);
            }
        }
    }

    fn module_expr(&mut self, module_expr: &mut ModuleExpr) {
        self.loc(&mut module_expr.pmod_loc);
        self.attributes(&mut module_expr.pmod_attributes);
        self.module_expr_desc(&mut module_expr.pmod_desc);
    }

    fn module_expr_desc(&mut self, desc: &mut ModuleExprDesc) {
        match desc {
            ModuleExprDesc::Pmod_ident(lid) => self.located(lid),
            ModuleExprDesc::Pmod_structure(items) => {
                let original = std::mem::take(items);
                match map_structure_items_with_mapper(&original, self.arena, true) {
                    Ok(mapped) => **items = mapped,
                    Err(error) => {
                        *items = original;
                        self.error = Some(error);
                    }
                }
            }
            ModuleExprDesc::Pmod_functor(inner) => {
                let (ref mut name, ref mut mty, ref mut body) = **inner;
                self.located(name);
                if let Some(mty) = mty {
                    self.mod_type_idx(mty);
                }
                self.mod_expr_idx(body);
            }
            ModuleExprDesc::Pmod_apply(lhs, rhs) => {
                self.mod_expr_idx(lhs);
                self.mod_expr_idx(rhs);
            }
            ModuleExprDesc::Pmod_constraint(expr, mty) => {
                self.mod_expr_idx(expr);
                self.mod_type_idx(mty);
            }
            ModuleExprDesc::Pmod_unpack(expr) => self.expression_idx(expr),
            ModuleExprDesc::Pmod_extension(ext) => self.extension(ext),
        }
    }

    fn module_type(&mut self, module_type: &mut ModuleType) {
        self.loc(&mut module_type.pmty_loc);
        self.attributes(&mut module_type.pmty_attributes);
        self.module_type_desc(&mut module_type.pmty_desc);
    }

    fn with_constraint(&mut self, constraint: &mut WithConstraint) {
        match constraint {
            WithConstraint::Pwith_type(lid, decl) | WithConstraint::Pwith_typesubst(lid, decl) => {
                self.located(lid);
                self.type_declaration(decl);
            }
            WithConstraint::Pwith_module(lid, rhs) | WithConstraint::Pwith_modsubst(lid, rhs) => {
                self.located(lid);
                self.located(rhs);
            }
        }
    }

    fn module_type_desc(&mut self, desc: &mut ModuleTypeDesc) {
        match desc {
            ModuleTypeDesc::Pmty_ident(lid) | ModuleTypeDesc::Pmty_alias(lid) => {
                self.located(lid);
            }
            ModuleTypeDesc::Pmty_signature(items) => {
                let original = std::mem::take(items);
                match map_signature_items_with_mapper(&original, self.arena, true) {
                    Ok(mapped) => **items = mapped,
                    Err(error) => {
                        *items = original;
                        self.error = Some(error);
                    }
                }
            }
            ModuleTypeDesc::Pmty_functor(inner) => {
                let (ref mut name, ref mut arg, ref mut body) = **inner;
                self.located(name);
                if let Some(arg) = arg {
                    self.mod_type_idx(arg);
                }
                self.mod_type_idx(body);
            }
            ModuleTypeDesc::Pmty_with(inner) => {
                let (ref mut mty, ref mut constraints) = **inner;
                self.mod_type_idx(mty);
                for constraint in constraints.iter_mut() {
                    self.with_constraint(constraint);
                }
            }
            ModuleTypeDesc::Pmty_typeof(expr) => self.mod_expr_idx(expr),
            ModuleTypeDesc::Pmty_extension(ext) => self.extension(ext),
        }
    }

    fn module_binding(&mut self, binding: &mut ModuleBinding) {
        self.located(&mut binding.pmb_name);
        self.mod_expr_idx(&mut binding.pmb_expr);
        self.attributes(&mut binding.pmb_attributes);
        self.loc(&mut binding.pmb_loc);
    }

    fn module_declaration(&mut self, decl: &mut ModuleDeclaration) {
        self.located(&mut decl.pmd_name);
        self.mod_type_idx(&mut decl.pmd_type);
        self.attributes(&mut decl.pmd_attributes);
        self.loc(&mut decl.pmd_loc);
    }

    fn module_type_declaration(&mut self, decl: &mut ModuleTypeDeclaration) {
        self.located(&mut decl.pmtd_name);
        if let Some(mty) = &mut decl.pmtd_type {
            self.mod_type_idx(mty);
        }
        self.attributes(&mut decl.pmtd_attributes);
        self.loc(&mut decl.pmtd_loc);
    }

    fn open_description(&mut self, open: &mut OpenDescription) {
        self.located(&mut open.popen_lid);
        self.loc(&mut open.popen_loc);
        self.attributes(&mut open.popen_attributes);
    }

    fn include_declaration(&mut self, include: &mut IncludeDeclaration) {
        self.mod_expr_idx(&mut include.pincl_mod);
        self.loc(&mut include.pincl_loc);
        self.attributes(&mut include.pincl_attributes);
    }

    fn include_description(&mut self, include: &mut IncludeDescription) {
        self.mod_type_idx(&mut include.pincl_mod);
        self.loc(&mut include.pincl_loc);
        self.attributes(&mut include.pincl_attributes);
    }

    fn constructor_arguments(&mut self, args: &mut ConstructorArguments) {
        match args {
            ConstructorArguments::Pcstr_tuple(types) => {
                for typ in types {
                    self.core_type_idx(typ);
                }
            }
            ConstructorArguments::Pcstr_record(fields) => {
                for field in fields {
                    self.label_declaration(field);
                }
            }
        }
    }

    fn constructor_declaration(&mut self, decl: &mut ConstructorDeclaration) {
        self.located(&mut decl.pcd_name);
        self.constructor_arguments(&mut decl.pcd_args);
        if let Some(res) = &mut decl.pcd_res {
            self.core_type_idx(res);
        }
        self.loc(&mut decl.pcd_loc);
        self.attributes(&mut decl.pcd_attributes);
    }

    fn label_declaration(&mut self, decl: &mut LabelDeclaration) {
        self.located(&mut decl.pld_name);
        self.core_type_idx(&mut decl.pld_type);
        self.loc(&mut decl.pld_loc);
        self.attributes(&mut decl.pld_attributes);
    }

    fn type_kind(&mut self, kind: &mut TypeKind) {
        match kind {
            TypeKind::Ptype_abstract | TypeKind::Ptype_open => {}
            TypeKind::Ptype_variant(constructors) => {
                for decl in constructors {
                    self.constructor_declaration(decl);
                }
            }
            TypeKind::Ptype_record(fields) => {
                for field in fields {
                    self.label_declaration(field);
                }
            }
        }
    }

    fn type_declaration(&mut self, decl: &mut TypeDeclaration) {
        self.located(&mut decl.ptype_name);
        for (typ, _) in decl.ptype_params.iter_mut() {
            self.core_type_idx(typ);
        }
        for (lhs, rhs, loc) in decl.ptype_cstrs.iter_mut() {
            self.core_type_idx(lhs);
            self.core_type_idx(rhs);
            self.loc(loc);
        }
        self.type_kind(&mut decl.ptype_kind);
        if let Some(manifest) = &mut decl.ptype_manifest {
            self.core_type_idx(manifest);
        }
        self.attributes(&mut decl.ptype_attributes);
        self.loc(&mut decl.ptype_loc);
    }

    fn type_extension(&mut self, ext: &mut TypeExtension) {
        self.located(&mut ext.ptyext_path);
        for (typ, _) in ext.ptyext_params.iter_mut() {
            self.core_type_idx(typ);
        }
        for ctor in ext.ptyext_constructors.iter_mut() {
            self.extension_constructor(ctor);
        }
        self.attributes(&mut ext.ptyext_attributes);
    }

    fn extension_constructor(&mut self, ext: &mut ExtensionConstructor) {
        self.located(&mut ext.pext_name);
        self.extension_constructor_kind(&mut ext.pext_kind);
        self.loc(&mut ext.pext_loc);
        self.attributes(&mut ext.pext_attributes);
    }

    fn extension_constructor_kind(&mut self, kind: &mut ExtensionConstructorKind) {
        match kind {
            ExtensionConstructorKind::Pext_decl(args, res) => {
                self.constructor_arguments(args);
                if let Some(res) = res {
                    self.core_type_idx(res);
                }
            }
            ExtensionConstructorKind::Pext_rebind(lid) => self.located(lid),
        }
    }

    fn structure_item(&mut self, item: &mut StructureItem) {
        self.loc(&mut item.pstr_loc);
        self.structure_item_desc(&mut item.pstr_desc);
    }

    fn structure_item_desc(&mut self, desc: &mut StructureItemDesc) {
        match desc {
            StructureItemDesc::Pstr_eval(inner) => {
                let (ref mut expr, ref mut attrs) = **inner;
                self.expression_idx(expr);
                self.attributes(attrs);
            }
            StructureItemDesc::Pstr_value(inner) => {
                let (_, ref mut bindings) = **inner;
                for binding in bindings.iter_mut() {
                    self.value_binding(binding);
                }
            }
            StructureItemDesc::Pstr_primitive(vd) => self.value_description(vd),
            StructureItemDesc::Pstr_type(inner) => {
                let (_, ref mut decls) = **inner;
                for decl in decls.iter_mut() {
                    self.type_declaration(decl);
                }
            }
            StructureItemDesc::Pstr_typext(ext) => self.type_extension(ext),
            StructureItemDesc::Pstr_exception(ext) => self.extension_constructor(ext),
            StructureItemDesc::Pstr_module(binding) => self.module_binding(binding),
            StructureItemDesc::Pstr_recmodule(bindings) => {
                for binding in bindings.iter_mut() {
                    self.module_binding(binding);
                }
            }
            StructureItemDesc::Pstr_modtype(decl) => self.module_type_declaration(decl),
            StructureItemDesc::Pstr_open(open) => self.open_description(open),
            StructureItemDesc::Pstr_include(include) => self.include_declaration(include),
            StructureItemDesc::Pstr_attribute(attr) => self.attribute(attr),
            StructureItemDesc::Pstr_extension(inner) => {
                let (ref mut ext, ref mut attrs) = **inner;
                self.extension(ext);
                self.attributes(attrs);
            }
        }
    }

    fn signature_item(&mut self, item: &mut SignatureItem) {
        self.loc(&mut item.psig_loc);
        self.signature_item_desc(&mut item.psig_desc);
    }

    fn signature_item_desc(&mut self, desc: &mut SignatureItemDesc) {
        match desc {
            SignatureItemDesc::Psig_value(vd) => self.value_description(vd),
            SignatureItemDesc::Psig_type(inner) => {
                let (_, ref mut decls) = **inner;
                for decl in decls.iter_mut() {
                    self.type_declaration(decl);
                }
            }
            SignatureItemDesc::Psig_typext(ext) => self.type_extension(ext),
            SignatureItemDesc::Psig_exception(ext) => self.extension_constructor(ext),
            SignatureItemDesc::Psig_module(decl) => self.module_declaration(decl),
            SignatureItemDesc::Psig_recmodule(decls) => {
                for decl in decls.iter_mut() {
                    self.module_declaration(decl);
                }
            }
            SignatureItemDesc::Psig_modtype(decl) => self.module_type_declaration(decl),
            SignatureItemDesc::Psig_open(open) => self.open_description(open),
            SignatureItemDesc::Psig_include(include) => self.include_description(include),
            SignatureItemDesc::Psig_attribute(attr) => self.attribute(attr),
            SignatureItemDesc::Psig_extension(inner) => {
                let (ref mut ext, ref mut attrs) = **inner;
                self.extension(ext);
                self.attributes(attrs);
            }
        }
    }
}

fn clone_mapped_structure_item(
    item: &StructureItem,
    arena: &mut ParseArena,
) -> SpiceResult<StructureItem> {
    let mut mapped_item = item.clone();
    let mut cloner = LocCloner::new(arena);
    cloner.structure_item(&mut mapped_item);
    cloner.finish()?;
    Ok(mapped_item)
}

fn clone_mapped_signature_item(
    item: &SignatureItem,
    arena: &mut ParseArena,
) -> SpiceResult<SignatureItem> {
    let mut mapped_item = item.clone();
    let mut cloner = LocCloner::new(arena);
    cloner.signature_item(&mut mapped_item);
    cloner.finish()?;
    Ok(mapped_item)
}

fn map_structure_item_spice(
    item: &StructureItem,
    arena: &mut ParseArena,
    mapper_active: bool,
) -> SpiceResult<Vec<StructureItem>> {
    let mut mapped_item = item.clone();
    let contains_spice_subtree = structure_item_contains_spice_type_decl(item, arena);

    match &*item.pstr_desc {
        StructureItemDesc::Pstr_type(inner) => {
            let (ref rec_flag, ref decls) = **inner;
            let mut vbs = Vec::new();
            for decl in decls {
                vbs.extend(map_type_decl_structure(decl, arena)?);
            }

            if vbs.is_empty() {
                if mapper_active {
                    mapped_item = clone_mapped_structure_item(item, arena)?;
                }
                Ok(vec![mapped_item])
            } else {
                mapped_item = clone_mapped_structure_item(item, arena)?;

                let value_item = StructureItem {
                    pstr_desc: Box::new(StructureItemDesc::Pstr_value(Box::new((*rec_flag, vbs)))),
                    pstr_loc: arena.dummy_loc(),
                };
                Ok(vec![mapped_item, value_item])
            }
        }
        _ => {
            if mapper_active || contains_spice_subtree {
                mapped_item = clone_mapped_structure_item(item, arena)?;
            }
            Ok(vec![mapped_item])
        }
    }
}

fn add_encoder_params(
    param_names: &[String],
    result_type: CoreType,
    arena: &mut ParseArena,
) -> CoreType {
    if param_names.is_empty() {
        return result_type;
    }
    let mut res = result_type;
    for name in param_names.iter().rev() {
        let arg_type = mk_type_arrow_no_arity(mk_type_var(name, arena), ctyp_json_t(arena), arena);
        res = mk_type_arrow(arg_type, res, arena);
    }
    res
}

fn make_result_type(value_type: CoreType, arena: &mut ParseArena) -> CoreType {
    let decode_error = mk_type_constr_with_lid_loc(
        lident_path_parse(arena, &["Spice", "decodeError"]),
        arena.dummy_loc(),
        vec![],
        arena,
    );
    let result_lid = {
        let lident_name = arena.intern_string("result");
        arena.push_lident_from_idx(lident_name)
    };
    mk_type_constr_with_lid_loc(
        result_lid,
        arena.dummy_loc(),
        vec![value_type, decode_error],
        arena,
    )
}

fn add_decoder_params(
    param_names: &[String],
    result_type: CoreType,
    arena: &mut ParseArena,
) -> CoreType {
    if param_names.is_empty() {
        return result_type;
    }
    let mut res = result_type;
    for name in param_names.iter().rev() {
        let decoder_param = mk_type_arrow(
            ctyp_json_t(arena),
            make_result_type(mk_type_var(name, arena), arena),
            arena,
        );
        res = mk_type_arrow(decoder_param, res, arena);
    }
    res
}

fn generate_sig_decls(
    settings: GeneratorSettings,
    type_name: &str,
    param_names: &[String],
    arena: &mut ParseArena,
) -> Vec<SignatureItem> {
    let mut decls = Vec::new();

    let type_args: Vec<CoreType> = param_names.iter().map(|p| mk_type_var(p, arena)).collect();
    let type_lid = {
        let lident_name = arena.intern_string(type_name);
        arena.push_lident_from_idx(lident_name)
    };
    let value_type = mk_type_constr(type_lid, type_args, arena);

    if settings.do_encode {
        for suffix in [ENCODER_FUNC_SUFFIX, VALUE_ENCODER_FUNC_SUFFIX] {
            let base = mk_type_arrow(value_type.clone(), ctyp_json_t(arena), arena);
            let ty = add_encoder_params(param_names, base, arena);
            let name = format!("{}{}", type_name, suffix);
            let name_idx = arena.push_string(name);
            let vd = ValueDescription {
                pval_name: Located::new(name_idx, arena.none_loc()),
                pval_type: arena.push_core_type(ty),
                pval_prim: None,
                pval_attributes: Attributes::new(),
                pval_loc: arena.dummy_loc(),
            };
            decls.push(SignatureItem {
                psig_desc: Box::new(SignatureItemDesc::Psig_value(Box::new(vd))),
                psig_loc: arena.dummy_loc(),
            });
        }
    }

    if settings.do_decode {
        let base = mk_type_arrow(
            ctyp_json_t(arena),
            make_result_type(value_type, arena),
            arena,
        );
        let ty = add_decoder_params(param_names, base, arena);
        let name = format!("{}{}", type_name, DECODER_FUNC_SUFFIX);
        let name_idx = arena.push_string(name);
        let vd = ValueDescription {
            pval_name: Located::new(name_idx, arena.none_loc()),
            pval_type: arena.push_core_type(ty),
            pval_prim: None,
            pval_attributes: Attributes::new(),
            pval_loc: arena.dummy_loc(),
        };
        decls.push(SignatureItem {
            psig_desc: Box::new(SignatureItemDesc::Psig_value(Box::new(vd))),
            psig_loc: arena.dummy_loc(),
        });
    }

    decls
}

fn map_signature_item_spice(
    item: &SignatureItem,
    arena: &mut ParseArena,
    mapper_active: bool,
) -> SpiceResult<Vec<SignatureItem>> {
    let mut mapped_item = item.clone();
    let contains_spice_subtree = signature_item_contains_spice_type_decl(item, arena);

    match &*item.psig_desc {
        SignatureItemDesc::Psig_type(inner) => {
            let (_, ref decls) = **inner;
            let mut generated = Vec::new();
            for decl in decls {
                let settings =
                    match get_generator_settings_from_attributes(&decl.ptype_attributes, arena) {
                        Ok(v) => v,
                        Err(e) => return Err(e),
                    };
                if let Some(settings) = settings {
                    let param_names = get_param_names(&decl.ptype_params, arena)?;
                    let type_name = arena.get_string(decl.ptype_name.txt).to_string();
                    generated.extend(generate_sig_decls(
                        settings,
                        &type_name,
                        &param_names,
                        arena,
                    ));
                }
            }
            if generated.is_empty() {
                if mapper_active {
                    mapped_item = clone_mapped_signature_item(item, arena)?;
                }
                Ok(vec![mapped_item])
            } else {
                mapped_item = clone_mapped_signature_item(item, arena)?;

                let mut out = Vec::new();
                out.push(mapped_item);
                out.extend(generated);
                Ok(out)
            }
        }
        _ => {
            if mapper_active || contains_spice_subtree {
                mapped_item = clone_mapped_signature_item(item, arena)?;
            }
            Ok(vec![mapped_item])
        }
    }
}

fn structure_contains_spice_type_decl(structure: &[StructureItem], arena: &ParseArena) -> bool {
    structure
        .iter()
        .any(|item| structure_item_contains_spice_type_decl(item, arena))
}

fn signature_contains_spice_type_decl(signature: &[SignatureItem], arena: &ParseArena) -> bool {
    signature
        .iter()
        .any(|item| signature_item_contains_spice_type_decl(item, arena))
}

/// Returns true when the Spice mapper should be applied over the whole structure.
pub fn structure_uses_spice_mapper(structure: &[StructureItem], arena: &ParseArena) -> bool {
    structure_contains_spice_type_decl(structure, arena)
}

/// Returns true when the Spice mapper should be applied over the whole signature.
pub fn signature_uses_spice_mapper(signature: &[SignatureItem], arena: &ParseArena) -> bool {
    signature_contains_spice_type_decl(signature, arena)
}

pub fn expand_structure_item_with_mapper(
    item: &StructureItem,
    arena: &mut ParseArena,
    mapper_active: bool,
) -> SpiceResult<Vec<StructureItem>> {
    if !arena.builtin_spice_enabled() {
        return Ok(vec![item.clone()]);
    }
    map_structure_item_spice(item, arena, mapper_active)
}

pub fn expand_structure_item(
    item: &StructureItem,
    arena: &mut ParseArena,
) -> SpiceResult<Vec<StructureItem>> {
    if !arena.builtin_spice_enabled() {
        return Ok(vec![item.clone()]);
    }
    let mapper_active = structure_item_contains_spice_type_decl(item, arena);
    map_structure_item_spice(item, arena, mapper_active)
}

fn map_structure_items_with_mapper(
    structure: &[StructureItem],
    arena: &mut ParseArena,
    mapper_active: bool,
) -> SpiceResult<Vec<StructureItem>> {
    let mut expanded = Vec::new();
    for item in structure {
        expanded.extend(map_structure_item_spice(item, arena, mapper_active)?);
    }
    Ok(expanded)
}

pub fn expand_structure(
    structure: &[StructureItem],
    arena: &mut ParseArena,
) -> SpiceResult<Vec<StructureItem>> {
    if !arena.builtin_spice_enabled() {
        return Ok(structure.to_vec());
    }
    let mapper_active = structure_contains_spice_type_decl(structure, arena);
    map_structure_items_with_mapper(structure, arena, mapper_active)
}

pub fn expand_signature_item_with_mapper(
    item: &SignatureItem,
    arena: &mut ParseArena,
    mapper_active: bool,
) -> SpiceResult<Vec<SignatureItem>> {
    if !arena.builtin_spice_enabled() {
        return Ok(vec![item.clone()]);
    }
    map_signature_item_spice(item, arena, mapper_active)
}

pub fn expand_signature_item(
    item: &SignatureItem,
    arena: &mut ParseArena,
) -> SpiceResult<Vec<SignatureItem>> {
    if !arena.builtin_spice_enabled() {
        return Ok(vec![item.clone()]);
    }
    let mapper_active = signature_item_contains_spice_type_decl(item, arena);
    map_signature_item_spice(item, arena, mapper_active)
}

fn map_signature_items_with_mapper(
    signature: &[SignatureItem],
    arena: &mut ParseArena,
    mapper_active: bool,
) -> SpiceResult<Vec<SignatureItem>> {
    let mut expanded = Vec::new();
    for item in signature {
        expanded.extend(map_signature_item_spice(item, arena, mapper_active)?);
    }
    Ok(expanded)
}
