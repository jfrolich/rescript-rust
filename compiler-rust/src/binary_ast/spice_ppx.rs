//! Internal Spice PPX implementation.
//!
//! This is a direct port of the OCaml ppx_spice implementation, adapted to
//! ReScript's current AST representation (arity fields, partial flags, etc.).

use crate::parse_arena::{Located, LocIdx, ParseArena, StrIdx, LidentIdx};
use crate::parser::ast::{
    ArgLabel, Attribute, Case, Constant, CoreType, CoreTypeDesc, Expression, ExpressionDesc,
    ExpressionRecordField, LabelDeclaration, Pattern, PatternDesc, Payload, RecFlag, RowField,
    SignatureItem, SignatureItemDesc, StructureItem, StructureItemDesc, TypeArg, TypeDeclaration,
    TypeKind, ValueBinding, ValueDescription,
};
use crate::parser::longident::Longident;

const ANNOTATION_NAME: &str = "spice";
const ENCODER_FUNC_SUFFIX: &str = "_encode";
const DECODER_FUNC_SUFFIX: &str = "_decode";
const ENCODER_VAR_PREFIX: &str = "encoder_";
const DECODER_VAR_PREFIX: &str = "decoder_";

#[derive(Clone, Copy, Debug)]
struct GeneratorSettings {
    do_encode: bool,
    do_decode: bool,
}

#[derive(Clone, Debug)]
struct ParsedRecordField {
    name: String,
    key: Expression,
    field: Expression,
    codecs: (Option<Expression>, Option<Expression>),
    default: Option<Expression>,
    is_optional: bool,
    is_option: bool,
}

#[derive(Clone, Debug)]
struct ParsedVariantDecl {
    name: String,
    alias: Expression,
    has_attr_as: bool,
    constr_decl: crate::parser::ast::ConstructorDeclaration,
}

#[derive(Clone, Debug)]
struct ParsedPolyvariantField {
    name: String,
    alias: Expression,
    has_attr_as: bool,
    row_field: crate::parser::ast::RowField,
}

fn loc_none() -> LocIdx {
    LocIdx::none()
}

fn mknoloc<T>(txt: T) -> Located<T> {
    Located::mknoloc(txt)
}

fn intern_str(arena: &mut ParseArena, s: &str) -> StrIdx {
    arena.intern_string(s)
}

fn lident_from_str_idx(arena: &mut ParseArena, idx: StrIdx) -> LidentIdx {
    arena.push_longident(Longident::Lident(idx))
}

fn lident_static(arena: &mut ParseArena, name: &str) -> LidentIdx {
    let idx = intern_str(arena, name);
    arena.push_longident(Longident::Lident(idx))
}

fn lident_path_static(arena: &mut ParseArena, parts: &[&str]) -> LidentIdx {
    if parts.is_empty() {
        return lident_static(arena, "");
    }
    let mut lid = Longident::Lident(intern_str(arena, parts[0]));
    for part in &parts[1..] {
        lid = Longident::Ldot(Box::new(lid), intern_str(arena, part));
    }
    arena.push_longident(lid)
}

fn lident_path_from_parts(arena: &mut ParseArena, parts: &[StrIdx]) -> LidentIdx {
    if parts.is_empty() {
        return lident_static(arena, "");
    }
    let mut lid = Longident::Lident(parts[0]);
    for part in &parts[1..] {
        lid = Longident::Ldot(Box::new(lid), *part);
    }
    arena.push_longident(lid)
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

fn expr_ident_with_loc(lid_idx: LidentIdx, loc: LocIdx) -> Expression {
    Expression {
        pexp_desc: ExpressionDesc::Pexp_ident(Located::new(lid_idx, loc)),
        pexp_loc: loc,
        pexp_attributes: vec![],
    }
}

fn expr_ident_path(arena: &mut ParseArena, parts: &[&str]) -> Expression {
    let lid_idx = lident_path_static(arena, parts);
    expr_ident_with_loc(lid_idx, loc_none())
}

fn expr_ident_dynamic(arena: &mut ParseArena, name: String) -> Expression {
    let idx = intern_str(arena, &name);
    let lid_idx = lident_from_str_idx(arena, idx);
    expr_ident_with_loc(lid_idx, loc_none())
}

fn expr_constant(constant: Constant) -> Expression {
    Expression {
        pexp_desc: ExpressionDesc::Pexp_constant(constant),
        pexp_loc: loc_none(),
        pexp_attributes: vec![],
    }
}

fn expr_apply(funct: Expression, args: Vec<(ArgLabel, Expression)>, partial: bool, loc: LocIdx) -> Expression {
    Expression {
        pexp_desc: ExpressionDesc::Pexp_apply {
            funct: Box::new(funct),
            args,
            partial,
            transformed_jsx: false,
        },
        pexp_loc: loc,
        pexp_attributes: vec![],
    }
}

fn expr_fun(arg_label: ArgLabel, lhs: Pattern, rhs: Expression, arity: Option<i32>, arena: &mut ParseArena) -> Expression {
    let arity_idx = arena.push_arity(arity);
    Expression {
        pexp_desc: ExpressionDesc::Pexp_fun {
            arg_label,
            default: None,
            lhs,
            rhs: Box::new(rhs),
            arity: arity_idx,
            is_async: false,
        },
        pexp_loc: loc_none(),
        pexp_attributes: vec![],
    }
}

fn expr_tuple(items: Vec<Expression>) -> Expression {
    Expression {
        pexp_desc: ExpressionDesc::Pexp_tuple(items),
        pexp_loc: loc_none(),
        pexp_attributes: vec![],
    }
}

fn expr_array(items: Vec<Expression>) -> Expression {
    Expression {
        pexp_desc: ExpressionDesc::Pexp_array(items),
        pexp_loc: loc_none(),
        pexp_attributes: vec![],
    }
}

fn expr_construct(lid_idx: LidentIdx, arg: Option<Expression>) -> Expression {
    Expression {
        pexp_desc: ExpressionDesc::Pexp_construct(Located::new(lid_idx, loc_none()), arg.map(Box::new)),
        pexp_loc: loc_none(),
        pexp_attributes: vec![],
    }
}

fn expr_variant(label: String, arg: Option<Expression>) -> Expression {
    Expression {
        pexp_desc: ExpressionDesc::Pexp_variant(label, arg.map(Box::new)),
        pexp_loc: loc_none(),
        pexp_attributes: vec![],
    }
}

fn expr_match(expr: Expression, cases: Vec<Case>) -> Expression {
    Expression {
        pexp_desc: ExpressionDesc::Pexp_match(Box::new(expr), cases),
        pexp_loc: loc_none(),
        pexp_attributes: vec![],
    }
}

fn expr_ifthenelse(cond: Expression, then_expr: Expression, else_expr: Option<Expression>) -> Expression {
    Expression {
        pexp_desc: ExpressionDesc::Pexp_ifthenelse(Box::new(cond), Box::new(then_expr), else_expr.map(Box::new)),
        pexp_loc: loc_none(),
        pexp_attributes: vec![],
    }
}

fn expr_let(rec_flag: RecFlag, bindings: Vec<ValueBinding>, body: Expression) -> Expression {
    Expression {
        pexp_desc: ExpressionDesc::Pexp_let(rec_flag, bindings, Box::new(body)),
        pexp_loc: loc_none(),
        pexp_attributes: vec![],
    }
}

fn expr_constraint(expr: Expression, typ: CoreType) -> Expression {
    Expression {
        pexp_desc: ExpressionDesc::Pexp_constraint(Box::new(expr), typ),
        pexp_loc: loc_none(),
        pexp_attributes: vec![],
    }
}

fn expr_field(expr: Expression, lid_idx: LidentIdx) -> Expression {
    Expression {
        pexp_desc: ExpressionDesc::Pexp_field(Box::new(expr), Located::new(lid_idx, loc_none())),
        pexp_loc: loc_none(),
        pexp_attributes: vec![],
    }
}

fn expr_record(fields: Vec<ExpressionRecordField>, base: Option<Expression>) -> Expression {
    Expression {
        pexp_desc: ExpressionDesc::Pexp_record(fields, base.map(Box::new)),
        pexp_loc: loc_none(),
        pexp_attributes: vec![],
    }
}

fn pat_any() -> Pattern {
    Pattern {
        ppat_desc: PatternDesc::Ppat_any,
        ppat_loc: loc_none(),
        ppat_attributes: vec![],
    }
}

fn pat_var(arena: &mut ParseArena, name: &str, loc: LocIdx) -> Pattern {
    let idx = intern_str(arena, name);
    Pattern {
        ppat_desc: PatternDesc::Ppat_var(Located::new(idx, loc)),
        ppat_loc: loc,
        ppat_attributes: vec![],
    }
}

fn pat_tuple(items: Vec<Pattern>) -> Pattern {
    Pattern {
        ppat_desc: PatternDesc::Ppat_tuple(items),
        ppat_loc: loc_none(),
        ppat_attributes: vec![],
    }
}

fn pat_array(items: Vec<Pattern>) -> Pattern {
    Pattern {
        ppat_desc: PatternDesc::Ppat_array(items),
        ppat_loc: loc_none(),
        ppat_attributes: vec![],
    }
}

fn pat_construct(lid_idx: LidentIdx, arg: Option<Pattern>) -> Pattern {
    Pattern {
        ppat_desc: PatternDesc::Ppat_construct(Located::new(lid_idx, loc_none()), arg.map(Box::new)),
        ppat_loc: loc_none(),
        ppat_attributes: vec![],
    }
}

fn pat_variant(label: String, arg: Option<Pattern>) -> Pattern {
    Pattern {
        ppat_desc: PatternDesc::Ppat_variant(label, arg.map(Box::new)),
        ppat_loc: loc_none(),
        ppat_attributes: vec![],
    }
}

fn pat_constraint(pat: Pattern, typ: CoreType) -> Pattern {
    Pattern {
        ppat_desc: PatternDesc::Ppat_constraint(Box::new(pat), typ),
        ppat_loc: loc_none(),
        ppat_attributes: vec![],
    }
}

fn case(pat: Pattern, rhs: Expression) -> Case {
    Case {
        pc_bar: None,
        pc_lhs: pat,
        pc_guard: None,
        pc_rhs: rhs,
    }
}

fn tuple_expr_or_singleton(items: Vec<Expression>) -> Expression {
    if items.len() == 1 {
        items.into_iter().next().unwrap()
    } else {
        expr_tuple(items)
    }
}

fn tuple_pat_or_singleton(items: Vec<Pattern>) -> Pattern {
    if items.len() == 1 {
        items.into_iter().next().unwrap()
    } else {
        pat_tuple(items)
    }
}

fn mk_type_constr(lid_idx: LidentIdx, args: Vec<CoreType>) -> CoreType {
    CoreType {
        ptyp_desc: CoreTypeDesc::Ptyp_constr(Located::new(lid_idx, loc_none()), args),
        ptyp_loc: loc_none(),
        ptyp_attributes: vec![],
    }
}

fn mk_type_var(name: &str) -> CoreType {
    CoreType {
        ptyp_desc: CoreTypeDesc::Ptyp_var(name.to_string()),
        ptyp_loc: loc_none(),
        ptyp_attributes: vec![],
    }
}

fn mk_type_arrow(arg_type: CoreType, ret_type: CoreType, arena: &mut ParseArena) -> CoreType {
    let arg = TypeArg {
        attrs: vec![],
        lbl: ArgLabel::Nolabel,
        typ: arg_type,
    };
    CoreType {
        ptyp_desc: CoreTypeDesc::Ptyp_arrow {
            arg: Box::new(arg),
            ret: Box::new(ret_type),
            arity: arena.push_arity(Some(1)),
        },
        ptyp_loc: loc_none(),
        ptyp_attributes: vec![],
    }
}

fn ctyp_json_t(arena: &mut ParseArena) -> CoreType {
    let json_lid = lident_path_static(arena, &["JSON", "t"]);
    mk_type_constr(json_lid, vec![])
}

fn make_ident_expr(arena: &mut ParseArena, name: &str) -> Expression {
    expr_ident_path(arena, &[name])
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
        Some(_) => Ok(Some(GeneratorSettings { do_encode: true, do_decode: true })),
        None => {
            let decode = get_attribute_by_name(attrs, "spice.decode", arena)?;
            let encode = get_attribute_by_name(attrs, "spice.encode", arena)?;
            match (decode, encode) {
                (Some(_), Some(_)) => Ok(Some(GeneratorSettings { do_encode: true, do_decode: true })),
                (Some(_), None) => Ok(Some(GeneratorSettings { do_encode: false, do_decode: true })),
                (None, Some(_)) => Ok(Some(GeneratorSettings { do_encode: true, do_decode: false })),
                (None, None) => Ok(None),
            }
        }
    }
}

fn get_expression_from_payload(attr: &Attribute) -> Result<Expression, String> {
    let payload = &attr.1;
    match payload {
        Payload::PStr(items) => {
            if items.len() != 1 {
                return Err("Expected expression as attribute payload".to_string());
            }
            match &items[0].pstr_desc {
                StructureItemDesc::Pstr_eval(expr, _) => Ok(expr.clone()),
                _ => Err("Expected expression as attribute payload".to_string()),
            }
        }
        _ => Err("Expected expression as attribute payload".to_string()),
    }
}

fn get_param_names(params: &[(CoreType, crate::parser::ast::Variance)]) -> Result<Vec<String>, String> {
    let mut names = Vec::with_capacity(params.len());
    for (typ, _) in params {
        match &typ.ptyp_desc {
            CoreTypeDesc::Ptyp_var(name) => names.push(name.clone()),
            _ => return Err("Unhandled param type".to_string()),
        }
    }
    Ok(names)
}

fn get_string_from_expression(expr: &Expression) -> Result<Option<Constant>, String> {
    match &expr.pexp_desc {
        ExpressionDesc::Pexp_constant(constant) => match constant {
            Constant::String(_, _) => Ok(Some(constant.clone())),
            Constant::Float(_, _) => Ok(None),
            _ => Err("cannot find a name??".to_string()),
        },
        _ => Err("cannot find a name??".to_string()),
    }
}

fn get_float_from_expression(expr: &Expression) -> Result<Option<Constant>, String> {
    match &expr.pexp_desc {
        ExpressionDesc::Pexp_constant(constant) => match constant {
            Constant::String(_, _) => Ok(None),
            Constant::Float(_, _) => Ok(Some(constant.clone())),
            _ => Err("cannot find a name??".to_string()),
        },
        _ => Err("cannot find a name??".to_string()),
    }
}

fn index_const(i: usize) -> Expression {
    let value = format!("[{}]", i);
    expr_constant(Constant::String(value, Some("*j".to_string())))
}

fn check_option_type(typ: &CoreType, arena: &ParseArena) -> bool {
    match &typ.ptyp_desc {
        CoreTypeDesc::Ptyp_constr(lid, args) => longident_matches(arena, lid.txt, &["option"]) && args.len() == 1,
        _ => false,
    }
}

fn expr_spice_error(
    arena: &mut ParseArena,
    message: Expression,
    value: Expression,
    path: Option<Expression>,
) -> Expression {
    let func = expr_ident_path(arena, &["Spice", "error"]);
    let mut args: Vec<(ArgLabel, Expression)> = Vec::new();
    if let Some(path_expr) = path {
        let label_idx = intern_str(arena, "path");
        args.push((ArgLabel::Labelled(Located::mknoloc(label_idx)), path_expr));
    }
    args.push((ArgLabel::Nolabel, message));
    args.push((ArgLabel::Nolabel, value));
    expr_apply(func, args, false, loc_none())
}

fn expr_concat(arena: &mut ParseArena, left: Expression, right: Expression) -> Expression {
    let op = expr_ident_path(arena, &["++"]);
    expr_apply(op, vec![(ArgLabel::Nolabel, left), (ArgLabel::Nolabel, right)], false, loc_none())
}

fn expr_equal(arena: &mut ParseArena, left: Expression, right: Expression) -> Expression {
    let op = expr_ident_path(arena, &["=="]);
    expr_apply(op, vec![(ArgLabel::Nolabel, left), (ArgLabel::Nolabel, right)], false, loc_none())
}

fn build_ifthenelse(arena: &mut ParseArena, cases: Vec<(Expression, Expression)>) -> Expression {
    let mut iter = cases.into_iter().rev();
    let v_expr = expr_ident_path(arena, &["v"]);
    let mut acc = expr_spice_error(
        arena,
        expr_constant(Constant::String("Not matched".to_string(), None)),
        v_expr,
        None,
    );
    while let Some((if_expr, then_expr)) = iter.next() {
        acc = expr_ifthenelse(if_expr, then_expr, Some(acc));
    }
    acc
}

fn tuple_or_singleton_expr(items: Vec<Expression>) -> Expression {
    tuple_expr_or_singleton(items)
}

fn tuple_or_singleton_pat(items: Vec<Pattern>) -> Pattern {
    tuple_pat_or_singleton(items)
}

fn generate_error_case(num_args: usize, index: usize, arena: &mut ParseArena) -> Case {
    let mut pats = Vec::with_capacity(num_args);
    for which in 0..num_args {
        if which == index {
            let e_pat = pat_var(arena, "e", loc_none());
            let decode_error_type = mk_type_constr(lident_path_static(arena, &["Spice", "decodeError"]), vec![]);
            let err_pat = pat_constraint(e_pat, decode_error_type);
            let error_lid = lident_static(arena, "Error");
            pats.push(pat_construct(error_lid, Some(err_pat)));
        } else {
            pats.push(pat_any());
        }
    }
    let lhs = tuple_or_singleton_pat(pats);

    let e_expr = expr_ident_path(arena, &["e"]);
    let path_field = expr_field(e_expr.clone(), lident_static(arena, "path"));
    let new_path = expr_concat(arena, index_const(index), path_field);

    let record_field = ExpressionRecordField {
        lid: Located::new(lident_static(arena, "path"), loc_none()),
        expr: new_path,
        opt: false,
    };
    let record_expr = expr_record(vec![record_field], Some(e_expr));
    let error_expr = expr_construct(lident_static(arena, "Error"), Some(record_expr));

    Case {
        pc_bar: None,
        pc_lhs: lhs,
        pc_guard: None,
        pc_rhs: error_expr,
    }
}

fn tuple_generate_encoder(composite_encoders: Vec<Expression>, arena: &mut ParseArena) -> Expression {
    let mut arr_items = Vec::with_capacity(composite_encoders.len());
    for (i, encoder) in composite_encoders.iter().enumerate() {
        let v_expr = expr_ident_dynamic(arena, format!("v{}", i));
        let applied = expr_apply(encoder.clone(), vec![(ArgLabel::Nolabel, v_expr)], false, loc_none());
        arr_items.push(applied);
    }

    let arr_expr = expr_array(arr_items);
    let json_array = expr_construct(lident_path_static(arena, &["JSON", "Array"]), Some(arr_expr));
    let json_t = ctyp_json_t(arena);
    let constrained = expr_constraint(json_array, json_t);

    let mut pat_vars = Vec::with_capacity(composite_encoders.len());
    for i in 0..composite_encoders.len() {
        pat_vars.push(pat_var(arena, &format!("v{}", i), loc_none()));
    }
    let deconstructor = pat_tuple(pat_vars);

    let fun_expr = expr_fun(ArgLabel::Nolabel, deconstructor, constrained, Some(1), arena);
    fun_expr
}

fn tuple_generate_decode_success_case(num_args: usize, arena: &mut ParseArena) -> Case {
    let mut pats = Vec::with_capacity(num_args);
    for i in 0..num_args {
        let v_pat = pat_var(arena, &format!("v{}", i), loc_none());
        let ok_lid = lident_static(arena, "Ok");
        pats.push(pat_construct(ok_lid, Some(v_pat)));
    }
    let lhs = tuple_or_singleton_pat(pats);

    let mut exprs = Vec::with_capacity(num_args);
    for i in 0..num_args {
        exprs.push(expr_ident_dynamic(arena, format!("v{}", i)));
    }
    let tuple = tuple_or_singleton_expr(exprs);
    let ok_expr = expr_construct(lident_static(arena, "Ok"), Some(tuple));

    case(lhs, ok_expr)
}

fn tuple_generate_decode_switch(composite_decoders: Vec<Expression>, arena: &mut ParseArena) -> Expression {
    let num_args = composite_decoders.len();
    let mut decode_exprs = Vec::with_capacity(num_args);
    for (i, decoder) in composite_decoders.iter().enumerate() {
        let v_expr = expr_ident_dynamic(arena, format!("v{}", i));
        let applied = expr_apply(decoder.clone(), vec![(ArgLabel::Nolabel, v_expr)], false, loc_none());
        decode_exprs.push(applied);
    }
    let tuple_expr = tuple_or_singleton_expr(decode_exprs);

    let mut cases = Vec::new();
    cases.push(tuple_generate_decode_success_case(num_args, arena));
    for i in 0..num_args {
        cases.push(generate_error_case(num_args, i, arena));
    }

    expr_match(tuple_expr, cases)
}

fn tuple_generate_decoder(composite_decoders: Vec<Expression>, arena: &mut ParseArena) -> Expression {
    let mut match_arr_vars = Vec::with_capacity(composite_decoders.len());
    for i in 0..composite_decoders.len() {
        match_arr_vars.push(pat_var(arena, &format!("v{}", i), loc_none()));
    }
    let array_pat = pat_array(match_arr_vars);

    let json_array_pat = pat_construct(lident_path_static(arena, &["JSON", "Array"]), Some(array_pat));
    let json_array_any = pat_construct(lident_path_static(arena, &["JSON", "Array"]), Some(pat_any()));

    let json_expr = expr_ident_path(arena, &["json"]);
    let constrained = expr_constraint(json_expr.clone(), ctyp_json_t(arena));

    let mut cases = Vec::new();
    cases.push(case(json_array_pat, tuple_generate_decode_switch(composite_decoders, arena)));
    cases.push(case(
        json_array_any,
        expr_spice_error(
            arena,
            expr_constant(Constant::String("Incorrect cardinality".to_string(), None)),
            json_expr.clone(),
            None,
        ),
    ));
    cases.push(case(
        pat_any(),
        expr_spice_error(
            arena,
            expr_constant(Constant::String("Not a tuple".to_string(), None)),
            json_expr,
            None,
        ),
    ));

    let match_expr = expr_match(constrained, cases);
    let fun_pat = pat_var(arena, "json", loc_none());
    expr_fun(ArgLabel::Nolabel, fun_pat, match_expr, Some(1), arena)
}

fn codecs_generate_constr_codecs(
    settings: GeneratorSettings,
    lid: &Located<LidentIdx>,
    arena: &mut ParseArena,
) -> (Option<Expression>, Option<Expression>) {
    let do_encode = settings.do_encode;
    let do_decode = settings.do_decode;

    let lid_idx = lid.txt;
    let encode = if do_encode {
        if longident_matches(arena, lid_idx, &["string"]) {
            Some(expr_ident_path(arena, &["Spice", "stringToJson"]))
        } else if longident_matches(arena, lid_idx, &["int"]) {
            Some(expr_ident_path(arena, &["Spice", "intToJson"]))
        } else if longident_matches(arena, lid_idx, &["bigint"]) {
            Some(expr_ident_path(arena, &["Spice", "bigintToJson"]))
        } else if longident_matches(arena, lid_idx, &["float"]) {
            Some(expr_ident_path(arena, &["Spice", "floatToJson"]))
        } else if longident_matches(arena, lid_idx, &["bool"]) {
            Some(expr_ident_path(arena, &["Spice", "boolToJson"]))
        } else if longident_matches(arena, lid_idx, &["unit"]) {
            Some(expr_ident_path(arena, &["Spice", "unitToJson"]))
        } else if longident_matches(arena, lid_idx, &["array"]) {
            Some(expr_ident_path(arena, &["Spice", "arrayToJson"]))
        } else if longident_matches(arena, lid_idx, &["list"]) {
            Some(expr_ident_path(arena, &["Spice", "listToJson"]))
        } else if longident_matches(arena, lid_idx, &["option"]) {
            Some(expr_ident_path(arena, &["Spice", "optionToJson"]))
        } else if longident_matches(arena, lid_idx, &["Js", "null"]) ||
                  longident_matches(arena, lid_idx, &["Js", "Null", "t"]) ||
                  longident_matches(arena, lid_idx, &["Null", "t"]) {
            Some(expr_ident_path(arena, &["Spice", "nullToJson"]))
        } else if longident_matches(arena, lid_idx, &["result"]) ||
                  longident_matches(arena, lid_idx, &["Belt", "Result", "t"]) {
            Some(expr_ident_path(arena, &["Spice", "resultToJson"]))
        } else if longident_matches(arena, lid_idx, &["Js", "Dict", "t"]) ||
                  longident_matches(arena, lid_idx, &["Dict", "t"]) {
            Some(expr_ident_path(arena, &["Spice", "dictToJson"]))
        } else if longident_matches(arena, lid_idx, &["Js", "Json", "t"]) ||
                  longident_matches(arena, lid_idx, &["JSON", "t"]) {
            let v_pat = pat_var(arena, "v", loc_none());
            let v_expr = expr_ident_path(arena, &["v"]);
            Some(expr_fun(ArgLabel::Nolabel, v_pat, v_expr, Some(1), arena))
        } else {
            let lid = arena.get_longident(lid_idx).clone();
            match lid {
                Longident::Lident(s) => {
                    let name = arena.get_string(s);
                    Some(expr_ident_dynamic(arena, format!("{}{}", name, ENCODER_FUNC_SUFFIX)))
                }
                Longident::Ldot(prefix, right) => {
                    let right_name = arena.get_string(right);
                    let new_name = format!("{}{}", right_name, ENCODER_FUNC_SUFFIX);
                    let new_idx = intern_str(arena, &new_name);
                    let new_lid = Longident::Ldot(prefix.clone(), new_idx);
                    let lid_idx = arena.push_longident(new_lid);
                    Some(expr_ident_with_loc(lid_idx, loc_none()))
                }
                Longident::Lapply(_, _) => None,
            }
        }
    } else {
        None
    };

    let decode = if do_decode {
        if longident_matches(arena, lid_idx, &["string"]) {
            Some(expr_ident_path(arena, &["Spice", "stringFromJson"]))
        } else if longident_matches(arena, lid_idx, &["int"]) {
            Some(expr_ident_path(arena, &["Spice", "intFromJson"]))
        } else if longident_matches(arena, lid_idx, &["bigint"]) {
            Some(expr_ident_path(arena, &["Spice", "bigintFromJson"]))
        } else if longident_matches(arena, lid_idx, &["float"]) {
            Some(expr_ident_path(arena, &["Spice", "floatFromJson"]))
        } else if longident_matches(arena, lid_idx, &["bool"]) {
            Some(expr_ident_path(arena, &["Spice", "boolFromJson"]))
        } else if longident_matches(arena, lid_idx, &["unit"]) {
            Some(expr_ident_path(arena, &["Spice", "unitFromJson"]))
        } else if longident_matches(arena, lid_idx, &["array"]) {
            Some(expr_ident_path(arena, &["Spice", "arrayFromJson"]))
        } else if longident_matches(arena, lid_idx, &["list"]) {
            Some(expr_ident_path(arena, &["Spice", "listFromJson"]))
        } else if longident_matches(arena, lid_idx, &["option"]) {
            Some(expr_ident_path(arena, &["Spice", "optionFromJson"]))
        } else if longident_matches(arena, lid_idx, &["Js", "null"]) ||
                  longident_matches(arena, lid_idx, &["Js", "Null", "t"]) ||
                  longident_matches(arena, lid_idx, &["Null", "t"]) {
            Some(expr_ident_path(arena, &["Spice", "nullFromJson"]))
        } else if longident_matches(arena, lid_idx, &["result"]) ||
                  longident_matches(arena, lid_idx, &["Belt", "Result", "t"]) {
            Some(expr_ident_path(arena, &["Spice", "resultFromJson"]))
        } else if longident_matches(arena, lid_idx, &["Js", "Dict", "t"]) ||
                  longident_matches(arena, lid_idx, &["Dict", "t"]) {
            Some(expr_ident_path(arena, &["Spice", "dictFromJson"]))
        } else if longident_matches(arena, lid_idx, &["Js", "Json", "t"]) ||
                  longident_matches(arena, lid_idx, &["JSON", "t"]) {
            let v_pat = pat_var(arena, "v", loc_none());
            let ok_expr = expr_construct(lident_static(arena, "Ok"), Some(expr_ident_path(arena, &["v"])));
            Some(expr_fun(ArgLabel::Nolabel, v_pat, ok_expr, Some(1), arena))
        } else {
            let lid = arena.get_longident(lid_idx).clone();
            match lid {
                Longident::Lident(s) => {
                    let name = arena.get_string(s);
                    Some(expr_ident_dynamic(arena, format!("{}{}", name, DECODER_FUNC_SUFFIX)))
                }
                Longident::Ldot(prefix, right) => {
                    let right_name = arena.get_string(right);
                    let new_name = format!("{}{}", right_name, DECODER_FUNC_SUFFIX);
                    let new_idx = intern_str(arena, &new_name);
                    let new_lid = Longident::Ldot(prefix.clone(), new_idx);
                    let lid_idx = arena.push_longident(new_lid);
                    Some(expr_ident_with_loc(lid_idx, loc_none()))
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
    type_args: &[CoreType],
    encoder_func: Option<Expression>,
    decoder_func: Option<Expression>,
    settings: GeneratorSettings,
    arena: &mut ParseArena,
) -> (Option<Expression>, Option<Expression>) {
    let mut sub_encoders = Vec::new();
    let mut sub_decoders = Vec::new();
    for typ in type_args {
        let (enc, dec) = codecs_generate_codecs(settings, typ, arena);
        sub_encoders.push(enc);
        sub_decoders.push(dec);
    }

    let encoder = match encoder_func {
        None => None,
        Some(func) => {
            let mut args = Vec::new();
            for e in sub_encoders.into_iter() {
                let enc = e.expect("missing encoder");
                args.push((ArgLabel::Nolabel, enc));
            }
            Some(expr_apply(func, args, true, loc_none()))
        }
    };

    let decoder = match decoder_func {
        None => None,
        Some(func) => {
            let mut args = Vec::new();
            for d in sub_decoders.into_iter() {
                let dec = d.expect("missing decoder");
                args.push((ArgLabel::Nolabel, dec));
            }
            Some(expr_apply(func, args, true, loc_none()))
        }
    };

    (encoder, decoder)
}

fn codecs_generate_codecs(
    settings: GeneratorSettings,
    typ: &CoreType,
    arena: &mut ParseArena,
) -> (Option<Expression>, Option<Expression>) {
    match &typ.ptyp_desc {
        CoreTypeDesc::Ptyp_any => panic!("Can't generate codecs for `any` type"),
        CoreTypeDesc::Ptyp_arrow { .. } => panic!("Can't generate codecs for function type"),
        CoreTypeDesc::Ptyp_package(_) => panic!("Can't generate codecs for module type"),
        CoreTypeDesc::Ptyp_tuple(types) => {
            let mut encoders = Vec::new();
            let mut decoders = Vec::new();
            for t in types {
                let (enc, dec) = codecs_generate_codecs(settings, t, arena);
                encoders.push(enc.expect("missing encoder"));
                decoders.push(dec.expect("missing decoder"));
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
            (encoder, decoder)
        }
        CoreTypeDesc::Ptyp_var(name) => (
            if settings.do_encode {
                Some(expr_ident_dynamic(arena, format!("{}{}", ENCODER_VAR_PREFIX, name)))
            } else {
                None
            },
            if settings.do_decode {
                Some(expr_ident_dynamic(arena, format!("{}{}", DECODER_VAR_PREFIX, name)))
            } else {
                None
            },
        ),
        CoreTypeDesc::Ptyp_constr(constr, type_args) => {
            let custom_codec = get_attribute_by_name(&typ.ptyp_attributes, "spice.codec", arena);
            let (encode, decode) = match custom_codec {
                Ok(Some(attr)) => {
                    let expr = get_expression_from_payload(attr).unwrap_or_else(|e| panic!("{}", e));
                    let encode_expr = if settings.do_encode {
                        let pat = pat_tuple(vec![pat_var(arena, "e", loc_none()), pat_any()]);
                        let vb = ValueBinding {
                            pvb_pat: pat,
                            pvb_expr: expr.clone(),
                            pvb_attributes: vec![],
                            pvb_loc: loc_none(),
                        };
                        let body = expr_ident_path(arena, &["e"]);
                        Some(expr_let(RecFlag::Nonrecursive, vec![vb], body))
                    } else {
                        None
                    };
                    let decode_expr = if settings.do_decode {
                        let pat = pat_tuple(vec![pat_any(), pat_var(arena, "d", loc_none())]);
                        let vb = ValueBinding {
                            pvb_pat: pat,
                            pvb_expr: expr,
                            pvb_attributes: vec![],
                            pvb_loc: loc_none(),
                        };
                        let body = expr_ident_path(arena, &["d"]);
                        Some(expr_let(RecFlag::Nonrecursive, vec![vb], body))
                    } else {
                        None
                    };
                    (encode_expr, decode_expr)
                }
                Ok(None) => codecs_generate_constr_codecs(settings, constr, arena),
                Err(e) => panic!("{}", e),
            };

            if type_args.is_empty() {
                (encode, decode)
            } else {
                codecs_parameterize_codecs(type_args, encode, decode, settings, arena)
            }
        }
        _ => panic!("This syntax is not yet handled by spice"),
    }
}

fn records_parse_decl(
    settings: GeneratorSettings,
    decl: &LabelDeclaration,
    arena: &mut ParseArena,
) -> ParsedRecordField {
    let default = match get_attribute_by_name(&decl.pld_attributes, "spice.default", arena) {
        Ok(Some(attr)) => Some(get_expression_from_payload(attr).unwrap_or_else(|e| panic!("{}", e))),
        Ok(None) => None,
        Err(e) => panic!("{}", e),
    };

    let key = match get_attribute_by_name(&decl.pld_attributes, "spice.key", arena) {
        Ok(Some(attr)) => get_expression_from_payload(attr).unwrap_or_else(|e| panic!("{}", e)),
        Ok(None) => {
            let name = arena.get_string(decl.pld_name.txt);
            expr_constant(Constant::String(name.to_string(), Some("*j".to_string())))
        }
        Err(e) => panic!("{}", e),
    };

    let optional_attr_names = ["ns.optional", "res.optional"];
    let mut is_optional = decl.pld_optional;
    if !is_optional {
        for attr_name in &optional_attr_names {
            if let Ok(Some(_)) = get_attribute_by_name(&decl.pld_attributes, attr_name, arena) {
                is_optional = true;
                break;
            }
        }
    }

    let is_option = check_option_type(&decl.pld_type, arena);

    let codecs = codecs_generate_codecs(settings, &decl.pld_type, arena);

    let codecs = if is_optional {
        match codecs {
            (Some(encode), Some(decode)) => {
                let opt_encode = expr_apply(
                    expr_ident_path(arena, &["Spice", "optionToJson"]),
                    vec![(ArgLabel::Nolabel, encode)],
                    true,
                    loc_none(),
                );
                let opt_decode = expr_apply(
                    expr_ident_path(arena, &["Spice", "optionFromJson"]),
                    vec![(ArgLabel::Nolabel, decode)],
                    true,
                    loc_none(),
                );
                (Some(opt_encode), Some(opt_decode))
            }
            (Some(encode), None) => {
                let opt_encode = expr_apply(
                    expr_ident_path(arena, &["Spice", "optionToJson"]),
                    vec![(ArgLabel::Nolabel, encode)],
                    true,
                    loc_none(),
                );
                (Some(opt_encode), None)
            }
            (None, Some(decode)) => {
                let opt_decode = expr_apply(
                    expr_ident_path(arena, &["Spice", "optionFromJson"]),
                    vec![(ArgLabel::Nolabel, decode)],
                    true,
                    loc_none(),
                );
                (None, Some(opt_decode))
            }
            _ => codecs,
        }
    } else {
        codecs
    };

    let field_name = arena.get_string(decl.pld_name.txt).to_string();
    let field_lid = lident_from_str_idx(arena, decl.pld_name.txt);
    let field_expr = expr_field(expr_ident_path(arena, &["v"]), field_lid);

    ParsedRecordField {
        name: field_name,
        key,
        field: field_expr,
        codecs,
        default,
        is_optional,
        is_option,
    }
}

fn records_generate_encoder(fields: &[ParsedRecordField], unboxed: bool, arena: &mut ParseArena) -> Expression {
    if unboxed {
        let field = fields.first().expect("missing field");
        let encoder = field.codecs.0.clone().expect("missing encoder");
        let applied = expr_apply(encoder, vec![(ArgLabel::Nolabel, field.field.clone())], false, loc_none());
        let fun_pat = pat_var(arena, "v", loc_none());
        return expr_fun(ArgLabel::Nolabel, fun_pat, applied, Some(1), arena);
    }

    let mut arr_items = Vec::with_capacity(fields.len());
    for field in fields {
        let encoder = field.codecs.0.clone().expect("missing encoder");
        let encoded = expr_apply(encoder, vec![(ArgLabel::Nolabel, field.field.clone())], false, loc_none());
        let tuple_expr = if field.is_optional || field.is_option {
            expr_tuple(vec![field.key.clone(), encoded])
        } else {
            let some_expr = expr_construct(lident_static(arena, "Some"), Some(encoded));
            expr_tuple(vec![field.key.clone(), some_expr])
        };
        arr_items.push(tuple_expr);
    }

    let arr_expr = expr_array(arr_items);
    let filtered = expr_apply(
        expr_ident_path(arena, &["Spice", "filterOptional"]),
        vec![(ArgLabel::Nolabel, arr_expr)],
        false,
        loc_none(),
    );
    let dict_from_array = expr_apply(
        expr_ident_path(arena, &["Dict", "fromArray"]),
        vec![(ArgLabel::Nolabel, filtered)],
        false,
        loc_none(),
    );
    let json_object = expr_construct(lident_path_static(arena, &["JSON", "Object"]), Some(dict_from_array));
    let constrained = expr_constraint(json_object, ctyp_json_t(arena));

    let fun_pat = pat_var(arena, "v", loc_none());
    expr_fun(ArgLabel::Nolabel, fun_pat, constrained, Some(1), arena)
}

fn records_generate_flat_decoder_expr(fields: &[ParsedRecordField], arena: &mut ParseArena) -> Expression {
    let dict_expr = expr_ident_path(arena, &["dict"]);

    let mut result_names: Vec<(String, Expression)> = Vec::with_capacity(fields.len());

    for field in fields {
        let result_name = format!("{}_result", field.name);
        let decode_expr = match &field.codecs.1 {
            Some(decode) => {
                let get_expr = expr_apply(
                    expr_ident_path(arena, &["Dict", "get"]),
                    vec![(ArgLabel::Nolabel, dict_expr.clone()), (ArgLabel::Nolabel, field.key.clone())],
                    false,
                    loc_none(),
                );
                let decode_applied = decode.clone();
                let opt_map = expr_apply(
                    expr_ident_path(arena, &["Option", "map"]),
                    vec![(ArgLabel::Nolabel, get_expr), (ArgLabel::Nolabel, decode_applied)],
                    false,
                    loc_none(),
                );

                let default_expr = if field.is_optional {
                    match &field.default {
                        Some(d) => {
                            expr_apply(
                                expr_ident_path(arena, &["Option", "getOr"]),
                                vec![(ArgLabel::Nolabel, opt_map.clone()), (ArgLabel::Nolabel, expr_construct(lident_static(arena, "Ok"), Some(d.clone())))],
                                false,
                                loc_none(),
                            )
                        }
                        None => {
                            let ok_none = expr_construct(lident_static(arena, "Ok"), Some(expr_construct(lident_static(arena, "None"), None)));
                            expr_apply(
                                expr_ident_path(arena, &["Option", "getOr"]),
                                vec![(ArgLabel::Nolabel, opt_map.clone()), (ArgLabel::Nolabel, ok_none)],
                                false,
                                loc_none(),
                            )
                        }
                    }
                } else if field.is_option {
                    let ok_none = expr_construct(lident_static(arena, "Ok"), Some(expr_construct(lident_static(arena, "None"), None)));
                    expr_apply(
                        expr_ident_path(arena, &["Option", "getOr"]),
                        vec![(ArgLabel::Nolabel, opt_map.clone()), (ArgLabel::Nolabel, ok_none)],
                        false,
                        loc_none(),
                    )
                } else if let Some(d) = &field.default {
                    let ok_default = expr_construct(lident_static(arena, "Ok"), Some(d.clone()));
                    expr_apply(
                        expr_ident_path(arena, &["Option", "getOr"]),
                        vec![(ArgLabel::Nolabel, opt_map.clone()), (ArgLabel::Nolabel, ok_default)],
                        false,
                        loc_none(),
                    )
                } else {
                    let msg = expr_concat(arena, field.key.clone(), expr_constant(Constant::String(" missing".to_string(), None)));
                    let v_expr = expr_ident_path(arena, &["v"]);
                    let err_expr = expr_spice_error(arena, msg, v_expr, None);
                    expr_apply(
                        expr_ident_path(arena, &["Option", "getOr"]),
                        vec![
                            (ArgLabel::Nolabel, opt_map.clone()),
                            (ArgLabel::Nolabel, err_expr),
                        ],
                        false,
                        loc_none(),
                    )
                };

                default_expr
            }
            None => {
                let msg = expr_concat(arena, field.key.clone(), expr_constant(Constant::String(" missing".to_string(), None)));
                let v_expr = expr_ident_path(arena, &["v"]);
                expr_spice_error(arena, msg, v_expr, None)
            }
        };

        result_names.push((result_name, decode_expr));
    }

    let mut let_bindings = Vec::with_capacity(result_names.len());
    for (name, expr) in &result_names {
        let vb = ValueBinding {
            pvb_pat: pat_var(arena, name, loc_none()),
            pvb_expr: expr.clone(),
            pvb_attributes: vec![],
            pvb_loc: loc_none(),
        };
        let_bindings.push(vb);
    }

    let mut tuple_exprs = Vec::with_capacity(result_names.len());
    for (name, _) in &result_names {
        tuple_exprs.push(expr_ident_dynamic(arena, name.clone()));
    }
    let tuple_expr = tuple_or_singleton_expr(tuple_exprs);

    let mut ok_pats = Vec::with_capacity(fields.len());
    for field in fields {
        let name = field.name.clone();
        let ok_pat = pat_construct(lident_static(arena, "Ok"), Some(pat_var(arena, &name, loc_none())));
        ok_pats.push(ok_pat);
    }
    let ok_pattern = tuple_or_singleton_pat(ok_pats);

    let mut record_fields = Vec::with_capacity(fields.len());
    for field in fields {
        let name_idx = intern_str(arena, &field.name);
        let lid = lident_from_str_idx(arena, name_idx);
        let expr = expr_ident_dynamic(arena, field.name.clone());
        record_fields.push(ExpressionRecordField {
            lid: Located::new(lid, loc_none()),
            expr,
            opt: field.is_optional,
        });
    }
    let ok_expr = expr_construct(lident_static(arena, "Ok"), Some(expr_record(record_fields, None)));

    let mut error_cases = Vec::new();
    for (i, field) in fields.iter().enumerate() {
        let mut pats = Vec::with_capacity(fields.len());
        for j in 0..fields.len() {
            if i == j {
                let e_pat = pat_var(arena, "e", loc_none());
                let decode_error_type = mk_type_constr(lident_path_static(arena, &["Spice", "decodeError"]), vec![]);
                let err_pat = pat_constraint(e_pat, decode_error_type);
                pats.push(pat_construct(lident_static(arena, "Error"), Some(err_pat)));
            } else {
                pats.push(pat_any());
            }
        }
        let pat = tuple_or_singleton_pat(pats);
        let e_expr = expr_ident_path(arena, &["e"]);
        let msg_expr = expr_field(e_expr.clone(), lident_static(arena, "message"));
        let val_expr = expr_field(e_expr.clone(), lident_static(arena, "value"));
        let rhs = expr_spice_error(arena, msg_expr, val_expr, Some(field.key.clone()));
        error_cases.push(case(pat, rhs));
    }

    let mut cases = Vec::new();
    cases.push(case(ok_pattern, ok_expr));
    cases.extend(error_cases);

    let match_expr = expr_match(tuple_expr, cases);

    let mut acc = match_expr;
    for vb in let_bindings.into_iter().rev() {
        acc = expr_let(RecFlag::Nonrecursive, vec![vb], acc);
    }

    acc
}

fn records_generate_decoder(fields: &[ParsedRecordField], unboxed: bool, arena: &mut ParseArena) -> Expression {
    if unboxed {
        let field = fields.first().expect("missing field");
        let decoder = field.codecs.1.clone().expect("missing decoder");

        let name_idx = intern_str(arena, &field.name);
        let field_lid = lident_from_str_idx(arena, name_idx);
        let record_fields = vec![ExpressionRecordField {
            lid: Located::new(field_lid, loc_none()),
            expr: expr_ident_path(arena, &["v"]),
            opt: field.is_optional,
        }];
        let record_expr = expr_record(record_fields, None);

        let inner_fun = expr_fun(ArgLabel::Nolabel, pat_var(arena, "v", loc_none()), record_expr, Some(1), arena);
        let map_expr = expr_apply(
            expr_ident_path(arena, &["Result", "map"]),
            vec![(ArgLabel::Nolabel, expr_apply(decoder, vec![(ArgLabel::Nolabel, expr_ident_path(arena, &["v"]))], false, loc_none())),
                 (ArgLabel::Nolabel, inner_fun)],
            false,
            loc_none(),
        );
        return expr_fun(ArgLabel::Nolabel, pat_var(arena, "v", loc_none()), map_expr, Some(1), arena);
    }

    let json_expr = expr_ident_path(arena, &["v"]);
    let json_obj_pat = pat_construct(lident_path_static(arena, &["JSON", "Object"]), Some(pat_var(arena, "dict", loc_none())));
    let error_expr = expr_spice_error(
        arena,
        expr_constant(Constant::String("Not an object".to_string(), None)),
        json_expr.clone(),
        None,
    );

    let match_expr = expr_match(
        expr_constraint(json_expr.clone(), ctyp_json_t(arena)),
        vec![
            case(json_obj_pat, records_generate_flat_decoder_expr(fields, arena)),
            case(pat_any(), error_expr),
        ],
    );

    expr_fun(ArgLabel::Nolabel, pat_var(arena, "v", loc_none()), match_expr, Some(1), arena)
}

fn records_generate_codecs(
    settings: GeneratorSettings,
    decls: &[LabelDeclaration],
    unboxed: bool,
    arena: &mut ParseArena,
) -> (Option<Expression>, Option<Expression>) {
    let parsed: Vec<ParsedRecordField> = decls.iter().map(|d| records_parse_decl(settings, d, arena)).collect();

    let encoder = if settings.do_encode {
        Some(records_generate_encoder(&parsed, unboxed, arena))
    } else {
        None
    };
    let decoder = if settings.do_decode {
        Some(records_generate_decoder(&parsed, unboxed, arena))
    } else {
        None
    };
    (encoder, decoder)
}

fn variants_parse_decl(
    decl: &crate::parser::ast::ConstructorDeclaration,
    arena: &mut ParseArena,
) -> ParsedVariantDecl {
    let name = arena.get_string(decl.pcd_name.txt).to_string();
    let (alias, has_attr_as) = match get_attribute_by_name(&decl.pcd_attributes, "spice.as", arena) {
        Ok(Some(attr)) => (get_expression_from_payload(attr).unwrap_or_else(|e| panic!("{}", e)), true),
        Ok(None) => (
            expr_constant(Constant::String(name.clone(), Some("*j".to_string()))),
            false,
        ),
        Err(e) => panic!("{}", e),
    };

    ParsedVariantDecl {
        name,
        alias,
        has_attr_as,
        constr_decl: decl.clone(),
    }
}

fn variants_generate_encoder_case(
    settings: GeneratorSettings,
    unboxed: bool,
    has_attr_as: bool,
    decl: &ParsedVariantDecl,
    arena: &mut ParseArena,
) -> Case {
    let pcd_loc = decl.constr_decl.pcd_loc;

    let json_expr = match &decl.alias.pexp_desc {
        ExpressionDesc::Pexp_constant(constant) => match constant {
            Constant::String(_, _) => expr_construct(lident_path_static(arena, &["JSON", "String"]), Some(decl.alias.clone())),
            Constant::Float(_, _) | Constant::Integer(_, _) => expr_construct(lident_path_static(arena, &["JSON", "Number"]), Some(decl.alias.clone())),
            _ => panic!("cannot find a name??!"),
        },
        _ => panic!("cannot find a name???"),
    };

    let (lhs_vars, rhs_list) = match &decl.constr_decl.pcd_args {
        crate::parser::ast::ConstructorArguments::Pcstr_tuple(args) => {
            let lhs_vars = match args.len() {
                0 => None,
                1 => Some(pat_var(arena, "v0", loc_none())),
                _ => {
                    let mut vars = Vec::with_capacity(args.len());
                    for i in 0..args.len() {
                        vars.push(pat_var(arena, &format!("v{}", i), pcd_loc));
                    }
                    Some(pat_tuple(vars))
                }
            };

            let mut rhs_list = Vec::new();
            rhs_list.push(json_expr.clone());
            for (i, arg) in args.iter().enumerate() {
                let (enc, _) = codecs_generate_codecs(settings, arg, arena);
                let encoder = enc.expect("missing encoder");
                let v_expr = expr_ident_dynamic(arena, format!("v{}", i));
                let applied = expr_apply(encoder, vec![(ArgLabel::Nolabel, v_expr)], false, pcd_loc);
                rhs_list.push(applied);
            }

            (lhs_vars, rhs_list)
        }
        crate::parser::ast::ConstructorArguments::Pcstr_record(_) => panic!("This syntax is not yet implemented by spice"),
    };

    let rhs = if unboxed {
        rhs_list.get(1).cloned().unwrap_or_else(|| json_expr.clone())
    } else if has_attr_as {
        json_expr
    } else {
        let arr = expr_array(rhs_list);
        expr_construct(lident_path_static(arena, &["JSON", "Array"]), Some(arr))
    };

    let pat = pat_construct(lident_from_str_idx(arena, decl.constr_decl.pcd_name.txt), lhs_vars);

    Case {
        pc_bar: None,
        pc_lhs: pat,
        pc_guard: None,
        pc_rhs: rhs,
    }
}

fn variants_generate_decode_success_case(num_args: usize, constructor_name: &str, arena: &mut ParseArena) -> Case {
    let mut pats = Vec::with_capacity(num_args);
    for i in 0..num_args {
        let v_pat = pat_var(arena, &format!("v{}", i), loc_none());
        pats.push(pat_construct(lident_static(arena, "Ok"), Some(v_pat)));
    }
    let lhs = tuple_or_singleton_pat(pats);

    let mut exprs = Vec::with_capacity(num_args);
    for i in 0..num_args {
        exprs.push(expr_ident_dynamic(arena, format!("v{}", i)));
    }
    let payload = tuple_or_singleton_expr(exprs);
    let ctor = expr_construct(lident_static(arena, constructor_name), Some(payload));
    let ok_expr = expr_construct(lident_static(arena, "Ok"), Some(ctor));

    case(lhs, ok_expr)
}

fn variants_generate_arg_decoder(
    settings: GeneratorSettings,
    args: &[CoreType],
    constructor_name: &str,
    arena: &mut ParseArena,
) -> Expression {
    let num_args = args.len();

    let mut decode_exprs = Vec::with_capacity(num_args);
    for (i, arg) in args.iter().enumerate() {
        let (_, dec) = codecs_generate_codecs(settings, arg, arena);
        let decoder = dec.expect("missing decoder");
        let idx_expr = expr_constant(Constant::Integer((i + 1).to_string(), None));
        let arg_expr = expr_apply(
            expr_ident_path(arena, &["Array", "getUnsafe"]),
            vec![(ArgLabel::Nolabel, expr_ident_path(arena, &["json_arr"])), (ArgLabel::Nolabel, idx_expr)],
            false,
            loc_none(),
        );
        let applied = expr_apply(decoder, vec![(ArgLabel::Nolabel, arg_expr)], false, loc_none());
        decode_exprs.push(applied);
    }

    let tuple_expr = tuple_or_singleton_expr(decode_exprs);

    let mut cases = Vec::new();
    cases.push(variants_generate_decode_success_case(num_args, constructor_name, arena));
    for i in 0..num_args {
        cases.push(generate_error_case(num_args, i, arena));
    }

    expr_match(tuple_expr, cases)
}

fn variants_generate_decoder_case(
    settings: GeneratorSettings,
    decl: &crate::parser::ast::ConstructorDeclaration,
    arena: &mut ParseArena,
) -> Case {
    let name = arena.get_string(decl.pcd_name.txt).to_string();
    match &decl.pcd_args {
        crate::parser::ast::ConstructorArguments::Pcstr_tuple(args) => {
            let arg_len = expr_constant(Constant::Integer((args.len() + 1).to_string(), None));
            let decoded = if args.is_empty() {
                let ctor = expr_construct(lident_static(arena, &name), None);
                expr_construct(lident_static(arena, "Ok"), Some(ctor))
            } else {
                variants_generate_arg_decoder(settings, args, &name, arena)
            };

            let json_str_pat = pat_construct(
                lident_path_static(arena, &["JSON", "String"]),
                Some(Pattern {
                    ppat_desc: PatternDesc::Ppat_constant(Constant::String(name.clone(), None)),
                    ppat_loc: loc_none(),
                    ppat_attributes: vec![],
                }),
            );

            let json_arr_expr = expr_ident_path(arena, &["json_arr"]);
            let len_expr = expr_apply(
                expr_ident_path(arena, &["Array", "length"]),
                vec![(ArgLabel::Nolabel, json_arr_expr)],
                false,
                loc_none(),
            );
            let cond = expr_equal(arena, len_expr, arg_len);

            let v_expr = expr_ident_path(arena, &["v"]);
            let err_expr = expr_spice_error(
                arena,
                expr_constant(Constant::String("Invalid number of arguments to variant constructor".to_string(), None)),
                v_expr,
                None,
            );
            let rhs = expr_ifthenelse(cond, decoded, Some(err_expr));

            case(json_str_pat, rhs)
        }
        crate::parser::ast::ConstructorArguments::Pcstr_record(_) => panic!("This syntax is not yet implemented by spice"),
    }
}

fn variants_generate_decoder_case_attr(
    is_string: bool,
    settings: GeneratorSettings,
    decl: &ParsedVariantDecl,
    arena: &mut ParseArena,
) -> Option<(Expression, Expression)> {
    match &decl.constr_decl.pcd_args {
        crate::parser::ast::ConstructorArguments::Pcstr_tuple(args) => {
            let const_opt = if is_string {
                get_string_from_expression(&decl.alias).ok().flatten()
            } else {
                get_float_from_expression(&decl.alias).ok().flatten()
            };
            let const_value = match const_opt {
                Some(c) => c,
                None => return None,
            };

            let decoded = if args.is_empty() {
                let ctor = expr_construct(lident_static(arena, &decl.name), None);
                expr_construct(lident_static(arena, "Ok"), Some(ctor))
            } else {
                variants_generate_arg_decoder(settings, args, &decl.name, arena)
            };

            let const_expr = expr_constant(const_value);
            let str_expr = expr_ident_path(arena, &["str_or_num"]);
            let if_expr = expr_equal(arena, const_expr, str_expr);
            Some((if_expr, decoded))
        }
        crate::parser::ast::ConstructorArguments::Pcstr_record(_) => panic!("This syntax is not yet implemented by spice"),
    }
}

fn variants_generate_unboxed_decode(
    settings: GeneratorSettings,
    decl: &crate::parser::ast::ConstructorDeclaration,
    arena: &mut ParseArena,
) -> Option<Expression> {
    match &decl.pcd_args {
        crate::parser::ast::ConstructorArguments::Pcstr_tuple(args) => {
            if args.len() != 1 {
                panic!("Expected exactly one type argument");
            }
            let (_, dec) = codecs_generate_codecs(settings, &args[0], arena);
            let decoder = dec?;
            let ctor_name = arena.get_string(decl.pcd_name.txt).to_string();
            let ctor_expr = expr_construct(lident_static(arena, &ctor_name), Some(expr_ident_path(arena, &["v"])));
            let inner_fun = expr_fun(ArgLabel::Nolabel, pat_var(arena, "v", loc_none()), ctor_expr, Some(1), arena);
            let map_expr = expr_apply(
                expr_ident_path(arena, &["Result", "map"]),
                vec![
                    (ArgLabel::Nolabel, expr_apply(decoder, vec![(ArgLabel::Nolabel, expr_ident_path(arena, &["v"]))], false, loc_none())),
                    (ArgLabel::Nolabel, inner_fun),
                ],
                false,
                loc_none(),
            );
            Some(expr_fun(ArgLabel::Nolabel, pat_var(arena, "v", loc_none()), map_expr, Some(1), arena))
        }
        crate::parser::ast::ConstructorArguments::Pcstr_record(_) => panic!("This syntax is not yet implemented by spice"),
    }
}

fn variants_generate_codecs(
    settings: GeneratorSettings,
    constr_decls: &[crate::parser::ast::ConstructorDeclaration],
    unboxed: bool,
    arena: &mut ParseArena,
) -> (Option<Expression>, Option<Expression>) {
    let parsed: Vec<ParsedVariantDecl> = constr_decls.iter().map(|d| variants_parse_decl(d, arena)).collect();
    let count_has_attr = parsed.iter().filter(|v| v.has_attr_as).count();
    let has_attr_as = if count_has_attr > 0 {
        if count_has_attr == parsed.len() {
            true
        } else {
            panic!("Partial @spice.as usage is not allowed");
        }
    } else {
        false
    };

    let encoder = if settings.do_encode {
        let mut cases = Vec::new();
        for decl in &parsed {
            cases.push(variants_generate_encoder_case(settings, unboxed, has_attr_as, decl, arena));
        }
        let match_expr = expr_match(expr_ident_path(arena, &["v"]), cases);
        let constrained = expr_constraint(match_expr, ctyp_json_t(arena));
        Some(expr_fun(ArgLabel::Nolabel, pat_var(arena, "v", loc_none()), constrained, Some(1), arena))
    } else {
        None
    };

    let decoder = if settings.do_decode {
        if unboxed {
            variants_generate_unboxed_decode(settings, &constr_decls[0], arena)
        } else if has_attr_as {
            let mut string_cases = Vec::new();
            let mut number_cases = Vec::new();
            for decl in &parsed {
                if let Some(pair) = variants_generate_decoder_case_attr(true, settings, decl, arena) {
                    string_cases.push(pair);
                }
                if let Some(pair) = variants_generate_decoder_case_attr(false, settings, decl, arena) {
                    number_cases.push(pair);
                }
            }

            let decoder_switch = build_ifthenelse(arena, string_cases);
            let decoder_switch_num = build_ifthenelse(arena, number_cases);

            let json_expr = expr_ident_path(arena, &["v"]);
            let match_expr = expr_match(
                expr_constraint(json_expr.clone(), ctyp_json_t(arena)),
                vec![
                    case(
                        pat_construct(lident_path_static(arena, &["JSON", "String"]), Some(pat_var(arena, "str_or_num", loc_none()))),
                        decoder_switch,
                    ),
                    case(
                        pat_construct(lident_path_static(arena, &["JSON", "Number"]), Some(pat_var(arena, "str_or_num", loc_none()))),
                        decoder_switch_num,
                    ),
                    case(
                        pat_any(),
                        expr_spice_error(
                            arena,
                            expr_constant(Constant::String("Not a JSONString".to_string(), None)),
                            json_expr,
                            None,
                        ),
                    ),
                ],
            );
            Some(expr_fun(ArgLabel::Nolabel, pat_var(arena, "v", loc_none()), match_expr, Some(1), arena))
        } else {
            let mut cases = Vec::new();
            for decl in constr_decls {
                cases.push(variants_generate_decoder_case(settings, decl, arena));
            }
            let json_arr_expr = expr_ident_path(arena, &["json_arr"]);
            let head_expr = expr_apply(
                expr_ident_path(arena, &["Array", "getUnsafe"]),
                vec![
                    (ArgLabel::Nolabel, json_arr_expr.clone()),
                    (ArgLabel::Nolabel, expr_constant(Constant::Integer("0".to_string(), None))),
                ],
                false,
                loc_none(),
            );
            let default_case = case(
                pat_any(),
                expr_spice_error(
                    arena,
                    expr_constant(Constant::String("Invalid variant constructor".to_string(), None)),
                    head_expr.clone(),
                    None,
                ),
            );
            cases.push(default_case);

            let decoder_switch = expr_match(
                head_expr,
                cases,
            );

            let json_expr = expr_ident_path(arena, &["v"]);
            let match_expr = expr_match(
                expr_constraint(json_expr.clone(), ctyp_json_t(arena)),
                vec![
                    case(
                        pat_construct(lident_path_static(arena, &["JSON", "Array"]), Some(pat_array(vec![]))),
                        expr_spice_error(
                            arena,
                            expr_constant(Constant::String("Expected variant, found empty array".to_string(), None)),
                            json_expr.clone(),
                            None,
                        ),
                    ),
                    case(
                        pat_construct(lident_path_static(arena, &["JSON", "Array"]), Some(pat_var(arena, "json_arr", loc_none()))),
                        decoder_switch,
                    ),
                    case(
                        pat_any(),
                        expr_spice_error(
                            arena,
                            expr_constant(Constant::String("Not a variant".to_string(), None)),
                            json_expr,
                            None,
                        ),
                    ),
                ],
            );
            Some(expr_fun(ArgLabel::Nolabel, pat_var(arena, "v", loc_none()), match_expr, Some(1), arena))
        }
    } else {
        None
    };

    (encoder, decoder)
}

fn polyvars_get_args(_loc: LocIdx, core_types: &[CoreType]) -> Vec<CoreType> {
    match core_types.len() {
        0 => vec![],
        1 => {
            match &core_types[0].ptyp_desc {
                CoreTypeDesc::Ptyp_tuple(types) => types.clone(),
                _ => vec![core_types[0].clone()],
            }
        }
        _ => panic!("This error shoudn't happen, means that the AST of your polyvariant is wrong"),
    }
}

fn polyvars_parse_decl(row_field: &RowField, arena: &mut ParseArena) -> ParsedPolyvariantField {
    let name = match row_field {
        RowField::Rtag(tag, _, _, _) => tag.txt.clone(),
        _ => panic!("cannot get polymorphic variant constructor"),
    };

    let (alias, has_attr_as) = match row_field {
        RowField::Rtag(_, attrs, _, _) => match get_attribute_by_name(attrs, "spice.as", arena) {
            Ok(Some(attr)) => (get_expression_from_payload(attr).unwrap_or_else(|e| panic!("{}", e)), true),
            Ok(None) => (
                expr_constant(Constant::String(name.clone(), Some("*j".to_string()))),
                false,
            ),
            Err(e) => panic!("{}", e),
        },
        RowField::Rinherit(_) => panic!("This syntax is not yet implemented by spice"),
    };

    ParsedPolyvariantField {
        name,
        alias,
        has_attr_as,
        row_field: row_field.clone(),
    }
}

fn polyvars_generate_encoder_case(
    settings: GeneratorSettings,
    unboxed: bool,
    has_attr_as: bool,
    row: &ParsedPolyvariantField,
    arena: &mut ParseArena,
) -> Case {
    let (json_expr, args) = match &row.row_field {
        RowField::Rtag(_, _, _, core_types) => {
            let json_expr = match &row.alias.pexp_desc {
                ExpressionDesc::Pexp_constant(constant) => match constant {
                    Constant::String(_, _) => expr_construct(lident_path_static(arena, &["JSON", "String"]), Some(row.alias.clone())),
                    Constant::Float(_, _) => expr_construct(lident_path_static(arena, &["JSON", "Number"]), Some(row.alias.clone())),
                    _ => panic!("cannot find a name??"),
                },
                _ => panic!("cannot find a name??"),
            };
            let args = polyvars_get_args(loc_none(), core_types);
            (json_expr, args)
        }
        RowField::Rinherit(_arg) => panic!("This syntax is not yet implemented by spice"),
    };

    let lhs_vars = match args.len() {
        0 => None,
        1 => Some(pat_var(arena, "v0", loc_none())),
        _ => {
            let mut vars = Vec::with_capacity(args.len());
            for i in 0..args.len() {
                vars.push(pat_var(arena, &format!("v{}", i), loc_none()));
            }
            Some(pat_tuple(vars))
        }
    };

    let mut rhs_list = Vec::new();
    rhs_list.push(json_expr.clone());
    for (i, arg) in args.iter().enumerate() {
        let (enc, _) = codecs_generate_codecs(settings, arg, arena);
        let encoder = enc.expect("missing encoder");
        let v_expr = expr_ident_dynamic(arena, format!("v{}", i));
        let applied = expr_apply(encoder, vec![(ArgLabel::Nolabel, v_expr)], false, loc_none());
        rhs_list.push(applied);
    }

    let rhs = if unboxed {
        rhs_list.get(1).cloned().unwrap_or_else(|| json_expr.clone())
    } else if has_attr_as {
        json_expr
    } else {
        let arr = expr_array(rhs_list);
        expr_construct(lident_path_static(arena, &["JSON", "Array"]), Some(arr))
    };

    let pat = pat_variant(row.name.clone(), lhs_vars);

    Case {
        pc_bar: None,
        pc_lhs: pat,
        pc_guard: None,
        pc_rhs: rhs,
    }
}

fn polyvars_generate_decode_success_case(num_args: usize, constructor_name: &str, arena: &mut ParseArena) -> Case {
    let mut pats = Vec::with_capacity(num_args);
    for i in 0..num_args {
        let v_pat = pat_var(arena, &format!("v{}", i), loc_none());
        pats.push(pat_construct(lident_static(arena, "Ok"), Some(v_pat)));
    }
    let lhs = tuple_or_singleton_pat(pats);

    let mut exprs = Vec::with_capacity(num_args);
    for i in 0..num_args {
        exprs.push(expr_ident_dynamic(arena, format!("v{}", i)));
    }
    let payload = tuple_or_singleton_expr(exprs);
    let ctor = expr_variant(constructor_name.to_string(), Some(payload));
    let ok_expr = expr_construct(lident_static(arena, "Ok"), Some(ctor));

    case(lhs, ok_expr)
}

fn polyvars_generate_arg_decoder(
    settings: GeneratorSettings,
    args: &[CoreType],
    constructor_name: &str,
    arena: &mut ParseArena,
) -> Expression {
    let num_args = args.len();

    let mut decode_exprs = Vec::with_capacity(num_args);
    for (i, arg) in args.iter().enumerate() {
        let (_, dec) = codecs_generate_codecs(settings, arg, arena);
        let decoder = dec.expect("missing decoder");
        let idx_expr = expr_constant(Constant::Integer((i + 1).to_string(), None));
        let arg_expr = expr_apply(
            expr_ident_path(arena, &["Array", "getUnsafe"]),
            vec![(ArgLabel::Nolabel, expr_ident_path(arena, &["json_arr"])), (ArgLabel::Nolabel, idx_expr)],
            false,
            loc_none(),
        );
        let applied = expr_apply(decoder, vec![(ArgLabel::Nolabel, arg_expr)], false, loc_none());
        decode_exprs.push(applied);
    }

    let tuple_expr = tuple_or_singleton_expr(decode_exprs);

    let mut cases = Vec::new();
    cases.push(polyvars_generate_decode_success_case(num_args, constructor_name, arena));
    for i in 0..num_args {
        cases.push(generate_error_case(num_args, i, arena));
    }

    expr_match(tuple_expr, cases)
}

fn polyvars_generate_decoder_case(
    settings: GeneratorSettings,
    row_field: &RowField,
    arena: &mut ParseArena,
) -> Case {
    match row_field {
        RowField::Rtag(tag, _, _, core_types) => {
            let args = polyvars_get_args(loc_none(), core_types);
            let arg_len = expr_constant(Constant::Integer((args.len() + 1).to_string(), None));
            let decoded = if args.is_empty() {
                let ctor = expr_variant(tag.txt.clone(), None);
                expr_construct(lident_static(arena, "Ok"), Some(ctor))
            } else {
                polyvars_generate_arg_decoder(settings, &args, &tag.txt, arena)
            };

            let json_str_pat = pat_construct(
                lident_path_static(arena, &["JSON", "String"]),
                Some(Pattern {
                    ppat_desc: PatternDesc::Ppat_constant(Constant::String(tag.txt.clone(), None)),
                    ppat_loc: loc_none(),
                    ppat_attributes: vec![],
                }),
            );

            let json_arr_expr = expr_ident_path(arena, &["json_arr"]);
            let len_expr = expr_apply(
                expr_ident_path(arena, &["Array", "length"]),
                vec![(ArgLabel::Nolabel, json_arr_expr)],
                false,
                loc_none(),
            );
            let cond = expr_equal(arena, len_expr, arg_len);

            let v_expr = expr_ident_path(arena, &["v"]);
            let err_expr = expr_spice_error(
                arena,
                expr_constant(Constant::String("Invalid number of arguments to polyvariant constructor".to_string(), None)),
                v_expr,
                None,
            );
            let rhs = expr_ifthenelse(cond, decoded, Some(err_expr));
            case(json_str_pat, rhs)
        }
        RowField::Rinherit(_core_type) => panic!("This syntax is not yet implemented by spice"),
    }
}

fn polyvars_generate_decoder_case_attr(
    is_string: bool,
    settings: GeneratorSettings,
    row: &ParsedPolyvariantField,
    arena: &mut ParseArena,
) -> Option<(Expression, Expression)> {
    match &row.row_field {
        RowField::Rtag(tag, _, _, core_types) => {
            let args = polyvars_get_args(loc_none(), core_types);
            let const_opt = if is_string {
                get_string_from_expression(&row.alias).ok().flatten()
            } else {
                get_float_from_expression(&row.alias).ok().flatten()
            };
            let const_value = match const_opt {
                Some(c) => c,
                None => return None,
            };

            let decoded = if args.is_empty() {
                let ctor = expr_variant(tag.txt.clone(), None);
                expr_construct(lident_static(arena, "Ok"), Some(ctor))
            } else {
                polyvars_generate_arg_decoder(settings, &args, &tag.txt, arena)
            };

            let const_expr = expr_constant(const_value);
            let str_expr = expr_ident_path(arena, &["str_or_num"]);
            let if_expr = expr_equal(arena, const_expr, str_expr);
            Some((if_expr, decoded))
        }
        RowField::Rinherit(_) => panic!("This syntax is not yet implemented by spice"),
    }
}

fn polyvars_generate_unboxed_decode(
    settings: GeneratorSettings,
    row_field: &RowField,
    arena: &mut ParseArena,
) -> Option<Expression> {
    match row_field {
        RowField::Rtag(tag, _, _, args) => {
            if args.len() != 1 {
                panic!("Expected exactly one type argument");
            }
            let (_, dec) = codecs_generate_codecs(settings, &args[0], arena);
            let decoder = dec?;
            let ctor_expr = expr_construct(lident_static(arena, &tag.txt), Some(expr_ident_path(arena, &["v"])));
            let inner_fun = expr_fun(ArgLabel::Nolabel, pat_var(arena, "v", loc_none()), ctor_expr, Some(1), arena);
            let map_expr = expr_apply(
                expr_ident_path(arena, &["Result", "map"]),
                vec![
                    (ArgLabel::Nolabel, expr_apply(decoder, vec![(ArgLabel::Nolabel, expr_ident_path(arena, &["v"]))], false, loc_none())),
                    (ArgLabel::Nolabel, inner_fun),
                ],
                false,
                loc_none(),
            );
            Some(expr_fun(ArgLabel::Nolabel, pat_var(arena, "v", loc_none()), map_expr, Some(1), arena))
        }
        RowField::Rinherit(_core_type) => panic!("This syntax is not yet implemented by spice"),
    }
}

fn polyvars_generate_codecs(
    settings: GeneratorSettings,
    row_fields: &[RowField],
    unboxed: bool,
    arena: &mut ParseArena,
) -> (Option<Expression>, Option<Expression>) {
    let parsed: Vec<ParsedPolyvariantField> = row_fields.iter().map(|r| polyvars_parse_decl(r, arena)).collect();
    let count_has_attr = parsed.iter().filter(|v| v.has_attr_as).count();
    let has_attr_as = if count_has_attr > 0 {
        if count_has_attr == parsed.len() {
            true
        } else {
            panic!("Partial @spice.as usage is not allowed");
        }
    } else {
        false
    };

    let encoder = if settings.do_encode {
        let mut cases = Vec::new();
        for row in &parsed {
            cases.push(polyvars_generate_encoder_case(settings, unboxed, has_attr_as, row, arena));
        }
        let match_expr = expr_match(expr_ident_path(arena, &["v"]), cases);
        Some(expr_fun(ArgLabel::Nolabel, pat_var(arena, "v", loc_none()), match_expr, Some(1), arena))
    } else {
        None
    };

    let decoder = if settings.do_decode {
        if unboxed {
            polyvars_generate_unboxed_decode(settings, &row_fields[0], arena)
        } else if has_attr_as {
            let mut string_cases = Vec::new();
            let mut number_cases = Vec::new();
            for row in &parsed {
                if let Some(pair) = polyvars_generate_decoder_case_attr(true, settings, row, arena) {
                    string_cases.push(pair);
                }
                if let Some(pair) = polyvars_generate_decoder_case_attr(false, settings, row, arena) {
                    number_cases.push(pair);
                }
            }

            let decoder_switch = build_ifthenelse(arena, string_cases);
            let decoder_switch_num = build_ifthenelse(arena, number_cases);

            let json_expr = expr_ident_path(arena, &["v"]);
            let match_expr = expr_match(
                expr_constraint(json_expr.clone(), ctyp_json_t(arena)),
                vec![
                    case(
                        pat_construct(lident_path_static(arena, &["JSON", "String"]), Some(pat_var(arena, "str_or_num", loc_none()))),
                        decoder_switch,
                    ),
                    case(
                        pat_construct(lident_path_static(arena, &["JSON", "Number"]), Some(pat_var(arena, "str_or_num", loc_none()))),
                        decoder_switch_num,
                    ),
                    case(
                        pat_any(),
                        expr_spice_error(
                            arena,
                            expr_constant(Constant::String("Not a JSONString".to_string(), None)),
                            json_expr,
                            None,
                        ),
                    ),
                ],
            );
            Some(expr_fun(ArgLabel::Nolabel, pat_var(arena, "v", loc_none()), match_expr, Some(1), arena))
        } else {
            let mut cases = Vec::new();
            for row in row_fields {
                cases.push(polyvars_generate_decoder_case(settings, row, arena));
            }
            let json_arr_expr = expr_ident_path(arena, &["json_arr"]);
            let head_expr = expr_apply(
                expr_ident_path(arena, &["Array", "getUnsafe"]),
                vec![
                    (ArgLabel::Nolabel, json_arr_expr.clone()),
                    (ArgLabel::Nolabel, expr_constant(Constant::Integer("0".to_string(), None))),
                ],
                false,
                loc_none(),
            );
            let default_case = case(
                pat_any(),
                expr_spice_error(
                    arena,
                    expr_constant(Constant::String("Invalid polymorphic variant constructor".to_string(), None)),
                    head_expr.clone(),
                    None,
                ),
            );
            cases.push(default_case);

            let decoder_switch = expr_match(
                head_expr,
                cases,
            );

            let json_expr = expr_ident_path(arena, &["v"]);
            let match_expr = expr_match(
                expr_constraint(json_expr.clone(), ctyp_json_t(arena)),
                vec![
                    case(
                        pat_construct(lident_path_static(arena, &["JSON", "Array"]), Some(pat_array(vec![]))),
                        expr_spice_error(
                            arena,
                            expr_constant(Constant::String("Expected polyvariant, found empty array".to_string(), None)),
                            json_expr.clone(),
                            None,
                        ),
                    ),
                    case(
                        pat_construct(lident_path_static(arena, &["JSON", "Array"]), Some(pat_var(arena, "json_arr", loc_none()))),
                        decoder_switch,
                    ),
                    case(
                        pat_any(),
                        expr_spice_error(
                            arena,
                            expr_constant(Constant::String("Not a polyvariant".to_string(), None)),
                            json_expr,
                            None,
                        ),
                    ),
                ],
            );
            Some(expr_fun(ArgLabel::Nolabel, pat_var(arena, "v", loc_none()), match_expr, Some(1), arena))
        }
    } else {
        None
    };

    (encoder, decoder)
}

fn generate_codec_decls(
    type_name: &str,
    param_names: &[String],
    codecs: (Option<Expression>, Option<Expression>),
    arena: &mut ParseArena,
) -> Vec<ValueBinding> {
    let mut vbs = Vec::new();

    if let Some(encoder) = codecs.0 {
        let mut expr = expr_fun(
            ArgLabel::Nolabel,
            pat_var(arena, "v", loc_none()),
            expr_apply(encoder, vec![(ArgLabel::Nolabel, expr_ident_path(arena, &["v"]))], false, loc_none()),
            Some(1),
            arena,
        );
        for param in param_names.iter().rev() {
            let name = format!("{}{}", ENCODER_VAR_PREFIX, param);
            expr = expr_fun(ArgLabel::Nolabel, pat_var(arena, &name, loc_none()), expr, None, arena);
        }

        let name = format!("{}{}", type_name, ENCODER_FUNC_SUFFIX);
        vbs.push(ValueBinding {
            pvb_pat: pat_var(arena, &name, loc_none()),
            pvb_expr: expr,
            pvb_attributes: vec![],
            pvb_loc: loc_none(),
        });
    }

    if let Some(decoder) = codecs.1 {
        let mut expr = expr_fun(
            ArgLabel::Nolabel,
            pat_var(arena, "v", loc_none()),
            expr_apply(decoder, vec![(ArgLabel::Nolabel, expr_ident_path(arena, &["v"]))], false, loc_none()),
            Some(1),
            arena,
        );
        for param in param_names.iter().rev() {
            let name = format!("{}{}", DECODER_VAR_PREFIX, param);
            expr = expr_fun(ArgLabel::Nolabel, pat_var(arena, &name, loc_none()), expr, None, arena);
        }

        let name = format!("{}{}", type_name, DECODER_FUNC_SUFFIX);
        vbs.push(ValueBinding {
            pvb_pat: pat_var(arena, &name, loc_none()),
            pvb_expr: expr,
            pvb_attributes: vec![],
            pvb_loc: loc_none(),
        });
    }

    vbs
}

fn map_type_decl_structure(
    decl: &TypeDeclaration,
    arena: &mut ParseArena,
) -> Vec<ValueBinding> {
    let type_name = arena.get_string(decl.ptype_name.txt).to_string();

    let is_unboxed = match get_attribute_by_name(&decl.ptype_attributes, "unboxed", arena) {
        Ok(Some(_)) => true,
        _ => false,
    };

    let generator_settings = match get_generator_settings_from_attributes(&decl.ptype_attributes, arena) {
        Ok(v) => v,
        Err(e) => panic!("{}", e),
    };

    let settings = match generator_settings {
        None => return vec![],
        Some(v) => v,
    };

    let param_names = get_param_names(&decl.ptype_params).unwrap_or_else(|e| panic!("{}", e));

    match (&decl.ptype_manifest, &decl.ptype_kind) {
        (None, TypeKind::Ptype_abstract) => panic!("Can't generate codecs for unspecified type"),
        (Some(manifest), TypeKind::Ptype_abstract) => match &manifest.ptyp_desc {
            CoreTypeDesc::Ptyp_variant(row_fields, _, _) => {
                let codecs = polyvars_generate_codecs(settings, row_fields, is_unboxed, arena);
                generate_codec_decls(&type_name, &param_names, codecs, arena)
            }
            _ => {
                let codecs = codecs_generate_codecs(settings, manifest, arena);
                generate_codec_decls(&type_name, &param_names, codecs, arena)
            }
        },
        (Some(manifest), _) => {
            let codecs = codecs_generate_codecs(settings, manifest, arena);
            generate_codec_decls(&type_name, &param_names, codecs, arena)
        }
        (None, TypeKind::Ptype_variant(constructors)) => {
            let codecs = variants_generate_codecs(settings, constructors, is_unboxed, arena);
            generate_codec_decls(&type_name, &param_names, codecs, arena)
        }
        (None, TypeKind::Ptype_record(labels)) => {
            let codecs = records_generate_codecs(settings, labels, is_unboxed, arena);
            generate_codec_decls(&type_name, &param_names, codecs, arena)
        }
        _ => panic!("This type is not handled by spice"),
    }
}

fn map_structure_item_spice(
    item: &StructureItem,
    arena: &mut ParseArena,
) -> Vec<StructureItem> {
    match &item.pstr_desc {
        StructureItemDesc::Pstr_type(rec_flag, decls) => {
            let mut vbs = Vec::new();
            for decl in decls {
                vbs.extend(map_type_decl_structure(decl, arena));
            }

            if vbs.is_empty() {
                vec![item.clone()]
            } else {
                let value_item = StructureItem {
                    pstr_desc: StructureItemDesc::Pstr_value(*rec_flag, vbs),
                    pstr_loc: loc_none(),
                };
                vec![item.clone(), value_item]
            }
        }
        _ => vec![item.clone()],
    }
}

fn add_encoder_params(param_names: &[String], result_type: CoreType, arena: &mut ParseArena) -> CoreType {
    if param_names.is_empty() {
        return result_type;
    }
    let mut res = result_type;
    for name in param_names.iter().rev() {
        let arg_type = mk_type_arrow(mk_type_var(name), ctyp_json_t(arena), arena);
        res = mk_type_arrow(arg_type, res, arena);
    }
    res
}

fn make_result_type(value_type: CoreType, arena: &mut ParseArena) -> CoreType {
    let decode_error = mk_type_constr(lident_path_static(arena, &["Spice", "decodeError"]), vec![]);
    let result_lid = lident_static(arena, "result");
    mk_type_constr(result_lid, vec![value_type, decode_error])
}

fn add_decoder_params(param_names: &[String], result_type: CoreType, arena: &mut ParseArena) -> CoreType {
    if param_names.is_empty() {
        return result_type;
    }
    let mut res = result_type;
    for name in param_names.iter().rev() {
        let decoder_param = mk_type_arrow(ctyp_json_t(arena), make_result_type(mk_type_var(name), arena), arena);
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

    let type_args: Vec<CoreType> = param_names.iter().map(|p| mk_type_var(p)).collect();
    let type_lid = lident_static(arena, type_name);
    let value_type = mk_type_constr(type_lid, type_args);

    if settings.do_encode {
        let base = mk_type_arrow(value_type.clone(), ctyp_json_t(arena), arena);
        let ty = add_encoder_params(param_names, base, arena);
        let name = format!("{}{}", type_name, ENCODER_FUNC_SUFFIX);
        let name_idx = intern_str(arena, &name);
        let vd = ValueDescription {
            pval_name: Located::new(name_idx, loc_none()),
            pval_type: ty,
            pval_prim: vec![],
            pval_attributes: vec![],
            pval_loc: loc_none(),
        };
        decls.push(SignatureItem {
            psig_desc: SignatureItemDesc::Psig_value(vd),
            psig_loc: loc_none(),
        });
    }

    if settings.do_decode {
        let base = mk_type_arrow(ctyp_json_t(arena), make_result_type(value_type, arena), arena);
        let ty = add_decoder_params(param_names, base, arena);
        let name = format!("{}{}", type_name, DECODER_FUNC_SUFFIX);
        let name_idx = intern_str(arena, &name);
        let vd = ValueDescription {
            pval_name: Located::new(name_idx, loc_none()),
            pval_type: ty,
            pval_prim: vec![],
            pval_attributes: vec![],
            pval_loc: loc_none(),
        };
        decls.push(SignatureItem {
            psig_desc: SignatureItemDesc::Psig_value(vd),
            psig_loc: loc_none(),
        });
    }

    decls
}

fn map_signature_item_spice(
    item: &SignatureItem,
    arena: &mut ParseArena,
) -> Vec<SignatureItem> {
    match &item.psig_desc {
        SignatureItemDesc::Psig_type(_, decls) => {
            let mut generated = Vec::new();
            for decl in decls {
                let settings = match get_generator_settings_from_attributes(&decl.ptype_attributes, arena) {
                    Ok(v) => v,
                    Err(e) => panic!("{}", e),
                };
                if let Some(settings) = settings {
                    let param_names = get_param_names(&decl.ptype_params).unwrap_or_else(|e| panic!("{}", e));
                    let type_name = arena.get_string(decl.ptype_name.txt).to_string();
                    generated.extend(generate_sig_decls(settings, &type_name, &param_names, arena));
                }
            }
            if generated.is_empty() {
                vec![item.clone()]
            } else {
                let mut out = Vec::new();
                out.push(item.clone());
                out.extend(generated);
                out
            }
        }
        _ => vec![item.clone()],
    }
}

pub fn expand_structure_item(
    item: &StructureItem,
    arena: &mut ParseArena,
) -> Vec<StructureItem> {
    map_structure_item_spice(item, arena)
}

pub fn expand_structure(
    structure: &[StructureItem],
    arena: &mut ParseArena,
) -> Vec<StructureItem> {
    structure
        .iter()
        .flat_map(|item| expand_structure_item(item, arena))
        .collect()
}

pub fn expand_signature_item(
    item: &SignatureItem,
    arena: &mut ParseArena,
) -> Vec<SignatureItem> {
    map_signature_item_spice(item, arena)
}

pub fn expand_signature(
    signature: &[SignatureItem],
    arena: &mut ParseArena,
) -> Vec<SignatureItem> {
    signature
        .iter()
        .flat_map(|item| expand_signature_item(item, arena))
        .collect()
}
