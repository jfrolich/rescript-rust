//! Expression smart constructors for JS IR.
//!
//! Port of `js_exp_make.ml` — expression-level helpers used during
//! Lambda-to-JS compilation.

use crate::ident::Ident;
use crate::js_ir::op::{Kind, LengthObject, Number};
use crate::js_ir::{
    BinOp, Block, CallInfo, CaseClause, Expression, ExpressionDesc, ModuleId, Statement,
    StatementDesc, StringClause, VIdent, expression_has_no_side_effects,
};
use crate::lambda::lam_compat::Comparison;
use crate::lambda::lam_primitive::Primitive;
use crate::lambda::{Lambda, SwitchCaseTag, TagInfo};

pub(crate) fn js_expr_no_side_effects(expr: &Expression) -> bool {
    match &expr.desc {
        ExpressionDesc::Undefined { .. }
        | ExpressionDesc::Null
        | ExpressionDesc::Bool(_)
        | ExpressionDesc::Var(_)
        | ExpressionDesc::Fun { .. }
        | ExpressionDesc::Number(_)
        | ExpressionDesc::Str { .. } => true,
        ExpressionDesc::StaticIndex(target, _, _) => js_expr_no_side_effects(target),
        ExpressionDesc::StringIndex(left, right)
        | ExpressionDesc::ArrayIndex(left, right)
        | ExpressionDesc::In(left, right)
        | ExpressionDesc::StringAppend(left, right)
        | ExpressionDesc::Seq(left, right) => {
            js_expr_no_side_effects(left) && js_expr_no_side_effects(right)
        }
        ExpressionDesc::IsNullOrUndefined(inner)
        | ExpressionDesc::Length(inner, _)
        | ExpressionDesc::Typeof(inner)
        | ExpressionDesc::JsNot(inner)
        | ExpressionDesc::JsBnot(inner)
        | ExpressionDesc::CamlBlockTag(inner, _)
        | ExpressionDesc::OptionalBlock(inner, _) => js_expr_no_side_effects(inner),
        ExpressionDesc::Array(items, _) => items.iter().all(js_expr_no_side_effects),
        ExpressionDesc::CamlBlock(items, _, _) => items.iter().all(js_expr_no_side_effects),
        ExpressionDesc::Object(dup, props) => {
            dup.as_deref().is_none_or(js_expr_no_side_effects)
                && props
                    .iter()
                    .all(|(_, value)| js_expr_no_side_effects(value))
        }
        ExpressionDesc::Cond(test, consequent, alternate) => {
            js_expr_no_side_effects(test)
                && js_expr_no_side_effects(consequent)
                && js_expr_no_side_effects(alternate)
        }
        ExpressionDesc::Bin(op, left, right) => {
            *op != BinOp::Eq && js_expr_no_side_effects(left) && js_expr_no_side_effects(right)
        }
        ExpressionDesc::TaggedTemplate(tag, strings, values) => {
            js_expr_no_side_effects(tag)
                && strings.iter().all(js_expr_no_side_effects)
                && values.iter().all(js_expr_no_side_effects)
        }
        ExpressionDesc::FlatCall(_, _)
        | ExpressionDesc::Call(_, _, _)
        | ExpressionDesc::New(_, _)
        | ExpressionDesc::RawJsCode(_)
        | ExpressionDesc::Await(_)
        | ExpressionDesc::Spread(_)
        | ExpressionDesc::RecordRest(_, _) => false,
    }
}

pub(crate) fn remove_pure_subexpression(expr: Expression) -> Option<Expression> {
    match expr.desc {
        ExpressionDesc::Var(_) | ExpressionDesc::Str { .. } | ExpressionDesc::Number(_) => None,
        ExpressionDesc::ArrayIndex(left, right) => {
            if is_pure_subexpression(left.as_ref()) && is_pure_subexpression(right.as_ref()) {
                None
            } else {
                Some(Expression::new(ExpressionDesc::ArrayIndex(left, right)))
            }
        }
        ExpressionDesc::Array(items, mutable_flag) => {
            if items.iter().all(is_pure_subexpression) {
                None
            } else {
                Some(Expression::new(ExpressionDesc::Array(items, mutable_flag)))
            }
        }
        ExpressionDesc::Seq(left, right) => {
            match (
                remove_pure_subexpression(*left),
                remove_pure_subexpression(*right),
            ) {
                (None, None) => None,
                (Some(left), Some(right)) => Some(js_seq(left, right)),
                (None, Some(right)) => Some(right),
                (Some(left), None) => Some(left),
            }
        }
        desc => Some(Expression::new(desc)),
    }
}

pub(crate) fn is_pure_subexpression(expr: &Expression) -> bool {
    remove_pure_subexpression(expr.clone()).is_none()
}

pub(crate) fn comparison_to_binop(cmp: Comparison) -> BinOp {
    match cmp {
        Comparison::Eq => BinOp::EqEqEq,
        Comparison::Neq => BinOp::NotEqEq,
        Comparison::Lt => BinOp::Lt,
        Comparison::Le => BinOp::Le,
        Comparison::Gt => BinOp::Gt,
        Comparison::Ge => BinOp::Ge,
    }
}

pub(crate) fn comparison_to_runtime_member(cmp: Comparison) -> &'static str {
    match cmp {
        Comparison::Eq => "equal",
        Comparison::Neq => "notequal",
        Comparison::Lt => "lessthan",
        Comparison::Le => "lessequal",
        Comparison::Gt => "greaterthan",
        Comparison::Ge => "greaterequal",
    }
}

pub(crate) fn runtime_member_for_eta_wrapped_primitive(
    primitive: &Primitive,
) -> Option<(&'static str, &'static str)> {
    match primitive {
        Primitive::Pobjcomp(cmp) => Some(("Primitive_object", comparison_to_runtime_member(*cmp))),
        Primitive::Pobjorder => Some(("Primitive_object", "compare")),
        Primitive::Pobjmin => Some(("Primitive_object", "min")),
        Primitive::Pobjmax => Some(("Primitive_object", "max")),
        Primitive::Pboolorder => Some(("Primitive_bool", "compare")),
        Primitive::Pboolmin => Some(("Primitive_bool", "min")),
        Primitive::Pboolmax => Some(("Primitive_bool", "max")),
        Primitive::Phash => Some(("Primitive_hash", "hash")),
        Primitive::PhashMixint => Some(("Primitive_hash", "hash_mix_int")),
        Primitive::PhashMixstring => Some(("Primitive_hash", "hash_mix_string")),
        Primitive::PhashFinalmix => Some(("Primitive_hash", "hash_final_mix")),
        Primitive::Pintorder => Some(("Primitive_int", "compare")),
        Primitive::Pintmin => Some(("Primitive_int", "min")),
        Primitive::Pintmax => Some(("Primitive_int", "max")),
        Primitive::Pfloatorder => Some(("Primitive_float", "compare")),
        Primitive::Pfloatmin => Some(("Primitive_float", "min")),
        Primitive::Pfloatmax => Some(("Primitive_float", "max")),
        Primitive::Pbigintorder => Some(("Primitive_bigint", "compare")),
        Primitive::Pbigintmin => Some(("Primitive_bigint", "min")),
        Primitive::Pbigintmax => Some(("Primitive_bigint", "max")),
        Primitive::Pstringorder => Some(("Primitive_string", "compare")),
        Primitive::Pstringmin => Some(("Primitive_string", "min")),
        Primitive::Pstringmax => Some(("Primitive_string", "max")),
        _ => None,
    }
}

pub(crate) fn eta_wrapped_args_match_params(params: &[Ident], args: &[Lambda]) -> bool {
    params.len() == args.len()
        && params
            .iter()
            .zip(args)
            .all(|(param, arg)| matches!(arg, Lambda::Lvar(id) if id.same(param)))
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum NullishLiteral {
    Null,
    Undefined,
}

pub(crate) fn is_nullish_literal(expr: &Expression) -> Option<NullishLiteral> {
    match expr.desc {
        ExpressionDesc::Null => Some(NullishLiteral::Null),
        ExpressionDesc::Undefined { .. } => Some(NullishLiteral::Undefined),
        _ => None,
    }
}

pub(crate) fn is_nullish_eq_impossible_non_null_expr(expr: &Expression) -> bool {
    matches!(
        expr.desc,
        ExpressionDesc::Bool(_)
            | ExpressionDesc::Number(_)
            | ExpressionDesc::Typeof(_)
            | ExpressionDesc::Fun { .. }
            | ExpressionDesc::Array(_, _)
            | ExpressionDesc::CamlBlock(_, _, _)
    ) && js_expr_no_side_effects(expr)
}

pub(crate) fn compile_nullish_strict_comparison(
    cmp: Comparison,
    left: Expression,
    right: Expression,
) -> Expression {
    match (is_nullish_literal(&left), is_nullish_literal(&right)) {
        (Some(NullishLiteral::Null), Some(NullishLiteral::Null))
        | (Some(NullishLiteral::Undefined), Some(NullishLiteral::Undefined)) => {
            return Expression::bool(matches!(cmp, Comparison::Eq));
        }
        (Some(NullishLiteral::Null), Some(NullishLiteral::Undefined))
        | (Some(NullishLiteral::Undefined), Some(NullishLiteral::Null)) => {
            return Expression::bool(matches!(cmp, Comparison::Neq));
        }
        _ => {}
    }

    if is_nullish_literal(&left).is_some() && is_nullish_eq_impossible_non_null_expr(&right) {
        return Expression::bool(matches!(cmp, Comparison::Neq));
    }

    if is_nullish_literal(&right).is_some() && is_nullish_eq_impossible_non_null_expr(&left) {
        return Expression::bool(matches!(cmp, Comparison::Neq));
    }

    // OCaml's `eq_null_undefined_boolean` / `neq_null_undefined_boolean`
    // (js_exp_make.ml:1743-1771) construct the final comparison via raw
    // `{expression_desc = Bin (EqEqEq | NotEqEq, a, b); ...}`. This bypasses
    // the `triple_equal` fold that would otherwise collapse
    // `Optional_block === Undefined` to `false_`. Use `raw_bin_expression`
    // here to match that behavior — an `Expression::bin` call would route
    // through `fold_strict_equality` and incorrectly fold the comparison.
    crate::js_ir::raw_bin_expression(comparison_to_binop(cmp), left, right)
}

pub(crate) fn compile_raw_comparison(
    cmp: Comparison,
    left: Expression,
    right: Expression,
) -> Expression {
    Expression::bin(comparison_to_binop(cmp), left, right)
}

pub(crate) fn compare_bool_literals(cmp: Comparison, left: bool, right: bool) -> bool {
    match cmp {
        Comparison::Eq => left == right,
        Comparison::Neq => left != right,
        Comparison::Lt => left < right,
        Comparison::Le => left <= right,
        Comparison::Gt => left > right,
        Comparison::Ge => left >= right,
    }
}

pub(crate) fn compare_int_literals(cmp: Comparison, left: i32, right: i32) -> bool {
    match cmp {
        Comparison::Eq => left == right,
        Comparison::Neq => left != right,
        Comparison::Lt => left < right,
        Comparison::Le => left <= right,
        Comparison::Gt => left > right,
        Comparison::Ge => left >= right,
    }
}

pub(crate) fn compile_int_equality(left: Expression, right: Expression) -> Expression {
    match (&left.desc, &right.desc) {
        (
            ExpressionDesc::Number(Number::Float(left_float)),
            ExpressionDesc::Number(Number::Float(right_float)),
        ) if left_float.f == right_float.f => Expression::bool(true),
        // OCaml's `float_equal` (= `int_equal`) folds Number Int,Number Int
        // via `bool (i0 = i1)` at `js_exp_make.ml:1217`.
        (
            ExpressionDesc::Number(Number::Int { i: left_int, .. }),
            ExpressionDesc::Number(Number::Int { i: right_int, .. }),
        ) => Expression::bool(left_int == right_int),
        // OCaml's `Js_exp_make.int_equal` (= float_equal) constructs a raw
        // `Bin (EqEqEq, e0, e1)` without going through `bin`/`triple_equal`,
        // so `3 === null` from `Pintcomp Ceq` stays as the literal comparison
        // rather than folding to `false` via the nullish-impossible rule in
        // triple_equal. `Expression::bin`'s `fold_strict_comparison` would
        // fold here, so we bypass it with the raw constructor.
        _ => crate::js_ir::raw_bin_expression(comparison_to_binop(Comparison::Eq), left, right),
    }
}

pub(crate) fn runtime_compare_call_args(expr: &Expression) -> Option<(&Expression, &Expression)> {
    let ExpressionDesc::Call(func, args, _) = &expr.desc else {
        return None;
    };
    let ExpressionDesc::Var(VIdent::Qualified(module, Some(member))) = &func.desc else {
        return None;
    };
    if !matches!(module.kind, Kind::Runtime) || member != "compare" {
        return None;
    }

    match args.as_slice() {
        [left, right] => Some((left, right)),
        _ => None,
    }
}

pub(crate) fn compare_string_literals(left: &Expression, right: &Expression) -> Option<bool> {
    match (&left.desc, &right.desc) {
        (
            ExpressionDesc::Str {
                txt: left_txt,
                delim: left_delim,
            },
            ExpressionDesc::Str {
                txt: right_txt,
                delim: right_delim,
            },
        ) if left_delim == right_delim => {
            if left_txt == right_txt {
                Some(true)
            } else if is_simple_string_comparison(left_txt)
                && is_simple_string_comparison(right_txt)
            {
                Some(false)
            } else {
                None
            }
        }
        _ => None,
    }
}

pub(crate) fn normalize_bigint_literal_digits(digits: &str) -> String {
    let trimmed: String = digits.chars().filter(|c| *c != '_').collect();
    let trimmed = trimmed.trim_start_matches('0');
    if trimmed.is_empty() {
        "0".to_string()
    } else {
        trimmed.to_string()
    }
}

pub(crate) fn compare_bigint_literals(left: &Expression, right: &Expression) -> Option<bool> {
    match (&left.desc, &right.desc) {
        (
            ExpressionDesc::Number(Number::BigInt(left_bigint)),
            ExpressionDesc::Number(Number::BigInt(right_bigint)),
        ) => Some(
            left_bigint.positive == right_bigint.positive
                && normalize_bigint_literal_digits(&left_bigint.value)
                    == normalize_bigint_literal_digits(&right_bigint.value),
        ),
        _ => None,
    }
}

pub(crate) fn is_simple_string_comparison(text: &str) -> bool {
    text.is_ascii() && !text.as_bytes().contains(&b'\\')
}

pub(crate) fn is_optional_block(expr: &Expression) -> bool {
    matches!(expr.desc, ExpressionDesc::OptionalBlock(_, _))
}

pub(crate) fn js_seq(left: Expression, right: Expression) -> Expression {
    match (&left.desc, &right.desc) {
        (ExpressionDesc::Seq(first, second), _)
            if matches!(
                second.as_ref().desc,
                ExpressionDesc::Number(_) | ExpressionDesc::Undefined { .. }
            ) =>
        {
            return js_seq(first.as_ref().clone(), right);
        }
        (ExpressionDesc::Seq(first, second), _)
            if matches!(
                first.as_ref().desc,
                ExpressionDesc::Number(_) | ExpressionDesc::Undefined { .. }
            ) =>
        {
            return js_seq(second.as_ref().clone(), right);
        }
        (_, ExpressionDesc::Seq(first, second))
            if matches!(
                first.as_ref().desc,
                ExpressionDesc::Number(_) | ExpressionDesc::Undefined { .. }
            ) =>
        {
            return js_seq(left, second.as_ref().clone());
        }
        (_, ExpressionDesc::Seq(first, second))
            if matches!(
                second.as_ref().desc,
                ExpressionDesc::Number(_) | ExpressionDesc::Undefined { .. }
            ) =>
        {
            return js_seq(
                js_seq(left, first.as_ref().clone()),
                second.as_ref().clone(),
            );
        }
        (
            ExpressionDesc::Number(_) | ExpressionDesc::Var(_) | ExpressionDesc::Undefined { .. },
            _,
        ) => return right,
        _ => (),
    }

    Expression::new(ExpressionDesc::Seq(Box::new(left), Box::new(right)))
}

pub(crate) fn bool_literal(expr: &Expression) -> Option<bool> {
    match expr.desc {
        ExpressionDesc::Bool(value) => Some(value),
        _ => None,
    }
}

pub(crate) fn both_bool_literals(left: &Expression, right: &Expression) -> bool {
    bool_literal(left).is_some() && bool_literal(right).is_some()
}

pub(crate) fn both_int_literals(left: &Expression, right: &Expression) -> bool {
    int_literal(left).is_some() && int_literal(right).is_some()
}

pub(crate) fn both_float_literals(left: &Expression, right: &Expression) -> bool {
    matches!(left.desc, ExpressionDesc::Number(Number::Float(_)))
        && matches!(right.desc, ExpressionDesc::Number(Number::Float(_)))
}

pub(crate) fn both_bigint_literals(left: &Expression, right: &Expression) -> bool {
    matches!(left.desc, ExpressionDesc::Number(Number::BigInt(_)))
        && matches!(right.desc, ExpressionDesc::Number(Number::BigInt(_)))
}

pub(crate) fn both_string_literals(left: &Expression, right: &Expression) -> bool {
    matches!(left.desc, ExpressionDesc::Str { .. })
        && matches!(right.desc, ExpressionDesc::Str { .. })
}

pub(crate) fn int_expr(value: i32) -> Expression {
    Expression::number(Number::int(value))
}

pub(crate) fn int_literal(expr: &Expression) -> Option<i32> {
    match &expr.desc {
        ExpressionDesc::Number(Number::Int { i, .. }) => Some(*i),
        _ => None,
    }
}

pub(crate) fn is_zero_int(expr: &Expression) -> bool {
    int_literal(expr) == Some(0)
}

pub(crate) fn positive_power_of_two_shift(value: i32) -> Option<u32> {
    if value <= 0 {
        return None;
    }

    let value = value as u32;
    if value.is_power_of_two() {
        Some(value.trailing_zeros())
    } else {
        None
    }
}

pub(crate) fn to_int32(expr: Expression) -> Expression {
    int32_bor(expr, int_expr(0))
}

pub(crate) fn int32_add(left: Expression, right: Expression) -> Expression {
    match (int_literal(&left), int_literal(&right)) {
        (Some(lhs), Some(rhs)) => int_expr(lhs.wrapping_add(rhs)),
        _ => to_int32(Expression::bin(BinOp::Plus, left, right)),
    }
}

pub(crate) fn int32_minus(left: Expression, right: Expression) -> Expression {
    match (int_literal(&left), int_literal(&right)) {
        (Some(lhs), Some(rhs)) => int_expr(lhs.wrapping_sub(rhs)),
        _ => to_int32(Expression::bin(BinOp::Minus, left, right)),
    }
}

pub(crate) fn int32_mul(left: Expression, right: Expression) -> Expression {
    match (int_literal(&left), int_literal(&right)) {
        (_, Some(0)) if expression_has_no_side_effects(&left) => int_expr(0),
        (Some(0), _) if expression_has_no_side_effects(&right) => int_expr(0),
        (Some(lhs), Some(rhs)) => int_expr(lhs.wrapping_mul(rhs)),
        (_, Some(rhs)) => match positive_power_of_two_shift(rhs) {
            Some(shift) => int32_lsl(left, int_expr(shift as i32)),
            None => to_int32(Expression::bin(BinOp::Mul, left, right)),
        },
        (Some(lhs), _) => match positive_power_of_two_shift(lhs) {
            Some(shift) => int32_lsl(right, int_expr(shift as i32)),
            None => to_int32(Expression::bin(BinOp::Mul, left, right)),
        },
        _ => to_int32(Expression::bin(BinOp::Mul, left, right)),
    }
}

pub(crate) fn ocaml_int32_pow(base: i32, exponent: i32) -> i32 {
    let result = (base as f64).powf(exponent as f64);
    if result > i32::MAX as f64 || result < i32::MIN as f64 {
        let wide = result.trunc() as i64;
        ((wide & 0xFFFF_FFFF) as u32) as i32
    } else {
        result.trunc() as i32
    }
}

pub(crate) fn int32_pow(left: Expression, right: Expression) -> Expression {
    match (int_literal(&left), int_literal(&right)) {
        (Some(lhs), Some(rhs)) => int_expr(ocaml_int32_pow(lhs, rhs)),
        _ => to_int32(Expression::bin(BinOp::Pow, left, right)),
    }
}

pub(crate) fn int32_lsl(left: Expression, right: Expression) -> Expression {
    match (int_literal(&left), int_literal(&right)) {
        (Some(lhs), Some(rhs)) => int_expr(lhs.wrapping_shl(rhs as u32)),
        _ => Expression::bin(BinOp::Lsl, left, right),
    }
}

pub(crate) fn int32_bor(left: Expression, right: Expression) -> Expression {
    match (&left.desc, &right.desc) {
        (
            ExpressionDesc::Number(Number::Int { i: lhs, .. }),
            ExpressionDesc::Number(Number::Int { i: rhs, .. }),
        ) => int_expr(*lhs | *rhs),
        (_, ExpressionDesc::Bin(BinOp::Lsr, inner, shift)) if is_zero_int(shift.as_ref()) => {
            int32_bor(left, inner.as_ref().clone())
        }
        (ExpressionDesc::Bin(BinOp::Lsr, inner, shift), _) if is_zero_int(shift.as_ref()) => {
            int32_bor(inner.as_ref().clone(), right)
        }
        (ExpressionDesc::Bin(BinOp::Lsr, _, shift), _)
            if is_zero_int(&right)
                && int_literal(shift.as_ref()).is_some_and(|value| value > 0) =>
        {
            left
        }
        (ExpressionDesc::Bin(BinOp::Bor, inner, truncation), _)
            if is_zero_int(&right) && is_zero_int(truncation.as_ref()) =>
        {
            int32_bor(inner.as_ref().clone(), right)
        }
        _ => Expression::bin(BinOp::Bor, left, right),
    }
}

pub(crate) fn int32_lsr(left: Expression, right: Expression) -> Expression {
    match (&left.desc, &right.desc) {
        (
            ExpressionDesc::Number(Number::Int { i: lhs, .. }),
            ExpressionDesc::Number(Number::Int { i: rhs, .. }),
        ) => int_expr(((*lhs as u32) >> (*rhs as u32)) as i32),
        (ExpressionDesc::Bin(BinOp::Lsr, _, _), _) if is_zero_int(&right) => left,
        (ExpressionDesc::Bin(BinOp::Bor, inner, truncation), _)
            if is_zero_int(&right) && is_zero_int(truncation.as_ref()) =>
        {
            int32_lsr(inner.as_ref().clone(), right)
        }
        // OCaml returns the raw logical shift here rather than applying
        // `to_int32` (`compiler/core/js_exp_make.ml:1447-1456`).
        _ => Expression::bin(BinOp::Lsr, left, right),
    }
}

pub(crate) fn int32_bxor(left: Expression, right: Expression) -> Expression {
    match (&left.desc, &right.desc) {
        (
            ExpressionDesc::Number(Number::Int { i: lhs, .. }),
            ExpressionDesc::Number(Number::Int { i: rhs, .. }),
        ) => int_expr(*lhs ^ *rhs),
        (_, ExpressionDesc::Bin(BinOp::Lsr, inner, shift)) if is_zero_int(shift.as_ref()) => {
            int32_bxor(left, inner.as_ref().clone())
        }
        (ExpressionDesc::Bin(BinOp::Lsr, inner, shift), _) if is_zero_int(shift.as_ref()) => {
            int32_bxor(inner.as_ref().clone(), right)
        }
        _ => Expression::bin(BinOp::Bxor, left, right),
    }
}

pub(crate) fn int32_band(left: Expression, right: Expression) -> Expression {
    match &left.desc {
        ExpressionDesc::Bin(BinOp::Bor, inner, zero) if is_zero_int(zero.as_ref()) => {
            int32_band(inner.as_ref().clone(), right)
        }
        _ => Expression::bin(BinOp::Band, left, right),
    }
}

pub(crate) fn int32_offset(expr: Expression, offset: i32) -> Expression {
    if offset == 0 {
        expr
    } else {
        int32_add(expr, int_expr(offset))
    }
}

pub(crate) fn ocaml_typeof_expr(expr: Expression) -> Expression {
    let Expression {
        source_loc,
        desc,
        comment,
    } = expr;
    match desc {
        ExpressionDesc::Number(_) | ExpressionDesc::Length(_, _) => Expression::string("number"),
        ExpressionDesc::Str { .. } => Expression::string("string"),
        ExpressionDesc::Array(_, _) => Expression::string("object"),
        ExpressionDesc::Bool(_) => Expression::string("boolean"),
        desc => Expression::new(ExpressionDesc::Typeof(Box::new(Expression {
            source_loc: None,
            desc,
            comment,
        }))),
    }
}

pub(crate) fn raw_typeof_comparison(expr: Expression, op: BinOp, type_name: &str) -> Expression {
    Expression::bin(op, ocaml_typeof_expr(expr), Expression::string(type_name))
}

pub(crate) fn is_type_number_expr(expr: Expression) -> Expression {
    raw_typeof_comparison(expr, BinOp::EqEqEq, "number")
}

pub(crate) fn pure_indexed_block_item(target: &Expression, idx: i32) -> Option<Expression> {
    if !js_expr_no_side_effects(target) {
        return None;
    }

    let index = usize::try_from(idx).ok()?;
    match &target.desc {
        ExpressionDesc::Array(items, _) | ExpressionDesc::CamlBlock(items, _, _) => {
            items.get(index).cloned()
        }
        _ => None,
    }
}

pub(crate) fn pure_record_field_item(
    target: &Expression,
    field: &str,
    idx: i32,
) -> Option<Expression> {
    if !js_expr_no_side_effects(target) {
        return None;
    }

    match &target.desc {
        ExpressionDesc::CamlBlock(items, _, tag)
            if matches!(
                **tag,
                TagInfo::Record { .. } | TagInfo::RecordInlined { .. }
            ) =>
        {
            let (TagInfo::Record { fields, .. } | TagInfo::RecordInlined { fields, .. }) = &**tag
            else {
                unreachable!()
            };
            for (item, (field_name, _)) in items.iter().zip(fields.iter()) {
                if field_name == field {
                    return Some(item.clone());
                }
            }
            None
        }
        _ => pure_indexed_block_item(target, idx),
    }
}

pub(crate) fn direct_projection_from_pure_literal(
    target: &Expression,
    field: Option<&str>,
    index: Option<i32>,
) -> Option<Expression> {
    if !js_expr_no_side_effects(target) {
        return None;
    }

    match &target.desc {
        ExpressionDesc::CamlBlock(items, _, tag)
            if matches!(
                **tag,
                TagInfo::Record { .. } | TagInfo::RecordInlined { .. }
            ) =>
        {
            let (TagInfo::Record { fields, .. } | TagInfo::RecordInlined { fields, .. }) = &**tag
            else {
                unreachable!()
            };
            if let Some(field) = field {
                for (item, (field_name, _)) in items.iter().zip(fields.iter()) {
                    if field_name == field {
                        return Some(item.clone());
                    }
                }
                None
            } else {
                let index = usize::try_from(index?).ok()?;
                items.get(index).cloned()
            }
        }
        ExpressionDesc::Array(items, _) | ExpressionDesc::CamlBlock(items, _, _) => {
            let index = usize::try_from(index?).ok()?;
            items.get(index).cloned()
        }
        _ => None,
    }
}

pub(crate) fn poly_var_tag_access(target: &Expression) -> Expression {
    match &target.desc {
        ExpressionDesc::CamlBlock(items, _, _) if js_expr_no_side_effects(target) => items
            .first()
            .cloned()
            .expect("polyvariant tag access expects a tag element"),
        _ => Expression::new(ExpressionDesc::StaticIndex(
            Box::new(target.clone()),
            "NAME".to_string(),
            Some(0),
        )),
    }
}

pub(crate) fn poly_var_value_access(target: &Expression) -> Expression {
    match &target.desc {
        ExpressionDesc::CamlBlock(items, _, _) if js_expr_no_side_effects(target) => items
            .get(1)
            .cloned()
            .expect("polyvariant value access expects a payload element"),
        _ => Expression::new(ExpressionDesc::StaticIndex(
            Box::new(target.clone()),
            "VAL".to_string(),
            Some(1),
        )),
    }
}

pub(crate) fn external_polyvar_string_dispatch(
    dispatches: &[(String, String)],
    txt: &str,
) -> String {
    dispatches
        .iter()
        .find(|(source, _)| source == txt)
        .map(|(_, target)| target.clone())
        .unwrap_or_else(|| panic!("missing polyvariant string dispatch for {txt}"))
}

pub(crate) fn external_polyvar_int_dispatch(dispatches: &[(String, i64)], txt: &str) -> i64 {
    dispatches
        .iter()
        .find(|(source, _)| source == txt)
        .map(|(_, target)| *target)
        .unwrap_or_else(|| panic!("missing polyvariant int dispatch for {txt}"))
}

pub(crate) fn string_switch_iife(
    scrutinee: Expression,
    cases: Vec<(String, Expression)>,
) -> Expression {
    let clauses = cases
        .into_iter()
        .map(|(tag, value)| StringClause {
            tag_type: SwitchCaseTag::String(tag),
            clause: CaseClause {
                source_loc: None,
                body: vec![Statement::return_(value)],
                should_break: false,
                comment: None,
            },
        })
        .collect();
    Expression::call(
        Expression::new(ExpressionDesc::Fun {
            is_method: false,
            params: vec![],
            body: vec![Statement::new(StatementDesc::StringSwitch(
                scrutinee, clauses, None,
            ))],
            env: Default::default(),
            return_unit: false,
            async_: false,
            directive: None,
        }),
        vec![],
        CallInfo::default(),
    )
}

pub(crate) fn block_with_return_expr_iife(mut block: Block, expr: Expression) -> Expression {
    if block.is_empty() {
        return expr;
    }

    block.push(Statement::return_(expr));
    Expression::call(
        Expression::new(ExpressionDesc::Fun {
            is_method: false,
            params: vec![],
            body: block,
            env: Default::default(),
            return_unit: false,
            async_: false,
            directive: None,
        }),
        vec![],
        CallInfo::default(),
    )
}

pub(crate) fn is_type_object_expr(expr: Expression) -> Expression {
    raw_typeof_comparison(expr, BinOp::EqEqEq, "object")
}

pub(crate) fn int_bnot(expr: Expression) -> Expression {
    match int_literal(&expr) {
        Some(value) => int_expr(!value),
        None => Expression::new(ExpressionDesc::JsBnot(Box::new(expr))),
    }
}
