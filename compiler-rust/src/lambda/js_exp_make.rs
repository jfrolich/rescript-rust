//! Expression smart constructors for JS IR.
//!
//! Port of `js_exp_make.ml` — expression-level helpers used during
//! Lambda-to-JS compilation.

use crate::js_ir::op::{Kind, Number};
use crate::js_ir::{
    BinOp, Block, CallInfo, CaseClause, Expression, ExpressionDesc, ObjectEntry, Statement,
    StatementDesc, StringClause, VIdent, expression_has_no_side_effects,
};
use crate::lambda::lam_compat::Comparison;
use crate::lambda::lam_primitive::Primitive;
use crate::lambda::{SwitchCaseTag, TagInfo};

pub(crate) fn js_expr_no_side_effects(expr: &Expression) -> bool {
    match &expr.desc {
        ExpressionDesc::Undefined { .. }
        | ExpressionDesc::Null
        | ExpressionDesc::Bool(_)
        | ExpressionDesc::Var(_)
        | ExpressionDesc::Fun { .. }
        | ExpressionDesc::Number(_)
        | ExpressionDesc::Str(_)
        | ExpressionDesc::TemplateLiteral(_)
        | ExpressionDesc::JsonLiteral(_) => true,
        ExpressionDesc::StaticIndex(target, _, _) => js_expr_no_side_effects(target),
        ExpressionDesc::ArrayIndex(left, right)
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
        // A spread reads the source's properties, which may run getters or
        // proxy traps.
        ExpressionDesc::Jsx(_) => false,
        ExpressionDesc::Object(entries) => entries.iter().all(|entry| match entry {
            ObjectEntry::Property(_, value) => js_expr_no_side_effects(value),
            ObjectEntry::Spread(_) => false,
        }),
        ExpressionDesc::Cond(test, consequent, alternate) => {
            js_expr_no_side_effects(test)
                && js_expr_no_side_effects(consequent)
                && js_expr_no_side_effects(alternate)
        }
        ExpressionDesc::Bin(BinOp::Eq, _, _) => false,
        ExpressionDesc::Bin(op @ (BinOp::Pow | BinOp::Div | BinOp::Mod), left, right) => {
            // js_analyzer.ml: on BigInt operands these throw (`**` on a
            // negative exponent, `/` and `%` on a zero divisor). The operand
            // types are not known here, so only a literal right operand that
            // cannot throw is taken as pure.
            let safe_literal = match &right.desc {
                ExpressionDesc::Number(Number::BigInt(lit)) => {
                    if *op == BinOp::Pow {
                        lit.positive
                    } else {
                        lit.value != "0"
                    }
                }
                ExpressionDesc::Number(Number::Int { i, .. }) => *op == BinOp::Pow || *i != 0,
                ExpressionDesc::Number(Number::Float(_)) => true,
                _ => false,
            };
            safe_literal && js_expr_no_side_effects(left)
        }
        ExpressionDesc::Bin(_, left, right) => {
            js_expr_no_side_effects(left) && js_expr_no_side_effects(right)
        }
        ExpressionDesc::TaggedTemplate(tag, _, values) => {
            js_expr_no_side_effects(tag) && values.iter().all(js_expr_no_side_effects)
        }
        ExpressionDesc::InterpolatedTemplate { values, .. } => {
            values.iter().all(js_expr_no_side_effects)
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

/// js_exp_make.ml:36-50 `remove_pure_sub_exp`: an impure expression is kept
/// as it is (`Some x`), including its comment and source location.
pub(crate) fn remove_pure_subexpression(expr: Expression) -> Option<Expression> {
    match expr.desc {
        ExpressionDesc::Var(_)
        | ExpressionDesc::Str(_)
        | ExpressionDesc::TemplateLiteral(_)
        | ExpressionDesc::JsonLiteral(_)
        | ExpressionDesc::Number(_) => None,
        ExpressionDesc::ArrayIndex(ref left, ref right) => {
            if is_pure_subexpression(left.as_ref()) && is_pure_subexpression(right.as_ref()) {
                None
            } else {
                Some(expr)
            }
        }
        ExpressionDesc::Array(ref items, _) => {
            if items.iter().all(is_pure_subexpression) {
                None
            } else {
                Some(expr)
            }
        }
        ExpressionDesc::Seq(left, right) => {
            match (
                remove_pure_subexpression(*left),
                remove_pure_subexpression(*right),
            ) {
                (None, None) => None,
                // `{x with expression_desc = Seq (u, v)}`.
                (Some(left), Some(right)) => {
                    let mut seq = js_seq(left, right);
                    if seq.source_loc.is_none() {
                        seq.source_loc = expr.source_loc;
                    }
                    if seq.comment.is_none() {
                        seq.comment = expr.comment;
                    }
                    Some(seq)
                }
                (None, Some(right)) => Some(right),
                (Some(left), None) => Some(left),
            }
        }
        _ => Some(expr),
    }
}

/// Borrowed form of `remove_pure_subexpression(expr).is_none()`.
pub(crate) fn is_pure_subexpression(expr: &Expression) -> bool {
    match &expr.desc {
        ExpressionDesc::Var(_)
        | ExpressionDesc::Str(_)
        | ExpressionDesc::TemplateLiteral(_)
        | ExpressionDesc::JsonLiteral(_)
        | ExpressionDesc::Number(_) => true,
        ExpressionDesc::ArrayIndex(left, right) | ExpressionDesc::Seq(left, right) => {
            is_pure_subexpression(left) && is_pure_subexpression(right)
        }
        ExpressionDesc::Array(items, _) => items.iter().all(is_pure_subexpression),
        _ => false,
    }
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
        Comparison::Lt => !left & right,
        Comparison::Le => left <= right,
        Comparison::Gt => left & !right,
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

/// js_exp_make.ml `string_comp`: literal operands fold by comparing their
/// semantic values.
pub(crate) fn compare_string_literals(left: &Expression, right: &Expression) -> Option<bool> {
    match (
        left.string_literal_semantic(),
        right.string_literal_semantic(),
    ) {
        (Some(left), Some(right)) => Some(left == right),
        _ => None,
    }
}

/// BigInt literal digits without `_` separators and leading zeros; all-zero
/// literals yield an empty sequence, so equal values compare equal.
fn significant_bigint_digits(digits: &str) -> impl Iterator<Item = char> + '_ {
    digits
        .chars()
        .filter(|c| *c != '_')
        .skip_while(|c| *c == '0')
}

pub(crate) fn compare_bigint_literals(left: &Expression, right: &Expression) -> Option<bool> {
    match (&left.desc, &right.desc) {
        (
            ExpressionDesc::Number(Number::BigInt(left_bigint)),
            ExpressionDesc::Number(Number::BigInt(right_bigint)),
        ) => Some(
            left_bigint.positive == right_bigint.positive
                && significant_bigint_digits(&left_bigint.value)
                    .eq(significant_bigint_digits(&right_bigint.value)),
        ),
        _ => None,
    }
}

pub(crate) fn is_optional_block(expr: &Expression) -> bool {
    matches!(expr.desc, ExpressionDesc::OptionalBlock(_, _))
}

fn is_number_or_undefined(expr: &Expression) -> bool {
    matches!(
        expr.desc,
        ExpressionDesc::Number(_) | ExpressionDesc::Undefined { .. }
    )
}

pub(crate) fn js_seq(left: Expression, right: Expression) -> Expression {
    let Expression {
        source_loc,
        desc,
        comment,
    } = left;
    let left = match desc {
        ExpressionDesc::Seq(first, second) if is_number_or_undefined(&second) => {
            return js_seq(*first, right);
        }
        ExpressionDesc::Seq(first, second) if is_number_or_undefined(&first) => {
            return js_seq(*second, right);
        }
        desc => Expression {
            source_loc,
            desc,
            comment,
        },
    };
    let Expression {
        source_loc,
        desc,
        comment,
    } = right;
    let right = match desc {
        ExpressionDesc::Seq(first, second) if is_number_or_undefined(&first) => {
            return js_seq(left, *second);
        }
        ExpressionDesc::Seq(first, second) if is_number_or_undefined(&second) => {
            return js_seq(js_seq(left, *first), *second);
        }
        desc => Expression {
            source_loc,
            desc,
            comment,
        },
    };
    if matches!(
        left.desc,
        ExpressionDesc::Number(_) | ExpressionDesc::Var(_) | ExpressionDesc::Undefined { .. }
    ) {
        return right;
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
    matches!(
        left.desc,
        ExpressionDesc::Str(_) | ExpressionDesc::TemplateLiteral(_)
    ) && matches!(
        right.desc,
        ExpressionDesc::Str(_) | ExpressionDesc::TemplateLiteral(_)
    )
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

/// Moves the left operand out of a `Bin` expression the caller has already
/// matched.
fn into_bin_left(expr: Expression) -> Expression {
    match expr.desc {
        ExpressionDesc::Bin(_, inner, _) => *inner,
        _ => unreachable!("into_bin_left expects a Bin expression"),
    }
}

pub(crate) fn int32_bor(left: Expression, right: Expression) -> Expression {
    match (&left.desc, &right.desc) {
        (
            ExpressionDesc::Number(Number::Int { i: lhs, .. }),
            ExpressionDesc::Number(Number::Int { i: rhs, .. }),
        ) => int_expr(*lhs | *rhs),
        (_, ExpressionDesc::Bin(BinOp::Lsr, _, shift)) if is_zero_int(shift.as_ref()) => {
            int32_bor(left, into_bin_left(right))
        }
        (ExpressionDesc::Bin(BinOp::Lsr, _, shift), _) if is_zero_int(shift.as_ref()) => {
            int32_bor(into_bin_left(left), right)
        }
        (ExpressionDesc::Bin(BinOp::Lsr, _, shift), _)
            if is_zero_int(&right)
                && int_literal(shift.as_ref()).is_some_and(|value| value > 0) =>
        {
            left
        }
        (ExpressionDesc::Bin(BinOp::Bor, _, truncation), _)
            if is_zero_int(&right) && is_zero_int(truncation.as_ref()) =>
        {
            int32_bor(into_bin_left(left), right)
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
        (ExpressionDesc::Bin(BinOp::Bor, _, truncation), _)
            if is_zero_int(&right) && is_zero_int(truncation.as_ref()) =>
        {
            int32_lsr(into_bin_left(left), right)
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
        (_, ExpressionDesc::Bin(BinOp::Lsr, _, shift)) if is_zero_int(shift.as_ref()) => {
            int32_bxor(left, into_bin_left(right))
        }
        (ExpressionDesc::Bin(BinOp::Lsr, _, shift), _) if is_zero_int(shift.as_ref()) => {
            int32_bxor(into_bin_left(left), right)
        }
        _ => Expression::bin(BinOp::Bxor, left, right),
    }
}

pub(crate) fn int32_band(left: Expression, right: Expression) -> Expression {
    match &left.desc {
        ExpressionDesc::Bin(BinOp::Bor, _, zero) if is_zero_int(zero.as_ref()) => {
            int32_band(into_bin_left(left), right)
        }
        _ => Expression::bin(BinOp::Band, left, right),
    }
}

pub(crate) fn ocaml_typeof_expr(expr: Expression) -> Expression {
    let Expression {
        source_loc: _,
        desc,
        comment,
    } = expr;
    match desc {
        ExpressionDesc::Number(_) | ExpressionDesc::Length(_, _) => Expression::string("number"),
        ExpressionDesc::Str(_) | ExpressionDesc::TemplateLiteral(_) => Expression::string("string"),
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

/// js_exp_make.ml `interpolated_template`: fold literal values into their
/// neighbouring segments; a template left without values is a literal.
pub(crate) fn interpolated_template(
    segments: Vec<crate::string_literal::TemplateSegment>,
    values: Vec<Expression>,
) -> Expression {
    use crate::string_literal::{concat_template, template_from_semantic};
    fn literal_segment(value: &Expression) -> Option<crate::string_literal::TemplateSegment> {
        if value.comment.is_some() {
            return None;
        }
        match &value.desc {
            ExpressionDesc::Str(semantic) => Some(template_from_semantic(semantic)),
            ExpressionDesc::TemplateLiteral(segment) => Some(segment.clone()),
            _ => None,
        }
    }
    assert_eq!(
        segments.len(),
        values.len() + 1,
        "a template has one more segment than value"
    );
    let mut segments = segments.into_iter();
    let mut parts = vec![
        segments
            .next()
            .expect("a template has at least one segment"),
    ];
    let mut merged_segments = Vec::new();
    let mut merged_values = Vec::new();
    for (next_segment, value) in segments.zip(values) {
        match literal_segment(&value) {
            Some(literal) => {
                parts.push(literal);
                parts.push(next_segment);
            }
            None => {
                merged_segments.push(concat_template(&parts));
                merged_values.push(value);
                parts = vec![next_segment];
            }
        }
    }
    merged_segments.push(concat_template(&parts));
    if merged_segments.len() == 1 && merged_values.is_empty() {
        Expression::new(ExpressionDesc::TemplateLiteral(
            merged_segments.pop().expect("one segment"),
        ))
    } else {
        Expression::new(ExpressionDesc::InterpolatedTemplate {
            segments: merged_segments,
            values: merged_values,
        })
    }
}
