//! Expression smart constructors for JS IR.
//!
//! Port of `js_exp_make.ml` — expression-level helpers used during
//! Lambda-to-JS compilation. Builders take the arena last (see
//! `js_ir::build`).

use crate::js_ir::CallInfo;
use crate::js_ir::arena::{Block, Clause, Expr, ExprKind, FunInfo, JsArena, StringClauseInfo};
use crate::js_ir::build::{exp as E, expression_has_no_side_effects, int_of, stmt as S};
use crate::js_ir::op::{BinOp, Kind, Number};
use crate::lambda::lam_compat::Comparison;
use crate::lambda::lam_primitive::Primitive;
use crate::lambda::{SwitchCaseTag, TagInfo};

pub(crate) fn js_expr_no_side_effects(a: &JsArena, expr: Expr) -> bool {
    let pure = |e: Expr| js_expr_no_side_effects(a, e);
    match a.ek(expr) {
        ExprKind::Undefined { .. }
        | ExprKind::Null
        | ExprKind::Bool(_)
        | ExprKind::Var(_)
        | ExprKind::Qualified(_)
        | ExprKind::Fun(_)
        | ExprKind::Number(_)
        | ExprKind::Str(_)
        | ExprKind::TemplateLiteral(_)
        | ExprKind::JsonLiteral(_) => true,
        ExprKind::StaticIndex(target, _, _) => pure(target),
        ExprKind::StringIndex(left, right)
        | ExprKind::ArrayIndex(left, right)
        | ExprKind::In(left, right)
        | ExprKind::StringAppend(left, right)
        | ExprKind::Seq(left, right) => pure(left) && pure(right),
        ExprKind::IsNullOrUndefined(inner)
        | ExprKind::Length(inner, _)
        | ExprKind::Typeof(inner)
        | ExprKind::JsNot(inner)
        | ExprKind::JsBnot(inner)
        | ExprKind::CamlBlockTag(inner, _)
        | ExprKind::OptionalBlock(inner, _) => pure(inner),
        ExprKind::Array(items, _) | ExprKind::CamlBlock(items, _, _) => {
            a.exprs(items).iter().all(|e| pure(*e))
        }
        ExprKind::Object(dup, props) => {
            dup.is_none_or(pure) && a.props(props).iter().all(|(_, value)| pure(*value))
        }
        ExprKind::Cond(test, consequent, alternate) => {
            pure(test) && pure(consequent) && pure(alternate)
        }
        ExprKind::Bin(BinOp::Eq, _, _) => false,
        ExprKind::Bin(op @ (BinOp::Pow | BinOp::Div | BinOp::Mod), left, right) => {
            // js_analyzer.ml: on BigInt operands these throw (`**` on a
            // negative exponent, `/` and `%` on a zero divisor). The operand
            // types are not known here, so only a literal right operand that
            // cannot throw is taken as pure.
            let safe_literal = match a.ek(right) {
                ExprKind::Number(n) => match a.number(n) {
                    Number::BigInt(lit) => {
                        if op == BinOp::Pow {
                            lit.positive
                        } else {
                            lit.value != "0"
                        }
                    }
                    Number::Int { i, .. } => op == BinOp::Pow || *i != 0,
                    Number::Float(_) => true,
                },
                _ => false,
            };
            safe_literal && pure(left)
        }
        ExprKind::Bin(_, left, right) => pure(left) && pure(right),
        ExprKind::TaggedTemplate(tag, _, values) => {
            pure(tag) && a.exprs(values).iter().all(|e| pure(*e))
        }
        ExprKind::InterpolatedTemplate(_, values) => a.exprs(values).iter().all(|e| pure(*e)),
        ExprKind::FlatCall(_, _)
        | ExprKind::Call(_, _, _)
        | ExprKind::New(_, _)
        | ExprKind::RawJsCode(_)
        | ExprKind::Await(_)
        | ExprKind::Spread(_)
        | ExprKind::RecordRest(_, _) => false,
    }
}

/// js_exp_make.ml:36-50 `remove_pure_sub_exp`: an impure expression is kept
/// as it is (`Some x`), including its comment and source location.
pub(crate) fn remove_pure_subexpression(expr: Expr, j: &mut JsArena) -> Option<Expr> {
    match j.ek(expr) {
        ExprKind::Var(_)
        | ExprKind::Qualified(_)
        | ExprKind::Str(_)
        | ExprKind::TemplateLiteral(_)
        | ExprKind::JsonLiteral(_)
        | ExprKind::Number(_) => None,
        ExprKind::ArrayIndex(left, right) => {
            if is_pure_subexpression(j, left) && is_pure_subexpression(j, right) {
                None
            } else {
                Some(expr)
            }
        }
        ExprKind::Array(items, _) => {
            if j.exprs(items).iter().all(|e| is_pure_subexpression(j, *e)) {
                None
            } else {
                Some(expr)
            }
        }
        ExprKind::Seq(left, right) => {
            let left = remove_pure_subexpression(left, j);
            let right = remove_pure_subexpression(right, j);
            match (left, right) {
                (None, None) => None,
                // `{x with expression_desc = Seq (u, v)}`.
                (Some(left), Some(right)) => {
                    let seq = js_seq(left, right, j);
                    let mut cold = j.expr_cold(seq);
                    let outer = j.expr_cold(expr);
                    if cold.source_loc.is_none() {
                        cold.source_loc = outer.source_loc;
                    }
                    if cold.comment.is_none() {
                        cold.comment = outer.comment;
                    }
                    Some(j.with_expr_cold(seq, cold))
                }
                (None, Some(right)) => Some(right),
                (Some(left), None) => Some(left),
            }
        }
        _ => Some(expr),
    }
}

/// Borrowed form of `remove_pure_subexpression(expr).is_none()`.
pub(crate) fn is_pure_subexpression(a: &JsArena, expr: Expr) -> bool {
    match a.ek(expr) {
        ExprKind::Var(_)
        | ExprKind::Qualified(_)
        | ExprKind::Str(_)
        | ExprKind::TemplateLiteral(_)
        | ExprKind::JsonLiteral(_)
        | ExprKind::Number(_) => true,
        ExprKind::ArrayIndex(left, right) | ExprKind::Seq(left, right) => {
            is_pure_subexpression(a, left) && is_pure_subexpression(a, right)
        }
        ExprKind::Array(items, _) => a.exprs(items).iter().all(|e| is_pure_subexpression(a, *e)),
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

pub(crate) fn is_nullish_literal(a: &JsArena, expr: Expr) -> Option<NullishLiteral> {
    match a.ek(expr) {
        ExprKind::Null => Some(NullishLiteral::Null),
        ExprKind::Undefined { .. } => Some(NullishLiteral::Undefined),
        _ => None,
    }
}

pub(crate) fn is_nullish_eq_impossible_non_null_expr(a: &JsArena, expr: Expr) -> bool {
    matches!(
        a.ek(expr),
        ExprKind::Bool(_)
            | ExprKind::Number(_)
            | ExprKind::Typeof(_)
            | ExprKind::Fun(_)
            | ExprKind::Array(_, _)
            | ExprKind::CamlBlock(_, _, _)
    ) && js_expr_no_side_effects(a, expr)
}

pub(crate) fn compile_nullish_strict_comparison(
    cmp: Comparison,
    left: Expr,
    right: Expr,
    j: &mut JsArena,
) -> Expr {
    match (is_nullish_literal(j, left), is_nullish_literal(j, right)) {
        (Some(NullishLiteral::Null), Some(NullishLiteral::Null))
        | (Some(NullishLiteral::Undefined), Some(NullishLiteral::Undefined)) => {
            return E::bool(matches!(cmp, Comparison::Eq), j);
        }
        (Some(NullishLiteral::Null), Some(NullishLiteral::Undefined))
        | (Some(NullishLiteral::Undefined), Some(NullishLiteral::Null)) => {
            return E::bool(matches!(cmp, Comparison::Neq), j);
        }
        _ => {}
    }

    if is_nullish_literal(j, left).is_some() && is_nullish_eq_impossible_non_null_expr(j, right) {
        return E::bool(matches!(cmp, Comparison::Neq), j);
    }

    if is_nullish_literal(j, right).is_some() && is_nullish_eq_impossible_non_null_expr(j, left) {
        return E::bool(matches!(cmp, Comparison::Neq), j);
    }

    // OCaml's `eq_null_undefined_boolean` / `neq_null_undefined_boolean`
    // (js_exp_make.ml:1743-1771) construct the final comparison via raw
    // `{expression_desc = Bin (EqEqEq | NotEqEq, a, b); ...}`. This bypasses
    // the `triple_equal` fold that would otherwise collapse
    // `Optional_block === Undefined` to `false_`.
    E::raw_bin(comparison_to_binop(cmp), left, right, j)
}

pub(crate) fn compile_raw_comparison(
    cmp: Comparison,
    left: Expr,
    right: Expr,
    j: &mut JsArena,
) -> Expr {
    E::bin(comparison_to_binop(cmp), left, right, j)
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

fn float_literal(a: &JsArena, e: Expr) -> Option<&str> {
    match a.ek(e) {
        ExprKind::Number(n) => match a.number(n) {
            Number::Float(f) => Some(&f.f),
            _ => None,
        },
        _ => None,
    }
}

fn bigint_literal(a: &JsArena, e: Expr) -> Option<&crate::js_ir::op::BigIntLit> {
    match a.ek(e) {
        ExprKind::Number(n) => match a.number(n) {
            Number::BigInt(b) => Some(b),
            _ => None,
        },
        _ => None,
    }
}

pub(crate) fn compile_int_equality(left: Expr, right: Expr, j: &mut JsArena) -> Expr {
    if let (Some(l), Some(r)) = (float_literal(j, left), float_literal(j, right))
        && l == r
    {
        return E::bool(true, j);
    }
    // OCaml's `float_equal` (= `int_equal`) folds Number Int,Number Int
    // via `bool (i0 = i1)` at `js_exp_make.ml:1217`.
    if let (Some(l), Some(r)) = (int_of(j, left), int_of(j, right)) {
        return E::bool(l == r, j);
    }
    // OCaml's `Js_exp_make.int_equal` (= float_equal) constructs a raw
    // `Bin (EqEqEq, e0, e1)` without going through `bin`/`triple_equal`,
    // so `3 === null` from `Pintcomp Ceq` stays as the literal comparison.
    E::raw_bin(comparison_to_binop(Comparison::Eq), left, right, j)
}

pub(crate) fn runtime_compare_call_args(a: &JsArena, expr: Expr) -> Option<(Expr, Expr)> {
    let ExprKind::Call(func, args, _) = a.ek(expr) else {
        return None;
    };
    let ExprKind::Qualified(q) = a.ek(func) else {
        return None;
    };
    let (module, member) = a.qual(q);
    if !matches!(module.kind, Kind::Runtime) || member != Some("compare") {
        return None;
    }

    match a.exprs(args) {
        [left, right] => Some((*left, *right)),
        _ => None,
    }
}

/// js_exp_make.ml `string_comp`: literal operands fold by comparing their
/// semantic values.
pub(crate) fn compare_string_literals(a: &JsArena, left: Expr, right: Expr) -> Option<bool> {
    use crate::js_ir::build::string_literal_semantic as lit;
    match (lit(a, left), lit(a, right)) {
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

pub(crate) fn compare_bigint_literals(a: &JsArena, left: Expr, right: Expr) -> Option<bool> {
    match (bigint_literal(a, left), bigint_literal(a, right)) {
        (Some(l), Some(r)) => Some(
            l.positive == r.positive
                && significant_bigint_digits(&l.value).eq(significant_bigint_digits(&r.value)),
        ),
        _ => None,
    }
}

pub(crate) fn is_optional_block(a: &JsArena, expr: Expr) -> bool {
    matches!(a.ek(expr), ExprKind::OptionalBlock(_, _))
}

fn is_number_or_undefined(a: &JsArena, expr: Expr) -> bool {
    matches!(a.ek(expr), ExprKind::Number(_) | ExprKind::Undefined { .. })
}

pub(crate) fn js_seq(left: Expr, right: Expr, j: &mut JsArena) -> Expr {
    if let ExprKind::Seq(first, second) = j.ek(left) {
        if is_number_or_undefined(j, second) {
            return js_seq(first, right, j);
        }
        if is_number_or_undefined(j, first) {
            return js_seq(second, right, j);
        }
    }
    if let ExprKind::Seq(first, second) = j.ek(right) {
        if is_number_or_undefined(j, first) {
            return js_seq(left, second, j);
        }
        if is_number_or_undefined(j, second) {
            let inner = js_seq(left, first, j);
            return js_seq(inner, second, j);
        }
    }
    if matches!(
        j.ek(left),
        ExprKind::Number(_)
            | ExprKind::Var(_)
            | ExprKind::Qualified(_)
            | ExprKind::Undefined { .. }
    ) {
        return right;
    }

    E::seq(left, right, j)
}

pub(crate) fn bool_literal(a: &JsArena, expr: Expr) -> Option<bool> {
    match a.ek(expr) {
        ExprKind::Bool(value) => Some(value),
        _ => None,
    }
}

pub(crate) fn both_bool_literals(a: &JsArena, left: Expr, right: Expr) -> bool {
    bool_literal(a, left).is_some() && bool_literal(a, right).is_some()
}

pub(crate) fn both_int_literals(a: &JsArena, left: Expr, right: Expr) -> bool {
    int_literal(a, left).is_some() && int_literal(a, right).is_some()
}

pub(crate) fn both_float_literals(a: &JsArena, left: Expr, right: Expr) -> bool {
    float_literal(a, left).is_some() && float_literal(a, right).is_some()
}

pub(crate) fn both_bigint_literals(a: &JsArena, left: Expr, right: Expr) -> bool {
    bigint_literal(a, left).is_some() && bigint_literal(a, right).is_some()
}

pub(crate) fn both_string_literals(a: &JsArena, left: Expr, right: Expr) -> bool {
    matches!(a.ek(left), ExprKind::Str(_) | ExprKind::TemplateLiteral(_))
        && matches!(a.ek(right), ExprKind::Str(_) | ExprKind::TemplateLiteral(_))
}

pub(crate) fn int_expr(value: i32, j: &mut JsArena) -> Expr {
    E::int(value, j)
}

pub(crate) fn int_literal(a: &JsArena, expr: Expr) -> Option<i32> {
    int_of(a, expr)
}

pub(crate) fn is_zero_int(a: &JsArena, expr: Expr) -> bool {
    int_literal(a, expr) == Some(0)
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

pub(crate) fn to_int32(expr: Expr, j: &mut JsArena) -> Expr {
    let zero = int_expr(0, j);
    int32_bor(expr, zero, j)
}

pub(crate) fn int32_add(left: Expr, right: Expr, j: &mut JsArena) -> Expr {
    match (int_literal(j, left), int_literal(j, right)) {
        (Some(lhs), Some(rhs)) => int_expr(lhs.wrapping_add(rhs), j),
        _ => {
            let sum = E::bin(BinOp::Plus, left, right, j);
            to_int32(sum, j)
        }
    }
}

pub(crate) fn int32_minus(left: Expr, right: Expr, j: &mut JsArena) -> Expr {
    match (int_literal(j, left), int_literal(j, right)) {
        (Some(lhs), Some(rhs)) => int_expr(lhs.wrapping_sub(rhs), j),
        _ => {
            let diff = E::bin(BinOp::Minus, left, right, j);
            to_int32(diff, j)
        }
    }
}

pub(crate) fn int32_mul(left: Expr, right: Expr, j: &mut JsArena) -> Expr {
    let mul = |left, right, j: &mut JsArena| {
        let product = E::bin(BinOp::Mul, left, right, j);
        to_int32(product, j)
    };
    match (int_literal(j, left), int_literal(j, right)) {
        (_, Some(0)) if expression_has_no_side_effects(j, left) => int_expr(0, j),
        (Some(0), _) if expression_has_no_side_effects(j, right) => int_expr(0, j),
        (Some(lhs), Some(rhs)) => int_expr(lhs.wrapping_mul(rhs), j),
        (_, Some(rhs)) => match positive_power_of_two_shift(rhs) {
            Some(shift) => {
                let shift = int_expr(shift as i32, j);
                int32_lsl(left, shift, j)
            }
            None => mul(left, right, j),
        },
        (Some(lhs), _) => match positive_power_of_two_shift(lhs) {
            Some(shift) => {
                let shift = int_expr(shift as i32, j);
                int32_lsl(right, shift, j)
            }
            None => mul(left, right, j),
        },
        _ => mul(left, right, j),
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

pub(crate) fn int32_pow(left: Expr, right: Expr, j: &mut JsArena) -> Expr {
    match (int_literal(j, left), int_literal(j, right)) {
        (Some(lhs), Some(rhs)) => int_expr(ocaml_int32_pow(lhs, rhs), j),
        _ => {
            let pow = E::bin(BinOp::Pow, left, right, j);
            to_int32(pow, j)
        }
    }
}

pub(crate) fn int32_lsl(left: Expr, right: Expr, j: &mut JsArena) -> Expr {
    match (int_literal(j, left), int_literal(j, right)) {
        (Some(lhs), Some(rhs)) => int_expr(lhs.wrapping_shl(rhs as u32), j),
        _ => E::bin(BinOp::Lsl, left, right, j),
    }
}

/// The operands of `Bin(op, left, right)`.
fn bin_parts(a: &JsArena, e: Expr, op: BinOp) -> Option<(Expr, Expr)> {
    match a.ek(e) {
        ExprKind::Bin(o, l, r) if o == op => Some((l, r)),
        _ => None,
    }
}

pub(crate) fn int32_bor(left: Expr, right: Expr, j: &mut JsArena) -> Expr {
    if let (Some(lhs), Some(rhs)) = (int_literal(j, left), int_literal(j, right)) {
        return int_expr(lhs | rhs, j);
    }
    if let Some((inner, shift)) = bin_parts(j, right, BinOp::Lsr)
        && is_zero_int(j, shift)
    {
        return int32_bor(left, inner, j);
    }
    if let Some((inner, shift)) = bin_parts(j, left, BinOp::Lsr) {
        if is_zero_int(j, shift) {
            return int32_bor(inner, right, j);
        }
        if is_zero_int(j, right) && int_literal(j, shift).is_some_and(|value| value > 0) {
            return left;
        }
    }
    if let Some((inner, truncation)) = bin_parts(j, left, BinOp::Bor)
        && is_zero_int(j, right)
        && is_zero_int(j, truncation)
    {
        return int32_bor(inner, right, j);
    }
    E::bin(BinOp::Bor, left, right, j)
}

pub(crate) fn int32_lsr(left: Expr, right: Expr, j: &mut JsArena) -> Expr {
    if let (Some(lhs), Some(rhs)) = (int_literal(j, left), int_literal(j, right)) {
        return int_expr(((lhs as u32) >> (rhs as u32)) as i32, j);
    }
    if bin_parts(j, left, BinOp::Lsr).is_some() && is_zero_int(j, right) {
        return left;
    }
    if let Some((inner, truncation)) = bin_parts(j, left, BinOp::Bor)
        && is_zero_int(j, right)
        && is_zero_int(j, truncation)
    {
        return int32_lsr(inner, right, j);
    }
    // OCaml returns the raw logical shift here rather than applying
    // `to_int32` (`compiler/core/js_exp_make.ml:1447-1456`).
    E::bin(BinOp::Lsr, left, right, j)
}

pub(crate) fn int32_bxor(left: Expr, right: Expr, j: &mut JsArena) -> Expr {
    if let (Some(lhs), Some(rhs)) = (int_literal(j, left), int_literal(j, right)) {
        return int_expr(lhs ^ rhs, j);
    }
    if let Some((inner, shift)) = bin_parts(j, right, BinOp::Lsr)
        && is_zero_int(j, shift)
    {
        return int32_bxor(left, inner, j);
    }
    if let Some((inner, shift)) = bin_parts(j, left, BinOp::Lsr)
        && is_zero_int(j, shift)
    {
        return int32_bxor(inner, right, j);
    }
    E::bin(BinOp::Bxor, left, right, j)
}

pub(crate) fn int32_band(left: Expr, right: Expr, j: &mut JsArena) -> Expr {
    if let Some((inner, zero)) = bin_parts(j, left, BinOp::Bor)
        && is_zero_int(j, zero)
    {
        return int32_band(inner, right, j);
    }
    E::bin(BinOp::Band, left, right, j)
}

pub(crate) fn ocaml_typeof_expr(expr: Expr, j: &mut JsArena) -> Expr {
    match j.ek(expr) {
        ExprKind::Number(_) | ExprKind::Length(_, _) => E::string("number", j),
        ExprKind::Str(_) | ExprKind::TemplateLiteral(_) => E::string("string", j),
        ExprKind::Array(_, _) => E::string("object", j),
        ExprKind::Bool(_) => E::string("boolean", j),
        _ => {
            let inner = j.with_expr_loc(expr, None);
            j.expr(ExprKind::Typeof(inner))
        }
    }
}

pub(crate) fn raw_typeof_comparison(
    expr: Expr,
    op: BinOp,
    type_name: &str,
    j: &mut JsArena,
) -> Expr {
    let typeof_expr = ocaml_typeof_expr(expr, j);
    let name = E::string(type_name, j);
    E::bin(op, typeof_expr, name, j)
}

pub(crate) fn is_type_number_expr(expr: Expr, j: &mut JsArena) -> Expr {
    raw_typeof_comparison(expr, BinOp::EqEqEq, "number", j)
}

pub(crate) fn pure_indexed_block_item(a: &JsArena, target: Expr, idx: i32) -> Option<Expr> {
    if !js_expr_no_side_effects(a, target) {
        return None;
    }

    let index = usize::try_from(idx).ok()?;
    match a.ek(target) {
        ExprKind::Array(items, _) | ExprKind::CamlBlock(items, _, _) => {
            a.exprs(items).get(index).copied()
        }
        _ => None,
    }
}

fn record_block_field(a: &JsArena, target: Expr, field: &str) -> Option<Option<Expr>> {
    match a.ek(target) {
        ExprKind::CamlBlock(items, _, tag)
            if matches!(a.tag(tag), TagInfo::Record(_) | TagInfo::RecordInlined(_)) =>
        {
            let fields = a.tag(tag).record_fields().expect("record block");
            for (item, (field_name, _)) in a.exprs(items).iter().zip(fields.iter()) {
                if field_name == field {
                    return Some(Some(*item));
                }
            }
            Some(None)
        }
        _ => None,
    }
}

pub(crate) fn pure_record_field_item(
    a: &JsArena,
    target: Expr,
    field: &str,
    idx: i32,
) -> Option<Expr> {
    if !js_expr_no_side_effects(a, target) {
        return None;
    }

    match record_block_field(a, target, field) {
        Some(found) => found,
        None => pure_indexed_block_item(a, target, idx),
    }
}

pub(crate) fn direct_projection_from_pure_literal(
    a: &JsArena,
    target: Expr,
    field: Option<&str>,
    index: Option<i32>,
) -> Option<Expr> {
    if !js_expr_no_side_effects(a, target) {
        return None;
    }

    match a.ek(target) {
        ExprKind::CamlBlock(items, _, tag)
            if matches!(a.tag(tag), TagInfo::Record(_) | TagInfo::RecordInlined(_)) =>
        {
            if let Some(field) = field {
                record_block_field(a, target, field).flatten()
            } else {
                let index = usize::try_from(index?).ok()?;
                a.exprs(items).get(index).copied()
            }
        }
        ExprKind::Array(items, _) | ExprKind::CamlBlock(items, _, _) => {
            let index = usize::try_from(index?).ok()?;
            a.exprs(items).get(index).copied()
        }
        _ => None,
    }
}

pub(crate) fn poly_var_tag_access(target: Expr, j: &mut JsArena) -> Expr {
    match j.ek(target) {
        ExprKind::CamlBlock(items, _, _) if js_expr_no_side_effects(j, target) => *j
            .exprs(items)
            .first()
            .expect("polyvariant tag access expects a tag element"),
        _ => E::static_index(target, "NAME", Some(0), j),
    }
}

pub(crate) fn poly_var_value_access(target: Expr, j: &mut JsArena) -> Expr {
    match j.ek(target) {
        ExprKind::CamlBlock(items, _, _) if js_expr_no_side_effects(j, target) => *j
            .exprs(items)
            .get(1)
            .expect("polyvariant value access expects a payload element"),
        _ => E::static_index(target, "VAL", Some(1), j),
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

/// `function () { body }` called with no arguments.
pub(crate) fn iife(body: &[crate::js_ir::arena::Stmt], j: &mut JsArena) -> Expr {
    let f = fun_expr(false, &[], body, false, false, j);
    E::call(f, &[], CallInfo::default(), j)
}

/// A function expression (`J.Fun`).
pub(crate) fn fun_expr(
    is_method: bool,
    params: &[crate::ident::Ident],
    body: &[crate::js_ir::arena::Stmt],
    return_unit: bool,
    async_: bool,
    j: &mut JsArena,
) -> Expr {
    let params = j.ident_list(params);
    let body = j.stmt_list(body);
    let f = j.fun_id(FunInfo {
        is_method,
        params,
        body,
        return_unit,
        async_,
        directive: None,
    });
    j.expr(ExprKind::Fun(f))
}

pub(crate) fn string_switch_iife(
    scrutinee: Expr,
    cases: Vec<(String, Expr)>,
    j: &mut JsArena,
) -> Expr {
    let clauses = cases
        .into_iter()
        .map(|(tag, value)| {
            let ret = S::return_(value, j);
            StringClauseInfo {
                tag_type: SwitchCaseTag::String(tag),
                clause: Clause {
                    source_loc: None,
                    body: j.stmt_list(&[ret]),
                    should_break: false,
                    comment: None,
                },
            }
        })
        .collect();
    let switch = S::string_switch(scrutinee, clauses, None, j);
    iife(&[switch], j)
}

pub(crate) fn block_with_return_expr_iife(mut block: Block, expr: Expr, j: &mut JsArena) -> Expr {
    if block.is_empty() {
        return expr;
    }

    block.push(S::return_(expr, j));
    iife(&block, j)
}

pub(crate) fn is_type_object_expr(expr: Expr, j: &mut JsArena) -> Expr {
    raw_typeof_comparison(expr, BinOp::EqEqEq, "object", j)
}

pub(crate) fn int_bnot(expr: Expr, j: &mut JsArena) -> Expr {
    match int_literal(j, expr) {
        Some(value) => int_expr(!value, j),
        None => j.expr(ExprKind::JsBnot(expr)),
    }
}

/// js_exp_make.ml `interpolated_template`: fold literal values into their
/// neighbouring segments; a template left without values is a literal.
pub(crate) fn interpolated_template(
    segments: Vec<crate::string_literal::TemplateSegment>,
    values: Vec<Expr>,
    j: &mut JsArena,
) -> Expr {
    use crate::string_literal::{concat_template, template_from_semantic};
    fn literal_segment(a: &JsArena, value: Expr) -> Option<crate::string_literal::TemplateSegment> {
        if a.expr_comment(value).is_some() {
            return None;
        }
        match a.ek(value) {
            ExprKind::Str(semantic) => Some(template_from_semantic(a.text(semantic))),
            ExprKind::TemplateLiteral(segment) => Some(a.template(segment).clone()),
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
        match literal_segment(j, value) {
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
        let t = j.template_id(merged_segments.pop().expect("one segment"));
        j.expr(ExprKind::TemplateLiteral(t))
    } else {
        let segments = j.segments_id(merged_segments);
        let values = j.expr_list(&merged_values);
        j.expr(ExprKind::InterpolatedTemplate(segments, values))
    }
}
