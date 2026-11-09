//! Smart constructors for the arena JS IR (`Js_exp_make` / `Js_stmt_make`).
//!
//! [`exp`] builds expressions and [`stmt`] statements, folding like the OCaml
//! constructors. Every builder takes the arena as its last argument, so
//! nested builder calls evaluate their arguments before borrowing it:
//! `E::seq(E::var(x, j), y, j)`.

use super::arena::*;
use super::op::{BinOp, Kind, LengthObject, MutableFlag, Number};
use super::{CallInfo, ForDirection, ModuleId};
use crate::ident::Ident;
use crate::lambda::SwitchCaseTag;

/// A variable reference viewed through the arena (`J.vident`).
#[derive(Clone, Copy)]
pub enum VRef<'a> {
    Id(Ident),
    Qualified(&'a ModuleId, Option<&'a str>),
}

/// The variable `e` refers to, if it is a `Var`/`Qualified` node.
pub fn vident(a: &JsArena, e: Expr) -> Option<VRef<'_>> {
    match a.ek(e) {
        ExprKind::Var(id) => Some(VRef::Id(a.ident(id))),
        ExprKind::Qualified(q) => {
            let (module, member) = a.qual(q);
            Some(VRef::Qualified(module, member))
        }
        _ => None,
    }
}

pub fn same_vident(left: VRef<'_>, right: VRef<'_>) -> bool {
    match (left, right) {
        (VRef::Id(left_id), VRef::Id(right_id)) => left_id.same(&right_id),
        (
            VRef::Qualified(left_module, left_member),
            VRef::Qualified(right_module, right_member),
        ) => {
            left_module.id.same(&right_module.id)
                && same_vident_kind(&left_module.kind, &right_module.kind)
                && left_member == right_member
        }
        _ => false,
    }
}

/// Structural `VIdent` equality (the derived `PartialEq` of the tree IR).
pub fn vident_eq(left: VRef<'_>, right: VRef<'_>) -> bool {
    match (left, right) {
        (VRef::Id(l), VRef::Id(r)) => l == r,
        (VRef::Qualified(lm, lmem), VRef::Qualified(rm, rmem)) => lm == rm && lmem == rmem,
        _ => false,
    }
}

fn same_vident_kind(left: &Kind, right: &Kind) -> bool {
    match (left, right) {
        (Kind::Ml, Kind::Ml) | (Kind::Runtime, Kind::Runtime) => true,
        (
            Kind::External {
                name: left_name, ..
            },
            Kind::External {
                name: right_name, ..
            },
        ) => left_name == right_name,
        _ => false,
    }
}

/// The integer of an `Int` number literal.
pub fn int_of(a: &JsArena, e: Expr) -> Option<i32> {
    match a.ek(e) {
        ExprKind::Number(n) => match a.number(n) {
            Number::Int { i, .. } => Some(*i),
            _ => None,
        },
        _ => None,
    }
}

/// `Js_exp_make.string_literal_semantic`: the runtime value of a string or
/// non-interpolated template literal.
pub fn string_literal_semantic(a: &JsArena, e: Expr) -> Option<&str> {
    match a.ek(e) {
        ExprKind::Str(s) => Some(a.text(s)),
        ExprKind::TemplateLiteral(t) => Some(a.template(t).semantic()),
        _ => None,
    }
}

pub fn is_undefined(a: &JsArena, e: Expr) -> bool {
    matches!(a.ek(e), ExprKind::Undefined { .. })
}

pub(crate) fn expression_has_no_side_effects(a: &JsArena, expr: Expr) -> bool {
    let pure = |e: Expr| expression_has_no_side_effects(a, e);
    match a.ek(expr) {
        ExprKind::Undefined { .. }
        | ExprKind::Null
        | ExprKind::Bool(_)
        | ExprKind::Var(_)
        | ExprKind::Qualified(_)
        | ExprKind::Fun(_)
        | ExprKind::Number(_)
        | ExprKind::JsonLiteral(_)
        | ExprKind::Str(_)
        | ExprKind::TemplateLiteral(_) => true,
        ExprKind::InterpolatedTemplate(_, values) => a.exprs(values).iter().all(|v| pure(*v)),
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
            a.exprs(items).iter().all(|v| pure(*v))
        }
        ExprKind::Object(dup, props) => {
            dup.is_none_or(pure) && a.props(props).iter().all(|(_, value)| pure(*value))
        }
        ExprKind::Cond(test, consequent, alternate) => {
            pure(test) && pure(consequent) && pure(alternate)
        }
        ExprKind::Bin(op, left, right) => op != BinOp::Eq && pure(left) && pure(right),
        ExprKind::TaggedTemplate(tag, _, values) => {
            pure(tag) && a.exprs(values).iter().all(|v| pure(*v))
        }
        ExprKind::Call(func, args, _)
            if is_array_is_array_callee(a, func) && a.exprs(args).len() == 1 =>
        {
            a.exprs(args).iter().all(|v| pure(*v))
        }
        ExprKind::FlatCall(_, _)
        | ExprKind::Call(_, _, _)
        | ExprKind::New(_, _)
        | ExprKind::RawJsCode(_)
        | ExprKind::Await(_)
        | ExprKind::Spread(_)
        | ExprKind::RecordRest(_, _) => false,
    }
}

fn is_array_is_array_callee(a: &JsArena, expr: Expr) -> bool {
    matches!(
        a.ek(expr),
        ExprKind::StaticIndex(target, field, _)
            if a.text(field) == "isArray"
                && matches!(a.ek(target), ExprKind::Var(id) if a.ident(id).name() == "Array")
    )
}

pub(crate) fn ocaml_eq_block(a: &JsArena, left: &[Stmt], right: &[Stmt]) -> bool {
    left.len() == right.len()
        && left
            .iter()
            .zip(right)
            .all(|(l, r)| ocaml_eq_statement(a, *l, *r))
}

fn ocaml_eq_statement(a: &JsArena, left: Stmt, right: Stmt) -> bool {
    match (a.sk(left), a.sk(right)) {
        (StmtKind::Exp(l), StmtKind::Exp(r)) | (StmtKind::Return(l), StmtKind::Return(r)) => {
            ocaml_eq_expression(a, l, r)
        }
        (StmtKind::Debugger, StmtKind::Debugger) => true,
        (StmtKind::Break(l), StmtKind::Break(r)) => l.map(|s| a.text(s)) == r.map(|s| a.text(s)),
        (StmtKind::Block(l), StmtKind::Block(r)) => ocaml_eq_block(a, a.stmts(l), a.stmts(r)),
        _ => false,
    }
}

pub(crate) fn ocaml_eq_expression(a: &JsArena, left: Expr, right: Expr) -> bool {
    let eq = |l: Expr, r: Expr| ocaml_eq_expression(a, l, r);
    let eq_list = |l: ExprList, r: ExprList| {
        let (l, r) = (a.exprs(l), a.exprs(r));
        l.len() == r.len() && l.iter().zip(r).all(|(l, r)| eq(*l, *r))
    };
    match (a.ek(left), a.ek(right)) {
        (ExprKind::Null, ExprKind::Null) => true,
        (ExprKind::Undefined { is_unit: l }, ExprKind::Undefined { is_unit: r }) => l == r,
        (ExprKind::Number(l), ExprKind::Number(r)) => match (a.number(l), a.number(r)) {
            (Number::Int { i: l, .. }, Number::Int { i: r, .. }) => l == r,
            (Number::BigInt(l), Number::BigInt(r)) => l == r,
            _ => false,
        },
        (ExprKind::StringIndex(lo, li), ExprKind::StringIndex(ro, ri))
        | (ExprKind::ArrayIndex(lo, li), ExprKind::ArrayIndex(ro, ri)) => eq(lo, ro) && eq(li, ri),
        (ExprKind::Call(lf, la, _), ExprKind::Call(rf, ra, _)) => eq(lf, rf) && eq_list(la, ra),
        (ExprKind::Var(_) | ExprKind::Qualified(_), ExprKind::Var(_) | ExprKind::Qualified(_)) => {
            same_vident(
                vident(a, left).expect("a variable"),
                vident(a, right).expect("a variable"),
            )
        }
        (ExprKind::Bin(lop, ll, lr), ExprKind::Bin(rop, rl, rr)) => {
            lop == rop && eq(ll, rl) && eq(lr, rr)
        }
        (ExprKind::Str(l), ExprKind::Str(r)) => a.text(l) == a.text(r),
        (ExprKind::TemplateLiteral(l), ExprKind::TemplateLiteral(r)) => {
            a.template(l) == a.template(r)
        }
        (ExprKind::StaticIndex(lo, lf, lp), ExprKind::StaticIndex(ro, rf, rp)) => {
            a.text(lf) == a.text(rf) && lp == rp && eq(lo, ro)
        }
        (ExprKind::Seq(lf, ls), ExprKind::Seq(rf, rs)) => eq(lf, rf) && eq(ls, rs),
        // js_analyzer.ml `eq_expression`: `String_append _` is never equal.
        (ExprKind::Bool(l), ExprKind::Bool(r)) => l == r,
        (ExprKind::OptionalBlock(li, lid), ExprKind::OptionalBlock(ri, rid)) => {
            lid == rid && eq(li, ri)
        }
        (ExprKind::CamlBlock(li, lm, lt), ExprKind::CamlBlock(ri, rm, rt)) => {
            lm == rm && eq_list(li, ri) && a.tag(lt) == a.tag(rt)
        }
        _ => false,
    }
}

/// Expression builders (`Js_exp_make`).
#[allow(non_snake_case)]
pub mod exp {
    use super::*;

    pub fn new(kind: ExprKind, j: &mut JsArena) -> Expr {
        j.expr(kind)
    }

    /// An expression list (arena last, so items may be built inline).
    pub fn list(items: &[Expr], j: &mut JsArena) -> ExprList {
        j.expr_list(items)
    }

    /// An interned string (arena last, like the other builders).
    pub fn str_id(s: &str, j: &mut JsArena) -> StrId {
        j.str(s)
    }

    pub fn with_comment(kind: ExprKind, comment: &str, j: &mut JsArena) -> Expr {
        j.expr_commented(kind, comment)
    }

    pub fn bool(value: bool, j: &mut JsArena) -> Expr {
        j.expr(ExprKind::Bool(value))
    }

    pub fn var(id: Ident, j: &mut JsArena) -> Expr {
        let id = j.ident_id(id);
        j.expr(ExprKind::Var(id))
    }

    pub fn qualified(module: ModuleId, member: Option<String>, j: &mut JsArena) -> Expr {
        let q = j.qual_id(module, member);
        j.expr(ExprKind::Qualified(q))
    }

    /// `Js_exp_make.str`.
    pub fn string(txt: &str, j: &mut JsArena) -> Expr {
        let s = j.str(txt);
        j.expr(ExprKind::Str(s))
    }

    pub fn undefined(is_unit: bool, j: &mut JsArena) -> Expr {
        j.expr(ExprKind::Undefined { is_unit })
    }

    pub fn null(j: &mut JsArena) -> Expr {
        j.expr(ExprKind::Null)
    }

    pub fn number(n: Number, j: &mut JsArena) -> Expr {
        let n = j.number_id(n);
        j.expr(ExprKind::Number(n))
    }

    pub fn int(i: i32, j: &mut JsArena) -> Expr {
        number(Number::int(i), j)
    }

    pub fn array(elements: &[Expr], mutable_flag: MutableFlag, j: &mut JsArena) -> Expr {
        let l = j.expr_list(elements);
        j.expr(ExprKind::Array(l, mutable_flag))
    }

    pub fn call(func: Expr, args: &[Expr], info: CallInfo, j: &mut JsArena) -> Expr {
        let args = j.expr_list(args);
        let info = j.call_id(info);
        j.expr(ExprKind::Call(func, args, info))
    }

    pub fn static_index(target: Expr, field: &str, pos: Option<i32>, j: &mut JsArena) -> Expr {
        let field = j.str(field);
        j.expr(ExprKind::StaticIndex(target, field, FieldPos::new(pos)))
    }

    pub fn caml_block(
        items: &[Expr],
        flag: MutableFlag,
        tag: crate::lambda::TagInfo,
        j: &mut JsArena,
    ) -> Expr {
        let items = j.expr_list(items);
        let tag = j.tag_id(tag);
        j.expr(ExprKind::CamlBlock(items, flag, tag))
    }

    pub fn raw_bin(op: BinOp, left: Expr, right: Expr, j: &mut JsArena) -> Expr {
        j.expr(ExprKind::Bin(op, left, right))
    }

    pub fn seq(left: Expr, right: Expr, j: &mut JsArena) -> Expr {
        j.expr(ExprKind::Seq(left, right))
    }

    /// `e` with the given comment.
    pub fn comment(e: Expr, comment: &str, j: &mut JsArena) -> Expr {
        j.with_expr_comment(e, Some(comment))
    }

    /// `Js_exp_make.string_append`.
    pub fn string_append(left: Expr, right: Expr, j: &mut JsArena) -> Expr {
        // A string literal `a ^ b` keeping `base`'s comment and source loc.
        fn concat(base: Expr, a: &str, b: &str, keep_cold: bool, j: &mut JsArena) -> Expr {
            let joined = format!("{a}{b}");
            let s = j.str(&joined);
            let cold = if keep_cold {
                j.expr_cold(base)
            } else {
                Cold::default()
            };
            j.expr_with(ExprKind::Str(s), cold)
        }
        fn lit(j: &JsArena, e: Expr) -> Option<String> {
            string_literal_semantic(j, e).map(str::to_string)
        }

        let (left_lit, right_lit) = (lit(j, left), lit(j, right));
        match (left_lit.as_deref(), right_lit.as_deref()) {
            (Some(""), _) => return right,
            (_, Some("")) => return left,
            (Some(a), Some(b)) => return concat(left, a, b, false, j),
            _ => {}
        }

        match (j.ek(left), j.ek(right)) {
            // `(a ^ "b") ^ ("c" ^ d)` -> `(a ^ "bc") ^ d`
            (ExprKind::StringAppend(a_, b_expr), ExprKind::StringAppend(c_expr, d))
                if lit(j, b_expr).is_some() && lit(j, c_expr).is_some() =>
            {
                let (b, c) = (lit(j, b_expr).unwrap(), lit(j, c_expr).unwrap());
                let merged = concat(b_expr, &b, &c, true, j);
                let inner = string_append(a_, merged, j);
                string_append(inner, d, j)
            }
            // `"a" ^ ("b" ^ c)` -> `"ab" ^ c`
            (_, ExprKind::StringAppend(b_expr, c))
                if left_lit.is_some() && lit(j, b_expr).is_some() =>
            {
                let b = lit(j, b_expr).unwrap();
                let merged = concat(left, left_lit.as_deref().unwrap(), &b, true, j);
                string_append(merged, c, j)
            }
            // `(c ^ "b") ^ "a"` -> `c ^ "ba"`
            (ExprKind::StringAppend(c, b_expr), _)
                if lit(j, b_expr).is_some() && right_lit.is_some() =>
            {
                let b = lit(j, b_expr).unwrap();
                let merged = concat(b_expr, &b, right_lit.as_deref().unwrap(), true, j);
                string_append(c, merged, j)
            }
            _ => j.expr(ExprKind::StringAppend(left, right)),
        }
    }

    /// A `.length` expression with OCaml-aligned constant folding.
    pub fn length(target: Expr, object: LengthObject, j: &mut JsArena) -> Expr {
        match (j.ek(target), object) {
            (ExprKind::Array(items, _) | ExprKind::CamlBlock(items, _, _), LengthObject::Array)
                if expression_has_no_side_effects(j, target) =>
            {
                let n = j.exprs(items).len() as i32;
                int(n, j)
            }
            // js_exp_make.ml `string_length`: `String_literal.utf16_length`
            // of a literal's semantic value.
            (ExprKind::Str(_) | ExprKind::TemplateLiteral(_), LengthObject::String) => {
                let semantic = string_literal_semantic(j, target).expect("a string literal");
                let n = crate::string_literal::utf16_length(semantic)
                    .expect("String_literal.utf16_length: Invalid_utf8")
                    as i32;
                int(n, j)
            }
            (ExprKind::Fun(f), LengthObject::Function) => {
                let info = j.fun(f);
                let len = j.ident_slice(info.params).len() as i32;
                int(if info.is_method { len - 1 } else { len }, j)
            }
            _ => j.expr(ExprKind::Length(target, object)),
        }
    }

    /// A loose null/undefined check with OCaml-aligned constant folding.
    pub fn is_null_or_undefined(target: Expr, j: &mut JsArena) -> Expr {
        match j.ek(target) {
            ExprKind::Null | ExprKind::Undefined { .. } => bool(true, j),
            ExprKind::Number(_) | ExprKind::Array(_, _) | ExprKind::CamlBlock(_, _, _) => {
                bool(false, j)
            }
            _ => j.expr(ExprKind::IsNullOrUndefined(target)),
        }
    }

    /// A binary operation (`Js_exp_make.bin`).
    pub fn bin(op: BinOp, left: Expr, right: Expr, j: &mut JsArena) -> Expr {
        if let Some(expr) = rewrite_plus_negative_int_rhs(op, left, right, j) {
            return expr;
        }
        if let Some(expr) = rewrite_length_bin_comparison(op, left, right, j) {
            return expr;
        }
        if let Some(value) = fold_int_comparison(j, op, left, right) {
            return bool(value, j);
        }
        if let Some(value) = fold_strict_comparison(j, op, left, right) {
            return bool(value, j);
        }
        match op {
            BinOp::And => js_and(left, right, j),
            BinOp::Or => js_or(left, right, j),
            _ => raw_bin(op, left, right, j),
        }
    }

    /// A conditional expression (`Js_exp_make.econd`).
    pub fn cond(test: Expr, consequent: Expr, alternate: Expr, j: &mut JsArena) -> Expr {
        if let (ExprKind::Seq(c_effect, c_suffix), ExprKind::Seq(a_effect, a_suffix)) =
            (j.ek(consequent), j.ek(alternate))
            && is_undefined(j, c_suffix)
            && is_undefined(j, a_suffix)
        {
            let inner = cond(test, c_effect, a_effect, j);
            let undef = undefined(false, j);
            return seq(inner, undef, j);
        }

        match j.ek(test) {
            ExprKind::Bool(false) => return alternate,
            ExprKind::Number(_) if int_of(j, test) == Some(0) => return alternate,
            ExprKind::Bool(true) => return consequent,
            ExprKind::Number(_) | ExprKind::Array(_, _) | ExprKind::CamlBlock(_, _, _)
                if expression_has_no_side_effects(j, test) =>
            {
                return consequent;
            }
            _ => {}
        }

        if matches!(
            (j.ek(consequent), j.ek(alternate)),
            (ExprKind::Bool(true), ExprKind::Bool(false))
        ) {
            return test;
        }

        if ocaml_eq_expression(j, consequent, alternate) {
            if expression_has_no_side_effects(j, test) {
                return consequent;
            }
            return seq(test, consequent, j);
        }

        if let ExprKind::Cond(inner_test, inner_then, inner_else) = j.ek(consequent) {
            if ocaml_eq_expression(j, inner_else, alternate) {
                let t = js_and(test, inner_test, j);
                return cond(t, inner_then, alternate, j);
            }
            if ocaml_eq_expression(j, inner_then, alternate) {
                let n = not(inner_test, j);
                let t = js_and(test, n, j);
                return cond(t, inner_else, alternate, j);
            }
        }

        if let ExprKind::Cond(inner_test, inner_then, inner_else) = j.ek(alternate) {
            if ocaml_eq_expression(j, consequent, inner_then) {
                let t = js_or(test, inner_test, j);
                return cond(t, consequent, inner_else, j);
            }
            if ocaml_eq_expression(j, consequent, inner_else) {
                let n = not(inner_test, j);
                let t = js_or(test, n, j);
                return cond(t, consequent, inner_then, j);
            }
        }

        if let ExprKind::JsNot(inner) = j.ek(test) {
            if expression_branch_is_not_empty(j, alternate) {
                return cond(inner, alternate, consequent, j);
            }
            // A fresh `!inner` node without the original's comment.
            let negated = j.expr(ExprKind::JsNot(inner));
            return j.expr(ExprKind::Cond(negated, consequent, alternate));
        }

        if matches!(j.ek(alternate), ExprKind::Bool(false))
            && let Some(expr) = simplify_and_if_no_side_effects(test, consequent, j)
        {
            return expr;
        }

        if matches!(j.ek(consequent), ExprKind::Bool(false)) {
            let negated = not(test, j);
            if let Some(expr) = simplify_and_if_no_side_effects(negated, alternate, j) {
                return expr;
            }
        }

        j.expr(ExprKind::Cond(test, consequent, alternate))
    }

    /// A negated boolean expression (`Js_exp_make.not`).
    pub fn not(expr: Expr, j: &mut JsArena) -> Expr {
        let cold = j.expr_cold(expr);
        let no_loc = Cold {
            comment: cold.comment,
            source_loc: None,
        };
        match j.ek(expr) {
            ExprKind::Number(n) if matches!(j.number(n), Number::Int { .. }) => {
                let zero = int_of(j, expr) == Some(0);
                j.expr_with(ExprKind::Bool(zero), no_loc)
            }
            ExprKind::JsNot(inner) => inner,
            ExprKind::Bool(value) => j.expr_with(ExprKind::Bool(!value), no_loc),
            ExprKind::Bin(op, left, right)
                if matches!(
                    op,
                    BinOp::EqEqEq | BinOp::NotEqEq | BinOp::Lt | BinOp::Ge | BinOp::Le | BinOp::Gt
                ) =>
            {
                let negated = match op {
                    BinOp::EqEqEq => BinOp::NotEqEq,
                    BinOp::NotEqEq => BinOp::EqEqEq,
                    BinOp::Lt => BinOp::Ge,
                    BinOp::Ge => BinOp::Lt,
                    BinOp::Le => BinOp::Gt,
                    BinOp::Gt => BinOp::Le,
                    _ => unreachable!(),
                };
                j.expr_with(ExprKind::Bin(negated, left, right), cold)
            }
            _ => push_negation(expr, j).unwrap_or_else(|| j.expr(ExprKind::JsNot(expr))),
        }
    }

    pub(crate) fn push_negation(expr: Expr, j: &mut JsArena) -> Option<Expr> {
        let cold = j.expr_cold(expr);
        match j.ek(expr) {
            ExprKind::JsNot(inner) => Some(inner),
            ExprKind::Bool(value) => Some(j.expr_with(
                ExprKind::Bool(!value),
                Cold {
                    comment: cold.comment,
                    source_loc: None,
                },
            )),
            ExprKind::Bin(BinOp::EqEqEq, left, right) => {
                Some(j.expr_with(ExprKind::Bin(BinOp::NotEqEq, left, right), cold))
            }
            ExprKind::Bin(BinOp::NotEqEq, left, right) => {
                Some(j.expr_with(ExprKind::Bin(BinOp::EqEqEq, left, right), cold))
            }
            ExprKind::Bin(op @ (BinOp::And | BinOp::Or), left, right) => {
                let left = push_negation(left, j)?;
                let right = push_negation(right, j)?;
                let flipped = if op == BinOp::And {
                    BinOp::Or
                } else {
                    BinOp::And
                };
                Some(j.expr_with(ExprKind::Bin(flipped, left, right), cold))
            }
            _ => None,
        }
    }

    fn fold_int_comparison(j: &JsArena, op: BinOp, left: Expr, right: Expr) -> Option<bool> {
        let (Some(left_int), Some(right_int)) = (int_of(j, left), int_of(j, right)) else {
            return None;
        };
        // OCaml's Js_exp_make.int_comp compares the left literal via
        // Ext_int.int32_unsigned_to_int and the right via Int32.to_int.
        let left_int = (left_int as u32) as i64;
        let right_int = right_int as i64;
        Some(match op {
            BinOp::Lt => left_int < right_int,
            BinOp::Le => left_int <= right_int,
            BinOp::Gt => left_int > right_int,
            BinOp::Ge => left_int >= right_int,
            _ => return None,
        })
    }

    fn fold_strict_comparison(j: &JsArena, op: BinOp, left: Expr, right: Expr) -> Option<bool> {
        // OCaml's `Js_exp_make.bin` (js_exp_make.ml:623-631) routes only
        // `EqEqEq` through `triple_equal`; `NotEqEq` has no symmetric fold.
        if !matches!(op, BinOp::EqEqEq) {
            return None;
        }
        fold_strict_equality(j, left, right)
    }

    fn rewrite_length_bin_comparison(
        op: BinOp,
        left: Expr,
        right: Expr,
        j: &mut JsArena,
    ) -> Option<Expr> {
        let ExprKind::Length(target, _) = j.ek(left) else {
            return None;
        };
        if int_of(j, right) != Some(0) {
            return None;
        }
        match op {
            BinOp::Ge if expression_has_no_side_effects(j, target) => Some(bool(true, j)),
            BinOp::Gt => Some(raw_bin(BinOp::NotEqEq, left, right, j)),
            _ => None,
        }
    }

    pub(crate) fn fold_strict_equality(j: &JsArena, left: Expr, right: Expr) -> Option<bool> {
        match (j.ek(left), j.ek(right)) {
            (ExprKind::OptionalBlock(l, _), ExprKind::OptionalBlock(r, _)) => {
                return fold_strict_equality(j, l, r);
            }
            (ExprKind::Number(_), ExprKind::Number(_)) => {
                if let (Some(l), Some(r)) = (int_of(j, left), int_of(j, right)) {
                    return Some(l == r);
                }
            }
            _ => {}
        }

        // js_exp_make.ml `string_comp`: literal strings compare by semantic value.
        if let (Some(l), Some(r)) = (
            string_literal_semantic(j, left),
            string_literal_semantic(j, right),
        ) {
            return Some(l == r);
        }

        match (j.ek(left), j.ek(right)) {
            (ExprKind::Null, ExprKind::Null)
            | (ExprKind::Undefined { .. }, ExprKind::Undefined { .. }) => return Some(true),
            (ExprKind::Null, ExprKind::Undefined { .. })
            | (ExprKind::Undefined { .. }, ExprKind::Null) => return Some(false),
            (ExprKind::Undefined { .. }, ExprKind::OptionalBlock(_, _))
            | (ExprKind::OptionalBlock(_, _), ExprKind::Undefined { .. })
                if expression_has_no_side_effects(j, left)
                    && expression_has_no_side_effects(j, right) =>
            {
                return Some(false);
            }
            _ => {}
        }

        if is_nullish_literal(j, left) && is_nullish_eq_impossible_non_null_expr(j, right) {
            return Some(false);
        }
        if is_nullish_literal(j, right) && is_nullish_eq_impossible_non_null_expr(j, left) {
            return Some(false);
        }
        None
    }

    fn is_nullish_literal(j: &JsArena, expr: Expr) -> bool {
        matches!(j.ek(expr), ExprKind::Null | ExprKind::Undefined { .. })
    }

    fn is_nullish_eq_impossible_non_null_expr(j: &JsArena, expr: Expr) -> bool {
        matches!(
            j.ek(expr),
            ExprKind::Bool(_)
                | ExprKind::Number(_)
                | ExprKind::Typeof(_)
                | ExprKind::Fun(_)
                | ExprKind::Array(_, _)
                | ExprKind::CamlBlock(_, _, _)
        ) && expression_has_no_side_effects(j, expr)
    }

    fn rewrite_plus_negative_int_rhs(
        op: BinOp,
        left: Expr,
        right: Expr,
        j: &mut JsArena,
    ) -> Option<Expr> {
        if op != BinOp::Plus {
            return None;
        }
        let ExprKind::Number(n) = j.ek(right) else {
            return None;
        };
        let Number::Int { i, c } = j.number(n).clone() else {
            return None;
        };
        if i >= 0 {
            return None;
        }
        let positive_n = j.number_id(Number::Int {
            i: i.wrapping_neg(),
            c,
        });
        let positive = j.expr_with(ExprKind::Number(positive_n), j.expr_cold(right));
        Some(j.expr(ExprKind::Bin(BinOp::Minus, left, positive)))
    }

    fn expression_branch_is_not_empty(j: &JsArena, expr: Expr) -> bool {
        !(int_of(j, expr) == Some(0) || is_undefined(j, expr))
    }

    const JS_SIMPLIFY_MAX_DEPTH: usize = 10;

    pub(crate) fn js_and(left: Expr, right: Expr, j: &mut JsArena) -> Expr {
        let lv = vident(j, left);
        if let Some(lv) = lv {
            if let Some(rv) = vident(j, right)
                && same_vident(lv, rv)
            {
                return left;
            }
            if let ExprKind::Bin(BinOp::And, right_left, right_right) = j.ek(right) {
                if vident(j, right_left).is_some_and(|rv| same_vident(lv, rv)) {
                    return right;
                }
                if vident(j, right_right).is_some_and(|rv| same_vident(lv, rv)) {
                    return raw_bin(BinOp::And, right_right, right_left, j);
                }
            }
        }
        if let (
            ExprKind::Bin(BinOp::NotEqEq, left_lhs, left_rhs),
            ExprKind::Bin(BinOp::EqEqEq, right_lhs, right_rhs),
        ) = (j.ek(left), j.ek(right))
            && is_undefined(j, left_rhs)
            && matches!(j.ek(right_rhs), ExprKind::Str(_) | ExprKind::Number(_))
            && let (Some(l), Some(r)) = (var_ident(j, left_lhs), var_ident(j, right_lhs))
            && same_vident(l, r)
        {
            return right;
        }

        simplify_and_if_no_side_effects(left, right, j)
            .unwrap_or_else(|| raw_bin(BinOp::And, left, right, j))
    }

    /// `vident` for the `ExpressionDesc::Var(_)` patterns of the tree IR,
    /// which matched both local and qualified variables.
    fn var_ident(j: &JsArena, e: Expr) -> Option<VRef<'_>> {
        vident(j, e)
    }

    pub(crate) fn js_or(left: Expr, right: Expr, j: &mut JsArena) -> Expr {
        if let Some(lv) = vident(j, left) {
            if let Some(rv) = vident(j, right)
                && same_vident(lv, rv)
            {
                return left;
            }
            if let ExprKind::Bin(BinOp::Or, right_left, right_right) = j.ek(right) {
                if vident(j, right_left).is_some_and(|rv| same_vident(lv, rv)) {
                    return right;
                }
                if vident(j, right_right).is_some_and(|rv| same_vident(lv, rv)) {
                    return raw_bin(BinOp::Or, right_right, right_left, j);
                }
            }
        }

        simplify_or_if_no_side_effects(left, right, j)
            .unwrap_or_else(|| raw_bin(BinOp::Or, left, right, j))
    }

    fn simplify_and_if_no_side_effects(left: Expr, right: Expr, j: &mut JsArena) -> Option<Expr> {
        if expression_has_no_side_effects(j, left) && expression_has_no_side_effects(j, right) {
            simplify_and_with_depth(left, right, 0, true, j)
        } else {
            None
        }
    }

    fn simplify_or_if_no_side_effects(left: Expr, right: Expr, j: &mut JsArena) -> Option<Expr> {
        if expression_has_no_side_effects(j, left) && expression_has_no_side_effects(j, right) {
            simplify_or_with_depth(left, right, 0, true, j)
        } else {
            None
        }
    }

    /// `pure` is true when both operands are already known to have no side
    /// effects. Sub-expressions of pure `&&`/`||` operands, their negations
    /// and conjunctions of them are pure as well, so recursive calls on those
    /// pass it on instead of walking the operands again (for long `||`
    /// chains that walk made each step linear and whole-chain construction
    /// quadratic).
    fn simplify_and_with_depth(
        left: Expr,
        right: Expr,
        depth: usize,
        pure: bool,
        j: &mut JsArena,
    ) -> Option<Expr> {
        if depth > JS_SIMPLIFY_MAX_DEPTH {
            return None;
        }

        match (j.ek(left), j.ek(right)) {
            (ExprKind::Bool(false), _) | (_, ExprKind::Bool(false)) => {
                return Some(bool(false, j));
            }
            (ExprKind::Bool(true), _) => return Some(right),
            (_, ExprKind::Bool(true)) => return Some(left),
            _ => {}
        }

        if pure
            || (expression_has_no_side_effects(j, left) && expression_has_no_side_effects(j, right))
        {
            match (j.ek(left), j.ek(right)) {
                (ExprKind::Bin(BinOp::And, left_a, left_b), _) => {
                    let simplified_left_a =
                        simplify_and_with_depth(left_a, right, depth + 1, true, j);
                    let simplified_left_b =
                        simplify_and_with_depth(left_b, right, depth + 1, true, j);
                    return match (simplified_left_a, simplified_left_b) {
                        (None, None) => simplify_and_with_depth(left_a, left_b, depth + 1, true, j)
                            .and_then(|expr| simplify_and_force(expr, right, depth + 1, j)),
                        (Some(left_a), None) => simplify_and_force(left_a, left_b, depth + 1, j),
                        (None, Some(left_b)) => simplify_and_force(left_a, left_b, depth + 1, j),
                        (Some(left_a), Some(left_b)) => {
                            simplify_and_force(left_a, left_b, depth + 1, j)
                        }
                    };
                }
                (_, ExprKind::Bin(BinOp::And, right_a, right_b)) => {
                    let combined = raw_bin(BinOp::And, left, right_a, j);
                    return simplify_and_with_depth(combined, right_b, depth + 1, true, j);
                }
                (ExprKind::Bin(BinOp::Or, left_a, left_b), _) => {
                    let simplified_left_a =
                        simplify_and_with_depth(left_a, right, depth + 1, true, j);
                    let simplified_left_b =
                        simplify_and_with_depth(left_b, right, depth + 1, true, j);
                    return match (simplified_left_a, simplified_left_b) {
                        (Some(expr), None) if matches!(j.ek(expr), ExprKind::Bool(false)) => {
                            Some(raw_bin(BinOp::And, left_b, right, j))
                        }
                        (None, Some(expr)) if matches!(j.ek(expr), ExprKind::Bool(false)) => {
                            Some(raw_bin(BinOp::And, left_a, right, j))
                        }
                        (None, _) | (_, None) => {
                            simplify_or_with_depth(left_a, left_b, depth + 1, true, j)
                                .and_then(|expr| simplify_and_force(expr, right, depth + 1, j))
                        }
                        (Some(left_a), Some(left_b)) => {
                            simplify_or_force(left_a, left_b, depth + 1, j)
                        }
                    };
                }
                _ => {}
            }
        }

        if ocaml_eq_expression(j, left, right) {
            return Some(left);
        }

        if (pure || expression_has_no_side_effects(j, left))
            && disjunction_contains_expression(j, left, right)
        {
            return Some(right);
        }
        if (pure || expression_has_no_side_effects(j, right))
            && disjunction_contains_expression(j, right, left)
        {
            return Some(left);
        }

        if let Some(expr) = simplify_typeof_and_literal_and(left, right, j) {
            return Some(expr);
        }
        if let Some(expr) = simplify_typeof_and_literal_and(right, left, j) {
            return Some(expr);
        }

        if let Some(expr) = simplify_array_is_array_and_literal_and(left, right, j) {
            return Some(expr);
        }
        if let Some(expr) = simplify_array_is_array_and_literal_and(right, left, j) {
            return Some(expr);
        }

        if let Some(expr) = simplify_same_var_literal_and(left, right, j) {
            return Some(expr);
        }

        None
    }

    /// See `simplify_and_with_depth` for `pure`.
    fn simplify_or_with_depth(
        left: Expr,
        right: Expr,
        depth: usize,
        pure: bool,
        j: &mut JsArena,
    ) -> Option<Expr> {
        if depth > JS_SIMPLIFY_MAX_DEPTH {
            return None;
        }

        match (j.ek(left), j.ek(right)) {
            (ExprKind::Bool(true), _) | (_, ExprKind::Bool(true)) => {
                return Some(bool(true, j));
            }
            (ExprKind::Bool(false), _) => return Some(right),
            (_, ExprKind::Bool(false)) => return Some(left),
            _ => {}
        }

        if (pure || expression_has_no_side_effects(j, left))
            && conjunction_contains_expression(j, left, right)
        {
            return Some(right);
        }
        if (pure || expression_has_no_side_effects(j, right))
            && conjunction_contains_expression(j, right, left)
        {
            return Some(left);
        }

        let left_not = push_negation(left, j)?;
        let right_not = push_negation(right, j)?;
        // Negation keeps operands pure.
        let simplified = simplify_and_with_depth(left_not, right_not, depth + 1, pure, j)?;
        push_negation(simplified, j)
    }

    fn simplify_and_force(left: Expr, right: Expr, depth: usize, j: &mut JsArena) -> Option<Expr> {
        simplify_and_with_depth(left, right, depth, false, j)
            .or_else(|| Some(raw_bin(BinOp::And, left, right, j)))
    }

    fn simplify_or_force(left: Expr, right: Expr, depth: usize, j: &mut JsArena) -> Option<Expr> {
        simplify_or_with_depth(left, right, depth, false, j)
            .or_else(|| Some(raw_bin(BinOp::Or, left, right, j)))
    }

    /// A fresh variable node referring to the same variable as `var`.
    fn fresh_var(var: Expr, j: &mut JsArena) -> Expr {
        let kind = j.ek(var);
        j.expr(kind)
    }

    fn simplify_typeof_and_literal_and(
        typeof_expr: Expr,
        other: Expr,
        j: &mut JsArena,
    ) -> Option<Expr> {
        let (var_expr, type_name) = typeof_var_type_test(j, typeof_expr)?;
        let type_name = type_name.to_string();
        let type_name = type_name.as_str();
        let typeof_vident_matches = |j: &JsArena, e: Expr| {
            let (Some(v), Some(o)) = (vident(j, var_expr), vident(j, e)) else {
                return false;
            };
            same_vident(v, o)
        };

        match j.ek(other) {
            ExprKind::Var(_) | ExprKind::Qualified(_)
                if type_name == "boolean" && typeof_vident_matches(j, other) =>
            {
                let v = fresh_var(other, j);
                let t = bool(true, j);
                return Some(bin(BinOp::EqEqEq, v, t, j));
            }
            ExprKind::JsNot(inner)
                if type_name == "boolean"
                    && matches!(j.ek(inner), ExprKind::Var(_) | ExprKind::Qualified(_))
                    && typeof_vident_matches(j, inner) =>
            {
                let v = fresh_var(inner, j);
                let f = bool(false, j);
                return Some(bin(BinOp::EqEqEq, v, f, j));
            }
            _ => {}
        }

        let (op, other_var, literal) = strict_var_literal_comparison(j, other)?;
        if !typeof_vident_matches(j, other_var) {
            return None;
        }

        if op == BinOp::EqEqEq {
            if literal_matches_type_name(j, literal, type_name) {
                return Some(other);
            }
            if matches!(type_name, "boolean" | "string" | "number")
                && is_scalar_nullish_literal(j, literal)
            {
                return Some(bool(false, j));
            }
            return None;
        }

        if type_name == "boolean"
            && let ExprKind::Bool(value) = j.ek(literal)
        {
            return Some(bool(!value, j));
        }

        if matches!(type_name, "string" | "number")
            && literal_matches_type_name(j, literal, type_name)
        {
            return None;
        }

        if type_name == "object" && matches!(j.ek(literal), ExprKind::Null) {
            return None;
        }

        if matches!(type_name, "boolean" | "string" | "number" | "object")
            && is_scalar_nullish_literal(j, literal)
        {
            return Some(typeof_expr);
        }

        None
    }

    fn simplify_array_is_array_and_literal_and(
        array_test: Expr,
        other: Expr,
        j: &mut JsArena,
    ) -> Option<Expr> {
        let var_expr = array_is_array_var(j, array_test)?;
        let (op, other_var, literal) = strict_var_literal_comparison(j, other)?;
        let same = match (vident(j, var_expr), vident(j, other_var)) {
            (Some(l), Some(r)) => same_vident(l, r),
            _ => false,
        };
        if !same || !is_scalar_nullish_literal(j, literal) {
            return None;
        }
        match op {
            BinOp::EqEqEq => Some(bool(false, j)),
            BinOp::NotEqEq => Some(array_test),
            _ => None,
        }
    }

    fn simplify_same_var_literal_and(left: Expr, right: Expr, j: &mut JsArena) -> Option<Expr> {
        let (left_op, left_var, left_literal) = strict_var_literal_comparison(j, left)?;
        let (right_op, right_var, right_literal) = strict_var_literal_comparison(j, right)?;
        let same = match (vident(j, left_var), vident(j, right_var)) {
            (Some(l), Some(r)) => same_vident(l, r),
            _ => false,
        };
        if !same {
            return None;
        }

        if left_op == right_op {
            if ocaml_eq_expression(j, left_literal, right_literal) {
                return Some(left);
            }
            if matches!(left_op, BinOp::EqEqEq) {
                return Some(bool(false, j));
            }
            return None;
        }

        if ocaml_eq_expression(j, left_literal, right_literal) {
            return Some(bool(false, j));
        }

        if matches!(left_op, BinOp::EqEqEq) {
            return Some(left);
        }

        Some(right)
    }

    /// `typeof v === "name"`: the variable expression and the type name.
    fn typeof_var_type_test(j: &JsArena, expr: Expr) -> Option<(Expr, &str)> {
        let ExprKind::Bin(BinOp::EqEqEq, left, right) = j.ek(expr) else {
            return None;
        };
        let ExprKind::Typeof(value) = j.ek(left) else {
            return None;
        };
        if !matches!(j.ek(value), ExprKind::Var(_) | ExprKind::Qualified(_)) {
            return None;
        }
        let ExprKind::Str(txt) = j.ek(right) else {
            return None;
        };
        Some((value, j.text(txt)))
    }

    /// `v === lit` / `v !== lit`: the operator, variable expression and literal.
    fn strict_var_literal_comparison(j: &JsArena, expr: Expr) -> Option<(BinOp, Expr, Expr)> {
        let ExprKind::Bin(op @ (BinOp::EqEqEq | BinOp::NotEqEq), left, right) = j.ek(expr) else {
            return None;
        };
        if !matches!(j.ek(left), ExprKind::Var(_) | ExprKind::Qualified(_)) {
            return None;
        }
        if !is_scalar_nullish_literal(j, right) {
            return None;
        }
        Some((op, left, right))
    }

    fn array_is_array_var(j: &JsArena, expr: Expr) -> Option<Expr> {
        let ExprKind::Call(func, args, _) = j.ek(expr) else {
            return None;
        };
        if !is_array_is_array_callee(j, func) {
            return None;
        }
        let [arg] = j.exprs(args) else {
            return None;
        };
        matches!(j.ek(*arg), ExprKind::Var(_) | ExprKind::Qualified(_)).then_some(*arg)
    }

    fn literal_matches_type_name(j: &JsArena, literal: Expr, type_name: &str) -> bool {
        matches!(
            (j.ek(literal), type_name),
            (ExprKind::Bool(_), "boolean")
                | (ExprKind::Str(_), "string")
                | (ExprKind::Number(_), "number")
        )
    }

    fn is_scalar_nullish_literal(j: &JsArena, expr: Expr) -> bool {
        matches!(
            j.ek(expr),
            ExprKind::Bool(_)
                | ExprKind::Null
                | ExprKind::Undefined { .. }
                | ExprKind::Number(_)
                | ExprKind::Str(_)
        )
    }

    fn disjunction_contains_expression(j: &JsArena, disjunction: Expr, needle: Expr) -> bool {
        if ocaml_eq_expression(j, disjunction, needle) {
            return true;
        }
        match j.ek(disjunction) {
            ExprKind::Bin(BinOp::Or, left, right) => {
                disjunction_contains_expression(j, left, needle)
                    || disjunction_contains_expression(j, right, needle)
            }
            _ => false,
        }
    }

    pub(crate) fn conjunction_contains_expression(j: &JsArena, conjunction: Expr, needle: Expr) -> bool {
        if ocaml_eq_expression(j, conjunction, needle) {
            return true;
        }
        match j.ek(conjunction) {
            ExprKind::Bin(BinOp::And, left, right) => {
                conjunction_contains_expression(j, left, needle)
                    || conjunction_contains_expression(j, right, needle)
            }
            _ => false,
        }
    }
}

/// Statement builders (`Js_stmt_make`).
pub mod stmt {
    use super::exp as E;
    use super::*;

    /// A statement with no folding.
    pub fn new(kind: StmtKind, j: &mut JsArena) -> Stmt {
        normalize(kind, None, j)
    }

    /// A statement list (arena last, so items may be built inline).
    pub fn list(items: &[Stmt], j: &mut JsArena) -> StmtList {
        j.stmt_list(items)
    }

    /// A statement with a comment.
    pub fn with_comment(kind: StmtKind, comment: &str, j: &mut JsArena) -> Stmt {
        normalize(kind, Some(comment), j)
    }

    /// An expression statement (`Js_stmt_make.exp`).
    pub fn exp(expr: Expr, j: &mut JsArena) -> Stmt {
        match j.ek(expr) {
            ExprKind::Seq(left, right) => {
                if expression_stmt_is_trivial(j, left) {
                    return exp(right, j);
                }
                if expression_stmt_is_trivial(j, right) {
                    return exp(left, j);
                }
                let e = j.with_expr_loc(expr, None);
                j.stmt(StmtKind::Exp(e))
            }
            ExprKind::Number(_) | ExprKind::Undefined { .. } => block(&[], j),
            _ => j.stmt(StmtKind::Exp(expr)),
        }
    }

    /// A block statement using OCaml's block normalization rules.
    pub fn block(stmts: &[Stmt], j: &mut JsArena) -> Stmt {
        match stmts {
            [] => {
                let empty = j.empty_block();
                j.stmt(StmtKind::Block(empty))
            }
            [stmt] => match j.sk(*stmt) {
                StmtKind::Block(inner) => {
                    let inner = j.block_vec(inner);
                    block(&inner, j)
                }
                _ => *stmt,
            },
            _ => {
                let l = j.stmt_list(stmts);
                j.stmt(StmtKind::Block(l))
            }
        }
    }

    fn block_with_comment(stmts: &[Stmt], comment: Option<&str>, j: &mut JsArena) -> Stmt {
        match stmts {
            [stmt] => match j.sk(*stmt) {
                StmtKind::Block(inner) => {
                    let inner = j.block_vec(inner);
                    block_with_comment(&inner, comment, j)
                }
                _ => *stmt,
            },
            _ => {
                let l = j.stmt_list(stmts);
                let comment = comment.map(|c| j.str(c));
                j.stmt_with(
                    StmtKind::Block(l),
                    Cold {
                        comment,
                        source_loc: None,
                    },
                )
            }
        }
    }

    fn normalize(kind: StmtKind, comment: Option<&str>, j: &mut JsArena) -> Stmt {
        match kind {
            StmtKind::IntSwitch(e, info) if int_of(j, e).is_some() => {
                let i = int_of(j, e).unwrap();
                let info = j.int_switch(info);
                let continuation = info
                    .clauses
                    .iter()
                    .find_map(|(case, clause)| (*case == i).then_some(clause.body))
                    .or(info.default)
                    .expect("literal int switch must have a matching case or default");
                let stmts = j.block_vec(continuation);
                block_with_comment(&stmts, comment, j)
            }
            StmtKind::StringSwitch(e, info) if matches!(j.ek(e), ExprKind::Str(_)) => {
                let ExprKind::Str(txt) = j.ek(e) else {
                    unreachable!()
                };
                let txt = j.text(txt);
                let info = j.string_switch(info);
                let continuation = info
                    .clauses
                    .iter()
                    .find_map(|clause| match &clause.tag_type {
                        SwitchCaseTag::String(s) if s == txt => Some(clause.clause.body),
                        _ => None,
                    })
                    .or(info.default)
                    .expect("literal string switch must have a matching case or default");
                let stmts = j.block_vec(continuation);
                block_with_comment(&stmts, comment, j)
            }
            _ => {
                let comment = comment.map(|c| j.str(c));
                j.stmt_with(
                    kind,
                    Cold {
                        comment,
                        source_loc: None,
                    },
                )
            }
        }
    }

    /// An if statement (`Js_stmt_make.if_`).
    pub fn if_(cond: Expr, then_: &[Stmt], else_: &[Stmt], j: &mut JsArena) -> Stmt {
        simplify_if(cond, then_.to_vec(), else_.to_vec(), j)
    }

    /// An `If` node with no folding.
    pub fn raw_if(cond: Expr, then_: &[Stmt], else_: &[Stmt], j: &mut JsArena) -> Stmt {
        let then_ = j.stmt_list(then_);
        let else_ = j.stmt_list(else_);
        new(StmtKind::If(cond, then_, else_), j)
    }

    pub fn while_(label: Option<&str>, cond: Expr, body: &[Stmt], j: &mut JsArena) -> Stmt {
        let label = label.map(|l| j.str(l));
        let body = j.stmt_list(body);
        new(StmtKind::While(label, cond, body), j)
    }

    pub fn for_range(
        label: Option<&str>,
        init: Option<Expr>,
        end: Expr,
        ident: Ident,
        direction: ForDirection,
        body: &[Stmt],
        j: &mut JsArena,
    ) -> Stmt {
        let label = label.map(|l| j.str(l));
        let ident = j.ident_id(ident);
        let body = j.stmt_list(body);
        let id = j.for_range_id(ForRangeInfo {
            label,
            init,
            end,
            ident,
            direction,
            body,
        });
        new(StmtKind::ForRange(id), j)
    }

    /// `S.for_of` / `S.for_await_of`.
    pub fn for_of(
        is_await: bool,
        label: Option<&str>,
        ident: Ident,
        iterable: Expr,
        body: &[Stmt],
        j: &mut JsArena,
    ) -> Stmt {
        let label = label.map(|l| j.str(l));
        let ident = j.ident_id(ident);
        let body = j.stmt_list(body);
        let id = j.for_of_id(ForOfInfo {
            label,
            ident,
            iterable,
            body,
        });
        new(
            if is_await {
                StmtKind::ForAwaitOf(id)
            } else {
                StmtKind::ForOf(id)
            },
            j,
        )
    }

    /// js_stmt_make.ml:29-30: return statements carry no source location of
    /// their own; the returned expression keeps its location.
    pub fn return_(expr: Expr, j: &mut JsArena) -> Stmt {
        new(StmtKind::Return(expr), j)
    }

    pub fn throw(expr: Expr, j: &mut JsArena) -> Stmt {
        new(StmtKind::Throw(expr), j)
    }

    pub fn break_(label: Option<&str>, j: &mut JsArena) -> Stmt {
        let label = label.map(|l| j.str(l));
        new(StmtKind::Break(label), j)
    }

    pub fn continue_(label: Option<&str>, j: &mut JsArena) -> Stmt {
        let label = label.map(|l| j.str(l));
        new(StmtKind::Continue(label), j)
    }

    pub fn debugger(j: &mut JsArena) -> Stmt {
        new(StmtKind::Debugger, j)
    }

    pub fn variable(decl: VarDecl, j: &mut JsArena) -> Stmt {
        let v = j.var_id(decl);
        new(StmtKind::Variable(v), j)
    }

    /// `let id = value` (or `let id` without a value) with default info.
    pub fn define(
        ident: Ident,
        value: Option<Expr>,
        property: super::super::op::Property,
        j: &mut JsArena,
    ) -> Stmt {
        variable(
            VarDecl {
                ident,
                value,
                property,
                ident_info: Default::default(),
            },
            j,
        )
    }

    pub fn int_switch(
        e: Expr,
        clauses: Vec<(i32, Clause)>,
        default: Option<StmtList>,
        j: &mut JsArena,
    ) -> Stmt {
        let id = j.int_switch_id(IntSwitchInfo { clauses, default });
        new(StmtKind::IntSwitch(e, id), j)
    }

    pub fn string_switch(
        e: Expr,
        clauses: Vec<StringClauseInfo>,
        default: Option<StmtList>,
        j: &mut JsArena,
    ) -> Stmt {
        let id = j.string_switch_id(StringSwitchInfo { clauses, default });
        new(StmtKind::StringSwitch(e, id), j)
    }

    pub fn try_(
        body: &[Stmt],
        catch: Option<(Ident, &[Stmt])>,
        finally: Option<&[Stmt]>,
        j: &mut JsArena,
    ) -> Stmt {
        let body = j.stmt_list(body);
        let catch = catch.map(|(id, b)| {
            let id = j.ident_id(id);
            (id, j.stmt_list(b))
        });
        let finally = finally.map(|b| j.stmt_list(b));
        let id = j.try_id(TryInfo {
            body,
            catch,
            finally,
        });
        new(StmtKind::Try(id), j)
    }

    /// A case clause with the given body.
    pub fn clause(body: &[Stmt], should_break: bool, j: &mut JsArena) -> Clause {
        Clause {
            body: j.stmt_list(body),
            should_break,
            comment: None,
            source_loc: None,
        }
    }

    fn expression_stmt_is_trivial(j: &JsArena, expr: Expr) -> bool {
        matches!(j.ek(expr), ExprKind::Number(_) | ExprKind::Undefined { .. })
    }

    fn single_return_expr(j: &JsArena, block: &[Stmt]) -> Option<Expr> {
        match block {
            [stmt] => match j.sk(*stmt) {
                StmtKind::Return(e) => Some(e),
                _ => None,
            },
            _ => None,
        }
    }

    fn single_exp_expr(j: &JsArena, block: &[Stmt]) -> Option<Expr> {
        match block {
            [stmt] => match j.sk(*stmt) {
                StmtKind::Exp(e) => Some(e),
                _ => None,
            },
            _ => None,
        }
    }

    fn single_assignment_expr(j: &JsArena, block: &[Stmt]) -> Option<(Expr, Expr)> {
        let e = single_exp_expr(j, block)?;
        match j.ek(e) {
            ExprKind::Bin(BinOp::Eq, lhs, rhs) => Some((lhs, rhs)),
            _ => None,
        }
    }

    fn same_assignment_target(j: &JsArena, lhs: Expr, rhs: Expr) -> bool {
        match (j.ek(lhs), j.ek(rhs)) {
            (
                ExprKind::Var(_) | ExprKind::Qualified(_),
                ExprKind::Var(_) | ExprKind::Qualified(_),
            ) => vident_eq(vident(j, lhs).unwrap(), vident(j, rhs).unwrap()),
            (ExprKind::StaticIndex(lo, lf, lp), ExprKind::StaticIndex(ro, rf, rp)) => {
                j.text(lf) == j.text(rf) && lp == rp && same_assignment_target(j, lo, ro)
            }
            (ExprKind::ArrayIndex(lo, li), ExprKind::ArrayIndex(ro, ri))
            | (ExprKind::StringIndex(lo, li), ExprKind::StringIndex(ro, ri)) => {
                same_assignment_target(j, lo, ro) && same_assignment_target(j, li, ri)
            }
            _ => false,
        }
    }

    fn single_if_block(j: &JsArena, block: &[Stmt]) -> Option<(Expr, StmtList, StmtList)> {
        match block {
            [stmt] => match j.sk(*stmt) {
                StmtKind::If(c, t, e) => Some((c, t, e)),
                _ => None,
            },
            _ => None,
        }
    }

    /// Mirrors OCaml's `block_last_is_return_throw_or_continue`
    /// (js_stmt_make.ml:186-193), which inspects the literal last statement
    /// of a block and does not recurse into a trailing `Block`.
    pub(crate) fn block_last_is_terminal(j: &JsArena, block: &[Stmt]) -> bool {
        matches!(
            block.last().map(|s| j.sk(*s)),
            Some(
                StmtKind::Return(_)
                    | StmtKind::Throw(_)
                    | StmtKind::Continue(_)
                    | StmtKind::Break(_)
            )
        )
    }

    /// Direct port of OCaml's `Js_output.unnest_block` (js_output.ml:77-80):
    /// strips a single-element `[Block ...]` wrapper recursively.
    pub fn unnest_block(block: Vec<Stmt>, j: &JsArena) -> Vec<Stmt> {
        match block.as_slice() {
            [stmt] => match j.sk(*stmt) {
                StmtKind::Block(inner) => unnest_block(j.block_vec(inner), j),
                _ => block,
            },
            _ => block,
        }
    }

    fn simplify_if(cond: Expr, then_: Vec<Stmt>, else_: Vec<Stmt>, j: &mut JsArena) -> Stmt {
        match j.ek(cond) {
            ExprKind::Bool(value) => {
                return block(if value { &then_ } else { &else_ }, j);
            }
            ExprKind::JsNot(inner) if !else_.is_empty() => {
                return simplify_if(inner, else_, then_, j);
            }
            _ => {}
        }

        if then_.is_empty() {
            if else_.is_empty() {
                return exp(cond, j);
            }
            let negated = E::not(cond, j);
            return simplify_if(negated, else_, vec![], j);
        }

        if let (Some(then_ret), Some(else_ret)) =
            (single_return_expr(j, &then_), single_return_expr(j, &else_))
        {
            let c = E::cond(cond, then_ret, else_ret, j);
            return return_(c, j);
        }

        // js_stmt_make.ml:255-261: `_, [Return _]` flips to an early return.
        if let Some(else_ret) = single_return_expr(j, &else_) {
            let negated = E::not(cond, j);
            let ret = return_(else_ret, j);
            let guard = raw_if(negated, &[ret], &[], j);
            let mut stmts = Vec::with_capacity(1 + then_.len());
            stmts.push(guard);
            stmts.extend(then_);
            return block(&stmts, j);
        }

        // js_stmt_make.ml:262-265.
        if block_last_is_terminal(j, &then_) {
            let guard = raw_if(cond, &then_, &[], j);
            let mut stmts = Vec::with_capacity(1 + else_.len());
            stmts.push(guard);
            stmts.extend(else_);
            return block(&stmts, j);
        }

        if let (Some((lhs_then, rhs_then)), Some((lhs_else, rhs_else))) = (
            single_assignment_expr(j, &then_),
            single_assignment_expr(j, &else_),
        ) && same_assignment_target(j, lhs_then, lhs_else)
        {
            let c = E::cond(cond, rhs_then, rhs_else, j);
            let assign = E::bin(BinOp::Eq, lhs_then, c, j);
            return exp(assign, j);
        }

        if let (Some(then_expr), Some(else_expr)) =
            (single_exp_expr(j, &then_), single_exp_expr(j, &else_))
        {
            let c = E::cond(cond, then_expr, else_expr, j);
            return exp(c, j);
        }

        if let Some((nested_cond, nested_then, nested_else)) = single_if_block(j, &then_) {
            // OCaml's `S.if_` rule 10 (compiler/core/js_stmt_make.ml:290-292)
            // merges `if c1 { if c2 then2 else2 } else2` into
            // `if (c1 && c2) then2 else2`.
            if ocaml_eq_block(j, j.stmts(nested_else), &else_) {
                let c = E::js_and(cond, nested_cond, j);
                let (t, e) = (j.block_vec(nested_then), j.block_vec(nested_else));
                return simplify_if(c, t, e, j);
            }

            if !j.stmts(nested_then).is_empty() && ocaml_eq_block(j, j.stmts(nested_then), &else_) {
                let n = E::not(nested_cond, j);
                let c = E::js_and(cond, n, j);
                let (t, e) = (j.block_vec(nested_else), j.block_vec(nested_then));
                return simplify_if(c, t, e, j);
            }
        }

        if let Some((nested_cond, nested_then, nested_else)) = single_if_block(j, &else_) {
            if !then_.is_empty()
                && !j.stmts(nested_then).is_empty()
                && ocaml_eq_block(j, &then_, j.stmts(nested_then))
            {
                let c = E::js_or(cond, nested_cond, j);
                let e = j.block_vec(nested_else);
                return simplify_if(c, then_, e, j);
            }

            if !then_.is_empty()
                && !j.stmts(nested_else).is_empty()
                && ocaml_eq_block(j, &then_, j.stmts(nested_else))
            {
                let n = E::not(nested_cond, j);
                let c = E::js_or(cond, n, j);
                let e = j.block_vec(nested_then);
                return simplify_if(c, then_, e, j);
            }
        }

        raw_if(cond, &then_, &else_, j)
    }
}

#[cfg(test)]
#[path = "build_tests.rs"]
mod tests;
