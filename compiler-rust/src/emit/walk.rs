//! Shared token-shape decisions. Unsupported decisions reject the entire module.
use super::Unsupported;
use crate::js_ir::arena::{Expr, ExprKind, FunId, JsArena, Stmt, StmtKind, VarDecl};
use crate::js_ir::op::{BinOp, Number, UsedStats};
use crate::js_ir::{CallArity, CallKind};

pub(super) enum Declaration {
    Omit,
    Effect(Expr),
    Binding,
}
pub(super) fn prints_declaration(decl: &VarDecl) -> Declaration {
    match decl.ident_info.used_stats {
        UsedStats::DeadPure => Declaration::Omit,
        UsedStats::DeadNonPure => decl.value.map_or(Declaration::Omit, Declaration::Effect),
        _ => Declaration::Binding,
    }
}

pub(super) fn eta_target(a: &JsArena, f: FunId) -> Option<Expr> {
    let f = a.fun(f);
    if f.is_method || f.async_ || f.directive.is_some() {
        return None;
    }
    let [stmt] = a.stmts(f.body) else { return None };
    let StmtKind::Return(e) = a.sk(*stmt) else {
        return None;
    };
    let ExprKind::Call(callee, args, info) = a.ek(e) else {
        return None;
    };
    if !matches!(a.ek(callee), ExprKind::Var(_) | ExprKind::Qualified(_)) {
        return None;
    }
    let params = a.ident_slice(f.params);
    let args = a.exprs(args);
    if args.len() != params.len()
        || !args
            .iter()
            .zip(params)
            .all(|(arg, param)| matches!(a.ek(*arg), ExprKind::Var(id) if a.ident(id).same(param)))
    {
        return None;
    }
    let info = a.call_info(info);
    if !matches!(info.kind, CallKind::MlCall | CallKind::BuiltinRuntime)
        || info.arity != CallArity::Full
    {
        return None;
    }
    if let ExprKind::Var(id) = a.ek(callee)
        && params.iter().any(|p| p.same(&a.ident(id)))
    {
        return None;
    }
    Some(callee)
}

#[derive(Clone, Copy)]
pub(super) enum FunctionForm {
    Eta(Expr),
    Declaration,
    ArrowExpression(Expr),
    ArrowBlock,
    ArrowEmpty,
}
pub(super) fn function_form(a: &JsArena, f: FunId, top: bool) -> Result<FunctionForm, Unsupported> {
    if let Some(target) = eta_target(a, f) {
        return Ok(FunctionForm::Eta(target));
    }
    let f = a.fun(f);
    if f.is_method {
        return Err(Unsupported("method function"));
    }
    if f.directive.is_some() {
        return Err(Unsupported("function directive"));
    }
    if top {
        return Ok(FunctionForm::Declaration);
    }
    if let [stmt] = a.stmts(f.body) {
        match a.sk(*stmt) {
            StmtKind::Return(e) if undefined(a, e) => return Ok(FunctionForm::ArrowEmpty),
            StmtKind::Return(e) | StmtKind::Exp(e) => {
                // Newly reachable with scoped naming: the reference reformat
                // retains parentheses around an arrow returned by an arrow.
                // Leave that separate token-shape slice to its own change.
                if matches!(a.ek(e), ExprKind::Fun(_)) {
                    return Err(Unsupported("nested arrow expression body"));
                }
                return Ok(FunctionForm::ArrowExpression(e));
            }
            _ => {}
        }
    }
    Ok(FunctionForm::ArrowBlock)
}
pub(super) fn undefined(a: &JsArena, e: Expr) -> bool {
    matches!(a.ek(e), ExprKind::Undefined { .. })
}
pub(super) fn return_undefined(a: &JsArena, s: Stmt) -> bool {
    matches!(a.sk(s), StmtKind::Return(e) if undefined(a, e))
}
pub(super) fn function_body<'a>(a: &JsArena, body: &'a [Stmt]) -> &'a [Stmt] {
    if body.len() >= 2 && return_undefined(a, body[body.len() - 1]) {
        &body[..body.len() - 1]
    } else {
        body
    }
}
pub(super) fn omitted_expression(a: &JsArena, e: Expr) -> bool {
    matches!(
        a.ek(e),
        ExprKind::Var(_)
            | ExprKind::Qualified(_)
            | ExprKind::Str(_)
            | ExprKind::TemplateLiteral(_)
            | ExprKind::JsonLiteral(_)
    )
}
pub(super) fn else_omitted(a: &JsArena, body: &[Stmt]) -> bool {
    match body {
        [] => true,
        [s] => match a.sk(*s) {
            StmtKind::Block(b) => a.stmts(b).is_empty(),
            StmtKind::Exp(e) => matches!(a.ek(e), ExprKind::Var(_) | ExprKind::Qualified(_)),
            _ => false,
        },
        _ => false,
    }
}
pub(super) fn else_if(a: &JsArena, body: &[Stmt]) -> Option<Stmt> {
    match body {
        [s] => match a.sk(*s) {
            StmtKind::If(..) => Some(*s),
            StmtKind::Block(b) => match a.stmts(b) {
                [s] if matches!(a.sk(*s), StmtKind::If(..)) => Some(*s),
                _ => None,
            },
            _ => None,
        },
        _ => None,
    }
}
pub(super) fn arguments<'a>(a: &JsArena, args: &'a [Expr]) -> &'a [Expr] {
    match args {
        [e] if matches!(a.ek(*e), ExprKind::Undefined { is_unit: true }) => &[],
        _ => args,
    }
}
pub(super) fn negation_form(a: &JsArena, op: BinOp, left: Expr) -> bool {
    op == BinOp::Minus
        && matches!(a.ek(left), ExprKind::Number(n) if match a.number(n) {
            Number::Int { i: 0, .. } => true,
            Number::Float(f) => f.f == "0.",
            _ => false,
        })
}

// Nullish rewriting relies on structural equality. Until that comparison is
// available, don't emit a potentially different `||` tree for this shape.
pub(super) fn possible_nullish(a: &JsArena, op: BinOp, l: Expr, r: Expr) -> bool {
    op == BinOp::Or
        && [l, r]
            .iter()
            .all(|e| matches!(a.ek(*e), ExprKind::Bin(BinOp::EqEqEq, _, _)))
}
pub(super) fn member_form(name: &str) -> (&str, bool) {
    let name = name
        .strip_prefix("\\\"")
        .and_then(|s| s.strip_suffix('"'))
        .unwrap_or(name);
    let mut chars = name.chars();
    let dot = matches!(chars.next(), Some(c) if c.is_ascii_alphabetic() || c == '_' || c == '$')
        && chars.all(|c| c.is_ascii_alphanumeric() || c == '_' || c == '$');
    (name, dot)
}
