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
    Method,
    ArrowEmpty,
}
pub(super) fn function_form(a: &JsArena, f: FunId, top: bool) -> Result<FunctionForm, Unsupported> {
    if let Some(target) = eta_target(a, f) {
        return Ok(FunctionForm::Eta(target));
    }
    let f = a.fun(f);
    if f.is_method && a.ident_slice(f.params).is_empty() {
        return Err(Unsupported("method without this parameter"));
    }
    if f.directive.is_some() {
        return Err(Unsupported("function directive"));
    }
    if top {
        return Ok(FunctionForm::Declaration);
    }
    if f.is_method {
        return Ok(FunctionForm::Method);
    }
    if let [stmt] = a.stmts(f.body) {
        match a.sk(*stmt) {
            StmtKind::Return(e) if undefined(a, e) => return Ok(FunctionForm::ArrowEmpty),
            StmtKind::Return(e) | StmtKind::Exp(e) => {
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

/// Legacy rewrites x === null || x === undefined to x == null when the
/// rendered targets match. For identical variables/qualified paths this can
/// be proven without rendering or allocating; other target comparisons remain
/// a specific fallback. Only the retained left target is met by naming.
pub(super) fn nullish_target(
    a: &JsArena,
    op: BinOp,
    l: Expr,
    r: Expr,
) -> Result<Option<Expr>, Unsupported> {
    if op != BinOp::Or {
        return Ok(None);
    }
    let (ExprKind::Bin(BinOp::EqEqEq, x, lx), ExprKind::Bin(BinOp::EqEqEq, y, ly)) =
        (a.ek(l), a.ek(r))
    else {
        return Ok(None);
    };
    if !matches!(
        (a.ek(lx), a.ek(ly)),
        (ExprKind::Null, ExprKind::Undefined { .. }) | (ExprKind::Undefined { .. }, ExprKind::Null)
    ) {
        return Ok(None);
    }
    let same = x == y
        || match (a.ek(x), a.ek(y)) {
            (ExprKind::Var(x), ExprKind::Var(y)) => a.ident(x).same(&a.ident(y)),
            (ExprKind::Qualified(x), ExprKind::Qualified(y)) => a.qual(x) == a.qual(y),
            _ => false,
        };
    if same {
        Ok(Some(x))
    } else {
        Err(Unsupported("nullish comparison target equality"))
    }
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

/// Validate block shapes before either assigning names or building AST nodes.
/// Keep shape-specific fallbacks here so naming cannot accept a block the
/// builder rejects (or reject a block the builder can emit).
pub(super) fn block_supported(
    elements: &[Expr],
    tag: &crate::lambda::TagInfo,
) -> Result<(), Unsupported> {
    use crate::lambda::TagInfo;
    let runtime = match tag {
        TagInfo::Constructor(c) if c.name != "::" => Some(&*c.runtime),
        TagInfo::RecordInlined(r) if r.fields.len() == elements.len() => match &*r.runtime {
            crate::types::VariantBlock::Tagged(t) => Some(t),
            crate::types::VariantBlock::Untagged { .. } => None,
        },
        TagInfo::PolyVar(_) if elements.is_empty() => {
            return Err(Unsupported("block literal: empty polymorphic variant"));
        }
        _ => None,
    };
    if let Some(t) = runtime
        && let crate::types::VariantLiteralTag::Float(s) = &t.tag.literal
    {
        block_float_tag(s)?;
    }
    Ok(())
}

pub(super) fn block_float_tag(s: &str) -> Result<f64, Unsupported> {
    s.parse::<f64>()
        .map_err(|_| Unsupported("block literal: float tag"))
}

/// Children in legacy print order, with their original field indices.
/// `print_caml_block` skips only literal Undefined optional fields: such a
/// node cannot contain any identifiers. The legacy free-variable scan visits
/// it, but that has no naming effect. PolyVar prints at most NAME and VAL.
/// The analysis pass separately retains the legacy scan of extra polyvar
/// elements, which can affect function-environment reservations in malformed IR.
pub(super) fn block_elements<'a>(
    a: &'a JsArena,
    elements: &'a [Expr],
    tag: &'a crate::lambda::TagInfo,
) -> impl Iterator<Item = (usize, Expr)> + 'a {
    use crate::lambda::TagInfo;
    let optional_fields = match tag {
        TagInfo::Record(r) if !r.array && r.fields.len() == elements.len() => Some(&r.fields),
        TagInfo::RecordInlined(r) if r.fields.len() == elements.len() => Some(&r.fields),
        _ => None,
    };
    elements.iter().copied().enumerate().filter(move |&(i, e)| {
        (!matches!(tag, TagInfo::PolyVar(_)) || i < 2)
            && !optional_fields.is_some_and(|fields| fields[i].1 && undefined(a, e))
    })
}

/// `print_exp_statement_of`: only unit tails discard numbers/undefined and
/// simplify sequences with a trivial side. Naming visits only the surviving
/// expression; the builder supplies statement parentheses and semicolons.
pub(super) fn tail_effect(a: &JsArena, e: Expr) -> Option<Expr> {
    let trivial = |e| matches!(a.ek(e), ExprKind::Number(_) | ExprKind::Undefined { .. });
    match a.ek(e) {
        ExprKind::Seq(l, r) if trivial(l) => tail_effect(a, r),
        ExprKind::Seq(l, r) if trivial(r) => tail_effect(a, l),
        _ if trivial(e) || omitted_expression(a, e) => None,
        _ => Some(e),
    }
}

/// Range loops name their binder, then a synthetic finish binder, then visit
/// start, finish and body. Only numbers and variable references avoid caching.
pub(super) fn finish_binding(a: &JsArena, e: Expr) -> bool {
    !matches!(
        a.ek(e),
        ExprKind::Number(_) | ExprKind::Var(_) | ExprKind::Qualified(_)
    )
}

/// Assignment meets the target before the value. Only identifiers and member
/// accesses are valid targets; codegen owns precedence and the final semicolon.
pub(super) fn assignment_target(a: &JsArena, e: Expr) -> Result<(), Unsupported> {
    match a.ek(e) {
        ExprKind::Var(_)
        | ExprKind::Qualified(_)
        | ExprKind::StaticIndex(..)
        | ExprKind::ArrayIndex(..)
        | ExprKind::Length(..)
        | ExprKind::CamlBlockTag(..) => Ok(()),
        _ => Err(Unsupported("assignment target")),
    }
}

pub(super) enum StatementChild {
    Binder(crate::ident::Ident),
    Finish(Stmt),
    Expression(Expr),
    Block(crate::js_ir::arena::StmtList),
}

/// Print-order traversal of control statements (printer::print_statement).
/// Loops share the function scope. Catch binders precede the handler, after the
/// try body. Switch tests precede cases, then default; `should_break` alone
/// controls inserted breaks, including empty cases. While has a trailing empty
/// statement; other loops do not. Throw visits exception fields in their stored
/// order and appends `Error: new Error()` only for literal extension blocks.
/// Braces, labels, parentheses and semicolons are represented by AST nodes.
pub(super) fn statement_children(
    a: &JsArena,
    s: Stmt,
    mut visit: impl FnMut(StatementChild) -> Result<(), Unsupported>,
) -> Result<(), Unsupported> {
    use StatementChild::*;
    match a.sk(s) {
        StmtKind::While(_, e, b) => {
            visit(Expression(e))?;
            visit(Block(b))?;
        }
        StmtKind::ForRange(id) => {
            let f = a.for_range(id);
            range_supported(a, f)?;
            visit(Binder(a.ident(f.ident)))?;
            if finish_binding(a, f.end) {
                visit(Finish(s))?;
            }
            if let Some(e) = f.init {
                visit(Expression(e))?;
            }
            visit(Expression(f.end))?;
            visit(Block(f.body))?;
        }
        StmtKind::ForOf(id) | StmtKind::ForAwaitOf(id) => {
            let f = a.for_of(id);
            visit(Binder(a.ident(f.ident)))?;
            visit(Expression(f.iterable))?;
            visit(Block(f.body))?;
        }
        StmtKind::Try(id) => {
            let t = a.try_info(id);
            visit(Block(t.body))?;
            if let Some((id, b)) = t.catch {
                visit(Binder(a.ident(id)))?;
                visit(Block(b))?;
            }
            if let Some(b) = t.finally {
                visit(Block(b))?;
            }
        }
        StmtKind::IntSwitch(e, id) => {
            visit(Expression(e))?;
            let t = a.int_switch(id);
            for (_, c) in &t.clauses {
                visit(Block(c.body))?;
            }
            if let Some(b) = t.default {
                visit(Block(b))?;
            }
        }
        StmtKind::StringSwitch(e, id) => {
            visit(Expression(e))?;
            let t = a.string_switch(id);
            for c in &t.clauses {
                switch_tag_supported(&c.tag_type)?;
                visit(Block(c.clause.body))?;
            }
            if let Some(b) = t.default {
                visit(Block(b))?;
            }
        }
        StmtKind::Throw(e) => visit(Expression(e))?,
        StmtKind::Break(_) | StmtKind::Continue(_) => {}
        _ => unreachable!("ordinary statements have their own traversal"),
    }
    Ok(())
}

/// Decimal bigint case keys borrow their digits. Other spellings stay on the
/// legacy path until radix normalization has reusable scratch storage.
pub(super) fn switch_tag_supported(tag: &crate::lambda::SwitchCaseTag) -> Result<(), Unsupported> {
    if let crate::lambda::SwitchCaseTag::BigInt(s) = tag {
        let digits = s.trim_start_matches(['-', '+']);
        if digits.is_empty() || !digits.bytes().all(|b| b.is_ascii_digit()) {
            return Err(Unsupported("switch bigint radix"));
        }
    }
    Ok(())
}

/// The legacy uncached header prints its initializer at precedence zero. A
/// sequence there parses as additional declarators, not a sequence initializer.
/// Keep that exceptional shape on the legacy path rather than changing tokens.
pub(super) fn range_supported(
    a: &JsArena,
    f: crate::js_ir::arena::ForRangeInfo,
) -> Result<(), Unsupported> {
    if !finish_binding(a, f.end) && f.init.is_some_and(|e| matches!(a.ek(e), ExprKind::Seq(..))) {
        return Err(Unsupported(
            "range initializer sequence without cached bound",
        ));
    }
    Ok(())
}

/// Legacy OptionalBlock(false) spells Primitive_option.some, a fixed global
/// (not a named IR identifier), followed by the operand except synthetic unit.
/// Calls supply the parentheses; no synthetic identifier enters naming.
pub(super) fn optional_argument(a: &JsArena, e: Expr) -> Option<Expr> {
    (!matches!(a.ek(e), ExprKind::Undefined { is_unit: true })).then_some(e)
}

/// Unlike logical operators, string + preserves right association: the legacy
/// printer uses Plus's right precedence 12, above its own precedence 11.
pub(super) fn string_children(a: &JsArena, e: Expr) -> Option<(Expr, Expr)> {
    match a.ek(e) {
        ExprKind::StringAppend(l, r) => Some((l, r)),
        _ => None,
    }
}

/// Traverse string leaves in printed order, without stack growth with depth.
pub(super) fn string_leaves(
    a: &JsArena,
    root: Expr,
    pending: &mut Vec<Expr>,
    mut visit: impl FnMut(Expr) -> Result<(), Unsupported>,
) -> Result<(), Unsupported> {
    pending.push(root);
    while let Some(e) = pending.pop() {
        if let Some((l, r)) = string_children(a, e) {
            pending.push(r);
            pending.push(l);
        } else {
            visit(e)?;
        }
    }
    Ok(())
}

/// Preserve-mode JSX needs a separate AST shape; runtime-mode JSX prints a
/// normal call and never drops its tag, props or key, even when they are unit.
pub(super) fn jsx_runtime(
    a: &JsArena,
    id: crate::js_ir::arena::JsxId,
    preserve: bool,
) -> Result<crate::js_ir::arena::JsxInfo, Unsupported> {
    if preserve {
        return Err(Unsupported("JSX preserve mode"));
    }
    let jsx = a.jsx(id);
    if a.props(jsx.props)
        .iter()
        .any(|(key, _)| !matches!(key, crate::js_ir::arena::PropName::Lit(_)))
    {
        return Err(Unsupported("symbol JSX key"));
    }
    Ok(jsx)
}

/// Destructuring declarations meet excluded-field binders before the rest
/// binder and source. Expression-position rest uses only synthetic binders.
pub(super) fn rest_declaration(
    a: &JsArena,
    d: &VarDecl,
) -> Option<(crate::js_ir::arena::RestId, Expr)> {
    match a.ek(d.value?) {
        ExprKind::RecordRest(fields, source) => Some((fields, source)),
        _ => None,
    }
}

/// Canonical integer property text is emitted as a numeric index by legacy.
/// Keep the newly exposed member shape separate from record-rest support.
pub(super) fn static_member_supported(name: &str) -> Result<(), Unsupported> {
    let (name, _) = member_form(name);
    if name.parse::<i64>().is_ok_and(|n| n.to_string() == name) {
        Err(Unsupported("numeric static member"))
    } else {
        Ok(())
    }
}
