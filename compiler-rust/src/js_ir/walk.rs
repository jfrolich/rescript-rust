//! Traversals of the arena JS IR.
//!
//! [`Visitor`] walks a program read-only, so passes can check first whether
//! it contains anything they would change. [`Mapper`] rebuilds it like
//! OCaml's `Js_record_map`: the default methods map every child in field
//! order and push a new node only when a child changed, so unchanged
//! subtrees keep their handles.

use super::arena::*;

/// Callbacks for [`walk_block`]. Every expression is visited before its
/// children; every variable declaration before its initializer.
pub(crate) trait Visitor {
    fn visit_expression(&mut self, _a: &JsArena, _expression: Expr) {}
    fn visit_declaration(&mut self, _a: &JsArena, _declaration: &VarDecl) {}
    /// Called for every block before its statements.
    fn visit_block(&mut self, _a: &JsArena, _block: &[Stmt]) {}
    /// Whether the walk can stop early.
    fn done(&self) -> bool {
        false
    }
}

pub(crate) fn walk_block(visitor: &mut impl Visitor, a: &JsArena, block: &[Stmt]) {
    visitor.visit_block(a, block);
    for statement in block {
        if visitor.done() {
            return;
        }
        walk_statement(visitor, a, *statement);
    }
}

fn walk_list(visitor: &mut impl Visitor, a: &JsArena, block: StmtList) {
    walk_block(visitor, a, a.stmts(block));
}

fn walk_statement(visitor: &mut impl Visitor, a: &JsArena, statement: Stmt) {
    match a.sk(statement) {
        StmtKind::Block(block) => walk_list(visitor, a, block),
        StmtKind::Variable(declaration) => {
            let declaration = a.var(declaration);
            visitor.visit_declaration(a, declaration);
            if let Some(value) = declaration.value {
                walk_expression(visitor, a, value);
            }
        }
        StmtKind::Exp(expression) | StmtKind::Return(expression) | StmtKind::Throw(expression) => {
            walk_expression(visitor, a, expression)
        }
        StmtKind::If(cond, then_block, else_block) => {
            walk_expression(visitor, a, cond);
            walk_list(visitor, a, then_block);
            walk_list(visitor, a, else_block);
        }
        StmtKind::While(_, cond, body) => {
            walk_expression(visitor, a, cond);
            walk_list(visitor, a, body);
        }
        StmtKind::ForRange(info) => {
            let info = a.for_range(info);
            if let Some(init) = info.init {
                walk_expression(visitor, a, init);
            }
            walk_expression(visitor, a, info.end);
            walk_list(visitor, a, info.body);
        }
        StmtKind::ForOf(info) | StmtKind::ForAwaitOf(info) => {
            let info = a.for_of(info);
            walk_expression(visitor, a, info.iterable);
            walk_list(visitor, a, info.body);
        }
        StmtKind::Continue(_) | StmtKind::Break(_) | StmtKind::Debugger => {}
        StmtKind::IntSwitch(expression, info) => {
            walk_expression(visitor, a, expression);
            let info = a.int_switch(info);
            for (_, clause) in &info.clauses {
                walk_list(visitor, a, clause.body);
            }
            if let Some(block) = info.default {
                walk_list(visitor, a, block);
            }
        }
        StmtKind::StringSwitch(expression, info) => {
            walk_expression(visitor, a, expression);
            let info = a.string_switch(info);
            for clause in &info.clauses {
                walk_list(visitor, a, clause.clause.body);
            }
            if let Some(block) = info.default {
                walk_list(visitor, a, block);
            }
        }
        StmtKind::Try(info) => {
            let info = a.try_info(info);
            walk_list(visitor, a, info.body);
            if let Some((_, block)) = info.catch {
                walk_list(visitor, a, block);
            }
            if let Some(block) = info.finally {
                walk_list(visitor, a, block);
            }
        }
    }
}

pub(crate) fn walk_expression(visitor: &mut impl Visitor, a: &JsArena, expression: Expr) {
    if visitor.done() {
        return;
    }
    visitor.visit_expression(a, expression);
    match a.ek(expression) {
        ExprKind::Var(_)
        | ExprKind::Qualified(_)
        | ExprKind::Bool(_)
        | ExprKind::Str(_)
        | ExprKind::TemplateLiteral(_)
        | ExprKind::JsonLiteral(_)
        | ExprKind::RawJsCode(_)
        | ExprKind::Number(_)
        | ExprKind::Undefined { .. }
        | ExprKind::Null => {}
        ExprKind::Length(inner, _)
        | ExprKind::IsNullOrUndefined(inner)
        | ExprKind::Typeof(inner)
        | ExprKind::JsNot(inner)
        | ExprKind::JsBnot(inner)
        | ExprKind::StaticIndex(inner, _, _)
        | ExprKind::OptionalBlock(inner, _)
        | ExprKind::CamlBlockTag(inner, _)
        | ExprKind::Await(inner)
        | ExprKind::Spread(inner)
        | ExprKind::RecordRest(_, inner) => walk_expression(visitor, a, inner),
        ExprKind::StringAppend(left, right)
        | ExprKind::In(left, right)
        | ExprKind::Seq(left, right)
        | ExprKind::Bin(_, left, right)
        | ExprKind::FlatCall(left, right)
        | ExprKind::StringIndex(left, right)
        | ExprKind::ArrayIndex(left, right) => {
            walk_expression(visitor, a, left);
            walk_expression(visitor, a, right);
        }
        ExprKind::Cond(cond, then_, else_) => {
            walk_expression(visitor, a, cond);
            walk_expression(visitor, a, then_);
            walk_expression(visitor, a, else_);
        }
        ExprKind::Call(func, args, _) | ExprKind::TaggedTemplate(func, _, args) => {
            walk_expression(visitor, a, func);
            for arg in a.exprs(args) {
                walk_expression(visitor, a, *arg);
            }
        }
        ExprKind::InterpolatedTemplate(_, values) => {
            for item in a.exprs(values) {
                walk_expression(visitor, a, *item);
            }
        }
        ExprKind::New(ctor, args) => {
            walk_expression(visitor, a, ctor);
            if let Some(args) = args {
                for arg in a.exprs(args) {
                    walk_expression(visitor, a, *arg);
                }
            }
        }
        ExprKind::Fun(f) => walk_list(visitor, a, a.fun(f).body),
        ExprKind::Array(items, _) | ExprKind::CamlBlock(items, _, _) => {
            for item in a.exprs(items) {
                walk_expression(visitor, a, *item);
            }
        }
        ExprKind::Object(proto, props) => {
            if let Some(proto) = proto {
                walk_expression(visitor, a, proto);
            }
            for (_, value) in a.props(props) {
                walk_expression(visitor, a, *value);
            }
        }
    }
}

/// A rebuilding traversal (`Js_record_map`). Override a method to rewrite
/// that node kind and call the matching `map_*_children` function for the
/// default (`super#...`) behavior.
pub(crate) trait Mapper {
    fn expression(&mut self, j: &mut JsArena, e: Expr) -> Expr {
        map_expression_children(self, j, e)
    }

    fn statement(&mut self, j: &mut JsArena, s: Stmt) -> Stmt {
        map_statement_children(self, j, s)
    }

    /// Maps a block's statements; the default maps each one in place.
    fn block_items(&mut self, j: &mut JsArena, items: &[Stmt]) -> Vec<Stmt> {
        items.iter().map(|s| self.statement(j, *s)).collect()
    }

    fn block(&mut self, j: &mut JsArena, block: StmtList) -> StmtList {
        let items = j.block_vec(block);
        let mapped = self.block_items(j, &items);
        if mapped == items {
            block
        } else {
            j.stmt_list(&mapped)
        }
    }
}

/// Maps the expressions of a list, reusing the list when none changed.
pub(crate) fn map_expr_list<M: Mapper + ?Sized>(
    m: &mut M,
    j: &mut JsArena,
    list: ExprList,
) -> ExprList {
    let items = j.expr_vec(list);
    let mut changed = false;
    let mapped: Vec<Expr> = items
        .iter()
        .map(|e| {
            let n = m.expression(j, *e);
            changed |= n != *e;
            n
        })
        .collect();
    if changed { j.expr_list(&mapped) } else { list }
}

pub(crate) fn map_expression_children<M: Mapper + ?Sized>(
    m: &mut M,
    j: &mut JsArena,
    e: Expr,
) -> Expr {
    let kind = match j.ek(e) {
        ExprKind::Length(inner, o) => ExprKind::Length(m.expression(j, inner), o),
        ExprKind::IsNullOrUndefined(inner) => ExprKind::IsNullOrUndefined(m.expression(j, inner)),
        ExprKind::StringAppend(l, r) => {
            let l = m.expression(j, l);
            ExprKind::StringAppend(l, m.expression(j, r))
        }
        ExprKind::Typeof(inner) => ExprKind::Typeof(m.expression(j, inner)),
        ExprKind::In(l, r) => {
            let l = m.expression(j, l);
            ExprKind::In(l, m.expression(j, r))
        }
        ExprKind::JsNot(inner) => ExprKind::JsNot(m.expression(j, inner)),
        ExprKind::JsBnot(inner) => ExprKind::JsBnot(m.expression(j, inner)),
        ExprKind::Seq(l, r) => {
            let l = m.expression(j, l);
            ExprKind::Seq(l, m.expression(j, r))
        }
        ExprKind::Cond(t, c, a) => {
            let t = m.expression(j, t);
            let c = m.expression(j, c);
            ExprKind::Cond(t, c, m.expression(j, a))
        }
        ExprKind::Bin(op, l, r) => {
            let l = m.expression(j, l);
            ExprKind::Bin(op, l, m.expression(j, r))
        }
        ExprKind::FlatCall(l, r) => {
            let l = m.expression(j, l);
            ExprKind::FlatCall(l, m.expression(j, r))
        }
        ExprKind::Call(f, args, info) => {
            let f = m.expression(j, f);
            ExprKind::Call(f, map_expr_list(m, j, args), info)
        }
        ExprKind::StringIndex(l, r) => {
            let l = m.expression(j, l);
            ExprKind::StringIndex(l, m.expression(j, r))
        }
        ExprKind::ArrayIndex(l, r) => {
            let l = m.expression(j, l);
            ExprKind::ArrayIndex(l, m.expression(j, r))
        }
        ExprKind::TaggedTemplate(tag, strings, values) => {
            let tag = m.expression(j, tag);
            ExprKind::TaggedTemplate(tag, strings, map_expr_list(m, j, values))
        }
        ExprKind::InterpolatedTemplate(segments, values) => {
            ExprKind::InterpolatedTemplate(segments, map_expr_list(m, j, values))
        }
        ExprKind::StaticIndex(target, field, pos) => {
            ExprKind::StaticIndex(m.expression(j, target), field, pos)
        }
        ExprKind::New(target, args) => {
            let target = m.expression(j, target);
            ExprKind::New(target, args.map(|args| map_expr_list(m, j, args)))
        }
        ExprKind::Fun(f) => {
            let info = j.fun(f);
            let body = m.block(j, info.body);
            if body == info.body {
                return e;
            }
            ExprKind::Fun(j.fun_id(FunInfo { body, ..info }))
        }
        ExprKind::Array(items, flag) => ExprKind::Array(map_expr_list(m, j, items), flag),
        ExprKind::OptionalBlock(inner, flag) => {
            ExprKind::OptionalBlock(m.expression(j, inner), flag)
        }
        ExprKind::CamlBlock(items, flag, tag) => {
            ExprKind::CamlBlock(map_expr_list(m, j, items), flag, tag)
        }
        ExprKind::CamlBlockTag(inner, tag) => ExprKind::CamlBlockTag(m.expression(j, inner), tag),
        ExprKind::Object(dup, props) => {
            let dup = dup.map(|d| m.expression(j, d));
            let items = j.props(props).to_vec();
            let mut changed = false;
            let mapped: Vec<(PropName, Expr)> = items
                .iter()
                .map(|(name, value)| {
                    let n = m.expression(j, *value);
                    changed |= n != *value;
                    (*name, n)
                })
                .collect();
            let props = if changed { j.prop_list(&mapped) } else { props };
            ExprKind::Object(dup, props)
        }
        ExprKind::Await(inner) => ExprKind::Await(m.expression(j, inner)),
        ExprKind::Spread(inner) => ExprKind::Spread(m.expression(j, inner)),
        ExprKind::RecordRest(fields, source) => {
            ExprKind::RecordRest(fields, m.expression(j, source))
        }
        ExprKind::Bool(_)
        | ExprKind::Var(_)
        | ExprKind::Qualified(_)
        | ExprKind::Str(_)
        | ExprKind::TemplateLiteral(_)
        | ExprKind::JsonLiteral(_)
        | ExprKind::RawJsCode(_)
        | ExprKind::Number(_)
        | ExprKind::Undefined { .. }
        | ExprKind::Null => return e,
    };
    j.rekind_expr(e, kind)
}

fn map_clause<M: Mapper + ?Sized>(m: &mut M, j: &mut JsArena, clause: Clause) -> Clause {
    Clause {
        body: m.block(j, clause.body),
        ..clause
    }
}

pub(crate) fn map_statement_children<M: Mapper + ?Sized>(
    m: &mut M,
    j: &mut JsArena,
    s: Stmt,
) -> Stmt {
    let kind = match j.sk(s) {
        StmtKind::Block(block) => StmtKind::Block(m.block(j, block)),
        StmtKind::Variable(v) => {
            let decl = j.var(v).clone();
            let Some(value) = decl.value else {
                return s;
            };
            let new_value = m.expression(j, value);
            if new_value == value {
                return s;
            }
            StmtKind::Variable(j.var_id(VarDecl {
                value: Some(new_value),
                ..decl
            }))
        }
        StmtKind::Exp(e) => StmtKind::Exp(m.expression(j, e)),
        StmtKind::Return(e) => StmtKind::Return(m.expression(j, e)),
        StmtKind::Throw(e) => StmtKind::Throw(m.expression(j, e)),
        StmtKind::If(c, t, e) => {
            let c = m.expression(j, c);
            let t = m.block(j, t);
            StmtKind::If(c, t, m.block(j, e))
        }
        StmtKind::While(label, c, body) => {
            let c = m.expression(j, c);
            StmtKind::While(label, c, m.block(j, body))
        }
        StmtKind::ForRange(id) => {
            let info = j.for_range(id);
            let init = info.init.map(|e| m.expression(j, e));
            let end = m.expression(j, info.end);
            let body = m.block(j, info.body);
            let new = ForRangeInfo {
                init,
                end,
                body,
                ..info
            };
            if new == info {
                return s;
            }
            StmtKind::ForRange(j.for_range_id(new))
        }
        StmtKind::ForOf(id) | StmtKind::ForAwaitOf(id) => {
            let info = j.for_of(id);
            let iterable = m.expression(j, info.iterable);
            let body = m.block(j, info.body);
            let new = ForOfInfo {
                iterable,
                body,
                ..info
            };
            if new == info {
                return s;
            }
            let id = j.for_of_id(new);
            if matches!(j.sk(s), StmtKind::ForOf(_)) {
                StmtKind::ForOf(id)
            } else {
                StmtKind::ForAwaitOf(id)
            }
        }
        StmtKind::IntSwitch(test, id) => {
            let test = m.expression(j, test);
            let info = j.int_switch(id).clone();
            let clauses: Vec<(i32, Clause)> = info
                .clauses
                .iter()
                .map(|(tag, clause)| (*tag, map_clause(m, j, *clause)))
                .collect();
            let default = info.default.map(|d| m.block(j, d));
            let id = if clauses == info.clauses && default == info.default {
                id
            } else {
                j.int_switch_id(IntSwitchInfo { clauses, default })
            };
            StmtKind::IntSwitch(test, id)
        }
        StmtKind::StringSwitch(test, id) => {
            let test = m.expression(j, test);
            let info = j.string_switch(id).clone();
            let clauses: Vec<StringClauseInfo> = info
                .clauses
                .iter()
                .map(|c| StringClauseInfo {
                    tag_type: c.tag_type.clone(),
                    clause: map_clause(m, j, c.clause),
                })
                .collect();
            let default = info.default.map(|d| m.block(j, d));
            let unchanged = default == info.default
                && clauses
                    .iter()
                    .zip(&info.clauses)
                    .all(|(n, o)| n.clause == o.clause);
            let id = if unchanged {
                id
            } else {
                j.string_switch_id(StringSwitchInfo { clauses, default })
            };
            StmtKind::StringSwitch(test, id)
        }
        StmtKind::Try(id) => {
            let info = j.try_info(id);
            let body = m.block(j, info.body);
            let catch = info.catch.map(|(ident, b)| (ident, m.block(j, b)));
            let finally = info.finally.map(|b| m.block(j, b));
            let new = TryInfo {
                body,
                catch,
                finally,
            };
            if new == info {
                return s;
            }
            StmtKind::Try(j.try_id(new))
        }
        StmtKind::Continue(_) | StmtKind::Break(_) | StmtKind::Debugger => return s,
    };
    j.rekind_stmt(s, kind)
}

/// Whether `f` holds for some direct sub-expression of `e`, in field order.
/// Function bodies are not sub-expressions.
pub(crate) fn any_child(a: &JsArena, e: Expr, mut f: impl FnMut(Expr) -> bool) -> bool {
    match a.ek(e) {
        ExprKind::Length(inner, _)
        | ExprKind::IsNullOrUndefined(inner)
        | ExprKind::Typeof(inner)
        | ExprKind::JsNot(inner)
        | ExprKind::JsBnot(inner)
        | ExprKind::StaticIndex(inner, _, _)
        | ExprKind::OptionalBlock(inner, _)
        | ExprKind::CamlBlockTag(inner, _)
        | ExprKind::Await(inner)
        | ExprKind::Spread(inner)
        | ExprKind::RecordRest(_, inner) => f(inner),
        ExprKind::StringAppend(l, r)
        | ExprKind::In(l, r)
        | ExprKind::Seq(l, r)
        | ExprKind::Bin(_, l, r)
        | ExprKind::FlatCall(l, r)
        | ExprKind::StringIndex(l, r)
        | ExprKind::ArrayIndex(l, r) => f(l) || f(r),
        ExprKind::Cond(t, c, x) => f(t) || f(c) || f(x),
        ExprKind::Call(func, args, _) | ExprKind::TaggedTemplate(func, _, args) => {
            f(func) || a.exprs(args).iter().any(|e| f(*e))
        }
        ExprKind::InterpolatedTemplate(_, values) => a.exprs(values).iter().any(|e| f(*e)),
        ExprKind::New(target, args) => {
            f(target) || args.is_some_and(|args| a.exprs(args).iter().any(|e| f(*e)))
        }
        ExprKind::Array(items, _) | ExprKind::CamlBlock(items, _, _) => {
            a.exprs(items).iter().any(|e| f(*e))
        }
        ExprKind::Object(dup, props) => {
            dup.is_some_and(&mut f) || a.props(props).iter().any(|(_, v)| f(*v))
        }
        ExprKind::Fun(_)
        | ExprKind::Var(_)
        | ExprKind::Qualified(_)
        | ExprKind::Bool(_)
        | ExprKind::Str(_)
        | ExprKind::TemplateLiteral(_)
        | ExprKind::JsonLiteral(_)
        | ExprKind::RawJsCode(_)
        | ExprKind::Number(_)
        | ExprKind::Undefined { .. }
        | ExprKind::Null => false,
    }
}

/// Calls `f` on every direct sub-expression of `e`, in field order.
pub(crate) fn each_child(a: &JsArena, e: Expr, mut f: impl FnMut(Expr)) {
    any_child(a, e, |c| {
        f(c);
        false
    });
}
