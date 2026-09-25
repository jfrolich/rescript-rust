//! Read-only traversal of the JS IR.
//!
//! Passes that rebuild the program by value can use this to check first
//! whether the program contains anything they would change.

use super::{Block, Expression, ExpressionDesc, Statement, StatementDesc, VariableDeclaration};

/// Callbacks for [`walk_block`]. Every expression is visited before its
/// children; every variable declaration before its initializer.
pub(crate) trait Visitor<'a> {
    fn visit_expression(&mut self, _expression: &'a Expression) {}
    fn visit_declaration(&mut self, _declaration: &'a VariableDeclaration) {}
    /// Whether the walk can stop early.
    fn done(&self) -> bool {
        false
    }
}

pub(crate) fn walk_block<'a>(visitor: &mut impl Visitor<'a>, block: &'a Block) {
    for statement in block {
        if visitor.done() {
            return;
        }
        walk_statement(visitor, statement);
    }
}

fn walk_statement<'a>(visitor: &mut impl Visitor<'a>, statement: &'a Statement) {
    match &statement.desc {
        StatementDesc::Block(block) => walk_block(visitor, block),
        StatementDesc::Variable(declaration) => {
            visitor.visit_declaration(declaration);
            if let Some(value) = &declaration.value {
                walk_expression(visitor, value);
            }
        }
        StatementDesc::Exp(expression)
        | StatementDesc::Return(expression)
        | StatementDesc::Throw(expression) => walk_expression(visitor, expression),
        StatementDesc::If(cond, then_block, else_block) => {
            walk_expression(visitor, cond);
            walk_block(visitor, then_block);
            walk_block(visitor, else_block);
        }
        StatementDesc::While(_, cond, body) => {
            walk_expression(visitor, cond);
            walk_block(visitor, body);
        }
        StatementDesc::ForRange(_, init, end, _, _, body) => {
            if let Some(init) = init {
                walk_expression(visitor, init);
            }
            walk_expression(visitor, end);
            walk_block(visitor, body);
        }
        StatementDesc::ForOf(_, _, iterable, body) | StatementDesc::ForAwaitOf(_, _, iterable, body) => {
            walk_expression(visitor, iterable);
            walk_block(visitor, body);
        }
        StatementDesc::Continue(_) | StatementDesc::Break(_) | StatementDesc::Debugger => {}
        StatementDesc::IntSwitch(expression, clauses, default) => {
            walk_expression(visitor, expression);
            for (_, clause) in clauses {
                walk_block(visitor, &clause.body);
            }
            if let Some(block) = default {
                walk_block(visitor, block);
            }
        }
        StatementDesc::StringSwitch(expression, clauses, default) => {
            walk_expression(visitor, expression);
            for clause in clauses {
                walk_block(visitor, &clause.clause.body);
            }
            if let Some(block) = default {
                walk_block(visitor, block);
            }
        }
        StatementDesc::Try(body, catch, finally) => {
            walk_block(visitor, body);
            if let Some((_, block)) = catch {
                walk_block(visitor, block);
            }
            if let Some(block) = finally {
                walk_block(visitor, block);
            }
        }
    }
}

pub(crate) fn walk_expression<'a>(visitor: &mut impl Visitor<'a>, expression: &'a Expression) {
    if visitor.done() {
        return;
    }
    visitor.visit_expression(expression);
    match &expression.desc {
        ExpressionDesc::Var(_)
        | ExpressionDesc::Bool(_)
        | ExpressionDesc::Str { .. }
        | ExpressionDesc::RawJsCode(_)
        | ExpressionDesc::Number(_)
        | ExpressionDesc::Undefined { .. }
        | ExpressionDesc::Null => {}
        ExpressionDesc::Length(inner, _)
        | ExpressionDesc::IsNullOrUndefined(inner)
        | ExpressionDesc::Typeof(inner)
        | ExpressionDesc::JsNot(inner)
        | ExpressionDesc::JsBnot(inner)
        | ExpressionDesc::StaticIndex(inner, _, _)
        | ExpressionDesc::OptionalBlock(inner, _)
        | ExpressionDesc::CamlBlockTag(inner, _)
        | ExpressionDesc::Await(inner)
        | ExpressionDesc::Spread(inner)
        | ExpressionDesc::RecordRest(_, inner) => walk_expression(visitor, inner),
        ExpressionDesc::StringAppend(left, right)
        | ExpressionDesc::In(left, right)
        | ExpressionDesc::Seq(left, right)
        | ExpressionDesc::Bin(_, left, right)
        | ExpressionDesc::FlatCall(left, right)
        | ExpressionDesc::StringIndex(left, right)
        | ExpressionDesc::ArrayIndex(left, right) => {
            walk_expression(visitor, left);
            walk_expression(visitor, right);
        }
        ExpressionDesc::Cond(cond, then_, else_) => {
            walk_expression(visitor, cond);
            walk_expression(visitor, then_);
            walk_expression(visitor, else_);
        }
        ExpressionDesc::Call(func, args, _) => {
            walk_expression(visitor, func);
            for arg in args {
                walk_expression(visitor, arg);
            }
        }
        ExpressionDesc::TaggedTemplate(func, strings, values) => {
            walk_expression(visitor, func);
            for item in strings.iter().chain(values.iter()) {
                walk_expression(visitor, item);
            }
        }
        ExpressionDesc::New(ctor, args) => {
            walk_expression(visitor, ctor);
            for arg in args.iter().flatten() {
                walk_expression(visitor, arg);
            }
        }
        ExpressionDesc::Fun { body, .. } => walk_block(visitor, body),
        ExpressionDesc::Array(items, _) | ExpressionDesc::CamlBlock(items, _, _) => {
            for item in items {
                walk_expression(visitor, item);
            }
        }
        ExpressionDesc::Object(proto, props) => {
            if let Some(proto) = proto {
                walk_expression(visitor, proto);
            }
            for (_, value) in props {
                walk_expression(visitor, value);
            }
        }
    }
}
