//! JS IR pass: rewrite references to externally-shadowed globals.
//!
//! When a top-level `let`/`const` binding shadows a built-in global name
//! (e.g. `let Map = ...`), later references to the *original* global must
//! go through `globalThis.Map` instead of bare `Map`.

use std::collections::HashSet;

use crate::ident::Ident;
use crate::js_ir::printer::is_js_keyword_or_global;
use crate::js_ir::{
    Block, DepsProgram, Expression, ExpressionDesc, Statement, StatementDesc, VariableDeclaration,
};
use crate::lambda::lam_compat::LetKind;

pub(crate) fn apply_external_shadow_pass(mut deps: DepsProgram) -> DepsProgram {
    let shadowed_globals = deps
        .program
        .block
        .iter()
        .filter_map(|stmt| match &stmt.desc {
            StatementDesc::Variable(VariableDeclaration {
                ident, property, ..
            }) if is_lexical_binding_kind(*property) && should_rewrite_binding(ident) => {
                Some(ident.name().to_string())
            }
            _ => None,
        })
        .collect::<HashSet<_>>();

    if shadowed_globals.is_empty() {
        return deps;
    }

    deps.program.block = rewrite_block(&deps.program.block, &shadowed_globals);
    deps
}

pub(crate) fn is_lexical_binding_kind(property: LetKind) -> bool {
    matches!(
        property,
        LetKind::Strict | LetKind::StrictOpt | LetKind::Alias
    )
}

fn should_rewrite_binding(ident: &Ident) -> bool {
    !ident.is_global() && !is_js_keyword_or_global(ident.name())
}

fn rewrite_block(block: &Block, shadowed_globals: &HashSet<String>) -> Block {
    block
        .iter()
        .map(|stmt| rewrite_statement(stmt, shadowed_globals))
        .collect()
}

fn rewrite_statement(stmt: &Statement, shadowed_globals: &HashSet<String>) -> Statement {
    let desc = match &stmt.desc {
        StatementDesc::Block(block) => StatementDesc::Block(rewrite_block(block, shadowed_globals)),
        StatementDesc::Variable(decl) => {
            let value = decl.value.as_ref().map(|value| {
                let value = if is_lexical_binding_kind(decl.property)
                    && should_rewrite_binding(&decl.ident)
                {
                    rewrite_shadowed_global_in_expr(value, decl.ident.name())
                } else {
                    value.clone()
                };
                rewrite_global_static_index_expr(&value, shadowed_globals)
            });
            StatementDesc::Variable(VariableDeclaration {
                ident: decl.ident.clone(),
                value,
                property: decl.property,
                ident_info: decl.ident_info.clone(),
            })
        }
        StatementDesc::Exp(expr) => {
            StatementDesc::Exp(rewrite_global_static_index_expr(expr, shadowed_globals))
        }
        StatementDesc::If(cond, then_block, else_block) => StatementDesc::If(
            rewrite_global_static_index_expr(cond, shadowed_globals),
            rewrite_block(then_block, shadowed_globals),
            rewrite_block(else_block, shadowed_globals),
        ),
        StatementDesc::While(label, cond, body) => StatementDesc::While(
            label.clone(),
            rewrite_global_static_index_expr(cond, shadowed_globals),
            rewrite_block(body, shadowed_globals),
        ),
        StatementDesc::ForRange(label, init, end, id, direction, body) => {
            StatementDesc::ForRange(
                label.clone(),
                init.as_ref()
                    .map(|expr| rewrite_global_static_index_expr(expr, shadowed_globals)),
                rewrite_global_static_index_expr(end, shadowed_globals),
                id.clone(),
                *direction,
                rewrite_block(body, shadowed_globals),
            )
        }
        StatementDesc::ForOf(label, id, iterable, body) => StatementDesc::ForOf(
            label.clone(),
            id.clone(),
            rewrite_global_static_index_expr(iterable, shadowed_globals),
            rewrite_block(body, shadowed_globals),
        ),
        StatementDesc::ForAwaitOf(label, id, iterable, body) => StatementDesc::ForAwaitOf(
            label.clone(),
            id.clone(),
            rewrite_global_static_index_expr(iterable, shadowed_globals),
            rewrite_block(body, shadowed_globals),
        ),
        StatementDesc::Continue(label) => StatementDesc::Continue(label.clone()),
        StatementDesc::Break(label) => StatementDesc::Break(label.clone()),
        StatementDesc::Return(expr) => {
            StatementDesc::Return(rewrite_global_static_index_expr(expr, shadowed_globals))
        }
        StatementDesc::IntSwitch(expr, clauses, default) => StatementDesc::IntSwitch(
            rewrite_global_static_index_expr(expr, shadowed_globals),
            clauses
                .iter()
                .map(|(value, clause)| (*value, rewrite_case_clause(clause, shadowed_globals)))
                .collect(),
            default
                .as_ref()
                .map(|block| rewrite_block(block, shadowed_globals)),
        ),
        StatementDesc::StringSwitch(expr, clauses, default) => StatementDesc::StringSwitch(
            rewrite_global_static_index_expr(expr, shadowed_globals),
            clauses
                .iter()
                .map(|clause| crate::js_ir::StringClause {
                    tag_type: clause.tag_type.clone(),
                    clause: rewrite_case_clause(&clause.clause, shadowed_globals),
                })
                .collect(),
            default
                .as_ref()
                .map(|block| rewrite_block(block, shadowed_globals)),
        ),
        StatementDesc::Throw(expr) => {
            StatementDesc::Throw(rewrite_global_static_index_expr(expr, shadowed_globals))
        }
        StatementDesc::Try(body, catch, finally) => StatementDesc::Try(
            rewrite_block(body, shadowed_globals),
            catch
                .as_ref()
                .map(|(ident, block)| (ident.clone(), rewrite_block(block, shadowed_globals))),
            finally
                .as_ref()
                .map(|block| rewrite_block(block, shadowed_globals)),
        ),
        StatementDesc::Debugger => StatementDesc::Debugger,
    };

    Statement {
        desc,
        comment: stmt.comment.clone(),
    }
}

fn rewrite_case_clause(
    clause: &crate::js_ir::CaseClause,
    shadowed_globals: &HashSet<String>,
) -> crate::js_ir::CaseClause {
    crate::js_ir::CaseClause {
        body: rewrite_block(&clause.body, shadowed_globals),
        should_break: clause.should_break,
        comment: clause.comment.clone(),
    }
}

fn rewrite_shadowed_global_in_expr(expr: &Expression, name: &str) -> Expression {
    let expr = rewrite_expr_children(expr, &|child| rewrite_shadowed_global_in_expr(child, name));
    match &expr.desc {
        ExpressionDesc::Var(crate::js_ir::VIdent::Id(id))
            if id.is_global() && id.name() == name =>
        {
            global_this_field(name)
        }
        _ => expr,
    }
}

fn rewrite_global_static_index_expr(
    expr: &Expression,
    shadowed_globals: &HashSet<String>,
) -> Expression {
    let expr = rewrite_expr_children(expr, &|child| {
        rewrite_global_static_index_expr(child, shadowed_globals)
    });
    match &expr.desc {
        ExpressionDesc::StaticIndex(obj, field, pos) => match &obj.desc {
            ExpressionDesc::Var(crate::js_ir::VIdent::Id(id))
                if id.is_global() && shadowed_globals.contains(id.name()) =>
            {
                Expression::new(ExpressionDesc::StaticIndex(
                    Box::new(global_this_field(id.name())),
                    field.clone(),
                    *pos,
                ))
            }
            _ => expr,
        },
        _ => expr,
    }
}

fn rewrite_expr_children(
    expr: &Expression,
    rewrite: &impl Fn(&Expression) -> Expression,
) -> Expression {
    let desc = match &expr.desc {
        ExpressionDesc::Length(inner, kind) => {
            ExpressionDesc::Length(Box::new(rewrite(inner)), kind.clone())
        }
        ExpressionDesc::IsNullOrUndefined(inner) => {
            ExpressionDesc::IsNullOrUndefined(Box::new(rewrite(inner)))
        }
        ExpressionDesc::StringAppend(left, right) => {
            ExpressionDesc::StringAppend(Box::new(rewrite(left)), Box::new(rewrite(right)))
        }
        ExpressionDesc::Bool(value) => ExpressionDesc::Bool(*value),
        ExpressionDesc::Typeof(inner) => ExpressionDesc::Typeof(Box::new(rewrite(inner))),
        ExpressionDesc::In(left, right) => {
            ExpressionDesc::In(Box::new(rewrite(left)), Box::new(rewrite(right)))
        }
        ExpressionDesc::JsNot(inner) => ExpressionDesc::JsNot(Box::new(rewrite(inner))),
        ExpressionDesc::JsBnot(inner) => ExpressionDesc::JsBnot(Box::new(rewrite(inner))),
        ExpressionDesc::Seq(first, second) => {
            ExpressionDesc::Seq(Box::new(rewrite(first)), Box::new(rewrite(second)))
        }
        ExpressionDesc::Cond(cond, then_, else_) => ExpressionDesc::Cond(
            Box::new(rewrite(cond)),
            Box::new(rewrite(then_)),
            Box::new(rewrite(else_)),
        ),
        ExpressionDesc::Bin(op, left, right) => {
            ExpressionDesc::Bin(*op, Box::new(rewrite(left)), Box::new(rewrite(right)))
        }
        ExpressionDesc::FlatCall(func, args) => {
            ExpressionDesc::FlatCall(Box::new(rewrite(func)), Box::new(rewrite(args)))
        }
        ExpressionDesc::Call(func, args, info) => ExpressionDesc::Call(
            Box::new(rewrite(func)),
            args.iter().map(rewrite).collect(),
            info.clone(),
        ),
        ExpressionDesc::StringIndex(value, index) => {
            ExpressionDesc::StringIndex(Box::new(rewrite(value)), Box::new(rewrite(index)))
        }
        ExpressionDesc::ArrayIndex(value, index) => {
            ExpressionDesc::ArrayIndex(Box::new(rewrite(value)), Box::new(rewrite(index)))
        }
        ExpressionDesc::TaggedTemplate(func, strings, values) => ExpressionDesc::TaggedTemplate(
            Box::new(rewrite(func)),
            strings.iter().map(rewrite).collect(),
            values.iter().map(rewrite).collect(),
        ),
        ExpressionDesc::StaticIndex(obj, field, pos) => {
            ExpressionDesc::StaticIndex(Box::new(rewrite(obj)), field.clone(), *pos)
        }
        ExpressionDesc::New(ctor, args) => ExpressionDesc::New(
            Box::new(rewrite(ctor)),
            args.as_ref()
                .map(|items| items.iter().map(rewrite).collect()),
        ),
        ExpressionDesc::Var(vident) => ExpressionDesc::Var(vident.clone()),
        ExpressionDesc::Fun {
            is_method,
            params,
            body,
            env,
            return_unit,
            async_,
            directive,
        } => ExpressionDesc::Fun {
            is_method: *is_method,
            params: params.clone(),
            body: rewrite_block(body, &HashSet::new()),
            env: env.clone(),
            return_unit: *return_unit,
            async_: *async_,
            directive: directive.clone(),
        },
        ExpressionDesc::Str { delim, txt } => ExpressionDesc::Str {
            delim: *delim,
            txt: txt.clone(),
        },
        ExpressionDesc::RawJsCode(info) => ExpressionDesc::RawJsCode(info.clone()),
        ExpressionDesc::Array(items, mutable_flag) => {
            ExpressionDesc::Array(items.iter().map(rewrite).collect(), *mutable_flag)
        }
        ExpressionDesc::OptionalBlock(value, flag) => {
            ExpressionDesc::OptionalBlock(Box::new(rewrite(value)), *flag)
        }
        ExpressionDesc::CamlBlock(values, mutable_flag, tag, tag_info) => {
            ExpressionDesc::CamlBlock(
                values.iter().map(rewrite).collect(),
                *mutable_flag,
                Box::new(rewrite(tag)),
                tag_info.clone(),
            )
        }
        ExpressionDesc::CamlBlockTag(value, tag) => {
            ExpressionDesc::CamlBlockTag(Box::new(rewrite(value)), tag.clone())
        }
        ExpressionDesc::Number(number) => ExpressionDesc::Number(number.clone()),
        ExpressionDesc::Object(proto, props) => ExpressionDesc::Object(
            proto.as_ref().map(|expr| Box::new(rewrite(expr))),
            props
                .iter()
                .map(|(name, value)| (name.clone(), rewrite(value)))
                .collect(),
        ),
        ExpressionDesc::Undefined { is_unit } => ExpressionDesc::Undefined { is_unit: *is_unit },
        ExpressionDesc::Null => ExpressionDesc::Null,
        ExpressionDesc::Await(inner) => ExpressionDesc::Await(Box::new(rewrite(inner))),
        ExpressionDesc::Spread(inner) => ExpressionDesc::Spread(Box::new(rewrite(inner))),
    };

    Expression {
        desc,
        comment: expr.comment.clone(),
    }
}

fn global_this_field(name: &str) -> Expression {
    Expression::new(ExpressionDesc::StaticIndex(
        Box::new(Expression::var(Ident::create_persistent("globalThis"))),
        name.to_string(),
        None,
    ))
}
