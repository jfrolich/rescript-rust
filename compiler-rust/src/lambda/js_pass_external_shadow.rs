//! JS IR pass: rewrite references to externally-shadowed globals.
//!
//! When a top-level `let`/`const` binding shadows a built-in global name
//! (e.g. `let Map = ...`), later references to the *original* global must
//! go through `globalThis.Map` instead of bare `Map`.

use crate::ident::Ident;
use crate::js_ir::printer::is_js_keyword_or_global;
use crate::js_ir::{
    Block, CaseClause, DepsProgram, Expression, ExpressionDesc, Statement, StatementDesc,
    StringClause, VariableDeclaration,
};
use crate::lambda::lam_compat::LetKind;
use ahash::AHashSet as HashSet;

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

    deps.program.block = rewrite_block(std::mem::take(&mut deps.program.block), &shadowed_globals);
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

fn rewrite_block(block: Block, shadowed_globals: &HashSet<String>) -> Block {
    block
        .into_iter()
        .map(|stmt| rewrite_statement(stmt, shadowed_globals))
        .collect()
}

fn rewrite_statement(stmt: Statement, shadowed_globals: &HashSet<String>) -> Statement {
    let Statement {
        source_loc,
        desc,
        comment,
    } = stmt;
    let desc = match desc {
        StatementDesc::Block(block) => StatementDesc::Block(rewrite_block(block, shadowed_globals)),
        StatementDesc::Variable(decl) => {
            let value = decl.value.map(|value| {
                let value = if is_lexical_binding_kind(decl.property)
                    && should_rewrite_binding(&decl.ident)
                {
                    rewrite_shadowed_global_in_expr(value, decl.ident.name())
                } else {
                    value
                };
                rewrite_global_static_index_expr(value, shadowed_globals)
            });
            StatementDesc::Variable(VariableDeclaration {
                ident: decl.ident,
                value,
                property: decl.property,
                ident_info: decl.ident_info,
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
            label,
            rewrite_global_static_index_expr(cond, shadowed_globals),
            rewrite_block(body, shadowed_globals),
        ),
        StatementDesc::ForRange(label, init, end, id, direction, body) => StatementDesc::ForRange(
            label,
            init.map(|expr| Box::new(rewrite_global_static_index_expr(*expr, shadowed_globals))),
            Box::new(rewrite_global_static_index_expr(*end, shadowed_globals)),
            id,
            direction,
            rewrite_block(body, shadowed_globals),
        ),
        StatementDesc::ForOf(label, id, iterable, body) => StatementDesc::ForOf(
            label,
            id,
            Box::new(rewrite_global_static_index_expr(*iterable, shadowed_globals)),
            rewrite_block(body, shadowed_globals),
        ),
        StatementDesc::ForAwaitOf(label, id, iterable, body) => StatementDesc::ForAwaitOf(
            label,
            id,
            Box::new(rewrite_global_static_index_expr(*iterable, shadowed_globals)),
            rewrite_block(body, shadowed_globals),
        ),
        StatementDesc::Continue(label) => StatementDesc::Continue(label),
        StatementDesc::Break(label) => StatementDesc::Break(label),
        StatementDesc::Return(expr) => {
            StatementDesc::Return(rewrite_global_static_index_expr(expr, shadowed_globals))
        }
        StatementDesc::IntSwitch(expr, clauses, default) => StatementDesc::IntSwitch(
            rewrite_global_static_index_expr(expr, shadowed_globals),
            clauses
                .into_iter()
                .map(|(value, clause)| (value, rewrite_case_clause(clause, shadowed_globals)))
                .collect(),
            default.map(|block| rewrite_block(block, shadowed_globals)),
        ),
        StatementDesc::StringSwitch(expr, clauses, default) => StatementDesc::StringSwitch(
            rewrite_global_static_index_expr(expr, shadowed_globals),
            clauses
                .into_iter()
                .map(|clause| StringClause {
                    tag_type: clause.tag_type,
                    clause: rewrite_case_clause(clause.clause, shadowed_globals),
                })
                .collect(),
            default.map(|block| rewrite_block(block, shadowed_globals)),
        ),
        StatementDesc::Throw(expr) => {
            StatementDesc::Throw(rewrite_global_static_index_expr(expr, shadowed_globals))
        }
        StatementDesc::Try(body, catch, finally) => StatementDesc::Try(
            rewrite_block(body, shadowed_globals),
            catch.map(|(ident, block)| (ident, rewrite_block(block, shadowed_globals))),
            finally.map(|block| rewrite_block(block, shadowed_globals)),
        ),
        StatementDesc::Debugger => StatementDesc::Debugger,
    };

    Statement {
        source_loc,
        desc,
        comment,
    }
}

fn rewrite_case_clause(clause: CaseClause, shadowed_globals: &HashSet<String>) -> CaseClause {
    CaseClause {
        source_loc: clause.source_loc,
        body: rewrite_block(clause.body, shadowed_globals),
        should_break: clause.should_break,
        comment: clause.comment,
    }
}

fn rewrite_shadowed_global_in_expr(expr: Expression, name: &str) -> Expression {
    let mut rewrite_expr = |child| rewrite_shadowed_global_in_expr(child, name);
    let mut rewrite_function_body = |body| {
        rewrite_block_exprs(body, &mut |expr| {
            rewrite_shadowed_global_in_expr(expr, name)
        })
    };
    let expr = rewrite_expr_children(expr, &mut rewrite_expr, &mut rewrite_function_body);
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
    expr: Expression,
    shadowed_globals: &HashSet<String>,
) -> Expression {
    let mut rewrite_expr = |child| rewrite_global_static_index_expr(child, shadowed_globals);
    let mut rewrite_function_body = |body| rewrite_block(body, shadowed_globals);
    let expr = rewrite_expr_children(expr, &mut rewrite_expr, &mut rewrite_function_body);
    let Expression {
        source_loc,
        desc,
        comment,
    } = expr;
    match desc {
        ExpressionDesc::StaticIndex(obj, field, pos) => match &obj.desc {
            ExpressionDesc::Var(crate::js_ir::VIdent::Id(id))
                if id.is_global() && shadowed_globals.contains(id.name()) =>
            {
                Expression::new(ExpressionDesc::StaticIndex(
                    Box::new(global_this_field(id.name())),
                    field,
                    pos,
                ))
            }
            _ => Expression {
                source_loc,
                desc: ExpressionDesc::StaticIndex(obj, field, pos),
                comment,
            },
        },
        desc => Expression {
            source_loc,
            desc,
            comment,
        },
    }
}

fn rewrite_expr_children(
    expr: Expression,
    rewrite: &mut impl FnMut(Expression) -> Expression,
    rewrite_function_body: &mut impl FnMut(Block) -> Block,
) -> Expression {
    let Expression {
        source_loc,
        desc,
        comment,
    } = expr;
    let desc = match desc {
        ExpressionDesc::Length(inner, kind) => {
            ExpressionDesc::Length(Box::new(rewrite(*inner)), kind)
        }
        ExpressionDesc::IsNullOrUndefined(inner) => {
            ExpressionDesc::IsNullOrUndefined(Box::new(rewrite(*inner)))
        }
        ExpressionDesc::StringAppend(left, right) => {
            ExpressionDesc::StringAppend(Box::new(rewrite(*left)), Box::new(rewrite(*right)))
        }
        ExpressionDesc::Bool(value) => ExpressionDesc::Bool(value),
        ExpressionDesc::Typeof(inner) => ExpressionDesc::Typeof(Box::new(rewrite(*inner))),
        ExpressionDesc::In(left, right) => {
            ExpressionDesc::In(Box::new(rewrite(*left)), Box::new(rewrite(*right)))
        }
        ExpressionDesc::JsNot(inner) => ExpressionDesc::JsNot(Box::new(rewrite(*inner))),
        ExpressionDesc::JsBnot(inner) => ExpressionDesc::JsBnot(Box::new(rewrite(*inner))),
        ExpressionDesc::Seq(first, second) => {
            ExpressionDesc::Seq(Box::new(rewrite(*first)), Box::new(rewrite(*second)))
        }
        ExpressionDesc::Cond(cond, then_, else_) => ExpressionDesc::Cond(
            Box::new(rewrite(*cond)),
            Box::new(rewrite(*then_)),
            Box::new(rewrite(*else_)),
        ),
        ExpressionDesc::Bin(op, left, right) => {
            ExpressionDesc::Bin(op, Box::new(rewrite(*left)), Box::new(rewrite(*right)))
        }
        ExpressionDesc::FlatCall(func, args) => {
            ExpressionDesc::FlatCall(Box::new(rewrite(*func)), Box::new(rewrite(*args)))
        }
        ExpressionDesc::Call(func, args, info) => ExpressionDesc::Call(
            Box::new(rewrite(*func)),
            args.into_iter().map(rewrite).collect(),
            info,
        ),
        ExpressionDesc::StringIndex(value, index) => {
            ExpressionDesc::StringIndex(Box::new(rewrite(*value)), Box::new(rewrite(*index)))
        }
        ExpressionDesc::ArrayIndex(value, index) => {
            ExpressionDesc::ArrayIndex(Box::new(rewrite(*value)), Box::new(rewrite(*index)))
        }
        ExpressionDesc::TaggedTemplate(func, strings, values) => ExpressionDesc::TaggedTemplate(
            Box::new(rewrite(*func)),
            strings.into_iter().map(&mut *rewrite).collect(),
            values.into_iter().map(&mut *rewrite).collect(),
        ),
        ExpressionDesc::StaticIndex(obj, field, pos) => {
            ExpressionDesc::StaticIndex(Box::new(rewrite(*obj)), field, pos)
        }
        ExpressionDesc::New(ctor, args) => ExpressionDesc::New(
            Box::new(rewrite(*ctor)),
            args.map(|items| items.into_iter().map(rewrite).collect()),
        ),
        ExpressionDesc::Var(vident) => ExpressionDesc::Var(vident),
        ExpressionDesc::Fun {
            is_method,
            params,
            body,
            env,
            return_unit,
            async_,
            directive,
        } => ExpressionDesc::Fun {
            is_method,
            params,
            // Match `Js_record_map.super` as used by
            // `compiler/core/js_pass_external_shadow.ml:43-57` and 76-101:
            // function expressions recurse into their body through
            // `compiler/core/js_record_map.ml:165-168`, so global-shadow
            // rewrites remain visible inside nested functions.
            body: rewrite_function_body(body),
            env,
            return_unit,
            async_,
            directive,
        },
        ExpressionDesc::Str { delim, txt } => ExpressionDesc::Str { delim, txt },
        ExpressionDesc::RawJsCode(info) => ExpressionDesc::RawJsCode(info),
        ExpressionDesc::Array(items, mutable_flag) => {
            ExpressionDesc::Array(items.into_iter().map(rewrite).collect(), mutable_flag)
        }
        ExpressionDesc::OptionalBlock(value, flag) => {
            ExpressionDesc::OptionalBlock(Box::new(rewrite(*value)), flag)
        }
        ExpressionDesc::CamlBlock(values, mutable_flag, tag_info) => ExpressionDesc::CamlBlock(
            values.into_iter().map(&mut *rewrite).collect(),
            mutable_flag,
            tag_info,
        ),
        ExpressionDesc::CamlBlockTag(value, tag) => {
            ExpressionDesc::CamlBlockTag(Box::new(rewrite(*value)), tag)
        }
        ExpressionDesc::Number(number) => ExpressionDesc::Number(number),
        ExpressionDesc::Object(proto, props) => ExpressionDesc::Object(
            proto.map(|expr| Box::new(rewrite(*expr))),
            props
                .into_iter()
                .map(|(name, value)| (name, rewrite(value)))
                .collect(),
        ),
        ExpressionDesc::Undefined { is_unit } => ExpressionDesc::Undefined { is_unit },
        ExpressionDesc::Null => ExpressionDesc::Null,
        ExpressionDesc::Await(inner) => ExpressionDesc::Await(Box::new(rewrite(*inner))),
        ExpressionDesc::Spread(inner) => ExpressionDesc::Spread(Box::new(rewrite(*inner))),
        ExpressionDesc::RecordRest(fields, source) => {
            ExpressionDesc::RecordRest(fields, Box::new(rewrite(*source)))
        }
    };

    Expression {
        source_loc,
        desc,
        comment,
    }
}

fn rewrite_block_exprs(block: Block, rewrite: &mut impl FnMut(Expression) -> Expression) -> Block {
    block
        .into_iter()
        .map(|stmt| rewrite_statement_exprs(stmt, rewrite))
        .collect()
}

fn rewrite_case_clause_exprs(
    clause: CaseClause,
    rewrite: &mut impl FnMut(Expression) -> Expression,
) -> CaseClause {
    CaseClause {
        source_loc: clause.source_loc,
        body: rewrite_block_exprs(clause.body, rewrite),
        should_break: clause.should_break,
        comment: clause.comment,
    }
}

fn rewrite_statement_exprs(
    stmt: Statement,
    rewrite: &mut impl FnMut(Expression) -> Expression,
) -> Statement {
    let Statement {
        source_loc,
        desc,
        comment,
    } = stmt;
    let desc = match desc {
        StatementDesc::Block(block) => StatementDesc::Block(rewrite_block_exprs(block, rewrite)),
        StatementDesc::Variable(mut decl) => {
            decl.value = decl.value.map(rewrite);
            StatementDesc::Variable(decl)
        }
        StatementDesc::Exp(expr) => StatementDesc::Exp(rewrite(expr)),
        StatementDesc::If(cond, then_block, else_block) => StatementDesc::If(
            rewrite(cond),
            rewrite_block_exprs(then_block, rewrite),
            rewrite_block_exprs(else_block, rewrite),
        ),
        StatementDesc::While(label, cond, body) => {
            StatementDesc::While(label, rewrite(cond), rewrite_block_exprs(body, rewrite))
        }
        StatementDesc::ForRange(label, init, end, id, direction, body) => StatementDesc::ForRange(
            label,
            init.map(|expr| Box::new(rewrite(*expr))),
            Box::new(rewrite(*end)),
            id,
            direction,
            rewrite_block_exprs(body, rewrite),
        ),
        StatementDesc::ForOf(label, id, iterable, body) => StatementDesc::ForOf(
            label,
            id,
            Box::new(rewrite(*iterable)),
            rewrite_block_exprs(body, rewrite),
        ),
        StatementDesc::ForAwaitOf(label, id, iterable, body) => StatementDesc::ForAwaitOf(
            label,
            id,
            Box::new(rewrite(*iterable)),
            rewrite_block_exprs(body, rewrite),
        ),
        StatementDesc::Continue(label) => StatementDesc::Continue(label),
        StatementDesc::Break(label) => StatementDesc::Break(label),
        StatementDesc::Return(expr) => StatementDesc::Return(rewrite(expr)),
        StatementDesc::IntSwitch(expr, clauses, default) => StatementDesc::IntSwitch(
            rewrite(expr),
            clauses
                .into_iter()
                .map(|(value, clause)| (value, rewrite_case_clause_exprs(clause, rewrite)))
                .collect(),
            default.map(|block| rewrite_block_exprs(block, rewrite)),
        ),
        StatementDesc::StringSwitch(expr, clauses, default) => StatementDesc::StringSwitch(
            rewrite(expr),
            clauses
                .into_iter()
                .map(|clause| StringClause {
                    tag_type: clause.tag_type,
                    clause: rewrite_case_clause_exprs(clause.clause, rewrite),
                })
                .collect(),
            default.map(|block| rewrite_block_exprs(block, rewrite)),
        ),
        StatementDesc::Throw(expr) => StatementDesc::Throw(rewrite(expr)),
        StatementDesc::Try(body, catch, finally) => StatementDesc::Try(
            rewrite_block_exprs(body, rewrite),
            catch.map(|(ident, block)| (ident, rewrite_block_exprs(block, rewrite))),
            finally.map(|block| rewrite_block_exprs(block, rewrite)),
        ),
        StatementDesc::Debugger => StatementDesc::Debugger,
    };

    Statement {
        source_loc,
        desc,
        comment,
    }
}

fn global_this_field(name: &str) -> Expression {
    Expression::new(ExpressionDesc::StaticIndex(
        Box::new(Expression::var(Ident::create_persistent("globalThis"))),
        name.to_string(),
        None,
    ))
}
