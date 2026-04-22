//! JS IR pass: flatten and mark dead.
//!
//! This pass flattens nested block structures, substitutes caml block
//! projections, collapses sync component make aliases, rebinds materialized
//! local module field aliases, and marks dead code for elimination.

use std::collections::{HashMap, HashSet};

use crate::context::IdGenerator;
use crate::ident::Ident;
use crate::js_ir::op::{IdentInfo, MutableFlag, Number, UsedStats};
use crate::js_ir::{
    BinOp, Block, CaseClause, DepsProgram, Expression, ExpressionDesc, Program, Statement,
    StatementDesc, StringClause, VIdent, VariableDeclaration,
};
use crate::lambda::compat::LetKind;
use crate::lambda::TagInfo;

use super::compile::max_ident_stamp_in_block;
use super::js_exp_make::{
    direct_projection_from_pure_literal, int_literal, js_expr_no_side_effects,
};

pub(crate) fn apply_js_flatten_pass(mut deps: DepsProgram) -> DepsProgram {
    deps.program = flatten_program(deps.program);
    deps
}

pub(crate) fn apply_js_flatten_and_mark_dead_pass(mut deps: DepsProgram, jsx_preserve: bool) -> DepsProgram {
    let id_gen = IdGenerator::with_start_stamp(max_ident_stamp_in_program(&deps.program));
    deps.program = flatten_and_mark_dead_program(deps.program, &id_gen, jsx_preserve);
    deps
}

fn flatten_and_mark_dead_program(
    mut program: Program,
    id_gen: &IdGenerator,
    jsx_preserve: bool,
) -> Program {
    let mut substitution = HashMap::new();
    program.block =
        flatten_and_mark_dead_block(program.block, id_gen, &mut substitution, jsx_preserve);
    program.block = collapse_sync_component_make_aliases(program.block, &program.export_set);
    program.block = rebind_materialized_local_module_field_aliases(program.block);
    mark_dead_code(&mut program);
    program
}

fn collapse_sync_component_make_aliases(block: Block, export_set: &HashSet<Ident>) -> Block {
    let mut rewritten = Vec::with_capacity(block.len());
    let mut index = 0;

    while index < block.len() {
        let Some(current) = block.get(index) else {
            break;
        };
        let Some(next) = block.get(index + 1) else {
            rewritten.push(current.clone());
            break;
        };

        let StatementDesc::Variable(function_decl) = &current.desc else {
            rewritten.push(current.clone());
            index += 1;
            continue;
        };
        let StatementDesc::Variable(alias_decl) = &next.desc else {
            rewritten.push(current.clone());
            index += 1;
            continue;
        };

        let Some(Expression {
            desc: ExpressionDesc::Fun {
                async_, directive, ..
            },
            ..
        }) = &function_decl.value
        else {
            rewritten.push(current.clone());
            index += 1;
            continue;
        };

        if *async_
            || directive.is_some()
            || !is_make_like_binding_name(function_decl.ident.name())
            || !is_descriptive_component_binding_name(alias_decl.ident.name())
            || export_set.contains(&function_decl.ident)
            || !matches!(
                alias_decl.value.as_ref(),
                Some(Expression {
                    desc: ExpressionDesc::Var(VIdent::Id(id)),
                    ..
                }) if id.same(&function_decl.ident)
            )
            || expression_mentions_ident(
                function_decl
                    .value
                    .as_ref()
                    .expect("function value checked above"),
                &function_decl.ident,
            )
            || statements_mention_ident(&block[(index + 2)..], &function_decl.ident)
            || !export_set.contains(&alias_decl.ident)
                && !statements_mention_ident(&block[(index + 2)..], &alias_decl.ident)
        {
            rewritten.push(current.clone());
            index += 1;
            continue;
        }

        rewritten.push(Statement {
            desc: StatementDesc::Variable(VariableDeclaration {
                ident: alias_decl.ident.clone(),
                value: function_decl.value.clone(),
                property: function_decl.property,
                ident_info: function_decl.ident_info.clone(),
            }),
            comment: current.comment.clone().or_else(|| next.comment.clone()),
        });
        index += 2;
    }

    rewritten
}

fn rebind_materialized_local_module_field_aliases(block: Block) -> Block {
    let mut name_counts = HashMap::new();
    collect_transparent_block_var_name_counts(&block, &mut name_counts);
    let mut dynamic_import_bindings = HashSet::new();
    collect_transparent_block_dynamic_import_bindings(&block, &mut dynamic_import_bindings);
    rebind_materialized_local_module_field_aliases_with_counts(
        block,
        &name_counts,
        &dynamic_import_bindings,
    )
}

fn collect_transparent_block_var_name_counts(block: &Block, counts: &mut HashMap<String, usize>) {
    for stmt in block {
        match &stmt.desc {
            StatementDesc::Variable(decl) => {
                *counts
                    .entry(decl.ident.name().to_string())
                    .or_insert(0usize) += 1;
            }
            StatementDesc::Block(inner) => collect_transparent_block_var_name_counts(inner, counts),
            _ => {}
        }
    }
}

fn collect_transparent_block_dynamic_import_bindings(block: &Block, bindings: &mut HashSet<Ident>) {
    for stmt in block {
        match &stmt.desc {
            StatementDesc::Variable(decl) => {
                if decl
                    .value
                    .as_ref()
                    .is_some_and(expression_is_awaited_dynamic_import_like)
                {
                    bindings.insert(decl.ident.clone());
                }
            }
            StatementDesc::Block(inner) => {
                collect_transparent_block_dynamic_import_bindings(inner, bindings)
            }
            _ => {}
        }
    }
}

fn rebind_materialized_local_module_field_aliases_with_counts(
    mut block: Block,
    name_counts: &HashMap<String, usize>,
    dynamic_import_bindings: &HashSet<Ident>,
) -> Block {
    for stmt in &mut block {
        rebind_materialized_local_module_field_aliases_in_statement(
            stmt,
            name_counts,
            dynamic_import_bindings,
        );
    }

    for index in 0..block.len().saturating_sub(1) {
        let renamed = {
            let Some(current) = block.get(index) else {
                continue;
            };
            let Some(next) = block.get(index + 1) else {
                continue;
            };
            let StatementDesc::Variable(alias_decl) = &current.desc else {
                continue;
            };
            let Some(count) = name_counts.get(alias_decl.ident.name()) else {
                continue;
            };
            if *count <= 1 {
                continue;
            }
            let StatementDesc::Variable(module_decl) = &next.desc else {
                continue;
            };
            materialized_local_module_field_alias_name(
                alias_decl,
                module_decl,
                dynamic_import_bindings,
            )
        };

        let Some(new_name) = renamed else {
            continue;
        };

        let old_ident = match &block[index].desc {
            StatementDesc::Variable(alias_decl) => alias_decl.ident.clone(),
            _ => continue,
        };
        let new_ident = Ident::new(new_name, old_ident.stamp(), old_ident.flags());

        let (head, tail) = block.split_at_mut(index + 1);
        let StatementDesc::Variable(alias_decl) = &mut head[index].desc else {
            continue;
        };
        alias_decl.ident = new_ident.clone();
        rename_ident_in_statements(tail, &old_ident, &new_ident);
    }

    block
}

fn rebind_materialized_local_module_field_aliases_in_statement(
    stmt: &mut Statement,
    parent_counts: &HashMap<String, usize>,
    dynamic_import_bindings: &HashSet<Ident>,
) {
    match &mut stmt.desc {
        StatementDesc::Block(inner) => {
            let rewritten = rebind_materialized_local_module_field_aliases_with_counts(
                std::mem::take(inner),
                parent_counts,
                dynamic_import_bindings,
            );
            *inner = rewritten;
        }
        StatementDesc::If(_, then_block, else_block) => {
            let mut then_counts = HashMap::new();
            collect_transparent_block_var_name_counts(then_block, &mut then_counts);
            let mut else_counts = HashMap::new();
            collect_transparent_block_var_name_counts(else_block, &mut else_counts);
            *then_block = rebind_materialized_local_module_field_aliases_with_counts(
                std::mem::take(then_block),
                &then_counts,
                dynamic_import_bindings,
            );
            *else_block = rebind_materialized_local_module_field_aliases_with_counts(
                std::mem::take(else_block),
                &else_counts,
                dynamic_import_bindings,
            );
        }
        StatementDesc::While(_, body) => {
            let mut counts = HashMap::new();
            collect_transparent_block_var_name_counts(body, &mut counts);
            *body = rebind_materialized_local_module_field_aliases_with_counts(
                std::mem::take(body),
                &counts,
                dynamic_import_bindings,
            );
        }
        StatementDesc::ForRange(_, _, _, _, body) => {
            let mut counts = HashMap::new();
            collect_transparent_block_var_name_counts(body, &mut counts);
            *body = rebind_materialized_local_module_field_aliases_with_counts(
                std::mem::take(body),
                &counts,
                dynamic_import_bindings,
            );
        }
        StatementDesc::IntSwitch(_, clauses, default) => {
            for (_, clause) in clauses {
                let mut counts = HashMap::new();
                collect_transparent_block_var_name_counts(&clause.body, &mut counts);
                clause.body = rebind_materialized_local_module_field_aliases_with_counts(
                    std::mem::take(&mut clause.body),
                    &counts,
                    dynamic_import_bindings,
                );
            }
            if let Some(default) = default {
                let mut counts = HashMap::new();
                collect_transparent_block_var_name_counts(default, &mut counts);
                *default = rebind_materialized_local_module_field_aliases_with_counts(
                    std::mem::take(default),
                    &counts,
                    dynamic_import_bindings,
                );
            }
        }
        StatementDesc::StringSwitch(_, clauses, default) => {
            for clause in clauses {
                let mut counts = HashMap::new();
                collect_transparent_block_var_name_counts(&clause.clause.body, &mut counts);
                clause.clause.body = rebind_materialized_local_module_field_aliases_with_counts(
                    std::mem::take(&mut clause.clause.body),
                    &counts,
                    dynamic_import_bindings,
                );
            }
            if let Some(default) = default {
                let mut counts = HashMap::new();
                collect_transparent_block_var_name_counts(default, &mut counts);
                *default = rebind_materialized_local_module_field_aliases_with_counts(
                    std::mem::take(default),
                    &counts,
                    dynamic_import_bindings,
                );
            }
        }
        StatementDesc::Try(body, catch, finally) => {
            let mut body_counts = HashMap::new();
            collect_transparent_block_var_name_counts(body, &mut body_counts);
            *body = rebind_materialized_local_module_field_aliases_with_counts(
                std::mem::take(body),
                &body_counts,
                dynamic_import_bindings,
            );
            if let Some((_, catch_block)) = catch {
                let mut catch_counts = HashMap::new();
                collect_transparent_block_var_name_counts(catch_block, &mut catch_counts);
                *catch_block = rebind_materialized_local_module_field_aliases_with_counts(
                    std::mem::take(catch_block),
                    &catch_counts,
                    dynamic_import_bindings,
                );
            }
            if let Some(finally) = finally {
                let mut finally_counts = HashMap::new();
                collect_transparent_block_var_name_counts(finally, &mut finally_counts);
                *finally = rebind_materialized_local_module_field_aliases_with_counts(
                    std::mem::take(finally),
                    &finally_counts,
                    dynamic_import_bindings,
                );
            }
        }
        StatementDesc::Variable(_)
        | StatementDesc::Exp(_)
        | StatementDesc::Return(_)
        | StatementDesc::Throw(_)
        | StatementDesc::Debugger
        | StatementDesc::Break
        | StatementDesc::Continue => {}
    }
}

fn materialized_local_module_field_alias_name(
    alias_decl: &VariableDeclaration,
    module_decl: &VariableDeclaration,
    dynamic_import_bindings: &HashSet<Ident>,
) -> Option<String> {
    let Some(Expression {
        desc: ExpressionDesc::StaticIndex(inner, _, _),
        ..
    }) = alias_decl.value.as_ref()
    else {
        return None;
    };

    let Expression {
        desc: ExpressionDesc::Var(VIdent::Id(base_ident)),
        ..
    } = inner.as_ref()
    else {
        return None;
    };

    if !dynamic_import_bindings.contains(base_ident) {
        return None;
    }

    let Some(Expression {
        desc: ExpressionDesc::CamlBlock(items, MutableFlag::Immutable, _, TagInfo::Module(fields)),
        ..
    }) = module_decl.value.as_ref()
    else {
        return None;
    };

    fields
        .iter()
        .zip(items.iter())
        .find_map(|(field, item)| match &item.desc {
            ExpressionDesc::Var(VIdent::Id(id)) if id.same(&alias_decl.ident) => {
                Some(format!("{}_{}", module_decl.ident.name(), field))
            }
            _ => None,
        })
}

fn expression_is_awaited_dynamic_import_like(expr: &Expression) -> bool {
    match &expr.desc {
        ExpressionDesc::Await(inner) => expression_is_dynamic_import_like(inner),
        _ => false,
    }
}

fn expression_is_dynamic_import_like(expr: &Expression) -> bool {
    match &expr.desc {
        ExpressionDesc::Call(func, _, _) => match &func.desc {
            ExpressionDesc::Var(VIdent::Id(id)) => id.name() == "import",
            ExpressionDesc::StaticIndex(target, field, _) => {
                field == "then" && expression_is_dynamic_import_like(target)
            }
            _ => false,
        },
        _ => false,
    }
}

fn rename_ident_in_statements(stmts: &mut [Statement], from: &Ident, to: &Ident) {
    for stmt in stmts {
        rename_ident_in_statement(stmt, from, to);
    }
}

fn rename_ident_in_statement(stmt: &mut Statement, from: &Ident, to: &Ident) {
    match &mut stmt.desc {
        StatementDesc::Block(block) => rename_ident_in_statements(block, from, to),
        StatementDesc::Variable(VariableDeclaration { ident, value, .. }) => {
            if ident.same(from) {
                *ident = to.clone();
            }
            if let Some(value) = value {
                rename_ident_in_expression(value, from, to);
            }
        }
        StatementDesc::Exp(expr) | StatementDesc::Return(expr) | StatementDesc::Throw(expr) => {
            rename_ident_in_expression(expr, from, to);
        }
        StatementDesc::If(cond, then_block, else_block) => {
            rename_ident_in_expression(cond, from, to);
            rename_ident_in_statements(then_block, from, to);
            rename_ident_in_statements(else_block, from, to);
        }
        StatementDesc::While(cond, body) => {
            rename_ident_in_expression(cond, from, to);
            rename_ident_in_statements(body, from, to);
        }
        StatementDesc::ForRange(start, finish, ident, _, body) => {
            if let Some(start) = start {
                rename_ident_in_expression(start, from, to);
            }
            rename_ident_in_expression(finish, from, to);
            if ident.same(from) {
                *ident = to.clone();
            }
            rename_ident_in_statements(body, from, to);
        }
        StatementDesc::IntSwitch(test, clauses, default) => {
            rename_ident_in_expression(test, from, to);
            for (_, clause) in clauses {
                rename_ident_in_statements(&mut clause.body, from, to);
            }
            if let Some(default) = default {
                rename_ident_in_statements(default, from, to);
            }
        }
        StatementDesc::StringSwitch(test, clauses, default) => {
            rename_ident_in_expression(test, from, to);
            for clause in clauses {
                rename_ident_in_statements(&mut clause.clause.body, from, to);
            }
            if let Some(default) = default {
                rename_ident_in_statements(default, from, to);
            }
        }
        StatementDesc::Try(body, catch, finally) => {
            rename_ident_in_statements(body, from, to);
            if let Some((catch_ident, catch_block)) = catch {
                if catch_ident.same(from) {
                    *catch_ident = to.clone();
                }
                rename_ident_in_statements(catch_block, from, to);
            }
            if let Some(finally) = finally {
                rename_ident_in_statements(finally, from, to);
            }
        }
        StatementDesc::Debugger | StatementDesc::Break | StatementDesc::Continue => {}
    }
}

fn rename_ident_in_expression(expr: &mut Expression, from: &Ident, to: &Ident) {
    match &mut expr.desc {
        ExpressionDesc::Var(VIdent::Id(id)) => {
            if id.same(from) {
                *id = to.clone();
            }
        }
        ExpressionDesc::Var(VIdent::Qualified(_, _))
        | ExpressionDesc::Bool(_)
        | ExpressionDesc::Str { .. }
        | ExpressionDesc::Number(_)
        | ExpressionDesc::Undefined { .. }
        | ExpressionDesc::Null
        | ExpressionDesc::RawJsCode(_) => {}
        ExpressionDesc::Length(inner, _)
        | ExpressionDesc::IsNullOrUndefined(inner)
        | ExpressionDesc::Typeof(inner)
        | ExpressionDesc::JsNot(inner)
        | ExpressionDesc::JsBnot(inner)
        | ExpressionDesc::Spread(inner)
        | ExpressionDesc::Await(inner)
        | ExpressionDesc::OptionalBlock(inner, _)
        | ExpressionDesc::StaticIndex(inner, _, _)
        | ExpressionDesc::CamlBlockTag(inner, _)
        | ExpressionDesc::New(inner, None) => rename_ident_in_expression(inner, from, to),
        ExpressionDesc::In(left, right)
        | ExpressionDesc::StringAppend(left, right)
        | ExpressionDesc::Seq(left, right)
        | ExpressionDesc::Bin(_, left, right)
        | ExpressionDesc::FlatCall(left, right)
        | ExpressionDesc::StringIndex(left, right)
        | ExpressionDesc::ArrayIndex(left, right) => {
            rename_ident_in_expression(left, from, to);
            rename_ident_in_expression(right, from, to);
        }
        ExpressionDesc::Cond(test, consequent, alternate) => {
            rename_ident_in_expression(test, from, to);
            rename_ident_in_expression(consequent, from, to);
            rename_ident_in_expression(alternate, from, to);
        }
        ExpressionDesc::Call(func, args, _)
        | ExpressionDesc::New(func, Some(args))
        | ExpressionDesc::TaggedTemplate(func, _, args) => {
            rename_ident_in_expression(func, from, to);
            for arg in args {
                rename_ident_in_expression(arg, from, to);
            }
        }
        ExpressionDesc::Fun { params, body, .. } => {
            for param in params {
                if param.same(from) {
                    *param = to.clone();
                }
            }
            rename_ident_in_statements(body, from, to);
        }
        ExpressionDesc::Array(items, _) => {
            for item in items {
                rename_ident_in_expression(item, from, to);
            }
        }
        ExpressionDesc::CamlBlock(items, _, tag, _) => {
            for item in items {
                rename_ident_in_expression(item, from, to);
            }
            rename_ident_in_expression(tag, from, to);
        }
        ExpressionDesc::Object(dup, props) => {
            if let Some(dup) = dup {
                rename_ident_in_expression(dup, from, to);
            }
            for (_, value) in props {
                rename_ident_in_expression(value, from, to);
            }
        }
    }
}

fn is_make_like_binding_name(name: &str) -> bool {
    name == "make"
        || name
            .strip_prefix("make$")
            .is_some_and(|suffix| !suffix.is_empty() && suffix.chars().all(|c| c.is_ascii_digit()))
}

fn is_descriptive_component_binding_name(name: &str) -> bool {
    !is_make_like_binding_name(name)
        && name
            .chars()
            .next()
            .is_some_and(|first| first.is_ascii_uppercase())
}

fn statements_mention_ident(stmts: &[Statement], target: &Ident) -> bool {
    stmts
        .iter()
        .any(|stmt| statement_mentions_ident(stmt, target))
}

fn statement_mentions_ident(stmt: &Statement, target: &Ident) -> bool {
    match &stmt.desc {
        StatementDesc::Block(block) => statements_mention_ident(block, target),
        StatementDesc::Variable(VariableDeclaration { ident, value, .. }) => {
            ident.same(target)
                || value
                    .as_ref()
                    .is_some_and(|value| expression_mentions_ident(value, target))
        }
        StatementDesc::Exp(expr) | StatementDesc::Return(expr) | StatementDesc::Throw(expr) => {
            expression_mentions_ident(expr, target)
        }
        StatementDesc::If(cond, then_block, else_block) => {
            expression_mentions_ident(cond, target)
                || statements_mention_ident(then_block, target)
                || statements_mention_ident(else_block, target)
        }
        StatementDesc::While(cond, body) => {
            expression_mentions_ident(cond, target) || statements_mention_ident(body, target)
        }
        StatementDesc::ForRange(start, finish, loop_ident, _, body) => {
            loop_ident.same(target)
                || start
                    .as_ref()
                    .is_some_and(|start| expression_mentions_ident(start, target))
                || expression_mentions_ident(finish, target)
                || statements_mention_ident(body, target)
        }
        StatementDesc::IntSwitch(test, clauses, default) => {
            expression_mentions_ident(test, target)
                || clauses
                    .iter()
                    .any(|(_, clause)| statements_mention_ident(&clause.body, target))
                || default
                    .as_ref()
                    .is_some_and(|block| statements_mention_ident(block, target))
        }
        StatementDesc::StringSwitch(test, clauses, default) => {
            expression_mentions_ident(test, target)
                || clauses
                    .iter()
                    .any(|clause| statements_mention_ident(&clause.clause.body, target))
                || default
                    .as_ref()
                    .is_some_and(|block| statements_mention_ident(block, target))
        }
        StatementDesc::Try(body, catch, finally) => {
            statements_mention_ident(body, target)
                || catch.as_ref().is_some_and(|(catch_ident, catch_block)| {
                    catch_ident.same(target) || statements_mention_ident(catch_block, target)
                })
                || finally
                    .as_ref()
                    .is_some_and(|block| statements_mention_ident(block, target))
        }
        StatementDesc::Debugger | StatementDesc::Break | StatementDesc::Continue => false,
    }
}

fn expression_mentions_ident(expr: &Expression, target: &Ident) -> bool {
    match &expr.desc {
        ExpressionDesc::Var(VIdent::Id(ident)) => ident.same(target),
        ExpressionDesc::Var(VIdent::Qualified(_, _))
        | ExpressionDesc::Bool(_)
        | ExpressionDesc::Str { .. }
        | ExpressionDesc::Number(_)
        | ExpressionDesc::Undefined { .. }
        | ExpressionDesc::Null
        | ExpressionDesc::RawJsCode(_) => false,
        ExpressionDesc::Length(inner, _)
        | ExpressionDesc::IsNullOrUndefined(inner)
        | ExpressionDesc::Typeof(inner)
        | ExpressionDesc::JsNot(inner)
        | ExpressionDesc::JsBnot(inner)
        | ExpressionDesc::Spread(inner)
        | ExpressionDesc::Await(inner)
        | ExpressionDesc::OptionalBlock(inner, _)
        | ExpressionDesc::StaticIndex(inner, _, _)
        | ExpressionDesc::New(inner, None) => expression_mentions_ident(inner, target),
        ExpressionDesc::In(left, right)
        | ExpressionDesc::StringAppend(left, right)
        | ExpressionDesc::Seq(left, right)
        | ExpressionDesc::Bin(_, left, right)
        | ExpressionDesc::FlatCall(left, right)
        | ExpressionDesc::StringIndex(left, right)
        | ExpressionDesc::ArrayIndex(left, right) => {
            expression_mentions_ident(left, target) || expression_mentions_ident(right, target)
        }
        ExpressionDesc::Cond(test, consequent, alternate) => {
            expression_mentions_ident(test, target)
                || expression_mentions_ident(consequent, target)
                || expression_mentions_ident(alternate, target)
        }
        ExpressionDesc::Call(func, args, _)
        | ExpressionDesc::New(func, Some(args))
        | ExpressionDesc::TaggedTemplate(func, _, args) => {
            expression_mentions_ident(func, target)
                || args
                    .iter()
                    .any(|arg| expression_mentions_ident(arg, target))
        }
        ExpressionDesc::Fun { params, body, .. } => {
            params.iter().any(|param| param.same(target)) || statements_mention_ident(body, target)
        }
        ExpressionDesc::Array(items, _) => items
            .iter()
            .any(|item| expression_mentions_ident(item, target)),
        ExpressionDesc::CamlBlock(items, _, tag, _) => {
            expression_mentions_ident(tag, target)
                || items
                    .iter()
                    .any(|item| expression_mentions_ident(item, target))
        }
        ExpressionDesc::Object(dup, props) => {
            dup.as_deref()
                .is_some_and(|dup| expression_mentions_ident(dup, target))
                || props
                    .iter()
                    .any(|(_, value)| expression_mentions_ident(value, target))
        }
        ExpressionDesc::CamlBlockTag(inner, _) => expression_mentions_ident(inner, target),
    }
}

fn flatten_and_mark_dead_block(
    block: Block,
    id_gen: &IdGenerator,
    substitution: &mut HashMap<Ident, Expression>,
    jsx_preserve: bool,
) -> Block {
    block
        .into_iter()
        .map(|stmt| flatten_and_mark_dead_statement(stmt, id_gen, substitution, jsx_preserve))
        .collect()
}

fn flatten_and_mark_dead_statement(
    stmt: Statement,
    id_gen: &IdGenerator,
    substitution: &mut HashMap<Ident, Expression>,
    jsx_preserve: bool,
) -> Statement {
    let Statement { desc, comment } = stmt;
    match desc {
        StatementDesc::Variable(decl) => {
            if matches!(decl.ident_info.used_stats, UsedStats::DeadPure) {
                return Statement {
                    desc: StatementDesc::Block(vec![]),
                    comment,
                };
            }

            if matches!(decl.ident_info.used_stats, UsedStats::DeadNonPure) {
                return match decl.value {
                    None => Statement {
                        desc: StatementDesc::Block(vec![]),
                        comment,
                    },
                    Some(value) => Statement {
                        desc: StatementDesc::Exp(value),
                        comment,
                    },
                };
            }

            if matches!(
                decl.property,
                LetKind::Strict | LetKind::StrictOpt | LetKind::Alias
            ) {
                if let Some(Expression {
                    desc: ExpressionDesc::CamlBlock(items, MutableFlag::Immutable, tag, tag_info),
                    comment: value_comment,
                }) = decl.value
                {
                    if should_materialize_block_binding_items(decl.property, &items, &tag_info) {
                        let mut rewritten_items = Vec::with_capacity(items.len());
                        let mut bindings = Vec::new();

                        for (index, item) in items.into_iter().enumerate() {
                            if is_simple_block_binding_item(decl.property, &item) {
                                rewritten_items.push(item);
                            } else {
                                let rewritten = flatten_and_mark_dead_expression(
                                    item,
                                    id_gen,
                                    substitution,
                                    jsx_preserve,
                                );
                                let temp = id_gen.create(&block_substitution_name(
                                    &decl.ident,
                                    &tag_info,
                                    index,
                                ));
                                rewritten_items.push(Expression::var(temp.clone()));
                                bindings.push(Statement::variable(VariableDeclaration {
                                    ident: temp,
                                    value: Some(rewritten),
                                    property: LetKind::Strict,
                                    ident_info: IdentInfo::default(),
                                }));
                            }
                        }

                        let rewritten_value = Expression {
                            desc: ExpressionDesc::CamlBlock(
                                rewritten_items,
                                MutableFlag::Immutable,
                                tag,
                                tag_info,
                            ),
                            comment: value_comment,
                        };
                        substitution.insert(decl.ident.clone(), rewritten_value.clone());

                        let original = Statement {
                            desc: StatementDesc::Variable(VariableDeclaration {
                                ident: decl.ident,
                                value: Some(rewritten_value),
                                property: decl.property,
                                ident_info: decl.ident_info,
                            }),
                            comment,
                        };

                        if bindings.is_empty() {
                            return original;
                        }

                        bindings.push(original);
                        return Statement {
                            desc: StatementDesc::Block(bindings),
                            comment: None,
                        };
                    }

                    // OCaml's js_pass_flatten_and_mark_dead matches
                    // `_ :: _ :: _ as ls`, which means immutable Caml blocks
                    // with at least two payload elements. Polyvar wrappers stay
                    // out of this path because their exported `NAME`/`VAL`
                    // object shape is already materialized before this pass in
                    // the OCaml backend.
                    return Statement {
                        desc: {
                            let rewritten_value = Expression {
                                desc: ExpressionDesc::CamlBlock(
                                    items
                                        .into_iter()
                                        .map(|item| {
                                            flatten_and_mark_dead_expression(
                                                item,
                                                id_gen,
                                                substitution,
                                                jsx_preserve,
                                            )
                                        })
                                        .collect(),
                                    MutableFlag::Immutable,
                                    Box::new(flatten_and_mark_dead_expression(
                                        *tag,
                                        id_gen,
                                        substitution,
                                        jsx_preserve,
                                    )),
                                    tag_info,
                                ),
                                comment: value_comment,
                            };
                            StatementDesc::Variable(VariableDeclaration {
                                ident: decl.ident,
                                value: Some(rewritten_value),
                                property: decl.property,
                                ident_info: decl.ident_info,
                            })
                        },
                        comment,
                    };
                }
            }

            Statement {
                desc: StatementDesc::Variable(VariableDeclaration {
                    ident: decl.ident,
                    value: decl.value.map(|value| {
                        flatten_and_mark_dead_expression(value, id_gen, substitution, jsx_preserve)
                    }),
                    property: decl.property,
                    ident_info: decl.ident_info,
                }),
                comment,
            }
        }
        StatementDesc::Block(block) => Statement {
            desc: StatementDesc::Block(flatten_and_mark_dead_block(
                block,
                id_gen,
                substitution,
                jsx_preserve,
            )),
            comment,
        },
        StatementDesc::Exp(expr) => Statement {
            desc: StatementDesc::Exp(flatten_and_mark_dead_expression(
                expr,
                id_gen,
                substitution,
                jsx_preserve,
            )),
            comment,
        },
        StatementDesc::Return(expr) => Statement {
            desc: StatementDesc::Return(flatten_and_mark_dead_expression(
                expr,
                id_gen,
                substitution,
                jsx_preserve,
            )),
            comment,
        },
        StatementDesc::If(cond, then_block, else_block) => Statement {
            desc: StatementDesc::If(
                flatten_and_mark_dead_expression(cond, id_gen, substitution, jsx_preserve),
                flatten_and_mark_dead_block(then_block, id_gen, substitution, jsx_preserve),
                flatten_and_mark_dead_block(else_block, id_gen, substitution, jsx_preserve),
            ),
            comment,
        },
        StatementDesc::While(cond, body) => Statement {
            desc: StatementDesc::While(
                flatten_and_mark_dead_expression(cond, id_gen, substitution, jsx_preserve),
                flatten_and_mark_dead_block(body, id_gen, substitution, jsx_preserve),
            ),
            comment,
        },
        StatementDesc::ForRange(start, finish, ident, direction, body) => Statement {
            desc: StatementDesc::ForRange(
                start.map(|expr| {
                    flatten_and_mark_dead_expression(expr, id_gen, substitution, jsx_preserve)
                }),
                flatten_and_mark_dead_expression(finish, id_gen, substitution, jsx_preserve),
                ident,
                direction,
                flatten_and_mark_dead_block(body, id_gen, substitution, jsx_preserve),
            ),
            comment,
        },
        StatementDesc::IntSwitch(test, clauses, default) => Statement {
            desc: StatementDesc::IntSwitch(
                flatten_and_mark_dead_expression(test, id_gen, substitution, jsx_preserve),
                clauses
                    .into_iter()
                    .map(|(tag, clause)| {
                        (
                            tag,
                            CaseClause {
                                body: flatten_and_mark_dead_block(
                                    clause.body,
                                    id_gen,
                                    substitution,
                                    jsx_preserve,
                                ),
                                should_break: clause.should_break,
                                comment: clause.comment,
                            },
                        )
                    })
                    .collect(),
                default.map(|block| {
                    flatten_and_mark_dead_block(block, id_gen, substitution, jsx_preserve)
                }),
            ),
            comment,
        },
        StatementDesc::StringSwitch(test, clauses, default) => Statement {
            desc: StatementDesc::StringSwitch(
                flatten_and_mark_dead_expression(test, id_gen, substitution, jsx_preserve),
                clauses
                    .into_iter()
                    .map(|clause| crate::js_ir::StringClause {
                        tag_type: clause.tag_type,
                        clause: CaseClause {
                            body: flatten_and_mark_dead_block(
                                clause.clause.body,
                                id_gen,
                                substitution,
                                jsx_preserve,
                            ),
                            should_break: clause.clause.should_break,
                            comment: clause.clause.comment,
                        },
                    })
                    .collect(),
                default.map(|block| {
                    flatten_and_mark_dead_block(block, id_gen, substitution, jsx_preserve)
                }),
            ),
            comment,
        },
        StatementDesc::Throw(expr) => Statement {
            desc: StatementDesc::Throw(flatten_and_mark_dead_expression(
                expr,
                id_gen,
                substitution,
                jsx_preserve,
            )),
            comment,
        },
        StatementDesc::Try(body, catch, finally) => Statement {
            desc: StatementDesc::Try(
                flatten_and_mark_dead_block(body, id_gen, substitution, jsx_preserve),
                catch.map(|(ident, block)| {
                    (
                        ident,
                        flatten_and_mark_dead_block(block, id_gen, substitution, jsx_preserve),
                    )
                }),
                finally.map(|block| {
                    flatten_and_mark_dead_block(block, id_gen, substitution, jsx_preserve)
                }),
            ),
            comment,
        },
        StatementDesc::Debugger => Statement {
            desc: StatementDesc::Debugger,
            comment,
        },
        StatementDesc::Break => Statement {
            desc: StatementDesc::Break,
            comment,
        },
        StatementDesc::Continue => Statement {
            desc: StatementDesc::Continue,
            comment,
        },
    }
}

fn flatten_and_mark_dead_expression(
    expr: Expression,
    id_gen: &IdGenerator,
    substitution: &mut HashMap<Ident, Expression>,
    jsx_preserve: bool,
) -> Expression {
    if let Some(rewritten) = try_substitute_caml_block_projection(&expr, substitution) {
        return rewritten;
    }

    let Expression { desc, comment } = expr;
    let desc = match desc {
        ExpressionDesc::Length(inner, object) => ExpressionDesc::Length(
            Box::new(flatten_and_mark_dead_expression(
                *inner,
                id_gen,
                substitution,
                jsx_preserve,
            )),
            object,
        ),
        ExpressionDesc::IsNullOrUndefined(inner) => ExpressionDesc::IsNullOrUndefined(Box::new(
            flatten_and_mark_dead_expression(*inner, id_gen, substitution, jsx_preserve),
        )),
        ExpressionDesc::StringAppend(left, right) => ExpressionDesc::StringAppend(
            Box::new(flatten_and_mark_dead_expression(
                *left,
                id_gen,
                substitution,
                jsx_preserve,
            )),
            Box::new(flatten_and_mark_dead_expression(
                *right,
                id_gen,
                substitution,
                jsx_preserve,
            )),
        ),
        ExpressionDesc::Bool(value) => ExpressionDesc::Bool(value),
        ExpressionDesc::Typeof(inner) => ExpressionDesc::Typeof(Box::new(
            flatten_and_mark_dead_expression(*inner, id_gen, substitution, jsx_preserve),
        )),
        ExpressionDesc::In(left, right) => ExpressionDesc::In(
            Box::new(flatten_and_mark_dead_expression(
                *left,
                id_gen,
                substitution,
                jsx_preserve,
            )),
            Box::new(flatten_and_mark_dead_expression(
                *right,
                id_gen,
                substitution,
                jsx_preserve,
            )),
        ),
        ExpressionDesc::JsNot(inner) => ExpressionDesc::JsNot(Box::new(
            flatten_and_mark_dead_expression(*inner, id_gen, substitution, jsx_preserve),
        )),
        ExpressionDesc::JsBnot(inner) => ExpressionDesc::JsBnot(Box::new(
            flatten_and_mark_dead_expression(*inner, id_gen, substitution, jsx_preserve),
        )),
        ExpressionDesc::Seq(left, right) => ExpressionDesc::Seq(
            Box::new(flatten_and_mark_dead_expression(
                *left,
                id_gen,
                substitution,
                jsx_preserve,
            )),
            Box::new(flatten_and_mark_dead_expression(
                *right,
                id_gen,
                substitution,
                jsx_preserve,
            )),
        ),
        ExpressionDesc::Cond(test, consequent, alternate) => ExpressionDesc::Cond(
            Box::new(flatten_and_mark_dead_expression(
                *test,
                id_gen,
                substitution,
                jsx_preserve,
            )),
            Box::new(flatten_and_mark_dead_expression(
                *consequent,
                id_gen,
                substitution,
                jsx_preserve,
            )),
            Box::new(flatten_and_mark_dead_expression(
                *alternate,
                id_gen,
                substitution,
                jsx_preserve,
            )),
        ),
        ExpressionDesc::Bin(op, left, right) => ExpressionDesc::Bin(
            op,
            Box::new(flatten_and_mark_dead_expression(
                *left,
                id_gen,
                substitution,
                jsx_preserve,
            )),
            Box::new(flatten_and_mark_dead_expression(
                *right,
                id_gen,
                substitution,
                jsx_preserve,
            )),
        ),
        ExpressionDesc::FlatCall(func, args) => ExpressionDesc::FlatCall(
            Box::new(flatten_and_mark_dead_expression(
                *func,
                id_gen,
                substitution,
                jsx_preserve,
            )),
            Box::new(flatten_and_mark_dead_expression(
                *args,
                id_gen,
                substitution,
                jsx_preserve,
            )),
        ),
        ExpressionDesc::Call(func, args, info) => ExpressionDesc::Call(
            Box::new(flatten_and_mark_dead_expression(
                *func,
                id_gen,
                substitution,
                jsx_preserve,
            )),
            args.into_iter()
                .enumerate()
                .map(|(index, arg)| {
                    if jsx_preserve && info.call_transformed_jsx && index == 0 {
                        flatten_and_mark_dead_transformed_jsx_tag_expression(
                            arg,
                            id_gen,
                            substitution,
                            jsx_preserve,
                        )
                    } else {
                        flatten_and_mark_dead_expression(arg, id_gen, substitution, jsx_preserve)
                    }
                })
                .collect(),
            info,
        ),
        ExpressionDesc::StringIndex(left, right) => ExpressionDesc::StringIndex(
            Box::new(flatten_and_mark_dead_expression(
                *left,
                id_gen,
                substitution,
                jsx_preserve,
            )),
            Box::new(flatten_and_mark_dead_expression(
                *right,
                id_gen,
                substitution,
                jsx_preserve,
            )),
        ),
        ExpressionDesc::ArrayIndex(left, right) => {
            let left = flatten_and_mark_dead_expression(*left, id_gen, substitution, jsx_preserve);
            let right =
                flatten_and_mark_dead_expression(*right, id_gen, substitution, jsx_preserve);
            if let Some(rewritten) =
                direct_projection_from_pure_literal(&left, None, int_literal(&right))
            {
                return rewritten;
            }
            ExpressionDesc::ArrayIndex(Box::new(left), Box::new(right))
        }
        ExpressionDesc::TaggedTemplate(tag, strings, values) => ExpressionDesc::TaggedTemplate(
            Box::new(flatten_and_mark_dead_expression(
                *tag,
                id_gen,
                substitution,
                jsx_preserve,
            )),
            strings
                .into_iter()
                .map(|value| {
                    flatten_and_mark_dead_expression(value, id_gen, substitution, jsx_preserve)
                })
                .collect(),
            values
                .into_iter()
                .map(|value| {
                    flatten_and_mark_dead_expression(value, id_gen, substitution, jsx_preserve)
                })
                .collect(),
        ),
        ExpressionDesc::StaticIndex(target, field, pos) => {
            let target =
                flatten_and_mark_dead_expression(*target, id_gen, substitution, jsx_preserve);
            if let Some(rewritten) = direct_projection_from_pure_literal(&target, Some(&field), pos)
            {
                return rewritten;
            }
            ExpressionDesc::StaticIndex(Box::new(target), field, pos)
        }
        ExpressionDesc::New(target, args) => ExpressionDesc::New(
            Box::new(flatten_and_mark_dead_expression(
                *target,
                id_gen,
                substitution,
                jsx_preserve,
            )),
            args.map(|items| {
                items
                    .into_iter()
                    .map(|arg| {
                        flatten_and_mark_dead_expression(arg, id_gen, substitution, jsx_preserve)
                    })
                    .collect()
            }),
        ),
        ExpressionDesc::Var(var) => ExpressionDesc::Var(var),
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
            body: flatten_and_mark_dead_block(body, id_gen, substitution, jsx_preserve),
            env,
            return_unit,
            async_,
            directive,
        },
        ExpressionDesc::Str { delim, txt } => ExpressionDesc::Str { delim, txt },
        ExpressionDesc::RawJsCode(info) => ExpressionDesc::RawJsCode(info),
        ExpressionDesc::Array(items, mutable_flag) => ExpressionDesc::Array(
            items
                .into_iter()
                .map(|item| {
                    flatten_and_mark_dead_expression(item, id_gen, substitution, jsx_preserve)
                })
                .collect(),
            mutable_flag,
        ),
        ExpressionDesc::OptionalBlock(inner, flag) => ExpressionDesc::OptionalBlock(
            Box::new(flatten_and_mark_dead_expression(
                *inner,
                id_gen,
                substitution,
                jsx_preserve,
            )),
            flag,
        ),
        ExpressionDesc::CamlBlock(items, mutable_flag, tag, tag_info) => ExpressionDesc::CamlBlock(
            items
                .into_iter()
                .map(|item| {
                    flatten_and_mark_dead_expression(item, id_gen, substitution, jsx_preserve)
                })
                .collect(),
            mutable_flag,
            Box::new(flatten_and_mark_dead_expression(
                *tag,
                id_gen,
                substitution,
                jsx_preserve,
            )),
            tag_info,
        ),
        ExpressionDesc::CamlBlockTag(inner, tag) => ExpressionDesc::CamlBlockTag(
            Box::new(flatten_and_mark_dead_expression(
                *inner,
                id_gen,
                substitution,
                jsx_preserve,
            )),
            tag,
        ),
        ExpressionDesc::Number(number) => ExpressionDesc::Number(number),
        ExpressionDesc::Object(dup, props) => ExpressionDesc::Object(
            dup.map(|expr| {
                Box::new(flatten_and_mark_dead_expression(
                    *expr,
                    id_gen,
                    substitution,
                    jsx_preserve,
                ))
            }),
            props
                .into_iter()
                .map(|(name, value)| {
                    (
                        name,
                        flatten_and_mark_dead_expression(value, id_gen, substitution, jsx_preserve),
                    )
                })
                .collect(),
        ),
        ExpressionDesc::Undefined { is_unit } => ExpressionDesc::Undefined { is_unit },
        ExpressionDesc::Null => ExpressionDesc::Null,
        ExpressionDesc::Await(inner) => ExpressionDesc::Await(Box::new(
            flatten_and_mark_dead_expression(*inner, id_gen, substitution, jsx_preserve),
        )),
        ExpressionDesc::Spread(inner) => ExpressionDesc::Spread(Box::new(
            flatten_and_mark_dead_expression(*inner, id_gen, substitution, jsx_preserve),
        )),
    };

    Expression { desc, comment }
}

fn flatten_and_mark_dead_transformed_jsx_tag_expression(
    expr: Expression,
    id_gen: &IdGenerator,
    substitution: &mut HashMap<Ident, Expression>,
    jsx_preserve: bool,
) -> Expression {
    let Expression { desc, comment } = expr;
    match desc {
        // OCaml's js_pass_flatten_and_mark_dead preserves component `.make`
        // projections in JSX-preserve mode so the dumper can print `<Foo.make />`.
        ExpressionDesc::StaticIndex(target, field, Some(index)) if field == "make" => Expression {
            desc: ExpressionDesc::StaticIndex(
                Box::new(flatten_and_mark_dead_expression(
                    *target,
                    id_gen,
                    substitution,
                    jsx_preserve,
                )),
                field,
                Some(index),
            ),
            comment,
        },
        other => flatten_and_mark_dead_expression(
            Expression {
                desc: other,
                comment,
            },
            id_gen,
            substitution,
            jsx_preserve,
        ),
    }
}

fn try_substitute_caml_block_projection(
    expr: &Expression,
    substitution: &HashMap<Ident, Expression>,
) -> Option<Expression> {
    match &expr.desc {
        ExpressionDesc::ArrayIndex(left, right) => {
            let ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)) = &left.desc else {
                return None;
            };
            let ExpressionDesc::Number(Number::Int { i, .. }) = right.desc else {
                return None;
            };
            substituted_caml_block_item(substitution, id, i)
        }
        ExpressionDesc::StaticIndex(target, _, Some(index)) => {
            let ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)) = &target.desc else {
                return None;
            };
            substituted_caml_block_item(substitution, id, *index)
        }
        _ => None,
    }
}

fn substituted_caml_block_item(
    substitution: &HashMap<Ident, Expression>,
    id: &Ident,
    index: i32,
) -> Option<Expression> {
    let expression = substitution.get(id)?;
    let ExpressionDesc::CamlBlock(items, MutableFlag::Immutable, _, _) = &expression.desc else {
        return None;
    };
    let item = items.get(usize::try_from(index).ok()?)?;
    is_simple_substituted_index_value(item).then(|| item.clone())
}

fn should_materialize_block_binding_items(
    property: LetKind,
    items: &[Expression],
    tag_info: &TagInfo,
) -> bool {
    if items.len() < 2 || matches!(tag_info, TagInfo::PolyVar(_)) {
        return false;
    }

    // Checked-in OCaml snapshots keep alias-bound deep constants inline, while
    // still materializing Strict/StrictOpt bindings and alias blocks with
    // computed payloads.
    !(property == LetKind::Alias && items.iter().all(is_deep_constant_block_binding_item))
}

fn is_deep_constant_block_binding_item(expr: &Expression) -> bool {
    match &expr.desc {
        ExpressionDesc::Number(_)
        | ExpressionDesc::Str { .. }
        | ExpressionDesc::Bool(_)
        | ExpressionDesc::Undefined { .. } => true,
        ExpressionDesc::OptionalBlock(inner, _) => is_deep_constant_block_binding_item(inner),
        ExpressionDesc::CamlBlock(items, MutableFlag::Immutable, _, _) => {
            items.iter().all(is_deep_constant_block_binding_item)
        }
        _ => false,
    }
}

fn is_simple_block_binding_item(property: LetKind, expr: &Expression) -> bool {
    // Mirror OCaml's `js_pass_flatten_and_mark_dead.ml:188-193` "simple"
    // case: only `Var`, `Number`, `Str`, `Bool`, `Undefined` items stay
    // inline; everything else (including any `Caml_block`) is hoisted into
    // a fresh local binding. `Lconst Const_block` materializes as
    // `Caml_block(NA, ...)` (see `Self::compile_constant`) so it intentionally
    // does NOT match `Caml_block(Immutable, ...)` patterns elsewhere — and
    // therefore does NOT count as simple here either.
    match &expr.desc {
        ExpressionDesc::Var(_)
        | ExpressionDesc::Number(_)
        | ExpressionDesc::Str { .. }
        | ExpressionDesc::Bool(_)
        | ExpressionDesc::Undefined { .. } => true,
        ExpressionDesc::OptionalBlock(inner, true) if property != LetKind::StrictOpt => {
            is_simple_block_binding_item(property, inner)
        }
        _ => false,
    }
}

fn is_simple_substituted_index_value(expr: &Expression) -> bool {
    match &expr.desc {
        ExpressionDesc::Var(_)
        | ExpressionDesc::Number(_)
        | ExpressionDesc::Str { .. }
        | ExpressionDesc::Undefined { .. } => true,
        ExpressionDesc::CamlBlock(
            items,
            MutableFlag::Immutable,
            _,
            TagInfo::Constructor { .. },
        ) => items.iter().all(is_simple_substituted_index_value),
        _ => false,
    }
}

fn block_substitution_name(ident: &Ident, tag_info: &TagInfo, index: usize) -> String {
    let suffix = match tag_info {
        TagInfo::Module(fields) => fields
            .get(index)
            .cloned()
            .unwrap_or_else(|| index.to_string()),
        TagInfo::Record { fields, .. } => fields
            .get(index)
            .map(|(field, _)| field.clone())
            .unwrap_or_else(|| index.to_string()),
        _ => index.to_string(),
    };
    format!("{}_{}", ident.name(), suffix)
}

fn max_ident_stamp_in_program(program: &Program) -> i32 {
    program.exports.iter().fold(
        max_ident_stamp_in_block(&program.block),
        |max_stamp, export| max_stamp.max(export.stamp()),
    )
}

#[derive(Debug, Clone, Copy)]
enum MarkDeadInfo {
    Recursive,
    Info {
        pure: bool,
        used: bool,
        exported: bool,
    },
}

fn mark_dead_code(program: &mut Program) {
    let mut states = HashMap::new();
    collect_mark_dead_states_block(&program.block, &program.export_set, &mut states);
    apply_mark_dead_states_block(&mut program.block, &states);
}

fn collect_mark_dead_states_block(
    block: &Block,
    export_set: &HashSet<Ident>,
    states: &mut HashMap<Ident, MarkDeadInfo>,
) {
    for stmt in block {
        collect_mark_dead_states_statement(stmt, export_set, states);
    }
}

fn collect_mark_dead_states_statement(
    stmt: &Statement,
    export_set: &HashSet<Ident>,
    states: &mut HashMap<Ident, MarkDeadInfo>,
) {
    match &stmt.desc {
        StatementDesc::Block(block) => collect_mark_dead_states_block(block, export_set, states),
        StatementDesc::Variable(decl) => {
            collect_mark_dead_states_variable(decl, export_set, states)
        }
        StatementDesc::Exp(expr) | StatementDesc::Return(expr) | StatementDesc::Throw(expr) => {
            collect_mark_dead_states_expression(expr, states);
        }
        StatementDesc::If(cond, then_block, else_block) => {
            collect_mark_dead_states_expression(cond, states);
            collect_mark_dead_states_block(then_block, export_set, states);
            collect_mark_dead_states_block(else_block, export_set, states);
        }
        StatementDesc::While(cond, body) => {
            collect_mark_dead_states_expression(cond, states);
            collect_mark_dead_states_block(body, export_set, states);
        }
        StatementDesc::ForRange(start, finish, _, _, body) => {
            if let Some(start) = start {
                collect_mark_dead_states_expression(start, states);
            }
            collect_mark_dead_states_expression(finish, states);
            collect_mark_dead_states_block(body, export_set, states);
        }
        StatementDesc::IntSwitch(test, clauses, default) => {
            collect_mark_dead_states_expression(test, states);
            for (_, clause) in clauses {
                collect_mark_dead_states_block(&clause.body, export_set, states);
            }
            if let Some(default) = default {
                collect_mark_dead_states_block(default, export_set, states);
            }
        }
        StatementDesc::StringSwitch(test, clauses, default) => {
            collect_mark_dead_states_expression(test, states);
            for clause in clauses {
                collect_mark_dead_states_block(&clause.clause.body, export_set, states);
            }
            if let Some(default) = default {
                collect_mark_dead_states_block(default, export_set, states);
            }
        }
        StatementDesc::Try(body, catch, finally) => {
            collect_mark_dead_states_block(body, export_set, states);
            if let Some((_, block)) = catch {
                collect_mark_dead_states_block(block, export_set, states);
            }
            if let Some(block) = finally {
                collect_mark_dead_states_block(block, export_set, states);
            }
        }
        StatementDesc::Debugger | StatementDesc::Break | StatementDesc::Continue => {}
    }
}

fn collect_mark_dead_states_variable(
    decl: &VariableDeclaration,
    export_set: &HashSet<Ident>,
    states: &mut HashMap<Ident, MarkDeadInfo>,
) {
    match decl.ident_info.used_stats {
        UsedStats::DeadPure => return,
        UsedStats::DeadNonPure => {
            if let Some(value) = &decl.value {
                collect_mark_dead_states_expression(value, states);
            }
            return;
        }
        _ => {}
    }

    let pure = match &decl.value {
        None => true,
        Some(value) => {
            collect_mark_dead_states_expression(value, states);
            js_expr_no_side_effects(value)
        }
    };
    let exported = export_set.contains(&decl.ident);
    match states.get(&decl.ident).copied() {
        Some(MarkDeadInfo::Recursive) => {
            states.insert(
                decl.ident.clone(),
                MarkDeadInfo::Info {
                    pure,
                    used: true,
                    exported,
                },
            );
        }
        Some(MarkDeadInfo::Info { .. }) => {}
        None => {
            states.insert(
                decl.ident.clone(),
                MarkDeadInfo::Info {
                    pure,
                    used: false,
                    exported,
                },
            );
        }
    }
}

fn collect_mark_dead_states_expression(
    expr: &Expression,
    states: &mut HashMap<Ident, MarkDeadInfo>,
) {
    match &expr.desc {
        ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)) => mark_dead_ident_use(id, states),
        ExpressionDesc::Var(crate::js_ir::VIdent::Qualified(_, _))
        | ExpressionDesc::Undefined { .. }
        | ExpressionDesc::Null
        | ExpressionDesc::Bool(_)
        | ExpressionDesc::Str { .. }
        | ExpressionDesc::RawJsCode(_)
        | ExpressionDesc::Number(_) => {}
        ExpressionDesc::Length(inner, _)
        | ExpressionDesc::IsNullOrUndefined(inner)
        | ExpressionDesc::Typeof(inner)
        | ExpressionDesc::JsNot(inner)
        | ExpressionDesc::JsBnot(inner)
        | ExpressionDesc::CamlBlockTag(inner, _)
        | ExpressionDesc::OptionalBlock(inner, _)
        | ExpressionDesc::Await(inner)
        | ExpressionDesc::Spread(inner) => collect_mark_dead_states_expression(inner, states),
        ExpressionDesc::StringAppend(left, right)
        | ExpressionDesc::In(left, right)
        | ExpressionDesc::Seq(left, right)
        | ExpressionDesc::Bin(_, left, right)
        | ExpressionDesc::FlatCall(left, right)
        | ExpressionDesc::StringIndex(left, right)
        | ExpressionDesc::ArrayIndex(left, right) => {
            collect_mark_dead_states_expression(left, states);
            collect_mark_dead_states_expression(right, states);
        }
        ExpressionDesc::Cond(test, consequent, alternate) => {
            collect_mark_dead_states_expression(test, states);
            collect_mark_dead_states_expression(consequent, states);
            collect_mark_dead_states_expression(alternate, states);
        }
        ExpressionDesc::Call(func, args, _) => {
            collect_mark_dead_states_expression(func, states);
            for arg in args {
                collect_mark_dead_states_expression(arg, states);
            }
        }
        ExpressionDesc::TaggedTemplate(tag, strings, values) => {
            collect_mark_dead_states_expression(tag, states);
            for string in strings {
                collect_mark_dead_states_expression(string, states);
            }
            for value in values {
                collect_mark_dead_states_expression(value, states);
            }
        }
        ExpressionDesc::StaticIndex(target, _, _) => {
            collect_mark_dead_states_expression(target, states)
        }
        ExpressionDesc::New(target, args) => {
            collect_mark_dead_states_expression(target, states);
            if let Some(args) = args {
                for arg in args {
                    collect_mark_dead_states_expression(arg, states);
                }
            }
        }
        ExpressionDesc::Fun { body, .. } => {
            for stmt in body {
                collect_mark_dead_states_statement(stmt, &HashSet::new(), states);
            }
        }
        ExpressionDesc::Array(items, _) => {
            for item in items {
                collect_mark_dead_states_expression(item, states);
            }
        }
        ExpressionDesc::CamlBlock(items, _, tag, _) => {
            for item in items {
                collect_mark_dead_states_expression(item, states);
            }
            collect_mark_dead_states_expression(tag, states);
        }
        ExpressionDesc::Object(dup, props) => {
            if let Some(dup) = dup {
                collect_mark_dead_states_expression(dup, states);
            }
            for (_, value) in props {
                collect_mark_dead_states_expression(value, states);
            }
        }
    }
}

fn mark_dead_ident_use(id: &Ident, states: &mut HashMap<Ident, MarkDeadInfo>) {
    match states.get_mut(id) {
        None => {
            states.insert(id.clone(), MarkDeadInfo::Recursive);
        }
        Some(MarkDeadInfo::Recursive) => {}
        Some(MarkDeadInfo::Info { used, .. }) => {
            *used = true;
        }
    }
}

fn apply_mark_dead_states_block(block: &mut Block, states: &HashMap<Ident, MarkDeadInfo>) {
    for stmt in block {
        apply_mark_dead_states_statement(stmt, states);
    }
}

fn apply_mark_dead_states_statement(stmt: &mut Statement, states: &HashMap<Ident, MarkDeadInfo>) {
    match &mut stmt.desc {
        StatementDesc::Block(block) => apply_mark_dead_states_block(block, states),
        StatementDesc::Variable(decl) => {
            apply_mark_dead_states_variable(decl, states);
            if let Some(value) = &mut decl.value {
                apply_mark_dead_states_expression(value, states);
            }
        }
        StatementDesc::Exp(expr) | StatementDesc::Return(expr) | StatementDesc::Throw(expr) => {
            apply_mark_dead_states_expression(expr, states);
        }
        StatementDesc::If(_, then_block, else_block) => {
            apply_mark_dead_states_block(then_block, states);
            apply_mark_dead_states_block(else_block, states);
        }
        StatementDesc::While(_, body) => apply_mark_dead_states_block(body, states),
        StatementDesc::ForRange(_, _, _, _, body) => apply_mark_dead_states_block(body, states),
        StatementDesc::IntSwitch(_, clauses, default) => {
            for (_, clause) in clauses {
                apply_mark_dead_states_block(&mut clause.body, states);
            }
            if let Some(default) = default {
                apply_mark_dead_states_block(default, states);
            }
        }
        StatementDesc::StringSwitch(_, clauses, default) => {
            for clause in clauses {
                apply_mark_dead_states_block(&mut clause.clause.body, states);
            }
            if let Some(default) = default {
                apply_mark_dead_states_block(default, states);
            }
        }
        StatementDesc::Try(body, catch, finally) => {
            apply_mark_dead_states_block(body, states);
            if let Some((_, block)) = catch {
                apply_mark_dead_states_block(block, states);
            }
            if let Some(block) = finally {
                apply_mark_dead_states_block(block, states);
            }
        }
        StatementDesc::Debugger | StatementDesc::Break | StatementDesc::Continue => {}
    }
}

fn apply_mark_dead_states_variable(
    decl: &mut VariableDeclaration,
    states: &HashMap<Ident, MarkDeadInfo>,
) {
    let Some(MarkDeadInfo::Info {
        pure,
        used,
        exported,
    }) = states.get(&decl.ident).copied()
    else {
        return;
    };

    let status = if exported {
        UsedStats::Exported
    } else if used {
        UsedStats::Used
    } else if pure {
        UsedStats::DeadPure
    } else {
        UsedStats::DeadNonPure
    };
    update_used_stats(&mut decl.ident_info, status);
}

fn apply_mark_dead_states_expression(expr: &mut Expression, states: &HashMap<Ident, MarkDeadInfo>) {
    match &mut expr.desc {
        ExpressionDesc::Length(inner, _)
        | ExpressionDesc::IsNullOrUndefined(inner)
        | ExpressionDesc::Typeof(inner)
        | ExpressionDesc::JsNot(inner)
        | ExpressionDesc::JsBnot(inner)
        | ExpressionDesc::CamlBlockTag(inner, _)
        | ExpressionDesc::OptionalBlock(inner, _)
        | ExpressionDesc::Await(inner)
        | ExpressionDesc::Spread(inner) => apply_mark_dead_states_expression(inner, states),
        ExpressionDesc::StringAppend(left, right)
        | ExpressionDesc::In(left, right)
        | ExpressionDesc::Seq(left, right)
        | ExpressionDesc::Bin(_, left, right)
        | ExpressionDesc::FlatCall(left, right)
        | ExpressionDesc::StringIndex(left, right)
        | ExpressionDesc::ArrayIndex(left, right) => {
            apply_mark_dead_states_expression(left, states);
            apply_mark_dead_states_expression(right, states);
        }
        ExpressionDesc::Cond(test, consequent, alternate) => {
            apply_mark_dead_states_expression(test, states);
            apply_mark_dead_states_expression(consequent, states);
            apply_mark_dead_states_expression(alternate, states);
        }
        ExpressionDesc::Call(func, args, _) => {
            apply_mark_dead_states_expression(func, states);
            for arg in args {
                apply_mark_dead_states_expression(arg, states);
            }
        }
        ExpressionDesc::TaggedTemplate(tag, strings, values) => {
            apply_mark_dead_states_expression(tag, states);
            for string in strings {
                apply_mark_dead_states_expression(string, states);
            }
            for value in values {
                apply_mark_dead_states_expression(value, states);
            }
        }
        ExpressionDesc::StaticIndex(target, _, _) => {
            apply_mark_dead_states_expression(target, states)
        }
        ExpressionDesc::New(target, args) => {
            apply_mark_dead_states_expression(target, states);
            if let Some(args) = args {
                for arg in args {
                    apply_mark_dead_states_expression(arg, states);
                }
            }
        }
        ExpressionDesc::Fun { body, .. } => apply_mark_dead_states_block(body, states),
        ExpressionDesc::Array(items, _) => {
            for item in items {
                apply_mark_dead_states_expression(item, states);
            }
        }
        ExpressionDesc::CamlBlock(items, _, tag, _) => {
            for item in items {
                apply_mark_dead_states_expression(item, states);
            }
            apply_mark_dead_states_expression(tag, states);
        }
        ExpressionDesc::Object(dup, props) => {
            if let Some(dup) = dup {
                apply_mark_dead_states_expression(dup, states);
            }
            for (_, value) in props {
                apply_mark_dead_states_expression(value, states);
            }
        }
        ExpressionDesc::Var(_)
        | ExpressionDesc::Undefined { .. }
        | ExpressionDesc::Null
        | ExpressionDesc::Bool(_)
        | ExpressionDesc::Str { .. }
        | ExpressionDesc::RawJsCode(_)
        | ExpressionDesc::Number(_) => {}
    }
}

fn update_used_stats(info: &mut IdentInfo, status: UsedStats) {
    if matches!(
        info.used_stats,
        UsedStats::DeadPure | UsedStats::DeadNonPure | UsedStats::Exported
    ) {
        return;
    }
    info.used_stats = status;
}

fn flatten_program(mut program: Program) -> Program {
    program.block = flatten_block(program.block);
    program
}

fn flatten_block(block: Block) -> Block {
    let mut flattened = Vec::new();

    for stmt in block {
        match flatten_statement(stmt) {
            Statement {
                desc: StatementDesc::Block(inner),
                ..
            } => flattened.extend(inner),
            other => flattened.push(other),
        }
    }

    flattened
}

fn flatten_statement(stmt: Statement) -> Statement {
    let Statement { desc, comment } = stmt;

    match desc {
        StatementDesc::Exp(expr) => {
            let Expression {
                desc,
                comment: expr_comment,
            } = expr;

            match desc {
                ExpressionDesc::Seq(_, _) => {
                    let block = flatten_sequence_statements(Expression {
                        desc,
                        comment: expr_comment,
                    });
                    Statement::new(StatementDesc::Block(block))
                }
                ExpressionDesc::CamlBlock(args, _, _, _) => {
                    let block = args
                        .into_iter()
                        .map(|arg| flatten_statement(Statement::exp(arg)))
                        .collect();
                    Statement::new(StatementDesc::Block(block))
                }
                ExpressionDesc::Cond(test, consequent, alternate) => Statement {
                    desc: StatementDesc::If(
                        flatten_expression(*test),
                        vec![flatten_statement(Statement::exp(*consequent))],
                        vec![flatten_statement(Statement::exp(*alternate))],
                    ),
                    comment,
                },
                ExpressionDesc::Bin(BinOp::Eq, target, value) => {
                    if matches!(value.desc, ExpressionDesc::Seq(_, _)) {
                        let mut exprs = Vec::new();
                        flatten_sequence_expressions(*value, &mut exprs);
                        let last = exprs
                            .pop()
                            .expect("sequence flattening must produce at least one expression");
                        let mut block: Block = exprs
                            .into_iter()
                            .map(|expr| flatten_statement(Statement::exp(expr)))
                            .collect();
                        block.push(flatten_statement(Statement::exp(Expression::bin(
                            BinOp::Eq,
                            *target,
                            last,
                        ))));
                        Statement::new(StatementDesc::Block(block))
                    } else {
                        Statement {
                            desc: StatementDesc::Exp(flatten_expression(Expression {
                                desc: ExpressionDesc::Bin(BinOp::Eq, target, value),
                                comment: expr_comment,
                            })),
                            comment,
                        }
                    }
                }
                desc => Statement {
                    desc: StatementDesc::Exp(flatten_expression(Expression {
                        desc,
                        comment: expr_comment,
                    })),
                    comment,
                },
            }
        }
        StatementDesc::Return(expr) => {
            let Expression {
                desc,
                comment: expr_comment,
            } = expr;

            match desc {
                ExpressionDesc::Cond(test, consequent, alternate) => Statement {
                    desc: StatementDesc::If(
                        flatten_expression(*test),
                        vec![flatten_statement(Statement::return_(*consequent))],
                        vec![flatten_statement(Statement::return_(*alternate))],
                    ),
                    comment,
                },
                ExpressionDesc::Seq(_, _) => {
                    let mut exprs = Vec::new();
                    flatten_sequence_expressions(
                        Expression {
                            desc,
                            comment: expr_comment,
                        },
                        &mut exprs,
                    );
                    let last = exprs
                        .pop()
                        .expect("return sequence flattening must produce at least one expression");
                    let mut block: Block = exprs
                        .into_iter()
                        .map(|expr| flatten_statement(Statement::exp(expr)))
                        .collect();
                    block.push(flatten_statement(Statement::return_(last)));
                    Statement::new(StatementDesc::Block(block))
                }
                desc => Statement {
                    desc: StatementDesc::Return(flatten_expression(Expression {
                        desc,
                        comment: expr_comment,
                    })),
                    comment,
                },
            }
        }
        StatementDesc::Block(block) => {
            if block.len() == 1 {
                flatten_statement(block.into_iter().next().expect("single-item block"))
            } else {
                Statement {
                    desc: StatementDesc::Block(flatten_block(block)),
                    comment,
                }
            }
        }
        StatementDesc::Variable(decl) => Statement {
            desc: StatementDesc::Variable(VariableDeclaration {
                ident: decl.ident,
                value: decl.value.map(flatten_expression),
                property: decl.property,
                ident_info: decl.ident_info,
            }),
            comment,
        },
        StatementDesc::If(cond, then_block, else_block) => Statement {
            desc: StatementDesc::If(
                flatten_expression(cond),
                flatten_block(then_block),
                flatten_block(else_block),
            ),
            comment,
        },
        StatementDesc::While(cond, body) => Statement {
            desc: StatementDesc::While(flatten_expression(cond), flatten_block(body)),
            comment,
        },
        StatementDesc::ForRange(start, finish, ident, direction, body) => Statement {
            desc: StatementDesc::ForRange(
                start.map(flatten_expression),
                flatten_expression(finish),
                ident,
                direction,
                flatten_block(body),
            ),
            comment,
        },
        StatementDesc::IntSwitch(test, clauses, default) => Statement {
            desc: StatementDesc::IntSwitch(
                flatten_expression(test),
                clauses
                    .into_iter()
                    .map(|(tag, clause)| (tag, flatten_case_clause(clause)))
                    .collect(),
                default.map(flatten_block),
            ),
            comment,
        },
        StatementDesc::StringSwitch(test, clauses, default) => Statement {
            desc: StatementDesc::StringSwitch(
                flatten_expression(test),
                clauses
                    .into_iter()
                    .map(|clause| StringClause {
                        tag_type: clause.tag_type,
                        clause: flatten_case_clause(clause.clause),
                    })
                    .collect(),
                default.map(flatten_block),
            ),
            comment,
        },
        StatementDesc::Throw(expr) => Statement {
            desc: StatementDesc::Throw(flatten_expression(expr)),
            comment,
        },
        StatementDesc::Try(body, catch, finally) => Statement {
            desc: StatementDesc::Try(
                flatten_block(body),
                catch.map(|(id, block)| (id, flatten_block(block))),
                finally.map(flatten_block),
            ),
            comment,
        },
        StatementDesc::Debugger => Statement {
            desc: StatementDesc::Debugger,
            comment,
        },
        StatementDesc::Break => Statement {
            desc: StatementDesc::Break,
            comment,
        },
        StatementDesc::Continue => Statement {
            desc: StatementDesc::Continue,
            comment,
        },
    }
}

fn flatten_case_clause(clause: CaseClause) -> CaseClause {
    CaseClause {
        body: flatten_block(clause.body),
        should_break: clause.should_break,
        comment: clause.comment,
    }
}

fn flatten_expression(expr: Expression) -> Expression {
    let comment = expr.comment;
    let desc = match expr.desc {
        ExpressionDesc::Length(inner, object) => {
            ExpressionDesc::Length(Box::new(flatten_expression(*inner)), object)
        }
        ExpressionDesc::IsNullOrUndefined(inner) => {
            ExpressionDesc::IsNullOrUndefined(Box::new(flatten_expression(*inner)))
        }
        ExpressionDesc::StringAppend(left, right) => ExpressionDesc::StringAppend(
            Box::new(flatten_expression(*left)),
            Box::new(flatten_expression(*right)),
        ),
        ExpressionDesc::Bool(value) => ExpressionDesc::Bool(value),
        ExpressionDesc::Typeof(inner) => {
            ExpressionDesc::Typeof(Box::new(flatten_expression(*inner)))
        }
        ExpressionDesc::In(left, right) => ExpressionDesc::In(
            Box::new(flatten_expression(*left)),
            Box::new(flatten_expression(*right)),
        ),
        ExpressionDesc::JsNot(inner) => ExpressionDesc::JsNot(Box::new(flatten_expression(*inner))),
        ExpressionDesc::JsBnot(inner) => {
            ExpressionDesc::JsBnot(Box::new(flatten_expression(*inner)))
        }
        ExpressionDesc::Seq(left, right) => ExpressionDesc::Seq(
            Box::new(flatten_expression(*left)),
            Box::new(flatten_expression(*right)),
        ),
        ExpressionDesc::Cond(test, consequent, alternate) => ExpressionDesc::Cond(
            Box::new(flatten_expression(*test)),
            Box::new(flatten_expression(*consequent)),
            Box::new(flatten_expression(*alternate)),
        ),
        ExpressionDesc::Bin(op, left, right) => ExpressionDesc::Bin(
            op,
            Box::new(flatten_expression(*left)),
            Box::new(flatten_expression(*right)),
        ),
        ExpressionDesc::FlatCall(func, args) => ExpressionDesc::FlatCall(
            Box::new(flatten_expression(*func)),
            Box::new(flatten_expression(*args)),
        ),
        ExpressionDesc::Call(func, args, info) => ExpressionDesc::Call(
            Box::new(flatten_expression(*func)),
            args.into_iter().map(flatten_expression).collect(),
            info,
        ),
        ExpressionDesc::StringIndex(left, right) => ExpressionDesc::StringIndex(
            Box::new(flatten_expression(*left)),
            Box::new(flatten_expression(*right)),
        ),
        ExpressionDesc::ArrayIndex(left, right) => ExpressionDesc::ArrayIndex(
            Box::new(flatten_expression(*left)),
            Box::new(flatten_expression(*right)),
        ),
        ExpressionDesc::TaggedTemplate(tag, strings, values) => ExpressionDesc::TaggedTemplate(
            Box::new(flatten_expression(*tag)),
            strings.into_iter().map(flatten_expression).collect(),
            values.into_iter().map(flatten_expression).collect(),
        ),
        ExpressionDesc::StaticIndex(target, field, pos) => {
            ExpressionDesc::StaticIndex(Box::new(flatten_expression(*target)), field, pos)
        }
        ExpressionDesc::New(target, args) => ExpressionDesc::New(
            Box::new(flatten_expression(*target)),
            args.map(|args| args.into_iter().map(flatten_expression).collect()),
        ),
        ExpressionDesc::Var(var) => ExpressionDesc::Var(var),
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
            body: flatten_block(body),
            env,
            return_unit,
            async_,
            directive,
        },
        ExpressionDesc::Str { delim, txt } => ExpressionDesc::Str { delim, txt },
        ExpressionDesc::RawJsCode(info) => ExpressionDesc::RawJsCode(info),
        ExpressionDesc::Array(items, mutable_flag) => ExpressionDesc::Array(
            items.into_iter().map(flatten_expression).collect(),
            mutable_flag,
        ),
        ExpressionDesc::OptionalBlock(inner, flag) => {
            ExpressionDesc::OptionalBlock(Box::new(flatten_expression(*inner)), flag)
        }
        ExpressionDesc::CamlBlock(items, mutable_flag, tag, tag_info) => ExpressionDesc::CamlBlock(
            items.into_iter().map(flatten_expression).collect(),
            mutable_flag,
            Box::new(flatten_expression(*tag)),
            tag_info,
        ),
        ExpressionDesc::CamlBlockTag(inner, tag) => {
            ExpressionDesc::CamlBlockTag(Box::new(flatten_expression(*inner)), tag)
        }
        ExpressionDesc::Number(number) => ExpressionDesc::Number(number),
        ExpressionDesc::Object(dup, props) => ExpressionDesc::Object(
            dup.map(|dup| Box::new(flatten_expression(*dup))),
            props
                .into_iter()
                .map(|(name, value)| (name, flatten_expression(value)))
                .collect(),
        ),
        ExpressionDesc::Undefined { is_unit } => ExpressionDesc::Undefined { is_unit },
        ExpressionDesc::Null => ExpressionDesc::Null,
        ExpressionDesc::Await(inner) => ExpressionDesc::Await(Box::new(flatten_expression(*inner))),
        ExpressionDesc::Spread(inner) => {
            ExpressionDesc::Spread(Box::new(flatten_expression(*inner)))
        }
    };

    Expression { desc, comment }
}

fn flatten_sequence_statements(expr: Expression) -> Block {
    let mut exprs = Vec::new();
    flatten_sequence_expressions(expr, &mut exprs);
    exprs
        .into_iter()
        .map(|expr| flatten_statement(Statement::exp(expr)))
        .collect()
}

fn flatten_sequence_expressions(expr: Expression, out: &mut Vec<Expression>) {
    match expr.desc {
        ExpressionDesc::Seq(left, right) => {
            flatten_sequence_expressions(*left, out);
            flatten_sequence_expressions(*right, out);
        }
        desc => out.push(Expression {
            desc,
            comment: expr.comment,
        }),
    }
}
