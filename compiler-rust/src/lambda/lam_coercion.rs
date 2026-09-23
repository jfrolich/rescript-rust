//! Export alias resolution and toplevel rewriting.
//!
//! Port of `lam_coercion.ml` — resolves export aliases, rewrites toplevel
//! variable initializers, and handles toplevel export extraction.

use std::collections::{HashMap, HashSet};

use crate::ident::Ident;
use crate::js_ir::op::IdentInfo;
use crate::js_ir::{
    Block, Expression, ExpressionDesc, Statement, StatementDesc, VIdent, VariableDeclaration,
    ocaml_eq_expression,
};
use crate::lambda::TagInfo;
use crate::lambda::js_exp_make::js_expr_no_side_effects;
use crate::lambda::js_shake::{
    TailMoveInitializerKind, flatten_toplevel_block_owned, flatten_toplevel_block_refs,
    resolve_tail_move_initializer_kind, resolve_tail_move_replacement_expression,
    statement_mentions_ident_anywhere, tail_move_materialized_root_ident,
};
use crate::lambda::lam_compat::LetKind;

pub(crate) fn resolve_export_aliases(block: &Block, exports: Vec<Ident>) -> Vec<Ident> {
    let mut declared = HashSet::new();
    collect_declared_idents(block, &mut declared);
    let mut aliases = HashMap::new();
    collect_export_aliases(block, &mut aliases);
    exports
        .into_iter()
        .map(|export| {
            if keeps_declared_same_name_function_export_alias(block, &export) {
                return export;
            }
            resolve_declared_same_name_self_alias_target(block, &export)
                .or_else(|| reusable_declared_same_name_export_alias(block, &export))
                .unwrap_or_else(|| resolve_export_alias(&export, &aliases, &declared))
        })
        .collect()
}

pub(crate) fn keeps_declared_same_name_function_export_alias(
    block: &Block,
    export: &Ident,
) -> bool {
    block_declares_initialized_ident(block, export)
        && matches!(
            resolve_tail_move_initializer_kind(block, export),
            Some(TailMoveInitializerKind::Function)
        )
        && count_materialized_same_name_binding_roots(block, export.name()) > 1
}

pub(crate) fn count_materialized_same_name_binding_roots(block: &Block, name: &str) -> usize {
    flatten_toplevel_block_refs(block)
        .into_iter()
        .filter(|stmt| match &stmt.desc {
            StatementDesc::Variable(VariableDeclaration {
                ident,
                value: Some(initializer),
                ..
            }) if ident.name() == name => !matches!(
                &initializer.desc,
                ExpressionDesc::Var(VIdent::Id(target)) if target.name() == ident.name()
            ),
            _ => false,
        })
        .count()
}

pub(crate) fn resolve_declared_same_name_self_alias_target(
    block: &Block,
    export: &Ident,
) -> Option<Ident> {
    match resolve_tail_move_replacement_expression(
        block,
        &Expression::var(export.clone()),
        export,
        false,
    )
    .desc
    {
        ExpressionDesc::Var(VIdent::Id(target))
            if !target.same(export) && block_declares_ident(block, &target) =>
        {
            Some(target)
        }
        _ => None,
    }
}

pub(crate) fn reusable_declared_same_name_export_alias(
    block: &Block,
    export: &Ident,
) -> Option<Ident> {
    let flattened_refs = flatten_toplevel_block_refs(block);
    let initializer = flattened_refs.iter().find_map(|stmt| match &stmt.desc {
        StatementDesc::Variable(VariableDeclaration {
            ident,
            value: Some(initializer),
            ..
        }) if ident.same(export) => Some(initializer),
        _ => None,
    })?;
    reusable_same_name_export_binding_ref(&flattened_refs, export, initializer)
}

pub(crate) fn collect_declared_idents(block: &Block, declared: &mut HashSet<Ident>) {
    for stmt in block {
        match &stmt.desc {
            StatementDesc::Variable(VariableDeclaration { ident, .. }) => {
                declared.insert(ident.clone());
            }
            StatementDesc::Block(inner) => collect_declared_idents(inner, declared),
            StatementDesc::If(_, then_block, else_block) => {
                collect_declared_idents(then_block, declared);
                collect_declared_idents(else_block, declared);
            }
            _ => {}
        }
    }
}

pub(crate) fn block_declares_initialized_ident(block: &Block, target: &Ident) -> bool {
    block.iter().find_map(|stmt| match &stmt.desc {
        StatementDesc::Variable(VariableDeclaration { ident, value, .. }) if ident.same(target) => {
            Some(value.is_some())
        }
        _ => None,
    }) == Some(true)
}

pub(crate) fn block_declares_ident(block: &Block, target: &Ident) -> bool {
    block.iter().any(|stmt| {
        matches!(
            &stmt.desc,
            StatementDesc::Variable(VariableDeclaration { ident, .. }) if ident.same(target)
        )
    })
}

pub(crate) fn collect_export_aliases(block: &Block, aliases: &mut HashMap<Ident, Ident>) {
    for stmt in block {
        match &stmt.desc {
            StatementDesc::Variable(VariableDeclaration {
                ident,
                value:
                    Some(Expression {
                        desc: ExpressionDesc::Var(VIdent::Id(target)),
                        ..
                    }),
                ..
            }) => {
                aliases.insert(ident.clone(), target.clone());
            }
            StatementDesc::Block(inner) => collect_export_aliases(inner, aliases),
            StatementDesc::If(_, then_block, else_block) => {
                collect_export_aliases(then_block, aliases);
                collect_export_aliases(else_block, aliases);
            }
            _ => {}
        }
    }
}

pub(crate) fn rewrite_toplevel_variable_initializers_through_rewriteable_aliases(
    block: &mut Block,
    exports: &[Ident],
) {
    if exports.is_empty() {
        return;
    }

    let exported_idents: HashSet<Ident> = exports.iter().cloned().collect();
    // OCaml export coercion works over the flattened lambda group list before
    // JS lowering (`compiler/core/lam_coercion.ml:179-199`) and only
    // substitutes Strict/Alias/StrictOpt bindings
    // (`compiler/core/lam_pass_lets_dce.ml:21-23`). This Rust repair pass runs
    // after JS lowering, owns the top-level block, and mirrors that flattened
    // traversal by moving statements into one list instead of cloning it.
    let mut flattened = flatten_toplevel_block_owned(std::mem::take(block));
    let mut changed = true;

    while changed {
        changed = false;
        for index in 0..flattened.len() {
            let Some((ident, target, current_value)) = (match &flattened[index].desc {
                StatementDesc::Variable(VariableDeclaration {
                    ident,
                    value:
                        Some(Expression {
                            desc: ExpressionDesc::Var(VIdent::Id(target)),
                            ..
                        }),
                    ..
                }) if exported_idents.contains(ident) => Some((
                    ident.clone(),
                    target.clone(),
                    variable_initializer(&flattened[index]).cloned(),
                )),
                _ => None,
            }) else {
                continue;
            };

            let Some(current_value) = current_value else {
                continue;
            };

            let materialized_root = tail_move_materialized_root_ident(&flattened, &current_value);
            let Some(mut replacement) =
                resolve_rewriteable_toplevel_alias_initializer(&flattened, &target)
            else {
                continue;
            };
            if matches!(
                replacement.desc,
                ExpressionDesc::Number(_)
                    | ExpressionDesc::Str { .. }
                    | ExpressionDesc::Bool(_)
                    | ExpressionDesc::Undefined { .. }
                    | ExpressionDesc::Null
            ) {
                if let Some(root) = materialized_root {
                    // Exported roots are uses too: the final export block is
                    // counted by Lam_pass_count.collect_occurs. Export coercion
                    // retains Lvar for a differently named export (lam_coercion.ml:112-121).
                    if exported_idents.contains(&root)
                        || rewriteable_alias_root_has_other_toplevel_uses(&flattened, index, &root)
                    {
                        replacement = Expression::var(root);
                    }
                }
            }

            if ocaml_eq_expression(&current_value, &replacement) {
                continue;
            }

            let StatementDesc::Variable(VariableDeclaration { value, .. }) =
                &mut flattened[index].desc
            else {
                continue;
            };
            *value = Some(replacement);
            debug_assert!(exported_idents.contains(&ident));
            changed = true;
        }
    }

    *block = flattened;
}

pub(crate) fn rewriteable_alias_root_has_other_toplevel_uses(
    block: &Block,
    alias_index: usize,
    root: &Ident,
) -> bool {
    block.iter().enumerate().any(|(index, stmt)| {
        if index == alias_index {
            return false;
        }
        match &stmt.desc {
            StatementDesc::Variable(VariableDeclaration { ident, .. }) if ident.same(root) => false,
            _ => statement_mentions_ident_anywhere(stmt, root),
        }
    })
}

pub(crate) fn resolve_rewriteable_toplevel_alias_initializer(
    block: &[Statement],
    start: &Ident,
) -> Option<Expression> {
    let mut current = start.clone();
    let mut seen = HashSet::new();

    loop {
        if !seen.insert(current.clone()) {
            return None;
        }

        let (value, property) = block.iter().find_map(|stmt| match &stmt.desc {
            StatementDesc::Variable(VariableDeclaration {
                ident,
                value: Some(initializer),
                property,
                ..
            }) if ident.same(&current) => Some((initializer, *property)),
            _ => None,
        })?;

        // OCaml's `compiler/core/lam_pass_lets_dce.ml:21-23` only substitutes
        // Strict / Alias / StrictOpt. A Variable-kind binding compiles to a
        // `let`-mutable JS declaration (post-eliminate_ref ref); folding
        // through its initial value is unsound because later code may mutate
        // the binding.
        if matches!(property, LetKind::Variable) {
            return None;
        }

        match &value.desc {
            ExpressionDesc::Var(VIdent::Id(next)) if next.name() == current.name() => {
                current = next.clone();
            }
            ExpressionDesc::Fun { .. } => return Some(Expression::var(current)),
            ExpressionDesc::Number(_)
            | ExpressionDesc::Str { .. }
            | ExpressionDesc::Bool(_)
            | ExpressionDesc::Undefined { .. }
            | ExpressionDesc::Null => return Some(value.clone()),
            _ => return None,
        }
    }
}

pub(crate) fn variable_initializer(stmt: &Statement) -> Option<&Expression> {
    match &stmt.desc {
        StatementDesc::Variable(VariableDeclaration { value, .. }) => value.as_ref(),
        _ => None,
    }
}

pub(crate) fn max_ident_stamp_in_block(block: &Block) -> i32 {
    block.iter().fold(0, |max_stamp, stmt| {
        max_stamp.max(max_ident_stamp_in_statement(stmt))
    })
}

pub(crate) fn max_ident_stamp_in_statement(stmt: &Statement) -> i32 {
    match &stmt.desc {
        StatementDesc::Block(block) => max_ident_stamp_in_block(block),
        StatementDesc::Variable(VariableDeclaration { ident, value, .. }) => value
            .as_ref()
            .map(max_ident_stamp_in_expression)
            .unwrap_or(0)
            .max(ident.stamp()),
        StatementDesc::Exp(expr) | StatementDesc::Return(expr) | StatementDesc::Throw(expr) => {
            max_ident_stamp_in_expression(expr)
        }
        StatementDesc::If(cond, then_block, else_block) => max_ident_stamp_in_expression(cond)
            .max(max_ident_stamp_in_block(then_block))
            .max(max_ident_stamp_in_block(else_block)),
        StatementDesc::While(_, cond, body) => {
            max_ident_stamp_in_expression(cond).max(max_ident_stamp_in_block(body))
        }
        StatementDesc::ForRange(_, start, finish, ident, _, body) => start
            .as_ref()
            .map(max_ident_stamp_in_expression)
            .unwrap_or(0)
            .max(max_ident_stamp_in_expression(finish))
            .max(ident.stamp())
            .max(max_ident_stamp_in_block(body)),
        StatementDesc::ForOf(_, ident, iterable, body)
        | StatementDesc::ForAwaitOf(_, ident, iterable, body) => {
            max_ident_stamp_in_expression(iterable)
                .max(ident.stamp())
                .max(max_ident_stamp_in_block(body))
        }
        StatementDesc::IntSwitch(test, clauses, default) => {
            let mut max_stamp = max_ident_stamp_in_expression(test);
            for (_, clause) in clauses {
                max_stamp = max_stamp.max(max_ident_stamp_in_block(&clause.body));
            }
            if let Some(default) = default {
                max_stamp = max_stamp.max(max_ident_stamp_in_block(default));
            }
            max_stamp
        }
        StatementDesc::StringSwitch(test, clauses, default) => {
            let mut max_stamp = max_ident_stamp_in_expression(test);
            for clause in clauses {
                max_stamp = max_stamp.max(max_ident_stamp_in_block(&clause.clause.body));
            }
            if let Some(default) = default {
                max_stamp = max_stamp.max(max_ident_stamp_in_block(default));
            }
            max_stamp
        }
        StatementDesc::Try(body, catch, finally) => {
            let mut max_stamp = max_ident_stamp_in_block(body);
            if let Some((ident, catch_block)) = catch {
                max_stamp = max_stamp
                    .max(ident.stamp())
                    .max(max_ident_stamp_in_block(catch_block));
            }
            if let Some(finally) = finally {
                max_stamp = max_stamp.max(max_ident_stamp_in_block(finally));
            }
            max_stamp
        }
        StatementDesc::Debugger | StatementDesc::Break(_) | StatementDesc::Continue(_) => 0,
    }
}

pub(crate) fn max_ident_stamp_in_expression(expr: &Expression) -> i32 {
    match &expr.desc {
        ExpressionDesc::Var(VIdent::Id(ident)) => ident.stamp(),
        ExpressionDesc::Var(VIdent::Qualified(module, _)) => module.id.stamp(),
        ExpressionDesc::Length(inner, _)
        | ExpressionDesc::IsNullOrUndefined(inner)
        | ExpressionDesc::Typeof(inner)
        | ExpressionDesc::JsNot(inner)
        | ExpressionDesc::JsBnot(inner)
        | ExpressionDesc::CamlBlockTag(inner, _)
        | ExpressionDesc::OptionalBlock(inner, _)
        | ExpressionDesc::Await(inner)
        | ExpressionDesc::Spread(inner)
        | ExpressionDesc::RecordRest(_, inner) => max_ident_stamp_in_expression(inner),
        ExpressionDesc::StringAppend(left, right)
        | ExpressionDesc::In(left, right)
        | ExpressionDesc::Seq(left, right)
        | ExpressionDesc::Bin(_, left, right)
        | ExpressionDesc::FlatCall(left, right)
        | ExpressionDesc::StringIndex(left, right)
        | ExpressionDesc::ArrayIndex(left, right) => {
            max_ident_stamp_in_expression(left).max(max_ident_stamp_in_expression(right))
        }
        ExpressionDesc::Cond(test, consequent, alternate) => max_ident_stamp_in_expression(test)
            .max(max_ident_stamp_in_expression(consequent))
            .max(max_ident_stamp_in_expression(alternate)),
        ExpressionDesc::Call(func, args, _) => args
            .iter()
            .fold(max_ident_stamp_in_expression(func), |max_stamp, arg| {
                max_stamp.max(max_ident_stamp_in_expression(arg))
            }),
        ExpressionDesc::TaggedTemplate(tag, strings, values) => {
            let mut max_stamp = max_ident_stamp_in_expression(tag);
            for string in strings {
                max_stamp = max_stamp.max(max_ident_stamp_in_expression(string));
            }
            for value in values {
                max_stamp = max_stamp.max(max_ident_stamp_in_expression(value));
            }
            max_stamp
        }
        ExpressionDesc::StaticIndex(target, _, _) => max_ident_stamp_in_expression(target),
        ExpressionDesc::New(target, args) => {
            let mut max_stamp = max_ident_stamp_in_expression(target);
            if let Some(args) = args {
                for arg in args {
                    max_stamp = max_stamp.max(max_ident_stamp_in_expression(arg));
                }
            }
            max_stamp
        }
        ExpressionDesc::Fun { params, body, .. } => params
            .iter()
            .fold(max_ident_stamp_in_block(body), |max_stamp, param| {
                max_stamp.max(param.stamp())
            }),
        ExpressionDesc::Array(items, _) => items.iter().fold(0, |max_stamp, item| {
            max_stamp.max(max_ident_stamp_in_expression(item))
        }),
        ExpressionDesc::CamlBlock(items, _, _) => items.iter().fold(0, |max_stamp, item| {
            max_stamp.max(max_ident_stamp_in_expression(item))
        }),
        ExpressionDesc::Object(dup, props) => {
            let mut max_stamp = dup
                .as_ref()
                .map(|dup| max_ident_stamp_in_expression(dup))
                .unwrap_or(0);
            for (_, value) in props {
                max_stamp = max_stamp.max(max_ident_stamp_in_expression(value));
            }
            max_stamp
        }
        ExpressionDesc::Bool(_)
        | ExpressionDesc::Str { .. }
        | ExpressionDesc::RawJsCode(_)
        | ExpressionDesc::Number(_)
        | ExpressionDesc::Undefined { .. }
        | ExpressionDesc::Null => 0,
    }
}

pub(crate) fn resolve_export_alias(
    export: &Ident,
    aliases: &HashMap<Ident, Ident>,
    declared: &HashSet<Ident>,
) -> Ident {
    let mut current = export.clone();
    let mut seen = HashSet::new();

    while let Some(target) = aliases.get(&current) {
        if target.name() != export.name()
            || !declared.contains(target)
            || !seen.insert(current.clone())
        {
            break;
        }
        current = target.clone();
    }

    current
}

#[derive(Debug)]
pub(crate) struct ExtractedExports {
    pub(crate) exports: Vec<Ident>,
    pub(crate) values: Vec<Expression>,
}

pub(crate) fn extract_toplevel_exports(
    expr: Expression,
    block: &mut Block,
) -> Option<ExtractedExports> {
    let Expression {
        source_loc,
        desc,
        comment,
    } = expr;
    match desc {
        ExpressionDesc::CamlBlock(values, _, TagInfo::ModuleExport(exports)) => {
            debug_assert_eq!(
                exports.len(),
                values.len(),
                "module export idents and payloads must stay aligned"
            );
            Some(ExtractedExports { exports, values })
        }
        ExpressionDesc::Undefined { .. } => None,
        ExpressionDesc::Seq(left, right) => {
            let mut right_block = Vec::new();
            if let Some(exports) = extract_toplevel_exports((*right).clone(), &mut right_block) {
                push_effect_expression(block, *left);
                block.extend(right_block);
                Some(exports)
            } else {
                push_effect_expression(
                    block,
                    Expression {
                        source_loc,
                        desc: ExpressionDesc::Seq(left, right),
                        comment,
                    },
                );
                None
            }
        }
        other => {
            push_effect_expression(
                block,
                Expression {
                    source_loc,
                    desc: other,
                    comment,
                },
            );
            None
        }
    }
}

pub(crate) fn can_reuse_existing_undefined_export_binding(block: &Block, export: &Ident) -> bool {
    let flattened = flatten_toplevel_block_refs(block);
    let Some(export_index) = flattened.iter().position(|stmt| {
        matches!(
            &stmt.desc,
            StatementDesc::Variable(VariableDeclaration { ident, .. }) if ident.same(export)
        )
    }) else {
        return false;
    };

    flattened[export_index + 1..]
        .iter()
        .all(|stmt| statement_allows_undefined_export_reuse(*stmt))
}

pub(crate) fn insert_rebound_export_before_equivalent_later_binding(
    block: &mut Block,
    export: &Ident,
    value: &Expression,
    later_exports: &[Ident],
) -> Option<Ident> {
    if !matches!(
        value.desc,
        ExpressionDesc::Number(_)
            | ExpressionDesc::Str { .. }
            | ExpressionDesc::Bool(_)
            | ExpressionDesc::Undefined { .. }
            | ExpressionDesc::Null
    ) {
        return None;
    }

    let insert_index = block.iter().position(|stmt| match &stmt.desc {
        StatementDesc::Variable(VariableDeclaration {
            ident,
            value: Some(initializer),
            ..
        }) => {
            later_exports.iter().any(|later| later.same(ident))
                && ocaml_eq_expression(initializer, value)
        }
        _ => false,
    })?;

    if !block[insert_index..].iter().all(|stmt| match &stmt.desc {
        StatementDesc::Variable(VariableDeclaration {
            ident,
            value: Some(initializer),
            ..
        }) => {
            later_exports.iter().any(|later| later.same(ident))
                && ocaml_eq_expression(initializer, value)
        }
        _ => false,
    }) {
        return None;
    }

    block.insert(
        insert_index,
        Statement::variable(VariableDeclaration {
            ident: export.clone(),
            value: Some(value.clone()),
            property: LetKind::Strict,
            ident_info: IdentInfo::default(),
        }),
    );
    Some(export.clone())
}

pub(crate) fn reusable_same_name_export_binding(
    block: &Block,
    export: &Ident,
    value: &Expression,
) -> Option<Ident> {
    let flattened_refs = flatten_toplevel_block_refs(block);
    reusable_same_name_export_binding_ref(&flattened_refs, export, value)
}

fn reusable_same_name_export_binding_ref(
    block: &[&Statement],
    export: &Ident,
    value: &Expression,
) -> Option<Ident> {
    block.iter().find_map(|stmt| match &stmt.desc {
        StatementDesc::Variable(VariableDeclaration {
            ident,
            value: Some(initializer),
            property,
            ..
        }) if ident.name() == export.name()
            && !ident.same(export)
            && !matches!(property, LetKind::Variable)
            && same_reusable_export_value(&initializer, value) =>
        {
            Some(ident.clone())
        }
        _ => None,
    })
}

pub(crate) fn same_reusable_export_value(left: &Expression, right: &Expression) -> bool {
    match (&left.desc, &right.desc) {
        (ExpressionDesc::Var(left_ident), ExpressionDesc::Var(right_ident)) => {
            left_ident == right_ident
        }
        (
            ExpressionDesc::StaticIndex(left_target, left_field, left_pos),
            ExpressionDesc::StaticIndex(right_target, right_field, right_pos),
        ) => {
            left_field == right_field
                && left_pos == right_pos
                && same_reusable_export_value(left_target, right_target)
        }
        _ => false,
    }
}

pub(crate) fn push_effect_expression(block: &mut Block, expr: Expression) {
    match expr.desc {
        ExpressionDesc::Seq(left, right) => {
            push_effect_expression(block, *left);
            push_effect_expression(block, *right);
        }
        _ if js_expr_no_side_effects(&expr) => {}
        _ => block.push(Statement::exp(expr)),
    }
}

/// Mirrors OCaml's `S.exp` (js_stmt_make.ml:45-53): keeps pure expressions as
/// `Exp` statements except for literal `Number`/`Undefined` payloads, which
/// are silently dropped (along with the Number/Undefined side of a top-level
/// `Seq`). Use this wherever OCaml would construct `S.exp e` — e.g. the
/// empty-branches reduction inside `S.if_` (js_stmt_make.ml:242), and the
/// all-empty switch collapses. `push_effect_expression` is more aggressive and
/// strips every side-effect-free expression, which matches OCaml's
/// `output_of_expression` (js_output.ml:42-52) but not `S.exp`.
pub(crate) fn push_s_exp(block: &mut Block, expr: Expression) {
    let source_loc = expr.source_loc;
    match expr.desc {
        ExpressionDesc::Number(_) | ExpressionDesc::Undefined { .. } => {}
        ExpressionDesc::Seq(left, right) => match (&left.desc, &right.desc) {
            (ExpressionDesc::Number(_) | ExpressionDesc::Undefined { .. }, _) => {
                push_s_exp(block, *right);
            }
            (_, ExpressionDesc::Number(_) | ExpressionDesc::Undefined { .. }) => {
                push_s_exp(block, *left);
            }
            _ => block.push(Statement::exp(Expression {
                source_loc,
                desc: ExpressionDesc::Seq(left, right),
                comment: expr.comment,
            })),
        },
        _ => block.push(Statement::exp(expr)),
    }
}

pub(crate) fn statement_allows_undefined_export_reuse(stmt: &Statement) -> bool {
    match &stmt.desc {
        StatementDesc::Variable(VariableDeclaration { value, .. }) => {
            value.as_ref().is_none_or(|expr| {
                !matches!(expr.desc, ExpressionDesc::Fun { .. }) && js_expr_no_side_effects(expr)
            })
        }
        _ => false,
    }
}
