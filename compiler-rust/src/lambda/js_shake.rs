//! JS IR pass: tree shaking.
//!
//! Removes unused top-level bindings and reorders export aliases to the tail
//! of the program block. Also includes free variable analysis and side-effect
//! checking for JS IR statements and expressions.

use ahash::AHashSet as HashSet;

use crate::ident::Ident;
use crate::js_ir::op::{IdentInfo, Kind, UsedStats};
use crate::js_ir::{
    Block, DepsProgram, Expression, ExpressionDesc, Program, Statement, StatementDesc, VIdent,
    VariableDeclaration,
};
use crate::lambda::lam_compat::LetKind;

use super::js_exp_make::js_expr_no_side_effects;
use super::lam_coercion::same_reusable_export_value;

pub(crate) fn apply_js_shake_pass(mut deps: DepsProgram) -> DepsProgram {
    deps.program = shake_program(deps.program);
    deps
}

pub(crate) fn move_same_name_export_alias_to_export_tail(
    block: &mut Block,
    export: &Ident,
    value: &Expression,
) -> Option<(Expression, LetKind)> {
    let ExpressionDesc::Var(VIdent::Id(target)) = &value.desc else {
        return None;
    };
    if target.name() != export.name() {
        return None;
    }

    // OCaml coerces exports over flattened lambda groups before JS lowering
    // (`compiler/core/lam_coercion.ml:179-199`,
    // `compiler/core/lam_compile_main.ml:220-254`). Keep the Rust-only JS IR
    // scans borrowed until we know we must rewrite, so the read-only path has
    // the same semantics without cloning the full block.
    let (mut flattened, index, replacement, property) = {
        let flattened_refs = flatten_toplevel_block_refs(block);
        let Some((index, initializer, property)) =
            same_name_export_alias_binding_ref(&flattened_refs, target)
        else {
            return None;
        };
        let initializer_kind = same_name_export_initializer_kind_ref(&flattened_refs, initializer);
        // OCaml only substitutes Strict/Alias/StrictOpt simple bindings in
        // `compiler/core/lam_pass_lets_dce.ml:21-23` and
        // `compiler/core/lam_pass_lets_dce.ml:44-72`, then JS dead-code
        // marking gathers use info in one pass
        // (`compiler/core/js_pass_flatten_and_mark_dead.ml:32-91`). If this
        // binding is already outside the tail-movable shapes, the later
        // reference scans cannot make it movable; this is the same
        // `blocked_by_kind` / `blocked_by_variable` rejection below, just
        // before walking large function bodies.
        if matches!(property, LetKind::Variable)
            || matches!(initializer_kind, TailMoveInitializerKind::Other)
        {
            return None;
        }
        let remaining = &flattened_refs[index + 1..];
        let later_initializer_mentions_target =
            later_toplevel_initializer_mentions_ident_ref(remaining, target);
        let prefer_materialized_root =
            tail_move_materialized_root_ident_ref(&flattened_refs, initializer).is_some_and(
                |root| {
                    !root.same(target)
                        && (later_initializer_mentions_target
                            || remaining
                                .iter()
                                .any(|stmt| statement_mentions_ident_anywhere(stmt, &root)))
                },
            );
        let replacement = resolve_tail_move_replacement_expression_ref(
            &flattened_refs,
            initializer,
            target,
            prefer_materialized_root,
        );
        let binding_is_direct_literal = matches!(
            &initializer.desc,
            ExpressionDesc::Number(_)
                | ExpressionDesc::Str { .. }
                | ExpressionDesc::Bool(_)
                | ExpressionDesc::Undefined { .. }
                | ExpressionDesc::Null
        );
        let binding_is_local_alias =
            matches!(&initializer.desc, ExpressionDesc::Var(VIdent::Id(_)));
        let has_later_function_binding = has_later_toplevel_function_binding_ref(remaining);
        let later_function_mentions_target =
            later_toplevel_function_mentions_ident_ref(remaining, target);
        let later_initializer_mentions_target =
            later_toplevel_initializer_mentions_ident_ref(remaining, target);
        // A Literal+Alias binding existing in the block means
        // `compiler/core/lam_pass_lets_dce.ml:121-133` entered the Strict arm
        // and `compiler/core/lam_util.ml:118-124` downgraded to Alias without
        // substituting the value. That is the exact shape OCaml keeps in source
        // order via `compiler/core/lam_coercion.ml:99-121`, so we must not
        // relocate the binding. The Alias-arm substitution path in OCaml always
        // removes the binding, in which case this function never finds a
        // declaration to move.
        let blocked_by_literal_binding =
            matches!(initializer_kind, TailMoveInitializerKind::Literal)
                && !matches!(property, LetKind::Alias);
        let blocked_by_literal_alias_preserved_in_block =
            matches!(initializer_kind, TailMoveInitializerKind::Literal)
                && matches!(property, LetKind::Alias);
        let blocked_by_direct_literal_reuse =
            matches!(initializer_kind, TailMoveInitializerKind::Literal)
                && binding_is_direct_literal
                && later_initializer_mentions_target;
        let blocked_by_literal_alias_without_materialized_root =
            matches!(initializer_kind, TailMoveInitializerKind::Literal)
                && binding_is_local_alias
                && !prefer_materialized_root;
        let blocked_by_later_function_capture = later_function_mentions_target;
        let blocked_by_qualified_binding_before_later_function = has_later_function_binding
            && matches!(initializer_kind, TailMoveInitializerKind::Qualified);
        let blocked_by_variable = matches!(property, LetKind::Variable);
        let blocked_by_kind = matches!(initializer_kind, TailMoveInitializerKind::Other);
        let blocked_by_effects = !js_expr_no_side_effects(&replacement);
        let blocked_by_self_mention = expression_mentions_ident_anywhere(&replacement, target);
        let blocked_by_prior_use = flattened_refs[..index]
            .iter()
            .any(|stmt| statement_mentions_ident_anywhere(stmt, target));
        let has_remaining_use = remaining
            .iter()
            .any(|stmt| statement_mentions_ident_anywhere(stmt, target));
        let blocked_by_unsafe_inline =
            matches!(initializer_kind, TailMoveInitializerKind::Qualified)
                && !qualified_tail_move_uses_are_safe_to_inline_ref(
                    remaining,
                    target,
                    &replacement,
                );
        let blocked_by_later_initializer = later_initializer_mentions_target
            && !matches!(initializer_kind, TailMoveInitializerKind::Literal);
        let blocked_by_later_effect = !later_toplevel_effect_allows_tail_move_ref(
            remaining,
            target,
            initializer_kind,
            &replacement,
            replacement_resolves_to_recursive_function_ref(&flattened_refs, &replacement),
        ) && !(target.same(export)
            && !has_remaining_use
            && ml_module_field_tail_move_replacement(&replacement));
        if blocked_by_variable
            || blocked_by_literal_binding
            || blocked_by_literal_alias_preserved_in_block
            || blocked_by_direct_literal_reuse
            || blocked_by_literal_alias_without_materialized_root
            || blocked_by_later_function_capture
            || blocked_by_qualified_binding_before_later_function
            || blocked_by_kind
            || blocked_by_effects
            || blocked_by_self_mention
            || blocked_by_prior_use
            || blocked_by_unsafe_inline
            || blocked_by_later_initializer
            || blocked_by_later_effect
        {
            return None;
        }

        (
            clone_flattened_block_refs(&flattened_refs),
            index,
            replacement,
            property,
        )
    };

    for stmt in &mut flattened[index + 1..] {
        substitute_export_alias_use_in_statement(stmt, target, &replacement);
    }
    flattened.remove(index);
    *block = flattened;
    Some((replacement, property))
}

pub(crate) fn move_reused_same_name_export_binding_to_export_tail(
    block: &mut Block,
    export: &Ident,
    value: &Expression,
) -> Option<(Expression, LetKind)> {
    // Same OCaml contract as `move_same_name_export_alias_to_export_tail`:
    // export identity decisions come from `compiler/core/lam_coercion.ml:82-121`;
    // this Rust JS-IR pass only preserves the final output shape and clones
    // after the borrowed checks choose a mutation.
    let (mut flattened, index, reused, replacement, property) = {
        let flattened_refs = flatten_toplevel_block_refs(block);
        let Some((index, reused, _initializer, property)) =
            direct_reused_same_name_export_alias_binding_ref(&flattened_refs, export, value)
        else {
            return None;
        };
        let replacement =
            resolve_tail_move_replacement_expression_ref(&flattened_refs, value, reused, false);
        let initializer_kind = same_name_export_initializer_kind_ref(&flattened_refs, &replacement);
        let remaining = &flattened_refs[index + 1..];
        let blocked_by_literal_binding =
            matches!(initializer_kind, TailMoveInitializerKind::Literal)
                && (!matches!(property, LetKind::Alias)
                    || !has_later_toplevel_function_binding_ref(remaining));
        let blocked_by_later_effect = !later_toplevel_effect_allows_tail_move_ref(
            remaining,
            reused,
            initializer_kind,
            &replacement,
            replacement_resolves_to_recursive_function_ref(&flattened_refs, &replacement),
        );
        if matches!(property, LetKind::Variable)
            || blocked_by_literal_binding
            || matches!(initializer_kind, TailMoveInitializerKind::Other)
            || !js_expr_no_side_effects(&replacement)
            || flattened_refs[..index]
                .iter()
                .any(|stmt| statement_mentions_ident_anywhere(stmt, reused))
            || (matches!(initializer_kind, TailMoveInitializerKind::Qualified)
                && !qualified_tail_move_uses_are_safe_to_inline_ref(
                    remaining,
                    reused,
                    &replacement,
                ))
            || later_toplevel_initializer_mentions_ident_ref(remaining, reused)
            || blocked_by_later_effect
        {
            return None;
        }

        (
            clone_flattened_block_refs(&flattened_refs),
            index,
            reused.clone(),
            replacement,
            property,
        )
    };

    for stmt in &mut flattened[index + 1..] {
        substitute_export_alias_use_in_statement(stmt, &reused, &replacement);
    }
    flattened.remove(index);
    *block = flattened;
    Some((replacement, property))
}

fn same_name_export_alias_binding_ref<'a>(
    block: &'a [&'a Statement],
    target: &Ident,
) -> Option<(usize, &'a Expression, LetKind)> {
    block
        .iter()
        .enumerate()
        .find_map(|(index, stmt)| match &stmt.desc {
            StatementDesc::Variable(VariableDeclaration {
                ident,
                value: Some(initializer),
                property,
                ..
            }) if ident.same(target) => Some((index, initializer, *property)),
            _ => None,
        })
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum TailMoveInitializerKind {
    Qualified,
    Function,
    Literal,
    Other,
}

fn same_name_export_initializer_kind_ref(
    block: &[&Statement],
    initializer: &Expression,
) -> TailMoveInitializerKind {
    match &initializer.desc {
        ExpressionDesc::Number(_)
        | ExpressionDesc::Str { .. }
        | ExpressionDesc::Bool(_)
        | ExpressionDesc::Undefined { .. }
        | ExpressionDesc::Null => TailMoveInitializerKind::Literal,
        ExpressionDesc::Var(VIdent::Qualified(_, _)) => TailMoveInitializerKind::Qualified,
        ExpressionDesc::Var(VIdent::Id(target)) => {
            resolve_tail_move_initializer_kind_ref(block, target)
                .unwrap_or(TailMoveInitializerKind::Other)
        }
        _ => TailMoveInitializerKind::Other,
    }
}

pub(crate) fn resolve_tail_move_replacement_expression(
    block: &Block,
    initializer: &Expression,
    rebound: &Ident,
    prefer_materialized_root: bool,
) -> Expression {
    let ExpressionDesc::Var(VIdent::Id(start)) = &initializer.desc else {
        return initializer.clone();
    };

    let mut current = start.clone();
    let mut seen = HashSet::new();

    loop {
        if !seen.insert(current.clone()) {
            return initializer.clone();
        }

        let stmt = match block.iter().find(|stmt| {
            matches!(
                &stmt.desc,
                StatementDesc::Variable(VariableDeclaration { ident, .. }) if ident.same(&current)
            )
        }) {
            Some(stmt) => stmt,
            None => return Expression::var(current),
        };

        let StatementDesc::Variable(VariableDeclaration {
            value: Some(value),
            property,
            ..
        }) = &stmt.desc
        else {
            return Expression::var(current);
        };

        // OCaml's `compiler/core/lam_pass_lets_dce.ml:21-23` only substitutes
        // Strict / Alias / StrictOpt. Stop at a Variable-kind binding
        // (post-eliminate_ref ref); folding through it is unsound because later
        // code may mutate it.
        if matches!(property, LetKind::Variable) {
            return Expression::var(current);
        }

        match &value.desc {
            ExpressionDesc::Fun { .. } => return Expression::var(current),
            ExpressionDesc::Var(VIdent::Qualified(module, field)) => {
                return if prefer_materialized_root && !current.same(rebound) {
                    Expression::var(current)
                } else if current.same(rebound) {
                    Expression::qualified(module.clone(), field.clone())
                } else {
                    Expression::var(current)
                };
            }
            ExpressionDesc::Var(VIdent::Id(next)) if next.name() == current.name() => {
                current = next.clone();
            }
            ExpressionDesc::Number(_)
            | ExpressionDesc::Str { .. }
            | ExpressionDesc::Bool(_)
            | ExpressionDesc::Undefined { .. }
            | ExpressionDesc::Null => {
                return if prefer_materialized_root && !current.same(rebound) {
                    Expression::var(current)
                } else {
                    value.clone()
                };
            }
            _ => return Expression::var(current),
        }
    }
}

fn resolve_tail_move_replacement_expression_ref(
    block: &[&Statement],
    initializer: &Expression,
    rebound: &Ident,
    prefer_materialized_root: bool,
) -> Expression {
    // Borrowed twin of `resolve_tail_move_replacement_expression`, preserving
    // the substitution boundary from `compiler/core/lam_pass_lets_dce.ml:21-23`
    // while avoiding JS statement clones on read-only export checks.
    let ExpressionDesc::Var(VIdent::Id(start)) = &initializer.desc else {
        return initializer.clone();
    };

    let mut current = start.clone();
    let mut seen = HashSet::new();

    loop {
        if !seen.insert(current.clone()) {
            return initializer.clone();
        }

        let stmt = match block.iter().find(|stmt| {
            matches!(
                &stmt.desc,
                StatementDesc::Variable(VariableDeclaration { ident, .. }) if ident.same(&current)
            )
        }) {
            Some(stmt) => stmt,
            None => return Expression::var(current),
        };

        let StatementDesc::Variable(VariableDeclaration {
            value: Some(value),
            property,
            ..
        }) = &stmt.desc
        else {
            return Expression::var(current);
        };

        if matches!(property, LetKind::Variable) {
            return Expression::var(current);
        }

        match &value.desc {
            ExpressionDesc::Fun { .. } => return Expression::var(current),
            ExpressionDesc::Var(VIdent::Qualified(module, field)) => {
                return if prefer_materialized_root && !current.same(rebound) {
                    Expression::var(current)
                } else if current.same(rebound) {
                    Expression::qualified(module.clone(), field.clone())
                } else {
                    Expression::var(current)
                };
            }
            ExpressionDesc::Var(VIdent::Id(next)) if next.name() == current.name() => {
                current = next.clone();
            }
            ExpressionDesc::Number(_)
            | ExpressionDesc::Str { .. }
            | ExpressionDesc::Bool(_)
            | ExpressionDesc::Undefined { .. }
            | ExpressionDesc::Null => {
                return if prefer_materialized_root && !current.same(rebound) {
                    Expression::var(current)
                } else {
                    value.clone()
                };
            }
            _ => return Expression::var(current),
        }
    }
}

fn tail_move_materialized_root_ident_ref(
    block: &[&Statement],
    initializer: &Expression,
) -> Option<Ident> {
    let ExpressionDesc::Var(VIdent::Id(start)) = &initializer.desc else {
        return None;
    };

    let mut current = start.clone();
    let mut seen = HashSet::new();

    loop {
        if !seen.insert(current.clone()) {
            return None;
        }

        let stmt = block.iter().find(|stmt| {
            matches!(
                &stmt.desc,
                StatementDesc::Variable(VariableDeclaration { ident, .. }) if ident.same(&current)
            )
        })?;

        let StatementDesc::Variable(VariableDeclaration {
            value: Some(value), ..
        }) = &stmt.desc
        else {
            return Some(current);
        };

        match &value.desc {
            ExpressionDesc::Var(VIdent::Id(next)) if next.name() == current.name() => {
                current = next.clone();
            }
            _ => return Some(current),
        }
    }
}

pub(crate) fn resolve_tail_move_initializer_kind(
    block: &Block,
    start: &Ident,
) -> Option<TailMoveInitializerKind> {
    let mut current = start.clone();
    let mut seen = HashSet::new();

    loop {
        if !seen.insert(current.clone()) {
            return None;
        }

        let stmt = block.iter().find(|stmt| {
            matches!(
                &stmt.desc,
                StatementDesc::Variable(VariableDeclaration { ident, .. }) if ident.same(&current)
            )
        })?;

        let StatementDesc::Variable(VariableDeclaration {
            value: Some(value), ..
        }) = &stmt.desc
        else {
            return None;
        };

        match &value.desc {
            ExpressionDesc::Fun { .. } => return Some(TailMoveInitializerKind::Function),
            ExpressionDesc::Var(VIdent::Qualified(_, _)) => {
                return Some(TailMoveInitializerKind::Qualified);
            }
            ExpressionDesc::Number(_)
            | ExpressionDesc::Str { .. }
            | ExpressionDesc::Bool(_)
            | ExpressionDesc::Undefined { .. }
            | ExpressionDesc::Null => return Some(TailMoveInitializerKind::Literal),
            ExpressionDesc::Var(VIdent::Id(next)) => current = next.clone(),
            _ => return None,
        }
    }
}

fn resolve_tail_move_initializer_kind_ref(
    block: &[&Statement],
    start: &Ident,
) -> Option<TailMoveInitializerKind> {
    let mut current = start.clone();
    let mut seen = HashSet::new();

    loop {
        if !seen.insert(current.clone()) {
            return None;
        }

        let stmt = block.iter().find(|stmt| {
            matches!(
                &stmt.desc,
                StatementDesc::Variable(VariableDeclaration { ident, .. }) if ident.same(&current)
            )
        })?;

        let StatementDesc::Variable(VariableDeclaration {
            value: Some(value), ..
        }) = &stmt.desc
        else {
            return None;
        };

        match &value.desc {
            ExpressionDesc::Fun { .. } => return Some(TailMoveInitializerKind::Function),
            ExpressionDesc::Var(VIdent::Qualified(_, _)) => {
                return Some(TailMoveInitializerKind::Qualified);
            }
            ExpressionDesc::Number(_)
            | ExpressionDesc::Str { .. }
            | ExpressionDesc::Bool(_)
            | ExpressionDesc::Undefined { .. }
            | ExpressionDesc::Null => return Some(TailMoveInitializerKind::Literal),
            ExpressionDesc::Var(VIdent::Id(next)) => current = next.clone(),
            _ => return None,
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum TailMoveUseContext {
    Other,
    CallCallee,
    NewTarget,
}

fn tail_move_uses_are_safe_to_inline(block: &[Statement], target: &Ident) -> bool {
    block
        .iter()
        .all(|stmt| statement_uses_ident_only_in_tail_move_safe_positions(stmt, target))
}

fn tail_move_uses_are_safe_to_inline_ref(block: &[&Statement], target: &Ident) -> bool {
    block
        .iter()
        .all(|stmt| statement_uses_ident_only_in_tail_move_safe_positions(stmt, target))
}

fn qualified_tail_move_uses_are_safe_to_inline_ref(
    block: &[&Statement],
    target: &Ident,
    replacement: &Expression,
) -> bool {
    same_name_ml_module_field_tail_move_replacement(replacement, target.name())
        || tail_move_uses_are_safe_to_inline_ref(block, target)
}

fn same_name_ml_module_field_tail_move_replacement(
    replacement: &Expression,
    target_name: &str,
) -> bool {
    matches!(
        &replacement.desc,
        ExpressionDesc::Var(VIdent::Qualified(module, Some(field)))
            if field == target_name && module.kind.eq(&Kind::Ml)
    )
}

fn ml_module_field_tail_move_replacement(replacement: &Expression) -> bool {
    matches!(
        &replacement.desc,
        ExpressionDesc::Var(VIdent::Qualified(module, _)) if module.kind.eq(&Kind::Ml)
    )
}

fn later_toplevel_effect_allows_tail_move_ref(
    block: &[&Statement],
    target: &Ident,
    initializer_kind: TailMoveInitializerKind,
    replacement: &Expression,
    replacement_is_recursive_function: bool,
) -> bool {
    if !later_toplevel_effect_statement_ref(block) {
        return true;
    }
    if matches!(initializer_kind, TailMoveInitializerKind::Literal) {
        return true;
    }
    let has_remaining_use = block
        .iter()
        .any(|stmt| statement_mentions_ident_anywhere(stmt, target));
    if !has_remaining_use {
        return matches!(initializer_kind, TailMoveInitializerKind::Function)
            && replacement_is_recursive_function;
    }

    match initializer_kind {
        TailMoveInitializerKind::Function => tail_move_uses_are_safe_to_inline_ref(block, target),
        TailMoveInitializerKind::Qualified => {
            qualified_tail_move_uses_are_safe_to_inline_ref(block, target, replacement)
        }
        TailMoveInitializerKind::Literal | TailMoveInitializerKind::Other => false,
    }
}

fn replacement_resolves_to_recursive_function_ref(
    block: &[&Statement],
    replacement: &Expression,
) -> bool {
    let ExpressionDesc::Var(VIdent::Id(binding)) = &replacement.desc else {
        return false;
    };
    block.iter().any(|stmt| match &stmt.desc {
        StatementDesc::Variable(VariableDeclaration {
            ident,
            value:
                Some(Expression {
                    desc: ExpressionDesc::Fun { body, .. },
                    ..
                }),
            ..
        }) if ident.same(binding) => body
            .iter()
            .any(|stmt| statement_mentions_ident_anywhere(stmt, binding)),
        _ => false,
    })
}

fn statement_uses_ident_only_in_tail_move_safe_positions(stmt: &Statement, target: &Ident) -> bool {
    match &stmt.desc {
        StatementDesc::Block(block) => tail_move_uses_are_safe_to_inline(block, target),
        StatementDesc::Variable(VariableDeclaration { ident, value, .. }) => {
            !ident.same(target)
                && value.as_ref().is_none_or(|value| {
                    expression_uses_ident_only_in_tail_move_safe_positions(
                        value,
                        target,
                        TailMoveUseContext::Other,
                    )
                })
        }
        StatementDesc::Exp(expr) | StatementDesc::Return(expr) | StatementDesc::Throw(expr) => {
            expression_uses_ident_only_in_tail_move_safe_positions(
                expr,
                target,
                TailMoveUseContext::Other,
            )
        }
        StatementDesc::If(cond, then_block, else_block) => {
            expression_uses_ident_only_in_tail_move_safe_positions(
                cond,
                target,
                TailMoveUseContext::Other,
            ) && tail_move_uses_are_safe_to_inline(then_block, target)
                && tail_move_uses_are_safe_to_inline(else_block, target)
        }
        StatementDesc::While(_, cond, body) => {
            expression_uses_ident_only_in_tail_move_safe_positions(
                cond,
                target,
                TailMoveUseContext::Other,
            ) && tail_move_uses_are_safe_to_inline(body, target)
        }
        StatementDesc::ForRange(_, start, finish, loop_ident, _, body) => {
            !loop_ident.same(target)
                && start.as_ref().is_none_or(|expr| {
                    expression_uses_ident_only_in_tail_move_safe_positions(
                        expr,
                        target,
                        TailMoveUseContext::Other,
                    )
                })
                && expression_uses_ident_only_in_tail_move_safe_positions(
                    finish,
                    target,
                    TailMoveUseContext::Other,
                )
                && tail_move_uses_are_safe_to_inline(body, target)
        }
        StatementDesc::ForOf(_, loop_ident, iterable, body)
        | StatementDesc::ForAwaitOf(_, loop_ident, iterable, body) => {
            !loop_ident.same(target)
                && expression_uses_ident_only_in_tail_move_safe_positions(
                    iterable,
                    target,
                    TailMoveUseContext::Other,
                )
                && tail_move_uses_are_safe_to_inline(body, target)
        }
        StatementDesc::IntSwitch(test, clauses, default) => {
            expression_uses_ident_only_in_tail_move_safe_positions(
                test,
                target,
                TailMoveUseContext::Other,
            ) && clauses
                .iter()
                .all(|(_, clause)| tail_move_uses_are_safe_to_inline(&clause.body, target))
                && default
                    .as_ref()
                    .is_none_or(|block| tail_move_uses_are_safe_to_inline(block, target))
        }
        StatementDesc::StringSwitch(test, clauses, default) => {
            expression_uses_ident_only_in_tail_move_safe_positions(
                test,
                target,
                TailMoveUseContext::Other,
            ) && clauses
                .iter()
                .all(|clause| tail_move_uses_are_safe_to_inline(&clause.clause.body, target))
                && default
                    .as_ref()
                    .is_none_or(|block| tail_move_uses_are_safe_to_inline(block, target))
        }
        StatementDesc::Try(body, catch, finally) => {
            tail_move_uses_are_safe_to_inline(body, target)
                && catch.as_ref().is_none_or(|(catch_ident, block)| {
                    !catch_ident.same(target) && tail_move_uses_are_safe_to_inline(block, target)
                })
                && finally
                    .as_ref()
                    .is_none_or(|block| tail_move_uses_are_safe_to_inline(block, target))
        }
        StatementDesc::Debugger | StatementDesc::Break(_) | StatementDesc::Continue(_) => true,
    }
}

fn expression_uses_ident_only_in_tail_move_safe_positions(
    expr: &Expression,
    target: &Ident,
    context: TailMoveUseContext,
) -> bool {
    match &expr.desc {
        ExpressionDesc::Var(VIdent::Id(ident)) => {
            !ident.same(target)
                || matches!(
                    context,
                    TailMoveUseContext::CallCallee | TailMoveUseContext::NewTarget
                )
        }
        ExpressionDesc::Var(VIdent::Qualified(_, _))
        | ExpressionDesc::Bool(_)
        | ExpressionDesc::Str { .. }
        | ExpressionDesc::Number(_)
        | ExpressionDesc::Undefined { .. }
        | ExpressionDesc::Null
        | ExpressionDesc::RawJsCode(_) => true,
        ExpressionDesc::Length(inner, _)
        | ExpressionDesc::IsNullOrUndefined(inner)
        | ExpressionDesc::Typeof(inner)
        | ExpressionDesc::JsNot(inner)
        | ExpressionDesc::JsBnot(inner)
        | ExpressionDesc::Spread(inner)
        | ExpressionDesc::RecordRest(_, inner)
        | ExpressionDesc::Await(inner)
        | ExpressionDesc::OptionalBlock(inner, _)
        | ExpressionDesc::StaticIndex(inner, _, _)
        | ExpressionDesc::CamlBlockTag(inner, _) => {
            expression_uses_ident_only_in_tail_move_safe_positions(
                inner,
                target,
                TailMoveUseContext::Other,
            )
        }
        ExpressionDesc::StringAppend(left, right)
        | ExpressionDesc::In(left, right)
        | ExpressionDesc::Seq(left, right)
        | ExpressionDesc::Bin(_, left, right)
        | ExpressionDesc::StringIndex(left, right)
        | ExpressionDesc::ArrayIndex(left, right) => {
            expression_uses_ident_only_in_tail_move_safe_positions(
                left,
                target,
                TailMoveUseContext::Other,
            ) && expression_uses_ident_only_in_tail_move_safe_positions(
                right,
                target,
                TailMoveUseContext::Other,
            )
        }
        ExpressionDesc::FlatCall(left, right) => {
            expression_uses_ident_only_in_tail_move_safe_positions(
                left,
                target,
                TailMoveUseContext::CallCallee,
            ) && expression_uses_ident_only_in_tail_move_safe_positions(
                right,
                target,
                TailMoveUseContext::Other,
            )
        }
        ExpressionDesc::Cond(test, consequent, alternate) => {
            expression_uses_ident_only_in_tail_move_safe_positions(
                test,
                target,
                TailMoveUseContext::Other,
            ) && expression_uses_ident_only_in_tail_move_safe_positions(
                consequent,
                target,
                TailMoveUseContext::Other,
            ) && expression_uses_ident_only_in_tail_move_safe_positions(
                alternate,
                target,
                TailMoveUseContext::Other,
            )
        }
        ExpressionDesc::Call(func, args, _) => {
            expression_uses_ident_only_in_tail_move_safe_positions(
                func,
                target,
                TailMoveUseContext::CallCallee,
            ) && args.iter().all(|arg| {
                expression_uses_ident_only_in_tail_move_safe_positions(
                    arg,
                    target,
                    TailMoveUseContext::Other,
                )
            })
        }
        ExpressionDesc::TaggedTemplate(tag, strings, values) => {
            expression_uses_ident_only_in_tail_move_safe_positions(
                tag,
                target,
                TailMoveUseContext::CallCallee,
            ) && strings.iter().all(|expr| {
                expression_uses_ident_only_in_tail_move_safe_positions(
                    expr,
                    target,
                    TailMoveUseContext::Other,
                )
            }) && values.iter().all(|expr| {
                expression_uses_ident_only_in_tail_move_safe_positions(
                    expr,
                    target,
                    TailMoveUseContext::Other,
                )
            })
        }
        ExpressionDesc::New(func, args) => {
            expression_uses_ident_only_in_tail_move_safe_positions(
                func,
                target,
                TailMoveUseContext::NewTarget,
            ) && args.as_ref().is_none_or(|args| {
                args.iter().all(|arg| {
                    expression_uses_ident_only_in_tail_move_safe_positions(
                        arg,
                        target,
                        TailMoveUseContext::Other,
                    )
                })
            })
        }
        ExpressionDesc::Fun { body, .. } => tail_move_uses_are_safe_to_inline(body, target),
        ExpressionDesc::Array(items, _) => items.iter().all(|item| {
            expression_uses_ident_only_in_tail_move_safe_positions(
                item,
                target,
                TailMoveUseContext::Other,
            )
        }),
        ExpressionDesc::CamlBlock(items, _, _) => items.iter().all(|item| {
            expression_uses_ident_only_in_tail_move_safe_positions(
                item,
                target,
                TailMoveUseContext::Other,
            )
        }),
        ExpressionDesc::Object(dup, props) => {
            dup.as_ref().is_none_or(|expr| {
                expression_uses_ident_only_in_tail_move_safe_positions(
                    expr,
                    target,
                    TailMoveUseContext::Other,
                )
            }) && props.iter().all(|(_, value)| {
                expression_uses_ident_only_in_tail_move_safe_positions(
                    value,
                    target,
                    TailMoveUseContext::Other,
                )
            })
        }
    }
}

fn direct_reused_same_name_export_alias_binding_ref<'a>(
    block: &'a [&'a Statement],
    export: &Ident,
    value: &Expression,
) -> Option<(usize, &'a Ident, &'a Expression, LetKind)> {
    block
        .iter()
        .enumerate()
        .find_map(|(index, stmt)| match &stmt.desc {
            StatementDesc::Variable(VariableDeclaration {
                ident,
                value: Some(initializer),
                property,
                ..
            }) if ident.name() == export.name()
                && same_reusable_export_value(initializer, value) =>
            {
                Some((index, ident, initializer, *property))
            }
            _ => None,
        })
}

pub(crate) fn keeps_declared_same_name_reusable_export_binding(
    block: &Block,
    export: &Ident,
    value: &Expression,
) -> bool {
    let flattened_refs = flatten_toplevel_block_refs(block);
    direct_reused_same_name_export_alias_binding_ref(&flattened_refs, export, value).is_some_and(
        |(_, ident, _, property)| ident.same(export) && !matches!(property, LetKind::Variable),
    )
}

fn has_later_toplevel_function_binding_ref(block: &[&Statement]) -> bool {
    block.iter().any(|stmt| {
        matches!(
            &stmt.desc,
            StatementDesc::Variable(VariableDeclaration {
                value: Some(Expression {
                    desc: ExpressionDesc::Fun { .. },
                    ..
                }),
                ..
            })
        )
    })
}

fn later_toplevel_function_mentions_ident_ref(block: &[&Statement], target: &Ident) -> bool {
    block.iter().any(|stmt| match &stmt.desc {
        StatementDesc::Variable(VariableDeclaration {
            value:
                Some(Expression {
                    desc: ExpressionDesc::Fun { .. },
                    ..
                }),
            ..
        }) => statement_mentions_ident_anywhere(stmt, target),
        _ => false,
    })
}

fn later_toplevel_initializer_mentions_ident_ref(block: &[&Statement], target: &Ident) -> bool {
    block.iter().any(|stmt| match &stmt.desc {
        StatementDesc::Variable(VariableDeclaration {
            value: Some(value), ..
        }) => expression_mentions_ident_outside_nested_functions(value, target),
        _ => false,
    })
}

fn later_toplevel_effect_statement_ref(block: &[&Statement]) -> bool {
    block.iter().any(|stmt| statement_has_toplevel_effect(stmt))
}

fn statement_has_toplevel_effect(stmt: &Statement) -> bool {
    match &stmt.desc {
        StatementDesc::Variable(VariableDeclaration { value, .. }) => value
            .as_ref()
            .is_some_and(|expr| !js_expr_no_side_effects(expr)),
        _ => !js_statement_no_side_effects(stmt),
    }
}

fn expression_mentions_ident_outside_nested_functions(expr: &Expression, target: &Ident) -> bool {
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
        | ExpressionDesc::RecordRest(_, inner)
        | ExpressionDesc::Await(inner)
        | ExpressionDesc::OptionalBlock(inner, _)
        | ExpressionDesc::StaticIndex(inner, _, _)
        | ExpressionDesc::CamlBlockTag(inner, _)
        | ExpressionDesc::New(inner, None) => {
            expression_mentions_ident_outside_nested_functions(inner, target)
        }
        ExpressionDesc::In(left, right)
        | ExpressionDesc::StringAppend(left, right)
        | ExpressionDesc::Seq(left, right)
        | ExpressionDesc::Bin(_, left, right)
        | ExpressionDesc::FlatCall(left, right)
        | ExpressionDesc::StringIndex(left, right)
        | ExpressionDesc::ArrayIndex(left, right) => {
            expression_mentions_ident_outside_nested_functions(left, target)
                || expression_mentions_ident_outside_nested_functions(right, target)
        }
        ExpressionDesc::Cond(test, consequent, alternate) => {
            expression_mentions_ident_outside_nested_functions(test, target)
                || expression_mentions_ident_outside_nested_functions(consequent, target)
                || expression_mentions_ident_outside_nested_functions(alternate, target)
        }
        ExpressionDesc::Call(func, args, _) => {
            expression_mentions_ident_outside_nested_functions(func, target)
                || args
                    .iter()
                    .any(|arg| expression_mentions_ident_outside_nested_functions(arg, target))
        }
        ExpressionDesc::TaggedTemplate(tag, strings, values) => {
            expression_mentions_ident_outside_nested_functions(tag, target)
                || strings
                    .iter()
                    .any(|expr| expression_mentions_ident_outside_nested_functions(expr, target))
                || values
                    .iter()
                    .any(|expr| expression_mentions_ident_outside_nested_functions(expr, target))
        }
        ExpressionDesc::New(func, Some(args)) => {
            expression_mentions_ident_outside_nested_functions(func, target)
                || args
                    .iter()
                    .any(|arg| expression_mentions_ident_outside_nested_functions(arg, target))
        }
        ExpressionDesc::Fun { .. } => false,
        ExpressionDesc::Array(items, _) => items
            .iter()
            .any(|item| expression_mentions_ident_outside_nested_functions(item, target)),
        ExpressionDesc::CamlBlock(items, _, _) => items
            .iter()
            .any(|item| expression_mentions_ident_outside_nested_functions(item, target)),
        ExpressionDesc::Object(dup, props) => {
            dup.as_deref()
                .is_some_and(|dup| expression_mentions_ident_outside_nested_functions(dup, target))
                || props.iter().any(|(_, value)| {
                    expression_mentions_ident_outside_nested_functions(value, target)
                })
        }
    }
}

fn substitute_export_alias_use_in_statement(
    stmt: &mut Statement,
    target: &Ident,
    replacement: &Expression,
) {
    match &mut stmt.desc {
        StatementDesc::Block(block) => {
            for stmt in block {
                substitute_export_alias_use_in_statement(stmt, target, replacement);
            }
        }
        StatementDesc::Variable(decl) => {
            if let Some(value) = &mut decl.value {
                substitute_export_alias_use_in_expression(value, target, replacement);
            }
        }
        StatementDesc::Exp(expr) | StatementDesc::Return(expr) | StatementDesc::Throw(expr) => {
            substitute_export_alias_use_in_expression(expr, target, replacement);
        }
        StatementDesc::If(cond, then_block, else_block) => {
            substitute_export_alias_use_in_expression(cond, target, replacement);
            for stmt in then_block {
                substitute_export_alias_use_in_statement(stmt, target, replacement);
            }
            for stmt in else_block {
                substitute_export_alias_use_in_statement(stmt, target, replacement);
            }
        }
        StatementDesc::While(_, cond, body) => {
            substitute_export_alias_use_in_expression(cond, target, replacement);
            for stmt in body {
                substitute_export_alias_use_in_statement(stmt, target, replacement);
            }
        }
        StatementDesc::ForRange(_, start, finish, ident, _, body) => {
            if !ident.same(target) {
                if let Some(start) = start {
                    substitute_export_alias_use_in_expression(start, target, replacement);
                }
                substitute_export_alias_use_in_expression(finish, target, replacement);
                for stmt in body {
                    substitute_export_alias_use_in_statement(stmt, target, replacement);
                }
            }
        }
        StatementDesc::ForOf(_, ident, iterable, body)
        | StatementDesc::ForAwaitOf(_, ident, iterable, body) => {
            if !ident.same(target) {
                substitute_export_alias_use_in_expression(iterable, target, replacement);
                for stmt in body {
                    substitute_export_alias_use_in_statement(stmt, target, replacement);
                }
            }
        }
        StatementDesc::IntSwitch(test, clauses, default) => {
            substitute_export_alias_use_in_expression(test, target, replacement);
            for (_, clause) in clauses {
                for stmt in &mut clause.body {
                    substitute_export_alias_use_in_statement(stmt, target, replacement);
                }
            }
            if let Some(default) = default {
                for stmt in default {
                    substitute_export_alias_use_in_statement(stmt, target, replacement);
                }
            }
        }
        StatementDesc::StringSwitch(test, clauses, default) => {
            substitute_export_alias_use_in_expression(test, target, replacement);
            for clause in clauses {
                for stmt in &mut clause.clause.body {
                    substitute_export_alias_use_in_statement(stmt, target, replacement);
                }
            }
            if let Some(default) = default {
                for stmt in default {
                    substitute_export_alias_use_in_statement(stmt, target, replacement);
                }
            }
        }
        StatementDesc::Try(body, catch, finally) => {
            for stmt in body {
                substitute_export_alias_use_in_statement(stmt, target, replacement);
            }
            if let Some((catch_ident, block)) = catch {
                if !catch_ident.same(target) {
                    for stmt in block {
                        substitute_export_alias_use_in_statement(stmt, target, replacement);
                    }
                }
            }
            if let Some(block) = finally {
                for stmt in block {
                    substitute_export_alias_use_in_statement(stmt, target, replacement);
                }
            }
        }
        StatementDesc::Debugger | StatementDesc::Break(_) | StatementDesc::Continue(_) => {}
    }
}

fn substitute_export_alias_use_in_expression(
    expr: &mut Expression,
    target: &Ident,
    replacement: &Expression,
) {
    match &mut expr.desc {
        ExpressionDesc::Var(VIdent::Id(ident)) if ident.same(target) => {
            *expr = replacement.clone();
        }
        ExpressionDesc::Var(VIdent::Id(_))
        | ExpressionDesc::Var(VIdent::Qualified(_, _))
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
        | ExpressionDesc::RecordRest(_, inner)
        | ExpressionDesc::Await(inner)
        | ExpressionDesc::OptionalBlock(inner, _)
        | ExpressionDesc::StaticIndex(inner, _, _)
        | ExpressionDesc::CamlBlockTag(inner, _)
        | ExpressionDesc::New(inner, None) => {
            substitute_export_alias_use_in_expression(inner, target, replacement);
        }
        ExpressionDesc::In(left, right)
        | ExpressionDesc::StringAppend(left, right)
        | ExpressionDesc::Seq(left, right)
        | ExpressionDesc::Bin(_, left, right)
        | ExpressionDesc::FlatCall(left, right)
        | ExpressionDesc::StringIndex(left, right)
        | ExpressionDesc::ArrayIndex(left, right) => {
            substitute_export_alias_use_in_expression(left, target, replacement);
            substitute_export_alias_use_in_expression(right, target, replacement);
        }
        ExpressionDesc::Cond(test, consequent, alternate) => {
            substitute_export_alias_use_in_expression(test, target, replacement);
            substitute_export_alias_use_in_expression(consequent, target, replacement);
            substitute_export_alias_use_in_expression(alternate, target, replacement);
        }
        ExpressionDesc::Call(func, args, _) => {
            substitute_export_alias_use_in_expression(func, target, replacement);
            for arg in args {
                substitute_export_alias_use_in_expression(arg, target, replacement);
            }
        }
        ExpressionDesc::TaggedTemplate(tag, strings, values) => {
            substitute_export_alias_use_in_expression(tag, target, replacement);
            for string in strings {
                substitute_export_alias_use_in_expression(string, target, replacement);
            }
            for value in values {
                substitute_export_alias_use_in_expression(value, target, replacement);
            }
        }
        ExpressionDesc::New(func, Some(args)) => {
            substitute_export_alias_use_in_expression(func, target, replacement);
            for arg in args {
                substitute_export_alias_use_in_expression(arg, target, replacement);
            }
        }
        ExpressionDesc::Fun { params, body, .. } => {
            if !params.iter().any(|param| param.same(target)) {
                for stmt in body {
                    substitute_export_alias_use_in_statement(stmt, target, replacement);
                }
            }
        }
        ExpressionDesc::Array(items, _) => {
            for item in items {
                substitute_export_alias_use_in_expression(item, target, replacement);
            }
        }
        ExpressionDesc::CamlBlock(items, _, _) => {
            for item in items {
                substitute_export_alias_use_in_expression(item, target, replacement);
            }
        }
        ExpressionDesc::Object(dup, props) => {
            if let Some(dup) = dup {
                substitute_export_alias_use_in_expression(dup, target, replacement);
            }
            for (_, value) in props {
                substitute_export_alias_use_in_expression(value, target, replacement);
            }
        }
    }
}

pub(crate) fn statement_mentions_ident_anywhere(stmt: &Statement, target: &Ident) -> bool {
    match &stmt.desc {
        StatementDesc::Block(block) => block
            .iter()
            .any(|stmt| statement_mentions_ident_anywhere(stmt, target)),
        StatementDesc::Variable(VariableDeclaration { value, .. }) => value
            .as_ref()
            .is_some_and(|value| expression_mentions_ident_anywhere(value, target)),
        StatementDesc::Exp(expr) | StatementDesc::Return(expr) | StatementDesc::Throw(expr) => {
            expression_mentions_ident_anywhere(expr, target)
        }
        StatementDesc::If(cond, then_block, else_block) => {
            expression_mentions_ident_anywhere(cond, target)
                || then_block
                    .iter()
                    .any(|stmt| statement_mentions_ident_anywhere(stmt, target))
                || else_block
                    .iter()
                    .any(|stmt| statement_mentions_ident_anywhere(stmt, target))
        }
        StatementDesc::While(_, cond, body) => {
            expression_mentions_ident_anywhere(cond, target)
                || body
                    .iter()
                    .any(|stmt| statement_mentions_ident_anywhere(stmt, target))
        }
        StatementDesc::ForRange(_, start, finish, ident, _, body) => {
            !ident.same(target)
                && (start
                    .as_ref()
                    .is_some_and(|start| expression_mentions_ident_anywhere(start, target))
                    || expression_mentions_ident_anywhere(finish, target)
                    || body
                        .iter()
                        .any(|stmt| statement_mentions_ident_anywhere(stmt, target)))
        }
        StatementDesc::ForOf(_, ident, iterable, body)
        | StatementDesc::ForAwaitOf(_, ident, iterable, body) => {
            !ident.same(target)
                && (expression_mentions_ident_anywhere(iterable, target)
                    || body
                        .iter()
                        .any(|stmt| statement_mentions_ident_anywhere(stmt, target)))
        }
        StatementDesc::IntSwitch(test, clauses, default) => {
            expression_mentions_ident_anywhere(test, target)
                || clauses.iter().any(|(_, clause)| {
                    clause
                        .body
                        .iter()
                        .any(|stmt| statement_mentions_ident_anywhere(stmt, target))
                })
                || default.as_ref().is_some_and(|block| {
                    block
                        .iter()
                        .any(|stmt| statement_mentions_ident_anywhere(stmt, target))
                })
        }
        StatementDesc::StringSwitch(test, clauses, default) => {
            expression_mentions_ident_anywhere(test, target)
                || clauses.iter().any(|clause| {
                    clause
                        .clause
                        .body
                        .iter()
                        .any(|stmt| statement_mentions_ident_anywhere(stmt, target))
                })
                || default.as_ref().is_some_and(|block| {
                    block
                        .iter()
                        .any(|stmt| statement_mentions_ident_anywhere(stmt, target))
                })
        }
        StatementDesc::Try(body, catch, finally) => {
            body.iter()
                .any(|stmt| statement_mentions_ident_anywhere(stmt, target))
                || catch.as_ref().is_some_and(|(ident, block)| {
                    !ident.same(target)
                        && block
                            .iter()
                            .any(|stmt| statement_mentions_ident_anywhere(stmt, target))
                })
                || finally.as_ref().is_some_and(|block| {
                    block
                        .iter()
                        .any(|stmt| statement_mentions_ident_anywhere(stmt, target))
                })
        }
        StatementDesc::Debugger | StatementDesc::Break(_) | StatementDesc::Continue(_) => false,
    }
}

fn expression_mentions_ident_anywhere(expr: &Expression, target: &Ident) -> bool {
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
        | ExpressionDesc::RecordRest(_, inner)
        | ExpressionDesc::Await(inner)
        | ExpressionDesc::OptionalBlock(inner, _)
        | ExpressionDesc::StaticIndex(inner, _, _)
        | ExpressionDesc::CamlBlockTag(inner, _)
        | ExpressionDesc::New(inner, None) => expression_mentions_ident_anywhere(inner, target),
        ExpressionDesc::In(left, right)
        | ExpressionDesc::StringAppend(left, right)
        | ExpressionDesc::Seq(left, right)
        | ExpressionDesc::Bin(_, left, right)
        | ExpressionDesc::FlatCall(left, right)
        | ExpressionDesc::StringIndex(left, right)
        | ExpressionDesc::ArrayIndex(left, right) => {
            expression_mentions_ident_anywhere(left, target)
                || expression_mentions_ident_anywhere(right, target)
        }
        ExpressionDesc::Cond(test, consequent, alternate) => {
            expression_mentions_ident_anywhere(test, target)
                || expression_mentions_ident_anywhere(consequent, target)
                || expression_mentions_ident_anywhere(alternate, target)
        }
        ExpressionDesc::Call(func, args, _) => {
            expression_mentions_ident_anywhere(func, target)
                || args
                    .iter()
                    .any(|arg| expression_mentions_ident_anywhere(arg, target))
        }
        ExpressionDesc::TaggedTemplate(tag, strings, values) => {
            expression_mentions_ident_anywhere(tag, target)
                || strings
                    .iter()
                    .any(|expr| expression_mentions_ident_anywhere(expr, target))
                || values
                    .iter()
                    .any(|expr| expression_mentions_ident_anywhere(expr, target))
        }
        ExpressionDesc::New(func, Some(args)) => {
            expression_mentions_ident_anywhere(func, target)
                || args
                    .iter()
                    .any(|arg| expression_mentions_ident_anywhere(arg, target))
        }
        ExpressionDesc::Fun { params, body, .. } => {
            !params.iter().any(|param| param.same(target))
                && body
                    .iter()
                    .any(|stmt| statement_mentions_ident_anywhere(stmt, target))
        }
        ExpressionDesc::Array(items, _) => items
            .iter()
            .any(|item| expression_mentions_ident_anywhere(item, target)),
        ExpressionDesc::CamlBlock(items, _, _) => items
            .iter()
            .any(|item| expression_mentions_ident_anywhere(item, target)),
        ExpressionDesc::Object(dup, props) => {
            dup.as_deref()
                .is_some_and(|dup| expression_mentions_ident_anywhere(dup, target))
                || props
                    .iter()
                    .any(|(_, value)| expression_mentions_ident_anywhere(value, target))
        }
    }
}

fn shake_program(mut program: Program) -> Program {
    // OCaml flattens the JS block once, computes the required identifiers over
    // that same list, then folds it to keep live/effectful statements
    // (`compiler/core/js_shake.ml:62-104`). This pass owns the Rust `Program`,
    // so moving statements into that flattened list is functionally equivalent
    // to OCaml's shared-list traversal and avoids cloning the full JS tree.
    program.block = shake_block_owned(std::mem::take(&mut program.block), &program.export_set);
    program
}

fn shake_block_owned(block: Block, export_set: &HashSet<Ident>) -> Block {
    let block = flatten_toplevel_block_owned(block);
    let required = fixed_point_required_idents(&block, export_set);

    block
        .into_iter()
        .filter(|stmt| match &stmt.desc {
            StatementDesc::Variable(VariableDeclaration { ident, value, .. }) => {
                if required.contains(ident) {
                    true
                } else {
                    value
                        .as_ref()
                        .is_some_and(|expr| !js_expr_no_side_effects(expr))
                }
            }
            _ => !js_statement_no_side_effects(stmt),
        })
        .collect()
}

pub(crate) fn flatten_toplevel_block_owned(block: Block) -> Block {
    // Owned flattened traversal: same filtering as OCaml's
    // `Js_analyzer.rev_toplevel_flatten` use in `compiler/core/js_shake.ml:64`,
    // but it moves `Statement`s instead of cloning them because `shake_program`
    // consumes the post-pass `Program`.
    let mut flattened = Vec::with_capacity(block.len());
    flatten_toplevel_block_owned_into(block, &mut flattened);
    flattened
}

pub(crate) fn flatten_toplevel_block_refs(block: &Block) -> Vec<&Statement> {
    // Borrowed flattened traversal. OCaml flattens once and
    // then folds the same list (`compiler/core/js_shake.ml:63-104`); callers
    // that only inspect exports should not pay for cloning a JS block.
    let mut flattened = Vec::with_capacity(block.len());
    flatten_toplevel_block_refs_into(block, &mut flattened);
    flattened
}

fn flatten_toplevel_block_owned_into(block: Block, flattened: &mut Block) {
    for stmt in block {
        let Statement {
            source_loc,
            desc,
            comment,
        } = stmt;
        match desc {
            StatementDesc::Variable(VariableDeclaration {
                ident_info:
                    IdentInfo {
                        used_stats: UsedStats::DeadPure,
                    },
                ..
            })
            | StatementDesc::Variable(VariableDeclaration {
                ident_info:
                    IdentInfo {
                        used_stats: UsedStats::DeadNonPure,
                    },
                value: None,
                ..
            }) => {}
            StatementDesc::Block(inner) => flatten_toplevel_block_owned_into(inner, flattened),
            desc => flattened.push(Statement {
                source_loc,
                desc,
                comment,
            }),
        }
    }
}

fn flatten_toplevel_block_refs_into<'a>(block: &'a Block, flattened: &mut Vec<&'a Statement>) {
    for stmt in block {
        match &stmt.desc {
            StatementDesc::Variable(VariableDeclaration {
                ident_info:
                    IdentInfo {
                        used_stats: UsedStats::DeadPure,
                    },
                ..
            })
            | StatementDesc::Variable(VariableDeclaration {
                ident_info:
                    IdentInfo {
                        used_stats: UsedStats::DeadNonPure,
                    },
                value: None,
                ..
            }) => {}
            StatementDesc::Block(inner) => flatten_toplevel_block_refs_into(inner, flattened),
            _ => flattened.push(stmt),
        }
    }
}

fn clone_flattened_block_refs(block: &[&Statement]) -> Block {
    block.iter().map(|stmt| (*stmt).clone()).collect()
}

fn fixed_point_required_idents(block: &Block, export_set: &HashSet<Ident>) -> HashSet<Ident> {
    let mut required = required_idents(block, export_set, true);
    loop {
        let next = required_idents(block, &required, false);
        if next.len() == required.len() && next.is_subset(&required) {
            return required;
        }
        required = next;
    }
}

fn required_idents(
    block: &Block,
    initial: &HashSet<Ident>,
    count_effect_statements: bool,
) -> HashSet<Ident> {
    let mut required = initial.clone();

    for stmt in block {
        match &stmt.desc {
            StatementDesc::Variable(VariableDeclaration { ident, value, .. }) => {
                if required.contains(ident) {
                    if let Some(value) = value {
                        required.extend(free_variables_of_expression(value));
                    }
                } else if let Some(value) = value {
                    if !js_expr_no_side_effects(value) {
                        required.insert(ident.clone());
                        required.extend(free_variables_of_expression(value));
                    }
                }
            }
            _ => {
                if count_effect_statements && !js_statement_no_side_effects(stmt) {
                    required.extend(free_variables_of_statement(stmt));
                }
            }
        }
    }

    required
}

#[derive(Default)]
struct JsIdentStats {
    used_idents: HashSet<Ident>,
    defined_idents: HashSet<Ident>,
}

impl JsIdentStats {
    fn with_defined<I>(idents: I) -> Self
    where
        I: IntoIterator<Item = Ident>,
    {
        Self {
            used_idents: HashSet::new(),
            defined_idents: idents.into_iter().collect(),
        }
    }

    fn add_used_ident(&mut self, ident: &Ident) {
        if !self.defined_idents.contains(ident) {
            self.used_idents.insert(ident.clone());
        }
    }

    fn add_defined_ident(&mut self, ident: &Ident) {
        self.defined_idents.insert(ident.clone());
    }

    fn extend_free_idents(&mut self, other: HashSet<Ident>) {
        self.used_idents.extend(other);
    }

    fn free_variables(mut self) -> HashSet<Ident> {
        self.used_idents
            .retain(|ident| !self.defined_idents.contains(ident));
        self.used_idents
    }
}

fn free_variables_of_statement(stmt: &Statement) -> HashSet<Ident> {
    let mut stats = JsIdentStats::default();
    collect_statement_idents(stmt, &mut stats);
    stats.free_variables()
}

fn free_variables_of_expression(expr: &Expression) -> HashSet<Ident> {
    let mut stats = JsIdentStats::default();
    collect_expression_idents(expr, &mut stats);
    stats.free_variables()
}

fn free_variables_of_block_with_defined(
    block: &Block,
    defined: impl IntoIterator<Item = Ident>,
) -> HashSet<Ident> {
    let mut stats = JsIdentStats::with_defined(defined);
    collect_block_idents(block, &mut stats);
    stats.free_variables()
}

fn collect_block_idents(block: &Block, stats: &mut JsIdentStats) {
    for stmt in block {
        collect_statement_idents(stmt, stats);
    }
}

fn collect_statement_idents(stmt: &Statement, stats: &mut JsIdentStats) {
    match &stmt.desc {
        StatementDesc::Block(block) => collect_block_idents(block, stats),
        StatementDesc::Variable(VariableDeclaration { ident, value, .. }) => {
            stats.add_defined_ident(ident);
            if let Some(value) = value {
                collect_expression_idents(value, stats);
            }
        }
        StatementDesc::Exp(expr) | StatementDesc::Return(expr) | StatementDesc::Throw(expr) => {
            collect_expression_idents(expr, stats);
        }
        StatementDesc::If(cond, then_block, else_block) => {
            collect_expression_idents(cond, stats);
            collect_block_idents(then_block, stats);
            collect_block_idents(else_block, stats);
        }
        StatementDesc::While(_, cond, body) => {
            collect_expression_idents(cond, stats);
            collect_block_idents(body, stats);
        }
        StatementDesc::ForRange(_, start, finish, loop_ident, _, body) => {
            if let Some(start) = start {
                collect_expression_idents(start, stats);
            }
            collect_expression_idents(finish, stats);
            stats.extend_free_idents(free_variables_of_block_with_defined(
                body,
                std::iter::once(loop_ident.clone()),
            ));
        }
        StatementDesc::ForOf(_, loop_ident, iterable, body)
        | StatementDesc::ForAwaitOf(_, loop_ident, iterable, body) => {
            collect_expression_idents(iterable, stats);
            stats.extend_free_idents(free_variables_of_block_with_defined(
                body,
                std::iter::once(loop_ident.clone()),
            ));
        }
        StatementDesc::IntSwitch(test, clauses, default) => {
            collect_expression_idents(test, stats);
            for (_, clause) in clauses {
                collect_block_idents(&clause.body, stats);
            }
            if let Some(default) = default {
                collect_block_idents(default, stats);
            }
        }
        StatementDesc::StringSwitch(test, clauses, default) => {
            collect_expression_idents(test, stats);
            for clause in clauses {
                collect_block_idents(&clause.clause.body, stats);
            }
            if let Some(default) = default {
                collect_block_idents(default, stats);
            }
        }
        StatementDesc::Try(body, catch, finally) => {
            collect_block_idents(body, stats);
            if let Some((catch_ident, catch_block)) = catch {
                stats.extend_free_idents(free_variables_of_block_with_defined(
                    catch_block,
                    std::iter::once(catch_ident.clone()),
                ));
            }
            if let Some(finally) = finally {
                collect_block_idents(finally, stats);
            }
        }
        StatementDesc::Debugger | StatementDesc::Break(_) | StatementDesc::Continue(_) => {}
    }
}

fn collect_expression_idents(expr: &Expression, stats: &mut JsIdentStats) {
    match &expr.desc {
        ExpressionDesc::Var(crate::js_ir::VIdent::Id(ident)) => stats.add_used_ident(ident),
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
        | ExpressionDesc::Spread(inner)
        | ExpressionDesc::RecordRest(_, inner) => collect_expression_idents(inner, stats),
        ExpressionDesc::StringAppend(left, right)
        | ExpressionDesc::In(left, right)
        | ExpressionDesc::Seq(left, right)
        | ExpressionDesc::Bin(_, left, right)
        | ExpressionDesc::FlatCall(left, right)
        | ExpressionDesc::StringIndex(left, right)
        | ExpressionDesc::ArrayIndex(left, right) => {
            collect_expression_idents(left, stats);
            collect_expression_idents(right, stats);
        }
        ExpressionDesc::Cond(test, consequent, alternate) => {
            collect_expression_idents(test, stats);
            collect_expression_idents(consequent, stats);
            collect_expression_idents(alternate, stats);
        }
        ExpressionDesc::Call(func, args, _) => {
            collect_expression_idents(func, stats);
            for arg in args {
                collect_expression_idents(arg, stats);
            }
        }
        ExpressionDesc::TaggedTemplate(tag, strings, values) => {
            collect_expression_idents(tag, stats);
            for string in strings {
                collect_expression_idents(string, stats);
            }
            for value in values {
                collect_expression_idents(value, stats);
            }
        }
        ExpressionDesc::StaticIndex(target, _, _) => collect_expression_idents(target, stats),
        ExpressionDesc::New(target, args) => {
            collect_expression_idents(target, stats);
            if let Some(args) = args {
                for arg in args {
                    collect_expression_idents(arg, stats);
                }
            }
        }
        ExpressionDesc::Fun { params, body, .. } => {
            stats.extend_free_idents(free_variables_of_block_with_defined(
                body,
                params.iter().cloned(),
            ));
        }
        ExpressionDesc::Array(items, _) => {
            for item in items {
                collect_expression_idents(item, stats);
            }
        }
        ExpressionDesc::CamlBlock(items, _, _) => {
            for item in items {
                collect_expression_idents(item, stats);
            }
        }
        ExpressionDesc::Object(dup, props) => {
            if let Some(dup) = dup {
                collect_expression_idents(dup, stats);
            }
            for (_, value) in props {
                collect_expression_idents(value, stats);
            }
        }
    }
}

fn js_block_no_side_effects(block: &Block) -> bool {
    block.iter().all(js_statement_no_side_effects)
}

fn js_statement_no_side_effects(stmt: &Statement) -> bool {
    match &stmt.desc {
        StatementDesc::Throw(_)
        | StatementDesc::Debugger
        | StatementDesc::Break(_)
        | StatementDesc::Variable(_)
        | StatementDesc::Continue(_) => false,
        StatementDesc::Exp(expr) | StatementDesc::Return(expr) => js_expr_no_side_effects(expr),
        StatementDesc::Block(block) => js_block_no_side_effects(block),
        StatementDesc::If(cond, then_block, else_block) => {
            js_expr_no_side_effects(cond)
                && js_block_no_side_effects(then_block)
                && js_block_no_side_effects(else_block)
        }
        StatementDesc::While(_, cond, body) => {
            js_expr_no_side_effects(cond) && js_block_no_side_effects(body)
        }
        StatementDesc::ForRange(_, start, finish, _, _, body) => {
            start.as_deref().is_none_or(js_expr_no_side_effects)
                && js_expr_no_side_effects(finish)
                && js_block_no_side_effects(body)
        }
        // OCaml `js_analyzer.ml` `no_side_effect_obj`: `ForOf` / `ForAwaitOf`
        // raise Not_found, i.e. always considered side-effecting (the iterator
        // protocol can run arbitrary user code).
        StatementDesc::ForOf(_, _, _, _) | StatementDesc::ForAwaitOf(_, _, _, _) => false,
        StatementDesc::IntSwitch(test, clauses, default) => {
            js_expr_no_side_effects(test)
                && clauses
                    .iter()
                    .all(|(_, clause)| js_block_no_side_effects(&clause.body))
                && default.as_ref().is_none_or(js_block_no_side_effects)
        }
        StatementDesc::StringSwitch(test, clauses, default) => {
            js_expr_no_side_effects(test)
                && clauses
                    .iter()
                    .all(|clause| js_block_no_side_effects(&clause.clause.body))
                && default.as_ref().is_none_or(js_block_no_side_effects)
        }
        StatementDesc::Try(body, catch, finally) => {
            js_block_no_side_effects(body)
                && catch
                    .as_ref()
                    .is_none_or(|(_, block)| js_block_no_side_effects(block))
                && finally.as_ref().is_none_or(js_block_no_side_effects)
        }
    }
}
