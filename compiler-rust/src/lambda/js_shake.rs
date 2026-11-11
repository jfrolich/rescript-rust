//! JS IR pass: tree shaking.
//!
//! Removes unused top-level bindings and reorders export aliases to the tail
//! of the program block. Also includes free variable analysis and side-effect
//! checking for JS IR statements and expressions.

use ahash::AHashSet as HashSet;

use crate::ident::Ident;
use crate::js_ir::arena::{
    Block, Expr, ExprKind, JsArena, JsDepsProgram as DepsProgram, JsProgram as Program, Stmt,
    StmtKind, StmtList,
};
use crate::js_ir::build::exp as E;
use crate::js_ir::op::{Kind, UsedStats};
use crate::js_ir::walk::{
    Mapper, any_child, each_child, map_expression_children, map_statement_children,
};
use crate::lambda::lam_compat::LetKind;

use super::js_exp_make::js_expr_no_side_effects;
use super::lam_coercion::same_reusable_export_value;

pub(crate) fn apply_js_shake_pass(mut deps: DepsProgram) -> DepsProgram {
    shake_program(&mut deps.program);
    deps
}

fn local_var(a: &JsArena, e: Expr) -> Option<Ident> {
    match a.ek(e) {
        ExprKind::Var(id) => Some(a.ident(id)),
        _ => None,
    }
}

fn is_literal(a: &JsArena, e: Expr) -> bool {
    matches!(
        a.ek(e),
        ExprKind::Number(_)
            | ExprKind::Str(_)
            | ExprKind::Bool(_)
            | ExprKind::Undefined { .. }
            | ExprKind::Null
    )
}

pub(crate) fn move_same_name_export_alias_to_export_tail(
    j: &mut JsArena,
    block: &mut Block,
    export: &Ident,
    value: Expr,
) -> Option<(Expr, LetKind)> {
    let target = local_var(j, value)?;
    let target = &target;
    if target.name() != export.name() {
        return None;
    }

    // OCaml coerces exports over flattened lambda groups before JS lowering
    // (`compiler/core/lam_coercion.ml:179-199`,
    // `compiler/core/lam_compile_main.ml:220-254`).
    let flattened = flatten_toplevel_block(j, block);
    let (index, initializer, property) = same_name_export_alias_binding(j, &flattened, target)?;
    let initializer_kind = same_name_export_initializer_kind(j, &flattened, initializer);
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
    let remaining = &flattened[index + 1..];
    let later_initializer_mentions_target =
        later_toplevel_initializer_mentions_ident(j, remaining, target);
    let prefer_materialized_root = tail_move_materialized_root_ident(j, &flattened, initializer)
        .is_some_and(|root| {
            !root.same(target)
                && (later_initializer_mentions_target
                    || remaining
                        .iter()
                        .any(|stmt| statement_mentions_ident_anywhere(j, *stmt, &root)))
        });
    let replacement = resolve_tail_move_replacement_expression(
        j,
        &flattened,
        initializer,
        target,
        prefer_materialized_root,
    );
    let a: &JsArena = j;
    let binding_is_direct_literal = is_literal(a, initializer);
    let binding_is_local_alias = matches!(a.ek(initializer), ExprKind::Var(_));
    let has_later_function_binding = has_later_toplevel_function_binding(a, remaining);
    let later_function_mentions_target =
        later_toplevel_function_mentions_ident(a, remaining, target);
    // A Literal+Alias binding existing in the block means
    // `compiler/core/lam_pass_lets_dce.ml:121-133` entered the Strict arm
    // and `compiler/core/lam_util.ml:118-124` downgraded to Alias without
    // substituting the value. That is the exact shape OCaml keeps in source
    // order via `compiler/core/lam_coercion.ml:99-121`, so we must not
    // relocate the binding. The Alias-arm substitution path in OCaml always
    // removes the binding, in which case this function never finds a
    // declaration to move.
    let literal = matches!(initializer_kind, TailMoveInitializerKind::Literal);
    let qualified = matches!(initializer_kind, TailMoveInitializerKind::Qualified);
    let blocked_by_literal_binding = literal && !matches!(property, LetKind::Alias);
    let blocked_by_literal_alias_preserved_in_block = literal && matches!(property, LetKind::Alias);
    let blocked_by_direct_literal_reuse =
        literal && binding_is_direct_literal && later_initializer_mentions_target;
    let blocked_by_literal_alias_without_materialized_root =
        literal && binding_is_local_alias && !prefer_materialized_root;
    let blocked_by_later_function_capture = later_function_mentions_target;
    let blocked_by_qualified_binding_before_later_function =
        has_later_function_binding && qualified;
    let blocked_by_effects = !js_expr_no_side_effects(a, replacement);
    let blocked_by_self_mention = expression_mentions_ident_anywhere(a, replacement, target);
    let blocked_by_prior_use = flattened[..index]
        .iter()
        .any(|stmt| statement_mentions_ident_anywhere(a, *stmt, target));
    let has_remaining_use = remaining
        .iter()
        .any(|stmt| statement_mentions_ident_anywhere(a, *stmt, target));
    let blocked_by_unsafe_inline = qualified
        && !qualified_tail_move_uses_are_safe_to_inline(a, remaining, target, replacement);
    let blocked_by_later_initializer = later_initializer_mentions_target && !literal;
    let blocked_by_later_effect = !later_toplevel_effect_allows_tail_move(
        a,
        remaining,
        target,
        initializer_kind,
        replacement,
        replacement_resolves_to_recursive_function(a, &flattened, replacement),
    ) && !(target.same(export)
        && !has_remaining_use
        && ml_module_field_tail_move_replacement(a, replacement));
    if blocked_by_literal_binding
        || blocked_by_literal_alias_preserved_in_block
        || blocked_by_direct_literal_reuse
        || blocked_by_literal_alias_without_materialized_root
        || blocked_by_later_function_capture
        || blocked_by_qualified_binding_before_later_function
        || blocked_by_effects
        || blocked_by_self_mention
        || blocked_by_prior_use
        || blocked_by_unsafe_inline
        || blocked_by_later_initializer
        || blocked_by_later_effect
    {
        return None;
    }

    *block = substitute_after(j, flattened, index, target, replacement);
    Some((replacement, property))
}

/// Drops `flattened[index]` and replaces `target` with `replacement` in the
/// statements after it.
fn substitute_after(
    j: &mut JsArena,
    mut flattened: Vec<Stmt>,
    index: usize,
    target: &Ident,
    replacement: Expr,
) -> Block {
    let mut sub = SubstituteExportAlias {
        target: *target,
        replacement,
    };
    for stmt in &mut flattened[index + 1..] {
        *stmt = sub.statement(j, *stmt);
    }
    flattened.remove(index);
    flattened
}

pub(crate) fn move_reused_same_name_export_binding_to_export_tail(
    j: &mut JsArena,
    block: &mut Block,
    export: &Ident,
    value: Expr,
) -> Option<(Expr, LetKind)> {
    // Same OCaml contract as `move_same_name_export_alias_to_export_tail`:
    // export identity decisions come from `compiler/core/lam_coercion.ml:82-121`.
    let flattened = flatten_toplevel_block(j, block);
    let (index, reused, _initializer, property) =
        direct_reused_same_name_export_alias_binding(j, &flattened, export, value)?;
    let replacement =
        resolve_tail_move_replacement_expression(j, &flattened, value, &reused, false);
    let a: &JsArena = j;
    let initializer_kind = same_name_export_initializer_kind(a, &flattened, replacement);
    let remaining = &flattened[index + 1..];
    let blocked_by_literal_binding = matches!(initializer_kind, TailMoveInitializerKind::Literal)
        && (!matches!(property, LetKind::Alias)
            || !has_later_toplevel_function_binding(a, remaining));
    let blocked_by_later_effect = !later_toplevel_effect_allows_tail_move(
        a,
        remaining,
        &reused,
        initializer_kind,
        replacement,
        replacement_resolves_to_recursive_function(a, &flattened, replacement),
    );
    if matches!(property, LetKind::Variable)
        || blocked_by_literal_binding
        || matches!(initializer_kind, TailMoveInitializerKind::Other)
        || !js_expr_no_side_effects(a, replacement)
        || flattened[..index]
            .iter()
            .any(|stmt| statement_mentions_ident_anywhere(a, *stmt, &reused))
        || (matches!(initializer_kind, TailMoveInitializerKind::Qualified)
            && !qualified_tail_move_uses_are_safe_to_inline(a, remaining, &reused, replacement))
        || later_toplevel_initializer_mentions_ident(a, remaining, &reused)
        || blocked_by_later_effect
    {
        return None;
    }

    *block = substitute_after(j, flattened, index, &reused, replacement);
    Some((replacement, property))
}

fn same_name_export_alias_binding(
    a: &JsArena,
    block: &[Stmt],
    target: &Ident,
) -> Option<(usize, Expr, LetKind)> {
    block.iter().enumerate().find_map(|(index, stmt)| {
        let StmtKind::Variable(v) = a.sk(*stmt) else {
            return None;
        };
        let decl = a.var(v);
        match decl.value {
            Some(initializer) if decl.ident.same(target) => {
                Some((index, initializer, decl.property))
            }
            _ => None,
        }
    })
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum TailMoveInitializerKind {
    Qualified,
    Function,
    Literal,
    Other,
}

fn same_name_export_initializer_kind(
    a: &JsArena,
    block: &[Stmt],
    initializer: Expr,
) -> TailMoveInitializerKind {
    match a.ek(initializer) {
        _ if is_literal(a, initializer) => TailMoveInitializerKind::Literal,
        ExprKind::Qualified(_) => TailMoveInitializerKind::Qualified,
        ExprKind::Var(target) => resolve_tail_move_initializer_kind(a, block, &a.ident(target))
            .unwrap_or(TailMoveInitializerKind::Other),
        _ => TailMoveInitializerKind::Other,
    }
}

/// The declaration of `ident` among `block`'s statements.
fn find_declaration<'a>(
    a: &'a JsArena,
    block: &[Stmt],
    ident: &Ident,
) -> Option<&'a crate::js_ir::arena::VarDecl> {
    block.iter().find_map(|stmt| match a.sk(*stmt) {
        StmtKind::Variable(v) if a.var(v).ident.same(ident) => Some(a.var(v)),
        _ => None,
    })
}

pub(crate) fn resolve_tail_move_replacement_expression(
    j: &mut JsArena,
    block: &[Stmt],
    initializer: Expr,
    rebound: &Ident,
    prefer_materialized_root: bool,
) -> Expr {
    let Some(mut current) = local_var(j, initializer) else {
        return initializer;
    };
    let mut seen = HashSet::new();

    loop {
        if !seen.insert(current) {
            return initializer;
        }

        let Some(decl) = find_declaration(j, block, &current) else {
            return E::var(current, j);
        };
        let Some(value) = decl.value else {
            return E::var(current, j);
        };

        // OCaml's `compiler/core/lam_pass_lets_dce.ml:21-23` only substitutes
        // Strict / Alias / StrictOpt. Stop at a Variable-kind binding
        // (post-eliminate_ref ref); folding through it is unsound because later
        // code may mutate it.
        if matches!(decl.property, LetKind::Variable) {
            return E::var(current, j);
        }

        match j.ek(value) {
            ExprKind::Qualified(_) => {
                return if current.same(rebound) {
                    // A fresh node with the same module and member.
                    let kind = j.ek(value);
                    j.expr(kind)
                } else {
                    E::var(current, j)
                };
            }
            ExprKind::Var(next) if j.ident(next).name() == current.name() => {
                current = j.ident(next);
            }
            _ if is_literal(j, value) => {
                return if prefer_materialized_root && !current.same(rebound) {
                    E::var(current, j)
                } else {
                    value
                };
            }
            _ => return E::var(current, j),
        }
    }
}

fn tail_move_materialized_root_ident(
    a: &JsArena,
    block: &[Stmt],
    initializer: Expr,
) -> Option<Ident> {
    let mut current = local_var(a, initializer)?;
    let mut seen = HashSet::new();

    loop {
        if !seen.insert(current) {
            return None;
        }
        let decl = find_declaration(a, block, &current)?;
        let Some(value) = decl.value else {
            return Some(current);
        };
        match a.ek(value) {
            ExprKind::Var(next) if a.ident(next).name() == current.name() => {
                current = a.ident(next);
            }
            _ => return Some(current),
        }
    }
}

pub(crate) fn resolve_tail_move_initializer_kind(
    a: &JsArena,
    block: &[Stmt],
    start: &Ident,
) -> Option<TailMoveInitializerKind> {
    let mut current = *start;
    let mut seen = HashSet::new();

    loop {
        if !seen.insert(current) {
            return None;
        }
        let value = find_declaration(a, block, &current)?.value?;
        match a.ek(value) {
            ExprKind::Fun(_) => return Some(TailMoveInitializerKind::Function),
            ExprKind::Qualified(_) => return Some(TailMoveInitializerKind::Qualified),
            _ if is_literal(a, value) => return Some(TailMoveInitializerKind::Literal),
            ExprKind::Var(next) => current = a.ident(next),
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

fn tail_move_uses_are_safe_to_inline(a: &JsArena, block: &[Stmt], target: &Ident) -> bool {
    block
        .iter()
        .all(|stmt| statement_uses_ident_only_in_tail_move_safe_positions(a, *stmt, target))
}

fn tail_move_list_safe(a: &JsArena, block: StmtList, target: &Ident) -> bool {
    tail_move_uses_are_safe_to_inline(a, a.stmts(block), target)
}

fn qualified_tail_move_uses_are_safe_to_inline(
    a: &JsArena,
    block: &[Stmt],
    target: &Ident,
    replacement: Expr,
) -> bool {
    same_name_ml_module_field_tail_move_replacement(a, replacement, target.name())
        || tail_move_uses_are_safe_to_inline(a, block, target)
}

fn same_name_ml_module_field_tail_move_replacement(
    a: &JsArena,
    replacement: Expr,
    target_name: &str,
) -> bool {
    match a.ek(replacement) {
        ExprKind::Qualified(q) => {
            let (module, field) = a.qual(q);
            field == Some(target_name) && module.kind.eq(&Kind::Ml)
        }
        _ => false,
    }
}

fn ml_module_field_tail_move_replacement(a: &JsArena, replacement: Expr) -> bool {
    match a.ek(replacement) {
        ExprKind::Qualified(q) => a.qual(q).0.kind.eq(&Kind::Ml),
        _ => false,
    }
}

fn later_toplevel_effect_allows_tail_move(
    a: &JsArena,
    block: &[Stmt],
    target: &Ident,
    initializer_kind: TailMoveInitializerKind,
    replacement: Expr,
    replacement_is_recursive_function: bool,
) -> bool {
    if !block
        .iter()
        .any(|stmt| statement_has_toplevel_effect(a, *stmt))
    {
        return true;
    }
    if matches!(initializer_kind, TailMoveInitializerKind::Literal) {
        return true;
    }
    let has_remaining_use = block
        .iter()
        .any(|stmt| statement_mentions_ident_anywhere(a, *stmt, target));
    if !has_remaining_use {
        return matches!(initializer_kind, TailMoveInitializerKind::Function)
            && replacement_is_recursive_function;
    }

    match initializer_kind {
        TailMoveInitializerKind::Function => tail_move_uses_are_safe_to_inline(a, block, target),
        TailMoveInitializerKind::Qualified => {
            qualified_tail_move_uses_are_safe_to_inline(a, block, target, replacement)
        }
        TailMoveInitializerKind::Literal | TailMoveInitializerKind::Other => false,
    }
}

fn replacement_resolves_to_recursive_function(
    a: &JsArena,
    block: &[Stmt],
    replacement: Expr,
) -> bool {
    let Some(binding) = local_var(a, replacement) else {
        return false;
    };
    block.iter().any(|stmt| {
        let StmtKind::Variable(v) = a.sk(*stmt) else {
            return false;
        };
        let decl = a.var(v);
        if !decl.ident.same(&binding) {
            return false;
        }
        let Some(value) = decl.value else {
            return false;
        };
        let ExprKind::Fun(f) = a.ek(value) else {
            return false;
        };
        a.stmts(a.fun(f).body)
            .iter()
            .any(|stmt| statement_mentions_ident_anywhere(a, *stmt, &binding))
    })
}

fn statement_uses_ident_only_in_tail_move_safe_positions(
    a: &JsArena,
    stmt: Stmt,
    target: &Ident,
) -> bool {
    let other = |e: Expr| {
        expression_uses_ident_only_in_tail_move_safe_positions(
            a,
            e,
            target,
            TailMoveUseContext::Other,
        )
    };
    let list = |b: StmtList| tail_move_list_safe(a, b, target);
    match a.sk(stmt) {
        StmtKind::Block(block) => list(block),
        StmtKind::Variable(v) => {
            let decl = a.var(v);
            !decl.ident.same(target) && decl.value.is_none_or(other)
        }
        StmtKind::Exp(e) | StmtKind::Return(e) | StmtKind::Throw(e) => other(e),
        StmtKind::If(cond, then_block, else_block) => {
            other(cond) && list(then_block) && list(else_block)
        }
        StmtKind::While(_, cond, body) => other(cond) && list(body),
        StmtKind::ForRange(info) => {
            let info = a.for_range(info);
            !a.ident(info.ident).same(target)
                && info.init.is_none_or(other)
                && other(info.end)
                && list(info.body)
        }
        StmtKind::ForOf(info) | StmtKind::ForAwaitOf(info) => {
            let info = a.for_of(info);
            !a.ident(info.ident).same(target) && other(info.iterable) && list(info.body)
        }
        StmtKind::IntSwitch(test, info) => {
            let info = a.int_switch(info);
            other(test)
                && info.clauses.iter().all(|(_, clause)| list(clause.body))
                && info.default.is_none_or(list)
        }
        StmtKind::StringSwitch(test, info) => {
            let info = a.string_switch(info);
            other(test)
                && info.clauses.iter().all(|clause| list(clause.clause.body))
                && info.default.is_none_or(list)
        }
        StmtKind::Try(info) => {
            let info = a.try_info(info);
            list(info.body)
                && info.catch.is_none_or(|(catch_ident, block)| {
                    !a.ident(catch_ident).same(target) && list(block)
                })
                && info.finally.is_none_or(list)
        }
        StmtKind::Debugger | StmtKind::Break(_) | StmtKind::Continue(_) => true,
    }
}

fn expression_uses_ident_only_in_tail_move_safe_positions(
    a: &JsArena,
    expr: Expr,
    target: &Ident,
    context: TailMoveUseContext,
) -> bool {
    use TailMoveUseContext::*;
    let check = |e: Expr, context| {
        expression_uses_ident_only_in_tail_move_safe_positions(a, e, target, context)
    };
    let all = |list: crate::js_ir::arena::ExprList| a.exprs(list).iter().all(|e| check(*e, Other));
    match a.ek(expr) {
        ExprKind::Var(ident) => {
            !a.ident(ident).same(target) || matches!(context, CallCallee | NewTarget)
        }
        ExprKind::FlatCall(left, right) => check(left, CallCallee) && check(right, Other),
        ExprKind::Call(func, args, _) | ExprKind::TaggedTemplate(func, _, args) => {
            check(func, CallCallee) && all(args)
        }
        ExprKind::New(func, args) => check(func, NewTarget) && args.is_none_or(all),
        ExprKind::Fun(f) => tail_move_list_safe(a, a.fun(f).body, target),
        _ => !any_child(a, expr, |child| !check(child, Other)),
    }
}

fn direct_reused_same_name_export_alias_binding(
    a: &JsArena,
    block: &[Stmt],
    export: &Ident,
    value: Expr,
) -> Option<(usize, Ident, Expr, LetKind)> {
    block.iter().enumerate().find_map(|(index, stmt)| {
        let StmtKind::Variable(v) = a.sk(*stmt) else {
            return None;
        };
        let decl = a.var(v);
        let initializer = decl.value?;
        (decl.ident.name() == export.name() && same_reusable_export_value(a, initializer, value))
            .then_some((index, decl.ident, initializer, decl.property))
    })
}

pub(crate) fn keeps_declared_same_name_reusable_export_binding(
    a: &JsArena,
    block: &[Stmt],
    export: &Ident,
    value: Expr,
) -> bool {
    let flattened = flatten_toplevel_block(a, block);
    direct_reused_same_name_export_alias_binding(a, &flattened, export, value).is_some_and(
        |(_, ident, _, property)| ident.same(export) && !matches!(property, LetKind::Variable),
    )
}

/// The initializer of a top-level `let x = function ...`.
fn function_binding(a: &JsArena, stmt: Stmt) -> bool {
    match a.sk(stmt) {
        StmtKind::Variable(v) => a
            .var(v)
            .value
            .is_some_and(|value| matches!(a.ek(value), ExprKind::Fun(_))),
        _ => false,
    }
}

fn has_later_toplevel_function_binding(a: &JsArena, block: &[Stmt]) -> bool {
    block.iter().any(|stmt| function_binding(a, *stmt))
}

fn later_toplevel_function_mentions_ident(a: &JsArena, block: &[Stmt], target: &Ident) -> bool {
    block.iter().any(|stmt| {
        function_binding(a, *stmt) && statement_mentions_ident_anywhere(a, *stmt, target)
    })
}

fn later_toplevel_initializer_mentions_ident(a: &JsArena, block: &[Stmt], target: &Ident) -> bool {
    block.iter().any(|stmt| match a.sk(*stmt) {
        StmtKind::Variable(v) => a.var(v).value.is_some_and(|value| {
            expression_mentions_ident_outside_nested_functions(a, value, target)
        }),
        _ => false,
    })
}

fn statement_has_toplevel_effect(a: &JsArena, stmt: Stmt) -> bool {
    match a.sk(stmt) {
        StmtKind::Variable(v) => a
            .var(v)
            .value
            .is_some_and(|expr| !js_expr_no_side_effects(a, expr)),
        _ => !js_statement_no_side_effects(a, stmt),
    }
}

fn expression_mentions_ident_outside_nested_functions(
    a: &JsArena,
    expr: Expr,
    target: &Ident,
) -> bool {
    match a.ek(expr) {
        ExprKind::Var(ident) => a.ident(ident).same(target),
        ExprKind::Fun(_) => false,
        _ => any_child(a, expr, |child| {
            expression_mentions_ident_outside_nested_functions(a, child, target)
        }),
    }
}

/// Replaces uses of `target` with `replacement`, respecting shadowing by
/// loop, catch and function parameters.
struct SubstituteExportAlias {
    target: Ident,
    replacement: Expr,
}

impl Mapper for SubstituteExportAlias {
    fn statement(&mut self, j: &mut JsArena, s: Stmt) -> Stmt {
        match j.sk(s) {
            StmtKind::ForRange(info) if j.ident(j.for_range(info).ident).same(&self.target) => s,
            StmtKind::ForOf(info) | StmtKind::ForAwaitOf(info)
                if j.ident(j.for_of(info).ident).same(&self.target) =>
            {
                s
            }
            StmtKind::Try(id) => {
                let info = j.try_info(id);
                let body = self.block(j, info.body);
                let catch = info.catch.map(|(ident, block)| {
                    if j.ident(ident).same(&self.target) {
                        (ident, block)
                    } else {
                        (ident, self.block(j, block))
                    }
                });
                let finally = info.finally.map(|b| self.block(j, b));
                let new = crate::js_ir::arena::TryInfo {
                    body,
                    catch,
                    finally,
                };
                if new == info {
                    return s;
                }
                let id = j.try_id(new);
                j.rekind_stmt(s, StmtKind::Try(id))
            }
            _ => map_statement_children(self, j, s),
        }
    }

    fn expression(&mut self, j: &mut JsArena, e: Expr) -> Expr {
        match j.ek(e) {
            ExprKind::Var(ident) if j.ident(ident).same(&self.target) => self.replacement,
            ExprKind::Fun(f)
                if j.ident_slice(j.fun(f).params)
                    .iter()
                    .any(|param| param.same(&self.target)) =>
            {
                e
            }
            _ => map_expression_children(self, j, e),
        }
    }
}

fn list_mentions(a: &JsArena, block: StmtList, target: &Ident) -> bool {
    a.stmts(block)
        .iter()
        .any(|stmt| statement_mentions_ident_anywhere(a, *stmt, target))
}

pub(crate) fn statement_mentions_ident_anywhere(a: &JsArena, stmt: Stmt, target: &Ident) -> bool {
    let expr = |e: Expr| expression_mentions_ident_anywhere(a, e, target);
    let list = |b: StmtList| list_mentions(a, b, target);
    match a.sk(stmt) {
        StmtKind::Block(block) => list(block),
        StmtKind::Variable(v) => a.var(v).value.is_some_and(expr),
        StmtKind::Exp(e) | StmtKind::Return(e) | StmtKind::Throw(e) => expr(e),
        StmtKind::If(cond, then_block, else_block) => {
            expr(cond) || list(then_block) || list(else_block)
        }
        StmtKind::While(_, cond, body) => expr(cond) || list(body),
        StmtKind::ForRange(info) => {
            let info = a.for_range(info);
            !a.ident(info.ident).same(target)
                && (info.init.is_some_and(expr) || expr(info.end) || list(info.body))
        }
        StmtKind::ForOf(info) | StmtKind::ForAwaitOf(info) => {
            let info = a.for_of(info);
            !a.ident(info.ident).same(target) && (expr(info.iterable) || list(info.body))
        }
        StmtKind::IntSwitch(test, info) => {
            let info = a.int_switch(info);
            expr(test)
                || info.clauses.iter().any(|(_, clause)| list(clause.body))
                || info.default.is_some_and(list)
        }
        StmtKind::StringSwitch(test, info) => {
            let info = a.string_switch(info);
            expr(test)
                || info.clauses.iter().any(|clause| list(clause.clause.body))
                || info.default.is_some_and(list)
        }
        StmtKind::Try(info) => {
            let info = a.try_info(info);
            list(info.body)
                || info
                    .catch
                    .is_some_and(|(ident, block)| !a.ident(ident).same(target) && list(block))
                || info.finally.is_some_and(list)
        }
        StmtKind::Debugger | StmtKind::Break(_) | StmtKind::Continue(_) => false,
    }
}

fn expression_mentions_ident_anywhere(a: &JsArena, expr: Expr, target: &Ident) -> bool {
    match a.ek(expr) {
        ExprKind::Var(ident) => a.ident(ident).same(target),
        ExprKind::Fun(f) => {
            let info = a.fun(f);
            !a.ident_slice(info.params)
                .iter()
                .any(|param| param.same(target))
                && list_mentions(a, info.body, target)
        }
        _ => any_child(a, expr, |child| {
            expression_mentions_ident_anywhere(a, child, target)
        }),
    }
}

fn shake_program(program: &mut Program) {
    // OCaml flattens the JS block once, computes the required identifiers over
    // that same list, then folds it to keep live/effectful statements
    // (`compiler/core/js_shake.ml:62-104`).
    let a = &program.arena;
    let block = flatten_toplevel_block(a, &program.block);
    let required = live_idents(a, &block, &program.export_set);

    program.block = block
        .into_iter()
        .filter(|stmt| match a.sk(*stmt) {
            StmtKind::Variable(v) => {
                let decl = a.var(v);
                required.contains(&decl.ident)
                    || decl
                        .value
                        .is_some_and(|expr| !js_expr_no_side_effects(a, expr))
            }
            _ => !js_statement_no_side_effects(a, *stmt),
        })
        .collect();
}

/// `Js_analyzer.rev_toplevel_flatten` (`compiler/core/js_shake.ml:64`):
/// splices nested blocks and drops dead declarations.
pub(crate) fn flatten_toplevel_block(a: &JsArena, block: &[Stmt]) -> Vec<Stmt> {
    let mut flattened = Vec::with_capacity(block.len());
    flatten_toplevel_block_into(a, block, &mut flattened);
    flattened
}

fn flatten_toplevel_block_into(a: &JsArena, block: &[Stmt], flattened: &mut Vec<Stmt>) {
    for stmt in block {
        match a.sk(*stmt) {
            StmtKind::Variable(v) => {
                let decl = a.var(v);
                match decl.ident_info.used_stats {
                    UsedStats::DeadPure => {}
                    UsedStats::DeadNonPure if decl.value.is_none() => {}
                    _ => flattened.push(*stmt),
                }
            }
            StmtKind::Block(inner) => flatten_toplevel_block_into(a, a.stmts(inner), flattened),
            _ => flattened.push(*stmt),
        }
    }
}

/// `live_idents export_set block` (js_shake.ml): the identifiers the
/// toplevel `block` needs: the exports, everything a statement with side
/// effects refers to, and transitively the free variables of the initializers
/// of needed declarations. Each initializer's free variables are computed
/// once, and a worklist follows the dependencies.
fn live_idents(a: &JsArena, block: &[Stmt], export_set: &HashSet<Ident>) -> HashSet<Ident> {
    // Free variables of the initializer of each toplevel declaration.
    let mut deps: ahash::AHashMap<Ident, HashSet<Ident>> = ahash::AHashMap::default();
    let mut live: HashSet<Ident> = HashSet::default();
    let mut worklist: Vec<Ident> = Vec::new();
    let mark = |id: Ident, live: &mut HashSet<Ident>, worklist: &mut Vec<Ident>| {
        if live.insert(id) {
            worklist.push(id);
        }
    };
    for stmt in block {
        match a.sk(*stmt) {
            StmtKind::Variable(v) => {
                let decl = a.var(v);
                if let Some(value) = decl.value {
                    let free = free_variables_of_expression(a, value);
                    deps.entry(decl.ident).or_default().extend(free);
                    if !js_expr_no_side_effects(a, value) {
                        mark(decl.ident, &mut live, &mut worklist);
                    }
                }
            }
            _ => {
                if !js_statement_no_side_effects(a, *stmt) {
                    for id in free_variables_of_statement(a, *stmt) {
                        mark(id, &mut live, &mut worklist);
                    }
                }
            }
        }
    }
    for id in export_set {
        mark(*id, &mut live, &mut worklist);
    }
    while let Some(id) = worklist.pop() {
        if let Some(free) = deps.get(&id) {
            for id in free {
                mark(*id, &mut live, &mut worklist);
            }
        }
    }
    live
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
            self.used_idents.insert(*ident);
        }
    }

    fn free_variables(mut self) -> HashSet<Ident> {
        self.used_idents
            .retain(|ident| !self.defined_idents.contains(ident));
        self.used_idents
    }
}

fn free_variables_of_statement(a: &JsArena, stmt: Stmt) -> HashSet<Ident> {
    let mut stats = JsIdentStats::default();
    collect_statement_idents(a, stmt, &mut stats);
    stats.free_variables()
}

fn free_variables_of_expression(a: &JsArena, expr: Expr) -> HashSet<Ident> {
    let mut stats = JsIdentStats::default();
    collect_expression_idents(a, expr, &mut stats);
    stats.free_variables()
}

fn free_variables_of_block_with_defined(
    a: &JsArena,
    block: StmtList,
    defined: impl IntoIterator<Item = Ident>,
) -> HashSet<Ident> {
    let mut stats = JsIdentStats::with_defined(defined);
    collect_block_idents(a, block, &mut stats);
    stats.free_variables()
}

fn collect_block_idents(a: &JsArena, block: StmtList, stats: &mut JsIdentStats) {
    for stmt in a.stmts(block) {
        collect_statement_idents(a, *stmt, stats);
    }
}

fn collect_statement_idents(a: &JsArena, stmt: Stmt, stats: &mut JsIdentStats) {
    match a.sk(stmt) {
        StmtKind::Block(block) => collect_block_idents(a, block, stats),
        StmtKind::Variable(v) => {
            let decl = a.var(v);
            stats.defined_idents.insert(decl.ident);
            if let Some(value) = decl.value {
                collect_expression_idents(a, value, stats);
            }
        }
        StmtKind::Exp(e) | StmtKind::Return(e) | StmtKind::Throw(e) => {
            collect_expression_idents(a, e, stats)
        }
        StmtKind::If(cond, then_block, else_block) => {
            collect_expression_idents(a, cond, stats);
            collect_block_idents(a, then_block, stats);
            collect_block_idents(a, else_block, stats);
        }
        StmtKind::While(_, cond, body) => {
            collect_expression_idents(a, cond, stats);
            collect_block_idents(a, body, stats);
        }
        StmtKind::ForRange(info) => {
            let info = a.for_range(info);
            if let Some(init) = info.init {
                collect_expression_idents(a, init, stats);
            }
            collect_expression_idents(a, info.end, stats);
            stats
                .used_idents
                .extend(free_variables_of_block_with_defined(
                    a,
                    info.body,
                    std::iter::once(a.ident(info.ident)),
                ));
        }
        StmtKind::ForOf(info) | StmtKind::ForAwaitOf(info) => {
            let info = a.for_of(info);
            collect_expression_idents(a, info.iterable, stats);
            stats
                .used_idents
                .extend(free_variables_of_block_with_defined(
                    a,
                    info.body,
                    std::iter::once(a.ident(info.ident)),
                ));
        }
        StmtKind::IntSwitch(test, info) => {
            collect_expression_idents(a, test, stats);
            let info = a.int_switch(info);
            for (_, clause) in &info.clauses {
                collect_block_idents(a, clause.body, stats);
            }
            if let Some(default) = info.default {
                collect_block_idents(a, default, stats);
            }
        }
        StmtKind::StringSwitch(test, info) => {
            collect_expression_idents(a, test, stats);
            let info = a.string_switch(info);
            for clause in &info.clauses {
                collect_block_idents(a, clause.clause.body, stats);
            }
            if let Some(default) = info.default {
                collect_block_idents(a, default, stats);
            }
        }
        StmtKind::Try(info) => {
            let info = a.try_info(info);
            collect_block_idents(a, info.body, stats);
            if let Some((catch_ident, catch_block)) = info.catch {
                stats
                    .used_idents
                    .extend(free_variables_of_block_with_defined(
                        a,
                        catch_block,
                        std::iter::once(a.ident(catch_ident)),
                    ));
            }
            if let Some(finally) = info.finally {
                collect_block_idents(a, finally, stats);
            }
        }
        StmtKind::Debugger | StmtKind::Break(_) | StmtKind::Continue(_) => {}
    }
}

fn collect_expression_idents(a: &JsArena, expr: Expr, stats: &mut JsIdentStats) {
    match a.ek(expr) {
        ExprKind::Var(ident) => stats.add_used_ident(&a.ident(ident)),
        ExprKind::Fun(f) => {
            let info = a.fun(f);
            stats
                .used_idents
                .extend(free_variables_of_block_with_defined(
                    a,
                    info.body,
                    a.ident_slice(info.params).iter().copied(),
                ));
        }
        _ => each_child(a, expr, |child| collect_expression_idents(a, child, stats)),
    }
}

fn js_block_no_side_effects(a: &JsArena, block: StmtList) -> bool {
    a.stmts(block)
        .iter()
        .all(|stmt| js_statement_no_side_effects(a, *stmt))
}

fn js_statement_no_side_effects(a: &JsArena, stmt: Stmt) -> bool {
    let expr = |e: Expr| js_expr_no_side_effects(a, e);
    let list = |b: StmtList| js_block_no_side_effects(a, b);
    match a.sk(stmt) {
        StmtKind::Throw(_)
        | StmtKind::Debugger
        | StmtKind::Break(_)
        | StmtKind::Variable(_)
        | StmtKind::Continue(_) => false,
        StmtKind::Exp(e) | StmtKind::Return(e) => expr(e),
        StmtKind::Block(block) => list(block),
        StmtKind::If(cond, then_block, else_block) => {
            expr(cond) && list(then_block) && list(else_block)
        }
        StmtKind::While(_, cond, body) => expr(cond) && list(body),
        StmtKind::ForRange(info) => {
            let info = a.for_range(info);
            info.init.is_none_or(expr) && expr(info.end) && list(info.body)
        }
        // OCaml `js_analyzer.ml` `no_side_effect_obj`: `ForOf` / `ForAwaitOf`
        // raise Not_found, i.e. always considered side-effecting (the iterator
        // protocol can run arbitrary user code).
        StmtKind::ForOf(_) | StmtKind::ForAwaitOf(_) => false,
        StmtKind::IntSwitch(test, info) => {
            let info = a.int_switch(info);
            expr(test)
                && info.clauses.iter().all(|(_, clause)| list(clause.body))
                && info.default.is_none_or(list)
        }
        StmtKind::StringSwitch(test, info) => {
            let info = a.string_switch(info);
            expr(test)
                && info.clauses.iter().all(|clause| list(clause.clause.body))
                && info.default.is_none_or(list)
        }
        StmtKind::Try(info) => {
            let info = a.try_info(info);
            list(info.body)
                && info.catch.is_none_or(|(_, block)| list(block))
                && info.finally.is_none_or(list)
        }
    }
}
