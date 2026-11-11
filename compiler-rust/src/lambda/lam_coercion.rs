//! Export alias resolution and toplevel rewriting.
//!
//! Port of `lam_coercion.ml` — resolves export aliases, rewrites toplevel
//! variable initializers, and handles toplevel export extraction.

use ahash::{AHashMap as HashMap, AHashSet as HashSet};

use crate::ident::Ident;
use crate::js_ir::arena::{Block, Expr, ExprKind, JsArena, Stmt, StmtKind};
use crate::js_ir::build::{exp as E, ocaml_eq_expression, stmt as S};
use crate::lambda::TagInfo;
use crate::lambda::js_exp_make::js_expr_no_side_effects;
use crate::lambda::js_shake::{
    TailMoveInitializerKind, flatten_toplevel_block, resolve_tail_move_initializer_kind,
    resolve_tail_move_replacement_expression,
};
use crate::lambda::lam_compat::LetKind;

/// The declaration of a variable statement: `(ident, initializer, property)`.
fn declaration(a: &JsArena, stmt: Stmt) -> Option<(Ident, Option<Expr>, LetKind)> {
    match a.sk(stmt) {
        StmtKind::Variable(v) => {
            let decl = a.var(v);
            Some((decl.ident, decl.value, decl.property))
        }
        _ => None,
    }
}

pub(crate) fn resolve_export_aliases(
    j: &mut JsArena,
    block: &[Stmt],
    exports: Vec<Ident>,
) -> Vec<Ident> {
    let mut declared = HashSet::new();
    collect_declared_idents(j, block, &mut declared);
    let mut aliases = HashMap::new();
    collect_export_aliases(j, block, &mut aliases);
    exports
        .into_iter()
        .map(|export| {
            if keeps_declared_same_name_function_export_alias(j, block, &export) {
                return export;
            }
            resolve_declared_same_name_self_alias_target(j, block, &export)
                .or_else(|| reusable_declared_same_name_export_alias(j, block, &export))
                .unwrap_or_else(|| resolve_export_alias(&export, &aliases, &declared))
        })
        .collect()
}

pub(crate) fn keeps_declared_same_name_function_export_alias(
    a: &JsArena,
    block: &[Stmt],
    export: &Ident,
) -> bool {
    block_declares_initialized_ident(a, block, export)
        && matches!(
            resolve_tail_move_initializer_kind(a, block, export),
            Some(TailMoveInitializerKind::Function)
        )
        && count_materialized_same_name_binding_roots(a, block, export.name()) > 1
}

pub(crate) fn count_materialized_same_name_binding_roots(
    a: &JsArena,
    block: &[Stmt],
    name: &str,
) -> usize {
    flatten_toplevel_block(a, block)
        .into_iter()
        .filter(|stmt| match declaration(a, *stmt) {
            Some((ident, Some(initializer), _)) if ident.name() == name => !matches!(
                a.ek(initializer),
                ExprKind::Var(target) if a.ident(target).name() == ident.name()
            ),
            _ => false,
        })
        .count()
}

pub(crate) fn resolve_declared_same_name_self_alias_target(
    j: &mut JsArena,
    block: &[Stmt],
    export: &Ident,
) -> Option<Ident> {
    let start = E::var(*export, j);
    let resolved = resolve_tail_move_replacement_expression(j, block, start, export, false);
    match j.ek(resolved) {
        ExprKind::Var(target) => {
            let target = j.ident(target);
            (!target.same(export) && block_declares_ident(j, block, &target)).then_some(target)
        }
        _ => None,
    }
}

pub(crate) fn reusable_declared_same_name_export_alias(
    a: &JsArena,
    block: &[Stmt],
    export: &Ident,
) -> Option<Ident> {
    let flattened = flatten_toplevel_block(a, block);
    let initializer = flattened
        .iter()
        .find_map(|stmt| match declaration(a, *stmt) {
            Some((ident, Some(initializer), _)) if ident.same(export) => Some(initializer),
            _ => None,
        })?;
    reusable_same_name_export_binding_in(a, &flattened, export, initializer)
}

pub(crate) fn collect_declared_idents(a: &JsArena, block: &[Stmt], declared: &mut HashSet<Ident>) {
    for stmt in block {
        match a.sk(*stmt) {
            StmtKind::Variable(v) => {
                declared.insert(a.var(v).ident);
            }
            StmtKind::Block(inner) => collect_declared_idents(a, a.stmts(inner), declared),
            StmtKind::If(_, then_block, else_block) => {
                collect_declared_idents(a, a.stmts(then_block), declared);
                collect_declared_idents(a, a.stmts(else_block), declared);
            }
            _ => {}
        }
    }
}

pub(crate) fn block_declares_initialized_ident(
    a: &JsArena,
    block: &[Stmt],
    target: &Ident,
) -> bool {
    block.iter().find_map(|stmt| match declaration(a, *stmt) {
        Some((ident, value, _)) if ident.same(target) => Some(value.is_some()),
        _ => None,
    }) == Some(true)
}

pub(crate) fn block_declares_ident(a: &JsArena, block: &[Stmt], target: &Ident) -> bool {
    block
        .iter()
        .any(|stmt| declaration(a, *stmt).is_some_and(|(ident, _, _)| ident.same(target)))
}

pub(crate) fn collect_export_aliases(
    a: &JsArena,
    block: &[Stmt],
    aliases: &mut HashMap<Ident, Ident>,
) {
    for stmt in block {
        match a.sk(*stmt) {
            StmtKind::Variable(v) => {
                let decl = a.var(v);
                if let Some(value) = decl.value
                    && let ExprKind::Var(target) = a.ek(value)
                {
                    aliases.insert(decl.ident, a.ident(target));
                }
            }
            StmtKind::Block(inner) => collect_export_aliases(a, a.stmts(inner), aliases),
            StmtKind::If(_, then_block, else_block) => {
                collect_export_aliases(a, a.stmts(then_block), aliases);
                collect_export_aliases(a, a.stmts(else_block), aliases);
            }
            _ => {}
        }
    }
}

pub(crate) fn resolve_export_alias(
    export: &Ident,
    aliases: &HashMap<Ident, Ident>,
    declared: &HashSet<Ident>,
) -> Ident {
    let mut current = *export;
    let mut seen = HashSet::new();

    while let Some(target) = aliases.get(&current) {
        if target.name() != export.name() || !declared.contains(target) || !seen.insert(current) {
            break;
        }
        current = *target;
    }

    current
}

#[derive(Debug)]
pub(crate) struct ExtractedExports {
    pub(crate) exports: Vec<Ident>,
    pub(crate) values: Vec<Expr>,
}

/// Whether `extract_toplevel_exports` succeeds on `expr`: the right spine of
/// `Seq`s ends in a module-export block.
fn ends_in_module_export(a: &JsArena, mut expr: Expr) -> bool {
    loop {
        match a.ek(expr) {
            ExprKind::CamlBlock(_, _, tag) => {
                return matches!(a.tag(tag), TagInfo::ModuleExport(_));
            }
            ExprKind::Seq(_, right) => expr = right,
            _ => return false,
        }
    }
}

pub(crate) fn extract_toplevel_exports(
    j: &mut JsArena,
    expr: Expr,
    block: &mut Block,
) -> Option<ExtractedExports> {
    match j.ek(expr) {
        ExprKind::CamlBlock(values, _, tag) if matches!(j.tag(tag), TagInfo::ModuleExport(_)) => {
            let TagInfo::ModuleExport(exports) = j.tag(tag) else {
                unreachable!()
            };
            let exports = exports.clone();
            let values = j.expr_vec(values);
            debug_assert_eq!(
                exports.len(),
                values.len(),
                "module export idents and payloads must stay aligned"
            );
            Some(ExtractedExports { exports, values })
        }
        ExprKind::Undefined { .. } => None,
        ExprKind::Seq(left, right) if ends_in_module_export(j, right) => {
            push_effect_expression(j, block, left);
            extract_toplevel_exports(j, right, block)
        }
        _ => {
            push_effect_expression(j, block, expr);
            None
        }
    }
}

pub(crate) fn can_reuse_existing_undefined_export_binding(
    a: &JsArena,
    block: &[Stmt],
    export: &Ident,
) -> bool {
    let flattened = flatten_toplevel_block(a, block);
    let Some(export_index) = flattened
        .iter()
        .position(|stmt| declaration(a, *stmt).is_some_and(|(ident, _, _)| ident.same(export)))
    else {
        return false;
    };

    flattened[export_index + 1..]
        .iter()
        .all(|stmt| statement_allows_undefined_export_reuse(a, *stmt))
}

pub(crate) fn insert_rebound_export_before_equivalent_later_binding(
    j: &mut JsArena,
    block: &mut Block,
    export: &Ident,
    value: Expr,
    later_exports: &[Ident],
) -> Option<Ident> {
    if !matches!(
        j.ek(value),
        ExprKind::Number(_)
            | ExprKind::Str(_)
            | ExprKind::Bool(_)
            | ExprKind::Undefined { .. }
            | ExprKind::Null
    ) {
        return None;
    }

    let a: &JsArena = j;
    let equivalent_later = |stmt: &Stmt| match declaration(a, *stmt) {
        Some((ident, Some(initializer), _)) => {
            later_exports.iter().any(|later| later.same(&ident))
                && ocaml_eq_expression(a, initializer, value)
        }
        _ => false,
    };
    let insert_index = block.iter().position(equivalent_later)?;
    if !block[insert_index..].iter().all(equivalent_later) {
        return None;
    }

    let stmt = S::define(*export, Some(value), LetKind::Strict, j);
    block.insert(insert_index, stmt);
    Some(*export)
}

pub(crate) fn reusable_same_name_export_binding(
    a: &JsArena,
    block: &[Stmt],
    export: &Ident,
    value: Expr,
) -> Option<Ident> {
    let flattened = flatten_toplevel_block(a, block);
    reusable_same_name_export_binding_in(a, &flattened, export, value)
}

fn reusable_same_name_export_binding_in(
    a: &JsArena,
    block: &[Stmt],
    export: &Ident,
    value: Expr,
) -> Option<Ident> {
    block.iter().find_map(|stmt| match declaration(a, *stmt) {
        Some((ident, Some(initializer), property))
            if ident.name() == export.name()
                && !ident.same(export)
                && !matches!(property, LetKind::Variable)
                && same_reusable_export_value(a, initializer, value) =>
        {
            Some(ident)
        }
        _ => None,
    })
}

pub(crate) fn same_reusable_export_value(a: &JsArena, left: Expr, right: Expr) -> bool {
    match (a.ek(left), a.ek(right)) {
        (ExprKind::Var(l), ExprKind::Var(r)) => a.ident(l) == a.ident(r),
        (ExprKind::Qualified(l), ExprKind::Qualified(r)) => a.qual(l) == a.qual(r),
        (
            ExprKind::StaticIndex(left_target, left_field, left_pos),
            ExprKind::StaticIndex(right_target, right_field, right_pos),
        ) => {
            a.text(left_field) == a.text(right_field)
                && left_pos == right_pos
                && same_reusable_export_value(a, left_target, right_target)
        }
        _ => false,
    }
}

pub(crate) fn push_effect_expression(j: &mut JsArena, block: &mut Block, expr: Expr) {
    let expr = effect_value_without_unit(j, expr);
    match j.ek(expr) {
        ExprKind::Seq(left, right) => {
            push_effect_expression(j, block, left);
            push_effect_expression(j, block, right);
        }
        _ if js_expr_no_side_effects(j, expr) => {}
        _ => block.push(S::exp(expr, j)),
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
pub(crate) fn push_s_if_empty(j: &mut JsArena, block: &mut Block, cond: Expr) {
    if matches!(j.ek(cond), ExprKind::Bool(_))
        || crate::js_ir::build::expression_has_no_side_effects(j, cond)
    {
        return;
    }
    push_s_exp(j, block, cond);
}

pub(crate) fn push_s_exp(j: &mut JsArena, block: &mut Block, expr: Expr) {
    let trivial =
        |a: &JsArena, e: Expr| matches!(a.ek(e), ExprKind::Number(_) | ExprKind::Undefined { .. });
    match j.ek(expr) {
        ExprKind::Number(_) | ExprKind::Undefined { .. } => {}
        ExprKind::Seq(left, _) if trivial(j, left) => {
            let ExprKind::Seq(_, right) = j.ek(expr) else {
                unreachable!()
            };
            push_s_exp(j, block, right);
        }
        ExprKind::Seq(left, right) if trivial(j, right) => push_s_exp(j, block, left),
        _ => block.push(S::exp(expr, j)),
    }
}

pub(crate) fn statement_allows_undefined_export_reuse(a: &JsArena, stmt: Stmt) -> bool {
    match declaration(a, stmt) {
        Some((_, value, _)) => value.is_none_or(|expr| {
            !matches!(a.ek(expr), ExprKind::Fun(_)) && js_expr_no_side_effects(a, expr)
        }),
        None => false,
    }
}

/// lam_compile_primitive.ml:30-36 `ensure_value_unit`: in effect position
/// (`EffectCall Not_tail`) a field or array store is the bare assignment, so
/// the primitive's `with_source_loc` lands on the assignment itself rather
/// than on a `(assignment, undefined)` sequence.
fn effect_value_without_unit(j: &mut JsArena, expr: Expr) -> Expr {
    let ExprKind::Seq(left, right) = j.ek(expr) else {
        return expr;
    };
    let cold = j.expr_cold(expr);
    let Some(loc) = cold.source_loc else {
        return expr;
    };
    if !matches!(j.ek(right), ExprKind::Undefined { is_unit: false })
        || j.expr_loc(left).is_some()
        || !matches!(j.ek(left), ExprKind::Bin(crate::js_ir::BinOp::Eq, _, _))
    {
        return expr;
    }
    let mut left_cold = j.expr_cold(left);
    left_cold.source_loc = Some(loc);
    if left_cold.comment.is_none() {
        left_cold.comment = cold.comment;
    }
    j.with_expr_cold(left, left_cold)
}
