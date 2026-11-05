//! Parenthesization logic for the printer.
//!
//! This module provides functions to determine when parentheses or braces
//! are needed in printed output. It's a port of OCaml's `res_parens.ml`.

use crate::parse_arena::{LocIdx, ParseArena};
use crate::parser::ast::*;
use crate::parser::longident::Longident;
use crate::parser::parsetree_viewer;

/// Result of checking if parentheses/braces are needed.
#[derive(Debug, Clone, PartialEq)]
pub enum ParenKind {
    /// Parentheses are needed
    Parenthesized,
    /// Braces are needed at the given location
    Braced(LocIdx),
    /// No wrapping needed
    Nothing,
}

#[inline]
fn braces_from_attr(arena: &ParseArena, expr: &Expression) -> Option<ParenKind> {
    parsetree_viewer::process_braces(arena, expr)
        .0
        .map(ParenKind::Braced)
}

#[inline]
fn is_module_pack_constraint(arena: &ParseArena, expr: &Expression) -> bool {
    if let ExpressionDesc::Pexp_constraint(inner) = &expr.pexp_desc {
        let (ref inner_expr_idx, ref typ) = **inner;
        let inner_expr = arena.get_expr(*inner_expr_idx);
        matches!(&inner_expr.pexp_desc, ExpressionDesc::Pexp_pack(_))
            && matches!(
                &arena.get_core_type(*typ).ptyp_desc,
                CoreTypeDesc::Ptyp_package(_)
            )
    } else {
        false
    }
}

/// res_parens.ml `expr_with_coercion_kind`.
fn expr_with_coercion_kind(
    arena: &ParseArena,
    coercion_kind: ParenKind,
    expr: &Expression,
) -> ParenKind {
    if let Some(kind) = braces_from_attr(arena, expr) {
        return kind;
    }

    match &expr.pexp_desc {
        _ if is_module_pack_constraint(arena, expr) => ParenKind::Nothing,
        ExpressionDesc::Pexp_coerce(_) => coercion_kind,
        ExpressionDesc::Pexp_constraint(_) => ParenKind::Parenthesized,
        _ => ParenKind::Nothing,
    }
}

/// Check if an expression needs parentheses/braces.
pub fn expr(arena: &ParseArena, expr: &Expression) -> ParenKind {
    expr_with_coercion_kind(arena, ParenKind::Parenthesized, expr)
}

/// res_parens.ml `expr_allowing_coercion`.
pub fn expr_allowing_coercion(arena: &ParseArena, expr: &Expression) -> ParenKind {
    expr_with_coercion_kind(arena, ParenKind::Nothing, expr)
}

/// Check if expression record row RHS needs parentheses.
pub fn expr_record_row_rhs(arena: &ParseArena, optional: bool, e: &Expression) -> ParenKind {
    let kind = expr(arena, e);
    match kind {
        ParenKind::Nothing if optional => match &e.pexp_desc {
            ExpressionDesc::Pexp_ifthenelse(_)
            | ExpressionDesc::Pexp_ternary(_)
            | ExpressionDesc::Pexp_fun(_) => ParenKind::Parenthesized,
            _ if parsetree_viewer::is_binary_expression(arena, e) => ParenKind::Parenthesized,
            _ => kind,
        },
        _ => kind,
    }
}

/// Check if a call expression needs parentheses/braces.
pub fn call_expr(arena: &ParseArena, expr: &Expression) -> ParenKind {
    if let Some(kind) = braces_from_attr(arena, expr) {
        return kind;
    }

    // Check for parsing attrs
    if parsetree_viewer::has_non_parsing_attrs(arena, expr.pexp_attributes.as_slice()) {
        return ParenKind::Parenthesized;
    }

    if parsetree_viewer::is_unary_expression(arena, expr)
        || parsetree_viewer::is_binary_expression(arena, expr)
    {
        return ParenKind::Parenthesized;
    }

    match &expr.pexp_desc {
        _ if is_module_pack_constraint(arena, expr) => ParenKind::Nothing,
        ExpressionDesc::Pexp_fun(_) if parsetree_viewer::is_underscore_apply_sugar(arena, expr) => {
            ParenKind::Nothing
        }
        ExpressionDesc::Pexp_assert(_)
        | ExpressionDesc::Pexp_fun(_)
        | ExpressionDesc::Pexp_newtype(_)
        | ExpressionDesc::Pexp_constraint(_)
        | ExpressionDesc::Pexp_coerce(_)
        | ExpressionDesc::Pexp_setfield(_)
        | ExpressionDesc::Pexp_match(_)
        | ExpressionDesc::Pexp_try(_)
        | ExpressionDesc::Pexp_while(_, _)
        | ExpressionDesc::Pexp_for(_)
        | ExpressionDesc::Pexp_for_of(_)
        | ExpressionDesc::Pexp_for_await_of(_)
        | ExpressionDesc::Pexp_ifthenelse(_)
        | ExpressionDesc::Pexp_ternary(_) => ParenKind::Parenthesized,
        _ if parsetree_viewer::expr_is_uncurried_fun(arena, expr) => ParenKind::Parenthesized,
        _ if parsetree_viewer::expr_is_await(expr) => ParenKind::Parenthesized,
        _ => ParenKind::Nothing,
    }
}

/// Check if a structure expression needs parentheses/braces.
pub fn structure_expr(arena: &ParseArena, expr: &Expression) -> ParenKind {
    if let Some(kind) = braces_from_attr(arena, expr) {
        return kind;
    }

    match &expr.pexp_desc {
        ExpressionDesc::Pexp_jsx_element(_) => ParenKind::Nothing,
        _ if parsetree_viewer::has_attributes(arena, &expr.pexp_attributes) => {
            ParenKind::Parenthesized
        }
        _ if is_module_pack_constraint(arena, expr) => ParenKind::Nothing,
        ExpressionDesc::Pexp_constraint(_) | ExpressionDesc::Pexp_coerce(_) => {
            ParenKind::Parenthesized
        }
        _ => ParenKind::Nothing,
    }
}

/// Check if a unary expression operand needs parentheses/braces.
pub fn unary_expr_operand(arena: &ParseArena, expr: &Expression) -> ParenKind {
    if let Some(kind) = braces_from_attr(arena, expr) {
        return kind;
    }

    if parsetree_viewer::has_non_parsing_attrs(arena, expr.pexp_attributes.as_slice()) {
        return ParenKind::Parenthesized;
    }

    if parsetree_viewer::is_unary_expression(arena, expr)
        || parsetree_viewer::is_binary_expression(arena, expr)
    {
        return ParenKind::Parenthesized;
    }

    match &expr.pexp_desc {
        _ if is_module_pack_constraint(arena, expr) => ParenKind::Nothing,
        ExpressionDesc::Pexp_fun(_) if parsetree_viewer::is_underscore_apply_sugar(arena, expr) => {
            ParenKind::Nothing
        }
        ExpressionDesc::Pexp_assert(_)
        | ExpressionDesc::Pexp_fun(_)
        | ExpressionDesc::Pexp_newtype(_)
        | ExpressionDesc::Pexp_constraint(_)
        | ExpressionDesc::Pexp_coerce(_)
        | ExpressionDesc::Pexp_setfield(_)
        | ExpressionDesc::Pexp_extension(_)
        | ExpressionDesc::Pexp_object_literal(_)
        | ExpressionDesc::Pexp_object_set(_)
        | ExpressionDesc::Pexp_match(_)
        | ExpressionDesc::Pexp_try(_)
        | ExpressionDesc::Pexp_while(_, _)
        | ExpressionDesc::Pexp_for(_)
        | ExpressionDesc::Pexp_for_of(_)
        | ExpressionDesc::Pexp_for_await_of(_)
        | ExpressionDesc::Pexp_ifthenelse(_)
        | ExpressionDesc::Pexp_ternary(_) => ParenKind::Parenthesized,
        _ if parsetree_viewer::expr_is_await(expr) => ParenKind::Parenthesized,
        _ => ParenKind::Nothing,
    }
}

/// Check if a binary expression operand needs parentheses/braces.
pub fn binary_expr_operand(arena: &ParseArena, is_lhs: bool, expr: &Expression) -> ParenKind {
    if let Some(kind) = braces_from_attr(arena, expr) {
        return kind;
    }

    match &expr.pexp_desc {
        _ if is_module_pack_constraint(arena, expr) => ParenKind::Nothing,
        ExpressionDesc::Pexp_fun(_) if parsetree_viewer::is_underscore_apply_sugar(arena, expr) => {
            ParenKind::Nothing
        }
        ExpressionDesc::Pexp_constraint(_)
        | ExpressionDesc::Pexp_coerce(_)
        | ExpressionDesc::Pexp_fun(_)
        | ExpressionDesc::Pexp_newtype(_) => ParenKind::Parenthesized,
        _ if parsetree_viewer::expr_is_uncurried_fun(arena, expr) => ParenKind::Parenthesized,
        _ if parsetree_viewer::is_binary_expression(arena, expr) => ParenKind::Parenthesized,
        _ if parsetree_viewer::is_ternary_expr(expr) => ParenKind::Parenthesized,
        ExpressionDesc::Pexp_assert(_) if is_lhs => ParenKind::Parenthesized,
        _ if parsetree_viewer::expr_is_await(expr) => ParenKind::Parenthesized,
        _ if parsetree_viewer::has_printable_attributes(arena, &expr.pexp_attributes) => {
            ParenKind::Parenthesized
        }
        _ => ParenKind::Nothing,
    }
}

/// Check if sub-binary expression operand needs parens based on precedence.
pub fn sub_binary_expr_operand(parent_operator: &str, child_operator: &str) -> bool {
    let prec_parent = parsetree_viewer::operator_precedence(parent_operator);
    let prec_child = parsetree_viewer::operator_precedence(child_operator);

    prec_parent > prec_child
        || (parsetree_viewer::is_equality_operator(parent_operator)
            && parsetree_viewer::is_equality_operator(child_operator))
        // a && b || c, add parens to (a && b) for readability
        || (parent_operator == "||" && child_operator == "&&")
}

/// Check if RHS binary expression operand needs parentheses.
pub fn rhs_binary_expr_operand(
    arena: &crate::parse_arena::ParseArena,
    parent_operator: &str,
    rhs: &Expression,
) -> bool {
    match &rhs.pexp_desc {
        ExpressionDesc::Pexp_apply(inner) => {
            let PexpApply { ref funct, .. } = *inner;
            let args = arena.apply_args(inner.args);
            if args.len() != 2 {
                return false;
            }
            let funct_expr = arena.get_expr(*funct);
            match &funct_expr.pexp_desc {
                ExpressionDesc::Pexp_ident(ident) if funct_expr.pexp_attributes.is_empty() => {
                    if let Longident::Lident(op_idx) = arena.get_longident(ident.txt) {
                        let operator = arena.get_string(*op_idx);
                        if parsetree_viewer::not_ghost_operator(
                            operator,
                            arena.loc_ghost(ident.loc),
                        ) {
                            let prec_parent =
                                parsetree_viewer::operator_precedence(parent_operator);
                            let prec_child = parsetree_viewer::operator_precedence(operator);
                            return prec_parent == prec_child;
                        }
                    }
                    false
                }
                _ => false,
            }
        }
        _ => false,
    }
}

/// Check if flatten operand RHS needs parentheses.
pub fn flatten_operand_rhs(
    arena: &crate::parse_arena::ParseArena,
    parent_operator: &str,
    rhs: &Expression,
) -> bool {
    match &rhs.pexp_desc {
        ExpressionDesc::Pexp_apply(inner) => {
            let PexpApply { ref funct, .. } = *inner;
            let args = arena.apply_args(inner.args);
            if args.len() != 2 {
                return false;
            }
            let funct_expr = arena.get_expr(*funct);
            match &funct_expr.pexp_desc {
                ExpressionDesc::Pexp_ident(ident) => {
                    if let Longident::Lident(op_idx) = arena.get_longident(ident.txt) {
                        let operator = arena.get_string(*op_idx);
                        if parsetree_viewer::not_ghost_operator(
                            operator,
                            arena.loc_ghost(ident.loc),
                        ) {
                            let prec_parent =
                                parsetree_viewer::operator_precedence(parent_operator);
                            let prec_child = parsetree_viewer::operator_precedence(operator);
                            return prec_parent >= prec_child || !rhs.pexp_attributes.is_empty();
                        }
                    }
                    false
                }
                _ => false,
            }
        }
        ExpressionDesc::Pexp_constraint(inner)
            if {
                let (ref inner_expr_idx, ref typ) = **inner;
                let inner_expr = arena.get_expr(*inner_expr_idx);
                matches!(&inner_expr.pexp_desc, ExpressionDesc::Pexp_pack(_))
                    && matches!(
                        &arena.get_core_type(*typ).ptyp_desc,
                        CoreTypeDesc::Ptyp_package(_)
                    )
            } =>
        {
            false
        }
        ExpressionDesc::Pexp_fun(inner) => {
            let PexpFun { ref lhs, .. } = **inner;
            if let PatternDesc::Ppat_var(name) = &arena.get_pat(*lhs).ppat_desc {
                if arena.get_string(name.txt) == "__x" {
                    return false;
                }
            }
            true
        }
        ExpressionDesc::Pexp_newtype(_)
        | ExpressionDesc::Pexp_setfield(_)
        | ExpressionDesc::Pexp_constraint(_)
        | ExpressionDesc::Pexp_coerce(_) => true,
        _ if parsetree_viewer::is_ternary_expr(rhs) => true,
        _ => false,
    }
}

/// Check if flatten operand RHS needs parentheses, ignoring the attribute check.
/// This is used when we've already partitioned printable attrs and will handle them separately.
pub fn flatten_operand_rhs_without_attrs(
    arena: &crate::parse_arena::ParseArena,
    parent_operator: &str,
    rhs: &Expression,
) -> bool {
    match &rhs.pexp_desc {
        ExpressionDesc::Pexp_apply(inner) => {
            let PexpApply { ref funct, .. } = *inner;
            let args = arena.apply_args(inner.args);
            if args.len() != 2 {
                return false;
            }
            let funct_expr = arena.get_expr(*funct);
            match &funct_expr.pexp_desc {
                ExpressionDesc::Pexp_ident(ident) => {
                    if let Longident::Lident(op_idx) = arena.get_longident(ident.txt) {
                        let operator = arena.get_string(*op_idx);
                        if parsetree_viewer::not_ghost_operator(
                            operator,
                            arena.loc_ghost(ident.loc),
                        ) {
                            let prec_parent =
                                parsetree_viewer::operator_precedence(parent_operator);
                            let prec_child = parsetree_viewer::operator_precedence(operator);
                            // NOTE: Unlike flatten_operand_rhs, we don't check rhs.pexp_attributes here
                            return prec_parent >= prec_child;
                        }
                    }
                    false
                }
                _ => false,
            }
        }
        ExpressionDesc::Pexp_constraint(inner)
            if {
                let (ref inner_expr_idx, ref typ) = **inner;
                let inner_expr = arena.get_expr(*inner_expr_idx);
                matches!(&inner_expr.pexp_desc, ExpressionDesc::Pexp_pack(_))
                    && matches!(
                        &arena.get_core_type(*typ).ptyp_desc,
                        CoreTypeDesc::Ptyp_package(_)
                    )
            } =>
        {
            false
        }
        ExpressionDesc::Pexp_fun(inner) => {
            let PexpFun { ref lhs, .. } = **inner;
            if let PatternDesc::Ppat_var(name) = &arena.get_pat(*lhs).ppat_desc {
                if arena.get_string(name.txt) == "__x" {
                    return false;
                }
            }
            true
        }
        ExpressionDesc::Pexp_newtype(_)
        | ExpressionDesc::Pexp_setfield(_)
        | ExpressionDesc::Pexp_constraint(_)
        | ExpressionDesc::Pexp_coerce(_) => true,
        _ if parsetree_viewer::is_ternary_expr(rhs) => true,
        _ => false,
    }
}

/// Check if binary operator inside await needs parentheses.
pub fn binary_operator_inside_await_needs_parens(operator: &str) -> bool {
    parsetree_viewer::operator_precedence(operator) < parsetree_viewer::operator_precedence("->")
}

/// Check if assert or await expression RHS needs parentheses/braces.
pub fn assert_or_await_expr_rhs(
    arena: &ParseArena,
    in_await: bool,
    expr: &Expression,
) -> ParenKind {
    if let Some(kind) = braces_from_attr(arena, expr) {
        return kind;
    }
    assert_or_await_expr_rhs_inner(arena, in_await, expr)
}

fn assert_or_await_expr_rhs_inner(
    arena: &ParseArena,
    in_await: bool,
    expr: &Expression,
) -> ParenKind {
    if parsetree_viewer::has_non_parsing_attrs(arena, expr.pexp_attributes.as_slice()) {
        return ParenKind::Parenthesized;
    }

    match &expr.pexp_desc {
        ExpressionDesc::Pexp_apply(apply_inner)
            if parsetree_viewer::is_binary_expression(arena, expr) =>
        {
            let PexpApply { ref funct, .. } = *apply_inner;
            let funct_expr = arena.get_expr(*funct);
            if let ExpressionDesc::Pexp_ident(ident) = &funct_expr.pexp_desc {
                if let Longident::Lident(op_idx) = arena.get_longident(ident.txt) {
                    let operator = arena.get_string(*op_idx);
                    if in_await && !binary_operator_inside_await_needs_parens(operator) {
                        return ParenKind::Nothing;
                    }
                }
            }
            ParenKind::Parenthesized
        }
        _ if is_module_pack_constraint(arena, expr) => ParenKind::Nothing,
        ExpressionDesc::Pexp_fun(_) if parsetree_viewer::is_underscore_apply_sugar(arena, expr) => {
            ParenKind::Nothing
        }
        ExpressionDesc::Pexp_assert(_)
        | ExpressionDesc::Pexp_fun(_)
        | ExpressionDesc::Pexp_newtype(_)
        | ExpressionDesc::Pexp_constraint(_)
        | ExpressionDesc::Pexp_coerce(_)
        | ExpressionDesc::Pexp_setfield(_)
        | ExpressionDesc::Pexp_match(_)
        | ExpressionDesc::Pexp_try(_)
        | ExpressionDesc::Pexp_while(_, _)
        | ExpressionDesc::Pexp_for(_)
        | ExpressionDesc::Pexp_for_of(_)
        | ExpressionDesc::Pexp_for_await_of(_)
        | ExpressionDesc::Pexp_ifthenelse(_)
        | ExpressionDesc::Pexp_ternary(_) => ParenKind::Parenthesized,
        _ if !in_await && parsetree_viewer::expr_is_await(expr) => ParenKind::Parenthesized,
        _ => ParenKind::Nothing,
    }
}

/// Check if a constant is negative.
pub fn is_negative_constant(constant: &Constant, arena: &ParseArena) -> bool {
    fn is_neg(txt: &str) -> bool {
        txt.starts_with('-')
    }
    match constant {
        Constant::Integer(i, _) | Constant::Float(i, _) => is_neg(arena.get_string(*i)),
        _ => false,
    }
}

/// Check if field expression needs parentheses/braces.
pub fn field_expr(arena: &ParseArena, expr: &Expression) -> ParenKind {
    if let Some(kind) = braces_from_attr(arena, expr) {
        return kind;
    }

    if parsetree_viewer::has_non_parsing_attrs(arena, expr.pexp_attributes.as_slice()) {
        return ParenKind::Parenthesized;
    }

    if parsetree_viewer::is_binary_expression(arena, expr)
        || parsetree_viewer::is_unary_expression(arena, expr)
    {
        return ParenKind::Parenthesized;
    }

    match &expr.pexp_desc {
        _ if is_module_pack_constraint(arena, expr) => ParenKind::Nothing,
        ExpressionDesc::Pexp_constant(c) if is_negative_constant(c, arena) => {
            ParenKind::Parenthesized
        }
        ExpressionDesc::Pexp_fun(_) if parsetree_viewer::is_underscore_apply_sugar(arena, expr) => {
            ParenKind::Nothing
        }
        ExpressionDesc::Pexp_assert(_)
        | ExpressionDesc::Pexp_extension(_)
        | ExpressionDesc::Pexp_regexp(_)
        | ExpressionDesc::Pexp_object_literal(_)
        | ExpressionDesc::Pexp_fun(_)
        | ExpressionDesc::Pexp_newtype(_)
        | ExpressionDesc::Pexp_constraint(_)
        | ExpressionDesc::Pexp_coerce(_)
        | ExpressionDesc::Pexp_setfield(_)
        | ExpressionDesc::Pexp_match(_)
        | ExpressionDesc::Pexp_try(_)
        | ExpressionDesc::Pexp_while(_, _)
        | ExpressionDesc::Pexp_for(_)
        | ExpressionDesc::Pexp_for_of(_)
        | ExpressionDesc::Pexp_for_await_of(_)
        | ExpressionDesc::Pexp_ifthenelse(_)
        | ExpressionDesc::Pexp_ternary(_) => ParenKind::Parenthesized,
        _ if parsetree_viewer::expr_is_await(expr) => ParenKind::Parenthesized,
        _ => ParenKind::Nothing,
    }
}

/// Check if ternary operand needs parentheses/braces.
pub fn ternary_operand(arena: &ParseArena, expr: &Expression) -> ParenKind {
    if let Some(kind) = braces_from_attr(arena, expr) {
        return kind;
    }

    match &expr.pexp_desc {
        _ if is_module_pack_constraint(arena, expr) => ParenKind::Nothing,
        ExpressionDesc::Pexp_ternary(_) => ParenKind::Parenthesized,
        ExpressionDesc::Pexp_constraint(_) | ExpressionDesc::Pexp_coerce(_) => {
            ParenKind::Parenthesized
        }
        _ if parsetree_viewer::is_fun_newtype(arena, expr) => {
            let (_, _, return_expr) = parsetree_viewer::fun_expr(arena, expr);
            match &return_expr.pexp_desc {
                ExpressionDesc::Pexp_constraint(_) | ExpressionDesc::Pexp_coerce(_) => {
                    ParenKind::Parenthesized
                }
                _ => ParenKind::Nothing,
            }
        }
        _ => ParenKind::Nothing,
    }
}

/// Check if a string starts with minus.
pub fn starts_with_minus(txt: &str) -> bool {
    txt.starts_with('-')
}

/// Check if JSX prop expression needs parentheses/braces.
pub fn jsx_prop_expr(arena: &ParseArena, expr: &Expression) -> ParenKind {
    match &expr.pexp_desc {
        ExpressionDesc::Pexp_let(_)
        | ExpressionDesc::Pexp_sequence(_, _)
        | ExpressionDesc::Pexp_letexception(_)
        | ExpressionDesc::Pexp_letmodule(_)
        | ExpressionDesc::Pexp_open(_) => ParenKind::Nothing,
        ExpressionDesc::Pexp_braces(braces)
            if parsetree_viewer::is_block_expr(arena, arena.get_expr(braces.expr)) =>
        {
            ParenKind::Nothing
        }
        _ => {
            if let Some(kind) = braces_from_attr(arena, expr) {
                return kind;
            }

            match &expr.pexp_desc {
                ExpressionDesc::Pexp_constant(c)
                    if expr.pexp_attributes.is_empty()
                        && matches!(&*c, Constant::Integer(x, _) | Constant::Float(x, _) if starts_with_minus(arena.get_string(*x))) =>
                {
                    ParenKind::Parenthesized
                }
                _ if parsetree_viewer::expr_is_await(expr) => ParenKind::Parenthesized,
                ExpressionDesc::Pexp_ident(_)
                | ExpressionDesc::Pexp_constant(_)
                | ExpressionDesc::Pexp_field(_, _)
                | ExpressionDesc::Pexp_construct(_, _)
                | ExpressionDesc::Pexp_variant(_)
                | ExpressionDesc::Pexp_array(_)
                | ExpressionDesc::Pexp_pack(_)
                | ExpressionDesc::Pexp_record { .. }
                | ExpressionDesc::Pexp_extension(_)
                | ExpressionDesc::Pexp_object_literal(_)
                | ExpressionDesc::Pexp_letmodule(_)
                | ExpressionDesc::Pexp_letexception(_)
                | ExpressionDesc::Pexp_open(_)
                | ExpressionDesc::Pexp_sequence(_, _)
                | ExpressionDesc::Pexp_let(_)
                | ExpressionDesc::Pexp_tuple(_)
                    if expr.pexp_attributes.is_empty() =>
                {
                    ParenKind::Nothing
                }
                _ if is_module_pack_constraint(arena, expr) && expr.pexp_attributes.is_empty() => {
                    ParenKind::Nothing
                }
                _ => ParenKind::Parenthesized,
            }
        }
    }
}

/// Check if JSX child expression needs parentheses/braces.
pub fn jsx_child_expr(arena: &ParseArena, expr: &Expression) -> ParenKind {
    match &expr.pexp_desc {
        ExpressionDesc::Pexp_let(_)
        | ExpressionDesc::Pexp_sequence(_, _)
        | ExpressionDesc::Pexp_letexception(_)
        | ExpressionDesc::Pexp_letmodule(_)
        | ExpressionDesc::Pexp_open(_) => ParenKind::Nothing,
        ExpressionDesc::Pexp_braces(braces)
            if parsetree_viewer::is_block_expr(arena, arena.get_expr(braces.expr)) =>
        {
            ParenKind::Nothing
        }
        _ => {
            if let Some(kind) = braces_from_attr(arena, expr) {
                return kind;
            }

            match &expr.pexp_desc {
                ExpressionDesc::Pexp_constant(c)
                    if expr.pexp_attributes.is_empty()
                        && matches!(&*c, Constant::Integer(x, _) | Constant::Float(x, _) if starts_with_minus(arena.get_string(*x))) =>
                {
                    ParenKind::Parenthesized
                }
                _ if parsetree_viewer::expr_is_await(expr) => ParenKind::Parenthesized,
                ExpressionDesc::Pexp_ident(_)
                | ExpressionDesc::Pexp_constant(_)
                | ExpressionDesc::Pexp_field(_, _)
                | ExpressionDesc::Pexp_construct(_, _)
                | ExpressionDesc::Pexp_variant(_)
                | ExpressionDesc::Pexp_array(_)
                | ExpressionDesc::Pexp_pack(_)
                | ExpressionDesc::Pexp_record { .. }
                | ExpressionDesc::Pexp_extension(_)
                | ExpressionDesc::Pexp_object_literal(_)
                | ExpressionDesc::Pexp_letmodule(_)
                | ExpressionDesc::Pexp_letexception(_)
                | ExpressionDesc::Pexp_open(_)
                | ExpressionDesc::Pexp_sequence(_, _)
                | ExpressionDesc::Pexp_let(_)
                | ExpressionDesc::Pexp_jsx_element(_)
                | ExpressionDesc::Pexp_regexp(_)
                    if expr.pexp_attributes.is_empty() =>
                {
                    ParenKind::Nothing
                }
                _ if is_module_pack_constraint(arena, expr) && expr.pexp_attributes.is_empty() => {
                    ParenKind::Nothing
                }
                ExpressionDesc::Pexp_jsx_element(_) => ParenKind::Nothing,
                _ => ParenKind::Parenthesized,
            }
        }
    }
}

/// Check if binary expression needs parentheses/braces.
pub fn binary_expr(arena: &ParseArena, expr: &Expression) -> ParenKind {
    binary_expr_with_attrs(arena, expr, !expr.pexp_attributes.is_empty())
}

/// [`binary_expr`] for `expr` with its attributes replaced by a list that is
/// non-empty iff `has_attrs`; only that emptiness is read.
pub fn binary_expr_with_attrs(arena: &ParseArena, expr: &Expression, has_attrs: bool) -> ParenKind {
    if let Some(kind) = braces_from_attr(arena, expr) {
        return kind;
    }

    if has_attrs && parsetree_viewer::is_binary_expression(arena, expr) {
        ParenKind::Parenthesized
    } else {
        ParenKind::Nothing
    }
}

/// Check if module type functor return needs parentheses.
pub fn mod_type_functor_return(mod_type: &ModuleType) -> bool {
    matches!(&mod_type.pmty_desc, ModuleTypeDesc::Pmty_with(_))
}

/// Check if module type with operand needs parentheses.
pub fn mod_type_with_operand(mod_type: &ModuleType) -> bool {
    matches!(
        &mod_type.pmty_desc,
        ModuleTypeDesc::Pmty_functor(_) | ModuleTypeDesc::Pmty_with(_)
    )
}

/// Check if module expression functor constraint needs parentheses.
pub fn mod_expr_functor_constraint(mod_type: &ModuleType) -> bool {
    matches!(
        &mod_type.pmty_desc,
        ModuleTypeDesc::Pmty_functor(_) | ModuleTypeDesc::Pmty_with(_)
    )
}

/// Check if braced expression needs explicit braces.
pub fn braced_expr(arena: &ParseArena, expr: &Expression) -> bool {
    match &parsetree_viewer::unwrap_braces(arena, expr).pexp_desc {
        ExpressionDesc::Pexp_constraint(inner) => {
            let (ref inner_expr_idx, ref typ) = **inner;
            let inner_expr = arena.get_expr(*inner_expr_idx);
            !(matches!(&inner_expr.pexp_desc, ExpressionDesc::Pexp_pack(_))
                && matches!(
                    &arena.get_core_type(*typ).ptyp_desc,
                    CoreTypeDesc::Ptyp_package(_)
                ))
        }
        _ => false,
    }
}

/// Check if include module expression needs parentheses.
pub fn include_mod_expr(mod_expr: &ModuleExpr) -> bool {
    matches!(&mod_expr.pmod_desc, ModuleExprDesc::Pmod_constraint(_, _))
}

/// Check if module expression needs parentheses.
/// OCaml logic:
/// - Pmod_constraint(Pmod_structure, Pmty_signature(Box::new([Psig_module]))) -> false
/// - Pmod_constraint(_, Pmty_signature(Box::new([Psig_module]))) -> true
/// - Otherwise -> false
pub fn mod_expr_parens(arena: &ParseArena, mod_expr: &ModuleExpr) -> bool {
    match &mod_expr.pmod_desc {
        ModuleExprDesc::Pmod_constraint(inner_idx, typ_idx) => {
            let inner = arena.get_mod_expr(*inner_idx);
            let typ = arena.get_mod_type(*typ_idx);
            // Check if typ is Pmty_signature with single Psig_module
            if let ModuleTypeDesc::Pmty_signature(items) = &typ.pmty_desc {
                if items.len() == 1 {
                    if let SignatureItemDesc::Psig_module(_) = &items[0].psig_desc {
                        // Sig is [Psig_module] - return false if inner is Pmod_structure, true otherwise
                        return !matches!(&inner.pmod_desc, ModuleExprDesc::Pmod_structure(_));
                    }
                }
            }
            // Not the special [Psig_module] case -> false
            false
        }
        _ => false,
    }
}

/// Check if arrow return type expression needs parentheses.
pub fn arrow_return_typ_expr(typ_expr: &CoreType) -> bool {
    matches!(&typ_expr.ptyp_desc, CoreTypeDesc::Ptyp_arrow(_))
}

/// Check if pattern record row RHS needs parentheses.
pub fn pattern_record_row_rhs(arena: &ParseArena, pattern: &Pattern) -> bool {
    match &pattern.ppat_desc {
        PatternDesc::Ppat_constraint(inner) => {
            let (ref inner_pat_idx, ref typ) = **inner;
            let inner_pat = arena.get_pat(*inner_pat_idx);
            !(matches!(&inner_pat.ppat_desc, PatternDesc::Ppat_unpack(_))
                && matches!(
                    &arena.get_core_type(*typ).ptyp_desc,
                    CoreTypeDesc::Ptyp_package(_)
                ))
        }
        _ => false,
    }
}
