//! Parsetree viewer utilities.
//!
//! This module provides helper functions for analyzing and inspecting the AST.
//! It's a port of OCaml's `res_parsetree_viewer.ml`.

use crate::parse_arena::{ExprIdx, LocIdx, ParseArena};
use crate::parser::ast::*;
use crate::parser::longident::Longident;

// ============================================================================
// Expression Analysis
// ============================================================================

/// Check if an expression is a "block" expression (let, sequence, etc.),
/// looking through explicit braces (res_parsetree_viewer.ml `is_block_expr`).
pub fn is_block_expr(arena: &ParseArena, expr: &Expression) -> bool {
    matches!(
        &unwrap_braces(arena, expr).pexp_desc,
        ExpressionDesc::Pexp_letmodule(_)
            | ExpressionDesc::Pexp_letexception(_)
            | ExpressionDesc::Pexp_let(_)
            | ExpressionDesc::Pexp_open(_)
            | ExpressionDesc::Pexp_sequence(_, _)
    )
}

/// Check if an expression is an explicit braces node.
pub fn is_braced_expr(expr: &Expression) -> bool {
    matches!(&expr.pexp_desc, ExpressionDesc::Pexp_braces(_))
}

/// res_parsetree_viewer.ml `process_braces`: the braces location and the
/// enclosed expression of an explicit braces node.
pub fn process_braces<'a>(
    arena: &'a ParseArena,
    expr: &'a Expression,
) -> (Option<LocIdx>, &'a Expression) {
    match &expr.pexp_desc {
        ExpressionDesc::Pexp_braces(braces) => {
            (Some(braces.braces_loc), arena.get_expr(braces.expr))
        }
        _ => (None, expr),
    }
}

/// res_parsetree_viewer.ml `unwrap_braces`.
pub fn unwrap_braces<'a>(arena: &'a ParseArena, expr: &'a Expression) -> &'a Expression {
    let mut expr = expr;
    while let ExpressionDesc::Pexp_braces(braces) = &expr.pexp_desc {
        expr = arena.get_expr(braces.expr);
    }
    expr
}

/// Check if an expression is a ternary expression.
pub fn is_ternary_expr(expr: &Expression) -> bool {
    matches!(&expr.pexp_desc, ExpressionDesc::Pexp_ternary(_))
}

/// Collect the parts of a ternary expression chain.
/// Returns a list of (condition, consequent) pairs and the final alternate expression.
pub fn collect_ternary_parts<'a>(
    arena: &'a ParseArena,
    expr: &'a Expression,
) -> (Vec<(&'a Expression, &'a Expression)>, &'a Expression) {
    let mut parts = Vec::new();
    let mut current = expr;

    while let ExpressionDesc::Pexp_ternary(inner) = &current.pexp_desc {
        let (condition, consequent, alternate) = **inner;
        parts.push((arena.get_expr(condition), arena.get_expr(consequent)));
        current = arena.get_expr(alternate);
    }

    (parts, current)
}

/// Check if an expression is a if-then-else (any form).
pub fn is_if_then_else_expr(expr: &Expression) -> bool {
    matches!(&expr.pexp_desc, ExpressionDesc::Pexp_ifthenelse(_))
}

/// Check if attributes contain the "res.iflet" marker.
pub fn has_if_let_attribute(arena: &ParseArena, attrs: &[Attribute]) -> bool {
    attrs
        .iter()
        .any(|attr| arena.get_string(attr.0.txt) == "res.iflet")
}

/// Check if an expression is an "if let" expression.
/// This is a `Pexp_match` with the `res.iflet` attribute.
pub fn is_if_let_expr(arena: &ParseArena, expr: &Expression) -> bool {
    matches!(&expr.pexp_desc, ExpressionDesc::Pexp_match(_))
        && has_if_let_attribute(arena, &expr.pexp_attributes)
}

/// Represents the kind of condition in an if-chain.
#[derive(Debug)]
pub enum IfConditionKind<'a> {
    /// Regular if condition: `if expr { ... }`
    If(&'a Expression),
    /// If-let pattern matching: `if let pattern = expr { ... }`
    IfLet(&'a Pattern, &'a Expression),
}

/// Collect all the branches of an if-expression chain.
/// Returns a list of (location, condition_kind, then_expr) tuples and the final else expression.
pub fn collect_if_expressions<'a>(
    arena: &'a crate::parse_arena::ParseArena,
    expr: &'a Expression,
) -> (
    Vec<(&'a LocIdx, IfConditionKind<'a>, &'a Expression)>,
    Option<&'a Expression>,
) {
    let mut acc = Vec::new();
    let mut current = expr;

    loop {
        let expr_loc = &current.pexp_loc;
        match &current.pexp_desc {
            // Regular if-then-else (with or without else branch)
            ExpressionDesc::Pexp_ifthenelse(inner) => {
                let (ref if_idx, ref then_idx, ref opt_else) = **inner;
                let if_expr: &Expression = arena.get_expr(*if_idx);
                let then_expr: &Expression = arena.get_expr(*then_idx);
                acc.push((expr_loc, IfConditionKind::If(if_expr), then_expr));
                match opt_else {
                    Some(else_idx) => current = arena.get_expr(*else_idx),
                    None => return (acc, None),
                }
            }
            // if let with no else (pattern matches unit constructor in else branch)
            ExpressionDesc::Pexp_match(inner)
                if is_if_let_expr(arena, current)
                    && inner.1.len() == 2
                    && inner.1[0].pc_guard.is_none()
                    && matches!(
                        &arena.get_expr(inner.1[1].pc_rhs).pexp_desc,
                        ExpressionDesc::Pexp_construct(lid, _) if arena.is_lident(lid.txt, "()")
                    ) =>
            {
                let (ref condition_idx, ref cases) = **inner;
                let pattern: &Pattern = arena.get_pat(cases[0].pc_lhs);
                let then_expr: &Expression = arena.get_expr(cases[0].pc_rhs);
                let condition: &Expression = arena.get_expr(*condition_idx);
                acc.push((
                    expr_loc,
                    IfConditionKind::IfLet(pattern, condition),
                    then_expr,
                ));
                return (acc, None);
            }
            // if let with else branch
            ExpressionDesc::Pexp_match(inner)
                if is_if_let_expr(arena, current)
                    && inner.1.len() == 2
                    && inner.1[0].pc_guard.is_none() =>
            {
                let (ref condition_idx, ref cases) = **inner;
                let pattern: &Pattern = arena.get_pat(cases[0].pc_lhs);
                let then_expr: &Expression = arena.get_expr(cases[0].pc_rhs);
                let else_expr: &Expression = arena.get_expr(cases[1].pc_rhs);
                let condition: &Expression = arena.get_expr(*condition_idx);
                acc.push((
                    expr_loc,
                    IfConditionKind::IfLet(pattern, condition),
                    then_expr,
                ));
                current = else_expr;
            }
            // End of chain
            _ => {
                return (acc, Some(current));
            }
        }
    }
}

/// Check if expression is a binary expression.
pub fn is_binary_expression(arena: &crate::parse_arena::ParseArena, expr: &Expression) -> bool {
    match &expr.pexp_desc {
        ExpressionDesc::Pexp_apply(inner) => {
            let PexpApply {
                ref funct,
                ref args,
                ..
            } = **inner;
            if args.len() != 2
                || args
                    .iter()
                    .any(|(lbl, _)| !matches!(lbl, ArgLabel::Nolabel))
            {
                return false;
            }
            let funct_expr = arena.get_expr(*funct);
            match &funct_expr.pexp_desc {
                ExpressionDesc::Pexp_ident(ident) => {
                    if let Longident::Lident(op_idx) = arena.get_longident(ident.txt) {
                        let op = arena.get_string(*op_idx);
                        not_ghost_operator(op, arena.loc_ghost(ident.loc))
                    } else {
                        false
                    }
                }
                _ => false,
            }
        }
        _ => false,
    }
}

/// Check if an expression is a single pipe expression.
/// Returns true for `x->f(g)` but not for `x->f->g` (multiple pipes).
/// Used for value binding layout optimization.
pub fn is_single_pipe_expr(arena: &crate::parse_arena::ParseArena, expr: &Expression) -> bool {
    // Helper to check if expr is a pipe expression
    fn is_pipe(arena: &crate::parse_arena::ParseArena, expr: &Expression) -> bool {
        match &expr.pexp_desc {
            ExpressionDesc::Pexp_apply(inner) => {
                let PexpApply {
                    ref funct,
                    ref args,
                    ..
                } = **inner;
                if args.len() != 2 {
                    return false;
                }
                let funct_expr = arena.get_expr(*funct);
                if let ExpressionDesc::Pexp_ident(ident) = &funct_expr.pexp_desc {
                    if let Longident::Lident(op_idx) = arena.get_longident(ident.txt) {
                        return arena.get_string(*op_idx) == "->";
                    }
                }
                false
            }
            _ => false,
        }
    }

    // Check if this is a pipe where the LHS is NOT also a pipe
    match &expr.pexp_desc {
        ExpressionDesc::Pexp_apply(inner) => {
            let PexpApply {
                ref funct,
                ref args,
                ..
            } = **inner;
            if args.len() != 2 {
                return false;
            }
            let funct_expr = arena.get_expr(*funct);
            if let ExpressionDesc::Pexp_ident(ident) = &funct_expr.pexp_desc {
                if let Longident::Lident(op_idx) = arena.get_longident(ident.txt) {
                    if arena.get_string(*op_idx) == "->" {
                        // It's a pipe - check that LHS is not also a pipe
                        let operand1 = arena.get_expr(args[0].1);
                        return !is_pipe(arena, operand1);
                    }
                }
            }
            false
        }
        _ => false,
    }
}

/// Check if expression is an await expression.
pub fn expr_is_await(expr: &Expression) -> bool {
    matches!(&expr.pexp_desc, ExpressionDesc::Pexp_await(_))
}

/// Check if expression is underscore apply sugar: `(__x) => f(...)`.
pub fn is_underscore_apply_sugar(arena: &ParseArena, expr: &Expression) -> bool {
    match &expr.pexp_desc {
        ExpressionDesc::Pexp_fun(inner) => {
            let PexpFun {
                ref arg_label,
                ref default,
                ref lhs,
                ref rhs,
                ..
            } = **inner;
            if *arg_label != ArgLabel::Nolabel || default.is_some() {
                return false;
            }
            let lhs_pat = arena.get_pat(*lhs);
            if let PatternDesc::Ppat_var(name) = &lhs_pat.ppat_desc {
                if arena.get_string(name.txt) == "__x" {
                    let rhs_expr = arena.get_expr(*rhs);
                    return matches!(&rhs_expr.pexp_desc, ExpressionDesc::Pexp_apply(_));
                }
            }
            false
        }
        _ => false,
    }
}

/// Check if expression is a function or newtype, looking through explicit
/// braces (res_parsetree_viewer.ml `is_fun_expr`).
pub fn is_fun_newtype(arena: &ParseArena, expr: &Expression) -> bool {
    matches!(
        &unwrap_braces(arena, expr).pexp_desc,
        ExpressionDesc::Pexp_fun(_) | ExpressionDesc::Pexp_newtype(_)
    )
}

/// Check if expression is an uncurried function (has explicit arity).
/// Requires arena to look up arity value (Arity is now ArityIdx).
pub fn expr_is_uncurried_fun(arena: &ParseArena, expr: &Expression) -> bool {
    if let ExpressionDesc::Pexp_fun(fun_inner) = &expr.pexp_desc {
        // Has explicit arity if arena.get_arity returns Some(_)
        arena.get_arity(fun_inner.arity).is_some()
    } else {
        false
    }
}

/// Check if the last argument is a callback that needs special printing.
/// This returns true if the last argument is a function/newtype and
/// all other arguments are NOT functions/newtypes.
/// Note: underscore apply sugar is NOT considered a callback here because
/// OCaml rewrites it before this check, and after rewriting it becomes Pexp_apply.
///
/// `partial` stands for the dummy `~...` argument res_printer.ml:4764-4769
/// appends to a partial application before these checks; a callback is then
/// never the last argument.
pub fn requires_special_callback_printing_last_arg(
    arena: &ParseArena,
    args: &[(ArgLabel, ExprIdx)],
    partial: bool,
) -> bool {
    if partial {
        return false;
    }
    let mut iter = args.iter().peekable();
    while let Some((_, expr_idx)) = iter.next() {
        let expr = arena.get_expr(*expr_idx);
        // Skip underscore apply sugar - it gets rewritten to Pexp_apply
        if is_underscore_apply_sugar(arena, expr) {
            continue;
        }
        if is_fun_newtype(arena, expr) {
            // If this is the last element, return true
            // Otherwise (function in non-last position), return false
            return iter.peek().is_none();
        }
    }
    false
}

/// Check if the first argument is a callback that needs special printing.
/// This returns true if:
/// - The first argument is a function/newtype (but NOT underscore apply sugar)
/// - AND there is at least one more argument after it
/// - AND all remaining arguments are NOT functions/newtypes
pub fn requires_special_callback_printing_first_arg(
    arena: &ParseArena,
    args: &[(ArgLabel, ExprIdx)],
    partial: bool,
) -> bool {
    // Helper: is it a real callback (not underscore apply sugar)
    let is_real_callback = |expr_idx: &ExprIdx| -> bool {
        let expr = arena.get_expr(*expr_idx);
        is_fun_newtype(arena, expr) && !is_underscore_apply_sugar(arena, expr)
    };
    match args {
        // Single argument callback - use normal printing (a partial
        // application has the dummy `~...` argument after it).
        [(_, expr_idx)] if is_real_callback(expr_idx) => partial,
        // First is callback, need to check rest
        [(_, expr_idx), rest @ ..] if is_real_callback(expr_idx) => {
            // All remaining args must NOT be callbacks
            rest.iter().all(|(_, e)| !is_real_callback(e))
        }
        _ => false,
    }
}

/// Check if an expression is "huggable" (can be printed without line breaks).
pub fn is_huggable_expression(arena: &crate::parse_arena::ParseArena, expr: &Expression) -> bool {
    match &expr.pexp_desc {
        ExpressionDesc::Pexp_array(_)
        | ExpressionDesc::Pexp_tuple(_)
        | ExpressionDesc::Pexp_record(_) => true,
        ExpressionDesc::Pexp_constant(c)
            if matches!(&**c, Constant::Json(_) | Constant::Char { .. }) =>
        {
            true
        }
        ExpressionDesc::Pexp_template(template) if template.values.is_empty() => true,
        ExpressionDesc::Pexp_construct(lid, _)
            if arena.is_lident(lid.txt, "::") || arena.is_lident(lid.txt, "[]") =>
        {
            true
        }
        ExpressionDesc::Pexp_object_literal(_) | ExpressionDesc::Pexp_braces(_) => true,
        _ if is_block_expr(arena, expr) => true,
        ExpressionDesc::Pexp_constant(c) => match &**c {
            Constant::String(payload) => is_multiline_text(payload.source()),
            Constant::RawSource(source) => is_multiline_text(source),
            _ => false,
        },
        _ => false,
    }
}

/// Check if text contains newlines (is multiline).
fn is_multiline_text(txt: &str) -> bool {
    let bytes = txt.as_bytes();
    let len = bytes.len();
    let mut i = 0;
    while i < len {
        match bytes[i] {
            b'\n' | b'\r' => return true,
            b'\\' => {
                if i + 2 >= len {
                    return false;
                }
                i += 2;
            }
            _ => i += 1,
        }
    }
    false
}

/// Check if an expression is "huggable" as a RHS (simpler than is_huggable_expression).
pub fn is_huggable_rhs(expr: &Expression) -> bool {
    matches!(
        &expr.pexp_desc,
        ExpressionDesc::Pexp_array(_)
            | ExpressionDesc::Pexp_tuple(_)
            | ExpressionDesc::Pexp_record(_)
            | ExpressionDesc::Pexp_object_literal(_)
            | ExpressionDesc::Pexp_braces(_)
    )
}

/// Check if an expression is a unary expression.
pub fn is_unary_expression(arena: &crate::parse_arena::ParseArena, expr: &Expression) -> bool {
    match &expr.pexp_desc {
        ExpressionDesc::Pexp_apply(inner) => {
            let PexpApply {
                ref funct,
                ref args,
                ..
            } = **inner;
            if args.len() != 1
                || args
                    .iter()
                    .any(|(lbl, _)| !matches!(lbl, ArgLabel::Nolabel))
            {
                return false;
            }
            let funct_expr = arena.get_expr(*funct);
            if let ExpressionDesc::Pexp_ident(ident) = &funct_expr.pexp_desc {
                is_unary_operator_idx(arena, ident.txt)
            } else {
                false
            }
        }
        _ => false,
    }
}

/// Check if a longident index represents a unary operator.
pub fn is_unary_operator_idx(
    arena: &crate::parse_arena::ParseArena,
    lid_idx: crate::parse_arena::LidentIdx,
) -> bool {
    if let Longident::Lident(op_idx) = arena.get_longident(lid_idx) {
        let op = arena.get_string(*op_idx);
        matches!(op, "~+" | "~+." | "~-" | "~-." | "~~~" | "!" | "not")
    } else {
        false
    }
}

/// Check if the RHS of a binary expression should be inlined (not put on a new line).
/// This matches OCaml's should_inline_rhs_binary_expr from res_parsetree_viewer.ml:
/// - Pexp_constant: inline
/// - Pexp_let, Pexp_letmodule, Pexp_letexception: inline
/// - Pexp_sequence, Pexp_open, Pexp_ifthenelse: inline
/// - Pexp_for, Pexp_while, Pexp_try: inline
/// - Pexp_array, Pexp_record: inline
/// Note: Pexp_match (switch) is NOT in this list, so it will NOT inline
pub fn should_inline_rhs_binary_expr(arena: &ParseArena, expr: &Expression) -> bool {
    matches!(
        &unwrap_braces(arena, expr).pexp_desc,
        ExpressionDesc::Pexp_constant(_)
            | ExpressionDesc::Pexp_let(_)
            | ExpressionDesc::Pexp_letmodule(_)
            | ExpressionDesc::Pexp_letexception(_)
            | ExpressionDesc::Pexp_sequence(_, _)
            | ExpressionDesc::Pexp_open(_)
            | ExpressionDesc::Pexp_ifthenelse(_)
            | ExpressionDesc::Pexp_ternary(_)
            | ExpressionDesc::Pexp_for(_)
            | ExpressionDesc::Pexp_for_of(_)
            | ExpressionDesc::Pexp_for_await_of(_)
            | ExpressionDesc::Pexp_while(_, _)
            | ExpressionDesc::Pexp_try(_)
            | ExpressionDesc::Pexp_array(_)
            | ExpressionDesc::Pexp_record(_)
    )
}

// ============================================================================
// Dict and List Utilities
// ============================================================================

/// A source fragment in a dictionary spread expression.
pub enum DictExprPart<'a> {
    /// Literal dictionary rows encoded as a `Primitive_dict.make` argument.
    Rows(&'a Expression),
    /// An expression introduced with dictionary spread syntax.
    Spread(&'a Expression),
}

/// Recover the source fragments of a dictionary spread expression.
///
/// This mirrors `collect_spread_dict_expr_parts` in the OCaml parsetree
/// viewer. The parser encodes `dict{...a, "b": c}` as an attributed call to
/// `Primitive_dict.spread`; the printer uses these fragments to reconstruct
/// the surface syntax.
pub fn collect_spread_dict_expr_parts<'a>(
    arena: &'a ParseArena,
    expr: &'a Expression,
) -> Option<Vec<DictExprPart<'a>>> {
    fn literal_dict_rows<'a>(
        arena: &'a ParseArena,
        expr: &'a Expression,
    ) -> Option<&'a Expression> {
        let ExpressionDesc::Pexp_apply(apply) = &expr.pexp_desc else {
            return None;
        };
        let function = arena.get_expr(apply.funct);
        let ExpressionDesc::Pexp_ident(identifier) = &function.pexp_desc else {
            return None;
        };
        let Longident::Ldot(parent, field) = arena.get_longident(identifier.txt) else {
            return None;
        };
        let Longident::Lident(module_name) = parent.as_ref() else {
            return None;
        };
        if arena.get_string(*module_name) != "Primitive_dict"
            || arena.get_string(*field) != "make"
            || apply.args.len() != 1
            || !matches!(apply.args[0].0, ArgLabel::Nolabel)
        {
            return None;
        }
        let rows = arena.get_expr(apply.args[0].1);
        is_tuple_array(arena, rows).then_some(rows)
    }

    let ExpressionDesc::Pexp_apply(apply) = &expr.pexp_desc else {
        return None;
    };
    let function = arena.get_expr(apply.funct);
    let ExpressionDesc::Pexp_ident(identifier) = &function.pexp_desc else {
        return None;
    };
    let Longident::Ldot(parent, field) = arena.get_longident(identifier.txt) else {
        return None;
    };
    let Longident::Lident(module_name) = parent.as_ref() else {
        return None;
    };
    if arena.get_string(*module_name) != "Primitive_dict"
        || arena.get_string(*field) != "spread"
        || !function
            .pexp_attributes
            .iter()
            .any(|attribute| arena.get_string(attribute.0.txt) == "res.dictSpread")
        || apply.args.len() != 2
        || !apply
            .args
            .iter()
            .all(|(label, _)| matches!(label, ArgLabel::Nolabel))
    {
        return None;
    }

    let target = arena.get_expr(apply.args[0].1);
    let sources = arena.get_expr(apply.args[1].1);
    let ExpressionDesc::Pexp_array(source_indices) = &sources.pexp_desc else {
        return None;
    };

    let mut parts = Vec::with_capacity(source_indices.len() + 1);
    for part in std::iter::once(target).chain(source_indices.iter().map(|idx| arena.get_expr(*idx)))
    {
        if let Some(rows) = literal_dict_rows(arena, part) {
            if !matches!(&rows.pexp_desc, ExpressionDesc::Pexp_array(items) if items.is_empty()) {
                parts.push(DictExprPart::Rows(rows));
            }
        } else {
            parts.push(DictExprPart::Spread(part));
        }
    }
    Some(parts)
}

/// Check if an expression is an array of tuples (for dict detection).
/// Used to detect dict{} syntax which desugars to Primitive_dict.make([("key", value), ...])
pub fn is_tuple_array(arena: &ParseArena, expr: &Expression) -> bool {
    if let ExpressionDesc::Pexp_array(items) = &expr.pexp_desc {
        items
            .iter()
            .all(|e| matches!(&arena.get_expr(*e).pexp_desc, ExpressionDesc::Pexp_tuple(_)))
    } else {
        false
    }
}

/// Check if a pattern has the res.dictPattern attribute.
/// Used to detect dict{} pattern syntax which desugars to @res.dictPattern {...}
pub fn has_dict_pattern_attribute(arena: &ParseArena, attrs: &[Attribute]) -> bool {
    attrs
        .iter()
        .any(|attr| arena.get_string(attr.0.txt) == "res.dictPattern")
}

/// Check if a pattern is "huggable" (can be printed without line breaks).
/// Used for dict pattern rows to determine if the pattern should be on the same line as the key.
pub fn is_huggable_pattern(pat: &Pattern) -> bool {
    matches!(
        &pat.ppat_desc,
        PatternDesc::Ppat_array(_)
            | PatternDesc::Ppat_tuple(_)
            | PatternDesc::Ppat_record(_)
            | PatternDesc::Ppat_variant(_)
            | PatternDesc::Ppat_construct(_, _)
    )
}

/// Collect expressions from a list constructor (::).
/// Returns (list of expressions, optional spread expression).
pub fn collect_list_expressions<'a>(
    arena: &'a crate::parse_arena::ParseArena,
    expr: &'a Expression,
) -> (Vec<&'a Expression>, Option<&'a Expression>) {
    let mut acc = Vec::new();
    let mut current = expr;

    loop {
        match &current.pexp_desc {
            // res_parsetree_viewer.ml `collect_list_expressions`: `::` takes
            // its head and tail as two arguments, or as one 2-tuple.
            ExpressionDesc::Pexp_construct(lid, _) if arena.is_lident(lid.txt, "[]") => {
                return (acc, None);
            }
            ExpressionDesc::Pexp_construct(lid, args) if arena.is_lident(lid.txt, "::") => {
                let pair = match args.txt.as_slice() {
                    [head, tail] => Some((*head, *tail)),
                    [arg] => match &arena.get_expr(*arg).pexp_desc {
                        ExpressionDesc::Pexp_tuple(exprs) if exprs.len() == 2 => {
                            Some((exprs[0], exprs[1]))
                        }
                        _ => None,
                    },
                    _ => None,
                };
                match pair {
                    Some((head, tail)) => {
                        acc.push(arena.get_expr(head));
                        current = arena.get_expr(tail);
                        continue;
                    }
                    None => return (acc, Some(current)),
                }
            }
            _ => {
                // Not a list constructor, this is a spread
                return (acc, Some(current));
            }
        }
    }
}

/// res_parsetree_viewer.ml:646-653 collect_patterns_from_list_construct:
/// the `::` heads and the remaining tail pattern.
pub fn collect_list_patterns<'a>(
    arena: &'a crate::parse_arena::ParseArena,
    pat: &'a Pattern,
) -> (Vec<&'a Pattern>, &'a Pattern) {
    let mut acc = Vec::new();
    let mut current = pat;
    loop {
        if let PatternDesc::Ppat_construct(lid, args) = &current.ppat_desc
            && arena.is_lident(lid.txt, "::")
        {
            let pair = match args.txt.as_slice() {
                [head, rest] => Some((*head, *rest)),
                [arg] => match &arena.get_pat(*arg).ppat_desc {
                    PatternDesc::Ppat_tuple(pats) if pats.len() == 2 => Some((pats[0], pats[1])),
                    _ => None,
                },
                _ => None,
            };
            if let Some((head, rest)) = pair {
                acc.push(arena.get_pat(head));
                current = arena.get_pat(rest);
                continue;
            }
        }
        return (acc, current);
    }
}

// ============================================================================
// Array Collection
// ============================================================================

/// Collect expressions from an array (or tuple).
pub fn collect_array_expressions<'a>(
    arena: &'a ParseArena,
    expr: &'a Expression,
) -> (Vec<&'a Expression>, Option<&'a Expression>) {
    match &expr.pexp_desc {
        ExpressionDesc::Pexp_array(exprs) => {
            (exprs.iter().map(|idx| arena.get_expr(*idx)).collect(), None)
        }
        _ => (vec![], Some(expr)),
    }
}

// ============================================================================
// Function Analysis
// ============================================================================

/// Parameter for a function expression.
#[derive(Debug)]
pub enum FunParam<'a> {
    /// Regular parameter with pattern
    Parameter {
        attrs: &'a [Attribute],
        label: &'a ArgLabel,
        default_expr: Option<&'a Expression>,
        pat: &'a Pattern,
    },
    /// Newtype parameter(s): (type t) or (type t u v)
    /// Multiple consecutive newtypes are combined into a single NewTypes variant.
    NewTypes {
        attrs: &'a [Attribute],
        names: Vec<&'a StringLoc>,
    },
}

/// `newtype_params` (res_parsetree_viewer.ml:191-211) for a function's n-ary
/// newtypes: a newtype without attributes joins the previous group.
fn push_nary_newtypes<'a>(arena: &'a ParseArena, fun: &'a PexpFun, params: &mut Vec<FunParam<'a>>) {
    for (name, attrs) in arena.nary_fun_newtypes(fun) {
        match params.last_mut() {
            Some(FunParam::NewTypes { names, .. }) if attrs.is_empty() => names.push(name),
            _ => params.push(FunParam::NewTypes {
                attrs: attrs.as_slice(),
                names: vec![name],
            }),
        }
    }
}

/// Extract function parameters from a potentially nested function expression.
/// Returns (is_async, parameters, body).
///
/// This matches OCaml's fun_expr which uses the `arity` field to determine
/// when to stop collecting parameters. For curried functions like
/// `(a, b, c) => (d, e, f) => 4`, the first function has an arity marker
/// that signals the end of its parameter list.
///
/// The rule from OCaml: collect params when `arity = None || n_fun = 0`
/// - Always collect from the first function (n_fun = 0)
/// - For nested functions, only collect if arity is Unknown (no marker)
///
/// IMPORTANT: OCaml's fun_expr only collects Pexp_newtype at the BEGINNING,
/// not during the collect_params loop. After encountering any Pexp_fun,
/// the loop stops at non-Pexp_fun nodes (including Pexp_newtype).
pub fn fun_expr<'a>(
    arena: &'a ParseArena,
    expr: &'a Expression,
) -> (bool, Vec<FunParam<'a>>, &'a Expression) {
    // Check for async attribute on the outermost expression
    let mut is_async = expr
        .pexp_attributes
        .iter()
        .any(|attr| arena.get_string(attr.0.txt) == "res.async");

    let mut params = Vec::new();
    let mut current = expr;

    // First, collect leading Pexp_newtype (like OCaml's top-level match)
    // This combines consecutive newtypes like "type t, type u" into "type t u"
    if let ExpressionDesc::Pexp_newtype(newtype_inner) = &current.pexp_desc {
        let (ref name, ref body_idx) = **newtype_inner;
        let mut names = vec![name];
        current = arena.get_expr(*body_idx);

        // Collect any additional consecutive newtypes
        while let ExpressionDesc::Pexp_newtype(next_inner) = &current.pexp_desc {
            let (ref next_name, ref next_body_idx) = **next_inner;
            names.push(next_name);
            current = arena.get_expr(*next_body_idx);
        }

        params.push(FunParam::NewTypes { attrs: &[], names });
    }

    // Now collect_params: only handle Pexp_fun, stop at anything else
    let mut n_fun = 0;
    let mut found_first_pexp_fun = false;

    loop {
        match &current.pexp_desc {
            ExpressionDesc::Pexp_fun(inner) => {
                if let Some(source_params) = arena.stored_nary_fun_params(inner) {
                    // A function with its own parameter list is a separate
                    // `Pexp_fun` in the body (res_parsetree_viewer.ml:213-216
                    // reads only the outer node's params).
                    if n_fun > 0 {
                        break;
                    }
                    if !found_first_pexp_fun {
                        is_async = is_async || inner.is_async;
                    }
                    push_nary_newtypes(arena, inner, &mut params);
                    for source in source_params {
                        params.push(FunParam::Parameter {
                            attrs: &source.p_attrs,
                            label: &source.p_lbl,
                            default_expr: source.p_default.map(|idx| arena.get_expr(idx)),
                            pat: arena.get_pat(source.p_pat),
                        });
                    }
                    current = arena.get_expr(inner.rhs);
                    break;
                }
                let PexpFun {
                    arg_label,
                    default,
                    lhs,
                    rhs,
                    arity,
                    is_async: expr_is_async,
                } = &**inner;
                // Check is_async on the FIRST Pexp_fun we encounter
                // (it may be nested inside Pexp_newtype)
                if !found_first_pexp_fun {
                    is_async = is_async || *expr_is_async;
                    found_first_pexp_fun = true;
                }

                // OCaml's condition: arity = None || n_fun = 0
                // ArityIdx: arena.get_arity() returns None for unknown, Some(_) for known
                // Only collect if this is the first function OR there's no arity marker
                if n_fun == 0 {
                    push_nary_newtypes(arena, inner, &mut params);
                }
                if n_fun == 0 || arena.get_arity(*arity).is_none() {
                    // OCaml's fun_expr passes {expr_ with pexp_attributes = []} to collect_params,
                    // which means the FIRST parameter always gets empty attrs. For nested functions,
                    // the inner expression keeps its attributes. We emulate this by using empty
                    // slice for n_fun == 0.
                    let attrs: &[Attribute] = if n_fun == 0 {
                        &[] // First parameter: OCaml strips top-level attrs
                    } else {
                        &current.pexp_attributes // Nested: preserve attrs
                    };
                    let pat_ref: &Pattern = arena.get_pat(*lhs);
                    params.push(FunParam::Parameter {
                        attrs,
                        label: arg_label,
                        default_expr: default.as_ref().map(|idx| {
                            let e: &Expression = arena.get_expr(*idx);
                            e
                        }),
                        pat: pat_ref,
                    });
                    n_fun += 1;
                    current = arena.get_expr(*rhs);
                } else {
                    // Stop collecting - arity marker indicates end of this function's params
                    break;
                }
            }
            // IMPORTANT: Don't collect Pexp_newtype here - OCaml's collect_params doesn't
            // This ensures `(type a, ()) => (type b c, x) => 3` keeps the two functions separate
            _ => break,
        }
    }

    (is_async, params, current)
}

// ============================================================================
// Attribute Processing
// ============================================================================

/// `Res_parsetree_viewer.filter_fragile_match_attributes`
/// (res_parsetree_viewer.ml:506-521): drop the `@warning("-4")` that the
/// parser attaches to if-let matches.
pub fn filter_fragile_match_attributes<'a>(
    arena: &ParseArena,
    attrs: &'a Attributes,
) -> Vec<&'a Attribute> {
    attrs
        .iter()
        .filter(|attr| {
            if arena.get_string(attr.0.txt) != "warning" {
                return true;
            }
            let Payload::PStr(items) = &attr.1 else {
                return true;
            };
            let [item] = items.as_slice() else {
                return true;
            };
            let StructureItemDesc::Pstr_eval(inner) = &*item.pstr_desc else {
                return true;
            };
            !matches!(
                &arena.get_expr(inner.0).pexp_desc,
                ExpressionDesc::Pexp_constant(constant)
                    if matches!(&**constant, Constant::String(s) if s.semantic() == "-4")
            )
        })
        .collect()
}

/// Check if expression has spread attribute (...).
pub fn has_spread_attr(arena: &ParseArena, attrs: &Attributes) -> bool {
    attrs
        .iter()
        .any(|attr| arena.get_string(attr.0.txt) == "res.spread")
}

/// Check if pattern has spread attribute (...).
pub fn pattern_has_spread_attr(arena: &ParseArena, attrs: &Attributes) -> bool {
    has_spread_attr(arena, attrs)
}

/// Check if expression is `Primitive_array.spread` with @res.spread attribute.
/// This is the desugared form of `[...xs, a, b]`.
pub fn is_spread_belt_array_concat(arena: &ParseArena, expr: &Expression) -> bool {
    is_primitive_spread(arena, expr, "Primitive_array")
}

/// Check if expression is `Primitive_list.spread` with @res.spread attribute.
/// This is the desugared form of `list{...xs, a, b}`.
pub fn is_spread_belt_list_concat(arena: &ParseArena, expr: &Expression) -> bool {
    is_primitive_spread(arena, expr, "Primitive_list")
}

fn is_primitive_spread(arena: &ParseArena, expr: &Expression, module_name: &str) -> bool {
    let ExpressionDesc::Pexp_ident(loc_idx) = &expr.pexp_desc else {
        return false;
    };
    let Longident::Ldot(parent, name_idx) = arena.get_longident(loc_idx.txt) else {
        return false;
    };
    matches!(parent.as_ref(), Longident::Lident(base_idx)
        if arena.get_string(*base_idx) == module_name)
        && arena.get_string(*name_idx) == "spread"
        && has_spread_attr(arena, &expr.pexp_attributes)
}

/// Filter out parsing-only attributes (res.braces, res.ternary, res.await, etc.)
pub fn filter_parsing_attrs<'a>(arena: &ParseArena, attrs: &'a Attributes) -> Vec<&'a Attribute> {
    filter_parsing_attrs_slice(arena, attrs.as_slice())
}

/// Like `filter_parsing_attrs` but takes a plain slice instead of Attributes.
pub fn filter_parsing_attrs_slice<'a>(
    arena: &ParseArena,
    attrs: &'a [Attribute],
) -> Vec<&'a Attribute> {
    attrs
        .iter()
        .filter(|attr| !is_parsing_attr(arena, attr))
        .collect()
}

/// Whether `attr` is one of the parser-internal markers that
/// `filter_parsing_attrs` drops.
pub fn is_parsing_attr(arena: &ParseArena, attr: &Attribute) -> bool {
    matches!(
        arena.get_string(attr.0.txt),
        "res.iflet"
            | "res.ternary"
            | "res.await"
            | "res.patVariantSpread"
            | "res.dictPattern"
            | "res.dictSpread"
    )
}

/// `filter_parsing_attrs attrs <> []`, without building the filtered list.
pub fn has_non_parsing_attrs(arena: &ParseArena, attrs: &[Attribute]) -> bool {
    attrs.iter().any(|attr| !is_parsing_attr(arena, attr))
}

/// Check if an attribute is printable (not an internal parsing attribute).
pub fn is_printable_attribute(arena: &ParseArena, attr: &Attribute) -> bool {
    !matches!(
        arena.get_string(attr.0.txt),
        "res.iflet" | "res.await" | "res.ternary" | "res.dictPattern"
    )
}

/// Check if attributes contain any printable attributes.
pub fn has_printable_attributes(arena: &ParseArena, attrs: &Attributes) -> bool {
    attrs.iter().any(|a| is_printable_attribute(arena, a))
}

/// Check if expression has any attributes (excluding internal parsing ones).
pub fn has_attributes(arena: &ParseArena, attrs: &Attributes) -> bool {
    attrs.iter().any(|attr| {
        let name = arena.get_string(attr.0.txt);
        if matches!(name, "res.iflet" | "res.ternary" | "res.await") {
            return false;
        }
        // res_parsetree_viewer.ml:395-405: the fragile-match warning of an
        // if-let does not count.
        if name == "warning" && is_fragile_match_warning_payload(arena, &attr.1) {
            return !has_if_let_attribute(arena, attrs);
        }
        true
    })
}

/// `PStr [Pstr_eval (Pexp_constant (Pconst_string ("-4", None)), _)]`.
fn is_fragile_match_warning_payload(arena: &ParseArena, payload: &Payload) -> bool {
    let Payload::PStr(items) = payload else {
        return false;
    };
    let [item] = items.as_slice() else {
        return false;
    };
    let StructureItemDesc::Pstr_eval(inner) = &*item.pstr_desc else {
        return false;
    };
    matches!(
        &arena.get_expr(inner.0).pexp_desc,
        ExpressionDesc::Pexp_constant(constant)
            if matches!(&**constant, Constant::String(s) if s.semantic() == "-4")
    )
}

// ============================================================================
// JSX Analysis
// ============================================================================

// ============================================================================
// Operator Precedence
// ============================================================================

/// Get the precedence of a binary operator.
/// Higher number = higher precedence (binds tighter).
/// This matches the OCaml res_parsetree_viewer.ml exactly.
pub fn operator_precedence(op: &str) -> i32 {
    match op {
        ":=" => 1,
        "||" => 2,
        "&&" => 3,
        "|||" => 4,
        "^^^" => 5,
        "&&&" => 6,
        "==" | "===" | "<" | ">" | "!=" | "<>" | "!==" | "<=" | ">=" => 7,
        "<<" | ">>" | ">>>" => 8,
        "+" | "+." | "-" | "-." | "++" => 9,
        "*" | "*." | "/" | "/." | "%" => 10,
        "**" => 11,
        "#" | "##" | "->" => 12,
        _ => 0,
    }
}

/// Check if operator is an equality operator.
pub fn is_equality_operator(op: &str) -> bool {
    matches!(op, "==" | "===" | "!=" | "!==")
}

/// Check if the operator is right-associative.
/// Currently only exponentiation (**) is right-associative.
pub fn is_rhs_binary_operator(op: &str) -> bool {
    op == "**"
}

/// Check if parent and child operators can be flattened (same precedence, not both equality).
pub fn flattenable_operators(parent_op: &str, child_op: &str) -> bool {
    let prec_parent = operator_precedence(parent_op);
    let prec_child = operator_precedence(child_op);
    if prec_parent == prec_child {
        !(is_equality_operator(parent_op) && is_equality_operator(child_op))
    } else {
        false
    }
}

/// Check if a binary expression should have its RHS indented.
/// Returns true if:
/// - The operator is an equality operator (==, ===, !=, !==), OR
/// - The LHS is NOT a same-precedence sub-expression, OR
/// - The operator is `:=`
pub fn should_indent_binary_expr(
    arena: &crate::parse_arena::ParseArena,
    expr: &Expression,
) -> bool {
    use crate::parser::longident::Longident;

    match &expr.pexp_desc {
        ExpressionDesc::Pexp_apply(apply_inner) if apply_inner.args.len() == 2 => {
            let PexpApply {
                ref funct,
                ref args,
                ..
            } = **apply_inner;
            let funct_expr = arena.get_expr(*funct);
            if let ExpressionDesc::Pexp_ident(ident) = &funct_expr.pexp_desc {
                if let Longident::Lident(op_idx) = arena.get_longident(ident.txt) {
                    let op = arena.get_string(*op_idx);
                    if is_binary_operator_str(op) {
                        // Check the three conditions
                        if is_equality_operator(op) {
                            return true;
                        }
                        // Check if LHS is NOT a same-precedence sub-expression
                        let (_, lhs_idx) = &args[0];
                        let lhs = arena.get_expr(*lhs_idx);
                        if !same_precedence_sub_expression(arena, op, lhs) {
                            return true;
                        }
                    }
                }
            }
            false
        }
        _ => false,
    }
}

/// Check if sub_expression is a binary expression with same precedence as parent operator.
fn same_precedence_sub_expression(
    arena: &crate::parse_arena::ParseArena,
    parent_op: &str,
    sub_expr: &Expression,
) -> bool {
    use crate::parser::longident::Longident;

    match &sub_expr.pexp_desc {
        ExpressionDesc::Pexp_apply(apply_inner) if apply_inner.args.len() == 2 => {
            let PexpApply {
                ref funct, args: _, ..
            } = **apply_inner;
            let funct_expr = arena.get_expr(*funct);
            if let ExpressionDesc::Pexp_ident(ident) = &funct_expr.pexp_desc {
                if let Longident::Lident(op_idx) = arena.get_longident(ident.txt) {
                    let sub_op = arena.get_string(*op_idx);
                    if is_binary_operator_str(sub_op) {
                        return flattenable_operators(parent_op, sub_op);
                    }
                }
            }
            // Not a binary expression, so not same precedence
            true
        }
        // Not a binary expression
        _ => true,
    }
}

/// Check if string is a binary operator.
pub fn is_binary_operator_str(op: &str) -> bool {
    matches!(
        op,
        ":=" | "||"
            | "&&"
            | "=="
            | "==="
            | "<"
            | ">"
            | "!="
            | "!=="
            | "<="
            | ">="
            | "+"
            | "+."
            | "-"
            | "-."
            | "++"
            | "*"
            | "*."
            | "/"
            | "/."
            | "**"
            | "->"
            | "<>"
            | "%"
            | "|||"
            | "^^^"
            | "&&&"
            | "<<"
            | ">>"
            | ">>>"
    )
}

/// Check if operator is not a ghost operator.
/// Ghost operators are internal and shouldn't be printed as binary ops.
pub fn not_ghost_operator(op: &str, is_ghost: bool) -> bool {
    is_binary_operator_str(op) && !(is_ghost && op == "++")
}

// ============================================================================
// Expression Rewriting
// ============================================================================

/// Check if an expression is a `__x` identifier that should be printed as `_`.
/// Used when printing inside underscore apply sugar.
pub fn is_underscore_ident(expr: &Expression, arena: &ParseArena) -> bool {
    match &expr.pexp_desc {
        ExpressionDesc::Pexp_ident(lid) => arena.is_lident(lid.txt, "__x"),
        _ => false,
    }
}

// ============================================================================
// Type Analysis
// ============================================================================

/// A type parameter extracted from an arrow type.
#[derive(Debug)]
pub struct TypeParameter<'a> {
    /// Attributes on the parameter.
    pub attrs: &'a Attributes,
    /// Parameter label.
    pub lbl: &'a ArgLabel,
    /// Parameter type.
    pub typ: &'a CoreType,
}

/// `Res_parsetree_viewer.arrow_type` (res_parsetree_viewer.ml:3-7): an arrow
/// is its attributes, its n-ary parameters and its return type.
pub fn arrow_type<'a>(
    arena: &'a ParseArena,
    typ: &'a CoreType,
) -> (&'a Attributes, Vec<TypeParameter<'a>>, &'a CoreType) {
    match &typ.ptyp_desc {
        CoreTypeDesc::Ptyp_arrow(inner) => {
            let (arg, ret, _) = &**inner;
            let params = arena
                .nary_arrow_args_slice(arg)
                .unwrap_or(std::slice::from_ref(&**arg));
            let params = params
                .iter()
                .map(|param| TypeParameter {
                    attrs: &param.attrs,
                    lbl: &param.lbl,
                    typ: arena.get_core_type(param.typ),
                })
                .collect();
            (&typ.ptyp_attributes, params, arena.get_core_type(*ret))
        }
        _ => (&EMPTY_ATTRS, Vec::new(), typ),
    }
}

/// Empty attributes constant for returning references.
static EMPTY_ATTRS: Attributes = Attributes(None);

// ============================================================================
// Module Analysis
// ============================================================================

/// Extract functor applications from a module expression.
///
/// For `F(A)(B)(C)`, returns `([A, B, C], F)`.
pub fn mod_expr_apply<'a>(
    arena: &'a ParseArena,
    mod_expr: &'a ModuleExpr,
) -> (Vec<&'a ModuleExpr>, &'a ModuleExpr) {
    fn loop_apply<'a>(
        arena: &'a ParseArena,
        acc: Vec<&'a ModuleExpr>,
        mod_expr: &'a ModuleExpr,
    ) -> (Vec<&'a ModuleExpr>, &'a ModuleExpr) {
        match &*mod_expr.pmod_desc {
            ModuleExprDesc::Pmod_apply(next_idx, arg_idx) => {
                let arg: &ModuleExpr = arena.get_mod_expr(*arg_idx);
                let next: &ModuleExpr = arena.get_mod_expr(*next_idx);
                let mut new_acc = vec![arg];
                new_acc.extend(acc);
                loop_apply(arena, new_acc, next)
            }
            _ => (acc, mod_expr),
        }
    }
    loop_apply(arena, Vec::new(), mod_expr)
}

/// A functor parameter.
pub struct FunctorParam<'a> {
    /// Attributes on the parameter.
    pub attrs: &'a Attributes,
    /// Parameter name.
    pub lbl: &'a StringLoc,
    /// Optional module type constraint.
    pub mod_type: Option<&'a ModuleType>,
}

/// Extract functor parameters from a module expression.
///
/// For `(A: X, B: Y) => body`, returns `([(attrs, A, Some(X)), (attrs, B, Some(Y))], body)`.
pub fn mod_expr_functor<'a>(
    arena: &'a ParseArena,
    mod_expr: &'a ModuleExpr,
) -> (Vec<FunctorParam<'a>>, &'a ModuleExpr) {
    fn loop_functor<'a>(
        arena: &'a ParseArena,
        acc: Vec<FunctorParam<'a>>,
        mod_expr: &'a ModuleExpr,
    ) -> (Vec<FunctorParam<'a>>, &'a ModuleExpr) {
        match &*mod_expr.pmod_desc {
            ModuleExprDesc::Pmod_functor(inner) => {
                let (ref lbl, ref mod_type_idx, ref return_mod_expr_idx) = **inner;
                let param = FunctorParam {
                    attrs: &mod_expr.pmod_attributes,
                    lbl,
                    mod_type: mod_type_idx.as_ref().map(|idx| {
                        let mt: &ModuleType = arena.get_mod_type(*idx);
                        mt
                    }),
                };
                let return_mod_expr: &ModuleExpr = arena.get_mod_expr(*return_mod_expr_idx);
                let mut new_acc = acc;
                new_acc.push(param);
                loop_functor(arena, new_acc, return_mod_expr)
            }
            _ => (acc, mod_expr),
        }
    }
    let (params, body) = loop_functor(arena, Vec::new(), mod_expr);
    (params, body)
}

/// Check if attributes contain the await attribute.
pub fn has_await_attribute(arena: &ParseArena, attrs: &Attributes) -> bool {
    attrs
        .iter()
        .any(|attr| arena.get_string(attr.0.txt) == "res.await")
}

// ============================================================================
// Array/String Access Detection
// ============================================================================

/// Check if an expression is `Array.get(arr, idx)`.
pub fn is_array_access(arena: &crate::parse_arena::ParseArena, expr: &Expression) -> bool {
    match &expr.pexp_desc {
        ExpressionDesc::Pexp_apply(inner) => {
            let PexpApply {
                ref funct,
                ref args,
                ..
            } = **inner;
            if args.len() != 2
                || args
                    .iter()
                    .any(|(lbl, _)| !matches!(lbl, ArgLabel::Nolabel))
            {
                return false;
            }
            let funct_expr = arena.get_expr(*funct);
            if let ExpressionDesc::Pexp_ident(lid) = &funct_expr.pexp_desc {
                if let Longident::Ldot(base, method_idx) = arena.get_longident(lid.txt) {
                    if let Longident::Lident(module_idx) = base.as_ref() {
                        let module = arena.get_string(*module_idx);
                        let method = arena.get_string(*method_idx);
                        return module == "Array" && method == "get";
                    }
                }
            }
            false
        }
        _ => false,
    }
}

/// Check if an expression is `Array.set(arr, idx, value)`.
pub fn is_array_set(arena: &crate::parse_arena::ParseArena, expr: &Expression) -> bool {
    match &expr.pexp_desc {
        ExpressionDesc::Pexp_apply(inner) => {
            let PexpApply {
                ref funct,
                ref args,
                ..
            } = **inner;
            if args.len() != 3
                || args
                    .iter()
                    .any(|(lbl, _)| !matches!(lbl, ArgLabel::Nolabel))
            {
                return false;
            }
            let funct_expr = arena.get_expr(*funct);
            if let ExpressionDesc::Pexp_ident(lid) = &funct_expr.pexp_desc {
                if let Longident::Ldot(base, method_idx) = arena.get_longident(lid.txt) {
                    if let Longident::Lident(module_idx) = base.as_ref() {
                        let module = arena.get_string(*module_idx);
                        let method = arena.get_string(*method_idx);
                        return module == "Array" && method == "set";
                    }
                }
            }
            false
        }
        _ => false,
    }
}

/// Check if an expression is a rewritten underscore apply sugar pattern.
/// i.e., the pattern `_` that comes from `arr[_]` being rewritten to `(__x) => Array.get(__x, _)`.
pub fn is_rewritten_underscore_apply_sugar(
    arena: &crate::parse_arena::ParseArena,
    expr: &Expression,
) -> bool {
    match &expr.pexp_desc {
        ExpressionDesc::Pexp_ident(lid) => arena.is_lident(lid.txt, "_"),
        _ => false,
    }
}

/// Partition attributes into doc comments and regular attributes.
/// res_parsetree_viewer.ml:581-597: a `res.doc` attribute whose payload is
/// one string constant.
pub fn is_doc_comment_attribute(arena: &ParseArena, attr: &Attribute) -> bool {
    if arena.get_string(attr.0.txt) != "res.doc" {
        return false;
    }
    let Payload::PStr(items) = &attr.1 else {
        return false;
    };
    let [item] = items.as_slice() else {
        return false;
    };
    let StructureItemDesc::Pstr_eval(eval) = &*item.pstr_desc else {
        return false;
    };
    matches!(
        &arena.get_expr(eval.0).pexp_desc,
        ExpressionDesc::Pexp_constant(c) if matches!(&**c, Constant::String(..))
    )
}

pub fn partition_doc_comment_attributes<'a>(
    arena: &ParseArena,
    attrs: &'a Attributes,
) -> (Vec<&'a Attribute>, Vec<&'a Attribute>) {
    let mut doc_comments = Vec::new();
    let mut others = Vec::new();
    for attr in attrs {
        if is_doc_comment_attribute(arena, attr) {
            doc_comments.push(attr);
        } else {
            others.push(attr);
        }
    }
    (doc_comments, others)
}

// ============================================================================
// Pattern Analysis
// ============================================================================

/// Collect all patterns in an or-pattern chain.
/// For example, `Red | Blue | Green` becomes `[Red, Blue, Green]`.
/// For `Red | (Blue | Green)`, this becomes `[Red, Ppat_or(Blue, Green)]`,
/// preserving the nested or-pattern (which should be wrapped in parens when printed).
pub fn collect_or_pattern_chain<'a>(arena: &'a ParseArena, pat: &'a Pattern) -> Vec<&'a Pattern> {
    fn loop_collect<'a>(arena: &'a ParseArena, pattern: &'a Pattern, chain: &mut Vec<&'a Pattern>) {
        match &pattern.ppat_desc {
            PatternDesc::Ppat_or(left_idx, right_idx) => {
                let left: &Pattern = arena.get_pat(*left_idx);
                let right: &Pattern = arena.get_pat(*right_idx);
                loop_collect(arena, left, chain);
                chain.push(right);
            }
            _ => {
                chain.push(pattern);
            }
        }
    }

    let mut result = Vec::new();
    loop_collect(arena, pat, &mut result);
    result
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_operator_precedence() {
        assert!(operator_precedence("*") > operator_precedence("+"));
        assert!(operator_precedence("**") > operator_precedence("*"));
        assert!(operator_precedence("&&") > operator_precedence("||"));
    }
}
