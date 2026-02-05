//! Built-in PPX transformations.
//!
//! This module implements the built-in PPX transformations that OCaml applies
//! before type checking. These are transformations on the parsed AST that need
//! to happen before type checking.
//!
//! Key transformations:
//!
//! 1. **Record let → match**: Transform `let {a, b} = x in body` into
//!    `match x with {a, b} -> body`. This is how OCaml handles refutable
//!    record patterns in let bindings.
//!
//! 2. **String delimiter transformation**: Transform `Pconst_string(s, Some "js")`
//!    into `Pconst_string(s', Some "*j")` for regular strings (with escape processing),
//!    or `Pconst_string(s, Some "bq")` for template literals (with `res.template` attr).
//!
//! This mirrors the transformations in `compiler/frontend/bs_builtin_ppx.ml`.

use super::ast::{
    Attribute, Case, Constant, Expression, ExpressionDesc, Loc, Pattern, PatternDesc, RecFlag,
    Structure, StructureItem, StructureItemDesc, ValueBinding,
};
use crate::parse_arena::{LidentIdx, ParseArena};

/// Transform a structure with built-in PPX transformations.
pub fn transform_structure(arena: &ParseArena, structure: &mut Structure) {
    for item in structure.iter_mut() {
        transform_structure_item(arena, item);
    }
}

/// Transform a structure item.
fn transform_structure_item(arena: &ParseArena, item: &mut StructureItem) {
    match &mut item.pstr_desc {
        StructureItemDesc::Pstr_eval(expr, _) => {
            transform_expression(arena, expr);
        }
        StructureItemDesc::Pstr_value(_, bindings) => {
            for binding in bindings.iter_mut() {
                transform_pattern(&mut binding.pvb_pat);
                transform_expression(arena, &mut binding.pvb_expr);
            }
        }
        StructureItemDesc::Pstr_module(module_binding) => {
            transform_module_expr(arena, &mut module_binding.pmb_expr);
        }
        StructureItemDesc::Pstr_recmodule(module_bindings) => {
            for mb in module_bindings.iter_mut() {
                transform_module_expr(arena, &mut mb.pmb_expr);
            }
        }
        StructureItemDesc::Pstr_include(incl) => {
            transform_module_expr(arena, &mut incl.pincl_mod);
        }
        // Other items don't need transformation
        _ => {}
    }
}

/// Transform a module expression.
fn transform_module_expr(arena: &ParseArena, mexpr: &mut super::ast::ModuleExpr) {
    match &mut mexpr.pmod_desc {
        super::ast::ModuleExprDesc::Pmod_structure(structure) => {
            transform_structure(arena, structure);
        }
        super::ast::ModuleExprDesc::Pmod_functor(_, _, body) => {
            transform_module_expr(arena, body);
        }
        super::ast::ModuleExprDesc::Pmod_apply(m1, m2) => {
            transform_module_expr(arena, m1);
            transform_module_expr(arena, m2);
        }
        super::ast::ModuleExprDesc::Pmod_constraint(m, _) => {
            transform_module_expr(arena, m);
        }
        super::ast::ModuleExprDesc::Pmod_unpack(e) => {
            transform_expression(arena, e);
        }
        _ => {}
    }
}

/// Check if an expression has the `res.template` or `res.taggedTemplate` attribute.
fn is_template_literal(arena: &ParseArena, attrs: &[Attribute]) -> bool {
    attrs.iter().any(|(name, _)| {
        let s = arena.get_string(name.txt);
        s == "res.template" || s == "res.taggedTemplate"
    })
}

/// Process a JavaScript string's escape sequences, matching OCaml's
/// `Ast_utf8_string.transform`. This validates and passes through escape
/// sequences for JS output.
fn transform_utf8_string(s: &str) -> String {
    // For most strings, the content doesn't change - the OCaml transform
    // just validates escape sequences and passes them through.
    // The main difference is that it ensures proper escape handling.
    // For now, return the string as-is since the parser already handles escapes.
    s.to_string()
}

/// Transform string delimiters in an expression constant.
/// `Pconst_string(s, Some "js")` becomes:
/// - `Pconst_string(s, Some "*j")` for regular strings (with escape processing)
/// - `Pconst_string(s, Some "bq")` for template literals
fn transform_string_constant_expr(arena: &ParseArena, expr: &mut Expression) {
    if let ExpressionDesc::Pexp_constant(Constant::String(ref mut s, ref mut delim)) =
        expr.pexp_desc
    {
        if delim.as_deref() == Some("js") {
            if is_template_literal(arena, &expr.pexp_attributes) {
                // Template literal: change delimiter to "bq", keep content as-is
                *delim = Some("bq".to_string());
            } else {
                // Regular string: process escape sequences and change delimiter to "*j"
                *s = transform_utf8_string(s);
                *delim = Some("*j".to_string());
            }
        }
    }
}

/// Transform string delimiters in a pattern constant.
/// `Pconst_string(s, Some "js")` becomes `Pconst_string(s', Some "*j")`
fn transform_string_constant_pat(pat: &mut Pattern) {
    if let PatternDesc::Ppat_constant(Constant::String(ref mut s, ref mut delim)) = pat.ppat_desc {
        if delim.as_deref() == Some("js") {
            *s = transform_utf8_string(s);
            *delim = Some("*j".to_string());
        }
    }
}

/// Transform a pattern recursively (for string constant transformation).
fn transform_pattern(pat: &mut Pattern) {
    // Apply string constant transformation
    transform_string_constant_pat(pat);

    // Recurse into sub-patterns
    match &mut pat.ppat_desc {
        PatternDesc::Ppat_alias(p, _) => {
            transform_pattern(p);
        }
        PatternDesc::Ppat_tuple(pats) => {
            for p in pats.iter_mut() {
                transform_pattern(p);
            }
        }
        PatternDesc::Ppat_construct(_, Some(p)) => {
            transform_pattern(p);
        }
        PatternDesc::Ppat_variant(_, Some(p)) => {
            transform_pattern(p);
        }
        PatternDesc::Ppat_record(fields, _) => {
            for field in fields.iter_mut() {
                transform_pattern(&mut field.pat);
            }
        }
        PatternDesc::Ppat_array(pats) => {
            for p in pats.iter_mut() {
                transform_pattern(p);
            }
        }
        PatternDesc::Ppat_or(p1, p2) => {
            transform_pattern(p1);
            transform_pattern(p2);
        }
        PatternDesc::Ppat_constraint(p, _) => {
            transform_pattern(p);
        }
        PatternDesc::Ppat_exception(p) => {
            transform_pattern(p);
        }
        PatternDesc::Ppat_open(_, p) => {
            transform_pattern(p);
        }
        _ => {}
    }
}

/// Transform an expression recursively.
fn transform_expression(arena: &ParseArena, expr: &mut Expression) {
    // First, apply the record let → match transformation
    let transformed = try_transform_record_let(expr);

    // Now recurse into sub-expressions based on the (possibly transformed) expression
    let target = if transformed { expr } else { expr };

    // Apply string constant transformation
    transform_string_constant_expr(arena, target);

    match &mut target.pexp_desc {
        ExpressionDesc::Pexp_let(_, bindings, body) => {
            for binding in bindings.iter_mut() {
                transform_pattern(&mut binding.pvb_pat);
                transform_expression(arena, &mut binding.pvb_expr);
            }
            transform_expression(arena, body);
        }
        ExpressionDesc::Pexp_fun {
            default, lhs, rhs, ..
        } => {
            transform_pattern(lhs);
            if let Some(d) = default {
                transform_expression(arena, d);
            }
            transform_expression(arena, rhs);
        }
        ExpressionDesc::Pexp_apply { funct, args, .. } => {
            transform_expression(arena, funct);
            for (_, arg) in args.iter_mut() {
                transform_expression(arena, arg);
            }
        }
        ExpressionDesc::Pexp_match(scrutinee, cases) => {
            transform_expression(arena, scrutinee);
            for case in cases.iter_mut() {
                transform_pattern(&mut case.pc_lhs);
                if let Some(guard) = &mut case.pc_guard {
                    transform_expression(arena, guard);
                }
                transform_expression(arena, &mut case.pc_rhs);
            }
        }
        ExpressionDesc::Pexp_try(body, cases) => {
            transform_expression(arena, body);
            for case in cases.iter_mut() {
                transform_pattern(&mut case.pc_lhs);
                if let Some(guard) = &mut case.pc_guard {
                    transform_expression(arena, guard);
                }
                transform_expression(arena, &mut case.pc_rhs);
            }
        }
        ExpressionDesc::Pexp_tuple(exprs) => {
            for e in exprs.iter_mut() {
                transform_expression(arena, e);
            }
        }
        ExpressionDesc::Pexp_construct(_, Some(arg)) => {
            transform_expression(arena, arg);
        }
        ExpressionDesc::Pexp_variant(_, Some(arg)) => {
            transform_expression(arena, arg);
        }
        ExpressionDesc::Pexp_record(fields, spread) => {
            for field in fields.iter_mut() {
                transform_expression(arena, &mut field.expr);
            }
            if let Some(s) = spread {
                transform_expression(arena, s);
            }
        }
        ExpressionDesc::Pexp_field(e, _) => {
            transform_expression(arena, e);
        }
        ExpressionDesc::Pexp_setfield(e1, _, e2) => {
            transform_expression(arena, e1);
            transform_expression(arena, e2);
        }
        ExpressionDesc::Pexp_array(exprs) => {
            for e in exprs.iter_mut() {
                transform_expression(arena, e);
            }
        }
        ExpressionDesc::Pexp_ifthenelse(cond, then_, else_) => {
            transform_expression(arena, cond);
            transform_expression(arena, then_);
            if let Some(e) = else_ {
                transform_expression(arena, e);
            }
        }
        ExpressionDesc::Pexp_sequence(e1, e2) => {
            transform_expression(arena, e1);
            transform_expression(arena, e2);
        }
        ExpressionDesc::Pexp_while(cond, body) => {
            transform_expression(arena, cond);
            transform_expression(arena, body);
        }
        ExpressionDesc::Pexp_for(_, e1, e2, _, body) => {
            transform_expression(arena, e1);
            transform_expression(arena, e2);
            transform_expression(arena, body);
        }
        ExpressionDesc::Pexp_constraint(e, _) => {
            transform_expression(arena, e);
        }
        ExpressionDesc::Pexp_coerce(e, _, _) => {
            transform_expression(arena, e);
        }
        ExpressionDesc::Pexp_send(e, _) => {
            transform_expression(arena, e);
        }
        ExpressionDesc::Pexp_letmodule(_, me, body) => {
            transform_module_expr(arena, me);
            transform_expression(arena, body);
        }
        ExpressionDesc::Pexp_letexception(_, body) => {
            transform_expression(arena, body);
        }
        ExpressionDesc::Pexp_assert(e) => {
            transform_expression(arena, e);
        }
        ExpressionDesc::Pexp_newtype(_, e) => {
            transform_expression(arena, e);
        }
        ExpressionDesc::Pexp_pack(me) => {
            transform_module_expr(arena, me);
        }
        ExpressionDesc::Pexp_open(_, _, e) => {
            transform_expression(arena, e);
        }
        // Other cases don't need transformation
        _ => {}
    }
}

/// Check if a pattern is a record pattern (possibly aliased).
fn is_record_pattern(pat: &Pattern) -> bool {
    match &pat.ppat_desc {
        PatternDesc::Ppat_record(_, _) => true,
        PatternDesc::Ppat_alias(inner, _) => is_record_pattern(inner),
        _ => false,
    }
}

/// Try to transform `let {record_pattern} = expr in body` into
/// `match expr with {record_pattern} -> body`.
///
/// Returns true if transformation was applied.
fn try_transform_record_let(expr: &mut Expression) -> bool {
    // Check if this is a non-recursive let with a single binding
    // whose pattern is a record pattern
    let should_transform = match &expr.pexp_desc {
        ExpressionDesc::Pexp_let(RecFlag::Nonrecursive, bindings, _body) => {
            // Only transform single binding with record pattern
            if bindings.len() == 1 {
                let binding = &bindings[0];
                // Skip if binding has Pexp_pack (module unpacking)
                if matches!(binding.pvb_expr.pexp_desc, ExpressionDesc::Pexp_pack(_)) {
                    false
                } else {
                    is_record_pattern(&binding.pvb_pat)
                }
            } else {
                false
            }
        }
        _ => false,
    };

    if !should_transform {
        return false;
    }

    // Extract components and transform
    let (bindings, body, let_attrs) = match std::mem::replace(
        &mut expr.pexp_desc,
        ExpressionDesc::Pexp_ident(Loc {
            txt: LidentIdx(0),
            loc: expr.pexp_loc,
        }),
    ) {
        ExpressionDesc::Pexp_let(_, bindings, body) => {
            (bindings, body, std::mem::take(&mut expr.pexp_attributes))
        }
        _ => unreachable!(),
    };

    let binding = bindings.into_iter().next().unwrap();
    let ValueBinding {
        pvb_pat,
        pvb_expr,
        pvb_attributes,
        pvb_loc: _,
    } = binding;

    // Create the case for the match
    let case = Case {
        pc_bar: None,
        pc_lhs: pvb_pat,
        pc_guard: None,
        pc_rhs: *body,
    };

    // Replace the expression with a match
    expr.pexp_desc = ExpressionDesc::Pexp_match(Box::new(pvb_expr), vec![case]);

    // Merge attributes: expression attributes + binding attributes
    let mut combined_attrs = let_attrs;
    combined_attrs.extend(pvb_attributes);
    expr.pexp_attributes = combined_attrs;

    true
}
