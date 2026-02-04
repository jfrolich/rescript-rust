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
//! This mirrors the transformations in `compiler/frontend/bs_builtin_ppx.ml`.

use super::ast::{
    Case, Expression, ExpressionDesc, Loc, Pattern, PatternDesc, RecFlag, Structure, StructureItem,
    StructureItemDesc, ValueBinding,
};
use crate::parse_arena::LidentIdx;

/// Transform a structure with built-in PPX transformations.
pub fn transform_structure(structure: &mut Structure) {
    for item in structure.iter_mut() {
        transform_structure_item(item);
    }
}

/// Transform a structure item.
fn transform_structure_item(item: &mut StructureItem) {
    match &mut item.pstr_desc {
        StructureItemDesc::Pstr_eval(expr, _) => {
            transform_expression(expr);
        }
        StructureItemDesc::Pstr_value(_, bindings) => {
            for binding in bindings.iter_mut() {
                transform_expression(&mut binding.pvb_expr);
            }
        }
        StructureItemDesc::Pstr_module(module_binding) => {
            transform_module_expr(&mut module_binding.pmb_expr);
        }
        StructureItemDesc::Pstr_recmodule(module_bindings) => {
            for mb in module_bindings.iter_mut() {
                transform_module_expr(&mut mb.pmb_expr);
            }
        }
        StructureItemDesc::Pstr_include(incl) => {
            transform_module_expr(&mut incl.pincl_mod);
        }
        // Other items don't need transformation
        _ => {}
    }
}

/// Transform a module expression.
fn transform_module_expr(mexpr: &mut super::ast::ModuleExpr) {
    match &mut mexpr.pmod_desc {
        super::ast::ModuleExprDesc::Pmod_structure(structure) => {
            transform_structure(structure);
        }
        super::ast::ModuleExprDesc::Pmod_functor(_, _, body) => {
            transform_module_expr(body);
        }
        super::ast::ModuleExprDesc::Pmod_apply(m1, m2) => {
            transform_module_expr(m1);
            transform_module_expr(m2);
        }
        super::ast::ModuleExprDesc::Pmod_constraint(m, _) => {
            transform_module_expr(m);
        }
        super::ast::ModuleExprDesc::Pmod_unpack(e) => {
            transform_expression(e);
        }
        _ => {}
    }
}

/// Transform an expression recursively.
fn transform_expression(expr: &mut Expression) {
    // First, apply the record let → match transformation
    let transformed = try_transform_record_let(expr);

    // Now recurse into sub-expressions based on the (possibly transformed) expression
    let target = if transformed { expr } else { expr };

    match &mut target.pexp_desc {
        ExpressionDesc::Pexp_let(_, bindings, body) => {
            for binding in bindings.iter_mut() {
                transform_expression(&mut binding.pvb_expr);
            }
            transform_expression(body);
        }
        ExpressionDesc::Pexp_fun { default, rhs, .. } => {
            if let Some(d) = default {
                transform_expression(d);
            }
            transform_expression(rhs);
        }
        ExpressionDesc::Pexp_apply { funct, args, .. } => {
            transform_expression(funct);
            for (_, arg) in args.iter_mut() {
                transform_expression(arg);
            }
        }
        ExpressionDesc::Pexp_match(scrutinee, cases) => {
            transform_expression(scrutinee);
            for case in cases.iter_mut() {
                if let Some(guard) = &mut case.pc_guard {
                    transform_expression(guard);
                }
                transform_expression(&mut case.pc_rhs);
            }
        }
        ExpressionDesc::Pexp_try(body, cases) => {
            transform_expression(body);
            for case in cases.iter_mut() {
                if let Some(guard) = &mut case.pc_guard {
                    transform_expression(guard);
                }
                transform_expression(&mut case.pc_rhs);
            }
        }
        ExpressionDesc::Pexp_tuple(exprs) => {
            for e in exprs.iter_mut() {
                transform_expression(e);
            }
        }
        ExpressionDesc::Pexp_construct(_, Some(arg)) => {
            transform_expression(arg);
        }
        ExpressionDesc::Pexp_variant(_, Some(arg)) => {
            transform_expression(arg);
        }
        ExpressionDesc::Pexp_record(fields, spread) => {
            for field in fields.iter_mut() {
                transform_expression(&mut field.expr);
            }
            if let Some(s) = spread {
                transform_expression(s);
            }
        }
        ExpressionDesc::Pexp_field(e, _) => {
            transform_expression(e);
        }
        ExpressionDesc::Pexp_setfield(e1, _, e2) => {
            transform_expression(e1);
            transform_expression(e2);
        }
        ExpressionDesc::Pexp_array(exprs) => {
            for e in exprs.iter_mut() {
                transform_expression(e);
            }
        }
        ExpressionDesc::Pexp_ifthenelse(cond, then_, else_) => {
            transform_expression(cond);
            transform_expression(then_);
            if let Some(e) = else_ {
                transform_expression(e);
            }
        }
        ExpressionDesc::Pexp_sequence(e1, e2) => {
            transform_expression(e1);
            transform_expression(e2);
        }
        ExpressionDesc::Pexp_while(cond, body) => {
            transform_expression(cond);
            transform_expression(body);
        }
        ExpressionDesc::Pexp_for(_, e1, e2, _, body) => {
            transform_expression(e1);
            transform_expression(e2);
            transform_expression(body);
        }
        ExpressionDesc::Pexp_constraint(e, _) => {
            transform_expression(e);
        }
        ExpressionDesc::Pexp_coerce(e, _, _) => {
            transform_expression(e);
        }
        ExpressionDesc::Pexp_send(e, _) => {
            transform_expression(e);
        }
        ExpressionDesc::Pexp_letmodule(_, me, body) => {
            transform_module_expr(me);
            transform_expression(body);
        }
        ExpressionDesc::Pexp_letexception(_, body) => {
            transform_expression(body);
        }
        ExpressionDesc::Pexp_assert(e) => {
            transform_expression(e);
        }
        ExpressionDesc::Pexp_newtype(_, e) => {
            transform_expression(e);
        }
        ExpressionDesc::Pexp_pack(me) => {
            transform_module_expr(me);
        }
        ExpressionDesc::Pexp_open(_, _, e) => {
            transform_expression(e);
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
