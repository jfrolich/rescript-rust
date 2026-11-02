//! Expression parsing for ReScript.
//!
//! This module contains the expression parsing logic, converting tokens
//! into expression AST nodes.

use super::module::parse_attributes;
use std::borrow::Cow;

use crate::parse_arena::{ExprIdx, LidentIdx, LocIdx, Located, ParseArena, PosIdx, StrIdx};

use super::ast::*;
use super::core::{ExprContext, ast_helper, mknoloc, recover, with_loc};
use super::diagnostics::DiagnosticCategory;
use super::grammar;
use super::grammar::Grammar;
use super::longident::Longident;
use super::state::Parser;
use super::token::Token;
use crate::location::Position;

// ============================================================================
// Constants
// ============================================================================

/// OCaml `parse_string_constant` (res_core.ml): validate an ordinary string
/// literal body, reporting an invalid escape or code point unless a scanner
/// diagnostic already covers the literal.
pub fn parse_string_constant(
    p: &mut Parser<'_>,
    start_pos: Position,
    end_pos: Position,
    source: &str,
) -> Constant {
    match crate::string_literal::string_from_source(source) {
        Some(payload) => Constant::String(payload),
        None => {
            let has_literal_diagnostic = p.diagnostics().iter().any(|diagnostic| {
                let diagnostic_start = diagnostic.start_pos();
                diagnostic_start.cnum >= start_pos.cnum && diagnostic_start.cnum <= end_pos.cnum
            });
            if !has_literal_diagnostic {
                let message = if crate::string_literal::is_valid_utf8(source) {
                    "Invalid string escape sequence"
                } else {
                    "Invalid code point"
                };
                p.err_at(
                    start_pos,
                    end_pos,
                    DiagnosticCategory::Message(message.to_string()),
                );
            }
            Constant::String(crate::string_literal::invalid_string_for_recovery(source))
        }
    }
}

/// Parse a constant value (number, string, char, etc).
/// OCaml `parse_constant` (compiler/syntax/src/res_core.ml:1004-1043).
pub fn parse_constant(p: &mut Parser<'_>) -> Constant {
    let is_negative = match p.token {
        Token::Minus => {
            p.next();
            true
        }
        Token::Plus => {
            p.next();
            false
        }
        _ => false,
    };
    let constant = match &p.token {
        Token::Int { i, suffix } => {
            let s = *suffix;
            let i = extend_cow_lifetime(i.clone());
            if s == Some('n') && !is_valid_bigint_literal(&i) {
                p.err(DiagnosticCategory::Message(
                    "Invalid bigint literal. Only decimal literal is allowed for bigint."
                        .to_string(),
                ));
            }
            let value = if is_negative {
                Cow::Owned(format!("-{i}"))
            } else {
                i
            };
            Constant::Integer(value, s)
        }
        Token::Float { f, suffix } => {
            let value = if is_negative {
                Cow::Owned(format!("-{f}"))
            } else {
                extend_cow_lifetime(f.clone())
            };
            Constant::Float(value, *suffix)
        }
        Token::String(s) => {
            let source = s.clone();
            let (start_pos, end_pos) = (p.start_pos, p.end_pos);
            parse_string_constant(p, start_pos, end_pos, &source)
        }
        Token::Codepoint { c, original } => Constant::Char {
            source: extend_cow_lifetime(original.clone()),
            semantic: *c,
        },
        _ => {
            p.err_unexpected();
            Constant::string("")
        }
    };
    p.next_unsafe();
    constant
}

fn is_valid_bigint_literal(s: &str) -> bool {
    if s.is_empty() {
        return false;
    }

    let mut chars = s.chars();
    let first = chars.next().unwrap();
    if first != '-' && first != '+' && !first.is_ascii_digit() && first != '_' {
        return false;
    }

    chars.all(|c| c.is_ascii_digit() || c == '_')
}

// ============================================================================
// Placeholder Transformation
// ============================================================================

/// Check and emit "consecutive expressions" error if expressions on same line without semicolon.
///
/// Matches OCaml's `parse_newline_or_semicolon_expr_block`:
/// - If token is Semicolon, consume it
/// - If token can start a block expression AND on same line as previous, emit error
/// - Otherwise, do nothing
pub fn parse_newline_or_semicolon_expr_block(p: &mut Parser<'_>) {
    if p.token == Token::Semicolon {
        p.next();
        return;
    }

    if grammar::is_block_expr_start(&p.token) {
        // Check if we're on the same line as the previous token
        // OCaml: if p.prev_end_pos.pos_lnum < p.start_pos.pos_lnum then () else err
        if p.prev_end_pos.line >= p.start_pos.line {
            // Same line: emit error
            // Use err_at which respects regions (like OCaml's Parser.err)
            p.err_at(
                p.prev_end_pos,
                p.end_pos,
                DiagnosticCategory::message(
                    "consecutive expressions on a line must be separated by ';' or a newline",
                ),
            );
        }
    }
}

/// Check if an expression is the underscore placeholder `_`
fn is_underscore_placeholder(expr: &Expression, arena: &ParseArena) -> bool {
    match &*expr.pexp_desc {
        ExpressionDesc::Pexp_ident(loc) => arena.is_lident(loc.txt, "_"),
        _ => false,
    }
}

/// Replace underscore placeholders with a reference to the given variable name.
/// Creates a new LidentIdx for each replacement, but all share the same StrIdx.
/// This matches OCaml where each `Longident.Lident hidden_var` is a new block,
/// but the string inside (`hidden_var`) is the same pointer and gets shared.
fn replace_underscores_in_expr(
    expr: Expression,
    var_str_idx: StrIdx,
    arena: &mut ParseArena,
) -> Expression {
    if is_underscore_placeholder(&expr, arena) {
        let loc = expr.pexp_loc;
        // Create a NEW LidentIdx for this use (OCaml creates a new Lident block each time)
        // but using the SHARED StrIdx (OCaml's hidden_var string is the same pointer).
        // The marshaller will share the string via StrIdx-based sharing.
        let lid_idx = arena.push_lident_from_idx(var_str_idx);
        Expression {
            pexp_desc: Box::new(ExpressionDesc::Pexp_ident(with_loc(lid_idx, loc))),
            pexp_loc: loc,
            pexp_attributes: Attributes::new(),
        }
    } else {
        expr
    }
}

/// Transform function application with underscore placeholders.
/// f(a, _, b) becomes: fun __x -> f(a, __x, b)
fn transform_placeholder_application(
    funct: ExprIdx,
    args: Vec<(ArgLabel, Expression)>,
    partial: bool,
    loc: Location,
    arena: &mut ParseArena,
) -> Expression {
    // Find the LAST underscore placeholder and get its location
    // OCaml uses a mutable ref that gets overwritten for each underscore found,
    // so the last one's location is used
    let underscore_loc = args
        .iter()
        .filter_map(|(_, expr)| {
            if is_underscore_placeholder(expr, arena) {
                Some(expr.pexp_loc)
            } else {
                None
            }
        })
        .last();

    let underscore_loc = match underscore_loc {
        Some(loc) => loc,
        None => {
            // No placeholders, return normal Pexp_apply
            let args: Vec<(ArgLabel, ExprIdx)> = args
                .into_iter()
                .map(|(l, e)| (l, arena.push_expr(e)))
                .collect();
            return Expression {
                pexp_desc: Box::new(ExpressionDesc::Pexp_apply(Box::new(PexpApply {
                    funct,
                    args,
                    partial,
                    transformed_jsx: false,
                }))),
                pexp_loc: loc,
                pexp_attributes: Attributes::new(),
            };
        }
    };

    // Intern __x ONCE so both the pattern and all identifier uses share the same StrIdx.
    // This matches OCaml where `hidden_var` is a single string binding used everywhere.
    // The marshaller will share the string via StrIdx-based sharing.
    let var_str_idx = arena.intern("__x");

    // Replace all underscores with __x (each gets a NEW LidentIdx but same StrIdx)
    let transformed_args: Vec<(ArgLabel, ExprIdx)> = args
        .into_iter()
        .map(|(label, expr)| {
            let replaced = replace_underscores_in_expr(expr, var_str_idx, arena);
            (label, arena.push_expr(replaced))
        })
        .collect();

    // Create the inner Pexp_apply
    let inner_apply = Expression {
        pexp_desc: Box::new(ExpressionDesc::Pexp_apply(Box::new(PexpApply {
            funct,
            args: transformed_args,
            partial,
            transformed_jsx: false,
        }))),
        pexp_loc: loc,
        pexp_attributes: Attributes::new(),
    };

    // Create Pexp_fun wrapping the application
    // OCaml: pattern has ppat_loc: Location.none, but StringLoc uses underscore's location
    let pattern = Pattern {
        ppat_desc: Box::new(PatternDesc::Ppat_var(with_loc(var_str_idx, underscore_loc))),
        ppat_loc: LocIdx::none(),
        ppat_attributes: Attributes::new(),
    };

    // LITERAL path: OCaml line 614 `Exp.fun_ ~arity:(Some 1)` (underscore sugar)
    // Use static arity to match OCaml's CSE sharing behavior
    let rhs_idx = arena.push_expr(inner_apply);
    let pat_idx = arena.push_pat(pattern);
    Expression {
        pexp_desc: Box::new(ExpressionDesc::Pexp_fun(Box::new(PexpFun {
            arg_label: ArgLabel::Nolabel,
            default: None,
            lhs: pat_idx,
            rhs: rhs_idx,
            arity: arena.static_arity_1(),
            is_async: false,
        }))),
        pexp_loc: underscore_loc,
        pexp_attributes: Attributes::new(),
    }
}

// ============================================================================
// Value and Constructor Parsing
// ============================================================================

/// OCaml `parse_value_path_after_dot` (res_core.ml:778-784).
fn parse_value_path_after_dot(p: &mut Parser<'_>) -> Located<LidentIdx> {
    let start_pos_idx = p.start_pos_idx();
    match p.token {
        Token::Lident(_) | Token::Uident(_) => {
            let (parts, loc) = super::module::parse_value_path(p);
            let lid = super::core::build_longident(p.arena_mut(), &parts);
            let lid_idx = p.push_longident(lid);
            with_loc(lid_idx, loc)
        }
        _ => {
            p.err_unexpected();
            let lid_idx = p.push_lident("_");
            let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
            with_loc(lid_idx, loc)
        }
    }
}

/// OCaml `parse_value_or_constructor` (compiler/syntax/src/res_core.ml:4212-4267).
pub fn parse_value_or_constructor(p: &mut Parser<'_>) -> Expression {
    let start_pos_idx = p.start_pos_idx();
    let mut acc: Vec<Cow<'_, str>> = Vec::new();
    loop {
        match p.token.clone() {
            Token::Uident(ident) => {
                let end_pos_lident = p.end_pos_idx();
                p.next();
                match p.token {
                    Token::Dot => {
                        p.next();
                        acc.push(ident);
                    }
                    Token::Lparen if p.prev_end_pos.line == p.start_pos.line => {
                        let args = parse_constructor_args(p);
                        acc.push(ident);
                        let lid_idx = super::core::build_longident_idx(p, &acc);
                        let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
                        let ident_loc = p.mk_loc_idx(start_pos_idx, end_pos_lident);
                        return Expression {
                            pexp_desc: Box::new(ExpressionDesc::Pexp_construct(
                                with_loc(lid_idx, ident_loc),
                                Box::new(args),
                            )),
                            pexp_loc: loc,
                            pexp_attributes: Attributes::new(),
                        };
                    }
                    _ => {
                        let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
                        acc.push(ident);
                        let lid_idx = super::core::build_longident_idx(p, &acc);
                        return Expression {
                            pexp_desc: Box::new(ExpressionDesc::Pexp_construct(
                                with_loc(lid_idx, loc),
                                ctor_args(Vec::new(), loc),
                            )),
                            pexp_loc: loc,
                            pexp_attributes: Attributes::new(),
                        };
                    }
                }
            }
            Token::Lident(ident) => {
                p.next();
                let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
                acc.push(ident);
                let lid_idx = super::core::build_longident_idx(p, &acc);
                return ast_helper::make_ident_idx(lid_idx, loc);
            }
            token => {
                let token = token.into_owned();
                if acc.is_empty() {
                    p.next_unsafe();
                    let context = p.breadcrumbs().to_vec();
                    p.err(DiagnosticCategory::Unexpected { token, context });
                    return recover::default_expr(p.arena_mut());
                }
                let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
                let context = p.breadcrumbs().to_vec();
                p.err(DiagnosticCategory::Unexpected { token, context });
                acc.push(Cow::Borrowed("_"));
                let lid_idx = super::core::build_longident_idx(p, &acc);
                return ast_helper::make_ident_idx(lid_idx, loc);
            }
        }
    }
}

/// OCaml `parse_coerced_expr` (compiler/syntax/src/res_core.ml:2042-2046).
fn parse_coerced_expr(p: &mut Parser<'_>, expr: Expression) -> Expression {
    p.expect(Token::ColonGreaterThan);
    let typ = super::typ::parse_typ_expr(p);
    let expr_start_idx = p.loc_start_idx(expr.pexp_loc);
    let loc = p.mk_loc_idx_to_prev_end(expr_start_idx);
    let expr_idx = p.arena_mut().push_expr(expr);
    let typ_idx = p.arena_mut().push_core_type(typ);
    Expression {
        pexp_desc: Box::new(ExpressionDesc::Pexp_coerce(Box::new((
            expr_idx, None, typ_idx,
        )))),
        pexp_loc: loc,
        pexp_attributes: Attributes::new(),
    }
}

/// OCaml `parse_constrained_expr_region` (compiler/syntax/src/res_core.ml:2064-2076).
pub(super) fn parse_constrained_expr_region(p: &mut Parser<'_>) -> Option<Expression> {
    if !super::grammar::is_expr_start(&p.token) {
        return None;
    }
    let expr = parse_expr(p);
    match p.token {
        Token::ColonGreaterThan => Some(parse_coerced_expr(p, expr)),
        Token::Colon => {
            p.next();
            let typ = super::typ::parse_typ_expr(p);
            let loc = p.mk_loc_spanning(expr.pexp_loc, typ.ptyp_loc);
            let expr_idx = p.arena_mut().push_expr(expr);
            let typ_idx = p.arena_mut().push_core_type(typ);
            Some(Expression {
                pexp_desc: Box::new(ExpressionDesc::Pexp_constraint(Box::new((
                    expr_idx, typ_idx,
                )))),
                pexp_loc: loc,
                pexp_attributes: Attributes::new(),
            })
        }
        _ => Some(expr),
    }
}

/// OCaml `parse_constructor_args` (compiler/syntax/src/res_core.ml:4299-4315).
/// OCaml `parse_constructor_args` (res_core.ml): the argument list, located
/// at its parentheses. `C()` is `C(())`.
fn parse_constructor_args(p: &mut Parser<'_>) -> Located<Vec<ExprIdx>> {
    let lparen = p.start_pos_idx();
    p.expect(Token::Lparen);
    let args = super::core::parse_comma_delimited_region(
        p,
        Grammar::ExprList,
        Token::Rparen,
        parse_constrained_expr_region,
    );
    p.expect(Token::Rparen);
    let loc = p.mk_loc_idx_to_prev_end(lparen);
    let args = if args.is_empty() {
        let lid_idx = p.push_lident_static("()");
        vec![Expression {
            pexp_desc: Box::new(ExpressionDesc::Pexp_construct(
                with_loc(lid_idx, loc),
                ctor_args(Vec::new(), loc),
            )),
            pexp_loc: loc,
            pexp_attributes: Attributes::new(),
        }]
    } else {
        args
    };
    let txt = args
        .into_iter()
        .map(|e| p.arena_mut().push_expr(e))
        .collect();
    Located { txt, loc }
}

// ============================================================================
// Main Expression Parsing
// ============================================================================

/// Parse an expression.
pub fn parse_expr(p: &mut Parser<'_>) -> Expression {
    parse_expr_with_context(p, ExprContext::Ordinary)
}

/// Parse an expression starting from an already-parsed operand.
/// Used when the caller has parsed an atomic expression and wants to continue.
pub fn parse_expr_with_operand(p: &mut Parser<'_>, operand: Expression) -> Expression {
    // Continue with primary parsing (function calls, field access, etc.)
    let expr = parse_primary_expr(p, operand, false);
    // Then binary and ternary
    let expr = parse_binary_expr(p, expr, 1, ExprContext::Ordinary);
    parse_ternary_expr(p, expr)
}

/// Parse an expression with a specific context.
pub fn parse_expr_with_context(p: &mut Parser<'_>, context: ExprContext) -> Expression {
    let expr = parse_operand_expr(p, context);
    let expr = parse_binary_expr(p, expr, 1, context);
    // OCaml `parse_expr` (res_core.ml:1780-1783) stops after the ternary;
    // coercions are only parsed by the callers that expect them.
    parse_ternary_expr(p, expr)
}

/// Parse a ternary expression (condition ? true_branch : false_branch).
pub fn parse_ternary_expr(p: &mut Parser<'_>, left_operand: Expression) -> Expression {
    if p.token == Token::Question {
        p.leave_breadcrumb(Grammar::Ternary);
        p.next();

        let true_branch = parse_expr_with_context(p, ExprContext::TernaryTrueBranch);
        p.expect(Token::Colon);
        let false_branch = parse_expr(p);

        p.eat_breadcrumb();

        let loc = p.mk_loc_spanning(left_operand.pexp_loc, false_branch.pexp_loc);

        let cond_idx = p.arena_mut().push_expr(left_operand);
        let true_idx = p.arena_mut().push_expr(true_branch);
        let false_idx = p.arena_mut().push_expr(false_branch);
        Expression {
            pexp_desc: Box::new(ExpressionDesc::Pexp_ternary(Box::new((
                cond_idx, true_idx, false_idx,
            )))),
            pexp_loc: loc,
            pexp_attributes: Attributes::new(),
        }
    } else {
        left_operand
    }
}

/// Parse an operand expression (handles unary operators and primary expressions).
pub fn parse_operand_expr(p: &mut Parser<'_>, context: ExprContext) -> Expression {
    let start_pos_idx = p.start_pos_idx();

    // Parse leading attributes first (e.g., @attr expr)
    let mut attrs = parse_attributes(p);

    // Handle unary operators
    // Track whether attrs were passed to arrow expression (so we don't attach them twice)
    let (expr, attrs_consumed) = match &p.token {
        Token::Plus
        | Token::PlusDot
        | Token::Minus
        | Token::MinusDot
        | Token::Bang
        | Token::Bnot => {
            let token = p.token.clone();
            p.leave_breadcrumb(Grammar::ExprUnary);
            p.next();
            let token_end_idx = p.prev_end_pos_idx();
            let operand = parse_unary_expr(p);
            p.eat_breadcrumb();
            (
                super::core::make_unary_expr(p, start_pos_idx, token_end_idx, token, operand),
                false,
            )
        }
        Token::Lident(s) if s == "async" => {
            // async arrow function
            // OCaml res_core.ml:2366-2374 runs `is_es6_arrow_expression` with
            // `async` still the current token.
            let is_arrow =
                super::core::is_es6_arrow_expression(p, context == ExprContext::TernaryTrueBranch);
            p.next();
            if is_arrow {
                // The arrow consumes attrs; its location starts after `async`.
                (
                    parse_es6_arrow_expression_async(p, std::mem::take(&mut attrs), context),
                    true,
                )
            } else {
                // Just a regular "async" identifier - continue with primary expr parsing
                // to handle function calls like async(x)
                let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
                let lid_idx = p.push_lident("async");
                let ident = ast_helper::make_ident_idx(lid_idx, loc);
                (parse_primary_expr(p, ident, false), false)
            }
        }
        Token::Await => (parse_await_expression(p), false),
        // OCaml res_core.ml:2377-2381: these are operands, not atomic
        // expressions, so no unary operator or postfix applies to them.
        Token::Try => (parse_try_expr(p), false),
        Token::If => (parse_if_expr(p), false),
        Token::For => (parse_for_expr(p), false),
        Token::While => (parse_while_expr(p), false),
        Token::Switch => (parse_switch_expr(p), false),
        Token::Assert => {
            // Handle assert directly to preserve attribute location in expr location
            p.next();
            let arg = parse_expr(p);
            let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
            let arg_idx = p.arena_mut().push_expr(arg);
            (
                Expression {
                    pexp_desc: Box::new(ExpressionDesc::Pexp_assert(arg_idx)),
                    pexp_loc: loc,
                    pexp_attributes: Attributes::new(),
                },
                false,
            )
        }
        _ => {
            let is_arrow = context != ExprContext::When
                && super::core::is_es6_arrow_expression(
                    p,
                    context == ExprContext::TernaryTrueBranch,
                );
            if is_arrow {
                // The arrow consumes attrs.
                (
                    parse_es6_arrow_expression(p, false, None, std::mem::take(&mut attrs), context),
                    true,
                )
            } else {
                (parse_unary_expr(p), false)
            }
        }
    };

    // Attach attributes to the expression if not already consumed by arrow expression
    if attrs.is_empty() || attrs_consumed {
        expr
    } else {
        // Combine existing attributes with parsed attributes
        let mut expr = expr;
        expr.pexp_attributes.extend(attrs);
        expr
    }
}

/// Parse a unary expression.
pub fn parse_unary_expr(p: &mut Parser<'_>) -> Expression {
    // OCaml `parse_unary_expr` (compiler/syntax/src/res_core.ml:2340-2351):
    // attributes belong to the enclosing operand, not to unary expressions.
    let start_pos_idx = p.start_pos_idx();

    match &p.token {
        Token::Plus
        | Token::PlusDot
        | Token::Minus
        | Token::MinusDot
        | Token::Bang
        | Token::Bnot => {
            let token = p.token.clone();
            p.leave_breadcrumb(Grammar::ExprUnary);
            p.next();
            let token_end_idx = p.prev_end_pos_idx();
            let operand = parse_unary_expr(p);
            p.eat_breadcrumb();
            super::core::make_unary_expr(p, start_pos_idx, token_end_idx, token, operand)
        }
        _ => {
            let atomic = parse_atomic_expr(p);
            parse_primary_expr(p, atomic, false)
        }
    }
}

/// Parse an await expression.
pub fn parse_await_expression(p: &mut Parser<'_>) -> Expression {
    let start_pos_idx = p.start_pos_idx();
    p.expect(Token::Await);
    // Parse with -> precedence to match OCaml behavior
    // This allows: await x->Promise.resolve to parse as await (x->Promise.resolve)
    let token_prec = Token::MinusGreater.precedence();
    // OCaml `parse_binary_expr` without `~a` starts with `parse_operand_expr`,
    // which parses the operand's attributes (compiler/syntax/src/res_core.ml:3694-3701).
    let operand = parse_operand_expr(p, ExprContext::Ordinary);
    let expr = parse_binary_expr(p, operand, token_prec, ExprContext::Ordinary);
    let loc = p.mk_loc_idx_to_end_of(start_pos_idx, expr.pexp_loc);

    let expr_idx = p.arena_mut().push_expr(expr);
    Expression {
        pexp_desc: Box::new(ExpressionDesc::Pexp_await(expr_idx)),
        pexp_loc: loc,
        pexp_attributes: Attributes::new(),
    }
}

/// Parse an ES6 arrow function expression for async functions, called after
/// `async` was consumed (the Pexp_fun location starts after `async`).
fn parse_es6_arrow_expression_async(
    p: &mut Parser<'_>,
    arrow_attrs: Attributes,
    context: ExprContext,
) -> Expression {
    parse_es6_arrow_expression_internal(p, true, None, arrow_attrs, context, None)
}

/// Parse an ES6 arrow function expression.
pub fn parse_es6_arrow_expression(
    p: &mut Parser<'_>,
    is_async: bool,
    arrow_start_pos_idx: Option<PosIdx>,
    arrow_attrs: Attributes,
    context: ExprContext,
) -> Expression {
    parse_es6_arrow_expression_internal(
        p,
        is_async,
        arrow_start_pos_idx,
        arrow_attrs,
        context,
        None,
    )
}

/// Internal implementation of ES6 arrow expression parsing.
fn parse_es6_arrow_expression_internal(
    p: &mut Parser<'_>,
    is_async: bool,
    arrow_start_pos_idx: Option<PosIdx>,
    arrow_attrs: Attributes,
    context: ExprContext,
    term_parameters: Option<Vec<super::core::FundefParameter>>,
) -> Expression {
    let start_pos_idx = arrow_start_pos_idx.unwrap_or_else(|| p.start_pos_idx());
    p.leave_breadcrumb(Grammar::Es6ArrowExpr);

    // OCaml `parse_es6_arrow_expression ?term_parameters` (res_core.ml:1806-1818).
    let parameters = match term_parameters {
        Some(parameters) => parameters,
        None => parse_parameters(p),
    };

    // Parse optional return type
    // We use parse_typ_expr_no_arrow to avoid confusing the return type
    // with the arrow body (e.g., (x): int => body shouldn't parse as int => body)
    let return_type = if p.token == Token::Colon {
        p.next();
        Some(super::typ::parse_typ_expr_no_arrow(p))
    } else {
        None
    };

    // Expect =>
    p.expect(Token::EqualGreater);

    // Parse body
    let body = parse_expr_with_context(p, context);
    let body = match return_type {
        Some(typ) => {
            let loc = p.mk_loc_spanning(body.pexp_loc, typ.ptyp_loc);
            let body_idx = p.arena_mut().push_expr(body);
            let typ_idx = p.arena_mut().push_core_type(typ);
            Expression {
                pexp_desc: Box::new(ExpressionDesc::Pexp_constraint(Box::new((
                    body_idx, typ_idx,
                )))),
                pexp_loc: loc,
                pexp_attributes: Attributes::new(),
            }
        }
        None => body,
    };

    p.eat_breadcrumb();
    // Use PosIdx for end position to enable sharing with body's loc_end
    // In OCaml, `end_pos = p.prev_end_pos` is captured once and reused for all
    // Pexp_fun locations. We mimic this by getting a cached PosIdx.
    let end_pos_idx = p.prev_end_pos_idx();

    // Build the function expression from parameters
    let (type_params, term_params) = super::core::extract_fundef_params(parameters);
    let has_type_params = !type_params.is_empty();

    // Build the authoritative `Pexp_fun.newtypes` list: each type-parameter
    // group carries its attributes on its first newtype (mirrors upstream
    // res_core.ml `newtypes` construction).
    let mut newtypes: Vec<(StringLoc, Attributes)> = Vec::new();
    for tp in &type_params {
        let mut locs = tp.locs.iter();
        if let Some(first) = locs.next() {
            newtypes.push((*first, tp.attrs.clone()));
            for name in locs {
                newtypes.push((*name, Attributes::new()));
            }
        }
    }

    // Fold the term parameters into nested functions
    // If there are type params but no term params, add an implicit unit param
    // We capture the Pexp_fun location for use in the final wrapper (for position sharing)
    let (arrow_expr, pexp_fun_loc) = if term_params.is_empty() && has_type_params {
        // Implicit unit parameter for type-only arrow
        // OCaml uses the location of the parenthesized type params group for the implicit unit PATTERN
        // but the Pexp_fun location spans from the paren start to the end of the body
        let tp = &type_params[0];
        let (unit_pat_loc, pexp_fun_loc) = match (tp.paren_start_pos_idx, tp.paren_end_pos_idx) {
            (Some(start_idx), Some(paren_end_idx)) => {
                (
                    p.mk_loc_idx(start_idx, paren_end_idx), // Pattern: from ( to )
                    p.mk_loc_idx(start_idx, end_pos_idx),   // Pexp_fun: from ( to end of body
                )
            }
            _ => {
                let loc = p.mk_loc_idx(tp.start_pos_idx, end_pos_idx);
                (loc, loc)
            }
        };
        let unit_lid = p.push_lident_static("()");
        let unit_pat = Pattern {
            ppat_desc: Box::new(PatternDesc::Ppat_construct(
                with_loc(unit_lid, unit_pat_loc),
                ctor_args(Vec::new(), unit_pat_loc),
            )),
            ppat_loc: unit_pat_loc,
            ppat_attributes: Attributes::new(),
        };
        let rhs_idx = p.arena_mut().push_expr(body);
        let unit_pat_idx = p.arena_mut().push_pat(unit_pat);
        (
            Expression {
                pexp_desc: Box::new(ExpressionDesc::Pexp_fun(Box::new(PexpFun {
                    arg_label: ArgLabel::Nolabel,
                    default: None,
                    lhs: unit_pat_idx,
                    rhs: rhs_idx,
                    arity: p.push_arity_full(1), // Implicit unit param has arity 1
                    is_async,
                }))),
                pexp_loc: pexp_fun_loc,
                pexp_attributes: arrow_attrs,
            },
            pexp_fun_loc,
        )
    } else if term_params.is_empty() {
        // No params at all - use a dummy location (shouldn't happen in practice)
        let loc = p.mk_loc_idx(end_pos_idx, end_pos_idx);
        (body, loc)
    } else {
        // Upstream parsetree stores all source parameters on one Pexp_fun.
        // Keep that logical shape in the arena side table while retaining the
        // compact first-parameter payload needed by frozen-v0 PPX conversion.
        let total_arity = term_params.len();
        let full_arity_idx = p.push_arity_full(total_arity);
        let unknown_arity_idx = p.push_arity_unknown();
        let outermost_param = &term_params[0];
        let pattern_start_idx = p.loc_start_idx(outermost_param.pat.ppat_loc);
        let wrapper_start_idx = if start_pos_idx == pattern_start_idx {
            pattern_start_idx
        } else {
            start_pos_idx
        };
        let wrapper_loc = p.mk_loc_idx(wrapper_start_idx, end_pos_idx);
        let body_idx = p.arena_mut().push_expr(body);
        let mut params = Vec::with_capacity(total_arity);
        for param in term_params {
            let default = param.expr.map(|expr| p.arena_mut().push_expr(expr));
            let pat = p.arena_mut().push_pat(param.pat);
            params.push(FunParam {
                p_attrs: param.attrs,
                p_lbl: param.label,
                p_default: default,
                p_pat: pat,
            });
        }
        let first = params[0].clone();
        p.arena_mut()
            .set_nary_fun_params(full_arity_idx, params, unknown_arity_idx);
        (
            Expression {
                pexp_desc: Box::new(ExpressionDesc::Pexp_fun(Box::new(PexpFun {
                    arg_label: first.p_lbl,
                    default: first.p_default,
                    lhs: first.p_pat,
                    rhs: body_idx,
                    arity: full_arity_idx,
                    is_async,
                }))),
                pexp_loc: wrapper_loc,
                pexp_attributes: arrow_attrs,
            },
            wrapper_loc,
        )
    };

    // Register the authoritative `Pexp_fun.newtypes` list beside the parameter
    // table, keyed by the function's first parameter pattern.
    if !newtypes.is_empty()
        && let ExpressionDesc::Pexp_fun(inner) = &*arrow_expr.pexp_desc
    {
        p.arena_mut().set_nary_fun_newtypes(inner.lhs, newtypes);
    }

    // Update the location, preserving position sharing.
    // In OCaml (res_core.ml line 1807):
    //   {arrow_expr with pexp_loc = {arrow_expr.pexp_loc with loc_start = start_pos}}
    //
    // For position sharing: we use pexp_fun_loc which has the correct loc_start PosIdx
    // (from the parameter pattern's location). In OCaml, start_pos at line 1726 and
    // parameter.p_pos are the SAME object (both captured from p.Parser.start_pos before
    // any tokens were consumed). So the final record update doesn't create a new position.
    //
    // We use pexp_fun_loc (captured before newtype wrapping) to get the correct indices.
    // This ensures the final wrapper uses the same position indices as the Pexp_fun,
    // achieving the same sharing as OCaml where start_pos and parameter.p_pos are
    // the same object.
    let start_idx = p.loc_start_idx(pexp_fun_loc);
    let end_idx = p.loc_end_idx(pexp_fun_loc);
    Expression {
        pexp_loc: p.mk_loc_idx(start_idx, end_idx),
        ..arrow_expr
    }
}

/// Parse function parameters.
fn parse_parameters(p: &mut Parser<'_>) -> Vec<super::core::FundefParameter> {
    let mut params = vec![];

    match &p.token {
        Token::Lparen => {
            let lparen_pos_idx = p.start_pos_idx();
            p.next();

            // Skip deprecated uncurried marker.
            let had_dot = if p.token == Token::Dot {
                p.warn_uncurried_dot_syntax();
                p.next();
                true
            } else {
                false
            };

            if p.token == Token::Rparen {
                // Unit parameter: () or (.)
                let end_pos_idx = p.end_pos_idx();
                p.next();
                let loc = p.mk_loc_idx(lparen_pos_idx, end_pos_idx);
                let unit_lid = p.push_lident_static("()");
                let unit_pat = Pattern {
                    ppat_desc: Box::new(PatternDesc::Ppat_construct(
                        with_loc(unit_lid, loc),
                        ctor_args(Vec::new(), loc),
                    )),
                    ppat_loc: loc,
                    ppat_attributes: Attributes::new(),
                };
                params.push(super::core::FundefParameter::Term(
                    super::core::FundefTermParam {
                        attrs: Attributes::new(),
                        label: ArgLabel::Nolabel,
                        expr: None,
                        pat: unit_pat,
                        start_pos_idx: lparen_pos_idx,
                    },
                ));
            } else if had_dot {
                // We had a dot but there are more tokens - parse parameters
                p.leave_breadcrumb(Grammar::ParameterList);
                while p.token != Token::Rparen && p.token != Token::Eof {
                    if let Some(param) = parse_parameter(p) {
                        params.push(param);
                    } else {
                        // No param parsed - check if we should continue or stop
                        if recover::should_abort_list_parse(p) {
                            break;
                        }
                        // Unexpected token - report error and skip
                        p.err_unexpected();
                        p.next();
                        continue;
                    }

                    // Check for comma or handle missing comma like OCaml
                    if p.token == Token::Comma {
                        p.next();
                    } else if p.token == Token::Rparen || p.token == Token::Eof {
                        break;
                    } else if grammar::is_parameter_start(&p.token) {
                        // Token looks like another param but no comma - missing comma case
                        p.expect(Token::Comma);
                    } else {
                        // res_core.ml `parse_comma_delimited_region`: report a
                        // missing comma unless the token ends/aborts the list,
                        // skip a `;`, and keep looping either way.
                        if !recover::should_abort_list_parse(p) {
                            p.expect(Token::Comma);
                        }
                        if p.token == Token::Semicolon {
                            p.next();
                        }
                    }
                }
                p.eat_breadcrumb();
                p.expect(Token::Rparen);
                let rparen_end_pos_idx = p.prev_end_pos_idx();
                // Set paren positions on the first type param (if any)
                set_first_type_param_paren_pos_idx(&mut params, lparen_pos_idx, rparen_end_pos_idx);
            } else {
                p.leave_breadcrumb(Grammar::ParameterList);
                while p.token != Token::Rparen && p.token != Token::Eof {
                    if let Some(param) = parse_parameter(p) {
                        params.push(param);
                    } else {
                        // No param parsed - check if we should continue or stop
                        if recover::should_abort_list_parse(p) {
                            break;
                        }
                        // Unexpected token - report error and skip
                        p.err_unexpected();
                        p.next();
                        continue;
                    }

                    // Check for comma or handle missing comma like OCaml
                    if p.token == Token::Comma {
                        p.next();
                    } else if p.token == Token::Rparen || p.token == Token::Eof {
                        break;
                    } else if grammar::is_parameter_start(&p.token) {
                        // Token looks like another param but no comma - missing comma case
                        p.expect(Token::Comma);
                    } else {
                        // res_core.ml `parse_comma_delimited_region`: report a
                        // missing comma unless the token ends/aborts the list,
                        // skip a `;`, and keep looping either way.
                        if !recover::should_abort_list_parse(p) {
                            p.expect(Token::Comma);
                        }
                        if p.token == Token::Semicolon {
                            p.next();
                        }
                    }
                }
                p.eat_breadcrumb();
                p.expect(Token::Rparen);
                let rparen_end_pos_idx = p.prev_end_pos_idx();
                // Set paren positions on the first type param (if any)
                set_first_type_param_paren_pos_idx(&mut params, lparen_pos_idx, rparen_end_pos_idx);
            }
        }
        Token::Lident(_) | Token::Underscore => {
            // Single parameter without parens
            if let Some(param) = parse_parameter(p) {
                params.push(param);
            }
        }
        _ => {}
    }

    params
}

/// Set paren position indices on the first type param in the list (if any).
/// Used for computing the implicit unit pattern location in type-only arrows.
fn set_first_type_param_paren_pos_idx(
    params: &mut [super::core::FundefParameter],
    lparen_pos_idx: PosIdx,
    rparen_end_pos_idx: PosIdx,
) {
    for param in params.iter_mut() {
        if let super::core::FundefParameter::Type(tp) = param {
            tp.paren_start_pos_idx = Some(lparen_pos_idx);
            tp.paren_end_pos_idx = Some(rparen_end_pos_idx);
            break; // Only set on the first type param
        }
    }
}

/// Parse a single function parameter.
fn parse_parameter(p: &mut Parser<'_>) -> Option<super::core::FundefParameter> {
    // res_core.ml:1893-1896: only `type`, `~`, `.` or a pattern start begins a
    // parameter.
    if !matches!(p.token, Token::Typ | Token::Tilde | Token::Dot)
        && !grammar::is_pattern_start(&p.token)
    {
        return None;
    }
    let start_pos_idx = p.start_pos_idx();

    // Skip deprecated uncurried marker.
    if p.token == Token::Dot {
        p.warn_uncurried_dot_syntax();
        p.next();
    }

    // Parse attributes
    let attrs = parse_attributes(p);

    // Check for type parameter
    if p.token == Token::Typ {
        p.next();
        let lidents = parse_lident_list(p);
        return Some(super::core::FundefParameter::Type(
            super::core::FundefTypeParam {
                attrs,
                locs: lidents,
                start_pos_idx,
                // These are set by parse_parameters for the first type param in parenthesized groups
                paren_start_pos_idx: None,
                paren_end_pos_idx: None,
            },
        ));
    }

    // Check for labeled parameter
    if p.token == Token::Tilde {
        // Capture tilde position - OCaml includes ~ in the pattern var location but NOT label location
        let tilde_pos_idx = p.start_pos_idx();
        p.next();
        let (lbl_name, lbl_loc) = parse_lident(p);
        // Push a unique string (no global deduplication) - user identifiers should not be shared
        // with other uses of the same name elsewhere. But we DO reuse this same StrIdx for both
        // the label and the pattern in punned cases (like `~x` which means label=x, pattern=x).
        let lbl_str_idx = p.arena_mut().push_interned_string(&lbl_name);
        // OCaml: label location is just the name, not including ~
        let lbl_located = Located::new(lbl_str_idx, lbl_loc);
        // OCaml: pattern var location includes ~ (from tilde_pos to end of name)
        let name_loc_with_tilde = p.mk_loc_idx_to_prev_end(tilde_pos_idx);
        let lbl = match &p.token {
            Token::Comma | Token::Equal | Token::Rparen => {
                // Just ~name
                // OCaml (line 1855): Ast_helper.Pat.var ~attrs ~loc
                let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
                // Reuse the same StrIdx for sharing in marshal output
                let mut pat = ast_helper::make_var_pat(lbl_str_idx, loc);
                pat.ppat_attributes = attrs.clone();
                (ArgLabel::Labelled(lbl_located), pat, None)
            }
            Token::Colon => {
                // ~name: type
                // OCaml: var_pat location includes ~ (from tilde to end of name)
                // But if there are attributes, it includes those too (from start_pos)
                p.next();
                let typ = super::typ::parse_typ_expr(p);
                let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
                // Use start_pos if there are attributes, otherwise use tilde_pos
                // OCaml includes @as() attributes in the inner Ppat_var location
                let var_loc = if attrs.is_empty() {
                    name_loc_with_tilde
                } else {
                    let name_end_idx = p.loc_end_idx(name_loc_with_tilde);
                    p.mk_loc_idx(start_pos_idx, name_end_idx)
                };
                // Reuse the same StrIdx for sharing in marshal output
                let var_pat = ast_helper::make_var_pat(lbl_str_idx, var_loc);
                // OCaml (lines 1863-1864): Ast_helper.Pat.constraint_ ~attrs ~loc pat typ
                // The attrs go on the OUTER constraint pattern
                let pat = Pattern {
                    ppat_desc: {
                        let p_idx = p.arena_mut().push_pat(var_pat);
                        let t_idx = p.arena_mut().push_core_type(typ);
                        Box::new(PatternDesc::Ppat_constraint(Box::new((p_idx, t_idx))))
                    },
                    ppat_loc: loc,
                    ppat_attributes: attrs.clone(),
                };
                (ArgLabel::Labelled(lbl_located), pat, None)
            }
            Token::As => {
                // ~name as pattern
                // OCaml (line 1871): {pat with ppat_attributes = attrs @ pat.ppat_attributes}
                p.next();
                let mut pat = super::pattern::parse_constrained_pattern(p);
                // Prepend attrs to pattern's existing attributes
                let mut new_attrs = attrs.clone();
                new_attrs.extend(pat.ppat_attributes);
                pat.ppat_attributes = new_attrs;
                (ArgLabel::Labelled(lbl_located), pat, None)
            }
            _ => {
                // res_core.ml:1937-1942: any other token is unexpected.
                p.err_unexpected();
                let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
                // Reuse the same StrIdx for sharing in marshal output
                let mut pat = ast_helper::make_var_pat(lbl_str_idx, loc);
                pat.ppat_attributes = attrs.clone();
                (ArgLabel::Labelled(lbl_located), pat, None)
            }
        };

        let (label, pat, default) = lbl;

        // Check for default value
        let (label, pat, default) = if p.token == Token::Equal {
            p.next();
            let label = match label {
                ArgLabel::Labelled(name) => ArgLabel::Optional(name),
                other => other,
            };
            if p.token == Token::Question {
                p.next();
                (label, pat, None)
            } else {
                let expr = parse_expr(p);
                // Check for type annotation after default: ~name = default : type
                // The type constraint goes on the expression, not the pattern
                let expr = if p.token == Token::Colon {
                    p.next();
                    let typ = super::typ::parse_typ_expr(p);
                    let loc = p.mk_loc_spanning(expr.pexp_loc, typ.ptyp_loc);
                    let expr_idx = p.arena_mut().push_expr(expr);
                    let typ_idx = p.arena_mut().push_core_type(typ);
                    Expression {
                        pexp_desc: Box::new(ExpressionDesc::Pexp_constraint(Box::new((
                            expr_idx, typ_idx,
                        )))),
                        pexp_loc: loc,
                        pexp_attributes: Attributes::new(),
                    }
                } else {
                    expr
                };

                // OCaml typecore rewrites optional defaults through a synthetic
                // ghost span from lhs start to default end. Seed that span here
                // so later typedtree rewriting can reuse it by bounds.
                if matches!(label, ArgLabel::Optional(_))
                    && matches!(&*pat.ppat_desc, PatternDesc::Ppat_var(_))
                {
                    let sloc_start = p.loc_start_idx(pat.ppat_loc);
                    let sloc_end = p.loc_end_idx(expr.pexp_loc);
                    p.arena_mut().push_loc(sloc_start, sloc_end, true);
                }

                (label, pat, Some(expr))
            }
        } else {
            (label, pat, default)
        };

        // OCaml puts labeled arg attrs directly on the pattern (not on the returned parameter)
        // So FundefTermParam.attrs should be empty for labeled args with attrs on the pattern
        return Some(super::core::FundefParameter::Term(
            super::core::FundefTermParam {
                attrs: Attributes::new(), // attrs are already on pat.ppat_attributes
                label,
                expr: default,
                pat,
                start_pos_idx,
            },
        ));
    }

    // Regular pattern parameter: res_core.ml:1940-1975 always parses a
    // (constrained) pattern here, reporting any unexpected token itself.
    {
        let pat = super::pattern::parse_pattern(p);
        // Handle constraint inline to allow full arrow types (unlike switch cases)
        // For function parameters like `(x: int => int)`, we want to parse
        // the full arrow type, but `parse_constrained_pattern` uses
        // `parse_typ_expr_no_arrow` which is correct for switch cases but not here.
        let mut pat = if p.token == Token::Colon {
            p.next();
            let typ = super::typ::parse_typ_expr(p);
            let loc = p.mk_loc_spanning(pat.ppat_loc, typ.ptyp_loc);
            let pat_idx = p.arena_mut().push_pat(pat);
            let typ_idx = p.arena_mut().push_core_type(typ);
            Pattern {
                ppat_desc: Box::new(PatternDesc::Ppat_constraint(Box::new((pat_idx, typ_idx)))),
                ppat_loc: loc,
                ppat_attributes: Attributes::new(),
            }
        } else {
            pat
        };
        let mut pattern_attrs = attrs;
        pattern_attrs.extend(pat.ppat_attributes);
        pat.ppat_attributes = pattern_attrs;

        // Check for default value (= expr) - this means it's a labeled param missing the ~
        if p.token == Token::Equal {
            // Get the name from the pattern for the error message
            let lbl_name_str = match &*pat.ppat_desc {
                PatternDesc::Ppat_var(var) => p.arena().get_string(var.txt).to_string(),
                _ => String::new(),
            };

            p.next(); // consume = (OCaml does this first, so prev_end_pos includes =)

            // OCaml: emit "missing tilde" error
            let msg = if lbl_name_str.is_empty() {
                "A labeled parameter starts with a `~`.".to_string()
            } else {
                format!(
                    "A labeled parameter starts with a `~`. Did you mean: `~{}`?",
                    lbl_name_str
                )
            };
            let start_pos_for_err = *p.arena().get_position(start_pos_idx);
            p.err_at(
                start_pos_for_err,
                p.prev_end_pos,
                DiagnosticCategory::Message(msg),
            );

            // Create label as Optional
            let lbl_str_idx = p.arena_mut().intern_string(&lbl_name_str);
            let lbl_loc = pat.ppat_loc;
            let label = ArgLabel::Optional(Located::new(lbl_str_idx, lbl_loc));

            // Check for =? (optional with no default)
            let default = if p.token == Token::Question {
                p.next();
                None
            } else {
                Some(parse_constrained_or_coerced_expr(p))
            };

            return Some(super::core::FundefParameter::Term(
                super::core::FundefTermParam {
                    attrs: Attributes::new(),
                    label,
                    expr: default,
                    pat,
                    start_pos_idx,
                },
            ));
        }

        Some(super::core::FundefParameter::Term(
            super::core::FundefTermParam {
                attrs: Attributes::new(),
                label: ArgLabel::Nolabel,
                expr: None,
                pat,
                start_pos_idx,
            },
        ))
    }
}

/// Parse a list of lowercase identifiers.
pub(crate) fn parse_lident_list(p: &mut Parser<'_>) -> Vec<StringLoc> {
    let mut lidents = vec![];
    while let Token::Lident(name) = &p.token {
        let name = name.clone();
        let loc = p.mk_loc_current();
        p.next();
        let str_idx = p.arena_mut().push_interned_string(&name);
        lidents.push(with_loc(str_idx, loc));
    }
    lidents
}

/// Parse a lowercase identifier.
fn parse_lident(p: &mut Parser<'_>) -> (String, Location) {
    match &p.token {
        Token::Lident(name) => {
            let name = name.to_string();
            let loc = p.mk_loc_current();
            p.next();
            (name, loc)
        }
        Token::Eof => {
            p.err_unexpected();
            ("_".to_string(), p.mk_loc_current())
        }
        _ => {
            // OCaml: parse_lident recovery - if keyword on same line, skip it.
            // Otherwise skip tokens until we find an Lident or should abort.
            p.err(DiagnosticCategory::Lident(p.token.clone().into_owned()));
            if p.token.is_keyword() && p.prev_end_pos.line == p.start_pos.line {
                p.next();
            } else {
                p.next(); // skip the bad token
                // Skip tokens until we find an Lident or should abort list parse
                while !super::core::recover::should_abort_list_parse(p) && p.token != Token::Eof {
                    p.next();
                }
                if matches!(p.token, Token::Lident(_)) {
                    return parse_lident(p);
                }
            }
            ("_".to_string(), p.mk_loc_current())
        }
    }
}

// ============================================================================
// Binary Expression Parsing
// ============================================================================

/// Parse a binary expression with precedence climbing.
pub fn parse_binary_expr(
    p: &mut Parser<'_>,
    left: Expression,
    min_prec: i32,
    context: ExprContext,
) -> Expression {
    // OCaml `parse_binary_expr` (compiler/syntax/src/res_core.ml:2408-2458).
    let mut left = left;
    loop {
        let token = p.peek_binary_operator().into_owned();
        let token_prec = match token {
            // Can the minus be interpreted as a binary operator? Or is it a
            // unary? See `Scanner.is_binary_op`.
            Token::Minus | Token::MinusDot | Token::LessThan | Token::Percent
                if !p.is_binary_op() && p.start_pos.line > p.prev_end_pos.line =>
            {
                -1
            }
            ref token => token.precedence(),
        };
        if token_prec < min_prec {
            return left;
        }
        p.leave_breadcrumb(Grammar::ExprBinaryAfterOp(token.clone()));
        let op_start_idx = p.start_pos_idx();
        p.next();
        let op_end_idx = p.prev_end_pos_idx();
        // Exponentiation is right-associative.
        let next_prec = if token == Token::Exponentiation {
            token_prec
        } else {
            token_prec + 1
        };
        let right = parse_operand_expr(p, context);
        let right = parse_binary_expr(p, right, next_prec, context);
        let loc = p.mk_loc_spanning(left.pexp_loc, right.pexp_loc);
        let op_expr = super::core::make_infix_operator(p, token, op_start_idx, op_end_idx);
        left = ast_helper::make_apply(
            p.arena_mut(),
            op_expr,
            vec![(ArgLabel::Nolabel, left), (ArgLabel::Nolabel, right)],
            loc,
        );
        p.eat_breadcrumb();
    }
}

// ============================================================================
// Atomic Expressions
// ============================================================================

/// Parse an atomic expression.
pub fn parse_atomic_expr(p: &mut Parser<'_>) -> Expression {
    p.leave_breadcrumb(Grammar::ExprOperand);
    let start_pos_idx = p.start_pos_idx();

    let expr = match &p.token {
        Token::True | Token::False => {
            let is_true = p.token == Token::True;
            p.next();
            let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
            let lid = super::core::make_lident_static(
                p.arena_mut(),
                if is_true { "true" } else { "false" },
            );
            let lid_idx = p.push_longident(lid);
            Expression {
                pexp_desc: Box::new(ExpressionDesc::Pexp_construct(
                    with_loc(lid_idx, loc),
                    ctor_args(Vec::new(), loc),
                )),
                pexp_loc: loc,
                pexp_attributes: Attributes::new(),
            }
        }
        Token::Int { .. } | Token::String(_) | Token::Float { .. } | Token::Codepoint { .. } => {
            let c = parse_constant(p);
            let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
            ast_helper::make_constant(c, loc)
        }
        // OCaml `parse_regex`: rescan `/` or `/.` as a regexp literal.
        Token::Forwardslash | Token::ForwardslashDot => {
            p.next_regex_token();
            let (pattern, flags) = match &p.token {
                Token::Regex { pattern, flags } => (pattern.to_string(), flags.to_string()),
                _ => unreachable!("next_regex_token always returns Regex"),
            };
            p.next();
            let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
            Expression {
                pexp_desc: Box::new(ExpressionDesc::Pexp_regexp(Box::new(
                    crate::parser::ast::PexpRegexp { pattern, flags },
                ))),
                pexp_loc: loc,
                pexp_attributes: Attributes::new(),
            }
        }
        Token::Uident(_) | Token::Lident(_) => parse_value_or_constructor(p),
        Token::Lparen => {
            p.next();
            if p.token == Token::Rparen {
                // Unit: ()
                p.next();
                let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
                let lid_idx = p.push_lident_static("()");
                Expression {
                    pexp_desc: Box::new(ExpressionDesc::Pexp_construct(
                        with_loc(lid_idx, loc),
                        ctor_args(Vec::new(), loc),
                    )),
                    pexp_loc: loc,
                    pexp_attributes: Attributes::new(),
                }
            } else {
                // Parenthesized expression or tuple
                let expr = parse_constrained_or_coerced_expr(p);
                if p.token == Token::Comma {
                    // Tuple
                    p.next();
                    parse_tuple_expr(p, start_pos_idx, expr)
                } else {
                    p.expect(Token::Rparen);
                    expr
                }
            }
        }
        Token::Lbracket => parse_array_expr(p),
        Token::Lbrace => parse_braced_or_record_expr(p),
        Token::List => {
            p.next();
            parse_list_expr(p, start_pos_idx)
        }
        Token::Dict => {
            p.next();
            parse_dict_expr(p, start_pos_idx)
        }
        Token::Percent => {
            // Extension expression: %ext, %ext.with.dots, %ext(payload)
            // OCaml includes the % in the extension name location
            let id_start_idx = p.start_pos_idx();
            p.next();
            let name = super::module::parse_extension_id(p, id_start_idx);

            let payload = super::module::parse_payload_region(p);
            let payload = super::module::raw_source_extension_payload(p, &name, payload);

            let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
            Expression {
                pexp_desc: Box::new(ExpressionDesc::Pexp_extension(Box::new((name, payload)))),
                pexp_loc: loc,
                pexp_attributes: Attributes::new(),
            }
        }
        Token::LessThan => parse_jsx(p),
        Token::Backtick | Token::TemplateTail { .. } | Token::TemplatePart { .. } => {
            // OCaml: after parse_template_expr, overrides location to [start_pos, p.prev_end_pos)
            // This ensures the outer expression location spans from opening to closing backtick
            let mut expr = parse_template_literal(p);
            expr.pexp_loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
            expr
        }
        Token::Hash => {
            // Polyvariant: #tag or #tag(arg)
            // OCaml `parse_poly_variant_expr` uses `parse_hash_ident`.
            let hash_start_idx = p.start_pos_idx();
            p.next();
            let tag: Label = Cow::Owned(super::core::parse_hash_ident(p, hash_start_idx).0);

            // Check for argument
            // OCaml compiler/syntax/src/res_core.ml:4272-4297.
            // OCaml `parse_poly_variant_expr`: the arguments, or an empty
            // list located at the whole expression.
            let args = if p.token == Token::Lparen && !p.has_newline_before() {
                Some(parse_constructor_args(p))
            } else {
                None
            };
            let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
            let arg = args.unwrap_or(Located {
                txt: Vec::new(),
                loc,
            });
            Expression {
                pexp_desc: Box::new(ExpressionDesc::Pexp_variant(Box::new((tag, arg)))),
                pexp_loc: loc,
                pexp_attributes: Attributes::new(),
            }
        }
        Token::Module => {
            // First-class module: module(Expr) or module(Expr: Type)
            p.next();
            parse_first_class_module_expr(p, start_pos_idx)
        }
        Token::Underscore => {
            // OCaml: Underscore is not a valid expression operand, emit an error
            // This matches OCaml's parse_atomic_expr which uses Diagnostics.lident
            p.err(DiagnosticCategory::Lident(Token::Underscore));
            p.next();
            recover::default_expr(p.arena_mut())
        }
        Token::Eof => {
            p.err_at(
                p.prev_end_pos,
                p.end_pos,
                DiagnosticCategory::unexpected(
                    p.token.clone().into_owned(),
                    p.breadcrumbs().to_vec(),
                ),
            );
            recover::default_expr(p.arena_mut())
        }
        _ => {
            // Use err_unexpected which creates a proper Unexpected diagnostic
            // with breadcrumbs, matching OCaml's parse_region behavior
            // OCaml uses prev_end_pos as start, but p.end_pos as end
            let err_start = p.prev_end_pos;
            let err_end = p.end_pos;
            p.err_at(
                err_start,
                err_end,
                DiagnosticCategory::unexpected(
                    p.token.clone().into_owned(),
                    p.breadcrumbs().to_vec(),
                ),
            );

            // Try to skip tokens and retry parsing if we find a valid start token
            // This matches OCaml's skip_tokens_and_maybe_retry behavior
            if recover::skip_tokens_and_maybe_retry(p, grammar::is_atomic_expr_start) {
                // Eat our breadcrumb first, then recurse
                // OCaml returns from match, then eat_breadcrumb runs
                p.eat_breadcrumb();
                return parse_atomic_expr(p);
            }
            recover::default_expr(p.arena_mut())
        }
    };

    p.eat_breadcrumb();
    expr
}

/// Parse a constrained or coerced expression.
pub fn parse_constrained_or_coerced_expr(p: &mut Parser<'_>) -> Expression {
    let expr = parse_expr(p);

    if p.token == Token::Colon {
        p.next();
        let typ = super::typ::parse_typ_expr(p);
        // Check for coercion: (expr : type :> type)
        if p.token == Token::ColonGreaterThan {
            // OCaml: The inner Pexp_constraint has a location that ends at the constraint type,
            // not extending to the outer coercion target type
            let constraint_loc = p.mk_loc_spanning(expr.pexp_loc, typ.ptyp_loc);
            let expr_start_idx = p.loc_start_idx(expr.pexp_loc);
            p.next();
            let target_typ = super::typ::parse_typ_expr(p);
            let coerce_loc = p.mk_loc_idx_to_prev_end(expr_start_idx);
            // OCaml represents (x : t :> int) as Pexp_coerce(Pexp_constraint(x, t), int)
            // The constraint is nested inside the expression, not as the optional middle type
            let expr_idx = p.arena_mut().push_expr(expr);
            let typ_idx = p.arena_mut().push_core_type(typ);
            let constraint_expr = Expression {
                pexp_desc: Box::new(ExpressionDesc::Pexp_constraint(Box::new((
                    expr_idx, typ_idx,
                )))),
                pexp_loc: constraint_loc,
                pexp_attributes: Attributes::new(),
            };
            let constraint_idx = p.arena_mut().push_expr(constraint_expr);
            let target_typ_idx = p.arena_mut().push_core_type(target_typ);
            Expression {
                pexp_desc: Box::new(ExpressionDesc::Pexp_coerce(Box::new((
                    constraint_idx,
                    None,
                    target_typ_idx,
                )))),
                pexp_loc: coerce_loc,
                pexp_attributes: Attributes::new(),
            }
        } else {
            let loc = p.mk_loc_spanning(expr.pexp_loc, typ.ptyp_loc);
            let expr_idx = p.arena_mut().push_expr(expr);
            let typ_idx = p.arena_mut().push_core_type(typ);
            Expression {
                pexp_desc: Box::new(ExpressionDesc::Pexp_constraint(Box::new((
                    expr_idx, typ_idx,
                )))),
                pexp_loc: loc,
                pexp_attributes: Attributes::new(),
            }
        }
    } else if p.token == Token::ColonGreaterThan {
        // Direct coercion: expr :> type
        p.next();
        let typ = super::typ::parse_typ_expr(p);
        let expr_start_idx = p.loc_start_idx(expr.pexp_loc);
        let loc = p.mk_loc_idx_to_prev_end(expr_start_idx);
        let expr_idx = p.arena_mut().push_expr(expr);
        let typ_idx = p.arena_mut().push_core_type(typ);
        Expression {
            pexp_desc: Box::new(ExpressionDesc::Pexp_coerce(Box::new((
                expr_idx, None, typ_idx,
            )))),
            pexp_loc: loc,
            pexp_attributes: Attributes::new(),
        }
    } else {
        expr
    }
}

/// OCaml's over_parse_constrained_or_coerced_or_arrow_expression.
/// After parsing a block expression or let binding value, check if `:` follows
/// and handle the constraint/coercion/arrow overparse with appropriate error messages.
pub fn over_parse_constrained_or_coerced_or_arrow_expression(
    p: &mut Parser<'_>,
    expr: Expression,
) -> Expression {
    match &p.token {
        Token::ColonGreaterThan => {
            // Coercion: expr :> type
            p.next();
            let typ = super::typ::parse_typ_expr(p);
            let expr_start_idx = p.loc_start_idx(expr.pexp_loc);
            let loc = p.mk_loc_idx_to_prev_end(expr_start_idx);
            let expr_idx = p.arena_mut().push_expr(expr);
            let typ_idx = p.arena_mut().push_core_type(typ);
            Expression {
                pexp_desc: Box::new(ExpressionDesc::Pexp_coerce(Box::new((
                    expr_idx, None, typ_idx,
                )))),
                pexp_loc: loc,
                pexp_attributes: Attributes::new(),
            }
        }
        Token::Colon => {
            p.next();
            let typ = super::typ::parse_typ_expr_no_arrow(p);
            match &p.token {
                Token::EqualGreater => {
                    // Ambiguous arrow: expr: type => body
                    p.next();
                    let body = parse_expr(p);

                    // Convert expression to pattern
                    let (pat, expr_is_unit) = match &*expr.pexp_desc {
                        ExpressionDesc::Pexp_ident(longident) => {
                            // Longident.flatten |> String.concat "."
                            let lid = p.arena().get_longident(longident.txt);
                            let parts: Vec<&str> = lid
                                .flatten_idx()
                                .iter()
                                .map(|idx| p.arena().get_string(*idx))
                                .collect();
                            let name = parts.join(".");
                            let name_str_idx = p.arena_mut().intern_string(&name);
                            let name_loc = with_loc(name_str_idx, longident.loc);
                            (
                                Pattern {
                                    ppat_desc: Box::new(PatternDesc::Ppat_var(name_loc)),
                                    ppat_loc: expr.pexp_loc,
                                    ppat_attributes: Attributes::new(),
                                },
                                false,
                            )
                        }
                        ExpressionDesc::Pexp_construct(lid, args) if args.txt.is_empty() => {
                            let longident = p.arena().get_longident(lid.txt);
                            let is_unit = matches!(longident, Longident::Lident(s) if p.arena().get_string(*s) == "()");
                            if is_unit {
                                (
                                    Pattern {
                                        ppat_desc: Box::new(PatternDesc::Ppat_construct(
                                            *lid,
                                            ctor_args(Vec::new(), expr.pexp_loc),
                                        )),
                                        ppat_loc: expr.pexp_loc,
                                        ppat_attributes: Attributes::new(),
                                    },
                                    true,
                                )
                            } else {
                                let pattern_str_idx = p.arena_mut().intern("pattern");
                                let name_loc = with_loc(pattern_str_idx, expr.pexp_loc);
                                (
                                    Pattern {
                                        ppat_desc: Box::new(PatternDesc::Ppat_var(name_loc)),
                                        ppat_loc: expr.pexp_loc,
                                        ppat_attributes: Attributes::new(),
                                    },
                                    false,
                                )
                            }
                        }
                        _ => {
                            let pattern_str_idx = p.arena_mut().intern("pattern");
                            let name_loc = with_loc(pattern_str_idx, expr.pexp_loc);
                            (
                                Pattern {
                                    ppat_desc: Box::new(PatternDesc::Ppat_var(name_loc)),
                                    ppat_loc: expr.pexp_loc,
                                    ppat_attributes: Attributes::new(),
                                },
                                false,
                            )
                        }
                    };

                    let arrow_loc = p.mk_loc_spanning(expr.pexp_loc, body.pexp_loc);

                    // Interpretation 1: (param) => (body : type)
                    let full_arity = p.push_arity_full(1);
                    let body_idx = p.arena_mut().push_expr(body.clone());
                    let typ_idx = p.arena_mut().push_core_type(typ.clone());
                    let constrained_body = Expression {
                        pexp_desc: Box::new(ExpressionDesc::Pexp_constraint(Box::new((
                            body_idx, typ_idx,
                        )))),
                        pexp_loc: p.mk_loc_spanning(body.pexp_loc, typ.ptyp_loc),
                        pexp_attributes: Attributes::new(),
                    };
                    let rhs_idx = p.arena_mut().push_expr(constrained_body);
                    let pat1_idx = p.arena_mut().push_pat(pat.clone());
                    let arrow1 = Expression {
                        pexp_desc: Box::new(ExpressionDesc::Pexp_fun(Box::new(PexpFun {
                            arity: full_arity,
                            arg_label: ArgLabel::Nolabel,
                            default: None,
                            lhs: pat1_idx,
                            rhs: rhs_idx,
                            is_async: false,
                        }))),
                        pexp_loc: arrow_loc,
                        pexp_attributes: Attributes::new(),
                    };

                    if expr_is_unit {
                        arrow1
                    } else {
                        // Interpretation 2: (param: type) => body
                        let full_arity2 = p.push_arity_full(1);
                        let pat_idx = p.arena_mut().push_pat(pat);
                        let typ_idx2 = p.arena_mut().push_core_type(typ.clone());
                        let body_idx2 = p.arena_mut().push_expr(body.clone());
                        let constraint_pat = Pattern {
                            ppat_desc: Box::new(PatternDesc::Ppat_constraint(Box::new((
                                pat_idx, typ_idx2,
                            )))),
                            ppat_loc: p.mk_loc_spanning(expr.pexp_loc, typ.ptyp_loc),
                            ppat_attributes: Attributes::new(),
                        };
                        let constraint_pat_idx = p.arena_mut().push_pat(constraint_pat);
                        let arrow2 = Expression {
                            pexp_desc: Box::new(ExpressionDesc::Pexp_fun(Box::new(PexpFun {
                                arity: full_arity2,
                                arg_label: ArgLabel::Nolabel,
                                default: None,
                                lhs: constraint_pat_idx,
                                rhs: body_idx2,
                                is_async: false,
                            }))),
                            pexp_loc: arrow_loc,
                            pexp_attributes: Attributes::new(),
                        };

                        // Use ResPrinter to render both interpretations
                        use super::comment_table::CommentTable;
                        use super::doc::Doc;
                        use super::printer;
                        let state = printer::PrinterState::init();
                        let mut cmt_tbl = CommentTable::new();
                        let msg = Doc::breakable_group(
                            Doc::concat(vec![
                                Doc::text("Did you mean to annotate the parameter type or the return type?"),
                                Doc::indent(Doc::concat(vec![
                                    Doc::line(),
                                    Doc::text("1) "),
                                    printer::print_expression(&state, &arrow1, &mut cmt_tbl, p.arena()),
                                    Doc::line(),
                                    Doc::text("2) "),
                                    printer::print_expression(&state, &arrow2, &mut cmt_tbl, p.arena()),
                                ])),
                            ]),
                            true,
                        ).to_string(80);

                        p.err_at(
                            p.loc_start(expr.pexp_loc),
                            p.loc_end(body.pexp_loc),
                            DiagnosticCategory::message(&msg),
                        );
                        arrow1
                    }
                }
                _ => {
                    // Simple constraint: expr : type
                    let loc = p.mk_loc_spanning(expr.pexp_loc, typ.ptyp_loc);
                    let expr_idx = p.arena_mut().push_expr(expr);
                    let typ_idx = p.arena_mut().push_core_type(typ.clone());
                    let constrained = Expression {
                        pexp_desc: Box::new(ExpressionDesc::Pexp_constraint(Box::new((
                            expr_idx, typ_idx,
                        )))),
                        pexp_loc: loc,
                        pexp_attributes: Attributes::new(),
                    };

                    // Use ResPrinter to render the constrained expression in parens
                    use super::comment_table::CommentTable;
                    use super::doc::Doc;
                    use super::printer;
                    let state = printer::PrinterState::init();
                    let mut cmt_tbl = CommentTable::new();
                    let printed = printer::add_parens(printer::print_expression(
                        &state,
                        &constrained,
                        &mut cmt_tbl,
                        p.arena(),
                    ));
                    let msg = Doc::breakable_group(
                        Doc::concat(vec![
                            Doc::text(
                                "Expressions with type constraints need to be wrapped in parens:",
                            ),
                            Doc::indent(Doc::concat(vec![Doc::line(), printed])),
                        ]),
                        true,
                    )
                    .to_string(80);

                    p.err_at(
                        p.loc_start(constrained.pexp_loc),
                        p.loc_end(typ.ptyp_loc),
                        DiagnosticCategory::message(&msg),
                    );
                    constrained
                }
            }
        }
        _ => expr,
    }
}

/// Parse an expression with optional type constraint for function arguments.
/// Used in labeled argument contexts like `~compare=?intCompare: (int, int) => int`.
fn parse_constrained_expr_in_arg(p: &mut Parser<'_>) -> Expression {
    // OCaml: _ is valid in labeled argument position (~label=_)
    // BUT NOT if it's the start of an arrow function: (~onClick=_ => ...)
    // This must be checked before parse_constrained_or_coerced_expr
    if p.token == Token::Underscore && !super::core::is_es6_arrow_expression(p, false) {
        let start_pos_idx = p.start_pos_idx();
        p.next();
        let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
        let lid = super::core::make_lident_static(p.arena_mut(), "_");
        return ast_helper::make_ident(p, lid, loc);
    }
    parse_constrained_or_coerced_expr(p)
}

// ============================================================================
// Primary Expression Parsing
// ============================================================================

/// Parse a primary expression (handles field access, method calls, array indexing).
pub fn parse_primary_expr(p: &mut Parser<'_>, operand: Expression, no_call: bool) -> Expression {
    // OCaml: let start_pos = operand.pexp_loc.loc_start in
    // Capture start position from operand BEFORE any transformations (like underscore apply)
    // This ensures that subsequent operations (field access, etc.) use the original location.
    // IMPORTANT: Reuse the existing PosIdx from operand.pexp_loc to match OCaml's sharing.
    // In OCaml, `operand.pexp_loc.loc_start` is the same object used for all derived locations.
    let start_pos_idx = p.loc_start_idx(operand.pexp_loc);
    let _start_pos = p.loc_start(operand.pexp_loc); // For comparisons where we need Position value
    let mut expr = operand;

    loop {
        match &p.token {
            Token::Dot => {
                // OCaml `parse_primary_expr` (res_core.ml:2296-2311).
                p.next();
                let lident = parse_value_path_after_dot(p);
                if p.token == Token::Equal && !no_call {
                    p.leave_breadcrumb(Grammar::ExprSetField);
                    p.next();
                    let target_expr = parse_expr(p);
                    let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
                    let e_idx = p.arena_mut().push_expr(expr);
                    let v_idx = p.arena_mut().push_expr(target_expr);
                    let setfield = Expression {
                        pexp_desc: Box::new(ExpressionDesc::Pexp_setfield(Box::new((
                            e_idx, lident, v_idx,
                        )))),
                        pexp_loc: loc,
                        pexp_attributes: Attributes::new(),
                    };
                    p.eat_breadcrumb();
                    return setfield;
                }
                let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
                let e_idx = p.arena_mut().push_expr(expr);
                expr = Expression {
                    pexp_desc: Box::new(ExpressionDesc::Pexp_field(e_idx, lident)),
                    pexp_loc: loc,
                    pexp_attributes: Attributes::new(),
                };
            }
            Token::Lparen if !no_call => {
                // Function call - but only if on the same line
                // A ( on a new line should not be treated as a function call
                if p.prev_end_pos.line < p.start_pos.line {
                    break;
                }
                let (args, partial) = parse_call_args(p);
                // OCaml: let loc = {fun_expr.pexp_loc with loc_end = p.prev_end_pos} in
                // For function calls, use expr's current location start, NOT the original operand's start
                // This is important for chained calls like f(a, _, b)(x, y) where the second call
                // should start from the Pexp_fun's location (the underscore position)
                // IMPORTANT: Reuse the existing PosIdx from expr.pexp_loc to match OCaml's sharing.
                // In OCaml, `{loc with loc_end = p.prev_end_pos}` reuses the same loc_start object.
                let loc_start_idx = p.loc_start_idx(expr.pexp_loc);
                let loc = p.mk_loc_idx_to_prev_end(loc_start_idx);
                // Apply placeholder transformation: f(a, _, b) => fun __x -> f(a, __x, b)
                let funct_idx = p.arena_mut().push_expr(expr);
                expr =
                    transform_placeholder_application(funct_idx, args, partial, loc, p.arena_mut());
            }
            // OCaml `parse_primary_expr` (res_core.ml:2312-2314): bracket access
            // on the same line hands the rest of the expression to
            // `parse_bracket_access`.
            Token::Lbracket if !no_call && p.prev_end_pos.line == p.start_pos.line => {
                return parse_bracket_access(p, expr, start_pos_idx);
            }
            // Note: MinusGreater (->) is handled by parse_binary_expr as a regular
            // binary operator, not here. It is NOT desugared - a->f(b) stays as (->)(a, f(b))
            Token::Backtick if !no_call => {
                // Tagged template literal: tag`strings${values}`
                // Only if on same line
                if p.prev_end_pos.line < p.start_pos.line {
                    break;
                }
                // res_core.ml:2317-2328: the template ends the primary
                // expression (it is not fed back into `loop`).
                match &*expr.pexp_desc {
                    ExpressionDesc::Pexp_ident(lid) => {
                        let prefix = (lid.txt, lid.loc);
                        return parse_template_literal_with_prefix(p, Some(prefix));
                    }
                    _ => {
                        // OCaml: only bare names are valid as tagged template tags
                        p.err_at(
                            p.loc_start(expr.pexp_loc),
                            p.loc_end(expr.pexp_loc),
                            DiagnosticCategory::message(
                                "Tagged template literals are currently restricted to names like: \
                                 myTagFunction`foo ${bar}`.",
                            ),
                        );
                        return parse_template_literal_with_prefix(p, None);
                    }
                }
            }
            _ => break,
        }
    }

    expr
}

/// OCaml `parse_bracket_access` (compiler/syntax/src/res_core.ml:2214-2284):
/// a string literal right after `[` is JS object access (`Pexp_send`), with an
/// optional `#=` assignment; anything else is `Array.get`/`Array.set`.
fn parse_bracket_access(
    p: &mut Parser<'_>,
    expr: Expression,
    start_pos_idx: crate::parse_arena::PosIdx,
) -> Expression {
    p.leave_breadcrumb(Grammar::ExprArrayAccess);
    let lbracket_start_idx = p.start_pos_idx();
    p.expect(Token::Lbracket);
    let string_start_idx = p.start_pos_idx();
    if let Token::String(s) = &p.token {
        let s = extend_cow_lifetime(s.clone());
        p.next();
        let string_end_idx = p.prev_end_pos_idx();
        p.expect(Token::Rbracket);
        p.eat_breadcrumb();
        let rbracket_end_idx = p.prev_end_pos_idx();
        let ident_loc = p.mk_loc_idx(string_start_idx, string_end_idx);
        let expr_idx = p.arena_mut().push_expr(expr);
        let send = Expression {
            pexp_desc: Box::new(ExpressionDesc::Pexp_object_get(Box::new((
                expr_idx,
                Loc {
                    txt: s,
                    loc: ident_loc,
                },
            )))),
            pexp_loc: p.mk_loc_idx(start_pos_idx, rbracket_end_idx),
            pexp_attributes: Attributes::new(),
        };
        let e = parse_primary_expr(p, send, false);
        if p.token != Token::Equal {
            return e;
        }
        let equal_start_idx = p.start_pos_idx();
        p.next();
        let equal_end_idx = p.prev_end_pos_idx();
        let rhs = parse_expr(p);
        let rhs_end_idx = p.loc_end_idx(rhs.pexp_loc);
        let loc = p.mk_loc_idx(start_pos_idx, rhs_end_idx);
        let Expression {
            pexp_desc,
            pexp_loc: e_loc,
            pexp_attributes: e_attrs,
        } = e;
        match *pexp_desc {
            ExpressionDesc::Pexp_object_get(inner) => {
                let (obj, name) = *inner;
                let rhs_idx = p.arena_mut().push_expr(rhs);
                return Expression {
                    pexp_desc: Box::new(ExpressionDesc::Pexp_object_set(Box::new((
                        obj, name, rhs_idx,
                    )))),
                    pexp_loc: loc,
                    pexp_attributes: Attributes::new(),
                };
            }
            desc => {
                let start = *p.arena().get_position(equal_start_idx);
                let end = *p.arena().get_position(equal_end_idx);
                p.err_at(
                    start,
                    end,
                    DiagnosticCategory::Message(
                        "The left-hand side of this assignment is not an object property access."
                            .to_string(),
                    ),
                );
                return Expression {
                    pexp_desc: Box::new(desc),
                    pexp_loc: e_loc,
                    pexp_attributes: e_attrs,
                };
            }
        }
    }
    let index = parse_constrained_or_coerced_expr(p);
    p.expect(Token::Rbracket);
    p.eat_breadcrumb();
    let rbracket_end_idx = p.prev_end_pos_idx();
    let array_loc = p.mk_loc_idx(lbracket_start_idx, rbracket_end_idx);
    if p.token == Token::Equal {
        p.leave_breadcrumb(Grammar::ExprArrayMutation);
        p.next();
        let rhs = parse_expr(p);
        let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
        let array_set = ast_helper::make_ident_idx(p.arena().array_set_lid(), array_loc);
        let apply = ast_helper::make_apply(
            p.arena_mut(),
            array_set,
            vec![
                (ArgLabel::Nolabel, expr),
                (ArgLabel::Nolabel, index),
                (ArgLabel::Nolabel, rhs),
            ],
            loc,
        );
        p.eat_breadcrumb();
        return apply;
    }
    let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
    let array_get = ast_helper::make_ident_idx(p.arena().array_get_lid(), array_loc);
    let e = ast_helper::make_apply(
        p.arena_mut(),
        array_get,
        vec![(ArgLabel::Nolabel, expr), (ArgLabel::Nolabel, index)],
        loc,
    );
    parse_primary_expr(p, e, false)
}

/// Parse function call arguments.
fn parse_call_args(p: &mut Parser<'_>) -> (Vec<(ArgLabel, Expression)>, bool) {
    let mut args = vec![];
    let mut partial = false;

    p.expect(Token::Lparen);
    // Capture start position AFTER consuming '(' (to match OCaml behavior)
    // OCaml's start_pos for empty args is the position after '(' is consumed
    let start_pos_idx = p.start_pos_idx();

    // OCaml `parse_call_expr` (compiler/syntax/src/res_core.ml:4161-4175):
    // `parse_comma_delimited_region ~grammar:ArgumentList ~closing:Rparen
    // ~f:parse_argument` (res_core.ml:1068-1108), then an optional `...`
    // partial-application marker after at least one argument.
    p.leave_breadcrumb(Grammar::ExprCall);
    p.leave_breadcrumb(Grammar::ArgumentList);
    loop {
        if grammar::is_argument_start(&p.token) {
            let (label, expr) = parse_argument(p);
            args.push((label, expr));
            match p.token {
                Token::Comma => p.next(),
                Token::Rparen | Token::Eof => break,
                ref token if grammar::is_argument_start(token) => p.expect(Token::Comma),
                _ => {
                    if !(p.token == Token::Eof
                        || p.token == Token::Rparen
                        || recover::should_abort_list_parse(p))
                    {
                        p.expect(Token::Comma);
                    }
                    if p.token == Token::Semicolon {
                        p.next();
                    }
                }
            }
        } else if p.token == Token::Eof
            || p.token == Token::Rparen
            || recover::should_abort_list_parse(p)
        {
            break;
        } else {
            p.err(DiagnosticCategory::unexpected(
                p.token.clone().into_owned(),
                p.breadcrumbs().to_vec(),
            ));
            p.next();
        }
    }
    p.eat_breadcrumb();
    if p.token == Token::DotDotDot && !args.is_empty() {
        p.next();
        partial = true;
    }
    p.expect(Token::Rparen);
    p.eat_breadcrumb();
    // Get prev_end_pos AFTER consuming ')' to match OCaml behavior
    let rparen_end_idx = p.prev_end_pos_idx();

    // If no arguments were parsed, treat f() as f(())
    // OCaml treats empty parens as a unit argument
    if args.is_empty() {
        let unit_loc = p.mk_loc_idx(start_pos_idx, rparen_end_idx);
        let lid_idx = p.push_lident_static("()");
        let unit_expr = Expression {
            pexp_desc: Box::new(ExpressionDesc::Pexp_construct(
                Loc {
                    txt: lid_idx,
                    loc: unit_loc,
                },
                ctor_args(Vec::new(), unit_loc),
            )),
            pexp_loc: unit_loc,
            pexp_attributes: Attributes::new(),
        };
        args.push((ArgLabel::Nolabel, unit_expr));
    }

    (args, partial)
}

/// Parse a single argument (possibly labeled).
/// Handles uncurried dot prefix: f(. x, y, . z) - the dot is consumed but
/// doesn't change the argument structure (it's just part of uncurried syntax).
fn parse_argument(p: &mut Parser<'_>) -> (ArgLabel, Expression) {
    // Handle uncurried dot marker before argument
    // In f(. a, b, . c), each dot is consumed before the argument
    if p.token == Token::Dot {
        p.warn_uncurried_dot_syntax();
        p.next();
        // Check for apply(.) - uncurried unit call
        if p.token == Token::Rparen {
            let lid_idx = p.push_lident_static("()");
            let unit_expr = Expression {
                pexp_desc: Box::new(ExpressionDesc::Pexp_construct(
                    Loc {
                        txt: lid_idx,
                        loc: LocIdx::none(),
                    },
                    ctor_args(Vec::new(), LocIdx::none()),
                )),
                pexp_loc: LocIdx::none(),
                pexp_attributes: Attributes::new(),
            };
            return (ArgLabel::Nolabel, unit_expr);
        }
        // Fall through to parse the actual argument
    }

    if p.token == Token::Tilde {
        p.next();
        // OCaml `parse_argument2` (res_core.ml:4073-4157): a non-Lident token
        // after `~` reports `Diagnostics.lident` without consuming it and
        // yields a `Nolabel` expression hole.
        if !matches!(p.token, Token::Lident(_)) {
            p.err(DiagnosticCategory::Lident(p.token.clone().into_owned()));
            return (ArgLabel::Nolabel, recover::default_expr(p.arena_mut()));
        }
        let (name, name_loc) = parse_lident(p);
        // Push a unique string (no global deduplication) - user identifiers should not be shared
        // with other uses of the same name elsewhere. The same StrIdx is reused for both label and
        // expression in punned cases (like `f(~x)` which means `f(~x=x)`).
        let name_str_idx = p.arena_mut().push_interned_string(&name);
        let name_located = Located::new(name_str_idx, name_loc);

        if p.token == Token::Equal {
            p.next();
            if p.token == Token::Question {
                p.next();
                // ~label=?expr or ~label=?expr: type
                (
                    ArgLabel::Optional(name_located),
                    parse_constrained_expr_in_arg(p),
                )
            } else {
                // ~label=expr or ~label=expr: type
                (
                    ArgLabel::Labelled(name_located),
                    parse_constrained_expr_in_arg(p),
                )
            }
        } else if p.token == Token::Question {
            // ~label? (optional punning)
            p.next();
            // Use the same interned StrIdx for the identifier - this enables sharing
            let expr = ast_helper::make_ident(p, Longident::Lident(name_str_idx), name_loc);
            (ArgLabel::Optional(name_located), expr)
        } else if p.token == Token::Colon {
            // ~label: ... could be type constraint or wrong separator
            // OCaml checks is_typ_expr_start to decide
            let colon_start = p.start_pos;
            p.next();
            let colon_end = p.prev_end_pos;
            if super::grammar::is_typ_expr_start(&p.token) {
                // ~label: type (labeled with type annotation - punning with constraint)
                let typ = super::typ::parse_typ_expr(p);
                // Use the same interned StrIdx for the identifier - this enables sharing
                let ident_expr =
                    ast_helper::make_ident(p, Longident::Lident(name_str_idx), name_loc);
                // Constraint location spans from label name to end of type
                let constraint_start_idx = p.loc_start_idx(name_loc);
                let constraint_loc = p.mk_loc_idx_to_prev_end(constraint_start_idx);
                let expr = Expression {
                    pexp_desc: {
                        let e_idx = p.arena_mut().push_expr(ident_expr);
                        let t_idx = p.arena_mut().push_core_type(typ);
                        Box::new(ExpressionDesc::Pexp_constraint(Box::new((e_idx, t_idx))))
                    },
                    pexp_loc: constraint_loc,
                    pexp_attributes: Attributes::new(),
                };
                (ArgLabel::Labelled(name_located), expr)
            } else if p.token == Token::Question {
                // ~label:?value -> should be ~label=?value
                p.err_at(
                    colon_start,
                    colon_end,
                    DiagnosticCategory::message(
                        "Optional labelled arguments use `=?`. Example: `~label=?value`",
                    ),
                );
                p.next();
                let expr = parse_constrained_or_coerced_expr(p);
                (ArgLabel::Optional(name_located), expr)
            } else {
                // ~label:value -> should be ~label=value
                p.err_at(
                    colon_start,
                    colon_end,
                    DiagnosticCategory::message(
                        "Use `=` to pass a labelled argument. Example: `~label=value`",
                    ),
                );
                let expr = if p.token == Token::Underscore
                    && !super::core::is_es6_arrow_expression(p, false)
                {
                    let start_idx = p.start_pos_idx();
                    p.next();
                    let loc = p.mk_loc_idx_to_prev_end(start_idx);
                    let lid = super::core::make_lident_static(p.arena_mut(), "_");
                    ast_helper::make_ident(p, lid, loc)
                } else {
                    parse_constrained_or_coerced_expr(p)
                };
                (ArgLabel::Labelled(name_located), expr)
            }
        } else {
            // ~label (punning)
            // Use the same interned StrIdx for the identifier - this enables sharing
            let expr = ast_helper::make_ident(p, Longident::Lident(name_str_idx), name_loc);
            (ArgLabel::Labelled(name_located), expr)
        }
    } else if p.token == Token::Underscore && !super::core::is_es6_arrow_expression(p, false) {
        // OCaml: _ as argument is valid (placeholder for partial application)
        // BUT NOT if it's the start of an arrow function: f(_ => ...)
        // This must be checked before parse_constrained_or_coerced_expr which
        // would now treat _ as an error in parse_atomic_expr
        let start_pos_idx = p.start_pos_idx();
        p.next();
        let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
        let lid = super::core::make_lident_static(p.arena_mut(), "_");
        let expr = ast_helper::make_ident(p, lid, loc);
        (ArgLabel::Nolabel, expr)
    } else {
        // Unlabeled argument - may have type constraint like f({}:t)
        (ArgLabel::Nolabel, parse_constrained_or_coerced_expr(p))
    }
}

// ============================================================================
// Tuple Expression
// ============================================================================

/// Parse a tuple expression.
fn parse_tuple_expr(p: &mut Parser<'_>, start_pos_idx: PosIdx, first: Expression) -> Expression {
    // OCaml `parse_tuple_expr` (compiler/syntax/src/res_core.ml:4317-4333).
    let mut elements = vec![first];
    elements.extend(super::core::parse_comma_delimited_region(
        p,
        Grammar::ExprList,
        Token::Rparen,
        parse_constrained_expr_region,
    ));

    p.expect(Token::Rparen);
    let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);

    // OCaml: A tuple needs at least two elements
    if elements.len() < 2 {
        p.err_at(
            *p.arena().get_position(start_pos_idx),
            p.prev_end_pos,
            DiagnosticCategory::Message("A tuple needs at least two elements".to_string()),
        );
    }

    let elements_idx: Vec<ExprIdx> = elements
        .into_iter()
        .map(|e| p.arena_mut().push_expr(e))
        .collect();
    Expression {
        pexp_desc: Box::new(ExpressionDesc::Pexp_tuple(Box::new(elements_idx))),
        pexp_loc: loc,
        pexp_attributes: Attributes::new(),
    }
}

// ============================================================================
// Collection Expressions
// ============================================================================

/// Parse an array expression [e1, e2, ...].
/// - `[a, b, c]` becomes `Pexp_array(Box::new([a, b, c]))`
/// - `[...xs, a, b]` becomes `Primitive_array.spread([xs, [a, b]])`
fn parse_array_expr(p: &mut Parser<'_>) -> Expression {
    let start_pos_idx = p.start_pos_idx();
    p.expect(Token::Lbracket);

    // OCaml res_core.ml:4498-4502: `parse_comma_delimited_reversed_list
    // ~grammar:ExprList ~closing:Rbracket ~f:parse_spread_expr_region_with_loc`.
    let mut items: Vec<(bool, Expression)> = super::core::parse_comma_delimited_reversed_list(
        p,
        Grammar::ExprList,
        Token::Rbracket,
        parse_spread_expr_region_with_loc,
    )
    .into_iter()
    .map(|(is_spread, expr, _, _)| (is_spread, expr))
    .collect();
    items.reverse();
    p.expect(Token::Rbracket);
    let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);

    // Check if there are any spreads
    let has_spread = items.iter().any(|(is_spread, _)| *is_spread);

    if !has_spread {
        // Simple case: no spread, just return array
        let elements: Vec<ExprIdx> = items
            .into_iter()
            .map(|(_, e)| p.arena_mut().push_expr(e))
            .collect();
        return Expression {
            pexp_desc: Box::new(ExpressionDesc::Pexp_array(Box::new(elements))),
            pexp_loc: loc,
            pexp_attributes: Attributes::new(),
        };
    }

    // With spread: [...xs, a, b, ...ys, c] becomes Primitive_array.spread([xs, [a, b], ys, [c]])
    // Split into segments: each spread item becomes its own array element,
    // consecutive non-spread items become a single array
    let mut array_items: Vec<Expression> = vec![];
    let mut current_non_spread: Vec<ExprIdx> = vec![];

    for (is_spread, expr) in items {
        if is_spread {
            // Flush any accumulated non-spread items as an array
            if !current_non_spread.is_empty() {
                array_items.push(Expression {
                    pexp_desc: Box::new(ExpressionDesc::Pexp_array(Box::new(std::mem::take(
                        &mut current_non_spread,
                    )))),
                    pexp_loc: loc,
                    pexp_attributes: Attributes::new(),
                });
            }
            // Add the spread item directly
            array_items.push(expr);
        } else {
            current_non_spread.push(p.arena_mut().push_expr(expr));
        }
    }

    // Flush remaining non-spread items
    if !current_non_spread.is_empty() {
        array_items.push(Expression {
            pexp_desc: Box::new(ExpressionDesc::Pexp_array(Box::new(current_non_spread))),
            pexp_loc: loc,
            pexp_attributes: Attributes::new(),
        });
    }

    // Create Primitive_array.spread([...])
    let array_items_idx: Vec<ExprIdx> = array_items
        .into_iter()
        .map(|e| p.arena_mut().push_expr(e))
        .collect();
    let outer_array = Expression {
        pexp_desc: Box::new(ExpressionDesc::Pexp_array(Box::new(array_items_idx))),
        pexp_loc: loc,
        pexp_attributes: Attributes::new(),
    };

    // OCaml builds the Primitive_array.spread longident inline at each spread
    // site (res_core.ml:4528), allocating fresh Longident blocks per occurrence.
    let lid_idx = p.arena_mut().fresh_belt_array_spread_lid();
    let spread_idx = p.arena_mut().intern("res.spread");
    let concat_many = Expression {
        pexp_desc: Box::new(ExpressionDesc::Pexp_ident(with_loc(lid_idx, loc))),
        pexp_loc: loc,
        pexp_attributes: Attributes::from_vec(vec![(
            mknoloc(spread_idx),
            Payload::PStr(Box::default()),
        )]),
    };

    let funct_idx = p.arena_mut().push_expr(concat_many);
    let outer_array_idx = p.arena_mut().push_expr(outer_array);
    Expression {
        pexp_desc: Box::new(ExpressionDesc::Pexp_apply(Box::new(PexpApply {
            funct: funct_idx,
            args: vec![(ArgLabel::Nolabel, outer_array_idx)],
            partial: false,
            transformed_jsx: false,
        }))),
        pexp_loc: loc,
        pexp_attributes: Attributes::new(),
    }
}

/// Parse a list expression list{e1, e2, ...} and lower to nested :: constructors.
/// - `list{1, 2, 3}` becomes `1 :: (2 :: (3 :: []))`
/// - `list{1, 2, ...rest}` becomes `1 :: (2 :: rest)`
/// - `list{...xs, ...ys}` becomes `Primitive_list.spread([xs, ys])`
/// - `list{...xs, 1, ...ys}` becomes `Primitive_list.spread([xs, 1 :: ys])`
///
/// OCaml `parse_spread_expr_region_with_loc` (res_core.ml:4334-4343).
fn parse_spread_expr_region_with_loc(
    p: &mut Parser<'_>,
) -> Option<(bool, Expression, PosIdx, PosIdx)> {
    let start_pos_idx = p.prev_end_pos_idx();
    if p.token == Token::DotDotDot {
        p.next();
        let expr = parse_constrained_or_coerced_expr(p);
        Some((true, expr, start_pos_idx, p.prev_end_pos_idx()))
    } else if grammar::is_expr_start(&p.token) {
        let expr = parse_constrained_or_coerced_expr(p);
        Some((false, expr, start_pos_idx, p.prev_end_pos_idx()))
    } else {
        None
    }
}

fn parse_list_expr(p: &mut Parser<'_>, start_pos_idx: PosIdx) -> Expression {
    // Token::List already consumed the opening '{'
    // Each item is (is_spread, expr, spread_start_pos)
    // For spread items, spread_start_pos is before `...`; for non-spread, it's at the expr start
    // OCaml res_core.ml:4370-4373: `parse_comma_delimited_reversed_list
    // ~grammar:ListExpr ~closing:Rbrace ~f:parse_spread_expr_region_with_loc`.
    let mut items: Vec<(bool, Expression, PosIdx, PosIdx)> =
        super::core::parse_comma_delimited_reversed_list(
            p,
            Grammar::ListExpr,
            Token::Rbrace,
            parse_spread_expr_region_with_loc,
        );
    items.reverse();

    p.expect(Token::Rbrace);
    let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);

    // Split items into segments by spread boundaries
    // Each segment is (non_spread_items, optional_spread)
    let segments = split_list_by_spread(items);

    match segments.len() {
        0 => {
            // Empty list: list{} → []
            // OCaml: {expr with pexp_loc = loc} - overwrite ghost pexp_loc with original location
            let mut expr = make_empty_list(p, loc);
            expr.pexp_loc = loc;
            expr
        }
        1 => {
            // Single segment: just build with :: constructors
            // OCaml: spread expression keeps its original location in single segment case
            let (exprs, spread, _, _) = segments.into_iter().next().unwrap();
            let mut result = make_list_expression_simple(p, loc, exprs, spread);
            // The outermost expression should have the full list location
            result.pexp_loc = loc;
            result
        }
        _ => {
            // Multiple segments: use Primitive_list.spread([...])
            // OCaml uses segment locations for sub-expressions
            let sub_exprs: Vec<ExprIdx> = segments
                .into_iter()
                .map(|(exprs, spread, seg_start, seg_end)| {
                    let expr = make_list_expression_with_loc(p, exprs, spread, seg_start, seg_end);
                    p.arena_mut().push_expr(expr)
                })
                .collect();

            let array_expr = Expression {
                pexp_desc: Box::new(ExpressionDesc::Pexp_array(Box::new(sub_exprs))),
                pexp_loc: loc,
                pexp_attributes: Attributes::new(),
            };

            // OCaml builds the Primitive_list.spread longident inline at each
            // spread site (res_core.ml:4386), allocating fresh Longident blocks.
            let lid_idx = p.arena_mut().fresh_belt_list_spread_lid();
            let spread_idx = p.arena_mut().intern("res.spread");
            let concat_many_ident = Expression {
                pexp_desc: Box::new(ExpressionDesc::Pexp_ident(Loc { txt: lid_idx, loc })),
                pexp_loc: loc,
                // Add the res.spread attribute to match OCaml
                pexp_attributes: Attributes::from_vec(vec![(
                    mknoloc(spread_idx),
                    Payload::PStr(Box::default()),
                )]),
            };

            let funct_idx = p.arena_mut().push_expr(concat_many_ident);
            let array_expr_idx = p.arena_mut().push_expr(array_expr);
            Expression {
                pexp_desc: Box::new(ExpressionDesc::Pexp_apply(Box::new(PexpApply {
                    funct: funct_idx,
                    args: vec![(ArgLabel::Nolabel, array_expr_idx)],
                    partial: false,
                    transformed_jsx: false,
                }))),
                pexp_loc: loc,
                pexp_attributes: Attributes::new(),
            }
        }
    }
}

/// Split list items by spread into segments.
/// Each segment contains (non_spread_items, optional_spread_at_end).
/// A spread at the beginning of items starts a new segment.
/// Segment data: (non_spread_exprs, optional_spread, segment_start, segment_end)
/// OCaml tracks segment extents: start is first non-spread item (or spread), end is spread/last item
type ListSegment = (Vec<Expression>, Option<Expression>, PosIdx, PosIdx);

fn split_list_by_spread(items: Vec<(bool, Expression, PosIdx, PosIdx)>) -> Vec<ListSegment> {
    // OCaml processes items in reverse using fold_left, building segments as:
    // - spread: create new segment ([], spread, spread_start, spread_end)
    // - non-spread with existing segment: prepend to segment, update start to non-spread's start
    // - non-spread with empty: create ([item], None, item_start, item_end)
    //
    // We'll process forward then reverse to match OCaml's final order.
    let mut segments: Vec<ListSegment> = vec![];

    // Process in reverse to match OCaml's fold_left from reversed list
    for (is_spread, expr, item_start, item_end) in items.into_iter().rev() {
        if is_spread {
            // Spread: create new segment
            segments.push((vec![], Some(expr), item_start, item_end));
        } else if let Some(last) = segments.last_mut() {
            // Non-spread with existing segment: prepend and update start
            last.0.push(expr);
            last.2 = item_start;
        } else {
            // Non-spread with no segments: create segment with no spread
            segments.push((vec![expr], None, item_start, item_end));
        }
    }

    // Reverse each segment's exprs (they were added in reverse order)
    for seg in &mut segments {
        seg.0.reverse();
    }

    // Reverse segments to get correct order
    segments.reverse();
    segments
}

/// Build an empty list expression `[]` with ghost locations.
/// Both pexp_loc and the inner Longident location are ghost.
/// This matches OCaml's handle_seq base case: construct ~loc nil None (where loc is ghost).
/// The caller should overwrite pexp_loc if needed (e.g., for outermost list expression).
fn make_empty_list(p: &mut Parser<'_>, loc: Location) -> Expression {
    // OCaml: let loc = {loc with Location.loc_ghost = true}
    let ghost_loc = p.arena_mut().mk_ghost_loc(loc);
    let lid_idx = p.expr_nil();
    Expression {
        pexp_desc: Box::new(ExpressionDesc::Pexp_construct(
            Loc {
                txt: lid_idx,
                loc: ghost_loc,
            },
            ctor_args(Vec::new(), ghost_loc),
        )),
        pexp_loc: ghost_loc,
        pexp_attributes: Attributes::new(),
    }
}

/// Build a list expression from items and optional spread tail (simple version)
/// Used for single-segment lists where OCaml does NOT update spread location
/// `[e1, e2]` → `e1 :: (e2 :: [])`
/// `[e1, e2, ...rest]` → `e1 :: (e2 :: rest)`
fn make_list_expression_simple(
    p: &mut Parser<'_>,
    loc: Location,
    exprs: Vec<Expression>,
    spread: Option<Expression>,
) -> Expression {
    // For lists with spread, the inner cons cells end at the spread's end
    // For lists without spread, they end at the empty list's end
    let list_end_idx = spread
        .as_ref()
        .map(|s| p.loc_end_idx(s.pexp_loc))
        .unwrap_or_else(|| p.loc_end_idx(loc));
    let mut acc = spread.unwrap_or_else(|| make_empty_list(p, loc));

    // Build from right: 3 :: [] -> 2 :: (3 :: []) -> 1 :: (2 :: (3 :: []))
    for item in exprs.into_iter().rev() {
        // Reuse the existing PosIdx from item.pexp_loc to match OCaml's sharing
        let item_start_idx = p.loc_start_idx(item.pexp_loc);
        let cons_loc = p.mk_loc_idx(item_start_idx, list_end_idx);
        let item_idx = p.arena_mut().push_expr(item);
        let acc_idx = p.arena_mut().push_expr(acc);
        let lid_idx = p.expr_cons();
        acc = Expression {
            pexp_desc: Box::new(ExpressionDesc::Pexp_construct(
                Loc {
                    txt: lid_idx,
                    loc: cons_loc,
                },
                ctor_args(vec![item_idx, acc_idx], cons_loc),
            )),
            pexp_loc: cons_loc,
            pexp_attributes: Attributes::new(),
        };
    }
    acc
}

/// Build a list expression for multi-segment lists with explicit segment locations
/// OCaml uses the segment's start/end for the sub-expression location
/// And updates the final expression's pexp_loc to segment extent
fn make_list_expression_with_loc(
    p: &mut Parser<'_>,
    exprs: Vec<Expression>,
    spread: Option<Expression>,
    seg_start: PosIdx,
    seg_end: PosIdx,
) -> Expression {
    let seg_loc = p.mk_loc_idx(seg_start, seg_end);

    // Use expression-context list constructor lidents (from ast_helper.ml)
    let nil_idx = p.expr_nil();
    let cons_idx = p.expr_cons();

    // Build the list using cons cells
    let list_end_idx = seg_end;
    let mut acc = spread.unwrap_or_else(|| {
        // Empty list with ghost location (same as OCaml's make_list_expression)
        let ghost_loc = LocIdx::none();
        Expression {
            pexp_desc: Box::new(ExpressionDesc::Pexp_construct(
                Loc {
                    txt: nil_idx,
                    loc: ghost_loc,
                },
                ctor_args(Vec::new(), ghost_loc),
            )),
            pexp_loc: ghost_loc,
            pexp_attributes: Attributes::new(),
        }
    });

    for item in exprs.into_iter().rev() {
        // Reuse the existing PosIdx from item.pexp_loc to match OCaml's sharing
        let item_start_idx = p.loc_start_idx(item.pexp_loc);
        let cons_loc = p.mk_loc_idx(item_start_idx, list_end_idx);
        let item_idx = p.arena_mut().push_expr(item);
        let acc_idx = p.arena_mut().push_expr(acc);
        acc = Expression {
            pexp_desc: Box::new(ExpressionDesc::Pexp_construct(
                Loc {
                    txt: cons_idx,
                    loc: cons_loc,
                },
                ctor_args(vec![item_idx, acc_idx], cons_loc),
            )),
            pexp_loc: cons_loc,
            pexp_attributes: Attributes::new(),
        };
    }

    // OCaml: `{expr with pexp_loc = loc}` updates outermost expression's location
    Expression {
        pexp_loc: seg_loc,
        ..acc
    }
}

/// OCaml `parse_dict_expr` (compiler/syntax/src/res_core.ml): a dict literal
/// `dict{"key": value, ...spread}` is a `Pexp_dict` node. The `dict{` token is
/// already consumed.
fn parse_dict_expr(p: &mut Parser<'_>, start_pos_idx: PosIdx) -> Expression {
    let entries: Vec<DictEntry> = super::core::parse_comma_delimited_region(
        p,
        Grammar::DictRows,
        Token::Rbrace,
        parse_dict_expr_part,
    );
    p.expect(Token::Rbrace);
    let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
    Expression {
        pexp_desc: Box::new(ExpressionDesc::Pexp_dict(Box::new(entries))),
        pexp_loc: loc,
        pexp_attributes: Attributes::new(),
    }
}

/// OCaml `parse_dict_expr_part`: `...spread` or `"key": value`, where a
/// missing `: value` puns the key as an identifier.
fn parse_dict_expr_part(p: &mut Parser<'_>) -> Option<DictEntry> {
    if p.token == Token::DotDotDot {
        p.next();
        let spread_expr = parse_constrained_or_coerced_expr(p);
        let spread_idx = p.arena_mut().push_expr(spread_expr);
        return Some(DictEntry::Pdict_spread(spread_idx));
    }
    let Token::String(s) = &p.token else {
        return None;
    };
    let key = extend_cow_lifetime(s.clone());
    let key_loc = p.mk_loc_current();
    p.next();
    let key_idx = p.arena_mut().intern(key.as_ref());
    let value = match p.token {
        Token::Colon => {
            p.next();
            parse_expr(p)
        }
        Token::Equal => {
            p.err_at(
                p.start_pos,
                p.end_pos,
                DiagnosticCategory::message(
                    "Dict entries use `:` to separate keys from values. Example: `{\"k\": v}`",
                ),
            );
            p.next();
            parse_expr(p)
        }
        _ => {
            let lid_idx = p.push_lident(key.as_ref());
            Expression {
                pexp_desc: Box::new(ExpressionDesc::Pexp_ident(with_loc(lid_idx, key_loc))),
                pexp_loc: key_loc,
                pexp_attributes: Attributes::new(),
            }
        }
    };
    let value_idx = p.arena_mut().push_expr(value);
    Some(DictEntry::Pdict_entry(
        with_loc(key_idx, key_loc),
        value_idx,
    ))
}

// ============================================================================
// Blocks, braced expressions and record expressions
// (OCaml compiler/syntax/src/res_core.ml:3099-3688)
// ============================================================================

/// `Ast_helper.Exp.braces ~braces_loc expr`, with the braces spanning `{` to
/// the previous token. The node keeps the inner expression's location.
fn with_braces(p: &mut Parser<'_>, start_pos_idx: PosIdx, expr: Expression) -> Expression {
    let braces_loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
    let loc = expr.pexp_loc;
    let inner = p.arena_mut().push_expr(expr);
    Expression {
        pexp_desc: Box::new(ExpressionDesc::Pexp_braces(Box::new(
            crate::parser::ast::PexpBraces {
                expr: inner,
                braces_loc,
            },
        ))),
        pexp_loc: loc,
        pexp_attributes: Attributes::new(),
    }
}

/// OCaml `parse_braced_or_record_expr` (compiler/syntax/src/res_core.ml:3099-3330).
fn parse_braced_or_record_expr(p: &mut Parser<'_>) -> Expression {
    let start_pos_idx = p.start_pos_idx();
    p.expect(Token::Lbrace);
    match p.token.clone() {
        Token::Break | Token::Continue => {
            let expr = parse_expr_block(p);
            p.expect(Token::Rbrace);
            with_braces(p, start_pos_idx, expr)
        }
        token if token.is_keyword() => {
            match super::core::recover_keyword_field_name_if_probably_field(
                p,
                super::core::error_messages::keyword_field_in_expr,
            ) {
                Some((recovered_field_name, loc)) => {
                    p.expect(Token::Colon);
                    let opt = parse_optional_label(p);
                    let field_expr = parse_expr(p);
                    let lid_idx = p.push_lident(&recovered_field_name);
                    let expr = p.arena_mut().push_expr(field_expr);
                    let first_row = ExpressionRecordField {
                        lid: with_loc(lid_idx, loc),
                        expr,
                        opt,
                    };
                    let expr = parse_record_expr(p, start_pos_idx, None, vec![first_row]);
                    p.expect(Token::Rbrace);
                    expr
                }
                None => {
                    let expr = parse_expr_block(p);
                    p.expect(Token::Rbrace);
                    with_braces(p, start_pos_idx, expr)
                }
            }
        }
        Token::Rbrace => {
            p.next();
            let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
            Expression {
                pexp_desc: Box::new(ExpressionDesc::Pexp_record(Box::new((vec![], None)))),
                pexp_loc: loc,
                pexp_attributes: Attributes::new(),
            }
        }
        Token::DotDotDot => {
            p.next();
            let spread_expr = parse_constrained_or_coerced_expr(p);
            p.expect(Token::Comma);
            let expr = parse_record_expr(p, start_pos_idx, Some(spread_expr), vec![]);
            p.expect(Token::Rbrace);
            expr
        }
        Token::String(s) => {
            let loc = p.mk_loc_current();
            p.next();
            let lid_idx = p.push_lident(&s);
            let field = with_loc(lid_idx, loc);
            match p.token {
                Token::Colon | Token::Equal => {
                    if p.token == Token::Equal {
                        p.err_at(
                            p.start_pos,
                            p.end_pos,
                            DiagnosticCategory::Message(
                                super::core::error_messages::RECORD_FIELD_MISSING_COLON.to_string(),
                            ),
                        );
                    }
                    p.next();
                    let field_expr = parse_expr(p);
                    p.optional(&Token::Comma);
                    let expr = p.arena_mut().push_expr(field_expr);
                    let first_row = ExpressionRecordField {
                        lid: field,
                        expr,
                        opt: false,
                    };
                    let expr = parse_record_expr_with_string_keys(p, start_pos_idx, first_row);
                    p.expect(Token::Rbrace);
                    expr
                }
                _ => {
                    let field_start = p.loc_start(field.loc);
                    let field_end = p.loc_end(field.loc);
                    let constant = parse_string_constant(p, field_start, field_end, &s);
                    let constant = Expression {
                        pexp_desc: Box::new(ExpressionDesc::Pexp_constant(Box::new(constant))),
                        pexp_loc: field.loc,
                        pexp_attributes: Attributes::new(),
                    };
                    let a = parse_primary_expr(p, constant, false);
                    let e = parse_binary_expr(p, a, 1, ExprContext::Ordinary);
                    let e = parse_ternary_expr(p, e);
                    finish_braced_block(p, start_pos_idx, e)
                }
            }
        }
        Token::Question => {
            let expr = parse_record_expr(p, start_pos_idx, None, vec![]);
            p.expect(Token::Rbrace);
            expr
        }
        Token::Lident(ref s) if s == "async" && super::core::is_es6_arrow_expression(p, false) => {
            p.expect(Token::Lident("async".into()));
            let expr =
                parse_es6_arrow_expression_async(p, Attributes::new(), ExprContext::Ordinary);
            let expr = parse_expr_block_first(p, Some(expr));
            p.expect(Token::Rbrace);
            with_braces(p, start_pos_idx, expr)
        }
        Token::Uident(_) | Token::Lident(_) => {
            let start_token_is_uident = matches!(p.token, Token::Uident(_));
            let value_or_constructor = parse_value_or_constructor(p);
            let path_ident = match &*value_or_constructor.pexp_desc {
                ExpressionDesc::Pexp_ident(path_ident) => Some(*path_ident),
                _ => None,
            };
            let Some(path_ident) = path_ident else {
                p.leave_breadcrumb(Grammar::ExprBlock);
                let a = parse_primary_expr(p, value_or_constructor, false);
                let e = parse_binary_expr(p, a, 1, ExprContext::Ordinary);
                let e = parse_ternary_expr(p, e);
                p.eat_breadcrumb();
                return finish_braced_block(p, start_pos_idx, e);
            };
            let ident_end_pos_idx = p.prev_end_pos_idx();
            match p.token {
                Token::Comma => {
                    p.next();
                    let value = if start_token_is_uident {
                        remove_module_name_from_punned_field_value(p, value_or_constructor)
                    } else {
                        value_or_constructor
                    };
                    let expr = p.arena_mut().push_expr(value);
                    let first_row = ExpressionRecordField {
                        lid: path_ident,
                        expr,
                        opt: false,
                    };
                    let expr = parse_record_expr(p, start_pos_idx, None, vec![first_row]);
                    p.expect(Token::Rbrace);
                    expr
                }
                Token::Colon | Token::Equal => {
                    if p.token == Token::Equal {
                        p.err_at(
                            p.start_pos,
                            p.end_pos,
                            DiagnosticCategory::Message(
                                super::core::error_messages::RECORD_FIELD_MISSING_COLON.to_string(),
                            ),
                        );
                    }
                    p.next();
                    let opt = parse_optional_label(p);
                    let field_expr = parse_expr(p);
                    let expr = p.arena_mut().push_expr(field_expr);
                    let first_row = ExpressionRecordField {
                        lid: path_ident,
                        expr,
                        opt,
                    };
                    if p.token == Token::Rbrace {
                        p.next();
                        let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
                        Expression {
                            pexp_desc: Box::new(ExpressionDesc::Pexp_record(Box::new((
                                vec![first_row],
                                None,
                            )))),
                            pexp_loc: loc,
                            pexp_attributes: Attributes::new(),
                        }
                    } else {
                        p.expect(Token::Comma);
                        let expr = parse_record_expr(p, start_pos_idx, None, vec![first_row]);
                        p.expect(Token::Rbrace);
                        expr
                    }
                }
                // error case
                Token::Lident(_) => {
                    if p.prev_end_pos.line < p.start_pos.line {
                        p.expect(Token::Comma);
                    } else {
                        p.expect(Token::Colon);
                    }
                    let expr = p.arena_mut().push_expr(value_or_constructor);
                    let first_row = ExpressionRecordField {
                        lid: path_ident,
                        expr,
                        opt: false,
                    };
                    let expr = parse_record_expr(p, start_pos_idx, None, vec![first_row]);
                    p.expect(Token::Rbrace);
                    expr
                }
                Token::Semicolon => {
                    // `Ast_helper.Exp.ident path_ident` without `~loc`.
                    let first = ast_helper::make_ident_idx(path_ident.txt, LocIdx::none());
                    let first = Expression {
                        pexp_desc: Box::new(ExpressionDesc::Pexp_ident(path_ident)),
                        ..first
                    };
                    let expr = parse_expr_block_first(p, Some(first));
                    p.expect(Token::Rbrace);
                    with_braces(p, start_pos_idx, expr)
                }
                Token::Rbrace => {
                    p.next();
                    let expr = ast_helper::make_ident_idx(path_ident.txt, path_ident.loc);
                    let expr = Expression {
                        pexp_desc: Box::new(ExpressionDesc::Pexp_ident(path_ident)),
                        ..expr
                    };
                    with_braces(p, start_pos_idx, expr)
                }
                Token::EqualGreater => {
                    let loc = p.mk_loc_idx(start_pos_idx, ident_end_pos_idx);
                    let name = p.arena().get_longident(path_ident.txt).last_idx();
                    let pat = Pattern {
                        ppat_desc: Box::new(PatternDesc::Ppat_var(with_loc(name, loc))),
                        ppat_loc: loc,
                        ppat_attributes: Attributes::new(),
                    };
                    let term_param = super::core::FundefTermParam {
                        attrs: Attributes::new(),
                        label: ArgLabel::Nolabel,
                        expr: None,
                        pat,
                        start_pos_idx,
                    };
                    let a = parse_es6_arrow_expression_internal(
                        p,
                        false,
                        None,
                        Attributes::new(),
                        ExprContext::Ordinary,
                        Some(vec![super::core::FundefParameter::Term(term_param)]),
                    );
                    let e = parse_binary_expr(p, a, 1, ExprContext::Ordinary);
                    let e = parse_ternary_expr(p, e);
                    finish_braced_block(p, start_pos_idx, e)
                }
                _ => {
                    p.leave_breadcrumb(Grammar::ExprBlock);
                    let operand = ast_helper::make_ident_idx(path_ident.txt, path_ident.loc);
                    let operand = Expression {
                        pexp_desc: Box::new(ExpressionDesc::Pexp_ident(path_ident)),
                        ..operand
                    };
                    let a = parse_primary_expr(p, operand, false);
                    let e = parse_binary_expr(p, a, 1, ExprContext::Ordinary);
                    let e = parse_ternary_expr(p, e);
                    p.eat_breadcrumb();
                    finish_braced_block(p, start_pos_idx, e)
                }
            }
        }
        _ => {
            let expr = parse_expr_block(p);
            p.expect(Token::Rbrace);
            with_braces(p, start_pos_idx, expr)
        }
    }
}

/// The shared tail of the expression branches of `parse_braced_or_record_expr`:
/// `Semicolon`/`_` continue the block with `e` first; `Rbrace` ends it.
fn finish_braced_block(p: &mut Parser<'_>, start_pos_idx: PosIdx, e: Expression) -> Expression {
    if p.token == Token::Rbrace {
        p.next();
        return with_braces(p, start_pos_idx, e);
    }
    let expr = parse_expr_block_first(p, Some(e));
    p.expect(Token::Rbrace);
    with_braces(p, start_pos_idx, expr)
}

/// OCaml `parse_optional_label` (compiler/syntax/src/res_core.ml:1440-1445).
fn parse_optional_label(p: &mut Parser<'_>) -> bool {
    p.optional(&Token::Question)
}

/// OCaml `remove_module_name_from_punned_field_value`
/// (compiler/syntax/src/res_core.ml:648-658): `A.a` becomes `a`.
fn remove_module_name_from_punned_field_value(p: &mut Parser<'_>, exp: Expression) -> Expression {
    let ExpressionDesc::Pexp_ident(path_ident) = &*exp.pexp_desc else {
        return exp;
    };
    let last = p.arena().get_longident(path_ident.txt).last_idx();
    let lid_idx = p.push_longident(Longident::Lident(last));
    Expression {
        pexp_desc: Box::new(ExpressionDesc::Pexp_ident(with_loc(
            lid_idx,
            path_ident.loc,
        ))),
        ..exp
    }
}

/// OCaml `parse_record_expr_row` (compiler/syntax/src/res_core.ml:3440-3508).
fn parse_record_expr_row(p: &mut Parser<'_>) -> Option<ExpressionRecordField> {
    let attrs = parse_attributes(p);
    if p.token == Token::DotDotDot {
        p.err(DiagnosticCategory::Message(
            super::core::error_messages::RECORD_EXPR_SPREAD.to_string(),
        ));
        p.next();
    }
    match p.token {
        Token::Lident(_) | Token::Uident(_) => {
            let start_token_is_uident = matches!(p.token, Token::Uident(_));
            let field = parse_record_row_value_path(p);
            match p.token {
                Token::Colon | Token::Equal => {
                    if p.token == Token::Equal {
                        p.err_at(
                            p.start_pos,
                            p.end_pos,
                            DiagnosticCategory::Message(
                                super::core::error_messages::RECORD_FIELD_MISSING_COLON.to_string(),
                            ),
                        );
                    }
                    p.next();
                    let opt = parse_optional_label(p);
                    let field_expr = parse_expr(p);
                    let expr = p.arena_mut().push_expr(field_expr);
                    Some(ExpressionRecordField {
                        lid: field,
                        expr,
                        opt,
                    })
                }
                _ => {
                    let value = punned_field_value(p, field, attrs, start_token_is_uident);
                    let expr = p.arena_mut().push_expr(value);
                    Some(ExpressionRecordField {
                        lid: field,
                        expr,
                        opt: false,
                    })
                }
            }
        }
        Token::Question => {
            p.next();
            match p.token {
                Token::Lident(_) | Token::Uident(_) => {
                    let start_token_is_uident = matches!(p.token, Token::Uident(_));
                    let field = parse_record_row_value_path(p);
                    let value = punned_field_value(p, field, attrs, start_token_is_uident);
                    let expr = p.arena_mut().push_expr(value);
                    Some(ExpressionRecordField {
                        lid: field,
                        expr,
                        opt: true,
                    })
                }
                _ => None,
            }
        }
        _ if p.token.is_keyword() => {
            match super::core::recover_keyword_field_name_if_probably_field(
                p,
                super::core::error_messages::keyword_field_in_expr,
            ) {
                Some((recovered_field_name, loc)) => {
                    p.expect(Token::Colon);
                    let opt = parse_optional_label(p);
                    let field_expr = parse_expr(p);
                    let lid_idx = p.push_lident(&recovered_field_name);
                    let expr = p.arena_mut().push_expr(field_expr);
                    Some(ExpressionRecordField {
                        lid: with_loc(lid_idx, loc),
                        expr,
                        opt,
                    })
                }
                None => {
                    super::core::emit_keyword_field_error(
                        p,
                        super::core::error_messages::keyword_field_in_expr,
                    );
                    None
                }
            }
        }
        _ => None,
    }
}

/// OCaml `parse_value_path` as used by record rows (res_core.ml:742-776).
fn parse_record_row_value_path(p: &mut Parser<'_>) -> Located<LidentIdx> {
    let (path, loc) = super::module::parse_value_path(p);
    let lid_idx = super::core::build_longident_idx(p, &path);
    with_loc(lid_idx, loc)
}

/// A punned record row value: `Ast_helper.Exp.ident ~loc:field.loc ~attrs field`,
/// with the module path removed when the row started with an uppercase name.
fn punned_field_value(
    p: &mut Parser<'_>,
    field: Located<LidentIdx>,
    attrs: Attributes,
    start_token_is_uident: bool,
) -> Expression {
    let value = Expression {
        pexp_desc: Box::new(ExpressionDesc::Pexp_ident(field)),
        pexp_loc: field.loc,
        pexp_attributes: attrs,
    };
    if start_token_is_uident {
        remove_module_name_from_punned_field_value(p, value)
    } else {
        value
    }
}

/// OCaml `parse_record_expr_row_with_string_key` (res_core.ml:3413-3438).
fn parse_record_expr_row_with_string_key(p: &mut Parser<'_>) -> Option<ExpressionRecordField> {
    let Token::String(s) = p.token.clone() else {
        return None;
    };
    let loc = p.mk_loc_current();
    p.next();
    let lid_idx = p.push_lident(&s);
    let field = with_loc(lid_idx, loc);
    match p.token {
        Token::Colon | Token::Equal => {
            if p.token == Token::Equal {
                p.err_at(
                    p.start_pos,
                    p.end_pos,
                    DiagnosticCategory::Message(
                        super::core::error_messages::RECORD_FIELD_MISSING_COLON.to_string(),
                    ),
                );
            }
            p.next();
            let field_expr = parse_expr(p);
            let expr = p.arena_mut().push_expr(field_expr);
            Some(ExpressionRecordField {
                lid: field,
                expr,
                opt: false,
            })
        }
        _ => {
            let value = Expression {
                pexp_desc: Box::new(ExpressionDesc::Pexp_ident(field)),
                pexp_loc: field.loc,
                pexp_attributes: Attributes::new(),
            };
            let expr = p.arena_mut().push_expr(value);
            Some(ExpressionRecordField {
                lid: field,
                expr,
                opt: false,
            })
        }
    }
}

/// OCaml `parse_record_expr_with_string_keys` (res_core.ml:3533-3544).
fn parse_record_expr_with_string_keys(
    p: &mut Parser<'_>,
    start_pos_idx: PosIdx,
    first_row: ExpressionRecordField,
) -> Expression {
    let mut rows = vec![first_row];
    rows.extend(super::core::parse_comma_delimited_region(
        p,
        Grammar::RecordRowsStringKey,
        Token::Rbrace,
        parse_record_expr_row_with_string_key,
    ));
    let loc = p.mk_loc_idx_to_end(start_pos_idx);
    let fields = rows
        .into_iter()
        .map(|row| {
            let name = match p.arena().get_longident(row.lid.txt) {
                Longident::Lident(name) => p.arena().get_string(*name).to_owned(),
                _ => unreachable!("string-key record rows are always Lident"),
            };
            (
                Loc {
                    txt: Label::Owned(name),
                    loc: row.lid.loc,
                },
                row.expr,
            )
        })
        .collect();
    Expression {
        pexp_desc: Box::new(ExpressionDesc::Pexp_object_literal(Box::new(fields))),
        pexp_loc: loc,
        pexp_attributes: Attributes::new(),
    }
}

/// OCaml `parse_record_expr` (res_core.ml:3546-3559).
fn parse_record_expr(
    p: &mut Parser<'_>,
    start_pos_idx: PosIdx,
    spread: Option<Expression>,
    mut rows: Vec<ExpressionRecordField>,
) -> Expression {
    rows.extend(super::core::parse_comma_delimited_region(
        p,
        Grammar::RecordRows,
        Token::Rbrace,
        parse_record_expr_row,
    ));
    if rows.is_empty() {
        p.err(DiagnosticCategory::Message(
            "Record spread needs at least one field that's updated".to_string(),
        ));
    }
    let loc = p.mk_loc_idx_to_end(start_pos_idx);
    let spread = spread.map(|spread| p.arena_mut().push_expr(spread));
    Expression {
        pexp_desc: Box::new(ExpressionDesc::Pexp_record(Box::new((rows, spread)))),
        pexp_loc: loc,
        pexp_attributes: Attributes::new(),
    }
}

/// OCaml `parse_expr_block_item` (compiler/syntax/src/res_core.ml:3574-3658).
fn parse_expr_block_item(p: &mut Parser<'_>) -> Expression {
    let start_pos_idx = p.start_pos_idx();
    let attrs = parse_attributes(p);
    match p.token {
        Token::Break | Token::Continue => {
            let is_break = p.token == Token::Break;
            p.next();
            let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
            Expression {
                pexp_desc: Box::new(if is_break {
                    ExpressionDesc::Pexp_break
                } else {
                    ExpressionDesc::Pexp_continue
                }),
                pexp_loc: loc,
                pexp_attributes: attrs,
            }
        }
        Token::Module => {
            p.next();
            if p.token == Token::Lparen {
                let expr = parse_first_class_module_expr(p, start_pos_idx);
                let a = parse_primary_expr(p, expr, false);
                let expr = parse_binary_expr(p, a, 1, ExprContext::Ordinary);
                return parse_ternary_expr(p, expr);
            }
            let name = parse_module_name(p);
            let body = super::module::parse_module_binding_body(p);
            parse_newline_or_semicolon_expr_block(p);
            let expr = parse_expr_block(p);
            let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
            let body = p.arena_mut().push_mod_expr(body);
            let expr = p.arena_mut().push_expr(expr);
            Expression {
                pexp_desc: Box::new(ExpressionDesc::Pexp_letmodule(Box::new((name, body, expr)))),
                pexp_loc: loc,
                pexp_attributes: Attributes::new(),
            }
        }
        Token::Exception => {
            // OCaml `parse_exception_def ~attrs` (res_core.ml:6626-6631).
            let exception_start_idx = p.start_pos_idx();
            p.expect(Token::Exception);
            let ext = super::module::parse_extension_constructor(
                p,
                attrs,
                Some(exception_start_idx),
                false,
            );
            parse_newline_or_semicolon_expr_block(p);
            let block_expr = parse_expr_block(p);
            let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
            let block_expr = p.arena_mut().push_expr(block_expr);
            Expression {
                pexp_desc: Box::new(ExpressionDesc::Pexp_letexception(Box::new((
                    ext, block_expr,
                )))),
                pexp_loc: loc,
                pexp_attributes: Attributes::new(),
            }
        }
        Token::Open => {
            // OCaml `parse_open_description ~attrs` (res_core.ml); the
            // description's attributes are not kept by `Exp.open_`.
            p.leave_breadcrumb(Grammar::OpenDescription);
            p.expect(Token::Open);
            let override_flag = if p.optional(&Token::Bang) {
                OverrideFlag::Override
            } else {
                OverrideFlag::Fresh
            };
            let lid = super::module::parse_module_long_ident(p);
            p.eat_breadcrumb();
            parse_newline_or_semicolon_expr_block(p);
            let block_expr = parse_expr_block(p);
            let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
            let block_expr = p.arena_mut().push_expr(block_expr);
            Expression {
                pexp_desc: Box::new(ExpressionDesc::Pexp_open(Box::new((
                    override_flag,
                    lid,
                    block_expr,
                )))),
                pexp_loc: loc,
                pexp_attributes: Attributes::new(),
            }
        }
        Token::Let { unwrap } => {
            let (rec_flag, bindings) =
                super::module::parse_let_bindings_item(p, unwrap, attrs, start_pos_idx);
            parse_newline_or_semicolon_expr_block(p);
            let next = if grammar::is_block_expr_start(&p.token) {
                parse_expr_block(p)
            } else {
                let loc = p.mk_loc_current();
                ast_helper::make_unit(p, loc)
            };
            let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
            let next = p.arena_mut().push_expr(next);
            Expression {
                pexp_desc: Box::new(ExpressionDesc::Pexp_let(Box::new((
                    rec_flag, bindings, next,
                )))),
                pexp_loc: loc,
                pexp_attributes: Attributes::new(),
            }
        }
        Token::Typ => {
            // Parse to be able to give a good error message.
            let type_start = *p.arena().get_position(start_pos_idx);
            p.begin_region();
            let type_start_idx = p.start_pos_idx();
            let _ = super::module::parse_type_definition_or_extension(p, &attrs, type_start_idx);
            p.end_region();
            p.err_at(
                type_start,
                p.prev_end_pos,
                DiagnosticCategory::Message(
                    super::core::error_messages::TYPE_DEFINITION_IN_FUNCTION.to_string(),
                ),
            );
            parse_newline_or_semicolon_expr_block(p);
            parse_expr_block(p)
        }
        _ => {
            let mut e1 = parse_expr(p);
            if !attrs.is_empty() {
                let mut all = attrs;
                all.extend(e1.pexp_attributes.into_vec());
                e1.pexp_attributes = all;
            }
            parse_newline_or_semicolon_expr_block(p);
            if grammar::is_block_expr_start(&p.token) {
                let e2 = parse_expr_block(p);
                let loc = p.mk_loc_spanning_preserve_ghost(e1.pexp_loc, e2.pexp_loc);
                let e1 = p.arena_mut().push_expr(e1);
                let e2 = p.arena_mut().push_expr(e2);
                Expression {
                    pexp_desc: Box::new(ExpressionDesc::Pexp_sequence(e1, e2)),
                    pexp_loc: loc,
                    pexp_attributes: Attributes::new(),
                }
            } else {
                e1
            }
        }
    }
}

/// OCaml `parse_expr_block` without `?first` (res_core.ml:3672-3688).
fn parse_expr_block(p: &mut Parser<'_>) -> Expression {
    parse_expr_block_first(p, None)
}

/// OCaml `parse_expr_block ?first` (compiler/syntax/src/res_core.ml:3672-3688).
fn parse_expr_block_first(p: &mut Parser<'_>, first: Option<Expression>) -> Expression {
    p.leave_breadcrumb(Grammar::ExprBlock);
    let item = match first {
        Some(e) => e,
        None => parse_expr_block_item(p),
    };
    parse_newline_or_semicolon_expr_block(p);
    let block_expr = if grammar::is_block_expr_start(&p.token) {
        let next = parse_expr_block_item(p);
        let loc = p.mk_loc_spanning_preserve_ghost(item.pexp_loc, next.pexp_loc);
        let item = p.arena_mut().push_expr(item);
        let next = p.arena_mut().push_expr(next);
        Expression {
            pexp_desc: Box::new(ExpressionDesc::Pexp_sequence(item, next)),
            pexp_loc: loc,
            pexp_attributes: Attributes::new(),
        }
    } else {
        item
    };
    p.eat_breadcrumb();
    over_parse_constrained_or_coerced_or_arrow_expression(p, block_expr)
}

/// Parse a module name.
fn parse_module_name(p: &mut Parser<'_>) -> Located<StrIdx> {
    match &p.token {
        Token::Uident(name) => {
            let name = name.clone();
            let loc = p.mk_loc_current();
            p.next();
            let str_idx = p.arena_mut().push_interned_string(&name);
            with_loc(str_idx, loc)
        }
        _ => {
            p.err(DiagnosticCategory::Uident(p.token.clone().into_owned()));
            let str_idx = p.arena_mut().intern("_");
            mknoloc(str_idx)
        }
    }
}

// ============================================================================
// Control Flow Expressions
// ============================================================================

/// Parse the condition of an if expression.
/// OCaml: parse_if_condition
fn parse_if_condition(p: &mut Parser<'_>) -> Expression {
    p.leave_breadcrumb(Grammar::IfCondition);
    let condition = parse_expr_with_context(p, ExprContext::When);
    p.eat_breadcrumb();
    condition
}

/// Parse the then-branch of an if expression.
/// OCaml: parse_then_branch
fn parse_then_branch(p: &mut Parser<'_>) -> Expression {
    p.leave_breadcrumb(Grammar::IfBranch);
    p.expect(Token::Lbrace);
    let then_expr = parse_expr_block(p);
    p.expect(Token::Rbrace);
    p.eat_breadcrumb();
    then_expr
}

/// Parse the else-branch of an if expression (body only, after `else` is consumed).
/// OCaml: parse_else_branch
fn parse_else_branch(p: &mut Parser<'_>) -> Expression {
    p.expect(Token::Lbrace);
    let block_expr = parse_expr_block(p);
    p.expect(Token::Rbrace);
    block_expr
}

/// Parse the body of an if expression (after `if` is consumed).
/// OCaml: parse_if_expr
///
/// This function handles the region management for error suppression:
/// - The calling function (parse_if_or_if_let_expression) has already called begin_region
/// - When we see `else`, we end_region (to allow else branch to report its own errors)
///   then begin_region for the else branch
/// - We end_region at the end in both cases
fn parse_if_expr_body(p: &mut Parser<'_>, start_pos_idx: PosIdx) -> Expression {
    let condition = parse_if_condition(p);
    let then_branch = parse_then_branch(p);

    let else_branch = if p.token == Token::Else {
        // End the region for the then-branch (allows else branch to report errors)
        p.end_region();
        p.leave_breadcrumb(Grammar::ElseBranch);
        p.next(); // consume `else`
        // Begin a new region for the else-branch
        p.begin_region();

        let else_expr = if p.token == Token::If {
            // `else if` - recursively parse another if expression
            // Note: parse_if_or_if_let_expression will do its own begin_region
            parse_if_or_if_let_expression(p)
        } else {
            parse_else_branch(p)
        };

        p.eat_breadcrumb();
        p.end_region();
        Some(p.arena_mut().push_expr(else_expr))
    } else {
        // No else branch - end the region here
        p.end_region();
        None
    };

    let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);

    let cond_idx = p.arena_mut().push_expr(condition);
    let then_idx = p.arena_mut().push_expr(then_branch);
    Expression {
        pexp_desc: Box::new(ExpressionDesc::Pexp_ifthenelse(Box::new((
            cond_idx,
            then_idx,
            else_branch,
        )))),
        pexp_loc: loc,
        pexp_attributes: Attributes::new(),
    }
}

/// Parse an if expression (or if-let expression).
/// OCaml: parse_if_or_if_let_expression
///
/// This is the main entry point for parsing if expressions.
/// It sets up the region and breadcrumb, then delegates to parse_if_expr_body.
fn parse_if_or_if_let_expression(p: &mut Parser<'_>) -> Expression {
    p.begin_region();
    p.leave_breadcrumb(Grammar::ExprIf);
    let start_pos_idx = p.start_pos_idx();
    p.expect(Token::If);

    let expr = match &p.token {
        Token::Let { .. } => {
            // if-let expression: parse as a match
            p.next(); // consume `let`
            parse_if_let_expr(p, start_pos_idx)
        }
        _ => parse_if_expr_body(p, start_pos_idx),
    };

    p.eat_breadcrumb();
    expr
}

/// Parse an if-let expression (after `if` and `let` are consumed).
/// OCaml: parse_if_let_expr
///
/// Produces a Pexp_match and emits an experimental if-let error message.
fn parse_if_let_expr(p: &mut Parser<'_>, start_pos_idx: PosIdx) -> Expression {
    let pattern = super::pattern::parse_pattern(p);
    p.expect(Token::Equal);
    let condition_expr = parse_if_condition(p);
    let then_expr = parse_then_branch(p);

    let else_expr = match &p.token {
        Token::Else => {
            p.end_region();
            p.leave_breadcrumb(Grammar::ElseBranch);
            p.next(); // consume `else`
            p.begin_region();
            let else_expr = match &p.token {
                Token::If => parse_if_or_if_let_expression(p),
                _ => parse_else_branch(p),
            };
            p.eat_breadcrumb();
            p.end_region();
            else_expr
        }
        _ => {
            p.end_region();
            // No else: use () as the else expression
            let cur_start = p.start_pos_idx();
            let unit_loc = p.mk_loc_idx_to_prev_end(cur_start);
            ast_helper::make_unit(p, unit_loc)
        }
    };

    let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);

    // Build the match expression: match condition { | pattern => then | _ => else }
    let cond_idx = p.arena_mut().push_expr(condition_expr);
    let pattern_idx = p.arena_mut().push_pat(pattern);
    let then_expr_idx = p.arena_mut().push_expr(then_expr);
    // OCaml `Ast_helper.Pat.any ()` uses the default (none) location.
    let any_pat = Pattern {
        ppat_desc: Box::new(PatternDesc::Ppat_any),
        ppat_loc: LocIdx::none(),
        ppat_attributes: Attributes::new(),
    };
    let any_pat_idx = p.arena_mut().push_pat(any_pat);
    let else_expr_idx = p.arena_mut().push_expr(else_expr);
    let if_let_expr = Expression {
        pexp_desc: Box::new(ExpressionDesc::Pexp_match(Box::new((
            cond_idx,
            vec![
                Case {
                    pc_bar: None,
                    pc_lhs: pattern_idx,
                    pc_guard: None,
                    pc_rhs: then_expr_idx,
                },
                Case {
                    pc_bar: None,
                    pc_lhs: any_pat_idx,
                    pc_guard: None,
                    pc_rhs: else_expr_idx,
                },
            ],
        )))),
        pexp_loc: loc,
        pexp_attributes: Attributes::new(),
    };

    // Emit the experimental if-let error message using ResPrinter
    {
        use super::comment_table::CommentTable;
        use super::doc::Doc;
        use super::printer;

        let state = printer::PrinterState::init();
        let mut cmt_tbl = CommentTable::new();
        let msg = Doc::concat(vec![
            Doc::text("If-let is currently highly experimental."),
            Doc::line(),
            Doc::text("Use a regular `switch` with pattern matching instead:"),
            Doc::concat(vec![
                Doc::hard_line(),
                Doc::hard_line(),
                printer::print_expression(&state, &if_let_expr, &mut cmt_tbl, p.arena()),
            ]),
        ])
        .to_string(80);

        p.err_at(
            p.loc_start(if_let_expr.pexp_loc),
            p.loc_end(if_let_expr.pexp_loc),
            DiagnosticCategory::message(&msg),
        );
    }

    if_let_expr
}

/// Legacy entry point for if expressions - wraps parse_if_or_if_let_expression.
fn parse_if_expr(p: &mut Parser<'_>) -> Expression {
    parse_if_or_if_let_expression(p)
}

/// Parse a first-class module expression: module(Expr) or module(Expr: ModType)
/// `module` keyword already consumed, expects `(` next
fn parse_first_class_module_expr(p: &mut Parser<'_>, start_pos_idx: PosIdx) -> Expression {
    p.expect(Token::Lparen);
    parse_first_class_module_expr_inner(p, start_pos_idx)
}

/// Parse a first-class module expression after `module(` has been matched.
/// Used when the caller has already consumed `module` and checked for `(`.
/// Public for use from module.rs when parsing structure items.
pub fn parse_first_class_module_expr_from_paren(
    p: &mut Parser<'_>,
    start_pos_idx: PosIdx,
) -> Expression {
    p.expect(Token::Lparen);
    parse_first_class_module_expr_inner(p, start_pos_idx)
}

/// Inner implementation for first-class module expression parsing.
/// Expects the `(` to already be consumed.
fn parse_first_class_module_expr_inner(p: &mut Parser<'_>, start_pos_idx: PosIdx) -> Expression {
    // Use parse_module_expr_without_constraint so the `:` is available for package type.
    // For `module(Foo: Bar)`, we want Pexp_constraint(Pexp_pack(Foo), Ptyp_package(Box::new(Bar))),
    // not Pexp_pack(Box::new(Pmod_constraint(Foo, Bar))).
    let mod_expr = super::module::parse_module_expr_without_constraint(p);
    // Capture position after module expr for pack_expr location (before parsing type)
    let mod_expr_end_idx = p.prev_end_pos_idx();

    // Check for type annotation: module(Expr: ModType)
    // This becomes Pexp_constraint(Box::new((Pexp_pack(ME), Ptyp_package(Box::new(...)))))
    let package_type = if p.token == Token::Colon {
        // OCaml captures colon_start BEFORE consuming colon, then parses attributes,
        // then passes colon_start to parse_package_type
        let colon_pos_idx = p.start_pos_idx();
        p.next();
        // Parse any attributes between : and the module identifier
        let attrs = parse_attributes(p);
        Some(super::typ::parse_package_type(p, colon_pos_idx, attrs))
    } else {
        None
    };

    p.expect(Token::Rparen);
    let full_loc = p.mk_loc_idx_to_prev_end(start_pos_idx);

    if let Some(pkg_type) = package_type {
        // OCaml: when constrained, pack_expr location spans only start to end of module expr (not including type)
        let pack_loc = p.mk_loc_idx(start_pos_idx, mod_expr_end_idx);
        let pack_expr = Expression {
            pexp_desc: Box::new(ExpressionDesc::Pexp_pack(
                p.arena_mut().push_mod_expr(mod_expr),
            )),
            pexp_loc: pack_loc,
            pexp_attributes: Attributes::new(),
        };
        let pack_idx = p.arena_mut().push_expr(pack_expr);
        let pkg_type_idx = p.arena_mut().push_core_type(pkg_type);
        Expression {
            pexp_desc: Box::new(ExpressionDesc::Pexp_constraint(Box::new((
                pack_idx,
                pkg_type_idx,
            )))),
            pexp_loc: full_loc,
            pexp_attributes: Attributes::new(),
        }
    } else {
        // Without constraint, pack_expr uses full location
        Expression {
            pexp_desc: Box::new(ExpressionDesc::Pexp_pack(
                p.arena_mut().push_mod_expr(mod_expr),
            )),
            pexp_loc: full_loc,
            pexp_attributes: Attributes::new(),
        }
    }
}

/// Parse a block expression sequence for switch case RHS (no braces).
/// Parses one or more expressions separated by newlines/semicolons,
/// stopping at `|` (next case) or `}` (end of switch).
fn parse_switch_case_block(p: &mut Parser<'_>) -> Expression {
    // OCaml `parse_pattern_match_case` parses the right-hand side with the
    // ordinary `parse_expr_block` (compiler/syntax/src/res_core.ml:3988).
    parse_expr_block(p)
}

/// Parse a switch expression.
fn parse_switch_expr(p: &mut Parser<'_>) -> Expression {
    let start_pos_idx = p.start_pos_idx();
    p.expect(Token::Switch);

    let scrutinee = parse_expr_with_context(p, ExprContext::When);
    p.expect(Token::Lbrace);

    let cases = parse_pattern_matching(p);

    p.expect(Token::Rbrace);
    let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);

    Expression {
        pexp_desc: {
            let s_idx = p.arena_mut().push_expr(scrutinee);
            Box::new(ExpressionDesc::Pexp_match(Box::new((s_idx, cases))))
        },
        pexp_loc: loc,
        pexp_attributes: Attributes::new(),
    }
}

/// OCaml `parse_pattern_matching` (compiler/syntax/src/res_core.ml:3997-4009),
/// shared by `switch` and `try ... catch`.
fn parse_pattern_matching(p: &mut Parser<'_>) -> Vec<Case> {
    let cases = super::core::parse_delimited_region(
        p,
        Grammar::PatternMatching,
        Token::Rbrace,
        parse_pattern_match_case,
    );
    if cases.is_empty() {
        p.err_at(
            p.prev_end_pos,
            p.end_pos,
            DiagnosticCategory::Message("Pattern matching needs at least one case".to_string()),
        );
    }
    cases
}

/// OCaml `parse_pattern_match_case` (compiler/syntax/src/res_core.ml:3972-3995).
fn parse_pattern_match_case(p: &mut Parser<'_>) -> Option<Case> {
    p.begin_region();
    p.leave_breadcrumb(Grammar::PatternMatchCase);
    if p.token != Token::Bar {
        p.end_region();
        p.eat_breadcrumb();
        return None;
    }
    let bar_pos = Some(p.start_pos_idx());
    p.next();
    p.leave_breadcrumb(Grammar::Pattern);
    let lhs = super::pattern::parse_pattern(p);
    p.eat_breadcrumb();
    // OCaml `parse_pattern_guard` accepts both `when` and `if`.
    let guard = if matches!(p.token, Token::When | Token::If) {
        p.next();
        Some(parse_expr_with_context(p, ExprContext::When))
    } else {
        None
    };
    if p.token == Token::EqualGreater {
        p.next();
    } else {
        // OCaml `Recover.recover_equal_greater`.
        p.expect(Token::EqualGreater);
        if p.token == Token::MinusGreater {
            p.next();
        }
    }
    let rhs = parse_switch_case_block(p);
    let lhs_idx = p.arena_mut().push_pat(lhs);
    let guard_idx = guard.map(|g| p.arena_mut().push_expr(g));
    let rhs_idx = p.arena_mut().push_expr(rhs);
    p.end_region();
    p.eat_breadcrumb();
    Some(Case {
        pc_bar: bar_pos,
        pc_lhs: lhs_idx,
        pc_guard: guard_idx,
        pc_rhs: rhs_idx,
    })
}

/// Parse a while expression.
fn parse_while_expr(p: &mut Parser<'_>) -> Expression {
    let start_pos_idx = p.start_pos_idx();
    p.expect(Token::While);

    let condition = parse_expr_with_context(p, ExprContext::When);
    p.expect(Token::Lbrace);
    // Use parse_expr_block (no res.braces) for while body, matching OCaml behavior
    let body = parse_expr_block(p);
    p.expect(Token::Rbrace);

    let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);

    Expression {
        pexp_desc: {
            let c_idx = p.arena_mut().push_expr(condition);
            let b_idx = p.arena_mut().push_expr(body);
            Box::new(ExpressionDesc::Pexp_while(c_idx, b_idx))
        },
        pexp_loc: loc,
        pexp_attributes: Attributes::new(),
    }
}

/// Parse a for expression.
///
/// For loop patterns have complex parsing due to optional parentheses:
/// - `for () in 0 to 10 {...}` - unit pattern without outer parens
/// - `for (pattern in 0 to 10) {...}` - pattern with optional outer parens wrapping entire head
/// - `for (a, b) in 0 to 10 {...}` - tuple pattern (no outer paren)
fn parse_for_expr(p: &mut Parser<'_>) -> Expression {
    let start_pos_idx = p.start_pos_idx();
    p.expect(Token::For);
    p.leave_breadcrumb(Grammar::ExprFor);
    p.begin_region();

    // Upstream #7887 (`compiler/syntax/src/res_core.ml` `parse_for_expression`):
    // accept an optional `await` immediately after `for`, marking this as a
    // `for await ... of ...` loop.
    let await_kw = if p.token == Token::Await {
        p.next();
        true
    } else {
        false
    };

    let (pat, has_opening_paren) = if p.token == Token::Lparen {
        let lparen_pos_idx = p.start_pos_idx();
        p.next();

        if p.token == Token::Rparen {
            // for () - unit pattern, then check for alias
            p.next();
            let loc = p.mk_loc_idx_to_prev_end(lparen_pos_idx);
            let unit_pat = super::pattern::make_unit_construct_pattern(p, loc);
            let pat = super::pattern::parse_alias_pattern(p, unit_pat, &[]);
            (pat, false)
        } else {
            // Could be:
            // 1. for (pattern in start to end) - outer paren wraps for head
            // 2. for (a, b) in start to end - tuple pattern
            p.leave_breadcrumb(Grammar::Pattern);
            let pat = super::pattern::parse_pattern(p);
            p.eat_breadcrumb();

            if p.token == Token::Comma {
                // Tuple pattern: for (a, b, ...) in ...
                p.next();
                let tuple_pat = super::pattern::parse_tuple_pattern(p, lparen_pos_idx, pat, vec![]);
                let aliased = super::pattern::parse_alias_pattern(p, tuple_pat, &[]);
                (aliased, false)
            } else {
                // Pattern with outer paren: for (pattern in ...)
                // The ) will be expected after the end expression
                (pat, true)
            }
        }
    } else {
        // No leading paren: for pattern in ...
        p.leave_breadcrumb(Grammar::Pattern);
        let pat = super::pattern::parse_pattern(p);
        p.eat_breadcrumb();
        (pat, false)
    };

    parse_for_rest(p, start_pos_idx, has_opening_paren, await_kw, pat)
}

/// Continuation of `parse_for_expr`. Mirrors OCaml's `parse_for_rest`
/// (`compiler/syntax/src/res_core.ml` after #7887): dispatches on whether
/// we see `of` (for-of / for-await-of) or `in` (regular for-loop).
fn parse_for_rest(
    p: &mut Parser<'_>,
    start_pos_idx: crate::parse_arena::PosIdx,
    has_opening_paren: bool,
    await_kw: bool,
    pattern: super::ast::Pattern,
) -> Expression {
    match p.token {
        Token::Of => {
            p.next();
            let pattern = normalize_for_of_pattern(p, pattern);
            let iterable = parse_expr_with_context(p, ExprContext::When);
            let body = parse_for_loop_body(p, has_opening_paren);
            p.eat_breadcrumb();
            p.end_region();
            let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
            let pat_idx = p.arena_mut().push_pat(pattern);
            let it_idx = p.arena_mut().push_expr(iterable);
            let b_idx = p.arena_mut().push_expr(body);
            let desc = if await_kw {
                ExpressionDesc::Pexp_for_await_of(Box::new((pat_idx, it_idx, b_idx)))
            } else {
                ExpressionDesc::Pexp_for_of(Box::new((pat_idx, it_idx, b_idx)))
            };
            Expression {
                pexp_desc: Box::new(desc),
                pexp_loc: loc,
                pexp_attributes: Attributes::new(),
            }
        }
        Token::In => {
            if await_kw {
                p.err_at(
                    *p.arena().get_position(start_pos_idx),
                    p.end_pos,
                    DiagnosticCategory::Message(
                        "A `for await` loop must use `of`, like `for await item of items`."
                            .to_string(),
                    ),
                );
            }
            p.next();
            let start_expr = parse_expr(p);
            // res_core.ml:3853-3864: any other token is `unexpected` and the
            // direction defaults to `Upto`; the token is then consumed unless
            // it is the end of the file.
            let direction = if matches!(&p.token, Token::Lident(s) if s == "to") {
                DirectionFlag::Upto
            } else if matches!(&p.token, Token::Lident(s) if s == "downto") {
                DirectionFlag::Downto
            } else {
                p.err_unexpected();
                DirectionFlag::Upto
            };
            if p.token == Token::Eof {
                p.err_at(
                    p.start_pos,
                    p.end_pos,
                    DiagnosticCategory::Unexpected {
                        token: p.token.clone().into_owned(),
                        context: p.breadcrumbs().to_vec(),
                    },
                );
            } else {
                p.next();
            }
            let end_expr = parse_expr_with_context(p, ExprContext::When);
            let body = parse_for_loop_body(p, has_opening_paren);
            p.eat_breadcrumb();
            p.end_region();
            let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
            Expression {
                pexp_desc: {
                    let pat_idx = p.arena_mut().push_pat(pattern);
                    let s_idx = p.arena_mut().push_expr(start_expr);
                    let e_idx = p.arena_mut().push_expr(end_expr);
                    let b_idx = p.arena_mut().push_expr(body);
                    Box::new(ExpressionDesc::Pexp_for(Box::new((
                        pat_idx, s_idx, e_idx, direction, b_idx,
                    ))))
                },
                pexp_loc: loc,
                pexp_attributes: Attributes::new(),
            }
        }
        _ => {
            p.err(DiagnosticCategory::Message(
                "A for-loop has the following form: `for i in 0 to 10` or `for item of items`. \
                 Did you forget an `in` or `of` here?"
                    .to_string(),
            ));
            p.eat_breadcrumb();
            p.end_region();
            crate::parser::core::recover::default_expr(p.arena_mut())
        }
    }
}

/// Shared body parser used by both for-loop variants.
fn parse_for_loop_body(p: &mut Parser<'_>, has_opening_paren: bool) -> Expression {
    if has_opening_paren {
        p.expect(Token::Rparen);
    }
    p.expect(Token::Lbrace);
    let body = parse_expr_block(p);
    p.expect(Token::Rbrace);
    body
}

/// Mirrors OCaml's `normalize_for_of_pattern` (`res_core.ml` after #7887):
/// reject anything other than `_` or a variable. We replace destructuring
/// patterns with `_` and emit an error so parsing can continue.
fn normalize_for_of_pattern(
    p: &mut Parser<'_>,
    pattern: super::ast::Pattern,
) -> super::ast::Pattern {
    match &*pattern.ppat_desc {
        super::ast::PatternDesc::Ppat_any | super::ast::PatternDesc::Ppat_var(_) => pattern,
        _ => {
            p.err_at(
                p.loc_start(pattern.ppat_loc),
                p.loc_end(pattern.ppat_loc),
                DiagnosticCategory::Message(
                    "A `for...of` or `for await...of` loop only supports a variable or `_` on the \
                     left side. Destructuring patterns are not supported here."
                        .to_string(),
                ),
            );
            super::ast::Pattern {
                ppat_desc: Box::new(super::ast::PatternDesc::Ppat_any),
                ppat_loc: pattern.ppat_loc,
                ppat_attributes: super::ast::Attributes::new(),
            }
        }
    }
}

/// Parse a try expression.
fn parse_try_expr(p: &mut Parser<'_>) -> Expression {
    let start_pos_idx = p.start_pos_idx();
    p.expect(Token::Try);

    let body = parse_expr_with_context(p, ExprContext::When);
    // "catch" is not a keyword, but OCaml uses `Parser.expect Res_token.catch p`
    // where `Res_token.catch = Lident "catch"`. This produces "Did you forget a `catch` here?"
    p.expect(Token::Lident(Cow::Owned("catch".to_string())));
    p.expect(Token::Lbrace);

    let cases = parse_pattern_matching(p);

    p.expect(Token::Rbrace);
    let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);

    Expression {
        pexp_desc: {
            let b_idx = p.arena_mut().push_expr(body);
            Box::new(ExpressionDesc::Pexp_try(Box::new((b_idx, cases))))
        },
        pexp_loc: loc,
        pexp_attributes: Attributes::new(),
    }
}

// ============================================================================
// JSX Parsing (OCaml res_core.ml:836-958, 2826-3089)
// ============================================================================

#[derive(Clone, Copy, PartialEq, Eq)]
enum JsxIdentKind {
    Lower,
    Upper,
}

/// OCaml `peek_ident` (res_core.ml:840-845): the current identifier with its
/// start/end positions, without advancing.
fn jsx_peek_ident(p: &mut Parser<'_>) -> Option<(String, PosIdx, PosIdx, JsxIdentKind)> {
    let (txt, kind) = match &p.token {
        Token::Lident(txt) => (txt.to_string(), JsxIdentKind::Lower),
        Token::Uident(txt) => (txt.to_string(), JsxIdentKind::Upper),
        _ => return None,
    };
    Some((txt, p.start_pos_idx(), p.end_pos_idx(), kind))
}

/// OCaml `expect_ident` (res_core.ml:847-852).
fn jsx_expect_ident(p: &mut Parser<'_>) -> Option<(String, PosIdx, PosIdx, JsxIdentKind)> {
    let ident = jsx_peek_ident(p)?;
    p.next();
    Some(ident)
}

/// OCaml `read_hyphen_chain` (res_core.ml:855-874).
fn read_hyphen_chain(p: &mut Parser<'_>, buf: &mut String, last_end: &mut PosIdx) {
    while p.token == Token::Minus {
        p.next();
        match jsx_peek_ident(p) {
            Some((txt, _, _, _)) => {
                buf.push('-');
                buf.push_str(&txt);
                p.next();
                *last_end = p.prev_end_pos_idx();
            }
            None => {
                p.err(DiagnosticCategory::Message(
                    "JSX identifier cannot end with a hyphen".to_string(),
                ));
                return;
            }
        }
    }
}

/// OCaml `read_local_jsx_name` (res_core.ml:877-889).
fn read_local_jsx_name(p: &mut Parser<'_>) -> Option<(String, LocIdx, JsxIdentKind)> {
    let (head, start, head_end, kind) = jsx_expect_ident(p)?;
    let mut buf = head;
    let mut last_end = head_end;
    read_hyphen_chain(p, &mut buf, &mut last_end);
    let loc = p.mk_loc_idx(start, last_end);
    Some((buf, loc, kind))
}

/// OCaml `read_jsx_tag_name` (res_core.ml:901-958).
fn read_jsx_tag_name(p: &mut Parser<'_>) -> Result<(JsxTagName, LocIdx), String> {
    let Some((first_seg, start, first_end, kind)) = jsx_peek_ident(p) else {
        return Err(String::new());
    };
    if kind == JsxIdentKind::Lower {
        return read_local_jsx_name(p)
            .map(|(name, loc, _)| (JsxTagName::Lower(name), loc))
            .ok_or_else(String::new);
    }
    p.next();
    let mut segs = vec![first_seg];
    let mut last_end = first_end;
    loop {
        if p.token != Token::Dot {
            let path = super::core::build_longident(p.arena_mut(), &segs);
            let path_idx = p.push_longident(path);
            let loc = p.mk_loc_idx(start, last_end);
            return Ok((JsxTagName::Upper(path_idx), loc));
        }
        p.next();
        match jsx_peek_ident(p) {
            None => {
                p.err(DiagnosticCategory::Message(
                    "expected identifier after '.' in JSX tag name".to_string(),
                ));
                return Err(segs.join(".") + ".");
            }
            Some((txt, _, _, JsxIdentKind::Upper)) => {
                p.next();
                segs.push(txt);
                last_end = p.prev_end_pos_idx();
            }
            Some((_, _, _, JsxIdentKind::Lower)) => {
                let Some((lname, l_loc, _)) = read_local_jsx_name(p) else {
                    return Err(String::new());
                };
                let path = super::core::build_longident(p.arena_mut(), &segs);
                let path_idx = p.push_longident(path);
                let loc = p.mk_loc_idx_to_end_of(start, l_loc);
                return Ok((
                    JsxTagName::QualifiedLower {
                        path: path_idx,
                        name: lname,
                    },
                    loc,
                ));
            }
        }
    }
}

/// `Ast_helper.Jsx.longident_of_jsx_tag_name`, flattened to its segments
/// (`Longident.flatten`). Tag paths are built from `Lident`/`Ldot` only.
fn jsx_tag_name_segments<'p>(tag_name: &'p JsxTagName, p: &'p Parser<'_>) -> Vec<&'p str> {
    let arena = p.arena();
    let path_segments = |lid_idx| {
        arena
            .get_longident(lid_idx)
            .flatten_idx()
            .into_iter()
            .map(|idx| arena.get_string(idx))
    };
    match tag_name {
        JsxTagName::Lower(name) | JsxTagName::Invalid(name) => vec![name.as_str()],
        JsxTagName::Upper(lid_idx) => path_segments(*lid_idx).collect(),
        JsxTagName::QualifiedLower { path, name } => path_segments(*path)
            .chain(std::iter::once(name.as_str()))
            .collect(),
    }
}

/// `Ast_helper.Jsx.string_of_jsx_tag_name`.
fn jsx_tag_name_to_string_for_error(tag_name: &JsxTagName, p: &Parser<'_>) -> String {
    jsx_tag_name_segments(tag_name, p).join(".")
}

/// OCaml `parse_jsx_name` (res_core.ml:2826-2835).
fn parse_jsx_name(p: &mut Parser<'_>) -> (JsxTagName, LocIdx) {
    match read_jsx_tag_name(p) {
        Ok(name) => name,
        Err(invalid) => {
            p.err(DiagnosticCategory::Message(
                "A jsx name must be a lowercase or uppercase name, like: div in <div /> or Navbar in <Navbar />".to_string(),
            ));
            (JsxTagName::Invalid(invalid), LocIdx::none())
        }
    }
}

fn jsx_expression(desc: JsxElement, loc: LocIdx) -> Expression {
    Expression {
        pexp_desc: Box::new(ExpressionDesc::Pexp_jsx_element(Box::new(desc))),
        pexp_loc: loc,
        pexp_attributes: Attributes::new(),
    }
}

/// OCaml `parse_jsx_opening_or_self_closing_element` (res_core.ml:2837-2961).
fn parse_jsx_opening_or_self_closing_element(
    p: &mut Parser<'_>,
    start_pos_idx: PosIdx,
) -> Expression {
    let start_pos = *p.arena().get_position(start_pos_idx);
    let (name, name_loc) = parse_jsx_name(p);
    let props = parse_jsx_props(p);
    match p.token {
        Token::Forwardslash => {
            p.next();
            let jsx_end_pos = p.end_pos_idx();
            p.expect(Token::GreaterThan);
            let loc = p.mk_loc_idx(start_pos_idx, jsx_end_pos);
            jsx_expression(
                JsxElement::Unary(JsxUnaryElement {
                    tag_name: with_loc(name, name_loc),
                    props,
                }),
                loc,
            )
        }
        Token::GreaterThan => {
            let opening_tag_end = p.start_pos_idx();
            p.next();
            let children = parse_jsx_children(p);
            let closing_tag_start = if p.token == Token::LessThan && p.peek_slash() {
                let pos = p.start_pos_idx();
                p.next();
                p.next();
                Some(pos)
            } else if super::grammar::is_structure_item_start(&p.token) {
                None
            } else {
                p.err(DiagnosticCategory::Message(
                    "Did you forget a `</` here?".to_string(),
                ));
                None
            };
            let children: Vec<ExprIdx> = children
                .into_iter()
                .map(|e| p.arena_mut().push_expr(e))
                .collect();
            let token0 = p.token.clone().into_owned();
            let closing_tag = match token0 {
                Token::Lident(_) | Token::Uident(_) => {
                    let closing_name_res = read_jsx_tag_name(p);
                    let matches = matches!(&closing_name_res, Ok((closing, _))
                        if jsx_tag_name_segments(closing, p) == jsx_tag_name_segments(&name, p));
                    let (end_tag_name, closing_tag_end) = if matches {
                        let closing_tag_end = p.start_pos_idx();
                        p.expect(Token::GreaterThan);
                        (
                            closing_name_res.expect("matched closing name"),
                            closing_tag_end,
                        )
                    } else {
                        let end = p.prev_end_pos;
                        let opening_name = jsx_tag_name_to_string_for_error(&name, p);
                        if super::grammar::is_structure_item_start(&token0) {
                            p.err_at(
                                start_pos,
                                end,
                                DiagnosticCategory::Message(format!("Missing </{opening_name}>")),
                            );
                        } else {
                            p.err_at(
                                start_pos,
                                end,
                                DiagnosticCategory::Message(format!(
                                    "Closing jsx name should be the same as the opening name. Did you mean </{opening_name}> ?"
                                )),
                            );
                        }
                        p.expect(Token::GreaterThan);
                        let end_tag_name = match closing_name_res {
                            Ok(closing) => closing,
                            Err(invalid) => (JsxTagName::Invalid(invalid), LocIdx::none()),
                        };
                        (end_tag_name, p.prev_end_pos_idx())
                    };
                    closing_tag_start.map(|start| JsxClosingTag {
                        start,
                        name: with_loc(end_tag_name.0, end_tag_name.1),
                        end: closing_tag_end,
                    })
                }
                token => {
                    let end = p.prev_end_pos;
                    let opening_name = jsx_tag_name_to_string_for_error(&name, p);
                    if super::grammar::is_structure_item_start(&token) {
                        p.err_at(
                            start_pos,
                            end,
                            DiagnosticCategory::Message(format!("Missing </{opening_name}>")),
                        );
                    } else {
                        p.err_at(
                            start_pos,
                            end,
                            DiagnosticCategory::Message(format!(
                                "Closing jsx name should be the same as the opening name. Did you mean </{opening_name}> ?"
                            )),
                        );
                    }
                    None
                }
            };
            let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
            jsx_expression(
                JsxElement::Container(JsxContainerElement {
                    tag_name_start: with_loc(name, name_loc),
                    opening_end: opening_tag_end,
                    props,
                    children,
                    closing_tag,
                }),
                loc,
            )
        }
        _ => {
            p.err(DiagnosticCategory::unexpected(
                p.token.clone().into_owned(),
                p.breadcrumbs().to_vec(),
            ));
            let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
            jsx_expression(
                JsxElement::Unary(JsxUnaryElement {
                    tag_name: with_loc(name, name_loc),
                    props,
                }),
                loc,
            )
        }
    }
}

/// OCaml `parse_jsx` (res_core.ml:2972-2991).
fn parse_jsx(p: &mut Parser<'_>) -> Expression {
    p.leave_breadcrumb(Grammar::Jsx);
    let start_pos_idx = p.start_pos_idx();
    p.expect(Token::LessThan);
    let jsx_expr = match p.token {
        Token::Lident(_) | Token::Uident(_) => {
            parse_jsx_opening_or_self_closing_element(p, start_pos_idx)
        }
        Token::GreaterThan => parse_jsx_fragment(p, start_pos_idx),
        _ => {
            let (tag_name, loc) = parse_jsx_name(p);
            let segments: Vec<String> = jsx_tag_name_segments(&tag_name, p)
                .into_iter()
                .map(str::to_owned)
                .collect();
            let lid = super::core::build_longident(p.arena_mut(), &segments);
            let lid_idx = p.push_longident(lid);
            Expression {
                pexp_desc: Box::new(ExpressionDesc::Pexp_ident(with_loc(lid_idx, loc))),
                pexp_loc: loc,
                pexp_attributes: Attributes::new(),
            }
        }
    };
    p.eat_breadcrumb();
    jsx_expr
}

/// OCaml `parse_jsx_fragment` (res_core.ml:2997-3010).
fn parse_jsx_fragment(p: &mut Parser<'_>, start_pos_idx: PosIdx) -> Expression {
    let opening = p.start_pos_idx();
    p.expect(Token::GreaterThan);
    let children = parse_jsx_children(p);
    let closing = p.start_pos_idx();
    p.expect(Token::LessThan);
    p.expect(Token::Forwardslash);
    let end_pos = p.end_pos_idx();
    p.expect(Token::GreaterThan);
    let loc = p.mk_loc_idx(start_pos_idx, end_pos);
    let children: Vec<ExprIdx> = children
        .into_iter()
        .map(|e| p.arena_mut().push_expr(e))
        .collect();
    jsx_expression(
        JsxElement::Fragment(JsxFragment {
            opening,
            children,
            closing,
        }),
        loc,
    )
}

/// OCaml `parse_jsx_prop` (res_core.ml:3019-3056).
fn parse_jsx_prop(p: &mut Parser<'_>) -> Option<JsxProp> {
    match p.token {
        Token::Question | Token::Lident(_) => {
            let optional = p.optional(&Token::Question);
            match read_local_jsx_name(p) {
                Some((name, loc, JsxIdentKind::Lower)) => {
                    let name_idx = p.arena_mut().push_interned_string(&name);
                    let name = with_loc(name_idx, loc);
                    if optional {
                        return Some(JsxProp::Punning {
                            optional: true,
                            name,
                        });
                    }
                    if p.token == Token::Equal {
                        p.next();
                        let optional = p.optional(&Token::Question);
                        let operand = parse_atomic_expr(p);
                        let attr_expr = parse_primary_expr(p, operand, false);
                        let value = p.arena_mut().push_expr(attr_expr);
                        Some(JsxProp::Value {
                            name,
                            optional,
                            value,
                        })
                    } else {
                        Some(JsxProp::Punning {
                            optional: false,
                            name,
                        })
                    }
                }
                Some((_, _, JsxIdentKind::Upper)) => {
                    p.err(DiagnosticCategory::Message(
                        "JSX prop names must be lowercase".to_string(),
                    ));
                    None
                }
                None => None,
            }
        }
        Token::Lbrace => {
            let spread_start = p.start_pos_idx();
            p.next();
            if p.token != Token::DotDotDot {
                return None;
            }
            p.next();
            let operand = parse_expr(p);
            let attr_expr = parse_primary_expr(p, operand, false);
            if p.token != Token::Rbrace {
                return None;
            }
            let spread_end = p.end_pos_idx();
            let loc = p.mk_loc_idx(spread_start, spread_end);
            p.next();
            let expr = p.arena_mut().push_expr(attr_expr);
            Some(JsxProp::Spreading { loc, expr })
        }
        _ => None,
    }
}

/// OCaml `parse_jsx_props` (res_core.ml:3058-3059).
fn parse_jsx_props(p: &mut Parser<'_>) -> Vec<JsxProp> {
    super::core::parse_region(p, Grammar::JsxAttribute, parse_jsx_prop)
}

/// OCaml `parse_jsx_children` (res_core.ml:3061-3089).
fn parse_jsx_children(p: &mut Parser<'_>) -> Vec<Expression> {
    if p.token == Token::DotDotDot {
        p.err(DiagnosticCategory::Message(
            "Spreading JSX children is no longer supported.".to_string(),
        ));
        p.next();
        let operand = parse_atomic_expr(p);
        return vec![parse_primary_expr(p, operand, true)];
    }
    let mut children = vec![];
    loop {
        // res_core.ml `Lbrace when Parser.peek2 p = Rbrace`.
        let empty_braces = p.token == Token::Lbrace
            && p.lookahead(|p| {
                p.next();
                p.token == Token::Rbrace
            });
        match p.token {
            Token::Eof => return children,
            Token::LessThan if p.peek_slash() => return children,
            Token::Lbrace if empty_braces => {
                let start_pos_idx = p.start_pos_idx();
                let start_pos = p.start_pos;
                // Consuming `{` collects exactly the comments inside the braces.
                let comments_before = p.comments_len();
                p.next();
                let comments_inside = p.comments_len();
                p.next();
                // Only comment-containing containers are trivia. Keep bare `{}`
                // as an empty record, including when nested inside an
                // expression container.
                if comments_inside != comments_before {
                    let loc = crate::location::Location::from_positions(start_pos, p.prev_end_pos);
                    p.set_jsx_container(comments_before..comments_inside, loc);
                } else {
                    let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
                    let operand = Expression {
                        pexp_desc: Box::new(ExpressionDesc::Pexp_record(Box::new((vec![], None)))),
                        pexp_loc: loc,
                        pexp_attributes: Attributes::new(),
                    };
                    children.push(parse_primary_expr(p, operand, true));
                }
            }
            ref token if token == &Token::LessThan || grammar::is_jsx_child_start(token) => {
                let operand = parse_atomic_expr(p);
                children.push(parse_primary_expr(p, operand, true));
            }
            _ => return children,
        }
    }
}

// ============================================================================
// Template Literal Parsing
// ============================================================================

/// OCaml `parse_template_expr ?prefix` (res_core.ml).
fn parse_template_literal_with_prefix(
    p: &mut Parser<'_>,
    prefix: Option<(LidentIdx, Location)>,
) -> Expression {
    // OCaml `parse_parts`: capture `start_pos`, scan the next template token,
    // then take a tail, or a part followed by `parse_expr_block`; anything
    // else is an unexpected token and drops the parts.
    let mut parts: Vec<(Cow<'static, str>, LocIdx, Option<Expression>)> = vec![];
    let mut first = true;
    loop {
        let text_start_pos_idx = p.start_pos_idx();
        if !first || p.token == Token::Backtick {
            p.next_template_literal_token();
        }
        first = false;
        match &p.token {
            Token::TemplateTail { text, pos } => {
                let text = extend_cow_lifetime(text.clone());
                let pos = *pos;
                p.next();
                let text_end_idx = p.push_pos(pos);
                let text_loc = p.mk_loc_idx(text_start_pos_idx, text_end_idx);
                parts.push((text, text_loc, None));
                break;
            }
            Token::TemplatePart { text, pos } => {
                let text = extend_cow_lifetime(text.clone());
                let pos = *pos;
                p.next();
                let text_end_idx = p.push_pos(pos);
                let text_loc = p.mk_loc_idx(text_start_pos_idx, text_end_idx);
                let expr = parse_expr_block(p);
                parts.push((text, text_loc, Some(expr)));
            }
            _ => {
                p.err(DiagnosticCategory::unexpected(
                    p.token.clone().into_owned(),
                    p.breadcrumbs().to_vec(),
                ));
                parts.clear();
                break;
            }
        }
    }

    let template_loc = match (parts.first(), parts.last()) {
        (Some((_, first_loc, _)), Some((_, last_loc, _))) => {
            let start_idx = p.loc_start_idx(*first_loc);
            let end_idx = p.loc_end_idx(*last_loc);
            p.mk_loc_idx(start_idx, end_idx)
        }
        _ => p.none_loc(),
    };
    let mut sources: Vec<StringLoc> = Vec::with_capacity(parts.len());
    let mut source_texts: Vec<Cow<'static, str>> = Vec::with_capacity(parts.len());
    let mut values: Vec<Expression> = Vec::new();
    let only_part = parts.len() == 1 && parts[0].2.is_none();
    for (text, loc, value) in parts {
        let txt = p.arena_mut().intern_string(&text);
        sources.push(Located { txt, loc });
        source_texts.push(text);
        if let Some(value) = value {
            values.push(value);
        }
    }

    match prefix {
        Some((lid_idx, _)) if p.arena().is_lident(lid_idx, "json") => {
            if !only_part && !source_texts.is_empty() {
                let start = p.loc_start(template_loc);
                let end = p.loc_end(template_loc);
                p.err_at(
                    start,
                    end,
                    DiagnosticCategory::Message(
                        "`json` literals do not support interpolation".to_string(),
                    ),
                );
            }
            let source = source_texts.into_iter().next().unwrap_or(Cow::Borrowed(""));
            let loc = sources.first().map_or(LocIdx::none(), |s| s.loc);
            ast_helper::make_constant(Constant::Json(source), loc)
        }
        None => {
            for (text, source) in source_texts.iter().zip(sources.iter()) {
                if crate::string_literal::decode_js_template_escapes(text).is_none() {
                    let start = p.loc_start(source.loc);
                    let end = p.loc_end(source.loc);
                    let message = if crate::string_literal::is_valid_utf8(text) {
                        "Invalid string escape sequence"
                    } else {
                        "Invalid code point"
                    };
                    p.err_at(start, end, DiagnosticCategory::Message(message.to_string()));
                }
            }
            let values = values
                .into_iter()
                .map(|v| p.arena_mut().push_expr(v))
                .collect();
            Expression {
                pexp_desc: Box::new(ExpressionDesc::Pexp_template(Box::new(PexpTemplate {
                    source_segments: sources,
                    values,
                }))),
                pexp_loc: template_loc,
                pexp_attributes: Attributes::new(),
            }
        }
        Some((prefix_ident, prefix_loc)) => {
            let prefix_loc_idx = prefix_loc;
            let tag_expr = Expression {
                pexp_desc: Box::new(ExpressionDesc::Pexp_ident(with_loc(
                    prefix_ident,
                    prefix_loc_idx,
                ))),
                pexp_loc: prefix_loc_idx,
                pexp_attributes: Attributes::new(),
            };
            let tag = p.arena_mut().push_expr(tag_expr);
            let values = values
                .into_iter()
                .map(|v| p.arena_mut().push_expr(v))
                .collect();
            let start_idx = p.loc_start_idx(prefix_loc_idx);
            let loc = p.mk_loc_idx_to_prev_end(start_idx);
            Expression {
                pexp_desc: Box::new(ExpressionDesc::Pexp_tagged_template(Box::new(
                    PexpTaggedTemplate {
                        tag,
                        raw_sources: sources,
                        values,
                    },
                ))),
                pexp_loc: loc,
                pexp_attributes: Attributes::new(),
            }
        }
    }
}

/// Parse a template literal (untagged).
fn parse_template_literal(p: &mut Parser<'_>) -> Expression {
    parse_template_literal_with_prefix(p, None)
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    /// Parse source code into an expression with a timeout.
    fn parse_expr_with_timeout(source: &str) -> Expression {
        crate::parser::test_utils::parse_with_timeout(source, parse_expr)
    }

    /// Parse source code into a constant with a timeout.
    fn parse_constant_with_timeout(source: &str) -> Constant {
        crate::parser::test_utils::parse_with_timeout(source, parse_constant)
    }

    #[test]
    fn test_parse_constant_int() {
        let c = parse_constant_with_timeout("42");
        assert!(matches!(c, Constant::Integer(n, None) if n == "42"));
    }

    #[test]
    fn test_parse_constant_float() {
        let c = parse_constant_with_timeout("3.14");
        assert!(matches!(c, Constant::Float(n, None) if n == "3.14"));
    }

    #[test]
    fn test_parse_constant_string() {
        let c = parse_constant_with_timeout("\"hello\"");
        assert!(
            matches!(c, Constant::String(ref s) if s.source() == "hello" && s.semantic() == "hello")
        );
    }

    #[test]
    fn test_parse_expr_int() {
        let expr = parse_expr_with_timeout("42");
        assert!(matches!(
            &*expr.pexp_desc,
            ExpressionDesc::Pexp_constant(c) if matches!(&**c, Constant::Integer(..))
        ));
    }

    #[test]
    fn test_parse_expr_ident() {
        let expr = parse_expr_with_timeout("foo");
        assert!(matches!(*expr.pexp_desc, ExpressionDesc::Pexp_ident(_)));
    }

    #[test]
    fn test_parse_expr_unit() {
        let expr = parse_expr_with_timeout("()");
        assert!(matches!(
            *expr.pexp_desc,
            ExpressionDesc::Pexp_construct(..)
        ));
    }

    #[test]
    fn test_parse_expr_true() {
        let expr = parse_expr_with_timeout("true");
        assert!(matches!(
            *expr.pexp_desc,
            ExpressionDesc::Pexp_construct(..)
        ));
    }

    #[test]
    fn test_parse_array() {
        let expr = parse_expr_with_timeout("[1, 2, 3]");
        assert!(matches!(*expr.pexp_desc, ExpressionDesc::Pexp_array(_)));
    }

    #[test]
    fn test_is_send_sync() {
        fn assert_send_sync<T: Send + Sync>() {}
        assert_send_sync::<Constant>();
    }
}
