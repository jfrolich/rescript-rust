//! Type expression parsing for ReScript.
//!
//! This module contains the type expression parsing logic, converting tokens
//! into type AST nodes.

use std::borrow::Cow;
use std::collections::HashSet;

use super::ast::*;
use super::core::{ast_helper, recover, with_loc};
use super::diagnostics::DiagnosticCategory;
use super::grammar;
use super::grammar::Grammar;
use super::longident::Longident;
use super::state::{Parser, ParserMode};
use super::token::Token;
use crate::parse_arena::{CoreTypeIdx, LocIdx, Located, PosIdx, StrIdx};

fn extend_current_type_name_path(p: &Parser<'_>, field_name: &str) -> Option<Vec<String>> {
    p.current_type_name_path.as_ref().map(|path| {
        let mut extended = path.clone();
        extended.push(field_name.to_string());
        extended
    })
}

fn inline_type_name_exists(p: &Parser<'_>, name: &str) -> bool {
    p.inline_types_found.as_ref().is_some_and(|items| {
        items
            .iter()
            .any(|(existing, _, _, _)| p.arena().get_string(*existing) == name)
    })
}

fn inline_type_param_exists(p: &Parser<'_>, name: &str) -> bool {
    p.inline_types_params.iter().any(|(typ_idx, _)| {
        let typ = p.arena().get_core_type(*typ_idx);
        matches!(&*typ.ptyp_desc, CoreTypeDesc::Ptyp_var(existing) if existing.as_ref() == name)
    })
}

fn maybe_track_inline_type_param(p: &mut Parser<'_>, name: &str, loc: LocIdx) {
    if p.inline_types_collect_free_type_vars && !inline_type_param_exists(p, name) {
        // OCaml compiler/syntax/src/res_core.ml:49-56 appends free type
        // variables to the inline record context while parsing externals.
        let typ = CoreType {
            ptyp_desc: Box::new(CoreTypeDesc::Ptyp_var(Box::new(Cow::Owned(
                name.to_string(),
            )))),
            ptyp_loc: loc,
            ptyp_attributes: Attributes::new(),
        };
        let typ_idx = p.arena_mut().push_core_type(typ);
        p.inline_types_params.push((typ_idx, Variance::Invariant));
    }
}

fn make_inline_record_type_name(p: &Parser<'_>, base: &str) -> Option<Vec<String>> {
    let prefix = p.current_type_name_path.as_ref()?;
    let mut suffix = String::new();
    loop {
        let candidate = format!("{base}{suffix}");
        let mut path = prefix.clone();
        path.push(candidate);
        let full_name = path.join(".");
        if !inline_type_name_exists(p, &full_name) {
            return Some(path);
        }
        suffix.push('$');
    }
}

fn make_inline_record_return_type_name(p: &Parser<'_>) -> Option<Vec<String>> {
    // OCaml compiler/syntax/src/res_core.ml:74-82 uses `return.type` as the
    // synthesized inline-record path segment for arrow return records.
    make_inline_record_type_name(p, "return.type")
}

fn make_inline_record_argument_type_name(p: &Parser<'_>, index: usize) -> Option<Vec<String>> {
    // OCaml compiler/syntax/src/res_core.ml:79-82 uses `argN` for positional
    // inline-record argument types.
    make_inline_record_type_name(p, &format!("arg{index}"))
}

fn with_current_type_name_path<T, F>(p: &mut Parser<'_>, path: Option<Vec<String>>, f: F) -> T
where
    F: FnOnce(&mut Parser<'_>) -> T,
{
    if let Some(path) = path {
        let old_path = p.current_type_name_path.replace(path);
        let result = f(p);
        p.current_type_name_path = old_path;
        result
    } else {
        f(p)
    }
}

// ============================================================================
// Type Variable Substitution
// ============================================================================

/// Transform a type by converting Ptyp_constr with a single Lident that matches
/// one of the poly type variables into Ptyp_var.
/// This is needed for locally abstract types: `type a b c. list<a, b, c>` should
/// have `a`, `b`, `c` as Ptyp_var, not Ptyp_constr.
pub fn substitute_type_vars(
    arena: &mut crate::parse_arena::ParseArena,
    typ: CoreType,
    vars: &HashSet<String>,
) -> Result<CoreType, LocIdx> {
    let new_desc = match *typ.ptyp_desc {
        CoreTypeDesc::Ptyp_var(name) => {
            if vars.contains(name.as_ref().as_ref()) {
                return Err(typ.ptyp_loc);
            }
            CoreTypeDesc::Ptyp_var(name)
        }
        CoreTypeDesc::Ptyp_constr(inner) => {
            let (lid, args) = *inner;
            // Check if this is a simple Lident that matches a type variable
            if args.is_empty() {
                if let Longident::Lident(name_idx) = arena.get_longident(lid.txt) {
                    let name = arena.get_string(*name_idx);
                    if vars.contains(name) {
                        let source_idx = *name_idx;
                        let name = Cow::Owned(name.to_string());
                        arena.record_tyvar_source(typ.ptyp_loc, source_idx);
                        // Convert to Ptyp_var
                        return Ok(CoreType {
                            ptyp_desc: Box::new(CoreTypeDesc::Ptyp_var(Box::new(name))),
                            ptyp_loc: typ.ptyp_loc,
                            ptyp_attributes: typ.ptyp_attributes,
                        });
                    }
                }
            }
            // Recursively process type arguments
            let new_args: Vec<CoreTypeIdx> = args
                .into_iter()
                .map(|arg_idx| {
                    let arg_type = arena.get_core_type(arg_idx).clone();
                    substitute_type_vars(arena, arg_type, vars)
                        .map(|substituted| arena.push_core_type(substituted))
                })
                .collect::<Result<_, _>>()?;
            CoreTypeDesc::Ptyp_constr(Box::new((lid, new_args)))
        }
        CoreTypeDesc::Ptyp_arrow(inner) => {
            // `Ptyp_arrow {params; ret}`: the record's `ret` is evaluated
            // before `List.map` over the params (left to right).
            let (arg, ret, arity) = *inner;
            let params = arena.nary_arrow_args(&arg, arity).into_owned();
            let ret_type = arena.get_core_type(ret).clone();
            let substituted_ret = substitute_type_vars(arena, ret_type, vars)?;
            let new_ret = arena.push_core_type(substituted_ret);
            let mut new_params = Vec::with_capacity(params.len());
            for param in params {
                let param_type = arena.get_core_type(param.typ).clone();
                let substituted = substitute_type_vars(arena, param_type, vars)?;
                new_params.push(TypeArg {
                    typ: arena.push_core_type(substituted),
                    ..param
                });
            }
            let first = new_params[0].clone();
            arena.set_nary_arrow_args(arity, new_params);
            CoreTypeDesc::Ptyp_arrow(Box::new((Box::new(first), new_ret, arity)))
        }
        CoreTypeDesc::Ptyp_tuple(elements) => CoreTypeDesc::Ptyp_tuple(Box::new(
            (*elements)
                .into_iter()
                .map(|e_idx| {
                    let e_type = arena.get_core_type(e_idx).clone();
                    substitute_type_vars(arena, e_type, vars)
                        .map(|substituted| arena.push_core_type(substituted))
                })
                .collect::<Result<_, _>>()?,
        )),
        CoreTypeDesc::Ptyp_poly(inner) => {
            let (poly_vars, body_idx) = *inner;
            if poly_vars
                .iter()
                .any(|var| vars.contains(arena.get_string(var.txt)))
            {
                return Err(typ.ptyp_loc);
            }
            let body_type = arena.get_core_type(body_idx).clone();
            let substituted_body = substitute_type_vars(arena, body_type, vars)?;
            let new_body_idx = arena.push_core_type(substituted_body);
            CoreTypeDesc::Ptyp_poly(Box::new((poly_vars, new_body_idx)))
        }
        CoreTypeDesc::Ptyp_alias(inner) => {
            let (inner_idx, name) = *inner;
            if vars.contains(name.as_ref()) {
                return Err(typ.ptyp_loc);
            }
            let inner_type = arena.get_core_type(inner_idx).clone();
            let substituted_inner = substitute_type_vars(arena, inner_type, vars)?;
            CoreTypeDesc::Ptyp_alias(Box::new((arena.push_core_type(substituted_inner), name)))
        }
        CoreTypeDesc::Ptyp_object(inner) => {
            let (fields, closed) = *inner;
            let new_fields: Vec<ObjectField> = fields
                .into_iter()
                .map(|field| match field {
                    ObjectField::Otag(name, attrs, inner_typ_idx) => {
                        let inner_type = arena.get_core_type(inner_typ_idx).clone();
                        substitute_type_vars(arena, inner_type, vars).map(|substituted| {
                            ObjectField::Otag(name, attrs, arena.push_core_type(substituted))
                        })
                    }
                    ObjectField::Oinherit(inner_typ_idx) => {
                        let inner_type = arena.get_core_type(inner_typ_idx).clone();
                        substitute_type_vars(arena, inner_type, vars).map(|substituted| {
                            ObjectField::Oinherit(arena.push_core_type(substituted))
                        })
                    }
                })
                .collect::<Result<_, _>>()?;
            CoreTypeDesc::Ptyp_object(Box::new((new_fields, closed)))
        }
        CoreTypeDesc::Ptyp_variant(inner) => {
            let (rows, closed, labels) = *inner;
            let new_rows: Vec<RowField> = rows
                .into_iter()
                .map(|row| match row {
                    RowField::Rtag(name, attrs, empty, types) => {
                        let new_types: Vec<CoreTypeIdx> = types
                            .into_iter()
                            .map(|t_idx| {
                                let t_type = arena.get_core_type(t_idx).clone();
                                substitute_type_vars(arena, t_type, vars)
                                    .map(|substituted| arena.push_core_type(substituted))
                            })
                            .collect::<Result<_, _>>()?;
                        Ok(RowField::Rtag(name, attrs, empty, new_types))
                    }
                    RowField::Rinherit(inner_typ_idx) => {
                        let inner_type = arena.get_core_type(inner_typ_idx).clone();
                        substitute_type_vars(arena, inner_type, vars).map(|substituted| {
                            RowField::Rinherit(arena.push_core_type(substituted))
                        })
                    }
                })
                .collect::<Result<_, _>>()?;
            CoreTypeDesc::Ptyp_variant(Box::new((new_rows, closed, labels)))
        }
        CoreTypeDesc::Ptyp_package(pkg_inner) => {
            let (lid, constraints) = *pkg_inner;
            let new_constraints: Vec<_> = constraints
                .into_iter()
                .map(|(c_lid, c_typ_idx)| {
                    let c_type = arena.get_core_type(c_typ_idx).clone();
                    substitute_type_vars(arena, c_type, vars)
                        .map(|substituted| (c_lid, arena.push_core_type(substituted)))
                })
                .collect::<Result<_, _>>()?;
            CoreTypeDesc::Ptyp_package(Box::new((lid, new_constraints)))
        }
        // These don't contain nested types, return as-is
        other => other,
    };
    Ok(CoreType {
        ptyp_desc: Box::new(new_desc),
        ptyp_loc: typ.ptyp_loc,
        ptyp_attributes: typ.ptyp_attributes,
    })
}

// ============================================================================
// Main Type Parsing
// ============================================================================

/// Parse a type expression.
pub fn parse_typ_expr(p: &mut Parser<'_>) -> CoreType {
    let typ = parse_typ_expr_inner(p, true);
    parse_type_alias(p, typ)
}

/// Run `f` as an OCaml `parse_typ_expr p` call without `?current_type_name_path`
/// / `?inline_types_context`: no inline record context applies inside.
fn without_inline_types_context<T>(p: &mut Parser<'_>, f: impl FnOnce(&mut Parser<'_>) -> T) -> T {
    let old_path = p.current_type_name_path.take();
    let old_found = p.inline_types_found.take();
    let result = f(p);
    p.current_type_name_path = old_path;
    p.inline_types_found = old_found;
    result
}

/// Parse a polymorphic type expression.
/// Like parse_typ_expr but with special handling for `'a => T` patterns.
/// OCaml's parse_poly_type_expr has a special case where single type vars
/// followed by `=>` use the type var's location for the arrow, not start_pos.
/// This is used for record field types where `'a => T` should NOT include
/// the `'` in the arrow type's location.
pub fn parse_poly_type_expr(p: &mut Parser<'_>) -> CoreType {
    if p.token == Token::SingleQuote {
        let start_pos_idx = p.start_pos_idx();
        let vars = parse_type_var_list(p);
        match vars.as_slice() {
            [_, _, ..] => {
                p.expect(Token::Dot);
                let body = without_inline_types_context(p, parse_typ_expr);
                let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
                let body_idx = p.arena_mut().push_core_type(body);
                return CoreType {
                    ptyp_desc: Box::new(CoreTypeDesc::Ptyp_poly(Box::new((vars, body_idx)))),
                    ptyp_loc: loc,
                    ptyp_attributes: Attributes::new(),
                };
            }
            [var] => match p.token {
                Token::Dot => {
                    p.next();
                    let body = without_inline_types_context(p, parse_typ_expr);
                    let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
                    let body_idx = p.arena_mut().push_core_type(body);
                    return CoreType {
                        ptyp_desc: Box::new(CoreTypeDesc::Ptyp_poly(Box::new((vars, body_idx)))),
                        ptyp_loc: loc,
                        ptyp_attributes: Attributes::new(),
                    };
                }
                Token::EqualGreater => {
                    p.next();
                    let name = p.arena().get_string(var.txt).to_string();
                    let typ = CoreType {
                        ptyp_desc: Box::new(CoreTypeDesc::Ptyp_var(Box::new(Cow::Owned(name)))),
                        ptyp_loc: var.loc,
                        ptyp_attributes: Attributes::new(),
                    };
                    let return_type = without_inline_types_context(p, |p| parse_typ_expr_inner(p, true));
                    let typ_start_idx = p.loc_start_idx(typ.ptyp_loc);
                    let end_pos_idx = p.prev_end_pos_idx();
                    let loc = p.mk_loc_idx(typ_start_idx, end_pos_idx);
                    let typ_idx = p.arena_mut().push_core_type(typ);
                    let arg = TypeArg {
                        attrs: Attributes::new(),
                        lbl: ArgLabel::Nolabel,
                        typ: typ_idx,
                    };
                    let ret_idx = p.arena_mut().push_core_type(return_type);
                    return CoreType {
                        ptyp_desc: Box::new(CoreTypeDesc::Ptyp_arrow(Box::new((
                            Box::new(arg),
                            ret_idx,
                            p.static_arity_1(),
                        )))),
                        ptyp_loc: loc,
                        ptyp_attributes: Attributes::new(),
                    };
                }
                _ => {
                    let name = p.arena().get_string(var.txt).to_string();
                    return CoreType {
                        ptyp_desc: Box::new(CoreTypeDesc::Ptyp_var(Box::new(Cow::Owned(name)))),
                        ptyp_loc: var.loc,
                        ptyp_attributes: Attributes::new(),
                    };
                }
            },
            [] => unreachable!("parse_type_var_list always consumes at least one quote here"),
        }
    }

    // Fall through to regular type expression parsing
    let typ = parse_typ_expr_inner(p, true);
    parse_type_alias(p, typ)
}

fn parse_type_var_list(p: &mut Parser<'_>) -> Vec<StringLoc> {
    let mut vars = Vec::new();
    while p.token == Token::SingleQuote {
        p.next();
        let var_start_idx = p.start_pos_idx();
        let (name, loc) = if p.token == Token::Eof {
            p.err_at(
                p.start_pos,
                p.prev_end_pos,
                DiagnosticCategory::Unexpected {
                    token: p.token.clone().into_owned(),
                    context: vec![],
                },
            );
            (String::new(), p.mk_loc_idx_to_prev_end(var_start_idx))
        } else {
            super::core::parse_ident(p, super::core::error_messages::TYPE_PARAM, var_start_idx)
        };
        let name_idx = p.arena_mut().push_interned_string(&name);
        vars.push(with_loc(name_idx, loc));
    }
    vars
}

/// Parse a locally abstract type: `type a b c. SomeType`
/// This is called from let-binding sites when `Token::Typ` is encountered after `:`.
/// Returns a `Ptyp_poly(Box::new((vars, body)))` where body has `Ptyp_constr` for the type vars
/// (the caller is responsible for substituting to `Ptyp_var`).
pub fn parse_locally_abstract_type(p: &mut Parser<'_>) -> CoreType {
    let start_pos = p.start_pos.clone();
    p.expect(Token::Typ);
    let mut vars: Vec<StringLoc> = vec![];

    // Collect all type variable names until we see a dot
    while let Token::Lident(_) = &p.token {
        let name = if let Token::Lident(n) = &p.token {
            n.clone()
        } else {
            unreachable!()
        };
        let var_start_idx = p.start_pos_idx();
        p.next();
        let var_loc = p.mk_loc_idx_to_prev_end(var_start_idx);
        let name_idx = p.arena_mut().push_interned_string(&name);
        vars.push(with_loc(name_idx, var_loc));
    }

    p.expect(Token::Dot);
    let body = parse_typ_expr(p);
    let loc = p.mk_loc_to_end_of(&start_pos, body.ptyp_loc);
    let body_idx = p.arena_mut().push_core_type(body);
    CoreType {
        ptyp_desc: Box::new(CoreTypeDesc::Ptyp_poly(Box::new((vars, body_idx)))),
        ptyp_loc: loc,
        ptyp_attributes: Attributes::new(),
    }
}

/// Parse a type expression without allowing arrow types at the top level.
/// Used for return type annotations like `(x): int => body`.
pub fn parse_typ_expr_no_arrow(p: &mut Parser<'_>) -> CoreType {
    let typ = parse_typ_expr_inner(p, false);
    parse_type_alias(p, typ)
}

/// Parse a type expression with pre-parsed attributes.
fn parse_typ_expr_with_attrs(p: &mut Parser<'_>, attrs: Attributes) -> CoreType {
    let start_pos_idx = p.start_pos_idx();
    let mut typ = parse_atomic_typ_expr(p, attrs);
    // Match OCaml: handle both EqualGreater and MinusGreater (error recovery)
    if matches!(p.token, Token::EqualGreater | Token::MinusGreater) {
        typ = parse_arrow_type_rest(p, typ, start_pos_idx);
    }
    parse_type_alias(p, typ)
}

pub(super) fn parse_type_alias(p: &mut Parser<'_>, typ: CoreType) -> CoreType {
    // Handle type aliases (type as 'name)
    if p.token == Token::As {
        p.next();
        p.expect(Token::SingleQuote);
        let var_name: Cow<'static, str> = match &p.token {
            Token::Lident(name) | Token::Uident(name) => {
                let name = extend_cow_lifetime(name.clone());
                p.next();
                name
            }
            _ => {
                p.err(DiagnosticCategory::Message(
                    "Expected type variable after 'as'".to_string(),
                ));
                Cow::Borrowed("a")
            }
        };
        let typ_start_idx = p.loc_start_idx(typ.ptyp_loc);
        let end_pos_idx = p.prev_end_pos_idx();
        let loc = p.mk_loc_idx(typ_start_idx, end_pos_idx);
        let typ_idx = p.arena_mut().push_core_type(typ);
        return CoreType {
            ptyp_desc: Box::new(CoreTypeDesc::Ptyp_alias(Box::new((typ_idx, var_name)))),
            ptyp_loc: loc,
            ptyp_attributes: Attributes::new(),
        };
    }

    typ
}

/// Parse a type expression with optional ES6 arrow support.
fn parse_typ_expr_inner(p: &mut Parser<'_>, es6_arrow: bool) -> CoreType {
    parse_typ_expr_inner_with_start(p, es6_arrow, None)
}

/// Parse a type expression with optional ES6 arrow support.
/// `outer_start_pos_idx` is an optional PosIdx from the caller that can be reused for
/// position sharing. When provided, it's used instead of pushing a new start position.
fn parse_typ_expr_inner_with_start(
    p: &mut Parser<'_>,
    es6_arrow: bool,
    outer_start_pos_idx: Option<crate::parse_arena::PosIdx>,
) -> CoreType {
    // Use the outer start position if provided, otherwise use the stored index.
    // In OCaml, `let start_pos = p.Parser.start_pos` binds to the SAME pointer
    // that p.start_pos currently holds. If p.start_pos hasn't changed (no p.next()
    // between captures), multiple functions share the SAME heap object.
    // Using start_pos_idx() matches this — it returns the stored index.
    let start_pos_idx = outer_start_pos_idx.unwrap_or_else(|| p.start_pos_idx());
    let attrs = parse_type_attributes(p);

    if es6_arrow && super::core::is_es6_arrow_type(p) {
        parse_es6_arrow_type(p, attrs)
    } else {
        // Don't pass our start_pos_idx to parse_atomic_typ_expr_with_start.
        // In OCaml, parseTypExpr and parseAtomicTypExpr each independently capture
        // `let start_pos = p.start_pos`, creating different heap objects even though
        // they point to the same position. With identity-based PosIdx, each function
        // must push its own fresh position to avoid incorrect sharing.
        let typ = parse_atomic_typ_expr_with_start(p, attrs.clone(), None);
        // Match OCaml: handle both EqualGreater and MinusGreater (error recovery)
        // When MinusGreater is found where EqualGreater is expected, generate error and continue
        if es6_arrow && matches!(p.token, Token::EqualGreater | Token::MinusGreater) {
            parse_arrow_type_rest(p, typ, start_pos_idx)
        } else {
            typ
        }
    }
}

/// Parse the rest of an arrow type.
/// `start_pos_idx` is the PosIdx before parsing the first argument, for position sharing.
/// OCaml's parse_arrow_type_rest uses start_pos (before the argument) for location.
pub(super) fn parse_arrow_type_rest(
    p: &mut Parser<'_>,
    param_type: CoreType,
    start_pos_idx: crate::parse_arena::PosIdx,
) -> CoreType {
    // OCaml matches `(EqualGreater | MinusGreater) when es6_arrow` and
    // otherwise returns the type unchanged (res_core.ml:5057-5074).
    if !matches!(p.token, Token::EqualGreater | Token::MinusGreater) {
        return param_type;
    }
    // Error recovery: if user wrote -> instead of =>, report error but continue
    // This matches OCaml's: if token = MinusGreater then Parser.expect EqualGreater p;
    if p.token == Token::MinusGreater {
        p.expect(Token::EqualGreater); // generates "Did you forget a `=>` here?"
    }
    p.next(); // consume => or ->
    // Parse return type without alias - `as` binds looser than `=>`
    // So `int => unit as 'a` is `(int => unit) as 'a`, not `int => (unit as 'a)`
    let return_path = make_inline_record_return_type_name(p);
    let return_type =
        with_current_type_name_path(p, return_path, |p| parse_typ_expr_inner(p, true));
    // OCaml's parse_arrow_type_rest uses start_pos (before the argument),
    // NOT param_type.ptyp_loc.loc_start. This is different from the special case
    // in parse_poly_type_expr which uses typ.ptyp_loc.loc_start.
    // Use mk_loc_idx_to_prev_end to reuse the start_pos_idx for position sharing.
    let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);

    let param_type_idx = p.arena_mut().push_core_type(param_type);
    let arg = TypeArg {
        attrs: Attributes::new(),
        lbl: ArgLabel::Nolabel,
        typ: param_type_idx,
    };

    // LITERAL path: OCaml line 4822 `Typ.arrow ~arity:(Some 1)`
    // Use static arity to match OCaml's CSE sharing behavior
    let ret_idx = p.arena_mut().push_core_type(return_type);
    CoreType {
        ptyp_desc: Box::new(CoreTypeDesc::Ptyp_arrow(Box::new((
            Box::new(arg),
            ret_idx,
            p.static_arity_1(),
        )))),
        ptyp_loc: loc,
        ptyp_attributes: Attributes::new(),
    }
}

fn without_inline_record_context<T, F>(p: &mut Parser<'_>, f: F) -> T
where
    F: FnOnce(&mut Parser<'_>) -> T,
{
    let old_path = p.current_type_name_path.take();
    let old_found = p.inline_types_found.take();
    let old_params = std::mem::take(&mut p.inline_types_params);
    let old_collect = p.inline_types_collect_free_type_vars;
    p.inline_types_collect_free_type_vars = false;

    let result = f(p);

    p.current_type_name_path = old_path;
    p.inline_types_found = old_found;
    p.inline_types_params = old_params;
    p.inline_types_collect_free_type_vars = old_collect;
    result
}

fn is_external_bare_arrow_type(p: &mut Parser<'_>) -> bool {
    // OCaml compiler/syntax/src/res_core.ml:5126-5135 speculatively parses
    // one atomic type to detect externals like `external f: int => t = "f"`.
    p.lookahead(|state| {
        let attrs = parse_attributes(state);
        match state.token {
            Token::Lparen | Token::Tilde | Token::DocComment { .. } => false,
            _ => {
                // OCaml's lookahead calls `parse_atomic_typ_expr ~attrs state`
                // without an inline-types context.
                let _ = without_inline_record_context(state, |state| {
                    parse_atomic_typ_expr(state, attrs)
                });
                matches!(state.token, Token::EqualGreater | Token::MinusGreater)
            }
        }
    })
}

pub fn parse_external_type_expr(p: &mut Parser<'_>) -> CoreType {
    // OCaml compiler/syntax/src/res_core.ml:5137-5155 only passes the inline
    // record context to arrow externals. Non-arrow externals such as
    // `@val external x: {a: int} = "x"` stay ordinary record/object types.
    if is_external_bare_arrow_type(p) {
        let start_pos_idx = p.start_pos_idx();
        let attrs = parse_attributes(p);
        let arg_path = make_inline_record_argument_type_name(p, 0);
        let typ = with_current_type_name_path(p, arg_path, |p| parse_atomic_typ_expr(p, attrs));
        let typ = parse_arrow_type_rest(p, typ, start_pos_idx);
        parse_type_alias(p, typ)
    } else if super::core::is_es6_arrow_type(p) {
        parse_typ_expr(p)
    } else {
        without_inline_record_context(p, parse_typ_expr)
    }
}

/// Parse an ES6 arrow type starting at either `~` or a parenthesized parameter list.
fn parse_es6_arrow_type(p: &mut Parser<'_>, attrs: Attributes) -> CoreType {
    // OCaml line 4711: `let start_pos = p.Parser.start_pos in` — binds to
    // the same pointer as p.start_pos. Use stored index for sharing.
    let start_pos_idx = p.start_pos_idx();

    if p.token == Token::Tilde {
        p.next();
        let (name, name_loc) = parse_lident(p);
        // Pass grammar context for error message: "Did you forget a `:` here? It signals the start of a type"
        p.expect_with_grammar(Token::Colon, Some(Grammar::TypeExpression));

        // OCaml compiler/syntax/src/res_core.ml:4973-5004 extends
        // inline-record context through labeled arrow args and `return.type`.
        let arg_path = extend_current_type_name_path(p, &name);
        let typ = with_current_type_name_path(p, arg_path, |p| parse_typ_expr_inner(p, false));
        let name_idx = p.arena_mut().push_interned_string(&name);
        let mut lbl = ArgLabel::Labelled(Located::new(name_idx, name_loc));

        // Optional labeled args: `~x: t=?` (res_core.ml:4960-4963).
        if p.token == Token::Equal {
            p.next();
            p.expect(Token::Question);
            if let ArgLabel::Labelled(name) = lbl {
                lbl = ArgLabel::Optional(name);
            }
        }

        p.expect(Token::EqualGreater);
        // Parse return type without alias - `as` binds looser than `=>`
        let return_path = make_inline_record_return_type_name(p);
        let return_type =
            with_current_type_name_path(p, return_path, |p| parse_typ_expr_inner(p, true));

        // OCaml uses prev_end_pos (actual end after parsing return type), not return_type's ptyp_loc.loc_end
        let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
        let typ_idx = p.arena_mut().push_core_type(typ);
        let arg = TypeArg {
            attrs,
            lbl,
            typ: typ_idx,
        };

        let ret_idx = p.arena_mut().push_core_type(return_type);
        // A bare labeled arrow is the same complete one-parameter arrow as
        // its parenthesized spelling (res_core.ml:4973-4980).
        let full_arity = p.push_arity_full(1);
        p.arena_mut()
            .set_nary_arrow_args(full_arity, vec![arg.clone()]);
        CoreType {
            ptyp_desc: Box::new(CoreTypeDesc::Ptyp_arrow(Box::new((
                Box::new(arg),
                ret_idx,
                full_arity,
            )))),
            ptyp_loc: loc,
            ptyp_attributes: Attributes::new(),
        }
    } else {
        p.expect(Token::Lparen);
        let mut typ = parse_function_type(p, start_pos_idx);
        if !attrs.is_empty() {
            typ.ptyp_attributes.extend(attrs);
        }
        typ
    }
}

// ============================================================================
// Atomic Type Parsing
// ============================================================================

/// Parse attributes that can appear before a type (including doc comments).
fn parse_type_attributes(p: &mut Parser<'_>) -> Attributes {
    parse_attributes(p)
}

/// Parse an attribute payload (in type context).
fn parse_payload(p: &mut Parser<'_>) -> Payload {
    p.expect(Token::Lparen);
    let payload = super::module::parse_payload(p);
    p.expect(Token::Rparen);
    payload
}

/// Parse an atomic type expression.
/// `outer_start_pos_idx` is an optional PosIdx from the caller that can be reused
/// for position sharing with simple type constructors.
fn parse_atomic_typ_expr_with_start(
    p: &mut Parser<'_>,
    attrs: Attributes,
    outer_start_pos_idx: Option<crate::parse_arena::PosIdx>,
) -> CoreType {
    p.leave_breadcrumb(Grammar::AtomicTypExpr);
    // Use outer start if provided, otherwise use stored index.
    // In OCaml, `let start_pos = p.Parser.start_pos` binds to the same pointer.
    // Use start_pos_idx() for sharing when no attributes have been parsed.
    let start_pos_idx = outer_start_pos_idx.unwrap_or_else(|| p.start_pos_idx());

    let mut typ = match &p.token {
        Token::SingleQuote => {
            // Type variable: 'a
            p.next();
            let var_start_idx = p.start_pos_idx();
            let (name, var_loc) = if p.token == Token::Eof {
                p.err(DiagnosticCategory::Unexpected {
                    token: p.token.clone().into_owned(),
                    context: vec![],
                });
                (String::new(), p.mk_loc_idx_to_prev_end(var_start_idx))
            } else {
                super::core::parse_ident(p, super::core::error_messages::TYPE_VAR, var_start_idx)
            };
            maybe_track_inline_type_param(p, &name, var_loc);
            CoreType {
                ptyp_desc: Box::new(CoreTypeDesc::Ptyp_var(Box::new(Cow::Owned(name)))),
                ptyp_loc: var_loc,
                ptyp_attributes: Attributes::new(),
            }
        }
        Token::Underscore => {
            // Any type: _
            p.next();
            let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
            CoreType {
                ptyp_desc: Box::new(CoreTypeDesc::Ptyp_any),
                ptyp_loc: loc,
                ptyp_attributes: Attributes::new(),
            }
        }
        // In OCaml, parse_value_path captures `let start_pos = p.Parser.start_pos` (line 714).
        // Since p.start_pos hasn't changed, this is the SAME pointer as parse_atomic_typ_expr's
        // start_pos. Pass outer_start_pos_idx to share the same PosIdx.
        Token::Lident(_) | Token::Uident(_) => parse_type_constr_with_start(p, outer_start_pos_idx),
        Token::Lparen => {
            p.next();
            // OCaml `parse_atomic_typ_expr` (res_core.ml:4608-4627): `()`, a
            // parenthesized type, or a tuple. Function types are recognized
            // earlier by `is_es6_arrow_type` in `parse_typ_expr`.
            if p.token == Token::Rparen {
                // Unit type: ()
                // OCaml: Ast_helper.Typ.constr ~attrs unit_constr []
                // No ~loc passed, so ptyp_loc defaults to Location.none (ghost)
                // But lid_loc uses the real location
                p.next();
                let lid_loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
                let lid_idx = p.push_lident_static("unit");
                ast_helper::make_type_constr(lid_idx, vec![], lid_loc, LocIdx::none())
            } else {
                // Parenthesized type or tuple
                let typ = parse_typ_expr(p);
                if p.token == Token::Comma {
                    // Tuple type
                    parse_tuple_type(p, start_pos_idx, typ)
                } else {
                    p.expect(Token::Rparen);
                    // OCaml includes the surrounding parentheses in the type's location.
                    // When outer_start_pos_idx is provided (from parse_typ_expr_inner_with_start),
                    // use it for the parenthesized type's location start to enable position sharing
                    // with the outer arrow type (both use the same start_pos variable in OCaml).
                    let loc = match outer_start_pos_idx {
                        Some(idx) => p.mk_loc_idx_to_prev_end(idx),
                        None => p.mk_loc_idx_to_prev_end(start_pos_idx),
                    };
                    CoreType {
                        ptyp_loc: loc,
                        ..typ
                    }
                }
            }
        }
        Token::Lbrace => parse_record_or_object_type(p),
        Token::Lbracket => parse_poly_variant_type(p),
        Token::Module => {
            p.next();
            parse_package_type_with_parens(p, start_pos_idx)
        }
        Token::Percent => {
            // Extension: %ext
            let ext = parse_extension(p);
            let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
            CoreType {
                ptyp_desc: Box::new(CoreTypeDesc::Ptyp_extension(Box::new(ext))),
                ptyp_loc: loc,
                ptyp_attributes: Attributes::new(),
            }
        }
        Token::Eof => {
            p.err_unexpected();
            recover::default_type(p.arena_mut())
        }
        _ => {
            let token = p.token.clone().into_owned();
            p.err_unexpected();
            // Try to skip tokens and retry parsing if we find a valid start token
            // This matches OCaml's skip_tokens_and_maybe_retry behavior
            if recover::skip_tokens_and_maybe_retry(p, grammar::is_atomic_typ_expr_start) {
                // Eat our breadcrumb first, then recurse
                // OCaml returns from match, then eat_breadcrumb runs
                p.eat_breadcrumb();
                // The retry is `parse_atomic_typ_expr ~attrs p` (res_core.ml:4680):
                // no inline-record context.
                return without_inline_record_context(p, |p| parse_atomic_typ_expr(p, attrs));
            }
            // res_core.ml:4679-4683: report the token again from the
            // previous token's end before falling back to a default type.
            let context = p.breadcrumbs().to_vec();
            p.err_at(
                p.prev_end_pos,
                p.end_pos,
                DiagnosticCategory::Unexpected { token, context },
            );
            recover::default_type(p.arena_mut())
        }
    };

    // Attach any leading attributes to the type
    if !attrs.is_empty() {
        typ.ptyp_attributes.extend(attrs);
    }

    p.eat_breadcrumb();
    typ
}

/// Parse an atomic type expression (wrapper without outer start position).
pub(crate) fn parse_atomic_typ_expr(p: &mut Parser<'_>, attrs: Attributes) -> CoreType {
    parse_atomic_typ_expr_with_start(p, attrs, None)
}

// ============================================================================
// Type Constructor
// ============================================================================

/// Parse a type constructor (path with optional type arguments).
/// `outer_start_pos_idx` is an optional PosIdx from the caller that can be reused
/// for position sharing (e.g., when the caller has already pushed a start position
/// at the same coordinate).
fn parse_type_constr_with_start(
    p: &mut Parser<'_>,
    outer_start_pos_idx: Option<crate::parse_arena::PosIdx>,
) -> CoreType {
    // Use the outer start position if provided, otherwise use stored index.
    // In OCaml, `let start_pos = p.Parser.start_pos` binds to same pointer.
    let start_pos_idx = outer_start_pos_idx.unwrap_or_else(|| p.start_pos_idx());

    // OCaml `parse_atomic_typ_expr` reads the constructor with `parse_value_path`
    // (compiler/syntax/src/res_core.ml:742-776): a lowercase name ends the path
    // immediately; an uppercase head goes through `aux` + `next_unsafe`.
    let path_parts: Vec<String> = match &p.token {
        Token::Lident(name) => {
            let name = name.to_string();
            p.next();
            vec![name]
        }
        _ => super::module::parse_value_path_for_type(p).0,
    };

    let lid = super::core::build_longident(p.arena_mut(), &path_parts);
    let lid_idx = p.push_longident(lid);

    // Capture end position for identifier - use caching so it can be shared
    // with ptyp_loc when there are no type arguments
    let lid_end_idx = p.prev_end_pos_idx();
    let lid_loc = p.mk_loc_idx(start_pos_idx, lid_end_idx);

    // Parse optional type arguments
    // OCaml: parse_type_constructor_args handles both < and ( as opening tokens
    let args = if p.token == Token::LessThan || p.token == Token::Lparen {
        let opening = p.token.clone();
        let opening_start_pos = p.start_pos.clone();
        p.set_diamond_mode();
        p.next();
        let args = parse_type_args(p);
        if p.token == Token::Rparen && opening == Token::Lparen {
            // User wrote parens instead of angle brackets - emit helpful error
            let path_str = path_parts.join(".");
            let args_str: Vec<String> = args
                .iter()
                .map(|t| match &*t.ptyp_desc {
                    CoreTypeDesc::Ptyp_var(v) => format!("'{}", v),
                    _ => "_".to_string(),
                })
                .collect();
            let type_str = if args_str.is_empty() {
                path_str
            } else {
                format!("{}<{}>", path_str, args_str.join(", "))
            };
            let msg = format!("Type parameters require angle brackets:\n  {}", type_str);
            p.err_at(
                opening_start_pos,
                p.end_pos.clone(),
                DiagnosticCategory::message(&msg),
            );
            p.next(); // consume )
        } else {
            p.expect(Token::GreaterThan);
        }
        p.pop_diamond_mode();
        args
    } else {
        vec![]
    };

    // Check for multiple inline records in type constructor args (OCaml line 4462)
    if let Some(ref inline_types) = p.inline_types_found {
        // Collect inline type names first to avoid borrow conflict
        let inline_names: Vec<StrIdx> = inline_types.iter().map(|(n, _, _, _)| *n).collect();
        let count = args
            .iter()
            .filter(|arg| {
                if let CoreTypeDesc::Ptyp_constr(constr_inner) = &*arg.ptyp_desc {
                    let (ref lid, _) = **constr_inner;
                    inline_names
                        .iter()
                        .any(|iname| p.arena().is_lident(lid.txt, p.arena().get_string(*iname)))
                } else {
                    false
                }
            })
            .count();
        if count > 1 {
            p.err_at(
                p.arena().get_position(start_pos_idx).clone(),
                p.prev_end_pos.clone(),
                DiagnosticCategory::Message(
                    "Only one inline record definition is allowed per record field. This defines more than one inline record.".to_string(),
                ),
            );
        }
    }

    // ptyp_loc includes the full extent (identifier + type args)
    // Note: For Ldot types in certain contexts (type manifests, arrow parameters),
    // the location is adjusted later to exclude type args.
    // Reuse start_pos_idx for position sharing. End position uses caching -
    // when there are no type args, it shares the same end as lid_loc.
    let ptyp_end_idx = p.prev_end_pos_idx();
    let ptyp_loc = p.mk_loc_idx(start_pos_idx, ptyp_end_idx);
    let args_idx: Vec<CoreTypeIdx> = args
        .into_iter()
        .map(|a| p.arena_mut().push_core_type(a))
        .collect();
    ast_helper::make_type_constr(lid_idx, args_idx, lid_loc, ptyp_loc)
}

/// Parse a type constructor (path with optional type arguments).
fn parse_type_constr(p: &mut Parser<'_>) -> CoreType {
    parse_type_constr_with_start(p, None)
}

/// Parse type arguments.
/// Parse a single type constructor argument, matching OCaml's parse_type_constructor_arg_region.
/// Handles the special case where `<` tokens are silently skipped (e.g., `option(<node<int>>)`).
fn parse_type_constructor_arg_region(p: &mut Parser<'_>) -> Option<CoreType> {
    if super::grammar::is_typ_expr_start(&p.token) {
        Some(parse_typ_expr(p))
    } else if p.token == Token::LessThan {
        // OCaml: skip the < and retry
        p.next();
        parse_type_constructor_arg_region(p)
    } else {
        None
    }
}

fn parse_type_args(p: &mut Parser<'_>) -> Vec<CoreType> {
    // OCaml: parse_comma_delimited_region ~grammar:TypExprList ~closing:GreaterThan
    //        ~f:parse_type_constructor_arg_region
    let mut args = vec![];

    p.leave_breadcrumb(Grammar::TypExprList);
    loop {
        match parse_type_constructor_arg_region(p) {
            Some(typ) => {
                if p.token == Token::Comma {
                    p.next();
                    args.push(typ);
                } else if p.token == Token::GreaterThan || p.token == Token::Eof {
                    args.push(typ);
                    break;
                } else if super::grammar::is_typ_expr_start(&p.token) || p.token == Token::LessThan
                {
                    // Missing comma - report and continue
                    p.expect(Token::Comma);
                    args.push(typ);
                } else {
                    args.push(typ);
                    if !(p.token == Token::Eof
                        || p.token == Token::GreaterThan
                        || super::core::recover::should_abort_list_parse(p))
                    {
                        p.expect(Token::Comma);
                    }
                    if p.token == Token::Semicolon {
                        p.next();
                    }
                }
            }
            None => {
                if p.token == Token::Eof
                    || p.token == Token::GreaterThan
                    || super::core::recover::should_abort_list_parse(p)
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
        }
    }
    p.eat_breadcrumb();

    args
}

// ============================================================================
// Function Type
// ============================================================================

/// Parse a function type with labeled arguments.
fn parse_function_type(p: &mut Parser<'_>, start_pos_idx: PosIdx) -> CoreType {
    // Capture position before the first uncurried marker - OCaml includes . in argument type location
    // Use identity-based position (push_start_pos) to match OCaml's behavior where
    // nested function captures create different heap objects even at the same coordinate.
    let first_uncurried_start_idx = p.start_pos_idx();
    // Skip deprecated uncurried marker.
    let first_has_dot = if p.token == Token::Dot {
        p.warn_uncurried_dot_syntax();
        p.next();
        true
    } else {
        false
    };

    // `parse_type_parameters` builds the `unit` parameter only for `()`
    // (res_core.ml:4915-4921).
    let immediate_rparen = !first_has_dot && p.token == Token::Rparen;
    // Track both the TypeArg and its start position as PosIdx (for arrow location sharing)
    let mut params: Vec<(TypeArg, crate::parse_arena::PosIdx)> = vec![];
    let mut is_first_param = true;
    let mut positional_index = 0usize;
    // OCaml `parse_type_parameter` consumes a leading `.` and then requires a
    // parameter, so `(.)` is not an empty parameter list.
    let mut force_first_param = first_has_dot;

    while force_first_param || (p.token != Token::Rparen && p.token != Token::Eof) {
        force_first_param = false;
        // Capture position before the uncurried marker - OCaml includes . in argument type location
        // Use identity-based position tracking to match OCaml's behavior.
        let uncurried_start_idx = if is_first_param {
            first_uncurried_start_idx
        } else {
            p.start_pos_idx()
        };
        // Allow dotted parameters for uncurried segments (ignored for now).
        let has_dot = if is_first_param {
            is_first_param = false;
            first_has_dot
        } else if p.token == Token::Dot {
            p.warn_uncurried_dot_syntax();
            p.next();
            true
        } else {
            false
        };
        // OCaml handles doc comments separately from regular attributes for location purposes.
        // In OCaml parse_type_parameter:
        // 1. DocComment is consumed first (doc_attr)
        // 2. start_pos is captured AFTER doc comment
        // 3. Regular @-attributes are parsed after start_pos
        //
        // So doc comments should NOT be included in arrow location, but @-attrs SHOULD be.
        let mut doc_attrs = vec![];
        while let Token::DocComment { loc, content } = &p.token {
            let loc = loc.clone();
            let content = content.clone();
            p.next();
            let loc = p.from_location(&loc);
            doc_attrs.push(super::core::doc_comment_to_attribute(
                p.arena_mut(),
                loc,
                content,
            ));
        }

        // OCaml `parse_type_parameter` returns `None` unless the token can
        // start a parameter (`Tilde | Dot | is_typ_expr_start`,
        // res_core.ml:4827-4831); `parse_comma_delimited_region` then stops at
        // `)`/EOF/abort or reports the token and skips it
        // (res_core.ml:1068-1105).
        if !has_dot
            && p.token != Token::Tilde
            && !super::grammar::is_typ_expr_start(&p.token)
        {
            if p.token == Token::Eof
                || p.token == Token::Rparen
                || super::core::recover::should_abort_list_parse(p)
            {
                break;
            }
            p.err_unexpected();
            p.next();
            continue;
        }

        // Now capture the start position for the arrow - AFTER doc comments but BEFORE @-attrs
        // This matches OCaml: let start_pos = p.Parser.start_pos in
        // Use identity-based position to match OCaml's heap object creation behavior.
        let post_doc_start_idx = p.start_pos_idx();

        // Parse regular @-style attributes
        let regular_attrs = parse_regular_attributes(p);

        // Combine: doc_attrs @ regular_attrs (OCaml: doc_attr @ parse_attributes p)
        let param_attrs: Attributes = doc_attrs
            .into_iter()
            .chain(regular_attrs.into_iter())
            .collect();

        // Capture start position before label - OCaml includes the ~ in arrow location
        // But if there's an uncurried marker (.), the arrow should start at the .
        // The uncurried marker takes precedence over @-attributes for the start position
        // Doc comments do NOT affect the arrow start position
        let has_regular_attrs = param_attrs
            .iter()
            .any(|(name, _)| p.arena().get_string(name.txt) != "res.doc");
        let param_start_idx = if has_dot {
            // For uncurried parameters, OCaml includes the . in arrow location
            // Use the already-captured uncurried_start_idx (identity-based)
            uncurried_start_idx
        } else if has_regular_attrs {
            // If there are @-attributes (but no uncurried marker), start at the attribute
            post_doc_start_idx
        } else {
            p.start_pos_idx()
        };

        let (mut label, mut typ, prehandled_unlabeled_lident_attrs) = if p.token == Token::Tilde {
            p.next();
            let (name, name_loc) = parse_lident(p);
            // Pass grammar context for error message: "Did you forget a `:` here? It signals the start of a type"
            p.expect_with_grammar(Token::Colon, Some(Grammar::TypeExpression));
            // OCaml compiler/syntax/src/res_core.ml:4846-4931 threads
            // current_type_name_path through labeled parameters.
            let arg_path = extend_current_type_name_path(p, &name);
            let typ = with_current_type_name_path(p, arg_path, parse_typ_expr);
            let name_idx = p.arena_mut().push_interned_string(&name);
            (
                ArgLabel::Labelled(Located::new(name_idx, name_loc)),
                typ,
                false,
            )
        } else if matches!(p.token, Token::Lident(_)) {
            // Check if this is `name: type` (missing tilde)
            // OCaml: parse Lident first, then check for Colon
            let lookahead_is_labeled = p.lookahead(|state| {
                if matches!(state.token, Token::Lident(_)) {
                    state.next();
                    state.token == Token::Colon
                } else {
                    false
                }
            });
            if lookahead_is_labeled {
                // This is `name: type` but missing the tilde
                let (name, name_loc) = parse_lident(p);
                // Emit "missing tilde" error at the identifier location
                let error_msg = super::core::error_messages::missing_tilde_labeled_parameter(&name);
                let start_pos = p.loc_start(name_loc);
                let end_pos = p.loc_end(name_loc);
                p.err_at(start_pos, end_pos, DiagnosticCategory::Message(error_msg));
                // Consume the colon
                p.next();
                let arg_path = extend_current_type_name_path(p, &name);
                let typ = with_current_type_name_path(p, arg_path, parse_typ_expr);
                let name_idx = p.arena_mut().intern_string(&name);
                // Check for `=?` (optional without default)
                if p.token == Token::Equal {
                    p.next();
                    p.expect(Token::Question);
                    (
                        ArgLabel::Optional(Located::new(name_idx, name_loc)),
                        typ,
                        false,
                    )
                } else {
                    (
                        ArgLabel::Labelled(Located::new(name_idx, name_loc)),
                        typ,
                        false,
                    )
                }
            } else {
                // OCaml parse_type_parameter (Lident non-labeled path):
                // parse the constructor first with attrs on the constructor type,
                // then continue with parse_arrow_type_rest/parse_type_alias.
                let positional_path = make_inline_record_argument_type_name(p, positional_index);
                let typ = with_current_type_name_path(p, positional_path, |p| {
                    let mut typ = parse_type_constr(p);
                    if !typ.ptyp_loc.is_none() {
                        let constr_end_idx = p.prev_end_pos_idx();
                        typ.ptyp_loc = p.mk_loc_idx(param_start_idx, constr_end_idx);
                    }
                    if !param_attrs.is_empty() {
                        typ.ptyp_attributes = param_attrs.clone().concat(typ.ptyp_attributes);
                    }
                    if matches!(p.token, Token::EqualGreater | Token::MinusGreater) {
                        typ = parse_arrow_type_rest(p, typ, param_start_idx);
                    }
                    parse_type_alias(p, typ)
                });
                (ArgLabel::Nolabel, typ, true)
            }
        } else {
            // For unlabeled parameters, share param_start_idx with the type's location.
            // This matches OCaml's position sharing where both the arrow and the type
            // use the same start_pos variable reference.
            // But only when there are no attributes and no uncurried marker - when these
            // are present, the type should have its natural location, and ptyp_loc
            // is adjusted later to include attrs/dot.
            let outer_start = if param_attrs.is_empty() && !has_dot {
                Some(param_start_idx)
            } else {
                None
            };
            let positional_path = make_inline_record_argument_type_name(p, positional_index);
            let typ = with_current_type_name_path(p, positional_path, |p| {
                let typ = parse_typ_expr_inner_with_start(p, true, outer_start);
                parse_type_alias(p, typ)
            });
            (ArgLabel::Nolabel, typ, false)
        };

        // OCaml includes the uncurried marker (.) in the argument type's location,
        // but only for UNLABELED simple Ptyp_constr types (Lident), not for labeled arguments
        // or qualified types (Ldot) or other types like Ptyp_var.
        // Also, don't modify ghost locations (synthesized unit types from empty parens)
        // Don't modify parenthesized types with inner attributes - if param_attrs is empty
        // but typ already has attributes, the attrs came from inside parens like (@attr float)
        if has_dot
            && matches!(label, ArgLabel::Nolabel)
            && !typ.ptyp_loc.is_none()
            && !prehandled_unlabeled_lident_attrs
        {
            let is_simple_constr = matches!(
                &*typ.ptyp_desc,
                CoreTypeDesc::Ptyp_constr(inner) if p.arena().is_simple_lident(inner.0.txt)
            );
            // If param_attrs is empty but the type already has attributes, it was parsed as
            // a parenthesized expression with inner attributes like `(@attr float)`.
            // In that case, OCaml doesn't extend the type location to include the `.`
            let was_not_parenthesized_with_inner_attrs =
                !param_attrs.is_empty() || typ.ptyp_attributes.is_empty();
            if is_simple_constr && was_not_parenthesized_with_inner_attrs {
                let end_pos_idx = p.loc_end_idx(typ.ptyp_loc);
                typ = CoreType {
                    ptyp_loc: p.mk_loc_idx(uncurried_start_idx, end_pos_idx),
                    ..typ
                };
            }

            // For direct arrow types like `. unit => unit`, OCaml includes the `.` in both
            // the arrow's location AND the first argument's location.
            // But for nested/parenthesized arrows like `. (. string) => unit`, don't extend
            // because the inner arrow has its own `.` handling.
            // We detect direct arrows by checking if the arrow's first arg starts exactly
            // at post_doc_start. For nested arrows, the inner `.` extension moves the
            // first arg location before post_doc_start.
            if let CoreTypeDesc::Ptyp_arrow(inner) = *typ.ptyp_desc {
                let (arg, ret, arity) = *inner;
                let arg_typ = p.arena().get_core_type(arg.typ).clone();
                let first_arg_start = p.loc_start(arg_typ.ptyp_loc);
                // If first arg location starts exactly at post_doc_start, it's a direct arrow
                // If it starts elsewhere (before due to inner `.` or after due to parens), don't extend
                let post_doc_start = p.arena().get_position(post_doc_start_idx).clone();
                let is_direct_arrow = first_arg_start.cnum == post_doc_start.cnum;
                if is_direct_arrow {
                    // Extend arrow location to include `.`
                    let end_pos_idx = p.loc_end_idx(typ.ptyp_loc);
                    let new_arrow_loc = p.mk_loc_idx(uncurried_start_idx, end_pos_idx);

                    // Also extend first argument's location if it's a simple Lident
                    let new_arg = if matches!(
                        &*arg_typ.ptyp_desc,
                        CoreTypeDesc::Ptyp_constr(ci) if p.arena().is_simple_lident(ci.0.txt)
                    ) && !arg_typ.ptyp_loc.is_none()
                    {
                        let arg_end_idx = p.loc_end_idx(arg_typ.ptyp_loc);
                        let new_arg_loc = p.mk_loc_idx(uncurried_start_idx, arg_end_idx);
                        let new_arg_typ = CoreType {
                            ptyp_loc: new_arg_loc,
                            ..arg_typ
                        };
                        let new_arg_typ_idx = p.arena_mut().push_core_type(new_arg_typ);
                        TypeArg {
                            typ: new_arg_typ_idx,
                            ..*arg
                        }
                    } else {
                        *arg
                    };

                    typ = CoreType {
                        ptyp_desc: Box::new(CoreTypeDesc::Ptyp_arrow(Box::new((
                            Box::new(new_arg),
                            ret,
                            arity,
                        )))),
                        ptyp_loc: new_arrow_loc,
                        ptyp_attributes: typ.ptyp_attributes,
                    };
                } else {
                    // Restore the type without modification
                    typ = CoreType {
                        ptyp_desc: Box::new(CoreTypeDesc::Ptyp_arrow(Box::new((arg, ret, arity)))),
                        ..typ
                    };
                }
            }
        }

        // Optional labeled args: `~x: t=?` (res_core.ml:4849-4853).
        if p.token == Token::Equal {
            p.next();
            p.expect(Token::Question);
            if let ArgLabel::Labelled(name) = label {
                label = ArgLabel::Optional(name);
            }
        }

        // For unlabeled arguments with attributes, OCaml behavior depends on the type:
        // - For simple Lident types (like `@ignore unit`): type location includes attrs, attrs on type
        // - For other types: type location unchanged, attrs prepended to ptyp_attributes
        // In both cases, the arrow's attrs are empty for unlabeled args with outer attrs
        // Don't modify ghost locations (synthesized unit types from empty parens)
        let arrow_attrs = if prehandled_unlabeled_lident_attrs {
            // Already attached to the constructor type in the Lident branch above.
            Attributes::new()
        } else if matches!(label, ArgLabel::Nolabel) && !param_attrs.is_empty() {
            let is_simple_lident = matches!(
                &*typ.ptyp_desc,
                CoreTypeDesc::Ptyp_constr(inner) if p.arena().is_simple_lident(inner.0.txt)
            );
            if is_simple_lident && !typ.ptyp_loc.is_none() {
                // For simple Lident types, OCaml creates the type with location starting at attrs
                // and attrs passed directly to Ast_helper.Typ.constr
                // If there's an uncurried marker (.), the location should start at the .
                // Doc comments don't affect type location, only @-attributes do
                let end_pos_idx = p.loc_end_idx(typ.ptyp_loc);
                typ.ptyp_loc = if has_dot {
                    p.mk_loc_idx(uncurried_start_idx, end_pos_idx)
                } else if has_regular_attrs {
                    p.mk_loc_idx(post_doc_start_idx, end_pos_idx)
                } else {
                    typ.ptyp_loc
                };
                typ.ptyp_attributes = param_attrs.concat(typ.ptyp_attributes);
            } else {
                // For other types (or ghost locations), attrs are prepended but location unchanged
                typ.ptyp_attributes = param_attrs.concat(typ.ptyp_attributes);
            }
            // For unlabeled args, attributes go on type, not on arrow
            Attributes::new()
        } else {
            param_attrs
        };

        let typ_idx = p.arena_mut().push_core_type(typ);
        params.push((
            TypeArg {
                attrs: arrow_attrs,
                lbl: label,
                typ: typ_idx,
            },
            param_start_idx,
        ));
        positional_index += 1;

        if !p.optional(&Token::Comma) {
            if super::grammar::is_list_element(&super::grammar::Grammar::TypeParameters, &p.token) {
                // Missing comma but next token looks like another type parameter.
                // Emit "Did you forget a `,` here?" and continue parsing.
                p.expect(Token::Comma);
            } else if p.token != Token::Eof
                && p.token != Token::Rparen
                && !super::core::recover::should_abort_list_parse(p)
            {
                p.expect(Token::Comma);
                if p.token == Token::Semicolon {
                    p.next();
                }
            } else {
                break;
            }
        }
    }

    p.expect(Token::Rparen);
    let rparen_end_idx = p.prev_end_pos_idx();
    p.expect(Token::EqualGreater);
    // Parse return type without alias - `as` binds looser than `=>`
    let return_path = make_inline_record_return_type_name(p);
    let return_type =
        with_current_type_name_path(p, return_path, |p| parse_typ_expr_inner(p, true));
    // OCaml uses prev_end_pos (actual end after parsing return type) for arrow locations,
    // not return_type's ptyp_loc.loc_end. This matters for Ptyp_variant return types
    // whose ptyp_loc doesn't include the closing ]
    // Note: arrow_end_pos_idx uses cached prev_end_pos to enable sharing with return type's loc_end

    if params.is_empty() && !immediate_rparen {
        // Every parameter was skipped during error recovery: OCaml returns the
        // return type itself (res_core.ml:5002-5009).
        let end_pos_idx = p.prev_end_pos_idx();
        return CoreType {
            ptyp_loc: p.mk_loc_idx(start_pos_idx, end_pos_idx),
            ..return_type
        };
    }
    if params.is_empty() {
        // OCaml: Ast_helper.Typ.constr unit_constr []
        // No ~loc passed, so ptyp_loc defaults to Location.none (ghost)
        // But lid_loc uses the real location
        // Use stored PosIdx for sharing instead of pushing fresh position
        let lid_loc = p.mk_loc_idx(start_pos_idx, rparen_end_idx);
        let lid_idx = p.push_lident_static("unit");
        let unit_type = ast_helper::make_type_constr(lid_idx, vec![], lid_loc, LocIdx::none());
        let unit_type_idx = p.arena_mut().push_core_type(unit_type);
        params.push((
            TypeArg {
                attrs: Attributes::new(),
                lbl: ArgLabel::Nolabel,
                typ: unit_type_idx,
            },
            start_pos_idx,
        ));
    }

    // The total arity is the number of parameters
    // OCaml: When in external, decrement arity for labeled @as(_) parameters
    // These are parameters where: label is Labelled, type is Ptyp_any, and has @as attribute
    let as_underscore_count = if p.in_external {
        params
            .iter()
            .filter(|(param, _)| {
                let param_typ = p.arena().get_core_type(param.typ);
                matches!(param.lbl, ArgLabel::Labelled(_))
                    && matches!(*param_typ.ptyp_desc, CoreTypeDesc::Ptyp_any)
                    && param_typ
                        .ptyp_attributes
                        .iter()
                        .any(|(attr, _)| p.arena().get_string(attr.txt) == "as")
            })
            .count()
    } else {
        0
    };
    let total_arity = params.len() - as_underscore_count;

    // Current Parsetree stores one n-ary arrow. Keep the complete argument
    // list in the arena side table keyed by the fresh arity identity; the
    // inline payload retains the first argument for frozen-v0 conversion.
    let end_pos_idx = p.prev_end_pos_idx();
    let full_arity = p.push_arity_full(total_arity);
    let args = params.into_iter().map(|(arg, _)| arg).collect::<Vec<_>>();
    let first = args[0].clone();
    let ret = p.arena_mut().push_core_type(return_type);
    p.arena_mut().set_nary_arrow_args(full_arity, args);
    CoreType {
        ptyp_desc: Box::new(CoreTypeDesc::Ptyp_arrow(Box::new((
            Box::new(first),
            ret,
            full_arity,
        )))),
        ptyp_loc: p.mk_loc_idx(start_pos_idx, end_pos_idx),
        ptyp_attributes: Attributes::new(),
    }
}

/// Parse a lowercase identifier.
fn parse_lident(p: &mut Parser<'_>) -> (String, Location) {
    let start_pos_idx = p.start_pos_idx();
    match &p.token {
        Token::Lident(name) => {
            let name = name.to_string();
            p.next();
            let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
            (name, loc)
        }
        _ => {
            // OCaml uses Lident diagnostic here which produces context-sensitive error
            p.err(DiagnosticCategory::Lident(p.token.clone().into_owned()));
            p.next(); // Consume the invalid token
            let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
            ("_".to_string(), loc)
        }
    }
}

/// Parse attributes (including doc comments which become res.doc attributes).
fn parse_attributes(p: &mut Parser<'_>) -> Attributes {
    // OCaml `parse_attributes` = `parse_region ~grammar:Grammar.Attribute`
    // (compiler/syntax/src/res_core.ml:7635-7636, 1177-1192).
    p.leave_breadcrumb(super::grammar::Grammar::Attribute);
    let mut attrs = Attributes::new();
    loop {
        match &p.token {
            Token::At => {
                if let Some(attr) = parse_attribute(p) {
                    attrs.push(attr);
                }
            }
            Token::DocComment { loc, content } => {
                let loc_cloned = loc.clone();
                let content = content.clone();
                p.next();
                let loc = p.from_location(&loc_cloned);
                attrs.push(super::core::doc_comment_to_attribute(
                    p.arena_mut(),
                    loc,
                    content,
                ));
            }
            _ => break,
        }
    }
    p.eat_breadcrumb();
    attrs
}

/// Parse only @-style attributes (NOT doc comments).
/// Used when doc comments need to be handled separately for location purposes.
fn parse_regular_attributes(p: &mut Parser<'_>) -> Attributes {
    let mut attrs = Attributes::new();
    while p.token == Token::At {
        if let Some(attr) = parse_attribute(p) {
            attrs.push(attr);
        }
    }
    attrs
}

/// Parse a single attribute.
fn parse_attribute(p: &mut Parser<'_>) -> Option<Attribute> {
    if p.token != Token::At {
        return None;
    }
    // Use push_start_pos() to get a cached PosIdx for position sharing.
    // In OCaml, when parsing type parameters with attributes, both the
    // parameter's start_pos and the attribute's location start point to the
    // same position object (pointer equality). Using the cache ensures we
    // get the same PosIdx if someone else already captured this position.
    let start_pos_idx = p.start_pos_idx();
    p.next();

    // OCaml `parse_attribute_id` (compiler/syntax/src/res_core.ml:7531-7556).
    let attr_id = super::module::parse_extension_id(p, start_pos_idx);

    // Only parse Lparen as payload if it's immediately adjacent to the attribute ID
    let is_adjacent = p.start_pos.cnum == p.prev_end_pos.cnum;
    let payload = if p.token == Token::Lparen && is_adjacent {
        p.next();
        let payload = parse_attribute_payload(p);
        p.expect(Token::Rparen);
        payload
    } else {
        Payload::PStr(Box::new(vec![]))
    };

    Some((attr_id, payload))
}

/// Parse an attribute payload.
fn parse_attribute_payload(p: &mut Parser<'_>) -> Payload {
    // OCaml has a single `parse_payload` (compiler/syntax/src/res_core.ml:7568-7610).
    super::module::parse_payload(p)
}

// ============================================================================
// Tuple Type
// ============================================================================

/// OCaml `parse_typ_expr_region` (compiler/syntax/src/res_core.ml:5076-5078).
pub(super) fn parse_typ_expr_region(p: &mut Parser<'_>) -> Option<CoreType> {
    if grammar::is_typ_expr_start(&p.token) {
        Some(parse_typ_expr(p))
    } else {
        None
    }
}

/// Parse a tuple type.
fn parse_tuple_type(p: &mut Parser<'_>, start_pos_idx: PosIdx, first: CoreType) -> CoreType {
    // OCaml `parse_tuple_type` (compiler/syntax/src/res_core.ml:5112-5127);
    // the caller has consumed the first comma.
    p.expect(Token::Comma);
    let mut types = vec![first];
    types.extend(super::core::parse_comma_delimited_region(
        p,
        Grammar::TypExprList,
        Token::Rparen,
        parse_typ_expr_region,
    ));
    p.expect(Token::Rparen);

    // OCaml: A tuple needs at least two elements
    if types.len() == 1 {
        p.err_at(
            p.arena().get_position(start_pos_idx).clone(),
            p.prev_end_pos.clone(),
            DiagnosticCategory::Message("A tuple needs at least two elements".to_string()),
        );
    }

    let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);

    let types_idx: Vec<CoreTypeIdx> = types
        .into_iter()
        .map(|t| p.arena_mut().push_core_type(t))
        .collect();
    CoreType {
        ptyp_desc: Box::new(CoreTypeDesc::Ptyp_tuple(Box::new(types_idx))),
        ptyp_loc: loc,
        ptyp_attributes: Attributes::new(),
    }
}

// ============================================================================
// Record/Object Type
// ============================================================================

/// Parse a record or object type.
fn parse_record_or_object_type(p: &mut Parser<'_>) -> CoreType {
    let start_pos_idx = p.start_pos_idx();
    p.expect(Token::Lbrace);

    let closed = if p.token == Token::DotDot {
        p.next();
        ClosedFlag::Open
    } else if p.token == Token::Dot {
        p.next();
        ClosedFlag::Closed
    } else {
        ClosedFlag::Closed
    };

    // Check if we should extract this as an inline record type
    let has_inline_context = p.inline_types_found.is_some() && p.current_type_name_path.is_some();
    // OCaml compiler/syntax/src/res_core.ml:4777-4779 delegates this branch
    // to Grammar.is_field_decl_start from compiler/syntax/src/res_grammar.ml:191-196.
    // That deliberately excludes `...`, so object spreads stay on the object
    // field path even when an external inline-record context is active.
    let is_record_start = grammar::is_field_decl_start(&p.token);

    if has_inline_context && is_record_start {
        // Extract as inline record type - mimics OCaml's parse_record_or_object_type
        // when inline_types_context is present
        let current_path = p.current_type_name_path.clone().unwrap();
        let labels = super::module::parse_label_declarations_for_inline(p);
        p.expect(Token::Rbrace);
        let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);

        let inline_type_name = current_path.join(".");
        let inline_type_idx = p.arena_mut().push_string(inline_type_name);
        let params = p.inline_types_params.clone();

        // Register this inline type (insert at front to match OCaml's prepend order)
        if let Some(ref mut found) = p.inline_types_found {
            found.insert(
                0,
                (
                    inline_type_idx,
                    loc.clone(),
                    TypeKind::Ptype_record(labels),
                    params.clone(),
                ),
            );
        }

        // Return a Ptyp_constr pointing to the inline type
        let type_args: Vec<CoreTypeIdx> = params.into_iter().map(|(t, _)| t).collect();
        let lid_idx = p.push_lident_from_idx(inline_type_idx);
        CoreType {
            ptyp_desc: Box::new(CoreTypeDesc::Ptyp_constr(Box::new((
                with_loc(lid_idx, loc.clone()),
                type_args,
            )))),
            ptyp_loc: loc,
            ptyp_attributes: Attributes::new(),
        }
    } else {
        // OCaml res_core.ml:4777-4800: a lowercase name here is an inline
        // record in the wrong place; the fields are object fields.
        if matches!(p.token, Token::Lident(_)) {
            p.err(DiagnosticCategory::Message(
                "An inline record type declaration is only allowed in a variant constructor's declaration or nested inside of a record type declaration".to_string(),
            ));
        }
        let fields = super::core::parse_comma_delimited_region(
            p,
            Grammar::StringFieldDeclarations,
            Token::Rbrace,
            parse_string_field_declaration,
        );
        p.expect(Token::Rbrace);
        let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
        CoreType {
            ptyp_desc: Box::new(CoreTypeDesc::Ptyp_object(Box::new((fields, closed)))),
            ptyp_loc: loc,
            ptyp_attributes: Attributes::new(),
        }
    }
}

/// Parse object type body after `{` has been consumed.
/// This is used by constructor argument parsing where OCaml captures start_pos AFTER consuming `{`.
/// The caller should pass the position AFTER consuming `{` as `start_pos_idx`.
pub fn parse_object_type_body(p: &mut Parser<'_>, start_pos_idx: PosIdx) -> CoreType {
    // The caller provides the PosIdx directly for identity-based position sharing.

    // Check for open/closed markers: {. ... } or {.. ... }
    let closed = if p.token == Token::DotDot {
        p.next();
        ClosedFlag::Open
    } else if p.token == Token::Dot {
        p.next();
        ClosedFlag::Closed
    } else {
        ClosedFlag::Closed
    };

    let fields = super::core::parse_comma_delimited_region(
        p,
        Grammar::StringFieldDeclarations,
        Token::Rbrace,
        parse_string_field_declaration,
    );
    p.expect(Token::Rbrace);
    let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
    let typ = CoreType {
        ptyp_desc: Box::new(CoreTypeDesc::Ptyp_object(Box::new((fields, closed)))),
        ptyp_loc: loc,
        ptyp_attributes: Attributes::new(),
    };
    // Handle type alias: {...} as 'name
    let typ = parse_type_alias(p, typ);
    // Handle arrow rest if present
    // Match OCaml: handle both EqualGreater and MinusGreater (error recovery)
    if matches!(p.token, Token::EqualGreater | Token::MinusGreater) {
        parse_arrow_type_rest(p, typ, start_pos_idx)
    } else {
        typ
    }
}




/// OCaml `parse_string_field_declaration` (compiler/syntax/src/res_core.ml:5186-5222).
pub(super) fn parse_string_field_declaration(p: &mut Parser<'_>) -> Option<ObjectField> {
    let attrs = parse_attributes(p);
    let (name, name_loc) = match &p.token {
        Token::String(name) => {
            let name = name.to_string();
            let loc = p.mk_loc_current();
            (name, loc)
        }
        Token::DotDotDot => {
            p.next();
            let typ = parse_typ_expr(p);
            return Some(ObjectField::Oinherit(p.arena_mut().push_core_type(typ)));
        }
        Token::Lident(name) => {
            let name = name.to_string();
            let loc = p.mk_loc_current();
            p.err(DiagnosticCategory::Message(
                super::core::error_messages::object_quoted_field_name(&name),
            ));
            (name, loc)
        }
        _ => return None,
    };
    p.next();
    match p.token {
        Token::Colon => p.next(),
        Token::Equal => {
            p.err(DiagnosticCategory::Message(
                super::core::error_messages::RECORD_TYPE_FIELD_MISSING_COLON.to_string(),
            ));
            p.next();
        }
        _ => p.expect_with_grammar(Token::Colon, Some(Grammar::TypeExpression)),
    }
    let typ = parse_poly_type_expr(p);
    let typ_idx = p.arena_mut().push_core_type(typ);
    let name_idx = p.arena_mut().push_interned_string(&name);
    Some(ObjectField::Otag(
        with_loc(name_idx, name_loc),
        attrs,
        typ_idx,
    ))
}

// ============================================================================
// Polymorphic Variant Type
// ============================================================================

/// Parse polymorphic variant type args: `(typ1, typ2, ...)` for intersection types.
/// OCaml's `parse_polymorphic_variant_type_args` behavior:
/// - For a single non-tuple type, returns it without updating location (no parens in loc)
/// - For multiple types or a single tuple, creates a Ptyp_tuple with full parenthesis location
fn parse_polymorphic_variant_type_args(p: &mut Parser<'_>) -> CoreType {
    // OCaml `parse_polymorphic_variant_type_args` (compiler/syntax/src/res_core.ml:6303-6318).
    let start_pos_idx = p.start_pos_idx();
    p.expect(Token::Lparen);

    let args =
        super::core::parse_comma_delimited_region(p, Grammar::TypExprList, Token::Rparen, |p| {
            if super::grammar::is_typ_expr_start(&p.token) {
                Some(parse_typ_expr(p))
            } else {
                None
            }
        });
    p.expect(Token::Rparen);
    let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);

    match args.as_slice() {
        // Single tuple type:
        // In type-checker mode: pass through directly (no extra wrapping)
        // In printer mode: wrap in another tuple to distinguish (a, b) from ((a, b))
        [typ] if matches!(*typ.ptyp_desc, CoreTypeDesc::Ptyp_tuple(_)) => {
            if p.mode == ParserMode::ParseForTypeChecker {
                args.into_iter().next().unwrap()
            } else {
                let args_idx: Vec<CoreTypeIdx> = args
                    .into_iter()
                    .map(|a| p.arena_mut().push_core_type(a))
                    .collect();
                CoreType {
                    ptyp_desc: Box::new(CoreTypeDesc::Ptyp_tuple(Box::new(args_idx))),
                    ptyp_loc: loc,
                    ptyp_attributes: Attributes::new(),
                }
            }
        }
        // Single non-tuple type - return as-is (without parenthesis location!)
        [typ] => typ.clone(),
        // Multiple types - create tuple with full parenthesis location
        _ => {
            let args_idx: Vec<CoreTypeIdx> = args
                .into_iter()
                .map(|a| p.arena_mut().push_core_type(a))
                .collect();
            CoreType {
                ptyp_desc: Box::new(CoreTypeDesc::Ptyp_tuple(Box::new(args_idx))),
                ptyp_loc: loc,
                ptyp_attributes: Attributes::new(),
            }
        }
    }
}

/// OCaml `parse_polymorphic_variant_type` (compiler/syntax/src/res_core.ml:6108-6146).
fn parse_poly_variant_type(p: &mut Parser<'_>) -> CoreType {
    let start_pos_idx = p.start_pos_idx();
    p.expect(Token::Lbracket);
    let (fields, closed, low_tags) = match p.token {
        Token::GreaterThan => {
            p.next();
            let fields = match p.token {
                Token::Rbracket => vec![],
                Token::Bar => parse_tag_specs(p),
                _ => {
                    let first = parse_tag_spec(p);
                    let mut fields = vec![first];
                    fields.extend(parse_tag_specs(p));
                    fields
                }
            };
            (fields, ClosedFlag::Open, None)
        }
        Token::LessThan => {
            p.next();
            p.optional(&Token::Bar);
            let first = parse_tag_spec_full(p);
            let mut fields = vec![first];
            fields.extend(parse_tag_spec_fulls(p));
            let tag_names = parse_tag_names(p);
            (fields, ClosedFlag::Closed, Some(tag_names))
        }
        _ => {
            let mut fields = parse_tag_spec_first(p);
            fields.extend(parse_tag_specs(p));
            (fields, ClosedFlag::Closed, None)
        }
    };
    let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
    p.expect(Token::Rbracket);
    CoreType {
        ptyp_desc: Box::new(CoreTypeDesc::Ptyp_variant(Box::new((
            fields, closed, low_tags,
        )))),
        ptyp_loc: loc,
        ptyp_attributes: Attributes::new(),
    }
}

/// OCaml `parse_tag_names` (compiler/syntax/src/res_core.ml:6155-6168).
fn parse_tag_names(p: &mut Parser<'_>) -> Vec<Label> {
    if p.token != Token::GreaterThan {
        return vec![];
    }
    p.next();
    super::core::parse_region(p, Grammar::TagNames, |p| {
        if p.token == Token::Hash {
            let start_pos_idx = p.start_pos_idx();
            p.next();
            let (ident, _) = super::core::parse_hash_ident(p, start_pos_idx);
            Some(Cow::Owned(ident))
        } else {
            None
        }
    })
}

/// A leading doc comment becomes a `res.doc` attribute.
fn parse_optional_doc_comment_attr(p: &mut Parser<'_>) -> Attributes {
    if let Token::DocComment { loc, content } = &p.token {
        let loc = loc.clone();
        let content = content.clone();
        p.next();
        let loc = p.from_location(&loc);
        Attributes::from_vec(vec![super::core::doc_comment_to_attribute(
            p.arena_mut(),
            loc,
            content,
        )])
    } else {
        Attributes::new()
    }
}

fn prepend_row_field_attrs(p: &mut Parser<'_>, field: RowField, doc_attrs: Attributes) -> RowField {
    if doc_attrs.is_empty() {
        return field;
    }
    match field {
        RowField::Rtag(name, attrs, constant, types) => {
            RowField::Rtag(name, doc_attrs.concat(attrs), constant, types)
        }
        RowField::Rinherit(typ_idx) => {
            let mut typ = p.arena().get_core_type(typ_idx).clone();
            typ.ptyp_attributes = doc_attrs.concat(typ.ptyp_attributes);
            RowField::Rinherit(p.arena_mut().push_core_type(typ))
        }
    }
}

/// OCaml `parse_tag_spec_fulls` (compiler/syntax/src/res_core.ml:6170-6178).
fn parse_tag_spec_fulls(p: &mut Parser<'_>) -> Vec<RowField> {
    let mut fields = vec![];
    while p.token == Token::Bar {
        p.next();
        fields.push(parse_tag_spec_full(p));
    }
    fields
}

/// OCaml `parse_tag_spec_full` (compiler/syntax/src/res_core.ml:6180-6186).
fn parse_tag_spec_full(p: &mut Parser<'_>) -> RowField {
    let attrs = parse_type_attributes(p);
    if p.token == Token::Hash {
        parse_polymorphic_variant_type_spec_hash(p, attrs, true)
    } else {
        let typ = parse_typ_expr_with_attrs(p, attrs);
        RowField::Rinherit(p.arena_mut().push_core_type(typ))
    }
}

/// OCaml `parse_tag_specs` (compiler/syntax/src/res_core.ml:6188-6210).
fn parse_tag_specs(p: &mut Parser<'_>) -> Vec<RowField> {
    let mut fields = vec![];
    while matches!(p.token, Token::Bar | Token::DocComment { .. })
        && is_bar_or_doc_comment_then_bar(p)
    {
        let doc_attrs = parse_optional_doc_comment_attr(p);
        p.expect(Token::Bar);
        let tag = parse_tag_spec(p);
        fields.push(prepend_row_field_attrs(p, tag, doc_attrs));
    }
    fields
}

/// OCaml `parse_tag_spec` (compiler/syntax/src/res_core.ml:6212-6225).
fn parse_tag_spec(p: &mut Parser<'_>) -> RowField {
    let doc_attrs = parse_optional_doc_comment_attr(p);
    let attrs = doc_attrs.concat(parse_type_attributes(p));
    if p.token == Token::Hash {
        parse_polymorphic_variant_type_spec_hash(p, attrs, false)
    } else {
        let typ = parse_typ_expr_with_attrs(p, attrs);
        RowField::Rinherit(p.arena_mut().push_core_type(typ))
    }
}

/// OCaml `parse_tag_spec_first` (compiler/syntax/src/res_core.ml:6227-6276).
fn parse_tag_spec_first(p: &mut Parser<'_>) -> Vec<RowField> {
    let bar_first = is_bar_or_doc_comment_then_bar(p);
    match p.token {
        Token::Bar | Token::DocComment { .. } if bar_first => {
            let doc_attrs = parse_optional_doc_comment_attr(p);
            p.expect(Token::Bar);
            let tag = parse_tag_spec(p);
            vec![prepend_row_field_attrs(p, tag, doc_attrs)]
        }
        Token::DocComment { .. } | Token::Hash | Token::At => {
            let doc_attrs = parse_optional_doc_comment_attr(p);
            let attrs = doc_attrs.concat(parse_type_attributes(p));
            if p.token == Token::Hash {
                vec![parse_polymorphic_variant_type_spec_hash(p, attrs, false)]
            } else {
                let typ = parse_typ_expr_with_attrs(p, attrs);
                let typ_idx = p.arena_mut().push_core_type(typ);
                if p.token == Token::Rbracket {
                    vec![RowField::Rinherit(typ_idx)]
                } else {
                    p.expect(Token::Bar);
                    vec![RowField::Rinherit(typ_idx), parse_tag_spec(p)]
                }
            }
        }
        _ => {
            let typ = parse_typ_expr(p);
            let typ_idx = p.arena_mut().push_core_type(typ);
            if p.token == Token::Rbracket {
                vec![RowField::Rinherit(typ_idx)]
            } else {
                p.expect(Token::Bar);
                vec![RowField::Rinherit(typ_idx), parse_tag_spec(p)]
            }
        }
    }
}

/// OCaml `parse_polymorphic_variant_type_spec_hash` (compiler/syntax/src/res_core.ml:6278-6301).
fn parse_polymorphic_variant_type_spec_hash(
    p: &mut Parser<'_>,
    attrs: Attributes,
    full: bool,
) -> RowField {
    let start_pos_idx = p.start_pos_idx();
    p.expect(Token::Hash);
    let (ident, loc) = super::core::parse_hash_ident(p, start_pos_idx);
    let (mut tuples, constant) = match p.token {
        Token::Ampersand if full => {
            p.next();
            (vec![parse_polymorphic_variant_type_args(p)], true)
        }
        Token::Lparen => (vec![parse_polymorphic_variant_type_args(p)], false),
        _ => (vec![], true),
    };
    while full && p.token == Token::Ampersand {
        p.next();
        tuples.push(parse_polymorphic_variant_type_args(p));
    }
    let tuples = tuples
        .into_iter()
        .map(|t| p.arena_mut().push_core_type(t))
        .collect();
    RowField::Rtag(with_loc(Cow::Owned(ident), loc), attrs, constant, tuples)
}

/// Check if the current token is `|` or is a doc comment followed by `|`.
/// This matches OCaml's is_bar_or_doc_comment_then_bar function.
fn is_bar_or_doc_comment_then_bar(p: &mut Parser<'_>) -> bool {
    match &p.token {
        Token::Bar => true,
        Token::DocComment { .. } => {
            // Look ahead to see if there's a Bar after the doc comment
            p.lookahead(|state| {
                state.next(); // skip doc comment
                matches!(state.token, Token::Bar)
            })
        }
        _ => false,
    }
}

// ============================================================================
// Package Type
// ============================================================================

/// Parse a package type without leading paren: S [with type constraints].
/// Used for first-class module constraints: module(Expr: S)
/// OCaml `parse_package_type ~start_pos ~attrs` (res_core.ml:4694-4704).
pub fn parse_package_type(p: &mut Parser<'_>, start_pos_idx: PosIdx, attrs: Attributes) -> CoreType {
    let lid = parse_module_long_ident(p);

    // Parse optional constraints ("with" is not a keyword)
    let constraints = if matches!(&p.token, Token::Lident(s) if s == "with") {
        p.next();
        parse_package_constraints(p)
    } else {
        vec![]
    };

    let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);

    CoreType {
        ptyp_desc: Box::new(CoreTypeDesc::Ptyp_package(Box::new((lid, constraints)))),
        ptyp_loc: loc,
        ptyp_attributes: attrs,
    }
}

/// Parse a package type: module(S).
fn parse_package_type_with_parens(p: &mut Parser<'_>, start_pos_idx: PosIdx) -> CoreType {
    p.expect(Token::Lparen);

    let lid = parse_module_long_ident(p);

    // Parse optional constraints ("with" is not a keyword)
    let constraints = if matches!(&p.token, Token::Lident(s) if s == "with") {
        p.next();
        parse_package_constraints(p)
    } else {
        vec![]
    };

    p.expect(Token::Rparen);
    let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);

    CoreType {
        ptyp_desc: Box::new(CoreTypeDesc::Ptyp_package(Box::new((lid, constraints)))),
        ptyp_loc: loc,
        ptyp_attributes: Attributes::new(),
    }
}

/// Parse a module long identifier.
fn parse_module_long_ident(p: &mut Parser<'_>) -> super::ast::Loc<crate::parse_arena::LidentIdx> {
    let start_pos_idx = p.start_pos_idx();
    let mut path_parts: Vec<String> = vec![];

    loop {
        match &p.token {
            Token::Uident(name) => {
                path_parts.push(name.to_string());
                p.next();
                if p.token == Token::Dot {
                    p.next();
                    continue;
                }
                break;
            }
            Token::Lident(name) => {
                path_parts.push(name.to_string());
                p.next();
                break;
            }
            _ => {
                p.err(DiagnosticCategory::Uident(p.token.clone().into_owned()));
                path_parts.push("_".to_string());
                break;
            }
        }
    }

    let lid = super::core::build_longident(p.arena_mut(), &path_parts);
    let lid_idx = p.push_longident(lid);
    let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
    with_loc(lid_idx, loc)
}

/// Parse a type long identifier (module path ending in a type name).
fn parse_type_long_ident(p: &mut Parser<'_>) -> super::ast::Loc<crate::parse_arena::LidentIdx> {
    let start_pos_idx = p.start_pos_idx();
    let mut path_parts: Vec<String> = vec![];

    loop {
        match &p.token {
            Token::Uident(name) => {
                path_parts.push(name.to_string());
                p.next();
                if p.token == Token::Dot {
                    p.next();
                } else {
                    break;
                }
            }
            Token::Lident(name) => {
                path_parts.push(name.to_string());
                p.next();
                break;
            }
            _ => break,
        }
    }

    if path_parts.is_empty() {
        p.err(DiagnosticCategory::Message(
            "Expected type identifier".to_string(),
        ));
        path_parts.push("error".to_string());
    }

    let lid = super::core::build_longident(p.arena_mut(), &path_parts);
    let lid_idx = p.push_longident(lid);
    let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
    with_loc(lid_idx, loc)
}

/// Parse package constraints.
fn parse_package_constraints(
    p: &mut Parser<'_>,
) -> Vec<(super::ast::Loc<crate::parse_arena::LidentIdx>, CoreTypeIdx)> {
    let mut constraints = vec![];

    while p.token == Token::Typ || p.token == Token::And {
        if p.token == Token::And {
            p.next();
        }
        p.expect(Token::Typ);

        let lid = parse_type_long_ident(p);
        p.expect(Token::Equal);
        let typ = parse_typ_expr_inner(p, false);
        let typ_idx = p.arena_mut().push_core_type(typ);

        constraints.push((lid, typ_idx));
    }

    constraints
}

// ============================================================================
// Extension
// ============================================================================

/// Parse an extension.
fn parse_extension(p: &mut Parser<'_>) -> Extension {
    // OCaml includes the % in the extension name location
    let id_start_idx = p.start_pos_idx();
    p.expect(Token::Percent);
    let id = super::module::parse_extension_id(p, id_start_idx);

    // Parse optional payload: %ext(payload)
    let payload = if p.token == Token::Lparen {
        parse_payload(p)
    } else {
        Payload::PStr(Box::new(vec![]))
    };

    (id, payload)
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    /// Parse source code into a type expression with a timeout.
    fn parse_type_with_timeout(source: &str) -> CoreType {
        crate::parser::test_utils::parse_with_timeout(source, parse_typ_expr)
    }

    #[test]
    fn test_parse_type_var() {
        let typ = parse_type_with_timeout("'a");
        assert!(matches!(*typ.ptyp_desc, CoreTypeDesc::Ptyp_var(_)));
    }

    #[test]
    fn test_parse_type_any() {
        let typ = parse_type_with_timeout("_");
        assert!(matches!(*typ.ptyp_desc, CoreTypeDesc::Ptyp_any));
    }

    #[test]
    fn test_parse_type_constr_simple() {
        let typ = parse_type_with_timeout("int");
        assert!(matches!(*typ.ptyp_desc, CoreTypeDesc::Ptyp_constr(..)));
    }

    #[test]
    fn test_parse_type_constr_with_args() {
        let typ = parse_type_with_timeout("array<int>");
        assert!(matches!(*typ.ptyp_desc, CoreTypeDesc::Ptyp_constr(..)));
    }

    #[test]
    fn test_parse_type_tuple() {
        let typ = parse_type_with_timeout("(int, string)");
        assert!(matches!(*typ.ptyp_desc, CoreTypeDesc::Ptyp_tuple(_)));
    }

    #[test]
    fn test_parse_type_arrow() {
        let typ = parse_type_with_timeout("int => string");
        assert!(matches!(*typ.ptyp_desc, CoreTypeDesc::Ptyp_arrow(_)));
    }

    #[test]
    fn test_is_send_sync() {
        fn assert_send_sync<T: Send + Sync>() {}
        assert_send_sync::<CoreType>();
    }
}
