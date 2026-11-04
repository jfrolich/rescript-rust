//! Pattern parsing for ReScript.
//!
//! This module contains the pattern parsing logic, converting tokens
//! into pattern AST nodes.

use super::module::parse_attributes;
use std::borrow::Cow;

use super::ast::*;
use super::core::{ast_helper, mknoloc, recover, with_loc};
use super::diagnostics::DiagnosticCategory;
use super::grammar::{self, Grammar};
use super::longident::Longident;
use super::state::Parser;
use super::token::Token;
use crate::location::Position;
use crate::parse_arena::{LocIdx, Located, PatIdx, PosIdx};

// ============================================================================
// Main Pattern Parsing (OCaml res_core.ml:1210-1830)
// ============================================================================

/// OCaml `make_pat_variant_spread_attr` (res_core.ml:278-279).
fn make_pat_variant_spread_attr(p: &mut Parser<'_>) -> Attribute {
    let name = p.arena_mut().intern("res.patVariantSpread");
    (mknoloc(name), Payload::PStr(Box::default()))
}

fn pat(desc: PatternDesc, loc: LocIdx, attrs: Attributes) -> Pattern {
    Pattern {
        ppat_desc: desc,
        ppat_loc: loc,
        ppat_attributes: attrs,
    }
}

/// `Ast_helper.Pat.construct ~loc (mkloc (Lident name) loc) (mkloc [] loc)`.
fn construct_lident(
    p: &mut Parser<'_>,
    name: &'static str,
    loc: LocIdx,
    attrs: Attributes,
) -> Pattern {
    let lid_idx = if name == "()" {
        p.push_lident_static("()")
    } else {
        let name_idx = p.arena_mut().intern_string(name);
        p.push_longident(Longident::Lident(name_idx))
    };
    pat(
        PatternDesc::Ppat_construct(with_loc(lid_idx, loc), ctor_args(Vec::new(), loc)),
        loc,
        attrs,
    )
}

/// OCaml `parse_template_constant ~start_pos ~prefix` (res_core.ml).
fn parse_template_constant(
    p: &mut Parser<'_>,
    start_pos: Position,
    prefix: Option<Cow<'static, str>>,
) -> Constant {
    p.next_template_literal_token();
    if let Token::TemplateTail { text, .. } = &p.token {
        let text = text.to_string();
        p.next();
        return match prefix {
            None => match crate::string_literal::decode_js_template_escapes(&text) {
                Some(semantic) => Constant::string(&semantic),
                None => {
                    p.err_at(
                        start_pos,
                        p.prev_end_pos,
                        DiagnosticCategory::Message("Invalid string escape sequence".to_string()),
                    );
                    Constant::string("")
                }
            },
            Some(_) => {
                p.err_at(
                    start_pos,
                    p.prev_end_pos,
                    DiagnosticCategory::Message(
                        super::core::error_messages::TAGGED_TEMPLATE_IN_PATTERN.to_string(),
                    ),
                );
                Constant::string(&text)
            }
        };
    }
    fn skip_tokens(p: &mut Parser<'_>) {
        if p.token != Token::Eof {
            p.next();
            if p.token == Token::Backtick {
                p.next();
            } else {
                skip_tokens(p);
            }
        }
    }
    skip_tokens(p);
    p.err_at(
        start_pos,
        p.prev_end_pos,
        DiagnosticCategory::Message(
            super::core::error_messages::STRING_INTERPOLATION_IN_PATTERN.to_string(),
        ),
    );
    Constant::string("")
}

/// OCaml `parse_pattern` with the default `~alias:true ~or_:true`.
pub fn parse_pattern(p: &mut Parser<'_>) -> Pattern {
    parse_pattern_with(p, true, true)
}

/// OCaml `parse_pattern ?(alias = true) ?(or_ = true)` (res_core.ml:1210-1352).
fn parse_pattern_with(p: &mut Parser<'_>, alias: bool, or_: bool) -> Pattern {
    let start_pos_idx = p.start_pos_idx();
    let attrs = parse_attributes(p);
    let token = p.token.clone();
    let pattern = match token {
        Token::True | Token::False => {
            let end_pos = p.end_pos_idx();
            p.next();
            let loc = p.mk_loc_idx(start_pos_idx, end_pos);
            let name = if token == Token::True {
                "true"
            } else {
                "false"
            };
            construct_lident(p, name, loc, Attributes::new())
        }
        Token::Int { .. }
        | Token::String(_)
        | Token::Float { .. }
        | Token::Codepoint { .. }
        | Token::Minus
        | Token::Plus => {
            let c = super::expr::parse_constant(p);
            if p.token == Token::DotDot {
                p.next();
                let c2 = super::expr::parse_constant(p);
                let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
                pat(
                    PatternDesc::Ppat_interval(Box::new((c, c2))),
                    loc,
                    Attributes::new(),
                )
            } else {
                let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
                pat(
                    PatternDesc::Ppat_constant(Box::new(c)),
                    loc,
                    Attributes::new(),
                )
            }
        }
        Token::Backtick => {
            let start_pos = *p.arena().get_position(start_pos_idx);
            let constant = parse_template_constant(p, start_pos, None);
            let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
            pat(
                PatternDesc::Ppat_constant(Box::new(constant)),
                loc,
                Attributes::new(),
            )
        }
        Token::Lparen => {
            p.next();
            if p.token == Token::Rparen {
                p.next();
                let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
                construct_lident(p, "()", loc, Attributes::new())
            } else {
                let inner = parse_constrained_pattern(p);
                if p.token == Token::Comma {
                    p.next();
                    parse_tuple_pattern(p, start_pos_idx, inner, attrs.as_slice().to_vec())
                } else {
                    p.expect(Token::Rparen);
                    let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
                    let Pattern {
                        ppat_desc,
                        ppat_attributes,
                        ..
                    } = inner;
                    Pattern {
                        ppat_desc,
                        ppat_loc: loc,
                        ppat_attributes: attrs.clone().concat(ppat_attributes),
                    }
                }
            }
        }
        Token::Lbracket => parse_array_pattern(p, attrs.clone()),
        Token::Lbrace => parse_record_pattern(p, attrs.clone()),
        Token::Underscore => {
            let end_pos = p.end_pos_idx();
            let loc = p.mk_loc_idx(start_pos_idx, end_pos);
            p.next();
            pat(PatternDesc::Ppat_any, loc, attrs.clone())
        }
        Token::Lident(ident) => {
            let ident = ident.to_string();
            let end_pos = p.end_pos_idx();
            let loc = p.mk_loc_idx(start_pos_idx, end_pos);
            p.next();
            if p.token == Token::Backtick {
                let start_pos = *p.arena().get_position(start_pos_idx);
                let constant = parse_template_constant(p, start_pos, Some(Cow::Owned(ident)));
                let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
                pat(
                    PatternDesc::Ppat_constant(Box::new(constant)),
                    loc,
                    Attributes::new(),
                )
            } else {
                let name_idx = p.arena_mut().push_interned_string(&ident);
                pat(
                    PatternDesc::Ppat_var(with_loc(name_idx, loc)),
                    loc,
                    attrs.clone(),
                )
            }
        }
        Token::Uident(_) => {
            let constr = super::module::parse_module_long_ident(p);
            if p.token == Token::Lparen {
                parse_constructor_pattern_args(p, constr, start_pos_idx, attrs.clone())
            } else {
                let loc = constr.loc;
                pat(
                    PatternDesc::Ppat_construct(constr, ctor_args(Vec::new(), loc)),
                    loc,
                    attrs.clone(),
                )
            }
        }
        Token::DotDotDot => {
            p.next();
            let (parts, lid_loc) = super::module::parse_value_path(p);
            let lid_unloc = super::core::build_longident(p.arena_mut(), &parts);
            let lid = p.push_longident(lid_unloc);
            let loc = p.mk_loc_idx_to_end_of(start_pos_idx, lid_loc);
            let mut spread_attrs = vec![make_pat_variant_spread_attr(p)];
            spread_attrs.extend(attrs.iter().cloned());
            pat(
                PatternDesc::Ppat_type(with_loc(lid, lid_loc)),
                loc,
                Attributes::from_vec(spread_attrs),
            )
        }
        Token::Hash => {
            p.next();
            if p.token == Token::DotDotDot {
                p.next();
                let (parts, lid_loc) = super::module::parse_value_path(p);
                let lid_unloc = super::core::build_longident(p.arena_mut(), &parts);
                let lid = p.push_longident(lid_unloc);
                let loc = p.mk_loc_idx_to_end_of(start_pos_idx, lid_loc);
                pat(
                    PatternDesc::Ppat_type(with_loc(lid, lid_loc)),
                    loc,
                    attrs.clone(),
                )
            } else {
                let (ident, loc) = super::core::parse_hash_ident(p, start_pos_idx);
                if p.token == Token::Lparen {
                    parse_variant_pattern_args(p, ident, start_pos_idx, attrs.clone())
                } else {
                    pat(
                        PatternDesc::Ppat_variant(Box::new((
                            Cow::Owned(ident),
                            Located {
                                txt: Vec::new(),
                                loc,
                            },
                        ))),
                        loc,
                        attrs.clone(),
                    )
                }
            }
        }
        Token::Exception => {
            p.next();
            let inner = parse_pattern_with(p, false, false);
            let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
            let inner_idx = p.arena_mut().push_pat(inner);
            pat(PatternDesc::Ppat_exception(inner_idx), loc, attrs.clone())
        }
        Token::List => {
            p.next();
            parse_list_pattern(p, start_pos_idx, attrs.clone())
        }
        Token::Dict => {
            p.next();
            parse_dict_pattern(p, start_pos_idx, attrs.clone())
        }
        Token::Module => parse_module_pattern(p, attrs.clone()),
        Token::Percent => {
            let extension = super::module::parse_extension(p, false);
            let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
            pat(
                PatternDesc::Ppat_extension(Box::new(extension)),
                loc,
                attrs.clone(),
            )
        }
        Token::Eof => {
            p.err_unexpected();
            recover::default_pattern(p.arena_mut())
        }
        _ => {
            p.err_unexpected();
            if recover::skip_tokens_and_maybe_retry(p, grammar::is_atomic_pattern_start) {
                parse_pattern(p)
            } else {
                recover::default_pattern(p.arena_mut())
            }
        }
    };
    let pattern = if alias {
        parse_alias_pattern(p, pattern, attrs.as_slice())
    } else {
        pattern
    };
    if or_ {
        parse_or_pattern(p, pattern)
    } else {
        pattern
    }
}

/// OCaml `parse_alias_pattern ~attrs` (res_core.ml:1377-1386).
/// The attributes are only copied once an `as` alias is actually parsed.
pub fn parse_alias_pattern(p: &mut Parser<'_>, pattern: Pattern, attrs: &[Attribute]) -> Pattern {
    if p.token != Token::As {
        return pattern;
    }
    p.next();
    let (name, name_loc) = super::core::parse_lident(p);
    let name_idx = p.arena_mut().push_interned_string(&name);
    let loc = p.mk_loc_extend_to_prev_end(pattern.ppat_loc);
    let pattern_idx = p.arena_mut().push_pat(pattern);
    pat(
        PatternDesc::Ppat_alias(pattern_idx, with_loc(name_idx, name_loc)),
        loc,
        Attributes::from_vec(attrs.to_vec()),
    )
}

/// OCaml `parse_or_pattern` (res_core.ml:1390-1402).
fn parse_or_pattern(p: &mut Parser<'_>, pattern1: Pattern) -> Pattern {
    let mut pattern1 = pattern1;
    while p.token == Token::Bar {
        p.next();
        let pattern2 = parse_pattern_with(p, true, false);
        let loc = p.mk_loc_spanning_preserve_ghost(pattern1.ppat_loc, pattern2.ppat_loc);
        let left = p.arena_mut().push_pat(pattern1);
        let right = p.arena_mut().push_pat(pattern2);
        pattern1 = pat(PatternDesc::Ppat_or(left, right), loc, Attributes::new());
    }
    pattern1
}

/// `Ast_helper.Pat.constraint_ ~loc:(mk_loc pat.loc_start typ.loc_end)`.
fn constrain_pattern(p: &mut Parser<'_>, pattern: Pattern) -> Pattern {
    let typ = super::typ::parse_typ_expr(p);
    let loc = p.mk_loc_spanning(pattern.ppat_loc, typ.ptyp_loc);
    let pattern_idx = p.arena_mut().push_pat(pattern);
    let typ_idx = p.arena_mut().push_core_type(typ);
    pat(
        PatternDesc::Ppat_constraint(Box::new((pattern_idx, typ_idx))),
        loc,
        Attributes::new(),
    )
}

/// OCaml `parse_non_spread_pattern ~msg` (res_core.ml:1404-1422).
fn parse_non_spread_pattern(p: &mut Parser<'_>, msg: &str) -> Option<Pattern> {
    if p.token == Token::DotDotDot {
        p.err(DiagnosticCategory::Message(msg.to_string()));
        p.next();
    }
    if !grammar::is_pattern_start(&p.token) {
        return None;
    }
    let pattern = parse_pattern(p);
    if p.token == Token::Colon {
        p.next();
        Some(constrain_pattern(p, pattern))
    } else {
        Some(pattern)
    }
}

/// OCaml `parse_constrained_pattern` (res_core.ml:1424-1432).
pub fn parse_constrained_pattern(p: &mut Parser<'_>) -> Pattern {
    let pattern = parse_pattern(p);
    if p.token == Token::Colon {
        p.next();
        constrain_pattern(p, pattern)
    } else {
        pattern
    }
}

/// OCaml `parse_constrained_pattern_region` (res_core.ml:1434-1438).
fn parse_constrained_pattern_region(p: &mut Parser<'_>) -> Option<Pattern> {
    if grammar::is_pattern_start(&p.token) {
        Some(parse_constrained_pattern(p))
    } else {
        None
    }
}

/// Create a unit construct pattern `()`.
/// OCaml's Ast_helper.Pat.construct uses Location.none for the pattern location
/// when called without ~loc, so we use a ghost location here.
pub fn make_unit_construct_pattern(p: &mut super::state::Parser<'_>, lid_loc: Location) -> Pattern {
    let lid_idx = p.push_lident_static("()");
    // Use ghost location for the pattern, but real location for the longident
    ast_helper::make_construct_pat(
        p.arena_mut(),
        lid_idx,
        Vec::new(),
        lid_loc,
        lid_loc,
        LocIdx::none(),
    )
}

/// OCaml `parse_tuple_pattern ~attrs ~first ~start_pos` (res_core.ml:1602-1617).
/// The comma after `first` has been consumed by the caller.
pub fn parse_tuple_pattern(
    p: &mut Parser<'_>,
    start_pos_idx: PosIdx,
    first: Pattern,
    attrs: Vec<Attribute>,
) -> Pattern {
    let mut patterns = vec![first];
    patterns.extend(super::core::parse_comma_delimited_region(
        p,
        Grammar::PatternList,
        Token::Rparen,
        parse_constrained_pattern_region,
    ));
    p.expect(Token::Rparen);
    if patterns.len() == 1 {
        p.err_at(
            *p.arena().get_position(start_pos_idx),
            p.prev_end_pos,
            DiagnosticCategory::Message("A tuple needs at least two elements".to_string()),
        );
    }
    let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
    let pattern_indices: Vec<PatIdx> = patterns
        .into_iter()
        .map(|pattern| p.arena_mut().push_pat(pattern))
        .collect();
    pat(
        PatternDesc::Ppat_tuple(Box::new(pattern_indices)),
        loc,
        Attributes::from_vec(attrs),
    )
}

/// OCaml `parse_pattern_region` (res_core.ml:1619-1626).
fn parse_pattern_region(p: &mut Parser<'_>) -> Option<(bool, Pattern)> {
    if p.token == Token::DotDotDot {
        p.next();
        Some((true, parse_constrained_pattern(p)))
    } else if grammar::is_pattern_start(&p.token) {
        Some((false, parse_constrained_pattern(p)))
    } else {
        None
    }
}

/// OCaml `parse_module_pattern ~attrs` (res_core.ml:1628-1657).
fn parse_module_pattern(p: &mut Parser<'_>, attrs: Attributes) -> Pattern {
    let start_pos_idx = p.start_pos_idx();
    p.expect(Token::Module);
    p.expect(Token::Lparen);
    let uident = if let Token::Uident(uident) = &p.token {
        let uident = uident.to_string();
        let loc = p.mk_loc_current();
        p.next();
        let str_idx = p.arena_mut().push_interned_string(&uident);
        with_loc(str_idx, loc)
    } else {
        let str_idx = p.arena_mut().intern("_");
        mknoloc(str_idx)
    };
    if p.token == Token::Colon {
        let colon_start = p.start_pos_idx();
        p.next();
        let package_typ_attrs = parse_attributes(p);
        let package_type = super::typ::parse_package_type(p, colon_start, package_typ_attrs);
        p.expect(Token::Rparen);
        let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
        let unpack = pat(
            PatternDesc::Ppat_unpack(uident),
            uident.loc,
            Attributes::new(),
        );
        let unpack_idx = p.arena_mut().push_pat(unpack);
        let typ_idx = p.arena_mut().push_core_type(package_type);
        pat(
            PatternDesc::Ppat_constraint(Box::new((unpack_idx, typ_idx))),
            loc,
            attrs,
        )
    } else {
        p.expect(Token::Rparen);
        let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
        pat(PatternDesc::Ppat_unpack(uident), loc, attrs)
    }
}

/// OCaml `parse_list_pattern ~start_pos ~attrs` (res_core.ml:1659-1681).
fn parse_list_pattern(p: &mut Parser<'_>, start_pos_idx: PosIdx, attrs: Attributes) -> Pattern {
    let mut list_patterns = super::core::parse_comma_delimited_reversed_list(
        p,
        Grammar::PatternOcamlList,
        Token::Rbrace,
        parse_pattern_region,
    );
    p.expect(Token::Rbrace);
    let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
    let spread = if matches!(list_patterns.first(), Some((true, _))) {
        Some(list_patterns.remove(0).1)
    } else {
        None
    };
    let mut patterns: Vec<Pattern> = list_patterns
        .into_iter()
        .map(|(has_spread, pattern)| {
            if has_spread {
                p.err_at(
                    p.loc_start(pattern.ppat_loc),
                    p.end_pos,
                    DiagnosticCategory::Message(
                        super::core::error_messages::LIST_PATTERN_SPREAD.to_string(),
                    ),
                );
            }
            pattern
        })
        .collect();
    patterns.reverse();
    let mut pattern = ast_helper::make_list_pattern(p, loc, patterns, spread);
    pattern.ppat_loc = loc;
    pattern.ppat_attributes = attrs;
    pattern
}

/// OCaml `parse_array_pattern ~attrs` (res_core.ml:1706-1716).
fn parse_array_pattern(p: &mut Parser<'_>, attrs: Attributes) -> Pattern {
    let start_pos_idx = p.start_pos_idx();
    p.expect(Token::Lbracket);
    let patterns =
        super::core::parse_comma_delimited_region(p, Grammar::PatternList, Token::Rbracket, |p| {
            parse_non_spread_pattern(p, super::core::error_messages::ARRAY_PATTERN_SPREAD)
        });
    p.expect(Token::Rbracket);
    let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
    let pattern_indices: Vec<PatIdx> = patterns
        .into_iter()
        .map(|pattern| p.arena_mut().push_pat(pattern))
        .collect();
    pat(
        PatternDesc::Ppat_array(Box::new(pattern_indices)),
        loc,
        attrs,
    )
}

/// OCaml `parse_pattern_args` (res_core.ml): the parenthesized argument
/// list of a constructor or polymorphic variant pattern, located at its
/// parentheses. `C()` is `C(())`.
fn parse_pattern_args(p: &mut Parser<'_>) -> Located<Vec<PatIdx>> {
    let lparen = p.start_pos_idx();
    p.expect(Token::Lparen);
    let args = super::core::parse_comma_delimited_region(
        p,
        Grammar::PatternList,
        Token::Rparen,
        parse_constrained_pattern_region,
    );
    p.expect(Token::Rparen);
    let loc = p.mk_loc_idx_to_prev_end(lparen);
    let args = if args.is_empty() {
        vec![construct_lident(p, "()", loc, Attributes::new())]
    } else {
        args
    };
    let txt = args
        .into_iter()
        .map(|a| p.arena_mut().push_pat(a))
        .collect();
    Located { txt, loc }
}

/// OCaml `parse_constructor_pattern_args` (res_core.ml).
fn parse_constructor_pattern_args(
    p: &mut Parser<'_>,
    constr: Located<crate::parse_arena::LidentIdx>,
    start_pos_idx: PosIdx,
    attrs: Attributes,
) -> Pattern {
    let args = parse_pattern_args(p);
    let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
    pat(
        PatternDesc::Ppat_construct(constr, Box::new(args)),
        loc,
        attrs,
    )
}

/// OCaml `parse_variant_pattern_args` (res_core.ml).
fn parse_variant_pattern_args(
    p: &mut Parser<'_>,
    ident: String,
    start_pos_idx: PosIdx,
    attrs: Attributes,
) -> Pattern {
    let args = parse_pattern_args(p);
    let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
    pat(
        PatternDesc::Ppat_variant(Box::new((Cow::Owned(ident), args))),
        loc,
        attrs,
    )
}

/// A record pattern row (`PatField | PatRest | PatUnderscore`,
/// compiler/syntax/src/res_core.ml:1480).
enum RecordPatternRow {
    Field(PatternRecordField),
    Rest(crate::parser::ast::RecordPatRest),
    Underscore,
}

/// OCaml `parse_record_pattern_row_field ~attrs`
/// (compiler/syntax/src/res_core.ml:1457-1478).
fn parse_record_pattern_row_field(p: &mut Parser<'_>, attrs: Attributes) -> PatternRecordField {
    let (parts, label_loc) = super::module::parse_value_path(p);
    let lid_unloc = super::core::build_longident(p.arena_mut(), &parts);
    let lid_idx = p.push_longident(lid_unloc);
    let label = with_loc(lid_idx, label_loc);
    let (pat_idx, opt) = match p.token {
        Token::Colon => {
            p.next();
            let opt = p.optional(&Token::Question);
            let pat = parse_pattern(p);
            (p.arena_mut().push_pat(pat), opt)
        }
        Token::Equal => {
            p.err_at(
                p.start_pos,
                p.end_pos,
                DiagnosticCategory::message(
                    "Record patterns use `:` when matching fields. Example: `{field: value}`",
                ),
            );
            p.next();
            let opt = p.optional(&Token::Question);
            let pat = parse_pattern(p);
            (p.arena_mut().push_pat(pat), opt)
        }
        _ => {
            // `Longident.last label.txt` shares the label's string.
            let name_idx = p.arena().get_longident(lid_idx).last_idx();
            let mut pat = ast_helper::make_var_pat(name_idx, label_loc);
            pat.ppat_attributes = attrs;
            (p.arena_mut().push_pat(pat), false)
        }
    };
    PatternRecordField {
        lid: label,
        pat: pat_idx,
        opt,
    }
}

/// OCaml `parse_record_pattern_row` (compiler/syntax/src/res_core.ml:1481-1563).
fn parse_record_pattern_row(p: &mut Parser<'_>) -> Option<(bool, RecordPatternRow)> {
    let attrs = parse_attributes(p);
    match p.token {
        Token::DotDotDot => {
            let rest_start_pos_idx = p.start_pos_idx();
            p.next();
            let rest_name_start_pos_idx = p.start_pos_idx();
            let has_type_annotation = p.lookahead(|p| {
                let _ = super::typ::parse_atomic_typ_expr(p, Attributes::new());
                p.token == Token::As
            });
            if has_type_annotation {
                // ...TypeAnnotation<'a> as name
                let core_type = super::typ::parse_atomic_typ_expr(p, Attributes::new());
                let core_type_idx = p.arena_mut().push_core_type(core_type);
                p.expect(Token::As);
                let name_start_idx = p.start_pos_idx();
                let name = match p.token.clone() {
                    Token::Lident(ident) => {
                        // OCaml's lexer allocates a fresh string per token.
                        let name_idx = p.arena_mut().push_string(ident);
                        p.next();
                        with_loc(name_idx, p.mk_loc_idx_to_prev_end(name_start_idx))
                    }
                    _ => {
                        p.err_unexpected();
                        let name_idx = p.arena_mut().intern("_");
                        with_loc(name_idx, p.mk_loc_idx_to_prev_end(name_start_idx))
                    }
                };
                let rest_loc = p.mk_loc_idx_to_prev_end(rest_start_pos_idx);
                Some((
                    false,
                    RecordPatternRow::Rest(crate::parser::ast::RecordPatRest {
                        rest_loc,
                        rest_name: name,
                        rest_type: Some(core_type_idx),
                    }),
                ))
            } else {
                match p.token.clone() {
                    Token::Lident(ident) => {
                        // ...name (no type annotation)
                        let name_idx = p.arena_mut().push_string(ident);
                        p.next();
                        let rest_loc = p.mk_loc_idx_to_prev_end(rest_start_pos_idx);
                        let name_loc = p.mk_loc_idx_to_prev_end(rest_name_start_pos_idx);
                        Some((
                            false,
                            RecordPatternRow::Rest(crate::parser::ast::RecordPatRest {
                                rest_loc,
                                rest_name: with_loc(name_idx, name_loc),
                                rest_type: None,
                            }),
                        ))
                    }
                    // Fallback: treat as old-style spread (error).
                    _ => Some((
                        true,
                        RecordPatternRow::Field(parse_record_pattern_row_field(p, attrs)),
                    )),
                }
            }
        }
        Token::Uident(_) | Token::Lident(_) => Some((
            false,
            RecordPatternRow::Field(parse_record_pattern_row_field(p, attrs)),
        )),
        Token::Question => {
            p.next();
            match p.token {
                Token::Uident(_) | Token::Lident(_) => {
                    let field = parse_record_pattern_row_field(p, attrs);
                    Some((
                        false,
                        RecordPatternRow::Field(PatternRecordField { opt: true, ..field }),
                    ))
                }
                _ => None,
            }
        }
        Token::Underscore => {
            p.next();
            Some((false, RecordPatternRow::Underscore))
        }
        _ => {
            if p.token.is_keyword() {
                match super::core::recover_keyword_field_name_if_probably_field(
                    p,
                    super::core::error_messages::keyword_field_in_pattern,
                ) {
                    Some((recovered_name, loc)) => {
                        p.expect(Token::Colon);
                        let opt = p.optional(&Token::Question);
                        let pat = parse_pattern(p);
                        let pat_idx = p.arena_mut().push_pat(pat);
                        let lid_idx = p.push_lident(&recovered_name);
                        Some((
                            false,
                            RecordPatternRow::Field(PatternRecordField {
                                lid: with_loc(lid_idx, loc),
                                pat: pat_idx,
                                opt,
                            }),
                        ))
                    }
                    None => {
                        super::core::emit_keyword_field_error(
                            p,
                            super::core::error_messages::keyword_field_in_pattern,
                        );
                        None
                    }
                }
            } else {
                None
            }
        }
    }
}

/// OCaml `parse_record_pattern ~attrs` (compiler/syntax/src/res_core.ml:1565-1600).
fn parse_record_pattern(p: &mut Parser<'_>, attrs: Attributes) -> Pattern {
    let start_pos_idx = p.start_pos_idx();
    p.expect(Token::Lbrace);
    let mut raw_fields = super::core::parse_comma_delimited_reversed_list(
        p,
        Grammar::PatternRecord,
        Token::Rbrace,
        parse_record_pattern_row,
    );
    p.expect(Token::Rbrace);
    let closed = if matches!(raw_fields.first(), Some((_, RecordPatternRow::Underscore))) {
        raw_fields.remove(0);
        ClosedFlag::Open
    } else {
        ClosedFlag::Closed
    };
    let mut fields = vec![];
    let mut rest: Option<crate::parser::ast::RecordPatRest> = None;
    for (has_spread, field) in raw_fields {
        match field {
            RecordPatternRow::Field(field) => {
                if has_spread {
                    p.err_at(
                        p.loc_start(p.arena().get_pat(field.pat).ppat_loc),
                        p.end_pos,
                        DiagnosticCategory::Message(
                            super::core::error_messages::RECORD_PATTERN_SPREAD.to_string(),
                        ),
                    );
                }
                fields.insert(0, field);
            }
            RecordPatternRow::Rest(rest_pat) => {
                if rest.is_none() {
                    rest = Some(rest_pat);
                } else {
                    p.err_at(
                        p.loc_start(rest_pat.rest_loc),
                        p.end_pos,
                        DiagnosticCategory::Message(
                            super::core::error_messages::RECORD_PATTERN_MULTIPLE_REST.to_string(),
                        ),
                    );
                }
            }
            RecordPatternRow::Underscore => {}
        }
    }
    let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
    Pattern {
        ppat_desc: PatternDesc::Ppat_record(Box::new((fields, closed, rest))),
        ppat_loc: loc,
        ppat_attributes: attrs,
    }
}

/// OCaml `parse_dict_pattern_row` (compiler/syntax/src/res_core.ml:1683-1693).
fn parse_dict_pattern_row(p: &mut Parser<'_>) -> Option<PatternRecordField> {
    let Token::String(key) = &p.token else {
        return None;
    };
    let key = key.to_string();
    let loc = p.mk_loc_current();
    p.next();
    let lid_idx = p.push_lident(&key);
    p.expect(Token::Colon);
    let opt = p.optional(&Token::Question);
    let pat = parse_pattern(p);
    let pat_idx = p.arena_mut().push_pat(pat);
    Some(PatternRecordField {
        lid: with_loc(lid_idx, loc),
        pat: pat_idx,
        opt,
    })
}

/// OCaml `parse_dict_pattern ~start_pos ~attrs`
/// (compiler/syntax/src/res_core.ml:1695-1704). The `dict{` token is already
/// consumed.
fn parse_dict_pattern(p: &mut Parser<'_>, start_pos_idx: PosIdx, attrs: Attributes) -> Pattern {
    let fields = super::core::parse_comma_delimited_region(
        p,
        Grammar::DictRows,
        Token::Rbrace,
        parse_dict_pattern_row,
    );
    p.expect(Token::Rbrace);
    let loc = p.mk_loc_idx_to_prev_end(start_pos_idx);
    let dict_idx = p.arena_mut().intern("res.dictPattern");
    Pattern {
        ppat_desc: PatternDesc::Ppat_record(Box::new((fields, ClosedFlag::Open, None))),
        ppat_loc: loc,
        ppat_attributes: Attributes::from_vec(vec![(
            mknoloc(dict_idx),
            Payload::PStr(Box::default()),
        )])
        .concat(attrs),
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    /// Parse source code into a pattern with a timeout.
    fn parse_pattern_with_timeout(source: &str) -> Pattern {
        crate::parser::test_utils::parse_with_timeout(source, parse_pattern)
    }

    #[test]
    fn test_parse_pattern_underscore() {
        let pat = parse_pattern_with_timeout("_");
        assert!(matches!(pat.ppat_desc, PatternDesc::Ppat_any));
    }

    #[test]
    fn test_parse_pattern_var() {
        let pat = parse_pattern_with_timeout("foo");
        assert!(matches!(pat.ppat_desc, PatternDesc::Ppat_var(_)));
    }

    #[test]
    fn test_parse_pattern_unit() {
        let pat = parse_pattern_with_timeout("()");
        assert!(matches!(pat.ppat_desc, PatternDesc::Ppat_construct(..)));
    }

    #[test]
    fn test_parse_pattern_constant() {
        let pat = parse_pattern_with_timeout("42");
        assert!(matches!(pat.ppat_desc, PatternDesc::Ppat_constant(_)));
    }

    #[test]
    fn test_parse_pattern_tuple() {
        let pat = parse_pattern_with_timeout("(a, b, c)");
        assert!(matches!(pat.ppat_desc, PatternDesc::Ppat_tuple(_)));
    }

    #[test]
    fn test_parse_pattern_array() {
        let pat = parse_pattern_with_timeout("[a, b]");
        assert!(matches!(pat.ppat_desc, PatternDesc::Ppat_array(_)));
    }

    #[test]
    fn test_parse_pattern_constructor() {
        let pat = parse_pattern_with_timeout("Some(x)");
        assert!(matches!(pat.ppat_desc, PatternDesc::Ppat_construct(..)));
    }

    #[test]
    fn test_parse_pattern_record() {
        let pat = parse_pattern_with_timeout("{a, b: x}");
        assert!(matches!(pat.ppat_desc, PatternDesc::Ppat_record(..)));
    }

    #[test]
    fn test_is_send_sync() {
        fn assert_send_sync<T: Send + Sync>() {}
        assert_send_sync::<Pattern>();
    }
}
