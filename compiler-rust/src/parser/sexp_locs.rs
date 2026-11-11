//! S-expression printer for AST with location information
//!
//! This module produces sexp output that includes location information,
//! matching OCaml res_ast_debugger.ml SexpAstWithLocs output exactly.
//! Used for debugging position parity between the Rust and OCaml parsers.

use crate::parse_arena::{LidentIdx, LocIdx, Located, ParseArena, PosIdx};
use crate::parser::ast::*;
use crate::parser::sexp::{
    Sexp, closed_flag, direction_flag, longident_idx, map_empty, mutable_flag, override_flag,
    private_flag, quote_string, quote_string_literal, rec_flag, string_to_latin1_bytes, variance,
};
use std::io::Write;

// ============================================================================
// Location helpers
// ============================================================================

fn location(loc: LocIdx, arena: &ParseArena) -> Sexp {
    let loc_start = arena.loc_start(loc);
    let loc_end = arena.loc_end(loc);
    let start_col = loc_start.cnum - loc_start.bol;
    let end_col = loc_end.cnum - loc_end.bol;
    let mut items = vec![
        Sexp::atom("loc"),
        Sexp::atom(&loc_start.line.to_string()),
        Sexp::atom(&start_col.to_string()),
        Sexp::atom(&loc_end.line.to_string()),
        Sexp::atom(&end_col.to_string()),
    ];
    if arena.loc_ghost(loc) {
        items.push(Sexp::atom("ghost"));
    }
    Sexp::list(items)
}

// ============================================================================
// Lists
// ============================================================================

fn map_empty_with_arena<'a, T, F>(items: &'a [T], arena: &'a ParseArena, f: F) -> Vec<Sexp>
where
    F: Fn(&'a T, &'a ParseArena) -> Sexp,
{
    if items.is_empty() {
        vec![Sexp::list(vec![])]
    } else {
        items.iter().map(|item| f(item, arena)).collect()
    }
}

// ============================================================================
// Positions
// ============================================================================

fn position_opt_idx(pos: &Option<PosIdx>, arena: &ParseArena) -> Sexp {
    match pos {
        None => Sexp::atom("None"),
        Some(idx) => {
            let p = arena.get_position(*idx);
            let col = p.cnum - p.bol;
            Sexp::list(vec![
                Sexp::atom("Some"),
                Sexp::list(vec![
                    Sexp::atom("pos"),
                    Sexp::atom(&p.line.to_string()),
                    Sexp::atom(&col.to_string()),
                ]),
            ])
        }
    }
}

fn arg_label(lbl: &ArgLabel, arena: &ParseArena) -> Sexp {
    match lbl {
        ArgLabel::Nolabel => Sexp::atom("Nolabel"),
        ArgLabel::Labelled(s) => Sexp::list(vec![
            Sexp::atom("Labelled"),
            Sexp::atom(&quote_string(arena.get_string(s.txt))),
            location(s.loc, arena),
        ]),
        ArgLabel::Optional(s) => Sexp::list(vec![
            Sexp::atom("Optional"),
            Sexp::atom(&quote_string(arena.get_string(s.txt))),
            location(s.loc, arena),
        ]),
    }
}

// ============================================================================
// Constants
// ============================================================================

fn opt_char(oc: &Option<char>) -> Sexp {
    match oc {
        None => Sexp::atom("None"),
        Some(c) => Sexp::list(vec![Sexp::atom("Some"), Sexp::atom(&format!("'{}'", c))]),
    }
}

fn constant_inner(c: &Constant, arena: &ParseArena) -> Sexp {
    match c {
        Constant::Integer(txt, tag) => Sexp::list(vec![
            Sexp::atom("Pconst_integer"),
            Sexp::atom(&quote_string(arena.get_string(*txt))),
            opt_char(tag),
        ]),
        Constant::Char { source, semantic } => Sexp::list(vec![
            Sexp::atom("Pconst_char"),
            Sexp::atom(&quote_string_literal(arena.get_string(*source))),
            Sexp::atom(&semantic.to_string()),
        ]),
        Constant::String(payload) => Sexp::list(vec![
            Sexp::atom("Pconst_string"),
            Sexp::atom(&quote_string_literal(payload.source(arena))),
            Sexp::atom(&quote_string_literal(payload.semantic(arena))),
        ]),
        Constant::Float(txt, tag) => Sexp::list(vec![
            Sexp::atom("Pconst_float"),
            Sexp::atom(&quote_string(arena.get_string(*txt))),
            opt_char(tag),
        ]),
    }
}

fn constant(c: &Constant, arena: &ParseArena) -> Sexp {
    Sexp::list(vec![Sexp::atom("constant"), constant_inner(c, arena)])
}

// ============================================================================
// Attributes
// ============================================================================

fn payload(p: &Payload, arena: &ParseArena) -> Sexp {
    match p {
        Payload::PStr(items) => {
            let mut parts = vec![Sexp::atom("PStr")];
            parts.extend(map_empty_with_arena(items, arena, structure_item));
            Sexp::list(parts)
        }
        Payload::PSig(items) => Sexp::list(vec![Sexp::atom("PSig"), signature(items, arena)]),
        Payload::PTyp(ct) => Sexp::list(vec![
            Sexp::atom("PTyp"),
            core_type(arena.get_core_type(*ct), arena),
        ]),
        Payload::PPat(inner) => {
            let (ref pat, ref opt_expr) = **inner;
            Sexp::list(vec![
                Sexp::atom("PPat"),
                pattern(arena.get_pat(*pat), arena),
                match opt_expr {
                    Some(e) => Sexp::list(vec![
                        Sexp::atom("Some"),
                        expression(arena.get_expr(*e), arena),
                    ]),
                    None => Sexp::atom("None"),
                },
            ])
        }
    }
}

fn attribute(attr: &Attribute, arena: &ParseArena) -> Sexp {
    let (name, p) = attr;
    Sexp::list(vec![
        Sexp::atom("attribute"),
        Sexp::atom(arena.get_string(name.txt)),
        location(name.loc, arena),
        payload(p, arena),
    ])
}

fn extension(ext: &Extension, arena: &ParseArena) -> Sexp {
    let (name, p) = ext;
    Sexp::list(vec![
        Sexp::atom("extension"),
        Sexp::atom(arena.get_string(name.txt)),
        location(name.loc, arena),
        payload(p, arena),
    ])
}

fn attributes(attrs: &[Attribute], arena: &ParseArena) -> Sexp {
    let mut parts = vec![Sexp::atom("attributes")];
    parts.extend(map_empty_with_arena(attrs, arena, attribute));
    Sexp::list(parts)
}

// ============================================================================
// Types
// ============================================================================

fn core_type(typ: &CoreType, arena: &ParseArena) -> Sexp {
    let desc = match &typ.ptyp_desc {
        CoreTypeDesc::Ptyp_any => Sexp::atom("Ptyp_any"),
        CoreTypeDesc::Ptyp_var(var) => Sexp::list(vec![
            Sexp::atom("Ptyp_var"),
            Sexp::atom(&quote_string(arena.get_string(*var))),
        ]),
        CoreTypeDesc::Ptyp_arrow(inner) => {
            let (arg, ret, arity) = &**inner;
            let params = arena
                .nary_arrow_args(arg, *arity)
                .iter()
                .map(|param| match &param.fixed {
                    None => Sexp::list(vec![
                        arg_label(&param.lbl, arena),
                        attributes(&param.attrs, arena),
                        core_type(arena.get_core_type(param.typ), arena),
                    ]),
                    Some(fixed) => Sexp::list(vec![
                        Sexp::atom("Parg_fixed"),
                        arg_label(&param.lbl, arena),
                        attributes(&param.attrs, arena),
                        fixed_value(&fixed.value, arena),
                        location(fixed.value_loc, arena),
                        location(fixed.loc, arena),
                    ]),
                })
                .collect();
            Sexp::list(vec![
                Sexp::atom("Ptyp_arrow"),
                Sexp::list(params),
                core_type(arena.get_core_type(*ret), arena),
            ])
        }
        CoreTypeDesc::Ptyp_tuple(types) => Sexp::list(vec![
            Sexp::atom("Ptyp_tuple"),
            Sexp::list(if types.is_empty() {
                vec![Sexp::list(vec![])]
            } else {
                arena
                    .type_list(*types)
                    .iter()
                    .map(|t| core_type(arena.get_core_type(*t), arena))
                    .collect()
            }),
        ]),
        CoreTypeDesc::Ptyp_constr(inner) => {
            let (ref lid, ref types) = *inner;
            Sexp::list(vec![
                Sexp::atom("Ptyp_constr"),
                longident_idx(arena, lid.txt),
                location(lid.loc, arena),
                Sexp::list(if types.is_empty() {
                    vec![Sexp::list(vec![])]
                } else {
                    arena
                        .type_list(*types)
                        .iter()
                        .map(|t| core_type(arena.get_core_type(*t), arena))
                        .collect()
                }),
            ])
        }
        CoreTypeDesc::Ptyp_object(inner) => {
            let (ref fields, ref flag) = **inner;
            Sexp::list(vec![
                Sexp::atom("Ptyp_object"),
                closed_flag(flag),
                Sexp::list(map_empty_with_arena(fields, arena, object_field)),
            ])
        }
        CoreTypeDesc::Ptyp_alias(inner) => {
            let (ref t, ref alias) = **inner;
            Sexp::list(vec![
                Sexp::atom("Ptyp_alias"),
                core_type(arena.get_core_type(*t), arena),
                Sexp::atom(&quote_string(alias)),
            ])
        }
        CoreTypeDesc::Ptyp_variant(inner) => {
            let (ref rows, ref flag, ref opt_labels) = **inner;
            Sexp::list(vec![
                Sexp::atom("Ptyp_variant"),
                Sexp::list(map_empty_with_arena(rows, arena, row_field)),
                closed_flag(flag),
                match opt_labels {
                    None => Sexp::atom("None"),
                    Some(lbls) => Sexp::list(map_empty(lbls, |s| Sexp::atom(&quote_string(s)))),
                },
            ])
        }
        CoreTypeDesc::Ptyp_poly(inner) => {
            let (ref lbls, ref t) = **inner;
            Sexp::list(vec![
                Sexp::atom("Ptyp_poly"),
                // OCaml includes location for each type variable: (("a" (loc ...)))
                Sexp::list(if lbls.is_empty() {
                    vec![Sexp::list(vec![])]
                } else {
                    lbls.iter()
                        .map(|l| {
                            Sexp::list(vec![
                                Sexp::atom(&quote_string(arena.get_string(l.txt))),
                                location(l.loc, arena),
                            ])
                        })
                        .collect()
                }),
                core_type(arena.get_core_type(*t), arena),
            ])
        }
        CoreTypeDesc::Ptyp_package(pkg_inner) => {
            let (ref mod_name, ref constraints) = **pkg_inner;
            Sexp::list(vec![
                Sexp::atom("Ptyp_package"),
                package_type_idx(mod_name, constraints, arena),
            ])
        }
        CoreTypeDesc::Ptyp_extension(ext) => {
            Sexp::list(vec![Sexp::atom("Ptyp_extension"), extension(ext, arena)])
        }
    };
    Sexp::list(vec![
        Sexp::atom("core_type"),
        location(typ.ptyp_loc, arena),
        desc,
        attributes(&typ.ptyp_attributes, arena),
    ])
}

fn object_field(field: &ObjectField, arena: &ParseArena) -> Sexp {
    match field {
        ObjectField::Otag(lbl, attrs, t) => Sexp::list(vec![
            Sexp::atom("Otag"),
            Sexp::atom(&quote_string(arena.get_string(lbl.txt))),
            location(lbl.loc, arena),
            attributes(attrs, arena),
            core_type(arena.get_core_type(*t), arena),
        ]),
        ObjectField::Oinherit(t) => Sexp::list(vec![
            Sexp::atom("Oinherit"),
            core_type(arena.get_core_type(*t), arena),
        ]),
    }
}

fn row_field(field: &RowField, arena: &ParseArena) -> Sexp {
    match field {
        RowField::Rtag(lbl, attrs, empty, types) => Sexp::list(vec![
            Sexp::atom("Rtag"),
            Sexp::atom(&quote_string(&lbl.txt)),
            location(lbl.loc, arena),
            attributes(attrs, arena),
            Sexp::atom(if *empty { "true" } else { "false" }),
            Sexp::list(map_empty(types, |group| {
                Sexp::list(vec![
                    Sexp::list(map_empty(&group.txt, |t| {
                        core_type(arena.get_core_type(*t), arena)
                    })),
                    location(group.loc, arena),
                ])
            })),
        ]),
        RowField::Rinherit(t) => Sexp::list(vec![
            Sexp::atom("Rinherit"),
            core_type(arena.get_core_type(*t), arena),
        ]),
    }
}

fn package_type_idx(
    mod_name: &Located<LidentIdx>,
    constraints: &[(Located<LidentIdx>, crate::parse_arena::CoreTypeIdx)],
    arena: &ParseArena,
) -> Sexp {
    Sexp::list(vec![
        Sexp::atom("package_type"),
        longident_idx(arena, mod_name.txt),
        location(mod_name.loc, arena),
        Sexp::list(if constraints.is_empty() {
            vec![Sexp::list(vec![])]
        } else {
            constraints
                .iter()
                .map(|(lid, t)| {
                    Sexp::list(vec![
                        longident_idx(arena, lid.txt),
                        location(lid.loc, arena),
                        core_type(arena.get_core_type(*t), arena),
                    ])
                })
                .collect()
        }),
    ])
}

// ============================================================================
// Patterns
// ============================================================================

fn pattern(p: &Pattern, arena: &ParseArena) -> Sexp {
    let descr = match &p.ppat_desc {
        PatternDesc::Ppat_any => Sexp::atom("Ppat_any"),
        PatternDesc::Ppat_var(var) => Sexp::list(vec![
            Sexp::atom("Ppat_var"),
            Sexp::atom(&quote_string(arena.get_string(var.txt))),
            location(var.loc, arena),
        ]),
        PatternDesc::Ppat_alias(pat, alias) => Sexp::list(vec![
            Sexp::atom("Ppat_alias"),
            pattern(arena.get_pat(*pat), arena),
            Sexp::atom(&quote_string(arena.get_string(alias.txt))),
            location(alias.loc, arena),
        ]),
        PatternDesc::Ppat_constant(c) => {
            Sexp::list(vec![Sexp::atom("Ppat_constant"), constant(c, arena)])
        }
        PatternDesc::Ppat_interval(inner) => {
            let (ref lo, ref hi) = **inner;
            Sexp::list(vec![
                Sexp::atom("Ppat_interval"),
                constant(lo, arena),
                constant(hi, arena),
            ])
        }
        PatternDesc::Ppat_tuple(pats) => Sexp::list(vec![
            Sexp::atom("Ppat_tuple"),
            Sexp::list(if pats.is_empty() {
                vec![Sexp::list(vec![])]
            } else {
                arena
                    .pat_list(*pats)
                    .iter()
                    .map(|p| pattern(arena.get_pat(*p), arena))
                    .collect()
            }),
        ]),
        PatternDesc::Ppat_construct(lid, opt_pat) => Sexp::list(vec![
            Sexp::atom("Ppat_construct"),
            longident_idx(arena, lid.txt),
            location(lid.loc, arena),
            Sexp::list(map_empty(arena.pat_list(opt_pat.txt), |p| {
                pattern(arena.get_pat(*p), arena)
            })),
            location(opt_pat.loc, arena),
        ]),
        PatternDesc::Ppat_variant(inner) => {
            let (ref lbl, ref opt_pat) = **inner;
            Sexp::list(vec![
                Sexp::atom("Ppat_variant"),
                Sexp::atom(&quote_string(lbl)),
                Sexp::list(map_empty(arena.pat_list(opt_pat.txt), |p| {
                    pattern(arena.get_pat(*p), arena)
                })),
                location(opt_pat.loc, arena),
            ])
        }
        PatternDesc::Ppat_record(inner) => {
            let (ref fields, ref flag, ref record_rest) = **inner;
            Sexp::list(vec![
                Sexp::atom("Ppat_record"),
                closed_flag(flag),
                Sexp::list(if fields.is_empty() {
                    vec![Sexp::list(vec![])]
                } else {
                    arena
                        .pat_field_list(*fields)
                        .iter()
                        .map(|f| {
                            Sexp::list(vec![
                                longident_idx(arena, f.lid.txt),
                                location(f.lid.loc, arena),
                                pattern(arena.get_pat(f.pat), arena),
                                Sexp::atom(if f.opt { "true" } else { "false" }),
                            ])
                        })
                        .collect()
                }),
                match record_rest.as_ref() {
                    None => Sexp::atom("None"),
                    Some(rest) => Sexp::list(vec![
                        match rest.rest_type {
                            None => Sexp::atom("None"),
                            Some(ty) => Sexp::list(vec![
                                Sexp::atom("Some"),
                                core_type(arena.get_core_type(ty), arena),
                            ]),
                        },
                        Sexp::atom(&quote_string(arena.get_string(rest.rest_name.txt))),
                        location(rest.rest_name.loc, arena),
                    ]),
                },
            ])
        }
        PatternDesc::Ppat_dict(entries) => Sexp::list(vec![
            Sexp::atom("Ppat_dict"),
            Sexp::list(map_empty_with_arena(entries, arena, |entry, arena| {
                Sexp::list(vec![
                    Sexp::atom(&quote_string(arena.get_string(entry.pdp_key.txt))),
                    location(entry.pdp_key.loc, arena),
                    Sexp::atom(if entry.pdp_optional {
                        "optional"
                    } else {
                        "required"
                    }),
                    pattern(arena.get_pat(entry.pdp_pattern), arena),
                ])
            })),
        ]),
        PatternDesc::Ppat_array(pats) => Sexp::list(vec![
            Sexp::atom("Ppat_array"),
            Sexp::list(if pats.is_empty() {
                vec![Sexp::list(vec![])]
            } else {
                arena
                    .pat_list(*pats)
                    .iter()
                    .map(|p| pattern(arena.get_pat(*p), arena))
                    .collect()
            }),
        ]),
        PatternDesc::Ppat_or(p1, p2) => Sexp::list(vec![
            Sexp::atom("Ppat_or"),
            pattern(arena.get_pat(*p1), arena),
            pattern(arena.get_pat(*p2), arena),
        ]),
        PatternDesc::Ppat_constraint(inner) => {
            let (ref pat, ref t) = **inner;
            Sexp::list(vec![
                Sexp::atom("Ppat_constraint"),
                pattern(arena.get_pat(*pat), arena),
                core_type(arena.get_core_type(*t), arena),
            ])
        }
        PatternDesc::Ppat_type(lid) => Sexp::list(vec![
            Sexp::atom("Ppat_type"),
            longident_idx(arena, lid.txt),
            location(lid.loc, arena),
        ]),
        PatternDesc::Ppat_variant_spread(lid) => Sexp::list(vec![
            Sexp::atom("Ppat_variant_spread"),
            longident_idx(arena, lid.txt),
            location(lid.loc, arena),
        ]),
        PatternDesc::Ppat_unpack(name) => Sexp::list(vec![
            Sexp::atom("Ppat_unpack"),
            Sexp::atom(&quote_string(arena.get_string(name.txt))),
            location(name.loc, arena),
        ]),
        PatternDesc::Ppat_exception(pat) => Sexp::list(vec![
            Sexp::atom("Ppat_exception"),
            pattern(arena.get_pat(*pat), arena),
        ]),
        PatternDesc::Ppat_extension(ext) => {
            Sexp::list(vec![Sexp::atom("Ppat_extension"), extension(ext, arena)])
        }
    };
    Sexp::list(vec![
        Sexp::atom("pattern"),
        location(p.ppat_loc, arena),
        descr,
        attributes(&p.ppat_attributes, arena),
    ])
}

// ============================================================================
// Expressions
// ============================================================================

fn expression(expr: &Expression, arena: &ParseArena) -> Sexp {
    let desc = match &expr.pexp_desc {
        ExpressionDesc::Pexp_braces(braces) => Sexp::list(vec![
            Sexp::atom("Pexp_braces"),
            location(braces.braces_loc, arena),
            expression(arena.get_expr(braces.expr), arena),
        ]),
        ExpressionDesc::Pexp_ident(lid) => Sexp::list(vec![
            Sexp::atom("Pexp_ident"),
            longident_idx(arena, lid.txt),
            location(lid.loc, arena),
        ]),
        ExpressionDesc::Pexp_constant(c) => {
            Sexp::list(vec![Sexp::atom("Pexp_constant"), constant(c, arena)])
        }
        ExpressionDesc::Pexp_let(inner) => {
            let (ref flag, ref vbs, ref body) = *inner;
            Sexp::list(vec![
                Sexp::atom("Pexp_let"),
                rec_flag(flag),
                Sexp::list(map_empty_with_arena(
                    arena.vb_list(*vbs),
                    arena,
                    value_binding,
                )),
                expression(arena.get_expr(*body), arena),
            ])
        }
        ExpressionDesc::Pexp_fun(inner) => {
            let params = arena
                .nary_fun_params(inner)
                .iter()
                .map(|param| {
                    Sexp::list(vec![
                        attributes(&param.p_attrs, arena),
                        arg_label(&param.p_lbl, arena),
                        match param.p_default {
                            None => Sexp::atom("None"),
                            Some(default) => Sexp::list(vec![
                                Sexp::atom("Some"),
                                expression(arena.get_expr(default), arena),
                            ]),
                        },
                        pattern(arena.get_pat(param.p_pat), arena),
                    ])
                })
                .collect();
            Sexp::list(vec![
                Sexp::atom("Pexp_fun"),
                Sexp::list(
                    arena
                        .nary_fun_newtypes(inner)
                        .iter()
                        .map(|(name, attrs)| {
                            Sexp::list(vec![
                                Sexp::atom(&quote_string(arena.get_string(name.txt))),
                                attributes(attrs, arena),
                                location(name.loc, arena),
                            ])
                        })
                        .collect(),
                ),
                Sexp::list(params),
                expression(arena.get_expr(arena.nary_fun_body(inner)), arena),
                Sexp::atom(if inner.is_async { "true" } else { "false" }),
            ])
        }
        ExpressionDesc::Pexp_apply(inner) => {
            let PexpApply {
                ref funct,
                partial: ref is_partial,
                ref transformed_jsx,
                ..
            } = *inner;
            let args = arena.apply_args(inner.args);
            Sexp::list(vec![
                Sexp::atom("Pexp_apply"),
                expression(arena.get_expr(*funct), arena),
                Sexp::list(if args.is_empty() {
                    vec![Sexp::list(vec![])]
                } else {
                    args.iter()
                        .map(|(lbl, e)| {
                            Sexp::list(vec![
                                arg_label(lbl, arena),
                                expression(arena.get_expr(*e), arena),
                            ])
                        })
                        .collect()
                }),
                Sexp::atom(if *is_partial { "true" } else { "false" }),
                Sexp::atom(if *transformed_jsx { "true" } else { "false" }),
            ])
        }
        ExpressionDesc::Pexp_match(inner) => {
            let (ref scrutinee, ref cases) = *inner;
            Sexp::list(vec![
                Sexp::atom("Pexp_match"),
                expression(arena.get_expr(*scrutinee), arena),
                Sexp::list(map_empty_with_arena(arena.case_list(*cases), arena, case)),
            ])
        }
        ExpressionDesc::Pexp_try(inner) => {
            let (ref body, ref cases, ref finally) = *inner;
            Sexp::list(vec![
                Sexp::atom("Pexp_try"),
                expression(arena.get_expr(*body), arena),
                Sexp::list(map_empty_with_arena(arena.case_list(*cases), arena, case)),
                match finally {
                    None => Sexp::atom("None"),
                    Some(e) => {
                        Sexp::list(vec![Sexp::atom("Some"), expression(arena.get_expr(*e), arena)])
                    }
                },
            ])
        }
        ExpressionDesc::Pexp_tuple(exprs) => Sexp::list(vec![
            Sexp::atom("Pexp_tuple"),
            Sexp::list(if exprs.is_empty() {
                vec![Sexp::list(vec![])]
            } else {
                arena
                    .expr_list(*exprs)
                    .iter()
                    .map(|e| expression(arena.get_expr(*e), arena))
                    .collect()
            }),
        ]),
        ExpressionDesc::Pexp_construct(lid, opt_expr) => Sexp::list(vec![
            Sexp::atom("Pexp_construct"),
            longident_idx(arena, lid.txt),
            location(lid.loc, arena),
            Sexp::list(map_empty(arena.expr_list(opt_expr.txt), |e| {
                expression(arena.get_expr(*e), arena)
            })),
            location(opt_expr.loc, arena),
        ]),
        ExpressionDesc::Pexp_variant(inner) => {
            let (ref lbl, ref opt_expr) = **inner;
            Sexp::list(vec![
                Sexp::atom("Pexp_variant"),
                Sexp::atom(&quote_string(lbl)),
                Sexp::list(map_empty(arena.expr_list(opt_expr.txt), |e| {
                    expression(arena.get_expr(*e), arena)
                })),
                location(opt_expr.loc, arena),
            ])
        }
        ExpressionDesc::Pexp_record(inner) => {
            let (ref fields, ref opt_base) = *inner;
            Sexp::list(vec![
                Sexp::atom("Pexp_record"),
                Sexp::list(if fields.is_empty() {
                    vec![Sexp::list(vec![])]
                } else {
                    arena
                        .expr_field_list(*fields)
                        .iter()
                        .map(|f| {
                            Sexp::list(vec![
                                longident_idx(arena, f.lid.txt),
                                location(f.lid.loc, arena),
                                expression(arena.get_expr(f.expr), arena),
                                Sexp::atom(if f.opt { "true" } else { "false" }),
                            ])
                        })
                        .collect()
                }),
                match opt_base {
                    None => Sexp::atom("None"),
                    Some(e) => Sexp::list(vec![
                        Sexp::atom("Some"),
                        expression(arena.get_expr(*e), arena),
                    ]),
                },
            ])
        }
        ExpressionDesc::Pexp_field(e, lid) => Sexp::list(vec![
            Sexp::atom("Pexp_field"),
            expression(arena.get_expr(*e), arena),
            longident_idx(arena, lid.txt),
            location(lid.loc, arena),
        ]),
        ExpressionDesc::Pexp_setfield(inner) => {
            let (ref e1, ref lid, ref e2) = **inner;
            Sexp::list(vec![
                Sexp::atom("Pexp_setfield"),
                expression(arena.get_expr(*e1), arena),
                longident_idx(arena, lid.txt),
                location(lid.loc, arena),
                expression(arena.get_expr(*e2), arena),
            ])
        }
        ExpressionDesc::Pexp_dict(entries) => Sexp::list(vec![
            Sexp::atom("Pexp_dict"),
            Sexp::list(map_empty_with_arena(
                entries,
                arena,
                |entry, arena| match entry {
                    DictEntry::Pdict_entry(key, e) => Sexp::list(vec![
                        Sexp::atom("Pdict_entry"),
                        Sexp::atom(&quote_string(arena.get_string(key.txt))),
                        location(key.loc, arena),
                        expression(arena.get_expr(*e), arena),
                    ]),
                    DictEntry::Pdict_spread(e) => Sexp::list(vec![
                        Sexp::atom("Pdict_spread"),
                        expression(arena.get_expr(*e), arena),
                    ]),
                },
            )),
        ]),
        ExpressionDesc::Pexp_array(exprs) => Sexp::list(vec![
            Sexp::atom("Pexp_array"),
            Sexp::list(if exprs.is_empty() {
                vec![Sexp::list(vec![])]
            } else {
                arena
                    .expr_list(*exprs)
                    .iter()
                    .map(|e| expression(arena.get_expr(*e), arena))
                    .collect()
            }),
        ]),
        ExpressionDesc::Pexp_spread(kind, elements) => Sexp::list(vec![
            Sexp::atom("Pexp_spread"),
            Sexp::atom(crate::parser::sexp::spread_kind(*kind)),
            Sexp::list(map_empty_with_arena(
                arena.spread_element_list(*elements),
                arena,
                |element, arena| match element {
                    SpreadElement::Pspread_item(e) => Sexp::list(vec![
                        Sexp::atom("Pspread_item"),
                        expression(arena.get_expr(*e), arena),
                    ]),
                    SpreadElement::Pspread(e) => Sexp::list(vec![
                        Sexp::atom("Pspread"),
                        expression(arena.get_expr(*e), arena),
                    ]),
                },
            )),
        ]),
        ExpressionDesc::Pexp_ifthenelse(inner) => {
            let (ref cond, ref then_e, ref opt_else) = **inner;
            Sexp::list(vec![
                Sexp::atom("Pexp_ifthenelse"),
                expression(arena.get_expr(*cond), arena),
                expression(arena.get_expr(*then_e), arena),
                match opt_else {
                    None => Sexp::atom("None"),
                    Some(e) => Sexp::list(vec![
                        Sexp::atom("Some"),
                        expression(arena.get_expr(*e), arena),
                    ]),
                },
            ])
        }
        ExpressionDesc::Pexp_ternary(inner) => {
            let (cond, consequent, alternate) = **inner;
            Sexp::list(vec![
                Sexp::atom("Pexp_ternary"),
                expression(arena.get_expr(cond), arena),
                expression(arena.get_expr(consequent), arena),
                expression(arena.get_expr(alternate), arena),
            ])
        }
        ExpressionDesc::Pexp_sequence(e1, e2) => Sexp::list(vec![
            Sexp::atom("Pexp_sequence"),
            expression(arena.get_expr(*e1), arena),
            expression(arena.get_expr(*e2), arena),
        ]),
        ExpressionDesc::Pexp_break => Sexp::list(vec![Sexp::atom("Pexp_break")]),
        ExpressionDesc::Pexp_continue => Sexp::list(vec![Sexp::atom("Pexp_continue")]),
        ExpressionDesc::Pexp_while(cond, body) => Sexp::list(vec![
            Sexp::atom("Pexp_while"),
            expression(arena.get_expr(*cond), arena),
            expression(arena.get_expr(*body), arena),
        ]),
        ExpressionDesc::Pexp_for(inner) => {
            let (ref pat, ref e1, ref e2, ref flag, ref body) = **inner;
            Sexp::list(vec![
                Sexp::atom("Pexp_for"),
                pattern(arena.get_pat(*pat), arena),
                expression(arena.get_expr(*e1), arena),
                expression(arena.get_expr(*e2), arena),
                direction_flag(flag),
                expression(arena.get_expr(*body), arena),
            ])
        }
        // OCaml compiler/syntax/src/res_ast_debugger.ml:1741-1742 keeps
        // these constructors opaque in SexpAstWithLocs even though the plain
        // sexp printer expands them at
        // compiler/syntax/src/res_ast_debugger.ml:678-684.
        ExpressionDesc::Pexp_for_of(_) => Sexp::list(vec![Sexp::atom("Pexp_for_of")]),
        ExpressionDesc::Pexp_for_await_of(_) => Sexp::list(vec![Sexp::atom("Pexp_for_await_of")]),
        ExpressionDesc::Pexp_constraint(inner) => {
            let (ref e, ref t) = **inner;
            Sexp::list(vec![
                Sexp::atom("Pexp_constraint"),
                expression(arena.get_expr(*e), arena),
                core_type(arena.get_core_type(*t), arena),
            ])
        }
        ExpressionDesc::Pexp_coerce(inner) => {
            let (ref e, ref _t1, ref t2) = **inner;
            Sexp::list(vec![
                Sexp::atom("Pexp_coerce"),
                expression(arena.get_expr(*e), arena),
                core_type(arena.get_core_type(*t2), arena),
            ])
        }
        ExpressionDesc::Pexp_object_get(inner) => {
            let (ref obj, ref method_name) = **inner;
            Sexp::list(vec![
                Sexp::atom("Pexp_object_get"),
                Sexp::atom(&quote_string(&method_name.txt)),
                location(method_name.loc, arena),
                expression(arena.get_expr(*obj), arena),
            ])
        }
        ExpressionDesc::Pexp_object_set(inner) => {
            let (ref obj, ref name, ref value) = **inner;
            Sexp::list(vec![
                Sexp::atom("Pexp_object_set"),
                Sexp::atom(&quote_string(&name.txt)),
                location(name.loc, arena),
                expression(arena.get_expr(*obj), arena),
                expression(arena.get_expr(*value), arena),
            ])
        }
        ExpressionDesc::Pexp_object_literal(fields) => {
            let mut items = vec![Sexp::atom("Pexp_object_literal")];
            items.extend(fields.iter().map(|(name, e)| {
                Sexp::list(vec![
                    Sexp::atom(&quote_string(&name.txt)),
                    location(name.loc, arena),
                    expression(arena.get_expr(*e), arena),
                ])
            }));
            Sexp::list(items)
        }
        ExpressionDesc::Pexp_letmodule(inner) => {
            let (ref name, ref me, ref body) = **inner;
            Sexp::list(vec![
                Sexp::atom("Pexp_letmodule"),
                Sexp::atom(&quote_string(arena.get_string(name.txt))),
                location(name.loc, arena),
                module_expression(arena.get_mod_expr(*me), arena),
                expression(arena.get_expr(*body), arena),
            ])
        }
        ExpressionDesc::Pexp_letexception(inner) => {
            let (ref ec, ref body) = **inner;
            Sexp::list(vec![
                Sexp::atom("Pexp_letexception"),
                extension_constructor(ec, arena),
                expression(arena.get_expr(*body), arena),
            ])
        }
        ExpressionDesc::Pexp_assert(e) => Sexp::list(vec![
            Sexp::atom("Pexp_assert"),
            expression(arena.get_expr(*e), arena),
        ]),
        ExpressionDesc::Pexp_newtype(inner) => {
            let (ref name, ref body) = **inner;
            Sexp::list(vec![
                Sexp::atom("Pexp_newtype"),
                Sexp::atom(&quote_string(arena.get_string(name.txt))),
                location(name.loc, arena),
                expression(arena.get_expr(*body), arena),
            ])
        }
        ExpressionDesc::Pexp_pack(me) => Sexp::list(vec![
            Sexp::atom("Pexp_pack"),
            module_expression(arena.get_mod_expr(*me), arena),
        ]),
        ExpressionDesc::Pexp_open(inner) => {
            let (ref flag, ref lid, ref body) = **inner;
            Sexp::list(vec![
                Sexp::atom("Pexp_open"),
                override_flag(flag),
                longident_idx(arena, lid.txt),
                location(lid.loc, arena),
                expression(arena.get_expr(*body), arena),
            ])
        }
        ExpressionDesc::Pexp_regexp(regexp) => Sexp::list(vec![
            Sexp::atom("Pexp_regexp"),
            Sexp::atom(&quote_string(&regexp.pattern)),
            Sexp::atom(&quote_string(&regexp.flags)),
        ]),
        ExpressionDesc::Pexp_extension(ext) => {
            Sexp::list(vec![Sexp::atom("Pexp_extension"), extension(ext, arena)])
        }
        ExpressionDesc::Pexp_raw(raw) => Sexp::list(vec![
            Sexp::atom("Pexp_raw"),
            crate::parser::sexp::raw_kind(raw.kind),
            location(raw.name_loc, arena),
            raw_source(&raw.source, arena),
        ]),
        ExpressionDesc::Pexp_todo(todo) => Sexp::list(vec![
            Sexp::atom("Pexp_todo"),
            location(todo.name_loc, arena),
            match todo.message {
                None => Sexp::atom("None"),
                Some(message) => Sexp::list(vec![
                    Sexp::atom("Some"),
                    expression(arena.get_expr(message), arena),
                ]),
            },
        ]),
        ExpressionDesc::Pexp_template(template) => Sexp::list(vec![
            Sexp::atom("Pexp_template"),
            Sexp::list(
                template
                    .source_segments
                    .iter()
                    .map(|seg| {
                        Sexp::list(vec![
                            Sexp::atom(&quote_string_literal(arena.get_string(seg.txt))),
                            location(seg.loc, arena),
                        ])
                    })
                    .collect(),
            ),
            Sexp::list(
                template
                    .values
                    .iter()
                    .map(|v| expression(arena.get_expr(*v), arena))
                    .collect(),
            ),
        ]),
        ExpressionDesc::Pexp_tagged_template(template) => Sexp::list(vec![
            Sexp::atom("Pexp_tagged_template"),
            expression(arena.get_expr(template.tag), arena),
            Sexp::list(
                template
                    .raw_sources
                    .iter()
                    .map(|seg| {
                        Sexp::list(vec![
                            Sexp::atom(&quote_string_literal(arena.get_string(seg.txt))),
                            location(seg.loc, arena),
                        ])
                    })
                    .collect(),
            ),
            Sexp::list(
                template
                    .values
                    .iter()
                    .map(|v| expression(arena.get_expr(*v), arena))
                    .collect(),
            ),
        ]),
        ExpressionDesc::Pexp_await(e) => Sexp::list(vec![
            Sexp::atom("Pexp_await"),
            expression(arena.get_expr(*e), arena),
        ]),
        ExpressionDesc::Pexp_jsx_element(jsx) => jsx_element(jsx, arena),
    };
    Sexp::list(vec![
        Sexp::atom("expression"),
        location(expr.pexp_loc, arena),
        desc,
        attributes(&expr.pexp_attributes, arena),
    ])
}

fn jsx_element(jsx: &JsxElement, arena: &ParseArena) -> Sexp {
    match jsx {
        JsxElement::Fragment(frag) => Sexp::list(vec![
            Sexp::atom("Pexp_jsx_fragment"),
            Sexp::list(map_empty(&frag.children, |e| {
                expression(arena.get_expr(*e), arena)
            })),
        ]),
        JsxElement::Unary(elem) => Sexp::list(vec![
            Sexp::atom("Pexp_jsx_unary_element"),
            Sexp::list(map_empty_with_arena(&elem.props, arena, jsx_prop)),
        ]),
        JsxElement::Container(elem) => Sexp::list(vec![
            Sexp::atom("Pexp_jsx_container_element"),
            Sexp::list(map_empty_with_arena(&elem.props, arena, jsx_prop)),
            Sexp::list(map_empty(&elem.children, |e| {
                expression(arena.get_expr(*e), arena)
            })),
        ]),
    }
}

fn jsx_prop(prop: &JsxProp, arena: &ParseArena) -> Sexp {
    match prop {
        JsxProp::Punning { name, .. } => Sexp::list(vec![
            Sexp::atom(arena.get_string(name.txt)),
            location(name.loc, arena),
        ]),
        JsxProp::Value { name, value, .. } => Sexp::list(vec![
            Sexp::atom(arena.get_string(name.txt)),
            location(name.loc, arena),
            expression(arena.get_expr(*value), arena),
        ]),
        JsxProp::Spreading { loc, expr } => Sexp::list(vec![
            Sexp::atom("..."),
            location(*loc, arena),
            expression(arena.get_expr(*expr), arena),
        ]),
    }
}

fn case(c: &Case, arena: &ParseArena) -> Sexp {
    Sexp::list(vec![
        Sexp::atom("case"),
        Sexp::list(vec![
            Sexp::atom("pc_bar"),
            position_opt_idx(&c.pc_bar, arena),
        ]),
        Sexp::list(vec![
            Sexp::atom("pc_lhs"),
            pattern(arena.get_pat(c.pc_lhs), arena),
        ]),
        Sexp::list(vec![
            Sexp::atom("pc_guard"),
            match &c.pc_guard {
                None => Sexp::atom("None"),
                Some(e) => Sexp::list(vec![
                    Sexp::atom("Some"),
                    expression(arena.get_expr(*e), arena),
                ]),
            },
        ]),
        Sexp::list(vec![
            Sexp::atom("pc_rhs"),
            expression(arena.get_expr(c.pc_rhs), arena),
        ]),
    ])
}

fn value_binding(vb: &ValueBinding, arena: &ParseArena) -> Sexp {
    let constraint = arena.value_constraint(vb.pvb_pat).map_or_else(
        || Sexp::atom("None"),
        |constraint| {
            Sexp::list(vec![
                Sexp::atom("Some"),
                Sexp::list(
                    constraint
                        .pvc_newtypes
                        .iter()
                        .map(|name| {
                            Sexp::list(vec![
                                Sexp::atom(&quote_string(arena.get_string(name.txt))),
                                location(name.loc, arena),
                            ])
                        })
                        .collect(),
                ),
                core_type(arena.get_core_type(constraint.pvc_type), arena),
            ])
        },
    );
    Sexp::list(
        vec![
            Sexp::atom("value_binding"),
            location(vb.pvb_loc, arena),
            pattern(arena.get_pat(vb.pvb_pat), arena),
            constraint,
            expression(arena.get_expr(vb.pvb_expr), arena),
            attributes(&vb.pvb_attributes, arena),
        ]
        .into_iter()
        .chain(jsx_component(vb.pvb_jsx_component.as_deref(), arena))
        .collect(),
    )
}

// ============================================================================
// Type declarations
// ============================================================================

fn type_declaration(td: &TypeDeclaration, arena: &ParseArena) -> Sexp {
    Sexp::list(vec![
        Sexp::atom("type_declaration"),
        location(td.ptype_loc, arena),
        Sexp::atom(&quote_string(arena.get_string(td.ptype_name.txt))),
        location(td.ptype_name.loc, arena),
        Sexp::list(vec![
            Sexp::atom("ptype_params"),
            Sexp::list(if td.ptype_params.is_empty() {
                vec![Sexp::list(vec![])]
            } else {
                td.ptype_params
                    .iter()
                    .map(|(t, v)| {
                        Sexp::list(vec![core_type(arena.get_core_type(*t), arena), variance(v)])
                    })
                    .collect()
            }),
        ]),
        Sexp::list(vec![
            Sexp::atom("ptype_cstrs"),
            Sexp::list(if td.ptype_cstrs.is_empty() {
                vec![Sexp::list(vec![])]
            } else {
                td.ptype_cstrs
                    .iter()
                    .map(|(t1, t2, loc)| {
                        Sexp::list(vec![
                            core_type(arena.get_core_type(*t1), arena),
                            core_type(arena.get_core_type(*t2), arena),
                            location(*loc, arena),
                        ])
                    })
                    .collect()
            }),
        ]),
        Sexp::list(vec![
            Sexp::atom("ptype_kind"),
            type_kind(&td.ptype_kind, arena),
        ]),
        Sexp::list(vec![
            Sexp::atom("ptype_manifest"),
            match &td.ptype_manifest {
                None => Sexp::atom("None"),
                Some(t) => Sexp::list(vec![
                    Sexp::atom("Some"),
                    core_type(arena.get_core_type(*t), arena),
                ]),
            },
        ]),
        Sexp::list(vec![
            Sexp::atom("ptype_private"),
            private_flag(&td.ptype_private),
        ]),
        Sexp::list(vec![
            Sexp::atom("ptype_origin"),
            Sexp::atom(match td.ptype_origin {
                TypeDeclarationOrigin::Declared => "Declared",
                TypeDeclarationOrigin::Inline_record_definition => "Inline_record_definition",
            }),
        ]),
        attributes(&td.ptype_attributes, arena),
    ])
}

fn type_kind(kind: &TypeKind, arena: &ParseArena) -> Sexp {
    match kind {
        TypeKind::Ptype_abstract => Sexp::atom("Ptype_abstract"),
        TypeKind::Ptype_variant(ctors) => Sexp::list(vec![
            Sexp::atom("Ptype_variant"),
            Sexp::list(map_empty_with_arena(ctors, arena, constructor_declaration)),
        ]),
        TypeKind::Ptype_record(fields) => Sexp::list(vec![
            Sexp::atom("Ptype_record"),
            Sexp::list(map_empty_with_arena(fields, arena, label_declaration)),
        ]),
        TypeKind::Ptype_open => Sexp::atom("Ptype_open"),
    }
}

fn constructor_declaration(cd: &ConstructorDeclaration, arena: &ParseArena) -> Sexp {
    Sexp::list(vec![
        Sexp::atom("constructor_declaration"),
        location(cd.pcd_loc, arena),
        Sexp::atom(&quote_string(arena.get_string(cd.pcd_name.txt))),
        location(cd.pcd_name.loc, arena),
        Sexp::list(vec![
            Sexp::atom("pcd_args"),
            constructor_arguments(&cd.pcd_args, arena),
        ]),
        Sexp::list(vec![
            Sexp::atom("pcd_res"),
            match &cd.pcd_res {
                None => Sexp::atom("None"),
                Some(t) => Sexp::list(vec![
                    Sexp::atom("Some"),
                    core_type(arena.get_core_type(*t), arena),
                ]),
            },
        ]),
        attributes(&cd.pcd_attributes, arena),
    ])
}

fn constructor_arguments(args: &ConstructorArguments, arena: &ParseArena) -> Sexp {
    match args {
        ConstructorArguments::Pcstr_tuple(types) => Sexp::list(vec![
            Sexp::atom("Pcstr_tuple"),
            Sexp::list(map_empty(types, |t| {
                core_type(arena.get_core_type(*t), arena)
            })),
        ]),
        ConstructorArguments::Pcstr_record(fields) => Sexp::list(vec![
            Sexp::atom("Pcstr_record"),
            Sexp::list(map_empty_with_arena(fields, arena, label_declaration)),
        ]),
    }
}

fn label_declaration(ld: &LabelDeclaration, arena: &ParseArena) -> Sexp {
    Sexp::list(vec![
        Sexp::atom("label_declaration"),
        location(ld.pld_loc, arena),
        Sexp::atom(&quote_string(arena.get_string(ld.pld_name.txt))),
        location(ld.pld_name.loc, arena),
        mutable_flag(&ld.pld_mutable),
        Sexp::atom(if ld.pld_optional { "true" } else { "false" }),
        core_type(arena.get_core_type(ld.pld_type), arena),
        attributes(&ld.pld_attributes, arena),
    ])
}

fn extension_constructor(ec: &ExtensionConstructor, arena: &ParseArena) -> Sexp {
    Sexp::list(vec![
        Sexp::atom("extension_constructor"),
        location(ec.pext_loc, arena),
        Sexp::atom(&quote_string(arena.get_string(ec.pext_name.txt))),
        location(ec.pext_name.loc, arena),
        extension_constructor_kind(&ec.pext_kind, arena),
        attributes(&ec.pext_attributes, arena),
    ])
}

fn extension_constructor_kind(kind: &ExtensionConstructorKind, arena: &ParseArena) -> Sexp {
    match kind {
        ExtensionConstructorKind::Pext_decl(args, opt_res) => Sexp::list(vec![
            Sexp::atom("Pext_decl"),
            constructor_arguments(args, arena),
            match opt_res {
                None => Sexp::atom("None"),
                Some(t) => Sexp::list(vec![
                    Sexp::atom("Some"),
                    core_type(arena.get_core_type(*t), arena),
                ]),
            },
        ]),
        ExtensionConstructorKind::Pext_rebind(lid) => Sexp::list(vec![
            Sexp::atom("Pext_rebind"),
            longident_idx(arena, lid.txt),
            location(lid.loc, arena),
        ]),
    }
}

fn type_extension(te: &TypeExtension, arena: &ParseArena) -> Sexp {
    Sexp::list(vec![
        Sexp::atom("type_extension"),
        Sexp::list(vec![
            Sexp::atom("ptyext_path"),
            longident_idx(arena, te.ptyext_path.txt),
            location(te.ptyext_path.loc, arena),
        ]),
        Sexp::list(vec![
            Sexp::atom("ptyext_parms"),
            Sexp::list(if te.ptyext_params.is_empty() {
                vec![Sexp::list(vec![])]
            } else {
                te.ptyext_params
                    .iter()
                    .map(|(t, v)| {
                        Sexp::list(vec![core_type(arena.get_core_type(*t), arena), variance(v)])
                    })
                    .collect()
            }),
        ]),
        Sexp::list(vec![
            Sexp::atom("ptyext_constructors"),
            Sexp::list(map_empty_with_arena(
                &te.ptyext_constructors,
                arena,
                extension_constructor,
            )),
        ]),
        Sexp::list(vec![
            Sexp::atom("ptyext_private"),
            private_flag(&te.ptyext_private),
        ]),
        attributes(&te.ptyext_attributes, arena),
    ])
}

// ============================================================================
// Value descriptions
// ============================================================================

fn value_description(vd: &ValueDescription, arena: &ParseArena) -> Sexp {
    Sexp::list(
        vec![
            Sexp::atom("value_description"),
            location(vd.pval_loc, arena),
            Sexp::atom(&quote_string(arena.get_string(vd.pval_name.txt))),
            location(vd.pval_name.loc, arena),
            core_type(arena.get_core_type(vd.pval_type), arena),
            Sexp::list(map_empty(
                &vd.pval_prim
                    .as_ref()
                    .map(|prim| prim.debug_strings(arena))
                    .unwrap_or_default(),
                |s| Sexp::atom(&quote_string(s)),
            )),
            attributes(&vd.pval_attributes, arena),
        ]
        .into_iter()
        .chain(jsx_component(vd.pval_jsx_component.as_deref(), arena))
        .collect(),
    )
}

// ============================================================================
// Modules
// ============================================================================

fn module_expression(me: &ModuleExpr, arena: &ParseArena) -> Sexp {
    let desc = match &me.pmod_desc {
        ModuleExprDesc::Pmod_ident(lid) => Sexp::list(vec![
            Sexp::atom("Pmod_ident"),
            longident_idx(arena, lid.txt),
            location(lid.loc, arena),
        ]),
        ModuleExprDesc::Pmod_structure(items) => {
            Sexp::list(vec![Sexp::atom("Pmod_structure"), structure(items, arena)])
        }
        ModuleExprDesc::Pmod_functor(inner) => {
            let (ref name, ref opt_mt, ref body) = **inner;
            Sexp::list(vec![
                Sexp::atom("Pmod_functor"),
                Sexp::atom(&quote_string(arena.get_string(name.txt))),
                location(name.loc, arena),
                match opt_mt {
                    None => Sexp::atom("None"),
                    Some(mt) => Sexp::list(vec![
                        Sexp::atom("Some"),
                        module_type(arena.get_mod_type(*mt), arena),
                    ]),
                },
                module_expression(arena.get_mod_expr(*body), arena),
            ])
        }
        ModuleExprDesc::Pmod_apply(me1, me2) => Sexp::list(vec![
            Sexp::atom("Pmod_apply"),
            module_expression(arena.get_mod_expr(*me1), arena),
            module_expression(arena.get_mod_expr(*me2), arena),
        ]),
        ModuleExprDesc::Pmod_constraint(me, mt) => Sexp::list(vec![
            Sexp::atom("Pmod_constraint"),
            module_expression(arena.get_mod_expr(*me), arena),
            module_type(arena.get_mod_type(*mt), arena),
        ]),
        ModuleExprDesc::Pmod_unpack(e) => Sexp::list(vec![
            Sexp::atom("Pmod_unpack"),
            expression(arena.get_expr(*e), arena),
        ]),
        ModuleExprDesc::Pmod_extension(ext) => {
            Sexp::list(vec![Sexp::atom("Pmod_extension"), extension(ext, arena)])
        }
        ModuleExprDesc::Pmod_await(m) => Sexp::list(vec![
            Sexp::atom("Pmod_await"),
            module_expression(arena.get_mod_expr(*m), arena),
        ]),
    };
    Sexp::list(vec![
        Sexp::atom("module_expr"),
        location(me.pmod_loc, arena),
        desc,
        attributes(&me.pmod_attributes, arena),
    ])
}

fn module_type(mt: &ModuleType, arena: &ParseArena) -> Sexp {
    let desc = match &mt.pmty_desc {
        ModuleTypeDesc::Pmty_ident(lid) => Sexp::list(vec![
            Sexp::atom("Pmty_ident"),
            longident_idx(arena, lid.txt),
            location(lid.loc, arena),
        ]),
        ModuleTypeDesc::Pmty_signature(items) => {
            Sexp::list(vec![Sexp::atom("Pmty_signature"), signature(items, arena)])
        }
        ModuleTypeDesc::Pmty_functor(inner) => {
            let (ref name, ref opt_mt, ref body) = **inner;
            Sexp::list(vec![
                Sexp::atom("Pmty_functor"),
                Sexp::atom(&quote_string(arena.get_string(name.txt))),
                location(name.loc, arena),
                match opt_mt {
                    None => Sexp::atom("None"),
                    Some(mt) => Sexp::list(vec![
                        Sexp::atom("Some"),
                        module_type(arena.get_mod_type(*mt), arena),
                    ]),
                },
                module_type(arena.get_mod_type(*body), arena),
            ])
        }
        ModuleTypeDesc::Pmty_with(inner) => {
            let (ref mt, ref constraints) = **inner;
            Sexp::list(vec![
                Sexp::atom("Pmty_with"),
                module_type(arena.get_mod_type(*mt), arena),
                Sexp::list(map_empty_with_arena(constraints, arena, with_constraint)),
            ])
        }
        ModuleTypeDesc::Pmty_typeof(me) => Sexp::list(vec![
            Sexp::atom("Pmty_typeof"),
            module_expression(arena.get_mod_expr(*me), arena),
        ]),
        ModuleTypeDesc::Pmty_extension(ext) => {
            Sexp::list(vec![Sexp::atom("Pmty_extension"), extension(ext, arena)])
        }
        ModuleTypeDesc::Pmty_alias(lid) => Sexp::list(vec![
            Sexp::atom("Pmty_alias"),
            longident_idx(arena, lid.txt),
            location(lid.loc, arena),
        ]),
    };
    Sexp::list(vec![
        Sexp::atom("module_type"),
        location(mt.pmty_loc, arena),
        desc,
        attributes(&mt.pmty_attributes, arena),
    ])
}

fn with_constraint(wc: &WithConstraint, arena: &ParseArena) -> Sexp {
    match wc {
        WithConstraint::Pwith_type(lid, td) => Sexp::list(vec![
            Sexp::atom("Pmty_with"),
            longident_idx(arena, lid.txt),
            location(lid.loc, arena),
            type_declaration(td, arena),
        ]),
        WithConstraint::Pwith_module(l1, l2) => Sexp::list(vec![
            Sexp::atom("Pwith_module"),
            longident_idx(arena, l1.txt),
            location(l1.loc, arena),
            longident_idx(arena, l2.txt),
            location(l2.loc, arena),
        ]),
        WithConstraint::Pwith_typesubst(lid, td) => Sexp::list(vec![
            Sexp::atom("Pwith_typesubst"),
            longident_idx(arena, lid.txt),
            location(lid.loc, arena),
            type_declaration(td, arena),
        ]),
        WithConstraint::Pwith_modsubst(l1, l2) => Sexp::list(vec![
            Sexp::atom("Pwith_modsubst"),
            longident_idx(arena, l1.txt),
            location(l1.loc, arena),
            longident_idx(arena, l2.txt),
            location(l2.loc, arena),
        ]),
    }
}

fn module_binding(mb: &ModuleBinding, arena: &ParseArena) -> Sexp {
    Sexp::list(vec![
        Sexp::atom("module_binding"),
        location(mb.pmb_loc, arena),
        Sexp::atom(&quote_string(arena.get_string(mb.pmb_name.txt))),
        location(mb.pmb_name.loc, arena),
        module_expression(arena.get_mod_expr(mb.pmb_expr), arena),
        attributes(&mb.pmb_attributes, arena),
    ])
}

fn module_declaration(md: &ModuleDeclaration, arena: &ParseArena) -> Sexp {
    Sexp::list(vec![
        Sexp::atom("module_declaration"),
        location(md.pmd_loc, arena),
        Sexp::atom(&quote_string(arena.get_string(md.pmd_name.txt))),
        location(md.pmd_name.loc, arena),
        module_type(arena.get_mod_type(md.pmd_type), arena),
        attributes(&md.pmd_attributes, arena),
    ])
}

fn module_type_declaration(mtd: &ModuleTypeDeclaration, arena: &ParseArena) -> Sexp {
    Sexp::list(vec![
        Sexp::atom("module_type_declaration"),
        location(mtd.pmtd_loc, arena),
        Sexp::atom(&quote_string(arena.get_string(mtd.pmtd_name.txt))),
        location(mtd.pmtd_name.loc, arena),
        match &mtd.pmtd_type {
            None => Sexp::atom("None"),
            Some(mt) => Sexp::list(vec![
                Sexp::atom("Some"),
                module_type(arena.get_mod_type(*mt), arena),
            ]),
        },
        attributes(&mtd.pmtd_attributes, arena),
    ])
}

fn open_description(od: &OpenDescription, arena: &ParseArena) -> Sexp {
    Sexp::list(vec![
        Sexp::atom("open_description"),
        location(od.popen_loc, arena),
        longident_idx(arena, od.popen_lid.txt),
        location(od.popen_lid.loc, arena),
        override_flag(&od.popen_override),
        attributes(&od.popen_attributes, arena),
    ])
}

fn include_declaration(id: &IncludeDeclaration, arena: &ParseArena) -> Sexp {
    Sexp::list(vec![
        Sexp::atom("include_declaration"),
        location(id.pincl_loc, arena),
        module_expression(arena.get_mod_expr(id.pincl_mod), arena),
        attributes(&id.pincl_attributes, arena),
    ])
}

fn include_description(id: &IncludeDescription, arena: &ParseArena) -> Sexp {
    Sexp::list(vec![
        Sexp::atom("include_description"),
        location(id.pincl_loc, arena),
        module_type(arena.get_mod_type(id.pincl_mod), arena),
        attributes(&id.pincl_attributes, arena),
    ])
}

// ============================================================================
// Structure
// ============================================================================

/// The sexp, with locations, of an implementation's structure.
pub fn structure(items: &[StructureItem], arena: &ParseArena) -> Sexp {
    let mut parts = vec![Sexp::atom("structure")];
    parts.extend(items.iter().map(|si| structure_item(si, arena)));
    Sexp::list(parts)
}

fn structure_item(si: &StructureItem, arena: &ParseArena) -> Sexp {
    let desc = match &si.pstr_desc {
        StructureItemDesc::Pstr_eval(inner) => {
            let (ref e, ref attrs) = **inner;
            Sexp::list(vec![
                Sexp::atom("Pstr_eval"),
                expression(arena.get_expr(*e), arena),
                attributes(attrs, arena),
            ])
        }
        StructureItemDesc::Pstr_value(inner) => {
            let (ref flag, ref vbs) = *inner;
            Sexp::list(vec![
                Sexp::atom("Pstr_value"),
                rec_flag(flag),
                Sexp::list(map_empty_with_arena(
                    arena.vb_list(*vbs),
                    arena,
                    value_binding,
                )),
            ])
        }
        StructureItemDesc::Pstr_primitive(vd) => Sexp::list(vec![
            Sexp::atom("Pstr_primitive"),
            value_description(vd, arena),
        ]),
        StructureItemDesc::Pstr_type(inner) => {
            let (ref flag, ref tds) = **inner;
            Sexp::list(vec![
                Sexp::atom("Pstr_type"),
                rec_flag(flag),
                Sexp::list(map_empty_with_arena(tds, arena, type_declaration)),
            ])
        }
        StructureItemDesc::Pstr_typext(te) => {
            Sexp::list(vec![Sexp::atom("Pstr_type"), type_extension(te, arena)])
        }
        StructureItemDesc::Pstr_exception(ec) => Sexp::list(vec![
            Sexp::atom("Pstr_exception"),
            extension_constructor(ec, arena),
        ]),
        StructureItemDesc::Pstr_module(mb) => {
            Sexp::list(vec![Sexp::atom("Pstr_module"), module_binding(mb, arena)])
        }
        StructureItemDesc::Pstr_recmodule(mbs) => Sexp::list(vec![
            Sexp::atom("Pstr_recmodule"),
            Sexp::list(map_empty_with_arena(mbs, arena, module_binding)),
        ]),
        StructureItemDesc::Pstr_modtype(mtd) => Sexp::list(vec![
            Sexp::atom("Pstr_modtype"),
            module_type_declaration(mtd, arena),
        ]),
        StructureItemDesc::Pstr_open(od) => {
            Sexp::list(vec![Sexp::atom("Pstr_open"), open_description(od, arena)])
        }
        StructureItemDesc::Pstr_include(id) => Sexp::list(vec![
            Sexp::atom("Pstr_include"),
            include_declaration(id, arena),
        ]),
        StructureItemDesc::Pstr_attribute(attr) => {
            Sexp::list(vec![Sexp::atom("Pstr_attribute"), attribute(attr, arena)])
        }
        StructureItemDesc::Pstr_raw(raw) => Sexp::list(vec![
            Sexp::atom("Pstr_raw"),
            location(raw.name_loc, arena),
            raw_source(&raw.source, arena),
            attributes(&raw.attrs, arena),
        ]),
        StructureItemDesc::Pstr_extension(inner) => {
            let (ref ext, ref attrs) = **inner;
            Sexp::list(vec![
                Sexp::atom("Pstr_extension"),
                extension(ext, arena),
                attributes(attrs, arena),
            ])
        }
    };
    Sexp::list(vec![
        Sexp::atom("structure_item"),
        location(si.pstr_loc, arena),
        desc,
    ])
}

// ============================================================================
// Signature
// ============================================================================

/// The sexp, with locations, of an interface's signature.
pub fn signature(items: &[SignatureItem], arena: &ParseArena) -> Sexp {
    let mut parts = vec![Sexp::atom("signature")];
    parts.extend(items.iter().map(|si| signature_item(si, arena)));
    Sexp::list(parts)
}

fn signature_item(si: &SignatureItem, arena: &ParseArena) -> Sexp {
    let desc = match &si.psig_desc {
        SignatureItemDesc::Psig_value(vd) => {
            Sexp::list(vec![Sexp::atom("Psig_value"), value_description(vd, arena)])
        }
        SignatureItemDesc::Psig_type(inner) => {
            let (ref flag, ref tds) = **inner;
            Sexp::list(vec![
                Sexp::atom("Psig_type"),
                rec_flag(flag),
                Sexp::list(map_empty_with_arena(tds, arena, type_declaration)),
            ])
        }
        SignatureItemDesc::Psig_typext(te) => {
            Sexp::list(vec![Sexp::atom("Psig_typext"), type_extension(te, arena)])
        }
        SignatureItemDesc::Psig_exception(ec) => Sexp::list(vec![
            Sexp::atom("Psig_exception"),
            extension_constructor(ec, arena),
        ]),
        SignatureItemDesc::Psig_module(md) => Sexp::list(vec![
            Sexp::atom("Psig_module"),
            module_declaration(md, arena),
        ]),
        SignatureItemDesc::Psig_recmodule(mds) => Sexp::list(vec![
            Sexp::atom("Psig_recmodule"),
            Sexp::list(map_empty_with_arena(mds, arena, module_declaration)),
        ]),
        SignatureItemDesc::Psig_modtype(mtd) => Sexp::list(vec![
            Sexp::atom("Psig_modtype"),
            module_type_declaration(mtd, arena),
        ]),
        SignatureItemDesc::Psig_open(od) => {
            Sexp::list(vec![Sexp::atom("Psig_open"), open_description(od, arena)])
        }
        SignatureItemDesc::Psig_include(id) => Sexp::list(vec![
            Sexp::atom("Psig_include"),
            include_description(id, arena),
        ]),
        SignatureItemDesc::Psig_attribute(attr) => {
            Sexp::list(vec![Sexp::atom("Psig_attribute"), attribute(attr, arena)])
        }
        SignatureItemDesc::Psig_extension(inner) => {
            let (ref ext, ref attrs) = **inner;
            Sexp::list(vec![
                Sexp::atom("Psig_extension"),
                extension(ext, arena),
                attributes(attrs, arena),
            ])
        }
    };
    Sexp::list(vec![
        Sexp::atom("signature_item"),
        location(si.psig_loc, arena),
        desc,
    ])
}

// ============================================================================
// Public API
// ============================================================================

/// Write the sexp, with locations, of a structure to `out`.
pub fn print_structure(items: &[StructureItem], arena: &ParseArena, out: &mut impl Write) {
    let sexp = structure(items, arena);
    let _ = out.write_all(&string_to_latin1_bytes(&sexp.to_string()));
}

/// Write the sexp, with locations, of a signature to `out`.
pub fn print_signature(items: &[SignatureItem], arena: &ParseArena, out: &mut impl Write) {
    let sexp = signature(items, arena);
    let _ = out.write_all(&string_to_latin1_bytes(&sexp.to_string()));
}

/// res_ast_debugger.ml `SexpAstWithLocs.fixed_value`.
fn fixed_value(value: &crate::parser::ast::FixedValue, arena: &ParseArena) -> Sexp {
    use crate::parser::ast::FixedValue;
    let source = |name: &str, s: &crate::parser::ast::StringLoc| {
        Sexp::list(vec![
            Sexp::atom(name),
            Sexp::atom(&quote_string_literal(arena.get_string(s.txt))),
            location(s.loc, arena),
        ])
    };
    match value {
        FixedValue::Int(s) => source("Pfixed_int", s),
        FixedValue::String(payload) => Sexp::list(vec![
            Sexp::atom("Pfixed_string"),
            Sexp::atom(&quote_string_literal(payload.source())),
            Sexp::atom(&quote_string_literal(payload.semantic())),
        ]),
        FixedValue::Template(s) => source("Pfixed_template", s),
        FixedValue::Json(s) => source("Pfixed_json", s),
    }
}

/// res_ast_debugger.ml `SexpAstWithLocs.raw_source`.
fn raw_source(source: &RawSource, arena: &ParseArena) -> Sexp {
    let (name, s) = match source {
        RawSource::String(s) => ("Raw_string", s),
        RawSource::Template(s) => ("Raw_template", s),
    };
    Sexp::list(vec![
        Sexp::atom(name),
        Sexp::atom(&quote_string_literal(arena.get_string(s.txt))),
        location(s.loc, arena),
    ])
}

/// res_ast_debugger.ml `SexpAstWithLocs.jsx_component`.
fn jsx_component(component: Option<&JsxComponent>, arena: &ParseArena) -> Option<Sexp> {
    let component = component?;
    Some(Sexp::list(vec![
        Sexp::atom("jsx_component"),
        location(component.pjc_loc, arena),
        crate::parser::sexp::jsx_component_kind(&component.pjc_kind, |t| {
            core_type(arena.get_core_type(t), arena)
        }),
        crate::parser::sexp::jsx_component_namespace(component.pjc_namespace),
    ]))
}
