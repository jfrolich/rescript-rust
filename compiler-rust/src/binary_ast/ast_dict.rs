//! Dict literals on the v0 PPX wire (OCaml `compiler/ml/ast_dict.ml`).
//!
//! `Pexp_dict` (`dict{"a": 1, ...d}`) used to be parsed into calls of the
//! runtime's `Primitive_dict`, which remain its encoding for v0 PPXs:
//! - without spreads, `Primitive_dict.make([("a", 1)])`, whose `make` carries
//!   the `res.dict` marker;
//! - with spreads, `Primitive_dict.spread(target, [part, ...])`, whose
//!   `spread` carries the `res.dictSpread` marker. The target is
//!   `Primitive_dict.make(rows)` with the rows before the first spread, and the
//!   parts are the spreads and `Primitive_dict.make(rows)` for the rows between
//!   them, like `Object.assign`. These `make` calls carry the `res.dictRows`
//!   marker.
//!
//! The markers tell the encoding apart from calls written in the source, and
//! the rows of a dict literal from a dict literal spread into it.

use crate::parse_arena::{ExprIdx, LocIdx, ParseArena};
use crate::parser::ast::{
    ArgLabel, Attributes, DictEntry, Expression, ExpressionDesc, Loc, Payload, PexpApply, StringLoc,
};
use crate::parser::core::mknoloc;
use crate::parser::longident::Longident;

/// `Ast_dict.literal_marker`.
pub const LITERAL_MARKER: &str = "res.dict";
/// `Ast_dict.spread_marker`.
pub const SPREAD_MARKER: &str = "res.dictSpread";
/// `Ast_dict.rows_marker`.
pub const ROWS_MARKER: &str = "res.dictRows";

fn marker_attributes(arena: &mut ParseArena, marker: &str) -> Attributes {
    let marker = arena.intern(marker);
    Attributes::from_vec(vec![(mknoloc(marker), Payload::PStr(Box::default()))])
}

/// `Ast_dict.part`: consecutive rows, or a spread.
pub enum Part<R, S> {
    Rows(Vec<R>),
    Spread(S),
}

/// `Ast_dict.entries`: a row or a spread, in source order.
pub enum Entry<R, S> {
    Row(R),
    Spread(S),
}

/// `Ast_dict.group`: group consecutive rows.
pub fn group<R, S>(entries: Vec<Entry<R, S>>) -> Vec<Part<R, S>> {
    let mut parts = Vec::new();
    let mut rows = Vec::new();
    for entry in entries {
        match entry {
            Entry::Row(row) => rows.push(row),
            Entry::Spread(spread) => {
                if !rows.is_empty() {
                    parts.push(Part::Rows(std::mem::take(&mut rows)));
                }
                parts.push(Part::Spread(spread));
            }
        }
    }
    if !rows.is_empty() {
        parts.push(Part::Rows(rows));
    }
    parts
}

/// `Ast_dict.target_and_sources`: the rows of a dict without spreads, or the
/// target and the sources it's built from.
pub enum TargetAndSources<R, S> {
    Rows(Vec<R>),
    Spread(Vec<R>, Vec<Part<R, S>>),
}

pub fn target_and_sources<R, S>(parts: Vec<Part<R, S>>) -> TargetAndSources<R, S> {
    let mut iter = parts.into_iter();
    match iter.next() {
        None => TargetAndSources::Rows(Vec::new()),
        Some(Part::Rows(rows)) => {
            let sources: Vec<_> = iter.collect();
            if sources.is_empty() {
                TargetAndSources::Rows(rows)
            } else {
                TargetAndSources::Spread(rows, sources)
            }
        }
        Some(first @ Part::Spread(_)) => {
            let mut sources = vec![first];
            sources.extend(iter);
            TargetAndSources::Spread(Vec::new(), sources)
        }
    }
}

/// `Ast_dict.parts`.
pub fn parts(entries: &[DictEntry]) -> Vec<Part<(StringLoc, ExprIdx), ExprIdx>> {
    group(
        entries
            .iter()
            .map(|entry| match entry {
                DictEntry::Pdict_entry(key, value) => Entry::Row((*key, *value)),
                DictEntry::Pdict_spread(spread) => Entry::Spread(*spread),
            })
            .collect(),
    )
}

/// `Ast_dict.rows_loc`: from the first key to the last value.
pub fn rows_loc(arena: &mut ParseArena, loc: LocIdx, rows: &[(StringLoc, ExprIdx)]) -> LocIdx {
    match (rows.first(), rows.last()) {
        (Some((first_key, _)), Some((_, last_value))) => {
            let start = arena.loc_start_idx(first_key.loc);
            let end = arena.loc_end_idx(arena.get_expr(*last_value).pexp_loc);
            arena.mk_loc(start, end)
        }
        _ => loc,
    }
}

/// `Ast_dict.rows_array`: `[("a", 1), ...]`, the argument of
/// `Primitive_dict.make`.
pub fn rows_array(
    arena: &mut ParseArena,
    loc: LocIdx,
    rows: &[(StringLoc, ExprIdx)],
) -> Expression {
    let items = rows
        .iter()
        .map(|(key, value)| {
            let start = arena.loc_start_idx(key.loc);
            let end = arena.loc_end_idx(arena.get_expr(*value).pexp_loc);
            let tuple_loc = arena.mk_loc(start, end);
            let key_text = arena.get_string(key.txt).to_string();
            let key_constant = arena.string_constant(&key_text);
            let key_expr = arena.push_expr(Expression {
                pexp_desc: ExpressionDesc::Pexp_constant(key_constant),
                pexp_loc: key.loc,
                pexp_attributes: Attributes::new(),
            });
            let tuple = arena.push_expr_list(&[key_expr, *value]);
            arena.push_expr(Expression {
                pexp_desc: ExpressionDesc::Pexp_tuple(tuple),
                pexp_loc: tuple_loc,
                pexp_attributes: Attributes::new(),
            })
        })
        .collect::<Vec<_>>();
    Expression {
        pexp_desc: ExpressionDesc::Pexp_array(arena.push_expr_list(&items)),
        pexp_loc: loc,
        pexp_attributes: Attributes::new(),
    }
}

/// `Ast_dict.primitive_dict`: `Primitive_dict.<name>`.
fn primitive_dict(
    arena: &mut ParseArena,
    loc: LocIdx,
    attrs: Attributes,
    name: &str,
) -> Expression {
    let module = arena.intern("Primitive_dict");
    let name = arena.intern(name);
    let lid = arena.push_longident(Longident::Ldot(Box::new(Longident::Lident(module)), name));
    Expression {
        pexp_desc: ExpressionDesc::Pexp_ident(Loc { txt: lid, loc }),
        pexp_loc: loc,
        pexp_attributes: attrs,
    }
}

fn apply(
    arena: &mut ParseArena,
    loc: LocIdx,
    funct: Expression,
    args: Vec<Expression>,
) -> Expression {
    let funct = arena.push_expr(funct);
    let args = args
        .into_iter()
        .map(|arg| (ArgLabel::Nolabel, arena.push_expr(arg)))
        .collect::<Vec<_>>();
    let args = arena.push_apply_args(&args);
    Expression {
        pexp_desc: ExpressionDesc::Pexp_apply(PexpApply {
            funct,
            args,
            partial: false,
            transformed_jsx: false,
        }),
        pexp_loc: loc,
        pexp_attributes: Attributes::new(),
    }
}

/// `Ast_dict.make`.
fn make(
    arena: &mut ParseArena,
    loc: LocIdx,
    marker: &str,
    rows: &[(StringLoc, ExprIdx)],
) -> Expression {
    let marker = marker_attributes(arena, marker);
    let funct = primitive_dict(arena, loc, marker, "make");
    let array = rows_array(arena, loc, rows);
    apply(arena, loc, funct, vec![array])
}

/// `Ast_dict.to_calls`: the calls encoding the dict literal `dict{entries}`
/// at `loc`.
pub fn to_calls(
    arena: &mut ParseArena,
    loc: LocIdx,
    attrs: Attributes,
    entries: &[DictEntry],
) -> Expression {
    let mut e = match target_and_sources(parts(entries)) {
        TargetAndSources::Rows(rows) => make(arena, loc, LITERAL_MARKER, &rows),
        TargetAndSources::Spread(target, sources) => {
            let marker = marker_attributes(arena, SPREAD_MARKER);
            let funct = primitive_dict(arena, loc, marker, "spread");
            let target_loc = rows_loc(arena, loc, &target);
            let target = make(arena, target_loc, ROWS_MARKER, &target);
            let sources = sources
                .into_iter()
                .map(|part| match part {
                    Part::Rows(rows) => {
                        let rows_loc = rows_loc(arena, loc, &rows);
                        let e = make(arena, rows_loc, ROWS_MARKER, &rows);
                        arena.push_expr(e)
                    }
                    Part::Spread(spread) => spread,
                })
                .collect::<Vec<_>>();
            let sources = Expression {
                pexp_desc: ExpressionDesc::Pexp_array(arena.push_expr_list(&sources)),
                pexp_loc: loc,
                pexp_attributes: Attributes::new(),
            };
            apply(arena, loc, funct, vec![target, sources])
        }
    };
    e.pexp_attributes = attrs;
    e
}
