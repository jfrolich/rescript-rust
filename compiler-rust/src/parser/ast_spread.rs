//! Array and list literals with spreads, `Pexp_spread` (OCaml
//! `compiler/ml/ast_spread.ml`): `[a, ...b]` and `list{...a, b}`. They compile
//! to calls of the runtime's `Primitive_array.spread` and
//! `Primitive_list.spread`, whose argument is an array of parts:
//! - for arrays, the spreads, and array literals of the items between them;
//! - for lists, the items before each spread consed onto it
//!   (`a :: b :: spread`), and a list literal of the items after the last one.
//!
//! The type checker types a literal as its parts, so the items keep the errors
//! of array and list literals. The array literals and `::` and `[]`
//! constructors built from the items have ghost locations, like any node the
//! compiler makes up; on the v0 PPX wire they also tell the items apart from
//! array and list literals that are spread (`Ast_mapper_to0.spread_call`).

use crate::parse_arena::{ExprIdx, ExprList, LocIdx, Located, ParseArena, PosIdx};
use crate::parser::ast::{Attributes, Expression, ExpressionDesc, SpreadElement, SpreadKind};

/// `Ast_spread.module_name`.
pub fn module_name(kind: SpreadKind) -> &'static str {
    match kind {
        SpreadKind::Spread_array => "Primitive_array",
        SpreadKind::Spread_list => "Primitive_list",
    }
}

/// `Ast_spread.groups`: the items before each spread with that spread, and
/// the items after the last spread.
pub fn groups(elements: &[SpreadElement]) -> Vec<(Vec<ExprIdx>, Option<ExprIdx>)> {
    let mut groups = Vec::new();
    let mut items = Vec::new();
    for element in elements {
        match *element {
            SpreadElement::Pspread_item(item) => items.push(item),
            SpreadElement::Pspread(spread) => {
                groups.push((std::mem::take(&mut items), Some(spread)));
            }
        }
    }
    if !items.is_empty() {
        groups.push((items, None));
    }
    groups
}

/// Where the parts' nodes are stored: the arena while it is exclusively
/// borrowed (the v0 PPX bridge), or the type checker's synthetic storage of a
/// shared arena.
pub trait PartStore {
    /// The arena the elements live in.
    fn arena(&self) -> &ParseArena;
    /// A ghost location from `start` to `end`.
    fn ghost_loc(&mut self, start: PosIdx, end: PosIdx) -> LocIdx;
    /// Store a part or one of its nodes.
    fn push_expr(&mut self, expr: Expression) -> ExprIdx;
    /// Store the items of an array part or a constructor's arguments.
    fn push_expr_list(&mut self, items: &[ExprIdx]) -> ExprList;
}

impl PartStore for &mut ParseArena {
    fn arena(&self) -> &ParseArena {
        self
    }
    fn ghost_loc(&mut self, start: PosIdx, end: PosIdx) -> LocIdx {
        self.push_loc(start, end, true)
    }
    fn push_expr(&mut self, expr: Expression) -> ExprIdx {
        ParseArena::push_expr(self, expr)
    }
    fn push_expr_list(&mut self, items: &[ExprIdx]) -> ExprList {
        ParseArena::push_expr_list(self, items)
    }
}

impl PartStore for &ParseArena {
    fn arena(&self) -> &ParseArena {
        self
    }
    fn ghost_loc(&mut self, start: PosIdx, end: PosIdx) -> LocIdx {
        self.push_typecheck_ghost_span(start, end)
    }
    fn push_expr(&mut self, expr: Expression) -> ExprIdx {
        self.push_shared_expr(expr)
    }
    fn push_expr_list(&mut self, items: &[ExprIdx]) -> ExprList {
        self.push_shared_expr_list(items)
    }
}

/// `Ast_spread.ghost_span`: from the start of `first` to the end of `last`.
fn ghost_span(store: &mut impl PartStore, first: LocIdx, last: LocIdx) -> LocIdx {
    let start = store.arena().loc_start_idx(first);
    let end = store.arena().loc_end_idx(last);
    store.ghost_loc(start, end)
}

/// `Ast_helper.Exp.construct ~loc (mkloc (Lident name) loc) (mkloc args loc)`
/// for `::` and `[]`.
fn construct(store: &mut impl PartStore, loc: LocIdx, cons: bool, args: &[ExprIdx]) -> ExprIdx {
    let lid = if cons {
        store.arena().expr_cons()
    } else {
        store.arena().expr_nil()
    };
    let args = store.push_expr_list(args);
    store.push_expr(Expression {
        pexp_desc: ExpressionDesc::Pexp_construct(Located::new(lid, loc), Located::new(args, loc)),
        pexp_loc: loc,
        pexp_attributes: Attributes::new(),
    })
}

/// `Ast_spread.parts`: the parts in the argument of `Primitive_array.spread`
/// or `Primitive_list.spread`, each an array or list.
pub fn parts(
    store: &mut impl PartStore,
    kind: SpreadKind,
    elements: &[SpreadElement],
) -> Vec<ExprIdx> {
    let mut parts = Vec::new();
    for (items, spread) in groups(elements) {
        let (Some(&first), Some(&last)) = (items.first(), items.last()) else {
            parts.extend(spread);
            continue;
        };
        match kind {
            SpreadKind::Spread_array => {
                let first_loc = store.arena().get_expr(first).pexp_loc;
                let last_loc = store.arena().get_expr(last).pexp_loc;
                let loc = ghost_span(store, first_loc, last_loc);
                let items = store.push_expr_list(&items);
                parts.push(store.push_expr(Expression {
                    pexp_desc: ExpressionDesc::Pexp_array(items),
                    pexp_loc: loc,
                    pexp_attributes: Attributes::new(),
                }));
                parts.extend(spread);
            }
            SpreadKind::Spread_list => {
                let mut tail = match spread {
                    Some(spread) => spread,
                    None => {
                        // `{last.pexp_loc with loc_start = last.pexp_loc.loc_end;
                        //   loc_ghost = true}`
                        let last_loc = store.arena().get_expr(last).pexp_loc;
                        let end = store.arena().loc_end_idx(last_loc);
                        let loc = store.ghost_loc(end, end);
                        construct(store, loc, false, &[])
                    }
                };
                // `List.fold_right`: the last item is consed first.
                for &item in items.iter().rev() {
                    let item_loc = store.arena().get_expr(item).pexp_loc;
                    let tail_loc = store.arena().get_expr(tail).pexp_loc;
                    let loc = ghost_span(store, item_loc, tail_loc);
                    tail = construct(store, loc, true, &[item, tail]);
                }
                parts.push(tail);
            }
        }
    }
    parts
}
