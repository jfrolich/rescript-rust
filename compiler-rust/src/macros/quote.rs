//! Lowering of quotes in a macro's own file.
//!
//! `%code(JSON.Encode.string(${value}))` becomes
//!
//! ```text
//! Macro.__quoteCode(["JSON.Encode.string(", ")"], [Macro.__holeCode(value)])
//! ```
//!
//! The pieces are the quote's source text between the holes, so a quote is
//! parsed and reported on where it is written and the macro's compiled
//! JavaScript carries it as string literals. The hole expressions stay
//! ordinary code of the macro: they are type checked, and a quote nested in a
//! hole is lowered by the next pass.
//!
//! Hygiene, as far as syntax decides it: a name the quote uses that the
//! macro's file defines at its top level is written with the module's name
//! (`encode` in `Json.res` becomes `Json.encode`), so it means the same where
//! the macro is used. Names the quote binds itself and all other names are
//! left as written and resolve at the use.

use std::collections::HashSet;

use crate::binary_ast::ast_iter::{self, AstIter};
use crate::parse_arena::{CoreTypeIdx, ExprIdx, LocIdx, ParseArena, PatIdx};
use crate::parser::ast::{
    CoreTypeDesc, ExpressionDesc, Extension, PatternDesc, Payload, StructureItem, StructureItemDesc,
};
use crate::parser::longident::Longident;
use crate::parser::module::HOLE_EXTENSION;

use super::edit::{Edit, Segment, SourceText};

/// The extension names that are quotes.
pub fn is_quote_name(name: &str) -> bool {
    matches!(name, "code" | "type" | "pat")
}

fn range(arena: &ParseArena, loc: LocIdx) -> (u32, u32) {
    let location = arena.to_location(loc);
    (
        location.loc_start.cnum.max(0) as u32,
        location.loc_end.cnum.max(0) as u32,
    )
}

/// A ReScript string literal with the value `text`.
pub fn string_literal(text: &str) -> String {
    let mut out = String::with_capacity(text.len() + 2);
    out.push('"');
    for ch in text.chars() {
        match ch {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            ch if (ch as u32) < 0x20 => out.push_str(&format!("\\u{:04x}", ch as u32)),
            ch => out.push(ch),
        }
    }
    out.push('"');
    out
}

/// Names the file defines at its top level.
#[derive(Default)]
struct TopLevel {
    values: HashSet<String>,
    modules: HashSet<String>,
}

fn pattern_names(arena: &ParseArena, pat: PatIdx, out: &mut HashSet<String>) {
    let mut collector = Binders { names: out };
    collector.pat(arena, pat);
}

struct Binders<'a> {
    names: &'a mut HashSet<String>,
}

impl AstIter for Binders<'_> {
    fn pat(&mut self, arena: &ParseArena, idx: PatIdx) {
        match &arena.get_pat(idx).ppat_desc {
            PatternDesc::Ppat_var(name) => {
                self.names.insert(arena.get_string(name.txt).to_string());
            }
            PatternDesc::Ppat_alias(_, name) => {
                self.names.insert(arena.get_string(name.txt).to_string());
                ast_iter::walk_pat(self, arena, idx);
            }
            // A hole in a pattern is filled when the macro runs.
            PatternDesc::Ppat_extension(_) => {}
            _ => ast_iter::walk_pat(self, arena, idx),
        }
    }
    // Only binders: do not descend into expressions and types of a pattern.
    fn expr(&mut self, _arena: &ParseArena, _idx: ExprIdx) {}
    fn typ(&mut self, _arena: &ParseArena, _idx: CoreTypeIdx) {}
}

fn top_level(arena: &ParseArena, structure: &[StructureItem]) -> TopLevel {
    let mut names = TopLevel::default();
    for item in structure {
        match &item.pstr_desc {
            StructureItemDesc::Pstr_value((_, bindings)) => {
                for binding in arena.vb_list(*bindings) {
                    pattern_names(arena, binding.pvb_pat, &mut names.values);
                }
            }
            StructureItemDesc::Pstr_primitive(description) => {
                names
                    .values
                    .insert(arena.get_string(description.pval_name.txt).to_string());
            }
            StructureItemDesc::Pstr_module(binding) => {
                names
                    .modules
                    .insert(arena.get_string(binding.pmb_name.txt).to_string());
            }
            StructureItemDesc::Pstr_recmodule(bindings) => {
                for binding in bindings.iter() {
                    names
                        .modules
                        .insert(arena.get_string(binding.pmb_name.txt).to_string());
                }
            }
            _ => {}
        }
    }
    names
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum HoleKind {
    Code,
    Type,
    Pat,
    Item,
}

struct Hole {
    /// The hole, `${...}`.
    outer: (u32, u32),
    /// The expression inside it.
    inner: (u32, u32),
    kind: HoleKind,
}

/// What a walk over a quote's payload finds.
struct QuoteScan<'a> {
    holes: Vec<Hole>,
    /// Value identifiers the quote uses: range and name, for a plain name;
    /// range and root module, for a path.
    value_uses: Vec<((u32, u32), String)>,
    module_roots: Vec<((u32, u32), String)>,
    bound: HashSet<String>,
    /// Expressions that are a structure item of the quote on their own.
    item_exprs: &'a HashSet<ExprIdx>,
}

fn hole_inner(arena: &ParseArena, extension: &Extension) -> Option<(u32, u32)> {
    if arena.get_string(extension.0.txt) != HOLE_EXTENSION {
        return None;
    }
    let Payload::PStr(items) = &extension.1 else {
        return None;
    };
    let [item] = items.as_slice() else {
        return None;
    };
    let StructureItemDesc::Pstr_eval(eval) = &item.pstr_desc else {
        return None;
    };
    Some(range(arena, arena.get_expr(eval.0).pexp_loc))
}

impl AstIter for QuoteScan<'_> {
    fn expr(&mut self, arena: &ParseArena, idx: ExprIdx) {
        let expr = arena.get_expr(idx);
        match &expr.pexp_desc {
            ExpressionDesc::Pexp_extension(extension) => {
                if let Some(inner) = hole_inner(arena, extension) {
                    let kind = if self.item_exprs.contains(&idx) {
                        HoleKind::Item
                    } else {
                        HoleKind::Code
                    };
                    self.holes.push(Hole {
                        outer: range(arena, expr.pexp_loc),
                        inner,
                        kind,
                    });
                    return;
                }
                // A quote inside a quote is the inner macro's business.
                if is_quote_name(arena.get_string(extension.0.txt)) {
                    return;
                }
                ast_iter::walk_expr(self, arena, idx);
            }
            ExpressionDesc::Pexp_ident(lid) => match arena.get_longident(lid.txt) {
                Longident::Lident(name) => {
                    self.value_uses.push((
                        range(arena, expr.pexp_loc),
                        arena.get_string(*name).to_string(),
                    ));
                }
                longident => {
                    if let Some(root) = longident.flatten_idx().first() {
                        self.module_roots.push((
                            range(arena, expr.pexp_loc),
                            arena.get_string(*root).to_string(),
                        ));
                    }
                }
            },
            _ => ast_iter::walk_expr(self, arena, idx),
        }
    }

    fn pat(&mut self, arena: &ParseArena, idx: PatIdx) {
        let pat = arena.get_pat(idx);
        match &pat.ppat_desc {
            PatternDesc::Ppat_extension(extension) => {
                if let Some(inner) = hole_inner(arena, extension) {
                    self.holes.push(Hole {
                        outer: range(arena, pat.ppat_loc),
                        inner,
                        kind: HoleKind::Pat,
                    });
                }
            }
            PatternDesc::Ppat_var(name) => {
                self.bound.insert(arena.get_string(name.txt).to_string());
            }
            PatternDesc::Ppat_alias(_, name) => {
                self.bound.insert(arena.get_string(name.txt).to_string());
                ast_iter::walk_pat(self, arena, idx);
            }
            _ => ast_iter::walk_pat(self, arena, idx),
        }
    }

    fn typ(&mut self, arena: &ParseArena, idx: CoreTypeIdx) {
        let typ = arena.get_core_type(idx);
        if let CoreTypeDesc::Ptyp_extension(extension) = &typ.ptyp_desc
            && let Some(inner) = hole_inner(arena, extension)
        {
            self.holes.push(Hole {
                outer: range(arena, typ.ptyp_loc),
                inner,
                kind: HoleKind::Type,
            });
            return;
        }
        ast_iter::walk_typ(self, arena, idx);
    }
}

/// Finds the quotes of a file that are not inside another quote.
struct QuoteFinder<'a> {
    text: &'a SourceText,
    module_name: &'a str,
    top_level: &'a TopLevel,
    edits: Vec<Edit>,
}

impl QuoteFinder<'_> {
    fn lower(&mut self, arena: &ParseArena, loc: LocIdx, extension: &Extension) {
        let name = arena.get_string(extension.0.txt);
        let (start, end) = range(arena, loc);
        // The payload is what is between the parentheses of `%code(...)`.
        let (_, id_end) = range(arena, extension.0.loc);
        if end <= id_end + 1 || self.text.slice(id_end, id_end + 1) != "(" {
            // `%code` without a payload: the type checker reports it.
            return;
        }
        let payload = (id_end + 1, end - 1);

        let mut item_exprs = HashSet::new();
        let mut single_expression = false;
        if let Payload::PStr(items) = &extension.1 {
            for item in items.iter() {
                if let StructureItemDesc::Pstr_eval(eval) = &item.pstr_desc {
                    item_exprs.insert(eval.0);
                }
            }
            single_expression = items.len() == 1 && item_exprs.len() == 1;
        }
        // The only item of `%code(${e})` is an expression hole, not a
        // declaration hole.
        let no_items = HashSet::new();
        let mut scan = QuoteScan {
            holes: Vec::new(),
            value_uses: Vec::new(),
            module_roots: Vec::new(),
            bound: HashSet::new(),
            item_exprs: if single_expression { &no_items } else { &item_exprs },
        };
        scan.payload(arena, &extension.1);

        let function = match name {
            "type" => "__quoteType",
            "pat" => "__quotePat",
            _ if single_expression => "__quoteCode",
            _ => "__quoteDecls",
        };

        // Qualify the names the file defines.
        let mut substitutions: Vec<((u32, u32), String)> = Vec::new();
        for (at, used) in &scan.value_uses {
            if self.top_level.values.contains(used) && !scan.bound.contains(used) {
                substitutions.push((*at, format!("{}.{}", self.module_name, used)));
            }
        }
        for (at, root) in &scan.module_roots {
            if self.top_level.modules.contains(root) {
                substitutions.push((
                    *at,
                    format!("{}.{}", self.module_name, self.text.slice(at.0, at.1)),
                ));
            }
        }

        scan.holes.sort_by_key(|hole| hole.outer.0);
        substitutions.sort_by_key(|(at, _)| at.0);
        let in_hole = |at: (u32, u32)| {
            scan.holes
                .iter()
                .any(|hole| at.0 >= hole.outer.0 && at.1 <= hole.outer.1)
        };
        substitutions.retain(|(at, _)| at.0 >= payload.0 && at.1 <= payload.1 && !in_hole(*at));

        // The text between two holes, with the substitutions applied.
        let piece = |from: u32, to: u32| -> String {
            let mut out = String::new();
            let mut cursor = from;
            for (at, replacement) in &substitutions {
                if at.0 < cursor || at.1 > to {
                    continue;
                }
                out.push_str(self.text.slice(cursor, at.0));
                out.push_str(replacement);
                cursor = at.1;
            }
            out.push_str(self.text.slice(cursor, to));
            out
        };

        let mut pieces = Vec::with_capacity(scan.holes.len() + 1);
        let mut cursor = payload.0;
        for hole in &scan.holes {
            pieces.push(string_literal(&piece(cursor, hole.outer.0)));
            cursor = hole.outer.1;
        }
        pieces.push(string_literal(&piece(cursor, payload.1)));

        let mut segments = vec![Segment::Text(format!(
            "(Macro.{function}([{}], [",
            pieces.join(", ")
        ))];
        for (index, hole) in scan.holes.iter().enumerate() {
            let wrapper = match hole.kind {
                HoleKind::Code => "__holeCode",
                HoleKind::Type => "__holeType",
                HoleKind::Pat => "__holePat",
                HoleKind::Item => "__holeItem",
            };
            segments.push(Segment::Text(format!(
                "{}Macro.{wrapper}(",
                if index == 0 { "" } else { ", " }
            )));
            segments.push(Segment::Copy(hole.inner.0, hole.inner.1));
            segments.push(Segment::Text(")".into()));
        }
        segments.push(Segment::Text("]))".into()));
        self.edits.push(Edit {
            start,
            end,
            segments,
        });
    }
}

impl AstIter for QuoteFinder<'_> {
    fn expr(&mut self, arena: &ParseArena, idx: ExprIdx) {
        let expr = arena.get_expr(idx);
        if let ExpressionDesc::Pexp_extension(extension) = &expr.pexp_desc
            && is_quote_name(arena.get_string(extension.0.txt))
        {
            self.lower(arena, expr.pexp_loc, extension);
            return;
        }
        ast_iter::walk_expr(self, arena, idx);
    }
}

/// The edits that lower the outermost quotes of `structure`.
pub fn lowering_edits(
    arena: &ParseArena,
    structure: &[StructureItem],
    text: &SourceText,
    module_name: &str,
) -> Vec<Edit> {
    let top_level = top_level(arena, structure);
    let mut finder = QuoteFinder {
        text,
        module_name,
        top_level: &top_level,
        edits: Vec::new(),
    };
    ast_iter::walk_structure(&mut finder, arena, structure);
    finder.edits
}
