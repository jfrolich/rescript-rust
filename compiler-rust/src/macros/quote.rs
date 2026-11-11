//! Lowering of quotes in a macro's own file.
//!
//! `%code(JSON.Encode.string(${value}))` becomes
//!
//! ```text
//! Macro.__quoteCode(
//!   [[("JSON.Encode.string(", 9, 20)], [(")", 9, 48)]],
//!   [Macro.__holeCode(value)],
//!   "Json.res",
//! )
//! ```
//!
//! The pieces are the quote's source text between the holes, so a quote is
//! parsed and reported on where it is written and the macro's compiled
//! JavaScript carries it as string literals. Each piece comes with the line
//! and column it has in the macro's file: the code a macro returns keeps
//! them, and an error in generated code says which line of which quote it
//! is in. The hole expressions stay ordinary code of the macro: they are
//! type checked, and a quote nested in a hole is lowered by the next pass.
//!
//! A splice hole `${...items}` stands for any number of items of a list:
//! the arguments of a call, the items of an array or a tuple, the fields of
//! a record, the cases of a switch. It is lowered to `Macro.__spliceItems`,
//! `Macro.__spliceEntries` or `Macro.__spliceCases` by the list it is in.
//!
//! Hygiene, as far as syntax decides it: a name the quote uses that the
//! macro's file defines at its top level is written with the module's name
//! (`encode` in `Json.res` becomes `Json.encode`), so it means the same where
//! the macro is used. Names the quote binds itself and all other names are
//! left as written and resolve at the use.

use std::collections::{HashMap, HashSet};

use crate::binary_ast::ast_iter::{self, AstIter};
use crate::parse_arena::{CoreTypeIdx, ExprIdx, LocIdx, ParseArena, PatIdx};
use crate::parser::ast::{
    ArgLabel, CoreTypeDesc, ExpressionDesc, Extension, PatternDesc, Payload, StructureItem,
    StructureItemDesc,
};
use crate::parser::longident::Longident;
use crate::parser::module::{HOLE_EXTENSION, SPLICE_HOLE_EXTENSION};

use super::edit::{Edit, LineTable, Segment, SourceText};

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

/// The list a splice hole `${...items}` stands in.
#[derive(Clone, Copy, PartialEq, Eq)]
enum SplicePlace {
    /// Arguments of a call or a constructor, items of an array or a tuple.
    Items,
    /// Fields of a record.
    Entries,
    /// Cases of a switch.
    Cases,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum HoleKind {
    Code,
    Type,
    Pat,
    Item,
    Splice(SplicePlace),
    /// A splice hole where no list is written. It is left in the lowered
    /// code, where [`stray_splice`] finds it.
    SpliceOutOfPlace,
}

/// The message for a splice hole that is not in a list of a quote.
pub const SPLICE_OUT_OF_PLACE: &str = "A splice `${...items}` stands for the items of a list in a quote: the arguments of a call, the items of an array or a tuple, the fields of a record, or the cases of a switch.";

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
    /// The splice holes that are an item of a list, with the list.
    splice_places: HashMap<ExprIdx, SplicePlace>,
}

fn is_splice(arena: &ParseArena, extension: &Extension) -> bool {
    arena.get_string(extension.0.txt) == SPLICE_HOLE_EXTENSION
}

fn is_splice_expr(arena: &ParseArena, idx: ExprIdx) -> bool {
    matches!(&arena.get_expr(idx).pexp_desc, ExpressionDesc::Pexp_extension(extension) if is_splice(arena, extension))
}

/// Whether `idx` is an operator, as the function of `a + b` is.
fn is_operator(arena: &ParseArena, idx: ExprIdx) -> bool {
    let ExpressionDesc::Pexp_ident(lid) = &arena.get_expr(idx).pexp_desc else {
        return false;
    };
    match arena.get_longident(lid.txt) {
        Longident::Lident(name) => !arena
            .get_string(*name)
            .starts_with(|ch: char| ch.is_alphabetic() || ch == '_'),
        _ => false,
    }
}

/// The range of the expression in a hole or a splice hole.
fn hole_inner(arena: &ParseArena, extension: &Extension) -> Option<(u32, u32)> {
    let name = arena.get_string(extension.0.txt);
    if name != HOLE_EXTENSION && name != SPLICE_HOLE_EXTENSION {
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

impl QuoteScan<'_> {
    /// Record the splice holes that are an item of a list of `idx`.
    fn find_splice_places(&mut self, arena: &ParseArena, idx: ExprIdx) {
        let mut place = |item: ExprIdx, place: SplicePlace| {
            if is_splice_expr(arena, item) {
                self.splice_places.insert(item, place);
            }
        };
        match &arena.get_expr(idx).pexp_desc {
            // `f(a, b)`, and not `a + b`, which is an application as well.
            ExpressionDesc::Pexp_apply(apply) if !is_operator(arena, apply.funct) => {
                for (label, arg) in arena.apply_args(apply.args) {
                    if matches!(label, ArgLabel::Nolabel) {
                        place(*arg, SplicePlace::Items);
                    }
                }
            }
            ExpressionDesc::Pexp_tuple(items) | ExpressionDesc::Pexp_array(items) => {
                for item in arena.expr_list(*items) {
                    place(*item, SplicePlace::Items);
                }
            }
            ExpressionDesc::Pexp_construct(_, args) => {
                for arg in arena.expr_list(args.txt) {
                    place(*arg, SplicePlace::Items);
                }
            }
            ExpressionDesc::Pexp_variant(inner) => {
                for arg in arena.expr_list(inner.1.txt) {
                    place(*arg, SplicePlace::Items);
                }
            }
            ExpressionDesc::Pexp_record(inner) => {
                for field in arena.expr_field_list(inner.0) {
                    place(field.expr, SplicePlace::Entries);
                }
            }
            ExpressionDesc::Pexp_match(inner) => {
                for case in arena.case_list(inner.1) {
                    // The parser makes a case without a bar of a splice hole
                    // only: `| _ => ${...cases}` is not one.
                    if case.pc_bar.is_none() {
                        place(case.pc_rhs, SplicePlace::Cases);
                    }
                }
            }
            _ => {}
        }
    }
}

impl AstIter for QuoteScan<'_> {
    fn expr(&mut self, arena: &ParseArena, idx: ExprIdx) {
        self.find_splice_places(arena, idx);
        let expr = arena.get_expr(idx);
        match &expr.pexp_desc {
            ExpressionDesc::Pexp_extension(extension) => {
                if let Some(inner) = hole_inner(arena, extension) {
                    let kind = if is_splice(arena, extension) {
                        match self.splice_places.get(&idx) {
                            Some(place) => HoleKind::Splice(*place),
                            None => HoleKind::SpliceOutOfPlace,
                        }
                    } else if self.item_exprs.contains(&idx) {
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
                        kind: if is_splice(arena, extension) {
                            HoleKind::SpliceOutOfPlace
                        } else {
                            HoleKind::Pat
                        },
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
                kind: if is_splice(arena, extension) {
                    HoleKind::SpliceOutOfPlace
                } else {
                    HoleKind::Type
                },
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
    /// The name of the file, as an error names it.
    file: &'a str,
    /// Lines of the file as written.
    lines: &'a LineTable,
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
            item_exprs: if single_expression {
                &no_items
            } else {
                &item_exprs
            },
            splice_places: HashMap::new(),
        };
        scan.payload(arena, &extension.1);

        let function = match name {
            "type" => "__quoteType",
            "pat" => "__quotePat",
            _ if single_expression => "__quoteCode",
            _ => "__quoteDecls",
        };

        // Qualify the names the file defines: where the module's name goes
        // in front.
        let mut substitutions: Vec<(u32, u32)> = Vec::new();
        for (at, used) in &scan.value_uses {
            if self.top_level.values.contains(used) && !scan.bound.contains(used) {
                substitutions.push(*at);
            }
        }
        for (at, root) in &scan.module_roots {
            if self.top_level.modules.contains(root) {
                substitutions.push(*at);
            }
        }

        scan.holes.sort_by_key(|hole| hole.outer.0);
        // The comma after a splice hole of items is the hole's: the hole
        // writes it when it has items, so that none leave no comma behind.
        let mut trailing_comma = vec![false; scan.holes.len()];
        for (hole, trailing) in scan.holes.iter_mut().zip(&mut trailing_comma) {
            if !matches!(
                hole.kind,
                HoleKind::Splice(SplicePlace::Items | SplicePlace::Entries)
            ) {
                continue;
            }
            let rest = self.text.slice(hole.outer.1, payload.1);
            let blank = rest.chars().take_while(|ch| ch.is_whitespace()).count() as u32;
            if rest.chars().nth(blank as usize) == Some(',') {
                hole.outer.1 += blank + 1;
                *trailing = true;
            }
        }
        substitutions.sort_by_key(|at| at.0);
        let in_hole = |at: (u32, u32)| {
            scan.holes
                .iter()
                .any(|hole| at.0 >= hole.outer.0 && at.1 <= hole.outer.1)
        };
        substitutions.retain(|at| at.0 >= payload.0 && at.1 <= payload.1 && !in_hole(*at));

        // The text between two holes, as the parts of it that are text of
        // the file, each with its line and column there, and the names that
        // were qualified in between.
        let fragment = |from: u32, to: u32| -> String {
            if from >= to {
                return String::new();
            }
            // Text a macro generated has no place in the file.
            let (line, column) = match self.text.generated(from) {
                Some(_) => (0, 0),
                None => {
                    let offset = self.text.origin(from);
                    let (line, line_start) = self.lines.line_of(offset);
                    (line, offset - line_start)
                }
            };
            format!(
                "({}, {line}, {column})",
                string_literal(self.text.slice(from, to))
            )
        };
        let piece = |from: u32, to: u32| -> String {
            let mut fragments = Vec::new();
            let mut cursor = from;
            let qualifier = format!(
                "({}, 0, 0)",
                string_literal(&format!("{}.", self.module_name))
            );
            for at in &substitutions {
                if at.0 < cursor || at.1 > to {
                    continue;
                }
                fragments.push(fragment(cursor, at.0));
                fragments.push(qualifier.clone());
                cursor = at.0;
            }
            fragments.push(fragment(cursor, to));
            fragments.retain(|fragment| !fragment.is_empty());
            format!("[{}]", fragments.join(", "))
        };

        let mut pieces = Vec::with_capacity(scan.holes.len() + 1);
        let mut cursor = payload.0;
        for hole in &scan.holes {
            pieces.push(piece(cursor, hole.outer.0));
            cursor = hole.outer.1;
        }
        pieces.push(piece(cursor, payload.1));

        let mut segments = vec![Segment::Text(format!(
            "(Macro.{function}([{}], [",
            pieces.join(", ")
        ))];
        for (index, hole) in scan.holes.iter().enumerate() {
            let wrapper = match hole.kind {
                HoleKind::Code | HoleKind::SpliceOutOfPlace => "__holeCode",
                HoleKind::Type => "__holeType",
                HoleKind::Pat => "__holePat",
                HoleKind::Item => "__holeItem",
                HoleKind::Splice(SplicePlace::Items) => "__spliceItems",
                HoleKind::Splice(SplicePlace::Entries) => "__spliceEntries",
                HoleKind::Splice(SplicePlace::Cases) => "__spliceCases",
            };
            segments.push(Segment::Text(format!(
                "{}Macro.{wrapper}(",
                if index == 0 { "" } else { ", " }
            )));
            match hole.kind {
                // The whole hole, `${...items}`, stays in the code.
                HoleKind::SpliceOutOfPlace => {
                    segments.push(Segment::Copy(hole.outer.0, hole.outer.1));
                }
                _ => segments.push(Segment::Copy(hole.inner.0, hole.inner.1)),
            }
            segments.push(Segment::Text(
                match hole.kind {
                    HoleKind::Splice(SplicePlace::Items | SplicePlace::Entries) => {
                        format!(", {})", trailing_comma[index])
                    }
                    _ => ")".into(),
                },
            ));
        }
        segments.push(Segment::Text(format!("], {}))", string_literal(self.file))));
        self.edits.push(Edit {
            start,
            end,
            segments,
            internal: true,
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

/// The edits that lower the outermost quotes of `structure`. `original` is
/// the file as written and `filename` its name.
pub fn lowering_edits(
    arena: &ParseArena,
    structure: &[StructureItem],
    text: &SourceText,
    original: &str,
    filename: &str,
    module_name: &str,
) -> Vec<Edit> {
    let top_level = top_level(arena, structure);
    let lines = LineTable::new(original);
    // The name without its directories: the compiled macro is the same
    // wherever the project is checked out.
    let file = filename.rsplit(['/', '\\']).next().unwrap_or(filename);
    let mut finder = QuoteFinder {
        text,
        module_name,
        file,
        lines: &lines,
        top_level: &top_level,
        edits: Vec::new(),
    };
    ast_iter::walk_structure(&mut finder, arena, structure);
    finder.edits
}

/// Finds a splice hole that no quote lowered.
struct StraySplice {
    found: Option<(u32, u32)>,
}

impl AstIter for StraySplice {
    fn expr(&mut self, arena: &ParseArena, idx: ExprIdx) {
        let expr = arena.get_expr(idx);
        if let ExpressionDesc::Pexp_extension(extension) = &expr.pexp_desc
            && is_splice(arena, extension)
        {
            self.found.get_or_insert(range(arena, expr.pexp_loc));
            return;
        }
        ast_iter::walk_expr(self, arena, idx);
    }

    fn pat(&mut self, arena: &ParseArena, idx: PatIdx) {
        let pat = arena.get_pat(idx);
        if let PatternDesc::Ppat_extension(extension) = &pat.ppat_desc
            && is_splice(arena, extension)
        {
            self.found.get_or_insert(range(arena, pat.ppat_loc));
            return;
        }
        ast_iter::walk_pat(self, arena, idx);
    }

    fn typ(&mut self, arena: &ParseArena, idx: CoreTypeIdx) {
        let typ = arena.get_core_type(idx);
        if let CoreTypeDesc::Ptyp_extension(extension) = &typ.ptyp_desc
            && is_splice(arena, extension)
        {
            self.found.get_or_insert(range(arena, typ.ptyp_loc));
            return;
        }
        ast_iter::walk_typ(self, arena, idx);
    }
}

/// The first splice hole `${...items}` of `structure` that is not in a list
/// of a quote, once the quotes are lowered: see [`SPLICE_OUT_OF_PLACE`].
pub fn stray_splice(arena: &ParseArena, structure: &[StructureItem]) -> Option<(u32, u32)> {
    let mut finder = StraySplice { found: None };
    ast_iter::walk_structure(&mut finder, arena, structure);
    finder.found
}
