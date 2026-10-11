//! ReScript AST printer - Doc-based implementation.
//!
//! This is a 1:1 port of OCaml's `res_printer.ml`, using Doc structures
//! for pretty-printing instead of direct string output.

use crate::location::Location as FullLocation;
use crate::parse_arena::{
    CoreTypeIdx, ExprIdx, LocIdx, ModExprIdx, ModTypeIdx, ParseArena, PatIdx,
};
use crate::parser::ast::*;
use crate::parser::comment::Comment;
use crate::parser::comment_table::{CommentTable, PosRange, walk_signature, walk_structure};
use crate::parser::doc::Doc;
use crate::parser::longident::Longident;
use crate::parser::token::Token;
// (HashMap import removed - unused)

// ============================================================================
// Printer State
// ============================================================================

#[derive(Debug, Clone)]
struct PendingInlineRecordDefinitions {
    external_name: String,
    definitions: Vec<TypeDeclaration>,
}

/// Printer state for tracking custom layout depth and inline record definitions.
///
/// This is used to limit the depth of nested custom layouts to avoid
/// exponential blowup in layout computation.
///
/// It also holds optional inline record definitions for printing nested record
/// types inline (e.g., `type t = { field: { nested: int } }` instead of
/// generating separate type declarations).
#[derive(Debug, Clone, Default)]
pub struct PrinterState {
    /// Current depth of nested custom layouts.
    custom_layout: i32,
    /// Inline record definitions for printing nested records inline.
    /// When printing a type constructor that references one of these definitions,
    /// we print the record definition inline instead of as a type reference.
    inline_record_definitions: Option<Vec<TypeDeclaration>>,
    pending_inline_record_definitions: Option<PendingInlineRecordDefinitions>,
}

impl PrinterState {
    /// Maximum depth of nested custom layouts before forcing breaks.
    const CUSTOM_LAYOUT_THRESHOLD: i32 = 2;

    /// Create a new printer state.
    pub fn init() -> Self {
        Self {
            custom_layout: 0,
            inline_record_definitions: None,
            pending_inline_record_definitions: None,
        }
    }

    /// Create a new state with incremented custom layout depth.
    pub fn next_custom_layout(&self) -> Self {
        Self {
            custom_layout: self.custom_layout + 1,
            inline_record_definitions: self.inline_record_definitions.clone(),
            pending_inline_record_definitions: self.pending_inline_record_definitions.clone(),
        }
    }

    /// Check if we should break callbacks due to custom layout depth.
    pub fn should_break_callback(&self) -> bool {
        self.custom_layout > Self::CUSTOM_LAYOUT_THRESHOLD
    }

    /// Create a new state with inline record definitions.
    pub fn with_inline_record_definitions(
        &self,
        inline_record_definitions: Vec<TypeDeclaration>,
    ) -> Self {
        Self {
            custom_layout: self.custom_layout,
            inline_record_definitions: Some(inline_record_definitions),
            pending_inline_record_definitions: self.pending_inline_record_definitions.clone(),
        }
    }

    /// Find an inline record definition by name.
    pub fn find_inline_record_definition(
        &self,
        arena: &ParseArena,
        name: &str,
    ) -> Option<&TypeDeclaration> {
        self.inline_record_definitions.as_ref().and_then(|defs| {
            defs.iter()
                .find(|decl| arena.get_string(decl.ptype_name.txt) == name)
        })
    }

    fn clear_pending_inline_record_definitions(&mut self) {
        self.pending_inline_record_definitions = None;
    }
}

// ============================================================================
// Identifier Classification
// ============================================================================

/// Classification of identifier style for printing.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum IdentifierStyle {
    /// Uppercase exotic identifier (starts with backslash)
    UppercaseExoticIdent,
    /// Exotic identifier (needs escaping)
    ExoticIdent,
    /// Normal identifier (can be printed as-is)
    NormalIdent,
}

/// Classify an identifier to determine if it needs escaping.
///
/// # Arguments
/// * `txt` - The identifier text
/// * `allow_uident` - Whether to allow uppercase identifiers
/// * `allow_hyphen` - Whether to allow hyphens (for JSX tags)
pub fn classify_ident_content(
    txt: &str,
    allow_uident: bool,
    allow_hyphen: bool,
) -> IdentifierStyle {
    // Keywords always need escaping
    if Token::is_keyword_txt(txt) {
        return IdentifierStyle::ExoticIdent;
    }

    let bytes = txt.as_bytes();
    let len = bytes.len();

    // res_printer.ml:430-431: `loop 0` on an empty string is `NormalIdent`.
    if len == 0 {
        return IdentifierStyle::NormalIdent;
    }

    // Check first character
    match bytes[0] {
        b'\\' => return IdentifierStyle::UppercaseExoticIdent,
        b'A'..=b'Z' if !allow_uident => return IdentifierStyle::ExoticIdent,
        b'a'..=b'z' | b'_' | b'A'..=b'Z' => {}
        _ => return IdentifierStyle::ExoticIdent,
    }

    // Check remaining characters
    for &c in &bytes[1..] {
        match c {
            b'A'..=b'Z' | b'a'..=b'z' | b'0'..=b'9' | b'\'' | b'_' => {}
            b'-' if allow_hyphen => {}
            _ => return IdentifierStyle::ExoticIdent,
        }
    }

    IdentifierStyle::NormalIdent
}

/// Print an identifier, escaping if necessary.
///
/// # Arguments
/// * `txt` - The identifier text
/// * `allow_uident` - Whether to allow uppercase identifiers
/// * `allow_hyphen` - Whether to allow hyphens
pub fn print_ident_like(txt: &str, allow_uident: bool, allow_hyphen: bool) -> Doc {
    match classify_ident_content(txt, allow_uident, allow_hyphen) {
        IdentifierStyle::ExoticIdent => {
            Doc::concat(vec![Doc::text("\\\""), Doc::text(txt), Doc::text("\"")])
        }
        IdentifierStyle::UppercaseExoticIdent | IdentifierStyle::NormalIdent => Doc::text(txt),
    }
}

/// Print an identifier with default settings (no uppercase, no hyphen).
pub fn print_ident(txt: &str) -> Doc {
    print_ident_like(txt, false, false)
}

// ============================================================================
// Longident Printing
// ============================================================================

/// Helper to flatten a longident into a list of docs.
fn print_longident_aux(
    arena: &crate::parse_arena::ParseArena,
    lid: &Longident,
    accu: &mut Vec<Doc>,
) {
    match lid {
        Longident::Lident(s_idx) => {
            let s = arena.get_string(*s_idx);
            accu.push(Doc::text(s.to_string()));
        }
        Longident::Ldot(inner, s_idx) => {
            print_longident_aux(arena, inner, accu);
            let s = arena.get_string(*s_idx);
            accu.push(Doc::text(s.to_string()));
        }
        Longident::Lapply(lid1, lid2) => {
            let mut docs1 = Vec::new();
            print_longident_aux(arena, lid1, &mut docs1);
            let d1 = Doc::join(Doc::dot(), docs1);

            let mut docs2 = Vec::new();
            print_longident_aux(arena, lid2, &mut docs2);
            let d2 = Doc::join(Doc::dot(), docs2);

            accu.push(Doc::concat(vec![d1, Doc::lparen(), d2, Doc::rparen()]));
        }
    }
}

/// Print a longident without escaping.
pub fn print_longident(arena: &crate::parse_arena::ParseArena, lid: &Longident) -> Doc {
    match lid {
        Longident::Lident(txt_idx) => {
            let txt = arena.get_string(*txt_idx);
            Doc::text(txt.to_string())
        }
        _ => {
            let mut docs = Vec::new();
            print_longident_aux(arena, lid, &mut docs);
            Doc::join(Doc::dot(), docs)
        }
    }
}

/// Print a longident with escaping for exotic identifiers.
pub fn print_lident(arena: &crate::parse_arena::ParseArena, lid: &Longident) -> Doc {
    match lid {
        Longident::Lident(txt_idx) => {
            let txt = arena.get_string(*txt_idx);
            print_ident(txt)
        }
        Longident::Ldot(path, txt_idx) => {
            // Flatten the path
            fn flat_lid(
                arena: &crate::parse_arena::ParseArena,
                lid: &Longident,
            ) -> Option<Vec<String>> {
                match lid {
                    Longident::Lident(txt_idx) => {
                        let txt = arena.get_string(*txt_idx);
                        Some(vec![txt.to_string()])
                    }
                    Longident::Ldot(inner, txt_idx) => {
                        let mut result = flat_lid(arena, inner)?;
                        let txt = arena.get_string(*txt_idx);
                        result.push(txt.to_string());
                        Some(result)
                    }
                    Longident::Lapply(_, _) => None,
                }
            }

            match flat_lid(arena, path) {
                Some(txts) => {
                    let mut docs: Vec<Doc> = txts.into_iter().map(|t| Doc::text(t)).collect();
                    let txt = arena.get_string(*txt_idx);
                    docs.push(print_ident(txt));
                    Doc::join(Doc::dot(), docs)
                }
                None => Doc::text("printLident: Longident.Lapply is not supported"),
            }
        }
        Longident::Lapply(_, _) => Doc::text("printLident: Longident.Lapply is not supported"),
    }
}

// ============================================================================
// Comment Printing
// ============================================================================

/// Trim leading/trailing spaces (not newlines) from comment text.
/// This matches OCaml's Comment.trim_spaces which only trims ' ' characters.
fn trim_spaces(s: &str) -> &str {
    let bytes = s.as_bytes();
    let len = bytes.len();
    if len == 0 {
        return s;
    }

    // Find start (skip leading spaces only)
    let mut start = 0;
    while start < len && bytes[start] == b' ' {
        start += 1;
    }

    // Find end (skip trailing spaces only)
    let mut end = len;
    while end > start && bytes[end - 1] == b' ' {
        end -= 1;
    }

    if start < end { &s[start..end] } else { "" }
}

/// Print multiline comment content with proper formatting.
/// Matches OCaml's print_multiline_comment_content behavior:
/// - For single line, wraps with /* and */
/// - For multiline, keeps first line on same line as /*, aligns * prefixed lines
fn print_multiline_comment_content(txt: &str) -> Doc {
    let lines: Vec<&str> = txt.split('\n').collect();

    match lines.len() {
        0 => Doc::text("/* */"),
        1 => {
            let trimmed = trim_spaces(lines[0]);
            Doc::concat(vec![Doc::text("/* "), Doc::text(trimmed), Doc::text(" */")])
        }
        _ => {
            let first_line = trim_spaces(lines[0]);
            let rest = &lines[1..];

            // Helper function similar to OCaml's indent_stars
            // Processes lines and returns (doc, early_exit)
            // early_exit is true if we hit a line that doesn't start with *
            fn indent_stars(lines: &[&str], txt: &str) -> (Doc, bool) {
                let mut docs = Vec::new();

                for (i, line) in lines.iter().enumerate() {
                    let trimmed = line.trim();
                    let is_last = i == lines.len() - 1;

                    if is_last {
                        // Last line handling
                        let trailing_space = if trimmed.is_empty() { "" } else { " " };
                        docs.push(Doc::hard_line());
                        docs.push(Doc::text(format!(" {}{}", trimmed, trailing_space)));
                    } else if !trimmed.is_empty() && trimmed.starts_with('*') {
                        // Star-prefixed line
                        docs.push(Doc::hard_line());
                        docs.push(Doc::text(format!(" {}", trimmed)));
                    } else {
                        // Non-star line: bail out and return original content
                        let trailing_space = if txt.ends_with(' ') {
                            Doc::space()
                        } else {
                            Doc::nil()
                        };
                        let content = trim_spaces(txt);
                        return (Doc::concat(vec![Doc::text(content), trailing_space]), true);
                    }
                }

                (Doc::concat(docs), false)
            }

            let (indent_doc, early_exit) = indent_stars(rest, txt);

            let mut docs = vec![Doc::text("/*")];

            // Add space before first line if not empty and not just "*"
            if !first_line.is_empty() && first_line != "*" {
                docs.push(Doc::space());
            }

            if early_exit {
                // Early exit case: just use the returned doc (original content)
                docs.push(indent_doc);
            } else {
                // Normal case: first line + processed rest
                docs.push(Doc::text(first_line));
                docs.push(indent_doc);
            }

            docs.push(Doc::text("*/"));
            Doc::concat(docs)
        }
    }
}

/// Print a leading comment, with optional reference to next comment for spacing.
fn print_leading_comment(comment: &Comment, next_comment: Option<&Comment>) -> Doc {
    let single_line = comment.is_single_line();
    let content = if single_line {
        Doc::text(format!("//{}", comment.txt()))
    } else {
        print_multiline_comment_content(comment.txt())
    };

    let separator = {
        let mut parts = Vec::new();

        if single_line {
            parts.push(Doc::hard_line());
            parts.push(Doc::break_parent());
        }

        if let Some(next) = next_comment {
            let next_loc = next.loc();
            let curr_loc = comment.loc();
            let diff = next_loc.loc_start.line as i32 - curr_loc.loc_end.line as i32;
            let next_single_line = next.is_single_line();

            if single_line && next_single_line {
                if diff > 1 {
                    parts.push(Doc::hard_line());
                }
            } else if single_line && !next_single_line {
                if diff > 1 {
                    parts.push(Doc::hard_line());
                }
            } else if diff > 1 {
                parts.push(Doc::hard_line());
                parts.push(Doc::hard_line());
            } else if diff == 1 {
                parts.push(Doc::hard_line());
            } else {
                parts.push(Doc::space());
            }
        }

        Doc::concat(parts)
    };

    Doc::concat(vec![content, separator])
}

/// Print a trailing comment.
fn print_trailing_comment(
    prev_loc: &FullLocation,
    node_loc: &FullLocation,
    comment: &Comment,
) -> Doc {
    let single_line = comment.is_single_line();
    let content = if single_line {
        Doc::text(format!("//{}", comment.txt()))
    } else {
        print_multiline_comment_content(comment.txt())
    };

    let cmt_start = &comment.loc().loc_start;
    let diff = cmt_start.line as i32 - prev_loc.loc_end.line as i32;
    let is_below = comment.loc().loc_start.line > node_loc.loc_end.line;

    if diff > 0 || is_below {
        Doc::concat(vec![
            Doc::break_parent(),
            Doc::line_suffix(Doc::concat(vec![
                Doc::hard_line(),
                if diff > 1 {
                    Doc::hard_line()
                } else {
                    Doc::nil()
                },
                content,
            ])),
        ])
    } else if !single_line {
        Doc::concat(vec![Doc::space(), content])
    } else {
        Doc::line_suffix(Doc::concat(vec![Doc::space(), content]))
    }
}

/// Print leading comments for a node (takes comments directly).
fn print_leading_comments_with(node: Doc, comments: Vec<Comment>, full_loc: &FullLocation) -> Doc {
    if comments.is_empty() {
        return node;
    }

    let mut acc = Vec::new();
    let len = comments.len();

    for (i, comment) in comments.iter().enumerate() {
        let next_comment = if i + 1 < len {
            Some(&comments[i + 1])
        } else {
            None
        };
        acc.push(print_leading_comment(comment, next_comment));
    }

    // Calculate separator based on last comment
    if let Some(last_comment) = comments.last() {
        let diff = full_loc.loc_start.line as i32 - last_comment.loc().loc_end.line as i32;
        let separator = if last_comment.is_single_line() {
            if diff > 1 {
                Doc::hard_line()
            } else {
                Doc::nil()
            }
        } else if diff == 0 {
            Doc::space()
        } else if diff > 1 {
            Doc::concat(vec![Doc::hard_line(), Doc::hard_line()])
        } else {
            Doc::hard_line()
        };

        acc.push(separator);
    }

    acc.push(node);
    Doc::group(Doc::concat(acc))
}

/// Print trailing comments for a node (takes comments directly).
fn print_trailing_comments_with(node: Doc, comments: Vec<Comment>, full_loc: &FullLocation) -> Doc {
    if comments.is_empty() {
        return node;
    }

    let mut acc = Vec::new();
    let mut prev_loc = full_loc.clone();

    for comment in &comments {
        acc.push(print_trailing_comment(&prev_loc, full_loc, comment));
        prev_loc = comment.loc().clone();
    }

    Doc::concat(vec![node, Doc::concat(acc)])
}

/// Print a node with its leading and trailing comments.
/// Uses position-based fallback when LocIdx lookup fails.
pub fn print_comments(
    doc: Doc,
    cmt_tbl: &mut CommentTable,
    loc: LocIdx,
    arena: &ParseArena,
) -> Doc {
    let full_loc = arena.to_location(loc);

    // Get leading comments with position-based fallback
    let leading_comments = cmt_tbl.remove_leading_comments_by_loc(loc, arena);
    let doc_with_leading = print_leading_comments_with(doc, leading_comments, &full_loc);

    // Get trailing comments with position-based fallback
    let trailing_comments = cmt_tbl.remove_trailing_comments_by_loc(loc, arena);
    print_trailing_comments_with(doc_with_leading, trailing_comments, &full_loc)
}

/// Print a node with its leading and trailing comments using position range directly.
/// Useful when we need to retrieve comments from a combined location without creating a new LocIdx.
fn print_comments_by_pos(
    doc: Doc,
    cmt_tbl: &mut CommentTable,
    pos_range: PosRange,
    full_loc: &FullLocation,
) -> Doc {
    // Get leading comments by position
    let leading_comments = cmt_tbl.remove_leading_comments_by_pos(pos_range);
    let doc_with_leading = print_leading_comments_with(doc, leading_comments, full_loc);

    // Get trailing comments by position
    let trailing_comments = cmt_tbl.remove_trailing_comments_by_pos(pos_range);
    print_trailing_comments_with(doc_with_leading, trailing_comments, full_loc)
}

/// res_printer.ml `print_comments_before_marker`: print `doc` with the
/// comments of the range, followed by `marker`, a token that the source writes
/// right after the range (such as `=?`). The trailing comments adjacent to the
/// range precede the marker in the source and print before it; the remaining
/// trailing comments print after it.
fn print_comments_before_marker_by_pos(
    doc: Doc,
    cmt_tbl: &mut CommentTable,
    pos_range: PosRange,
    full_loc: &FullLocation,
    marker: Doc,
) -> Doc {
    let after_marker = match cmt_tbl.trailing.remove(&pos_range) {
        None => Vec::new(),
        Some(comments) => {
            // Comment_table.partition_adjacent_trailing
            let mut before_marker = Vec::new();
            let mut after_marker = Vec::new();
            let mut prev_end_pos = full_loc.loc_end.cnum;
            for comment in comments {
                if after_marker.is_empty() && comment.prev_tok_end_pos().cnum == prev_end_pos {
                    prev_end_pos = comment.loc().loc_end.cnum;
                    before_marker.push(comment);
                } else {
                    after_marker.push(comment);
                }
            }
            cmt_tbl.trailing.insert(pos_range, before_marker);
            after_marker
        }
    };
    let doc = Doc::concat(vec![
        print_comments_by_pos(doc, cmt_tbl, pos_range, full_loc),
        marker,
    ]);
    if after_marker.is_empty() {
        doc
    } else {
        print_trailing_comments_with(doc, after_marker, full_loc)
    }
}

/// Print a node with only its leading comments.
/// Used for if-chains where we want to attach "else if" leading comments.
fn print_leading_comments(
    doc: Doc,
    cmt_tbl: &mut CommentTable,
    loc: LocIdx,
    arena: &ParseArena,
) -> Doc {
    let full_loc = arena.to_location(loc);
    let leading_comments = cmt_tbl.remove_leading_comments_by_loc(loc, arena);
    print_leading_comments_with(doc, leading_comments, &full_loc)
}

/// Get the first leading comment for a location, if any.
/// Uses position-based keys like OCaml's Location.t.
pub fn get_first_leading_comment<'a>(
    cmt_tbl: &'a CommentTable,
    loc: LocIdx,
    arena: &ParseArena,
) -> Option<&'a Comment> {
    cmt_tbl.get_first_leading_comment(loc, arena)
}

// ============================================================================
// List Printing
// ============================================================================

/// Print a list of nodes with proper comment handling and line breaks.
///
/// This function handles:
/// - Printing each node with its comments
/// - Adding appropriate separators (single or double hard lines)
/// - Creating a breakable group with optional forced breaks
pub fn print_list<'a, T, F, G>(
    get_loc: F,
    nodes: &'a [T],
    mut print: G,
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
    force_break: bool,
) -> Doc
where
    F: Fn(&'a T) -> LocIdx,
    G: FnMut(&'a T, &mut CommentTable) -> Doc,
{
    if nodes.is_empty() {
        return Doc::nil();
    }

    let mut docs = Vec::with_capacity(nodes.len() * 2);
    let mut first_loc = None;
    let mut previous_loc = None;

    for node in nodes {
        let loc = get_loc(node);

        let start_pos = match get_first_leading_comment(cmt_tbl, loc, arena) {
            Some(comment) => comment.loc().loc_start.clone(),
            None => arena.loc_start(loc).clone(),
        };

        let raw_doc = print(node, cmt_tbl);
        if matches!(raw_doc, Doc::Nil) {
            continue;
        }

        if let Some(previous_loc) = previous_loc {
            let previous_end = arena.loc_end(previous_loc);
            let separator = if start_pos.line as i32 - previous_end.line as i32 > 1 {
                Doc::concat(vec![Doc::hard_line(), Doc::hard_line()])
            } else {
                Doc::hard_line()
            };
            docs.push(separator);
        }

        docs.push(print_comments(raw_doc, cmt_tbl, loc, arena));
        first_loc.get_or_insert(loc);
        previous_loc = Some(loc);
    }

    let (Some(first_loc), Some(last_loc)) = (first_loc, previous_loc) else {
        return Doc::nil();
    };
    let should_break =
        force_break || arena.loc_start(first_loc).line != arena.loc_end(last_loc).line;

    Doc::breakable_group(Doc::concat(docs), should_break)
}

/// Print a list of nodes with index, with proper comment handling.
///
/// Similar to print_list but the print function also receives the index.
pub fn print_listi<'a, T, F, G>(
    get_loc: F,
    nodes: &'a [T],
    print: G,
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
    ignore_empty_lines: bool,
    force_break: bool,
) -> Doc
where
    F: Fn(&'a T) -> LocIdx,
    G: Fn(&'a T, &mut CommentTable, usize) -> Doc,
{
    if nodes.is_empty() {
        return Doc::nil();
    }

    let mut docs = Vec::with_capacity(nodes.len() * 2);
    let first = &nodes[0];
    let first_loc = get_loc(first);
    let first_doc = {
        let doc = print(first, cmt_tbl, 0);
        print_comments(doc, cmt_tbl, first_loc, arena)
    };
    docs.push(first_doc);

    let mut prev_loc = first_loc;

    for (i, node) in nodes[1..].iter().enumerate() {
        let loc = get_loc(node);

        // Determine separator based on line distance
        let start_pos = match get_first_leading_comment(cmt_tbl, loc, arena) {
            Some(comment) => comment.loc().loc_start.clone(),
            None => arena.loc_start(loc).clone(),
        };

        let prev_end = arena.loc_end(prev_loc);
        let sep = if start_pos.line as i32 - prev_end.line as i32 > 1 && !ignore_empty_lines {
            Doc::concat(vec![Doc::hard_line(), Doc::hard_line()])
        } else {
            Doc::line()
        };

        docs.push(sep);

        let doc = print(node, cmt_tbl, i + 1);
        let doc = print_comments(doc, cmt_tbl, loc, arena);
        docs.push(doc);

        prev_loc = loc;
    }

    // Determine if we need to force break based on span
    let last_loc = get_loc(&nodes[nodes.len() - 1]);
    let first_start = arena.loc_start(first_loc);
    let last_end = arena.loc_end(last_loc);
    let should_break = force_break || first_start.line != last_end.line;

    Doc::breakable_group(Doc::concat(docs), should_break)
}

// ============================================================================
// Comments Inside Empty Constructs
// ============================================================================

/// Print comments inside an empty construct (like empty block {}).
/// Uses position-based fallback when LocIdx lookup fails.
pub fn print_comments_inside(cmt_tbl: &mut CommentTable, loc: LocIdx, arena: &ParseArena) -> Doc {
    let force_break = arena.loc_start(loc).line != arena.loc_end(loc).line;

    // Get inside comments with position-based fallback
    let comments = cmt_tbl.remove_inside_comments_by_loc(loc, arena);
    if comments.is_empty() {
        return Doc::nil();
    }

    // Build the comment docs following OCaml's pattern:
    // For n comments, OCaml produces: soft_line, c1, line, c2, line, ..., cn
    // Where blank lines between comments produce double hard_line instead of line
    let mut acc = Vec::new();
    acc.push(Doc::soft_line());

    for (i, comment) in comments.iter().enumerate() {
        let single_line = comment.is_single_line();
        let txt = comment.txt();
        let cmt_doc = if single_line {
            Doc::text(format!("//{}", txt))
        } else {
            print_multiline_comment_content(txt)
        };

        acc.push(cmt_doc);

        if i < comments.len() - 1 {
            // Check if there's a blank line between this comment and the next
            let this_end = comment.loc().loc_end.line as u32;
            let next_start = comments[i + 1].loc().loc_start.line as u32;
            let sep = if next_start.saturating_sub(this_end) > 1 {
                // Blank line between comments - preserve it
                Doc::concat(vec![Doc::hard_line(), Doc::hard_line()])
            } else {
                Doc::line()
            };
            acc.push(sep);
        }
    }

    let cmts_doc = Doc::concat(acc);
    let indented = Doc::indent(cmts_doc.clone());

    Doc::breakable_group(
        Doc::concat(vec![Doc::if_breaks(indented, cmts_doc), Doc::soft_line()]),
        force_break,
    )
}

/// Print comments inside an empty file.
pub fn print_comments_inside_file(cmt_tbl: &mut CommentTable, _arena: &ParseArena) -> Doc {
    // Use PosRange::none() which corresponds to Location::none()
    match cmt_tbl.inside.remove(&PosRange::none()) {
        None => Doc::nil(),
        Some(comments) if comments.is_empty() => Doc::nil(),
        Some(comments) => {
            let mut acc = Vec::new();
            let len = comments.len();

            for (i, comment) in comments.iter().enumerate() {
                let next_comment = if i + 1 < len {
                    Some(&comments[i + 1])
                } else {
                    None
                };
                acc.push(print_leading_comment(comment, next_comment));
            }

            Doc::group(Doc::concat(acc))
        }
    }
}

// ============================================================================
// Polyvariant Printing
// ============================================================================

/// Check if a string is a valid numeric polyvariant number.
fn is_valid_numeric_polyvar_number(s: &str) -> bool {
    let bytes = s.as_bytes();
    let len = bytes.len();

    if len == 0 {
        return false;
    }

    let first = bytes[0];
    if first > b'9' {
        return false;
    }

    if len > 1 {
        // First digit must be > '0' (no leading zeros)
        if first <= b'0' {
            return false;
        }
        // Rest must be digits
        bytes[1..].iter().all(|&c| c >= b'0' && c <= b'9')
    } else {
        first >= b'0'
    }
}

/// Print a polyvariant identifier with proper escaping.
/// This does NOT include the leading `#` - call sites should add it.
pub fn print_poly_var_ident(txt: &str) -> Doc {
    // Numeric poly-vars don't need quotes
    if is_valid_numeric_polyvar_number(txt) {
        return Doc::text(txt);
    }

    match classify_ident_content(txt, true, false) {
        IdentifierStyle::UppercaseExoticIdent => {
            // UppercaseExoticIdent follows the \"..." format
            // OCaml just strips the leading backslash and outputs the rest
            // (which already includes the surrounding quotes)
            if txt.starts_with('\\') && txt.len() > 1 {
                Doc::text(&txt[1..])
            } else {
                // Fallback: wrap with quotes if format doesn't match
                Doc::concat(vec![Doc::text("\""), Doc::text(txt), Doc::text("\"")])
            }
        }
        IdentifierStyle::ExoticIdent => {
            Doc::concat(vec![Doc::text("\""), Doc::text(txt), Doc::text("\"")])
        }
        // res_printer.ml `print_poly_var_ident`: an empty tag is quoted.
        IdentifierStyle::NormalIdent if txt.is_empty() => {
            Doc::concat(vec![Doc::text("\""), Doc::text(txt), Doc::text("\"")])
        }
        IdentifierStyle::NormalIdent => Doc::text(txt),
    }
}

// ============================================================================
// String Printing
// ============================================================================

/// Print a string location (identifier with location).
pub fn print_string_loc(sloc: &StringLoc, cmt_tbl: &mut CommentTable, arena: &ParseArena) -> Doc {
    let doc = print_ident(arena.get_string(sloc.txt));
    print_comments(doc, cmt_tbl, sloc.loc, arena)
}

/// Print a longident location.
/// Print a longident location with escaping (for value identifiers).
pub fn print_longident_loc(
    lid: &crate::parse_arena::Located<crate::parse_arena::LidentIdx>,
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    let doc = print_lident(arena, arena.get_longident(lid.txt));
    print_comments(doc, cmt_tbl, lid.loc, arena)
}

/// Print a longident location without escaping (for module paths).
pub fn print_longident_location(
    lid: &crate::parse_arena::Located<crate::parse_arena::LidentIdx>,
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    let doc = print_longident(arena, arena.get_longident(lid.txt));
    print_comments(doc, cmt_tbl, lid.loc, arena)
}

// ============================================================================
// Parentheses and Braces Helpers
// ============================================================================

use crate::parser::parens::{self, ParenKind};
use crate::parser::parsetree_viewer;

/// Add parentheses around a Doc.
pub fn add_parens(doc: Doc) -> Doc {
    Doc::group(Doc::concat(vec![
        Doc::lparen(),
        Doc::indent(Doc::concat(vec![Doc::soft_line(), doc])),
        Doc::soft_line(),
        Doc::rparen(),
    ]))
}

/// Print an expression with braces at the given location.
pub fn print_braces(doc: Doc, expr: &Expression, braces_loc: LocIdx, arena: &ParseArena) -> Doc {
    let over_multiple_lines = arena.loc_start(braces_loc).line != arena.loc_end(braces_loc).line;

    // These expression types already have braces when printed, so just return doc as-is
    match &*parsetree_viewer::unwrap_braces(arena, expr).pexp_desc {
        ExpressionDesc::Pexp_letmodule(_)
        | ExpressionDesc::Pexp_letexception(_)
        | ExpressionDesc::Pexp_let(_)
        | ExpressionDesc::Pexp_open(_)
        | ExpressionDesc::Pexp_sequence(_, _) => {
            return doc;
        }
        _ => {}
    }

    // For other expressions, wrap in braces
    let inner_doc = if parens::braced_expr(arena, expr) {
        add_parens(doc)
    } else {
        doc
    };

    Doc::breakable_group(
        Doc::concat(vec![
            Doc::lbrace(),
            Doc::indent(Doc::concat(vec![Doc::soft_line(), inner_doc])),
            Doc::soft_line(),
            Doc::rbrace(),
        ]),
        over_multiple_lines,
    )
}

// ============================================================================
// Constant Printing
// ============================================================================

/// Print string contents with proper handling of newlines.
/// Matches OCaml's print_string_contents which splits on newlines
/// and joins with Doc.literal_line. This ensures proper position
/// tracking for multiline strings (especially in template literals).
fn print_string_contents(txt: &str) -> Doc {
    let lines: Vec<&str> = txt.split('\n').collect();
    let docs: Vec<Doc> = lines.iter().map(|line| Doc::text(*line)).collect();
    Doc::join(Doc::literal_line(), docs)
}

/// OCaml `interleave_template_parts`.
fn interleave_template_parts(sources: Vec<Doc>, values: Vec<Doc>) -> Doc {
    assert_eq!(sources.len(), values.len() + 1);
    let mut parts = Vec::with_capacity(sources.len() + values.len());
    let mut values = values.into_iter();
    for source in sources {
        parts.push(source);
        if let Some(value) = values.next() {
            parts.push(value);
        }
    }
    Doc::concat(parts)
}

/// OCaml `raw_source_fits_double_quotes`.
fn raw_source_fits_double_quotes(source: &str) -> bool {
    let bytes = source.as_bytes();
    let mut index = 0;
    while index < bytes.len() {
        match bytes[index] {
            b'"' => return false,
            b'\\' => {
                if index + 1 >= bytes.len() {
                    return false;
                }
                index += 2;
            }
            _ => index += 1,
        }
    }
    true
}

/// OCaml `print_constant`.
pub fn print_constant(c: &Constant) -> Doc {
    match c {
        Constant::Integer(s, suffix) => match suffix {
            Some(c) => Doc::text(format!("{}{}", s, c)),
            None => Doc::text(s.clone()),
        },
        Constant::String(payload) => Doc::concat(vec![
            Doc::text("\""),
            print_string_contents(payload.source()),
            Doc::text("\""),
        ]),
        Constant::Json(source) => Doc::concat(vec![
            Doc::text("json`"),
            print_string_contents(source),
            Doc::text("`"),
        ]),
        Constant::RawSource(source) => {
            let delimiter = if raw_source_fits_double_quotes(source) {
                "\""
            } else {
                "`"
            };
            Doc::concat(vec![
                Doc::text(delimiter),
                print_string_contents(source),
                Doc::text(delimiter),
            ])
        }
        Constant::Char { source, .. } => Doc::concat(vec![
            Doc::text("'"),
            Doc::text(source.clone()),
            Doc::text("'"),
        ]),
        Constant::Float(s, _) => Doc::text(s.clone()),
    }
}

// ============================================================================
// Expression Printing
// ============================================================================

/// Print an expression with its comments.
pub fn print_expression_with_comments(
    state: &PrinterState,
    expr: &Expression,
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    let doc = print_expression(state, expr, cmt_tbl, arena);
    print_comments(doc, cmt_tbl, expr.pexp_loc, arena)
}

/// res_printer.ml `print_expression_with_comments_and_parens`.
fn print_expression_with_comments_and_parens(
    state: &PrinterState,
    expr: &Expression,
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    let doc = print_expression_with_comments(state, expr, cmt_tbl, arena);
    match parens::expr(arena, expr) {
        ParenKind::Parenthesized => add_parens(doc),
        ParenKind::Braced(braces) => print_braces(doc, expr, braces, arena),
        ParenKind::Nothing => doc,
    }
}

/// Print an expression.
pub fn print_expression(
    state: &PrinterState,
    e: &Expression,
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    // res_printer.ml print_expression: a pipe chain whose braces open on an
    // earlier line than the chain breaks.
    let force_pipe_breaks = match &*e.pexp_desc {
        ExpressionDesc::Pexp_braces(braces) => {
            arena.loc_start(braces.braces_loc).line + 1
                < arena.loc_start(arena.get_expr(braces.expr).pexp_loc).line
        }
        _ => false,
    };
    // `unwrap_braces_with_attributes`: the braces nodes disappear and their
    // attributes move in front of the enclosed expression's.
    let unwrapped;
    let e: &Expression = if matches!(&*e.pexp_desc, ExpressionDesc::Pexp_braces(_)) {
        let mut attrs: Vec<Attribute> = Vec::new();
        let mut current = e;
        while let ExpressionDesc::Pexp_braces(braces) = &*current.pexp_desc {
            attrs.extend(current.pexp_attributes.iter().cloned());
            current = arena.get_expr(braces.expr);
        }
        if attrs.is_empty() {
            current
        } else {
            let mut owned = current.clone();
            attrs.extend(current.pexp_attributes.iter().cloned());
            owned.pexp_attributes = Attributes::from_vec(attrs);
            unwrapped = owned;
            &unwrapped
        }
    } else {
        e
    };
    let printed_expression = match &*e.pexp_desc {
        ExpressionDesc::Pexp_braces(braces) => {
            print_expression(state, arena.get_expr(braces.expr), cmt_tbl, arena)
        }
        // (__x) => f(a, __x, c) -----> f(a, _, c)
        ExpressionDesc::Pexp_fun(fun_inner)
            if {
                let PexpFun {
                    ref arg_label,
                    ref default,
                    ref lhs,
                    ref rhs,
                    ..
                } = **fun_inner;
                matches!(arg_label, ArgLabel::Nolabel)
                    && default.is_none()
                    && matches!(&*arena.get_pat(*lhs).ppat_desc, PatternDesc::Ppat_var(name) if arena.get_string(name.txt) == "__x")
                    && matches!(
                        &*arena.get_expr(*rhs).pexp_desc,
                        ExpressionDesc::Pexp_apply(_)
                    )
            } =>
        {
            let PexpFun { ref rhs, .. } = **fun_inner;
            // Print the inner apply with __x replaced by _ at print time
            print_underscore_apply(state, arena.get_expr(*rhs), cmt_tbl, arena)
        }
        // Function expressions
        ExpressionDesc::Pexp_fun(_) | ExpressionDesc::Pexp_newtype(_) => {
            print_arrow_expression(state, e, cmt_tbl, arena)
        }
        // Constants
        ExpressionDesc::Pexp_constant(c) => print_constant(c),
        ExpressionDesc::Pexp_template(template) => print_template_literal(
            state,
            &template.source_segments,
            &template.values,
            cmt_tbl,
            arena,
        ),
        ExpressionDesc::Pexp_tagged_template(template) => print_tagged_template_literal(
            state,
            arena.get_expr(template.tag),
            &template.raw_sources,
            &template.values,
            cmt_tbl,
            arena,
        ),
        // break / continue (leaf nodes)
        ExpressionDesc::Pexp_break => Doc::text("break"),
        ExpressionDesc::Pexp_continue => Doc::text("continue"),
        // Unit constructor: ()
        ExpressionDesc::Pexp_construct(lid, _) if arena.is_lident(lid.txt, "()") => Doc::text("()"),
        // Empty list: []
        ExpressionDesc::Pexp_construct(lid, _) if arena.is_lident(lid.txt, "[]") => {
            Doc::concat(vec![
                Doc::text("list{"),
                print_comments_inside(cmt_tbl, e.pexp_loc, arena),
                Doc::rbrace(),
            ])
        }
        // List constructor: ::
        ExpressionDesc::Pexp_construct(lid, _) if arena.is_lident(lid.txt, "::") => {
            print_list_expression(state, e, cmt_tbl, arena)
        }
        // Other constructors
        ExpressionDesc::Pexp_construct(longident_loc, args) => {
            let constr = print_longident_location(longident_loc, cmt_tbl, arena);
            let args_doc = print_expression_args(state, &args.txt, cmt_tbl, arena);
            Doc::group(Doc::concat(vec![constr, args_doc]))
        }
        // Identifier
        ExpressionDesc::Pexp_ident(path) => print_lident_path(path, cmt_tbl, arena),
        // Tuple
        ExpressionDesc::Pexp_tuple(exprs) => Doc::group(Doc::concat(vec![
            Doc::lparen(),
            Doc::indent(Doc::concat(vec![
                Doc::soft_line(),
                Doc::join(
                    Doc::concat(vec![Doc::text(","), Doc::line()]),
                    exprs
                        .iter()
                        .map(|expr_idx| {
                            let expr = arena.get_expr(*expr_idx);
                            let doc = print_expression_with_comments(state, expr, cmt_tbl, arena);
                            match parens::expr_allowing_coercion(arena, expr) {
                                ParenKind::Parenthesized => add_parens(doc),
                                ParenKind::Braced(loc) => print_braces(doc, expr, loc, arena),
                                ParenKind::Nothing => doc,
                            }
                        })
                        .collect(),
                ),
            ])),
            Doc::if_breaks(Doc::text(","), Doc::nil()),
            Doc::soft_line(),
            Doc::rparen(),
        ])),
        // Empty array
        ExpressionDesc::Pexp_array(exprs) if exprs.is_empty() => Doc::concat(vec![
            Doc::lbracket(),
            print_comments_inside(cmt_tbl, e.pexp_loc, arena),
            Doc::rbracket(),
        ]),
        // Array
        ExpressionDesc::Pexp_array(exprs) => Doc::group(Doc::concat(vec![
            Doc::lbracket(),
            Doc::indent(Doc::concat(vec![
                Doc::soft_line(),
                Doc::join(
                    Doc::concat(vec![Doc::text(","), Doc::line()]),
                    exprs
                        .iter()
                        .map(|expr_idx| {
                            let expr = arena.get_expr(*expr_idx);
                            let doc = print_expression_with_comments(state, expr, cmt_tbl, arena);
                            match parens::expr_allowing_coercion(arena, expr) {
                                ParenKind::Parenthesized => add_parens(doc),
                                ParenKind::Braced(loc) => print_braces(doc, expr, loc, arena),
                                ParenKind::Nothing => doc,
                            }
                        })
                        .collect(),
                ),
            ])),
            Doc::trailing_comma(),
            Doc::soft_line(),
            Doc::rbracket(),
        ])),
        // Variant
        ExpressionDesc::Pexp_variant(inner) => {
            let (ref label, ref args) = **inner;
            let variant_name = Doc::concat(vec![Doc::text("#"), print_poly_var_ident(label)]);
            let args_doc = print_expression_args(state, &args.txt, cmt_tbl, arena);
            Doc::group(Doc::concat(vec![variant_name, args_doc]))
        }
        // Record expression
        ExpressionDesc::Pexp_record(inner) => {
            let (ref fields, ref spread) = **inner;
            print_record_expression(
                state,
                e.pexp_loc,
                spread.as_ref().map(|idx| arena.get_expr(*idx)),
                fields,
                cmt_tbl,
                arena,
            )
        }
        // Field access: expr.field
        ExpressionDesc::Pexp_field(expr_idx, longident_loc) => {
            let expr = arena.get_expr(*expr_idx);
            let lhs = print_expression_with_comments(state, expr, cmt_tbl, arena);
            let lhs = match parens::field_expr(arena, expr) {
                ParenKind::Parenthesized => add_parens(lhs),
                ParenKind::Braced(loc) => print_braces(lhs, expr, loc, arena),
                ParenKind::Nothing => lhs,
            };
            let field = print_lident(arena, arena.get_longident(longident_loc.txt));
            let field = print_comments(field, cmt_tbl, longident_loc.loc, arena);
            Doc::concat(vec![lhs, Doc::dot(), field])
        }
        // Field set: expr.field = value
        ExpressionDesc::Pexp_setfield(inner) => {
            let (lhs, ref field, rhs) = **inner;
            print_set_field_expr(
                state,
                &e.pexp_attributes,
                arena.get_expr(lhs),
                field,
                arena.get_expr(rhs),
                e.pexp_loc,
                cmt_tbl,
                arena,
            )
        }
        // Ternary or if-then-else
        ExpressionDesc::Pexp_ternary(_) => print_ternary_expression(state, e, cmt_tbl, arena),
        ExpressionDesc::Pexp_ifthenelse(inner) => {
            let (_, _, _) = **inner;
            print_if_expression(state, e, cmt_tbl, arena)
        }
        // Sequence: expr1; expr2
        ExpressionDesc::Pexp_sequence(_, _) => {
            print_expression_block(state, true, e, cmt_tbl, arena)
        }
        // Let expression
        ExpressionDesc::Pexp_let(inner) => {
            let (_, _, _) = **inner;
            print_expression_block(state, true, e, cmt_tbl, arena)
        }
        // Spread array: Primitive_array.spread([xs, [a, b]]) -> [...xs, a, b]
        ExpressionDesc::Pexp_apply(apply_inner)
            if apply_inner.args.len() == 1
                && matches!(&apply_inner.args[0].0, ArgLabel::Nolabel)
                && matches!(
                    &*arena.get_expr(apply_inner.args[0].1).pexp_desc,
                    ExpressionDesc::Pexp_array(_)
                )
                && parsetree_viewer::is_spread_belt_array_concat(
                    arena,
                    arena.get_expr(apply_inner.funct),
                ) =>
        {
            let PexpApply { ref args, .. } = **apply_inner;
            if let ExpressionDesc::Pexp_array(sub_lists) = &*arena.get_expr(args[0].1).pexp_desc {
                print_belt_array_concat_apply(state, sub_lists, cmt_tbl, arena)
            } else {
                Doc::nil() // Should never happen due to guard
            }
        }
        // Spread list: Primitive_list.spread([xs, [a, b]]) -> list{...xs, a, b}
        ExpressionDesc::Pexp_apply(apply_inner)
            if apply_inner.args.len() == 1
                && matches!(&apply_inner.args[0].0, ArgLabel::Nolabel)
                && matches!(
                    &*arena.get_expr(apply_inner.args[0].1).pexp_desc,
                    ExpressionDesc::Pexp_array(_)
                )
                && parsetree_viewer::is_spread_belt_list_concat(
                    arena,
                    arena.get_expr(apply_inner.funct),
                ) =>
        {
            let PexpApply { ref args, .. } = **apply_inner;
            if let ExpressionDesc::Pexp_array(sub_lists) = &*arena.get_expr(args[0].1).pexp_desc {
                print_belt_list_concat_apply(state, sub_lists, cmt_tbl, arena)
            } else {
                Doc::nil() // Should never happen due to guard
            }
        }
        // Function application
        ExpressionDesc::Pexp_apply(inner) => {
            let PexpApply {
                ref funct,
                ref args,
                ref partial,
                ..
            } = **inner;
            print_pexp_apply(
                state,
                e,
                arena.get_expr(*funct),
                args,
                *partial,
                force_pipe_breaks,
                cmt_tbl,
                arena,
            )
        }
        // Constraint with pack: module(M: S)
        ExpressionDesc::Pexp_constraint(constraint_inner)
            if matches!(
                &*arena.get_expr(constraint_inner.0).pexp_desc,
                ExpressionDesc::Pexp_pack(_)
            ) && matches!(
                &*arena.get_core_type(constraint_inner.1).ptyp_desc,
                CoreTypeDesc::Ptyp_package(_)
            ) =>
        {
            let (ref inner_idx, ref typ) = **constraint_inner;
            let inner = arena.get_expr(*inner_idx);
            let typ = arena.get_core_type(*typ);
            match (&*inner.pexp_desc, &*typ.ptyp_desc) {
                (
                    ExpressionDesc::Pexp_pack(mod_expr_idx),
                    CoreTypeDesc::Ptyp_package(package_type),
                ) => {
                    let mod_doc =
                        print_mod_expr(state, arena.get_mod_expr(*mod_expr_idx), cmt_tbl, arena);
                    // Don't print "module(...)" wrapper - we're already inside module()
                    let type_doc = print_comments(
                        print_package_type(state, &**package_type, false, cmt_tbl, arena),
                        cmt_tbl,
                        typ.ptyp_loc,
                        arena,
                    );
                    // res_printer.ml:3789-3809
                    Doc::group(Doc::concat(vec![
                        Doc::text("module("),
                        Doc::indent(Doc::concat(vec![
                            Doc::soft_line(),
                            mod_doc,
                            Doc::text(": "),
                            type_doc,
                        ])),
                        Doc::soft_line(),
                        Doc::rparen(),
                    ]))
                }
                _ => Doc::nil(),
            }
        }
        // Constraint: expr: typ (parens added by caller when needed)
        ExpressionDesc::Pexp_constraint(inner) => {
            let (ref expr_idx, ref typ) = **inner;
            let expr = arena.get_expr(*expr_idx);
            let typ = arena.get_core_type(*typ);
            let expr_doc = {
                let doc = print_expression_with_comments(state, expr, cmt_tbl, arena);
                match parens::expr(arena, expr) {
                    parens::ParenKind::Parenthesized => add_parens(doc),
                    parens::ParenKind::Braced(braces) => print_braces(doc, expr, braces, arena),
                    parens::ParenKind::Nothing => doc,
                }
            };
            let typ_doc = print_typ_expr(state, typ, cmt_tbl, arena);
            Doc::concat(vec![expr_doc, Doc::text(": "), typ_doc])
        }
        // Coerce: (expr :> typ)
        ExpressionDesc::Pexp_coerce(inner) => {
            let (ref expr_idx, _, ref typ) = **inner;
            let expr = arena.get_expr(*expr_idx);
            let typ = arena.get_core_type(*typ);
            let expr_doc = print_expression_with_comments_and_parens(state, expr, cmt_tbl, arena);
            let typ_doc = print_typ_expr(state, typ, cmt_tbl, arena);
            let doc = Doc::concat(vec![expr_doc, Doc::text(" :> "), typ_doc]);
            // Keep attributes on the coercion rather than its operand.
            if parsetree_viewer::has_printable_attributes(arena, &e.pexp_attributes) {
                add_parens(doc)
            } else {
                doc
            }
        }
        // Extension
        ExpressionDesc::Pexp_object_literal(fields) => {
            print_object_literal(state, fields, e.pexp_loc, cmt_tbl, arena)
        }
        ExpressionDesc::Pexp_extension(ext) => print_extension(state, ext, false, cmt_tbl, arena),
        ExpressionDesc::Pexp_regexp(regexp) => {
            Doc::text(format!("/{}/{}", regexp.pattern, regexp.flags))
        }
        // res_printer.ml:3857-3859: an if-let prints as an if chain.
        ExpressionDesc::Pexp_match(inner)
            if inner.1.len() == 2 && parsetree_viewer::is_if_let_expr(arena, e) =>
        {
            print_if_chain(state, e, cmt_tbl, arena)
        }
        // Match expression
        ExpressionDesc::Pexp_match(inner) => {
            let (ref expr_idx, ref cases) = **inner;
            print_match_expression(state, arena.get_expr(*expr_idx), cases, cmt_tbl, arena)
        }
        // Try expression
        ExpressionDesc::Pexp_try(inner) => {
            let (ref expr_idx, ref cases) = **inner;
            print_try_expression(state, arena.get_expr(*expr_idx), cases, cmt_tbl, arena)
        }
        // Assert
        ExpressionDesc::Pexp_assert(expr_idx) => {
            let expr = arena.get_expr(*expr_idx);
            let rhs = print_expression_with_comments(state, expr, cmt_tbl, arena);
            Doc::concat(vec![Doc::text("assert("), rhs, Doc::text(")")])
        }
        // Await: parenthesization looks through explicit braces.
        ExpressionDesc::Pexp_await(expr_idx) => {
            let expr = arena.get_expr(*expr_idx);
            let rhs = print_expression_with_comments(state, expr, cmt_tbl, arena);
            let rhs = match parens::assert_or_await_expr_rhs(
                arena,
                true,
                parsetree_viewer::unwrap_braces(arena, expr),
            ) {
                ParenKind::Parenthesized => add_parens(rhs),
                ParenKind::Braced(loc) => print_braces(rhs, expr, loc, arena),
                ParenKind::Nothing => rhs,
            };
            Doc::concat(vec![Doc::text("await "), rhs])
        }
        // Open expression
        ExpressionDesc::Pexp_open(inner) => {
            let (_, _, _) = **inner;
            print_expression_block(state, true, e, cmt_tbl, arena)
        }
        // Let module
        ExpressionDesc::Pexp_letmodule(inner) => {
            let (_, _, _) = **inner;
            print_expression_block(state, true, e, cmt_tbl, arena)
        }
        // Let exception
        ExpressionDesc::Pexp_letexception(inner) => {
            let (_, _) = **inner;
            print_expression_block(state, true, e, cmt_tbl, arena)
        }
        // While loop
        ExpressionDesc::Pexp_while(cond_idx, body_idx) => {
            let cond = arena.get_expr(*cond_idx);
            let body = arena.get_expr(*body_idx);
            // Match OCaml: first check Parens.expr for braces, then apply block expr logic
            let condition = {
                let doc = print_expression_with_comments(state, cond, cmt_tbl, arena);
                match parens::expr(arena, cond) {
                    ParenKind::Parenthesized => add_parens(doc),
                    ParenKind::Braced(braces) => print_braces(doc, cond, braces, arena),
                    ParenKind::Nothing => doc,
                }
            };
            // Check if condition is a block expression - if not, add parens on break
            let cond_doc = if parsetree_viewer::is_block_expr(arena, cond) {
                condition
            } else {
                Doc::group(Doc::if_breaks(add_parens(condition.clone()), condition))
            };
            Doc::breakable_group(
                Doc::concat(vec![
                    Doc::text("while "),
                    cond_doc,
                    Doc::space(),
                    print_expression_block(state, true, body, cmt_tbl, arena),
                ]),
                true, // force_break
            )
        }
        // For-of loop (upstream #7887)
        ExpressionDesc::Pexp_for_of(inner) | ExpressionDesc::Pexp_for_await_of(inner) => {
            let (ref pat, ref iterable_idx, ref body_idx) = **inner;
            let iterable = arena.get_expr(*iterable_idx);
            let body = arena.get_expr(*body_idx);
            let iterable_doc = {
                let doc = print_expression_with_comments(state, iterable, cmt_tbl, arena);
                match parens::expr(arena, iterable) {
                    ParenKind::Parenthesized => add_parens(doc),
                    ParenKind::Braced(loc) => print_braces(doc, iterable, loc, arena),
                    ParenKind::Nothing => doc,
                }
            };
            let lead = if matches!(&*e.pexp_desc, ExpressionDesc::Pexp_for_await_of(_)) {
                "for await "
            } else {
                "for "
            };
            Doc::breakable_group(
                Doc::concat(vec![
                    Doc::text(lead),
                    print_pattern(state, arena.get_pat(*pat), cmt_tbl, arena),
                    Doc::text(" of "),
                    iterable_doc,
                    Doc::space(),
                    print_expression_block(state, true, body, cmt_tbl, arena),
                ]),
                true,
            )
        }
        // For loop
        ExpressionDesc::Pexp_for(inner) => {
            let (ref pat, ref start_idx, ref finish_idx, ref direction, ref body_idx) = **inner;
            let start = arena.get_expr(*start_idx);
            let finish = arena.get_expr(*finish_idx);
            let body = arena.get_expr(*body_idx);
            let dir = match direction {
                DirectionFlag::Upto => " to ",
                DirectionFlag::Downto => " downto ",
            };
            // Handle parens for from_expr
            let start_doc = {
                let doc = print_expression_with_comments(state, start, cmt_tbl, arena);
                match parens::expr(arena, start) {
                    ParenKind::Parenthesized => add_parens(doc),
                    ParenKind::Braced(loc) => print_braces(doc, start, loc, arena),
                    ParenKind::Nothing => doc,
                }
            };
            // Handle parens for to_expr
            let finish_doc = {
                let doc = print_expression_with_comments(state, finish, cmt_tbl, arena);
                match parens::expr(arena, finish) {
                    ParenKind::Parenthesized => add_parens(doc),
                    ParenKind::Braced(loc) => print_braces(doc, finish, loc, arena),
                    ParenKind::Nothing => doc,
                }
            };
            Doc::breakable_group(
                Doc::concat(vec![
                    Doc::text("for "),
                    print_pattern(state, arena.get_pat(*pat), cmt_tbl, arena),
                    Doc::text(" in "),
                    start_doc,
                    Doc::text(dir),
                    finish_doc,
                    Doc::space(),
                    print_expression_block(state, true, body, cmt_tbl, arena),
                ]),
                true, // force_break
            )
        }
        // Pack: module(M)
        // res_printer.ml:3829-3838
        ExpressionDesc::Pexp_pack(mod_expr_idx) => Doc::group(Doc::concat(vec![
            Doc::text("module("),
            Doc::indent(Doc::concat(vec![
                Doc::soft_line(),
                print_mod_expr(state, arena.get_mod_expr(*mod_expr_idx), cmt_tbl, arena),
            ])),
            Doc::soft_line(),
            Doc::rparen(),
        ])),
        // JSX element
        ExpressionDesc::Pexp_jsx_element(jsx) => {
            print_jsx_element(state, jsx, e.pexp_loc, cmt_tbl, arena)
        }
        ExpressionDesc::Pexp_object_get(inner) => {
            let (ref parent_expr_idx, ref label) = **inner;
            print_object_get_doc(
                state,
                arena.get_expr(*parent_expr_idx),
                label,
                cmt_tbl,
                arena,
            )
        }
        ExpressionDesc::Pexp_object_set(inner) => {
            let (ref obj, ref member, ref rhs) = **inner;
            print_object_set_expr(
                state,
                arena.get_expr(*obj),
                member,
                arena.get_expr(*rhs),
                cmt_tbl,
                arena,
            )
        }
    };

    // Handle attributes on the expression
    // Some expression types print their own attributes (fun, newtype, apply, etc.)
    // so we skip attribute printing here for those cases to avoid duplication.
    // This matches OCaml's should_print_its_own_attributes check.
    let should_print_its_own_attributes = match &*e.pexp_desc {
        ExpressionDesc::Pexp_apply(_)
        | ExpressionDesc::Pexp_fun(_)
        | ExpressionDesc::Pexp_newtype(_)
        | ExpressionDesc::Pexp_setfield(_)
        | ExpressionDesc::Pexp_ifthenelse(_)
        | ExpressionDesc::Pexp_ternary(_) => true,
        ExpressionDesc::Pexp_match(_) if parsetree_viewer::is_if_let_expr(arena, e) => true,
        ExpressionDesc::Pexp_jsx_element(_) => true,
        _ => false,
    };

    let attrs = &e.pexp_attributes;
    if attrs.is_empty() || should_print_its_own_attributes {
        printed_expression
    } else {
        // Use Doc::line() separator so it can break when the expression breaks
        // Wrap in Doc::group to control breaking behavior
        let attrs_doc = print_attributes(state, attrs, cmt_tbl, arena);
        Doc::group(Doc::concat(vec![attrs_doc, printed_expression]))
    }
}

// ============================================================================
// Expression Helper Functions
// ============================================================================

/// Print a longident path.
fn print_lident_path(
    path: &crate::parse_arena::Located<crate::parse_arena::LidentIdx>,
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    let doc = print_lident(arena, arena.get_longident(path.txt));
    print_comments(doc, cmt_tbl, path.loc, arena)
}

/// res_printer.ml `print_expression_args`: the argument list of a
/// constructor or polymorphic variant expression.
fn print_expression_args(
    state: &PrinterState,
    args: &[ExprIdx],
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    let mut print_arg = |expr: &Expression, cmt_tbl: &mut CommentTable| {
        let doc = print_expression_with_comments(state, expr, cmt_tbl, arena);
        match parens::expr_allowing_coercion(arena, expr) {
            ParenKind::Parenthesized => add_parens(doc),
            ParenKind::Braced(loc) => print_braces(doc, expr, loc, arena),
            ParenKind::Nothing => doc,
        }
    };
    match args {
        [] => Doc::nil(),
        [arg]
            if matches!(&*arena.get_expr(*arg).pexp_desc,
            ExpressionDesc::Pexp_construct(lid, _) if arena.is_lident(lid.txt, "()")) =>
        {
            Doc::text("()")
        }
        [arg] => {
            let arg = arena.get_expr(*arg);
            let arg_doc = print_arg(arg, cmt_tbl);
            let should_hug = parsetree_viewer::is_huggable_expression(arena, arg);
            Doc::concat(vec![
                Doc::lparen(),
                if should_hug {
                    arg_doc
                } else {
                    Doc::concat(vec![
                        Doc::indent(Doc::concat(vec![Doc::soft_line(), arg_doc])),
                        Doc::trailing_comma(),
                        Doc::soft_line(),
                    ])
                },
                Doc::rparen(),
            ])
        }
        args => {
            let docs = args
                .iter()
                .map(|idx| print_arg(arena.get_expr(*idx), cmt_tbl))
                .collect();
            Doc::concat(vec![
                Doc::lparen(),
                Doc::indent(Doc::concat(vec![
                    Doc::soft_line(),
                    Doc::join(Doc::concat(vec![Doc::comma(), Doc::line()]), docs),
                ])),
                Doc::trailing_comma(),
                Doc::soft_line(),
                Doc::rparen(),
            ])
        }
    }
}

/// res_printer.ml `print_pattern_args`: the argument list of a constructor
/// or polymorphic variant pattern.
fn print_pattern_args(
    state: &PrinterState,
    patterns: &[PatIdx],
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    match patterns {
        [] => Doc::nil(),
        [arg]
            if matches!(&*arena.get_pat(*arg).ppat_desc,
            PatternDesc::Ppat_construct(lid, _) if arena.is_lident(lid.txt, "()")) =>
        {
            Doc::concat(vec![
                Doc::lparen(),
                print_comments_inside(cmt_tbl, arena.get_pat(*arg).ppat_loc, arena),
                Doc::rparen(),
            ])
        }
        [arg] if matches!(&*arena.get_pat(*arg).ppat_desc, PatternDesc::Ppat_tuple(pats) if pats.is_empty()) => {
            Doc::concat(vec![
                Doc::lparen(),
                print_comments_inside(cmt_tbl, arena.get_pat(*arg).ppat_loc, arena),
                Doc::rparen(),
            ])
        }
        [arg] => {
            let arg = arena.get_pat(*arg);
            let arg_doc = print_pattern(state, arg, cmt_tbl, arena);
            let should_hug = is_huggable_pattern(arg);
            Doc::concat(vec![
                Doc::lparen(),
                if should_hug {
                    arg_doc
                } else {
                    Doc::concat(vec![
                        Doc::indent(Doc::concat(vec![Doc::soft_line(), arg_doc])),
                        Doc::trailing_comma(),
                        Doc::soft_line(),
                    ])
                },
                Doc::rparen(),
            ])
        }
        patterns => Doc::concat(vec![
            Doc::lparen(),
            Doc::indent(Doc::concat(vec![
                Doc::soft_line(),
                Doc::join(
                    Doc::concat(vec![Doc::comma(), Doc::line()]),
                    patterns
                        .iter()
                        .map(|p| print_pattern(state, arena.get_pat(*p), cmt_tbl, arena))
                        .collect(),
                ),
            ])),
            Doc::trailing_comma(),
            Doc::soft_line(),
            Doc::rparen(),
        ]),
    }
}

/// Print list expression (cons cells).
fn print_list_expression(
    state: &PrinterState,
    e: &Expression,
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    let (expressions, spread) = parsetree_viewer::collect_list_expressions(arena, e);
    let spread_doc = match spread {
        Some(expr) => Doc::concat(vec![Doc::text(","), Doc::line(), Doc::dotdotdot(), {
            let doc = print_expression_with_comments(state, expr, cmt_tbl, arena);
            match parens::expr_allowing_coercion(arena, expr) {
                ParenKind::Parenthesized => add_parens(doc),
                ParenKind::Braced(loc) => print_braces(doc, expr, loc, arena),
                ParenKind::Nothing => doc,
            }
        }]),
        None => Doc::nil(),
    };
    Doc::group(Doc::concat(vec![
        Doc::text("list{"),
        Doc::indent(Doc::concat(vec![
            Doc::soft_line(),
            Doc::join(
                Doc::concat(vec![Doc::text(","), Doc::line()]),
                expressions
                    .iter()
                    .map(|expr| {
                        let doc = print_expression_with_comments(state, expr, cmt_tbl, arena);
                        match parens::expr_allowing_coercion(arena, expr) {
                            ParenKind::Parenthesized => add_parens(doc),
                            ParenKind::Braced(loc) => print_braces(doc, *expr, loc, arena),
                            ParenKind::Nothing => doc,
                        }
                    })
                    .collect(),
            ),
            spread_doc,
        ])),
        Doc::trailing_comma(),
        Doc::soft_line(),
        Doc::rbrace(),
    ]))
}

/// Callback printing mode.
#[derive(Debug, Clone, Copy, PartialEq)]
enum InCallback {
    NoCallback,
    FitsOnOneLine,
    ArgumentsFitOnOneLine,
}

/// Print arrow expression (function).
fn print_arrow_expression(
    state: &PrinterState,
    e: &Expression,
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    // OCaml `print_expression`: `Pexp_fun _ -> print_pexp_fun ~in_callback:NoCallback`.
    print_pexp_fun(state, InCallback::NoCallback, e, cmt_tbl, arena)
}

/// Print a function expression (Pexp_fun/Pexp_newtype) with callback mode.
/// This is used by callback printing to try different layouts.
fn print_pexp_fun(
    state: &PrinterState,
    in_callback: InCallback,
    e: &Expression,
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    let (is_async, parameters, return_expr) = parsetree_viewer::fun_expr(arena, e);
    let attrs_on_arrow = &e.pexp_attributes;

    // Extract type constraint if present
    // When extracting, merge the attributes from the constraint onto the inner expression
    // This preserves @res.braces on the body when it's inside a constraint
    let (return_expr_owned, typ_constraint): (Option<Expression>, Option<&CoreType>) =
        match &*return_expr.pexp_desc {
            // res_printer.ml print_pexp_fun: braces around a constraint keep
            // their braces around the constrained expression, with the
            // constraint's attributes in front of the braces node's.
            ExpressionDesc::Pexp_braces(braces)
                if matches!(
                    &*arena.get_expr(braces.expr).pexp_desc,
                    ExpressionDesc::Pexp_constraint(_)
                ) =>
            {
                let constrained = arena.get_expr(braces.expr);
                let ExpressionDesc::Pexp_constraint(inner) = &*constrained.pexp_desc else {
                    unreachable!()
                };
                let (expr_idx, typ_idx) = **inner;
                let attrs = constrained
                    .pexp_attributes
                    .clone()
                    .concat(return_expr.pexp_attributes.clone());
                let braced = Expression {
                    pexp_desc: Box::new(ExpressionDesc::Pexp_braces(Box::new(PexpBraces {
                        expr: expr_idx,
                        braces_loc: braces.braces_loc,
                    }))),
                    pexp_loc: arena.get_expr(expr_idx).pexp_loc,
                    pexp_attributes: attrs,
                };
                (Some(braced), Some(arena.get_core_type(typ_idx)))
            }
            ExpressionDesc::Pexp_constraint(inner) => {
                let (ref expr_idx, ref typ_idx) = **inner;
                // Create a new expression with merged attributes
                let mut merged_expr = arena.get_expr(*expr_idx).clone();
                merged_expr.pexp_attributes = merged_expr
                    .pexp_attributes
                    .clone()
                    .concat(return_expr.pexp_attributes.clone());
                (Some(merged_expr), Some(arena.get_core_type(*typ_idx)))
            }
            _ => (None, None),
        };
    let return_expr: &Expression = return_expr_owned.as_ref().unwrap_or(return_expr);

    let has_constraint = typ_constraint.is_some();

    // Print parameters
    let parameters_doc = print_expr_fun_parameters(
        state,
        in_callback,
        is_async,
        has_constraint,
        &parameters,
        cmt_tbl,
        arena,
    );

    // Print return expression
    let return_expr_doc = {
        let opt_braces = parsetree_viewer::process_braces(arena, return_expr).0;
        let should_inline = match (&*return_expr.pexp_desc, opt_braces) {
            (_, Some(_)) => true,
            (
                ExpressionDesc::Pexp_array(_)
                | ExpressionDesc::Pexp_tuple(_)
                | ExpressionDesc::Pexp_record(_),
                _,
            ) => true,
            (ExpressionDesc::Pexp_construct(_, args), _) if !args.txt.is_empty() => true,
            _ => false,
        };
        let should_indent = match &*return_expr.pexp_desc {
            ExpressionDesc::Pexp_sequence(_, _)
            | ExpressionDesc::Pexp_let(_)
            | ExpressionDesc::Pexp_letmodule(_)
            | ExpressionDesc::Pexp_letexception(_)
            | ExpressionDesc::Pexp_open(_) => false,
            ExpressionDesc::Pexp_jsx_element(element) => {
                !matches!(&**element, JsxElement::Fragment(_))
            }
            _ => true,
        };

        let return_doc = {
            let doc = print_expression_with_comments(state, return_expr, cmt_tbl, arena);
            match parens::expr(arena, return_expr) {
                ParenKind::Parenthesized => add_parens(doc),
                ParenKind::Braced(loc) => print_braces(doc, return_expr, loc, arena),
                ParenKind::Nothing => doc,
            }
        };

        if should_inline {
            Doc::concat(vec![Doc::space(), return_doc])
        } else {
            Doc::group(if should_indent {
                Doc::concat(vec![
                    Doc::indent(Doc::concat(vec![Doc::line(), return_doc])),
                    // In callback mode, add soft_line after return expr
                    // This pushes trailing comments to after the function call
                    match in_callback {
                        InCallback::FitsOnOneLine | InCallback::ArgumentsFitOnOneLine => {
                            Doc::soft_line()
                        }
                        InCallback::NoCallback => Doc::nil(),
                    },
                ])
            } else {
                Doc::concat(vec![Doc::space(), return_doc])
            })
        }
    };

    // Print type constraint
    let typ_constraint_doc = match typ_constraint {
        Some(typ) => {
            let typ_doc = print_typ_expr(state, typ, cmt_tbl, arena);
            let typ_doc = if parens::arrow_return_typ_expr(typ) {
                add_parens(typ_doc)
            } else {
                typ_doc
            };
            Doc::concat(vec![Doc::text(": "), typ_doc])
        }
        None => Doc::nil(),
    };

    let attrs = print_attributes_with_loc(state, attrs_on_arrow, None, cmt_tbl, arena, true);

    let doc = Doc::concat(vec![
        attrs,
        parameters_doc,
        typ_constraint_doc,
        Doc::text(" =>"),
        return_expr_doc,
    ]);
    match in_callback {
        InCallback::NoCallback => Doc::group(doc),
        InCallback::FitsOnOneLine | InCallback::ArgumentsFitOnOneLine => doc,
    }
}

/// Print function parameters.
fn print_expr_fun_parameters(
    state: &PrinterState,
    in_callback: InCallback,
    is_async: bool,
    has_constraint: bool,
    parameters: &[parsetree_viewer::FunParam<'_>],
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    use parsetree_viewer::FunParam;

    // Handle special single parameter cases
    // Note: we filter out parsing attrs (like res.braces) when checking for empty attrs
    match parameters {
        // let f = _ => ()
        [
            FunParam::Parameter {
                attrs,
                label: ArgLabel::Nolabel,
                default_expr: None,
                pat,
            },
        ] if parsetree_viewer::filter_parsing_attrs_slice(arena, attrs).is_empty()
            && matches!(&*pat.ppat_desc, PatternDesc::Ppat_any) =>
        {
            let doc = if has_constraint {
                Doc::text("(_)")
            } else {
                Doc::text("_")
            };
            let doc = print_comments(doc, cmt_tbl, pat.ppat_loc, arena);
            return if is_async { add_async(doc) } else { doc };
        }
        // let f = a => ()
        [
            FunParam::Parameter {
                attrs,
                label: ArgLabel::Nolabel,
                default_expr: None,
                pat,
            },
        ] if parsetree_viewer::filter_parsing_attrs_slice(arena, attrs).is_empty()
            && matches!(&*pat.ppat_desc, PatternDesc::Ppat_var(_))
            && pat.ppat_attributes.is_empty() =>
        {
            if let PatternDesc::Ppat_var(string_loc) = &*pat.ppat_desc {
                let var = print_ident_like(arena.get_string(string_loc.txt), false, false);
                let var = if has_constraint { add_parens(var) } else { var };
                let doc = if is_async { add_async(var) } else { var };
                return print_comments(doc, cmt_tbl, string_loc.loc, arena);
            }
        }
        // let f = () => ()
        [
            FunParam::Parameter {
                attrs,
                label: ArgLabel::Nolabel,
                default_expr: None,
                pat,
            },
        ] if parsetree_viewer::filter_parsing_attrs_slice(arena, attrs).is_empty()
            && matches!(
                &*pat.ppat_desc,
                PatternDesc::Ppat_construct(lid, args)
                    if arena.is_lident(lid.txt, "()") && args.txt.is_empty()
            ) =>
        {
            let doc = Doc::text("()");
            let doc = if is_async { add_async(doc) } else { doc };
            return print_comments(doc, cmt_tbl, pat.ppat_loc, arena);
        }
        _ => {}
    }

    // General case: multiple parameters or complex single parameter
    let fits_on_one_line = matches!(in_callback, InCallback::FitsOnOneLine);
    let should_hug = parameters_should_hug(parameters);

    let lparen = if is_async {
        add_async(Doc::lparen())
    } else {
        Doc::lparen()
    };

    let printed_params = Doc::concat(vec![
        if should_hug || fits_on_one_line {
            Doc::nil()
        } else {
            Doc::soft_line()
        },
        Doc::join(
            Doc::concat(vec![Doc::comma(), Doc::line()]),
            parameters
                .iter()
                .map(|p| print_exp_fun_parameter(state, p, cmt_tbl, arena))
                .collect(),
        ),
    ]);

    Doc::group(Doc::concat(vec![
        lparen,
        if should_hug || fits_on_one_line {
            printed_params
        } else {
            Doc::concat(vec![
                Doc::indent(printed_params),
                Doc::trailing_comma(),
                Doc::soft_line(),
            ])
        },
        Doc::rparen(),
    ]))
}

/// Check if parameters should be hugged (printed without line breaks).
fn parameters_should_hug(parameters: &[parsetree_viewer::FunParam<'_>]) -> bool {
    use parsetree_viewer::FunParam;
    match parameters {
        [
            FunParam::Parameter {
                attrs,
                label: ArgLabel::Nolabel,
                default_expr: None,
                pat,
            },
        ] if attrs.is_empty() => is_huggable_pattern(pat),
        _ => false,
    }
}

/// Print a single function parameter.
fn print_exp_fun_parameter(
    state: &PrinterState,
    param: &parsetree_viewer::FunParam<'_>,
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    use parsetree_viewer::FunParam;
    match param {
        FunParam::NewTypes { attrs, names } => {
            let attrs_doc = print_attributes(state, attrs, cmt_tbl, arena);
            // Print all type names space-separated, e.g., "type t u v"
            let names_doc = Doc::join(
                Doc::space(),
                names
                    .iter()
                    .map(|name| {
                        print_comments(
                            print_ident_like(arena.get_string(name.txt), false, false),
                            cmt_tbl,
                            name.loc,
                            arena,
                        )
                    })
                    .collect(),
            );
            Doc::group(Doc::concat(vec![attrs_doc, Doc::text("type "), names_doc]))
        }
        FunParam::Parameter {
            attrs,
            label,
            default_expr,
            pat,
        } => {
            let attrs_doc = print_attributes(state, attrs, cmt_tbl, arena);
            let default_doc = match default_expr {
                Some(expr) => Doc::concat(vec![
                    Doc::text("="),
                    print_expression_with_comments(state, expr, cmt_tbl, arena),
                ]),
                None => Doc::nil(),
            };

            let label_with_pattern = match (label, &*pat.ppat_desc) {
                (ArgLabel::Nolabel, _) => print_pattern(state, pat, cmt_tbl, arena),
                // ~d (punning)
                (ArgLabel::Labelled(lbl) | ArgLabel::Optional(lbl), PatternDesc::Ppat_var(var))
                    if arena.get_string(lbl.txt) == arena.get_string(var.txt) =>
                {
                    print_comments(
                        Doc::concat(vec![
                            print_attributes(state, &pat.ppat_attributes, cmt_tbl, arena),
                            Doc::text("~"),
                            print_ident_like(arena.get_string(lbl.txt), false, false),
                        ]),
                        cmt_tbl,
                        pat.ppat_loc,
                        arena,
                    )
                }
                // ~d: typ (punning with type)
                (
                    ArgLabel::Labelled(lbl) | ArgLabel::Optional(lbl),
                    PatternDesc::Ppat_constraint(ppat_inner),
                ) if matches!(&*arena.get_pat(ppat_inner.0).ppat_desc, PatternDesc::Ppat_var(v) if arena.get_string(lbl.txt) == arena.get_string(v.txt)) =>
                {
                    let (ref var_pat_idx, ref typ) = **ppat_inner;
                    let var_pattern = arena.get_pat(*var_pat_idx);
                    let attrs = print_attributes(state, &pat.ppat_attributes, cmt_tbl, arena);
                    let label = print_comments(
                        Doc::concat(vec![
                            Doc::text("~"),
                            print_ident_like(arena.get_string(lbl.txt), false, false),
                        ]),
                        cmt_tbl,
                        var_pattern.ppat_loc,
                        arena,
                    );
                    let typ = print_typ_expr(state, arena.get_core_type(*typ), cmt_tbl, arena);
                    print_comments(
                        Doc::concat(vec![attrs, label, Doc::text(": "), typ]),
                        cmt_tbl,
                        pat.ppat_loc,
                        arena,
                    )
                }
                // ~d as x or ~d=pat
                (ArgLabel::Labelled(lbl), _) => Doc::concat(vec![
                    Doc::text("~"),
                    print_ident_like(arena.get_string(lbl.txt), false, false),
                    Doc::text(" as "),
                    print_pattern(state, pat, cmt_tbl, arena),
                ]),
                (ArgLabel::Optional(lbl), _) => Doc::concat(vec![
                    Doc::text("~"),
                    print_ident_like(arena.get_string(lbl.txt), false, false),
                    Doc::text(" as "),
                    print_pattern(state, pat, cmt_tbl, arena),
                ]),
            };

            // Only add =? for optional arguments without a default value
            // If there's a default value (=expr), we don't need =?
            let opt_marker = match (label, default_expr) {
                (ArgLabel::Optional(_), None) => Doc::text("=?"),
                _ => Doc::nil(),
            };

            let doc = Doc::group(Doc::concat(vec![
                attrs_doc,
                label_with_pattern,
                default_doc,
            ]));

            // Wrap with comments using combined location (like OCaml's print_exp_fun_parameter)
            // The location spans from the label (if present) to the end of pattern or default_expr
            let lbl_loc = match label {
                ArgLabel::Labelled(lbl) | ArgLabel::Optional(lbl)
                    if arena.to_location(lbl.loc) != FullLocation::none() =>
                {
                    lbl.loc
                }
                _ => pat.ppat_loc,
            };
            let end_loc = match default_expr {
                Some(expr) => expr.pexp_loc,
                None => pat.ppat_loc,
            };
            let (pos_range, full_loc) = make_combined_pos_range(lbl_loc, end_loc, arena);
            // Without a default, the range ends before `=?`.
            print_comments_before_marker_by_pos(doc, cmt_tbl, pos_range, &full_loc, opt_marker)
        }
    }
}

/// Add async marker to a doc.
fn add_async(doc: Doc) -> Doc {
    Doc::concat(vec![Doc::text("async "), doc])
}

/// res_printer.ml `Pexp_object_literal`: a JS object literal `{"key": value}`.
fn print_object_literal(
    state: &PrinterState,
    fields: &[(Loc<Label>, ExprIdx)],
    loc: LocIdx,
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    // If the object is written over multiple lines, break automatically.
    let loc = arena.get_location(loc);
    let force_break = arena.get_position(loc.loc_start).line < arena.get_position(loc.loc_end).line;
    let rows_doc = Doc::join(
        Doc::concat(vec![Doc::text(","), Doc::line()]),
        fields
            .iter()
            .map(|(name, e)| print_bs_object_row(state, &name.txt, name.loc, *e, cmt_tbl, arena))
            .collect(),
    );
    Doc::breakable_group(
        Doc::concat(vec![
            Doc::lbrace(),
            Doc::indent(Doc::concat(vec![Doc::soft_line(), rows_doc])),
            Doc::trailing_comma(),
            Doc::soft_line(),
            Doc::rbrace(),
        ]),
        force_break,
    )
}

/// Print a row of a BS/JS object with string key: "key": value
fn print_bs_object_row(
    state: &PrinterState,
    name: &str,
    name_loc: LocIdx,
    expr_idx: ExprIdx,
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    let lbl_doc = Doc::concat(vec![Doc::text("\""), Doc::text(name), Doc::text("\"")]);
    let lbl_doc = print_comments(lbl_doc, cmt_tbl, name_loc, arena);

    let expr = arena.get_expr(expr_idx);
    let expr_doc = print_expression_with_comments(state, expr, cmt_tbl, arena);
    let expr_doc = match parens::expr(arena, expr) {
        ParenKind::Parenthesized => add_parens(expr_doc),
        ParenKind::Braced(loc) => print_braces(expr_doc, expr, loc, arena),
        ParenKind::Nothing => expr_doc,
    };

    let doc = Doc::concat(vec![lbl_doc, Doc::text(": "), expr_doc]);
    // cmt_loc spans from label start to expression end, matching OCaml
    let (pos_range, full_loc) = make_combined_pos_range(name_loc, expr.pexp_loc, arena);
    print_comments_by_pos(doc, cmt_tbl, pos_range, &full_loc)
}

/// Print record expression.
fn print_record_expression(
    state: &PrinterState,
    loc: LocIdx,
    spread: Option<&Expression>,
    fields: &[ExpressionRecordField],
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    // res_printer.ml:3505-3508: `rows = []` prints `{}` (and the comments
    // inside), even when there is a spread.
    if fields.is_empty() {
        return Doc::concat(vec![
            Doc::lbrace(),
            print_comments_inside(cmt_tbl, loc, arena),
            Doc::rbrace(),
        ]);
    }

    // Calculate force_break: record written on multiple lines should break the group
    let force_break = match (spread, fields.first()) {
        (Some(expr), _) => {
            // If there's a spread, compare with spread expression's location
            arena.loc_start(loc).line < arena.loc_start(expr.pexp_loc).line
        }
        (None, Some(first_field)) => {
            // Otherwise, compare with the first row's location
            arena.loc_start(loc).line < arena.loc_start(first_field.lid.loc).line
        }
        (None, None) => false,
    };

    // Disallow punning for single-element records without spread
    let punning_allowed = !(spread.is_none() && fields.len() == 1);

    let spread_doc = match spread {
        Some(expr) => {
            // Print the expression, checking if it's just an identifier
            let expr_doc = match &*expr.pexp_desc {
                ExpressionDesc::Pexp_ident(path) => {
                    print_lident(arena, arena.get_longident(path.txt))
                }
                _ => print_expression(state, expr, cmt_tbl, arena),
            };
            // Apply parens if needed
            let expr_doc = match parens::expr_allowing_coercion(arena, expr) {
                ParenKind::Parenthesized => add_parens(expr_doc),
                ParenKind::Braced(loc) => print_braces(expr_doc, expr, loc, arena),
                ParenKind::Nothing => expr_doc,
            };
            // Combine ... with the expression
            let doc_with_spread = Doc::concat(vec![Doc::dotdotdot(), expr_doc]);
            // Wrap with comments using expr.pexp_loc - this puts leading comments BEFORE ...
            let doc_with_comments = print_comments(doc_with_spread, cmt_tbl, expr.pexp_loc, arena);
            Doc::concat(vec![doc_with_comments, Doc::text(","), Doc::line()])
        }
        None => Doc::nil(),
    };
    let fields_doc = Doc::join(
        Doc::concat(vec![Doc::text(","), Doc::line()]),
        fields
            .iter()
            .map(|field| {
                // Like OCaml's print_expression_record_row, print the label with its comments
                let field_name_with_comments = {
                    let doc = print_lident(arena, arena.get_longident(field.lid.txt));
                    print_comments(doc, cmt_tbl, field.lid.loc, arena)
                };
                let expr = arena.get_expr(field.expr);
                let expr_doc = print_expression_with_comments(state, expr, cmt_tbl, arena);
                // Check for punning
                let row_doc = if punning_allowed && is_punned_record_field(arena, field) {
                    // Punned: `?name` or `name`
                    if field.opt {
                        Doc::concat(vec![Doc::text("?"), field_name_with_comments])
                    } else {
                        field_name_with_comments
                    }
                } else {
                    // Non-punned: `name: ?value` or `name: value`
                    // Check if the expression needs parens/braces
                    let expr_doc = match parens::expr_record_row_rhs(arena, field.opt, expr) {
                        ParenKind::Parenthesized => add_parens(expr_doc),
                        ParenKind::Braced(loc) => print_braces(expr_doc, expr, loc, arena),
                        ParenKind::Nothing => expr_doc,
                    };
                    let opt_marker = if field.opt {
                        Doc::text("?")
                    } else {
                        Doc::nil()
                    };
                    Doc::group(Doc::concat(vec![
                        field_name_with_comments,
                        Doc::text(": "),
                        opt_marker,
                        expr_doc,
                    ]))
                };
                // Like OCaml, wrap with comments using combined location (from label to expression)
                let (pos_range, full_loc) =
                    make_combined_pos_range(field.lid.loc, expr.pexp_loc, arena);
                print_comments_by_pos(row_doc, cmt_tbl, pos_range, &full_loc)
            })
            .collect(),
    );
    Doc::breakable_group(
        Doc::concat(vec![
            Doc::lbrace(),
            Doc::indent(Doc::concat(vec![Doc::soft_line(), spread_doc, fields_doc])),
            Doc::trailing_comma(),
            Doc::soft_line(),
            Doc::rbrace(),
        ]),
        force_break,
    )
}

/// Get the last component of a longident (like OCaml's Longident.last).
fn longident_last<'a>(arena: &'a ParseArena, lid: &Longident) -> &'a str {
    match lid {
        Longident::Lident(s) => arena.get_string(*s),
        Longident::Ldot(_, s) => arena.get_string(*s),
        Longident::Lapply(_, _) => "",
    }
}

/// Check if a record field is punned.
/// A field is punned when the LAST component of the label matches the identifier expression,
/// e.g., `{a}` where a is Pexp_ident with txt = "a", or `{A.a}` where a is "a".
fn is_punned_record_field(arena: &ParseArena, field: &ExpressionRecordField) -> bool {
    let expr = arena.get_expr(field.expr);
    // Expression must have no attributes
    if !expr.pexp_attributes.is_empty() {
        return false;
    }

    // Expression must be a simple Lident
    if let ExpressionDesc::Pexp_ident(path) = &*expr.pexp_desc {
        if let Longident::Lident(ident_idx) = arena.get_longident(path.txt) {
            // Compare the LAST component of the label with the expression identifier
            let label_last = longident_last(arena, arena.get_longident(field.lid.txt));
            let ident_str = arena.get_string(*ident_idx);
            return label_last == ident_str;
        }
    }
    false
}

/// Print a ternary expression (cond ? then : else).
fn print_ternary_expression(
    state: &PrinterState,
    e: &Expression,
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    let (parts, alternate) = parsetree_viewer::collect_ternary_parts(arena, e);

    let ternary_doc = match parts.as_slice() {
        [(condition1, consequent1), rest @ ..] => {
            let rest_doc = rest
                .iter()
                .map(|(condition, consequent)| {
                    Doc::concat(vec![
                        Doc::line(),
                        Doc::text(": "),
                        print_ternary_operand(state, condition, cmt_tbl, arena),
                        Doc::line(),
                        Doc::text("? "),
                        print_ternary_operand(state, consequent, cmt_tbl, arena),
                    ])
                })
                .collect::<Vec<_>>();

            Doc::group(Doc::concat(vec![
                print_ternary_operand(state, condition1, cmt_tbl, arena),
                Doc::indent(Doc::concat(vec![
                    Doc::line(),
                    Doc::indent(Doc::concat(vec![
                        Doc::text("? "),
                        print_ternary_operand(state, consequent1, cmt_tbl, arena),
                    ])),
                    Doc::concat(rest_doc),
                    Doc::line(),
                    Doc::text(": "),
                    Doc::indent(print_ternary_operand(state, alternate, cmt_tbl, arena)),
                ])),
            ]))
        }
        _ => Doc::nil(),
    };

    // Print attributes - ternary handles its own attributes
    let attrs: Vec<&Attribute> = e.pexp_attributes.iter().collect();

    // Check if any of the printable attributes need parens wrapping
    let collected_attrs: Attributes = attrs.iter().map(|a| (*a).clone()).collect();
    let needs_parens = parsetree_viewer::filter_parsing_attrs(arena, &collected_attrs)
        .iter()
        .any(|attr| parsetree_viewer::is_printable_attribute(arena, attr));

    let attrs_doc = print_attributes(
        state,
        &attrs.into_iter().cloned().collect::<Vec<_>>(),
        cmt_tbl,
        arena,
    );
    Doc::concat(vec![
        attrs_doc,
        if needs_parens {
            add_parens(ternary_doc)
        } else {
            ternary_doc
        },
    ])
}

/// Print a ternary operand with appropriate parenthesization.
fn print_ternary_operand(
    state: &PrinterState,
    expr: &Expression,
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    let doc = print_expression_with_comments(state, expr, cmt_tbl, arena);

    // Use parens::ternary_operand to determine parenthesization
    match parens::ternary_operand(arena, expr) {
        ParenKind::Parenthesized => add_parens(doc),
        ParenKind::Braced(loc) => print_braces(doc, expr, loc, arena),
        ParenKind::Nothing => doc,
    }
}

/// Print if expression chain.
/// Handles `if`, `else if`, and `if let` chains properly.
fn print_if_expression(
    state: &PrinterState,
    e: &Expression,
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    print_if_chain(state, e, cmt_tbl, arena)
}

/// Print an if-expression chain with proper `else if` flattening.
fn print_if_chain(
    state: &PrinterState,
    e: &Expression,
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    let (ifs, else_expr) = parsetree_viewer::collect_if_expressions(arena, e);

    let if_docs: Vec<Doc> = ifs
        .iter()
        .enumerate()
        .map(|(i, (outer_loc, condition_kind, then_expr))| {
            let if_txt = if i > 0 {
                Doc::text("else if ")
            } else {
                Doc::text("if ")
            };

            let doc = match condition_kind {
                parsetree_viewer::IfConditionKind::If(if_expr) => {
                    let condition = if parsetree_viewer::is_block_expr(arena, if_expr) {
                        print_expression_block(state, true, if_expr, cmt_tbl, arena)
                    } else {
                        let doc = print_expression_with_comments(state, if_expr, cmt_tbl, arena);
                        match parens::expr(arena, if_expr) {
                            ParenKind::Parenthesized => add_parens(doc),
                            ParenKind::Braced(loc) => print_braces(doc, if_expr, loc, arena),
                            ParenKind::Nothing => Doc::if_breaks(add_parens(doc.clone()), doc),
                        }
                    };

                    // Strip explicit braces from then_expr (from Reason conversion)
                    let then_expr_to_print = parsetree_viewer::process_braces(arena, then_expr).1;

                    Doc::concat(vec![
                        if_txt,
                        Doc::group(condition),
                        Doc::space(),
                        print_expression_block(state, true, then_expr_to_print, cmt_tbl, arena),
                    ])
                }
                parsetree_viewer::IfConditionKind::IfLet(pattern, condition_expr) => {
                    let condition_doc = {
                        let doc =
                            print_expression_with_comments(state, condition_expr, cmt_tbl, arena);
                        match parens::expr(arena, condition_expr) {
                            ParenKind::Parenthesized => add_parens(doc),
                            ParenKind::Braced(loc) => print_braces(doc, condition_expr, loc, arena),
                            ParenKind::Nothing => doc,
                        }
                    };

                    Doc::concat(vec![
                        if_txt,
                        Doc::text("let "),
                        print_pattern(state, pattern, cmt_tbl, arena),
                        Doc::text(" = "),
                        condition_doc,
                        Doc::space(),
                        print_expression_block(state, true, then_expr, cmt_tbl, arena),
                    ])
                }
            };

            // Print leading comments for outer_loc
            // This handles comments that appear between `}` and `else if`
            print_leading_comments(doc, cmt_tbl, **outer_loc, arena)
        })
        .collect();

    let if_docs = Doc::join(Doc::space(), if_docs);

    let else_doc = match else_expr {
        None => Doc::nil(),
        Some(expr) => Doc::concat(vec![
            Doc::text(" else "),
            print_expression_block(
                state,
                true,
                parsetree_viewer::process_braces(arena, expr).1,
                cmt_tbl,
                arena,
            ),
        ]),
    };

    // Print attributes - Pexp_ifthenelse handles its own attributes
    // Filter out fragile match attributes (res.braces, res.ternary)
    let attrs = parsetree_viewer::filter_fragile_match_attributes(arena, &e.pexp_attributes);
    let attrs_doc = print_attributes(
        state,
        &attrs.into_iter().cloned().collect::<Vec<_>>(),
        cmt_tbl,
        arena,
    );
    Doc::concat(vec![attrs_doc, if_docs, else_doc])
}

/// A row in an expression block.
/// Uses PosRange for comment lookup (matches what the walker stores) plus line positions for spacing.
struct BlockRow {
    /// Position range for comment lookup - must match what the walker created
    pos_range: PosRange,
    /// Start line of the row
    start_line: usize,
    /// End line of the row
    end_line: usize,
    doc: Doc,
}

/// Print expression block (with braces).
/// This matches OCaml's print_expression_block which uses collect_rows and print_list.
fn print_expression_block(
    state: &PrinterState,
    braces: bool,
    expr: &Expression,
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    let expr = parsetree_viewer::unwrap_braces(arena, expr);
    // Collect all rows (statements) in the block
    let rows = collect_block_rows(state, expr, cmt_tbl, arena);

    // Print rows with position-based comment lookup
    let block = print_block_rows(&rows, cmt_tbl, arena);

    Doc::breakable_group(
        if braces {
            Doc::concat(vec![
                Doc::lbrace(),
                Doc::indent(Doc::concat(vec![Doc::line(), block])),
                Doc::line(),
                Doc::rbrace(),
            ])
        } else {
            block
        },
        true, // force_break
    )
}

/// Print block rows with proper comment handling and line breaks.
/// Uses PosRange directly for comment lookup to match what the walker stored.
fn print_block_rows(rows: &[BlockRow], cmt_tbl: &mut CommentTable, arena: &ParseArena) -> Doc {
    if rows.is_empty() {
        return Doc::nil();
    }

    let mut docs = Vec::with_capacity(rows.len() * 2);

    // First row
    let first = &rows[0];
    let first_doc = print_block_row_with_comments(
        &first.doc,
        first.pos_range,
        first.start_line,
        first.end_line,
        cmt_tbl,
        arena,
    );
    docs.push(first_doc);

    let mut prev_end_line = first.end_line;

    // Remaining rows
    for row in &rows[1..] {
        // Determine separator based on line distance
        // Match OCaml: look up first leading comment AFTER row docs are built
        // If comment was consumed during print_expression, it won't be found,
        // and we fall back to row.start_line (matching OCaml's loc.loc_start behavior)
        let start_line = match cmt_tbl.get_first_leading_comment_by_pos(row.pos_range) {
            Some(comment) => comment.loc().loc_start.line as usize,
            None => row.start_line,
        };

        let sep = if start_line.saturating_sub(prev_end_line) > 1 {
            Doc::concat(vec![Doc::hard_line(), Doc::hard_line()])
        } else {
            Doc::hard_line()
        };

        docs.push(sep);

        let doc = print_block_row_with_comments(
            &row.doc,
            row.pos_range,
            row.start_line,
            row.end_line,
            cmt_tbl,
            arena,
        );
        docs.push(doc);

        prev_end_line = row.end_line;
    }

    Doc::concat(docs)
}

/// Print a block row with its leading and trailing comments using position-based lookup.
fn print_block_row_with_comments(
    doc: &Doc,
    pos_range: PosRange,
    start_line: usize,
    end_line: usize,
    cmt_tbl: &mut CommentTable,
    _arena: &ParseArena,
) -> Doc {
    let leading_comments = cmt_tbl.remove_leading_comments_by_pos(pos_range);
    let trailing_comments = cmt_tbl.remove_trailing_comments_by_pos(pos_range);

    // Create a fake full location for printing helpers with actual line numbers
    let full_loc = crate::location::Location {
        loc_start: crate::location::Position {
            file_name: crate::intern::StrIdx::default(),
            line: start_line as i32,
            bol: 0,
            cnum: pos_range.start,
        },
        loc_end: crate::location::Position {
            file_name: crate::intern::StrIdx::default(),
            line: end_line as i32,
            bol: 0,
            cnum: pos_range.end,
        },
        loc_ghost: false,
    };

    // Use the existing comment printing helpers
    let doc_with_leading = print_leading_comments_with(doc.clone(), leading_comments, &full_loc);
    print_trailing_comments_with(doc_with_leading, trailing_comments, &full_loc)
}

/// Collect rows from an expression block, matching OCaml's collect_rows.
fn collect_block_rows(
    state: &PrinterState,
    expr: &Expression,
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Vec<BlockRow> {
    let mut rows = Vec::new();
    collect_block_rows_inner(state, expr, &mut rows, cmt_tbl, arena);
    rows
}

/// Inner recursive function for collect_block_rows.
fn collect_block_rows_inner(
    state: &PrinterState,
    expr: &Expression,
    rows: &mut Vec<BlockRow>,
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) {
    match &*expr.pexp_desc {
        ExpressionDesc::Pexp_letmodule(inner) => {
            let (ref name, ref mod_expr, ref body_idx) = **inner;
            let mod_expr = arena.get_mod_expr(*mod_expr);
            // Use combined location (expr start to mod_expr end) to match walker
            let start = arena.loc_start(expr.pexp_loc);
            let end = arena.loc_end(mod_expr.pmod_loc);
            let pos_range = PosRange {
                start: start.cnum,
                end: end.cnum,
            };

            // Print module name with comments
            let name_doc = {
                let doc = Doc::text(arena.get_string(name.txt));
                print_comments(doc, cmt_tbl, name.loc, arena)
            };

            // Handle module constraint: module M: T = E
            let (name_doc, mod_expr_to_print) = match &*mod_expr.pmod_desc {
                ModuleExprDesc::Pmod_constraint(inner_mod_idx, mod_type_idx)
                    if !parsetree_viewer::has_await_attribute(arena, &mod_expr.pmod_attributes) =>
                {
                    let name_with_type = Doc::concat(vec![
                        name_doc,
                        Doc::text(": "),
                        print_module_type(state, arena.get_mod_type(*mod_type_idx), cmt_tbl, arena),
                    ]);
                    (name_with_type, arena.get_mod_expr(*inner_mod_idx))
                }
                _ => (name_doc, mod_expr),
            };

            let let_module_doc = Doc::concat(vec![
                Doc::text("module "),
                name_doc,
                Doc::text(" = "),
                print_mod_expr(state, mod_expr_to_print, cmt_tbl, arena),
            ]);

            rows.push(BlockRow {
                pos_range,
                start_line: start.line as usize,
                end_line: end.line as usize,
                doc: let_module_doc,
            });
            collect_block_rows_inner(state, arena.get_expr(*body_idx), rows, cmt_tbl, arena);
        }

        ExpressionDesc::Pexp_letexception(inner) => {
            let (ref ext_constr, ref body_idx) = **inner;
            // Use combined location (expr start to ext_constr end) to match walker
            let base_start = arena.loc_start(expr.pexp_loc);
            let end = arena.loc_end(ext_constr.pext_loc);
            let pos_range = PosRange {
                start: base_start.cnum,
                end: end.cnum,
            };

            // Extend start_line to leading comment if present (matching OCaml's location extension)
            let start_line = match cmt_tbl.get_first_leading_comment_by_pos(pos_range) {
                Some(comment) => comment.loc().loc_start.line as usize,
                None => base_start.line as usize,
            };

            let let_exception_doc = print_exception_def(state, ext_constr, cmt_tbl, arena);

            rows.push(BlockRow {
                pos_range,
                start_line,
                end_line: end.line as usize,
                doc: let_exception_doc,
            });
            collect_block_rows_inner(state, arena.get_expr(*body_idx), rows, cmt_tbl, arena);
        }

        ExpressionDesc::Pexp_open(inner) => {
            let (ref override_flag, ref lid, ref body_idx) = **inner;
            // Use combined location (expr start to lid end) to match walker
            let start = arena.loc_start(expr.pexp_loc);
            let end = arena.loc_end(lid.loc);
            let pos_range = PosRange {
                start: start.cnum,
                end: end.cnum,
            };

            let open_doc = Doc::concat(vec![
                Doc::text("open"),
                match override_flag {
                    OverrideFlag::Override => Doc::text("!"),
                    OverrideFlag::Fresh => Doc::nil(),
                },
                Doc::space(),
                print_longident_location(lid, cmt_tbl, arena),
            ]);

            rows.push(BlockRow {
                pos_range,
                start_line: start.line as usize,
                end_line: end.line as usize,
                doc: open_doc,
            });
            collect_block_rows_inner(state, arena.get_expr(*body_idx), rows, cmt_tbl, arena);
        }

        ExpressionDesc::Pexp_sequence(e1_idx, e2_idx) => {
            let e1 = arena.get_expr(*e1_idx);
            let e2 = arena.get_expr(*e2_idx);
            // Use e1's location directly
            let start = arena.loc_start(e1.pexp_loc);
            let end = arena.loc_end(e1.pexp_loc);
            let pos_range = PosRange {
                start: start.cnum,
                end: end.cnum,
            };

            let expr_doc = {
                let doc = print_expression(state, e1, cmt_tbl, arena);
                match parens::expr(arena, e1) {
                    ParenKind::Parenthesized => add_parens(doc),
                    ParenKind::Braced(loc) => print_braces(doc, e1, loc, arena),
                    ParenKind::Nothing => doc,
                }
            };

            rows.push(BlockRow {
                pos_range,
                start_line: start.line as usize,
                end_line: end.line as usize,
                doc: expr_doc,
            });
            collect_block_rows_inner(state, e2, rows, cmt_tbl, arena);
        }

        ExpressionDesc::Pexp_let(inner) => {
            let (ref rec_flag, ref bindings, ref body_idx) = **inner;
            // Use first binding's location for comment lookup, matching OCaml's logic
            let (pos_range, base_start_line, end_line) =
                if let (Some(first), Some(last)) = (bindings.first(), bindings.last()) {
                    // Get the binding location matching what the walker uses
                    let first_pat = arena.get_pat(first.pvb_pat);
                    let first_expr = arena.get_expr(first.pvb_expr);
                    let binding_loc = if arena.loc_ghost(first_pat.ppat_loc) {
                        first_expr.pexp_loc
                    } else {
                        first.pvb_loc
                    };
                    let base_start = arena.loc_start(binding_loc);
                    let end = arena.loc_end(last.pvb_loc);
                    let pos_range = PosRange {
                        start: base_start.cnum,
                        end: end.cnum,
                    };

                    (pos_range, base_start.line as usize, end.line as usize)
                } else {
                    let start = arena.loc_start(expr.pexp_loc);
                    let end = arena.loc_end(expr.pexp_loc);
                    let pos_range = PosRange {
                        start: start.cnum,
                        end: end.cnum,
                    };
                    (pos_range, start.line as usize, end.line as usize)
                };

            // Extend start_line to leading comment if present (matching OCaml's location extension)
            let start_line = match cmt_tbl.get_first_leading_comment_by_pos(pos_range) {
                Some(comment) => comment.loc().loc_start.line as usize,
                None => base_start_line,
            };

            let rec_doc = match rec_flag {
                RecFlag::Nonrecursive => Doc::nil(),
                RecFlag::Recursive => Doc::text("rec "),
            };

            let let_doc = print_value_bindings_with_rec(state, bindings, &rec_doc, cmt_tbl, arena);

            rows.push(BlockRow {
                pos_range,
                start_line,
                end_line,
                doc: let_doc,
            });

            // Special case: if body is just (), don't print it
            // This matches OCaml: let () = { let () = foo(); () }
            let body = arena.get_expr(*body_idx);
            if !is_unit_expr(arena, body) {
                collect_block_rows_inner(state, body, rows, cmt_tbl, arena);
            }
        }

        _ => {
            // Terminal expression
            let start = arena.loc_start(expr.pexp_loc);
            let end = arena.loc_end(expr.pexp_loc);
            let pos_range = PosRange {
                start: start.cnum,
                end: end.cnum,
            };

            let expr_doc = {
                let doc = print_expression(state, expr, cmt_tbl, arena);
                match parens::expr(arena, expr) {
                    ParenKind::Parenthesized => add_parens(doc),
                    ParenKind::Braced(loc) => print_braces(doc, expr, loc, arena),
                    ParenKind::Nothing => doc,
                }
            };

            rows.push(BlockRow {
                pos_range,
                start_line: start.line as usize,
                end_line: end.line as usize,
                doc: expr_doc,
            });
        }
    }
}

/// Print value bindings with a pre-computed rec_doc (for use in expression blocks).
fn print_value_bindings_with_rec(
    state: &PrinterState,
    bindings: &[ValueBinding],
    rec_doc: &Doc,
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    print_listi(
        |vb: &ValueBinding| vb.pvb_loc,
        bindings,
        |vb, cmt_tbl_inner, i| print_value_binding(state, vb, i, rec_doc, cmt_tbl_inner, arena),
        cmt_tbl,
        arena,
        false, // ignore_empty_lines
        false, // force_break
    )
}

/// Check if an expression is an array of tuples (for dict detection)
fn is_tuple_array(arena: &ParseArena, expr: &Expression) -> bool {
    parsetree_viewer::is_tuple_array(arena, expr)
}

/// Try to print dict{} syntax for Primitive_dict.make([("key", value), ...])
fn try_print_dict_expr(
    state: &PrinterState,
    expr: &Expression,
    funct: &Expression,
    args: &[(ArgLabel, ExprIdx)],
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Option<Doc> {
    // Check if funct is Primitive_dict.make
    if let ExpressionDesc::Pexp_ident(lid) = &*funct.pexp_desc {
        let longident = arena.get_longident(lid.txt);
        if let Longident::Ldot(parent_box, make_idx) = longident {
            let make_str = arena.get_string(*make_idx);
            if let Longident::Lident(prim_idx) = parent_box.as_ref() {
                let prim_str = arena.get_string(*prim_idx);
                if prim_str == "Primitive_dict" && make_str == "make" {
                    // Check if args has exactly one Nolabel argument that's an array of tuples
                    if args.len() == 1 {
                        if let (ArgLabel::Nolabel, key_values) = &args[0] {
                            let key_values = arena.get_expr(*key_values);
                            if is_tuple_array(arena, key_values) {
                                return Some(print_dict_expr(
                                    state, expr, key_values, cmt_tbl, arena,
                                ));
                            }
                        }
                    }
                }
            }
        }
    }
    None
}

/// Print dict{key: value, ...} syntax
/// Matches OCaml's print_literal_dict_expr and print_bs_object_row
fn print_dict_rows(
    state: &PrinterState,
    key_values: &Expression,
    leading_line: bool,
    trailing_comma: bool,
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    let rows: Vec<Doc> = if let ExpressionDesc::Pexp_array(items) = &*key_values.pexp_desc {
        items
            .iter()
            .filter_map(|tuple_expr| {
                let tuple_expr = arena.get_expr(*tuple_expr);
                if let ExpressionDesc::Pexp_tuple(tuple_items) = &*tuple_expr.pexp_desc {
                    if tuple_items.len() == 2 {
                        let key_expr = arena.get_expr(tuple_items[0]);
                        let value_expr = arena.get_expr(tuple_items[1]);
                        // Key should be a string constant
                        if let ExpressionDesc::Pexp_constant(c) = &*key_expr.pexp_desc {
                            if let Constant::String(payload) = &**c {
                                let txt = payload.semantic();
                                // Create combined location from key to value (for row comments)
                                let (cmt_pos_range, cmt_full_loc) = make_combined_pos_range(
                                    key_expr.pexp_loc,
                                    value_expr.pexp_loc,
                                    arena,
                                );

                                // Print key with its comments
                                let key_doc = Doc::concat(vec![
                                    Doc::text("\""),
                                    Doc::text(txt.clone()),
                                    Doc::text("\""),
                                ]);
                                let key_doc =
                                    print_comments(key_doc, cmt_tbl, key_expr.pexp_loc, arena);

                                // Print value with its comments
                                let value_doc = print_expression_with_comments(
                                    state, value_expr, cmt_tbl, arena,
                                );

                                // Combine key: value
                                let row_doc =
                                    Doc::concat(vec![key_doc, Doc::text(": "), value_doc]);

                                // Wrap with comments for the combined location (key to value)
                                let row_doc = print_comments_by_pos(
                                    row_doc,
                                    cmt_tbl,
                                    cmt_pos_range,
                                    &cmt_full_loc,
                                );

                                // Then wrap with comments for the tuple's location (entire entry)
                                let row_doc =
                                    print_comments(row_doc, cmt_tbl, tuple_expr.pexp_loc, arena);

                                return Some(row_doc);
                            }
                        }
                    }
                }
                None
            })
            .collect()
    } else {
        vec![]
    };

    let rows_empty = rows.is_empty();
    let rows_doc = Doc::join(Doc::concat(vec![Doc::text(","), Doc::line()]), rows);
    let force_break = arena.loc_start(key_values.pexp_loc).line
        < arena.loc_end(key_values.pexp_loc).line
        || rows_doc.will_break();
    Doc::breakable_group(
        Doc::concat(vec![
            Doc::indent(Doc::concat(vec![
                if rows_empty || !leading_line {
                    Doc::nil()
                } else {
                    Doc::soft_line()
                },
                rows_doc,
            ])),
            if rows_empty || !trailing_comma {
                Doc::nil()
            } else {
                Doc::concat(vec![Doc::trailing_comma(), Doc::soft_line()])
            },
        ]),
        force_break,
    )
}

fn print_dict_expr(
    state: &PrinterState,
    expr: &Expression,
    key_values: &Expression,
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    Doc::concat(vec![
        Doc::text("dict{"),
        print_comments_inside(cmt_tbl, expr.pexp_loc, arena),
        print_dict_rows(state, key_values, true, true, cmt_tbl, arena),
        Doc::rbrace(),
    ])
}

fn print_spread_dict_expr(
    state: &PrinterState,
    parts: &[parsetree_viewer::DictExprPart<'_>],
    expr: &Expression,
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    let mut part_docs = Vec::with_capacity(parts.len());
    for part in parts {
        match part {
            parsetree_viewer::DictExprPart::Rows(rows) => {
                part_docs.push(print_dict_rows(state, rows, false, false, cmt_tbl, arena))
            }
            parsetree_viewer::DictExprPart::Spread(spread) => {
                let leading = print_leading_comments(Doc::nil(), cmt_tbl, spread.pexp_loc, arena);
                let spread_doc = print_expression(state, spread, cmt_tbl, arena);
                let spread_doc = match parens::expr_allowing_coercion(arena, spread) {
                    ParenKind::Parenthesized => add_parens(spread_doc),
                    ParenKind::Braced(braces) => print_braces(spread_doc, spread, braces, arena),
                    ParenKind::Nothing => spread_doc,
                };
                let full_loc = arena.to_location(spread.pexp_loc);
                let trailing = cmt_tbl.remove_trailing_comments_by_loc(spread.pexp_loc, arena);
                let spread_doc = print_trailing_comments_with(spread_doc, trailing, &full_loc);
                part_docs.push(Doc::concat(vec![leading, Doc::dotdotdot(), spread_doc]));
            }
        }
    }

    let parts_empty = part_docs.is_empty();
    let parts_doc = Doc::join(Doc::concat(vec![Doc::text(","), Doc::line()]), part_docs);
    let inside_comments = print_comments_inside(cmt_tbl, expr.pexp_loc, arena);
    let force_break = arena.loc_start(expr.pexp_loc).line < arena.loc_end(expr.pexp_loc).line
        || inside_comments.will_break()
        || parts_doc.will_break();

    Doc::breakable_group(
        Doc::concat(vec![
            Doc::text("dict{"),
            inside_comments,
            Doc::indent(Doc::concat(vec![
                if parts_empty {
                    Doc::nil()
                } else {
                    Doc::soft_line()
                },
                parts_doc,
            ])),
            if parts_empty {
                Doc::nil()
            } else {
                Doc::concat(vec![Doc::trailing_comma(), Doc::soft_line()])
            },
            Doc::rbrace(),
        ]),
        force_break,
    )
}

/// Check if expression has res.taggedTemplate attribute
/// OCaml `print_tagged_template_literal`.
fn print_tagged_template_literal(
    state: &PrinterState,
    tag: &Expression,
    raw_sources: &[StringLoc],
    values: &[ExprIdx],
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    let strings: Vec<Doc> = raw_sources
        .iter()
        .map(|source| print_string_contents(arena.get_string(source.txt)))
        .collect();
    let values: Vec<Doc> = values
        .iter()
        .map(|value| {
            Doc::concat(vec![
                Doc::text("${"),
                print_expression_with_comments(state, arena.get_expr(*value), cmt_tbl, arena),
                Doc::text("}"),
            ])
        })
        .collect();
    let content = interleave_template_parts(strings, values);
    let tag_doc = print_expression_with_comments(state, tag, cmt_tbl, arena);
    Doc::concat(vec![tag_doc, Doc::text("`"), content, Doc::text("`")])
}

/// Print spread array syntax: Primitive_array.spread([xs, [a, b]]) -> [...xs, a, b]
fn print_belt_array_concat_apply(
    state: &PrinterState,
    sub_lists: &[ExprIdx],
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    // Collect all elements (regular and spread) into a flat list with commas
    let mut elements: Vec<Doc> = Vec::new();

    for sub_list_idx in sub_lists {
        let sub_list = arena.get_expr(*sub_list_idx);
        let (expressions, spread) = parsetree_viewer::collect_array_expressions(arena, sub_list);

        // Print regular expressions
        for expr in expressions {
            if !elements.is_empty() {
                elements.push(Doc::text(","));
                elements.push(Doc::line());
            }
            let doc = print_expression_with_comments(state, expr, cmt_tbl, arena);
            let doc = match parens::expr_allowing_coercion(arena, expr) {
                ParenKind::Parenthesized => add_parens(doc),
                ParenKind::Braced(braces) => print_braces(doc, expr, braces, arena),
                ParenKind::Nothing => doc,
            };
            elements.push(doc);
        }

        // Print spread expression if present
        if let Some(expr) = spread {
            if !elements.is_empty() {
                elements.push(Doc::text(","));
                elements.push(Doc::line());
            }

            // Extract leading comments to print before dotdotdot
            let full_loc = arena.to_location(expr.pexp_loc);
            let leading_comments = cmt_tbl.remove_leading_comments_by_loc(expr.pexp_loc, arena);
            let leading_comments_doc =
                print_leading_comments_with(Doc::nil(), leading_comments, &full_loc);

            // Print expression (without leading comments which we extracted above)
            let expr_doc = {
                let doc = print_expression(state, expr, cmt_tbl, arena);
                match parens::expr_allowing_coercion(arena, expr) {
                    ParenKind::Parenthesized => add_parens(doc),
                    ParenKind::Braced(braces) => print_braces(doc, expr, braces, arena),
                    ParenKind::Nothing => doc,
                }
            };

            // Extract and print trailing comments
            let trailing_comments = cmt_tbl.remove_trailing_comments_by_loc(expr.pexp_loc, arena);
            let expr_with_trailing =
                print_trailing_comments_with(expr_doc, trailing_comments, &full_loc);

            elements.push(leading_comments_doc);
            elements.push(Doc::dotdotdot());
            elements.push(expr_with_trailing);
        }
    }

    Doc::group(Doc::concat(vec![
        Doc::lbracket(),
        Doc::indent(Doc::concat(vec![Doc::soft_line(), Doc::concat(elements)])),
        Doc::trailing_comma(),
        Doc::soft_line(),
        Doc::rbracket(),
    ]))
}

/// Print spread list syntax: Primitive_list.spread([xs, [a, b]]) -> list{...xs, a, b}
fn print_belt_list_concat_apply(
    state: &PrinterState,
    sub_lists: &[ExprIdx],
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    // Collect all elements (regular and spread) into a flat list with commas
    let mut elements: Vec<Doc> = Vec::new();

    for sub_list_idx in sub_lists {
        let sub_list = arena.get_expr(*sub_list_idx);
        let (expressions, spread) = parsetree_viewer::collect_list_expressions(arena, sub_list);

        // Print regular expressions
        for expr in expressions {
            if !elements.is_empty() {
                elements.push(Doc::text(","));
                elements.push(Doc::line());
            }
            let doc = print_expression_with_comments(state, expr, cmt_tbl, arena);
            let doc = match parens::expr_allowing_coercion(arena, expr) {
                ParenKind::Parenthesized => add_parens(doc),
                ParenKind::Braced(braces) => print_braces(doc, expr, braces, arena),
                ParenKind::Nothing => doc,
            };
            elements.push(doc);
        }

        // Print spread expression if present
        if let Some(expr) = spread {
            if !elements.is_empty() {
                elements.push(Doc::text(","));
                elements.push(Doc::line());
            }
            let expr_doc = {
                let doc = print_expression_with_comments(state, expr, cmt_tbl, arena);
                match parens::expr_allowing_coercion(arena, expr) {
                    ParenKind::Parenthesized => add_parens(doc),
                    ParenKind::Braced(braces) => print_braces(doc, expr, braces, arena),
                    ParenKind::Nothing => doc,
                }
            };
            elements.push(Doc::dotdotdot());
            elements.push(expr_doc);
        }
    }

    Doc::group(Doc::concat(vec![
        Doc::text("list{"),
        Doc::indent(Doc::concat(vec![Doc::soft_line(), Doc::concat(elements)])),
        Doc::trailing_comma(),
        Doc::soft_line(),
        Doc::rbrace(),
    ]))
}

/// Print template literal: `foo ${bar}` reconstructed from concatenation.
/// OCaml desugars `foo ${bar}` to `"foo " ++ bar ++ ""` with @res.template attribute.
fn print_template_literal(
    state: &PrinterState,
    source_segments: &[StringLoc],
    values: &[ExprIdx],
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    let strings: Vec<Doc> = source_segments
        .iter()
        .map(|source| print_string_contents(arena.get_string(source.txt)))
        .collect();
    let values: Vec<Doc> = values
        .iter()
        .map(|value| {
            let expr = arena.get_expr(*value);
            let doc = print_expression_with_comments(state, expr, cmt_tbl, arena);
            let doc = match parens::expr(arena, expr) {
                ParenKind::Parenthesized => add_parens(doc),
                ParenKind::Braced(braces) => print_braces(doc, expr, braces, arena),
                ParenKind::Nothing => doc,
            };
            Doc::group(Doc::concat(vec![
                Doc::text("${"),
                Doc::indent(doc),
                Doc::rbrace(),
            ]))
        })
        .collect();
    let content = interleave_template_parts(strings, values);
    Doc::concat(vec![Doc::text("`"), content, Doc::text("`")])
}

/// Get the body of an underscore apply sugar expression.
/// (__x) => body -> body
fn get_underscore_apply_body<'a>(expr: &'a Expression, arena: &'a ParseArena) -> &'a Expression {
    match &*expr.pexp_desc {
        ExpressionDesc::Pexp_fun(inner) => arena.get_expr(inner.rhs),
        _ => expr,
    }
}

/// Check if the first argument is the underscore placeholder.
fn first_arg_is_underscore(args: &[(ArgLabel, ExprIdx)], arena: &ParseArena) -> bool {
    if let Some((ArgLabel::Nolabel, expr_idx)) = args.first() {
        parsetree_viewer::is_underscore_ident(arena.get_expr(*expr_idx), arena)
    } else {
        false
    }
}

/// Check if any argument after the first is the underscore placeholder.
fn rest_args_have_underscore(args: &[(ArgLabel, ExprIdx)], arena: &ParseArena) -> bool {
    args.iter().skip(1).any(|(_, expr_idx)| {
        parsetree_viewer::is_underscore_ident(arena.get_expr(*expr_idx), arena)
    })
}

/// Print underscore apply in pipe context: `a->f(_)` -> `a->f`.
/// When underscore apply sugar has __x only in the first position, omit it entirely.
/// `(__x) => f(__x, a, b)` in pipe context prints as just `f(a, b)`.
fn print_underscore_apply_in_pipe(
    state: &PrinterState,
    expr: &Expression,
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    if !parsetree_viewer::is_underscore_apply_sugar(arena, expr) {
        return print_expression_with_comments(state, expr, cmt_tbl, arena);
    }

    let body_expr = get_underscore_apply_body(expr, arena);

    match &*body_expr.pexp_desc {
        ExpressionDesc::Pexp_apply(apply_inner) => {
            let PexpApply {
                ref funct,
                ref args,
                ..
            } = **apply_inner;
            let funct = arena.get_expr(*funct);
            // res_parsetree_viewer.ml:145-175: a sole `__x` in first position
            // is dropped; otherwise fall back to the regular rewrite.
            if first_arg_is_underscore(args, arena) && !rest_args_have_underscore(args, arena) {
                print_underscore_apply_call(state, funct, &args[1..], cmt_tbl, arena)
            } else {
                print_underscore_apply(state, body_expr, cmt_tbl, arena)
            }
        }
        _ => print_expression_with_comments(state, expr, cmt_tbl, arena),
    }
}

/// Print the application built by `rewrite_underscore_apply` /
/// `rewrite_underscore_apply_in_pipe` (res_parsetree_viewer.ml:82-175, with
/// `partial = false`) through the regular `Pexp_apply` printing
/// (res_printer.ml:4758-4817), substituting `__x` by `_`.
fn print_underscore_apply_call(
    state: &PrinterState,
    funct: &Expression,
    args: &[(ArgLabel, ExprIdx)],
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    let funct_doc = print_expression_with_comments(state, funct, cmt_tbl, arena);
    let funct_doc = match parens::call_expr(arena, funct) {
        ParenKind::Parenthesized => add_parens(funct_doc),
        ParenKind::Braced(loc) => print_braces(funct_doc, funct, loc, arena),
        ParenKind::Nothing => funct_doc,
    };
    // Note: OCaml checks this AFTER rewriting __x to _, so __x args are treated
    // as regular identifiers (not callbacks) in this check.
    let requires_regular_layout = arguments_require_regular_layout(cmt_tbl, args, arena);
    if !requires_regular_layout
        && parsetree_viewer::requires_special_callback_printing_first_arg(arena, args, false)
    {
        let args_doc = print_arguments_with_callback_in_first_position_underscore_subst(
            state, args, false, cmt_tbl, arena,
        );
        Doc::concat(vec![funct_doc, args_doc])
    } else if !requires_regular_layout
        && parsetree_viewer::requires_special_callback_printing_last_arg(arena, args, false)
    {
        let args_doc = print_arguments_with_callback_in_last_position_underscore_subst(
            state, args, false, cmt_tbl, arena,
        );
        let maybe_break_parent = if args_doc.will_break() {
            Doc::break_parent()
        } else {
            Doc::nil()
        };
        Doc::concat(vec![maybe_break_parent, funct_doc, args_doc])
    } else {
        let args_doc = print_arguments_with_underscore_subst(state, args, false, cmt_tbl, arena);
        Doc::concat(vec![funct_doc, args_doc])
    }
}

/// Print underscore apply sugar: `(__x) => f(a, __x, c)` prints as `f(a, _, c)`.
/// This prints the inner apply expression with __x replaced by _ at print time.
///
/// Note: OCaml rewrites the AST with `rewrite_underscore_apply` before printing,
/// which replaces `__x` with `_`. Then the regular callback detection/printing
/// happens. Since we can't modify the AST in Rust, we need to integrate the
/// underscore substitution into the callback printing logic here.
fn print_underscore_apply(
    state: &PrinterState,
    inner: &Expression,
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    match &*inner.pexp_desc {
        ExpressionDesc::Pexp_apply(apply_inner) => {
            let PexpApply {
                ref funct,
                ref args,
                ..
            } = **apply_inner;
            let funct = arena.get_expr(*funct);
            print_underscore_apply_call(state, funct, args, cmt_tbl, arena)
        }
        _ => print_expression_with_comments(state, inner, cmt_tbl, arena),
    }
}

/// Print a single argument with __x substituted by _.
fn print_argument_with_underscore_subst(
    state: &PrinterState,
    label: &ArgLabel,
    expr_idx: &ExprIdx,
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    let expr = arena.get_expr(*expr_idx);
    // Check if this is __x and print _ instead
    if parsetree_viewer::is_underscore_ident(expr, arena) {
        match label {
            ArgLabel::Nolabel => {
                let doc = Doc::text("_");
                print_comments(doc, cmt_tbl, expr.pexp_loc, arena)
            }
            ArgLabel::Labelled(name) => {
                let name_str = arena.get_string(name.txt);
                Doc::concat(vec![
                    Doc::text("~"),
                    print_ident_like(name_str, false, false),
                    Doc::text("=_"),
                ])
            }
            ArgLabel::Optional(name) => {
                let name_str = arena.get_string(name.txt);
                Doc::concat(vec![
                    Doc::text("~"),
                    print_ident_like(name_str, false, false),
                    Doc::text("=?_"),
                ])
            }
        }
    } else {
        // Use regular argument printing for non-__x arguments
        print_argument(state, label, expr, cmt_tbl, arena)
    }
}

/// Print arguments with __x substituted by _.
fn print_arguments_with_underscore_subst(
    state: &PrinterState,
    args: &[(ArgLabel, ExprIdx)],
    partial: bool,
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    if args.is_empty() {
        return Doc::text("()");
    }

    // res_printer.ml print_arguments `force_break`.
    let force_break = args.iter().any(|(label, arg)| {
        let arg = arena.get_expr(*arg);
        matches!(&*arg.pexp_desc, ExpressionDesc::Pexp_fun(_))
            && (cmt_tbl.has_any_trailing_line_comment_at(PosRange::argument(arena, label, arg))
                || cmt_tbl
                    .has_any_trailing_line_comment_at(PosRange::from_loc(arg.pexp_loc, arena)))
    });
    let mut all_docs: Vec<Doc> = args
        .iter()
        .map(|(lbl, arg)| print_argument_with_underscore_subst(state, lbl, arg, cmt_tbl, arena))
        .collect();
    if partial {
        all_docs.push(Doc::text("..."));
    }

    Doc::breakable_group(
        Doc::concat(vec![
            Doc::lparen(),
            Doc::indent(Doc::concat(vec![
                Doc::soft_line(),
                Doc::join(Doc::concat(vec![Doc::text(","), Doc::line()]), all_docs),
            ])),
            // Don't add trailing comma for partial application
            if partial {
                Doc::nil()
            } else {
                Doc::trailing_comma()
            },
            Doc::soft_line(),
            Doc::rparen(),
        ]),
        force_break,
    )
}

/// Print arguments with callback in first position, with underscore substitution.
/// This is used when printing underscore apply sugar that has a callback in first position.
fn print_arguments_with_callback_in_first_position_underscore_subst(
    state: &PrinterState,
    args: &[(ArgLabel, ExprIdx)],
    partial: bool,
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    // Because the same subtree gets printed twice, we need to copy the cmt_tbl.
    let state = state.next_custom_layout();

    // If we should break callback due to nesting depth, just break all args
    if state.should_break_callback() {
        return print_arguments_with_underscore_subst(&state, args, partial, cmt_tbl, arena);
    }

    let cmt_tbl_copy = cmt_tbl.copy();

    // Split args into callback and non-callback args
    let (callback_doc, printed_args_doc) =
        if let Some(((label, expr_idx), rest)) = args.split_first() {
            let expr = arena.get_expr(*expr_idx);
            // Print label prefix for the callback
            let lbl_doc = print_arg_label_prefix(label, arena);

            // Print callback - it may itself be underscore apply sugar
            let callback = if parsetree_viewer::is_underscore_apply_sugar(arena, expr) {
                let inner = get_underscore_apply_body(expr, arena);
                let doc = Doc::concat(vec![
                    lbl_doc,
                    print_underscore_apply(&state, inner, cmt_tbl, arena),
                ]);
                print_comments(doc, cmt_tbl, expr.pexp_loc, arena)
            } else {
                let pexp_fun_doc =
                    print_pexp_fun(&state, InCallback::FitsOnOneLine, expr, cmt_tbl, arena);
                let doc = Doc::concat(vec![lbl_doc, pexp_fun_doc]);
                print_comments(doc, cmt_tbl, expr.pexp_loc, arena)
            };

            // Print non-callback args with underscore substitution
            let mut printed_args = Vec::new();
            for (lbl, arg) in rest {
                printed_args.push(print_argument_with_underscore_subst(
                    &state, lbl, arg, cmt_tbl, arena,
                ));
            }
            if partial {
                printed_args.push(Doc::text("..."));
            }
            let printed_args_doc =
                Doc::join(Doc::concat(vec![Doc::comma(), Doc::line()]), printed_args);

            (callback, printed_args_doc)
        } else {
            return Doc::text("()");
        };

    // Thing.map((arg1, arg2) => MyModuleBlah.toList(argument), foo)
    let fits_on_one_line = Doc::concat(vec![
        Doc::lparen(),
        callback_doc,
        Doc::comma(),
        Doc::line(),
        printed_args_doc.clone(),
        Doc::rparen(),
    ]);

    // Thing.map(
    //   (param1, parm2) => doStuff(param1, parm2),
    //   arg1,
    //   arg2,
    // )
    let break_all_args = {
        let mut cmt_tbl_for_break = cmt_tbl_copy;
        print_arguments_with_underscore_subst(&state, args, partial, &mut cmt_tbl_for_break, arena)
    };

    // Check if any non-callback args will break
    if printed_args_doc.will_break() {
        return break_all_args;
    }

    Doc::custom_layout(vec![fits_on_one_line, break_all_args])
}

/// Print arguments with callback in last position, with underscore substitution.
/// This is used when printing underscore apply sugar that has a callback in last position.
fn print_arguments_with_callback_in_last_position_underscore_subst(
    state: &PrinterState,
    args: &[(ArgLabel, ExprIdx)],
    partial: bool,
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    // Because the same subtree gets printed twice, we need to copy the cmt_tbl.
    let state = state.next_custom_layout();

    // If we should break callback due to nesting depth, just break all args
    if state.should_break_callback() {
        return print_arguments_with_underscore_subst(&state, args, partial, cmt_tbl, arena);
    }

    let cmt_tbl_copy = cmt_tbl.copy();
    let cmt_tbl_copy2 = cmt_tbl.copy();

    // Split args into non-callback args and the callback
    let (non_callback_args, callback) = if let Some(((label, expr_idx), rest)) = args.split_last() {
        let expr = arena.get_expr(*expr_idx);
        // Print label prefix for the callback
        let lbl_doc = print_arg_label_prefix(label, arena);

        // Print non-callback args with underscore substitution
        let mut printed_args = Vec::new();
        for (lbl, arg) in rest {
            printed_args.push(print_argument_with_underscore_subst(
                &state, lbl, arg, cmt_tbl, arena,
            ));
        }
        let printed_args_doc = if printed_args.is_empty() {
            Doc::nil()
        } else {
            Doc::concat(vec![
                Doc::join(Doc::concat(vec![Doc::comma(), Doc::line()]), printed_args),
                Doc::comma(),
                Doc::line(),
            ])
        };

        // Callback that fits on one line - may itself be underscore apply sugar
        let callback_fits_on_one_line = if parsetree_viewer::is_underscore_apply_sugar(arena, expr)
        {
            let inner = get_underscore_apply_body(expr, arena);
            let mut cmt_tbl_for_callback = cmt_tbl.copy();
            let doc = Doc::concat(vec![
                lbl_doc.clone(),
                print_underscore_apply(&state, inner, &mut cmt_tbl_for_callback, arena),
            ]);
            print_comments(doc, &mut cmt_tbl_for_callback, expr.pexp_loc, arena)
        } else {
            let mut cmt_tbl_for_callback = cmt_tbl.copy();
            let pexp_fun_doc = print_pexp_fun(
                &state,
                InCallback::FitsOnOneLine,
                expr,
                &mut cmt_tbl_for_callback,
                arena,
            );
            let doc = Doc::concat(vec![lbl_doc.clone(), pexp_fun_doc]);
            print_comments(doc, &mut cmt_tbl_for_callback, expr.pexp_loc, arena)
        };

        // Callback with arguments fitting on one line (body may break)
        let callback_args_fit_on_one_line =
            if parsetree_viewer::is_underscore_apply_sugar(arena, expr) {
                let inner = get_underscore_apply_body(expr, arena);
                let mut cmt_tbl_for_callback = cmt_tbl_copy.clone();
                let doc = Doc::concat(vec![
                    lbl_doc,
                    print_underscore_apply(&state, inner, &mut cmt_tbl_for_callback, arena),
                ]);
                print_comments(doc, &mut cmt_tbl_for_callback, expr.pexp_loc, arena)
            } else {
                let mut cmt_tbl_for_callback = cmt_tbl_copy.clone();
                let pexp_fun_doc = print_pexp_fun(
                    &state,
                    InCallback::ArgumentsFitOnOneLine,
                    expr,
                    &mut cmt_tbl_for_callback,
                    arena,
                );
                let doc = Doc::concat(vec![lbl_doc, pexp_fun_doc]);
                print_comments(doc, &mut cmt_tbl_for_callback, expr.pexp_loc, arena)
            };

        (
            printed_args_doc,
            (callback_fits_on_one_line, callback_args_fit_on_one_line),
        )
    } else {
        return Doc::text("()");
    };

    let (callback_fits_on_one_line, callback_args_fit_on_one_line) = callback;

    // Break all args fallback
    let break_all_args = {
        let mut cmt_tbl_for_break = cmt_tbl_copy2;
        print_arguments_with_underscore_subst(&state, args, partial, &mut cmt_tbl_for_break, arena)
    };

    // Check if any non-callback args will break
    if non_callback_args.will_break() {
        return break_all_args;
    }

    // Thing.map(foo, (arg1, arg2) => MyModuleBlah.toList(argument))
    let fits_on_one_line = Doc::concat(vec![
        Doc::lparen(),
        non_callback_args.clone(),
        callback_fits_on_one_line,
        Doc::rparen(),
    ]);

    // Thing.map(longArgument, veryLooooongArgument, (arg1, arg2) =>
    //   MyModuleBlah.toList(argument)
    // )
    let arguments_fit_on_one_line = Doc::concat(vec![
        Doc::lparen(),
        non_callback_args,
        Doc::breakable_group(callback_args_fit_on_one_line, true),
        Doc::rparen(),
    ]);

    Doc::custom_layout(vec![
        fits_on_one_line,
        arguments_fit_on_one_line,
        break_all_args,
    ])
}

/// Print function application.
/// The member of an `Array.get`/`Array.set` access (res_printer.ml:4639-4657).
fn print_array_access_member(
    state: &PrinterState,
    member_expr: &Expression,
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    let member_doc = {
        let doc = print_expression_with_comments(state, member_expr, cmt_tbl, arena);
        match parens::expr_allowing_coercion(arena, member_expr) {
            ParenKind::Parenthesized => add_parens(doc),
            ParenKind::Braced(braces) => print_braces(doc, member_expr, braces, arena),
            ParenKind::Nothing => doc,
        }
    };
    let should_inline = matches!(
        &*member_expr.pexp_desc,
        ExpressionDesc::Pexp_constant(_)
            | ExpressionDesc::Pexp_ident(_)
            | ExpressionDesc::Pexp_braces(_)
    );
    if should_inline {
        member_doc
    } else {
        Doc::concat(vec![
            Doc::indent(Doc::concat(vec![Doc::soft_line(), member_doc])),
            Doc::soft_line(),
        ])
    }
}

fn print_unary_expr_operand(
    state: &PrinterState,
    expr: &Expression,
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    let doc = print_expression_with_comments(state, expr, cmt_tbl, arena);
    match parens::unary_expr_operand(arena, expr) {
        ParenKind::Parenthesized => add_parens(doc),
        ParenKind::Braced(braces) => print_braces(doc, expr, braces, arena),
        ParenKind::Nothing => doc,
    }
}

fn print_expr_with_parens(
    state: &PrinterState,
    expr: &Expression,
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    let doc = print_expression_with_comments(state, expr, cmt_tbl, arena);
    match parens::expr(arena, expr) {
        ParenKind::Parenthesized => add_parens(doc),
        ParenKind::Braced(braces) => print_braces(doc, expr, braces, arena),
        ParenKind::Nothing => doc,
    }
}

/// `Array.get(parent, member)` printed as `parent[member]`
/// (res_printer.ml:4628-4674).
fn print_array_get_apply(
    state: &PrinterState,
    expr: &Expression,
    parent_expr: &Expression,
    member_expr: &Expression,
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    let member = print_array_access_member(state, member_expr, cmt_tbl, arena);
    let parent_doc = print_unary_expr_operand(state, parent_expr, cmt_tbl, arena);
    Doc::group(Doc::concat(vec![
        print_attributes(state, &expr.pexp_attributes, cmt_tbl, arena),
        parent_doc,
        Doc::lbracket(),
        member,
        Doc::rbracket(),
    ]))
}

/// `Array.set(parent, member, target)` printed as `parent[member] = target`
/// (res_printer.ml:4675-4757).
fn print_array_set_apply(
    state: &PrinterState,
    expr: &Expression,
    parent_expr: &Expression,
    member_expr: &Expression,
    target_expr: &Expression,
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    let member = print_array_access_member(state, member_expr, cmt_tbl, arena);
    let should_indent_target_expr = if parsetree_viewer::is_braced_expr(target_expr) {
        false
    } else {
        parsetree_viewer::is_binary_expression(arena, target_expr)
            || match &*target_expr.pexp_desc {
                ExpressionDesc::Pexp_ifthenelse(ite)
                    if target_expr.pexp_attributes.len() == 1
                        && arena.get_string(target_expr.pexp_attributes[0].0.txt)
                            == "res.ternary" =>
                {
                    let if_expr = arena.get_expr(ite.0);
                    parsetree_viewer::is_binary_expression(arena, if_expr)
                        || parsetree_viewer::has_attributes(arena, &if_expr.pexp_attributes)
                }
                _ => {
                    parsetree_viewer::has_attributes(arena, &target_expr.pexp_attributes)
                        || parsetree_viewer::is_array_access(arena, target_expr)
                }
            }
    };
    let target_doc = print_expr_with_parens(state, target_expr, cmt_tbl, arena);
    let parent_doc = print_unary_expr_operand(state, parent_expr, cmt_tbl, arena);
    Doc::group(Doc::concat(vec![
        print_attributes(state, &expr.pexp_attributes, cmt_tbl, arena),
        parent_doc,
        Doc::lbracket(),
        member,
        Doc::rbracket(),
        Doc::text(" ="),
        if should_indent_target_expr {
            Doc::indent(Doc::concat(vec![Doc::line(), target_doc]))
        } else {
            Doc::concat(vec![Doc::space(), target_doc])
        },
    ]))
}

/// `##(parent, member)` printed as `parent["member"]` (res_printer.ml:4551-4582).
fn print_send_apply(
    state: &PrinterState,
    expr: &Expression,
    parent_expr: &Expression,
    member_expr: &Expression,
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    let parent_doc = print_unary_expr_operand(state, parent_expr, cmt_tbl, arena);
    let member_doc = match &*member_expr.pexp_desc {
        ExpressionDesc::Pexp_ident(lident) => print_comments(
            print_longident(arena, arena.get_longident(lident.txt)),
            cmt_tbl,
            member_expr.pexp_loc,
            arena,
        ),
        _ => print_expression_with_comments(state, member_expr, cmt_tbl, arena),
    };
    let member = Doc::concat(vec![Doc::text("\""), member_doc, Doc::text("\"")]);
    Doc::group(Doc::concat(vec![
        print_attributes(state, &expr.pexp_attributes, cmt_tbl, arena),
        parent_doc,
        Doc::lbracket(),
        member,
        Doc::rbracket(),
    ]))
}

/// `#=(lhs, rhs)` printed as `lhs = rhs` (res_printer.ml:4583-4614).
/// res_printer.ml `print_object_set_expr`: `obj["member"] = rhs`.
fn print_object_set_expr(
    state: &PrinterState,
    obj: &Expression,
    member: &Loc<Label>,
    rhs: &Expression,
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    let rhs_doc = print_expr_with_parens(state, rhs, cmt_tbl, arena);
    Doc::group(Doc::concat(vec![
        print_object_get_doc(state, obj, member, cmt_tbl, arena),
        print_assignment_rhs(arena, " =", rhs, rhs_doc),
    ]))
}

/// OCaml `print_assignment_rhs`: delimited expressions handle their own
/// indentation; binary expressions and switches can break after the
/// assignment operator.
fn print_assignment_rhs(arena: &ParseArena, operator: &str, rhs: &Expression, rhs_doc: Doc) -> Doc {
    let should_indent = !parsetree_viewer::is_braced_expr(rhs)
        && (parsetree_viewer::is_binary_expression(arena, rhs)
            || match &*rhs.pexp_desc {
                ExpressionDesc::Pexp_match(_) => !parsetree_viewer::is_if_let_expr(arena, rhs),
                _ => false,
            });
    Doc::concat(vec![
        Doc::text(operator),
        if should_indent {
            Doc::group(Doc::indent(Doc::concat(vec![Doc::line(), rhs_doc])))
        } else {
            Doc::concat(vec![Doc::space(), rhs_doc])
        },
    ])
}

/// res_printer.ml `print_object_get_doc`: `parent["member"]`.
fn print_object_get_doc(
    state: &PrinterState,
    parent_expr: &Expression,
    label: &Loc<Label>,
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    let parent_doc = print_expression_with_comments(state, parent_expr, cmt_tbl, arena);
    let parent_doc = match parens::unary_expr_operand(arena, parent_expr) {
        ParenKind::Parenthesized => add_parens(parent_doc),
        ParenKind::Braced(braces) => print_braces(parent_doc, parent_expr, braces, arena),
        ParenKind::Nothing => parent_doc,
    };
    let member_doc = print_comments(Doc::text(&*label.txt), cmt_tbl, label.loc, arena);
    let member = Doc::concat(vec![Doc::text("\""), member_doc, Doc::text("\"")]);
    Doc::group(Doc::concat(vec![
        parent_doc,
        Doc::lbracket(),
        member,
        Doc::rbracket(),
    ]))
}

fn print_pexp_apply(
    state: &PrinterState,
    expr: &Expression,
    funct: &Expression,
    args: &[(ArgLabel, ExprIdx)],
    partial: bool,
    force_pipe_breaks: bool,
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    // res_printer.ml:3632-3641 (print_expression's Pexp_apply dispatch).
    if parsetree_viewer::is_unary_expression(arena, expr) {
        let ExpressionDesc::Pexp_ident(ident) = &*funct.pexp_desc else {
            unreachable!()
        };
        let Longident::Lident(op) = arena.get_longident(ident.txt) else {
            unreachable!()
        };
        return print_unary_expression(state, arena.get_string(*op), args, cmt_tbl, arena);
    }
    if parsetree_viewer::is_binary_expression(arena, expr) {
        return print_binary_expression(state, force_pipe_breaks, expr, cmt_tbl, arena);
    }

    // res_printer.ml:4549-4757 print_pexp_apply special forms.
    if let (ExpressionDesc::Pexp_ident(ident), [(ArgLabel::Nolabel, a0), (ArgLabel::Nolabel, a1)]) =
        (&*funct.pexp_desc, args)
    {
        let (a0, a1) = (arena.get_expr(*a0), arena.get_expr(*a1));
        if arena.is_lident(ident.txt, "##") {
            return print_send_apply(state, expr, a0, a1, cmt_tbl, arena);
        }
    }
    if let Some(parts) = parsetree_viewer::collect_spread_dict_expr_parts(arena, expr) {
        return print_spread_dict_expr(state, &parts, expr, cmt_tbl, arena);
    }
    if let Some(doc) = try_print_dict_expr(state, expr, funct, args, cmt_tbl, arena) {
        return doc;
    }
    if parsetree_viewer::is_array_access(arena, expr) {
        let parent_expr = arena.get_expr(args[0].1);
        if !parsetree_viewer::is_rewritten_underscore_apply_sugar(arena, parent_expr) {
            let member_expr = arena.get_expr(args[1].1);
            return print_array_get_apply(state, expr, parent_expr, member_expr, cmt_tbl, arena);
        }
    }
    if parsetree_viewer::is_array_set(arena, expr) {
        let parent_expr = arena.get_expr(args[0].1);
        let member_expr = arena.get_expr(args[1].1);
        let target_expr = arena.get_expr(args[2].1);
        return print_array_set_apply(
            state,
            expr,
            parent_expr,
            member_expr,
            target_expr,
            cmt_tbl,
            arena,
        );
    }

    // Regular function application
    let funct_doc = print_expression_with_comments(state, funct, cmt_tbl, arena);
    let funct_doc = match parens::call_expr(arena, funct) {
        ParenKind::Parenthesized => add_parens(funct_doc),
        ParenKind::Braced(loc) => print_braces(funct_doc, funct, loc, arena),
        ParenKind::Nothing => funct_doc,
    };

    // res_printer.ml:4778-4817: the attributes are printed after the
    // arguments, and the plain call is not grouped on its own.
    let requires_regular_layout = arguments_require_regular_layout(cmt_tbl, args, arena);
    if !requires_regular_layout
        && parsetree_viewer::requires_special_callback_printing_first_arg(arena, args, partial)
    {
        let args_doc =
            print_arguments_with_callback_in_first_position(state, args, partial, cmt_tbl, arena);
        let attrs_doc = print_attributes(state, &expr.pexp_attributes, cmt_tbl, arena);
        Doc::concat(vec![attrs_doc, funct_doc, args_doc])
    } else if !requires_regular_layout
        && parsetree_viewer::requires_special_callback_printing_last_arg(arena, args, partial)
    {
        let args_doc =
            print_arguments_with_callback_in_last_position(state, args, partial, cmt_tbl, arena);
        // Check if args doc will break - if so, add break_parent
        // Fixes layout issues with nested callbacks
        let maybe_break_parent = if args_doc.will_break() {
            Doc::break_parent()
        } else {
            Doc::nil()
        };
        let attrs_doc = print_attributes(state, &expr.pexp_attributes, cmt_tbl, arena);
        Doc::concat(vec![maybe_break_parent, attrs_doc, funct_doc, args_doc])
    } else {
        let args_doc = print_arguments(state, args, partial, cmt_tbl, arena);
        let attrs_doc = print_attributes(state, &expr.pexp_attributes, cmt_tbl, arena);
        Doc::concat(vec![attrs_doc, funct_doc, args_doc])
    }
}

/// Print binary operator with appropriate spacing.
/// Matches OCaml's print_binary_operator.
fn print_binary_operator_with_spacing(operator: &str, inline_rhs: bool) -> Doc {
    let spacing_before = if operator == "->" {
        Doc::soft_line()
    } else {
        Doc::space()
    };
    let spacing_after = if operator == "->" {
        Doc::nil()
    } else if inline_rhs {
        Doc::space()
    } else {
        Doc::line()
    };
    Doc::concat(vec![spacing_before, Doc::text(operator), spacing_after])
}

/// Print a binary operand with flattening logic for same-precedence operators.
/// This matches OCaml's print_operand with its nested flatten function.
/// Attributes of `expr` split as res_parsetree_viewer.ml:578-579
/// `partition_printable_attributes`, as an expression copy that keeps only the
/// internal ones (`{expr with pexp_attributes = internal_attrs}`).
fn with_internal_attributes(arena: &ParseArena, expr: &Expression) -> (Attributes, Expression) {
    let (printable, internal): (Vec<Attribute>, Vec<Attribute>) = expr
        .pexp_attributes
        .iter()
        .cloned()
        .partition(|attr| parsetree_viewer::is_printable_attribute(arena, attr));
    let mut internal_expr = expr.clone();
    internal_expr.pexp_attributes = Attributes::from(internal);
    (Attributes::from(printable), internal_expr)
}

/// The `Pexp_apply {funct = Lident operator; args = [(_, l); (_, r)]}` parts
/// of a binary expression.
fn binary_expression_parts<'a>(
    arena: &'a ParseArena,
    expr: &Expression,
) -> Option<(&'a str, LocIdx, &'a Expression, &'a Expression)> {
    let ExpressionDesc::Pexp_apply(apply) = &*expr.pexp_desc else {
        return None;
    };
    let [(_, left), (_, right)] = apply.args.as_slice() else {
        return None;
    };
    let ExpressionDesc::Pexp_ident(ident) = &*arena.get_expr(apply.funct).pexp_desc else {
        return None;
    };
    let Longident::Lident(op) = arena.get_longident(ident.txt) else {
        return None;
    };
    Some((
        arena.get_string(*op),
        ident.loc,
        arena.get_expr(*left),
        arena.get_expr(*right),
    ))
}

/// `print_operand` / `flatten` of res_printer.ml:4174-4334.
/// OCaml `print_operand` in `print_binary_expression`: a braced right-hand
/// side of `:=` keeps its braces; everything else goes through `flatten`.
fn print_binary_operand(
    state: &PrinterState,
    force_pipe_breaks: bool,
    is_lhs: bool,
    is_multiline: bool,
    expr: &Expression,
    parent_operator: &str,
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    if parent_operator == ":=" && !is_lhs && parsetree_viewer::is_braced_expr(expr) {
        let doc = print_expression_with_comments(state, expr, cmt_tbl, arena);
        match parens::expr(arena, expr) {
            ParenKind::Braced(braces) => print_braces(doc, expr, braces, arena),
            ParenKind::Parenthesized => add_parens(doc),
            ParenKind::Nothing => doc,
        }
    } else {
        print_binary_operand_flatten(
            state,
            force_pipe_breaks,
            is_lhs,
            is_multiline,
            expr,
            parent_operator,
            cmt_tbl,
            arena,
        )
    }
}

fn print_binary_operand_flatten(
    state: &PrinterState,
    force_pipe_breaks: bool,
    is_lhs: bool,
    is_multiline: bool,
    expr: &Expression,
    parent_operator: &str,
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    if parsetree_viewer::is_binary_expression(arena, expr) {
        let (operator, _, left, right) =
            binary_expression_parts(arena, expr).expect("binary expression");
        if parsetree_viewer::flattenable_operators(parent_operator, operator)
            && !parsetree_viewer::has_attributes(arena, &expr.pexp_attributes)
        {
            let left_printed = print_binary_operand_flatten(
                state,
                force_pipe_breaks,
                true,
                is_multiline,
                left,
                operator,
                cmt_tbl,
                arena,
            );
            let right_printed = {
                let (right_printeable_attrs, right_internal) =
                    with_internal_attributes(arena, right);
                let doc = print_expression_with_comments(state, &right_internal, cmt_tbl, arena);
                let doc = if parens::flatten_operand_rhs(arena, parent_operator, right) {
                    Doc::concat(vec![Doc::lparen(), doc, Doc::rparen()])
                } else {
                    doc
                };
                let doc = Doc::concat(vec![
                    print_attributes(state, &right_printeable_attrs, cmt_tbl, arena),
                    doc,
                ]);
                if right_printeable_attrs.is_empty() {
                    doc
                } else {
                    add_parens(doc)
                }
            };
            let doc = if parsetree_viewer::expr_is_await(expr) {
                let parens = parens::binary_operator_inside_await_needs_parens(operator);
                Doc::concat(vec![
                    Doc::lparen(),
                    Doc::text("await "),
                    if parens { Doc::lparen() } else { Doc::nil() },
                    left_printed,
                    print_binary_operator_with_spacing(operator, false),
                    right_printed,
                    if parens { Doc::rparen() } else { Doc::nil() },
                    Doc::rparen(),
                ])
            } else if operator == "->" && (is_multiline || force_pipe_breaks) {
                Doc::breakable_group(
                    Doc::concat(vec![
                        left_printed,
                        print_binary_operator_with_spacing(operator, false),
                        right_printed,
                    ]),
                    true,
                )
            } else {
                Doc::concat(vec![
                    left_printed,
                    print_binary_operator_with_spacing(operator, false),
                    right_printed,
                ])
            };
            let doc = if !is_lhs && parens::rhs_binary_expr_operand(arena, operator, expr) {
                Doc::concat(vec![Doc::lparen(), doc, Doc::rparen()])
            } else {
                doc
            };
            print_comments(doc, cmt_tbl, expr.pexp_loc, arena)
        } else {
            let (printeable_attrs, internal_expr) = with_internal_attributes(arena, expr);
            let doc = print_expression_with_comments(state, &internal_expr, cmt_tbl, arena);
            let doc = if parens::sub_binary_expr_operand(parent_operator, operator)
                || (!printeable_attrs.is_empty()
                    && (parsetree_viewer::is_binary_expression(arena, expr)
                        || parsetree_viewer::is_ternary_expr(expr)))
            {
                Doc::concat(vec![Doc::lparen(), doc, Doc::rparen()])
            } else {
                doc
            };
            Doc::concat(vec![
                print_attributes(state, &printeable_attrs, cmt_tbl, arena),
                doc,
            ])
        }
    } else {
        match &*expr.pexp_desc {
            ExpressionDesc::Pexp_setfield(inner) => {
                let (lhs, ref field, rhs) = **inner;
                let doc = print_set_field_expr(
                    state,
                    &expr.pexp_attributes,
                    arena.get_expr(lhs),
                    field,
                    arena.get_expr(rhs),
                    expr.pexp_loc,
                    cmt_tbl,
                    arena,
                );
                if is_lhs { add_parens(doc) } else { doc }
            }
            ExpressionDesc::Pexp_object_set(inner) => {
                let (ref obj, ref member, ref rhs) = **inner;
                let doc = print_object_set_expr(
                    state,
                    arena.get_expr(*obj),
                    member,
                    arena.get_expr(*rhs),
                    cmt_tbl,
                    arena,
                );
                let doc = if expr.pexp_attributes.is_empty() {
                    doc
                } else {
                    Doc::group(Doc::concat(vec![
                        print_attributes(state, &expr.pexp_attributes, cmt_tbl, arena),
                        doc,
                    ]))
                };
                if is_lhs { add_parens(doc) } else { doc }
            }
            _ => {
                let doc = print_expression_with_comments(state, expr, cmt_tbl, arena);
                let parens = match &*expr.pexp_desc {
                    ExpressionDesc::Pexp_fun(_) if parent_operator == ":=" && !is_lhs => {
                        parens::expr(arena, expr)
                    }
                    _ => parens::binary_expr_operand(arena, is_lhs, expr),
                };
                match parens {
                    ParenKind::Parenthesized => add_parens(doc),
                    ParenKind::Braced(loc) => print_braces(doc, expr, loc, arena),
                    ParenKind::Nothing => doc,
                }
            }
        }
    }
}

fn is_nolabel_pair_apply(expr: &Expression) -> bool {
    matches!(
        &*expr.pexp_desc,
        ExpressionDesc::Pexp_apply(apply)
            if matches!(apply.args.as_slice(), [(ArgLabel::Nolabel, _), (ArgLabel::Nolabel, _)])
    )
}

/// res_printer.ml:4013-4048
#[allow(clippy::too_many_arguments)]
fn print_set_field_expr(
    state: &PrinterState,
    attrs: &Attributes,
    lhs: &Expression,
    longident_loc: &crate::parse_arena::Located<crate::parse_arena::LidentIdx>,
    rhs: &Expression,
    loc: LocIdx,
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    let rhs_doc = {
        let doc = print_expression_with_comments(state, rhs, cmt_tbl, arena);
        match parens::expr(arena, rhs) {
            ParenKind::Parenthesized => add_parens(doc),
            ParenKind::Braced(braces) => print_braces(doc, rhs, braces, arena),
            ParenKind::Nothing => doc,
        }
    };
    let lhs_doc = {
        let doc = print_expression_with_comments(state, lhs, cmt_tbl, arena);
        match parens::field_expr(arena, lhs) {
            ParenKind::Parenthesized => add_parens(doc),
            ParenKind::Braced(braces) => print_braces(doc, lhs, braces, arena),
            ParenKind::Nothing => doc,
        }
    };
    let doc = Doc::group(Doc::concat(vec![
        lhs_doc,
        Doc::dot(),
        print_lident_path(longident_loc, cmt_tbl, arena),
        print_assignment_rhs(arena, " =", rhs, rhs_doc),
    ]));
    let doc = if attrs.is_empty() {
        doc
    } else {
        Doc::group(Doc::concat(vec![
            print_attributes(state, attrs, cmt_tbl, arena),
            doc,
        ]))
    };
    print_comments(doc, cmt_tbl, loc, arena)
}

/// res_printer.ml:4161-4420 print_binary_expression.
fn print_binary_expression(
    state: &PrinterState,
    force_pipe_breaks: bool,
    expr: &Expression,
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    if !is_nolabel_pair_apply(expr) {
        return Doc::nil();
    }
    let Some((operator, _, lhs, rhs)) = binary_expression_parts(arena, expr) else {
        return Doc::nil();
    };
    if operator == "->"
        && !(parsetree_viewer::is_binary_expression(arena, lhs)
            || parsetree_viewer::is_binary_expression(arena, rhs)
            || !parsetree_viewer::filter_parsing_attrs(arena, &expr.pexp_attributes).is_empty())
    {
        let lhs_has_comment_below = has_comment_below(cmt_tbl, lhs.pexp_loc, arena);
        let lhs_doc = print_binary_operand(
            state,
            force_pipe_breaks,
            true,
            false,
            lhs,
            operator,
            cmt_tbl,
            arena,
        );
        // For pipe RHS, use the pipe-specific rewrite that omits a redundant
        // first underscore.
        let rhs_doc = if parsetree_viewer::is_underscore_apply_sugar(arena, rhs) {
            print_underscore_apply_in_pipe(state, rhs, cmt_tbl, arena)
        } else {
            print_binary_operand(
                state,
                force_pipe_breaks,
                false,
                false,
                rhs,
                operator,
                cmt_tbl,
                arena,
            )
        };
        return Doc::group(Doc::concat(vec![
            print_attributes(state, &expr.pexp_attributes, cmt_tbl, arena),
            lhs_doc,
            if lhs_has_comment_below {
                Doc::concat(vec![Doc::soft_line(), Doc::text("->")])
            } else {
                Doc::text("->")
            },
            rhs_doc,
        ]));
    }
    let is_multiline = arena.loc_start(lhs.pexp_loc).line < arena.loc_start(rhs.pexp_loc).line;
    let is_rhs_op = parsetree_viewer::is_rhs_binary_operator(operator);
    let right = {
        let rhs_doc = print_binary_operand(
            state,
            force_pipe_breaks,
            is_rhs_op,
            is_multiline,
            rhs,
            operator,
            cmt_tbl,
            arena,
        );
        if operator == ":=" {
            print_assignment_rhs(arena, " :=", rhs, rhs_doc)
        } else {
            let operator_with_rhs = Doc::concat(vec![
                print_binary_operator_with_spacing(
                    operator,
                    parsetree_viewer::should_inline_rhs_binary_expr(arena, rhs),
                ),
                rhs_doc,
            ]);
            if parsetree_viewer::should_indent_binary_expr(arena, expr) {
                Doc::group(Doc::indent(operator_with_rhs))
            } else {
                operator_with_rhs
            }
        }
    };
    let doc = Doc::breakable_group(
        Doc::concat(vec![
            print_binary_operand(
                state,
                force_pipe_breaks,
                !is_rhs_op,
                is_multiline,
                lhs,
                operator,
                cmt_tbl,
                arena,
            ),
            right,
        ]),
        force_pipe_breaks && operator == "->",
    );
    let printable = parsetree_viewer::filter_printable_attributes(arena, &expr.pexp_attributes);
    let mut printable_expr = expr.clone();
    printable_expr.pexp_attributes = printable.into_iter().cloned().collect();
    Doc::group(Doc::concat(vec![
        print_attributes(state, &expr.pexp_attributes, cmt_tbl, arena),
        match parens::binary_expr(arena, &printable_expr) {
            ParenKind::Braced(braces) => print_braces(doc, expr, braces, arena),
            ParenKind::Parenthesized => add_parens(doc),
            ParenKind::Nothing => doc,
        },
    ]))
}

/// Print unary expression.
fn print_unary_expression(
    state: &PrinterState,
    op: &str,
    args: &[(ArgLabel, ExprIdx)],
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    if args.is_empty() {
        return Doc::nil();
    }
    let (_, operand_idx) = &args[0];
    let operand = arena.get_expr(*operand_idx);
    let operand_doc = print_expression_with_comments(state, operand, cmt_tbl, arena);
    let operand_doc = match parens::unary_expr_operand(arena, operand) {
        ParenKind::Parenthesized => add_parens(operand_doc),
        ParenKind::Braced(loc) => print_braces(operand_doc, operand, loc, arena),
        ParenKind::Nothing => operand_doc,
    };

    // Convert internal operator names
    let printed_op = match op {
        "~-" => "-",
        "~-." => "-.",
        "~+" => "+",
        "~+." => "+.",
        "~~~" => "~~~",
        "not" => "!",
        _ => op,
    };

    Doc::concat(vec![Doc::text(printed_op), operand_doc])
}

/// Print label prefix for argument (used in callback printing).
fn print_arg_label_prefix(label: &ArgLabel, arena: &ParseArena) -> Doc {
    match label {
        ArgLabel::Nolabel => Doc::nil(),
        ArgLabel::Labelled(name) => {
            let name_str = arena.get_string(name.txt);
            Doc::concat(vec![
                Doc::text("~"),
                print_ident_like(name_str, false, false),
                Doc::text("="),
            ])
        }
        ArgLabel::Optional(name) => {
            let name_str = arena.get_string(name.txt);
            Doc::concat(vec![
                Doc::text("~"),
                print_ident_like(name_str, false, false),
                Doc::text("=?"),
            ])
        }
    }
}

/// Print arguments with callback in last position.
/// Uses custom_layout to try different layouts for callback formatting.
fn print_arguments_with_callback_in_last_position(
    state: &PrinterState,
    args: &[(ArgLabel, ExprIdx)],
    partial: bool,
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    // Because the same subtree gets printed twice, we need to copy the cmt_tbl.
    // Consumed comments need to be marked not-consumed and reprinted.
    let state = state.next_custom_layout();

    // If we should break callback due to nesting depth, just break all args
    // IMPORTANT: Check this BEFORE computing anything to avoid infinite recursion
    if state.should_break_callback() {
        return print_arguments(&state, args, partial, cmt_tbl, arena);
    }

    let cmt_tbl_copy = cmt_tbl.copy();
    let cmt_tbl_copy2 = cmt_tbl.copy();

    // Split args into non-callback args and the callback
    let (non_callback_args, callback) = if let Some(((label, expr), rest)) = args.split_last() {
        // Print label prefix for the callback
        let lbl_doc = print_arg_label_prefix(label, arena);

        // Print non-callback args
        let mut printed_args = Vec::new();
        for (lbl, arg) in rest {
            printed_args.push(print_argument(
                &state,
                lbl,
                arena.get_expr(*arg),
                cmt_tbl,
                arena,
            ));
        }
        let printed_args_doc = if printed_args.is_empty() {
            Doc::nil()
        } else {
            Doc::concat(vec![
                Doc::join(Doc::concat(vec![Doc::comma(), Doc::line()]), printed_args),
                Doc::comma(),
                Doc::line(),
            ])
        };

        // Callback that fits on one line
        let callback_fits_on_one_line = {
            let expr = arena.get_expr(*expr);
            let mut cmt_tbl_for_callback = cmt_tbl.copy();
            let pexp_fun_doc = print_pexp_fun(
                &state,
                InCallback::FitsOnOneLine,
                expr,
                &mut cmt_tbl_for_callback,
                arena,
            );
            let doc = Doc::concat(vec![lbl_doc.clone(), pexp_fun_doc]);
            print_comments(doc, &mut cmt_tbl_for_callback, expr.pexp_loc, arena)
        };

        // Callback with arguments fitting on one line (body may break)
        let callback_args_fit_on_one_line = {
            let expr = arena.get_expr(*expr);
            let mut cmt_tbl_for_callback = cmt_tbl_copy.clone();
            let pexp_fun_doc = print_pexp_fun(
                &state,
                InCallback::ArgumentsFitOnOneLine,
                expr,
                &mut cmt_tbl_for_callback,
                arena,
            );
            let doc = Doc::concat(vec![lbl_doc, pexp_fun_doc]);
            print_comments(doc, &mut cmt_tbl_for_callback, expr.pexp_loc, arena)
        };

        (
            printed_args_doc,
            (callback_fits_on_one_line, callback_args_fit_on_one_line),
        )
    } else {
        return Doc::text("()");
    };

    let (callback_fits_on_one_line, callback_args_fit_on_one_line) = callback;

    // If we should break callback due to nesting depth, just break all args
    // IMPORTANT: Check this BEFORE computing break_all_args to avoid infinite recursion
    if state.should_break_callback() {
        let mut cmt_tbl_for_break = cmt_tbl_copy2;
        return print_arguments(&state, args, partial, &mut cmt_tbl_for_break, arena);
    }

    // Thing.map(
    //   arg1,
    //   arg2,
    //   arg3,
    //   (param1, parm2) => doStuff(param1, parm2)
    // )
    let break_all_args = {
        let mut cmt_tbl_for_break = cmt_tbl_copy2;
        print_arguments(&state, args, partial, &mut cmt_tbl_for_break, arena)
    };

    // Check if any non-callback args will break - check before consuming non_callback_args
    if non_callback_args.will_break() {
        return break_all_args;
    }

    // Thing.map(foo, (arg1, arg2) => MyModuleBlah.toList(argument))
    let fits_on_one_line = Doc::concat(vec![
        Doc::lparen(),
        non_callback_args.clone(),
        callback_fits_on_one_line,
        Doc::rparen(),
    ]);

    // Thing.map(longArgument, veryLooooongArgument, (arg1, arg2) =>
    //   MyModuleBlah.toList(argument)
    // )
    let arguments_fit_on_one_line = Doc::concat(vec![
        Doc::lparen(),
        non_callback_args,
        Doc::breakable_group(callback_args_fit_on_one_line, true),
        Doc::rparen(),
    ]);

    Doc::custom_layout(vec![
        fits_on_one_line,
        arguments_fit_on_one_line,
        break_all_args,
    ])
}

/// Print arguments with callback in first position.
/// Uses custom_layout to try different layouts for callback formatting.
fn print_arguments_with_callback_in_first_position(
    state: &PrinterState,
    args: &[(ArgLabel, ExprIdx)],
    partial: bool,
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    // Because the same subtree gets printed twice, we need to copy the cmt_tbl.
    let state = state.next_custom_layout();

    // If we should break callback due to nesting depth, just break all args
    // IMPORTANT: Check this BEFORE computing anything to avoid infinite recursion
    if state.should_break_callback() {
        return print_arguments(&state, args, partial, cmt_tbl, arena);
    }

    let cmt_tbl_copy = cmt_tbl.copy();

    // Split args into callback and non-callback args
    let (callback_doc, printed_args_doc) = if let Some(((label, expr), rest)) = args.split_first() {
        // Print label prefix for the callback
        let lbl_doc = print_arg_label_prefix(label, arena);

        // Print callback
        let callback = {
            let expr = arena.get_expr(*expr);
            let pexp_fun_doc =
                print_pexp_fun(&state, InCallback::FitsOnOneLine, expr, cmt_tbl, arena);
            let doc = Doc::concat(vec![lbl_doc, pexp_fun_doc]);
            print_comments(doc, cmt_tbl, expr.pexp_loc, arena)
        };

        // Print non-callback args
        let mut printed_args = Vec::new();
        for (lbl, arg) in rest {
            printed_args.push(print_argument(
                &state,
                lbl,
                arena.get_expr(*arg),
                cmt_tbl,
                arena,
            ));
        }
        if partial {
            printed_args.push(Doc::text("..."));
        }
        let printed_args_doc =
            Doc::join(Doc::concat(vec![Doc::comma(), Doc::line()]), printed_args);

        (callback, printed_args_doc)
    } else {
        return Doc::text("()");
    };

    // Thing.map((arg1, arg2) => MyModuleBlah.toList(argument), foo)
    // Thing.map((arg1, arg2) => {
    //   MyModuleBlah.toList(argument)
    // }, longArgument, veryLooooongArgument)
    let fits_on_one_line = Doc::concat(vec![
        Doc::lparen(),
        callback_doc,
        Doc::comma(),
        Doc::line(),
        printed_args_doc.clone(),
        Doc::rparen(),
    ]);

    // Thing.map(
    //   (param1, parm2) => doStuff(param1, parm2),
    //   arg1,
    //   arg2,
    //   arg3,
    // )
    let break_all_args = {
        let mut cmt_tbl_for_break = cmt_tbl_copy;
        print_arguments(&state, args, partial, &mut cmt_tbl_for_break, arena)
    };

    // Check if any non-callback args will break
    if printed_args_doc.will_break() {
        return break_all_args;
    }

    Doc::custom_layout(vec![fits_on_one_line, break_all_args])
}

/// Print function arguments.
fn print_arguments(
    state: &PrinterState,
    args: &[(ArgLabel, ExprIdx)],
    partial: bool,
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    // res_printer.ml:4764-4769 appends a dummy `~...` argument to a partial
    // application, so the one-argument special cases below never apply.
    if args.is_empty() && !partial {
        return Doc::text("()");
    }

    // Special case: single unit argument () -> just print ()
    if let (false, [(ArgLabel::Nolabel, expr)]) = (partial, args) {
        let expr = arena.get_expr(*expr);
        if is_unit_expr(arena, expr) {
            // Check for leading comments
            if has_leading_line_comment(cmt_tbl, expr.pexp_loc, arena) {
                let cmt = print_comments(Doc::nil(), cmt_tbl, expr.pexp_loc, arena);
                return Doc::concat(vec![
                    Doc::lparen(),
                    Doc::indent(Doc::group(Doc::concat(vec![Doc::soft_line(), cmt]))),
                    Doc::rparen(),
                ]);
            }
            return Doc::text("()");
        }
    }

    // Special case: single huggable argument (array, tuple, record, etc.)
    if let (false, [(ArgLabel::Nolabel, arg)]) = (partial, args) {
        let arg = arena.get_expr(*arg);
        if parsetree_viewer::is_huggable_expression(arena, arg) {
            let arg_doc = {
                let doc = print_expression_with_comments(state, arg, cmt_tbl, arena);
                match parens::expr_allowing_coercion(arena, arg) {
                    ParenKind::Parenthesized => add_parens(doc),
                    ParenKind::Braced(loc) => print_braces(doc, arg, loc, arena),
                    ParenKind::Nothing => doc,
                }
            };
            return Doc::concat(vec![Doc::lparen(), arg_doc, Doc::rparen()]);
        }
    }

    // res_printer.ml print_arguments: flush a callback's line comment before
    // closing the argument list, so reparsing cannot attach it to an
    // enclosing call instead.
    let force_break = args.iter().any(|(label, arg)| {
        let arg = arena.get_expr(*arg);
        matches!(&*arg.pexp_desc, ExpressionDesc::Pexp_fun(_))
            && (cmt_tbl.has_any_trailing_line_comment_at(PosRange::argument(arena, label, arg))
                || cmt_tbl
                    .has_any_trailing_line_comment_at(PosRange::from_loc(arg.pexp_loc, arena)))
    });
    let args_doc: Vec<Doc> = args
        .iter()
        .map(|(label, expr)| print_argument(state, label, arena.get_expr(*expr), cmt_tbl, arena))
        .collect();

    // If partial, add ... at the end
    let mut all_docs = args_doc;
    if partial {
        all_docs.push(Doc::text("..."));
    }

    Doc::breakable_group(
        Doc::concat(vec![
            Doc::lparen(),
            Doc::indent(Doc::concat(vec![
                Doc::soft_line(),
                Doc::join(Doc::concat(vec![Doc::text(","), Doc::line()]), all_docs),
            ])),
            // Don't add trailing comma for partial application
            if partial {
                Doc::nil()
            } else {
                Doc::trailing_comma()
            },
            Doc::soft_line(),
            Doc::rparen(),
        ]),
        force_break,
    )
}

/// Print a single function argument (like OCaml's print_argument).
/// Properly handles comments attached to the combined label+expression location.
/// OCaml: each argument is rewritten with rewrite_underscore_apply before printing.
fn print_argument(
    state: &PrinterState,
    label: &ArgLabel,
    expr: &Expression,
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    // Check if the argument is underscore apply sugar: (__x) => f(a, __x, c) -> f(a, _, c)
    if parsetree_viewer::is_underscore_apply_sugar(arena, expr) {
        // Rewrite at print time: extract the inner apply and print with _ substitution
        let doc = print_underscore_apply(
            state,
            get_underscore_apply_body(expr, arena),
            cmt_tbl,
            arena,
        );
        // Handle labelled arguments
        return match label {
            ArgLabel::Nolabel => doc,
            ArgLabel::Labelled(name) => {
                let name_str = arena.get_string(name.txt);
                Doc::concat(vec![
                    Doc::text("~"),
                    print_ident_like(name_str, false, false),
                    Doc::text("="),
                    doc,
                ])
            }
            ArgLabel::Optional(name) => {
                let name_str = arena.get_string(name.txt);
                Doc::concat(vec![
                    Doc::text("~"),
                    print_ident_like(name_str, false, false),
                    Doc::text("=?"),
                    doc,
                ])
            }
        };
    }

    match label {
        ArgLabel::Nolabel => {
            // Unlabelled argument - just print the expression with its comments
            let doc = print_expression_with_comments(state, expr, cmt_tbl, arena);
            match parens::expr_allowing_coercion(arena, expr) {
                ParenKind::Parenthesized => add_parens(doc),
                ParenKind::Braced(loc) => print_braces(doc, expr, loc, arena),
                ParenKind::Nothing => doc,
            }
        }
        ArgLabel::Labelled(name) => {
            let name_str = arena.get_string(name.txt);
            // Check for punning: ~name where expr is Pexp_ident(Lident(name))
            if let ExpressionDesc::Pexp_ident(lid) = &*expr.pexp_desc {
                if let Longident::Lident(ident_idx) = arena.get_longident(lid.txt) {
                    let ident_str = arena.get_string(*ident_idx);
                    if ident_str == name_str && expr.pexp_attributes.is_empty() {
                        // Punned: ~name - create combined location from label to expression end
                        let (pos_range, full_loc) =
                            make_combined_pos_range(name.loc, expr.pexp_loc, arena);
                        let doc = Doc::concat(vec![
                            Doc::text("~"),
                            print_ident_like(name_str, false, false),
                        ]);
                        return print_comments_by_pos(doc, cmt_tbl, pos_range, &full_loc);
                    }
                }
            }
            // Check for punned with type constraint: ~name: type where expr is Pexp_constraint
            if let ExpressionDesc::Pexp_constraint(inner) = &*expr.pexp_desc {
                let (ref inner_expr_idx, ref typ) = **inner;
                let inner_expr = arena.get_expr(*inner_expr_idx);
                if expr.pexp_attributes.is_empty() {
                    if let ExpressionDesc::Pexp_ident(lid) = &*inner_expr.pexp_desc {
                        if let Longident::Lident(ident_idx) = arena.get_longident(lid.txt) {
                            let ident_str = arena.get_string(*ident_idx);
                            if ident_str == name_str {
                                // Punned with type: ~name: type
                                let (pos_range, full_loc) =
                                    make_combined_pos_range(name.loc, expr.pexp_loc, arena);
                                let typ_doc = print_typ_expr(
                                    state,
                                    arena.get_core_type(*typ),
                                    cmt_tbl,
                                    arena,
                                );
                                let doc = Doc::concat(vec![
                                    Doc::text("~"),
                                    print_ident_like(name_str, false, false),
                                    Doc::text(": "),
                                    typ_doc,
                                ]);
                                return print_comments_by_pos(doc, cmt_tbl, pos_range, &full_loc);
                            }
                        }
                    }
                }
            }
            // Regular labelled argument: ~name=expr
            // Print the label part with comments from label location
            let lbl_doc = Doc::concat(vec![
                Doc::text("~"),
                print_ident_like(name_str, false, false),
                Doc::text("="),
            ]);
            let lbl_doc = print_comments(lbl_doc, cmt_tbl, name.loc, arena);
            // Print expression with comments
            let expr_doc = {
                let doc = print_expression_with_comments(state, expr, cmt_tbl, arena);
                match parens::expr_allowing_coercion(arena, expr) {
                    ParenKind::Parenthesized => add_parens(doc),
                    ParenKind::Braced(loc) => print_braces(doc, expr, loc, arena),
                    ParenKind::Nothing => doc,
                }
            };
            // Create combined location from label to expression end and wrap
            let (pos_range, full_loc) = make_combined_pos_range(name.loc, expr.pexp_loc, arena);
            let doc = Doc::concat(vec![lbl_doc, expr_doc]);
            print_comments_by_pos(doc, cmt_tbl, pos_range, &full_loc)
        }
        ArgLabel::Optional(name) => {
            let name_str = arena.get_string(name.txt);
            // Check for punning: ~name? where expr is Pexp_ident(Lident(name))
            if let ExpressionDesc::Pexp_ident(lid) = &*expr.pexp_desc {
                if let Longident::Lident(ident_idx) = arena.get_longident(lid.txt) {
                    let ident_str = arena.get_string(*ident_idx);
                    if ident_str == name_str && expr.pexp_attributes.is_empty() {
                        // Punned optional: ~name?
                        let doc = Doc::concat(vec![
                            Doc::text("~"),
                            print_ident_like(name_str, false, false),
                            Doc::text("?"),
                        ]);
                        return print_comments(doc, cmt_tbl, name.loc, arena);
                    }
                }
            }
            // Regular optional argument: ~name=?expr
            let lbl_doc = Doc::concat(vec![
                Doc::text("~"),
                print_ident_like(name_str, false, false),
                Doc::text("=?"),
            ]);
            let lbl_doc = print_comments(lbl_doc, cmt_tbl, name.loc, arena);
            let expr_doc = {
                let doc = print_expression_with_comments(state, expr, cmt_tbl, arena);
                match parens::expr_allowing_coercion(arena, expr) {
                    ParenKind::Parenthesized => add_parens(doc),
                    ParenKind::Braced(loc) => print_braces(doc, expr, loc, arena),
                    ParenKind::Nothing => doc,
                }
            };
            let (pos_range, full_loc) = make_combined_pos_range(name.loc, expr.pexp_loc, arena);
            let doc = Doc::concat(vec![lbl_doc, expr_doc]);
            print_comments_by_pos(doc, cmt_tbl, pos_range, &full_loc)
        }
    }
}

/// Create a combined position range and full location spanning from start loc to end of end_loc.
/// Used for argument locations that span label to expression.
fn make_combined_pos_range(
    start_loc: LocIdx,
    end_loc: LocIdx,
    arena: &ParseArena,
) -> (PosRange, FullLocation) {
    let start = arena.loc_start(start_loc);
    let end = arena.loc_end(end_loc);
    let pos_range = PosRange {
        start: start.cnum,
        end: end.cnum,
    };
    let full_loc = FullLocation::from_positions(start.clone(), end.clone());
    (pos_range, full_loc)
}

/// Check if an expression is unit: `()`
fn is_unit_expr(arena: &ParseArena, expr: &Expression) -> bool {
    match &*expr.pexp_desc {
        ExpressionDesc::Pexp_construct(lid, _) => arena.is_lident(lid.txt, "()"),
        _ => false,
    }
}

/// res_printer.ml `argument_requires_regular_layout`: compact callback
/// layouts print expression comments but not comments on the full labeled
/// argument, and trailing comments can escape them when the body breaks.
fn argument_requires_regular_layout(
    cmt_tbl: &CommentTable,
    lbl: &ArgLabel,
    arg: &Expression,
    arena: &ParseArena,
) -> bool {
    let loc = PosRange::argument(arena, lbl, arg);
    let has_leading_label_comments = match lbl {
        ArgLabel::Nolabel => false,
        ArgLabel::Labelled(_) | ArgLabel::Optional(_) => {
            cmt_tbl.has_leading_comments_at(loc)
                || cmt_tbl.has_leading_comments(arg.pexp_loc, arena)
        }
    };
    has_leading_label_comments
        || cmt_tbl.has_trailing_comments_at(loc)
        || cmt_tbl.has_trailing_comments(arg.pexp_loc, arena)
}

/// Whether any argument rules out the compact callback layouts.
fn arguments_require_regular_layout(
    cmt_tbl: &CommentTable,
    args: &[(ArgLabel, ExprIdx)],
    arena: &ParseArena,
) -> bool {
    args.iter().any(|(lbl, arg)| {
        argument_requires_regular_layout(cmt_tbl, lbl, arena.get_expr(*arg), arena)
    })
}

/// Check if there's a leading line comment at a location.
fn has_leading_line_comment(cmt_tbl: &CommentTable, loc: LocIdx, arena: &ParseArena) -> bool {
    if let Some(comments) = cmt_tbl.get_leading_comments(loc, arena) {
        comments.iter().any(|c| c.is_single_line())
    } else {
        false
    }
}

/// Check if there's a trailing comment that starts on a line BELOW the location's end line.
/// This matches OCaml's has_comment_below which returns true when:
///   comment_loc.loc_start.pos_lnum > loc.loc_end.pos_lnum
fn has_comment_below(cmt_tbl: &CommentTable, loc: LocIdx, arena: &ParseArena) -> bool {
    if let Some(comments) = cmt_tbl.get_trailing_comments(loc, arena) {
        if let Some(comment) = comments.first() {
            let comment_start_line = comment.loc.loc_start.line;
            let loc_end_line = arena.loc_end(loc).line;
            return comment_start_line > loc_end_line;
        }
    }
    false
}

// ============================================================================
// Pattern Printing
// ============================================================================

/// Print a pattern with comments.
pub fn print_pattern_with_comments(
    state: &PrinterState,
    pat: &Pattern,
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    let doc = print_pattern(state, pat, cmt_tbl, arena);
    print_comments(doc, cmt_tbl, pat.ppat_loc, arena)
}

/// Print a pattern.
pub fn print_pattern(
    state: &PrinterState,
    pat: &Pattern,
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    let pattern_without_attrs = match &*pat.ppat_desc {
        // _
        PatternDesc::Ppat_any => Doc::text("_"),
        // x
        PatternDesc::Ppat_var(var) => print_ident_like(arena.get_string(var.txt), false, false),
        // 42, "hello", 'a', etc.
        PatternDesc::Ppat_constant(c) => print_constant(c),
        // (p1, p2, ...)
        PatternDesc::Ppat_tuple(patterns) => Doc::group(Doc::concat(vec![
            Doc::lparen(),
            Doc::indent(Doc::concat(vec![
                Doc::soft_line(),
                Doc::join(
                    Doc::concat(vec![Doc::text(","), Doc::line()]),
                    patterns
                        .iter()
                        .map(|p| print_pattern(state, arena.get_pat(*p), cmt_tbl, arena))
                        .collect(),
                ),
            ])),
            Doc::trailing_comma(),
            Doc::soft_line(),
            Doc::rparen(),
        ])),
        // []
        PatternDesc::Ppat_array(patterns) if patterns.is_empty() => Doc::concat(vec![
            Doc::lbracket(),
            print_comments_inside(cmt_tbl, pat.ppat_loc, arena),
            Doc::rbracket(),
        ]),
        // [p1, p2, ...]
        PatternDesc::Ppat_array(patterns) => Doc::group(Doc::concat(vec![
            Doc::text("["),
            Doc::indent(Doc::concat(vec![
                Doc::soft_line(),
                Doc::join(
                    Doc::concat(vec![Doc::text(","), Doc::line()]),
                    patterns
                        .iter()
                        .map(|p| print_pattern(state, arena.get_pat(*p), cmt_tbl, arena))
                        .collect(),
                ),
            ])),
            Doc::trailing_comma(),
            Doc::soft_line(),
            Doc::text("]"),
        ])),
        // ()
        PatternDesc::Ppat_construct(lid, _) if arena.is_lident(lid.txt, "()") => Doc::concat(vec![
            Doc::lparen(),
            print_comments_inside(cmt_tbl, pat.ppat_loc, arena),
            Doc::rparen(),
        ]),
        // list{}
        PatternDesc::Ppat_construct(lid, _) if arena.is_lident(lid.txt, "[]") => Doc::concat(vec![
            Doc::text("list{"),
            print_comments_inside(cmt_tbl, pat.ppat_loc, arena),
            Doc::rbrace(),
        ]),
        // list{p1, p2, ...spread}
        PatternDesc::Ppat_construct(lid, _) if arena.is_lident(lid.txt, "::") => {
            print_list_pattern(state, pat, cmt_tbl, arena)
        }
        // Constructor(args)
        PatternDesc::Ppat_construct(constr_name, constructor_args) => {
            let constr = print_longident_location(constr_name, cmt_tbl, arena);
            let args_doc = print_pattern_args(state, &constructor_args.txt, cmt_tbl, arena);
            Doc::group(Doc::concat(vec![constr, args_doc]))
        }
        // #variant or #variant(args)
        PatternDesc::Ppat_variant(inner) => {
            let (ref label, ref variant_args) = **inner;
            let variant_name = Doc::concat(vec![Doc::text("#"), print_poly_var_ident(label)]);
            let args_doc = print_pattern_args(state, &variant_args.txt, cmt_tbl, arena);
            Doc::group(Doc::concat(vec![variant_name, args_doc]))
        }
        // {field1, field2: pat, ...spread} or dict{"key": pat}
        PatternDesc::Ppat_record(inner) => {
            let (ref fields, ref closed, ref record_rest) = **inner;
            // Check if this is a dict pattern (has res.dictPattern attribute)
            if parsetree_viewer::has_dict_pattern_attribute(arena, &pat.ppat_attributes) {
                print_dict_pattern(state, fields, cmt_tbl, arena)
            } else {
                print_record_pattern(state, fields, &closed, record_rest.as_ref(), cmt_tbl, arena)
            }
        }
        // p | p
        PatternDesc::Ppat_or(_, _) => {
            // Collect the entire or-chain into a flat list
            let or_chain = parsetree_viewer::collect_or_pattern_chain(arena, pat);
            let docs: Vec<Doc> = or_chain
                .iter()
                .enumerate()
                .map(|(i, p)| {
                    let pattern_doc = print_pattern(state, p, cmt_tbl, arena);
                    // Wrap nested or-patterns in parentheses
                    let pattern_doc = if matches!(&*p.ppat_desc, PatternDesc::Ppat_or(_, _)) {
                        add_parens(pattern_doc)
                    } else {
                        pattern_doc
                    };
                    if i == 0 {
                        pattern_doc
                    } else {
                        Doc::concat(vec![Doc::line(), Doc::text("| "), pattern_doc])
                    }
                })
                .collect();

            // Check if the pattern spans multiple lines in source
            let is_spread_over_multiple_lines =
                if let (Some(first), Some(last)) = (or_chain.first(), or_chain.last()) {
                    arena.loc_start(first.ppat_loc).line < arena.loc_end(last.ppat_loc).line
                } else {
                    false
                };

            Doc::breakable_group(Doc::concat(docs), is_spread_over_multiple_lines)
        }
        // module(M: S) - first-class module with package type
        PatternDesc::Ppat_constraint(ppat_c_inner)
            if matches!(
                &*arena.get_pat(ppat_c_inner.0).ppat_desc,
                PatternDesc::Ppat_unpack(_)
            ) && matches!(
                &*arena.get_core_type(ppat_c_inner.1).ptyp_desc,
                CoreTypeDesc::Ptyp_package(_)
            ) =>
        {
            let (ref inner_idx, ref typ) = **ppat_c_inner;
            let inner = arena.get_pat(*inner_idx);
            let typ = arena.get_core_type(*typ);
            if let (PatternDesc::Ppat_unpack(name), CoreTypeDesc::Ptyp_package(package_type)) =
                (&*inner.ppat_desc, &*typ.ptyp_desc)
            {
                let name_doc = Doc::text(arena.get_string(name.txt));
                let name_doc = print_comments(name_doc, cmt_tbl, name.loc, arena);
                let pkg_doc = print_package_type(state, &**package_type, false, cmt_tbl, arena);
                let pkg_doc = print_comments(pkg_doc, cmt_tbl, typ.ptyp_loc, arena);
                Doc::concat(vec![
                    Doc::text("module("),
                    name_doc,
                    Doc::text(": "),
                    pkg_doc,
                    Doc::text(")"),
                ])
            } else {
                unreachable!()
            }
        }
        // p : type
        PatternDesc::Ppat_constraint(inner) => {
            let (ref pat_idx, ref typ) = **inner;
            let pat_inner = arena.get_pat(*pat_idx);
            let typ = arena.get_core_type(*typ);
            let pat_doc = print_pattern(state, pat_inner, cmt_tbl, arena);
            let typ_doc = print_typ_expr(state, typ, cmt_tbl, arena);
            Doc::concat(vec![pat_doc, Doc::text(": "), typ_doc])
        }
        // p as x
        PatternDesc::Ppat_alias(pat_idx, alias) => {
            let pat = arena.get_pat(*pat_idx);
            let needs_parens = matches!(
                &*pat.ppat_desc,
                PatternDesc::Ppat_or(_, _) | PatternDesc::Ppat_alias(_, _)
            );
            let pat_doc = print_pattern(state, pat, cmt_tbl, arena);
            let pat_doc = if needs_parens {
                Doc::concat(vec![Doc::text("("), pat_doc, Doc::text(")")])
            } else {
                pat_doc
            };
            // Wrap alias with print_comments for its location (like OCaml reference)
            let alias_doc = print_ident_like(arena.get_string(alias.txt), false, false);
            let alias_doc = print_comments(alias_doc, cmt_tbl, alias.loc, arena);
            Doc::concat(vec![pat_doc, Doc::text(" as "), alias_doc])
        }
        // module(M)
        PatternDesc::Ppat_unpack(name) => {
            // Wrap name with print_comments for its location (like OCaml reference)
            let name_doc = Doc::text(arena.get_string(name.txt));
            let name_doc = print_comments(name_doc, cmt_tbl, name.loc, arena);
            Doc::concat(vec![Doc::text("module("), name_doc, Doc::text(")")])
        }
        // exception pat
        PatternDesc::Ppat_exception(pat_idx) => {
            let pat = arena.get_pat(*pat_idx);
            let needs_parens = matches!(
                &*pat.ppat_desc,
                PatternDesc::Ppat_or(_, _) | PatternDesc::Ppat_alias(_, _)
            );
            let pat_doc = print_pattern(state, pat, cmt_tbl, arena);
            let pat_doc = if needs_parens {
                Doc::concat(vec![Doc::text("("), pat_doc, Doc::text(")")])
            } else {
                pat_doc
            };
            Doc::group(Doc::concat(vec![
                Doc::text("exception"),
                Doc::line(),
                pat_doc,
            ]))
        }
        // %extension
        PatternDesc::Ppat_extension(ext) => print_extension(state, ext, false, cmt_tbl, arena),
        // `type identifier
        PatternDesc::Ppat_type(lid) => {
            // Use print_lident for proper escaping of exotic identifiers
            let doc = print_lident(arena, arena.get_longident(lid.txt));
            let doc = print_comments(doc, cmt_tbl, lid.loc, arena);
            // res_printer.ml:2817-2822: a variant spread prints as `...t`.
            let prefix = if pat
                .ppat_attributes
                .iter()
                .any(|attr| arena.get_string(attr.0.txt) == "res.patVariantSpread")
            {
                "..."
            } else {
                "#..."
            };
            Doc::concat(vec![Doc::text(prefix), doc])
        }
        // interval: 'a' .. 'z'
        PatternDesc::Ppat_interval(inner) => {
            let (ref c1, ref c2) = **inner;
            Doc::concat(vec![
                print_constant(c1),
                Doc::text(" .. "),
                print_constant(c2),
            ])
        }
    };

    // Handle attributes
    let doc = if pat.ppat_attributes.is_empty() {
        pattern_without_attrs
    } else {
        let attrs = print_attributes(state, &pat.ppat_attributes, cmt_tbl, arena);
        Doc::group(Doc::concat(vec![attrs, pattern_without_attrs]))
    };

    // Wrap with print_comments to attach leading/trailing comments
    print_comments(doc, cmt_tbl, pat.ppat_loc, arena)
}

/// Check if a pattern is "huggable" (can be printed without line breaks).
fn is_huggable_pattern(pat: &Pattern) -> bool {
    matches!(
        &*pat.ppat_desc,
        PatternDesc::Ppat_array(_)
            | PatternDesc::Ppat_tuple(_)
            | PatternDesc::Ppat_record(_)
            | PatternDesc::Ppat_variant(_)
            | PatternDesc::Ppat_construct(_, _)
    )
}

/// Print list pattern.
fn print_list_pattern(
    state: &PrinterState,
    pat: &Pattern,
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    // res_printer.ml:2669-2710
    let (patterns, tail) = parsetree_viewer::collect_list_patterns(arena, pat);
    let tail_is_nil = matches!(
        &*tail.ppat_desc,
        PatternDesc::Ppat_construct(lid, _) if arena.is_lident(lid.txt, "[]")
    );
    let should_hug =
        matches!(patterns.as_slice(), [single] if is_huggable_pattern(single)) && tail_is_nil;
    let mut docs: Vec<Doc> = Vec::with_capacity(patterns.len());
    for p in &patterns {
        docs.push(print_pattern(state, p, cmt_tbl, arena));
    }
    let tail_doc = if tail_is_nil {
        Doc::nil()
    } else {
        let doc = Doc::concat(vec![
            Doc::text("..."),
            print_pattern(state, tail, cmt_tbl, arena),
        ]);
        let tail_doc = print_comments(doc, cmt_tbl, tail.ppat_loc, arena);
        Doc::concat(vec![Doc::text(","), Doc::line(), tail_doc])
    };
    let children = Doc::concat(vec![
        if should_hug {
            Doc::nil()
        } else {
            Doc::soft_line()
        },
        Doc::join(Doc::concat(vec![Doc::text(","), Doc::line()]), docs),
        tail_doc,
    ]);
    Doc::group(Doc::concat(vec![
        Doc::text("list{"),
        if should_hug {
            children
        } else {
            Doc::concat(vec![
                Doc::indent(children),
                Doc::if_breaks(Doc::text(","), Doc::nil()),
                Doc::soft_line(),
            ])
        },
        Doc::rbrace(),
    ]))
}

/// Print record pattern.
fn print_record_pattern(
    state: &PrinterState,
    fields: &[PatternRecordField],
    closed: &ClosedFlag,
    record_rest: Option<&RecordPatRest>,
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    let fields_doc = Doc::join(
        Doc::concat(vec![Doc::text(","), Doc::line()]),
        fields
            .iter()
            .map(|field| {
                let field_pat = arena.get_pat(field.pat);
                let label = print_lident(arena, arena.get_longident(field.lid.txt));
                // Check for punning
                if is_punned_pattern_field(arena, field) {
                    // For punned patterns, print pattern attributes before the label
                    // OCaml (line 2732-2734): print_attributes ~state ppat_attributes cmt_tbl;
                    //                         print_lident_path longident cmt_tbl;
                    let attrs_doc = if field_pat.ppat_attributes.is_empty() {
                        Doc::nil()
                    } else {
                        print_attributes(state, &field_pat.ppat_attributes, cmt_tbl, arena)
                    };
                    let label = print_comments(label, cmt_tbl, field.lid.loc, arena);
                    if field.opt {
                        Doc::concat(vec![Doc::text("?"), attrs_doc, label])
                    } else {
                        Doc::concat(vec![attrs_doc, label])
                    }
                } else {
                    // For non-punned patterns, comments are attached to BOTH:
                    // 1. Individual component locations (label and pattern)
                    // 2. The combined row location
                    // Like OCaml: print_lident_path (with comments on label), then print_comments on row
                    // res_printer.ml:3004-3026
                    let pat_doc = print_pattern(state, field_pat, cmt_tbl, arena);
                    // Check if pattern needs parentheses in record row context
                    let pat_doc = if parens::pattern_record_row_rhs(arena, field_pat) {
                        add_parens(pat_doc)
                    } else {
                        pat_doc
                    };
                    let rhs_doc = if field.opt {
                        Doc::concat(vec![Doc::text("?"), pat_doc])
                    } else {
                        pat_doc
                    };
                    let label = print_comments(label, cmt_tbl, field.lid.loc, arena);
                    let doc = Doc::group(Doc::concat(vec![
                        label,
                        Doc::text(":"),
                        if is_huggable_pattern(field_pat) {
                            Doc::concat(vec![Doc::space(), rhs_doc])
                        } else {
                            Doc::indent(Doc::concat(vec![Doc::line(), rhs_doc]))
                        },
                    ]));
                    // Create combined location and use position-based lookup explicitly
                    // This is needed because during walking, a new LocIdx is created for the combined
                    // location that won't match any AST node's LocIdx during printing
                    let pos_range = PosRange {
                        start: arena.loc_start(field.lid.loc).cnum,
                        end: arena.loc_end(field_pat.ppat_loc).cnum,
                    };
                    // Use explicit position-based lookup (not the generic print_comments)
                    let leading = cmt_tbl.remove_leading_comments_by_pos(pos_range);
                    let trailing = cmt_tbl.remove_trailing_comments_by_pos(pos_range);
                    let full_loc = FullLocation {
                        loc_start: arena.loc_start(field.lid.loc).clone(),
                        loc_end: arena.loc_end(field_pat.ppat_loc).clone(),
                        loc_ghost: false,
                    };
                    let doc = print_leading_comments_with(doc, leading, &full_loc);
                    print_trailing_comments_with(doc, trailing, &full_loc)
                }
            })
            .collect(),
    );

    // res_printer.ml Ppat_record: a rest row replaces the `_` of an open pattern.
    let open_doc = match (record_rest, closed) {
        (Some(rest), _) => {
            let rest_doc = match rest.rest_type {
                Some(typ) => Doc::concat(vec![
                    Doc::text("..."),
                    print_typ_expr(state, arena.get_core_type(typ), cmt_tbl, arena),
                    Doc::text(" as "),
                    print_string_loc(&rest.rest_name, cmt_tbl, arena),
                ]),
                None => Doc::concat(vec![
                    Doc::text("..."),
                    print_string_loc(&rest.rest_name, cmt_tbl, arena),
                ]),
            };
            let rest_doc = print_comments(rest_doc, cmt_tbl, rest.rest_loc, arena);
            if fields.is_empty() {
                rest_doc
            } else {
                Doc::concat(vec![Doc::text(","), Doc::line(), rest_doc])
            }
        }
        (None, ClosedFlag::Closed) => Doc::nil(),
        (None, ClosedFlag::Open) => {
            if fields.is_empty() {
                Doc::text("_")
            } else {
                Doc::concat(vec![Doc::text(","), Doc::line(), Doc::text("_")])
            }
        }
    };

    Doc::group(Doc::concat(vec![
        Doc::lbrace(),
        Doc::indent(Doc::concat(vec![Doc::soft_line(), fields_doc, open_doc])),
        Doc::trailing_comma(),
        Doc::soft_line(),
        Doc::rbrace(),
    ]))
}

/// Print dict pattern: dict{"key": pattern}
/// Matches OCaml's print_pattern_dict_row
fn print_dict_pattern(
    state: &PrinterState,
    fields: &[PatternRecordField],
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    let fields_doc = Doc::join(
        Doc::concat(vec![Doc::text(","), Doc::line()]),
        fields
            .iter()
            .filter_map(|field| {
                // Skip the _ (underscore) field that's always present in Open records
                if let Longident::Lident(name_idx) = arena.get_longident(field.lid.txt) {
                    if arena.get_string(*name_idx) == "_" {
                        return None;
                    }
                }
                Some(print_dict_pattern_row(state, field, cmt_tbl, arena))
            })
            .collect(),
    );

    Doc::concat(vec![
        Doc::text("dict{"),
        Doc::indent(Doc::concat(vec![Doc::soft_line(), fields_doc])),
        Doc::if_breaks(Doc::text(","), Doc::nil()),
        Doc::soft_line(),
        Doc::rbrace(),
    ])
}

/// Print a single dict pattern row: "key": pattern or "key": ?pattern
fn print_dict_pattern_row(
    state: &PrinterState,
    field: &PatternRecordField,
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    let field_pat = arena.get_pat(field.pat);
    // For dict patterns, keys are printed as quoted strings
    let label = match arena.get_longident(field.lid.txt) {
        Longident::Lident(name_idx) => {
            let name = arena.get_string(*name_idx);
            Doc::concat(vec![
                Doc::text("\""),
                Doc::text(name.to_string()),
                Doc::text("\""),
            ])
        }
        other => print_lident(arena, other),
    };

    // Print pattern
    let pat_doc = print_pattern(state, field_pat, cmt_tbl, arena);
    let pat_doc = if parens::pattern_record_row_rhs(arena, field_pat) {
        add_parens(pat_doc)
    } else {
        pat_doc
    };
    let rhs_doc = if field.opt {
        Doc::concat(vec![Doc::text("?"), pat_doc])
    } else {
        pat_doc
    };

    // Create the row doc
    let doc = Doc::group(Doc::concat(vec![
        label,
        Doc::text(":"),
        if parsetree_viewer::is_huggable_pattern(field_pat) {
            Doc::concat(vec![Doc::space(), rhs_doc])
        } else {
            Doc::indent(Doc::concat(vec![Doc::line(), rhs_doc]))
        },
    ]));

    // Wrap with comments for the combined location (label to pattern end)
    let pos_range = PosRange {
        start: arena.loc_start(field.lid.loc).cnum,
        end: arena.loc_end(field_pat.ppat_loc).cnum,
    };
    let leading = cmt_tbl.remove_leading_comments_by_pos(pos_range);
    let trailing = cmt_tbl.remove_trailing_comments_by_pos(pos_range);
    let full_loc = FullLocation {
        loc_start: arena.loc_start(field.lid.loc).clone(),
        loc_end: arena.loc_end(field_pat.ppat_loc).clone(),
        loc_ghost: false,
    };
    let doc = print_leading_comments_with(doc, leading, &full_loc);
    print_trailing_comments_with(doc, trailing, &full_loc)
}

/// Check if a pattern record field is punned.
fn is_punned_pattern_field(arena: &ParseArena, field: &PatternRecordField) -> bool {
    match (
        arena.get_longident(field.lid.txt),
        &*arena.get_pat(field.pat).ppat_desc,
    ) {
        (Longident::Lident(name_idx), PatternDesc::Ppat_var(var)) => {
            let name_str = arena.get_string(*name_idx);
            name_str == arena.get_string(var.txt)
        }
        _ => false,
    }
}

// ============================================================================
// Type Printing
// ============================================================================

/// Print a type expression.
pub fn print_typ_expr(
    state: &PrinterState,
    typ: &CoreType,
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    let rendered_type = match &*typ.ptyp_desc {
        CoreTypeDesc::Ptyp_any => Doc::text("_"),

        CoreTypeDesc::Ptyp_var(name) => {
            Doc::concat(vec![Doc::text("'"), print_ident_like(name, true, false)])
        }

        CoreTypeDesc::Ptyp_extension(ext) => print_extension(state, ext, false, cmt_tbl, arena),

        CoreTypeDesc::Ptyp_alias(inner) => {
            let (ref inner_typ_idx, ref alias) = **inner;
            let inner_typ = arena.get_core_type(*inner_typ_idx);
            let needs_parens = matches!(&*inner_typ.ptyp_desc, CoreTypeDesc::Ptyp_arrow(_));
            let typ_doc = print_typ_expr(state, inner_typ, cmt_tbl, arena);
            if needs_parens {
                Doc::concat(vec![
                    Doc::lparen(),
                    typ_doc,
                    Doc::rparen(),
                    Doc::text(" as "),
                    Doc::concat(vec![Doc::text("'"), print_ident_like(alias, false, false)]),
                ])
            } else {
                Doc::concat(vec![
                    typ_doc,
                    Doc::text(" as "),
                    Doc::concat(vec![Doc::text("'"), print_ident_like(alias, false, false)]),
                ])
            }
        }

        CoreTypeDesc::Ptyp_object(inner) => {
            let (ref fields, ref open_flag) = **inner;
            print_object(state, fields, open_flag, false, cmt_tbl, arena)
        }

        CoreTypeDesc::Ptyp_arrow(inner) => {
            let (_, _, ref arity) = **inner;
            print_arrow_type(state, typ, *arity, cmt_tbl, arena)
        }

        CoreTypeDesc::Ptyp_constr(inner) => {
            let (ref lid, ref args) = **inner;
            // Check if this is a reference to an inline record definition
            // OCaml: | Ptyp_constr ({txt = Lident inline_record_name}, _)
            //          when inline_record_definitions |> find_inline_record_definition inline_record_name |> Option.is_some
            if let Longident::Lident(inline_record_name_idx) = arena.get_longident(lid.txt) {
                let inline_record_name = arena.get_string(*inline_record_name_idx);
                if let Some(inline_def) =
                    state.find_inline_record_definition(arena, inline_record_name)
                {
                    // Print the record definition inline instead of as a type reference
                    if let TypeKind::Ptype_record(lds) = &inline_def.ptype_kind {
                        return print_record_declaration_with_inline_records(
                            state,
                            lds,
                            Some(inline_def.ptype_loc),
                            cmt_tbl,
                            arena,
                        );
                    }
                }
            }

            // Handle special case: object type inside type constructor
            if let [single_arg] = args.as_slice() {
                let single_arg = arena.get_core_type(*single_arg);
                if let CoreTypeDesc::Ptyp_object(obj_inner) = &*single_arg.ptyp_desc {
                    let (ref fields, ref open_flag) = **obj_inner;
                    let constr_name = print_lident_path(lid, cmt_tbl, arena);
                    Doc::concat(vec![
                        constr_name,
                        Doc::less_than(),
                        print_object(state, fields, open_flag, true, cmt_tbl, arena),
                        Doc::greater_than(),
                    ])
                }
                // Handle tuple inside constructor
                else if let CoreTypeDesc::Ptyp_tuple(types) = &*single_arg.ptyp_desc {
                    let constr_name = print_lident_path(lid, cmt_tbl, arena);
                    Doc::group(Doc::concat(vec![
                        constr_name,
                        Doc::less_than(),
                        print_tuple_type(state, types, true, cmt_tbl, arena),
                        Doc::greater_than(),
                    ]))
                } else {
                    // Regular single arg case
                    let constr_name = print_lident_path(lid, cmt_tbl, arena);
                    Doc::group(Doc::concat(vec![
                        constr_name,
                        Doc::less_than(),
                        Doc::indent(Doc::concat(vec![
                            Doc::soft_line(),
                            print_typ_expr(state, single_arg, cmt_tbl, arena),
                        ])),
                        Doc::trailing_comma(),
                        Doc::soft_line(),
                        Doc::greater_than(),
                    ]))
                }
            } else {
                let constr_name = print_lident_path(lid, cmt_tbl, arena);
                if args.is_empty() {
                    constr_name
                } else {
                    Doc::group(Doc::concat(vec![
                        constr_name,
                        Doc::less_than(),
                        Doc::indent(Doc::concat(vec![
                            Doc::soft_line(),
                            Doc::join(
                                Doc::concat(vec![Doc::text(","), Doc::line()]),
                                args.iter()
                                    .map(|arg| {
                                        print_typ_expr(
                                            state,
                                            arena.get_core_type(*arg),
                                            cmt_tbl,
                                            arena,
                                        )
                                    })
                                    .collect(),
                            ),
                        ])),
                        Doc::trailing_comma(),
                        Doc::soft_line(),
                        Doc::greater_than(),
                    ]))
                }
            }
        }

        CoreTypeDesc::Ptyp_tuple(types) => print_tuple_type(state, types, false, cmt_tbl, arena),

        CoreTypeDesc::Ptyp_poly(inner) => {
            let (ref vars, ref inner_typ_idx) = **inner;
            let inner_typ = arena.get_core_type(*inner_typ_idx);
            if vars.is_empty() {
                print_typ_expr(state, inner_typ, cmt_tbl, arena)
            } else {
                // OCaml: each type variable has its own location and we print comments for each
                Doc::concat(vec![
                    Doc::join(
                        Doc::space(),
                        vars.iter()
                            .map(|var| {
                                let doc = Doc::concat(vec![
                                    Doc::text("'"),
                                    Doc::text(arena.get_string(var.txt)),
                                ]);
                                print_comments(doc, cmt_tbl, var.loc, arena)
                            })
                            .collect(),
                    ),
                    Doc::text("."),
                    Doc::space(),
                    print_typ_expr(state, inner_typ, cmt_tbl, arena),
                ])
            }
        }

        CoreTypeDesc::Ptyp_package(package_type) => {
            print_package_type(state, package_type, true, cmt_tbl, arena)
        }

        CoreTypeDesc::Ptyp_variant(inner) => {
            let (ref row_fields, ref closed_flag, ref labels_opt) = **inner;
            print_variant_type(
                state,
                row_fields,
                closed_flag,
                labels_opt,
                typ,
                cmt_tbl,
                arena,
            )
        }
    };

    // Handle attributes
    let should_print_its_own_attributes = matches!(*typ.ptyp_desc, CoreTypeDesc::Ptyp_arrow(_));

    let doc = if !typ.ptyp_attributes.is_empty() && !should_print_its_own_attributes {
        let (doc_comment_attrs, other_attrs) =
            parsetree_viewer::partition_doc_comment_attributes(arena, &typ.ptyp_attributes);
        // Use Doc::space() as separator for doc comments on types (matches OCaml)
        // This keeps doc comments inline: `/** doc */ int` instead of on separate line
        let comment_doc = if doc_comment_attrs.is_empty() {
            Doc::nil()
        } else {
            print_doc_comments_with_sep(state, &doc_comment_attrs, cmt_tbl, arena, Doc::space())
        };
        let attrs_doc = if other_attrs.is_empty() {
            Doc::nil()
        } else {
            print_attributes_from_refs(state, &other_attrs, cmt_tbl, arena)
        };
        Doc::group(Doc::concat(vec![comment_doc, attrs_doc, rendered_type]))
    } else {
        rendered_type
    };

    // Wrap with print_comments to attach leading/trailing comments (like OCaml reference)
    print_comments(doc, cmt_tbl, typ.ptyp_loc, arena)
}

/// Print an arrow type.
fn print_arrow_type(
    state: &PrinterState,
    typ: &CoreType,
    arity: Arity,
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    let _ = arity;
    let (attrs_before, args, return_type) = parsetree_viewer::arrow_type(arena, typ);

    let return_type_needs_parens = matches!(*return_type.ptyp_desc, CoreTypeDesc::Ptyp_alias(_));

    let return_doc = {
        let doc = print_typ_expr(state, return_type, cmt_tbl, arena);
        if return_type_needs_parens {
            Doc::concat(vec![Doc::lparen(), doc, Doc::rparen()])
        } else {
            doc
        }
    };

    if args.is_empty() {
        return Doc::nil();
    }

    // Single unlabeled argument with no attrs
    if args.len() == 1 {
        let arg = &args[0];
        if matches!(arg.lbl, ArgLabel::Nolabel) && arg.attrs.is_empty() {
            let has_attrs_before = !attrs_before.is_empty();
            let attrs = if has_attrs_before {
                print_attributes_inline(state, attrs_before, cmt_tbl, arena)
            } else {
                Doc::nil()
            };
            let typ_doc = {
                let doc = print_typ_expr(state, arg.typ, cmt_tbl, arena);
                match &*arg.typ.ptyp_desc {
                    CoreTypeDesc::Ptyp_arrow(_)
                    | CoreTypeDesc::Ptyp_tuple(_)
                    | CoreTypeDesc::Ptyp_alias(_) => add_parens(doc),
                    _ => doc,
                }
            };
            return Doc::group(Doc::concat(vec![
                Doc::group(attrs),
                Doc::group(if has_attrs_before {
                    Doc::concat(vec![
                        Doc::lparen(),
                        Doc::indent(Doc::concat(vec![
                            Doc::soft_line(),
                            typ_doc,
                            Doc::text(" => "),
                            return_doc,
                        ])),
                        Doc::soft_line(),
                        Doc::rparen(),
                    ])
                } else {
                    Doc::concat(vec![typ_doc, Doc::text(" => "), return_doc])
                }),
            ]));
        }
    }

    // Multiple arguments or labeled argument
    let attrs = print_attributes_inline(state, attrs_before, cmt_tbl, arena);
    let rendered_args = Doc::concat(vec![
        attrs,
        Doc::text("("),
        Doc::indent(Doc::concat(vec![
            Doc::soft_line(),
            Doc::join(
                Doc::concat(vec![Doc::text(","), Doc::line()]),
                args.iter()
                    .map(|param| print_type_parameter(state, param, cmt_tbl, arena))
                    .collect(),
            ),
        ])),
        Doc::trailing_comma(),
        Doc::soft_line(),
        Doc::text(")"),
    ]);

    Doc::group(Doc::concat(vec![
        rendered_args,
        Doc::text(" => "),
        return_doc,
    ]))
}

/// Print a type parameter (argument in an arrow type).
fn print_type_parameter(
    state: &PrinterState,
    param: &parsetree_viewer::TypeParameter<'_>,
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    let attrs = print_attributes(state, param.attrs, cmt_tbl, arena);
    let label_doc = match param.lbl {
        ArgLabel::Nolabel => Doc::nil(),
        ArgLabel::Labelled(name) => Doc::concat(vec![
            Doc::text("~"),
            print_ident_like(arena.get_string(name.txt), false, false),
            Doc::text(": "),
        ]),
        ArgLabel::Optional(name) => Doc::concat(vec![
            Doc::text("~"),
            print_ident_like(arena.get_string(name.txt), false, false),
            Doc::text(": "),
        ]),
    };
    let optional_indicator = match param.lbl {
        ArgLabel::Optional(_) => Doc::text("=?"),
        _ => Doc::nil(),
    };
    let typ_doc = print_typ_expr(state, param.typ, cmt_tbl, arena);

    let doc = Doc::group(Doc::concat(vec![attrs, label_doc, typ_doc]));

    // OCaml: let loc = {(Asttypes.get_lbl_loc lbl) with loc_end = typ.ptyp_loc.loc_end}
    // This ensures comments before the label appear before ~label, not after.
    // [loc] ends before [=?].
    match param.lbl.located() {
        Some(name) => {
            let (pos_range, full_loc) =
                make_combined_pos_range(name.loc, param.typ.ptyp_loc, arena);
            print_comments_before_marker_by_pos(
                doc,
                cmt_tbl,
                pos_range,
                &full_loc,
                optional_indicator,
            )
        }
        None => {
            // Nolabel: use type's location only
            Doc::concat(vec![
                print_comments(doc, cmt_tbl, param.typ.ptyp_loc, arena),
                optional_indicator,
            ])
        }
    }
}

/// Print tuple type.
fn print_tuple_type(
    state: &PrinterState,
    types: &[CoreTypeIdx],
    inline: bool,
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    let tuple = Doc::concat(vec![
        Doc::lparen(),
        Doc::indent(Doc::concat(vec![
            Doc::soft_line(),
            Doc::join(
                Doc::concat(vec![Doc::text(","), Doc::line()]),
                types
                    .iter()
                    .map(|t| print_typ_expr(state, arena.get_core_type(*t), cmt_tbl, arena))
                    .collect(),
            ),
        ])),
        Doc::trailing_comma(),
        Doc::soft_line(),
        Doc::rparen(),
    ]);
    if inline { tuple } else { Doc::group(tuple) }
}

/// Print object type.
fn print_object(
    state: &PrinterState,
    fields: &[ObjectField],
    open_flag: &ClosedFlag,
    inline: bool,
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    if fields.is_empty() {
        let dot_or_dotdot = match open_flag {
            ClosedFlag::Closed => Doc::text("."),
            ClosedFlag::Open => Doc::text(".."),
        };
        return Doc::concat(vec![Doc::lbrace(), dot_or_dotdot, Doc::rbrace()]);
    }

    let open_doc = match open_flag {
        ClosedFlag::Closed => Doc::nil(),
        ClosedFlag::Open => {
            // Check if first field is inherit
            if matches!(fields.first(), Some(ObjectField::Oinherit(_))) {
                Doc::text(".. ")
            } else {
                Doc::text("..")
            }
        }
    };

    let fields_doc = Doc::join(
        Doc::concat(vec![Doc::text(","), Doc::line()]),
        fields
            .iter()
            .map(|field| print_object_field(state, field, cmt_tbl, arena))
            .collect(),
    );

    let doc = Doc::concat(vec![
        Doc::lbrace(),
        open_doc,
        Doc::indent(Doc::concat(vec![Doc::soft_line(), fields_doc])),
        Doc::trailing_comma(),
        Doc::soft_line(),
        Doc::rbrace(),
    ]);

    if inline { doc } else { Doc::group(doc) }
}

/// Print an object field.
fn print_object_field(
    state: &PrinterState,
    field: &ObjectField,
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    match field {
        ObjectField::Otag(label, attrs, typ) => {
            let typ = arena.get_core_type(*typ);
            // OCaml: wrap label with print_comments for label_loc.loc
            let label_doc = Doc::text(format!("\"{}\"", arena.get_string(label.txt)));
            let label_doc = print_comments(label_doc, cmt_tbl, label.loc, arena);

            let attrs_doc =
                print_attributes_with_loc(state, attrs, Some(label.loc), cmt_tbl, arena, false);
            let typ_doc = print_typ_expr(state, typ, cmt_tbl, arena);

            let doc = Doc::concat(vec![attrs_doc, label_doc, Doc::text(": "), typ_doc]);

            // OCaml: wrap entire field with print_comments using combined location
            // cmt_loc = {label_loc.loc with loc_end = typ.ptyp_loc.loc_end}
            let (pos_range, full_loc) = make_combined_pos_range(label.loc, typ.ptyp_loc, arena);
            print_comments_by_pos(doc, cmt_tbl, pos_range, &full_loc)
        }
        ObjectField::Oinherit(typ) => Doc::concat(vec![
            Doc::text("..."),
            print_typ_expr(state, arena.get_core_type(*typ), cmt_tbl, arena),
        ]),
    }
}

/// Print polymorphic variant type.
fn print_variant_type(
    state: &PrinterState,
    row_fields: &[RowField],
    closed_flag: &ClosedFlag,
    labels_opt: &Option<Vec<Label>>,
    typ: &CoreType,
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    let force_break = arena.loc_start(typ.ptyp_loc).line < arena.loc_end(typ.ptyp_loc).line;

    let docs: Vec<Doc> = row_fields
        .iter()
        .enumerate()
        .map(|(i, field)| print_row_field(state, i, field, cmt_tbl, arena))
        .collect();

    let cases = Doc::join(Doc::line(), docs);

    let opening_symbol = if *closed_flag == ClosedFlag::Open {
        Doc::concat(vec![Doc::greater_than(), Doc::line()])
    } else if labels_opt.is_none() {
        Doc::soft_line()
    } else {
        Doc::concat(vec![Doc::less_than(), Doc::line()])
    };

    let labels = match labels_opt {
        None => Doc::nil(),
        Some(labels) if labels.is_empty() => Doc::nil(),
        Some(labels) => Doc::concat(
            labels
                .iter()
                .map(|label| {
                    Doc::concat(vec![
                        Doc::line(),
                        Doc::text("#"),
                        print_poly_var_ident(label),
                    ])
                })
                .collect(),
        ),
    };

    let closing_symbol = match labels_opt {
        None => Doc::nil(),
        Some(labels) if labels.is_empty() => Doc::nil(),
        _ => Doc::text(" >"),
    };

    Doc::breakable_group(
        Doc::concat(vec![
            Doc::lbracket(),
            Doc::indent(Doc::concat(vec![
                opening_symbol,
                cases,
                closing_symbol,
                labels,
            ])),
            Doc::soft_line(),
            Doc::rbracket(),
        ]),
        force_break,
    )
}

/// Print a row field (polymorphic variant constructor).
fn print_row_field(
    state: &PrinterState,
    index: usize,
    field: &RowField,
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    match field {
        RowField::Rtag(label, attrs, has_empty_payload, types) => {
            let (doc_attrs, other_attrs) =
                parsetree_viewer::partition_doc_comment_attributes(arena, attrs);
            let comment_doc = if doc_attrs.is_empty() {
                Doc::nil()
            } else {
                print_doc_comments(state, &doc_attrs, cmt_tbl, arena)
            };
            let bar = if index > 0 || !doc_attrs.is_empty() {
                Doc::text("| ")
            } else {
                Doc::if_breaks(Doc::text("| "), Doc::nil())
            };

            let types_doc = if types.is_empty() {
                Doc::nil()
            } else {
                // res_printer.ml `do_group`: each payload group prints as a
                // parenthesized, comma-separated type list.
                let printed_types: Vec<Doc> = types
                    .iter()
                    .map(|group| {
                        let docs = group
                            .txt
                            .iter()
                            .map(|t| print_typ_expr(state, arena.get_core_type(*t), cmt_tbl, arena))
                            .collect();
                        Doc::concat(vec![
                            Doc::lparen(),
                            Doc::join(Doc::concat(vec![Doc::comma(), Doc::line()]), docs),
                            Doc::rparen(),
                        ])
                    })
                    .collect();
                let cases = Doc::join(
                    Doc::concat(vec![Doc::line(), Doc::text("& ")]),
                    printed_types,
                );
                if *has_empty_payload {
                    Doc::concat(vec![Doc::line(), Doc::text("& "), cases])
                } else {
                    cases
                }
            };

            let attrs_doc = print_attributes_from_refs(state, &other_attrs, cmt_tbl, arena);
            let tag_doc = Doc::group(Doc::concat(vec![
                attrs_doc,
                Doc::concat(vec![Doc::text("#"), print_poly_var_ident(&label.txt)]),
                types_doc,
            ]));
            // Wrap with print_comments to attach leading/trailing comments using label's location
            let tag_doc = print_comments(tag_doc, cmt_tbl, label.loc, arena);

            Doc::concat(vec![comment_doc, bar, tag_doc])
        }
        RowField::Rinherit(typ) => {
            let bar = if index > 0 {
                Doc::text("| ")
            } else {
                Doc::if_breaks(Doc::text("| "), Doc::nil())
            };
            // Note: For inherited types, OCaml uses the type's location for comments
            Doc::concat(vec![
                bar,
                print_typ_expr(state, arena.get_core_type(*typ), cmt_tbl, arena),
            ])
        }
    }
}

/// Print a package type.
fn print_package_type(
    state: &PrinterState,
    package_type: &PackageType,
    print_module_keyword: bool,
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    let (lid, constraints) = package_type;
    let lid_doc = print_longident(arena, arena.get_longident(lid.txt));
    // Wrap lid with print_comments for its location (like OCaml reference)
    let lid_doc = print_comments(lid_doc, cmt_tbl, lid.loc, arena);

    let doc = if constraints.is_empty() {
        Doc::group(lid_doc)
    } else {
        // Print constraints with proper line breaking
        // OCaml creates a cmt_loc spanning from longident to typexpr end for each constraint
        let constraint_docs: Vec<Doc> = constraints
            .iter()
            .enumerate()
            .map(|(i, (name, typ))| {
                let typ = arena.get_core_type(*typ);
                let prefix = if i == 0 { "type " } else { "and type " };
                // Print the constraint content (with comments on name via print_longident_location)
                let name_doc = print_longident(arena, arena.get_longident(name.txt));
                let name_doc = print_comments(name_doc, cmt_tbl, name.loc, arena);
                let constraint_doc = Doc::concat(vec![
                    Doc::text(prefix),
                    name_doc,
                    Doc::text(" = "),
                    print_typ_expr(state, typ, cmt_tbl, arena),
                ]);
                // OCaml wraps the entire constraint with comments using a location
                // that spans from name.loc.start to typ.ptyp_loc.end
                let (pos_range, full_loc) = make_combined_pos_range(name.loc, typ.ptyp_loc, arena);
                print_comments_by_pos(constraint_doc, cmt_tbl, pos_range, &full_loc)
            })
            .collect();

        Doc::group(Doc::concat(vec![
            lid_doc,
            Doc::text(" with"),
            Doc::indent(Doc::concat(vec![
                Doc::line(),
                Doc::join(Doc::line(), constraint_docs),
            ])),
            Doc::soft_line(),
        ]))
    };

    if print_module_keyword {
        Doc::concat(vec![Doc::text("module("), doc, Doc::rparen()])
    } else {
        doc
    }
}

/// Print doc comment attributes.
/// Print doc comments with optional separator.
/// OCaml's `print_doc_comments` takes a `sep` parameter that defaults to `hard_line`.
/// For type expressions, we use `space` as the separator to keep doc comments inline.
fn print_doc_comments_with_sep(
    state: &PrinterState,
    doc_attrs: &[&Attribute],
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
    sep: Doc,
) -> Doc {
    // res_printer.ml:5979-5986
    Doc::concat(vec![
        Doc::group(join_attributes_with_sep(state, doc_attrs, cmt_tbl, arena)),
        sep,
    ])
}

/// `Doc.join_with_sep (List.map print_attribute attrs)`: each attribute is
/// followed by its own separator, a hard line after a doc comment
/// (res_printer.ml:6117-6143, res_doc.ml:134-141).
fn join_attributes_with_sep(
    state: &PrinterState,
    attrs: &[&Attribute],
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    let mut docs = Vec::with_capacity(attrs.len() * 2);
    for (i, attr) in attrs.iter().enumerate() {
        if i > 0 {
            docs.push(
                if parsetree_viewer::is_doc_comment_attribute(arena, attrs[i - 1]) {
                    Doc::hard_line()
                } else {
                    Doc::line()
                },
            );
        }
        docs.push(print_attribute(state, attr, false, cmt_tbl, arena));
    }
    Doc::concat(docs)
}

/// Print doc comments with default separator (hard_line).
fn print_doc_comments(
    state: &PrinterState,
    doc_attrs: &[&Attribute],
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    print_doc_comments_with_sep(state, doc_attrs, cmt_tbl, arena, Doc::hard_line())
}

/// Print attributes from borrowed references.
fn print_attributes_from_refs(
    state: &PrinterState,
    attrs: &[&Attribute],
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    if attrs.is_empty() {
        return Doc::nil();
    }
    let attrs_doc: Vec<Doc> = attrs
        .iter()
        .map(|attr| print_attribute(state, attr, false, cmt_tbl, arena))
        .collect();
    // Join with line (space when flat, newline when breaking), add trailing line
    Doc::concat(vec![
        Doc::group(Doc::join(Doc::line(), attrs_doc)),
        Doc::line(),
    ])
}

/// Print attributes inline (for arrow type parameters).
/// Attributes are joined with line (space when not breaking) and followed by a space.
fn print_attributes_inline(
    state: &PrinterState,
    attrs: &Attributes,
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    if attrs.is_empty() {
        return Doc::nil();
    }
    let attrs_doc: Vec<Doc> = attrs
        .iter()
        .map(|attr| print_attribute(state, attr, false, cmt_tbl, arena))
        .collect();
    // Join with line (space when not breaking), add trailing space
    Doc::concat(vec![
        Doc::group(Doc::join(Doc::line(), attrs_doc)),
        Doc::space(),
    ])
}

// ============================================================================
// Module Printing
// ============================================================================

/// Print a module expression.
fn print_mod_expr(
    state: &PrinterState,
    mod_expr: &ModuleExpr,
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    let doc = match &*mod_expr.pmod_desc {
        ModuleExprDesc::Pmod_ident(lid) => print_longident_location(lid, cmt_tbl, arena),

        ModuleExprDesc::Pmod_structure(structure) if structure.is_empty() => {
            let should_break =
                arena.loc_start(mod_expr.pmod_loc).line < arena.loc_end(mod_expr.pmod_loc).line;
            Doc::breakable_group(
                Doc::concat(vec![
                    Doc::lbrace(),
                    print_comments_inside(cmt_tbl, mod_expr.pmod_loc, arena),
                    Doc::rbrace(),
                ]),
                should_break,
            )
        }

        ModuleExprDesc::Pmod_structure(structure) => Doc::breakable_group(
            Doc::concat(vec![
                Doc::lbrace(),
                Doc::indent(Doc::concat(vec![
                    Doc::soft_line(),
                    print_structure(state, structure, cmt_tbl, arena),
                ])),
                Doc::soft_line(),
                Doc::rbrace(),
            ]),
            true,
        ),

        ModuleExprDesc::Pmod_unpack(expr_idx) => {
            let expr = arena.get_expr(*expr_idx);
            // Check if we should "hug" the expression
            let should_hug = match &*parsetree_viewer::unwrap_braces(arena, expr).pexp_desc {
                ExpressionDesc::Pexp_let(_) => true,
                ExpressionDesc::Pexp_constraint(inner) => {
                    let (ref inner_expr_idx, ref typ) = **inner;
                    let typ = arena.get_core_type(*typ);
                    matches!(&*typ.ptyp_desc, CoreTypeDesc::Ptyp_package(_))
                        && parsetree_viewer::is_block_expr(arena, arena.get_expr(*inner_expr_idx))
                }
                _ => false,
            };

            // Extract module constraint if present
            let (expr_to_print, module_constraint) = match &*expr.pexp_desc {
                ExpressionDesc::Pexp_constraint(inner) => {
                    let (ref inner_expr_idx, ref typ) = **inner;
                    let typ = arena.get_core_type(*typ);
                    match &*typ.ptyp_desc {
                        CoreTypeDesc::Ptyp_package(package_type) => {
                            let package_doc =
                                print_package_type(state, &**package_type, false, cmt_tbl, arena);
                            let package_doc =
                                print_comments(package_doc, cmt_tbl, typ.ptyp_loc, arena);
                            let type_doc = Doc::group(Doc::concat(vec![
                                Doc::text(":"),
                                Doc::indent(Doc::concat(vec![Doc::line(), package_doc])),
                            ]));
                            (arena.get_expr(*inner_expr_idx), type_doc)
                        }
                        _ => (expr, Doc::nil()),
                    }
                }
                _ => (expr, Doc::nil()),
            };

            let unpack_doc = Doc::group(Doc::concat(vec![
                print_expression_with_comments_and_parens(state, expr_to_print, cmt_tbl, arena),
                module_constraint,
            ]));

            Doc::group(Doc::concat(vec![
                Doc::text("unpack("),
                if should_hug {
                    unpack_doc
                } else {
                    Doc::concat(vec![
                        Doc::indent(Doc::concat(vec![Doc::soft_line(), unpack_doc])),
                        Doc::soft_line(),
                    ])
                },
                Doc::rparen(),
            ]))
        }

        ModuleExprDesc::Pmod_extension(ext) => {
            print_extension_at_module_level(state, ext, cmt_tbl, arena, false)
        }

        ModuleExprDesc::Pmod_apply(_, _) => {
            let (args, call_expr) = parsetree_viewer::mod_expr_apply(arena, mod_expr);

            let is_unit_sugar = match args.as_slice() {
                [arg] => {
                    matches!(&*arg.pmod_desc, ModuleExprDesc::Pmod_structure(s) if s.is_empty())
                }
                _ => false,
            };

            let should_hug = match args.as_slice() {
                [arg] => matches!(&*arg.pmod_desc, ModuleExprDesc::Pmod_structure(_)),
                _ => false,
            };

            Doc::group(Doc::concat(vec![
                print_mod_expr(state, call_expr, cmt_tbl, arena),
                if is_unit_sugar {
                    print_mod_apply_arg(state, args[0], cmt_tbl, arena)
                } else {
                    Doc::concat(vec![
                        Doc::lparen(),
                        if should_hug {
                            print_mod_apply_arg(state, args[0], cmt_tbl, arena)
                        } else {
                            Doc::indent(Doc::concat(vec![
                                Doc::soft_line(),
                                Doc::join(
                                    Doc::concat(vec![Doc::comma(), Doc::line()]),
                                    args.iter()
                                        .map(|arg| print_mod_apply_arg(state, arg, cmt_tbl, arena))
                                        .collect(),
                                ),
                            ]))
                        },
                        if !should_hug {
                            Doc::concat(vec![Doc::trailing_comma(), Doc::soft_line()])
                        } else {
                            Doc::nil()
                        },
                        Doc::rparen(),
                    ])
                },
            ]))
        }

        ModuleExprDesc::Pmod_constraint(mod_expr_inner_idx, mod_type_idx) => Doc::concat(vec![
            print_mod_expr(
                state,
                arena.get_mod_expr(*mod_expr_inner_idx),
                cmt_tbl,
                arena,
            ),
            Doc::text(": "),
            print_module_type(state, arena.get_mod_type(*mod_type_idx), cmt_tbl, arena),
        ]),

        ModuleExprDesc::Pmod_functor(inner) => {
            let (_, _, _) = **inner;
            print_mod_functor(state, mod_expr, cmt_tbl, arena)
        }
    };

    // Handle await attribute
    let doc = if parsetree_viewer::has_await_attribute(arena, &mod_expr.pmod_attributes) {
        match &*mod_expr.pmod_desc {
            ModuleExprDesc::Pmod_constraint(_, _) => {
                Doc::concat(vec![Doc::text("await "), Doc::lparen(), doc, Doc::rparen()])
            }
            _ => Doc::concat(vec![Doc::text("await "), doc]),
        }
    } else {
        doc
    };

    print_comments(doc, cmt_tbl, mod_expr.pmod_loc, arena)
}

/// Print a functor module expression.
fn print_mod_functor(
    state: &PrinterState,
    mod_expr: &ModuleExpr,
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    let (parameters, return_mod_expr) = parsetree_viewer::mod_expr_functor(arena, mod_expr);

    // Extract return constraint if present
    let (return_constraint, return_body) = match &*return_mod_expr.pmod_desc {
        ModuleExprDesc::Pmod_constraint(inner_mod_expr_idx, mod_type_idx) => {
            let mod_type = arena.get_mod_type(*mod_type_idx);
            let constraint_doc = print_module_type(state, mod_type, cmt_tbl, arena);
            let constraint_doc = if parens::mod_expr_functor_constraint(mod_type) {
                add_parens(constraint_doc)
            } else {
                constraint_doc
            };
            let mod_constraint = Doc::concat(vec![Doc::text(": "), constraint_doc]);
            (
                mod_constraint,
                print_mod_expr(
                    state,
                    arena.get_mod_expr(*inner_mod_expr_idx),
                    cmt_tbl,
                    arena,
                ),
            )
        }
        _ => (
            Doc::nil(),
            print_mod_expr(state, return_mod_expr, cmt_tbl, arena),
        ),
    };

    let parameters_doc = match parameters.as_slice() {
        // Unit parameter: `()`
        [param] if arena.get_string(param.lbl.txt) == "*" && param.mod_type.is_none() => {
            Doc::group(Doc::concat(vec![
                print_attributes(state, param.attrs, cmt_tbl, arena),
                Doc::text("()"),
            ]))
        }
        // Single unlabeled parameter without type: just the name
        [param] if param.attrs.is_empty() && param.mod_type.is_none() => {
            Doc::text(arena.get_string(param.lbl.txt))
        }
        // Multiple parameters
        _ => Doc::group(Doc::concat(vec![
            Doc::lparen(),
            Doc::indent(Doc::concat(vec![
                Doc::soft_line(),
                Doc::join(
                    Doc::concat(vec![Doc::comma(), Doc::line()]),
                    parameters
                        .iter()
                        .map(|param| print_mod_functor_param(state, param, cmt_tbl, arena))
                        .collect(),
                ),
            ])),
            Doc::trailing_comma(),
            Doc::soft_line(),
            Doc::rparen(),
        ])),
    };

    Doc::group(Doc::concat(vec![
        parameters_doc,
        return_constraint,
        Doc::text(" => "),
        return_body,
    ]))
}

/// Print a functor parameter.
fn print_mod_functor_param(
    state: &PrinterState,
    param: &parsetree_viewer::FunctorParam<'_>,
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    let attrs = print_attributes(state, param.attrs, cmt_tbl, arena);
    let lbl_doc = if arena.get_string(param.lbl.txt) == "*" {
        Doc::text("()")
    } else {
        Doc::text(arena.get_string(param.lbl.txt))
    };
    let lbl_doc = print_comments(lbl_doc, cmt_tbl, param.lbl.loc, arena);

    let doc = Doc::group(Doc::concat(vec![
        attrs,
        lbl_doc,
        match param.mod_type {
            None => Doc::nil(),
            Some(mod_type) => Doc::concat(vec![
                Doc::text(": "),
                print_module_type(state, mod_type, cmt_tbl, arena),
            ]),
        },
    ]));

    // Use the full span from label to end of module type (if present) for comment attachment.
    // This matches OCaml's behavior where cmt_loc spans {lbl.loc with loc_end = mod_type.pmty_loc.loc_end}
    match param.mod_type {
        None => print_comments(doc, cmt_tbl, param.lbl.loc, arena),
        Some(mod_type) => {
            let (pos_range, full_loc) =
                make_combined_pos_range(param.lbl.loc, mod_type.pmty_loc, arena);
            print_comments_by_pos(doc, cmt_tbl, pos_range, &full_loc)
        }
    }
}

/// Print a module apply argument.
fn print_mod_apply_arg(
    state: &PrinterState,
    mod_expr: &ModuleExpr,
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    match &*mod_expr.pmod_desc {
        ModuleExprDesc::Pmod_structure(s) if s.is_empty() => Doc::text("()"),
        _ => print_mod_expr(state, mod_expr, cmt_tbl, arena),
    }
}

/// Print a module type.
fn print_module_type(
    state: &PrinterState,
    mty: &ModuleType,
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    // Track whether attributes are printed inside the match arm
    let attrs_already_printed = matches!(
        &*mty.pmty_desc,
        ModuleTypeDesc::Pmty_functor(_)
            | ModuleTypeDesc::Pmty_signature(_)
            | ModuleTypeDesc::Pmty_ident(_)
    );

    let doc = match &*mty.pmty_desc {
        ModuleTypeDesc::Pmty_ident(lid) => {
            // Print attributes with the identifier
            Doc::concat(vec![
                print_attributes_with_loc(
                    state,
                    &mty.pmty_attributes,
                    Some(lid.loc),
                    cmt_tbl,
                    arena,
                    false,
                ),
                print_longident_location(lid, cmt_tbl, arena),
            ])
        }

        ModuleTypeDesc::Pmty_signature(signature) if signature.is_empty() => {
            let comments_inside = print_comments_inside(cmt_tbl, mty.pmty_loc, arena);
            if !matches!(comments_inside, Doc::Nil) {
                // Has comments inside
                Doc::concat(vec![
                    print_attributes(state, &mty.pmty_attributes, cmt_tbl, arena),
                    Doc::lbrace(),
                    comments_inside,
                    Doc::rbrace(),
                ])
            } else {
                // No comments - use two soft_line elements
                let should_break =
                    arena.loc_start(mty.pmty_loc).line < arena.loc_end(mty.pmty_loc).line;
                Doc::concat(vec![
                    print_attributes(state, &mty.pmty_attributes, cmt_tbl, arena),
                    Doc::breakable_group(
                        Doc::concat(vec![
                            Doc::lbrace(),
                            Doc::soft_line(),
                            Doc::soft_line(),
                            Doc::rbrace(),
                        ]),
                        should_break,
                    ),
                ])
            }
        }

        ModuleTypeDesc::Pmty_signature(signature) => Doc::concat(vec![
            print_attributes(state, &mty.pmty_attributes, cmt_tbl, arena),
            Doc::breakable_group(
                Doc::concat(vec![
                    Doc::lbrace(),
                    Doc::indent(Doc::concat(vec![
                        Doc::soft_line(),
                        print_signature(state, signature, cmt_tbl, arena),
                    ])),
                    Doc::soft_line(),
                    Doc::rbrace(),
                ]),
                true,
            ),
        ]),

        ModuleTypeDesc::Pmty_functor(inner) => {
            let (_, _, _) = **inner;
            print_module_type_functor(state, mty, cmt_tbl, arena)
        }

        ModuleTypeDesc::Pmty_with(inner) => {
            let (ref mod_type_idx, ref with_constraints) = **inner;
            let mod_type = arena.get_mod_type(*mod_type_idx);
            let base_doc = print_module_type(state, mod_type, cmt_tbl, arena);
            let base_doc = if parens::mod_type_with_operand(mod_type) {
                Doc::concat(vec![Doc::lparen(), base_doc, Doc::rparen()])
            } else {
                base_doc
            };
            let constraints_doc = Doc::join(
                Doc::line(),
                with_constraints
                    .iter()
                    .enumerate()
                    .map(|(i, constraint)| {
                        let prefix = if i == 0 { "with " } else { "and " };
                        // res_printer.ml:988-1000
                        Doc::group(Doc::concat(vec![
                            Doc::text(prefix),
                            print_with_constraint(state, constraint, cmt_tbl, arena),
                        ]))
                    })
                    .collect(),
            );
            Doc::group(Doc::concat(vec![
                base_doc,
                Doc::indent(Doc::concat(vec![Doc::line(), constraints_doc])),
            ]))
        }

        ModuleTypeDesc::Pmty_typeof(mod_expr_idx) => Doc::concat(vec![
            Doc::text("module type of "),
            print_mod_expr(state, arena.get_mod_expr(*mod_expr_idx), cmt_tbl, arena),
        ]),

        ModuleTypeDesc::Pmty_extension(ext) => {
            print_extension_at_module_level(state, ext, cmt_tbl, arena, false)
        }

        ModuleTypeDesc::Pmty_alias(lid) => Doc::concat(vec![
            Doc::text("module "),
            print_longident_location(lid, cmt_tbl, arena),
        ]),
    };

    // Handle await attribute
    let doc = if parsetree_viewer::has_await_attribute(arena, &mty.pmty_attributes) {
        Doc::concat(vec![Doc::text("await "), doc])
    } else {
        doc
    };

    // Add attributes for types that don't print them internally
    let doc = if !attrs_already_printed && !mty.pmty_attributes.is_empty() {
        Doc::concat(vec![
            print_attributes(state, &mty.pmty_attributes, cmt_tbl, arena),
            doc,
        ])
    } else {
        doc
    };

    print_comments(doc, cmt_tbl, mty.pmty_loc, arena)
}

/// Print a functor module type.
/// Matches OCaml's print_mod_type for Pmty_functor.
fn print_module_type_functor(
    state: &PrinterState,
    mty: &ModuleType,
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    let (parameters, return_mty) = mod_type_functor(arena, mty);

    let parameters_doc = match parameters.as_slice() {
        // Empty parameters list - shouldn't happen but handle gracefully
        [] => Doc::nil(),
        // Unit parameter: `()`
        [(attrs, lbl, None)] if arena.get_string(lbl.txt) == "*" => {
            let attrs_doc = print_attributes(state, attrs, cmt_tbl, arena);
            let doc = Doc::concat(vec![attrs_doc, Doc::text("()")]);
            print_comments(doc, cmt_tbl, lbl.loc, arena)
        }
        // Single anonymous parameter with type: just print the type (no `_:`)
        // Use the param_mty location for comments since it covers the whole param
        [(attrs, _lbl, Some(param_mty))] if arena.get_string(_lbl.txt) == "_" => {
            let attrs_doc = print_attributes(state, attrs, cmt_tbl, arena);
            let doc = Doc::concat(vec![
                attrs_doc,
                print_module_type(state, param_mty, cmt_tbl, arena),
            ]);
            // Comments are handled by print_module_type, just return doc
            doc
        }
        // Multiple parameters - use parens
        params => {
            Doc::group(Doc::concat(vec![
                Doc::lparen(),
                Doc::indent(Doc::concat(vec![
                    Doc::soft_line(),
                    Doc::join(
                        Doc::concat(vec![Doc::comma(), Doc::line()]),
                        params
                            .iter()
                            .map(|(attrs, lbl, opt_mty)| {
                                let attrs_doc = print_attributes(state, attrs, cmt_tbl, arena);
                                // For "_" label, don't print the label
                                let lbl_doc = if arena.get_string(lbl.txt) == "_" {
                                    Doc::nil()
                                } else if arena.get_string(lbl.txt) == "*" {
                                    print_comments(Doc::text("()"), cmt_tbl, lbl.loc, arena)
                                } else {
                                    print_comments(
                                        Doc::text(arena.get_string(lbl.txt)),
                                        cmt_tbl,
                                        lbl.loc,
                                        arena,
                                    )
                                };
                                let doc = match opt_mty {
                                    None => Doc::concat(vec![attrs_doc, lbl_doc]),
                                    Some(mty) => {
                                        // For "_" label, don't add `: ` prefix
                                        let sep = if arena.get_string(lbl.txt) == "_" {
                                            Doc::nil()
                                        } else {
                                            Doc::text(": ")
                                        };
                                        Doc::concat(vec![
                                            attrs_doc,
                                            lbl_doc,
                                            sep,
                                            print_module_type(state, mty, cmt_tbl, arena),
                                        ])
                                    }
                                };
                                // Create combined position range for comments: from label start to mod_type end
                                // This matches OCaml which wraps the whole parameter with print_comments cmt_loc
                                let (pos_range, full_loc) = match opt_mty {
                                    None => {
                                        let fl = arena.to_location(lbl.loc);
                                        (PosRange::from_location(&fl), fl)
                                    }
                                    Some(mty) => {
                                        let start = arena.loc_start(lbl.loc);
                                        let end = arena.loc_end(mty.pmty_loc);
                                        let full_loc = FullLocation::from_positions(
                                            start.clone(),
                                            end.clone(),
                                        );
                                        (PosRange::from_location(&full_loc), full_loc)
                                    }
                                };
                                // Wrap entire parameter doc with comments using combined location
                                print_comments_by_pos(doc, cmt_tbl, pos_range, &full_loc)
                            })
                            .collect(),
                    ),
                ])),
                Doc::trailing_comma(),
                Doc::soft_line(),
                Doc::rparen(),
            ]))
        }
    };

    let return_doc = {
        let doc = print_module_type(state, return_mty, cmt_tbl, arena);
        if parens::mod_type_functor_return(return_mty) {
            add_parens(doc)
        } else {
            doc
        }
    };

    // res_printer.ml:934-947: a signature result keeps its `{` after `=>`.
    let arrow_sep = match &*return_mty.pmty_desc {
        ModuleTypeDesc::Pmty_signature(_) => Doc::space(),
        _ => Doc::line(),
    };
    Doc::group(Doc::concat(vec![
        parameters_doc,
        Doc::group(Doc::concat(vec![Doc::text(" =>"), arrow_sep, return_doc])),
    ]))
}

/// Extract functor parameters from a module type.
/// Returns a list of (attributes, label, optional param type) and the return type.
fn mod_type_functor<'a>(
    arena: &'a ParseArena,
    mty: &'a ModuleType,
) -> (
    Vec<(&'a [Attribute], &'a StringLoc, Option<&'a ModuleType>)>,
    &'a ModuleType,
) {
    fn loop_functor<'a>(
        arena: &'a ParseArena,
        acc: Vec<(&'a [Attribute], &'a StringLoc, Option<&'a ModuleType>)>,
        mty: &'a ModuleType,
    ) -> (
        Vec<(&'a [Attribute], &'a StringLoc, Option<&'a ModuleType>)>,
        &'a ModuleType,
    ) {
        match &*mty.pmty_desc {
            ModuleTypeDesc::Pmty_functor(inner) => {
                let (ref lbl, ref mod_type_idx, ref return_mty_idx) = **inner;
                let mut new_acc = acc;
                // Attributes on functor are for the parameter
                new_acc.push((
                    &mty.pmty_attributes,
                    lbl,
                    mod_type_idx.as_ref().map(|idx| arena.get_mod_type(*idx)),
                ));
                loop_functor(arena, new_acc, arena.get_mod_type(*return_mty_idx))
            }
            _ => (acc, mty),
        }
    }
    loop_functor(arena, Vec::new(), mty)
}

/// Print a with constraint.
fn print_with_constraint(
    state: &PrinterState,
    constraint: &WithConstraint,
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    match constraint {
        WithConstraint::Pwith_type(lid, type_decl) => {
            print_type_declaration_with_lid(state, lid, type_decl, false, cmt_tbl, arena)
        }
        WithConstraint::Pwith_module(lid1, lid2) => Doc::concat(vec![
            Doc::text("module "),
            print_longident(arena, arena.get_longident(lid1.txt)),
            Doc::text(" ="),
            Doc::indent(Doc::concat(vec![
                Doc::line(),
                print_longident(arena, arena.get_longident(lid2.txt)),
            ])),
        ]),
        WithConstraint::Pwith_typesubst(lid, type_decl) => {
            print_type_declaration_with_lid(state, lid, type_decl, true, cmt_tbl, arena)
        }
        WithConstraint::Pwith_modsubst(lid1, lid2) => Doc::concat(vec![
            Doc::text("module "),
            print_longident(arena, arena.get_longident(lid1.txt)),
            Doc::text(" :="),
            Doc::indent(Doc::concat(vec![
                Doc::line(),
                print_longident(arena, arena.get_longident(lid2.txt)),
            ])),
        ]),
    }
}

/// OCaml `Res_printer.print_type_params` (res_printer.ml:1554-1578).
pub fn print_type_params(
    state: &PrinterState,
    type_params: &[(CoreTypeIdx, Variance)],
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    if type_params.is_empty() {
        return Doc::nil();
    }
    let params: Vec<Doc> = type_params
        .iter()
        .map(|(typ, variance)| {
            let doc = print_type_param(state, typ, variance, cmt_tbl, arena);
            print_comments(doc, cmt_tbl, arena.get_core_type(*typ).ptyp_loc, arena)
        })
        .collect();
    Doc::group(Doc::concat(vec![
        Doc::less_than(),
        Doc::indent(Doc::concat(vec![
            Doc::soft_line(),
            Doc::join(Doc::concat(vec![Doc::comma(), Doc::line()]), params),
        ])),
        Doc::trailing_comma(),
        Doc::soft_line(),
        Doc::greater_than(),
    ]))
}

/// Print a type parameter with variance (covariant +, contravariant -, or invariant).
fn print_type_param(
    state: &PrinterState,
    typ: &CoreTypeIdx,
    variance: &Variance,
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    let variance_doc = match variance {
        Variance::Covariant => Doc::text("+"),
        Variance::Contravariant => Doc::text("-"),
        Variance::Invariant => Doc::nil(),
    };
    Doc::concat(vec![
        variance_doc,
        print_typ_expr(state, arena.get_core_type(*typ), cmt_tbl, arena),
    ])
}

/// Print a type declaration with its longident.
/// `is_substitution` determines whether to use `:=` (true) or `=` (false).
fn print_type_declaration_with_lid(
    state: &PrinterState,
    lid: &crate::parse_arena::Located<crate::parse_arena::LidentIdx>,
    td: &TypeDeclaration,
    is_substitution: bool,
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    // res_printer.ml:1006-1027: the name is printed with the real comment
    // table, the declaration itself with `Comment_table.empty`.
    let name = print_lident_path(lid, cmt_tbl, arena);
    let mut empty_tbl = CommentTable::new();
    let cmt_tbl = &mut empty_tbl;
    let equal_sign = if is_substitution { ":=" } else { "=" };
    // res_printer.ml:1364-1433 print_type_declaration (i = 0, no rec flag).
    let attrs = print_attributes_with_loc(
        state,
        &td.ptype_attributes,
        Some(td.ptype_loc),
        cmt_tbl,
        arena,
        false,
    );
    let private_flag = match td.ptype_private {
        PrivateFlag::Private => Doc::text("private "),
        PrivateFlag::Public => Doc::nil(),
    };
    let equal = Doc::concat(vec![Doc::space(), Doc::text(equal_sign), Doc::space()]);
    let type_params = print_type_params(state, &td.ptype_params, cmt_tbl, arena);
    let manifest = |cmt_tbl: &mut CommentTable| match &td.ptype_manifest {
        None => Doc::nil(),
        Some(typ) => Doc::concat(vec![
            equal.clone(),
            print_typ_expr(state, arena.get_core_type(*typ), cmt_tbl, arena),
        ]),
    };
    let manifest_and_kind = match &td.ptype_kind {
        TypeKind::Ptype_abstract => match &td.ptype_manifest {
            None => Doc::nil(),
            Some(typ) => Doc::concat(vec![
                equal.clone(),
                private_flag,
                print_typ_expr(state, arena.get_core_type(*typ), cmt_tbl, arena),
            ]),
        },
        TypeKind::Ptype_open => Doc::concat(vec![equal.clone(), private_flag, Doc::text("..")]),
        TypeKind::Ptype_record(lds) => {
            let manifest = manifest(cmt_tbl);
            Doc::concat(vec![
                manifest,
                equal.clone(),
                private_flag,
                print_record_declaration(state, lds, Some(td.ptype_loc), cmt_tbl, arena),
            ])
        }
        TypeKind::Ptype_variant(cds) => {
            let manifest = manifest(cmt_tbl);
            Doc::concat(vec![
                manifest,
                Doc::concat(vec![Doc::space(), Doc::text(equal_sign)]),
                print_constructor_declarations(state, cds, &td.ptype_private, cmt_tbl, arena),
            ])
        }
    };
    let constraints = print_type_constraints(state, &td.ptype_cstrs, cmt_tbl, arena);
    Doc::group(Doc::concat(vec![
        attrs,
        Doc::text("type "),
        name,
        type_params,
        manifest_and_kind,
        constraints,
    ]))
}

/// Print extension at module level.
/// This reuses the same logic as print_extension for attributes.
fn print_extension_at_module_level(
    state: &PrinterState,
    ext: &Extension,
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
    at_module_lvl: bool,
) -> Doc {
    let (name, payload) = ext;
    // OCaml: Doc.text "%" (if at_module_lvl then Doc.text "%" else Doc.nil) Doc.text txt
    let ext_name = Doc::concat(vec![
        Doc::text("%"),
        if at_module_lvl {
            Doc::text("%")
        } else {
            Doc::nil()
        },
        Doc::text(arena.get_string(name.txt)),
    ]);
    let ext_name = print_comments(ext_name, cmt_tbl, name.loc, arena);
    Doc::group(Doc::concat(vec![
        ext_name,
        print_payload(state, payload, cmt_tbl, arena),
    ]))
}

// ============================================================================
// Match/Try Printing (placeholder)
// ============================================================================

/// Print match expression.
fn print_match_expression(
    state: &PrinterState,
    expr: &Expression,
    cases: &[Case],
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    // Match OCaml: the scrutinee expression goes through Parens.expr for brace handling
    let scrutinee = {
        let doc = print_expression_with_comments(state, expr, cmt_tbl, arena);
        match parens::expr(arena, expr) {
            ParenKind::Parenthesized => add_parens(doc),
            ParenKind::Braced(braces) => print_braces(doc, expr, braces, arena),
            ParenKind::Nothing => doc,
        }
    };
    // print_cases_with_braces returns the full { cases } block
    let cases_block = print_cases_with_braces(state, cases, cmt_tbl, arena);
    Doc::concat(vec![
        Doc::text("switch "),
        scrutinee,
        Doc::space(),
        cases_block,
    ])
}

/// Print try expression.
fn print_try_expression(
    state: &PrinterState,
    expr: &Expression,
    cases: &[Case],
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    let body = {
        let doc = print_expression_with_comments(state, expr, cmt_tbl, arena);
        match parens::expr(arena, expr) {
            ParenKind::Parenthesized => add_parens(doc),
            ParenKind::Braced(braces) => print_braces(doc, expr, braces, arena),
            ParenKind::Nothing => doc,
        }
    };
    let cases_block = print_cases_with_braces(state, cases, cmt_tbl, arena);
    Doc::concat(vec![
        Doc::text("try "),
        body,
        Doc::text(" catch "),
        cases_block,
    ])
}

/// Check if a pattern needs parentheses in a case context.
/// Constraint patterns like `(p: typ)` need parens at the case level.
fn case_pattern_needs_parens(_arena: &ParseArena, pattern: &Pattern) -> bool {
    // res_printer.ml:5545-5549: every constrained case pattern is
    // parenthesized, `(module(M: S))` included.
    matches!(&*pattern.ppat_desc, PatternDesc::Ppat_constraint(_))
}

/// Get the position range for a case (from pattern start to rhs end).
/// This is used for comment attachment.
fn get_case_pos_range(case: &Case, arena: &ParseArena) -> PosRange {
    let lhs = arena.get_pat(case.pc_lhs);
    let rhs = arena.get_expr(case.pc_rhs);
    let start = arena.loc_start(lhs.ppat_loc).cnum;
    let end = match parsetree_viewer::process_braces(arena, rhs).0 {
        Some(braces_loc) => arena.loc_end(braces_loc).cnum,
        None => arena.loc_end(rhs.pexp_loc).cnum,
    };
    PosRange { start, end }
}

/// Print match cases with surrounding braces.
/// Returns the full `{ cases }` block with proper formatting.
/// This matches OCaml's print_cases which returns a breakable_group with force_break.
fn print_cases_with_braces(
    state: &PrinterState,
    cases: &[Case],
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    let cases_doc = print_cases(state, cases, cmt_tbl, arena);
    Doc::breakable_group(
        Doc::concat(vec![
            Doc::text("{"),
            Doc::concat(vec![
                Doc::line(), // Line break after { (like OCaml's Doc.line)
                cases_doc,
            ]),
            Doc::line(), // Line break before }
            Doc::text("}"),
        ]),
        true, // force_break
    )
}

/// Print match cases.
/// This is similar to OCaml's print_list but specialized for cases.
fn print_cases(
    state: &PrinterState,
    cases: &[Case],
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    if cases.is_empty() {
        return Doc::nil();
    }

    let mut result = Vec::new();
    let mut prev_end_line = 0i32;

    for (i, case) in cases.iter().enumerate() {
        let pos_range = get_case_pos_range(case, arena);

        // Get the effective start line for blank line calculation
        // If there's a leading comment, use the comment's start line instead of the case's
        // This matches OCaml's print_list behavior
        let start_line = match cmt_tbl.get_first_leading_comment_by_pos(pos_range) {
            Some(comment) => comment.loc.loc_start.line as i32,
            None => arena.loc_start(arena.get_pat(case.pc_lhs).ppat_loc).line as i32,
        };

        // Add separator between cases (not before first case)
        if i > 0 {
            // Check if there was a blank line in the source
            let sep = if start_line - prev_end_line > 1 {
                // More than 1 line between: preserve blank line
                Doc::concat(vec![Doc::hard_line(), Doc::hard_line()])
            } else {
                Doc::hard_line()
            };
            result.push(sep);
        }

        // Print the case (without leading hard_line, that's handled above)
        let doc = print_case_content(state, case, cmt_tbl, arena);

        // Print leading and trailing comments for this case
        let leading = cmt_tbl.remove_leading_comments_by_pos(pos_range);
        let trailing = cmt_tbl.remove_trailing_comments_by_pos(pos_range);
        // Use braces attribute location if present, matching get_case_pos_range
        let rhs = arena.get_expr(case.pc_rhs);
        let end_pos = match parsetree_viewer::process_braces(arena, rhs).0 {
            Some(braces_loc) => arena.loc_end(braces_loc).clone(),
            None => arena.loc_end(rhs.pexp_loc).clone(),
        };
        let full_loc = crate::location::Location {
            loc_start: arena.loc_start(arena.get_pat(case.pc_lhs).ppat_loc).clone(),
            loc_end: end_pos,
            loc_ghost: false,
        };
        let doc_with_leading = print_leading_comments_with(doc, leading, &full_loc);
        let doc_with_comments = print_trailing_comments_with(doc_with_leading, trailing, &full_loc);

        result.push(doc_with_comments);

        // Track end line for next iteration
        // Use braces attribute location if present, matching get_case_pos_range and full_loc
        prev_end_line = match parsetree_viewer::process_braces(arena, arena.get_expr(case.pc_rhs)).0
        {
            Some(braces_loc) => arena.loc_end(braces_loc).line as i32,
            None => arena.loc_end(arena.get_expr(case.pc_rhs).pexp_loc).line as i32,
        };
    }

    Doc::concat(result)
}

/// Print a single match case (content only, without leading hard_line).
/// The leading line breaks are handled by print_cases.
fn print_case_content(
    state: &PrinterState,
    case: &Case,
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    let lhs = arena.get_pat(case.pc_lhs);
    let rhs_expr = arena.get_expr(case.pc_rhs);
    // Print the RHS: a block (braced or not) prints without braces.
    let is_block_rhs = parsetree_viewer::is_block_expr(arena, rhs_expr);
    let rhs = if is_block_rhs {
        print_expression_block(state, false, rhs_expr, cmt_tbl, arena)
    } else {
        let doc = print_expression_with_comments(state, rhs_expr, cmt_tbl, arena);
        match parens::expr(arena, rhs_expr) {
            ParenKind::Parenthesized => add_parens(doc),
            _ => doc,
        }
    };

    // Print guard if present
    let guard = match &case.pc_guard {
        None => Doc::nil(),
        Some(expr) => Doc::group(Doc::concat(vec![
            Doc::line(),
            Doc::text("if "),
            print_expression_with_comments_and_parens(state, arena.get_expr(*expr), cmt_tbl, arena),
        ])),
    };

    // Check if RHS should be on the same line
    let should_inline_rhs = !is_block_rhs
        && match &*rhs_expr.pexp_desc {
            ExpressionDesc::Pexp_construct(lid, _) => {
                let name = match arena.get_longident(lid.txt) {
                    crate::parser::longident::Longident::Lident(s) => arena.get_string(*s),
                    _ => "",
                };
                matches!(name, "()" | "true" | "false")
            }
            ExpressionDesc::Pexp_constant(_) | ExpressionDesc::Pexp_ident(_) => true,
            _ if parsetree_viewer::is_huggable_rhs(arena, rhs_expr) => true,
            _ => false,
        };

    // Check if pattern should be indented
    let should_indent_pattern = !matches!(&*lhs.ppat_desc, PatternDesc::Ppat_or(_, _));

    // Print pattern
    let pattern_doc = {
        let doc = print_pattern(state, lhs, cmt_tbl, arena);
        if case_pattern_needs_parens(arena, lhs) {
            add_parens(doc)
        } else {
            doc
        }
    };

    let content = Doc::concat(vec![
        if should_indent_pattern {
            Doc::indent(pattern_doc)
        } else {
            pattern_doc
        },
        Doc::indent(guard),
        Doc::text(" =>"),
        Doc::indent(Doc::concat(vec![
            if should_inline_rhs {
                Doc::space()
            } else {
                Doc::line()
            },
            rhs,
        ])),
    ]);

    // Return just the grouped case content, without leading hard_line
    // (line breaks between cases are handled by print_cases)
    Doc::group(Doc::concat(vec![Doc::text("| "), content]))
}

// ============================================================================
// Value Bindings
// ============================================================================

/// Print value bindings using print_listi for proper comment handling.
fn print_value_bindings(
    state: &PrinterState,
    bindings: &[ValueBinding],
    rec_flag: &RecFlag,
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    let rec_doc = match rec_flag {
        RecFlag::Nonrecursive => Doc::nil(),
        RecFlag::Recursive => Doc::text("rec "),
    };

    print_listi(
        |vb: &ValueBinding| vb.pvb_loc,
        bindings,
        |vb, cmt_tbl_inner, i| print_value_binding(state, vb, i, &rec_doc, cmt_tbl_inner, arena),
        cmt_tbl,
        arena,
        false, // ignore_empty_lines
        false, // force_break (will be calculated by print_listi)
    )
}

/// Print a single value binding.
fn print_value_binding(
    state: &PrinterState,
    vb: &ValueBinding,
    index: usize,
    rec_doc: &Doc,
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    // Check for let.unwrap attribute
    let has_unwrap = vb
        .pvb_attributes
        .iter()
        .any(|attr| arena.get_string(attr.0.txt) == "let.unwrap");

    // Print attributes (filtering out let.unwrap)
    let attrs: Vec<&Attribute> = vb
        .pvb_attributes
        .iter()
        .filter(|attr| arena.get_string(attr.0.txt) != "let.unwrap")
        .collect();
    // Use print_attributes_with_loc to get proper line breaking behavior
    // (uses Doc::line() which can collapse to space when the outer group fits)
    let attrs_doc = {
        let attrs_slice: Vec<Attribute> = attrs.into_iter().cloned().collect();
        let pvb_pat = arena.get_pat(vb.pvb_pat);
        print_attributes_with_loc(
            state,
            &attrs_slice,
            Some(pvb_pat.ppat_loc),
            cmt_tbl,
            arena,
            false,
        )
    };

    let header = if index == 0 {
        let let_kw = if has_unwrap { "let? " } else { "let " };
        Doc::concat(vec![Doc::text(let_kw), rec_doc.clone()])
    } else {
        Doc::text("and ")
    };

    // res_printer.ml:2359-2392: `pvb_constraint = Some {pvc_newtypes; pvc_type}`
    // prints `let p: type a b. t = e`.
    if let Some(constraint) = arena.value_constraint(vb.pvb_pat) {
        let newtypes = Doc::join(
            Doc::space(),
            constraint
                .pvc_newtypes
                .iter()
                .map(|name| {
                    print_comments(
                        print_ident_like(arena.get_string(name.txt), false, false),
                        cmt_tbl,
                        name.loc,
                        arena,
                    )
                })
                .collect(),
        );
        let pat_doc = print_pattern(state, arena.get_pat(vb.pvb_pat), cmt_tbl, arena);
        let typ_doc = print_typ_expr(
            state,
            arena.get_core_type(constraint.pvc_type),
            cmt_tbl,
            arena,
        );
        let expr_doc = print_expression_with_comments_and_parens(
            state,
            arena.get_expr(vb.pvb_expr),
            cmt_tbl,
            arena,
        );
        return Doc::group(Doc::concat(vec![
            attrs_doc,
            header,
            pat_doc,
            Doc::text(":"),
            Doc::indent(Doc::concat(vec![
                Doc::line(),
                Doc::text("type "),
                newtypes,
                Doc::dot(),
                Doc::space(),
                typ_doc,
                Doc::text(" ="),
                Doc::line(),
                expr_doc,
            ])),
        ]));
    }

    // res_printer.ml:2393-2450: `Ppat_constraint (p, Ptyp_poly)` over a
    // `Pexp_fun` with newtypes.
    let fun_has_newtypes = match &*arena.get_expr(vb.pvb_expr).pexp_desc {
        ExpressionDesc::Pexp_fun(fun) => !arena.nary_fun_newtypes(fun).is_empty(),
        _ => false,
    };
    if let (PatternDesc::Ppat_constraint(pat_inner), true) =
        (&*arena.get_pat(vb.pvb_pat).ppat_desc, fun_has_newtypes)
    {
        let (ref inner_pat_idx, ref pat_typ) = **pat_inner;
        let pat_typ = arena.get_core_type(*pat_typ);
        let inner_pat = arena.get_pat(*inner_pat_idx);
        if matches!(*pat_typ.ptyp_desc, CoreTypeDesc::Ptyp_poly(_)) {
            let vb_expr = arena.get_expr(vb.pvb_expr);
            let (_, parameters, return_expr) = parsetree_viewer::fun_expr(arena, vb_expr);

            // Build the "type t u." part from NewTypes parameter
            let abstract_type = if let Some(parsetree_viewer::FunParam::NewTypes {
                names, ..
            }) = parameters.first()
            {
                if parameters.len() == 1 {
                    let names_doc: Vec<Doc> = names
                        .iter()
                        .map(|name| Doc::text(arena.get_string(name.txt)))
                        .collect();
                    Doc::concat(vec![
                        Doc::text("type "),
                        Doc::join(Doc::space(), names_doc),
                        Doc::text("."),
                    ])
                } else {
                    Doc::nil()
                }
            } else {
                Doc::nil()
            };

            // Print the inner pattern (without the type constraint)
            let pat_doc = print_pattern(state, inner_pat, cmt_tbl, arena);

            // Check if return_expr is Pexp_constraint
            if let ExpressionDesc::Pexp_constraint(constraint_inner) = &*return_expr.pexp_desc {
                let (ref expr_idx, ref typ) = **constraint_inner;
                let expr = arena.get_expr(*expr_idx);
                // Use the constraint's type and expression
                let typ_doc = print_typ_expr(state, arena.get_core_type(*typ), cmt_tbl, arena);
                let expr_doc =
                    print_expression_with_comments_and_parens(state, expr, cmt_tbl, arena);

                return Doc::group(Doc::concat(vec![
                    attrs_doc,
                    header,
                    pat_doc,
                    Doc::text(":"),
                    Doc::indent(Doc::concat(vec![
                        Doc::line(),
                        abstract_type,
                        Doc::space(),
                        typ_doc,
                        Doc::text(" ="),
                        Doc::concat(vec![Doc::line(), expr_doc]),
                    ])),
                ]));
            } else {
                // Use pat_typ from the pattern constraint
                let typ_doc = print_typ_expr(state, pat_typ, cmt_tbl, arena);
                let expr_doc =
                    print_expression_with_comments_and_parens(state, vb_expr, cmt_tbl, arena);

                return Doc::group(Doc::concat(vec![
                    attrs_doc,
                    header,
                    pat_doc,
                    Doc::text(":"),
                    Doc::indent(Doc::concat(vec![
                        Doc::line(),
                        abstract_type,
                        Doc::space(),
                        typ_doc,
                        Doc::text(" ="),
                        Doc::concat(vec![Doc::line(), expr_doc]),
                    ])),
                ]));
            }
        }
    }

    let vb_expr = arena.get_expr(vb.pvb_expr);
    // Print expression and check if it needs parens/braces
    let doc = print_expression_with_comments(state, vb_expr, cmt_tbl, arena);
    let printed_expr = match parens::expr(arena, vb_expr) {
        ParenKind::Parenthesized => add_parens(doc),
        ParenKind::Braced(loc) => print_braces(doc, vb_expr, loc, arena),
        ParenKind::Nothing => doc,
    };
    // res_printer.ml:2474-2482: a line comment trailing the pattern moves
    // `=` to its own line.
    let pvb_pat = arena.get_pat(vb.pvb_pat);
    let pattern_has_trailing_line_comment = cmt_tbl
        .get_trailing_comments(pvb_pat.ppat_loc, arena)
        .is_some_and(|comments| comments.iter().any(|c| c.is_single_line()));
    let pat = print_pattern(state, pvb_pat, cmt_tbl, arena);
    let equal_doc = if pattern_has_trailing_line_comment {
        Doc::indent(Doc::concat(vec![Doc::hard_line(), Doc::text("=")]))
    } else {
        Doc::text(" =")
    };

    // Special case: single pipe expression
    // OCaml uses custom_layout to try inline first, then indented
    // This handles: let x = switch z { | Red => 1 }->switch y { | Blue => 2 }
    if parsetree_viewer::is_single_pipe_expr(arena, vb_expr) {
        return Doc::custom_layout(vec![
            // First option: inline
            Doc::group(Doc::concat(vec![
                attrs_doc.clone(),
                header.clone(),
                pat.clone(),
                equal_doc.clone(),
                Doc::space(),
                printed_expr.clone(),
            ])),
            // Second option: indented
            Doc::group(Doc::concat(vec![
                attrs_doc,
                header,
                pat,
                equal_doc.clone(),
                Doc::indent(Doc::concat(vec![Doc::line(), printed_expr])),
            ])),
        ]);
    }

    // Check if expression should be indented after `=`
    // This matches OCaml's value_binding logic for indentation
    let opt_braces = parsetree_viewer::process_braces(arena, vb_expr).0;
    let should_indent = opt_braces.is_none() && {
        match &*vb_expr.pexp_desc {
            // Ternary without attributes: indent if condition is binary or has attrs
            ExpressionDesc::Pexp_ternary(inner) if vb_expr.pexp_attributes.is_empty() => {
                let (ref if_expr_idx, _, _) = **inner;
                let if_expr = arena.get_expr(*if_expr_idx);
                parsetree_viewer::is_binary_expression(arena, if_expr)
                    || parsetree_viewer::has_attributes(arena, &if_expr.pexp_attributes)
            }
            // Pexp_newtype: don't indent
            ExpressionDesc::Pexp_newtype { .. } => false,
            // Tagged template: don't indent
            ExpressionDesc::Pexp_tagged_template(_) => false,
            // JSX: indent
            ExpressionDesc::Pexp_jsx_element(_) => true,
            // Default: check attributes or array access or binary expression
            _ => {
                parsetree_viewer::has_attributes(arena, &vb_expr.pexp_attributes)
                    || parsetree_viewer::is_binary_expression(arena, vb_expr)
                    || parsetree_viewer::is_array_access(arena, vb_expr)
            }
        }
    };

    let rhs = if should_indent {
        Doc::indent(Doc::concat(vec![Doc::line(), printed_expr]))
    } else {
        Doc::concat(vec![Doc::space(), printed_expr])
    };

    Doc::group(Doc::concat(vec![
        attrs_doc,
        header,
        pat,
        equal_doc.clone(),
        rhs,
    ]))
}

// ============================================================================
// Attributes (placeholder)
// ============================================================================

/// Print attributes with a trailing separator.
/// When inline=true, uses space after attributes.
/// When inline=false (default), uses Doc::line which can break if needed.
fn print_attributes(
    state: &PrinterState,
    attrs: &[Attribute],
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    print_attributes_with_loc(state, attrs, None, cmt_tbl, arena, false)
}

/// Print attributes with location for proper line breaking.
/// If `loc` is provided and the attributed item starts on a different line
/// than the last attribute ends, uses hard_line instead of line.
/// Separates doc comments from regular attributes - doc comments go on their own line.
fn print_attributes_with_loc(
    state: &PrinterState,
    attrs: &[Attribute],
    loc: Option<Location>,
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
    inline: bool,
) -> Doc {
    // res_printer.ml:5994-5997: `Parsetree_viewer.filter_parsing_attrs`.
    let filtered: Vec<&Attribute> = parsetree_viewer::filter_parsing_attrs_slice(arena, attrs);
    if filtered.is_empty() {
        return Doc::nil();
    }

    // res_printer.ml:5999-6031
    let (comment_attrs, attrs): (Vec<&Attribute>, Vec<&Attribute>) = filtered
        .into_iter()
        .partition(|attr| parsetree_viewer::is_doc_comment_attribute(arena, attr));
    let line_break = match loc {
        None => Doc::line(),
        Some(loc) => match attrs.last() {
            Some((first_loc, _))
                if arena.loc_start(loc).line > arena.loc_end(first_loc.loc).line =>
            {
                Doc::hard_line()
            }
            _ => {
                if comment_attrs.is_empty() {
                    Doc::line()
                } else {
                    Doc::space()
                }
            }
        },
    };
    let doc_comment_doc = if comment_attrs.is_empty() {
        Doc::nil()
    } else {
        print_doc_comments(state, &comment_attrs, cmt_tbl, arena)
    };
    let attrs_doc = if attrs.is_empty() {
        Doc::nil()
    } else {
        Doc::concat(vec![
            Doc::group(join_attributes_with_sep(state, &attrs, cmt_tbl, arena)),
            if inline { Doc::space() } else { line_break },
        ])
    };
    Doc::concat(vec![doc_comment_doc, attrs_doc])
}

/// Print a single attribute.
/// If `standalone` is true, uses `@@` prefix (for floating attributes).
/// Otherwise uses `@` prefix.
fn print_attribute(
    state: &PrinterState,
    attr: &Attribute,
    standalone: bool,
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    let (name, payload) = attr;

    // Handle doc comments specially
    if arena.get_string(name.txt) == "res.doc" {
        if let Payload::PStr(items) = payload {
            if let [single] = &items[..] {
                if let StructureItemDesc::Pstr_eval(eval_inner) = &*single.pstr_desc {
                    let (ref expr_idx, _) = **eval_inner;
                    let expr = arena.get_expr(*expr_idx);
                    if let ExpressionDesc::Pexp_constant(c) = &*expr.pexp_desc {
                        if let Constant::String(payload) = &**c {
                            return Doc::concat(vec![
                                Doc::text(if standalone { "/***" } else { "/**" }),
                                Doc::text(payload.semantic()),
                                Doc::text("*/"),
                            ]);
                        }
                    }
                }
            }
        }
    }

    let prefix = if standalone { "@@" } else { "@" };
    let attr_name = Doc::text(format!("{}{}", prefix, arena.get_string(name.txt)));

    Doc::group(Doc::concat(vec![
        attr_name,
        print_payload(state, payload, cmt_tbl, arena),
    ]))
}

// ============================================================================
// Extension (placeholder)
// ============================================================================

/// Print an extension point.
fn print_extension(
    state: &PrinterState,
    ext: &Extension,
    at_module_lvl: bool,
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    let (name, payload) = ext;
    let ext_name = Doc::concat(vec![
        Doc::text("%"),
        if at_module_lvl {
            Doc::text("%")
        } else {
            Doc::nil()
        },
        Doc::text(arena.get_string(name.txt)),
    ]);
    let ext_name = print_comments(ext_name, cmt_tbl, name.loc, arena);
    Doc::group(Doc::concat(vec![
        ext_name,
        print_payload(state, payload, cmt_tbl, arena),
    ]))
}

/// Print a payload of an attribute or extension.
fn print_payload(
    state: &PrinterState,
    payload: &Payload,
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    match payload {
        Payload::PStr(items) if items.is_empty() => Doc::nil(),
        Payload::PStr(items) => {
            if let [single] = &items[..] {
                match &*single.pstr_desc {
                    StructureItemDesc::Pstr_eval(inner) => {
                        let (ref expr_idx, ref attrs) = **inner;
                        let expr = arena.get_expr(*expr_idx);
                        let expr_doc =
                            print_expression_with_comments_and_parens(state, expr, cmt_tbl, arena);
                        let needs_parens = !attrs.is_empty();
                        let should_hug = parsetree_viewer::is_huggable_expression(arena, expr);
                        if should_hug {
                            Doc::concat(vec![
                                Doc::lparen(),
                                print_attributes(state, attrs, cmt_tbl, arena),
                                if needs_parens {
                                    add_parens(expr_doc)
                                } else {
                                    expr_doc
                                },
                                Doc::rparen(),
                            ])
                        } else {
                            Doc::concat(vec![
                                Doc::lparen(),
                                Doc::indent(Doc::concat(vec![
                                    Doc::soft_line(),
                                    print_attributes(state, attrs, cmt_tbl, arena),
                                    if needs_parens {
                                        add_parens(expr_doc)
                                    } else {
                                        expr_doc
                                    },
                                ])),
                                Doc::soft_line(),
                                Doc::rparen(),
                            ])
                        }
                    }
                    StructureItemDesc::Pstr_value(inner) => {
                        let (_, _) = **inner;
                        // Single value binding - wrap in parens
                        add_parens(print_structure_item(state, single, cmt_tbl, arena))
                    }
                    _ => {
                        // General single structure item - wrap in parens
                        add_parens(print_structure_item(state, single, cmt_tbl, arena))
                    }
                }
            } else {
                // Multiple items - print full structure
                add_parens(print_structure(state, items, cmt_tbl, arena))
            }
        }
        Payload::PSig(signature) => Doc::concat(vec![
            Doc::lparen(),
            Doc::text(":"),
            Doc::indent(Doc::concat(vec![
                Doc::line(),
                print_signature(state, signature, cmt_tbl, arena),
            ])),
            Doc::soft_line(),
            Doc::rparen(),
        ]),
        Payload::PTyp(typ_idx) => Doc::concat(vec![
            Doc::text("(: "),
            print_typ_expr(state, arena.get_core_type(*typ_idx), cmt_tbl, arena),
            Doc::text(")"),
        ]),
        Payload::PPat(inner) => {
            let (ref pat_idx, ref guard) = **inner;
            let pat_doc = print_pattern(state, arena.get_pat(*pat_idx), cmt_tbl, arena);
            // OCaml: when_doc = Doc.line; Doc.text "if "; print_expression ...
            let guard_doc = match guard {
                Some(g) => Doc::concat(vec![
                    Doc::line(),
                    Doc::text("if "),
                    print_expression_with_comments_and_parens(
                        state,
                        arena.get_expr(*g),
                        cmt_tbl,
                        arena,
                    ),
                ]),
                None => Doc::nil(),
            };
            // OCaml wraps in indent with soft_line at start and end
            Doc::concat(vec![
                Doc::lparen(),
                Doc::indent(Doc::concat(vec![
                    Doc::soft_line(),
                    Doc::text("? "),
                    pat_doc,
                    guard_doc,
                ])),
                Doc::soft_line(),
                Doc::rparen(),
            ])
        }
    }
}

// ============================================================================
// Structure Printing
// ============================================================================

/// Print a structure (list of structure items).
pub fn print_structure(
    state: &PrinterState,
    structure: &[StructureItem],
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    if structure.is_empty() {
        return print_comments_inside_file(cmt_tbl, arena);
    }

    let mut sequential_state = state.clone();
    print_list(
        |item: &StructureItem| item.pstr_loc,
        structure,
        |item: &StructureItem, cmt_tbl: &mut CommentTable| {
            print_structure_item_sequential(&mut sequential_state, item, cmt_tbl, arena)
        },
        cmt_tbl,
        arena,
        false,
    )
}

/// Print a signature (list of signature items).
pub fn print_signature(
    state: &PrinterState,
    signature: &[SignatureItem],
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    if signature.is_empty() {
        return print_comments_inside_file(cmt_tbl, arena);
    }

    let mut sequential_state = state.clone();
    print_list(
        |item: &SignatureItem| item.psig_loc,
        signature,
        |item: &SignatureItem, cmt_tbl: &mut CommentTable| {
            print_signature_item_sequential(&mut sequential_state, item, cmt_tbl, arena)
        },
        cmt_tbl,
        arena,
        false,
    )
}

/// Print a signature item.
pub fn print_signature_item(
    state: &PrinterState,
    item: &SignatureItem,
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    let mut sequential_state = state.clone();
    print_signature_item_sequential(&mut sequential_state, item, cmt_tbl, arena)
}

fn print_signature_item_sequential(
    state: &mut PrinterState,
    item: &SignatureItem,
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    match &*item.psig_desc {
        SignatureItemDesc::Psig_value(_) | SignatureItemDesc::Psig_type(_) => {}
        SignatureItemDesc::Psig_typext(_)
        | SignatureItemDesc::Psig_exception(_)
        | SignatureItemDesc::Psig_module(_)
        | SignatureItemDesc::Psig_recmodule(_)
        | SignatureItemDesc::Psig_modtype(_)
        | SignatureItemDesc::Psig_open(_)
        | SignatureItemDesc::Psig_include(_)
        | SignatureItemDesc::Psig_attribute(_)
        | SignatureItemDesc::Psig_extension(_) => {
            state.clear_pending_inline_record_definitions();
        }
    }

    match &*item.psig_desc {
        SignatureItemDesc::Psig_value(val_desc) => {
            print_value_description(state, val_desc, cmt_tbl, arena)
        }

        SignatureItemDesc::Psig_type(inner) => {
            let (ref rec_flag, ref type_decls) = **inner;
            // Use print_type_declarations_with_rec_flag which handles everything
            // including the "type " prefix, using print_listi for proper comment handling
            print_type_declarations_with_rec_flag(state, rec_flag, type_decls, cmt_tbl, arena)
        }

        SignatureItemDesc::Psig_typext(type_ext) => {
            print_type_extension(state, type_ext, cmt_tbl, arena)
        }

        SignatureItemDesc::Psig_exception(ext_constr) => {
            print_exception_def(state, ext_constr, cmt_tbl, arena)
        }

        SignatureItemDesc::Psig_module(mod_decl) => {
            print_module_declaration(state, mod_decl, cmt_tbl, arena)
        }

        SignatureItemDesc::Psig_recmodule(mod_decls) => {
            print_rec_module_declarations(state, mod_decls, cmt_tbl, arena)
        }

        SignatureItemDesc::Psig_modtype(mod_type_decl) => {
            print_module_type_declaration(state, mod_type_decl, cmt_tbl, arena)
        }

        SignatureItemDesc::Psig_open(open_desc) => {
            print_open_description(state, open_desc, cmt_tbl, arena)
        }

        SignatureItemDesc::Psig_include(include_desc) => {
            print_include_description(state, include_desc, cmt_tbl, arena)
        }

        SignatureItemDesc::Psig_attribute(attr) => {
            print_attribute(state, attr, true, cmt_tbl, arena)
        }

        SignatureItemDesc::Psig_extension(inner) => {
            let (ref ext, ref attrs) = **inner;
            let attrs_doc = print_attributes(state, attrs, cmt_tbl, arena);
            Doc::concat(vec![
                attrs_doc,
                print_extension(state, ext, true, cmt_tbl, arena),
            ])
        }
    }
}

/// Print a module declaration.
fn print_module_declaration(
    state: &PrinterState,
    decl: &ModuleDeclaration,
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    let decl_mod_type = arena.get_mod_type(decl.pmd_type);
    let attrs_doc = print_attributes_with_loc(
        state,
        &decl.pmd_attributes,
        Some(decl.pmd_name.loc),
        cmt_tbl,
        arena,
        false,
    );
    let name_doc = Doc::text(arena.get_string(decl.pmd_name.txt));
    let name_doc = print_comments(name_doc, cmt_tbl, decl.pmd_name.loc, arena);

    // Check if this is a module alias (Pmty_alias) - uses "=" instead of ":"
    let body_doc = match &*decl_mod_type.pmty_desc {
        ModuleTypeDesc::Pmty_alias(lid) => Doc::concat(vec![
            Doc::text(" = "),
            print_longident(arena, arena.get_longident(lid.txt)),
        ]),
        _ => Doc::concat(vec![
            Doc::text(": "),
            print_module_type(state, decl_mod_type, cmt_tbl, arena),
        ]),
    };

    Doc::concat(vec![attrs_doc, Doc::text("module "), name_doc, body_doc])
}

/// Print recursive module declarations using print_listi for proper comment handling.
fn print_rec_module_declarations(
    state: &PrinterState,
    decls: &[ModuleDeclaration],
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    // Use print_listi to properly handle comments between declarations
    print_listi(
        |decl: &ModuleDeclaration| decl.pmd_loc,
        decls,
        |decl: &ModuleDeclaration, cmt_tbl: &mut CommentTable, i: usize| {
            let decl_mod_type = arena.get_mod_type(decl.pmd_type);
            let attrs_doc = print_attributes_with_loc(
                state,
                &decl.pmd_attributes,
                Some(decl.pmd_name.loc),
                cmt_tbl,
                arena,
                false,
            );
            let prefix = if i == 0 {
                Doc::text("module rec ")
            } else {
                Doc::text("and ")
            };
            let name_doc = Doc::text(arena.get_string(decl.pmd_name.txt));
            let name_doc = print_comments(name_doc, cmt_tbl, decl.pmd_name.loc, arena);

            // Handle alias vs regular module type
            let body_doc = match &*decl_mod_type.pmty_desc {
                ModuleTypeDesc::Pmty_alias(lid) => Doc::concat(vec![
                    Doc::text(" = "),
                    print_longident(arena, arena.get_longident(lid.txt)),
                ]),
                ModuleTypeDesc::Pmty_with(..) => {
                    // Needs parens for with constraints
                    Doc::concat(vec![
                        Doc::text(": "),
                        Doc::lparen(),
                        print_module_type(state, decl_mod_type, cmt_tbl, arena),
                        Doc::rparen(),
                    ])
                }
                _ => Doc::concat(vec![
                    Doc::text(": "),
                    print_module_type(state, decl_mod_type, cmt_tbl, arena),
                ]),
            };

            Doc::concat(vec![attrs_doc, prefix, name_doc, body_doc])
        },
        cmt_tbl,
        arena,
        false, // don't ignore empty lines
        false, // don't force break
    )
}

/// Print an include description.
fn print_include_description(
    state: &PrinterState,
    include_desc: &IncludeDescription,
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    let attrs_doc = print_attributes(state, &include_desc.pincl_attributes, cmt_tbl, arena);
    let mod_doc = print_module_type(
        state,
        arena.get_mod_type(include_desc.pincl_mod),
        cmt_tbl,
        arena,
    );

    Doc::concat(vec![attrs_doc, Doc::text("include "), mod_doc])
}

/// Print a structure item.
pub fn print_structure_item(
    state: &PrinterState,
    item: &StructureItem,
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    let mut sequential_state = state.clone();
    print_structure_item_sequential(&mut sequential_state, item, cmt_tbl, arena)
}

fn print_structure_item_sequential(
    state: &mut PrinterState,
    item: &StructureItem,
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    match &*item.pstr_desc {
        StructureItemDesc::Pstr_type(_) | StructureItemDesc::Pstr_primitive(_) => {}
        StructureItemDesc::Pstr_value(_)
        | StructureItemDesc::Pstr_typext(_)
        | StructureItemDesc::Pstr_exception(_)
        | StructureItemDesc::Pstr_module(_)
        | StructureItemDesc::Pstr_recmodule(_)
        | StructureItemDesc::Pstr_modtype(_)
        | StructureItemDesc::Pstr_open(_)
        | StructureItemDesc::Pstr_include(_)
        | StructureItemDesc::Pstr_attribute(_)
        | StructureItemDesc::Pstr_extension(_)
        | StructureItemDesc::Pstr_eval(_) => {
            state.clear_pending_inline_record_definitions();
        }
    }

    match &*item.pstr_desc {
        StructureItemDesc::Pstr_value(inner) => {
            let (ref rec_flag, ref bindings) = **inner;
            print_value_bindings(state, bindings, rec_flag, cmt_tbl, arena)
        }

        StructureItemDesc::Pstr_type(inner) => {
            let (ref rec_flag, ref type_decls) = **inner;
            // Use print_type_declarations_with_rec_flag which handles everything
            // including the "type " prefix, using print_listi for proper comment handling
            print_type_declarations_with_rec_flag(state, rec_flag, type_decls, cmt_tbl, arena)
        }

        StructureItemDesc::Pstr_primitive(val_desc) => {
            print_value_description(state, val_desc, cmt_tbl, arena)
        }

        StructureItemDesc::Pstr_typext(type_ext) => {
            print_type_extension(state, type_ext, cmt_tbl, arena)
        }

        StructureItemDesc::Pstr_exception(ext_constr) => {
            print_exception_def(state, ext_constr, cmt_tbl, arena)
        }

        StructureItemDesc::Pstr_module(mod_binding) => {
            print_module_binding(state, mod_binding, cmt_tbl, arena)
        }

        StructureItemDesc::Pstr_recmodule(mod_bindings) => {
            print_rec_module_bindings(state, mod_bindings, cmt_tbl, arena)
        }

        StructureItemDesc::Pstr_modtype(mod_type_decl) => {
            print_module_type_declaration(state, mod_type_decl, cmt_tbl, arena)
        }

        StructureItemDesc::Pstr_open(open_desc) => {
            print_open_description(state, open_desc, cmt_tbl, arena)
        }

        StructureItemDesc::Pstr_include(include_decl) => {
            print_include_declaration(state, include_decl, cmt_tbl, arena)
        }

        StructureItemDesc::Pstr_attribute(attr) => {
            print_attribute(state, attr, true, cmt_tbl, arena)
        }

        StructureItemDesc::Pstr_extension(inner) => {
            let (ref ext, ref attrs) = **inner;
            let attrs_doc = print_attributes(state, attrs, cmt_tbl, arena);
            Doc::concat(vec![
                attrs_doc,
                print_extension(state, ext, true, cmt_tbl, arena),
            ])
        }

        StructureItemDesc::Pstr_eval(inner) => {
            let (ref expr, ref attrs) = **inner;
            let expr = arena.get_expr(*expr);
            let attrs_doc = print_attributes(state, attrs, cmt_tbl, arena);
            let expr_doc = {
                let doc = print_expression_with_comments(state, expr, cmt_tbl, arena);
                match parens::structure_expr(arena, expr) {
                    parens::ParenKind::Parenthesized => add_parens(doc),
                    parens::ParenKind::Braced(loc) => print_braces(doc, expr, loc, arena),
                    parens::ParenKind::Nothing => doc,
                }
            };
            Doc::concat(vec![attrs_doc, expr_doc])
        }
    }
}

/// Check if any type declaration has the inline record definition attribute.
fn has_inline_type_definitions(decls: &[TypeDeclaration]) -> bool {
    decls
        .iter()
        .any(|decl| decl.ptype_origin == TypeDeclarationOrigin::Inline_record_definition)
}

fn inline_record_external_name<'a>(
    arena: &'a ParseArena,
    declaration: &TypeDeclaration,
) -> Option<&'a str> {
    arena
        .get_string(declaration.ptype_name.txt)
        .split_once('.')
        .map(|(external_name, _)| external_name)
}

fn pending_inline_record_definitions(
    arena: &ParseArena,
    definitions: &[TypeDeclaration],
) -> Option<PendingInlineRecordDefinitions> {
    let external_name = inline_record_external_name(arena, definitions.first()?)?.to_string();
    let all_definitions_match = definitions.iter().all(|declaration| {
        inline_record_external_name(arena, declaration) == Some(external_name.as_str())
    });
    if !all_definitions_match {
        return None;
    }

    Some(PendingInlineRecordDefinitions {
        external_name,
        definitions: definitions.to_vec(),
    })
}

/// Print type declarations.
/// Print type declarations with proper comment handling using print_listi.
/// This matches the OCaml implementation which uses print_listi for type declarations.
/// The rec_flag parameter is printed as part of the first declaration's prefix.
fn print_type_declarations_with_rec_flag(
    state: &mut PrinterState,
    rec_flag: &RecFlag,
    decls: &[TypeDeclaration],
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    // Check if we need to handle inline record definitions
    if has_inline_type_definitions(decls) {
        // Partition declarations into inline records and regular declarations
        let (inline_record_definitions, regular_declarations): (Vec<_>, Vec<_>) = decls
            .iter()
            .cloned()
            .partition(|decl| decl.ptype_origin == TypeDeclarationOrigin::Inline_record_definition);

        if regular_declarations.is_empty() {
            if let Some(pending) =
                pending_inline_record_definitions(arena, &inline_record_definitions)
            {
                state.pending_inline_record_definitions = Some(pending);
                return Doc::nil();
            }
        }

        state.pending_inline_record_definitions = None;

        // Adjust rec flag: only add "rec" if more than 1 regular declaration
        let adjusted_rec_doc = match rec_flag {
            RecFlag::Recursive => {
                if regular_declarations.len() > 1 {
                    Doc::text("rec ")
                } else {
                    Doc::nil()
                }
            }
            RecFlag::Nonrecursive => Doc::nil(),
        };

        // Create state with inline record definitions
        let state_with_inline = state.with_inline_record_definitions(inline_record_definitions);

        // Print only regular declarations, but with inline records available for substitution
        print_listi(
            |decl: &TypeDeclaration| decl.ptype_loc,
            &regular_declarations,
            |decl: &TypeDeclaration, cmt_tbl: &mut CommentTable, i: usize| {
                let prefix = if i > 0 {
                    Doc::text("and ")
                } else {
                    Doc::concat(vec![Doc::text("type "), adjusted_rec_doc.clone()])
                };
                let attrs = print_attributes_with_loc(
                    &state_with_inline,
                    &decl.ptype_attributes,
                    Some(decl.ptype_loc),
                    cmt_tbl,
                    arena,
                    false,
                );
                Doc::group(Doc::concat(vec![
                    attrs,
                    prefix,
                    print_type_declaration_inner(&state_with_inline, decl, cmt_tbl, arena, false),
                ]))
            },
            cmt_tbl,
            arena,
            false,
            false,
        )
    } else {
        state.pending_inline_record_definitions = None;
        // No inline record definitions, print normally
        let rec_doc = match rec_flag {
            RecFlag::Nonrecursive => Doc::nil(),
            RecFlag::Recursive => Doc::text("rec "),
        };

        // Use print_listi to properly handle comments between declarations
        // The "type " keyword is included in the first element's prefix,
        // so print_listi's print_comments wraps the entire declaration correctly.
        print_listi(
            |decl: &TypeDeclaration| decl.ptype_loc,
            decls,
            |decl: &TypeDeclaration, cmt_tbl: &mut CommentTable, i: usize| {
                // Match OCaml's print_type_declaration2 prefix logic:
                // if i > 0 then "and " else "type " ^ rec_flag
                let prefix = if i > 0 {
                    Doc::text("and ")
                } else {
                    Doc::concat(vec![Doc::text("type "), rec_doc.clone()])
                };
                // Print attributes + prefix + name + params + manifest + kind + constraints
                let attrs = print_attributes_with_loc(
                    state,
                    &decl.ptype_attributes,
                    Some(decl.ptype_loc),
                    cmt_tbl,
                    arena,
                    false,
                );
                Doc::group(Doc::concat(vec![
                    attrs,
                    prefix,
                    print_type_declaration_inner(state, decl, cmt_tbl, arena, false),
                ]))
            },
            cmt_tbl,
            arena,
            false, // don't ignore empty lines
            false, // don't force break
        )
    }
}

/// Print a type declaration with optional attributes.
fn print_type_declaration_inner(
    state: &PrinterState,
    decl: &TypeDeclaration,
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
    include_attrs: bool,
) -> Doc {
    // Use type declaration location for proper attribute line breaking
    let attrs_doc = if include_attrs {
        print_attributes_with_loc(
            state,
            &decl.ptype_attributes,
            Some(decl.ptype_loc),
            cmt_tbl,
            arena,
            false,
        )
    } else {
        Doc::nil()
    };
    let name_doc = print_ident_like(arena.get_string(decl.ptype_name.txt), false, false);
    let name_doc = print_comments(name_doc, cmt_tbl, decl.ptype_name.loc, arena);

    let params_doc = if decl.ptype_params.is_empty() {
        Doc::nil()
    } else {
        let params: Vec<Doc> = decl
            .ptype_params
            .iter()
            .map(|(typ, variance)| print_type_param(state, typ, variance, cmt_tbl, arena))
            .collect();
        Doc::group(Doc::concat(vec![
            Doc::less_than(),
            Doc::indent(Doc::concat(vec![
                Doc::soft_line(),
                Doc::join(Doc::concat(vec![Doc::text(","), Doc::line()]), params),
            ])),
            Doc::trailing_comma(),
            Doc::soft_line(),
            Doc::greater_than(),
        ]))
    };

    // Helper for private flag
    let private_doc = match decl.ptype_private {
        PrivateFlag::Private => Doc::text("private "),
        PrivateFlag::Public => Doc::nil(),
    };

    // For abstract types: " = private? <manifest type>"
    // For non-abstract types: manifest is handled separately
    let manifest_doc = match &decl.ptype_kind {
        TypeKind::Ptype_abstract => match &decl.ptype_manifest {
            Some(typ) => Doc::concat(vec![
                Doc::text(" = "),
                private_doc.clone(),
                print_typ_expr(state, arena.get_core_type(*typ), cmt_tbl, arena),
            ]),
            None => Doc::nil(),
        },
        TypeKind::Ptype_variant(_) => {
            // Manifest (if any) is printed without private flag
            match &decl.ptype_manifest {
                Some(typ) => Doc::concat(vec![
                    Doc::text(" = "),
                    print_typ_expr(state, arena.get_core_type(*typ), cmt_tbl, arena),
                ]),
                None => Doc::nil(),
            }
        }
        TypeKind::Ptype_record(_) => {
            // Manifest (if any) is printed without private flag
            match &decl.ptype_manifest {
                Some(typ) => Doc::concat(vec![
                    Doc::text(" = "),
                    print_typ_expr(state, arena.get_core_type(*typ), cmt_tbl, arena),
                ]),
                None => Doc::nil(),
            }
        }
        TypeKind::Ptype_open => Doc::nil(),
    };

    let kind_doc = match &decl.ptype_kind {
        TypeKind::Ptype_abstract => Doc::nil(),
        TypeKind::Ptype_variant(constrs) => {
            Doc::concat(vec![
                // No trailing space - print_constructor_declarations starts with Doc::line()
                Doc::text(" ="),
                print_constructor_declarations(state, constrs, &decl.ptype_private, cmt_tbl, arena),
            ])
        }
        TypeKind::Ptype_record(fields) => {
            // OCaml: special case for empty record with only comments inside
            if fields.is_empty() {
                Doc::concat(vec![
                    Doc::text(" = "),
                    private_doc.clone(),
                    Doc::lbrace(),
                    print_comments_inside(cmt_tbl, decl.ptype_loc, arena),
                    Doc::rbrace(),
                ])
            } else {
                Doc::concat(vec![
                    Doc::text(" = "),
                    private_doc.clone(),
                    print_record_declaration(state, fields, Some(decl.ptype_loc), cmt_tbl, arena),
                ])
            }
        }
        TypeKind::Ptype_open => Doc::concat(vec![Doc::text(" = "), private_doc, Doc::text("..")]),
    };

    // Print type constraints (constraint 'a = int)
    let constraints_doc = print_type_constraints(state, &decl.ptype_cstrs, cmt_tbl, arena);

    Doc::concat(vec![
        attrs_doc,
        name_doc,
        params_doc,
        manifest_doc,
        kind_doc,
        constraints_doc,
    ])
}

/// Print type definition constraints.
fn print_type_constraints(
    state: &PrinterState,
    constraints: &[(CoreTypeIdx, CoreTypeIdx, Location)],
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    if constraints.is_empty() {
        return Doc::nil();
    }
    let constraint_docs: Vec<Doc> = constraints
        .iter()
        .map(|(typ1, typ2, _loc)| {
            Doc::concat(vec![
                Doc::text("constraint "),
                print_typ_expr(state, arena.get_core_type(*typ1), cmt_tbl, arena),
                Doc::text(" = "),
                print_typ_expr(state, arena.get_core_type(*typ2), cmt_tbl, arena),
            ])
        })
        .collect();
    Doc::indent(Doc::group(Doc::concat(vec![
        Doc::line(),
        Doc::group(Doc::join(Doc::line(), constraint_docs)),
    ])))
}

/// Print constructor declarations.
/// Print constructor declarations using print_listi for proper comment handling.
fn print_constructor_declarations(
    state: &PrinterState,
    constrs: &[ConstructorDeclaration],
    private_flag: &PrivateFlag,
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    // Check if constructors span multiple lines (force_break)
    let force_break = match (constrs.first(), constrs.last()) {
        (Some(first), Some(last)) => {
            arena.loc_start(first.pcd_loc).line < arena.loc_end(last.pcd_loc).line
        }
        _ => false,
    };

    let private_doc = match private_flag {
        PrivateFlag::Private => Doc::concat(vec![Doc::text("private"), Doc::line()]),
        PrivateFlag::Public => Doc::nil(),
    };

    // Use print_listi for proper comment handling between constructors
    let rows = print_listi(
        |constr: &ConstructorDeclaration| constr.pcd_loc,
        constrs,
        |constr: &ConstructorDeclaration, cmt_tbl: &mut CommentTable, i: usize| {
            let doc = print_constructor_declaration2(state, i, constr, cmt_tbl, arena);
            print_comments(doc, cmt_tbl, constr.pcd_loc, arena)
        },
        cmt_tbl,
        arena,
        true, // ignore_empty_lines (OCaml passes this as true for constructors)
        force_break,
    );

    Doc::breakable_group(
        Doc::indent(Doc::concat(vec![Doc::line(), private_doc, rows])),
        force_break,
    )
}

/// res_printer.ml:1761-1806 print_constructor_declaration2.
fn print_constructor_declaration2(
    state: &PrinterState,
    i: usize,
    cd: &ConstructorDeclaration,
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    let all_attrs = crate::ast_helper_type::constructor_attributes(arena, cd);
    let (comment_attrs, attrs) =
        parsetree_viewer::partition_doc_comment_attributes(arena, &all_attrs);
    let comment_doc = if comment_attrs.is_empty() {
        Doc::nil()
    } else {
        print_doc_comments_with_sep(state, &comment_attrs, cmt_tbl, arena, Doc::hard_line())
    };
    let attrs: Vec<Attribute> = attrs.into_iter().cloned().collect();
    let attrs = print_attributes(state, &attrs, cmt_tbl, arena);
    let is_dot_dot_dot = arena.get_string(cd.pcd_name.txt) == "...";
    let bar = if i > 0 || !all_attrs.is_empty() || is_dot_dot_dot {
        Doc::text("| ")
    } else {
        Doc::if_breaks(Doc::text("| "), Doc::nil())
    };
    let constr_name = print_comments(
        Doc::text(arena.get_string(cd.pcd_name.txt)),
        cmt_tbl,
        cd.pcd_name.loc,
        arena,
    );
    let constr_args =
        print_constructor_arguments(state, &cd.pcd_args, is_dot_dot_dot, true, cmt_tbl, arena);
    let gadt = match &cd.pcd_res {
        None => Doc::nil(),
        Some(typ) => Doc::indent(Doc::concat(vec![
            Doc::text(": "),
            print_typ_expr(state, arena.get_core_type(*typ), cmt_tbl, arena),
        ])),
    };
    Doc::concat(vec![
        comment_doc,
        bar,
        Doc::group(Doc::concat(vec![attrs, constr_name, constr_args, gadt])),
    ])
}

/// Print record declaration.
fn print_record_declaration(
    state: &PrinterState,
    fields: &[LabelDeclaration],
    record_loc: Option<LocIdx>,
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    // Calculate force_break: if the opening brace and first field are on different lines
    let force_break = match (record_loc, fields.first()) {
        (Some(loc), Some(first_field)) => {
            // For spread fields (...), use the type location instead
            let field_line = if arena.get_string(first_field.pld_name.txt) == "..." {
                arena
                    .loc_start(arena.get_core_type(first_field.pld_type).ptyp_loc)
                    .line
            } else {
                arena.loc_start(first_field.pld_loc).line
            };
            arena.loc_start(loc).line < field_line
        }
        _ => false,
    };

    let field_docs: Vec<Doc> = fields
        .iter()
        .map(|field| {
            let doc = print_label_declaration(state, field, cmt_tbl, arena);
            // Wrap with print_comments for field location (like OCaml)
            print_comments(doc, cmt_tbl, field.pld_loc, arena)
        })
        .collect();
    Doc::breakable_group(
        Doc::concat(vec![
            Doc::lbrace(),
            Doc::indent(Doc::concat(vec![
                Doc::soft_line(),
                Doc::join(Doc::concat(vec![Doc::text(","), Doc::line()]), field_docs),
            ])),
            Doc::trailing_comma(),
            Doc::soft_line(),
            Doc::rbrace(),
        ]),
        force_break,
    )
}

/// Print record declaration when inline record definitions are available.
/// This is used when printing type constructors that reference inline record definitions.
/// The state already contains the inline_record_definitions, so this is just an alias.
fn print_record_declaration_with_inline_records(
    state: &PrinterState,
    fields: &[LabelDeclaration],
    record_loc: Option<LocIdx>,
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    print_record_declaration(state, fields, record_loc, cmt_tbl, arena)
}

/// Print a label declaration (record field).
fn print_label_declaration(
    state: &PrinterState,
    field: &LabelDeclaration,
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    // res_printer.ml:1860-1887: spread fields (`...t`) share the label path,
    // so their attributes are printed too.
    let is_dot = arena.get_string(field.pld_name.txt) == "...";
    // Pass field name location for proper attribute line breaking
    // The runtime name is held as a field rather than an attribute, so put
    // its surface syntax back (res_printer.ml `print_label_declaration`).
    let written_attrs = crate::ast_helper_type::field_attributes(arena, field);
    let attrs_doc = print_attributes_with_loc(
        state,
        &written_attrs,
        Some(field.pld_name.loc),
        cmt_tbl,
        arena,
        false,
    );
    let mutable_doc = if field.pld_mutable == MutableFlag::Mutable {
        Doc::text("mutable ")
    } else {
        Doc::nil()
    };
    let name_doc = if is_dot {
        Doc::text("...")
    } else {
        print_ident_like(arena.get_string(field.pld_name.txt), false, false)
    };
    let name_doc = print_comments(name_doc, cmt_tbl, field.pld_name.loc, arena);
    let optional_doc = if field.pld_optional {
        Doc::text("?")
    } else {
        Doc::nil()
    };
    let typ_doc = print_typ_expr(state, arena.get_core_type(field.pld_type), cmt_tbl, arena);

    Doc::group(Doc::concat(vec![
        attrs_doc,
        mutable_doc,
        name_doc,
        optional_doc,
        if is_dot { Doc::nil() } else { Doc::text(": ") },
        typ_doc,
    ]))
}

/// Print constructor arguments (tuple or record).
/// Matches OCaml's print_constructor_arguments.
fn print_constructor_arguments(
    state: &PrinterState,
    args: &ConstructorArguments,
    is_dot_dot_dot: bool,
    indent: bool,
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    match args {
        ConstructorArguments::Pcstr_tuple(types) if types.is_empty() => Doc::nil(),
        ConstructorArguments::Pcstr_tuple(types) => {
            let type_docs: Vec<Doc> = types
                .iter()
                .map(|t| print_typ_expr(state, arena.get_core_type(*t), cmt_tbl, arena))
                .collect();
            let inner = Doc::concat(vec![
                if is_dot_dot_dot {
                    Doc::nil()
                } else {
                    Doc::lparen()
                },
                Doc::indent(Doc::concat(vec![
                    Doc::soft_line(),
                    Doc::join(Doc::concat(vec![Doc::text(","), Doc::line()]), type_docs),
                ])),
                Doc::trailing_comma(),
                Doc::soft_line(),
                if is_dot_dot_dot {
                    Doc::nil()
                } else {
                    Doc::rparen()
                },
            ]);
            let result = Doc::group(if indent { Doc::indent(inner) } else { inner });
            result
        }
        ConstructorArguments::Pcstr_record(fields) => {
            // Manually inline the printRecordDeclaration, gives better layout
            let field_docs: Vec<Doc> = fields
                .iter()
                .map(|ld| {
                    let doc = print_label_declaration(state, ld, cmt_tbl, arena);
                    print_comments(doc, cmt_tbl, ld.pld_loc, arena)
                })
                .collect();
            let inner = Doc::concat(vec![
                Doc::lparen(),
                Doc::lbrace(),
                Doc::indent(Doc::concat(vec![
                    Doc::soft_line(),
                    Doc::join(Doc::concat(vec![Doc::text(","), Doc::line()]), field_docs),
                ])),
                Doc::trailing_comma(),
                Doc::soft_line(),
                Doc::rbrace(),
                Doc::rparen(),
            ]);
            Doc::group(if indent { Doc::indent(inner) } else { inner })
        }
    }
}

/// Print value description (external or let declaration in signatures).
fn print_value_description(
    state: &mut PrinterState,
    val_desc: &ValueDescription,
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    let is_external = val_desc.pval_prim.is_some();
    // Use value name location for proper attribute line breaking
    let attrs_doc = print_attributes_with_loc(
        state,
        &val_desc.pval_attributes,
        Some(val_desc.pval_name.loc),
        cmt_tbl,
        arena,
        false,
    );
    let name_doc = print_ident_like(arena.get_string(val_desc.pval_name.txt), false, false);
    let name_doc = print_comments(name_doc, cmt_tbl, val_desc.pval_name.loc, arena);

    let pending_inline_record_definitions = state.pending_inline_record_definitions.take();
    let inline_record_definitions = match pending_inline_record_definitions {
        Some(pending)
            if is_external && pending.external_name == arena.get_string(val_desc.pval_name.txt) =>
        {
            Some(pending.definitions)
        }
        Some(_) | None => None,
    };
    let state_with_inline = inline_record_definitions
        .map(|definitions| state.with_inline_record_definitions(definitions));
    let type_state = state_with_inline.as_ref().unwrap_or(state);
    let typ_doc = print_typ_expr(
        type_state,
        arena.get_core_type(val_desc.pval_type),
        cmt_tbl,
        arena,
    );
    let header = if is_external { "external " } else { "let " };

    let prim_doc = if is_external {
        // res_printer.ml:1266-1273.
        let s = match &val_desc.pval_prim {
            Some(PrimitiveRepr::PrimName(s)) => arena.get_string(*s),
            Some(PrimitiveRepr::PrimFfi { name, .. }) => name.as_str(),
            Some(PrimitiveRepr::PrimInlineConst(_)) | None => "",
        };
        Doc::group(Doc::concat(vec![
            Doc::text(" ="),
            Doc::indent(Doc::concat(vec![
                Doc::line(),
                Doc::concat(vec![Doc::text("\""), Doc::text(s), Doc::text("\"")]),
            ])),
        ]))
    } else {
        Doc::nil()
    };

    Doc::group(Doc::concat(vec![
        attrs_doc,
        Doc::text(header),
        name_doc,
        Doc::text(": "),
        typ_doc,
        prim_doc,
    ]))
}

/// Print type extension.
fn print_type_extension(
    state: &PrinterState,
    type_ext: &TypeExtension,
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    // Pass path location for proper attribute line breaking:
    // @attr\ntype t += ... should preserve the line break
    let attrs_doc = print_attributes_with_loc(
        state,
        &type_ext.ptyext_attributes,
        Some(type_ext.ptyext_path.loc),
        cmt_tbl,
        arena,
        false,
    );
    let path_doc = print_lident_path(&type_ext.ptyext_path, cmt_tbl, arena);

    let params_doc = if type_ext.ptyext_params.is_empty() {
        Doc::nil()
    } else {
        let params: Vec<Doc> = type_ext
            .ptyext_params
            .iter()
            .map(|(typ, variance)| print_type_param(state, typ, variance, cmt_tbl, arena))
            .collect();
        Doc::group(Doc::concat(vec![
            Doc::less_than(),
            Doc::indent(Doc::concat(vec![
                Doc::soft_line(),
                Doc::join(Doc::concat(vec![Doc::text(","), Doc::line()]), params),
            ])),
            Doc::trailing_comma(),
            Doc::soft_line(),
            Doc::greater_than(),
        ]))
    };

    let ecs = &type_ext.ptyext_constructors;
    // Determine if we should force a break based on locations
    let force_break = if let (Some(first), Some(last)) = (ecs.first(), ecs.last()) {
        let path_end = arena.loc_end(type_ext.ptyext_path.loc);
        let first_start = arena.loc_start(first.pext_loc);
        let last_end = arena.loc_end(last.pext_loc);
        first_start.line > path_end.line || first_start.line < last_end.line
    } else {
        false
    };

    let private_doc = match type_ext.ptyext_private {
        PrivateFlag::Private => Doc::concat(vec![Doc::text("private"), Doc::line()]),
        PrivateFlag::Public => Doc::nil(),
    };

    let constructors_doc = print_listi(
        |constr: &ExtensionConstructor| constr.pext_loc,
        ecs,
        |constr, cmt_tbl_inner, i| {
            print_extension_constructor(state, constr, i, cmt_tbl_inner, arena)
        },
        cmt_tbl,
        arena,
        false, // ignore_empty_lines
        force_break,
    );

    Doc::group(Doc::concat(vec![
        attrs_doc,
        Doc::text("type "),
        path_doc,
        params_doc,
        Doc::text(" +="),
        Doc::breakable_group(
            Doc::indent(Doc::concat(vec![
                Doc::line(),
                private_doc,
                constructors_doc,
            ])),
            force_break,
        ),
    ]))
}

/// Print extension constructor.
fn print_extension_constructor(
    state: &PrinterState,
    ext_constr: &ExtensionConstructor,
    index: usize,
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    let attrs_doc = print_attributes(state, &ext_constr.pext_attributes, cmt_tbl, arena);
    let name_doc = print_comments(
        Doc::text(arena.get_string(ext_constr.pext_name.txt)),
        cmt_tbl,
        ext_constr.pext_name.loc,
        arena,
    );

    // First constructor uses if_breaks, others always show |
    let bar = if index > 0 {
        Doc::text("| ")
    } else {
        Doc::if_breaks(Doc::text("| "), Doc::nil())
    };

    let kind_doc = match &ext_constr.pext_kind {
        ExtensionConstructorKind::Pext_decl(args, res) => {
            let gadt_doc = match res {
                Some(typ) => Doc::concat(vec![
                    Doc::text(": "),
                    print_typ_expr(state, arena.get_core_type(*typ), cmt_tbl, arena),
                ]),
                None => Doc::nil(),
            };
            Doc::concat(vec![
                print_constructor_arguments(state, args, false, false, cmt_tbl, arena),
                gadt_doc,
            ])
        }
        ExtensionConstructorKind::Pext_rebind(lid) => Doc::indent(Doc::concat(vec![
            Doc::text(" ="),
            Doc::line(),
            print_longident_location(&lid, cmt_tbl, arena),
        ])),
    };

    Doc::concat(vec![
        bar,
        Doc::group(Doc::concat(vec![attrs_doc, name_doc, kind_doc])),
    ])
}

/// Print exception definition (for exception declarations in signatures and structures).
fn print_exception_def(
    state: &PrinterState,
    ext_constr: &ExtensionConstructor,
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    let attrs_doc = print_attributes(state, &ext_constr.pext_attributes, cmt_tbl, arena);
    let name_doc = {
        let doc = Doc::text(arena.get_string(ext_constr.pext_name.txt));
        print_comments(doc, cmt_tbl, ext_constr.pext_name.loc, arena)
    };

    let kind_doc = match &ext_constr.pext_kind {
        ExtensionConstructorKind::Pext_decl(args, res) => {
            let gadt_doc = match res {
                Some(typ) => Doc::concat(vec![
                    Doc::text(": "),
                    print_typ_expr(state, arena.get_core_type(*typ), cmt_tbl, arena),
                ]),
                None => Doc::nil(),
            };
            Doc::concat(vec![
                print_constructor_arguments(state, args, false, false, cmt_tbl, arena),
                gadt_doc,
            ])
        }
        ExtensionConstructorKind::Pext_rebind(lid) => Doc::indent(Doc::concat(vec![
            Doc::text(" ="),
            Doc::line(),
            print_longident_location(lid, cmt_tbl, arena),
        ])),
    };

    let doc = Doc::group(Doc::concat(vec![
        attrs_doc,
        Doc::text("exception "),
        name_doc,
        kind_doc,
    ]));
    print_comments(doc, cmt_tbl, ext_constr.pext_loc, arena)
}

/// Print module binding.
fn print_module_binding(
    state: &PrinterState,
    binding: &ModuleBinding,
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    let binding_expr = arena.get_mod_expr(binding.pmb_expr);
    let attrs_doc = print_attributes_with_loc(
        state,
        &binding.pmb_attributes,
        Some(binding.pmb_name.loc),
        cmt_tbl,
        arena,
        false,
    );

    // Wrap module name with print_comments for its location (like OCaml reference)
    let name_doc = Doc::text(arena.get_string(binding.pmb_name.txt));
    let name_doc = print_comments(name_doc, cmt_tbl, binding.pmb_name.loc, arena);

    // Handle Pmod_constraint specially - print constraint before equals sign (like OCaml)
    // module X: Int = Y  vs  module X = Y: Int
    let (expr_doc, constraint_doc) = match &*binding_expr.pmod_desc {
        ModuleExprDesc::Pmod_constraint(mod_expr_idx, mod_type_idx)
            if !parsetree_viewer::has_await_attribute(arena, &binding_expr.pmod_attributes) =>
        {
            let expr_doc = print_mod_expr(state, arena.get_mod_expr(*mod_expr_idx), cmt_tbl, arena);
            // Wrap in parens based on the outer binding expr (not inner)
            let expr_doc = if parens::mod_expr_parens(arena, binding_expr) {
                Doc::concat(vec![Doc::lparen(), expr_doc, Doc::rparen()])
            } else {
                expr_doc
            };
            let constraint_doc = Doc::concat(vec![
                Doc::text(": "),
                print_module_type(state, arena.get_mod_type(*mod_type_idx), cmt_tbl, arena),
            ]);
            (expr_doc, constraint_doc)
        }
        _ => {
            let expr_doc = print_mod_expr(state, binding_expr, cmt_tbl, arena);
            (expr_doc, Doc::nil())
        }
    };

    let doc = Doc::concat(vec![
        attrs_doc,
        Doc::text("module "),
        name_doc,
        constraint_doc,
        Doc::text(" = "),
        expr_doc,
    ]);

    // Wrap entire result with print_comments for binding location (like OCaml reference)
    print_comments(doc, cmt_tbl, binding.pmb_loc, arena)
}

/// Print recursive module bindings using print_listi for proper comment handling.
fn print_rec_module_bindings(
    state: &PrinterState,
    bindings: &[ModuleBinding],
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    // Use print_listi to properly handle comments between bindings
    print_listi(
        |binding: &ModuleBinding| binding.pmb_loc,
        bindings,
        |binding: &ModuleBinding, cmt_tbl: &mut CommentTable, i: usize| {
            let binding_expr = arena.get_mod_expr(binding.pmb_expr);
            let attrs_doc = print_attributes_with_loc(
                state,
                &binding.pmb_attributes,
                Some(binding.pmb_name.loc),
                cmt_tbl,
                arena,
                false,
            );
            let prefix = if i == 0 {
                Doc::text("module rec ")
            } else {
                Doc::text("and ")
            };
            // Wrap module name with print_comments for its location
            let name_doc = Doc::text(arena.get_string(binding.pmb_name.txt));
            let name_doc = print_comments(name_doc, cmt_tbl, binding.pmb_name.loc, arena);

            // Handle Pmod_constraint specially - print constraint before equals sign (like OCaml)
            // module rec X: Int = Y  vs  module rec X = Y: Int
            let (expr_doc, constraint_doc) = match &*binding_expr.pmod_desc {
                ModuleExprDesc::Pmod_constraint(mod_expr_idx, mod_type_idx)
                    if !parsetree_viewer::has_await_attribute(
                        arena,
                        &binding_expr.pmod_attributes,
                    ) =>
                {
                    let expr_doc =
                        print_mod_expr(state, arena.get_mod_expr(*mod_expr_idx), cmt_tbl, arena);
                    // Wrap in parens based on the outer binding expr (not inner)
                    let expr_doc = if parens::mod_expr_parens(arena, binding_expr) {
                        Doc::concat(vec![Doc::lparen(), expr_doc, Doc::rparen()])
                    } else {
                        expr_doc
                    };
                    let constraint_doc = Doc::concat(vec![
                        Doc::text(": "),
                        print_module_type(state, arena.get_mod_type(*mod_type_idx), cmt_tbl, arena),
                    ]);
                    (expr_doc, constraint_doc)
                }
                _ => {
                    let expr_doc = print_mod_expr(state, binding_expr, cmt_tbl, arena);
                    (expr_doc, Doc::nil())
                }
            };

            Doc::concat(vec![
                attrs_doc,
                prefix,
                name_doc,
                constraint_doc,
                Doc::text(" = "),
                expr_doc,
            ])
        },
        cmt_tbl,
        arena,
        false, // don't ignore empty lines
        false, // don't force break
    )
}

/// Print module type declaration.
fn print_module_type_declaration(
    state: &PrinterState,
    decl: &ModuleTypeDeclaration,
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    let attrs_doc = print_attributes(state, &decl.pmtd_attributes, cmt_tbl, arena);
    // Wrap module type name with print_comments for its location (like OCaml reference)
    let name_doc = Doc::text(arena.get_string(decl.pmtd_name.txt));
    let name_doc = print_comments(name_doc, cmt_tbl, decl.pmtd_name.loc, arena);
    let typ_doc = match &decl.pmtd_type {
        Some(mty) => Doc::concat(vec![
            Doc::text(" = "),
            print_module_type(state, arena.get_mod_type(*mty), cmt_tbl, arena),
        ]),
        None => Doc::nil(),
    };

    Doc::concat(vec![
        attrs_doc,
        Doc::text("module type "),
        name_doc,
        typ_doc,
    ])
}

/// Print open description.
fn print_open_description(
    _state: &PrinterState,
    open_desc: &OpenDescription,
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    let attrs_doc = print_attributes(_state, &open_desc.popen_attributes, cmt_tbl, arena);
    let lid_doc = print_longident(arena, arena.get_longident(open_desc.popen_lid.txt));
    let lid_doc_with_comments = print_comments(lid_doc, cmt_tbl, open_desc.popen_lid.loc, arena);
    let override_doc = match open_desc.popen_override {
        OverrideFlag::Fresh => Doc::space(),
        OverrideFlag::Override => Doc::text("! "),
    };

    Doc::concat(vec![
        attrs_doc,
        Doc::text("open"),
        override_doc,
        lid_doc_with_comments,
    ])
}

/// Print include declaration.
fn print_include_declaration(
    state: &PrinterState,
    include_decl: &IncludeDeclaration,
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    let attrs_doc = print_attributes(state, &include_decl.pincl_attributes, cmt_tbl, arena);
    let include_mod = arena.get_mod_expr(include_decl.pincl_mod);

    // Special case: include Ident({single type alias})
    // Try to keep on one line if it fits
    let mod_doc = if let ModuleExprDesc::Pmod_apply(_, _) = &*include_mod.pmod_desc {
        let (args, call_expr) = parsetree_viewer::mod_expr_apply(arena, include_mod);

        // Check if callee is an ident and single arg is structure with single type alias
        if args.len() == 1 && matches!(&*call_expr.pmod_desc, ModuleExprDesc::Pmod_ident(_)) {
            if let ModuleExprDesc::Pmod_structure(items) = &*args[0].pmod_desc {
                if items.len() == 1 {
                    if let StructureItemDesc::Pstr_type(type_inner) = &*items[0].pstr_desc {
                        let (_, ref decls) = **type_inner;
                        if decls.len() == 1
                            && matches!(decls[0].ptype_kind, TypeKind::Ptype_abstract)
                            && decls[0].ptype_manifest.is_some()
                        {
                            // This is the special case - use force_break:false
                            return Doc::concat(vec![
                                attrs_doc,
                                Doc::text("include "),
                                print_mod_expr(state, call_expr, cmt_tbl, arena),
                                Doc::lparen(),
                                Doc::breakable_group(
                                    Doc::concat(vec![
                                        Doc::lbrace(),
                                        Doc::indent(Doc::concat(vec![
                                            Doc::soft_line(),
                                            print_structure_item(state, &items[0], cmt_tbl, arena),
                                        ])),
                                        Doc::soft_line(),
                                        Doc::rbrace(),
                                    ]),
                                    false, // force_break = false
                                ),
                                Doc::rparen(),
                            ]);
                        }
                    }
                }
            }
        }
        // Not the special case, use normal printing
        print_mod_expr(state, include_mod, cmt_tbl, arena)
    } else {
        print_mod_expr(state, include_mod, cmt_tbl, arena)
    };

    let include_doc = if parens::include_mod_expr(include_mod) {
        add_parens(mod_doc)
    } else {
        mod_doc
    };

    Doc::concat(vec![attrs_doc, Doc::text("include "), include_doc])
}

// ============================================================================
// Main Entry Points
// ============================================================================

/// Default print width.
pub const DEFAULT_PRINT_WIDTH: i32 = 100;

/// Print a structure with comments to a string.
pub fn print_implementation(
    structure: &[StructureItem],
    comments: Vec<Comment>,
    width: i32,
    arena: &mut ParseArena,
) -> String {
    let mut cmt_tbl = CommentTable::new();
    walk_structure(structure, &mut cmt_tbl, comments, arena);
    let state = PrinterState::init();
    let doc = print_structure(&state, structure, &mut cmt_tbl, arena);
    // res_printer.ml:6443-6456: `Doc.to_string ~width doc ^ "\n"`, also
    // for an empty file.
    format!("{}\n", doc.to_string(width))
}

/// Print a structure with comments using default width.
pub fn print_structure_with_comments(
    structure: &[StructureItem],
    comments: Vec<Comment>,
    arena: &mut ParseArena,
) -> String {
    print_implementation(structure, comments, DEFAULT_PRINT_WIDTH, arena)
}

/// Print a signature/interface to a string.
pub fn print_interface(
    signature: &[SignatureItem],
    comments: Vec<Comment>,
    width: i32,
    arena: &mut ParseArena,
) -> String {
    let mut cmt_tbl = CommentTable::new();
    walk_signature(signature, &mut cmt_tbl, comments, arena);
    let state = PrinterState::init();
    let doc = print_signature(&state, signature, &mut cmt_tbl, arena);
    // res_printer.ml:6443-6456: `Doc.to_string ~width doc ^ "\n"`, also
    // for an empty file.
    format!("{}\n", doc.to_string(width))
}

/// Print a signature with comments using default width.
pub fn print_signature_with_comments(
    signature: &[SignatureItem],
    comments: Vec<Comment>,
    arena: &mut ParseArena,
) -> String {
    print_interface(signature, comments, DEFAULT_PRINT_WIDTH, arena)
}

// ============================================================================
// JSX Printing
// ============================================================================

/// Print a JSX tag name.
fn print_jsx_name(arena: &ParseArena, tag_name: &JsxTagName) -> Doc {
    match tag_name {
        JsxTagName::Invalid(invalid) => Doc::text(invalid.clone()),
        JsxTagName::Lower(name) => print_ident_like(name, true, true),
        JsxTagName::QualifiedLower { path, name } => {
            let lid = arena.get_longident(*path);
            let mut segs: Vec<Doc> = Vec::new();
            // Flatten the longident into parts
            fn collect_parts(lid: &Longident, arena: &ParseArena, parts: &mut Vec<String>) {
                match lid {
                    Longident::Lident(s_idx) => {
                        parts.push(arena.get_string(*s_idx).to_string());
                    }
                    Longident::Ldot(inner, s_idx) => {
                        collect_parts(inner, arena, parts);
                        parts.push(arena.get_string(*s_idx).to_string());
                    }
                    Longident::Lapply(_, _) => {} // Not expected in JSX
                }
            }
            let mut parts = Vec::new();
            collect_parts(lid, arena, &mut parts);
            for part in &parts {
                segs.push(print_ident_like(part, true, false));
            }
            segs.push(print_ident_like(name, true, true));
            Doc::join(Doc::dot(), segs)
        }
        JsxTagName::Upper(path) => {
            let lid = arena.get_longident(*path);
            let mut parts = Vec::new();
            fn collect_parts(lid: &Longident, arena: &ParseArena, parts: &mut Vec<String>) {
                match lid {
                    Longident::Lident(s_idx) => {
                        parts.push(arena.get_string(*s_idx).to_string());
                    }
                    Longident::Ldot(inner, s_idx) => {
                        collect_parts(inner, arena, parts);
                        parts.push(arena.get_string(*s_idx).to_string());
                    }
                    Longident::Lapply(_, _) => {} // Not expected in JSX
                }
            }
            collect_parts(lid, arena, &mut parts);
            let segs: Vec<Doc> = parts
                .iter()
                .map(|s| print_ident_like(s, true, false))
                .collect();
            Doc::join(Doc::dot(), segs)
        }
    }
}

/// Get the position range of a JSX prop (for comment lookup).
fn get_jsx_prop_pos_range(prop: &JsxProp, arena: &ParseArena) -> PosRange {
    match prop {
        JsxProp::Punning { name, .. } => PosRange::from_loc(name.loc, arena),
        JsxProp::Value { name, value, .. } => {
            // Location spans from name to end of value
            let start = arena.loc_start(name.loc);
            let end = arena.loc_end(arena.get_expr(*value).pexp_loc);
            PosRange {
                start: start.cnum,
                end: end.cnum,
            }
        }
        JsxProp::Spreading { loc, .. } => PosRange::from_loc(*loc, arena),
    }
}

/// Get the full location of a JSX prop (for printing helpers).
fn get_jsx_prop_full_loc(prop: &JsxProp, arena: &ParseArena) -> FullLocation {
    match prop {
        JsxProp::Punning { name, .. } => arena.to_location(name.loc),
        JsxProp::Value { name, value, .. } => {
            let start = arena.to_location(name.loc);
            let end = arena.to_location(arena.get_expr(*value).pexp_loc);
            FullLocation {
                loc_start: start.loc_start,
                loc_end: end.loc_end,
                loc_ghost: false,
            }
        }
        JsxProp::Spreading { loc, .. } => arena.to_location(*loc),
    }
}

/// Print a JSX prop.
fn print_jsx_prop(
    state: &PrinterState,
    prop: &JsxProp,
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    let prop_pos_range = get_jsx_prop_pos_range(prop, arena);
    let prop_full_loc = get_jsx_prop_full_loc(prop, arena);
    let doc = match prop {
        JsxProp::Punning { optional, name } => {
            let name_doc = if *optional {
                Doc::concat(vec![
                    Doc::question(),
                    print_ident_like(arena.get_string(name.txt), false, false),
                ])
            } else {
                print_ident_like(arena.get_string(name.txt), false, false)
            };
            name_doc
        }
        JsxProp::Value {
            name,
            optional,
            value,
        } => {
            let has_trailing_comment_after_name =
                has_trailing_single_line_comment(cmt_tbl, name.loc, arena);

            let value_doc = {
                let value = arena.get_expr(*value);
                // A leading comment on a braced application may be attached
                // to the function or first argument rather than the wrapper.
                let leading_line_comment_present = match (
                    parens::jsx_prop_expr(arena, value),
                    &*parsetree_viewer::unwrap_braces(arena, value).pexp_desc,
                ) {
                    (parens::ParenKind::Braced(_), ExpressionDesc::Pexp_apply(apply_inner))
                        if !apply_inner.args.is_empty() =>
                    {
                        let funct = arena.get_expr(apply_inner.funct);
                        let head_arg = arena.get_expr(apply_inner.args[0].1);
                        has_leading_line_comment(cmt_tbl, funct.pexp_loc, arena)
                            || has_leading_line_comment(cmt_tbl, head_arg.pexp_loc, arena)
                    }
                    _ => has_leading_line_comment(cmt_tbl, value.pexp_loc, arena),
                };
                let doc = print_expression_with_comments(state, value, cmt_tbl, arena);
                match parens::jsx_prop_expr(arena, value) {
                    parens::ParenKind::Parenthesized | parens::ParenKind::Braced(_) => {
                        let inner_doc = if parens::braced_expr(arena, value) {
                            add_parens(doc)
                        } else {
                            doc
                        };
                        let multiline_before_value = match &*value.pexp_desc {
                            ExpressionDesc::Pexp_braces(braces) => {
                                arena.loc_start(braces.braces_loc).line + 1
                                    < arena.loc_start(arena.get_expr(braces.expr).pexp_loc).line
                            }
                            _ => false,
                        };
                        if leading_line_comment_present || multiline_before_value {
                            add_braces(inner_doc, true)
                        } else {
                            Doc::concat(vec![Doc::lbrace(), inner_doc, Doc::rbrace()])
                        }
                    }
                    parens::ParenKind::Nothing => doc,
                }
            };

            let name_doc = print_comments(
                print_ident_like(arena.get_string(name.txt), false, false),
                cmt_tbl,
                name.loc,
                arena,
            );

            let doc = Doc::concat(vec![
                name_doc,
                Doc::equal(),
                if *optional {
                    Doc::question()
                } else {
                    Doc::nil()
                },
                if has_trailing_comment_after_name {
                    Doc::hard_line()
                } else {
                    Doc::nil()
                },
                Doc::group(value_doc),
            ]);
            print_comments(doc, cmt_tbl, arena.get_expr(*value).pexp_loc, arena)
        }
        JsxProp::Spreading { expr, .. } => {
            let expr = arena.get_expr(*expr);
            Doc::group(Doc::concat(vec![
                Doc::lbrace(),
                Doc::dotdotdot(),
                print_expression_with_comments_and_parens(state, expr, cmt_tbl, arena),
                Doc::rbrace(),
            ]))
        }
    };
    print_comments_by_pos(doc, cmt_tbl, prop_pos_range, &prop_full_loc)
}

/// Print a list of JSX props.
fn print_jsx_props(
    state: &PrinterState,
    props: &[JsxProp],
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Vec<Doc> {
    props
        .iter()
        .map(|prop| print_jsx_prop(state, prop, cmt_tbl, arena))
        .collect()
}

/// Check if there's a trailing single-line comment at a location.
fn has_trailing_single_line_comment(
    cmt_tbl: &CommentTable,
    loc: LocIdx,
    arena: &ParseArena,
) -> bool {
    if let Some(comments) = cmt_tbl.get_trailing_comments(loc, arena) {
        if let Some(comment) = comments.first() {
            return comment.is_single_line();
        }
    }
    false
}

/// Get count of leading line comments.
fn get_leading_line_comment_count(cmt_tbl: &CommentTable, loc: LocIdx, arena: &ParseArena) -> i32 {
    if let Some(comments) = cmt_tbl.get_leading_comments(loc, arena) {
        comments.iter().filter(|c| c.is_single_line()).count() as i32
    } else {
        0
    }
}

/// Get the closing token position range for a unary JSX element.
/// Returns a position range for the "/>" at the end.
fn unary_element_closing_token_pos_range(
    expr_loc: LocIdx,
    arena: &ParseArena,
) -> (PosRange, FullLocation) {
    // The /> token is at the last 2 characters of the expression
    let end = arena.loc_end(expr_loc);
    let start_pos = crate::location::Position {
        file_name: end.file_name,
        line: end.line,
        bol: end.bol,
        cnum: end.cnum - 2,
    };
    let pos_range = PosRange {
        start: start_pos.cnum,
        end: end.cnum,
    };
    let full_loc = FullLocation {
        loc_start: start_pos,
        loc_end: end.clone(),
        loc_ghost: false,
    };
    (pos_range, full_loc)
}

/// Get the closing tag position range for a container JSX element.
fn container_element_closing_tag_pos_range(
    closing_tag: &JsxClosingTag,
    arena: &ParseArena,
) -> (PosRange, FullLocation) {
    let start_pos = arena.get_position(closing_tag.start);
    let end_pos = arena.get_position(closing_tag.end);
    let pos_range = PosRange {
        start: start_pos.cnum,
        end: end_pos.cnum,
    };
    let full_loc = FullLocation {
        loc_start: start_pos.clone(),
        loc_end: end_pos.clone(),
        loc_ghost: false,
    };
    (pos_range, full_loc)
}

/// Print a unary JSX tag: `<div />` or `<Component prop={value} />`.
fn print_jsx_unary_tag(
    state: &PrinterState,
    tag_name: &Loc<JsxTagName>,
    props: &[JsxProp],
    expr_loc: LocIdx,
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    let name = print_jsx_name(arena, &tag_name.txt);
    let formatted_props = print_jsx_props(state, props, cmt_tbl, arena);
    let tag_loc = tag_name.loc;
    let tag_has_trailing_comment = cmt_tbl.has_trailing_comments(tag_loc, arena);
    let tag_has_no_props = props.is_empty();
    let (closing_token_pos_range, closing_token_full_loc) =
        unary_element_closing_token_pos_range(expr_loc, arena);

    let has_leading_comments_on_closing = cmt_tbl.leading.contains_key(&closing_token_pos_range);

    let props_doc = if tag_has_no_props {
        if has_leading_comments_on_closing {
            Doc::soft_line()
        } else if tag_has_trailing_comment {
            Doc::nil()
        } else {
            Doc::space()
        }
    } else {
        Doc::concat(vec![
            Doc::indent(Doc::concat(vec![
                Doc::line(),
                Doc::group(Doc::join(Doc::line(), formatted_props)),
            ])),
            Doc::line(),
        ])
    };

    let opening_tag = print_comments(
        Doc::concat(vec![Doc::less_than(), name]),
        cmt_tbl,
        tag_loc,
        arena,
    );

    let opening_tag_doc = if tag_has_trailing_comment && !tag_has_no_props {
        Doc::indent(opening_tag)
    } else {
        opening_tag
    };

    let closing_tag_doc = print_comments_by_pos(
        Doc::text("/>"),
        cmt_tbl,
        closing_token_pos_range,
        &closing_token_full_loc,
    );

    Doc::group(Doc::concat(vec![
        opening_tag_doc,
        props_doc,
        if tag_has_trailing_comment && tag_has_no_props {
            Doc::space()
        } else {
            Doc::nil()
        },
        closing_tag_doc,
    ]))
}

/// Get the line separator for JSX children.
fn get_line_sep_for_jsx_children(children: &[ExprIdx], arena: &ParseArena) -> Doc {
    if children.len() > 1
        || children.iter().any(|child| {
            matches!(
                &*arena.get_expr(*child).pexp_desc,
                ExpressionDesc::Pexp_jsx_element(_)
            )
        })
    {
        Doc::hard_line()
    } else {
        Doc::line()
    }
}

/// Print JSX children.
fn print_jsx_children(
    state: &PrinterState,
    children: &[ExprIdx],
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    if children.is_empty() {
        return Doc::nil();
    }

    // Get location for a child expression, considering explicit braces
    let get_loc = |expr_idx: &ExprIdx| -> LocIdx {
        let expr = arena.get_expr(*expr_idx);
        match parsetree_viewer::process_braces(arena, expr).0 {
            Some(braces_loc) => braces_loc,
            None => expr.pexp_loc,
        }
    };

    let sep = get_line_sep_for_jsx_children(children, arena);

    let print_expr = |expr_idx: &ExprIdx, cmt_tbl: &mut CommentTable| -> Doc {
        let expr = arena.get_expr(*expr_idx);
        let leading_line_comment_present = has_leading_line_comment(cmt_tbl, expr.pexp_loc, arena);
        let expr_doc = print_expression_with_comments(state, expr, cmt_tbl, arena);

        let add_parens_or_braces = |expr_doc: Doc| -> Doc {
            // {(20: int)} make sure we also protect the expression inside
            let inner_doc = if parens::braced_expr(arena, expr) {
                add_parens(expr_doc)
            } else {
                expr_doc
            };
            if leading_line_comment_present {
                add_braces(inner_doc, false)
            } else {
                Doc::concat(vec![Doc::lbrace(), inner_doc, Doc::rbrace()])
            }
        };

        match parens::jsx_child_expr(arena, expr) {
            parens::ParenKind::Nothing => {
                print_comments(expr_doc, cmt_tbl, get_loc(expr_idx), arena)
            }
            parens::ParenKind::Parenthesized => add_parens_or_braces(expr_doc),
            parens::ParenKind::Braced(braces_loc) => {
                print_comments(add_parens_or_braces(expr_doc), cmt_tbl, braces_loc, arena)
            }
        }
    };

    let mut acc = Doc::nil();
    let mut iter = children.iter().peekable();

    while let Some(x) = iter.next() {
        let x_doc = print_expr(x, cmt_tbl);

        if let Some(y) = iter.peek() {
            let end_line_x = arena.loc_end(get_loc(x)).line;
            let start_line_y = arena.loc_start(get_loc(y)).line;
            let lines_between = start_line_y - end_line_x - 1;
            let leading_single_line_comments =
                get_leading_line_comment_count(cmt_tbl, get_loc(y), arena);

            // If there are lines between elements, preserve at least one line
            // unless they are all comments
            if lines_between > 0 && lines_between != leading_single_line_comments {
                acc = Doc::concat(vec![acc, x_doc, sep.clone(), Doc::hard_line()]);
            } else {
                acc = Doc::concat(vec![acc, x_doc, sep.clone()]);
            }
        } else {
            // Last element
            acc = Doc::concat(vec![acc, x_doc]);
        }
    }

    acc
}

/// Print a container JSX tag: `<div>children</div>`.
fn print_jsx_container_tag(
    state: &PrinterState,
    tag_name: &Loc<JsxTagName>,
    opening_greater_than: &crate::location::Position,
    props: &[JsxProp],
    children: &[ExprIdx],
    closing_tag: &Option<JsxClosingTag>,
    pexp_loc: LocIdx,
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    let name = print_jsx_name(arena, &tag_name.txt);
    let opening_greater_than_pos_range = PosRange {
        start: opening_greater_than.cnum,
        end: opening_greater_than.cnum,
    };
    let opening_greater_than_full_loc = FullLocation {
        loc_start: opening_greater_than.clone(),
        loc_end: opening_greater_than.clone(),
        loc_ghost: false,
    };

    let opening_greater_than_doc = print_comments_by_pos(
        Doc::greater_than(),
        cmt_tbl,
        opening_greater_than_pos_range,
        &opening_greater_than_full_loc,
    );

    let formatted_props = print_jsx_props(state, props, cmt_tbl, arena);
    let has_children = !children.is_empty();
    let line_sep = get_line_sep_for_jsx_children(children, arena);

    let print_children_doc = |children: &[ExprIdx], cmt_tbl: &mut CommentTable| -> Doc {
        Doc::concat(vec![
            Doc::indent(Doc::concat(vec![
                Doc::line(),
                print_jsx_children(state, children, cmt_tbl, arena),
            ])),
            line_sep.clone(),
        ])
    };

    // Comments between the opening and closing tag
    let has_comments_inside = cmt_tbl.has_inside_comments(pexp_loc, arena);

    let closing_element_doc = match closing_tag {
        None => Doc::nil(),
        Some(closing_tag) => {
            let (closing_tag_pos_range, closing_tag_full_loc) =
                container_element_closing_tag_pos_range(closing_tag, arena);
            let closing_name = print_jsx_name(arena, &closing_tag.name.txt);
            print_comments_by_pos(
                Doc::concat(vec![Doc::text("</"), closing_name, Doc::greater_than()]),
                cmt_tbl,
                closing_tag_pos_range,
                &closing_tag_full_loc,
            )
        }
    };

    let tag_loc = tag_name.loc;
    let opening_tag_name_doc = print_comments(
        Doc::concat(vec![Doc::less_than(), name]),
        cmt_tbl,
        tag_loc,
        arena,
    );

    let props_block_doc = if formatted_props.is_empty() {
        Doc::nil()
    } else {
        Doc::indent(Doc::concat(vec![
            Doc::line(),
            Doc::group(Doc::join(Doc::line(), formatted_props)),
        ]))
    };

    // If the element name has a single comment on the same line, force newline before '>'
    let after_name_and_props_doc = if has_trailing_single_line_comment(cmt_tbl, tag_loc, arena) {
        Doc::concat(vec![Doc::hard_line(), opening_greater_than_doc])
    } else {
        Doc::concat(vec![Doc::soft_line(), opening_greater_than_doc])
    };

    Doc::group(Doc::concat(vec![
        Doc::group(Doc::concat(vec![
            opening_tag_name_doc,
            props_block_doc,
            after_name_and_props_doc,
        ])),
        Doc::concat(vec![
            if has_children {
                print_children_doc(children, cmt_tbl)
            } else if !has_comments_inside {
                Doc::soft_line()
            } else {
                print_comments_inside(cmt_tbl, pexp_loc, arena)
            },
            closing_element_doc,
        ]),
    ]))
}

/// Print a JSX fragment: `<>children</>`.
fn print_jsx_fragment(
    state: &PrinterState,
    opening_greater_than: &crate::location::Position,
    children: &[ExprIdx],
    closing_lesser_than: &crate::location::Position,
    fragment_loc: LocIdx,
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    let fragment_start = arena.loc_start(fragment_loc);
    let fragment_end = arena.loc_end(fragment_loc);

    let opening_pos_range = PosRange {
        start: fragment_start.cnum,
        end: opening_greater_than.cnum,
    };
    let opening_full_loc = FullLocation {
        loc_start: fragment_start.clone(),
        loc_end: opening_greater_than.clone(),
        loc_ghost: false,
    };
    let opening = print_comments_by_pos(
        Doc::text("<>"),
        cmt_tbl,
        opening_pos_range,
        &opening_full_loc,
    );

    let closing_pos_range = PosRange {
        start: closing_lesser_than.cnum,
        end: fragment_end.cnum,
    };
    let closing_full_loc = FullLocation {
        loc_start: closing_lesser_than.clone(),
        loc_end: fragment_end.clone(),
        loc_ghost: false,
    };
    let closing = print_comments_by_pos(
        Doc::text("</>"),
        cmt_tbl,
        closing_pos_range,
        &closing_full_loc,
    );

    let has_children = !children.is_empty();
    let line_sep = get_line_sep_for_jsx_children(children, arena);

    Doc::group(Doc::concat(vec![
        opening,
        Doc::indent(Doc::concat(vec![
            Doc::line(),
            print_jsx_children(state, children, cmt_tbl, arena),
        ])),
        if has_children { line_sep } else { Doc::nil() },
        closing,
    ]))
}

/// Print a JSX element.
fn print_jsx_element(
    state: &PrinterState,
    jsx: &JsxElement,
    expr_loc: LocIdx,
    cmt_tbl: &mut CommentTable,
    arena: &ParseArena,
) -> Doc {
    match jsx {
        JsxElement::Fragment(fragment) => print_jsx_fragment(
            state,
            arena.get_position(fragment.opening),
            &fragment.children,
            arena.get_position(fragment.closing),
            expr_loc,
            cmt_tbl,
            arena,
        ),
        JsxElement::Unary(unary) => print_jsx_unary_tag(
            state,
            &unary.tag_name,
            &unary.props,
            expr_loc,
            cmt_tbl,
            arena,
        ),
        JsxElement::Container(container) => print_jsx_container_tag(
            state,
            &container.tag_name_start,
            arena.get_position(container.opening_end),
            &container.props,
            &container.children,
            &container.closing_tag,
            expr_loc,
            cmt_tbl,
            arena,
        ),
    }
}

/// Add braces around a doc (for JSX children with leading line comments).
fn add_braces(doc: Doc, force_break: bool) -> Doc {
    Doc::breakable_group(
        Doc::concat(vec![
            Doc::lbrace(),
            Doc::indent(Doc::concat(vec![Doc::soft_line(), doc])),
            Doc::soft_line(),
            Doc::rbrace(),
        ]),
        force_break,
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_classify_ident_content() {
        // Normal identifiers
        assert_eq!(
            classify_ident_content("foo", false, false),
            IdentifierStyle::NormalIdent
        );
        assert_eq!(
            classify_ident_content("foo_bar", false, false),
            IdentifierStyle::NormalIdent
        );
        assert_eq!(
            classify_ident_content("foo123", false, false),
            IdentifierStyle::NormalIdent
        );
        assert_eq!(
            classify_ident_content("_foo", false, false),
            IdentifierStyle::NormalIdent
        );

        // Keywords are exotic
        assert_eq!(
            classify_ident_content("let", false, false),
            IdentifierStyle::ExoticIdent
        );
        assert_eq!(
            classify_ident_content("type", false, false),
            IdentifierStyle::ExoticIdent
        );

        // Uppercase without allow_uident
        assert_eq!(
            classify_ident_content("Foo", false, false),
            IdentifierStyle::ExoticIdent
        );

        // Uppercase with allow_uident
        assert_eq!(
            classify_ident_content("Foo", true, false),
            IdentifierStyle::NormalIdent
        );

        // Hyphen without allow_hyphen
        assert_eq!(
            classify_ident_content("foo-bar", false, false),
            IdentifierStyle::ExoticIdent
        );

        // Hyphen with allow_hyphen
        assert_eq!(
            classify_ident_content("foo-bar", false, true),
            IdentifierStyle::NormalIdent
        );

        // Backslash prefix
        assert_eq!(
            classify_ident_content("\\foo", false, false),
            IdentifierStyle::UppercaseExoticIdent
        );
    }

    #[test]
    fn test_is_valid_numeric_polyvar_number() {
        assert!(is_valid_numeric_polyvar_number("0"));
        assert!(is_valid_numeric_polyvar_number("1"));
        assert!(is_valid_numeric_polyvar_number("123"));
        assert!(!is_valid_numeric_polyvar_number("01")); // Leading zero
        assert!(!is_valid_numeric_polyvar_number("abc"));
        assert!(!is_valid_numeric_polyvar_number(""));
    }
}
