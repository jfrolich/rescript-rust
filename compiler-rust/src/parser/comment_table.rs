//! Comment table for the ReScript printer.
//!
//! This module implements comment attachment to AST nodes. Comments are organized
//! into three categories: leading, inside, and trailing comments for each location.
//!
//! This is a 1:1 port of OCaml's `res_comments_table.ml`.

use crate::fast_hash::AHashMap as HashMap;
use crate::location::Location;
use crate::parse_arena::{CoreTypeIdx, ExprIdx, LidentIdx, LocIdx, ParseArena, PatIdx};
use crate::parser::ast::Payload::{PPat, PSig, PStr, PTyp};
use crate::parser::ast::{
    ArgLabel, Attribute, Case, ConstructorArguments, ConstructorDeclaration, CoreType,
    CoreTypeDesc, Expression, ExpressionDesc, Extension, ExtensionConstructor,
    ExtensionConstructorKind, IncludeDeclaration, IncludeDescription, JsxElement, JsxProp,
    LabelDeclaration, Loc, ModuleBinding, ModuleDeclaration, ModuleExpr, ModuleExprDesc,
    ModuleType, ModuleTypeDeclaration, ModuleTypeDesc, ObjectField, OpenDescription, Pattern,
    PatternDesc, PexpApply, RowField, SignatureItem, SignatureItemDesc, StructureItem,
    StructureItemDesc, TypeDeclaration, TypeExtension, TypeKind, ValueBinding, ValueDescription,
    WithConstraint,
};
use crate::parser::comment::Comment;
use crate::parser::longident::Longident;
use crate::parser::parsetree_viewer;

/// Position-based key for comment lookup.
/// Uses (start_cnum, end_cnum) to uniquely identify a location span.
/// This allows looking up comments by position even when LocIdx values differ.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct PosRange {
    pub start: i32,
    pub end: i32,
}

impl PosRange {
    pub fn from_loc(loc: LocIdx, arena: &ParseArena) -> Self {
        let start = arena.loc_start(loc);
        let end = arena.loc_end(loc);
        Self {
            start: start.cnum,
            end: end.cnum,
        }
    }

    pub fn from_location(loc: &Location) -> Self {
        Self {
            start: loc.loc_start.cnum,
            end: loc.loc_end.cnum,
        }
    }

    /// `Res_parsetree_viewer.argument_loc`: the full span of an application
    /// argument, from its label (if any) to the end of its expression.
    pub fn argument(arena: &ParseArena, lbl: &ArgLabel, expr: &Expression) -> Self {
        match lbl {
            ArgLabel::Labelled(lbl_loc) | ArgLabel::Optional(lbl_loc) => Self {
                start: arena.loc_start(lbl_loc.loc).cnum,
                end: arena.loc_end(expr.pexp_loc).cnum,
            },
            ArgLabel::Nolabel => Self::from_loc(expr.pexp_loc, arena),
        }
    }

    /// Special "none" range for file-level comments
    pub fn none() -> Self {
        Self { start: -1, end: -1 }
    }
}

/// A comment table that maps locations to their associated comments.
///
/// Uses position-based keys (PosRange) like OCaml's Location.t hash keys.
/// This ensures locations with the same positions hash to the same key,
/// regardless of which LocIdx they were created from.
#[derive(Debug, Clone, Default)]
pub struct CommentTable {
    /// Comments that appear before a location (indexed by position).
    pub leading: HashMap<PosRange, Vec<Comment>>,
    /// Comments that appear inside a location (indexed by position).
    pub inside: HashMap<PosRange, Vec<Comment>>,
    /// Comments that appear after a location (indexed by position).
    pub trailing: HashMap<PosRange, Vec<Comment>>,
}

impl CommentTable {
    /// Create a new empty comment table.
    pub fn new() -> Self {
        Self {
            leading: HashMap::with_capacity(100),
            inside: HashMap::with_capacity(100),
            trailing: HashMap::with_capacity(100),
        }
    }

    /// Create a copy of the comment table (OCaml `CommentTable.copy`).
    pub fn copy(&self) -> Self {
        self.clone()
    }

    /// Remove and return leading comments for a location.
    /// Like OCaml's Hashtbl.find/remove, this uses position-based keys.
    pub fn remove_leading_comments_by_loc(
        &mut self,
        loc: LocIdx,
        arena: &ParseArena,
    ) -> Vec<Comment> {
        let pos_range = PosRange::from_loc(loc, arena);
        self.leading.remove(&pos_range).unwrap_or_default()
    }

    /// Remove and return trailing comments for a location.
    /// Like OCaml's Hashtbl.find/remove, this uses position-based keys.
    pub fn remove_trailing_comments_by_loc(
        &mut self,
        loc: LocIdx,
        arena: &ParseArena,
    ) -> Vec<Comment> {
        let pos_range = PosRange::from_loc(loc, arena);
        self.trailing.remove(&pos_range).unwrap_or_default()
    }

    /// Remove and return inside comments for a location.
    /// Like OCaml's Hashtbl.find/remove, this uses position-based keys.
    pub fn remove_inside_comments_by_loc(
        &mut self,
        loc: LocIdx,
        arena: &ParseArena,
    ) -> Vec<Comment> {
        let pos_range = PosRange::from_loc(loc, arena);
        self.inside.remove(&pos_range).unwrap_or_default()
    }

    /// Remove and return leading comments by position range.
    pub fn remove_leading_comments_by_pos(&mut self, pos_range: PosRange) -> Vec<Comment> {
        self.leading.remove(&pos_range).unwrap_or_default()
    }

    /// Remove and return trailing comments by position range.
    pub fn remove_trailing_comments_by_pos(&mut self, pos_range: PosRange) -> Vec<Comment> {
        self.trailing.remove(&pos_range).unwrap_or_default()
    }

    /// Remove and return inside comments by position range.
    pub fn remove_inside_comments_by_pos(&mut self, pos_range: PosRange) -> Vec<Comment> {
        self.inside.remove(&pos_range).unwrap_or_default()
    }

    /// Attach leading comments to a location (position-based, like OCaml).
    pub fn attach_leading(&mut self, loc: LocIdx, comments: Vec<Comment>, arena: &ParseArena) {
        if !comments.is_empty() {
            let pos_range = PosRange::from_loc(loc, arena);
            self.leading.insert(pos_range, comments);
        }
    }

    /// Attach trailing comments to a location (position-based, like OCaml).
    pub fn attach_trailing(&mut self, loc: LocIdx, comments: Vec<Comment>, arena: &ParseArena) {
        if !comments.is_empty() {
            let pos_range = PosRange::from_loc(loc, arena);
            self.trailing.insert(pos_range, comments);
        }
    }

    /// Attach inside comments to a location (position-based, like OCaml).
    pub fn attach_inside(&mut self, loc: LocIdx, comments: Vec<Comment>, arena: &ParseArena) {
        if !comments.is_empty() {
            let pos_range = PosRange::from_loc(loc, arena);
            self.inside.insert(pos_range, comments);
        }
    }

    /// Check if there are leading comments for a location.
    pub fn has_leading_comments(&self, loc: LocIdx, arena: &ParseArena) -> bool {
        let pos_range = PosRange::from_loc(loc, arena);
        self.leading.contains_key(&pos_range)
    }

    /// Check if there are trailing comments for a location.
    pub fn has_trailing_comments(&self, loc: LocIdx, arena: &ParseArena) -> bool {
        let pos_range = PosRange::from_loc(loc, arena);
        self.trailing.contains_key(&pos_range)
    }

    /// `has_leading_comments` for a computed location.
    pub fn has_leading_comments_at(&self, range: PosRange) -> bool {
        self.leading.contains_key(&range)
    }

    /// `has_trailing_comments` for a computed location.
    pub fn has_trailing_comments_at(&self, range: PosRange) -> bool {
        self.trailing.contains_key(&range)
    }

    /// res_printer.ml `has_any_trailing_line_comment`.
    pub fn has_any_trailing_line_comment_at(&self, range: PosRange) -> bool {
        self.trailing
            .get(&range)
            .is_some_and(|comments| comments.iter().any(|c| c.is_single_line()))
    }

    /// Check if there are inside comments for a location.
    pub fn has_inside_comments(&self, loc: LocIdx, arena: &ParseArena) -> bool {
        let pos_range = PosRange::from_loc(loc, arena);
        self.inside.contains_key(&pos_range)
    }

    /// Get leading comments for a location.
    pub fn get_leading_comments(&self, loc: LocIdx, arena: &ParseArena) -> Option<&Vec<Comment>> {
        let pos_range = PosRange::from_loc(loc, arena);
        self.leading.get(&pos_range)
    }

    /// Get trailing comments for a location.
    pub fn get_trailing_comments(&self, loc: LocIdx, arena: &ParseArena) -> Option<&Vec<Comment>> {
        let pos_range = PosRange::from_loc(loc, arena);
        self.trailing.get(&pos_range)
    }

    /// Get inside comments for a location.
    pub fn get_inside_comments(&self, loc: LocIdx, arena: &ParseArena) -> Option<&Vec<Comment>> {
        let pos_range = PosRange::from_loc(loc, arena);
        self.inside.get(&pos_range)
    }

    /// Get the first leading comment for a location (if any).
    pub fn get_first_leading_comment(&self, loc: LocIdx, arena: &ParseArena) -> Option<&Comment> {
        let pos_range = PosRange::from_loc(loc, arena);
        self.leading
            .get(&pos_range)
            .and_then(|comments| comments.first())
    }

    /// Get the first leading comment for a position range (if any).
    pub fn get_first_leading_comment_by_pos(&self, pos_range: PosRange) -> Option<&Comment> {
        self.leading
            .get(&pos_range)
            .and_then(|comments| comments.first())
    }
}

/// Partitions a list of comments into three groups based on their position relative to a location:
/// - leading: comments that end before the location's start position
/// - inside: comments that overlap with the location
/// - trailing: comments that start after the location's end position
pub fn partition_by_loc(
    comments: Vec<Comment>,
    loc: LocIdx,
    arena: &mut ParseArena,
) -> (Vec<Comment>, Vec<Comment>, Vec<Comment>) {
    let loc = arena.to_location(loc);
    let mut leading = Vec::new();
    let mut inside = Vec::new();
    let mut trailing = Vec::new();

    for comment in comments {
        let cmt_loc = comment.loc();
        if cmt_loc.loc_end.cnum <= loc.loc_start.cnum {
            leading.push(comment);
        } else if cmt_loc.loc_start.cnum >= loc.loc_end.cnum {
            trailing.push(comment);
        } else {
            inside.push(comment);
        }
    }

    (leading, inside, trailing)
}

/// Splits a list of comments into two groups based on their position relative to a location:
/// - leading: comments that end before the location's start
/// - trailing: comments that start at or after the location's start
pub fn partition_leading_trailing(
    comments: Vec<Comment>,
    loc: LocIdx,
    arena: &mut ParseArena,
) -> (Vec<Comment>, Vec<Comment>) {
    let loc = arena.to_location(loc);
    let mut leading = Vec::new();
    let mut trailing = Vec::new();

    for comment in comments {
        let cmt_loc = comment.loc();
        if cmt_loc.loc_end.cnum <= loc.loc_start.cnum {
            leading.push(comment);
        } else {
            trailing.push(comment);
        }
    }

    (leading, trailing)
}

/// Splits comments into two groups based on whether they start on the same line as a location's end position.
pub fn partition_by_on_same_line(
    loc: LocIdx,
    comments: Vec<Comment>,
    arena: &mut ParseArena,
) -> (Vec<Comment>, Vec<Comment>) {
    let loc = arena.to_location(loc);
    let mut on_same_line = Vec::new();
    let mut on_other_line = Vec::new();

    for comment in comments {
        let cmt_loc = comment.loc();
        if cmt_loc.loc_start.line == loc.loc_end.line {
            on_same_line.push(comment);
        } else {
            on_other_line.push(comment);
        }
    }

    (on_same_line, on_other_line)
}

/// Partitions comments that are adjacent to a location (appear right after it without blank lines).
pub fn partition_adjacent_trailing(
    loc: LocIdx,
    comments: Vec<Comment>,
    arena: &mut ParseArena,
) -> (Vec<Comment>, Vec<Comment>) {
    let loc = arena.to_location(loc);
    let mut after_loc = Vec::new();
    let mut remaining = Vec::new();
    let mut prev_end_pos = loc.loc_end.cnum;
    let mut found_gap = false;

    for comment in comments {
        if found_gap {
            remaining.push(comment);
        } else {
            let cmt_prev_end_pos = comment.prev_tok_end_pos().cnum;
            if prev_end_pos == cmt_prev_end_pos {
                prev_end_pos = comment.loc().loc_end.cnum;
                after_loc.push(comment);
            } else {
                found_gap = true;
                remaining.push(comment);
            }
        }
    }

    (after_loc, remaining)
}

/// Like `partition_adjacent_trailing`, and also keeps the comments that
/// follow a `?` token placed right after `loc`, as in the `=?` of an optional
/// parameter without a default: `(~x /* before */ =? /* after */, ~y)`. Both
/// comments trail the parameter `~x`
/// (res_comments_table.ml `partition_adjacent_trailing_through_question`).
pub fn partition_adjacent_trailing_through_question(
    loc: LocIdx,
    comments: Vec<Comment>,
    arena: &mut ParseArena,
) -> (Vec<Comment>, Vec<Comment>) {
    let (mut after_loc, rest) = partition_adjacent_trailing(loc, comments, arena);
    match rest.first() {
        Some(first)
            if first.prev_tok_is_question()
                && first.prev_tok_end_pos().cnum > arena.loc_end(loc).cnum =>
        {
            let mut extended = arena.to_location(loc);
            extended.loc_end = *first.prev_tok_end_pos();
            let extended = arena.from_location(&extended);
            let (after_question, rest) = partition_adjacent_trailing(extended, rest, arena);
            after_loc.extend(after_question);
            (after_loc, rest)
        }
        _ => (after_loc, rest),
    }
}

/// Splits comments that follow a location but come before another token on the same line.
pub fn partition_adjacent_trailing_before_next_token_on_same_line(
    loc: LocIdx,
    next_token: LocIdx,
    comments: Vec<Comment>,
    arena: &mut ParseArena,
) -> (Vec<Comment>, Vec<Comment>) {
    let loc = arena.to_location(loc);
    let next_token = arena.to_location(next_token);
    let mut after_loc = Vec::new();
    let mut rest = Vec::new();
    let mut done = false;

    for comment in comments {
        if done {
            rest.push(comment);
            continue;
        }

        let cmt_loc = comment.loc();
        // Check if the comment is on the same line as the loc, and is entirely before the next_token
        if cmt_loc.loc_start.line == loc.loc_end.line
            && cmt_loc.loc_start.cnum > loc.loc_end.cnum
            && cmt_loc.loc_end.cnum <= next_token.loc_start.cnum
        {
            after_loc.push(comment);
        } else {
            done = true;
            rest.push(comment);
        }
    }

    (after_loc, rest)
}

/// Extracts comments that appear between two specified line numbers.
pub fn partition_between_lines(
    start_line: i32,
    end_line: i32,
    comments: Vec<Comment>,
) -> (Vec<Comment>, Vec<Comment>) {
    let mut between_comments = Vec::new();
    let mut rest = Vec::new();
    let mut done = false;

    for comment in comments {
        if done {
            rest.push(comment);
            continue;
        }

        let cmt_loc = comment.loc();
        if cmt_loc.loc_start.line > start_line && cmt_loc.loc_end.line < end_line {
            between_comments.push(comment);
        } else {
            done = true;
            rest.push(comment);
        }
    }

    (between_comments, rest)
}

/// AST node types for the walker.
#[derive(Debug)]
pub enum Node<'a> {
    Case(&'a Case),
    CoreType(&'a CoreType),
    CoreTypeIdx(CoreTypeIdx),
    ExprArgument { expr: ExprIdx, loc: LocIdx },
    Expression(&'a Expression),
    ExpressionIdx(ExprIdx),
    ExprRecordRow(&'a Loc<LidentIdx>, ExprIdx),
    ExtensionConstructor(&'a ExtensionConstructor),
    LabelDeclaration(&'a LabelDeclaration),
    ModuleBinding(&'a ModuleBinding),
    ModuleDeclaration(&'a ModuleDeclaration),
    ModuleExpr(&'a ModuleExpr),
    ObjectField(&'a ObjectField),
    PackageConstraint(&'a Loc<LidentIdx>, CoreTypeIdx),
    Pattern(&'a Pattern),
    PatternIdx(PatIdx),
    PatternRecordRow(&'a Loc<LidentIdx>, PatIdx),
    PatternRecordRest(&'a crate::parser::ast::RecordPatRest),
    RowField(&'a RowField),
    SignatureItem(&'a SignatureItem),
    StructureItem(&'a StructureItem),
    TypeDeclaration(&'a TypeDeclaration),
    ValueBinding(&'a ValueBinding),
    JsxProp(&'a JsxProp),
}

impl<'a> Node<'a> {
    /// Get the location of a node.
    pub fn get_loc(&self, arena: &mut ParseArena) -> LocIdx {
        match self {
            Node::Case(case) => {
                // The case location extends from pattern to the end of the expression
                // Check for braces attribute on RHS - if present, use its end location
                // This must match the logic in printer.rs:get_case_pos_range
                let pc_lhs = arena.get_pat(case.pc_lhs);
                let pc_rhs = arena.get_expr(case.pc_rhs);
                let start = arena.loc_start(pc_lhs.ppat_loc);
                let end = match parsetree_viewer::process_braces(arena, pc_rhs).0 {
                    Some(braces_loc) => arena.loc_end(braces_loc),
                    None => arena.loc_end(pc_rhs.pexp_loc),
                };
                arena.from_location(&Location::from_positions(*start, *end))
            }
            Node::CoreType(ct) => ct.ptyp_loc,
            Node::CoreTypeIdx(idx) => arena.get_core_type(*idx).ptyp_loc,
            Node::ExprArgument { loc, .. } => *loc,
            Node::Expression(e) => match parsetree_viewer::process_braces(arena, e).0 {
                Some(braces_loc) => braces_loc,
                None => e.pexp_loc,
            },
            Node::ExpressionIdx(idx) => {
                let e = arena.get_expr(*idx);
                match parsetree_viewer::process_braces(arena, e).0 {
                    Some(braces_loc) => braces_loc,
                    None => e.pexp_loc,
                }
            }
            Node::ExprRecordRow(li, expr_idx) => {
                let e = arena.get_expr(*expr_idx);
                let start = arena.loc_start(li.loc);
                let end = arena.loc_end(e.pexp_loc);
                arena.from_location(&Location::from_positions(*start, *end))
            }
            Node::ExtensionConstructor(ec) => ec.pext_loc,
            Node::LabelDeclaration(ld) => ld.pld_loc,
            Node::ModuleBinding(mb) => mb.pmb_loc,
            Node::ModuleDeclaration(md) => md.pmd_loc,
            Node::ModuleExpr(me) => me.pmod_loc,
            Node::ObjectField(field) => match field {
                ObjectField::Otag(lbl, _attrs, typ_idx) => {
                    let typ = arena.get_core_type(*typ_idx);
                    let start = arena.loc_start(lbl.loc);
                    let end = arena.loc_end(typ.ptyp_loc);
                    arena.from_location(&Location::from_positions(*start, *end))
                }
                ObjectField::Oinherit(typ_idx) => arena.get_core_type(*typ_idx).ptyp_loc,
            },
            Node::PackageConstraint(li, typ_idx) => {
                let te = arena.get_core_type(*typ_idx);
                let start = arena.loc_start(li.loc);
                let end = arena.loc_end(te.ptyp_loc);
                arena.from_location(&Location::from_positions(*start, *end))
            }
            Node::Pattern(p) => p.ppat_loc,
            Node::PatternIdx(idx) => arena.get_pat(*idx).ppat_loc,
            Node::PatternRecordRest(rest) => rest.rest_loc,
            Node::PatternRecordRow(li, pat_idx) => {
                let p = arena.get_pat(*pat_idx);
                // For punned patterns, li.loc and p.ppat_loc are the same
                // Use li.loc directly to avoid creating a new LocIdx that won't match during printing
                if li.loc == p.ppat_loc {
                    li.loc
                } else {
                    let start = arena.loc_start(li.loc);
                    let end = arena.loc_end(p.ppat_loc);
                    arena.from_location(&Location::from_positions(*start, *end))
                }
            }
            Node::RowField(rf) => match rf {
                RowField::Rtag(tag, _attrs, _flag, _args) => tag.loc,
                RowField::Rinherit(typ_idx) => arena.get_core_type(*typ_idx).ptyp_loc,
            },
            Node::SignatureItem(si) => si.psig_loc,
            Node::StructureItem(si) => si.pstr_loc,
            Node::TypeDeclaration(td) => td.ptype_loc,
            Node::ValueBinding(vb) => vb.pvb_loc,
            Node::JsxProp(prop) => get_jsx_prop_loc(prop, arena),
        }
    }
}

/// Get the location of a JSX prop.
fn get_jsx_prop_loc(prop: &JsxProp, arena: &mut ParseArena) -> LocIdx {
    match prop {
        JsxProp::Punning { name, .. } => name.loc,
        JsxProp::Value { name, value, .. } => {
            let val = arena.get_expr(*value);
            let start = arena.loc_start(name.loc);
            let end = arena.loc_end(val.pexp_loc);
            arena.from_location(&Location::from_positions(*start, *end))
        }
        JsxProp::Spreading { loc, .. } => *loc,
    }
}

/// Check if an expression is a block expression.
fn is_block_expr_idx(arena: &ParseArena, idx: ExprIdx) -> bool {
    is_block_expr(arena, arena.get_expr(idx))
}

fn is_block_expr(arena: &ParseArena, expr: &Expression) -> bool {
    match &expr.pexp_desc {
        ExpressionDesc::Pexp_braces(braces) => is_block_expr_idx(arena, braces.expr),
        ExpressionDesc::Pexp_letmodule(..)
        | ExpressionDesc::Pexp_letexception(..)
        | ExpressionDesc::Pexp_let(..)
        | ExpressionDesc::Pexp_open(..)
        | ExpressionDesc::Pexp_sequence(..) => true,
        ExpressionDesc::Pexp_apply(apply_inner)
            if {
                let PexpApply { ref funct, .. } = *apply_inner;
                is_block_expr_idx(arena, *funct)
            } =>
        {
            true
        }
        ExpressionDesc::Pexp_constraint(inner) if is_block_expr_idx(arena, inner.0) => true,
        ExpressionDesc::Pexp_field(inner, _) if is_block_expr_idx(arena, *inner) => true,
        ExpressionDesc::Pexp_setfield(inner) if is_block_expr_idx(arena, inner.0) => true,
        _ => false,
    }
}

/// Check if an expression is an if-then-else or a ternary
/// (res_comments_table.ml `is_conditional_expr`).
fn is_conditional_expr(expr: &Expression) -> bool {
    matches!(
        &expr.pexp_desc,
        ExpressionDesc::Pexp_ifthenelse(..) | ExpressionDesc::Pexp_ternary(..)
    )
}

/// Collect list patterns from a cons pattern.
fn collect_list_patterns(arena: &ParseArena, pattern: &Pattern) -> Vec<Pattern> {
    let mut acc = Vec::new();
    let mut current = pattern;

    loop {
        match &current.ppat_desc {
            // `::` takes its head and rest as two arguments, or as one 2-tuple.
            PatternDesc::Ppat_construct(name, args) if arena.is_lident(name.txt, "::") => {
                let pair = match args.txt.as_slice() {
                    [pat, rest] => Some((*pat, *rest)),
                    [arg] => match &arena.get_pat(*arg).ppat_desc {
                        PatternDesc::Ppat_tuple(tuple) if tuple.len() == 2 => {
                            Some((tuple[0], tuple[1]))
                        }
                        _ => None,
                    },
                    _ => None,
                };
                if let Some((pat, rest)) = pair {
                    acc.push(arena.get_pat(pat).clone());
                    current = arena.get_pat(rest);
                    continue;
                }
                acc.push(current.clone());
                break;
            }
            PatternDesc::Ppat_construct(name, args)
                if arena.is_lident(name.txt, "[]") && args.txt.is_empty() =>
            {
                break;
            }
            _ => {
                acc.push(current.clone());
                break;
            }
        }
    }

    acc
}

/// Collect list expressions from a cons expression.
fn collect_list_exprs(arena: &ParseArena, expr: &Expression) -> Vec<Expression> {
    let mut acc = Vec::new();
    let mut current = expr;

    loop {
        match &current.pexp_desc {
            // `::` takes its head and rest as two arguments, or as one 2-tuple.
            ExpressionDesc::Pexp_construct(name, args) if arena.is_lident(name.txt, "::") => {
                let pair = match args.txt.as_slice() {
                    [expr, rest] => Some((*expr, *rest)),
                    [arg] => match &arena.get_expr(*arg).pexp_desc {
                        ExpressionDesc::Pexp_tuple(tuple) if tuple.len() == 2 => {
                            Some((tuple[0], tuple[1]))
                        }
                        _ => None,
                    },
                    _ => None,
                };
                if let Some((expr, rest)) = pair {
                    acc.push(arena.get_expr(expr).clone());
                    current = arena.get_expr(rest);
                    continue;
                }
                acc.push(current.clone());
                break;
            }
            ExpressionDesc::Pexp_construct(name, _) if arena.is_lident(name.txt, "[]") => {
                break;
            }
            _ => {
                acc.push(current.clone());
                break;
            }
        }
    }

    acc
}

// ============================================================================
// Walk functions for populating the comment table
// ============================================================================

/// Walk a structure and attach comments to AST nodes.
pub fn walk_structure(
    structure: &[StructureItem],
    t: &mut CommentTable,
    comments: Vec<Comment>,
    arena: &mut ParseArena,
) {
    if comments.is_empty() {
        return;
    }
    if structure.is_empty() {
        t.attach_inside(LocIdx::none(), comments, arena);
        return;
    }

    let nodes: Vec<Node<'_>> = structure.iter().map(Node::StructureItem).collect();
    walk_list(&nodes, t, comments, arena);
}

/// Walk a signature and attach comments to AST nodes.
pub fn walk_signature(
    signature: &[SignatureItem],
    t: &mut CommentTable,
    comments: Vec<Comment>,
    arena: &mut ParseArena,
) {
    if comments.is_empty() {
        return;
    }
    if signature.is_empty() {
        t.attach_inside(LocIdx::none(), comments, arena);
        return;
    }

    let nodes: Vec<Node<'_>> = signature.iter().map(Node::SignatureItem).collect();
    walk_list(&nodes, t, comments, arena);
}

/// Walk a list of nodes.
fn walk_list(
    nodes: &[Node<'_>],
    t: &mut CommentTable,
    comments: Vec<Comment>,
    arena: &mut ParseArena,
) {
    walk_list_impl(nodes, t, comments, None, arena);
}

fn walk_list_impl(
    nodes: &[Node<'_>],
    t: &mut CommentTable,
    comments: Vec<Comment>,
    prev_loc: Option<LocIdx>,
    arena: &mut ParseArena,
) {
    if comments.is_empty() {
        return;
    }
    if nodes.is_empty() {
        if let Some(loc) = prev_loc {
            t.attach_trailing(loc, comments, arena);
        }
        return;
    }

    let node = &nodes[0];
    let rest_nodes = &nodes[1..];
    let curr_loc = node.get_loc(arena);

    let (leading, inside, trailing) = partition_by_loc(comments, curr_loc, arena);

    let prev_loc_resolved = prev_loc.map(|l| arena.to_location(l));
    let curr_loc_resolved = arena.to_location(curr_loc);

    match &prev_loc {
        None => {
            // First node, all leading comments attach here
            t.attach_leading(curr_loc, leading, arena);
        }
        Some(prev_loc_idx) => {
            let prev_loc_resolved = prev_loc_resolved.as_ref().unwrap();
            // Check if on same line
            if prev_loc_resolved.loc_end.line == curr_loc_resolved.loc_start.line {
                let (after_prev, before_curr) =
                    partition_adjacent_trailing(*prev_loc_idx, leading, arena);
                t.attach_trailing(*prev_loc_idx, after_prev, arena);
                t.attach_leading(curr_loc, before_curr, arena);
            } else {
                let (on_same_line_as_prev, after_prev) =
                    partition_by_on_same_line(*prev_loc_idx, leading, arena);
                t.attach_trailing(*prev_loc_idx, on_same_line_as_prev, arena);
                let (before_curr, _, _) = partition_by_loc(after_prev, curr_loc, arena);
                t.attach_leading(curr_loc, before_curr, arena);
            }
        }
    }

    walk_node(node, t, inside, arena);
    walk_list_impl(rest_nodes, t, trailing, Some(curr_loc), arena);
}

/// Walk a node and its children.
fn walk_node(
    node: &Node<'_>,
    t: &mut CommentTable,
    comments: Vec<Comment>,
    arena: &mut ParseArena,
) {
    match node {
        Node::Case(c) => walk_case(c, t, comments, arena),
        Node::CoreType(ct) => walk_core_type(ct, t, comments, arena),
        Node::CoreTypeIdx(idx) => {
            // Safety: arena is append-only, core type won't be invalidated
            let ct = arena.get_core_type(*idx).clone();
            walk_core_type(&ct, t, comments, arena);
        }
        Node::ExprArgument { expr, loc } => {
            // Safety: arena is append-only, expression won't be invalidated
            let e = arena.get_expr(*expr).clone();
            walk_expr_argument(&e, loc, t, comments, arena);
        }
        Node::Expression(e) => walk_expression(e, t, comments, arena),
        Node::ExpressionIdx(idx) => {
            // Safety: arena is append-only, expression won't be invalidated
            let e = arena.get_expr(*idx).clone();
            walk_expression(&e, t, comments, arena);
        }
        Node::ExprRecordRow(li, expr_idx) => {
            // Safety: arena is append-only, expression won't be invalidated
            let e = arena.get_expr(*expr_idx).clone();
            walk_expr_record_row(li, &e, t, comments, arena);
        }
        Node::ExtensionConstructor(ec) => walk_extension_constructor(ec, t, comments, arena),
        Node::LabelDeclaration(ld) => walk_label_declaration(ld, t, comments, arena),
        Node::ModuleBinding(mb) => walk_module_binding(mb, t, comments, arena),
        Node::ModuleDeclaration(md) => walk_module_declaration(md, t, comments, arena),
        Node::ModuleExpr(me) => walk_module_expr(me, t, comments, arena),
        Node::ObjectField(f) => walk_object_field(f, t, comments, arena),
        Node::PackageConstraint(li, typ_idx) => {
            // Safety: arena is append-only, core type won't be invalidated
            let te = arena.get_core_type(*typ_idx).clone();
            walk_package_constraint(li, &te, t, comments, arena);
        }
        Node::Pattern(p) => walk_pattern(p, t, comments, arena),
        Node::PatternIdx(idx) => {
            // Safety: arena is append-only, pattern won't be invalidated
            let p = arena.get_pat(*idx).clone();
            walk_pattern(&p, t, comments, arena);
        }
        Node::PatternRecordRow(li, pat_idx) => {
            // Safety: arena is append-only, pattern won't be invalidated
            let p = arena.get_pat(*pat_idx).clone();
            walk_pattern_record_row(li, &p, t, comments, arena);
        }
        Node::PatternRecordRest(rest) => walk_pattern_record_rest(rest, t, comments, arena),
        Node::RowField(rf) => walk_row_field(rf, t, comments, arena),
        Node::SignatureItem(si) => walk_signature_item(si, t, comments, arena),
        Node::StructureItem(si) => walk_structure_item(si, t, comments, arena),
        Node::TypeDeclaration(td) => walk_type_declaration(td, t, comments, arena),
        Node::ValueBinding(vb) => walk_value_binding(vb, t, comments, arena),
        Node::JsxProp(prop) => walk_jsx_prop(prop, t, comments, arena),
    }
}

fn walk_structure_item(
    si: &StructureItem,
    t: &mut CommentTable,
    comments: Vec<Comment>,
    arena: &mut ParseArena,
) {
    if comments.is_empty() {
        return;
    }

    match &*si.pstr_desc {
        StructureItemDesc::Pstr_primitive(vd) => walk_value_description(vd, t, comments, arena),
        StructureItemDesc::Pstr_open(od) => walk_open_description(od, t, comments, arena),
        StructureItemDesc::Pstr_value(inner) => {
            let (_, ref bindings) = **inner;
            walk_value_bindings(bindings, t, comments, arena)
        }
        StructureItemDesc::Pstr_type(inner) => {
            let (_, ref declarations) = **inner;
            walk_type_declarations(declarations, t, comments, arena)
        }
        StructureItemDesc::Pstr_eval(inner) => {
            let (ref expr_idx, _) = **inner;
            // Safety: arena is append-only, expression won't be invalidated
            let expr = arena.get_expr(*expr_idx).clone();
            walk_expression(&expr, t, comments, arena)
        }
        StructureItemDesc::Pstr_module(mb) => walk_module_binding(mb, t, comments, arena),
        StructureItemDesc::Pstr_recmodule(mbs) => {
            let nodes: Vec<Node<'_>> = mbs.iter().map(Node::ModuleBinding).collect();
            walk_list(&nodes, t, comments, arena);
        }
        StructureItemDesc::Pstr_modtype(mtd) => {
            walk_module_type_declaration(mtd, t, comments, arena)
        }
        StructureItemDesc::Pstr_attribute(attr) => walk_attribute(attr, t, comments, arena),
        StructureItemDesc::Pstr_extension(inner) => {
            let (ref ext, _) = **inner;
            walk_extension(ext, t, comments, arena)
        }
        StructureItemDesc::Pstr_include(id) => walk_include_declaration(id, t, comments, arena),
        StructureItemDesc::Pstr_exception(ec) => walk_extension_constructor(ec, t, comments, arena),
        StructureItemDesc::Pstr_typext(te) => walk_type_extension(te, t, comments, arena),
    }
}

fn walk_signature_item(
    si: &SignatureItem,
    t: &mut CommentTable,
    comments: Vec<Comment>,
    arena: &mut ParseArena,
) {
    if comments.is_empty() {
        return;
    }

    match &*si.psig_desc {
        SignatureItemDesc::Psig_value(vd) => walk_value_description(vd, t, comments, arena),
        SignatureItemDesc::Psig_type(inner) => {
            let (_, ref declarations) = **inner;
            walk_type_declarations(declarations, t, comments, arena)
        }
        SignatureItemDesc::Psig_typext(te) => walk_type_extension(te, t, comments, arena),
        SignatureItemDesc::Psig_exception(ec) => walk_extension_constructor(ec, t, comments, arena),
        SignatureItemDesc::Psig_module(md) => walk_module_declaration(md, t, comments, arena),
        SignatureItemDesc::Psig_recmodule(mds) => {
            let nodes: Vec<Node<'_>> = mds.iter().map(Node::ModuleDeclaration).collect();
            walk_list(&nodes, t, comments, arena);
        }
        SignatureItemDesc::Psig_modtype(mtd) => {
            walk_module_type_declaration(mtd, t, comments, arena)
        }
        SignatureItemDesc::Psig_open(od) => walk_open_description(od, t, comments, arena),
        SignatureItemDesc::Psig_include(id) => walk_include_description(id, t, comments, arena),
        SignatureItemDesc::Psig_attribute(attr) => walk_attribute(attr, t, comments, arena),
        SignatureItemDesc::Psig_extension(inner) => {
            let (ref ext, _) = **inner;
            walk_extension(ext, t, comments, arena)
        }
    }
}

fn walk_value_description(
    vd: &ValueDescription,
    t: &mut CommentTable,
    comments: Vec<Comment>,
    arena: &mut ParseArena,
) {
    let (leading, trailing) = partition_leading_trailing(comments, vd.pval_name.loc, arena);
    t.attach_leading(vd.pval_name.loc, leading, arena);

    let (after_name, rest) = partition_adjacent_trailing(vd.pval_name.loc, trailing, arena);
    t.attach_trailing(vd.pval_name.loc, after_name, arena);

    let pval_type = arena.get_core_type(vd.pval_type);
    let pval_type_loc = pval_type.ptyp_loc;
    let (before, inside, after) = partition_by_loc(rest, pval_type_loc, arena);
    t.attach_leading(pval_type_loc, before, arena);
    // Safety: arena is append-only, core type won't be invalidated
    let pval_type = arena.get_core_type(vd.pval_type).clone();
    walk_core_type(&pval_type, t, inside, arena);
    t.attach_trailing(pval_type_loc, after, arena);
}

fn walk_type_extension(
    te: &TypeExtension,
    t: &mut CommentTable,
    comments: Vec<Comment>,
    arena: &mut ParseArena,
) {
    let (leading, trailing) = partition_leading_trailing(comments, te.ptyext_path.loc, arena);
    t.attach_leading(te.ptyext_path.loc, leading, arena);

    let (after_path, rest) = partition_adjacent_trailing(te.ptyext_path.loc, trailing, arena);
    t.attach_trailing(te.ptyext_path.loc, after_path, arena);

    // Type params
    let rest = if te.ptyext_params.is_empty() {
        rest
    } else {
        visit_list_but_continue_with_remaining_comments(
            &te.ptyext_params,
            |param, arena| arena.get_core_type(param.0).ptyp_loc,
            |param, t, comments, arena| {
                // Safety: arena is append-only, core type won't be invalidated
                let ct = arena.get_core_type(param.0).clone();
                walk_core_type(&ct, t, comments, arena);
            },
            t,
            rest,
            false,
            arena,
        )
    };

    let nodes: Vec<Node<'_>> = te
        .ptyext_constructors
        .iter()
        .map(Node::ExtensionConstructor)
        .collect();
    walk_list(&nodes, t, rest, arena);
}

fn walk_include_declaration(
    id: &IncludeDeclaration,
    t: &mut CommentTable,
    comments: Vec<Comment>,
    arena: &mut ParseArena,
) {
    let pincl_mod = arena.get_mod_expr(id.pincl_mod);
    let pincl_mod_loc = pincl_mod.pmod_loc;
    let (before, inside, after) = partition_by_loc(comments, pincl_mod_loc, arena);
    t.attach_leading(pincl_mod_loc, before, arena);
    // Safety: arena is append-only, module expression won't be invalidated
    let pincl_mod = arena.get_mod_expr(id.pincl_mod).clone();
    walk_module_expr(&pincl_mod, t, inside, arena);
    t.attach_trailing(pincl_mod_loc, after, arena);
}

fn walk_include_description(
    id: &IncludeDescription,
    t: &mut CommentTable,
    comments: Vec<Comment>,
    arena: &mut ParseArena,
) {
    let pincl_mod = arena.get_mod_type(id.pincl_mod);
    let pincl_mod_loc = pincl_mod.pmty_loc;
    let (before, inside, after) = partition_by_loc(comments, pincl_mod_loc, arena);
    t.attach_leading(pincl_mod_loc, before, arena);
    // Safety: arena is append-only, module type won't be invalidated
    let pincl_mod = arena.get_mod_type(id.pincl_mod).clone();
    walk_mod_type(&pincl_mod, t, inside, arena);
    t.attach_trailing(pincl_mod_loc, after, arena);
}

fn walk_module_type_declaration(
    mtd: &ModuleTypeDeclaration,
    t: &mut CommentTable,
    comments: Vec<Comment>,
    arena: &mut ParseArena,
) {
    let (leading, trailing) = partition_leading_trailing(comments, mtd.pmtd_name.loc, arena);
    t.attach_leading(mtd.pmtd_name.loc, leading, arena);

    match &mtd.pmtd_type {
        None => {
            t.attach_trailing(mtd.pmtd_name.loc, trailing, arena);
        }
        Some(mod_type_idx) => {
            let (after_name, rest) =
                partition_adjacent_trailing(mtd.pmtd_name.loc, trailing, arena);
            t.attach_trailing(mtd.pmtd_name.loc, after_name, arena);

            let mod_type_loc = arena.get_mod_type(*mod_type_idx).pmty_loc;
            let (before, inside, after) = partition_by_loc(rest, mod_type_loc, arena);
            t.attach_leading(mod_type_loc, before, arena);
            // Safety: arena is append-only, module type won't be invalidated
            let mod_type = arena.get_mod_type(*mod_type_idx).clone();
            walk_mod_type(&mod_type, t, inside, arena);
            t.attach_trailing(mod_type_loc, after, arena);
        }
    }
}

fn walk_module_binding(
    mb: &ModuleBinding,
    t: &mut CommentTable,
    comments: Vec<Comment>,
    arena: &mut ParseArena,
) {
    let (leading, trailing) = partition_leading_trailing(comments, mb.pmb_name.loc, arena);
    t.attach_leading(mb.pmb_name.loc, leading, arena);

    let (after_name, rest) = partition_adjacent_trailing(mb.pmb_name.loc, trailing, arena);
    t.attach_trailing(mb.pmb_name.loc, after_name, arena);

    let pmb_expr = arena.get_mod_expr(mb.pmb_expr);
    let pmb_expr_loc = pmb_expr.pmod_loc;
    let is_constraint = matches!(&*pmb_expr.pmod_desc, ModuleExprDesc::Pmod_constraint(..));
    let (leading, inside, trailing) = partition_by_loc(rest, pmb_expr_loc, arena);

    // Safety: arena is append-only, module expression won't be invalidated
    let pmb_expr = arena.get_mod_expr(mb.pmb_expr).clone();
    if is_constraint {
        let combined: Vec<Comment> = leading.into_iter().chain(inside).collect();
        walk_module_expr(&pmb_expr, t, combined, arena);
    } else {
        t.attach_leading(pmb_expr_loc, leading, arena);
        walk_module_expr(&pmb_expr, t, inside, arena);
    }
    t.attach_trailing(pmb_expr_loc, trailing, arena);
}

fn walk_module_declaration(
    md: &ModuleDeclaration,
    t: &mut CommentTable,
    comments: Vec<Comment>,
    arena: &mut ParseArena,
) {
    let (leading, trailing) = partition_leading_trailing(comments, md.pmd_name.loc, arena);
    t.attach_leading(md.pmd_name.loc, leading, arena);

    let (after_name, rest) = partition_adjacent_trailing(md.pmd_name.loc, trailing, arena);
    t.attach_trailing(md.pmd_name.loc, after_name, arena);

    let pmd_type_loc = arena.get_mod_type(md.pmd_type).pmty_loc;
    let (leading, inside, trailing) = partition_by_loc(rest, pmd_type_loc, arena);
    t.attach_leading(pmd_type_loc, leading, arena);
    // Safety: arena is append-only, module type won't be invalidated
    let pmd_type = arena.get_mod_type(md.pmd_type).clone();
    walk_mod_type(&pmd_type, t, inside, arena);
    t.attach_trailing(pmd_type_loc, trailing, arena);
}

fn walk_open_description(
    od: &OpenDescription,
    t: &mut CommentTable,
    comments: Vec<Comment>,
    arena: &mut ParseArena,
) {
    let loc = od.popen_lid.loc;
    let (leading, trailing) = partition_leading_trailing(comments, loc, arena);
    t.attach_leading(loc, leading, arena);
    t.attach_trailing(loc, trailing, arena);
}

fn walk_value_bindings(
    vbs: &[ValueBinding],
    t: &mut CommentTable,
    comments: Vec<Comment>,
    arena: &mut ParseArena,
) {
    let nodes: Vec<Node<'_>> = vbs.iter().map(Node::ValueBinding).collect();
    walk_list(&nodes, t, comments, arena);
}

fn walk_type_declarations(
    tds: &[TypeDeclaration],
    t: &mut CommentTable,
    comments: Vec<Comment>,
    arena: &mut ParseArena,
) {
    let nodes: Vec<Node<'_>> = tds.iter().map(Node::TypeDeclaration).collect();
    walk_list(&nodes, t, comments, arena);
}

/// Rewrite value binding locations for sugar cases.
/// OCaml's comment_table.ml has special handling for value binding sugar:
/// - `let x: poly_type = expr` where expr is constraint/newtype
/// The AST locations for these sugar forms span the entire binding, which would
/// cause all comments to be "inside" the pattern. OCaml rewrites the locations
/// so the pattern ends at the type annotation, and uses the inner expression.
///
/// Returns (pattern_loc, expression_idx, expression_loc)
fn rewrite_value_binding_locs(
    vb: &ValueBinding,
    arena: &mut ParseArena,
) -> (LocIdx, ExprIdx, LocIdx) {
    // Default: use the value binding's own locations
    let pvb_pat = arena.get_pat(vb.pvb_pat);
    let pvb_expr = arena.get_expr(vb.pvb_expr).clone();
    let pvb_expr_loc = pvb_expr.pexp_loc;
    let default = (pvb_pat.ppat_loc, vb.pvb_expr, pvb_expr_loc);

    // Check for the sugar cases that OCaml handles specially
    match (&pvb_pat.ppat_desc, &pvb_expr.pexp_desc) {
        // Case 1: Ppat_constraint with Pexp_constraint, empty Ptyp_poly
        // let x: t = (expr: typ)
        (PatternDesc::Ppat_constraint(pat_inner), ExpressionDesc::Pexp_constraint(expr_inner)) => {
            let (ref pat_idx, ref typ_idx) = **pat_inner;
            let (ref expr_idx, _) = **expr_inner;
            let pat_loc = arena.get_pat(*pat_idx).ppat_loc;
            let typ = arena.get_core_type(*typ_idx);
            if let CoreTypeDesc::Ptyp_poly(poly_inner) = &typ.ptyp_desc {
                let (ref vars, ref inner_typ_idx) = **poly_inner;
                let inner_typ_loc = arena.get_core_type(*inner_typ_idx).ptyp_loc;
                if vars.is_empty() {
                    // Pattern loc ends at the inner type's location
                    let new_pat_loc = arena.from_location(&Location {
                        loc_start: *arena.loc_start(pat_loc),
                        loc_end: *arena.loc_end(inner_typ_loc),
                        loc_ghost: false,
                        origin: Default::default(),
                    });
                    let inner_expr_loc = arena.get_expr(*expr_idx).pexp_loc;
                    (new_pat_loc, *expr_idx, inner_expr_loc)
                } else {
                    default
                }
            } else {
                default
            }
        }

        // Case 2: Ppat_constraint with Pexp_fun, non-empty Ptyp_poly
        // let x: type a. t = (a, b) => ...
        (PatternDesc::Ppat_constraint(pat_inner), ExpressionDesc::Pexp_fun(_)) => {
            let (ref _pat_idx, ref typ_idx) = **pat_inner;
            let typ = arena.get_core_type(*typ_idx);
            if let CoreTypeDesc::Ptyp_poly(poly_inner) = &typ.ptyp_desc {
                let (ref vars, ref inner_typ_idx) = **poly_inner;
                let inner_typ_loc = arena.get_core_type(*inner_typ_idx).ptyp_loc;
                if !vars.is_empty() {
                    // Pattern loc ends at the inner type's location
                    let new_pat_loc = arena.from_location(&Location {
                        loc_start: *arena.loc_start(pvb_pat.ppat_loc),
                        loc_end: *arena.loc_end(inner_typ_loc),
                        loc_ghost: false,
                        origin: Default::default(),
                    });
                    (new_pat_loc, vb.pvb_expr, pvb_expr_loc)
                } else {
                    default
                }
            } else {
                default
            }
        }

        // Case 3: Ppat_constraint with Pexp_newtype containing Pexp_constraint
        // let x: type t. (...) => ... = (type t) => (a, b): (...) => ... => ...
        // This is the value binding sugar case
        (PatternDesc::Ppat_constraint(pat_inner), ExpressionDesc::Pexp_newtype(newtype_inner)) => {
            let (ref _pat_idx, ref typ_idx) = **pat_inner;
            let (_name, ref inner_expr_idx) = **newtype_inner;
            let typ = arena.get_core_type(*typ_idx);
            if let CoreTypeDesc::Ptyp_poly(poly_inner) = &typ.ptyp_desc {
                let (ref vars, ref inner_typ_idx) = **poly_inner;
                let inner_typ_loc = arena.get_core_type(*inner_typ_idx).ptyp_loc;
                if !vars.is_empty() {
                    // Check if inner expression is Pexp_constraint
                    // Extract the constraint's inner expr_idx before borrowing arena mutably
                    let constraint_expr_idx = {
                        let inner_expr = arena.get_expr(*inner_expr_idx).clone();
                        if let ExpressionDesc::Pexp_constraint(constraint_inner) =
                            &inner_expr.pexp_desc
                        {
                            let (ref expr_idx, _) = **constraint_inner;
                            Some(*expr_idx)
                        } else {
                            None
                        }
                    };
                    if let Some(expr_idx) = constraint_expr_idx {
                        let new_pat_loc = arena.from_location(&Location {
                            loc_start: *arena.loc_start(pvb_pat.ppat_loc),
                            loc_end: *arena.loc_end(inner_typ_loc),
                            loc_ghost: false,
                            origin: Default::default(),
                        });
                        let expr_loc = arena.get_expr(expr_idx).pexp_loc;
                        (new_pat_loc, expr_idx, expr_loc)
                    } else {
                        default
                    }
                } else {
                    default
                }
            } else {
                default
            }
        }

        _ => default,
    }
}

fn walk_value_binding(
    vb: &ValueBinding,
    t: &mut CommentTable,
    comments: Vec<Comment>,
    arena: &mut ParseArena,
) {
    // res_comments_table.ml:911-930: `pvb_constraint = Some {pvc_newtypes;
    // pvc_type}` walks the pattern, each newtype name, then the type, and
    // continues with the expression after the type.
    if let Some(constraint) = arena.value_constraint(vb.pvb_pat).cloned() {
        let pvb_pat = arena.get_pat(vb.pvb_pat).clone();
        let (leading, inside, trailing) = partition_by_loc(comments, pvb_pat.ppat_loc, arena);
        t.attach_leading(pvb_pat.ppat_loc, leading, arena);
        walk_pattern(&pvb_pat, t, inside, arena);
        let (after_pattern, rest) = partition_adjacent_trailing(pvb_pat.ppat_loc, trailing, arena);
        t.attach_trailing(pvb_pat.ppat_loc, after_pattern, arena);
        let rest = visit_list_but_continue_with_remaining_comments(
            &constraint.pvc_newtypes,
            |newtype, _| newtype.loc,
            |newtype, t, comments, arena| {
                let (leading, trailing) = partition_leading_trailing(comments, newtype.loc, arena);
                t.attach_leading(newtype.loc, leading, arena);
                t.attach_trailing(newtype.loc, trailing, arena);
            },
            t,
            rest,
            false,
            arena,
        );
        let typ = arena.get_core_type(constraint.pvc_type).clone();
        let (before_type, inside_type, after_type) = partition_by_loc(rest, typ.ptyp_loc, arena);
        t.attach_leading(typ.ptyp_loc, before_type, arena);
        walk_core_type(&typ, t, inside_type, arena);
        // `walk_expression_after pvc_type.ptyp_loc vb.pvb_expr after_type`.
        let (after_previous, surrounding_expr) =
            partition_adjacent_trailing(typ.ptyp_loc, after_type, arena);
        t.attach_trailing(typ.ptyp_loc, after_previous, arena);
        let expr = arena.get_expr(vb.pvb_expr).clone();
        let (before_expr, inside_expr, after_expr) =
            partition_by_loc(surrounding_expr, expr.pexp_loc, arena);
        if is_block_expr(arena, &expr) {
            let combined: Vec<Comment> = before_expr
                .into_iter()
                .chain(inside_expr)
                .chain(after_expr)
                .collect();
            walk_expression(&expr, t, combined, arena);
        } else {
            t.attach_leading(expr.pexp_loc, before_expr, arena);
            walk_expression(&expr, t, inside_expr, arena);
            t.attach_trailing(expr.pexp_loc, after_expr, arena);
        }
        return;
    }
    // OCaml rewrites value binding locations for sugar cases to properly partition comments.
    // This is necessary because the AST locations for sugar forms span the entire binding,
    // which causes all comments to be "inside" the pattern and none for the expression.
    let (pattern_loc, expr_idx, expr_loc) = rewrite_value_binding_locs(vb, arena);

    let (leading, inside, trailing) = partition_by_loc(comments, pattern_loc, arena);

    // Everything before start of pattern can only be leading on the pattern
    t.attach_leading(pattern_loc, leading, arena);
    // Safety: arena is append-only, pattern won't be invalidated
    let pvb_pat = arena.get_pat(vb.pvb_pat).clone();
    walk_pattern(&pvb_pat, t, inside, arena);

    let (after_pat, surrounding_expr) = partition_adjacent_trailing(pattern_loc, trailing, arena);
    t.attach_trailing(pattern_loc, after_pat, arena);

    let (before_expr, inside_expr, after_expr) =
        partition_by_loc(surrounding_expr, expr_loc, arena);

    let expr = arena.get_expr(expr_idx).clone();
    if is_block_expr(arena, &expr) {
        let combined: Vec<Comment> = before_expr
            .into_iter()
            .chain(inside_expr)
            .chain(after_expr)
            .collect();
        walk_expression(&expr, t, combined, arena);
    } else {
        t.attach_leading(expr_loc, before_expr, arena);
        walk_expression(&expr, t, inside_expr, arena);
        t.attach_trailing(expr_loc, after_expr, arena);
    }
}

fn walk_type_declaration(
    td: &TypeDeclaration,
    t: &mut CommentTable,
    comments: Vec<Comment>,
    arena: &mut ParseArena,
) {
    let (before_name, rest) = partition_leading_trailing(comments, td.ptype_name.loc, arena);
    t.attach_leading(td.ptype_name.loc, before_name, arena);

    let (after_name, rest) = partition_adjacent_trailing(td.ptype_name.loc, rest, arena);
    t.attach_trailing(td.ptype_name.loc, after_name, arena);

    // Type params
    let rest = if td.ptype_params.is_empty() {
        rest
    } else {
        visit_list_but_continue_with_remaining_comments(
            &td.ptype_params,
            |param, arena| arena.get_core_type(param.0).ptyp_loc,
            |param, t, comments, arena| {
                // Safety: arena is append-only, core type won't be invalidated
                let ct = arena.get_core_type(param.0).clone();
                walk_core_type(&ct, t, comments, arena);
            },
            t,
            rest,
            false,
            arena,
        )
    };

    // Manifest: = typexpr
    let rest = match &td.ptype_manifest {
        Some(typexpr_idx) => {
            let typexpr_loc = arena.get_core_type(*typexpr_idx).ptyp_loc;
            let (before_typ, inside_typ, after_typ) = partition_by_loc(rest, typexpr_loc, arena);
            t.attach_leading(typexpr_loc, before_typ, arena);
            // Safety: arena is append-only, core type won't be invalidated
            let typexpr = arena.get_core_type(*typexpr_idx).clone();
            walk_core_type(&typexpr, t, inside_typ, arena);
            let (after_typ_adj, rest) = partition_adjacent_trailing(typexpr_loc, after_typ, arena);
            t.attach_trailing(typexpr_loc, after_typ_adj, arena);
            rest
        }
        None => rest,
    };

    let rest = match &td.ptype_kind {
        TypeKind::Ptype_abstract | TypeKind::Ptype_open => rest,
        TypeKind::Ptype_record(lds) => {
            if lds.is_empty() {
                t.attach_inside(td.ptype_loc, rest, arena);
                Vec::new()
            } else {
                let nodes: Vec<Node<'_>> = lds.iter().map(Node::LabelDeclaration).collect();
                walk_list(&nodes, t, rest, arena);
                Vec::new()
            }
        }
        TypeKind::Ptype_variant(cds) => walk_constructor_declarations(cds, t, rest, arena),
    };

    t.attach_trailing(td.ptype_loc, rest, arena);
}

fn walk_label_declaration(
    ld: &LabelDeclaration,
    t: &mut CommentTable,
    comments: Vec<Comment>,
    arena: &mut ParseArena,
) {
    let (before_name, rest) = partition_leading_trailing(comments, ld.pld_name.loc, arena);
    t.attach_leading(ld.pld_name.loc, before_name, arena);

    let (after_name, rest) = partition_adjacent_trailing(ld.pld_name.loc, rest, arena);
    t.attach_trailing(ld.pld_name.loc, after_name, arena);

    let pld_type_loc = arena.get_core_type(ld.pld_type).ptyp_loc;
    let (before_typ, inside_typ, after_typ) = partition_by_loc(rest, pld_type_loc, arena);
    t.attach_leading(pld_type_loc, before_typ, arena);
    // Safety: arena is append-only, core type won't be invalidated
    let pld_type = arena.get_core_type(ld.pld_type).clone();
    walk_core_type(&pld_type, t, inside_typ, arena);
    t.attach_trailing(pld_type_loc, after_typ, arena);
}

fn walk_constructor_declarations(
    cds: &[ConstructorDeclaration],
    t: &mut CommentTable,
    comments: Vec<Comment>,
    arena: &mut ParseArena,
) -> Vec<Comment> {
    visit_list_but_continue_with_remaining_comments(
        cds,
        |cd, _arena| cd.pcd_loc,
        walk_constructor_declaration,
        t,
        comments,
        false,
        arena,
    )
}

fn walk_constructor_declaration(
    cd: &ConstructorDeclaration,
    t: &mut CommentTable,
    comments: Vec<Comment>,
    arena: &mut ParseArena,
) {
    let (before_name, rest) = partition_leading_trailing(comments, cd.pcd_name.loc, arena);
    t.attach_leading(cd.pcd_name.loc, before_name, arena);

    let (after_name, rest) = partition_adjacent_trailing(cd.pcd_name.loc, rest, arena);
    t.attach_trailing(cd.pcd_name.loc, after_name, arena);

    let rest = walk_constructor_arguments(&cd.pcd_args, t, rest, arena);

    let rest = match &cd.pcd_res {
        Some(typexpr_idx) => {
            let typexpr_loc = arena.get_core_type(*typexpr_idx).ptyp_loc;
            let (before_typ, inside_typ, after_typ) = partition_by_loc(rest, typexpr_loc, arena);
            t.attach_leading(typexpr_loc, before_typ, arena);
            // Safety: arena is append-only, core type won't be invalidated
            let typexpr = arena.get_core_type(*typexpr_idx).clone();
            walk_core_type(&typexpr, t, inside_typ, arena);
            let (after_typ_adj, rest) = partition_adjacent_trailing(typexpr_loc, after_typ, arena);
            t.attach_trailing(typexpr_loc, after_typ_adj, arena);
            rest
        }
        None => rest,
    };

    t.attach_trailing(cd.pcd_loc, rest, arena);
}

fn walk_constructor_arguments(
    args: &ConstructorArguments,
    t: &mut CommentTable,
    comments: Vec<Comment>,
    arena: &mut ParseArena,
) -> Vec<Comment> {
    match args {
        ConstructorArguments::Pcstr_tuple(typexprs) => {
            visit_list_but_continue_with_remaining_comments(
                typexprs,
                |te_idx, arena| arena.get_core_type(*te_idx).ptyp_loc,
                |te_idx, t, comments, arena| {
                    // Safety: arena is append-only, core type won't be invalidated
                    let te = arena.get_core_type(*te_idx).clone();
                    walk_core_type(&te, t, comments, arena);
                },
                t,
                comments,
                false,
                arena,
            )
        }
        ConstructorArguments::Pcstr_record(lds) => visit_list_but_continue_with_remaining_comments(
            lds,
            |ld, _arena| ld.pld_loc,
            walk_label_declaration,
            t,
            comments,
            false,
            arena,
        ),
    }
}

fn walk_extension_constructor(
    ec: &ExtensionConstructor,
    t: &mut CommentTable,
    comments: Vec<Comment>,
    arena: &mut ParseArena,
) {
    let (leading, trailing) = partition_leading_trailing(comments, ec.pext_name.loc, arena);
    t.attach_leading(ec.pext_name.loc, leading, arena);

    let (after_name, rest) = partition_adjacent_trailing(ec.pext_name.loc, trailing, arena);
    t.attach_trailing(ec.pext_name.loc, after_name, arena);

    match &ec.pext_kind {
        ExtensionConstructorKind::Pext_decl(args, res) => {
            let rest = walk_constructor_arguments(args, t, rest, arena);
            if let Some(typexpr_idx) = res {
                let typexpr_loc = arena.get_core_type(*typexpr_idx).ptyp_loc;
                let (before_typ, inside_typ, after_typ) =
                    partition_by_loc(rest, typexpr_loc, arena);
                t.attach_leading(typexpr_loc, before_typ, arena);
                // Safety: arena is append-only, core type won't be invalidated
                let typexpr = arena.get_core_type(*typexpr_idx).clone();
                walk_core_type(&typexpr, t, inside_typ, arena);
                t.attach_trailing(typexpr_loc, after_typ, arena);
            }
        }
        ExtensionConstructorKind::Pext_rebind(lid) => {
            let (leading, trailing) = partition_leading_trailing(rest, lid.loc, arena);
            t.attach_leading(lid.loc, leading, arena);
            t.attach_trailing(lid.loc, trailing, arena);
        }
    }
}

fn walk_expression(
    expr: &Expression,
    t: &mut CommentTable,
    comments: Vec<Comment>,
    arena: &mut ParseArena,
) {
    if comments.is_empty() {
        return;
    }

    match &expr.pexp_desc {
        ExpressionDesc::Pexp_braces(braces) if is_block_expr_idx(arena, braces.expr) => {
            let inner = arena.get_expr(braces.expr).clone();
            walk_expression(&inner, t, comments, arena);
        }
        ExpressionDesc::Pexp_braces(braces) => {
            let inner = arena.get_expr(braces.expr).clone();
            let (before, inside, after) = partition_by_loc(comments, inner.pexp_loc, arena);
            t.attach_leading(inner.pexp_loc, before, arena);
            walk_expression(&inner, t, inside, arena);
            t.attach_trailing(inner.pexp_loc, after, arena);
        }
        ExpressionDesc::Pexp_constant { .. }
        | ExpressionDesc::Pexp_regexp(_)
        | ExpressionDesc::Pexp_break
        | ExpressionDesc::Pexp_continue => {
            let (leading, trailing) = partition_leading_trailing(comments, expr.pexp_loc, arena);
            t.attach_leading(expr.pexp_loc, leading, arena);
            t.attach_trailing(expr.pexp_loc, trailing, arena);
        }
        ExpressionDesc::Pexp_ident(longident) => {
            let (leading, trailing) = partition_leading_trailing(comments, longident.loc, arena);
            t.attach_leading(longident.loc, leading, arena);
            t.attach_trailing(longident.loc, trailing, arena);
        }
        ExpressionDesc::Pexp_let(inner) => {
            let (_, ref bindings, ref body_idx) = **inner;
            // Safety: arena is append-only, expression won't be invalidated
            let body = arena.get_expr(*body_idx).clone();
            // Check if body is unit
            let body_is_unit = matches!(&body.pexp_desc, ExpressionDesc::Pexp_construct(name, args) if arena.is_lident(name.txt, "()") && args.txt.is_empty());
            if body_is_unit {
                walk_value_bindings(bindings, t, comments, arena);
            } else {
                let comments = visit_list_but_continue_with_remaining_comments(
                    bindings,
                    |vb, arena| {
                        let pvb_pat = arena.get_pat(vb.pvb_pat);
                        if arena.loc_ghost(pvb_pat.ppat_loc) {
                            arena.get_expr(vb.pvb_expr).pexp_loc
                        } else {
                            vb.pvb_loc
                        }
                    },
                    walk_value_binding,
                    t,
                    comments,
                    true,
                    arena,
                );

                if is_block_expr(arena, &body) {
                    walk_expression(&body, t, comments, arena);
                } else {
                    let (leading, inside, trailing) =
                        partition_by_loc(comments, body.pexp_loc, arena);
                    t.attach_leading(body.pexp_loc, leading, arena);
                    walk_expression(&body, t, inside, arena);
                    t.attach_trailing(body.pexp_loc, trailing, arena);
                }
            }
        }
        ExpressionDesc::Pexp_sequence(lhs_idx, rhs_idx) => {
            // Safety: arena is append-only, expressions won't be invalidated
            let lhs = arena.get_expr(*lhs_idx).clone();
            let rhs = arena.get_expr(*rhs_idx).clone();
            let (leading, inside, trailing) = partition_by_loc(comments, lhs.pexp_loc, arena);

            let comments = if is_block_expr(arena, &lhs) {
                let (after_expr, comments) =
                    partition_by_on_same_line(lhs.pexp_loc, trailing, arena);
                let combined: Vec<Comment> = leading
                    .into_iter()
                    .chain(inside)
                    .chain(after_expr)
                    .collect();
                walk_expression(&lhs, t, combined, arena);
                comments
            } else {
                t.attach_leading(lhs.pexp_loc, leading, arena);
                walk_expression(&lhs, t, inside, arena);
                let (after_expr, comments) =
                    partition_by_on_same_line(lhs.pexp_loc, trailing, arena);
                t.attach_trailing(lhs.pexp_loc, after_expr, arena);
                comments
            };

            if is_block_expr(arena, &rhs) {
                walk_expression(&rhs, t, comments, arena);
            } else {
                let (leading, inside, trailing) = partition_by_loc(comments, rhs.pexp_loc, arena);
                t.attach_leading(rhs.pexp_loc, leading, arena);
                walk_expression(&rhs, t, inside, arena);
                t.attach_trailing(rhs.pexp_loc, trailing, arena);
            }
        }
        ExpressionDesc::Pexp_open(inner) => {
            let (_, ref lid, ref body_idx) = **inner;
            // Safety: arena is append-only, expression won't be invalidated
            let body = arena.get_expr(*body_idx).clone();
            let (leading, comments) = partition_leading_trailing(comments, expr.pexp_loc, arena);
            let combined_loc = arena.from_location(&Location::from_positions(
                *arena.loc_start(expr.pexp_loc),
                *arena.loc_end(lid.loc),
            ));
            t.attach_leading(combined_loc, leading, arena);

            let (leading, trailing) = partition_leading_trailing(comments, lid.loc, arena);
            t.attach_leading(lid.loc, leading, arena);

            let (after_longident, rest) = partition_by_on_same_line(lid.loc, trailing, arena);
            t.attach_trailing(lid.loc, after_longident, arena);

            if is_block_expr(arena, &body) {
                walk_expression(&body, t, rest, arena);
            } else {
                let (leading, inside, trailing) = partition_by_loc(rest, body.pexp_loc, arena);
                t.attach_leading(body.pexp_loc, leading, arena);
                walk_expression(&body, t, inside, arena);
                t.attach_trailing(body.pexp_loc, trailing, arena);
            }
        }
        ExpressionDesc::Pexp_object_literal(fields) => {
            // `ExprRecordRow (Location.mkloc (Longident.Lident s.txt) s.loc, e)`
            let rows: Vec<(Loc<LidentIdx>, ExprIdx)> = fields
                .iter()
                .map(|(name, e)| {
                    let name_idx = arena.intern(&name.txt);
                    let lid = arena.push_longident(Longident::Lident(name_idx));
                    (
                        Loc {
                            txt: lid,
                            loc: name.loc,
                        },
                        *e,
                    )
                })
                .collect();
            let nodes: Vec<Node<'_>> = rows
                .iter()
                .map(|(lid, e)| Node::ExprRecordRow(lid, *e))
                .collect();
            walk_list(&nodes, t, comments, arena);
        }
        ExpressionDesc::Pexp_extension(ext) => walk_extension(ext, t, comments, arena),
        ExpressionDesc::Pexp_letexception(inner) => {
            let (ref ext, ref body_idx) = **inner;
            // Safety: arena is append-only, expression won't be invalidated
            let body = arena.get_expr(*body_idx).clone();
            let (leading, comments) = partition_leading_trailing(comments, expr.pexp_loc, arena);
            let combined_loc = arena.from_location(&Location::from_positions(
                *arena.loc_start(expr.pexp_loc),
                *arena.loc_end(ext.pext_loc),
            ));
            t.attach_leading(combined_loc, leading, arena);

            let (leading, inside, trailing) = partition_by_loc(comments, ext.pext_loc, arena);
            t.attach_leading(ext.pext_loc, leading, arena);
            walk_extension_constructor(ext, t, inside, arena);

            let (after_ext_constr, rest) = partition_by_on_same_line(ext.pext_loc, trailing, arena);
            t.attach_trailing(ext.pext_loc, after_ext_constr, arena);

            if is_block_expr(arena, &body) {
                walk_expression(&body, t, rest, arena);
            } else {
                let (leading, inside, trailing) = partition_by_loc(rest, body.pexp_loc, arena);
                t.attach_leading(body.pexp_loc, leading, arena);
                walk_expression(&body, t, inside, arena);
                t.attach_trailing(body.pexp_loc, trailing, arena);
            }
        }
        ExpressionDesc::Pexp_letmodule(inner) => {
            let (ref name, ref module_idx, ref body_idx) = **inner;
            // Safety: arena is append-only, expression won't be invalidated
            let body = arena.get_expr(*body_idx).clone();
            let module = arena.get_mod_expr(*module_idx);
            let module_loc = module.pmod_loc;
            let (leading, comments) = partition_leading_trailing(comments, expr.pexp_loc, arena);
            let combined_loc = arena.from_location(&Location::from_positions(
                *arena.loc_start(expr.pexp_loc),
                *arena.loc_end(module_loc),
            ));
            t.attach_leading(combined_loc, leading, arena);

            let (leading, trailing) = partition_leading_trailing(comments, name.loc, arena);
            t.attach_leading(name.loc, leading, arena);

            let (after_string, rest) = partition_adjacent_trailing(name.loc, trailing, arena);
            t.attach_trailing(name.loc, after_string, arena);

            let (before_mod_expr, inside_mod_expr, after_mod_expr) =
                partition_by_loc(rest, module_loc, arena);
            t.attach_leading(module_loc, before_mod_expr, arena);
            // Safety: arena is append-only, module expression won't be invalidated
            let module = arena.get_mod_expr(*module_idx).clone();
            walk_module_expr(&module, t, inside_mod_expr, arena);

            let (after_mod_expr_adj, rest) =
                partition_by_on_same_line(module_loc, after_mod_expr, arena);
            t.attach_trailing(module_loc, after_mod_expr_adj, arena);

            if is_block_expr(arena, &body) {
                walk_expression(&body, t, rest, arena);
            } else {
                let (leading, inside, trailing) = partition_by_loc(rest, body.pexp_loc, arena);
                t.attach_leading(body.pexp_loc, leading, arena);
                walk_expression(&body, t, inside, arena);
                t.attach_trailing(body.pexp_loc, trailing, arena);
            }
        }
        ExpressionDesc::Pexp_assert(inner_idx) => {
            // Safety: arena is append-only, expression won't be invalidated
            let inner = arena.get_expr(*inner_idx).clone();
            if is_block_expr(arena, &inner) {
                walk_expression(&inner, t, comments, arena);
            } else {
                let (leading, inside, trailing) = partition_by_loc(comments, inner.pexp_loc, arena);
                t.attach_leading(inner.pexp_loc, leading, arena);
                walk_expression(&inner, t, inside, arena);
                t.attach_trailing(inner.pexp_loc, trailing, arena);
            }
        }
        ExpressionDesc::Pexp_coerce(coerce_inner) => {
            let (ref inner_idx, _, ref typ_idx) = **coerce_inner;
            // Safety: arena is append-only, expression won't be invalidated
            let inner = arena.get_expr(*inner_idx).clone();
            let (leading, inside, trailing) = partition_by_loc(comments, inner.pexp_loc, arena);
            t.attach_leading(inner.pexp_loc, leading, arena);
            walk_expression(&inner, t, inside, arena);

            let (after_expr, rest) = partition_adjacent_trailing(inner.pexp_loc, trailing, arena);
            t.attach_trailing(inner.pexp_loc, after_expr, arena);

            let typ_loc = arena.get_core_type(*typ_idx).ptyp_loc;
            let (leading, inside, trailing) = partition_by_loc(rest, typ_loc, arena);
            t.attach_leading(typ_loc, leading, arena);
            // Safety: arena is append-only, core type won't be invalidated
            let typ = arena.get_core_type(*typ_idx).clone();
            walk_core_type(&typ, t, inside, arena);
            t.attach_trailing(typ_loc, trailing, arena);
        }
        ExpressionDesc::Pexp_constraint(constraint_inner) => {
            let (ref inner_idx, ref typ_idx) = **constraint_inner;
            // Safety: arena is append-only, expression won't be invalidated
            let inner = arena.get_expr(*inner_idx).clone();
            let (leading, inside, trailing) = partition_by_loc(comments, inner.pexp_loc, arena);
            t.attach_leading(inner.pexp_loc, leading, arena);
            walk_expression(&inner, t, inside, arena);

            let (after_expr, rest) = partition_adjacent_trailing(inner.pexp_loc, trailing, arena);
            t.attach_trailing(inner.pexp_loc, after_expr, arena);

            let typ_loc = arena.get_core_type(*typ_idx).ptyp_loc;
            let (leading, inside, trailing) = partition_by_loc(rest, typ_loc, arena);
            t.attach_leading(typ_loc, leading, arena);
            // Safety: arena is append-only, core type won't be invalidated
            let typ = arena.get_core_type(*typ_idx).clone();
            walk_core_type(&typ, t, inside, arena);
            t.attach_trailing(typ_loc, trailing, arena);
        }
        ExpressionDesc::Pexp_tuple(exprs) if exprs.is_empty() => {
            t.attach_inside(expr.pexp_loc, comments, arena);
        }
        ExpressionDesc::Pexp_array(exprs) if exprs.is_empty() => {
            t.attach_inside(expr.pexp_loc, comments, arena);
        }
        ExpressionDesc::Pexp_construct(name, _) if arena.is_lident(name.txt, "[]") => {
            t.attach_inside(expr.pexp_loc, comments, arena);
        }
        ExpressionDesc::Pexp_construct(name, _) if arena.is_lident(name.txt, "::") => {
            let list_exprs = collect_list_exprs(arena, expr);
            let nodes: Vec<Node<'_>> = list_exprs.iter().map(Node::Expression).collect();
            walk_list(&nodes, t, comments, arena);
        }
        ExpressionDesc::Pexp_construct(name, args) => {
            let (leading, trailing) = partition_leading_trailing(comments, name.loc, arena);
            t.attach_leading(name.loc, leading, arena);

            if args.txt.is_empty() {
                t.attach_trailing(name.loc, trailing, arena);
            } else {
                let (after_longident, rest) =
                    partition_adjacent_trailing(name.loc, trailing, arena);
                t.attach_trailing(name.loc, after_longident, arena);
                let nodes: Vec<Node<'_>> =
                    args.txt.iter().map(|e| Node::ExpressionIdx(*e)).collect();
                walk_list(&nodes, t, rest, arena);
            }
        }
        ExpressionDesc::Pexp_variant(inner) => {
            let nodes: Vec<Node<'_>> = inner
                .1
                .txt
                .iter()
                .map(|e| Node::ExpressionIdx(*e))
                .collect();
            walk_list(&nodes, t, comments, arena);
        }
        ExpressionDesc::Pexp_array(exprs) | ExpressionDesc::Pexp_tuple(exprs) => {
            let nodes: Vec<Node<'_>> = exprs.iter().map(|e| Node::ExpressionIdx(*e)).collect();
            walk_list(&nodes, t, comments, arena);
        }
        ExpressionDesc::Pexp_record(inner) => {
            let (ref fields, ref spread_idx) = **inner;
            if fields.is_empty() {
                t.attach_inside(expr.pexp_loc, comments, arena);
            } else {
                let comments = match spread_idx {
                    None => comments,
                    Some(spread_expr_idx) => {
                        // Safety: arena is append-only, expression won't be invalidated
                        let spread_expr = arena.get_expr(*spread_expr_idx).clone();
                        let (leading, inside, trailing) =
                            partition_by_loc(comments, spread_expr.pexp_loc, arena);
                        t.attach_leading(spread_expr.pexp_loc, leading, arena);
                        walk_expression(&spread_expr, t, inside, arena);
                        let (after_expr, rest) =
                            partition_adjacent_trailing(spread_expr.pexp_loc, trailing, arena);
                        t.attach_trailing(spread_expr.pexp_loc, after_expr, arena);
                        rest
                    }
                };

                let nodes: Vec<Node<'_>> = fields
                    .iter()
                    .map(|f| Node::ExprRecordRow(&f.lid, f.expr))
                    .collect();
                walk_list(&nodes, t, comments, arena);
            }
        }
        ExpressionDesc::Pexp_field(inner_idx, lid) => {
            // Safety: arena is append-only, expression won't be invalidated
            let inner = arena.get_expr(*inner_idx).clone();
            let (leading, inside, trailing) = partition_by_loc(comments, inner.pexp_loc, arena);

            let trailing = if is_block_expr(arena, &inner) {
                let (after_expr, rest) =
                    partition_adjacent_trailing(inner.pexp_loc, trailing, arena);
                let combined: Vec<Comment> = leading
                    .into_iter()
                    .chain(inside)
                    .chain(after_expr)
                    .collect();
                walk_expression(&inner, t, combined, arena);
                rest
            } else {
                t.attach_leading(inner.pexp_loc, leading, arena);
                walk_expression(&inner, t, inside, arena);
                trailing
            };

            let (after_expr, rest) = partition_adjacent_trailing(inner.pexp_loc, trailing, arena);
            t.attach_trailing(inner.pexp_loc, after_expr, arena);

            let (leading, trailing) = partition_leading_trailing(rest, lid.loc, arena);
            t.attach_leading(lid.loc, leading, arena);
            t.attach_trailing(lid.loc, trailing, arena);
        }
        ExpressionDesc::Pexp_setfield(setfield_inner) => {
            let (ref obj_idx, ref lid, ref value_idx) = **setfield_inner;
            // Safety: arena is append-only, expressions won't be invalidated
            let obj = arena.get_expr(*obj_idx).clone();
            let value = arena.get_expr(*value_idx).clone();
            let (leading, inside, trailing) = partition_by_loc(comments, obj.pexp_loc, arena);

            let rest = if is_block_expr(arena, &obj) {
                let (after_expr, rest) = partition_adjacent_trailing(obj.pexp_loc, trailing, arena);
                let combined: Vec<Comment> = leading
                    .into_iter()
                    .chain(inside)
                    .chain(after_expr)
                    .collect();
                walk_expression(&obj, t, combined, arena);
                rest
            } else {
                let (after_expr, rest) = partition_adjacent_trailing(obj.pexp_loc, trailing, arena);
                t.attach_leading(obj.pexp_loc, leading, arena);
                walk_expression(&obj, t, inside, arena);
                t.attach_trailing(obj.pexp_loc, after_expr, arena);
                rest
            };

            let (before_longident, after_longident) =
                partition_leading_trailing(rest, lid.loc, arena);
            t.attach_leading(lid.loc, before_longident, arena);

            let (after_longident_adj, rest) =
                partition_adjacent_trailing(lid.loc, after_longident, arena);
            t.attach_trailing(lid.loc, after_longident_adj, arena);

            if is_block_expr(arena, &value) {
                walk_expression(&value, t, rest, arena);
            } else {
                let (leading, inside, trailing) = partition_by_loc(rest, value.pexp_loc, arena);
                t.attach_leading(value.pexp_loc, leading, arena);
                walk_expression(&value, t, inside, arena);
                t.attach_trailing(value.pexp_loc, trailing, arena);
            }
        }
        ExpressionDesc::Pexp_ifthenelse(_) | ExpressionDesc::Pexp_ternary(_) => {
            let (cond_idx, then_idx, else_idx) = match &expr.pexp_desc {
                ExpressionDesc::Pexp_ifthenelse(inner) => (&inner.0, &inner.1, inner.2),
                ExpressionDesc::Pexp_ternary(inner) => (&inner.0, &inner.1, Some(inner.2)),
                _ => unreachable!(),
            };
            // Safety: arena is append-only, expressions won't be invalidated
            let cond = arena.get_expr(*cond_idx).clone();
            let then_branch = arena.get_expr(*then_idx).clone();
            let (leading, rest) = partition_leading_trailing(comments, expr.pexp_loc, arena);
            t.attach_leading(expr.pexp_loc, leading, arena);

            let (leading, inside, trailing) = partition_by_loc(rest, cond.pexp_loc, arena);

            let comments = if is_block_expr(arena, &cond) {
                let (after_expr, comments) =
                    partition_adjacent_trailing(cond.pexp_loc, trailing, arena);
                let combined: Vec<Comment> = leading
                    .into_iter()
                    .chain(inside)
                    .chain(after_expr)
                    .collect();
                walk_expression(&cond, t, combined, arena);
                comments
            } else {
                t.attach_leading(cond.pexp_loc, leading, arena);
                walk_expression(&cond, t, inside, arena);
                let (after_expr, comments) =
                    partition_adjacent_trailing(cond.pexp_loc, trailing, arena);
                t.attach_trailing(cond.pexp_loc, after_expr, arena);
                comments
            };

            let (leading, inside, trailing) =
                partition_by_loc(comments, then_branch.pexp_loc, arena);

            let comments = if is_block_expr(arena, &then_branch) {
                let (after_expr, trailing) =
                    partition_adjacent_trailing(then_branch.pexp_loc, trailing, arena);
                let combined: Vec<Comment> = leading
                    .into_iter()
                    .chain(inside)
                    .chain(after_expr)
                    .collect();
                walk_expression(&then_branch, t, combined, arena);
                trailing
            } else {
                t.attach_leading(then_branch.pexp_loc, leading, arena);
                walk_expression(&then_branch, t, inside, arena);
                let (after_expr, comments) =
                    partition_adjacent_trailing(then_branch.pexp_loc, trailing, arena);
                t.attach_trailing(then_branch.pexp_loc, after_expr, arena);
                comments
            };

            if let Some(else_expr_idx) = else_idx {
                // Safety: arena is append-only
                let else_expr = arena.get_expr(else_expr_idx).clone();
                if is_block_expr(arena, &else_expr) || is_conditional_expr(&else_expr) {
                    walk_expression(&else_expr, t, comments, arena);
                } else {
                    let (leading, inside, trailing) =
                        partition_by_loc(comments, else_expr.pexp_loc, arena);
                    t.attach_leading(else_expr.pexp_loc, leading, arena);
                    walk_expression(&else_expr, t, inside, arena);
                    t.attach_trailing(else_expr.pexp_loc, trailing, arena);
                }
            }
        }
        ExpressionDesc::Pexp_while(cond_idx, body_idx) => {
            // Safety: arena is append-only, expressions won't be invalidated
            let cond = arena.get_expr(*cond_idx).clone();
            let body = arena.get_expr(*body_idx).clone();
            let (leading, inside, trailing) = partition_by_loc(comments, cond.pexp_loc, arena);

            let rest = if is_block_expr(arena, &cond) {
                let (after_expr, rest) =
                    partition_adjacent_trailing(cond.pexp_loc, trailing, arena);
                let combined: Vec<Comment> = leading
                    .into_iter()
                    .chain(inside)
                    .chain(after_expr)
                    .collect();
                walk_expression(&cond, t, combined, arena);
                rest
            } else {
                t.attach_leading(cond.pexp_loc, leading, arena);
                walk_expression(&cond, t, inside, arena);
                let (after_expr, rest) =
                    partition_adjacent_trailing(cond.pexp_loc, trailing, arena);
                t.attach_trailing(cond.pexp_loc, after_expr, arena);
                rest
            };

            if is_block_expr(arena, &body) {
                walk_expression(&body, t, rest, arena);
            } else {
                let (leading, inside, trailing) = partition_by_loc(rest, body.pexp_loc, arena);
                t.attach_leading(body.pexp_loc, leading, arena);
                walk_expression(&body, t, inside, arena);
                t.attach_trailing(body.pexp_loc, trailing, arena);
            }
        }
        ExpressionDesc::Pexp_for_of(for_inner) | ExpressionDesc::Pexp_for_await_of(for_inner) => {
            let (ref pat_idx, ref iterable_idx, ref body_idx) = **for_inner;
            // Safety: arena is append-only, expressions/patterns won't be invalidated
            let iterable = arena.get_expr(*iterable_idx).clone();
            let body = arena.get_expr(*body_idx).clone();
            let pat = arena.get_pat(*pat_idx).clone();

            let (leading, inside, trailing) = partition_by_loc(comments, pat.ppat_loc, arena);
            t.attach_leading(pat.ppat_loc, leading, arena);
            walk_pattern(&pat, t, inside, arena);
            let (after_pat, rest) = partition_adjacent_trailing(pat.ppat_loc, trailing, arena);
            t.attach_trailing(pat.ppat_loc, after_pat, arena);

            let (leading, inside, trailing) = partition_by_loc(rest, iterable.pexp_loc, arena);
            t.attach_leading(iterable.pexp_loc, leading, arena);
            walk_expression(&iterable, t, inside, arena);
            let (after_expr, rest) =
                partition_adjacent_trailing(iterable.pexp_loc, trailing, arena);
            t.attach_trailing(iterable.pexp_loc, after_expr, arena);

            if is_block_expr(arena, &body) {
                walk_expression(&body, t, rest, arena);
            } else {
                let (leading, inside, trailing) = partition_by_loc(rest, body.pexp_loc, arena);
                t.attach_leading(body.pexp_loc, leading, arena);
                walk_expression(&body, t, inside, arena);
                t.attach_trailing(body.pexp_loc, trailing, arena);
            }
        }
        ExpressionDesc::Pexp_for(for_inner) => {
            let (ref pat_idx, ref from_idx, ref to_idx, _, ref body_idx) = **for_inner;
            // Safety: arena is append-only, expressions/patterns won't be invalidated
            let from = arena.get_expr(*from_idx).clone();
            let to = arena.get_expr(*to_idx).clone();
            let body = arena.get_expr(*body_idx).clone();
            let pat = arena.get_pat(*pat_idx).clone();
            let (leading, inside, trailing) = partition_by_loc(comments, pat.ppat_loc, arena);
            t.attach_leading(pat.ppat_loc, leading, arena);
            walk_pattern(&pat, t, inside, arena);

            let (after_pat, rest) = partition_adjacent_trailing(pat.ppat_loc, trailing, arena);
            t.attach_trailing(pat.ppat_loc, after_pat, arena);

            let (leading, inside, trailing) = partition_by_loc(rest, from.pexp_loc, arena);
            t.attach_leading(from.pexp_loc, leading, arena);
            walk_expression(&from, t, inside, arena);

            let (after_expr, rest) = partition_adjacent_trailing(from.pexp_loc, trailing, arena);
            t.attach_trailing(from.pexp_loc, after_expr, arena);

            let (leading, inside, trailing) = partition_by_loc(rest, to.pexp_loc, arena);
            t.attach_leading(to.pexp_loc, leading, arena);
            walk_expression(&to, t, inside, arena);

            let (after_expr, rest) = partition_adjacent_trailing(to.pexp_loc, trailing, arena);
            t.attach_trailing(to.pexp_loc, after_expr, arena);

            if is_block_expr(arena, &body) {
                walk_expression(&body, t, rest, arena);
            } else {
                let (leading, inside, trailing) = partition_by_loc(rest, body.pexp_loc, arena);
                t.attach_leading(body.pexp_loc, leading, arena);
                walk_expression(&body, t, inside, arena);
                t.attach_trailing(body.pexp_loc, trailing, arena);
            }
        }
        ExpressionDesc::Pexp_pack(mod_expr_idx) => {
            // Safety: arena is append-only, module expression won't be invalidated
            let mod_expr = arena.get_mod_expr(*mod_expr_idx).clone();
            let (before, inside, after) = partition_by_loc(comments, mod_expr.pmod_loc, arena);
            t.attach_leading(mod_expr.pmod_loc, before, arena);
            walk_module_expr(&mod_expr, t, inside, arena);
            t.attach_trailing(mod_expr.pmod_loc, after, arena);
        }
        ExpressionDesc::Pexp_match(inner) | ExpressionDesc::Pexp_try(inner) => {
            let (ref match_expr_idx, ref cases) = **inner;
            // Safety: arena is append-only, expression won't be invalidated
            let match_expr = arena.get_expr(*match_expr_idx).clone();
            let (before, inside, after) = partition_by_loc(comments, match_expr.pexp_loc, arena);

            let after = if is_block_expr(arena, &match_expr) {
                let (after_expr, rest) =
                    partition_adjacent_trailing(match_expr.pexp_loc, after, arena);
                let combined: Vec<Comment> =
                    before.into_iter().chain(inside).chain(after_expr).collect();
                walk_expression(&match_expr, t, combined, arena);
                rest
            } else {
                t.attach_leading(match_expr.pexp_loc, before, arena);
                walk_expression(&match_expr, t, inside, arena);
                after
            };

            let (after_expr, rest) = partition_adjacent_trailing(match_expr.pexp_loc, after, arena);
            t.attach_trailing(match_expr.pexp_loc, after_expr, arena);

            let nodes: Vec<Node<'_>> = cases.iter().map(Node::Case).collect();
            walk_list(&nodes, t, rest, arena);
        }
        ExpressionDesc::Pexp_apply(inner) => {
            let PexpApply { ref funct, .. } = *inner;
            let args = arena.apply_args(inner.args).to_vec();
            // Safety: arena is append-only, expression won't be invalidated
            let funct_expr = arena.get_expr(*funct).clone();
            // Check for unary expressions
            if args.len() == 1 {
                if let ExpressionDesc::Pexp_ident(ident) = &funct_expr.pexp_desc {
                    if let Longident::Lident(op) = arena.get_longident(ident.txt) {
                        let op_str = arena.get_string(*op);
                        if matches!(op_str, "~+" | "~+." | "~-" | "~-." | "~~~" | "not" | "!") {
                            let (_, arg_expr_idx) = &args[0];
                            // Safety: arena is append-only, expression won't be invalidated
                            let arg_expr = arena.get_expr(*arg_expr_idx).clone();
                            let (before, inside, after) =
                                partition_by_loc(comments, arg_expr.pexp_loc, arena);
                            t.attach_leading(arg_expr.pexp_loc, before, arena);
                            walk_expression(&arg_expr, t, inside, arena);
                            t.attach_trailing(arg_expr.pexp_loc, after, arena);
                            return;
                        }
                    }
                }
            }

            // Special case for Array.get: walk arguments directly like OCaml
            if args.len() == 2 {
                if let ExpressionDesc::Pexp_ident(ident) = &funct_expr.pexp_desc {
                    if let Longident::Ldot(base, method_idx) = arena.get_longident(ident.txt) {
                        if let Longident::Lident(module_idx) = base.as_ref() {
                            let module = arena.get_string(*module_idx);
                            let method = arena.get_string(*method_idx);
                            if module == "Array" && method == "get" {
                                // Match OCaml: walk_list [Expression parent_expr; Expression member_expr] t comments
                                let (_, parent_expr_idx) = &args[0];
                                let (_, member_expr_idx) = &args[1];
                                let nodes: Vec<Node<'_>> = vec![
                                    Node::ExpressionIdx(*parent_expr_idx),
                                    Node::ExpressionIdx(*member_expr_idx),
                                ];
                                walk_list(&nodes, t, comments, arena);
                                return;
                            }
                        }
                    }
                }
            }

            // Special case for Array.set: walk arguments directly like OCaml
            if args.len() == 3 {
                if let ExpressionDesc::Pexp_ident(ident) = &funct_expr.pexp_desc {
                    if let Longident::Ldot(base, method_idx) = arena.get_longident(ident.txt) {
                        if let Longident::Lident(module_idx) = base.as_ref() {
                            let module = arena.get_string(*module_idx);
                            let method = arena.get_string(*method_idx);
                            if module == "Array" && method == "set" {
                                // Match OCaml: walk_list [Expression parent_expr; Expression member_expr; Expression target_expr] t comments
                                let (_, parent_expr_idx) = &args[0];
                                let (_, member_expr_idx) = &args[1];
                                let (_, target_expr_idx) = &args[2];
                                let nodes: Vec<Node<'_>> = vec![
                                    Node::ExpressionIdx(*parent_expr_idx),
                                    Node::ExpressionIdx(*member_expr_idx),
                                    Node::ExpressionIdx(*target_expr_idx),
                                ];
                                walk_list(&nodes, t, comments, arena);
                                return;
                            }
                        }
                    }
                }
            }

            // Dictionary spreads are encoded as a call to
            // `Primitive_dict.spread`. Walk the reconstructed source parts so
            // comments attach to the spread expressions and literal rows that
            // the printer emits, rather than to the synthetic call.
            if let Some(parts) = parsetree_viewer::collect_spread_dict_expr_parts(arena, expr) {
                let source_parts: Vec<Expression> = parts
                    .into_iter()
                    .map(|part| match part {
                        parsetree_viewer::DictExprPart::Rows(rows)
                        | parsetree_viewer::DictExprPart::Spread(rows) => rows.clone(),
                    })
                    .collect();
                let nodes: Vec<Node<'_>> = source_parts.iter().map(Node::Expression).collect();
                walk_list(&nodes, t, comments, arena);
                return;
            }

            // Special case for Primitive_dict.make (dict{} syntax)
            // Match OCaml: just walk the key_values array expression
            if args.len() == 1 {
                if let ExpressionDesc::Pexp_ident(ident) = &funct_expr.pexp_desc {
                    if let Longident::Ldot(parent, method_idx) = arena.get_longident(ident.txt) {
                        if arena.get_string(*method_idx) == "make" {
                            if let Longident::Lident(module_idx) = parent.as_ref() {
                                if arena.get_string(*module_idx) == "Primitive_dict" {
                                    let (_, key_values_idx) = &args[0];
                                    let key_values = arena.get_expr(*key_values_idx);
                                    // Check if key_values is a tuple array (matching OCaml's is_tuple_array)
                                    if parsetree_viewer::is_tuple_array(arena, key_values) {
                                        // Walk the key_values expression directly
                                        walk_list(
                                            &[Node::ExpressionIdx(*key_values_idx)],
                                            t,
                                            comments,
                                            arena,
                                        );
                                        return;
                                    }
                                }
                            }
                        }
                    }
                }
            }

            // Special case for Primitive_array.spread (spread array syntax).
            // Match OCaml: flatten all sub-array expressions and walk them together.
            if args.len() == 1 && parsetree_viewer::is_spread_belt_array_concat(arena, &funct_expr)
            {
                let (_, arg_idx) = &args[0];
                let arg = arena.get_expr(*arg_idx);
                if let ExpressionDesc::Pexp_array(sub_arrays) = &arg.pexp_desc {
                    let mut all_expr_idxs: Vec<ExprIdx> = Vec::new();
                    for sub_array_idx in sub_arrays.iter() {
                        let sub_array = arena.get_expr(*sub_array_idx);
                        if let ExpressionDesc::Pexp_array(exprs) = &sub_array.pexp_desc {
                            all_expr_idxs.extend(exprs.iter().copied());
                        } else {
                            all_expr_idxs.push(*sub_array_idx);
                        }
                    }
                    let nodes: Vec<Node<'_>> =
                        all_expr_idxs.into_iter().map(Node::ExpressionIdx).collect();
                    walk_list(&nodes, t, comments, arena);
                    return;
                }
            }

            // Special case for Primitive_list.spread (spread list syntax).
            // Match OCaml: flatten all sub-list expressions and walk them together.
            if args.len() == 1 && parsetree_viewer::is_spread_belt_list_concat(arena, &funct_expr) {
                let (_, arg_idx) = &args[0];
                let arg = arena.get_expr(*arg_idx);
                if let ExpressionDesc::Pexp_array(sub_lists) = &arg.pexp_desc {
                    let mut all_exprs: Vec<Expression> = Vec::new();
                    for sub_list_idx in sub_lists.iter() {
                        let sub_list = arena.get_expr(*sub_list_idx);
                        let (exprs, spread) =
                            parsetree_viewer::collect_list_expressions(arena, sub_list);
                        all_exprs.extend(exprs.into_iter().cloned());
                        if let Some(spread_expr) = spread {
                            all_exprs.push(spread_expr.clone());
                        }
                    }
                    let nodes: Vec<Node<'_>> = all_exprs.iter().map(Node::Expression).collect();
                    walk_list(&nodes, t, comments, arena);
                    return;
                }
            }

            // Check for binary expressions - match OCaml's special handling
            if args.len() == 2 {
                if let ExpressionDesc::Pexp_ident(ident) = &funct_expr.pexp_desc {
                    if let Longident::Lident(op) = arena.get_longident(ident.txt) {
                        let op_str = arena.get_string(*op);
                        if matches!(
                            op_str,
                            ":=" | "||"
                                | "&&"
                                | "=="
                                | "==="
                                | "<"
                                | ">"
                                | "!="
                                | "!=="
                                | "<="
                                | ">="
                                | "+"
                                | "+."
                                | "-"
                                | "-."
                                | "++"
                                | "|||"
                                | "^^^"
                                | "&&&"
                                | "*"
                                | "*."
                                | "/"
                                | "/."
                                | "**"
                                | "->"
                                | "<>"
                        ) {
                            let (_, operand1_idx) = &args[0];
                            let (_, operand2_idx) = &args[1];
                            // Safety: arena is append-only, expressions won't be invalidated
                            let operand1 = arena.get_expr(*operand1_idx).clone();
                            let operand2 = arena.get_expr(*operand2_idx).clone();

                            // Handle operand1
                            let (before, inside, after) =
                                partition_by_loc(comments, operand1.pexp_loc, arena);
                            t.attach_leading(operand1.pexp_loc, before, arena);
                            walk_expression(&operand1, t, inside, arena);
                            let (after_operand1, rest) =
                                partition_adjacent_trailing(operand1.pexp_loc, after, arena);
                            t.attach_trailing(operand1.pexp_loc, after_operand1, arena);

                            // Handle operand2
                            let (before, inside, after) =
                                partition_by_loc(rest, operand2.pexp_loc, arena);
                            t.attach_leading(operand2.pexp_loc, before, arena);
                            walk_expression(&operand2, t, inside, arena);
                            t.attach_trailing(operand2.pexp_loc, after, arena);
                            return;
                        }
                    }
                }
            }

            // Regular apply
            walk_apply_expr(&funct_expr, &args, t, comments, arena);
        }
        ExpressionDesc::Pexp_fun(_) | ExpressionDesc::Pexp_newtype(_) => {
            // Walk through function parameters and body, matching OCaml's handling
            enum OwnedFunParam {
                Parameter {
                    label: ArgLabel,
                    default_expr: Option<Expression>,
                    pat: Pattern,
                },
                NewTypes {
                    names: Vec<crate::parser::ast::StringLoc>,
                },
            }

            let (_is_async, parameters, return_expr) = {
                use parsetree_viewer::FunParam;
                let (is_async, parameters, return_expr) = parsetree_viewer::fun_expr(arena, expr);
                let parameters: Vec<OwnedFunParam> = parameters
                    .into_iter()
                    .map(|param| match param {
                        FunParam::Parameter {
                            label,
                            default_expr,
                            pat,
                            ..
                        } => OwnedFunParam::Parameter {
                            label: *label,
                            default_expr: default_expr.cloned(),
                            pat: pat.clone(),
                        },
                        FunParam::NewTypes { names, .. } => OwnedFunParam::NewTypes {
                            names: names.into_iter().cloned().collect(),
                        },
                    })
                    .collect();
                // res_comments_table.ml:360-392: each newtype becomes a fake
                // `Nolabel` parameter whose pattern is the name at its own
                // location, and the parameters are walked in source order.
                let mut parameters: Vec<OwnedFunParam> = parameters
                    .into_iter()
                    .flat_map(|param| match param {
                        OwnedFunParam::NewTypes { names } => names
                            .into_iter()
                            .map(|name| OwnedFunParam::Parameter {
                                label: ArgLabel::Nolabel,
                                default_expr: None,
                                pat: Pattern {
                                    ppat_desc: PatternDesc::Ppat_var(name),
                                    ppat_loc: name.loc,
                                    ppat_attributes: crate::parser::ast::Attributes::new(),
                                },
                            })
                            .collect::<Vec<_>>(),
                        other => vec![other],
                    })
                    .collect();
                parameters.sort_by_key(|param| match param {
                    OwnedFunParam::Parameter { pat, .. } => arena.loc_start(pat.ppat_loc).cnum,
                    OwnedFunParam::NewTypes { .. } => 0,
                });
                (is_async, parameters, return_expr.clone())
            };

            // Walk each parameter, collecting remaining comments
            let mut prev_loc: Option<LocIdx> = None;
            let mut comments = comments;

            for param in &parameters {
                // Get location for this parameter
                let param_loc = match param {
                    OwnedFunParam::NewTypes { names } => {
                        // For NewTypes, use the first name's location.
                        // This matches OCaml's comment_table which creates a pattern
                        // with loc = string_loc.loc (the first newtype name's location).
                        if let Some(first) = names.first() {
                            first.loc
                        } else {
                            arena.none_loc()
                        }
                    }
                    OwnedFunParam::Parameter {
                        label,
                        default_expr,
                        pat,
                    } => {
                        let start_pos = match label {
                            ArgLabel::Labelled(lbl) | ArgLabel::Optional(lbl)
                                if arena.to_location(lbl.loc) != Location::none() =>
                            {
                                *arena.loc_start(lbl.loc)
                            }
                            _ => *arena.loc_start(pat.ppat_loc),
                        };
                        let end_pos = match default_expr {
                            Some(expr) => *arena.loc_end(expr.pexp_loc),
                            None => *arena.loc_end(pat.ppat_loc),
                        };
                        arena.from_location(&Location::from_positions(start_pos, end_pos))
                    }
                };

                let (leading, inside, trailing) =
                    partition_by_loc(comments.clone(), param_loc, arena);

                // Attach leading comments considering previous parameter
                match prev_loc {
                    None => {
                        t.attach_leading(param_loc, leading, arena);
                    }
                    Some(prev) => {
                        let prev_resolved = arena.to_location(prev);
                        let curr_resolved = arena.to_location(param_loc);
                        if prev_resolved.loc_end.line == curr_resolved.loc_start.line {
                            let (after_prev, before_curr) =
                                partition_adjacent_trailing_through_question(prev, leading, arena);
                            t.attach_trailing(prev, after_prev, arena);
                            t.attach_leading(param_loc, before_curr, arena);
                        } else {
                            let (on_same_line, after) =
                                partition_by_on_same_line(prev, leading, arena);
                            t.attach_trailing(prev, on_same_line, arena);
                            let (before_curr, _, _) = partition_by_loc(after, param_loc, arena);
                            t.attach_leading(param_loc, before_curr, arena);
                        }
                    }
                }

                // Walk the parameter
                match param {
                    OwnedFunParam::NewTypes { names } => {
                        // For newtypes, attach inside comments to the first name's location
                        if let Some(first) = names.first() {
                            t.attach_inside(first.loc, inside, arena);
                        }
                    }
                    OwnedFunParam::Parameter {
                        default_expr, pat, ..
                    } => {
                        let (leading, inside2, trailing2) =
                            partition_by_loc(inside, pat.ppat_loc, arena);
                        t.attach_leading(pat.ppat_loc, leading, arena);
                        walk_pattern(pat, t, inside2, arena);

                        match default_expr {
                            Some(expr) => {
                                let (after_pat, rest) =
                                    partition_adjacent_trailing(pat.ppat_loc, trailing2, arena);
                                t.attach_trailing(pat.ppat_loc, after_pat, arena);
                                if is_block_expr(arena, expr) {
                                    walk_expression(expr, t, rest, arena);
                                } else {
                                    let (l, i, tr) = partition_by_loc(rest, expr.pexp_loc, arena);
                                    t.attach_leading(expr.pexp_loc, l, arena);
                                    walk_expression(expr, t, i, arena);
                                    t.attach_trailing(expr.pexp_loc, tr, arena);
                                }
                            }
                            None => {
                                t.attach_trailing(pat.ppat_loc, trailing2, arena);
                            }
                        }
                    }
                }

                prev_loc = Some(param_loc);
                comments = trailing;
            }

            // Handle trailing comments after last parameter
            if let Some(prev) = prev_loc {
                let (after_prev, rest) =
                    partition_adjacent_trailing_through_question(prev, comments, arena);
                t.attach_trailing(prev, after_prev, arena);
                comments = rest;
            }

            // Walk return expression
            match &return_expr.pexp_desc {
                ExpressionDesc::Pexp_constraint(constraint_inner)
                    if {
                        let inner_loc = arena.get_expr(constraint_inner.0).pexp_loc;
                        let typ_loc = arena.get_core_type(constraint_inner.1).ptyp_loc;
                        inner_loc != LocIdx::default()
                            && arena.loc_start(inner_loc).cnum >= arena.loc_end(typ_loc).cnum
                    } =>
                {
                    let (ref inner_expr_idx, ref typ_idx) = **constraint_inner;
                    // Safety: arena is append-only, expression won't be invalidated
                    let inner_expr = arena.get_expr(*inner_expr_idx).clone();
                    let typ_loc = arena.get_core_type(*typ_idx).ptyp_loc;
                    let (leading, inside, trailing) = partition_by_loc(comments, typ_loc, arena);
                    t.attach_leading(typ_loc, leading, arena);
                    let typ = arena.get_core_type(*typ_idx).clone();
                    walk_core_type(&typ, t, inside, arena);
                    let (after_typ, rest) = partition_adjacent_trailing(typ_loc, trailing, arena);
                    t.attach_trailing(typ_loc, after_typ, arena);
                    if is_block_expr(arena, &inner_expr) {
                        walk_expression(&inner_expr, t, rest, arena);
                    } else {
                        let (l, i, tr) = partition_by_loc(rest, inner_expr.pexp_loc, arena);
                        t.attach_leading(inner_expr.pexp_loc, l, arena);
                        walk_expression(&inner_expr, t, i, arena);
                        t.attach_trailing(inner_expr.pexp_loc, tr, arena);
                    }
                }
                _ => {
                    if is_block_expr(arena, &return_expr) {
                        walk_expression(&return_expr, t, comments, arena);
                    } else {
                        let (l, i, tr) = partition_by_loc(comments, return_expr.pexp_loc, arena);
                        t.attach_leading(return_expr.pexp_loc, l, arena);
                        walk_expression(&return_expr, t, i, arena);
                        t.attach_trailing(return_expr.pexp_loc, tr, arena);
                    }
                }
            }
        }
        ExpressionDesc::Pexp_object_get(inner) => {
            // Safety: arena is append-only, expression won't be invalidated
            let send_expr = arena.get_expr(inner.0).clone();
            walk_expression(&send_expr, t, comments, arena);
        }
        ExpressionDesc::Pexp_object_set(inner) => {
            let e1 = arena.get_expr(inner.0).clone();
            let e2 = arena.get_expr(inner.2).clone();
            let (leading, inside, trailing) = partition_by_loc(comments, e1.pexp_loc, arena);
            t.attach_leading(e1.pexp_loc, leading, arena);
            walk_expression(&e1, t, inside, arena);
            let (after_lhs, rest) = partition_adjacent_trailing(e1.pexp_loc, trailing, arena);
            t.attach_trailing(e1.pexp_loc, after_lhs, arena);
            let (before, inside, after) = partition_by_loc(rest, e2.pexp_loc, arena);
            t.attach_leading(e2.pexp_loc, before, arena);
            walk_expression(&e2, t, inside, arena);
            t.attach_trailing(e2.pexp_loc, after, arena);
        }
        // res_comments_table.ml: template values (after the tag of a
        // tagged template) are walked as a list.
        ExpressionDesc::Pexp_tagged_template(template) => {
            let exprs: Vec<Expression> = std::iter::once(template.tag)
                .chain(template.values.iter().copied())
                .map(|idx| arena.get_expr(idx).clone())
                .collect();
            let nodes: Vec<Node<'_>> = exprs.iter().map(Node::Expression).collect();
            walk_list(&nodes, t, comments, arena);
        }
        ExpressionDesc::Pexp_template(template) => {
            let exprs: Vec<Expression> = template
                .values
                .iter()
                .map(|idx| arena.get_expr(*idx).clone())
                .collect();
            let nodes: Vec<Node<'_>> = exprs.iter().map(Node::Expression).collect();
            walk_list(&nodes, t, comments, arena);
        }
        ExpressionDesc::Pexp_await(inner_idx) => {
            // Safety: arena is append-only, expression won't be invalidated
            let inner = arena.get_expr(*inner_idx).clone();
            walk_expression(&inner, t, comments, arena);
        }
        ExpressionDesc::Pexp_jsx_element(jsx) => {
            walk_jsx_element(jsx, expr.pexp_loc, t, comments, arena);
        }
    }
}

fn walk_jsx_element(
    jsx: &JsxElement,
    pexp_loc: LocIdx,
    t: &mut CommentTable,
    comments: Vec<Comment>,
    arena: &mut ParseArena,
) {
    if comments.is_empty() {
        return;
    }

    match jsx {
        JsxElement::Fragment(fragment) => {
            // For fragment, get the opening token location (<>)
            let opening_loc = {
                let full_loc = arena.to_location(pexp_loc);
                arena.from_location(&Location::from_positions(
                    full_loc.loc_start,
                    *arena.get_position(fragment.opening),
                ))
            };

            // Partition on same line as opening
            let (on_same_line, rest) = partition_by_on_same_line(opening_loc, comments, arena);
            t.attach_trailing(opening_loc, on_same_line, arena);

            let nodes: Vec<Node<'_>> = fragment
                .children
                .iter()
                .map(|e| Node::ExpressionIdx(*e))
                .collect();
            walk_list(&nodes, t, rest, arena);
        }
        JsxElement::Unary(unary) => {
            // Compute the closing token location for />
            // OCaml: unary_element_closing_token creates a loc with start at expr_loc.end - 2
            let closing_token_loc = {
                let expr_loc = arena.to_location(pexp_loc);
                let end_pos = &expr_loc.loc_end;
                let start_pos = crate::location::Position {
                    file_name: end_pos.file_name,
                    line: end_pos.line,
                    bol: if end_pos.bol >= 2 { end_pos.bol - 2 } else { 0 },
                    cnum: if end_pos.cnum >= 2 {
                        end_pos.cnum - 2
                    } else {
                        0
                    },
                };
                arena.from_location(&Location::from_positions(start_pos, *end_pos))
            };

            let name_loc = unary.tag_name.loc;

            // Get the next token after the tag name (first prop or closing token)
            let next_token = if unary.props.is_empty() {
                closing_token_loc
            } else {
                get_jsx_prop_loc(&unary.props[0], arena)
            };

            // Partition comments: same line as tag name and before next token -> trailing of tag name
            let (after_opening_tag_name, rest) =
                partition_adjacent_trailing_before_next_token_on_same_line(
                    name_loc, next_token, comments, arena,
                );

            // Only attach comments to the element name if they are on the same line
            t.attach_trailing(name_loc, after_opening_tag_name, arena);

            if unary.props.is_empty() {
                // Attach comments to the closing /> token
                let (before_closing_token, _rest) =
                    partition_leading_trailing(rest, closing_token_loc, arena);
                t.attach_leading(closing_token_loc, before_closing_token, arena);
            } else {
                // Walk through props
                let (comments_for_props, _rest) =
                    partition_leading_trailing(rest, closing_token_loc, arena);
                let prop_nodes: Vec<Node<'_>> = unary.props.iter().map(Node::JsxProp).collect();
                walk_list(&prop_nodes, t, comments_for_props, arena);
            }
        }
        JsxElement::Container(container) => {
            // Create location for the opening > token
            let opening_greater_than_loc = {
                let opening_end = *arena.get_position(container.opening_end);
                arena.from_location(&Location::from_positions(opening_end, opening_end))
            };

            let name_loc = container.tag_name_start.loc;

            // Get the next token after the tag name (first prop or opening >)
            let next_token = if container.props.is_empty() {
                opening_greater_than_loc
            } else {
                get_jsx_prop_loc(&container.props[0], arena)
            };

            // Partition comments: same line as tag name and before next token
            let (after_opening_tag_name, rest) =
                partition_adjacent_trailing_before_next_token_on_same_line(
                    name_loc, next_token, comments, arena,
                );

            // Attach comments to the element name if they are on the same line
            t.attach_trailing(name_loc, after_opening_tag_name, arena);

            let rest = if container.props.is_empty() {
                // Attach comments to the opening > token
                let (before_greater_than, rest) =
                    partition_leading_trailing(rest, opening_greater_than_loc, arena);
                t.attach_leading(opening_greater_than_loc, before_greater_than, arena);
                rest
            } else {
                // Walk props
                let (comments_for_props, rest) =
                    partition_leading_trailing(rest, opening_greater_than_loc, arena);
                let prop_nodes: Vec<Node<'_>> = container.props.iter().map(Node::JsxProp).collect();
                walk_list(&prop_nodes, t, comments_for_props, arena);
                rest
            };

            // Comments after '>' on the same line should be attached to '>'
            let (after_opening_greater_than, rest) =
                partition_by_on_same_line(opening_greater_than_loc, rest, arena);
            t.attach_trailing(opening_greater_than_loc, after_opening_greater_than, arena);

            // Get closing tag location if present
            let (comments_for_children, _rest) = match &container.closing_tag {
                None => (rest, vec![]),
                Some(closing_tag) => {
                    let closing_tag_loc = {
                        arena.from_location(&Location::from_positions(
                            *arena.get_position(closing_tag.start),
                            *arena.get_position(closing_tag.end),
                        ))
                    };
                    partition_leading_trailing(rest, closing_tag_loc, arena)
                }
            };

            if container.children.is_empty() {
                // Attach all comments to the closing tag if there are no children
                if let Some(closing_tag) = &container.closing_tag {
                    let closing_tag_loc = arena.from_location(&Location::from_positions(
                        *arena.get_position(closing_tag.start),
                        *arena.get_position(closing_tag.end),
                    ));

                    let opening_end_line = arena.to_location(opening_greater_than_loc).loc_end.line;
                    let closing_start_line = arena.get_position(closing_tag.start).line;

                    // Check if there's space between opening and closing tags
                    if opening_end_line < closing_start_line + 1 {
                        // Comments between tags get attached to "inside" the expression
                        let (inside_comments, leading_for_closing) = partition_between_lines(
                            opening_end_line,
                            closing_start_line,
                            comments_for_children,
                        );
                        t.attach_inside(pexp_loc, inside_comments, arena);
                        t.attach_leading(closing_tag_loc, leading_for_closing, arena);
                    } else {
                        // If closing tag is on the same line, attach to closing tag
                        t.attach_leading(closing_tag_loc, comments_for_children, arena);
                    }
                }
            } else {
                // Walk through children
                let children_nodes: Vec<Node<'_>> = container
                    .children
                    .iter()
                    .map(|e| Node::ExpressionIdx(*e))
                    .collect();
                walk_list(&children_nodes, t, comments_for_children, arena);
            }
        }
    }
}

fn walk_jsx_prop(
    prop: &JsxProp,
    t: &mut CommentTable,
    comments: Vec<Comment>,
    arena: &mut ParseArena,
) {
    match prop {
        JsxProp::Punning { name, .. } => {
            let (leading, trailing) = partition_leading_trailing(comments, name.loc, arena);
            t.attach_leading(name.loc, leading, arena);
            t.attach_trailing(name.loc, trailing, arena);
        }
        JsxProp::Value { name, value, .. } => {
            // Match OCaml's walk_jsx_prop which calls walk_list [Expression value]
            // This is important because walk_list uses get_loc(Expression) which may
            // return the braces location if the expression has res.braces attribute
            let val = arena.get_expr(*value);
            let name_end_line = arena.loc_end(name.loc).line;
            let value_start_line = arena.loc_start(val.pexp_loc).line;

            if name_end_line == value_start_line {
                // In the rare case that comments are found between name=value,
                // where both are on the same line,
                // we assign them to the value, and not to the name.
                walk_list(&[Node::ExpressionIdx(*value)], t, comments, arena);
            } else {
                // otherwise we attach comments that come directly after the name to the name
                let (on_same_line_as_name, rest) =
                    partition_by_on_same_line(name.loc, comments, arena);
                t.attach_trailing(name.loc, on_same_line_as_name, arena);
                walk_list(&[Node::ExpressionIdx(*value)], t, rest, arena);
            }
        }
        JsxProp::Spreading { expr, .. } => {
            // Safety: arena is append-only, expression won't be invalidated
            let e = arena.get_expr(*expr).clone();
            walk_expression(&e, t, comments, arena);
        }
    }
}

fn walk_apply_expr(
    call_expr: &Expression,
    arguments: &[(ArgLabel, ExprIdx)],
    t: &mut CommentTable,
    comments: Vec<Comment>,
    arena: &mut ParseArena,
) {
    let (before, inside, after) = partition_by_loc(comments, call_expr.pexp_loc, arena);

    let after = if is_block_expr(arena, call_expr) {
        let (after_expr, rest) = partition_adjacent_trailing(call_expr.pexp_loc, after, arena);
        let combined: Vec<Comment> = before.into_iter().chain(inside).chain(after_expr).collect();
        walk_expression(call_expr, t, combined, arena);
        rest
    } else {
        t.attach_leading(call_expr.pexp_loc, before, arena);
        walk_expression(call_expr, t, inside, arena);
        after
    };

    let (after_expr, rest) = partition_adjacent_trailing(call_expr.pexp_loc, after, arena);
    t.attach_trailing(call_expr.pexp_loc, after_expr, arena);

    let nodes: Vec<Node<'_>> = arguments
        .iter()
        .map(|(lbl, expr_idx)| {
            let expr = arena.get_expr(*expr_idx);
            let loc = match lbl {
                ArgLabel::Labelled(lbl_loc) | ArgLabel::Optional(lbl_loc) => {
                    let start = arena.loc_start(lbl_loc.loc);
                    let end = arena.loc_end(expr.pexp_loc);
                    arena.from_location(&Location::from_positions(*start, *end))
                }
                ArgLabel::Nolabel => expr.pexp_loc,
            };
            Node::ExprArgument {
                expr: *expr_idx,
                loc,
            }
        })
        .collect();

    walk_list(&nodes, t, rest, arena);
}

fn walk_expr_argument(
    expr: &Expression,
    loc: &LocIdx,
    t: &mut CommentTable,
    comments: Vec<Comment>,
    arena: &mut ParseArena,
) {
    // Match OCaml's walk_expr_argument which handles labelled arguments properly
    let (leading, trailing) = partition_leading_trailing(comments, *loc, arena);
    t.attach_leading(*loc, leading, arena);

    let (after_label, rest) = partition_adjacent_trailing(*loc, trailing, arena);
    t.attach_trailing(*loc, after_label, arena);

    let (before, inside, after) = partition_by_loc(rest, expr.pexp_loc, arena);
    t.attach_leading(expr.pexp_loc, before, arena);
    walk_expression(expr, t, inside, arena);
    t.attach_trailing(expr.pexp_loc, after, arena);
}

fn walk_expr_record_row(
    li: &Loc<LidentIdx>,
    expr: &Expression,
    t: &mut CommentTable,
    comments: Vec<Comment>,
    arena: &mut ParseArena,
) {
    let (leading, trailing) = partition_leading_trailing(comments, li.loc, arena);
    t.attach_leading(li.loc, leading, arena);

    let (after_li, rest) = partition_adjacent_trailing(li.loc, trailing, arena);
    t.attach_trailing(li.loc, after_li, arena);

    let (before, inside, after) = partition_by_loc(rest, expr.pexp_loc, arena);
    t.attach_leading(expr.pexp_loc, before, arena);
    walk_expression(expr, t, inside, arena);
    t.attach_trailing(expr.pexp_loc, after, arena);
}

fn walk_case(case: &Case, t: &mut CommentTable, comments: Vec<Comment>, arena: &mut ParseArena) {
    let pc_lhs_loc = arena.get_pat(case.pc_lhs).ppat_loc;
    let (before, inside, after) = partition_by_loc(comments, pc_lhs_loc, arena);
    // cases don't have a location on their own, leading comments should go
    // after the bar on the pattern - match OCaml's List.concat [before; inside]
    let pattern_comments: Vec<Comment> = before.into_iter().chain(inside).collect();
    // Safety: arena is append-only, pattern won't be invalidated
    let pc_lhs = arena.get_pat(case.pc_lhs).clone();
    walk_pattern(&pc_lhs, t, pattern_comments, arena);

    let (after_pat, rest) = partition_adjacent_trailing(pc_lhs_loc, after, arena);
    t.attach_trailing(pc_lhs_loc, after_pat, arena);

    // Handle guard - match OCaml's special handling for block expressions
    let rest = match &case.pc_guard {
        Some(guard_idx) => {
            // Safety: arena is append-only, expression won't be invalidated
            let guard = arena.get_expr(*guard_idx).clone();
            let (before, inside, after) = partition_by_loc(rest, guard.pexp_loc, arena);
            let (after_guard, rest) = partition_adjacent_trailing(guard.pexp_loc, after, arena);
            if is_block_expr(arena, &guard) {
                // For block expressions, pass all comments into walk_expression
                let all_comments: Vec<Comment> = before
                    .into_iter()
                    .chain(inside)
                    .chain(after_guard)
                    .collect();
                walk_expression(&guard, t, all_comments, arena);
            } else {
                t.attach_leading(guard.pexp_loc, before, arena);
                walk_expression(&guard, t, inside, arena);
                t.attach_trailing(guard.pexp_loc, after_guard, arena);
            }
            rest
        }
        None => rest,
    };

    // Safety: arena is append-only, expression won't be invalidated
    let pc_rhs = arena.get_expr(case.pc_rhs).clone();
    if is_block_expr(arena, &pc_rhs) {
        walk_expression(&pc_rhs, t, rest, arena);
    } else {
        let (before, inside, after) = partition_by_loc(rest, pc_rhs.pexp_loc, arena);
        t.attach_leading(pc_rhs.pexp_loc, before, arena);
        walk_expression(&pc_rhs, t, inside, arena);
        t.attach_trailing(pc_rhs.pexp_loc, after, arena);
    }
}

fn walk_pattern(
    pattern: &Pattern,
    t: &mut CommentTable,
    comments: Vec<Comment>,
    arena: &mut ParseArena,
) {
    if comments.is_empty() {
        return;
    }

    match &pattern.ppat_desc {
        PatternDesc::Ppat_any
        | PatternDesc::Ppat_constant { .. }
        | PatternDesc::Ppat_interval { .. } => {
            let (leading, trailing) = partition_leading_trailing(comments, pattern.ppat_loc, arena);
            t.attach_leading(pattern.ppat_loc, leading, arena);
            t.attach_trailing(pattern.ppat_loc, trailing, arena);
        }
        PatternDesc::Ppat_var(name) => {
            let (leading, trailing) = partition_leading_trailing(comments, name.loc, arena);
            t.attach_leading(name.loc, leading, arena);
            t.attach_trailing(name.loc, trailing, arena);
        }
        PatternDesc::Ppat_alias(pat_idx, name) => {
            // Safety: arena is append-only, pattern won't be invalidated
            let pat = arena.get_pat(*pat_idx).clone();
            let (before, inside, after) = partition_by_loc(comments, pat.ppat_loc, arena);
            t.attach_leading(pat.ppat_loc, before, arena);
            walk_pattern(&pat, t, inside, arena);

            let (after_pat, rest) = partition_adjacent_trailing(pat.ppat_loc, after, arena);
            t.attach_trailing(pat.ppat_loc, after_pat, arena);

            let (leading, trailing) = partition_leading_trailing(rest, name.loc, arena);
            t.attach_leading(name.loc, leading, arena);
            t.attach_trailing(name.loc, trailing, arena);
        }
        PatternDesc::Ppat_tuple(pats) if pats.is_empty() => {
            t.attach_inside(pattern.ppat_loc, comments, arena);
        }
        PatternDesc::Ppat_array(pats) if pats.is_empty() => {
            t.attach_inside(pattern.ppat_loc, comments, arena);
        }
        PatternDesc::Ppat_construct(name, _)
            if arena.is_lident(name.txt, "()") || arena.is_lident(name.txt, "[]") =>
        {
            // Unit and empty list get comments inside (like OCaml reference)
            t.attach_inside(pattern.ppat_loc, comments, arena);
        }
        PatternDesc::Ppat_construct(name, _) if arena.is_lident(name.txt, "::") => {
            let list_pats = collect_list_patterns(arena, pattern);
            let nodes: Vec<Node<'_>> = list_pats.iter().map(Node::Pattern).collect();
            walk_list(&nodes, t, comments, arena);
        }
        PatternDesc::Ppat_construct(name, args) => {
            let (leading, trailing) = partition_leading_trailing(comments, name.loc, arena);
            t.attach_leading(name.loc, leading, arena);

            match args.txt.as_slice() {
                [] => t.attach_trailing(name.loc, trailing, arena),
                [arg_pat_idx] => {
                    let (after_longident, rest) =
                        partition_adjacent_trailing(name.loc, trailing, arena);
                    t.attach_trailing(name.loc, after_longident, arena);
                    let arg_pat = arena.get_pat(*arg_pat_idx).clone();
                    let (leading, inside, trailing) =
                        partition_by_loc(rest, arg_pat.ppat_loc, arena);
                    t.attach_leading(arg_pat.ppat_loc, leading, arena);
                    walk_pattern(&arg_pat, t, inside, arena);
                    t.attach_trailing(arg_pat.ppat_loc, trailing, arena);
                }
                pats => {
                    let (after_longident, rest) =
                        partition_adjacent_trailing(name.loc, trailing, arena);
                    t.attach_trailing(name.loc, after_longident, arena);
                    let nodes: Vec<Node<'_>> = pats.iter().map(|p| Node::PatternIdx(*p)).collect();
                    walk_list(&nodes, t, rest, arena);
                }
            }
        }
        PatternDesc::Ppat_variant(inner) => {
            let nodes: Vec<Node<'_>> = inner.1.txt.iter().map(|p| Node::PatternIdx(*p)).collect();
            walk_list(&nodes, t, comments, arena);
        }
        PatternDesc::Ppat_tuple(pats) | PatternDesc::Ppat_array(pats) => {
            let nodes: Vec<Node<'_>> = pats.iter().map(|p| Node::PatternIdx(*p)).collect();
            walk_list(&nodes, t, comments, arena);
        }
        PatternDesc::Ppat_record(inner) => {
            let (ref fields, _, ref record_rest) = **inner;
            let mut nodes: Vec<Node<'_>> = fields
                .iter()
                .map(|f| Node::PatternRecordRow(&f.lid, f.pat))
                .collect();
            if let Some(rest) = record_rest {
                nodes.push(Node::PatternRecordRest(rest));
            }
            walk_list(&nodes, t, comments, arena);
        }
        PatternDesc::Ppat_or(_, _) => {
            // Collect the entire or-chain and walk as a list (like OCaml reference)
            let or_chain: Vec<Pattern> = parsetree_viewer::collect_or_pattern_chain(arena, pattern)
                .into_iter()
                .cloned()
                .collect();
            let nodes: Vec<Node<'_>> = or_chain.iter().map(Node::Pattern).collect();
            walk_list(&nodes, t, comments, arena);
        }
        PatternDesc::Ppat_constraint(inner) => {
            let (ref pat_idx, ref typ_idx) = **inner;
            // Safety: arena is append-only, pattern won't be invalidated
            let pat = arena.get_pat(*pat_idx).clone();
            let (before, inside, after) = partition_by_loc(comments, pat.ppat_loc, arena);
            t.attach_leading(pat.ppat_loc, before, arena);
            walk_pattern(&pat, t, inside, arena);

            let (after_pat, rest) = partition_adjacent_trailing(pat.ppat_loc, after, arena);
            t.attach_trailing(pat.ppat_loc, after_pat, arena);

            let typ_loc = arena.get_core_type(*typ_idx).ptyp_loc;
            let (before, inside, after) = partition_by_loc(rest, typ_loc, arena);
            t.attach_leading(typ_loc, before, arena);
            // Safety: arena is append-only, core type won't be invalidated
            let typ = arena.get_core_type(*typ_idx).clone();
            walk_core_type(&typ, t, inside, arena);
            t.attach_trailing(typ_loc, after, arena);
        }
        PatternDesc::Ppat_type(lid) => {
            let (leading, trailing) = partition_leading_trailing(comments, lid.loc, arena);
            t.attach_leading(lid.loc, leading, arena);
            t.attach_trailing(lid.loc, trailing, arena);
        }
        PatternDesc::Ppat_exception(inner_idx) => {
            // Safety: arena is append-only, pattern won't be invalidated
            let inner = arena.get_pat(*inner_idx).clone();
            walk_pattern(&inner, t, comments, arena);
        }
        PatternDesc::Ppat_unpack(name) => {
            let (leading, trailing) = partition_leading_trailing(comments, name.loc, arena);
            t.attach_leading(name.loc, leading, arena);
            t.attach_trailing(name.loc, trailing, arena);
        }
        PatternDesc::Ppat_extension(ext) => {
            walk_extension(ext, t, comments, arena);
        }
    }
}

fn walk_pattern_record_row(
    li: &Loc<LidentIdx>,
    pat: &Pattern,
    t: &mut CommentTable,
    comments: Vec<Comment>,
    arena: &mut ParseArena,
) {
    let (leading, trailing) = partition_leading_trailing(comments, li.loc, arena);
    t.attach_leading(li.loc, leading, arena);

    let (after_li, rest) = partition_adjacent_trailing(li.loc, trailing, arena);
    t.attach_trailing(li.loc, after_li, arena);

    let (before, inside, after) = partition_by_loc(rest, pat.ppat_loc, arena);
    t.attach_leading(pat.ppat_loc, before, arena);
    walk_pattern(pat, t, inside, arena);
    t.attach_trailing(pat.ppat_loc, after, arena);
}

/// OCaml `walk_pattern_record_rest` (res_comments_table.ml:2115-2133).
fn walk_pattern_record_rest(
    rest: &crate::parser::ast::RecordPatRest,
    t: &mut CommentTable,
    comments: Vec<Comment>,
    arena: &mut ParseArena,
) {
    fn attach_rest_name(
        rest: &crate::parser::ast::RecordPatRest,
        t: &mut CommentTable,
        comments: Vec<Comment>,
        arena: &mut ParseArena,
    ) {
        let (before_name, after_name) =
            partition_leading_trailing(comments, rest.rest_name.loc, arena);
        t.attach_leading(rest.rest_name.loc, before_name, arena);
        t.attach_trailing(rest.rest_name.loc, after_name, arena);
    }
    match rest.rest_type {
        None => attach_rest_name(rest, t, comments, arena),
        Some(typ) => {
            let typ = arena.get_core_type(typ).clone();
            let (before_typ, inside_typ, after_typ) =
                partition_by_loc(comments, typ.ptyp_loc, arena);
            t.attach_leading(typ.ptyp_loc, before_typ, arena);
            walk_core_type(&typ, t, inside_typ, arena);
            let (after_typ, remaining) =
                partition_adjacent_trailing(typ.ptyp_loc, after_typ, arena);
            t.attach_trailing(typ.ptyp_loc, after_typ, arena);
            attach_rest_name(rest, t, remaining, arena);
        }
    }
}

fn walk_core_type(
    ct: &CoreType,
    t: &mut CommentTable,
    comments: Vec<Comment>,
    arena: &mut ParseArena,
) {
    if comments.is_empty() {
        return;
    }

    match &ct.ptyp_desc {
        CoreTypeDesc::Ptyp_any | CoreTypeDesc::Ptyp_var(_) => {
            let (leading, trailing) = partition_leading_trailing(comments, ct.ptyp_loc, arena);
            t.attach_leading(ct.ptyp_loc, leading, arena);
            t.attach_trailing(ct.ptyp_loc, trailing, arena);
        }
        CoreTypeDesc::Ptyp_constr(inner) => {
            let (ref name, ref args) = **inner;
            let (leading, trailing) = partition_leading_trailing(comments, name.loc, arena);
            t.attach_leading(name.loc, leading, arena);

            if args.is_empty() {
                t.attach_trailing(name.loc, trailing, arena);
            } else {
                let (after_name, rest) = partition_adjacent_trailing(name.loc, trailing, arena);
                t.attach_trailing(name.loc, after_name, arena);

                visit_list_but_continue_with_remaining_comments(
                    args,
                    |arg, arena| arena.get_core_type(*arg).ptyp_loc,
                    |arg, t, comments, arena| {
                        // Safety: arena is append-only, core type won't be invalidated
                        let ct = arena.get_core_type(*arg).clone();
                        walk_core_type(&ct, t, comments, arena);
                    },
                    t,
                    rest,
                    false,
                    arena,
                );
            }
        }
        CoreTypeDesc::Ptyp_arrow(inner) => {
            let (..) = **inner;
            // OCaml flattens the arrow type into a list of parameters first, then walks them.
            // This ensures comments between parameters are properly partitioned.
            use crate::parser::parsetree_viewer;
            let (parameters, return_type) = {
                let (_, parameters, return_type) = parsetree_viewer::arrow_type(arena, ct);
                let parameters: Vec<OwnedTypeParameter> = parameters
                    .into_iter()
                    .map(|param| OwnedTypeParameter {
                        lbl: *param.lbl,
                        typ: param.typ.clone(),
                    })
                    .collect();
                (parameters, return_type.clone())
            };

            // Walk type parameters using visit_list_but_continue_with_remaining_comments
            let comments = walk_type_parameters(&parameters, t, comments, arena);

            // Handle return type
            let (before_ret, inside_ret, after_ret) =
                partition_by_loc(comments, return_type.ptyp_loc, arena);
            t.attach_leading(return_type.ptyp_loc, before_ret, arena);
            walk_core_type(&return_type, t, inside_ret, arena);
            t.attach_trailing(return_type.ptyp_loc, after_ret, arena);
        }
        CoreTypeDesc::Ptyp_tuple(types) => {
            let nodes: Vec<Node<'_>> = types.iter().map(|ty| Node::CoreTypeIdx(*ty)).collect();
            walk_list(&nodes, t, comments, arena);
        }
        CoreTypeDesc::Ptyp_object(inner) => {
            let (ref fields, _) = **inner;
            let nodes: Vec<Node<'_>> = fields.iter().map(Node::ObjectField).collect();
            walk_list(&nodes, t, comments, arena);
        }
        CoreTypeDesc::Ptyp_poly(inner) => {
            let (ref vars, ref typ_idx) = **inner;
            // Safety: arena is append-only, core type won't be invalidated
            let typ = arena.get_core_type(*typ_idx).clone();
            // OCaml walks type variables as a list, attaching leading/trailing comments to each
            let comments = if vars.is_empty() {
                comments
            } else {
                visit_list_but_continue_with_remaining_comments(
                    vars,
                    |var, _arena| var.loc,
                    |var, t, comments, arena| {
                        let (before, after) = partition_leading_trailing(comments, var.loc, arena);
                        t.attach_leading(var.loc, before, arena);
                        t.attach_trailing(var.loc, after, arena);
                    },
                    t,
                    comments,
                    false,
                    arena,
                )
            };
            // Then handle the inner type
            let (before_typ, inside_typ, after_typ) =
                partition_by_loc(comments, typ.ptyp_loc, arena);
            t.attach_leading(typ.ptyp_loc, before_typ, arena);
            walk_core_type(&typ, t, inside_typ, arena);
            t.attach_trailing(typ.ptyp_loc, after_typ, arena);
        }
        CoreTypeDesc::Ptyp_variant(inner) => {
            let (ref fields, _, _) = **inner;
            let nodes: Vec<Node<'_>> = fields.iter().map(Node::RowField).collect();
            walk_list(&nodes, t, comments, arena);
        }
        CoreTypeDesc::Ptyp_package(pkg_inner) => {
            let (ref name, ref constraints) = **pkg_inner;
            let (leading, trailing) = partition_leading_trailing(comments, name.loc, arena);
            t.attach_leading(name.loc, leading, arena);

            if constraints.is_empty() {
                t.attach_trailing(name.loc, trailing, arena);
            } else {
                let (after_name, rest) = partition_adjacent_trailing(name.loc, trailing, arena);
                t.attach_trailing(name.loc, after_name, arena);

                let nodes: Vec<Node<'_>> = constraints
                    .iter()
                    .map(|(li, ty)| Node::PackageConstraint(li, *ty))
                    .collect();
                walk_list(&nodes, t, rest, arena);
            }
        }
        CoreTypeDesc::Ptyp_alias(inner) => {
            let (ref typ_idx, ref _name) = **inner;
            // Safety: arena is append-only, core type won't be invalidated
            let typ = arena.get_core_type(*typ_idx).clone();
            // The alias name is just a String without location info
            let (before, inside, after) = partition_by_loc(comments, typ.ptyp_loc, arena);
            t.attach_leading(typ.ptyp_loc, before, arena);
            walk_core_type(&typ, t, inside, arena);
            t.attach_trailing(typ.ptyp_loc, after, arena);
        }
        CoreTypeDesc::Ptyp_extension(ext) => {
            walk_extension(ext, t, comments, arena);
        }
    }
}

/// Walk type parameters of an arrow type, properly partitioning comments between parameters.
/// Returns remaining comments after all parameters.
struct OwnedTypeParameter {
    lbl: ArgLabel,
    typ: CoreType,
}

fn walk_type_parameters(
    parameters: &[OwnedTypeParameter],
    t: &mut CommentTable,
    comments: Vec<Comment>,
    arena: &mut ParseArena,
) -> Vec<Comment> {
    visit_list_but_continue_with_remaining_comments(
        parameters,
        |param, arena| {
            // OCaml: get_loc uses {(Asttypes.get_lbl_loc lbl) with loc_end = typ.ptyp_loc.loc_end}
            // For labeled parameters, the location starts at the label
            // For unlabeled parameters, use just the type's location
            match param.lbl.located() {
                Some(name) => arena.mk_loc_spanning(name.loc, param.typ.ptyp_loc),
                None => param.typ.ptyp_loc,
            }
        },
        |param, t, comments, arena| {
            // walk_node: walk each type parameter
            // OCaml uses typexpr.ptyp_loc for partitioning, not the combined location!
            // This means comments between the label and type (like `~a: /* c1 */ typ`)
            // become "before" comments and get attached as leading to the type.
            let (before, inside, after) = partition_by_loc(comments, param.typ.ptyp_loc, arena);
            t.attach_leading(param.typ.ptyp_loc, before, arena);
            walk_core_type(&param.typ, t, inside, arena);
            t.attach_trailing(param.typ.ptyp_loc, after, arena);
        },
        t,
        comments,
        false, // newline_delimited
        arena,
    )
}

fn walk_object_field(
    field: &ObjectField,
    t: &mut CommentTable,
    comments: Vec<Comment>,
    arena: &mut ParseArena,
) {
    match field {
        ObjectField::Otag(lbl, _attrs, typ) => {
            let (leading, trailing) = partition_leading_trailing(comments, lbl.loc, arena);
            t.attach_leading(lbl.loc, leading, arena);

            let (after_lbl, rest) = partition_adjacent_trailing(lbl.loc, trailing, arena);
            t.attach_trailing(lbl.loc, after_lbl, arena);

            let typ_loc = arena.get_core_type(*typ).ptyp_loc;
            let (before, inside, after) = partition_by_loc(rest, typ_loc, arena);
            t.attach_leading(typ_loc, before, arena);
            // Safety: arena is append-only, core type won't be invalidated
            let typ = arena.get_core_type(*typ).clone();
            walk_core_type(&typ, t, inside, arena);
            t.attach_trailing(typ_loc, after, arena);
        }
        ObjectField::Oinherit(typ) => {
            // Safety: arena is append-only, core type won't be invalidated
            let typ = arena.get_core_type(*typ).clone();
            walk_core_type(&typ, t, comments, arena);
        }
    }
}

fn walk_row_field(
    field: &RowField,
    t: &mut CommentTable,
    comments: Vec<Comment>,
    arena: &mut ParseArena,
) {
    match field {
        // res_comments_table.ml `walk_row_field`: comments around a tag
        // attach to the tag; its payload types are not walked.
        RowField::Rtag(tag, _attrs, _flag, _args) => {
            let (before, after) = partition_leading_trailing(comments, tag.loc, arena);
            t.attach_leading(tag.loc, before, arena);
            t.attach_trailing(tag.loc, after, arena);
        }
        RowField::Rinherit(_) => {}
    }
}

fn walk_package_constraint(
    li: &Loc<LidentIdx>,
    typ: &CoreType,
    t: &mut CommentTable,
    comments: Vec<Comment>,
    arena: &mut ParseArena,
) {
    let (leading, trailing) = partition_leading_trailing(comments, li.loc, arena);
    t.attach_leading(li.loc, leading, arena);

    let (after_li, rest) = partition_adjacent_trailing(li.loc, trailing, arena);
    t.attach_trailing(li.loc, after_li, arena);

    let (before, inside, after) = partition_by_loc(rest, typ.ptyp_loc, arena);
    t.attach_leading(typ.ptyp_loc, before, arena);
    walk_core_type(typ, t, inside, arena);
    t.attach_trailing(typ.ptyp_loc, after, arena);
}

fn walk_module_expr(
    me: &ModuleExpr,
    t: &mut CommentTable,
    comments: Vec<Comment>,
    arena: &mut ParseArena,
) {
    if comments.is_empty() {
        return;
    }

    match &*me.pmod_desc {
        ModuleExprDesc::Pmod_ident(lid) => {
            let (leading, trailing) = partition_leading_trailing(comments, lid.loc, arena);
            t.attach_leading(lid.loc, leading, arena);
            t.attach_trailing(lid.loc, trailing, arena);
        }
        ModuleExprDesc::Pmod_structure(structure) if structure.is_empty() => {
            // Empty structure - attach inside comments to the module expr location
            t.attach_inside(me.pmod_loc, comments, arena);
        }
        ModuleExprDesc::Pmod_structure(structure) => {
            walk_structure(structure, t, comments, arena);
        }
        ModuleExprDesc::Pmod_functor(inner) => {
            let (_, _, _) = **inner;
            // Collect all functor parameters and walk them as a list
            let (parameters, return_mod_expr) = {
                let (parameters, return_mod_expr) = parsetree_viewer::mod_expr_functor(arena, me);
                let parameters: Vec<OwnedModExprFunctorParam> = parameters
                    .into_iter()
                    .map(|param| OwnedModExprFunctorParam {
                        lbl: *param.lbl,
                        mod_type: param.mod_type.cloned(),
                    })
                    .collect();
                (parameters, return_mod_expr.clone())
            };

            // Use the combined location from label to end of mod_type for each parameter
            let comments = visit_list_but_continue_with_remaining_comments(
                &parameters,
                |param, arena| {
                    // Location spans from label start to mod_type end (if present)
                    match &param.mod_type {
                        None => param.lbl.loc,
                        Some(mod_type) => arena.mk_loc_spanning(param.lbl.loc, mod_type.pmty_loc),
                    }
                },
                |param, t, comments, arena| {
                    walk_mod_expr_parameter(param, t, comments, arena);
                },
                t,
                comments,
                false,
                arena,
            );

            // Handle return expression, with special case for Pmod_constraint
            // where the constraint comes before the expression (: Set => expr)
            match &*return_mod_expr.pmod_desc {
                ModuleExprDesc::Pmod_constraint(mod_expr_idx, mod_type_idx) => {
                    let mod_expr = arena.get_mod_expr(*mod_expr_idx).clone();
                    let mod_type = arena.get_mod_type(*mod_type_idx).clone();
                    if arena.loc_end(mod_type.pmty_loc).cnum
                        <= arena.loc_start(mod_expr.pmod_loc).cnum
                    {
                        let (before, inside, after) =
                            partition_by_loc(comments, mod_type.pmty_loc, arena);
                        t.attach_leading(mod_type.pmty_loc, before, arena);
                        walk_mod_type(&mod_type, t, inside, arena);
                        let (after_type, rest) =
                            partition_adjacent_trailing(mod_type.pmty_loc, after, arena);
                        t.attach_trailing(mod_type.pmty_loc, after_type, arena);

                        let (before, inside, after) =
                            partition_by_loc(rest, mod_expr.pmod_loc, arena);
                        t.attach_leading(mod_expr.pmod_loc, before, arena);
                        walk_module_expr(&mod_expr, t, inside, arena);
                        t.attach_trailing(mod_expr.pmod_loc, after, arena);
                    } else {
                        let (before, inside, after) =
                            partition_by_loc(comments, return_mod_expr.pmod_loc, arena);
                        t.attach_leading(return_mod_expr.pmod_loc, before, arena);
                        walk_module_expr(&return_mod_expr, t, inside, arena);
                        t.attach_trailing(return_mod_expr.pmod_loc, after, arena);
                    }
                }
                _ => {
                    let (before, inside, after) =
                        partition_by_loc(comments, return_mod_expr.pmod_loc, arena);
                    t.attach_leading(return_mod_expr.pmod_loc, before, arena);
                    walk_module_expr(&return_mod_expr, t, inside, arena);
                    t.attach_trailing(return_mod_expr.pmod_loc, after, arena);
                }
            }
        }
        ModuleExprDesc::Pmod_apply(_, _) => {
            // Collect all module expressions in the apply chain (call_expr first, then args)
            let (args, call_expr) = {
                let (args, call_expr) = parsetree_viewer::mod_expr_apply(arena, me);
                let args: Vec<ModuleExpr> = args.into_iter().cloned().collect();
                (args, call_expr.clone())
            };
            // OCaml's mod_expr_apply returns [call_expr, arg1, arg2, ...] but ours returns (args, call_expr)
            // Build the list with call_expr first
            let mut mod_exprs: Vec<ModuleExpr> = vec![call_expr];
            mod_exprs.extend(args);
            // Walk all module expressions as a list
            let nodes: Vec<Node<'_>> = mod_exprs.iter().map(Node::ModuleExpr).collect();
            walk_list(&nodes, t, comments, arena);
        }
        ModuleExprDesc::Pmod_constraint(module_expr_idx, mod_type_idx) => {
            // Safety: arena is append-only
            let module_expr = arena.get_mod_expr(*module_expr_idx).clone();
            let mod_type = arena.get_mod_type(*mod_type_idx).clone();
            // Check which comes first in the source: the type or the expression
            // For `X: Int` (normal constraint), type comes after
            // For `: Int = X` (module binding constraint), type comes before
            if arena.loc_start(mod_type.pmty_loc).cnum >= arena.loc_end(module_expr.pmod_loc).cnum {
                // Type comes after expr: `X: Int`
                let (before, inside, after) =
                    partition_by_loc(comments, module_expr.pmod_loc, arena);
                t.attach_leading(module_expr.pmod_loc, before, arena);
                walk_module_expr(&module_expr, t, inside, arena);
                let (after_mod, rest) =
                    partition_adjacent_trailing(module_expr.pmod_loc, after, arena);
                t.attach_trailing(module_expr.pmod_loc, after_mod, arena);

                let (before, inside, after) = partition_by_loc(rest, mod_type.pmty_loc, arena);
                t.attach_leading(mod_type.pmty_loc, before, arena);
                walk_mod_type(&mod_type, t, inside, arena);
                t.attach_trailing(mod_type.pmty_loc, after, arena);
            } else {
                // Type comes before expr: `: Int = X`
                let (before, inside, after) = partition_by_loc(comments, mod_type.pmty_loc, arena);
                t.attach_leading(mod_type.pmty_loc, before, arena);
                walk_mod_type(&mod_type, t, inside, arena);
                let (after_type, rest) =
                    partition_adjacent_trailing(mod_type.pmty_loc, after, arena);
                t.attach_trailing(mod_type.pmty_loc, after_type, arena);

                let (before, inside, after) = partition_by_loc(rest, module_expr.pmod_loc, arena);
                t.attach_leading(module_expr.pmod_loc, before, arena);
                walk_module_expr(&module_expr, t, inside, arena);
                t.attach_trailing(module_expr.pmod_loc, after, arena);
            }
        }
        ModuleExprDesc::Pmod_unpack(expr_idx) => {
            // Safety: arena is append-only
            let expr = arena.get_expr(*expr_idx).clone();
            walk_expression(&expr, t, comments, arena);
        }
        ModuleExprDesc::Pmod_extension(ext) => {
            walk_extension(ext, t, comments, arena);
        }
    }
}

/// Walk a functor parameter (attrs, label, optional mod_type)
struct OwnedModExprFunctorParam {
    lbl: crate::parser::ast::StringLoc,
    mod_type: Option<ModuleType>,
}

fn walk_mod_expr_parameter(
    param: &OwnedModExprFunctorParam,
    t: &mut CommentTable,
    comments: Vec<Comment>,
    arena: &mut ParseArena,
) {
    let (leading, trailing) = partition_leading_trailing(comments, param.lbl.loc, arena);
    t.attach_leading(param.lbl.loc, leading, arena);

    match param.mod_type {
        None => {
            t.attach_trailing(param.lbl.loc, trailing, arena);
        }
        Some(ref mod_type) => {
            let (after_lbl, rest) = partition_adjacent_trailing(param.lbl.loc, trailing, arena);
            t.attach_trailing(param.lbl.loc, after_lbl, arena);

            let (before, inside, after) = partition_by_loc(rest, mod_type.pmty_loc, arena);
            t.attach_leading(mod_type.pmty_loc, before, arena);
            walk_mod_type(mod_type, t, inside, arena);
            t.attach_trailing(mod_type.pmty_loc, after, arena);
        }
    }
}

fn walk_mod_type(
    mt: &ModuleType,
    t: &mut CommentTable,
    comments: Vec<Comment>,
    arena: &mut ParseArena,
) {
    if comments.is_empty() {
        return;
    }

    match &*mt.pmty_desc {
        ModuleTypeDesc::Pmty_ident(lid) => {
            let (leading, trailing) = partition_leading_trailing(comments, lid.loc, arena);
            t.attach_leading(lid.loc, leading, arena);
            t.attach_trailing(lid.loc, trailing, arena);
        }
        ModuleTypeDesc::Pmty_signature(sig) if sig.is_empty() => {
            // Empty signature - attach inside comments to the module type location
            t.attach_inside(mt.pmty_loc, comments, arena);
        }
        ModuleTypeDesc::Pmty_signature(sig) => {
            walk_signature(sig, t, comments, arena);
        }
        ModuleTypeDesc::Pmty_functor(_) => {
            // Collect all functor parameters like OCaml's functor_type
            let (parameters, return_mod_type) = {
                let (parameters, return_mod_type) = functor_type_params(mt, arena);
                (parameters, return_mod_type)
            };

            // Walk parameters using list-based comment distribution
            // This matches OCaml's visit_list_but_continue_with_remaining_comments
            let comments = visit_list_but_continue_with_remaining_comments(
                &parameters,
                |param, arena| {
                    // get_loc: compute the location for each parameter
                    // For "_" label, use just the mod_type location
                    // Otherwise, use label.loc to mod_type.loc.end (or just label.loc if no mod_type)
                    match &param.mod_type {
                        None => param.lbl.loc,
                        Some(mod_type) => {
                            if arena.get_string(param.lbl.txt) == "_" {
                                mod_type.pmty_loc
                            } else {
                                // Create a combined location from label start to mod_type end
                                arena.mk_loc_spanning(param.lbl.loc, mod_type.pmty_loc)
                            }
                        }
                    }
                },
                |param, t, comments, arena| {
                    walk_mod_type_parameter(param, t, comments, arena);
                },
                t,
                comments,
                false, // newline_delimited
                arena,
            );

            // Walk return type with remaining comments
            let (before, inside, after) =
                partition_by_loc(comments, return_mod_type.pmty_loc, arena);
            t.attach_leading(return_mod_type.pmty_loc, before, arena);
            walk_mod_type(&return_mod_type, t, inside, arena);
            t.attach_trailing(return_mod_type.pmty_loc, after, arena);
        }
        ModuleTypeDesc::Pmty_with(inner) => {
            let (ref typ_idx, ref constraints) = **inner;
            // Safety: arena is append-only
            let typ = arena.get_mod_type(*typ_idx).clone();
            let (before, inside, after) = partition_by_loc(comments, typ.pmty_loc, arena);
            t.attach_leading(typ.pmty_loc, before, arena);
            walk_mod_type(&typ, t, inside, arena);

            let (after_typ, rest) = partition_adjacent_trailing(typ.pmty_loc, after, arena);
            t.attach_trailing(typ.pmty_loc, after_typ, arena);

            // Walk with constraints if needed
            for constraint in constraints {
                match constraint {
                    WithConstraint::Pwith_type(lid, td)
                    | WithConstraint::Pwith_typesubst(lid, td) => {
                        let (leading, trailing) =
                            partition_leading_trailing(rest.clone(), lid.loc, arena);
                        t.attach_leading(lid.loc, leading, arena);
                        walk_type_declaration(td, t, trailing, arena);
                    }
                    WithConstraint::Pwith_module(mod_lid, target_lid)
                    | WithConstraint::Pwith_modsubst(mod_lid, target_lid) => {
                        let (leading, trailing) =
                            partition_leading_trailing(rest.clone(), mod_lid.loc, arena);
                        t.attach_leading(mod_lid.loc, leading, arena);
                        let (after_mod, rest2) =
                            partition_adjacent_trailing(mod_lid.loc, trailing, arena);
                        t.attach_trailing(mod_lid.loc, after_mod, arena);
                        let (leading, trailing) =
                            partition_leading_trailing(rest2, target_lid.loc, arena);
                        t.attach_leading(target_lid.loc, leading, arena);
                        t.attach_trailing(target_lid.loc, trailing, arena);
                    }
                }
            }
        }
        ModuleTypeDesc::Pmty_typeof(me_idx) => {
            // Safety: arena is append-only
            let me = arena.get_mod_expr(*me_idx).clone();
            // Partition comments by the module expression location
            // Leading comments attach to mod_expr.pmod_loc, not to items inside
            let (leading, inside, trailing) = partition_by_loc(comments, me.pmod_loc, arena);
            t.attach_leading(me.pmod_loc, leading, arena);
            walk_module_expr(&me, t, inside, arena);
            t.attach_trailing(me.pmod_loc, trailing, arena);
        }
        ModuleTypeDesc::Pmty_extension(ext) => {
            walk_extension(ext, t, comments, arena);
        }
        ModuleTypeDesc::Pmty_alias(lid) => {
            let (leading, trailing) = partition_leading_trailing(comments, lid.loc, arena);
            t.attach_leading(lid.loc, leading, arena);
            t.attach_trailing(lid.loc, trailing, arena);
        }
    }
}

fn walk_attribute(
    attr: &Attribute,
    t: &mut CommentTable,
    comments: Vec<Comment>,
    arena: &mut ParseArena,
) {
    let (name, payload) = attr;
    let (leading, trailing) = partition_leading_trailing(comments, name.loc, arena);
    t.attach_leading(name.loc, leading, arena);

    let (after_name, rest) = partition_adjacent_trailing(name.loc, trailing, arena);
    t.attach_trailing(name.loc, after_name, arena);

    // Walk the payload
    match payload {
        PStr(items) => {
            walk_structure(items, t, rest, arena);
        }
        PSig(items) => {
            walk_signature(items, t, rest, arena);
        }
        PTyp(typ_idx) => {
            // Safety: arena is append-only
            let typ = arena.get_core_type(*typ_idx).clone();
            walk_core_type(&typ, t, rest, arena);
        }
        PPat(inner) => {
            let (ref pat_idx, ref guard) = **inner;
            // Safety: arena is append-only
            let pat = arena.get_pat(*pat_idx).clone();
            walk_pattern(&pat, t, rest.clone(), arena);
            if let Some(guard_expr_idx) = guard {
                let guard_expr = arena.get_expr(*guard_expr_idx).clone();
                walk_expression(&guard_expr, t, Vec::new(), arena);
            }
        }
    }
}

fn walk_extension(
    ext: &Extension,
    t: &mut CommentTable,
    comments: Vec<Comment>,
    arena: &mut ParseArena,
) {
    let (name, payload) = ext;
    let (leading, trailing) = partition_leading_trailing(comments, name.loc, arena);
    t.attach_leading(name.loc, leading, arena);

    match payload {
        PStr(items) => {
            if !items.is_empty() {
                let (after_name, rest) = partition_adjacent_trailing(name.loc, trailing, arena);
                t.attach_trailing(name.loc, after_name, arena);
                walk_structure(items, t, rest, arena);
            } else {
                t.attach_trailing(name.loc, trailing, arena);
            }
        }
        PSig(items) => {
            if !items.is_empty() {
                let (after_name, rest) = partition_adjacent_trailing(name.loc, trailing, arena);
                t.attach_trailing(name.loc, after_name, arena);
                walk_signature(items, t, rest, arena);
            } else {
                t.attach_trailing(name.loc, trailing, arena);
            }
        }
        PTyp(typ_idx) => {
            // Safety: arena is append-only
            let typ = arena.get_core_type(*typ_idx).clone();
            let (after_name, rest) = partition_adjacent_trailing(name.loc, trailing, arena);
            t.attach_trailing(name.loc, after_name, arena);
            walk_core_type(&typ, t, rest, arena);
        }
        PPat(inner) => {
            let (ref pat_idx, ref guard) = **inner;
            // Safety: arena is append-only
            let pat = arena.get_pat(*pat_idx).clone();
            let (after_name, rest) = partition_adjacent_trailing(name.loc, trailing, arena);
            t.attach_trailing(name.loc, after_name, arena);
            walk_pattern(&pat, t, rest.clone(), arena);
            if let Some(guard_expr_idx) = guard {
                let guard_expr = arena.get_expr(*guard_expr_idx).clone();
                walk_expression(&guard_expr, t, Vec::new(), arena);
            }
        }
    }
}

/// Collect all functor parameters from a module type.
/// This is equivalent to OCaml's functor_type function.
struct OwnedModTypeFunctorParam {
    lbl: crate::parser::ast::StringLoc,
    mod_type: Option<ModuleType>,
}

fn functor_type_params(
    modtype: &ModuleType,
    arena: &ParseArena,
) -> (Vec<OwnedModTypeFunctorParam>, ModuleType) {
    fn process(
        mut acc: Vec<OwnedModTypeFunctorParam>,
        modtype: &ModuleType,
        arena: &ParseArena,
    ) -> (Vec<OwnedModTypeFunctorParam>, ModuleType) {
        match &*modtype.pmty_desc {
            ModuleTypeDesc::Pmty_functor(inner) => {
                let (ref lbl, ref arg_type, ref return_type) = **inner;
                acc.push(OwnedModTypeFunctorParam {
                    lbl: *lbl,
                    mod_type: arg_type
                        .as_ref()
                        .map(|idx| arena.get_mod_type(*idx).clone()),
                });
                let return_mt = arena.get_mod_type(*return_type);
                process(acc, return_mt, arena)
            }
            _ => (acc, modtype.clone()),
        }
    }
    process(Vec::new(), modtype, arena)
}

/// Walk a single functor parameter's comments.
/// This matches OCaml's walk_mod_type_parameter.
fn walk_mod_type_parameter(
    param: &OwnedModTypeFunctorParam,
    t: &mut CommentTable,
    comments: Vec<Comment>,
    arena: &mut ParseArena,
) {
    let (leading, trailing) = partition_leading_trailing(comments, param.lbl.loc, arena);
    t.attach_leading(param.lbl.loc, leading, arena);

    match &param.mod_type {
        None => {
            t.attach_trailing(param.lbl.loc, trailing, arena);
        }
        Some(mod_type) => {
            let (after_lbl, rest) = partition_adjacent_trailing(param.lbl.loc, trailing, arena);
            t.attach_trailing(param.lbl.loc, after_lbl, arena);
            let (before, inside, after) = partition_by_loc(rest, mod_type.pmty_loc, arena);
            t.attach_leading(mod_type.pmty_loc, before, arena);
            walk_mod_type(mod_type, t, inside, arena);
            t.attach_trailing(mod_type.pmty_loc, after, arena);
        }
    }
}

/// Visit a list of nodes but return any remaining comments.
fn visit_list_but_continue_with_remaining_comments<'a, T>(
    nodes: &'a [T],
    get_loc: impl Fn(&'a T, &mut ParseArena) -> LocIdx,
    walk_node: impl Fn(&'a T, &mut CommentTable, Vec<Comment>, &mut ParseArena),
    t: &mut CommentTable,
    comments: Vec<Comment>,
    newline_delimited: bool,
    arena: &mut ParseArena,
) -> Vec<Comment> {
    visit_list_impl(
        nodes,
        get_loc,
        walk_node,
        t,
        comments,
        newline_delimited,
        None,
        arena,
    )
}

fn visit_list_impl<'a, T>(
    nodes: &'a [T],
    get_loc: impl Fn(&'a T, &mut ParseArena) -> LocIdx,
    walk_node: impl Fn(&'a T, &mut CommentTable, Vec<Comment>, &mut ParseArena),
    t: &mut CommentTable,
    comments: Vec<Comment>,
    newline_delimited: bool,
    prev_loc: Option<LocIdx>,
    arena: &mut ParseArena,
) -> Vec<Comment> {
    if comments.is_empty() {
        return Vec::new();
    }
    if nodes.is_empty() {
        return match prev_loc {
            Some(loc) => {
                let (after_prev, rest) = if newline_delimited {
                    partition_by_on_same_line(loc, comments, arena)
                } else {
                    partition_adjacent_trailing_through_question(loc, comments, arena)
                };
                t.attach_trailing(loc, after_prev, arena);
                rest
            }
            None => comments,
        };
    }

    let node = &nodes[0];
    let rest_nodes = &nodes[1..];
    let curr_loc = get_loc(node, arena);

    let (leading, inside, trailing) = partition_by_loc(comments, curr_loc, arena);

    let prev_loc_resolved = prev_loc.map(|l| arena.to_location(l));
    let curr_loc_resolved = arena.to_location(curr_loc);

    match &prev_loc {
        None => {
            // First node, all leading comments attach here
            t.attach_leading(curr_loc, leading, arena);
        }
        Some(prev_loc_idx) => {
            let prev_loc_resolved = prev_loc_resolved.as_ref().unwrap();
            // Check if on same line
            if prev_loc_resolved.loc_end.line == curr_loc_resolved.loc_start.line {
                let (after_prev, before_curr) =
                    partition_adjacent_trailing_through_question(*prev_loc_idx, leading, arena);
                t.attach_trailing(*prev_loc_idx, after_prev, arena);
                t.attach_leading(curr_loc, before_curr, arena);
            } else {
                let (on_same_line_as_prev, after_prev) =
                    partition_by_on_same_line(*prev_loc_idx, leading, arena);
                t.attach_trailing(*prev_loc_idx, on_same_line_as_prev, arena);
                let (before_curr, _, _) = partition_by_loc(after_prev, curr_loc, arena);
                t.attach_leading(curr_loc, before_curr, arena);
            }
        }
    }

    walk_node(node, t, inside, arena);
    visit_list_impl(
        rest_nodes,
        get_loc,
        walk_node,
        t,
        trailing,
        newline_delimited,
        Some(curr_loc),
        arena,
    )
}

/// Create a comment table from a structure and comments.
pub fn make_for_structure(
    structure: &[StructureItem],
    comments: Vec<Comment>,
    arena: &mut ParseArena,
) -> CommentTable {
    let mut table = CommentTable::new();
    walk_structure(structure, &mut table, comments, arena);
    table
}

/// Create a comment table from a signature and comments.
pub fn make_for_signature(
    signature: &[SignatureItem],
    comments: Vec<Comment>,
    arena: &mut ParseArena,
) -> CommentTable {
    let mut table = CommentTable::new();
    walk_signature(signature, &mut table, comments, arena);
    table
}
