//! Parser state management.
//!
//! This module provides the parser state structure and basic operations
//! like advancing tokens, error handling, lookahead, and breadcrumb tracking.
//! It mirrors `res_parser.ml`.

use crate::intern::StrIdx;
use crate::location::{Location, Position};
use crate::parse_arena::{ArityIdx, CoreTypeIdx, LidentIdx, LocIdx, ParseArena, PosIdx};

use super::longident::Longident;

use super::comment::Comment;
use super::diagnostics::{DiagnosticCategory, ParserDiagnostic, ParserWarning, ParserWarningKind};
use super::grammar::Grammar;
use super::scanner::Scanner;
use super::token::Token;

/// An inline record type extracted while parsing a type declaration:
/// its name, location, kind and type parameters.
pub type InlineTypeEntry = (
    StrIdx,
    LocIdx,
    super::ast::TypeKind,
    Vec<(CoreTypeIdx, super::ast::Variance)>,
);

/// Region status for error reporting.
///
/// Used to avoid reporting duplicate errors in the same region.
/// The region stack is shallow and is copied on every lookahead, so it stays
/// inline.
type Regions = smallvec::SmallVec<[RegionStatus; 16]>;

/// Whether errors in a grammar region are reported.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RegionStatus {
    /// Errors in this region should be reported.
    Report,
    /// Errors in this region should be silenced.
    Silent,
}

/// Snapshot of parser state for backtracking.
///
/// Used by `parse_attributes_and_binding` to speculatively parse attributes
/// and restore state if they're not followed by `and`.
pub struct ParserSnapshot<'src> {
    scanner_snapshot: super::scanner::ScannerSnapshot,
    token: Token<'src>,
    start_pos: Position,
    end_pos: Position,
    prev_end_pos: Position,
    /// Arena index for start position (for identity-based sharing).
    start_pos_idx: PosIdx,
    /// Arena index for end position (for identity-based sharing).
    end_pos_idx: PosIdx,
    /// Arena index for prev end position (for identity-based sharing).
    prev_end_pos_idx: PosIdx,
    token_line_break: Option<usize>,
    line_break: Option<usize>,
    breadcrumbs: Vec<(Grammar, Position)>,
    regions: Regions,
    diagnostics_len: usize,
    warnings_len: usize,
    comments_len: usize,
    in_external: bool,
    current_type_name_path: Option<Vec<String>>,
    inline_types_found: Option<Vec<InlineTypeEntry>>,
    inline_types_params: Vec<(CoreTypeIdx, super::ast::Variance)>,
    inline_types_collect_free_type_vars: bool,
    pending_structure_len: usize,
    pending_signature_len: usize,
}

/// Lexical cursor saved only for arrow lookahead. Diagnostics and comments are
/// deliberately not replayed: the enclosing lookahead discards them.
struct ArrowCursor<'src> {
    scanner: super::scanner::ScannerSnapshot,
    token: Token<'src>,
    start: Position,
    end: Position,
    prev_end: Position,
}

/// Parser state for ReScript.
///
/// This structure tracks all state needed during parsing:
/// - Current token and positions
/// - Scanner for lexical analysis
/// - Breadcrumbs for error recovery
/// - Collected errors, diagnostics, and comments
/// - Arena for interned positions and locations
pub struct Parser<'src> {
    // Keyed by the first ordinary token after an opener and its expected closer.
    // Nested traversals populate this table too; it survives parser rollback.
    arrow_closings: std::collections::HashMap<(i32, u8), ArrowCursor<'src>>,
    /// The scanner for lexical analysis.
    scanner: Scanner<'src>,
    /// Current token.
    pub token: Token<'src>,
    /// Start position of current token (actual value for error reporting).
    pub start_pos: Position,
    /// End position of current token (actual value for error reporting).
    pub end_pos: Position,
    /// End position of previous token (actual value for error reporting).
    pub prev_end_pos: Position,
    /// Arena index for start position of current token.
    /// Using the index directly enables sharing - same index used everywhere.
    pub start_pos_idx: PosIdx,
    /// Arena index for end position of current token.
    pub end_pos_idx: PosIdx,
    /// Arena index for end position of previous token.
    pub prev_end_pos_idx: PosIdx,
    /// Byte offset of the first LF between the previous token and the
    /// current one, outside comments (res_parser.ml `token_cache.line_break`).
    token_line_break: Option<usize>,
    /// Byte offset of the first LF before a consumed token, outside literals
    /// and comments (res_parser.ml `line_break`); see `newline`.
    line_break: Option<usize>,
    /// Stack of breadcrumbs for error recovery.
    breadcrumbs: Vec<(Grammar, Position)>,
    /// Inside `lookahead`: number of breadcrumbs, from the bottom, that are
    /// still as they were when the innermost lookahead started (0 outside).
    lookahead_breadcrumb_floor: usize,
    /// Breadcrumbs popped from below the floor during lookaheads, in pop
    /// order, so `lookahead` can put them back without cloning the stack.
    lookahead_popped_breadcrumbs: Vec<(Grammar, Position)>,
    /// Collected diagnostics.
    diagnostics: Vec<ParserDiagnostic>,
    /// Collected parser warnings.
    warnings: Vec<ParserWarning>,
    /// Collected comments.
    comments: Vec<Comment>,
    /// Ordinary comment tokens scanned so far, counted whether or not they
    /// are collected: a location-free parse drops them from `comments`, but
    /// the grammar still distinguishes `{/* c */}` from `{}`.
    comment_tokens: usize,
    /// Stack of region statuses for error deduplication.
    regions: Regions,
    /// Arena for interned positions and locations.
    /// Used for efficient location storage with LocIdx/PosIdx indices.
    arena: ParseArena,
    /// Whether we're currently parsing an external definition.
    /// Used for arity calculation of @as(_) labeled parameters.
    pub in_external: bool,
    /// Depth of lookahead nesting. When > 0, next() skips arena position allocations.
    /// This prevents lookahead from affecting position indices for subsequent allocations.
    lookahead_depth: u32,
    /// Current type name path for inline record extraction (e.g., ["options", "extra"]).
    /// Set during type equation parsing to enable nested inline record extraction.
    pub current_type_name_path: Option<Vec<String>>,
    /// Collected inline types during type parsing.
    /// When Some, `{...}` in type positions will be extracted as inline record types.
    pub inline_types_found: Option<Vec<InlineTypeEntry>>,
    /// Type parameters from the outer type declaration for inline types.
    pub inline_types_params: Vec<(CoreTypeIdx, super::ast::Variance)>,
    /// Whether inline records should collect free type variables as parameters.
    pub inline_types_collect_free_type_vars: bool,
    /// Structure items synthesized after the current item.
    pub pending_structure_items: Vec<super::ast::StructureItem>,
    /// Signature items synthesized after the current item.
    pub pending_signature_items: Vec<super::ast::SignatureItem>,
}

impl<'src> Parser<'src> {
    /// Create a new parser for the given source code.
    pub fn new(filename: impl Into<String>, src: &'src str) -> Self {
        Self::with_locations(filename, src, true)
    }

    /// Parse with optional source-location side tables. The scanner still
    /// tracks its current cursor because line breaks participate in grammar.
    pub fn with_locations(
        filename: impl Into<String>,
        src: &'src str,
        store_locations: bool,
    ) -> Self {
        // Create arena first so we can intern the filename
        let mut arena = ParseArena::with_locations(store_locations);
        arena.reserve_for_source(src.len());
        // Intern the filename - this StrIdx will be shared by all positions in this file
        let filename_idx = arena.intern_string(&filename.into());
        arena.set_source_file(filename_idx);
        let scanner = Scanner::new(filename_idx, src);
        // Push initial default positions to arena
        let default_pos = Position::default();
        let default_pos_idx = arena.push_position(default_pos);
        let mut parser = Parser {
            arrow_closings: std::collections::HashMap::new(),
            scanner,
            token: Token::Semicolon, // Placeholder, will be replaced by first scan
            start_pos: default_pos,
            end_pos: default_pos,
            prev_end_pos: default_pos,
            start_pos_idx: default_pos_idx,
            end_pos_idx: default_pos_idx,
            prev_end_pos_idx: default_pos_idx,
            token_line_break: None,
            line_break: None,
            breadcrumbs: Vec::new(),
            lookahead_breadcrumb_floor: 0,
            lookahead_popped_breadcrumbs: Vec::new(),
            diagnostics: Vec::new(),
            warnings: Vec::new(),
            comments: Vec::new(),
            comment_tokens: 0,
            regions: smallvec::smallvec![RegionStatus::Report],
            arena,
            in_external: false,
            lookahead_depth: 0,
            current_type_name_path: None,
            inline_types_found: None,
            inline_types_params: vec![],
            inline_types_collect_free_type_vars: false,
            pending_structure_items: vec![],
            pending_signature_items: vec![],
        };
        // Scan the first token
        parser.next();
        parser
    }

    /// Create a location for the current token (start_pos to end_pos).
    /// Uses the stored start_pos_idx and end_pos_idx directly.
    pub fn mk_loc_current(&mut self) -> LocIdx {
        let start_idx = self.start_pos_idx;
        let end_idx = self.end_pos_idx;
        self.arena.mk_loc(start_idx, end_idx)
    }

    // ========== Arena-based location methods ==========

    /// Get the internal ParseArena for marshalling.
    /// Only use this after parsing is complete.
    pub fn into_arena(self) -> ParseArena {
        self.arena
    }

    /// Get a reference to the parse arena.
    pub fn arena(&self) -> &ParseArena {
        &self.arena
    }

    /// Get a mutable reference to the parse arena.
    pub fn arena_mut(&mut self) -> &mut ParseArena {
        &mut self.arena
    }

    // ========== Arity arena methods ==========

    /// Push an arity value into the arena - creates a FRESH index.
    ///
    /// Use this for COMPUTED arity paths (like `uncurried_type ~arity:n`)
    /// where OCaml creates fresh `Some n` objects.
    ///
    /// For LITERAL `Some 1` paths, use `static_arity_1()` instead.
    pub fn push_arity(&mut self, arity: Option<i32>) -> ArityIdx {
        self.arena.push_arity(arity)
    }

    /// Push a "Full" arity (known argument count) into the arena - creates FRESH index.
    ///
    /// Use this for COMPUTED arity paths (like `uncurried_fun ~arity:n`)
    /// where the arity value n is computed at runtime, not a literal.
    ///
    /// For literal `Some 1` paths, use `static_arity_1()` instead.
    pub fn push_arity_full(&mut self, n: usize) -> ArityIdx {
        self.arena.push_arity(Some(n as i32))
    }

    /// Push an "Unknown" arity into the arena - creates FRESH index.
    ///
    /// Use this for COMPUTED arity paths where `~arity:None` is used
    /// in a context that would create fresh objects in OCaml.
    pub fn push_arity_unknown(&mut self) -> ArityIdx {
        self.arena.push_arity(None)
    }

    /// Get the STATIC arity index for `Some(1)`.
    ///
    /// Use this for LITERAL `~arity:(Some 1)` paths in the OCaml parser:
    /// - res_core.ml:614 - `Exp.fun_ ~arity:(Some 1)` (underscore sugar)
    /// - res_core.ml:4367 - `Typ.arrow ~arity:(Some 1)` (type var arrow)
    /// - res_core.ml:4822 - `Typ.arrow ~arity:(Some 1)` (simple arrow type)
    /// - res_core.ml:5568 - `Typ.arrow ~arity:(Some 1)` (another arrow case)
    ///
    /// OCaml's CSE shares all literal `Some 1` values, so we return the same
    /// pre-allocated index to match that sharing behavior.
    pub fn static_arity_1(&self) -> ArityIdx {
        self.arena.static_arity_1()
    }

    /// Get the pre-allocated `Lident "[]"` for pattern contexts (res_core.ml).
    pub fn pat_nil(&self) -> LidentIdx {
        self.arena.pat_nil()
    }

    /// Get the pre-allocated `Lident "::"` for pattern contexts (res_core.ml).
    pub fn pat_cons(&self) -> LidentIdx {
        self.arena.pat_cons()
    }

    /// Get the pre-allocated `Lident "[]"` for expression contexts (ast_helper.ml).
    pub fn expr_nil(&self) -> LidentIdx {
        self.arena.expr_nil()
    }

    /// Get the pre-allocated `Lident "::"` for expression contexts (ast_helper.ml).
    pub fn expr_cons(&self) -> LidentIdx {
        self.arena.expr_cons()
    }

    /// Push a position into the arena and return its index.
    pub fn push_pos(&mut self, pos: Position) -> PosIdx {
        self.arena.push_position(pos)
    }

    /// Return the current start position index (no allocation).
    /// This enables sharing - multiple uses before `next()` return the same PosIdx,
    /// matching OCaml's reference semantics where `p.Parser.start_pos` is the same object.
    pub fn start_pos_idx(&self) -> PosIdx {
        self.start_pos_idx
    }

    /// Push a fresh start position into the arena.
    ///
    /// Use this when OCaml would create a FRESH position object, even if another
    /// function has already captured a position at the same coordinates.
    ///
    /// Example: When a nested function captures `let start_pos = p.start_pos`,
    /// OCaml creates a new object even if the outer function already captured
    /// one at the same position. Using `push_start_pos()` replicates this.
    ///
    /// Contrast with `start_pos_idx()` which returns the stored index for sharing.
    pub fn push_start_pos(&mut self) -> PosIdx {
        self.arena.push_position(self.start_pos)
    }

    /// OCaml `Scanner.peek_slash p.scanner`.
    pub fn peek_slash(&self) -> bool {
        self.scanner.peek_slash()
    }

    /// Return the current end position index (no allocation).
    /// This enables sharing - multiple uses of `p.end_pos` return the same PosIdx.
    pub fn end_pos_idx(&self) -> PosIdx {
        self.end_pos_idx
    }

    /// Return the previous end position index (no allocation).
    /// This enables sharing - multiple uses of `p.prev_end_pos` return the same PosIdx.
    pub fn prev_end_pos_idx(&self) -> PosIdx {
        self.prev_end_pos_idx
    }

    /// Create and push a location from position indices.
    pub fn mk_loc_idx(&mut self, start: PosIdx, end: PosIdx) -> LocIdx {
        self.arena.mk_loc(start, end)
    }

    /// Create a location from a start PosIdx to prev_end_pos.
    /// Uses the stored prev_end_pos_idx for sharing.
    pub fn mk_loc_idx_to_prev_end(&mut self, start: PosIdx) -> LocIdx {
        let end = self.prev_end_pos_idx();
        self.arena.mk_loc(start, end)
    }

    /// Create a location from a start PosIdx to current end_pos.
    /// Uses stored end_pos_idx for sharing.
    pub fn mk_loc_idx_to_end(&mut self, start: PosIdx) -> LocIdx {
        self.arena.mk_loc(start, self.end_pos_idx)
    }

    /// Create a location from a start PosIdx to another location's end.
    /// Reuses the end position from end_loc.
    pub fn mk_loc_idx_to_end_of(&mut self, start: PosIdx, end_loc: LocIdx) -> LocIdx {
        let end = self.arena.loc_end_idx(end_loc);
        self.arena.mk_loc(start, end)
    }

    /// Create a location with the start and ghost flag from an existing location,
    /// but with end set to prev_end_pos. This is equivalent to OCaml's
    /// `{loc with loc_end = p.prev_end_pos}`.
    pub fn mk_loc_extend_to_prev_end(&mut self, loc: LocIdx) -> LocIdx {
        let loc_info = self.arena.get_location(loc);
        let start_idx = loc_info.loc_start;
        let is_ghost = loc_info.loc_ghost;
        let end_idx = self.prev_end_pos_idx();
        self.arena.push_loc(start_idx, end_idx, is_ghost)
    }

    /// Get the "none" location index.
    pub fn none_loc(&self) -> LocIdx {
        self.arena.none_loc()
    }

    /// Get the start position of a location (cloned).
    pub fn loc_start(&self, loc: LocIdx) -> Position {
        *self.arena.loc_start(loc)
    }

    /// Get the end position of a location (cloned).
    pub fn loc_end(&self, loc: LocIdx) -> Position {
        *self.arena.loc_end(loc)
    }

    /// Get the start position index of a location.
    pub fn loc_start_idx(&self, loc: LocIdx) -> PosIdx {
        self.arena.loc_start_idx(loc)
    }

    /// Get the end position index of a location.
    pub fn loc_end_idx(&self, loc: LocIdx) -> PosIdx {
        self.arena.loc_end_idx(loc)
    }

    /// Check if a location is ghost.
    pub fn loc_ghost(&self, loc: LocIdx) -> bool {
        self.arena.loc_ghost(loc)
    }

    /// Convert a LocIdx to a full Location struct.
    pub fn to_location(&self, loc: LocIdx) -> Location {
        self.arena.to_location(loc)
    }

    /// Convert a full Location struct to LocIdx (push to arena).
    /// Use this when converting from Token locations (which use crate::location::Location)
    /// to AST locations (which use LocIdx).
    pub fn from_location(&mut self, loc: &Location) -> LocIdx {
        self.arena.from_location(loc)
    }

    /// Create a location spanning from one location's start to another's end.
    pub fn mk_loc_spanning(&mut self, start_loc: LocIdx, end_loc: LocIdx) -> LocIdx {
        self.arena.mk_loc_spanning(start_loc, end_loc)
    }

    /// Like mk_loc_spanning, but preserves the ghost flag from the start location.
    pub fn mk_loc_spanning_preserve_ghost(&mut self, start_loc: LocIdx, end_loc: LocIdx) -> LocIdx {
        self.arena
            .mk_loc_spanning_preserve_ghost(start_loc, end_loc)
    }

    /// Create a location from a start Position to another location's end.
    /// Useful pattern: `p.mk_loc_to_end_of(&start_pos, body.some_loc)`
    /// Reuses the end location's PosIdx for position sharing.
    pub fn mk_loc_to_end_of(&mut self, start: &Position, end_loc: LocIdx) -> LocIdx {
        let start_idx = self.arena.push_position(*start);
        let end_idx = self.arena.loc_end_idx(end_loc);
        self.arena.mk_loc(start_idx, end_idx)
    }

    // ========== Longident arena methods ==========

    /// Push a longident into the arena and return its index.
    pub fn push_longident(&mut self, lid: Longident) -> LidentIdx {
        self.arena.push_longident(lid)
    }

    /// Push a simple identifier (Lident) into the arena.
    pub fn push_lident(&mut self, name: &str) -> LidentIdx {
        self.arena.push_lident(name)
    }

    /// Push a simple identifier (Lident) with a static/interned string.
    /// Use this for hardcoded identifiers like "()", "::", "[]", etc.
    /// The string is interned so it will be shared during marshalling.
    pub fn push_lident_static(&mut self, name: &'static str) -> LidentIdx {
        self.arena.push_lident_static(name)
    }

    /// Push a simple identifier (Lident) from an existing StrIdx.
    /// Use when you already have a StrIdx (e.g., from a located string).
    pub fn push_lident_from_idx(&mut self, str_idx: StrIdx) -> LidentIdx {
        self.arena.push_lident_from_idx(str_idx)
    }

    /// Get a longident by index.
    pub fn get_longident(&self, idx: LidentIdx) -> &Longident {
        self.arena.get_longident(idx)
    }

    /// Record a diagnostic error.
    ///
    /// Errors are only recorded if the current region has `Report` status.
    /// After recording, the region is set to `Silent` to avoid duplicates.
    pub fn err(&mut self, category: DiagnosticCategory) {
        self.err_at(self.start_pos, self.end_pos, category);
    }

    /// Record a diagnostic error at specific positions.
    pub fn err_at(&mut self, start_pos: Position, end_pos: Position, category: DiagnosticCategory) {
        if let Some(region) = self.regions.last_mut() {
            if *region == RegionStatus::Report {
                let diagnostic = ParserDiagnostic {
                    start_pos,
                    end_pos,
                    category,
                };
                self.diagnostics.push(diagnostic);
                *region = RegionStatus::Silent;
            }
        }
    }

    /// res_parser.ml `err p (Diagnostics.lazy_message ...)`: report an error
    /// at the current token now (so it silences the region before recovery),
    /// with its message filled in later via `set_diagnostic_message`. Returns
    /// the diagnostic's index, or `None` when the region is silent.
    pub fn err_lazy_message(&mut self) -> Option<usize> {
        let len = self.diagnostics.len();
        self.err(DiagnosticCategory::Message(String::new()));
        (self.diagnostics.len() > len).then_some(len)
    }

    /// Fill in the message of a diagnostic reported by `err_lazy_message`.
    pub fn set_diagnostic_message(&mut self, index: usize, message: String) {
        if let Some(diagnostic) = self.diagnostics.get_mut(index) {
            diagnostic.category = DiagnosticCategory::Message(message);
        }
    }

    /// Record a parser warning at specific positions.
    pub fn warn_at(&mut self, start_pos: Position, end_pos: Position, kind: ParserWarningKind) {
        self.warnings
            .push(ParserWarning::new(start_pos, end_pos, kind));
    }

    /// Record the legacy uncurried dot deprecation warning for the current token.
    pub fn warn_uncurried_dot_syntax(&mut self) {
        self.warn_at(
            self.start_pos,
            self.end_pos,
            ParserWarningKind::DeprecatedUncurriedDotSyntax,
        );
    }

    /// Record an unexpected token error using the current breadcrumbs.
    /// This emits an error with context-aware messaging based on the parsing context.
    pub fn err_unexpected(&mut self) {
        let context: Vec<(Grammar, Position)> = self.breadcrumbs.clone();
        self.err(DiagnosticCategory::Unexpected {
            token: self.token.clone().into_owned(),
            context,
        });
    }

    /// Record an unexpected token error at specific positions using the current breadcrumbs.
    pub fn err_unexpected_at(&mut self, start_pos: Position) {
        let context: Vec<(Grammar, Position)> = self.breadcrumbs.clone();
        self.err_at(
            start_pos,
            self.end_pos,
            DiagnosticCategory::Unexpected {
                token: self.token.clone().into_owned(),
                context,
            },
        );
    }

    /// Begin a new error reporting region.
    pub fn begin_region(&mut self) {
        self.regions.push(RegionStatus::Report);
    }

    /// End the current error reporting region.
    pub fn end_region(&mut self) {
        if !self.regions.is_empty() {
            self.regions.pop();
        }
    }

    /// Advance to the next non-comment token.
    ///
    /// Comments are collected in the parser's comment list.
    /// Note: Doc/module comments are currently treated as comments (not tokens).
    pub fn next(&mut self) {
        if self.token == Token::Eof {
            return;
        }
        self.consume_line_break();
        // res_parser.ml `read`: the scanner records the first LF from here
        // on, across the comments before the next token.
        self.scanner.take_line_break();

        // The new prev_end is the current token's end. In OCaml this is the
        // SAME position object, so we reuse the current end_pos_idx.
        let prev_end = self.end_pos;
        let old_end_pos_idx = self.end_pos_idx;

        // In lookahead mode, skip arena allocations to prevent affecting position indices
        let in_lookahead = self.lookahead_depth > 0;
        // res_parser.ml `read`: a comment records whether the item scanned
        // right before it (the previous token, or an earlier comment) is `?`.
        let mut preceding_is_question = matches!(self.token, Token::Question);

        loop {
            let result = self.scanner.scan();

            // Propagate scanner diagnostics to parser
            if !self.scanner.diagnostics().is_empty() {
                self.collect_scanner_diagnostics();
            }

            match result.token {
                Token::Comment(mut comment) => {
                    self.comment_tokens += 1;
                    // Ordinary comments are formatter metadata. A location-free
                    // compilation must not retain their spans in this separate
                    // collection after omitting the arena's location tables.
                    // Doc/module comments are distinct tokens, handled below.
                    if self.arena.stores_locations() {
                        comment.set_prev_tok_end_pos(self.end_pos);
                        comment.set_prev_tok_is_question(preceding_is_question);
                        self.comments.push(comment);
                    }
                    preceding_is_question = false;
                    self.prev_end_pos = self.end_pos;
                    self.prev_end_pos_idx = self.end_pos_idx;
                    self.end_pos = result.end_pos;
                    if !in_lookahead {
                        self.end_pos_idx = self.arena.push_position(result.end_pos);
                    }
                    // Continue to next token
                }
                _ => {
                    // Source constructs whose generated code embeds source
                    // coordinates (`__LOC__` and friends, `assert`): a
                    // location-free arena records that this unit needs a
                    // located parse, so the driver can reparse it before
                    // type checking instead of type checking it twice.
                    if !self.arena.stores_locations() && needs_semantic_coordinates(&result.token) {
                        self.arena.require_locations();
                    }
                    self.token = result.token;
                    self.token_line_break = self.scanner.take_line_break();
                    self.prev_end_pos = prev_end;
                    self.start_pos = result.start_pos;
                    self.end_pos = result.end_pos;
                    // Only push positions to arena when not in lookahead mode
                    if !in_lookahead {
                        self.prev_end_pos_idx = old_end_pos_idx;
                        self.start_pos_idx = self.arena.push_position(result.start_pos);
                        self.end_pos_idx = self.arena.push_position(result.end_pos);
                    }
                    return;
                }
            }
        }
    }

    #[cold]
    #[inline(never)]
    fn collect_scanner_diagnostics(&mut self) {
        self.diagnostics.extend(self.scanner.take_diagnostics());
    }

    /// Advance to the next token, but only if not at EOF.
    pub fn next_unsafe(&mut self) {
        if self.token != Token::Eof {
            self.next();
        }
    }

    /// Record the line break before the current token as it is consumed
    /// (res_parser.ml `next`): only consumed tokens count, since lookahead
    /// can read the text after a backtick as code before it is rescanned as
    /// template text.
    fn consume_line_break(&mut self) {
        if self.line_break.is_none() {
            self.line_break = self.token_line_break;
        }
    }

    /// The newline to format the source with: CRLF when its first line break
    /// between tokens, outside literals and comments, is CRLF, LF otherwise
    /// (res_parser.ml `newline`, with the break before `Eof` that `finish`
    /// adds). Complete once the parse has reached `Eof`.
    pub fn newline(&self) -> &'static str {
        let line_break = match self.line_break {
            None if self.token == Token::Eof => self.token_line_break,
            line_break => line_break,
        };
        match line_break {
            Some(index) if index > 0 && self.scanner.src().as_bytes()[index - 1] == b'\r' => "\r\n",
            _ => "\n",
        }
    }

    /// Scan the next template literal token.
    ///
    /// res_parser.ml `next_template_literal_token`: the delimiter that is
    /// the current token is consumed, and the template text has no line
    /// break before it.
    pub fn next_template_literal_token(&mut self) {
        if self.token != Token::Eof {
            self.consume_line_break();
        }
        self.token_line_break = None;
        let result = self.scanner.scan_template_literal_token();

        // Propagate scanner diagnostics to parser
        let scanner_diagnostics = self.scanner.take_diagnostics();
        self.diagnostics.extend(scanner_diagnostics);

        self.token = result.token;
        self.prev_end_pos = self.end_pos;
        self.prev_end_pos_idx = self.end_pos_idx;
        self.start_pos = result.start_pos;
        self.end_pos = result.end_pos;
        // Only push positions to arena when not in lookahead mode
        if self.lookahead_depth == 0 {
            self.start_pos_idx = self.arena.push_position(result.start_pos);
            self.end_pos_idx = self.arena.push_position(result.end_pos);
        }
    }

    /// Rescan the current position as a regex literal.
    /// Matches OCaml's `next_regex_token` which is called when the parser sees `/` in
    /// expression position and needs to interpret it as a regex start.
    /// The scanner's current position should be just after the `/` that was already consumed.
    pub fn next_regex_token(&mut self) {
        let prefix_length = match self.token {
            Token::Forwardslash => 1,
            Token::ForwardslashDot => 2,
            _ => unreachable!("next_regex_token on a non-slash token"),
        };
        let result = self.scanner.scan_regex(self.start_pos, prefix_length);

        // Propagate scanner diagnostics to parser
        let scanner_diagnostics = self.scanner.take_diagnostics();
        self.diagnostics.extend(scanner_diagnostics);

        // res_parser.ml `next_regex_token` replaces the current token in
        // place: nothing is consumed, and the token keeps its start.
        self.token = result.token;
        self.end_pos = result.end_pos;
        if self.lookahead_depth == 0 {
            self.end_pos_idx = self.arena.push_position(result.end_pos);
        }
    }

    /// Check if the current token matches and consume it if so.
    ///
    /// Returns `true` if the token was consumed.
    pub fn optional(&mut self, token: &Token<'_>) -> bool {
        if &self.token == token {
            self.next();
            true
        } else {
            false
        }
    }

    /// Expect a specific token and consume it.
    ///
    /// If the token doesn't match, an error is recorded.
    pub fn expect(&mut self, token: Token<'static>) {
        self.expect_with_grammar(token, None);
    }

    /// Expect a specific token with grammar context for error messages.
    ///
    /// When the expected token is not found, an error is generated spanning from
    /// the previous token's end position to the current token's end position.
    /// This matches OCaml's `expect` which uses `~start_pos:p.prev_end_pos` with
    /// default `~end_pos:p.end_pos`.
    pub fn expect_with_grammar(&mut self, token: Token<'static>, grammar: Option<Grammar>) {
        if self.token == token {
            self.next();
        } else {
            let category = DiagnosticCategory::Expected {
                context: grammar,
                pos: self.prev_end_pos,
                token,
            };
            // OCaml uses prev_end_pos for start and end_pos (current token's end) for end.
            // This creates a span from where we expected the token to the current position.
            self.err_at(self.prev_end_pos, self.end_pos, category);
        }
    }

    /// Push a breadcrumb for error recovery.
    pub fn leave_breadcrumb(&mut self, grammar: Grammar) {
        self.breadcrumbs.push((grammar, self.start_pos));
    }

    /// Pop the most recent breadcrumb.
    pub fn eat_breadcrumb(&mut self) {
        if let Some(popped) = self.breadcrumbs.pop()
            && self.breadcrumbs.len() < self.lookahead_breadcrumb_floor
        {
            self.lookahead_breadcrumb_floor = self.breadcrumbs.len();
            self.lookahead_popped_breadcrumbs.push(popped);
        }
    }

    /// Get the current breadcrumbs.
    pub fn breadcrumbs(&self) -> &[(Grammar, Position)] {
        &self.breadcrumbs
    }

    /// Inspect one ordinary successor without cloning parser bookkeeping.
    pub(super) fn followed_by_arrow(&mut self) -> bool {
        let snapshot = self.scanner.snapshot();
        let answer = loop {
            match self.scanner.scan().token {
                Token::Comment(_) => continue,
                token => break matches!(token, Token::EqualGreater),
            }
        };
        self.scanner.restore(snapshot);
        answer
    }

    /// Reuse a bracket traversal only inside the side-effect-free arrow probe.
    pub(super) fn arrow_closing(&mut self, key: (i32, u8)) -> bool {
        debug_assert!(self.lookahead_depth > 0);
        let Some(cursor) = self.arrow_closings.get(&key) else {
            return false;
        };
        self.scanner.restore(cursor.scanner.clone());
        self.token = cursor.token.clone();
        self.start_pos = cursor.start;
        self.end_pos = cursor.end;
        self.prev_end_pos = cursor.prev_end;
        true
    }

    pub(super) fn save_arrow_closing(&mut self, key: (i32, u8)) {
        self.arrow_closings.insert(
            key,
            ArrowCursor {
                scanner: self.scanner.snapshot(),
                token: self.token.clone(),
                start: self.start_pos,
                end: self.end_pos,
                prev_end: self.prev_end_pos,
            },
        );
    }

    /// Execute a callback with lookahead, then restore parser state.
    ///
    /// This allows speculative parsing without affecting the parser state.
    /// During lookahead, next() skips arena position allocations to prevent
    /// lookahead from affecting position indices in the final AST.
    pub fn lookahead<T, F>(&mut self, callback: F) -> T
    where
        F: FnOnce(&mut Self) -> T,
    {
        // Save scanner state
        let scanner_snapshot = self.scanner.snapshot();

        // Save parser state (including position indices for identity-based sharing)
        let token = self.token.clone();
        let start_pos = self.start_pos;
        let end_pos = self.end_pos;
        let prev_end_pos = self.prev_end_pos;
        let start_pos_idx = self.start_pos_idx;
        let end_pos_idx = self.end_pos_idx;
        let prev_end_pos_idx = self.prev_end_pos_idx;
        let token_line_break = self.token_line_break;
        let line_break = self.line_break;
        // Breadcrumbs are restored from the untouched bottom of the stack
        // plus the entries popped from it (see `eat_breadcrumb`).
        let outer_breadcrumb_floor =
            std::mem::replace(&mut self.lookahead_breadcrumb_floor, self.breadcrumbs.len());
        let popped_breadcrumbs_len = self.lookahead_popped_breadcrumbs.len();
        let diagnostics_len = self.diagnostics.len();
        let regions = self.regions.clone();
        let warnings_len = self.warnings.len();
        let comments_len = self.comments.len();
        let comment_tokens = self.comment_tokens;
        let in_external = self.in_external;
        let current_type_name_path = self.current_type_name_path.clone();
        let inline_types_found = self.inline_types_found.clone();
        let inline_types_params = self.inline_types_params.clone();
        let inline_types_collect_free_type_vars = self.inline_types_collect_free_type_vars;
        let pending_structure_len = self.pending_structure_items.len();
        let pending_signature_len = self.pending_signature_items.len();

        // Enter lookahead mode - next() will skip arena position allocations
        self.lookahead_depth += 1;

        // Execute callback
        let result = callback(self);

        // Exit lookahead mode
        self.lookahead_depth -= 1;

        // Restore scanner state
        self.scanner.restore(scanner_snapshot);

        // Restore parser state (including position indices)
        self.token = token;
        self.start_pos = start_pos;
        self.end_pos = end_pos;
        self.prev_end_pos = prev_end_pos;
        self.start_pos_idx = start_pos_idx;
        self.end_pos_idx = end_pos_idx;
        self.prev_end_pos_idx = prev_end_pos_idx;
        self.token_line_break = token_line_break;
        self.line_break = line_break;
        self.breadcrumbs.truncate(self.lookahead_breadcrumb_floor);
        while self.lookahead_popped_breadcrumbs.len() > popped_breadcrumbs_len {
            let popped = self
                .lookahead_popped_breadcrumbs
                .pop()
                .expect("length checked above");
            self.breadcrumbs.push(popped);
        }
        self.lookahead_breadcrumb_floor = outer_breadcrumb_floor;
        // res_parser.ml `with_checkpoint`: immutable region states also roll
        // back error suppression, including nested regions.
        self.regions = regions;
        self.diagnostics.truncate(diagnostics_len);
        self.warnings.truncate(warnings_len);
        self.comments.truncate(comments_len);
        self.comment_tokens = comment_tokens;
        self.in_external = in_external;
        self.current_type_name_path = current_type_name_path;
        self.inline_types_found = inline_types_found;
        self.inline_types_params = inline_types_params;
        self.inline_types_collect_free_type_vars = inline_types_collect_free_type_vars;
        self.pending_structure_items.truncate(pending_structure_len);
        self.pending_signature_items.truncate(pending_signature_len);

        result
    }

    /// Create a snapshot of the current parser state.
    ///
    /// Used for speculative parsing with manual backtracking.
    /// Call `restore` to return to this state.
    pub fn snapshot(&self) -> ParserSnapshot<'src> {
        ParserSnapshot {
            scanner_snapshot: self.scanner.snapshot(),
            token: self.token.clone(),
            start_pos: self.start_pos,
            end_pos: self.end_pos,
            prev_end_pos: self.prev_end_pos,
            start_pos_idx: self.start_pos_idx,
            end_pos_idx: self.end_pos_idx,
            prev_end_pos_idx: self.prev_end_pos_idx,
            token_line_break: self.token_line_break,
            line_break: self.line_break,
            breadcrumbs: self.breadcrumbs.clone(),
            regions: self.regions.clone(),
            diagnostics_len: self.diagnostics.len(),
            warnings_len: self.warnings.len(),
            comments_len: self.comments.len(),
            in_external: self.in_external,
            current_type_name_path: self.current_type_name_path.clone(),
            inline_types_found: self.inline_types_found.clone(),
            inline_types_params: self.inline_types_params.clone(),
            inline_types_collect_free_type_vars: self.inline_types_collect_free_type_vars,
            pending_structure_len: self.pending_structure_items.len(),
            pending_signature_len: self.pending_signature_items.len(),
        }
    }

    /// Restore parser state from a snapshot.
    ///
    /// Used to backtrack after speculative parsing.
    /// Note: Arena allocations made during speculative parsing are not freed,
    /// but the indices won't be stored in the AST since we're restoring state.
    pub fn restore(&mut self, snapshot: ParserSnapshot<'src>) {
        self.scanner.restore(snapshot.scanner_snapshot);
        self.token = snapshot.token;
        self.start_pos = snapshot.start_pos;
        self.end_pos = snapshot.end_pos;
        self.prev_end_pos = snapshot.prev_end_pos;
        self.start_pos_idx = snapshot.start_pos_idx;
        self.end_pos_idx = snapshot.end_pos_idx;
        self.prev_end_pos_idx = snapshot.prev_end_pos_idx;
        self.token_line_break = snapshot.token_line_break;
        self.line_break = snapshot.line_break;
        self.breadcrumbs = snapshot.breadcrumbs;
        // res_parser.ml `with_checkpoint`: immutable region states also roll
        // back error suppression.
        self.regions = snapshot.regions;
        self.diagnostics.truncate(snapshot.diagnostics_len);
        self.warnings.truncate(snapshot.warnings_len);
        self.comments.truncate(snapshot.comments_len);
        self.in_external = snapshot.in_external;
        self.current_type_name_path = snapshot.current_type_name_path;
        self.inline_types_found = snapshot.inline_types_found;
        self.inline_types_params = snapshot.inline_types_params;
        self.inline_types_collect_free_type_vars = snapshot.inline_types_collect_free_type_vars;
        self.pending_structure_items
            .truncate(snapshot.pending_structure_len);
        self.pending_signature_items
            .truncate(snapshot.pending_signature_len);
        // Arena allocations made while speculating are kept: it's harmless,
        // since their indices won't be stored in the final AST.
    }

    /// Get collected diagnostics.
    pub fn diagnostics(&self) -> &[ParserDiagnostic] {
        &self.diagnostics
    }

    /// Get collected parser warnings.
    pub fn warnings(&self) -> &[ParserWarning] {
        &self.warnings
    }

    /// The number of collected comments.
    pub fn comments_len(&self) -> usize {
        self.comments.len()
    }

    /// The number of ordinary comment tokens scanned, collected or not.
    pub fn comment_tokens(&self) -> usize {
        self.comment_tokens
    }

    /// Mark the collected comments in `range` as inside the comment-only JSX
    /// container at `loc`.
    pub fn set_jsx_container(
        &mut self,
        range: std::ops::Range<usize>,
        loc: crate::location::Location,
    ) {
        for comment in &mut self.comments[range] {
            comment.jsx_container = Some(loc);
        }
    }

    /// Get collected comments.
    pub fn comments(&self) -> &[Comment] {
        &self.comments
    }

    /// Take ownership of collected comments.
    pub fn take_comments(&mut self) -> Vec<Comment> {
        std::mem::take(&mut self.comments)
    }

    /// Take ownership of collected diagnostics.
    pub fn take_diagnostics(&mut self) -> Vec<ParserDiagnostic> {
        std::mem::take(&mut self.diagnostics)
    }

    /// Check if there are any errors.
    pub fn has_errors(&self) -> bool {
        !self.diagnostics.is_empty()
    }

    /// Check if there's a newline between the previous token and the current token.
    ///
    /// This is used for disambiguating syntax like `[` which can be either
    /// an array literal (when starting a new line) or array indexing (when
    /// following an expression on the same line).
    pub fn has_newline_before(&self) -> bool {
        self.start_pos.line > self.prev_end_pos.line
    }

    /// Check if the current token has whitespace on both sides.
    ///
    /// Used to disambiguate operators like `-` which can be:
    /// - Binary (subtraction) when there's whitespace on both sides
    /// - Unary (negation) when at the start of a line without surrounding whitespace
    pub fn is_binary_op(&self) -> bool {
        self.scanner
            .is_binary_op(self.start_pos.cnum as usize, self.end_pos.cnum as usize)
    }

    /// res_parser.ml `peek_binary_operator`: the current token, with a `<` or
    /// `>` extended by an immediately adjacent operator suffix (`<<`, `>=`,
    /// `>>`, `>>>`). The extended token replaces the current one.
    pub fn peek_binary_operator(&mut self) -> Token<'src> {
        if matches!(self.token, Token::LessThan | Token::GreaterThan) {
            let current = self.token.clone();
            if let Some(operator) = self.scanner.scan_binary_operator(&current) {
                self.token = operator;
                self.end_pos = self.scanner.position();
                if self.lookahead_depth == 0 {
                    self.end_pos_idx = self.arena.push_position(self.end_pos);
                }
            }
        }
        self.token.clone()
    }

    /// Get the filename index being parsed.
    pub fn filename(&self) -> StrIdx {
        self.scanner.filename
    }
}

/// Tokens whose translation reads source coordinates (`Translcore`'s
/// `__LOC__`/`__LINE__`/`__POS__` constants and `Assert_failure` payloads).
/// Qualified forms (`Pervasives.__LOC__`) are still caught by the converter's
/// `require_locations` fallback.
fn needs_semantic_coordinates(token: &Token<'_>) -> bool {
    match token {
        Token::Assert => true,
        Token::Lident(name) => matches!(
            name.as_ref(),
            "__LOC__" | "__LINE__" | "__POS__" | "__LOC_OF__" | "__LINE_OF__" | "__POS_OF__"
        ),
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn location_free_parser_preserves_ast_shape() {
        let sources = [
            "let x = 1\nlet y = x + 2",
            "let f = (~x=1, y) => x + y\nlet z = f(~x=2, 3)",
            "type t = {a: int, b?: string}\nlet x = {a: 1}",
            "let f = x => switch x { | Some(y) => y | None => 0 }",
            "let f = x => {\n x\n -1\n}",
            "let x = <div className=\"test\">{React.string(\"hello\")}</div>",
            "type t = (. int => int) => int",
            "let x = `hello ${name}`",
            "let x = <div>{/* comment only */}<span /></div>",
            "let x = <>{/* comment only */}</>",
        ];
        for source in sources {
            let source = source.to_string();
            let (tx, rx) = std::sync::mpsc::channel();
            std::thread::spawn(move || {
                let parse = |locations| {
                    let mut parser = Parser::with_locations("test.res", &source, locations);
                    let structure = crate::parser::module::parse_structure(&mut parser);
                    assert!(
                        parser.diagnostics.is_empty(),
                        "{source}: {:?}",
                        parser.diagnostics
                    );
                    // The regular AST sexp also exposes braces offsets. They
                    // are intentionally absent; compare syntax, not locations.
                    fn syntax_only(sexp: &mut crate::parser::sexp::Sexp) {
                        use crate::parser::sexp::Sexp;
                        if let Sexp::List(items) = sexp {
                            if matches!(items.first(), Some(Sexp::Atom(tag)) if tag == "braces_loc")
                            {
                                items.truncate(1);
                            } else {
                                for item in items {
                                    syntax_only(item);
                                }
                            }
                        }
                    }
                    let mut output = crate::parser::sexp::structure(parser.arena(), &structure);
                    syntax_only(&mut output);
                    if !locations {
                        assert_eq!(parser.arena().position_count(), 0);
                        assert_eq!(parser.arena().location_count(), 0);
                    }
                    output.to_string()
                };
                assert_eq!(parse(true), parse(false), "{source}");
                tx.send(()).unwrap();
            });
            rx.recv_timeout(std::time::Duration::from_secs(5))
                .expect("location-free parse failed or hung");
        }
    }

    #[test]
    fn location_free_parser_does_not_retain_formatter_comment_spans() {
        let source = "// heading\n/** doc */\nlet x = /* value */ 1\n";
        let parse = |locations| {
            let mut parser = Parser::with_locations("comments.res", source, locations);
            let structure = crate::parser::module::parse_structure(&mut parser);
            assert!(parser.diagnostics.is_empty());
            assert_eq!(parser.comments().len(), if locations { 2 } else { 0 });
            let syntax = crate::parser::sexp::structure(parser.arena(), &structure).to_string();
            // Documentation is semantic attribute content, not a formatter comment.
            assert!(syntax.contains("doc"));
            syntax
        };
        assert_eq!(parse(false), parse(true));
    }

    #[test]
    fn location_free_parser_flags_units_whose_output_embeds_coordinates() {
        let flagged = |source: &str| {
            let source = source.to_string();
            std::thread::spawn(move || {
                let mut parser = Parser::with_locations("flags.res", &source, false);
                let _ = crate::parser::module::parse_structure(&mut parser);
                assert!(parser.diagnostics.is_empty(), "{source}");
                parser.arena().locations_required()
            })
            .join()
            .unwrap()
        };
        assert!(!flagged(
            "let x = 1\nlet f = y => y + x\nlet loc = \"__LOC__\""
        ));
        assert!(flagged("let here = __LOC__"));
        assert!(flagged("let line = __LINE__"));
        assert!(flagged("let pos = __POS__"));
        assert!(flagged("let check = x => assert(x > 0)"));
        assert!(flagged("module rec A: {let v: int} = {let v = 1}"));
        // A located parse never needs a retry.
        let mut located = Parser::with_locations("flags.res", "let here = __LOC__", true);
        let _ = crate::parser::module::parse_structure(&mut located);
        assert!(!located.arena().locations_required());
    }

    #[test]
    fn test_parser_new() {
        let parser = Parser::new("test.res", "let x = 42");
        assert!(matches!(parser.token, Token::Let { .. }));
    }

    #[test]
    fn test_parser_next() {
        let mut parser = Parser::new("test.res", "let x = 42");
        assert!(matches!(parser.token, Token::Let { .. }));
        parser.next();
        assert!(matches!(parser.token, Token::Lident(_)));
        parser.next();
        assert!(matches!(parser.token, Token::Equal));
        parser.next();
        assert!(matches!(parser.token, Token::Int { .. }));
        parser.next();
        assert!(matches!(parser.token, Token::Eof));
    }

    #[test]
    fn test_parser_optional() {
        let mut parser = Parser::new("test.res", "let x = 42");
        assert!(parser.optional(&Token::Let { unwrap: false }));
        assert!(matches!(parser.token, Token::Lident(_)));
        assert!(!parser.optional(&Token::Equal));
        assert!(matches!(parser.token, Token::Lident(_)));
    }

    #[test]
    fn test_parser_expect() {
        let mut parser = Parser::new("test.res", "let x = 42");
        parser.expect(Token::Let { unwrap: false });
        assert!(matches!(parser.token, Token::Lident(_)));
        // Expecting wrong token should record error
        parser.expect(Token::Equal);
        assert!(parser.has_errors());
    }

    #[test]
    fn test_parser_breadcrumbs() {
        let mut parser = Parser::new("test.res", "let x = 42");
        assert!(parser.breadcrumbs().is_empty());
        parser.leave_breadcrumb(Grammar::LetBinding);
        assert_eq!(parser.breadcrumbs().len(), 1);
        parser.leave_breadcrumb(Grammar::ExprOperand);
        assert_eq!(parser.breadcrumbs().len(), 2);
        parser.eat_breadcrumb();
        assert_eq!(parser.breadcrumbs().len(), 1);
    }

    #[test]
    fn lookahead_restores_breadcrumbs_popped_below_its_start() {
        fn names(parser: &Parser<'_>) -> Vec<String> {
            parser
                .breadcrumbs()
                .iter()
                .map(|(g, _)| format!("{g:?}"))
                .collect()
        }
        let mut parser = Parser::new("test.res", "let x = 42");
        parser.leave_breadcrumb(Grammar::Implementation);
        parser.leave_breadcrumb(Grammar::LetBinding);
        parser.leave_breadcrumb(Grammar::ExprOperand);
        let before = names(&parser);
        parser.lookahead(|p| {
            p.eat_breadcrumb();
            p.eat_breadcrumb();
            p.leave_breadcrumb(Grammar::TypeExpression);
            p.lookahead(|p| {
                p.eat_breadcrumb();
                p.eat_breadcrumb();
                p.leave_breadcrumb(Grammar::Pattern);
                p.leave_breadcrumb(Grammar::ExprBlock);
            });
            assert_eq!(names(p), vec!["Implementation", "TypeExpression"]);
            p.eat_breadcrumb();
            p.eat_breadcrumb();
            assert!(p.breadcrumbs().is_empty());
            p.leave_breadcrumb(Grammar::Pattern);
        });
        assert_eq!(names(&parser), before);
        // Outside a lookahead, pops are final.
        parser.eat_breadcrumb();
        assert_eq!(names(&parser), before[..2].to_vec());
    }

    #[test]
    fn test_parser_lookahead() {
        let mut parser = Parser::new("test.res", "let x = 42");
        assert!(matches!(parser.token, Token::Let { .. }));

        let found_equal = parser.lookahead(|p| {
            p.next(); // x
            p.next(); // =
            matches!(p.token, Token::Equal)
        });

        assert!(found_equal);
        // Parser state should be restored
        assert!(matches!(parser.token, Token::Let { .. }));
    }

    #[test]
    fn test_parser_regions() {
        let mut parser = Parser::new("test.res", "let x = 42");

        // First error in region should be recorded
        parser.err(DiagnosticCategory::Message("test error 1".to_string()));
        assert_eq!(parser.diagnostics().len(), 1);

        // Second error in same region should be silenced
        parser.err(DiagnosticCategory::Message("test error 2".to_string()));
        assert_eq!(parser.diagnostics().len(), 1);

        // New region should allow new errors
        parser.begin_region();
        parser.err(DiagnosticCategory::Message("test error 3".to_string()));
        assert_eq!(parser.diagnostics().len(), 2);

        parser.end_region();
    }

    #[test]
    fn test_parser_comments() {
        let parser = Parser::new("test.res", "// comment\nlet x = 42");
        // The comment should be collected, and we should be at 'let'
        assert!(matches!(parser.token, Token::Let { .. }));
        assert_eq!(parser.comments().len(), 1);
    }

    #[test]
    fn test_parser_is_send_sync() {
        fn assert_send<T: Send>() {}
        // Parser contains Scanner which contains a reference, so not Send
        // But we can still verify the basic types are
        assert_send::<RegionStatus>();
    }
}
