//! Arena for positions and locations during parsing.
//!
//! This module provides efficient storage for source locations in the AST.
//! Instead of storing full Position/Location values everywhere, we store
//! lightweight indices that can be compared cheaply.
//!
//! # Architecture
//!
//! - `PosIdx` and `LocIdx` are lightweight index types (4 bytes each)
//! - `ParseArena` contains arenas for positions and locations
//! - When parsing, positions are pushed to get indices
//! - During marshalling, indices are looked up to get actual values
//!
//! # Example
//!
//! ```ignore
//! use rescript_compiler::parse_arena::{ParseArena, LocIdx, Located};
//! use rescript_compiler::location::Position;
//!
//! let mut arena = ParseArena::new();
//! let start = arena.push_pos("test.res", 1, 0, 0);
//! let end = arena.push_pos("test.res", 1, 0, 10);
//! let loc = arena.mk_loc(start, end);
//!
//! let located = Located::new("hello", loc);
//! assert_eq!(located.txt, "hello");
//! ```

use std::collections::{HashMap, HashSet};

use serde::{Deserialize, Serialize};

use crate::arena::{Arena, ArenaIdx};
use crate::intern::Interner;
use crate::location::{Location, Position};
use crate::parser::longident::Longident;

/// Key for position deduplication.
/// Two positions with the same (file_name, line, bol, cnum) are the same position.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct PosKey {
    file_name: StrIdx,
    line: i32,
    bol: i32,
    cnum: i32,
}

impl PosKey {
    fn from_position(pos: &Position) -> Self {
        Self {
            file_name: pos.file_name,
            line: pos.line,
            bol: pos.bol,
            cnum: pos.cnum,
        }
    }
}

// Re-export StrIdx for convenience
pub use crate::intern::StrIdx;

// ============================================================================
// Index Types
// ============================================================================

/// Index into the position arena.
///
/// This is a lightweight handle (4 bytes) that can be copied and compared
/// cheaply. Two PosIdx values are equal if and only if they refer to the
/// same arena slot.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize, Default)]
pub struct PosIdx(pub u32);

impl ArenaIdx for PosIdx {
    fn from_u32(idx: u32) -> Self {
        PosIdx(idx)
    }
    fn to_u32(self) -> u32 {
        self.0
    }
}

/// Index into the location arena.
///
/// This is a lightweight handle (4 bytes) that can be copied and compared
/// cheaply. Two LocIdx values are equal if and only if they refer to the
/// same arena slot.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize, Default)]
pub struct LocIdx(pub u32);

impl ArenaIdx for LocIdx {
    fn from_u32(idx: u32) -> Self {
        LocIdx(idx)
    }
    fn to_u32(self) -> u32 {
        self.0
    }
}

impl LocIdx {
    /// Check if this is the "none" location (index 0).
    /// The "none" location is pre-allocated at index 0 in every ParseArena.
    pub fn is_none(&self) -> bool {
        self.0 == 0
    }

    /// Create the "none" location index (same as default).
    pub fn none() -> Self {
        Self(0)
    }
}

/// Index into the longident arena.
///
/// This is a lightweight handle (4 bytes) that can be copied and compared
/// cheaply. Two LidentIdx values are equal if and only if they refer to the
/// same arena slot.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize, Default)]
pub struct LidentIdx(pub u32);

impl ArenaIdx for LidentIdx {
    fn from_u32(idx: u32) -> Self {
        LidentIdx(idx)
    }
    fn to_u32(self) -> u32 {
        self.0
    }
}

/// Index into the arity arena.
///
/// This is a lightweight handle (4 bytes) that can be copied and compared
/// cheaply. Two ArityIdx values are equal if and only if they refer to the
/// same arena slot.
///
/// Arity sharing matches OCaml's native compiler CSE behavior:
/// - LITERAL `Some 1` in OCaml source code gets SHARED via constant folding
/// - COMPUTED `Some arity` (where arity is a parameter) creates FRESH objects
///
/// We replicate this with static vs fresh indices:
/// - Static indices for literal paths (use `static_arity_1()`, etc.)
/// - Fresh indices for computed paths (use `push_arity()`)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize, Default)]
pub struct ArityIdx(pub u32);

impl ArenaIdx for ArityIdx {
    fn from_u32(idx: u32) -> Self {
        ArityIdx(idx)
    }
    fn to_u32(self) -> u32 {
        self.0
    }
}

/// Pre-allocated static arity indices that match OCaml's CSE behavior.
///
/// OCaml's native compiler performs Common Subexpression Elimination on
/// literal `Some n` values in source code. When the OCaml parser writes
/// `~arity:(Some 1)` as a literal, all such uses share the same physical object.
/// When it writes `~arity:(Some n)` where n is a computed parameter, each
/// creates a fresh object.
///
/// These static indices correspond to the LITERAL paths in OCaml:
/// - res_core.ml:614 - `Exp.fun_ ~arity:(Some 1)` (underscore sugar)
/// - res_core.ml:4367 - `Typ.arrow ~arity:(Some 1)` (type var arrow)
/// - res_core.ml:4822 - `Typ.arrow ~arity:(Some 1)` (simple arrow type)
/// - res_core.ml:5568 - `Typ.arrow ~arity:(Some 1)` (another arrow case)
#[derive(Debug, Clone, Copy)]
pub struct StaticArities {
    /// Static arity for `None` (unknown arity)
    pub arity_none: ArityIdx,
    /// Static arity for `Some(1)` - used for literal single-argument arrows
    pub arity_1: ArityIdx,
}

/// Pre-allocated `Lident "[]"` and `Lident "::"` for list construction.
///
/// OCaml has TWO distinct sets of these because they come from two different
/// compilation units, each with their own CSE-promoted static allocations:
/// - **Pattern context** (`res_core.ml`): `make_list_pattern` creates `Lident "[]"` and `Lident "::"`
/// - **Expression context** (`ast_helper.ml`): `make_list_expression` creates `Lident "[]"` and `Lident "::"`
///
/// Files with both list patterns AND list expressions will have TWO distinct
/// `Lident "[]"` and TWO distinct `Lident "::"` in the binary AST.
/// Files with only one kind will have just ONE of each (all sharing within that context).
#[derive(Debug, Clone, Copy)]
pub struct StaticListLidents {
    /// `Lident "[]"` for pattern contexts (from res_core.ml)
    pub pat_nil: LidentIdx,
    /// `Lident "::"` for pattern contexts (from res_core.ml)
    pub pat_cons: LidentIdx,
    /// `Lident "[]"` for expression contexts (from ast_helper.ml)
    pub expr_nil: LidentIdx,
    /// `Lident "::"` for expression contexts (from ast_helper.ml)
    pub expr_cons: LidentIdx,
}

// ============================================================================
// InternedLocation (stored in arena)
// ============================================================================

/// A location in a source file (stored in arena).
///
/// This is stored in the ParseArena. Users work with `LocIdx` handles.
/// Note that `loc_start` and `loc_end` are `PosIdx`, not `Position`, so
/// locations reference positions by index rather than storing them inline.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct InternedLocation {
    /// Start position index.
    pub loc_start: PosIdx,
    /// End position index.
    pub loc_end: PosIdx,
    /// Whether this is a "ghost" location (synthesized, not from source).
    pub loc_ghost: bool,
}

impl InternedLocation {
    /// Create a new location from position indices.
    pub fn new(start: PosIdx, end: PosIdx, ghost: bool) -> Self {
        Self {
            loc_start: start,
            loc_end: end,
            loc_ghost: ghost,
        }
    }
}

impl Default for InternedLocation {
    fn default() -> Self {
        // Default to the "none" location (position index 0, ghost = true)
        Self {
            loc_start: PosIdx(0),
            loc_end: PosIdx(0),
            loc_ghost: true,
        }
    }
}

/// Pre-allocated static Longident indices for array operations.
///
/// OCaml's `res_core.ml` creates `Ldot(Lident "Array", "set")` and
/// `Ldot(Lident "Array", "get")` inline during parsing. OCaml's native code
/// compiler lifts these constant expressions to static allocations, so all
/// Array.set/get calls in a file share the same Longident pointer.
///
/// We replicate this by pre-allocating them in the arena.
#[derive(Debug, Clone, Copy)]
pub struct StaticArrayLidents {
    /// `Lident "Array"` prefix shared by Array.get/set.
    pub array_lident: LidentIdx,
    /// `Lident "Belt"` prefix shared by Belt.Array/List.
    pub belt_lident: LidentIdx,
    /// `Ldot(Lident "Belt", "Array")` prefix for Belt.Array.concatMany.
    pub belt_array: LidentIdx,
    /// `Ldot(Lident "Belt", "List")` prefix for Belt.List.concatMany.
    pub belt_list: LidentIdx,
    /// `Ldot(Lident "Array", "set")` for array assignment desugaring
    pub array_set: LidentIdx,
    /// `Ldot(Lident "Array", "get")` for array access desugaring
    pub array_get: LidentIdx,
    /// `Ldot(Ldot(Lident "Belt", "Array"), "concatMany")` for spread array desugaring
    pub belt_array_concat_many: LidentIdx,
    /// `Ldot(Ldot(Lident "Belt", "List"), "concatMany")` for spread list desugaring
    pub belt_list_concat_many: LidentIdx,
}

// ============================================================================
// ParseArena
// ============================================================================

/// Arena for positions and locations during parsing.
///
/// This provides:
/// - Efficient storage: positions/locations stored once, referenced by index
/// - Lightweight handles: indices are 4 bytes, cheap to copy/compare
/// - Identity for marshalling: same index = same object
///
/// This arena deduplicates positions by content - two positions with the same
/// (file_name, line, bol, cnum) will get the same index. This matches OCaml's
/// behavior where the same position captured at different times gets shared.
#[derive(Debug)]
pub struct ParseArena {
    /// Arena of positions (returns PosIdx).
    positions: Arena<Position, PosIdx>,
    /// Arena of locations (returns LocIdx).
    locations: Arena<InternedLocation, LocIdx>,
    /// Arena of longidents (returns LidentIdx).
    longidents: Arena<Longident, LidentIdx>,
    /// Arena of arities (returns ArityIdx).
    /// Use `push_arity()` for computed paths (fresh indices).
    /// Use `static_arities` for literal paths (shared indices).
    arities: Vec<Option<i32>>,
    /// Pre-allocated static arity indices for literal paths.
    /// These match OCaml's CSE behavior where literal `Some 1` values are shared.
    static_arities: StaticArities,
    /// Pre-allocated static Lident indices for list constructors.
    /// Pattern and expression contexts get separate Lidents to match OCaml's
    /// per-compilation-unit CSE behavior.
    static_list_lidents: StaticListLidents,
    /// Pre-allocated static Longident indices for Array.set/get/Belt.Array.concatMany.
    static_array_lidents: StaticArrayLidents,
    /// Pre-allocated `Ldot(Lident "Stdlib_RegExp", "t")` for `%re` lowering.
    /// OCaml uses `Ast_literal.Lid.regexp_id` as a module-level constant.
    static_regexp_t_lident: LidentIdx,
    /// Position deduplication table - maps position content to its index.
    position_dedup: HashMap<PosKey, PosIdx>,
    /// Simple Lident deduplication table - maps StrIdx to its LidentIdx.
    /// This enables sharing of common identifiers like "()", "::", etc.
    lident_dedup: HashMap<StrIdx, LidentIdx>,
    /// StrIdx values whose Lident wrappers should be shared by value during marshalling.
    /// This is used for internal PPX nodes that reuse a common prefix (e.g. `Spice`).
    longident_shareable_strs: HashSet<StrIdx>,
    /// String arena for all identifier strings.
    ///
    /// Strings can be added in two ways:
    /// - `intern(s)`: deduplicated, for static strings (same content = same StrIdx)
    /// - `push_string(s)`: NOT deduplicated, for dynamic strings (each call = new StrIdx)
    ///
    /// At marshal time, same StrIdx = same object = shared via back-references.
    strings: Interner,
    /// Pre-allocated empty string for External_ffi_types primitives.
    /// OCaml shares this literal across all uses in external_ffi_types.ml.
    prim_empty_external_ffi: StrIdx,
    /// Pre-allocated empty string for ast_derive_js_mapper primitives.
    /// This is a separate compilation unit, so it must not share with external_ffi_types.
    prim_empty_js_mapper: StrIdx,
    /// Pre-allocated "#raw_expr" string for raw expression primitives.
    /// OCaml shares this literal across all uses in ast_exp_handle_external.ml.
    prim_raw_expr: StrIdx,
    /// Pre-allocated "#raw_stmt" string for raw statement primitives.
    /// OCaml shares this literal across all uses in ast_exp_handle_external.ml.
    prim_raw_stmt: StrIdx,
    /// PPX-local "==" operator string.
    /// Kept separate from parser-token operator strings to match OCaml unit-local identity.
    ppx_eq_str: StrIdx,
    /// PPX-local "Js" identifier string.
    /// Kept separate from parser-token identifiers to match OCaml unit-local identity.
    ppx_js_str: StrIdx,
    /// Template-literal-local "++" operator string.
    /// Kept separate from regular infix parser operator strings.
    template_concat_str: StrIdx,
    /// Counter for generating unique local module names (for %%private).
    /// OCaml uses a global ref counter, so this matches that behavior.
    local_module_counter: u32,
    /// Expression locations rewritten via the default/generic PPX mapper path.
    ///
    /// This lets marshal distinguish mapper-rebuilt expression attributes
    /// (fresh payload wrappers) from parser-preserved ones.
    rewritten_expr_locs: HashSet<LocIdx>,
    /// Pre-allocated dummy location (line 0, _none_) used by internal PPX.
    dummy_loc: LocIdx,
    /// Spice PPX shared none location (line 1, _none_).
    spice_none_loc: Option<LocIdx>,
    /// Spice PPX shared "Spice" prefix for codecs module (non-interned).
    spice_codecs_str: Option<StrIdx>,
    /// Spice PPX shared "Spice" prefix for records module (non-interned).
    spice_records_str: Option<StrIdx>,
    /// Spice PPX shared "Spice" prefix for variants module (non-interned).
    spice_variants_str: Option<StrIdx>,
    /// Spice PPX shared "Spice" prefix for polyvariants module (non-interned).
    spice_polyvars_str: Option<StrIdx>,
    /// Spice PPX shared "Spice" prefix for tuple module (non-interned).
    spice_tuple_str: Option<StrIdx>,
    /// Spice PPX shared "JSON" prefix (non-interned).
    spice_json_str: Option<StrIdx>,
    /// Spice PPX shared "t" suffix for metaquoted JSON.t (non-interned).
    spice_json_t_str: Option<StrIdx>,
    /// Spice PPX shared Lident for Utils.ctyp_json_t (non-interned JSON).
    spice_json_ctyp_lident: Option<LidentIdx>,
    /// Spice PPX shared "Option" prefix (non-interned).
    spice_option_str: Option<StrIdx>,
    /// Spice PPX shared "Dict" prefix (non-interned).
    spice_dict_str: Option<StrIdx>,
    /// Spice PPX shared "Result" prefix (non-interned).
    spice_result_str: Option<StrIdx>,
    /// Spice PPX shared "Array" prefix (non-interned).
    spice_array_str: Option<StrIdx>,
    /// Spice PPX shared dynamic "v" identifier (non-interned).
    spice_runtime_v: Option<StrIdx>,
    /// Spice PPX shared "v" identifier for pattern variables.
    spice_pat_v: Option<StrIdx>,
    /// Spice PPX shared "v" identifier for record field access expressions.
    spice_field_v: Option<StrIdx>,
    /// Literal strings that should be value-shared during marshalling.
    shareable_literal_strs: HashSet<String>,
}

impl Default for ParseArena {
    fn default() -> Self {
        // Pre-allocate static arities at known indices
        // Index 0: None (unknown arity)
        // Index 1: Some(1) (literal single-argument)
        let arities = vec![None, Some(1)];
        let static_arities = StaticArities {
            arity_none: ArityIdx(0),
            arity_1: ArityIdx(1),
        };

        let mut strings = Interner::new();
        let mut longidents: Arena<Longident, LidentIdx> = Arena::default();

        // Pre-allocate external primitive empty strings.
        // These model literal "" values coming from distinct OCaml compilation units.
        let prim_empty_external_ffi = strings.push(String::new());
        let prim_empty_js_mapper = strings.push(String::new());
        let prim_raw_expr = strings.push("#raw_expr".to_string());
        let prim_raw_stmt = strings.push("#raw_stmt".to_string());
        let ppx_eq_str = strings.push("==".to_string());
        let ppx_js_str = strings.push("Js".to_string());
        let template_concat_str = strings.push("++".to_string());

        // Pre-allocate static list lidents.
        // We need TWO sets: one for pattern contexts (res_core.ml) and one for
        // expression contexts (ast_helper.ml). Each compilation unit in OCaml has
        // its own CSE-promoted statics, so both the Lident blocks AND the inner
        // strings must be distinct objects in the marshal output.
        // Pattern context: use fresh (non-interned) strings so they marshal as
        // separate objects from the expression context strings.
        let pat_nil_str = strings.push("[]".to_string());
        let pat_cons_str = strings.push("::".to_string());
        let pat_nil = longidents.push(Longident::Lident(pat_nil_str));
        let pat_cons = longidents.push(Longident::Lident(pat_cons_str));
        // Expression context: use interned strings (these will also be found by
        // push_lident_static for any other "[]"/"::").
        let expr_nil_str = strings.intern("[]");
        let expr_cons_str = strings.intern("::");
        let expr_nil = longidents.push(Longident::Lident(expr_nil_str));
        let expr_cons = longidents.push(Longident::Lident(expr_cons_str));
        let static_list_lidents = StaticListLidents {
            pat_nil,
            pat_cons,
            expr_nil,
            expr_cons,
        };

        // Seed the lident_dedup table with the expression context lidents.
        // This ensures that push_lident_static("[]") and push_lident_static("::")
        // return the expression-context lidents, which is correct for all non-list
        // pattern uses (e.g., "()").
        let mut lident_dedup = HashMap::new();
        lident_dedup.insert(expr_nil_str, expr_nil);
        lident_dedup.insert(expr_cons_str, expr_cons);

        // Pre-allocate static array operation lidents.
        // OCaml's native code compiler promotes these constant expressions to
        // static allocations, sharing them across all array operations in a file.
        let array_str = strings.intern("Array");
        let set_str = strings.intern("set");
        let get_str = strings.intern("get");
        let belt_str = strings.intern("Belt");
        let concat_many_str = strings.intern("concatMany");

        let lident_array = longidents.push(Longident::Lident(array_str));
        let array_set = longidents.push(Longident::Ldot(
            Box::new(Longident::Lident(array_str)),
            set_str,
        ));
        let array_get = longidents.push(Longident::Ldot(
            Box::new(Longident::Lident(array_str)),
            get_str,
        ));
        let lident_belt = longidents.push(Longident::Lident(belt_str));
        let belt_array = longidents.push(Longident::Ldot(
            Box::new(Longident::Lident(belt_str)),
            array_str,
        ));
        let belt_array_concat_many = longidents.push(Longident::Ldot(
            Box::new(Longident::Ldot(
                Box::new(Longident::Lident(belt_str)),
                array_str,
            )),
            concat_many_str,
        ));
        // Pre-allocate Belt.List.concatMany for list spread desugaring
        let list_str = strings.intern("List");
        let _lident_list = longidents.push(Longident::Lident(list_str));
        let belt_list = longidents.push(Longident::Ldot(
            Box::new(Longident::Lident(belt_str)),
            list_str,
        ));
        let belt_list_concat_many = longidents.push(Longident::Ldot(
            Box::new(Longident::Ldot(
                Box::new(Longident::Lident(belt_str)),
                list_str,
            )),
            concat_many_str,
        ));
        let static_array_lidents = StaticArrayLidents {
            array_lident: lident_array,
            belt_lident: lident_belt,
            belt_array,
            belt_list,
            array_set,
            array_get,
            belt_array_concat_many,
            belt_list_concat_many,
        };

        // Pre-allocate Ast_literal.Lid.regexp_id = Ldot(Lident "Stdlib_RegExp", "t").
        let stdlib_regexp_str = strings.intern("Stdlib_RegExp");
        let regexp_t_str = strings.intern("t");
        let static_regexp_t_lident = longidents.push(Longident::Ldot(
            Box::new(Longident::Lident(stdlib_regexp_str)),
            regexp_t_str,
        ));

        Self {
            positions: Arena::default(),
            locations: Arena::default(),
            longidents,
            arities,
            static_arities,
            static_list_lidents,
            static_array_lidents,
            static_regexp_t_lident,
            position_dedup: HashMap::new(),
            lident_dedup,
            longident_shareable_strs: HashSet::new(),
            strings,
            prim_empty_external_ffi,
            prim_empty_js_mapper,
            prim_raw_expr,
            prim_raw_stmt,
            ppx_eq_str,
            ppx_js_str,
            template_concat_str,
            local_module_counter: 0,
            rewritten_expr_locs: HashSet::new(),
            dummy_loc: LocIdx::default(),
            spice_none_loc: None,
            spice_codecs_str: None,
            spice_records_str: None,
            spice_variants_str: None,
            spice_polyvars_str: None,
            spice_tuple_str: None,
            spice_json_str: None,
            spice_json_t_str: None,
            spice_json_ctyp_lident: None,
            spice_option_str: None,
            spice_dict_str: None,
            spice_result_str: None,
            spice_array_str: None,
            spice_runtime_v: None,
            spice_pat_v: None,
            spice_field_v: None,
            shareable_literal_strs: HashSet::new(),
        }
    }
}

impl ParseArena {
    /// Create a new arena with the "none" position and location pre-allocated at index 0.
    ///
    /// This ensures that `LocIdx::default()` (which is `LocIdx(0)`) always refers to
    /// a valid "none" location, even without calling `none_loc()` first.
    pub fn new() -> Self {
        let mut arena = Self::default();
        // Pre-allocate none file name and position at index 0
        // This way LocIdx::default() == LocIdx(0) is always valid
        let none_file_idx = arena.strings.intern("_none_");
        let none_pos = Position::new(none_file_idx, 1, 0, -1);
        let pos_idx = arena.positions.push(none_pos);
        let none_loc = InternedLocation::new(pos_idx, pos_idx, true);
        arena.locations.push(none_loc);
        // Pre-allocate dummy location with line 0 for internal PPX nodes
        let dummy_file_idx = arena.strings.push("_none_".to_string());
        let dummy_pos = Position::new(dummy_file_idx, 0, 0, -1);
        let dummy_pos_idx = arena.positions.push(dummy_pos);
        let dummy_loc = InternedLocation::new(dummy_pos_idx, dummy_pos_idx, true);
        arena.dummy_loc = arena.locations.push(dummy_loc);
        // Pre-allocate placeholder longident at index 0
        // This way LidentIdx(0) is always a valid "placeholder" identifier
        let placeholder_idx = arena.strings.intern("placeholder");
        arena.longidents.push(Longident::Lident(placeholder_idx));
        arena
    }

    /// Get the placeholder longident index (pre-allocated at index 0).
    /// This is useful for creating placeholder AST nodes without mutating the arena.
    pub fn placeholder_lid(&self) -> LidentIdx {
        LidentIdx(0)
    }

    /// Create a Located<LidentIdx> with the placeholder longident and given location.
    pub fn placeholder_located(&self, loc: LocIdx) -> Located<LidentIdx> {
        Located {
            txt: self.placeholder_lid(),
            loc,
        }
    }

    // ========== Position methods ==========

    /// Push a position into the arena and return its index.
    /// Creates a fresh entry each time - sharing is achieved by passing the same
    /// PosIdx through code paths (reference sharing), not by value deduplication.
    pub fn push_position(&mut self, pos: Position) -> PosIdx {
        let key = PosKey::from_position(&pos);
        let idx = self.positions.push(pos);
        // Register in dedup table only if not already there (for lookup purposes)
        self.position_dedup.entry(key).or_insert(idx);
        idx
    }

    /// Get the index of a position if it exists in the dedup table.
    /// Returns None if this position content hasn't been seen before.
    #[allow(dead_code)]
    pub fn get_position_idx(&self, pos: &Position) -> Option<PosIdx> {
        let key = PosKey::from_position(pos);
        self.position_dedup.get(&key).copied()
    }

    /// Push a position with deduplication - reuses an existing index if the position
    /// content matches.
    pub fn push_position_dedup(&mut self, pos: Position) -> PosIdx {
        let key = PosKey::from_position(&pos);
        if let Some(&idx) = self.position_dedup.get(&key) {
            return idx;
        }
        let idx = self.positions.push(pos);
        self.position_dedup.insert(key, idx);
        idx
    }

    /// Push a position from components.
    /// Creates a fresh position each time (no deduplication).
    /// This matches OCaml's behavior where each position is a separate object.
    /// file_name should be an interned StrIdx (from arena.intern_string).
    pub fn push_pos(&mut self, file_name: StrIdx, line: i32, bol: i32, cnum: i32) -> PosIdx {
        self.positions
            .push(Position::new(file_name, line, bol, cnum))
    }

    /// Get the "none" position index (for _none_ file).
    /// Returns the pre-allocated index 0.
    pub fn none_pos(&self) -> PosIdx {
        PosIdx(0)
    }

    /// Look up a position by index.
    pub fn get_position(&self, idx: PosIdx) -> &Position {
        self.positions.get(idx)
    }

    /// Get all positions (for marshalling).
    pub fn positions(&self) -> &[Position] {
        self.positions.as_slice()
    }

    /// Get total number of positions.
    pub fn position_count(&self) -> usize {
        self.positions.len()
    }

    // ========== Location methods ==========

    /// Push a location into the arena and return its index.
    pub fn push_location(&mut self, loc: InternedLocation) -> LocIdx {
        self.locations.push(loc)
    }

    /// Push a location from position indices.
    pub fn push_loc(&mut self, start: PosIdx, end: PosIdx, ghost: bool) -> LocIdx {
        self.push_location(InternedLocation::new(start, end, ghost))
    }

    /// Create a location from two position indices and push it (non-ghost).
    pub fn mk_loc(&mut self, start: PosIdx, end: PosIdx) -> LocIdx {
        self.push_loc(start, end, false)
    }

    /// Create a location from two raw positions (push both positions first).
    /// Creates fresh positions - sharing is achieved by passing PosIdx through code paths.
    pub fn mk_loc_from_positions(&mut self, start: &Position, end: &Position) -> LocIdx {
        let start_idx = self.push_position(*start);
        let end_idx = self.push_position(*end);
        self.mk_loc(start_idx, end_idx)
    }

    /// Create a location spanning from one location's start to another's end.
    /// Reuses the existing PosIdx values to maintain position sharing.
    pub fn mk_loc_spanning(&mut self, start_loc: LocIdx, end_loc: LocIdx) -> LocIdx {
        let start_pos_idx = self.get_location(start_loc).loc_start;
        let end_pos_idx = self.get_location(end_loc).loc_end;
        self.mk_loc(start_pos_idx, end_pos_idx)
    }

    /// Like mk_loc_spanning, but preserves the ghost flag from the start location.
    /// Use this when the spanning location should inherit ghostness, e.g., for
    /// sequence expressions in braced blocks where the first expression is ghost.
    pub fn mk_loc_spanning_preserve_ghost(&mut self, start_loc: LocIdx, end_loc: LocIdx) -> LocIdx {
        let start_info = self.get_location(start_loc);
        let start_pos_idx = start_info.loc_start;
        let is_ghost = start_info.loc_ghost;
        let end_pos_idx = self.get_location(end_loc).loc_end;
        self.push_loc(start_pos_idx, end_pos_idx, is_ghost)
    }

    /// Get the "none" location index (ghost location with none positions).
    /// Returns the pre-allocated index 0.
    pub fn none_loc(&self) -> LocIdx {
        LocIdx(0)
    }

    /// Get the dummy location index (line 0, _none_ file).
    pub fn dummy_loc(&self) -> LocIdx {
        self.dummy_loc
    }

    /// Clone a location, creating fresh position objects with the same values.
    pub fn clone_loc(&mut self, loc: LocIdx) -> LocIdx {
        let info = self.get_location(loc).clone();
        let start = *self.get_position(info.loc_start);
        let end = *self.get_position(info.loc_end);
        let start_idx = self.push_position(start);
        let end_idx = self.push_position(end);
        self.push_loc(start_idx, end_idx, info.loc_ghost)
    }

    /// Clone a location but keep start/end sharing the same position.
    pub fn clone_loc_shared(&mut self, loc: LocIdx) -> LocIdx {
        let info = self.get_location(loc).clone();
        let start = *self.get_position(info.loc_start);
        let start_idx = self.push_position(start);
        self.push_loc(start_idx, start_idx, info.loc_ghost)
    }

    /// Shared line-1 none location for spice PPX nodes.
    pub fn spice_none_loc(&mut self) -> LocIdx {
        if let Some(loc) = self.spice_none_loc {
            return loc;
        }
        let file_idx = self.push_string("_none_".to_string());
        let pos = Position::new(file_idx, 1, 0, -1);
        let pos_idx = self.push_position(pos);
        let loc = self.push_loc(pos_idx, pos_idx, true);
        self.spice_none_loc = Some(loc);
        loc
    }

    /// Shared non-interned "Spice" prefix for the codecs module.
    pub fn spice_codecs_str(&mut self) -> StrIdx {
        if let Some(idx) = self.spice_codecs_str {
            return idx;
        }
        let idx = self.push_string("Spice".to_string());
        self.longident_shareable_strs.insert(idx);
        self.spice_codecs_str = Some(idx);
        idx
    }

    /// Shared non-interned "Spice" prefix for the records module.
    pub fn spice_records_str(&mut self) -> StrIdx {
        if let Some(idx) = self.spice_records_str {
            return idx;
        }
        let idx = self.push_string("Spice".to_string());
        self.longident_shareable_strs.insert(idx);
        self.spice_records_str = Some(idx);
        idx
    }

    /// Shared non-interned "Spice" prefix for the variants module.
    pub fn spice_variants_str(&mut self) -> StrIdx {
        if let Some(idx) = self.spice_variants_str {
            return idx;
        }
        let idx = self.push_string("Spice".to_string());
        self.longident_shareable_strs.insert(idx);
        self.spice_variants_str = Some(idx);
        idx
    }

    /// Shared non-interned "Spice" prefix for the polyvariants module.
    pub fn spice_polyvars_str(&mut self) -> StrIdx {
        if let Some(idx) = self.spice_polyvars_str {
            return idx;
        }
        let idx = self.push_string("Spice".to_string());
        self.longident_shareable_strs.insert(idx);
        self.spice_polyvars_str = Some(idx);
        idx
    }

    /// Shared non-interned "Spice" prefix for the tuple module.
    pub fn spice_tuple_str(&mut self) -> StrIdx {
        if let Some(idx) = self.spice_tuple_str {
            return idx;
        }
        let idx = self.push_string("Spice".to_string());
        self.longident_shareable_strs.insert(idx);
        self.spice_tuple_str = Some(idx);
        idx
    }

    /// Register a literal string to be value-shared during marshalling.
    pub fn register_shareable_literal(&mut self, s: &str) {
        self.shareable_literal_strs.insert(s.to_string());
    }

    /// Check if a literal string should be value-shared during marshalling.
    pub fn is_shareable_literal(&self, s: &str) -> bool {
        self.shareable_literal_strs.contains(s)
    }

    /// Shared non-interned "JSON" prefix for spice PPX.
    pub fn spice_json_str(&mut self) -> StrIdx {
        if let Some(idx) = self.spice_json_str {
            return idx;
        }
        let idx = self.push_string("JSON".to_string());
        self.longident_shareable_strs.insert(idx);
        self.spice_json_str = Some(idx);
        idx
    }

    /// Shared non-interned "t" suffix for metaquoted JSON.t.
    pub fn spice_json_t_str(&mut self) -> StrIdx {
        if let Some(idx) = self.spice_json_t_str {
            return idx;
        }
        let idx = self.push_string("t".to_string());
        self.spice_json_t_str = Some(idx);
        idx
    }

    /// Shared Lident for Utils.ctyp_json_t (uses a distinct non-interned "JSON").
    pub fn spice_json_ctyp_lident(&mut self) -> LidentIdx {
        if let Some(idx) = self.spice_json_ctyp_lident {
            return idx;
        }
        let json_idx = self.push_string("JSON".to_string());
        let t_idx = self.strings.intern("t");
        let lid = Longident::Ldot(Box::new(Longident::Lident(json_idx)), t_idx);
        let lid_idx = self.longidents.push(lid);
        self.spice_json_ctyp_lident = Some(lid_idx);
        lid_idx
    }

    /// Shared non-interned "Option" prefix for spice PPX.
    pub fn spice_option_str(&mut self) -> StrIdx {
        if let Some(idx) = self.spice_option_str {
            return idx;
        }
        let idx = self.push_string("Option".to_string());
        self.longident_shareable_strs.insert(idx);
        self.spice_option_str = Some(idx);
        idx
    }

    /// Shared non-interned "Dict" prefix for spice PPX.
    pub fn spice_dict_str(&mut self) -> StrIdx {
        if let Some(idx) = self.spice_dict_str {
            return idx;
        }
        let idx = self.push_string("Dict".to_string());
        self.longident_shareable_strs.insert(idx);
        self.spice_dict_str = Some(idx);
        idx
    }

    /// Shared non-interned "Result" prefix for spice PPX.
    pub fn spice_result_str(&mut self) -> StrIdx {
        if let Some(idx) = self.spice_result_str {
            return idx;
        }
        let idx = self.push_string("Result".to_string());
        self.longident_shareable_strs.insert(idx);
        self.spice_result_str = Some(idx);
        idx
    }

    /// Shared non-interned "Array" prefix for spice PPX.
    pub fn spice_array_str(&mut self) -> StrIdx {
        if let Some(idx) = self.spice_array_str {
            return idx;
        }
        let idx = self.push_string("Array".to_string());
        self.longident_shareable_strs.insert(idx);
        self.spice_array_str = Some(idx);
        idx
    }

    /// Shared non-interned "v" identifier for dynamic PPX-generated functions.
    pub fn spice_runtime_v(&mut self) -> StrIdx {
        if let Some(idx) = self.spice_runtime_v {
            return idx;
        }
        let idx = self.push_string("v".to_string());
        self.longident_shareable_strs.insert(idx);
        self.spice_runtime_v = Some(idx);
        idx
    }

    /// Shared non-interned "v" identifier for pattern variables.
    pub fn spice_pat_v(&mut self) -> StrIdx {
        if let Some(idx) = self.spice_pat_v {
            return idx;
        }
        let idx = self.push_string("v".to_string());
        self.spice_pat_v = Some(idx);
        idx
    }

    /// Shared non-interned "v" identifier for record field access expressions.
    pub fn spice_field_v(&mut self) -> StrIdx {
        if let Some(idx) = self.spice_field_v {
            return idx;
        }
        let idx = self.push_string("v".to_string());
        self.spice_field_v = Some(idx);
        idx
    }

    /// Mark a StrIdx as shareable when wrapped in a Longident::Lident.
    pub fn mark_longident_shareable_str(&mut self, idx: StrIdx) {
        self.longident_shareable_strs.insert(idx);
    }

    /// Check if a StrIdx is shareable when wrapped in a Longident::Lident.
    pub fn is_longident_shareable_str(&self, idx: StrIdx) -> bool {
        self.longident_shareable_strs.contains(&idx)
    }

    /// Look up a location by index.
    pub fn get_location(&self, idx: LocIdx) -> &InternedLocation {
        self.locations.get(idx)
    }

    /// Get all locations (for marshalling).
    pub fn locations(&self) -> &[InternedLocation] {
        self.locations.as_slice()
    }

    /// Get total number of locations.
    pub fn location_count(&self) -> usize {
        self.locations.len()
    }

    // ========== Location accessor helpers ==========

    /// Get the start position of a location.
    pub fn loc_start(&self, idx: LocIdx) -> &Position {
        let loc = self.get_location(idx);
        self.get_position(loc.loc_start)
    }

    /// Get the end position of a location.
    pub fn loc_end(&self, idx: LocIdx) -> &Position {
        let loc = self.get_location(idx);
        self.get_position(loc.loc_end)
    }

    /// Get the start position index of a location.
    pub fn loc_start_idx(&self, idx: LocIdx) -> PosIdx {
        self.get_location(idx).loc_start
    }

    /// Get the end position index of a location.
    pub fn loc_end_idx(&self, idx: LocIdx) -> PosIdx {
        self.get_location(idx).loc_end
    }

    /// Check if a location is ghost.
    pub fn loc_ghost(&self, idx: LocIdx) -> bool {
        self.get_location(idx).loc_ghost
    }

    /// Create a ghost version of an existing location.
    /// Returns a new LocIdx with the same positions but loc_ghost=true.
    pub fn mk_ghost_loc(&mut self, idx: LocIdx) -> LocIdx {
        let loc = self.get_location(idx);
        let start = loc.loc_start;
        let end = loc.loc_end;
        self.push_loc(start, end, true)
    }

    /// Reconstruct a full Location struct from a LocIdx.
    /// Useful for code that needs the full Location type (e.g., printer).
    pub fn to_location(&self, idx: LocIdx) -> Location {
        let loc = self.get_location(idx);
        Location {
            loc_start: self.get_position(loc.loc_start).clone(),
            loc_end: self.get_position(loc.loc_end).clone(),
            loc_ghost: loc.loc_ghost,
        }
    }

    /// Convert a full Location to a LocIdx by pushing its positions to the arena.
    /// Useful for migrating code that creates Location values.
    /// Creates fresh positions to match OCaml behavior.
    pub fn from_location(&mut self, loc: &Location) -> LocIdx {
        let start_idx = self.positions.push(loc.loc_start);
        let end_idx = self.positions.push(loc.loc_end);
        self.push_loc(start_idx, end_idx, loc.loc_ghost)
    }

    /// Convert a Located<T> using crate::location::Location to one using LocIdx.
    pub fn from_located<T: Clone>(&mut self, located: &crate::location::Located<T>) -> Located<T> {
        Located {
            txt: located.txt.clone(),
            loc: self.from_location(&located.loc),
        }
    }

    /// Convert a Located<T> using LocIdx to one using crate::location::Location.
    pub fn to_located<T: Clone>(&self, located: &Located<T>) -> crate::location::Located<T> {
        crate::location::Located {
            txt: located.txt.clone(),
            loc: self.to_location(located.loc),
        }
    }

    // ========================================================================
    // String interning
    // ========================================================================

    /// Intern a string, returning its index.
    ///
    /// If the string was previously interned, returns the existing index.
    /// Otherwise, stores the string and returns a new index.
    ///
    /// Use this for strings that should be shared in Marshal output
    /// (matching OCaml's interning behavior).
    pub fn intern(&mut self, s: &str) -> StrIdx {
        self.strings.intern(s)
    }

    /// Get an interned string by index.
    pub fn get_interned(&self, idx: StrIdx) -> &str {
        self.strings.get(idx)
    }

    // ========================================================================
    // Longident arena
    // ========================================================================

    /// Push a longident into the arena and return its index.
    pub fn push_longident(&mut self, lid: Longident) -> LidentIdx {
        self.longidents.push(lid)
    }

    /// Push a simple identifier (Lident) with a dynamic string (from tokens).
    ///
    /// Each call creates a new StrIdx, so same content != same identity.
    /// Use for user identifiers parsed from source (variable names, etc.).
    pub fn push_lident(&mut self, name: impl Into<String>) -> LidentIdx {
        let str_idx = self.strings.push(name.into());
        self.longidents.push(Longident::Lident(str_idx))
    }

    /// Push a simple identifier (Lident) with a static string (interned).
    ///
    /// For static strings (literals in Rust source code), this deduplicates
    /// BOTH the string AND the Lident wrapper:
    /// - same string content = same StrIdx
    /// - same StrIdx = same LidentIdx = shared during marshalling
    ///
    /// Use for operators from Token::to_string and hardcoded identifiers
    /// in the parser like "not", "::", "()", etc.
    pub fn push_lident_static(&mut self, name: &'static str) -> LidentIdx {
        let str_idx = self.strings.intern(name);
        // Check if we already have a Lident for this StrIdx
        if let Some(&lid_idx) = self.lident_dedup.get(&str_idx) {
            return lid_idx;
        }
        // Create new Lident and record for future deduplication
        let lid_idx = self.longidents.push(Longident::Lident(str_idx));
        self.lident_dedup.insert(str_idx, lid_idx);
        lid_idx
    }

    /// Push a simple identifier (Lident) with a StrIdx that already exists.
    ///
    /// This also deduplicates: same StrIdx = same LidentIdx.
    /// Use when you already have a StrIdx (e.g., from a located string).
    pub fn push_lident_from_idx(&mut self, str_idx: StrIdx) -> LidentIdx {
        // Check if we already have a Lident for this StrIdx
        if let Some(&lid_idx) = self.lident_dedup.get(&str_idx) {
            return lid_idx;
        }
        // Create new Lident and record for future deduplication
        let lid_idx = self.longidents.push(Longident::Lident(str_idx));
        self.lident_dedup.insert(str_idx, lid_idx);
        lid_idx
    }

    /// Push a dotted identifier (Ldot) with a dynamic string.
    pub fn push_ldot(&mut self, prefix: LidentIdx, name: impl Into<String>) -> LidentIdx {
        let str_idx = self.strings.push(name.into());
        let prefix_lid = self.get_longident(prefix).clone();
        self.longidents
            .push(Longident::Ldot(Box::new(prefix_lid), str_idx))
    }

    /// Push a dotted identifier (Ldot) with a static string.
    pub fn push_ldot_static(&mut self, prefix: LidentIdx, name: &'static str) -> LidentIdx {
        let str_idx = self.strings.intern(name);
        let prefix_lid = self.get_longident(prefix).clone();
        self.longidents
            .push(Longident::Ldot(Box::new(prefix_lid), str_idx))
    }

    /// Push a functor application (Lapply) into the arena.
    pub fn push_lapply(&mut self, functor: LidentIdx, arg: LidentIdx) -> LidentIdx {
        let func_lid = self.get_longident(functor).clone();
        let arg_lid = self.get_longident(arg).clone();
        self.longidents
            .push(Longident::Lapply(Box::new(func_lid), Box::new(arg_lid)))
    }

    /// Look up a longident by index.
    pub fn get_longident(&self, idx: LidentIdx) -> &Longident {
        self.longidents.get(idx)
    }

    /// Get total number of longidents.
    pub fn longident_count(&self) -> usize {
        self.longidents.len()
    }

    // ========================================================================
    // Arity arena
    // ========================================================================

    /// Push an arity value into the arena - creates a FRESH index.
    ///
    /// Use this for COMPUTED arity paths in the OCaml parser:
    /// - `uncurried_type ~arity:n` (ES6 arrow types with multiple params)
    /// - `uncurried_fun ~arity:n` (function expressions)
    ///
    /// These paths in OCaml create fresh `Some n` objects because the arity
    /// is a computed parameter, not a literal.
    ///
    /// For LITERAL paths (e.g., `~arity:(Some 1)` hardcoded in source),
    /// use `static_arity_1()` instead - those get shared via OCaml's CSE.
    pub fn push_arity(&mut self, arity: Option<i32>) -> ArityIdx {
        let idx = ArityIdx(self.arities.len() as u32);
        self.arities.push(arity);
        idx
    }

    /// Get the static arity index for `None` (unknown arity).
    ///
    /// Use this for LITERAL `~arity:None` paths where OCaml's CSE shares the value.
    pub fn static_arity_none(&self) -> ArityIdx {
        self.static_arities.arity_none
    }

    /// Get the static arity index for `Some(1)`.
    ///
    /// Use this for LITERAL `~arity:(Some 1)` paths in the OCaml parser:
    /// - res_core.ml:614 - `Exp.fun_ ~arity:(Some 1)` (underscore sugar)
    /// - res_core.ml:4367 - `Typ.arrow ~arity:(Some 1)` (type var arrow)
    /// - res_core.ml:4822 - `Typ.arrow ~arity:(Some 1)` (simple arrow type)
    /// - res_core.ml:5568 - `Typ.arrow ~arity:(Some 1)` (another arrow case)
    ///
    /// OCaml's native compiler CSE shares all literal `Some 1` values,
    /// so we return the same pre-allocated index for all these paths.
    pub fn static_arity_1(&self) -> ArityIdx {
        self.static_arities.arity_1
    }

    /// Look up an arity by index.
    pub fn get_arity(&self, idx: ArityIdx) -> Option<i32> {
        self.arities[idx.0 as usize]
    }

    /// Get total number of arities.
    pub fn arity_count(&self) -> usize {
        self.arities.len()
    }

    // ========================================================================
    // Static list lidents
    // ========================================================================

    /// Get the pre-allocated `Lident "[]"` for pattern contexts.
    /// Use in `make_list_pattern` (corresponds to OCaml's res_core.ml).
    pub fn pat_nil(&self) -> LidentIdx {
        self.static_list_lidents.pat_nil
    }

    /// Get the pre-allocated `Lident "::"` for pattern contexts.
    /// Use in `make_list_pattern` and `::` pattern parsing (corresponds to OCaml's res_core.ml).
    pub fn pat_cons(&self) -> LidentIdx {
        self.static_list_lidents.pat_cons
    }

    /// Get the pre-allocated `Lident "[]"` for expression contexts.
    /// Use in `make_list_expression` variants (corresponds to OCaml's ast_helper.ml).
    pub fn expr_nil(&self) -> LidentIdx {
        self.static_list_lidents.expr_nil
    }

    /// Get the pre-allocated `Lident "::"` for expression contexts.
    /// Use in `make_list_expression` variants (corresponds to OCaml's ast_helper.ml).
    pub fn expr_cons(&self) -> LidentIdx {
        self.static_list_lidents.expr_cons
    }

    // ========================================================================
    // Static array lidents
    // ========================================================================

    /// Get the pre-allocated `Ldot(Lident "Array", "set")`.
    /// Use in array assignment desugaring: `arr[i] = v` → `Array.set(arr, i, v)`.
    pub fn array_set_lid(&self) -> LidentIdx {
        self.static_array_lidents.array_set
    }

    /// Get the pre-allocated `Ldot(Lident "Array", "get")`.
    /// Use in array access desugaring: `arr[i]` → `Array.get(arr, i)`.
    pub fn array_get_lid(&self) -> LidentIdx {
        self.static_array_lidents.array_get
    }

    /// Get the pre-allocated `Lident "Array"` prefix.
    pub fn array_lident(&self) -> LidentIdx {
        self.static_array_lidents.array_lident
    }

    /// Get the pre-allocated `Lident "Belt"` prefix.
    pub fn belt_lident(&self) -> LidentIdx {
        self.static_array_lidents.belt_lident
    }

    /// Get the pre-allocated `Ldot(Lident "Belt", "Array")` prefix.
    pub fn belt_array_lident(&self) -> LidentIdx {
        self.static_array_lidents.belt_array
    }

    /// Get the pre-allocated `Ldot(Lident "Belt", "List")` prefix.
    pub fn belt_list_lident(&self) -> LidentIdx {
        self.static_array_lidents.belt_list
    }

    /// Get the pre-allocated `Ldot(Ldot(Lident "Belt", "Array"), "concatMany")`.
    /// Use in spread array desugaring: `[...a, ...b]` → `Belt.Array.concatMany(...)`.
    pub fn belt_array_concat_many_lid(&self) -> LidentIdx {
        self.static_array_lidents.belt_array_concat_many
    }

    /// Get the pre-allocated `Ldot(Ldot(Lident "Belt", "List"), "concatMany")`.
    /// Use in spread list desugaring: `list{...a, ...b}` → `Belt.List.concatMany(...)`.
    pub fn belt_list_concat_many_lid(&self) -> LidentIdx {
        self.static_array_lidents.belt_list_concat_many
    }

    /// Get the static `Stdlib_RegExp.t` longident index used for `%re`.
    pub fn regexp_t_lident(&self) -> LidentIdx {
        self.static_regexp_t_lident
    }

    // ========================================================================
    // Primitive empty strings
    // ========================================================================

    /// Empty string literal from `external_ffi_types.ml` (shared across all its uses).
    pub fn prim_empty_external_ffi(&self) -> StrIdx {
        self.prim_empty_external_ffi
    }

    /// Empty string literal from `ast_derive_js_mapper.ml` (separate unit).
    pub fn prim_empty_js_mapper(&self) -> StrIdx {
        self.prim_empty_js_mapper
    }

    pub fn prim_raw_expr(&self) -> StrIdx {
        self.prim_raw_expr
    }

    pub fn prim_raw_stmt(&self) -> StrIdx {
        self.prim_raw_stmt
    }

    pub fn ppx_eq_str(&self) -> StrIdx {
        self.ppx_eq_str
    }

    pub fn ppx_js_str(&self) -> StrIdx {
        self.ppx_js_str
    }

    pub fn template_concat_str(&self) -> StrIdx {
        self.template_concat_str
    }

    /// Get the string content for a StrIdx.
    pub fn get_string(&self, idx: StrIdx) -> &str {
        self.strings.get(idx)
    }

    /// Intern a string (returns existing idx if already interned).
    pub fn intern_string(&mut self, s: &str) -> StrIdx {
        self.strings.intern(s)
    }

    /// Push a string without deduplication (for dynamic user-input strings).
    pub fn push_string(&mut self, s: String) -> StrIdx {
        self.strings.push(s)
    }

    /// Generate the next local module name for %%private expansion.
    /// Returns "local_1", "local_2", etc. matching OCaml's behavior.
    pub fn next_local_module_name(&mut self) -> StrIdx {
        self.local_module_counter += 1;
        self.push_string(format!("local_{}", self.local_module_counter))
    }

    /// Mark an expression location as rewritten by the generic PPX mapper path.
    pub fn mark_rewritten_expr_loc(&mut self, loc: LocIdx) {
        self.rewritten_expr_locs.insert(loc);
    }

    /// Returns true when this expression location was rewritten generically.
    pub fn is_rewritten_expr_loc(&self, loc: LocIdx) -> bool {
        self.rewritten_expr_locs.contains(&loc)
    }

    /// Check if a longident is a simple Lident with the given name.
    pub fn is_lident(&self, idx: LidentIdx, name: &str) -> bool {
        match self.get_longident(idx) {
            Longident::Lident(str_idx) => self.strings.get(*str_idx) == name,
            _ => false,
        }
    }

    /// Check if a longident is a simple Lident (not dotted).
    pub fn is_simple_lident(&self, idx: LidentIdx) -> bool {
        matches!(self.get_longident(idx), Longident::Lident(_))
    }

    /// Check if a longident is an Ldot (qualified/dotted identifier).
    pub fn is_ldot(&self, idx: LidentIdx) -> bool {
        matches!(self.get_longident(idx), Longident::Ldot(..))
    }

    /// Get the last component of a longident as a string.
    pub fn lident_last(&self, idx: LidentIdx) -> &str {
        let str_idx = self.get_longident(idx).last_idx();
        self.strings.get(str_idx)
    }

    /// Convert a Located<LidentIdx> to Located<Longident>.
    /// Useful when you need to match on the Longident structure.
    pub fn to_longident_loc(
        &self,
        loc: &Located<LidentIdx>,
    ) -> crate::location::Located<Longident> {
        crate::location::Located {
            txt: self.get_longident(loc.txt).clone(),
            loc: self.to_location(loc.loc),
        }
    }
}

// ============================================================================
// Located<T> - A value with its source location
// ============================================================================

/// A value annotated with its source location (using LocIdx).
///
/// This is equivalent to OCaml's `'a loc` type, but uses `LocIdx` for efficiency.
/// This is the type to use in the AST for minimal memory footprint.
///
/// Note: There is also `crate::location::Located<T>` which stores a full
/// `Location` instead of `LocIdx`. Use that when you don't have access to
/// a ParseArena or need the full location data inline.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Located<T> {
    /// The value.
    pub txt: T,
    /// Location in source (as index).
    pub loc: LocIdx,
}

// Implement Copy for Located<T> when T: Copy (e.g., Located<StrIdx>)
impl<T: Copy> Copy for Located<T> {}

impl<T> Located<T> {
    /// Create a new located value.
    pub fn new(txt: T, loc: LocIdx) -> Self {
        Self { txt, loc }
    }

    /// Create a located value with the default "none" location.
    ///
    /// This uses `LocIdx::default()` which is `LocIdx(0)`, the pre-allocated
    /// none location in every ParseArena.
    pub fn mknoloc(txt: T) -> Self {
        Self {
            txt,
            loc: LocIdx::default(),
        }
    }

    /// Map the value while keeping the location.
    pub fn map<U, F: FnOnce(T) -> U>(self, f: F) -> Located<U> {
        Located {
            txt: f(self.txt),
            loc: self.loc,
        }
    }

    /// Get a reference to the text.
    pub fn as_ref(&self) -> Located<&T> {
        Located {
            txt: &self.txt,
            loc: self.loc,
        }
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_position_push() {
        let mut arena = ParseArena::new();
        let base_count = arena.position_count();
        assert_eq!(base_count, 1); // Pre-allocated none position

        let idx1 = arena.push_pos("test.res", 1, 0, 5);
        let idx2 = arena.push_pos("test.res", 1, 0, 5);
        let idx3 = arena.push_pos("test.res", 1, 0, 10);

        // Each push creates a new entry (no deduplication)
        assert_ne!(idx1, idx2);
        assert_ne!(idx1, idx3);
        assert_ne!(idx2, idx3);

        assert_eq!(arena.position_count(), base_count + 3);
    }

    #[test]
    fn test_location_push() {
        let mut arena = ParseArena::new();
        let base_count = arena.location_count();
        assert_eq!(base_count, 1); // Pre-allocated none location

        let start = arena.push_pos("test.res", 1, 0, 0);
        let end = arena.push_pos("test.res", 1, 0, 10);

        let loc1 = arena.mk_loc(start, end);
        let loc2 = arena.mk_loc(start, end);

        // Each push creates a new entry (no deduplication)
        assert_ne!(loc1, loc2);

        assert_eq!(arena.location_count(), base_count + 2);
    }

    #[test]
    fn test_none_at_index_zero() {
        let arena = ParseArena::new();

        let none_pos = arena.none_pos();
        let none_loc = arena.none_loc();

        assert_eq!(none_pos, PosIdx(0));
        assert_eq!(none_loc, LocIdx(0));
        assert_eq!(LocIdx::default(), none_loc);

        let pos = arena.get_position(none_pos);
        assert_eq!(pos.file_name, "_none_");
        assert!(arena.loc_ghost(none_loc));
    }

    #[test]
    fn test_located() {
        let arena = ParseArena::new();
        let loc = arena.none_loc();

        let located = Located::new("hello".to_string(), loc);
        assert_eq!(located.txt, "hello");
        assert_eq!(located.loc, loc);
    }

    #[test]
    fn test_mk_loc_from_positions() {
        let mut arena = ParseArena::new();

        let start = Position::new("test.res", 1, 0, 0);
        let end = Position::new("test.res", 1, 0, 10);

        let loc = arena.mk_loc_from_positions(&start, &end);

        assert_eq!(arena.loc_start(loc).line, 1);
        assert_eq!(arena.loc_end(loc).cnum, 10);
    }

    #[test]
    fn test_to_location() {
        let mut arena = ParseArena::new();

        let start = Position::new("test.res", 1, 0, 0);
        let end = Position::new("test.res", 1, 0, 10);

        let loc_idx = arena.mk_loc_from_positions(&start, &end);
        let loc = arena.to_location(loc_idx);

        assert_eq!(loc.loc_start.line, 1);
        assert_eq!(loc.loc_end.cnum, 10);
        assert!(!loc.loc_ghost);
    }

    #[test]
    fn test_mk_loc_spanning() {
        let mut arena = ParseArena::new();

        let pos1 = arena.push_pos("test.res", 1, 0, 0);
        let pos2 = arena.push_pos("test.res", 1, 0, 5);
        let pos3 = arena.push_pos("test.res", 2, 20, 25);
        let pos4 = arena.push_pos("test.res", 2, 20, 30);

        let loc1 = arena.mk_loc(pos1, pos2);
        let loc2 = arena.mk_loc(pos3, pos4);

        let spanning = arena.mk_loc_spanning(loc1, loc2);

        assert_eq!(arena.loc_start(spanning).line, 1);
        assert_eq!(arena.loc_start(spanning).cnum, 0);
        assert_eq!(arena.loc_end(spanning).line, 2);
        assert_eq!(arena.loc_end(spanning).cnum, 30);
    }
}
