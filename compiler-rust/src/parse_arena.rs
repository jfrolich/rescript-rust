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
use std::sync::OnceLock;
use std::sync::atomic::{AtomicUsize, Ordering};

use serde::{Deserialize, Serialize};

use crate::arena::{Arena, ArenaIdx};
use crate::intern::Interner;
use crate::location::{Location, Position};
use crate::parser::ast::{
    Attributes, CoreType, CoreTypeDesc, Expression, ExpressionDesc, FunParam, ModuleExpr,
    ModuleExprDesc, ModuleType, ModuleTypeDesc, Pattern, PatternDesc, StringLoc, ValueConstraint,
};
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

// ============================================================================
// AST Node Index Types
// ============================================================================

/// Index into the expression arena.
///
/// Replaces `Box<Expression>` for recursive AST references. 4 bytes instead
/// of 8 bytes (pointer), and eliminates per-node heap allocation. The
/// Expression is stored in a flat `Vec<Expression>` pool in `ParseArena`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct ExprIdx(pub u32);

impl ArenaIdx for ExprIdx {
    fn from_u32(idx: u32) -> Self {
        ExprIdx(idx)
    }
    fn to_u32(self) -> u32 {
        self.0
    }
}

/// Index into the pattern arena.
///
/// Replaces `Box<Pattern>` for recursive AST references. 4 bytes instead
/// of 8 bytes (pointer), eliminates per-node heap allocation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct PatIdx(pub u32);

impl ArenaIdx for PatIdx {
    fn from_u32(idx: u32) -> Self {
        PatIdx(idx)
    }
    fn to_u32(self) -> u32 {
        self.0
    }
}

/// Index into the core type arena.
///
/// Replaces `Box<CoreType>` for recursive AST references. 4 bytes instead
/// of 8 bytes (pointer), eliminates per-node heap allocation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct CoreTypeIdx(pub u32);

impl ArenaIdx for CoreTypeIdx {
    fn from_u32(idx: u32) -> Self {
        CoreTypeIdx(idx)
    }
    fn to_u32(self) -> u32 {
        self.0
    }
}

/// Index into the module expression arena.
///
/// Replaces `Box<ModuleExpr>` for recursive AST references.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct ModExprIdx(pub u32);

impl ArenaIdx for ModExprIdx {
    fn from_u32(idx: u32) -> Self {
        ModExprIdx(idx)
    }
    fn to_u32(self) -> u32 {
        self.0
    }
}

/// Index into the module type arena.
///
/// Replaces `Box<ModuleType>` for recursive AST references.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct ModTypeIdx(pub u32);

impl ArenaIdx for ModTypeIdx {
    fn from_u32(idx: u32) -> Self {
        ModTypeIdx(idx)
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
    /// Static arity for parser `Some(1)` literals (`res_core.ml` paths).
    pub arity_1: ArityIdx,
    /// Static arity for PPX/frontend `Some(1)` literals (`Ast_compatible.fun_` paths).
    pub arity_ppx_1: ArityIdx,
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
    /// `Lident "Primitive_array"` used by array spread lowering.
    pub belt_lident: LidentIdx,
    /// Alias of the `Primitive_array` prefix retained for marshal handling.
    pub belt_array: LidentIdx,
    /// `Lident "Primitive_list"` used by list spread lowering.
    pub belt_list: LidentIdx,
    /// `Ldot(Lident "Array", "set")` for array assignment desugaring
    pub array_set: LidentIdx,
    /// `Ldot(Lident "Array", "get")` for array access desugaring
    pub array_get: LidentIdx,
    /// `Ldot(Lident "Primitive_array", "spread")` for spread array desugaring.
    pub belt_array_concat_many: LidentIdx,
    /// `Ldot(Lident "Primitive_list", "spread")` for spread list desugaring.
    pub belt_list_concat_many: LidentIdx,
}

/// Pre-allocated static Longident indices for `%external` PPX helpers.
///
/// OCaml reuses these longident constants (`Js.typeof`, `Js.undefinedToOption`,
/// `Js.Undefined`, `Js.Undefined.empty`) across `%external` rewrites.
/// It also reuses `Ast_literal.Lid.js_oo` and `Ast_literal.Lid.js_meth_callback`
/// across `@this` callback rewrites.
#[derive(Debug, Clone, Copy)]
pub struct StaticPpxLidents {
    pub js_lident: LidentIdx,
    pub js_typeof: LidentIdx,
    pub js_undefined_to_option: LidentIdx,
    pub js_undefined: LidentIdx,
    pub js_undefined_empty: LidentIdx,
    pub js_oo_lident: LidentIdx,
    pub js_oo_callback: LidentIdx,
}

/// Pre-allocated `Ast_literal` core type nodes used by PPX rewrites.
///
/// OCaml's `ast_literal.ml` exposes module-level constants for these no-loc
/// core types. Reusing one arena index per type mirrors that pointer identity.
#[derive(Debug, Clone, Copy)]
pub struct StaticAstLiteralTypes {
    pub type_string: CoreTypeIdx,
    pub type_int: CoreTypeIdx,
    pub type_bool: CoreTypeIdx,
    pub type_float: CoreTypeIdx,
}

#[derive(Clone, Copy, Debug)]
enum SpiceStringKey {
    Codecs,
    Records,
    Variants,
    Polyvars,
    Tuple,
    Json,
    JsonT,
    Option,
    Dict,
    Result,
    Array,
    RuntimeV,
    PatV,
    FieldV,
}

impl SpiceStringKey {
    const COUNT: usize = 14;

    fn idx(self) -> usize {
        self as usize
    }
}

#[derive(Debug)]
struct SpiceCache {
    none_loc: Option<LocIdx>,
    json_ctyp_lident: Option<LidentIdx>,
    strings: [Option<StrIdx>; SpiceStringKey::COUNT],
}

impl SpiceCache {
    fn new() -> Self {
        Self {
            none_loc: None,
            json_ctyp_lident: None,
            strings: [None; SpiceStringKey::COUNT],
        }
    }

    fn get_string(&self, key: SpiceStringKey) -> Option<StrIdx> {
        self.strings[key.idx()]
    }

    fn set_string(&mut self, key: SpiceStringKey, idx: StrIdx) {
        self.strings[key.idx()] = Some(idx);
    }
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
    /// Slots reserved before type checking for environment-dependent synthetic
    /// longidents, such as record-field qualification and omitted labels.
    synthetic_longidents: Box<[OnceLock<Longident>]>,
    next_synthetic_longident: AtomicUsize,
    synthetic_longident_base: u32,
    /// Arena of arities (returns ArityIdx).
    /// Use `push_arity()` for computed paths (fresh indices).
    /// Use `static_arities` for literal paths (shared indices).
    arities: Vec<Option<i32>>,
    /// Arena of expressions (returns ExprIdx).
    /// Replaces `Box<Expression>` for recursive AST references.
    expressions: Arena<Expression, ExprIdx>,
    /// Intentional Rust performance representation for expression fields that
    /// are usually absent.
    ///
    /// OCaml compiler/ml/parsetree.ml:210-214 stores one expression record,
    /// and parsetree.ml:226-298 stores these payloads directly inside
    /// `expression_desc` variants. The arena parser keeps them in side tables
    /// keyed by stable `ExprIdx` so common expression nodes stay compact. Do
    /// not move these back inline during parity cleanup unless the replacement
    /// keeps the same AST behavior and comparable parser memory profile.
    /// Sparse side table for function default expressions, keyed by function ExprIdx.
    expr_fun_defaults: Vec<Option<ExprIdx>>,
    /// N-ary source parameter lists keyed by the function body's arena index.
    ///
    /// `PexpFun` keeps only a compact first-parameter fallback for frozen-v0 PPX
    /// conversion. Parser-created current parsetrees use this table as the
    /// authoritative `Pexp_fun.params` representation.
    nary_fun_params_by_first_pattern: HashMap<PatIdx, Box<[FunParam]>>,
    nary_fun_unknown_arity_by_first_pattern: HashMap<PatIdx, ArityIdx>,
    /// Optional-default lowering prepared before type checking.
    ///
    /// Typecore must not append to the parse arena through a shared reference:
    /// doing so invalidates Rust's aliasing guarantees and was miscompiled in
    /// release builds. Keep the OCaml-shaped synthetic AST here, constructed
    /// while the arena is still exclusively borrowed.
    nary_fun_default_bindings_by_first_pattern:
        HashMap<PatIdx, Box<[(FunParam, Option<crate::parser::ast::ValueBinding>)]>>,
    /// N-ary locally-abstract-type (`newtypes`) lists keyed by the function's
    /// first parameter pattern, mirroring `Pexp_fun.newtypes` in the current
    /// upstream parsetree. Each entry is `(name, attributes)`; the parser puts
    /// the type-parameter group's attributes on the group's first newtype.
    nary_fun_newtypes_by_first_pattern: HashMap<PatIdx, Box<[(StringLoc, Attributes)]>>,
    nary_arrow_args_by_first_type: HashMap<CoreTypeIdx, Box<[crate::parser::ast::TypeArg]>>,
    /// Sparse current-Parsetree value constraints keyed by the binding pattern.
    value_constraints_by_pattern: HashMap<PatIdx, ValueConstraint>,
    /// Sparse side table for case guards, keyed by owning match/try ExprIdx.
    /// Value is a case-indexed list of optional guard expressions.
    expr_case_guards: Vec<Option<Box<[Option<ExprIdx>]>>>,
    /// Sparse side table for constructor payload argument, keyed by construct ExprIdx.
    expr_construct_args: Vec<Option<ExprIdx>>,
    /// Sparse side table for polymorphic variant payload argument, keyed by variant ExprIdx.
    expr_variant_args: Vec<Option<ExprIdx>>,
    /// Sparse side table for record spread/base expression, keyed by record ExprIdx.
    expr_record_spreads: Vec<Option<ExprIdx>>,
    /// Sparse side table for record-rest pattern bindings (`...T as r`),
    /// keyed by the record pattern's own location index.
    ///
    /// OCaml compiler/ml/parsetree.ml:164-168 stores `record_pat_rest` inline
    /// in `Ppat_record`. The arena parser keeps it in a sparse side table keyed
    /// by the record pattern's `ppat_loc` (a stable arena index available both
    /// at parse time and during type checking).
    pat_record_rests: HashMap<LocIdx, crate::parser::ast::RecordPatRest>,
    /// Sparse side table for if-then-else else branch expression, keyed by if ExprIdx.
    expr_if_else_branches: Vec<Option<ExprIdx>>,
    /// Sparse side table for `Pexp_coerce` source type annotation, keyed by coerce ExprIdx.
    expr_coerce_from_types: Vec<Option<CoreTypeIdx>>,
    /// Arena of patterns (returns PatIdx).
    /// Replaces `Box<Pattern>` for recursive AST references.
    patterns: Arena<Pattern, PatIdx>,
    /// Slots exclusively reserved before type checking for OCaml-shaped
    /// synthetic pattern rewrites. `OnceLock` permits one-time initialization
    /// through the shared arena reference held by `TypeCheckContext` without
    /// violating aliasing rules or moving parser-created patterns.
    synthetic_patterns: Box<[OnceLock<Pattern>]>,
    next_synthetic_pattern: AtomicUsize,
    synthetic_pattern_base: u32,
    /// Slots reserved before type checking for strings discovered only after
    /// environment lookup (notably omitted record labels).
    synthetic_strings: Box<[OnceLock<String>]>,
    next_synthetic_string: AtomicUsize,
    synthetic_string_base: u32,
    /// Arena of core types (returns CoreTypeIdx).
    /// Replaces `Box<CoreType>` for recursive AST references.
    core_types: Arena<CoreType, CoreTypeIdx>,
    /// Arena of module expressions (returns ModExprIdx).
    /// Replaces `Box<ModuleExpr>` for recursive AST references.
    mod_exprs: Arena<ModuleExpr, ModExprIdx>,
    /// Arena of module types (returns ModTypeIdx).
    /// Replaces `Box<ModuleType>` for recursive AST references.
    mod_types: Arena<ModuleType, ModTypeIdx>,
    /// Pre-allocated static arity indices for literal paths.
    /// These match OCaml's CSE behavior where literal `Some 1` values are shared.
    static_arities: StaticArities,
    /// Pre-allocated static Lident indices for list constructors.
    /// Pattern and expression contexts get separate Lidents to match OCaml's
    /// per-compilation-unit CSE behavior.
    static_list_lidents: StaticListLidents,
    /// Pre-allocated static Longident indices for array access and spread lowering.
    static_array_lidents: StaticArrayLidents,
    /// Pre-allocated `Ldot(Lident "Stdlib_RegExp", "t")` for `%re` lowering.
    /// OCaml uses `Ast_literal.Lid.regexp_id` as a module-level constant.
    static_regexp_t_lident: LidentIdx,
    /// Pre-allocated `Ldot(Lident "*predef*", "option")` for lifted option types.
    /// OCaml uses `Ast_literal.predef_option` as a module-level constant.
    static_predef_option_lident: LidentIdx,
    /// Pre-allocated no-loc builtin types from `Ast_literal.No_loc`.
    static_ast_literal_types: StaticAstLiteralTypes,
    /// Pre-allocated `Lident "string"` for `Ast_literal.No_loc.type_string`.
    static_ast_literal_type_string_lident: LidentIdx,
    /// Pre-allocated `Lident "int"` for `Ast_literal.No_loc.type_int`.
    static_ast_literal_type_int_lident: LidentIdx,
    /// Pre-allocated `Lident "bool"` for `Ast_literal.No_loc.type_bool`.
    static_ast_literal_type_bool_lident: LidentIdx,
    /// Pre-allocated `Lident "float"` for `Ast_literal.type_float`.
    static_ast_literal_type_float_lident: LidentIdx,
    /// Pre-allocated placeholder longident (Lident "placeholder").
    /// Allocated in `new()`, not `default()`.
    static_placeholder_lid: LidentIdx,
    /// Pre-allocated `Lident "None"` for optional field desugaring.
    /// Allocated in `new()`, not `default()`.
    static_none_lid: LidentIdx,
    /// Pre-allocated `Ldot(Lident "*predef*", "None")` for optional-default rewrites.
    static_predef_none_lid: LidentIdx,
    /// Pre-allocated `Lident "Some"` for unqualified option wrapping paths.
    static_some_lid: LidentIdx,
    /// Pre-allocated `Ldot(Lident "*predef*", "Some")` for optional-default rewrites.
    static_predef_some_lid: LidentIdx,
    /// Pre-allocated `Lident "*opt*"` for optional-default rewrite binding names.
    static_optional_default_opt_lid: LidentIdx,
    /// Pre-allocated `Lident "*sth*"` for optional-default rewrite match payload names.
    static_optional_default_sth_lid: LidentIdx,
    /// Pre-allocated `"*opt*"` string for optional-default rewrite binding names.
    static_optional_default_opt_str: StrIdx,
    /// Pre-allocated `"*sth*"` string for optional-default rewrite match payload names.
    static_optional_default_sth_str: StrIdx,
    /// Pre-allocated `"#default"` attribute name used by optional-default rewrite lets.
    static_default_attr_str: StrIdx,
    /// Pre-allocated `"res.constructor_from_spread"` attribute name used by variant spreads.
    static_constructor_from_spread_attr_str: StrIdx,
    /// Pre-allocated `"res.patFromVariantSpread"` attribute name used for synthetic spread patterns.
    static_pat_from_variant_spread_attr_str: StrIdx,
    /// Pre-allocated static longidents used by `%external` rewrite helpers.
    static_ppx_lidents: StaticPpxLidents,
    /// Position deduplication table - maps position content to its index.
    position_dedup: HashMap<PosKey, PosIdx>,
    /// Simple Lident deduplication table - maps StrIdx to its LidentIdx.
    /// This enables sharing of common identifiers like "()", "::", etc.
    lident_dedup: HashMap<StrIdx, LidentIdx>,
    /// StrIdx values whose Lident wrappers should be shared by value during marshalling.
    /// This is used for internal PPX nodes that reuse a common prefix (e.g. `Spice`).
    longident_shareable_strs: HashSet<StrIdx>,
    /// Optional parent `LidentIdx` for `Ldot` nodes created via `push_ldot*`.
    /// This preserves prefix identity during marshal writing for PPX-generated paths.
    ldot_prefix_idx_table: HashMap<LidentIdx, LidentIdx>,
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
    /// PPX-local empty string literal.
    /// Used for `%external` string delimiters (`Some ""`) in ast_exp_handle_external.ml.
    ppx_empty_str: StrIdx,
    /// PPX-local `"undefined"` string literal.
    /// Used in `%external` rewrites (`Js.typeof(...) == "undefined"`).
    ppx_undefined_str: StrIdx,
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
    /// Spice PPX local caches for generated location/string/lident nodes.
    spice_cache: SpiceCache,
    /// Literal strings that should be value-shared during marshalling.
    shareable_literal_strs: HashSet<String>,
    /// Explicit constant-string identity registration `(ptr,len) -> StrIdx`.
    ///
    /// Used for narrow PPX parity cases where a `Constant::String` should
    /// share with a specific arena string identity.
    constant_string_identity_to_idx: HashMap<(usize, usize), StrIdx>,
    /// Source string identity for Ptyp_var nodes created by varification.
    ///
    /// When locally-abstract type varification converts `Ptyp_constr` to
    /// `Ptyp_var`, OCaml keeps sharing with the original constructor string.
    /// We record that source `StrIdx` by `CoreType.ptyp_loc` to reproduce the
    /// same marshal sharing.
    tyvar_source_by_loc: HashMap<LocIdx, StrIdx>,
}

impl Default for ParseArena {
    fn default() -> Self {
        // Pre-allocate static arities at known indices
        // Index 0: None (unknown arity)
        // Index 1: Some(1) for parser literals
        // Index 2: Some(1) for PPX/frontend literals
        let arities = vec![None, Some(1), Some(1)];
        let static_arities = StaticArities {
            arity_none: ArityIdx(0),
            arity_1: ArityIdx(1),
            arity_ppx_1: ArityIdx(2),
        };

        let mut strings = Interner::new();
        let mut longidents: Arena<Longident, LidentIdx> = Arena::default();
        let mut core_types: Arena<CoreType, CoreTypeIdx> = Arena::default();

        // Pre-allocate external primitive empty strings.
        // These model literal "" values coming from distinct OCaml compilation units.
        let prim_empty_external_ffi = strings.push(String::new());
        let prim_empty_js_mapper = strings.push(String::new());
        let prim_raw_expr = strings.push("#raw_expr".to_string());
        let prim_raw_stmt = strings.push("#raw_stmt".to_string());
        let ppx_eq_str = strings.push("==".to_string());
        let ppx_js_str = strings.push("Js".to_string());
        let ppx_empty_str = strings.push(String::new());
        let ppx_undefined_str = strings.push("undefined".to_string());
        let template_concat_str = strings.push("++".to_string());
        let static_optional_default_opt_str = strings.intern("*opt*");
        let static_optional_default_sth_str = strings.intern("*sth*");
        let static_default_attr_str = strings.intern("#default");
        let static_constructor_from_spread_attr_str = strings.intern("res.constructor_from_spread");
        let static_pat_from_variant_spread_attr_str = strings.intern("res.patFromVariantSpread");
        // CMI-loaded declaration attributes are converted back into parser attrs
        // during typedtree reconstruction. Pre-intern the common decl-attr names
        // that can arrive from external CMIs so that round-tripping imported
        // attrs does not depend on local source text having mentioned them.
        let _ = strings.intern("as");
        let _ = strings.intern("deprecated");
        let _ = strings.intern("tag");
        let _ = strings.intern("unboxed");
        let _ = strings.intern("genType");
        let _ = strings.intern("spice");
        let static_optional_default_opt_lid =
            longidents.push(Longident::Lident(static_optional_default_opt_str));
        let static_optional_default_sth_lid =
            longidents.push(Longident::Lident(static_optional_default_sth_str));

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

        // Pre-allocate static `%external` helper longidents.
        let ppx_js_lident = longidents.push(Longident::Lident(ppx_js_str));
        lident_dedup.insert(ppx_js_str, ppx_js_lident);
        let ppx_typeof_str = strings.intern("typeof");
        let ppx_undefined_to_option_str = strings.intern("undefinedToOption");
        let ppx_undefined_ctor_str = strings.intern("Undefined");
        let ppx_empty_field_str = strings.intern("empty");
        let ppx_js_typeof = longidents.push(Longident::Ldot(
            Box::new(Longident::Lident(ppx_js_str)),
            ppx_typeof_str,
        ));
        let ppx_js_undefined_to_option = longidents.push(Longident::Ldot(
            Box::new(Longident::Lident(ppx_js_str)),
            ppx_undefined_to_option_str,
        ));
        let ppx_js_undefined = longidents.push(Longident::Ldot(
            Box::new(Longident::Lident(ppx_js_str)),
            ppx_undefined_ctor_str,
        ));
        let ppx_js_undefined_empty = longidents.push(Longident::Ldot(
            Box::new(Longident::Ldot(
                Box::new(Longident::Lident(ppx_js_str)),
                ppx_undefined_ctor_str,
            )),
            ppx_empty_field_str,
        ));
        let ppx_js_oo_str = strings.intern("Primitive_js_extern");
        let ppx_callback_str = strings.intern("Callback");
        let ppx_js_oo_lident = longidents.push(Longident::Lident(ppx_js_oo_str));
        lident_dedup.insert(ppx_js_oo_str, ppx_js_oo_lident);
        let ppx_js_oo_callback = longidents.push(Longident::Ldot(
            Box::new(Longident::Lident(ppx_js_oo_str)),
            ppx_callback_str,
        ));
        let static_ppx_lidents = StaticPpxLidents {
            js_lident: ppx_js_lident,
            js_typeof: ppx_js_typeof,
            js_undefined_to_option: ppx_js_undefined_to_option,
            js_undefined: ppx_js_undefined,
            js_undefined_empty: ppx_js_undefined_empty,
            js_oo_lident: ppx_js_oo_lident,
            js_oo_callback: ppx_js_oo_callback,
        };
        let mut ldot_prefix_idx_table = HashMap::new();
        ldot_prefix_idx_table.insert(ppx_js_typeof, ppx_js_lident);
        ldot_prefix_idx_table.insert(ppx_js_undefined_to_option, ppx_js_lident);
        ldot_prefix_idx_table.insert(ppx_js_undefined, ppx_js_lident);
        ldot_prefix_idx_table.insert(ppx_js_undefined_empty, ppx_js_undefined);
        ldot_prefix_idx_table.insert(ppx_js_oo_callback, ppx_js_oo_lident);

        // Pre-allocate static array operation lidents.
        // OCaml's native code compiler promotes these constant expressions to
        // static allocations, sharing them across all array operations in a file.
        let array_str = strings.intern("Array");
        let set_str = strings.intern("set");
        let get_str = strings.intern("get");
        let belt_str = strings.intern("Primitive_array");
        let concat_many_str = strings.intern("spread");

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
        let belt_array = lident_belt;
        let belt_array_concat_many = longidents.push(Longident::Ldot(
            Box::new(Longident::Lident(belt_str)),
            concat_many_str,
        ));
        // Pre-allocate Primitive_list.spread for list spread desugaring.
        let list_str = strings.intern("Primitive_list");
        let belt_list = longidents.push(Longident::Lident(list_str));
        let belt_list_concat_many = longidents.push(Longident::Ldot(
            Box::new(Longident::Lident(list_str)),
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

        // Pre-allocate Ast_literal.predef_option = Ldot(Lident "*predef*", "option").
        let predef_str = strings.intern("*predef*");
        let option_str = strings.intern("option");
        let none_str = strings.intern("None");
        let static_predef_option_lident = longidents.push(Longident::Ldot(
            Box::new(Longident::Lident(predef_str)),
            option_str,
        ));
        let static_predef_none_lid = longidents.push(Longident::Ldot(
            Box::new(Longident::Lident(predef_str)),
            none_str,
        ));
        let some_str = strings.intern("Some");
        let static_predef_some_lid = longidents.push(Longident::Ldot(
            Box::new(Longident::Lident(predef_str)),
            some_str,
        ));
        let static_some_lid = longidents.push(Longident::Lident(some_str));

        // Pre-allocate Ast_literal no-loc core type longidents.
        // OCaml reuses these module-level constants (Ast_literal.No_loc.*), so
        // they must have stable identity distinct from generic parser lidents.
        let ast_literal_type_string_str = strings.intern("string");
        let static_ast_literal_type_string_lident =
            longidents.push(Longident::Lident(ast_literal_type_string_str));
        let ast_literal_type_int_str = strings.intern("int");
        let static_ast_literal_type_int_lident =
            longidents.push(Longident::Lident(ast_literal_type_int_str));
        let ast_literal_type_bool_str = strings.intern("bool");
        let static_ast_literal_type_bool_lident =
            longidents.push(Longident::Lident(ast_literal_type_bool_str));
        let ast_literal_type_float_str = strings.intern("float");
        let static_ast_literal_type_float_lident =
            longidents.push(Longident::Lident(ast_literal_type_float_str));
        // Pre-allocate Ast_literal.No_loc.{type_string,type_int,type_bool,type_float}.
        // These all use Location.none, which is LocIdx(0) once ParseArena::new()
        // inserts the none location.
        let none_loc = LocIdx::none();
        let mk_ast_literal_type = |txt: LidentIdx| CoreType {
            ptyp_desc: Box::new(CoreTypeDesc::Ptyp_constr(Box::new((
                Located { txt, loc: none_loc },
                vec![],
            )))),
            ptyp_loc: none_loc,
            ptyp_attributes: Attributes::new(),
        };
        let static_ast_literal_types = StaticAstLiteralTypes {
            type_string: core_types
                .push(mk_ast_literal_type(static_ast_literal_type_string_lident)),
            type_int: core_types.push(mk_ast_literal_type(static_ast_literal_type_int_lident)),
            type_bool: core_types.push(mk_ast_literal_type(static_ast_literal_type_bool_lident)),
            type_float: core_types.push(mk_ast_literal_type(static_ast_literal_type_float_lident)),
        };

        Self {
            positions: Arena::default(),
            locations: Arena::default(),
            longidents,
            synthetic_longidents: Box::new([]),
            next_synthetic_longident: AtomicUsize::new(0),
            synthetic_longident_base: 0,
            arities,
            expressions: Arena::default(),
            expr_fun_defaults: Vec::new(),
            nary_fun_params_by_first_pattern: HashMap::new(),
            nary_fun_unknown_arity_by_first_pattern: HashMap::new(),
            nary_fun_default_bindings_by_first_pattern: HashMap::new(),
            nary_fun_newtypes_by_first_pattern: HashMap::new(),
            nary_arrow_args_by_first_type: HashMap::new(),
            value_constraints_by_pattern: HashMap::new(),
            expr_case_guards: Vec::new(),
            expr_construct_args: Vec::new(),
            expr_variant_args: Vec::new(),
            expr_record_spreads: Vec::new(),
            pat_record_rests: HashMap::new(),
            expr_if_else_branches: Vec::new(),
            expr_coerce_from_types: Vec::new(),
            patterns: Arena::default(),
            synthetic_patterns: Box::new([]),
            next_synthetic_pattern: AtomicUsize::new(0),
            synthetic_pattern_base: 0,
            synthetic_strings: Box::new([]),
            next_synthetic_string: AtomicUsize::new(0),
            synthetic_string_base: 0,
            core_types,
            mod_exprs: Arena::default(),
            mod_types: Arena::default(),
            static_arities,
            static_list_lidents,
            static_array_lidents,
            static_regexp_t_lident,
            static_predef_option_lident,
            static_ast_literal_types,
            static_ast_literal_type_string_lident,
            static_ast_literal_type_int_lident,
            static_ast_literal_type_bool_lident,
            static_ast_literal_type_float_lident,
            static_placeholder_lid: LidentIdx::default(),
            static_none_lid: LidentIdx::default(),
            static_predef_none_lid,
            static_some_lid,
            static_predef_some_lid,
            static_optional_default_opt_lid,
            static_optional_default_sth_lid,
            static_optional_default_opt_str,
            static_optional_default_sth_str,
            static_default_attr_str,
            static_constructor_from_spread_attr_str,
            static_pat_from_variant_spread_attr_str,
            static_ppx_lidents,
            position_dedup: HashMap::new(),
            lident_dedup,
            longident_shareable_strs: HashSet::new(),
            ldot_prefix_idx_table,
            strings,
            prim_empty_external_ffi,
            prim_empty_js_mapper,
            prim_raw_expr,
            prim_raw_stmt,
            ppx_eq_str,
            ppx_js_str,
            ppx_empty_str,
            ppx_undefined_str,
            template_concat_str,
            local_module_counter: 0,
            rewritten_expr_locs: HashSet::new(),
            dummy_loc: LocIdx::default(),
            spice_cache: SpiceCache::new(),
            shareable_literal_strs: HashSet::new(),
            constant_string_identity_to_idx: HashMap::new(),
            tyvar_source_by_loc: HashMap::new(),
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
        // Pre-allocate placeholder longident (for placeholder AST nodes)
        let placeholder_idx = arena.strings.intern("placeholder");
        arena.static_placeholder_lid = arena.longidents.push(Longident::Lident(placeholder_idx));
        // Pre-allocate "None" longident (for optional field desugaring)
        let none_str = arena.strings.intern("None");
        arena.static_none_lid = arena.longidents.push(Longident::Lident(none_str));
        // Pre-allocate "*predef*" longident
        let predef_str = arena.strings.intern("*predef*");
        arena.longidents.push(Longident::Lident(predef_str));
        arena
    }

    /// Get the placeholder longident index.
    /// This is useful for creating placeholder AST nodes without mutating the arena.
    pub fn placeholder_lid(&self) -> LidentIdx {
        self.static_placeholder_lid
    }

    /// Get the pre-allocated "None" longident index.
    /// Used for optional field desugaring (synthesizing None for missing optional fields).
    pub fn none_lid(&self) -> LidentIdx {
        self.static_none_lid
    }

    /// Get the pre-allocated Ldot(*predef*, "None") longident index.
    /// Used for optional-default rewrites where constructors must resolve to option.
    pub fn predef_none_lid(&self) -> LidentIdx {
        self.static_predef_none_lid
    }

    /// Get the pre-allocated `Ldot(*predef*, "Some")` longident index.
    /// Used for optional label processing in typecore.
    pub fn some_lid(&self) -> LidentIdx {
        self.static_predef_some_lid
    }

    /// Get the pre-allocated `Ldot(*predef*, "Some")` longident index.
    /// Used for optional-default rewrites where constructors must resolve to option.
    pub fn predef_some_lid(&self) -> LidentIdx {
        self.static_predef_some_lid
    }

    /// Get the pre-allocated `Lident "Some"` longident index.
    /// Used for unqualified option wrappers (`option_some` paths).
    pub fn plain_some_lid(&self) -> LidentIdx {
        self.static_some_lid
    }

    /// Get the pre-allocated `Lident "*opt*"` longident index.
    /// Used for optional-default rewrite function parameter binding.
    pub fn optional_default_opt_lid(&self) -> LidentIdx {
        self.static_optional_default_opt_lid
    }

    /// Get the pre-allocated `Lident "*sth*"` longident index.
    /// Used for optional-default rewrite match payload binding.
    pub fn optional_default_sth_lid(&self) -> LidentIdx {
        self.static_optional_default_sth_lid
    }

    /// Get the pre-allocated `"*opt*"` string index.
    pub fn optional_default_opt_str(&self) -> StrIdx {
        self.static_optional_default_opt_str
    }

    /// Get the pre-allocated `"*sth*"` string index.
    pub fn optional_default_sth_str(&self) -> StrIdx {
        self.static_optional_default_sth_str
    }

    /// Get the pre-allocated `"#default"` attribute string index.
    pub fn default_attr_str(&self) -> StrIdx {
        self.static_default_attr_str
    }

    /// Get the pre-allocated `"res.constructor_from_spread"` attribute string index.
    pub fn constructor_from_spread_attr_str(&self) -> StrIdx {
        self.static_constructor_from_spread_attr_str
    }

    /// Get the pre-allocated `"res.patFromVariantSpread"` attribute string index.
    pub fn pat_from_variant_spread_attr_str(&self) -> StrIdx {
        self.static_pat_from_variant_spread_attr_str
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
        if let Some(loc) = self.spice_cache.none_loc {
            return loc;
        }
        let file_idx = self.push_string("_none_".to_string());
        let pos = Position::new(file_idx, 1, 0, -1);
        let pos_idx = self.push_position(pos);
        let loc = self.push_loc(pos_idx, pos_idx, true);
        self.spice_cache.none_loc = Some(loc);
        loc
    }

    fn spice_cached_string(
        &mut self,
        key: SpiceStringKey,
        value: &str,
        longident_shareable: bool,
    ) -> StrIdx {
        if let Some(idx) = self.spice_cache.get_string(key) {
            return idx;
        }
        let idx = self.push_interned_string(value);
        if longident_shareable {
            self.longident_shareable_strs.insert(idx);
        }
        self.spice_cache.set_string(key, idx);
        idx
    }

    /// Shared non-interned "Spice" prefix for the codecs module.
    pub fn spice_codecs_str(&mut self) -> StrIdx {
        self.spice_cached_string(SpiceStringKey::Codecs, "Spice", true)
    }

    /// Shared non-interned "Spice" prefix for the records module.
    pub fn spice_records_str(&mut self) -> StrIdx {
        self.spice_cached_string(SpiceStringKey::Records, "Spice", true)
    }

    /// Shared non-interned "Spice" prefix for the variants module.
    pub fn spice_variants_str(&mut self) -> StrIdx {
        self.spice_cached_string(SpiceStringKey::Variants, "Spice", true)
    }

    /// Shared non-interned "Spice" prefix for the polyvariants module.
    pub fn spice_polyvars_str(&mut self) -> StrIdx {
        self.spice_cached_string(SpiceStringKey::Polyvars, "Spice", true)
    }

    /// Shared non-interned "Spice" prefix for the tuple module.
    pub fn spice_tuple_str(&mut self) -> StrIdx {
        self.spice_cached_string(SpiceStringKey::Tuple, "Spice", true)
    }

    /// Register a literal string to be value-shared during marshalling.
    pub fn register_shareable_literal(&mut self, s: &str) {
        self.shareable_literal_strs.insert(s.to_string());
    }

    /// Check if a literal string should be value-shared during marshalling.
    pub fn is_shareable_literal(&self, s: &str) -> bool {
        self.shareable_literal_strs.contains(s)
    }

    /// Register a `Constant::String` identity to marshal via `StrIdx`.
    pub fn register_constant_string_identity(&mut self, s: &str, idx: StrIdx) {
        self.constant_string_identity_to_idx
            .insert((s.as_ptr() as usize, s.len()), idx);
    }

    /// Look up a registered `Constant::String` identity.
    pub fn constant_string_str_idx_by_identity(&self, s: &str) -> Option<StrIdx> {
        self.constant_string_identity_to_idx
            .get(&(s.as_ptr() as usize, s.len()))
            .copied()
    }

    /// Shared non-interned "JSON" prefix for spice PPX.
    pub fn spice_json_str(&mut self) -> StrIdx {
        self.spice_cached_string(SpiceStringKey::Json, "JSON", true)
    }

    /// Shared non-interned "t" suffix for metaquoted JSON.t.
    pub fn spice_json_t_str(&mut self) -> StrIdx {
        self.spice_cached_string(SpiceStringKey::JsonT, "t", false)
    }

    /// Shared Lident for Utils.ctyp_json_t (uses a distinct non-interned "JSON").
    pub fn spice_json_ctyp_lident(&mut self) -> LidentIdx {
        if let Some(idx) = self.spice_cache.json_ctyp_lident {
            return idx;
        }
        let json_idx = self.push_string("JSON".to_string());
        let t_idx = self.strings.intern("t");
        let lid = Longident::Ldot(Box::new(Longident::Lident(json_idx)), t_idx);
        let lid_idx = self.longidents.push(lid);
        self.spice_cache.json_ctyp_lident = Some(lid_idx);
        lid_idx
    }

    /// Shared non-interned "Option" prefix for spice PPX.
    pub fn spice_option_str(&mut self) -> StrIdx {
        self.spice_cached_string(SpiceStringKey::Option, "Option", true)
    }

    /// Shared non-interned "Dict" prefix for spice PPX.
    pub fn spice_dict_str(&mut self) -> StrIdx {
        self.spice_cached_string(SpiceStringKey::Dict, "Dict", true)
    }

    /// Shared non-interned "Result" prefix for spice PPX.
    pub fn spice_result_str(&mut self) -> StrIdx {
        self.spice_cached_string(SpiceStringKey::Result, "Result", true)
    }

    /// Shared non-interned "Array" prefix for spice PPX.
    pub fn spice_array_str(&mut self) -> StrIdx {
        self.spice_cached_string(SpiceStringKey::Array, "Array", true)
    }

    /// Shared non-interned "v" identifier for dynamic PPX-generated functions.
    pub fn spice_runtime_v(&mut self) -> StrIdx {
        self.spice_cached_string(SpiceStringKey::RuntimeV, "v", true)
    }

    /// Shared non-interned "v" identifier for pattern variables.
    pub fn spice_pat_v(&mut self) -> StrIdx {
        self.spice_cached_string(SpiceStringKey::PatV, "v", false)
    }

    /// Shared non-interned "v" identifier for record field access expressions.
    pub fn spice_field_v(&mut self) -> StrIdx {
        self.spice_cached_string(SpiceStringKey::FieldV, "v", false)
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
    /// Each call creates a new StrIdx (for marshal identity).
    /// Use for user identifiers parsed from source (variable names, etc.).
    pub fn push_lident(&mut self, name: &str) -> LidentIdx {
        let str_idx = self.strings.push_interned(name);
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
    pub fn push_ldot(&mut self, prefix: LidentIdx, name: &str) -> LidentIdx {
        let str_idx = self.strings.push_interned(name);
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

    /// Push a dotted identifier (Ldot) and remember the parent index for marshal sharing.
    ///
    /// Use this only when OCaml reuses the same prefix pointer and Rust must preserve
    /// that identity across generated nodes (e.g. `Js_OO.Callback.arityN` in `@this` rewrites).
    pub fn push_ldot_tracked(&mut self, prefix: LidentIdx, name: &str) -> LidentIdx {
        let str_idx = self.strings.push_interned(name);
        let prefix_lid = self.get_longident(prefix).clone();
        let idx = self
            .longidents
            .push(Longident::Ldot(Box::new(prefix_lid), str_idx));
        self.ldot_prefix_idx_table.insert(idx, prefix);
        idx
    }

    /// Push a dotted identifier (Ldot) with a static string and remember the parent index.
    ///
    /// This mirrors OCaml static string literal sharing for PPX-generated longidents
    /// (e.g. `Js_OO.unsafe_to_method`) while preserving tracked prefix identity.
    pub fn push_ldot_tracked_static(&mut self, prefix: LidentIdx, name: &'static str) -> LidentIdx {
        let str_idx = self.strings.intern(name);
        let prefix_lid = self.get_longident(prefix).clone();
        let idx = self
            .longidents
            .push(Longident::Ldot(Box::new(prefix_lid), str_idx));
        self.ldot_prefix_idx_table.insert(idx, prefix);
        idx
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
        let raw = idx.to_u32();
        if raw < self.synthetic_longident_base || self.synthetic_longidents.is_empty() {
            self.longidents.get(idx)
        } else {
            self.synthetic_longidents[(raw - self.synthetic_longident_base) as usize]
                .get()
                .expect("typechecker synthetic longident read before initialization")
        }
    }

    /// Get the parent prefix index for an `Ldot` created via `push_ldot*`.
    pub fn ldot_prefix_idx(&self, idx: LidentIdx) -> Option<LidentIdx> {
        self.ldot_prefix_idx_table.get(&idx).copied()
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

    /// Get the static PPX/frontend arity index for `Some(1)`.
    ///
    /// OCaml parser (`res_core.ml`) and frontend PPX helpers
    /// (`ast_compatible.ml` / derive mappers) come from different compilation
    /// units, so their literal `Some 1` values are not globally shared.
    pub fn static_ppx_arity_1(&self) -> ArityIdx {
        self.static_arities.arity_ppx_1
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

    /// Get the pre-allocated `Lident "Primitive_array"` prefix.
    pub fn belt_lident(&self) -> LidentIdx {
        self.static_array_lidents.belt_lident
    }

    /// Get the pre-allocated `Lident "Primitive_array"` prefix.
    pub fn belt_array_lident(&self) -> LidentIdx {
        self.static_array_lidents.belt_array
    }

    /// Get the pre-allocated `Lident "Primitive_list"` prefix.
    pub fn belt_list_lident(&self) -> LidentIdx {
        self.static_array_lidents.belt_list
    }

    /// Get the pre-allocated `Ldot(Lident "Primitive_array", "spread")`.
    /// Use in spread array desugaring: `[...a, ...b]` → `Primitive_array.spread(...)`.
    pub fn belt_array_concat_many_lid(&self) -> LidentIdx {
        self.static_array_lidents.belt_array_concat_many
    }

    /// Get the pre-allocated `Ldot(Lident "Primitive_list", "spread")`.
    /// Use in spread list desugaring: `list{...a, ...b}` → `Primitive_list.spread(...)`.
    pub fn belt_list_concat_many_lid(&self) -> LidentIdx {
        self.static_array_lidents.belt_list_concat_many
    }

    /// Fresh `Ldot(Lident "Primitive_array", "spread")` for one desugared occurrence.
    /// OCaml builds this longident inline at each spread site
    /// (compiler/syntax/src/res_core.ml:4528), so every occurrence allocates a
    /// new Longident block; only the name strings are static.
    pub fn fresh_belt_array_spread_lid(&mut self) -> LidentIdx {
        let module_str = self.strings.intern("Primitive_array");
        let spread_str = self.strings.intern("spread");
        self.longidents.push(Longident::Ldot(
            Box::new(Longident::Lident(module_str)),
            spread_str,
        ))
    }

    /// Fresh `Ldot(Lident "Primitive_list", "spread")` for one desugared occurrence.
    /// See `fresh_belt_array_spread_lid`; OCaml site is res_core.ml:4386.
    pub fn fresh_belt_list_spread_lid(&mut self) -> LidentIdx {
        let module_str = self.strings.intern("Primitive_list");
        let spread_str = self.strings.intern("spread");
        self.longidents.push(Longident::Ldot(
            Box::new(Longident::Lident(module_str)),
            spread_str,
        ))
    }

    /// Get the static `Stdlib_RegExp.t` longident index used for `%re`.
    pub fn regexp_t_lident(&self) -> LidentIdx {
        self.static_regexp_t_lident
    }

    /// Get the static `*predef*.option` longident index.
    pub fn predef_option_lident(&self) -> LidentIdx {
        self.static_predef_option_lident
    }

    /// Get `Ast_literal.No_loc.type_string`.
    pub fn ast_literal_type_string(&self) -> CoreTypeIdx {
        self.static_ast_literal_types.type_string
    }

    /// Get `Ast_literal.No_loc.type_int`.
    pub fn ast_literal_type_int(&self) -> CoreTypeIdx {
        self.static_ast_literal_types.type_int
    }

    /// Get `Ast_literal.No_loc.type_bool`.
    pub fn ast_literal_type_bool(&self) -> CoreTypeIdx {
        self.static_ast_literal_types.type_bool
    }

    /// Get `Ast_literal.type_float`.
    pub fn ast_literal_type_float(&self) -> CoreTypeIdx {
        self.static_ast_literal_types.type_float
    }

    /// Get the pre-allocated `Ast_literal.No_loc.type_string` longident.
    pub fn ast_literal_type_string_lident(&self) -> LidentIdx {
        self.static_ast_literal_type_string_lident
    }

    /// Get the pre-allocated `Ast_literal.No_loc.type_int` longident.
    pub fn ast_literal_type_int_lident(&self) -> LidentIdx {
        self.static_ast_literal_type_int_lident
    }

    /// Get the pre-allocated `Ast_literal.No_loc.type_bool` longident.
    pub fn ast_literal_type_bool_lident(&self) -> LidentIdx {
        self.static_ast_literal_type_bool_lident
    }

    /// Get the pre-allocated `Ast_literal.type_float` longident.
    pub fn ast_literal_type_float_lident(&self) -> LidentIdx {
        self.static_ast_literal_type_float_lident
    }

    /// Check whether a longident index is one of Ast_literal's shared simple types.
    pub fn is_ast_literal_simple_type_lident(&self, idx: LidentIdx) -> bool {
        idx == self.static_ast_literal_type_string_lident
            || idx == self.static_ast_literal_type_int_lident
            || idx == self.static_ast_literal_type_bool_lident
            || idx == self.static_ast_literal_type_float_lident
    }

    pub fn ppx_js_lident(&self) -> LidentIdx {
        self.static_ppx_lidents.js_lident
    }

    pub fn ppx_js_typeof_lid(&self) -> LidentIdx {
        self.static_ppx_lidents.js_typeof
    }

    pub fn ppx_js_undefined_to_option_lid(&self) -> LidentIdx {
        self.static_ppx_lidents.js_undefined_to_option
    }

    pub fn ppx_js_undefined_lid(&self) -> LidentIdx {
        self.static_ppx_lidents.js_undefined
    }

    pub fn ppx_js_undefined_empty_lid(&self) -> LidentIdx {
        self.static_ppx_lidents.js_undefined_empty
    }

    pub fn ppx_js_oo_lident(&self) -> LidentIdx {
        self.static_ppx_lidents.js_oo_lident
    }

    pub fn ppx_js_oo_callback_lid(&self) -> LidentIdx {
        self.static_ppx_lidents.js_oo_callback
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

    pub fn ppx_empty_str(&self) -> StrIdx {
        self.ppx_empty_str
    }

    pub fn ppx_undefined_str(&self) -> StrIdx {
        self.ppx_undefined_str
    }

    pub fn template_concat_str(&self) -> StrIdx {
        self.template_concat_str
    }

    /// Get the string content for a StrIdx.
    pub fn get_string(&self, idx: StrIdx) -> &str {
        let raw = idx.raw();
        if raw < self.synthetic_string_base || self.synthetic_strings.is_empty() {
            self.strings.get(idx)
        } else {
            self.synthetic_strings[(raw - self.synthetic_string_base) as usize]
                .get()
                .expect("typechecker synthetic string read before initialization")
        }
    }

    /// Number of strings currently stored in the arena string table.
    pub fn string_count(&self) -> usize {
        self.strings.len()
    }

    /// Reserve append-only AST space used by typecore synthetic rewrites.
    ///
    /// Typechecking creates a few parsed AST fragments to mirror OCaml rewrites
    /// such as optional-default lowering and variant-spread expansion. This must
    /// happen before the arena is handed to `TypeCheckContext` for the primary
    /// AST and identifier arenas: reserving at an append site can reallocate
    /// backing storage while existing parser refs are still live. Sparse side
    /// tables are keyed by `ExprIdx` and are only appended alongside synthetic
    /// expressions, so they do not need an unconditional per-file reserve.
    pub fn reserve_typecheck_synthetic_capacity(&mut self) {
        self.expressions.reserve(64);
        self.patterns.reserve(64);
        self.longidents.reserve(128);
        self.strings.reserve(128);

        self.synthetic_pattern_base = self.patterns.len() as u32;
        let synthetic_pattern_capacity = self.longidents.len().saturating_mul(2).max(64);
        self.synthetic_patterns = (0..synthetic_pattern_capacity)
            .map(|_| OnceLock::new())
            .collect();
        self.next_synthetic_pattern.store(0, Ordering::Relaxed);

        // A single sparse JSX record can synthesize hundreds of omitted
        // optional labels despite containing few source longidents. Keep a
        // practical floor while scaling with source complexity.
        let synthetic_longident_capacity = self.longidents.len().saturating_mul(2).max(1024);
        self.synthetic_longident_base = self.longidents.len() as u32;
        self.synthetic_longidents = (0..synthetic_longident_capacity)
            .map(|_| OnceLock::new())
            .collect();
        self.next_synthetic_longident.store(0, Ordering::Relaxed);

        let synthetic_string_capacity = synthetic_longident_capacity.max(self.strings.len());
        self.synthetic_string_base = self.strings.len() as u32;
        self.synthetic_strings = (0..synthetic_string_capacity)
            .map(|_| OnceLock::new())
            .collect();
        self.next_synthetic_string.store(0, Ordering::Relaxed);
    }

    /// Append a typechecker-generated longident to storage reserved before the
    /// arena became shared.
    pub fn push_typecheck_longident(&self, longident: Longident) -> LidentIdx {
        let slot = self
            .next_synthetic_longident
            .fetch_add(1, Ordering::Relaxed);
        let storage = self
            .synthetic_longidents
            .get(slot)
            .expect("typechecker synthetic longident capacity exhausted");
        storage
            .set(longident)
            .unwrap_or_else(|_| panic!("typechecker synthetic longident slot initialized twice"));
        LidentIdx::from_u32(self.synthetic_longident_base + slot as u32)
    }

    /// Append a typechecker-generated string to storage reserved before the
    /// arena became shared.
    pub fn push_typecheck_string(&self, string: String) -> StrIdx {
        let slot = self.next_synthetic_string.fetch_add(1, Ordering::Relaxed);
        let storage = self
            .synthetic_strings
            .get(slot)
            .expect("typechecker synthetic string capacity exhausted");
        storage
            .set(string)
            .unwrap_or_else(|_| panic!("typechecker synthetic string slot initialized twice"));
        StrIdx::from_raw(self.synthetic_string_base + slot as u32)
    }

    /// Append a typechecker-generated simple identifier, allocating its string
    /// in the matching reserved storage.
    pub fn push_typecheck_lident(&self, name: &str) -> LidentIdx {
        let name = self.push_typecheck_string(name.to_owned());
        self.push_typecheck_longident(Longident::Lident(name))
    }

    /// Append a typechecker-generated pattern to storage reserved before the
    /// arena became shared. This is a safe, append-only equivalent of OCaml's
    /// allocation during pattern rewrites.
    pub fn push_typecheck_pattern(&self, pattern: Pattern) -> PatIdx {
        let slot = self.next_synthetic_pattern.fetch_add(1, Ordering::Relaxed);
        let storage = self
            .synthetic_patterns
            .get(slot)
            .expect("typechecker synthetic pattern capacity exhausted");
        storage
            .set(pattern)
            .unwrap_or_else(|_| panic!("typechecker synthetic pattern slot initialized twice"));
        PatIdx::from_u32(self.synthetic_pattern_base + slot as u32)
    }

    /// Find the most recently inserted string index for the given content.
    ///
    /// This scans from the end to prefer the latest identity when the same string
    /// was pushed multiple times without interning.
    pub fn find_string_idx(&self, s: &str) -> Option<StrIdx> {
        for i in (0..self.strings.len()).rev() {
            let idx = StrIdx(i as u32);
            if self.strings.get(idx) == s {
                return Some(idx);
            }
        }
        None
    }

    /// Intern a string (returns existing idx if already interned).
    pub fn intern_string(&mut self, s: &str) -> StrIdx {
        self.strings.intern(s)
    }

    /// Push a string without deduplication (for dynamic user-input strings).
    pub fn push_string(&mut self, s: impl Into<String>) -> StrIdx {
        self.strings.push(s.into())
    }

    /// Push a string with a unique StrIdx.
    ///
    /// Returns a fresh StrIdx each time (preserving marshal identity semantics).
    /// Use for parsed identifiers from tokens where each occurrence needs its
    /// own StrIdx (for marshal parity).
    #[inline]
    pub fn push_interned_string(&mut self, s: &str) -> StrIdx {
        self.strings.push_interned(s)
    }

    /// Generate the next local module name for %%private expansion.
    /// Returns "local_1", "local_2", etc. matching OCaml's behavior.
    pub fn next_local_module_name(&mut self) -> StrIdx {
        self.local_module_counter += 1;
        self.push_string(format!("local_{}", self.local_module_counter))
    }

    /// Reset the local module counter to 0.
    /// Called before typecheck PPX passes when the arena was already used during
    /// binary AST writing (which also expands %%private and increments the counter).
    /// OCaml starts fresh for each bsc invocation, so we must reset to match.
    pub fn reset_local_module_counter(&mut self) {
        self.local_module_counter = 0;
    }

    /// Mark an expression location as rewritten by the generic PPX mapper path.
    pub fn mark_rewritten_expr_loc(&mut self, loc: LocIdx) {
        self.rewritten_expr_locs.insert(loc);
    }

    /// Returns true when this expression location was rewritten generically.
    pub fn is_rewritten_expr_loc(&self, loc: LocIdx) -> bool {
        self.rewritten_expr_locs.contains(&loc)
    }

    /// Record the source constructor string identity for a varified type var.
    pub fn record_tyvar_source(&mut self, loc: LocIdx, str_idx: StrIdx) {
        self.tyvar_source_by_loc.entry(loc).or_insert(str_idx);
    }

    /// Retrieve the source constructor string identity for a varified type var.
    pub fn tyvar_source_str(&self, loc: LocIdx) -> Option<StrIdx> {
        self.tyvar_source_by_loc.get(&loc).copied()
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

    // ========================================================================
    // AST node arenas
    // ========================================================================

    fn placeholder_lident_loc() -> Located<LidentIdx> {
        Located {
            txt: LidentIdx::default(),
            loc: LocIdx::default(),
        }
    }

    fn placeholder_expr() -> Expression {
        Expression {
            pexp_desc: Box::new(ExpressionDesc::Pexp_ident(Self::placeholder_lident_loc())),
            pexp_loc: LocIdx::default(),
            pexp_attributes: Attributes::new(),
        }
    }

    fn placeholder_pat() -> Pattern {
        Pattern {
            ppat_desc: Box::new(PatternDesc::Ppat_any),
            ppat_loc: LocIdx::default(),
            ppat_attributes: Attributes::new(),
        }
    }

    fn placeholder_core_type() -> CoreType {
        CoreType {
            ptyp_desc: Box::new(CoreTypeDesc::Ptyp_any),
            ptyp_loc: LocIdx::default(),
            ptyp_attributes: Attributes::new(),
        }
    }

    fn placeholder_mod_expr() -> ModuleExpr {
        ModuleExpr {
            pmod_desc: Box::new(ModuleExprDesc::Pmod_ident(Self::placeholder_lident_loc())),
            pmod_loc: LocIdx::default(),
            pmod_attributes: Attributes::new(),
        }
    }

    fn placeholder_mod_type() -> ModuleType {
        ModuleType {
            pmty_desc: Box::new(ModuleTypeDesc::Pmty_ident(Self::placeholder_lident_loc())),
            pmty_loc: LocIdx::default(),
            pmty_attributes: Attributes::new(),
        }
    }

    fn extract_fun_default(expr: &Expression) -> Option<ExprIdx> {
        match &*expr.pexp_desc {
            ExpressionDesc::Pexp_fun(inner) => inner.default,
            _ => None,
        }
    }

    fn extract_case_guards(expr: &Expression) -> Option<Box<[Option<ExprIdx>]>> {
        match &*expr.pexp_desc {
            ExpressionDesc::Pexp_match(inner) | ExpressionDesc::Pexp_try(inner) => {
                let (_, cases) = &**inner;
                if cases.iter().all(|case| case.pc_guard.is_none()) {
                    None
                } else {
                    Some(
                        cases
                            .iter()
                            .map(|case| case.pc_guard)
                            .collect::<Vec<_>>()
                            .into_boxed_slice(),
                    )
                }
            }
            _ => None,
        }
    }

    fn extract_construct_arg(expr: &Expression) -> Option<ExprIdx> {
        match &*expr.pexp_desc {
            ExpressionDesc::Pexp_construct(_, arg) => *arg,
            _ => None,
        }
    }

    fn extract_variant_arg(expr: &Expression) -> Option<ExprIdx> {
        match &*expr.pexp_desc {
            ExpressionDesc::Pexp_variant(inner) => {
                let (_, arg) = &**inner;
                *arg
            }
            _ => None,
        }
    }

    fn extract_record_spread(expr: &Expression) -> Option<ExprIdx> {
        match &*expr.pexp_desc {
            ExpressionDesc::Pexp_record(inner) => {
                let (_, spread) = &**inner;
                *spread
            }
            _ => None,
        }
    }

    fn extract_if_else_branch(expr: &Expression) -> Option<ExprIdx> {
        match &*expr.pexp_desc {
            ExpressionDesc::Pexp_ifthenelse(inner) => {
                let (_, _, else_branch) = &**inner;
                *else_branch
            }
            _ => None,
        }
    }

    fn extract_coerce_from_type(expr: &Expression) -> Option<CoreTypeIdx> {
        match &*expr.pexp_desc {
            ExpressionDesc::Pexp_coerce(inner) => {
                let (_, from_type, _) = &**inner;
                *from_type
            }
            _ => None,
        }
    }

    /// Push an expression into the arena and return its index.
    /// Use this instead of `Box::new(expr)` for recursive AST references.
    #[inline]
    pub fn push_expr(&mut self, expr: Expression) -> ExprIdx {
        let default = Self::extract_fun_default(&expr);
        let case_guards = Self::extract_case_guards(&expr);
        let construct_arg = Self::extract_construct_arg(&expr);
        let variant_arg = Self::extract_variant_arg(&expr);
        let record_spread = Self::extract_record_spread(&expr);
        let if_else = Self::extract_if_else_branch(&expr);
        let coerce_from = Self::extract_coerce_from_type(&expr);
        let idx = self.expressions.push(expr);
        self.expr_fun_defaults.push(default);
        self.expr_case_guards.push(case_guards);
        self.expr_construct_args.push(construct_arg);
        self.expr_variant_args.push(variant_arg);
        self.expr_record_spreads.push(record_spread);
        self.expr_if_else_branches.push(if_else);
        self.expr_coerce_from_types.push(coerce_from);
        idx
    }

    /// Reserve an expression index using a placeholder node.
    ///
    /// This is the first step of two-phase construction (`reserve -> initialize`),
    /// used when sparse side data must be keyed by stable `ExprIdx`.
    #[inline]
    pub fn reserve_expr(&mut self) -> ExprIdx {
        let idx = self.expressions.reserve_with(Self::placeholder_expr());
        self.expr_fun_defaults.push(None);
        self.expr_case_guards.push(None);
        self.expr_construct_args.push(None);
        self.expr_variant_args.push(None);
        self.expr_record_spreads.push(None);
        self.expr_if_else_branches.push(None);
        self.expr_coerce_from_types.push(None);
        idx
    }

    /// Initialize a previously reserved expression slot.
    #[inline]
    pub fn initialize_expr(&mut self, idx: ExprIdx, expr: Expression) {
        let slot = idx.0 as usize;
        debug_assert!(slot < self.expr_fun_defaults.len());
        debug_assert!(slot < self.expr_case_guards.len());
        debug_assert!(slot < self.expr_construct_args.len());
        debug_assert!(slot < self.expr_variant_args.len());
        debug_assert!(slot < self.expr_record_spreads.len());
        debug_assert!(slot < self.expr_if_else_branches.len());
        debug_assert!(slot < self.expr_coerce_from_types.len());
        let default = Self::extract_fun_default(&expr);
        let case_guards = Self::extract_case_guards(&expr);
        let construct_arg = Self::extract_construct_arg(&expr);
        let variant_arg = Self::extract_variant_arg(&expr);
        let record_spread = Self::extract_record_spread(&expr);
        let if_else = Self::extract_if_else_branch(&expr);
        let coerce_from = Self::extract_coerce_from_type(&expr);
        self.expressions.initialize(idx, expr);
        self.expr_fun_defaults[slot] = default;
        self.expr_case_guards[slot] = case_guards;
        self.expr_construct_args[slot] = construct_arg;
        self.expr_variant_args[slot] = variant_arg;
        self.expr_record_spreads[slot] = record_spread;
        self.expr_if_else_branches[slot] = if_else;
        self.expr_coerce_from_types[slot] = coerce_from;
    }

    /// Get an expression by index.
    #[inline]
    pub fn get_expr(&self, idx: ExprIdx) -> &Expression {
        self.expressions.get(idx)
    }

    /// Get a mutable expression by index.
    #[inline]
    pub fn get_expr_mut(&mut self, idx: ExprIdx) -> &mut Expression {
        let slot = idx.0 as usize;
        if slot < self.expr_fun_defaults.len() {
            self.expr_fun_defaults[slot] = None;
        }
        if slot < self.expr_case_guards.len() {
            self.expr_case_guards[slot] = None;
        }
        if slot < self.expr_construct_args.len() {
            self.expr_construct_args[slot] = None;
        }
        if slot < self.expr_variant_args.len() {
            self.expr_variant_args[slot] = None;
        }
        if slot < self.expr_record_spreads.len() {
            self.expr_record_spreads[slot] = None;
        }
        if slot < self.expr_if_else_branches.len() {
            self.expr_if_else_branches[slot] = None;
        }
        if slot < self.expr_coerce_from_types.len() {
            self.expr_coerce_from_types[slot] = None;
        }
        self.expressions.get_mut(idx)
    }

    /// Get the number of expressions in the arena.
    pub fn expr_count(&self) -> usize {
        self.expressions.len()
    }

    /// Store the authoritative n-ary argument list for a parser-created arrow.
    pub fn set_nary_arrow_args(
        &mut self,
        _arity: ArityIdx,
        args: Vec<crate::parser::ast::TypeArg>,
    ) {
        let first_type = args.first().expect("Ptyp_arrow has arguments").typ;
        self.nary_arrow_args_by_first_type
            .insert(first_type, args.into_boxed_slice());
    }

    pub fn nary_arrow_args<'a>(
        &'a self,
        arg: &'a crate::parser::ast::TypeArg,
        arity: ArityIdx,
    ) -> std::borrow::Cow<'a, [crate::parser::ast::TypeArg]> {
        let _ = arity;
        if let Some(args) = self.nary_arrow_args_by_first_type.get(&arg.typ) {
            std::borrow::Cow::Borrowed(&args[..])
        } else {
            std::borrow::Cow::Owned(vec![arg.clone()])
        }
    }

    /// Return snapshots of function nodes and their locations so typecore can
    /// prepare synthetic optional-default AST under an exclusive arena borrow.
    pub fn nary_functions(&self) -> Vec<(crate::parser::ast::PexpFun, LocIdx)> {
        self.expressions
            .as_slice()
            .iter()
            .filter_map(|expr| match &*expr.pexp_desc {
                ExpressionDesc::Pexp_fun(fun) => Some(((**fun).clone(), expr.pexp_loc)),
                _ => None,
            })
            .collect()
    }

    /// Store the optional-default lowering associated with a function's first pattern.
    pub fn set_nary_fun_default_bindings(
        &mut self,
        first_pattern: PatIdx,
        bindings: Vec<(FunParam, Option<crate::parser::ast::ValueBinding>)>,
    ) {
        self.nary_fun_default_bindings_by_first_pattern
            .insert(first_pattern, bindings.into_boxed_slice());
    }

    /// Return optional-default lowering prepared before type checking.
    pub fn nary_fun_default_bindings(
        &self,
        fun: &crate::parser::ast::PexpFun,
    ) -> Option<&[(FunParam, Option<crate::parser::ast::ValueBinding>)]> {
        self.nary_fun_default_bindings_by_first_pattern
            .get(&fun.lhs)
            .map(|bindings| &bindings[..])
    }

    /// Store the authoritative n-ary parameter list for a parser-created function.
    pub fn set_nary_fun_params(
        &mut self,
        arity: ArityIdx,
        params: Vec<FunParam>,
        unknown_arity: ArityIdx,
    ) {
        debug_assert!(!params.is_empty());
        let first_pattern = params[0].p_pat;
        self.nary_fun_params_by_first_pattern
            .insert(first_pattern, params.into_boxed_slice());
        self.nary_fun_unknown_arity_by_first_pattern
            .insert(first_pattern, unknown_arity);
        let _ = arity;
    }

    pub fn nary_fun_unknown_arity(&self, fun: &crate::parser::ast::PexpFun) -> ArityIdx {
        if self.get_arity(fun.arity).is_some() {
            self.nary_fun_unknown_arity_by_first_pattern
                .get(&fun.lhs)
                .copied()
                .or_else(|| match &*self.get_expr(fun.rhs).pexp_desc {
                    ExpressionDesc::Pexp_fun(next) => Some(next.arity),
                    _ => None,
                })
                .unwrap_or(fun.arity)
        } else {
            fun.arity
        }
    }

    /// Attach a current-Parsetree locally abstract constraint to a value binding.
    /// Also cache the polymorphic pattern that OCaml typecore synthesizes before
    /// typing let patterns (`typecore.ml:4503-4514`).
    pub fn set_value_constraint(
        &mut self,
        pattern: PatIdx,
        mut constraint: ValueConstraint,
        expression: ExprIdx,
        loc: LocIdx,
    ) -> Result<(), LocIdx> {
        let names = constraint
            .pvc_newtypes
            .iter()
            .map(|name| self.get_string(name.txt).to_string())
            .collect::<std::collections::HashSet<_>>();
        let source = self.get_core_type(constraint.pvc_type).clone();
        let body = crate::parser::typ::substitute_type_vars(self, source, &names)?;
        let body = self.push_core_type(body);
        let poly = self.push_core_type(CoreType {
            ptyp_desc: Box::new(CoreTypeDesc::Ptyp_poly(Box::new((
                constraint.pvc_newtypes.clone(),
                body,
            )))),
            ptyp_loc: loc,
            ptyp_attributes: Attributes::new(),
        });
        constraint.pvc_pattern = Some(self.push_pat(Pattern {
            ppat_desc: Box::new(PatternDesc::Ppat_constraint(Box::new((pattern, poly)))),
            ppat_loc: loc,
            ppat_attributes: Attributes::new(),
        }));
        let mut wrapped = self.push_expr(Expression {
            pexp_desc: Box::new(ExpressionDesc::Pexp_constraint(Box::new((
                expression,
                constraint.pvc_type,
            )))),
            pexp_loc: loc,
            pexp_attributes: Attributes::new(),
        });
        for name in constraint.pvc_newtypes.iter().rev() {
            wrapped = self.push_expr(Expression {
                pexp_desc: Box::new(ExpressionDesc::Pexp_newtype(Box::new((
                    name.clone(),
                    wrapped,
                )))),
                pexp_loc: loc,
                pexp_attributes: Attributes::new(),
            });
        }
        constraint.pvc_expression = Some(wrapped);
        self.value_constraints_by_pattern
            .insert(pattern, constraint);
        Ok(())
    }

    /// Return a value binding's locally abstract constraint, when present.
    pub fn value_constraint(&self, pattern: PatIdx) -> Option<&ValueConstraint> {
        self.value_constraints_by_pattern.get(&pattern)
    }

    /// Return the authoritative n-ary parameters, or the compact fallback.
    pub fn stored_nary_fun_params(&self, fun: &crate::parser::ast::PexpFun) -> Option<&[FunParam]> {
        self.nary_fun_params_by_first_pattern
            .get(&fun.lhs)
            .map(|params| &params[..])
    }

    /// Store the authoritative `Pexp_fun.newtypes` list for a parser-created function.
    pub fn set_nary_fun_newtypes(
        &mut self,
        first_pattern: PatIdx,
        newtypes: Vec<(StringLoc, Attributes)>,
    ) {
        self.nary_fun_newtypes_by_first_pattern
            .insert(first_pattern, newtypes.into_boxed_slice());
    }

    /// Return the authoritative n-ary newtypes list, or an empty slice.
    pub fn nary_fun_newtypes(
        &self,
        fun: &crate::parser::ast::PexpFun,
    ) -> &[(StringLoc, Attributes)] {
        self.nary_fun_newtypes_by_first_pattern
            .get(&fun.lhs)
            .map(|v| &v[..])
            .unwrap_or(&[])
    }

    pub fn nary_fun_params<'a>(
        &'a self,
        fun: &'a crate::parser::ast::PexpFun,
    ) -> std::borrow::Cow<'a, [FunParam]> {
        if self.get_arity(fun.arity).is_some()
            && let Some(params) = self.nary_fun_params_by_first_pattern.get(&fun.lhs)
        {
            std::borrow::Cow::Borrowed(params)
        } else {
            let mut params = vec![FunParam {
                p_attrs: self.get_pat(fun.lhs).ppat_attributes.clone(),
                p_lbl: fun.arg_label.clone(),
                p_default: fun.default,
                p_pat: fun.lhs,
            }];
            if let Some(arity) = self.get_arity(fun.arity) {
                let mut body = fun.rhs;
                while params.len() < arity.max(1) as usize {
                    let ExpressionDesc::Pexp_fun(next) = &*self.get_expr(body).pexp_desc else {
                        break;
                    };
                    params.push(FunParam {
                        p_attrs: self.get_pat(next.lhs).ppat_attributes.clone(),
                        p_lbl: next.arg_label.clone(),
                        p_default: next.default,
                        p_pat: next.lhs,
                    });
                    body = next.rhs;
                }
            }
            std::borrow::Cow::Owned(params)
        }
    }

    /// Return the body belonging to the n-ary parameter list.
    pub fn nary_fun_body(&self, fun: &crate::parser::ast::PexpFun) -> ExprIdx {
        if self.nary_fun_params_by_first_pattern.contains_key(&fun.lhs) {
            return fun.rhs;
        }
        let Some(arity) = self.get_arity(fun.arity) else {
            return fun.rhs;
        };
        let mut consumed = 1;
        let mut body = fun.rhs;
        while consumed < arity.max(1) as usize {
            let ExpressionDesc::Pexp_fun(next) = &*self.get_expr(body).pexp_desc else {
                break;
            };
            consumed += 1;
            body = next.rhs;
        }
        body
    }

    /// Attach sparse function default data to an expression node.
    ///
    /// The key must be the `ExprIdx` of the owning `Pexp_fun` expression.
    pub fn set_fun_default(&mut self, owner: ExprIdx, default: Option<ExprIdx>) {
        let slot = owner.0 as usize;
        if slot >= self.expr_fun_defaults.len() {
            self.expr_fun_defaults.resize(slot + 1, None);
        }
        self.expr_fun_defaults[slot] = default;
    }

    /// Get sparse function default data for a `Pexp_fun` expression node.
    pub fn fun_default(&self, owner: ExprIdx) -> Option<ExprIdx> {
        let slot = owner.0 as usize;
        self.expr_fun_defaults
            .get(slot)
            .copied()
            .flatten()
            .or_else(|| match &*self.get_expr(owner).pexp_desc {
                ExpressionDesc::Pexp_fun(inner) => inner.default,
                _ => None,
            })
    }

    /// Attach sparse case guard data to a `Pexp_match`/`Pexp_try` expression node.
    ///
    /// Guards are indexed by case position within the node's `Vec<Case>`.
    pub fn set_case_guards(&mut self, owner: ExprIdx, guards: Vec<Option<ExprIdx>>) {
        let slot = owner.0 as usize;
        if slot >= self.expr_case_guards.len() {
            self.expr_case_guards.resize(slot + 1, None);
        }
        self.expr_case_guards[slot] = if guards.is_empty() || guards.iter().all(|g| g.is_none()) {
            None
        } else {
            Some(guards.into_boxed_slice())
        };
    }

    /// Get the sparse case guard list for a match/try expression.
    pub fn case_guards(&self, owner: ExprIdx) -> Option<&[Option<ExprIdx>]> {
        self.expr_case_guards
            .get(owner.0 as usize)
            .and_then(|v| v.as_deref())
    }

    /// Get a sparse case guard by owner expression and case position.
    pub fn case_guard(&self, owner: ExprIdx, case_index: usize) -> Option<ExprIdx> {
        self.case_guards(owner)
            .and_then(|guards| guards.get(case_index))
            .copied()
            .flatten()
            .or_else(|| match &*self.get_expr(owner).pexp_desc {
                ExpressionDesc::Pexp_match(inner) | ExpressionDesc::Pexp_try(inner) => {
                    let (_, cases) = &**inner;
                    cases.get(case_index).and_then(|case| case.pc_guard)
                }
                _ => None,
            })
    }

    /// Attach sparse constructor payload argument data to a construct expression node.
    pub fn set_construct_arg(&mut self, owner: ExprIdx, arg: Option<ExprIdx>) {
        let slot = owner.0 as usize;
        if slot >= self.expr_construct_args.len() {
            self.expr_construct_args.resize(slot + 1, None);
        }
        self.expr_construct_args[slot] = arg;
    }

    /// Get sparse constructor payload argument data for a `Pexp_construct` expression node.
    pub fn construct_arg(&self, owner: ExprIdx) -> Option<ExprIdx> {
        let slot = owner.0 as usize;
        self.expr_construct_args
            .get(slot)
            .copied()
            .flatten()
            .or_else(|| match &*self.get_expr(owner).pexp_desc {
                ExpressionDesc::Pexp_construct(_, arg) => *arg,
                _ => None,
            })
    }

    /// Attach sparse polymorphic variant payload argument data to a variant expression node.
    pub fn set_variant_arg(&mut self, owner: ExprIdx, arg: Option<ExprIdx>) {
        let slot = owner.0 as usize;
        if slot >= self.expr_variant_args.len() {
            self.expr_variant_args.resize(slot + 1, None);
        }
        self.expr_variant_args[slot] = arg;
    }

    /// Get sparse polymorphic variant payload argument data for a `Pexp_variant` expression node.
    pub fn variant_arg(&self, owner: ExprIdx) -> Option<ExprIdx> {
        let slot = owner.0 as usize;
        self.expr_variant_args
            .get(slot)
            .copied()
            .flatten()
            .or_else(|| match &*self.get_expr(owner).pexp_desc {
                ExpressionDesc::Pexp_variant(inner) => {
                    let (_, arg) = &**inner;
                    *arg
                }
                _ => None,
            })
    }

    /// Attach sparse record spread/base expression data to a record expression node.
    /// Attach record-rest binding data to a record pattern, keyed by its location index.
    pub fn set_record_pat_rest(&mut self, loc: LocIdx, rest: crate::parser::ast::RecordPatRest) {
        self.pat_record_rests.insert(loc, rest);
    }

    /// Get sparse record-rest binding data for a record pattern node.
    pub fn record_pat_rest(&self, loc: LocIdx) -> Option<&crate::parser::ast::RecordPatRest> {
        self.pat_record_rests.get(&loc)
    }

    pub fn take_record_pat_rest(
        &mut self,
        loc: LocIdx,
    ) -> Option<crate::parser::ast::RecordPatRest> {
        self.pat_record_rests.remove(&loc)
    }

    pub fn set_record_spread(&mut self, owner: ExprIdx, spread: Option<ExprIdx>) {
        let slot = owner.0 as usize;
        if slot >= self.expr_record_spreads.len() {
            self.expr_record_spreads.resize(slot + 1, None);
        }
        self.expr_record_spreads[slot] = spread;
    }

    /// Get sparse record spread/base expression data for a `Pexp_record` expression node.
    pub fn record_spread(&self, owner: ExprIdx) -> Option<ExprIdx> {
        let slot = owner.0 as usize;
        self.expr_record_spreads
            .get(slot)
            .copied()
            .flatten()
            .or_else(|| match &*self.get_expr(owner).pexp_desc {
                ExpressionDesc::Pexp_record(inner) => {
                    let (_, spread) = &**inner;
                    *spread
                }
                _ => None,
            })
    }

    /// Attach sparse else-branch expression data to an if-then-else expression node.
    pub fn set_if_else_branch(&mut self, owner: ExprIdx, else_branch: Option<ExprIdx>) {
        let slot = owner.0 as usize;
        if slot >= self.expr_if_else_branches.len() {
            self.expr_if_else_branches.resize(slot + 1, None);
        }
        self.expr_if_else_branches[slot] = else_branch;
    }

    /// Get sparse else-branch expression data for a `Pexp_ifthenelse` expression node.
    pub fn if_else_branch(&self, owner: ExprIdx) -> Option<ExprIdx> {
        let slot = owner.0 as usize;
        self.expr_if_else_branches
            .get(slot)
            .copied()
            .flatten()
            .or_else(|| match &*self.get_expr(owner).pexp_desc {
                ExpressionDesc::Pexp_ifthenelse(inner) => {
                    let (_, _, else_branch) = &**inner;
                    *else_branch
                }
                _ => None,
            })
    }

    /// Attach sparse source type data to a coerce expression node.
    pub fn set_coerce_from_type(&mut self, owner: ExprIdx, from_type: Option<CoreTypeIdx>) {
        let slot = owner.0 as usize;
        if slot >= self.expr_coerce_from_types.len() {
            self.expr_coerce_from_types.resize(slot + 1, None);
        }
        self.expr_coerce_from_types[slot] = from_type;
    }

    /// Get sparse source type data for a `Pexp_coerce` expression node.
    pub fn coerce_from_type(&self, owner: ExprIdx) -> Option<CoreTypeIdx> {
        let slot = owner.0 as usize;
        self.expr_coerce_from_types
            .get(slot)
            .copied()
            .flatten()
            .or_else(|| match &*self.get_expr(owner).pexp_desc {
                ExpressionDesc::Pexp_coerce(inner) => {
                    let (_, from_type, _) = &**inner;
                    *from_type
                }
                _ => None,
            })
    }

    /// Push a pattern into the arena and return its index.
    #[inline]
    pub fn push_pat(&mut self, pat: Pattern) -> PatIdx {
        self.patterns.push(pat)
    }

    /// Reserve a pattern index using a placeholder node.
    #[inline]
    pub fn reserve_pat(&mut self) -> PatIdx {
        self.patterns.reserve_with(Self::placeholder_pat())
    }

    /// Initialize a previously reserved pattern slot.
    #[inline]
    pub fn initialize_pat(&mut self, idx: PatIdx, pat: Pattern) {
        self.patterns.initialize(idx, pat);
    }

    /// Get a pattern by index.
    #[inline]
    pub fn get_pat(&self, idx: PatIdx) -> &Pattern {
        let raw = idx.to_u32();
        if raw < self.synthetic_pattern_base || self.synthetic_patterns.is_empty() {
            self.patterns.get(idx)
        } else {
            self.synthetic_patterns[(raw - self.synthetic_pattern_base) as usize]
                .get()
                .expect("typechecker synthetic pattern read before initialization")
        }
    }

    /// Get a mutable pattern by index.
    #[inline]
    pub fn get_pat_mut(&mut self, idx: PatIdx) -> &mut Pattern {
        self.patterns.get_mut(idx)
    }

    /// Get the number of patterns in the arena.
    pub fn pat_count(&self) -> usize {
        self.patterns.len()
    }

    /// Push a core type into the arena and return its index.
    #[inline]
    pub fn push_core_type(&mut self, typ: CoreType) -> CoreTypeIdx {
        self.core_types.push(typ)
    }

    /// Reserve a core type index using a placeholder node.
    #[inline]
    pub fn reserve_core_type(&mut self) -> CoreTypeIdx {
        self.core_types.reserve_with(Self::placeholder_core_type())
    }

    /// Initialize a previously reserved core type slot.
    #[inline]
    pub fn initialize_core_type(&mut self, idx: CoreTypeIdx, typ: CoreType) {
        self.core_types.initialize(idx, typ);
    }

    /// Get a core type by index.
    #[inline]
    pub fn get_core_type(&self, idx: CoreTypeIdx) -> &CoreType {
        self.core_types.get(idx)
    }

    /// Get a mutable core type by index.
    #[inline]
    pub fn get_core_type_mut(&mut self, idx: CoreTypeIdx) -> &mut CoreType {
        self.core_types.get_mut(idx)
    }

    /// Get the number of core types in the arena.
    pub fn core_type_count(&self) -> usize {
        self.core_types.len()
    }

    /// Push a module expression into the arena and return its index.
    #[inline]
    pub fn push_mod_expr(&mut self, me: ModuleExpr) -> ModExprIdx {
        self.mod_exprs.push(me)
    }

    /// Reserve a module expression index using a placeholder node.
    #[inline]
    pub fn reserve_mod_expr(&mut self) -> ModExprIdx {
        self.mod_exprs.reserve_with(Self::placeholder_mod_expr())
    }

    /// Initialize a previously reserved module expression slot.
    #[inline]
    pub fn initialize_mod_expr(&mut self, idx: ModExprIdx, me: ModuleExpr) {
        self.mod_exprs.initialize(idx, me);
    }

    /// Get a module expression by index.
    #[inline]
    pub fn get_mod_expr(&self, idx: ModExprIdx) -> &ModuleExpr {
        self.mod_exprs.get(idx)
    }

    /// Get a mutable module expression by index.
    #[inline]
    pub fn get_mod_expr_mut(&mut self, idx: ModExprIdx) -> &mut ModuleExpr {
        self.mod_exprs.get_mut(idx)
    }

    /// Push a module type into the arena and return its index.
    #[inline]
    pub fn push_mod_type(&mut self, mt: ModuleType) -> ModTypeIdx {
        self.mod_types.push(mt)
    }

    /// Reserve a module type index using a placeholder node.
    #[inline]
    pub fn reserve_mod_type(&mut self) -> ModTypeIdx {
        self.mod_types.reserve_with(Self::placeholder_mod_type())
    }

    /// Initialize a previously reserved module type slot.
    #[inline]
    pub fn initialize_mod_type(&mut self, idx: ModTypeIdx, mt: ModuleType) {
        self.mod_types.initialize(idx, mt);
    }

    /// Get a module type by index.
    #[inline]
    pub fn get_mod_type(&self, idx: ModTypeIdx) -> &ModuleType {
        self.mod_types.get(idx)
    }

    /// Get a mutable module type by index.
    #[inline]
    pub fn get_mod_type_mut(&mut self, idx: ModTypeIdx) -> &mut ModuleType {
        self.mod_types.get_mut(idx)
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
    use crate::parser::ast::{
        ArgLabel, Attributes, Case, ExpressionDesc, Pattern, PatternDesc, PexpFun,
    };

    fn ident_expr(arena: &mut ParseArena, name: &str) -> Expression {
        let lid = arena.push_lident(name);
        Expression {
            pexp_desc: Box::new(ExpressionDesc::Pexp_ident(Located {
                txt: lid,
                loc: LocIdx::default(),
            })),
            pexp_loc: LocIdx::default(),
            pexp_attributes: Attributes::new(),
        }
    }

    #[test]
    fn test_position_push() {
        let mut arena = ParseArena::new();
        let test_file = arena.intern("test.res");
        let base_count = arena.position_count();
        assert_eq!(base_count, 2); // Pre-allocated none + dummy positions

        let idx1 = arena.push_pos(test_file, 1, 0, 5);
        let idx2 = arena.push_pos(test_file, 1, 0, 5);
        let idx3 = arena.push_pos(test_file, 1, 0, 10);

        // Each push creates a new entry (no deduplication)
        assert_ne!(idx1, idx2);
        assert_ne!(idx1, idx3);
        assert_ne!(idx2, idx3);

        assert_eq!(arena.position_count(), base_count + 3);
    }

    #[test]
    fn test_location_push() {
        let mut arena = ParseArena::new();
        let test_file = arena.intern("test.res");
        let base_count = arena.location_count();
        assert_eq!(base_count, 2); // Pre-allocated none + dummy locations

        let start = arena.push_pos(test_file, 1, 0, 0);
        let end = arena.push_pos(test_file, 1, 0, 10);

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
        assert_eq!(arena.get_string(pos.file_name), "_none_");
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
        let test_file = arena.intern("test.res");

        let start = Position::new(test_file, 1, 0, 0);
        let end = Position::new(test_file, 1, 0, 10);

        let loc = arena.mk_loc_from_positions(&start, &end);

        assert_eq!(arena.loc_start(loc).line, 1);
        assert_eq!(arena.loc_end(loc).cnum, 10);
    }

    #[test]
    fn test_to_location() {
        let mut arena = ParseArena::new();
        let test_file = arena.intern("test.res");

        let start = Position::new(test_file, 1, 0, 0);
        let end = Position::new(test_file, 1, 0, 10);

        let loc_idx = arena.mk_loc_from_positions(&start, &end);
        let loc = arena.to_location(loc_idx);

        assert_eq!(loc.loc_start.line, 1);
        assert_eq!(loc.loc_end.cnum, 10);
        assert!(!loc.loc_ghost);
    }

    #[test]
    fn test_mk_loc_spanning() {
        let mut arena = ParseArena::new();
        let test_file = arena.intern("test.res");

        let pos1 = arena.push_pos(test_file, 1, 0, 0);
        let pos2 = arena.push_pos(test_file, 1, 0, 5);
        let pos3 = arena.push_pos(test_file, 2, 20, 25);
        let pos4 = arena.push_pos(test_file, 2, 20, 30);

        let loc1 = arena.mk_loc(pos1, pos2);
        let loc2 = arena.mk_loc(pos3, pos4);

        let spanning = arena.mk_loc_spanning(loc1, loc2);

        assert_eq!(arena.loc_start(spanning).line, 1);
        assert_eq!(arena.loc_start(spanning).cnum, 0);
        assert_eq!(arena.loc_end(spanning).line, 2);
        assert_eq!(arena.loc_end(spanning).cnum, 30);
    }

    #[test]
    fn test_reserve_initialize_expr_two_phase() {
        let mut arena = ParseArena::new();
        let slot = arena.reserve_expr();
        let placeholder = arena.get_expr(slot);
        assert!(matches!(
            &*placeholder.pexp_desc,
            ExpressionDesc::Pexp_ident(_)
        ));

        let expr = ident_expr(&mut arena, "ready");
        arena.initialize_expr(slot, expr);

        let initialized = arena.get_expr(slot);
        match &*initialized.pexp_desc {
            ExpressionDesc::Pexp_ident(loc) => {
                assert_eq!(
                    arena.get_string(arena.get_longident(loc.txt).last_idx()),
                    "ready"
                );
            }
            _ => panic!("expected ident expression after initialize"),
        }
    }

    #[test]
    fn test_sparse_expr_side_tables() {
        let mut arena = ParseArena::new();
        let owner_expr = ident_expr(&mut arena, "owner");
        let owner = arena.push_expr(owner_expr);
        let default_expr_node = ident_expr(&mut arena, "def");
        let default_expr = arena.push_expr(default_expr_node);
        let guard_expr_node = ident_expr(&mut arena, "guard");
        let guard_expr = arena.push_expr(guard_expr_node);
        let from_type = arena.push_core_type(ParseArena::placeholder_core_type());

        assert_eq!(arena.fun_default(owner), None);
        assert_eq!(arena.case_guard(owner, 0), None);
        assert_eq!(arena.construct_arg(owner), None);
        assert_eq!(arena.variant_arg(owner), None);
        assert_eq!(arena.record_spread(owner), None);
        assert_eq!(arena.if_else_branch(owner), None);
        assert_eq!(arena.coerce_from_type(owner), None);

        arena.set_fun_default(owner, Some(default_expr));
        arena.set_case_guards(owner, vec![None, Some(guard_expr)]);
        arena.set_construct_arg(owner, Some(default_expr));
        arena.set_variant_arg(owner, Some(guard_expr));
        arena.set_record_spread(owner, Some(default_expr));
        arena.set_if_else_branch(owner, Some(guard_expr));
        arena.set_coerce_from_type(owner, Some(from_type));

        assert_eq!(arena.fun_default(owner), Some(default_expr));
        assert_eq!(arena.case_guard(owner, 0), None);
        assert_eq!(arena.case_guard(owner, 1), Some(guard_expr));
        assert_eq!(arena.case_guard(owner, 2), None);
        assert_eq!(arena.construct_arg(owner), Some(default_expr));
        assert_eq!(arena.variant_arg(owner), Some(guard_expr));
        assert_eq!(arena.record_spread(owner), Some(default_expr));
        assert_eq!(arena.if_else_branch(owner), Some(guard_expr));
        assert_eq!(arena.coerce_from_type(owner), Some(from_type));
    }

    #[test]
    fn test_sparse_expr_side_tables_seed_from_expr_and_fallback_after_mutation() {
        let mut arena = ParseArena::new();

        let lhs = arena.push_pat(Pattern {
            ppat_desc: Box::new(PatternDesc::Ppat_any),
            ppat_loc: LocIdx::default(),
            ppat_attributes: Attributes::new(),
        });
        let rhs_expr = ident_expr(&mut arena, "rhs");
        let rhs = arena.push_expr(rhs_expr);
        let default_expr_node = ident_expr(&mut arena, "default");
        let default_expr = arena.push_expr(default_expr_node);
        let fun_owner = arena.push_expr(Expression {
            pexp_desc: Box::new(ExpressionDesc::Pexp_fun(Box::new(PexpFun {
                arg_label: ArgLabel::Nolabel,
                default: Some(default_expr),
                lhs,
                rhs,
                arity: arena.static_arity_none(),
                is_async: false,
            }))),
            pexp_loc: LocIdx::default(),
            pexp_attributes: Attributes::new(),
        });

        let case_lhs = arena.push_pat(Pattern {
            ppat_desc: Box::new(PatternDesc::Ppat_any),
            ppat_loc: LocIdx::default(),
            ppat_attributes: Attributes::new(),
        });
        let case_rhs_node = ident_expr(&mut arena, "case_rhs");
        let case_rhs = arena.push_expr(case_rhs_node);
        let guard_expr_node = ident_expr(&mut arena, "guard");
        let guard_expr = arena.push_expr(guard_expr_node);
        let match_owner = arena.push_expr(Expression {
            pexp_desc: Box::new(ExpressionDesc::Pexp_match(Box::new((
                rhs,
                vec![Case {
                    pc_bar: None,
                    pc_lhs: case_lhs,
                    pc_guard: Some(guard_expr),
                    pc_rhs: case_rhs,
                }],
            )))),
            pexp_loc: LocIdx::default(),
            pexp_attributes: Attributes::new(),
        });

        let ctor_lid = Located {
            txt: arena.push_lident("Ctor"),
            loc: LocIdx::default(),
        };
        let construct_owner = arena.push_expr(Expression {
            pexp_desc: Box::new(ExpressionDesc::Pexp_construct(ctor_lid, Some(default_expr))),
            pexp_loc: LocIdx::default(),
            pexp_attributes: Attributes::new(),
        });

        let variant_owner = arena.push_expr(Expression {
            pexp_desc: Box::new(ExpressionDesc::Pexp_variant(Box::new((
                "Tag".into(),
                Some(guard_expr),
            )))),
            pexp_loc: LocIdx::default(),
            pexp_attributes: Attributes::new(),
        });

        let record_owner = arena.push_expr(Expression {
            pexp_desc: Box::new(ExpressionDesc::Pexp_record(Box::new((
                vec![],
                Some(default_expr),
            )))),
            pexp_loc: LocIdx::default(),
            pexp_attributes: Attributes::new(),
        });

        let if_owner = arena.push_expr(Expression {
            pexp_desc: Box::new(ExpressionDesc::Pexp_ifthenelse(Box::new((
                rhs,
                case_rhs,
                Some(guard_expr),
            )))),
            pexp_loc: LocIdx::default(),
            pexp_attributes: Attributes::new(),
        });

        let from_type = arena.push_core_type(ParseArena::placeholder_core_type());
        let to_type = arena.push_core_type(ParseArena::placeholder_core_type());
        let coerce_owner = arena.push_expr(Expression {
            pexp_desc: Box::new(ExpressionDesc::Pexp_coerce(Box::new((
                rhs,
                Some(from_type),
                to_type,
            )))),
            pexp_loc: LocIdx::default(),
            pexp_attributes: Attributes::new(),
        });

        assert_eq!(arena.fun_default(fun_owner), Some(default_expr));
        assert_eq!(arena.case_guard(match_owner, 0), Some(guard_expr));
        assert_eq!(arena.construct_arg(construct_owner), Some(default_expr));
        assert_eq!(arena.variant_arg(variant_owner), Some(guard_expr));
        assert_eq!(arena.record_spread(record_owner), Some(default_expr));
        assert_eq!(arena.if_else_branch(if_owner), Some(guard_expr));
        assert_eq!(arena.coerce_from_type(coerce_owner), Some(from_type));

        // get_expr_mut clears sparse cache entries; fallback to inline fields must preserve behavior.
        let _ = arena.get_expr_mut(fun_owner);
        let _ = arena.get_expr_mut(match_owner);
        let _ = arena.get_expr_mut(construct_owner);
        let _ = arena.get_expr_mut(variant_owner);
        let _ = arena.get_expr_mut(record_owner);
        let _ = arena.get_expr_mut(if_owner);
        let _ = arena.get_expr_mut(coerce_owner);

        assert_eq!(arena.fun_default(fun_owner), Some(default_expr));
        assert_eq!(arena.case_guard(match_owner, 0), Some(guard_expr));
        assert_eq!(arena.construct_arg(construct_owner), Some(default_expr));
        assert_eq!(arena.variant_arg(variant_owner), Some(guard_expr));
        assert_eq!(arena.record_spread(record_owner), Some(default_expr));
        assert_eq!(arena.if_else_branch(if_owner), Some(guard_expr));
        assert_eq!(arena.coerce_from_type(coerce_owner), Some(from_type));
    }

    #[test]
    fn test_reserve_initialize_other_node_kinds() {
        let mut arena = ParseArena::new();

        let pat_slot = arena.reserve_pat();
        let ty_slot = arena.reserve_core_type();
        let me_slot = arena.reserve_mod_expr();
        let mt_slot = arena.reserve_mod_type();

        arena.initialize_pat(pat_slot, ParseArena::placeholder_pat());
        arena.initialize_core_type(ty_slot, ParseArena::placeholder_core_type());
        arena.initialize_mod_expr(me_slot, ParseArena::placeholder_mod_expr());
        arena.initialize_mod_type(mt_slot, ParseArena::placeholder_mod_type());

        assert!(matches!(
            &*arena.get_pat(pat_slot).ppat_desc,
            PatternDesc::Ppat_any
        ));
        assert!(matches!(
            &*arena.get_core_type(ty_slot).ptyp_desc,
            CoreTypeDesc::Ptyp_any
        ));
        assert!(matches!(
            &*arena.get_mod_expr(me_slot).pmod_desc,
            ModuleExprDesc::Pmod_ident(_)
        ));
        assert!(matches!(
            &*arena.get_mod_type(mt_slot).pmty_desc,
            ModuleTypeDesc::Pmty_ident(_)
        ));
    }
}
