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

use ahash::{AHashMap as HashMap, AHashSet as HashSet};

use serde::{Deserialize, Serialize};

use crate::arena::{Arena, ArenaIdx};
use crate::intern::Interner;
use crate::location::{Location, Position};
use crate::parser::ast::{
    ArgLabel, Attributes, Case, Constant, CoreType, CoreTypeDesc, Expression, ExpressionDesc,
    ExpressionRecordField, FunParam, ModuleExpr, ModuleExprDesc, ModuleType, ModuleTypeDesc,
    Pattern, PatternDesc, PatternRecordField, StringConst, StringLoc, ValueBinding,
    ValueConstraint,
};
use crate::parser::longident::Longident;
use crate::string_literal::StringLiteral;

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

/// First index of typechecker-generated synthetic locations.
const SYNTHETIC_LOCATION_BASE: u32 = 0x8000_0000;
/// First index of the positions of typechecker-interned locations.
const SYNTHETIC_POSITION_BASE: u32 = 0x8000_0000;
/// First index of expressions appended while the arena is shared
/// ([`ParseArena::push_shared_expr`]).
const SHARED_EXPRESSION_BASE: u32 = 0x8000_0000;
/// First index of core types appended while the arena is shared.
const SHARED_CORE_TYPE_BASE: u32 = 0x8000_0000;
/// First index of strings appended through a shared arena
/// ([`ParseArena::push_shared_string`]); above every interned and
/// typechecker-synthetic string index.
const SHARED_STRING_BASE: u32 = 0xC000_0000;

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

/// Bit 2 of an expression's entry in `ParseArena::rewrite_free_exprs`.
const EXPANSION_BIT: u64 = 4;
/// Expressions per page of `ParseArena::expansion_targets`.
const EXPANSION_PAGE: usize = 64;

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
    /// Shared `Js` module identifier.
    pub js_lident: LidentIdx,
    /// Shared `Js.typeof` primitive path.
    pub js_typeof: LidentIdx,
    /// Shared `Js.undefinedToOption` helper path.
    pub js_undefined_to_option: LidentIdx,
    /// Shared `Js.Undefined` module path.
    pub js_undefined: LidentIdx,
    /// Shared `Js.Undefined.empty` value path.
    pub js_undefined_empty: LidentIdx,
    /// Shared `Primitive_js_extern` module path.
    pub js_oo_lident: LidentIdx,
    /// Shared `Primitive_js_extern.Callback` type path.
    pub js_oo_callback: LidentIdx,
}

/// Pre-allocated `Ast_literal` core type nodes used by PPX rewrites.
///
/// OCaml's `ast_literal.ml` exposes module-level constants for these no-loc
/// core types. Reusing one arena index per type mirrors that pointer identity.
#[derive(Debug, Clone, Copy)]
pub struct StaticAstLiteralTypes {
    /// Shared location-free `string` type node.
    pub type_string: CoreTypeIdx,
    /// Shared location-free `int` type node.
    pub type_int: CoreTypeIdx,
    /// Shared location-free `bool` type node.
    pub type_bool: CoreTypeIdx,
    /// Shared location-free `float` type node.
    pub type_float: CoreTypeIdx,
}

type FunDefaultBinding = (FunParam, Option<crate::parser::ast::ValueBinding>);

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
    json_ctyp_lident: Option<LidentIdx>,
    strings: [Option<StrIdx>; SpiceStringKey::COUNT],
}

impl SpiceCache {
    fn new() -> Self {
        Self {
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

/// Sparse expression payloads set explicitly (see `ParseArena::expr_overrides`).
///
/// Intentional Rust performance representation for expression fields that
/// are usually absent.
///
/// OCaml compiler/ml/parsetree.ml:210-214 stores one expression record,
/// and parsetree.ml:226-298 stores these payloads directly inside
/// `expression_desc` variants. The arena parser keeps them in side tables
/// keyed by stable `ExprIdx` so common expression nodes stay compact. Do
/// not move these back inline during parity cleanup unless the replacement
/// keeps the same AST behavior and comparable parser memory profile.
#[derive(Debug, Clone, Default)]
struct ExprOverrides {
    /// Function default expression, keyed by the function's ExprIdx.
    fun_default: Option<ExprIdx>,
    /// Case-indexed optional guard expressions of a match/try.
    case_guards: Option<Box<[Option<ExprIdx>]>>,
    /// Record spread/base expression.
    record_spread: Option<ExprIdx>,
    /// Else branch of an if-then-else.
    if_else_branch: Option<ExprIdx>,
    /// `Pexp_coerce` source type annotation.
    coerce_from_type: Option<CoreTypeIdx>,
}

/// Arena for positions and locations during parsing.
///
/// This provides:
/// - Efficient storage: positions/locations stored once, referenced by index
/// - Lightweight handles: indices are 4 bytes, cheap to copy/compare
/// - Identity for marshalling: same index = same object
///
/// The arena does not deduplicate by content: every `push_*` creates a fresh
/// entry, and sharing comes from reusing an index, mirroring OCaml's pointer
/// identity (the same value passed by reference marshals as one shared object).
/// Literal values shared by OCaml (e.g. `static_arity_*`) use pre-allocated
/// indices.
#[derive(Debug)]
pub struct ParseArena {
    /// Optional module-owned census, absent on the default compilation path.
    pub derived_census: Option<Box<crate::derived_census::Census>>,
    #[cfg(test)]
    pub(crate) derived_scope_steps: std::cell::Cell<crate::binary_ast::derive::ScopeSteps>,
    /// Location-free builds retain node identity and generated/source provenance,
    /// but allocate no position or location records. Full locations are populated
    /// only by a fresh diagnostic compilation.
    store_locations: bool,
    /// Assigned once by the first consuming context. The numeric scope
    /// survives arena moves and needs no address-based registration.
    declaration_location_scope: std::sync::OnceLock<u64>,
    next_location_identity: std::sync::atomic::AtomicU32,
    /// Location-free builds: `next_location_identity` when parsing (including
    /// the frontend) finished. Up to here each identity is the index the same
    /// source's located parse gives its location, so warnings can be placed
    /// with a fresh located parse instead of a second compilation.
    parse_location_slots: Option<u32>,
    /// Location-free identities the type checker re-imported from a
    /// `Location`'s `origin`. Such a value may have come from another unit's
    /// arena, so it is not known to name a slot of this unit's parse.
    reimported_location_identities: std::sync::Mutex<Vec<u32>>,
    locations_required: std::sync::atomic::AtomicBool,
    /// File identity is unit metadata, not a source span. JSX uses it for names.
    absent_position: Position,
    /// Arena of positions (returns PosIdx).
    positions: Arena<Position, PosIdx>,
    /// File names of all positions pushed so far (resolved lazily by
    /// `source_file_names`; arena strings are immutable).
    position_file_names: HashSet<StrIdx>,
    /// Most recent file name recorded in `position_file_names`.
    last_position_file_name: Option<StrIdx>,
    /// Arena of locations (returns LocIdx).
    locations: Arena<InternedLocation, LocIdx>,
    /// Arena of longidents (returns LidentIdx).
    longidents: Arena<Longident, LidentIdx>,
    /// Slots reserved before type checking for environment-dependent synthetic
    /// longidents, such as record-field qualification and omitted labels.
    synthetic_longidents: SyntheticVec<Longident>,
    synthetic_longident_base: u32,
    /// Arena of arities (returns ArityIdx).
    /// Use `push_arity()` for computed paths (fresh indices).
    /// Use `static_arities` for literal paths (shared indices).
    arities: Vec<Option<i32>>,
    /// Payloads set through `set_fun_default` and the other sparse setters,
    /// overriding the fields stored in the expression itself. Getters read
    /// the expression otherwise, so building an expression costs nothing here.
    expr_overrides: crate::fast_hash::AHashMap<u32, Box<ExprOverrides>>,
    /// Arena of expressions (returns ExprIdx).
    /// Replaces `Box<Expression>` for recursive AST references.
    expressions: Arena<Expression, ExprIdx>,
    /// Pool behind every `Pexp_apply` argument list.
    apply_args: ListPool<(ArgLabel, ExprIdx)>,
    /// Pools behind expression, pattern and core type index lists.
    expr_lists: ListPool<ExprIdx>,
    pat_lists: ListPool<PatIdx>,
    type_lists: ListPool<CoreTypeIdx>,
    /// Pool behind `let` value binding lists (`Pexp_let`, `Pstr_value`).
    vb_lists: ListPool<ValueBinding>,
    /// Derived structure-value groups, indexed by their binding-list start.
    /// Only group starts have a bit; no source-location or identifier keys.
    derived_value_groups: Vec<u64>,
    /// Plans of derived items: `StructureItemDesc::Pstr_derived` handles
    /// index these pools.
    plans: crate::binary_ast::derive::plan::Plans,
    /// Pools behind record field lists and match/try case lists.
    expr_field_lists: ListPool<ExpressionRecordField>,
    pat_field_lists: ListPool<PatternRecordField>,
    case_lists: ListPool<Case>,
    /// Pool behind the elements of `Pexp_spread`.
    spread_element_lists: ListPool<crate::parser::ast::SpreadElement>,
    /// N-ary source parameter lists keyed by the function body's arena index.
    ///
    /// `PexpFun` keeps only a compact first-parameter fallback for frozen-v0 PPX
    /// conversion. Parser-created current parsetrees use this table as the
    /// authoritative `Pexp_fun.params` representation.
    nary_fun_params_by_first_pattern: HashMap<PatIdx, ArenaList<FunParam>>,
    /// Pool behind `nary_fun_params_by_first_pattern`.
    nary_fun_param_lists: ListPool<FunParam>,
    nary_fun_unknown_arity_by_first_pattern: HashMap<PatIdx, ArityIdx>,
    /// Optional-default lowering prepared before type checking.
    ///
    /// Typecore must not append to the parse arena through a shared reference:
    /// doing so invalidates Rust's aliasing guarantees and was miscompiled in
    /// release builds. Keep the OCaml-shaped synthetic AST here, constructed
    /// while the arena is still exclusively borrowed.
    nary_fun_default_bindings_by_first_pattern:
        HashMap<PatIdx, Box<[FunDefaultBinding]>>,
    /// N-ary locally-abstract-type (`newtypes`) lists keyed by the function's
    /// first parameter pattern, mirroring `Pexp_fun.newtypes` in the current
    /// upstream parsetree. Each entry is `(name, attributes)`; the parser puts
    /// the type-parameter group's attributes on the group's first newtype.
    nary_fun_newtypes_by_first_pattern: HashMap<PatIdx, Box<[(StringLoc, Attributes)]>>,
    nary_arrow_args_by_first_type: HashMap<CoreTypeIdx, ArenaList<crate::parser::ast::TypeArg>>,
    /// Pool behind `nary_arrow_args_by_first_type`.
    nary_arrow_arg_lists: ListPool<crate::parser::ast::TypeArg>,
    /// Sparse current-Parsetree value constraints keyed by the binding pattern.
    value_constraints_by_pattern: HashMap<PatIdx, ValueConstraint>,
    /// Bindings whose `Ast_helper.Typ.varify_constructors` raises
    /// `Syntaxerr.Error`; OCaml only raises it when `type_let` reaches them.
    value_constraint_varify_errors: HashMap<PatIdx, LocIdx>,
    /// The first error raised by a nested builtin-ppx rewrite whose caller
    /// cannot return a `Result`; OCaml's mapper raises it immediately, so the
    /// public rewrite entry points report it before any later error.
    ppx_deferred_error: Option<crate::binary_ast::ppx::PpxError>,
    /// Whether the builtin spice mapper stands in for a configured external
    /// spice derive (see `binary_ast::derive`).
    builtin_spice_disabled: bool,
    /// Why the derive seam plans no item of this tree, or `None` when it
    /// plans. Only a tree that is compiled in the same process is planned:
    /// one that is stored, printed or handed to another program holds syntax.
    derived_plans_off: Option<crate::binary_ast::derive::GeneralReason>,
    /// `Experimental_features.is_enabled LetUnwrap` for the builtin PPX run on
    /// this arena, which decides the error a `let?` binding raises
    /// (bs_builtin_ppx.ml:273, 366, 565). Set by the rewrite entry points.
    experimental_let_unwrap: bool,
    /// OCaml `Used_attributes` (compiler/ml/used_attributes.ml): attribute name
    /// locations marked as consumed by the builtin PPX, consulted by the
    /// unused-attribute sweep (`Bs_ast_invariant.warn_unused_attribute`).
    used_attributes: std::sync::Mutex<HashSet<LocIdx>>,
    /// Conservative parser observation; speculative parses may leave this set.
    has_gentype_annotations: bool,
    /// The parser saw an attribute the checks of `crate::verify` read.
    has_verify_annotations: bool,
    /// Arena of patterns (returns PatIdx).
    /// Replaces `Box<Pattern>` for recursive AST references.
    patterns: Arena<Pattern, PatIdx>,
    /// Append-only stable storage for OCaml-shaped synthetic pattern rewrites.
    synthetic_patterns: SyntheticVec<Pattern>,
    synthetic_pattern_base: u32,
    /// Typechecker-generated locations (e.g. OCaml's `{loc with loc_ghost =
    /// true}` copies), appended while the arena is shared. Addressed from
    /// `SYNTHETIC_LOCATION_BASE` so they never collide with primary indices.
    synthetic_locations: elsa::sync::FrozenVec<Box<InternedLocation>>,
    /// Expressions built while the arena is shared, addressed from
    /// `SHARED_EXPRESSION_BASE`: the `@as` payloads printers put back with
    /// `Ast_helper.Type.field_attributes` / `constructor_attributes`.
    shared_expressions: elsa::sync::FrozenVec<Box<Expression>>,
    /// Core types built while the arena is shared, addressed from
    /// `SHARED_CORE_TYPE_BASE`: the tuples the type checker rebuilds from
    /// polymorphic variant payload groups (`Ast_helper.Typ.tuple`).
    shared_core_types: elsa::sync::FrozenVec<Box<CoreType>>,
    /// Strings built through a shared arena, addressed from
    /// `SHARED_STRING_BASE`: the payloads printers rebuild for `%raw`
    /// (`Ast_raw.to_extension`).
    shared_strings: elsa::sync::FrozenVec<Box<str>>,
    /// `Lident` of `true`, `false`, `null` and `undefined`, for those payloads.
    runtime_tag_lidents: [LidentIdx; 4],
    /// The attribute name `as`.
    as_attribute_name: StrIdx,
    /// The JSX component attribute names `react.component`,
    /// `react.componentWithProps`, `jsx.component` and
    /// `jsx.componentWithProps`, which printers put back from the
    /// `jsx_component` nodes (`Ast_helper.Jsx_component.to_attribute`).
    jsx_component_attribute_names: [StrIdx; 4],
    /// Positions of typechecker-interned locations, addressed from
    /// `SYNTHETIC_POSITION_BASE`.
    synthetic_positions: elsa::sync::FrozenVec<Box<Position>>,
    /// Slots reserved before type checking for strings discovered only after
    /// environment lookup (notably omitted record labels).
    synthetic_strings: elsa::sync::FrozenVec<String>,
    synthetic_string_base: u32,
    /// The interned [`crate::name::Name`] of each parsed string, filled on
    /// first use: identifier occurrences are resolved several times during
    /// type checking (lookup, open/module marking, usage marks), and each
    /// resolution would otherwise hash the string again. Sized to the parsed
    /// strings when first read; later strings are interned uncached.
    string_names: std::sync::OnceLock<Box<[std::sync::OnceLock<crate::name::Name>]>>,
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
    promise_primitives: [LidentIdx; 2],
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
    static_option_lid: LidentIdx,
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
    /// Pre-allocated empty string. OCaml string literals are statically shared,
    /// so conservative single-variable extraction of a wildcard needs one
    /// canonical empty StrIdx.
    static_empty_str: StrIdx,
    /// Pre-allocated `"x"`. OCaml's let-unwrap desugar falls back to the static
    /// literal `"x"` (bs_builtin_ppx.ml), shared across every site.
    static_x_name: StrIdx,
    /// Pre-allocated `"res.constructor_from_spread"` attribute name used by variant spreads.
    static_constructor_from_spread_attr_str: StrIdx,
    /// Pre-allocated `"res.patFromVariantSpread"` attribute name used for synthetic spread patterns.
    static_pat_from_variant_spread_attr_str: StrIdx,
    /// Pre-allocated static longidents used by `%external` rewrite helpers.
    static_ppx_lidents: StaticPpxLidents,
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
    /// The locations of the expressions the built-in mapper visited, one bit
    /// per location index.
    ///
    /// This lets marshal distinguish the attributes of expressions the OCaml
    /// mapper rebuilt (fresh payload wrappers) from parser-preserved ones.
    rewritten_expr_locs: Vec<u64>,
    /// Four bits per expression, sixteen expressions per word: two proofs
    /// computed bottom-up at allocation (no builtin rewrite/checker targets,
    /// bit 0; no unused-attribute sweep targets, bit 1), and "has an
    /// expansion" (bit 2, see `set_expansion`). Bit 3 is unused. Unknown kinds
    /// and mutable slots are never certified.
    rewrite_free_exprs: Vec<u64>,
    /// The expansions of the built-in rewrites, in pages of
    /// `EXPANSION_PAGE` consecutive expressions: `expansion_pages[idx / 64]`
    /// is 0 for a page without expansions, or 1 + the page's position in
    /// `expansion_targets`. The nodes as parsed are never overwritten.
    expansion_pages: Vec<u32>,
    /// `EXPANSION_PAGE` targets per allocated page; an entry is meaningful
    /// only where bit 2 of `rewrite_free_exprs` is set.
    expansion_targets: Vec<ExprIdx>,
    /// Pre-allocated dummy location (line 0, _none_) used by internal PPX.
    dummy_loc: LocIdx,
    /// Spice PPX local caches for generated location/string/lident nodes.
    spice_cache: SpiceCache,
    /// Literal strings that should be value-shared during marshalling.
    shareable_literal_strs: HashSet<String>,
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
        let prim_empty_external_ffi = strings.push_interned("");
        let prim_empty_js_mapper = strings.push_interned("");
        let prim_raw_expr = strings.push_interned("#raw_expr");
        let prim_raw_stmt = strings.push_interned("#raw_stmt");
        let ppx_eq_str = strings.push_interned("==");
        let ppx_js_str = strings.push_interned("Js");
        let ppx_empty_str = strings.push_interned("");
        let ppx_undefined_str = strings.push_interned("undefined");
        let template_concat_str = strings.push_interned("++");
        let static_optional_default_opt_str = strings.intern("*opt*");
        let static_optional_default_sth_str = strings.intern("*sth*");
        let static_default_attr_str = strings.intern("#default");
        let static_empty_str = strings.intern("");
        let static_x_name = strings.intern("x");
        let static_constructor_from_spread_attr_str = strings.intern("res.constructor_from_spread");
        let static_pat_from_variant_spread_attr_str = strings.intern("res.patFromVariantSpread");
        // CMI-loaded declaration attributes are converted back into parser attrs
        // during typedtree reconstruction. Pre-intern the common decl-attr names
        // that can arrive from external CMIs so that round-tripping imported
        // attrs does not depend on local source text having mentioned them.
        let as_attribute_name = strings.intern("as");
        let jsx_component_attribute_names = [
            "react.component",
            "react.componentWithProps",
            "jsx.component",
            "jsx.componentWithProps",
        ]
        .map(|name| strings.intern(name));
        let runtime_tag_lidents = ["true", "false", "null", "undefined"]
            .map(|name| longidents.push(Longident::Lident(strings.intern(name))));
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
        let pat_nil_str = strings.push_interned("[]");
        let pat_cons_str = strings.push_interned("::");
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

        // One pair per compilation, shared by direct promise typing. No
        // identifier or expression is appended when an await is checked.
        let promise = strings.intern("Primitive_promise");
        let await_name = strings.intern("unsafe_await");
        let async_name = strings.intern("unsafe_async");
        let promise_primitives = [
            longidents.push(Longident::Ldot(Box::new(Longident::Lident(promise)), await_name)),
            longidents.push(Longident::Ldot(Box::new(Longident::Lident(promise)), async_name)),
        ];

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
            ptyp_desc: CoreTypeDesc::Ptyp_constr((
                Located { txt, loc: none_loc },
                crate::parse_arena::ArenaList::EMPTY,
            )),
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
            store_locations: true,
            declaration_location_scope: std::sync::OnceLock::new(),
            next_location_identity: std::sync::atomic::AtomicU32::new(2),
            parse_location_slots: None,
            reimported_location_identities: std::sync::Mutex::new(Vec::new()),
            locations_required: std::sync::atomic::AtomicBool::new(false),
            absent_position: Position::default(),
            positions: Arena::default(),
            position_file_names: HashSet::new(),
            last_position_file_name: None,
            locations: Arena::default(),
            longidents,
            synthetic_longidents: SyntheticVec::default(),
            synthetic_longident_base: u32::MAX,
            arities,
            expr_overrides: crate::fast_hash::AHashMap::default(),
            expressions: Arena::default(),
            apply_args: ListPool::default(),
            expr_lists: ListPool::default(),
            pat_lists: ListPool::default(),
            type_lists: ListPool::default(),
            vb_lists: ListPool::default(),
            derived_value_groups: Vec::new(),
            plans: Default::default(),
            derived_census: None,
            #[cfg(test)]
            derived_scope_steps: Default::default(),
            expr_field_lists: ListPool::default(),
            pat_field_lists: ListPool::default(),
            case_lists: ListPool::default(),
            spread_element_lists: ListPool::default(),
            nary_fun_params_by_first_pattern: HashMap::new(),
            nary_fun_param_lists: ListPool::default(),
            nary_fun_unknown_arity_by_first_pattern: HashMap::new(),
            nary_fun_default_bindings_by_first_pattern: HashMap::new(),
            nary_fun_newtypes_by_first_pattern: HashMap::new(),
            nary_arrow_args_by_first_type: HashMap::new(),
            nary_arrow_arg_lists: ListPool::default(),
            value_constraints_by_pattern: HashMap::new(),
            value_constraint_varify_errors: HashMap::new(),
            ppx_deferred_error: None,
            builtin_spice_disabled: false,
            derived_plans_off: Some(crate::binary_ast::derive::GeneralReason::Switch),
            experimental_let_unwrap: false,
            used_attributes: std::sync::Mutex::new(HashSet::new()),
            has_gentype_annotations: false,
            has_verify_annotations: false,
            patterns: Arena::default(),
            synthetic_patterns: SyntheticVec::default(),
            synthetic_pattern_base: u32::MAX,
            synthetic_locations: elsa::sync::FrozenVec::new(),
            shared_expressions: elsa::sync::FrozenVec::new(),
            shared_core_types: elsa::sync::FrozenVec::new(),
            shared_strings: elsa::sync::FrozenVec::new(),
            runtime_tag_lidents,
            as_attribute_name,
            jsx_component_attribute_names,
            synthetic_positions: elsa::sync::FrozenVec::new(),
            synthetic_strings: elsa::sync::FrozenVec::new(),
            synthetic_string_base: u32::MAX,
            string_names: std::sync::OnceLock::new(),
            core_types,
            mod_exprs: Arena::default(),
            mod_types: Arena::default(),
            static_arities,
            static_list_lidents,
            static_array_lidents,
            static_regexp_t_lident,
            static_predef_option_lident,
            promise_primitives,
            static_ast_literal_types,
            static_ast_literal_type_string_lident,
            static_ast_literal_type_int_lident,
            static_ast_literal_type_bool_lident,
            static_ast_literal_type_float_lident,
            static_placeholder_lid: LidentIdx::default(),
            static_none_lid: LidentIdx::default(),
            static_option_lid: LidentIdx::default(),
            static_predef_none_lid,
            static_some_lid,
            static_predef_some_lid,
            static_optional_default_opt_lid,
            static_optional_default_sth_lid,
            static_optional_default_opt_str,
            static_optional_default_sth_str,
            static_default_attr_str,
            static_empty_str,
            static_x_name,
            static_constructor_from_spread_attr_str,
            static_pat_from_variant_spread_attr_str,
            static_ppx_lidents,
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
            rewritten_expr_locs: Vec::new(),
            rewrite_free_exprs: Vec::new(),
            expansion_pages: Vec::new(),
            expansion_targets: Vec::new(),
            dummy_loc: LocIdx::default(),
            spice_cache: SpiceCache::new(),
            shareable_literal_strs: HashSet::new(),
            tyvar_source_by_loc: HashMap::new(),
        }
    }
}

impl ParseArena {
    /// Reserve arena capacity for parsing `source_len` bytes.
    ///
    /// Growing the arenas by doubling copied every node table several times
    /// per file. The ratios are the 90th percentile of nodes per source byte
    /// over a large project, so most files never reallocate.
    pub fn reserve_for_source(&mut self, source_len: usize) {
        if self.store_locations {
            self.positions.reserve(source_len * 45 / 100);
            self.locations.reserve(source_len * 16 / 100);
        }
        self.expressions.reserve(source_len * 9 / 100);
        self.longidents.reserve(source_len * 65 / 1000);
        self.patterns.reserve(source_len * 2 / 100);
        self.core_types.reserve(source_len * 15 / 1000);
        self.strings.reserve(source_len / 10);
    }

    /// OCaml `Used_attributes.mark_used_attribute`: only non-ghost attributes.
    pub fn mark_used_attribute(&self, attr: &crate::parser::ast::Attribute) {
        if !self.loc_ghost(attr.0.loc) {
            self.used_attributes
                .lock()
                .expect("used attributes lock")
                .insert(attr.0.loc);
        }
    }

    /// OCaml `Used_attributes.is_used_attribute`.
    pub fn is_used_attribute(&self, loc: LocIdx) -> bool {
        self.used_attributes
            .lock()
            .expect("used attributes lock")
            .contains(&loc)
    }

    /// Create a new arena with the "none" position and location pre-allocated at index 0.
    ///
    /// This ensures that `LocIdx::default()` (which is `LocIdx(0)`) always refers to
    /// a valid "none" location, even without calling `none_loc()` first.
    pub fn new() -> Self {
        Self::with_locations(true)
    }

    /// Disable source-location storage for speculative, diagnostic-free builds.
    /// Scanner cursor positions remain transient parser state for the grammar.
    pub fn with_locations(store_locations: bool) -> Self {
        let mut arena = Self {
            store_locations,
            ..Self::default()
        };
        // Pre-allocate none file name and position at index 0
        // This way LocIdx::default() == LocIdx(0) is always valid
        let none_file_idx = arena.strings.intern("_none_");
        arena.position_file_names.insert(none_file_idx);
        let none_pos = Position::new(none_file_idx, 1, 0, -1);
        if store_locations {
            let pos_idx = arena.positions.push(none_pos);
            let none_loc = InternedLocation::new(pos_idx, pos_idx, true);
            arena.locations.push(none_loc);
        }
        // Pre-allocate dummy location with line 0 for internal PPX nodes
        let dummy_file_idx = arena.strings.push_interned("_none_");
        arena.position_file_names.insert(dummy_file_idx);
        let dummy_pos = Position::new(dummy_file_idx, 0, 0, -1);
        arena.dummy_loc = if store_locations {
            let dummy_pos_idx = arena.positions.push(dummy_pos);
            let dummy_loc = InternedLocation::new(dummy_pos_idx, dummy_pos_idx, true);
            arena.locations.push(dummy_loc)
        } else {
            LocIdx(1)
        };
        // Pre-allocate placeholder longident (for placeholder AST nodes)
        let placeholder_idx = arena.strings.intern("placeholder");
        arena.static_placeholder_lid = arena.longidents.push(Longident::Lident(placeholder_idx));
        // Pre-allocate "None" longident (for optional field desugaring)
        let none_str = arena.strings.intern("None");
        arena.static_none_lid = arena.longidents.push(Longident::Lident(none_str));
        // Pre-allocate "*predef*" longident
        let predef_str = arena.strings.intern("*predef*");
        arena.longidents.push(Longident::Lident(predef_str));
        // Pre-allocate "option" longident (for optional record label types)
        let option_str = arena.strings.intern("option");
        arena.static_option_lid = arena.longidents.push(Longident::Lident(option_str));
        arena
    }

    /// Set the source filename used by positions, including location-free placeholders.
    pub fn set_source_file(&mut self, file_name: StrIdx) {
        self.absent_position.file_name = file_name;
        self.record_position_file_name(file_name);
    }

    /// The file this arena's source was parsed from.
    pub fn source_file(&self) -> StrIdx {
        self.absent_position.file_name
    }

    /// Whether this arena stores complete source coordinates.
    pub fn stores_locations(&self) -> bool {
        self.store_locations
    }

    /// A semantic consumer (e.g. an assertion payload) needs a full-location
    /// retry even when the compilation emits no warning or error.
    pub fn require_locations(&self) {
        if !self.store_locations {
            self.locations_required
                .store(true, std::sync::atomic::Ordering::Relaxed);
        }
    }

    /// Whether a semantic consumer requested a retry with full source coordinates.
    pub fn locations_required(&self) -> bool {
        self.locations_required
            .load(std::sync::atomic::Ordering::Relaxed)
    }

    /// A location-free arena reuses an identity where a located arena appends
    /// a location (a ghost or cloned copy, a re-imported `Location`). Advance
    /// the identity counter anyway, so identities keep naming the slots a
    /// located parse of the same source allocates.
    fn skip_location_slot(&self) {
        self.next_location_identity
            .fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    }

    /// Record the end of parsing for a location-free arena; see
    /// [`ParseArena::located_parse_slot`].
    pub fn finish_parse_locations(&mut self) {
        if !self.store_locations {
            self.parse_location_slots = Some(
                self.next_location_identity
                    .load(std::sync::atomic::Ordering::Relaxed),
            );
        }
    }

    /// The number of primary locations a parse allocated: for a location-free
    /// arena the identities issued while parsing, otherwise the stored rows.
    pub fn parse_location_slot_count(&self) -> Option<u32> {
        if self.store_locations {
            Some(self.locations.len() as u32)
        } else {
            self.parse_location_slots
        }
    }

    /// The location a located parse of the same source gives the
    /// location-free identity `idx`, when that is certain: `idx` was issued
    /// while parsing (not by the type checker afterwards) and was not
    /// re-imported from a `Location` that may belong to another unit.
    /// Ghostness is dropped: only the span is read from the located arena.
    pub fn located_parse_slot(&self, idx: LocIdx) -> Option<LocIdx> {
        if self.store_locations {
            return None;
        }
        let id = idx.0 & 0x3fff_ffff;
        if id >= self.parse_location_slots? {
            return None;
        }
        if self
            .reimported_location_identities
            .lock()
            .expect("re-imported location identities lock")
            .contains(&id)
        {
            return None;
        }
        Some(LocIdx(id))
    }

    fn fresh_location_identity(&self, ghost: bool) -> LocIdx {
        // Ghostness affects warning eligibility, and identity tracks consumed
        // attributes. Neither encodes a source position. Do not collapse all
        // attributes onto Location.none, which would hide unused attributes.
        let id = self
            .next_location_identity
            .fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        assert!(id < 1 << 24, "location identity overflow");
        LocIdx(id | if ghost { 0x4000_0000 } else { 0 })
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

    /// Get the pre-allocated `Lident "option"` index. Optional record labels
    /// are typed as `Ptyp_constr (Lident "option", [typ])`
    /// (compiler/ml/typedecl.ml:314-329, 600-618).
    pub fn option_lid(&self) -> LidentIdx {
        self.static_option_lid
    }

    /// Get the pre-allocated Ldot(*predef*, "None") longident index.
    /// Used for optional-default rewrites where constructors must resolve to option.
    pub fn predef_none_lid(&self) -> LidentIdx {
        self.static_predef_none_lid
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

    /// Create a `Located<LidentIdx>` with the placeholder longident and given location.
    pub fn placeholder_located(&self, loc: LocIdx) -> Located<LidentIdx> {
        Located {
            txt: self.placeholder_lid(),
            loc,
        }
    }

    // ========== Position methods ==========

    fn record_position_file_name(&mut self, file_name: StrIdx) {
        // Almost every position in a parse shares one file name, so check the
        // most recent one before hashing.
        if self.last_position_file_name == Some(file_name) {
            return;
        }
        self.position_file_names.insert(file_name);
        self.last_position_file_name = Some(file_name);
    }

    pub(crate) fn declaration_location_scope(&self, allocate: impl FnOnce() -> u64) -> u64 {
        *self.declaration_location_scope.get_or_init(allocate)
    }

    /// Push a position into the arena and return its index.
    /// Creates a fresh entry each time - sharing is achieved by passing the same
    /// PosIdx through code paths (reference sharing), not by value deduplication.
    pub fn push_position(&mut self, pos: Position) -> PosIdx {
        self.record_position_file_name(pos.file_name);
        if self.store_locations {
            self.positions.push(pos)
        } else {
            self.none_pos()
        }
    }

    /// Push a position from components.
    /// Creates a fresh position each time (no deduplication).
    /// This matches OCaml's behavior where each position is a separate object.
    /// file_name should be an interned StrIdx (from arena.intern_string).
    pub fn push_pos(&mut self, file_name: StrIdx, line: i32, bol: i32, cnum: i32) -> PosIdx {
        self.push_position(Position::new(file_name, line, bol, cnum))
    }

    /// Get the "none" position index (for _none_ file).
    /// Returns the pre-allocated index 0.
    pub fn none_pos(&self) -> PosIdx {
        PosIdx(0)
    }

    /// Look up a position by index.
    pub fn get_position(&self, idx: PosIdx) -> &Position {
        if !self.store_locations {
            return &self.absent_position;
        }
        let raw = idx.to_u32();
        if raw < SYNTHETIC_POSITION_BASE {
            self.positions.get(idx)
        } else {
            self.synthetic_positions
                .get((raw - SYNTHETIC_POSITION_BASE) as usize)
                .expect("typechecker synthetic position read before initialization")
        }
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
        if self.store_locations {
            assert!(self.locations.len() < 1 << 30, "location pool overflow");
            self.locations.push(loc)
        } else {
            self.fresh_location_identity(loc.loc_ghost)
        }
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
        if !self.store_locations {
            self.skip_location_slot();
            return loc;
        }
        let info = self.get_location(loc).clone();
        let start = *self.get_position(info.loc_start);
        let end = *self.get_position(info.loc_end);
        let start_idx = self.push_position(start);
        let end_idx = self.push_position(end);
        self.push_loc(start_idx, end_idx, info.loc_ghost)
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
        let json_idx = self.push_string("JSON");
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

    /// Look up a location, applying its immutable ghost-view bit.
    /// Cost: one indexed load and one bit test for a source location; no
    /// allocation or synchronization for a ghost view of a source location.
    // Keep field-only readers scalar: an out-of-line 12-byte return copies
    // unused coordinates even when the caller only tests ghostness.
    #[inline(always)]
    pub fn get_location(&self, idx: LocIdx) -> InternedLocation {
        if !self.store_locations {
            const SOURCE: InternedLocation = InternedLocation {
                loc_start: PosIdx(0),
                loc_end: PosIdx(0),
                loc_ghost: false,
            };
            const GENERATED: InternedLocation = InternedLocation {
                loc_start: PosIdx(0),
                loc_end: PosIdx(0),
                loc_ghost: true,
            };
            return if idx.0 < 2 || idx.0 & 0x4000_0000 != 0 {
                GENERATED
            } else {
                SOURCE
            };
        }
        let raw = idx.to_u32() & !0x4000_0000;
        let mut location = if raw < SYNTHETIC_LOCATION_BASE {
            self.locations.get(LocIdx(raw)).clone()
        } else {
            self.synthetic_locations
                .get((raw - SYNTHETIC_LOCATION_BASE) as usize)
                .expect("typechecker synthetic location read before initialization").clone()
        };
        location.loc_ghost |= idx.0 & 0x4000_0000 != 0;
        location
    }

    /// An immutable ghost view of an existing location.
    /// Cost: one bitwise OR, no allocation, lookup, lock or stored row.
    #[inline]
    pub fn ghost_location(&self, idx: LocIdx) -> LocIdx {
        LocIdx(idx.0 | 0x4000_0000)
    }

    /// The await primitive's identifier, allocated once per arena.
    /// Cost: one field read; no lookup or allocation.
    pub fn promise_await_lident(&self) -> LidentIdx {
        self.promise_primitives[0]
    }

    /// The async primitive's identifier, allocated once per arena.
    /// Cost: one field read; no lookup or allocation.
    pub fn promise_async_lident(&self) -> LidentIdx {
        self.promise_primitives[1]
    }

    /// Intern a `Location` that comes from outside this arena (e.g. a label
    /// declaration read from a `.cmi`) while the arena is shared.
    /// `foreign_file_name` resolves file names that are not strings of this
    /// arena (the type context's `.cmi` name table); they are copied into the
    /// arena's typechecker string storage.
    pub fn push_typecheck_location(
        &self,
        loc: &crate::location::Location,
        foreign_file_name: &dyn Fn(StrIdx) -> Option<String>,
    ) -> LocIdx {
        if !self.store_locations {
            return if loc.origin.raw() != 0 {
                self.reimported_location_identities
                    .lock()
                    .expect("re-imported location identities lock")
                    .push(loc.origin.raw());
                LocIdx(loc.origin.raw() | if loc.loc_ghost { 0x4000_0000 } else { 0 })
            } else {
                self.fresh_location_identity(loc.loc_ghost)
            };
        }
        let push_pos = |pos: &Position| {
            // `Location::none()` is Rust's spelling of OCaml `Location.none`
            // (`in_file "_none_"`: line 1, bol 0, cnum -1).
            if pos.file_name == StrIdx::default() && pos.line == 0 {
                return self.none_pos();
            }
            let mut pos = *pos;
            if let Some(name) = foreign_file_name(pos.file_name) {
                pos.file_name = self.push_typecheck_string(name);
            }
            let slot = self.synthetic_positions.len();
            self.synthetic_positions.push(Box::new(pos));
            PosIdx::from_u32(SYNTHETIC_POSITION_BASE + slot as u32)
        };
        let start = push_pos(&loc.loc_start);
        let end = push_pos(&loc.loc_end);
        let slot = self.synthetic_locations.len();
        assert!(slot < 1 << 30, "synthetic location pool overflow");
        self.synthetic_locations
            .push(Box::new(InternedLocation::new(start, end, loc.loc_ghost)));
        LocIdx::from_u32(SYNTHETIC_LOCATION_BASE + slot as u32)
    }

    /// Append a typechecker-generated ghost copy of `idx` (OCaml
    /// `{loc with Location.loc_ghost = true}`) to storage reserved before the
    /// arena became shared. These indices live in a separate range, so scans
    /// over `locations()` do not see them.
    pub fn push_typecheck_ghost_loc(&self, idx: LocIdx) -> LocIdx {
        if !self.store_locations {
            return LocIdx(idx.0 | 0x4000_0000);
        }
        let loc = self.get_location(idx);
        let ghost = InternedLocation::new(loc.loc_start, loc.loc_end, true);
        let slot = self.synthetic_locations.len();
        assert!(slot < 1 << 30, "synthetic location pool overflow");
        self.synthetic_locations.push(Box::new(ghost));
        LocIdx::from_u32(SYNTHETIC_LOCATION_BASE + slot as u32)
    }

    /// OCaml `Location.in_file "command line"` (location.ml:24-26), where
    /// `Res_compmisc.open_implicit_module` locates `-open` modules: a ghost
    /// location without a printable range, so reports show only the name.
    pub fn push_typecheck_command_line_loc(&self) -> LocIdx {
        if !self.store_locations {
            return self.fresh_location_identity(true);
        }
        let pos = Position {
            file_name: self.push_shared_string("command line".to_string()),
            line: 1,
            bol: 0,
            cnum: -1,
        };
        let start_slot = self.synthetic_positions.len();
        self.synthetic_positions.push(Box::new(pos));
        let start = PosIdx::from_u32(SYNTHETIC_POSITION_BASE + start_slot as u32);
        let slot = self.synthetic_locations.len();
        assert!(slot < 1 << 30, "synthetic location pool overflow");
        self.synthetic_locations
            .push(Box::new(InternedLocation::new(start, start, true)));
        LocIdx::from_u32(SYNTHETIC_LOCATION_BASE + slot as u32)
    }

    /// A typechecker-generated ghost location from `start` to `end` (OCaml
    /// `{Location.loc_start; loc_end; loc_ghost = true}`), appended to the
    /// synthetic storage like `push_typecheck_ghost_loc`.
    pub fn push_typecheck_ghost_span(&self, start: PosIdx, end: PosIdx) -> LocIdx {
        if !self.store_locations {
            return self.fresh_location_identity(true);
        }
        let slot = self.synthetic_locations.len();
        assert!(slot < 1 << 30, "synthetic location pool overflow");
        self.synthetic_locations
            .push(Box::new(InternedLocation::new(start, end, true)));
        LocIdx::from_u32(SYNTHETIC_LOCATION_BASE + slot as u32)
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
        if !self.store_locations {
            self.skip_location_slot();
            return LocIdx(idx.0 | 0x4000_0000);
        }
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
            loc_start: *self.get_position(loc.loc_start),
            loc_end: *self.get_position(loc.loc_end),
            loc_ghost: loc.loc_ghost,
            origin: crate::location::LocationOrigin::new(if self.store_locations {
                0
            } else {
                idx.0 & 0x3fff_ffff
            }),
        }
    }

    /// Convert a full Location to a LocIdx by pushing its positions to the arena.
    /// Useful for migrating code that creates Location values.
    /// Creates fresh positions to match OCaml behavior.
    pub fn from_location(&mut self, loc: &Location) -> LocIdx {
        if !self.store_locations && loc.origin.raw() != 0 {
            self.skip_location_slot();
            return LocIdx(loc.origin.raw() | if loc.loc_ghost { 0x4000_0000 } else { 0 });
        }
        let start_idx = self.push_position(loc.loc_start);
        let end_idx = self.push_position(loc.loc_end);
        self.push_loc(start_idx, end_idx, loc.loc_ghost)
    }

    // ========================================================================
    // String interning
    // ========================================================================

    /// Record an attribute as it is parsed, without another AST traversal.
    pub fn observe_gentype_attribute(&mut self, name: StrIdx) {
        if !self.has_gentype_annotations {
            let name = self.get_string(name);
            self.has_gentype_annotations = name.starts_with("genType") || name.starts_with("gentype");
        }
        if !self.has_verify_annotations {
            self.has_verify_annotations = crate::verify::is_verify_attribute(self.get_string(name));
        }
    }

    /// Any parsed attribute that asks for a check of `crate::verify`
    /// (`@pure`, `@mutates`), wherever it is written.
    pub fn has_verify_annotations(&self) -> bool {
        self.has_verify_annotations
    }

    /// Any parsed genType-family attribute, including nested/file attributes.
    pub fn has_gentype_annotations(&self) -> bool {
        self.has_gentype_annotations
    }

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

    /// Fresh `Longident::Lident` for a synthesized AST node whose constructor
    /// is allocated dynamically by OCaml (for example `Lident var_name` in the
    /// let-unwrap rewrite). Static `Lident "Name"` values may instead be shared
    /// across calls and should use `push_lident_from_idx`.
    pub fn fresh_lident_from_idx(&mut self, str_idx: StrIdx) -> LidentIdx {
        self.longidents.push(Longident::Lident(str_idx))
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

    /// Render a longident as `A.b` / `F(X)` text (OCaml `Longident` printing).
    pub fn longident_to_string(&self, lid: &Longident) -> String {
        fn write(arena: &ParseArena, lid: &Longident, out: &mut String) {
            match lid {
                Longident::Lident(idx) => out.push_str(arena.get_string(*idx)),
                Longident::Ldot(prefix, idx) => {
                    write(arena, prefix, out);
                    out.push('.');
                    out.push_str(arena.get_string(*idx));
                }
                Longident::Lapply(f, a) => {
                    write(arena, f, out);
                    out.push('(');
                    write(arena, a, out);
                    out.push(')');
                }
            }
        }
        let mut out = String::new();
        write(self, lid, &mut out);
        out
    }

    /// Look up a longident by index.
    pub fn get_longident(&self, idx: LidentIdx) -> &Longident {
        let raw = idx.to_u32();
        if raw < self.synthetic_longident_base {
            self.longidents.get(idx)
        } else {
            self.synthetic_longidents
                .get((raw - self.synthetic_longident_base) as usize)
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

    /// Pre-interned empty string (OCaml static literal sharing).
    pub fn static_empty_str(&self) -> StrIdx {
        self.static_empty_str
    }

    /// Pre-interned `"x"` fallback binder name for let-unwrap desugaring.
    pub fn static_x_name(&self) -> StrIdx {
        self.static_x_name
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

    /// Return the shared `Js` module identifier.
    pub fn ppx_js_lident(&self) -> LidentIdx {
        self.static_ppx_lidents.js_lident
    }

    /// Return the shared `Js.typeof` path.
    pub fn ppx_js_typeof_lid(&self) -> LidentIdx {
        self.static_ppx_lidents.js_typeof
    }

    /// Return the shared `Js.undefinedToOption` path.
    pub fn ppx_js_undefined_to_option_lid(&self) -> LidentIdx {
        self.static_ppx_lidents.js_undefined_to_option
    }

    /// Return the shared `Js.Undefined` module path.
    pub fn ppx_js_undefined_lid(&self) -> LidentIdx {
        self.static_ppx_lidents.js_undefined
    }

    /// Return the shared `Js.Undefined.empty` path.
    pub fn ppx_js_undefined_empty_lid(&self) -> LidentIdx {
        self.static_ppx_lidents.js_undefined_empty
    }

    /// Return the shared `Primitive_js_extern` module path.
    pub fn ppx_js_oo_lident(&self) -> LidentIdx {
        self.static_ppx_lidents.js_oo_lident
    }

    /// Return the shared `Primitive_js_extern.Callback` type path.
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

    /// Return the cached primitive name for a raw JavaScript expression.
    pub fn prim_raw_expr(&self) -> StrIdx {
        self.prim_raw_expr
    }

    /// Return the cached primitive name for a raw JavaScript statement.
    pub fn prim_raw_stmt(&self) -> StrIdx {
        self.prim_raw_stmt
    }

    /// Return the shared equality operator spelling used by PPX rewrites.
    pub fn ppx_eq_str(&self) -> StrIdx {
        self.ppx_eq_str
    }

    /// Return the shared `Js` module spelling used by PPX rewrites.
    pub fn ppx_js_str(&self) -> StrIdx {
        self.ppx_js_str
    }

    /// Return the shared empty string used by PPX rewrites.
    pub fn ppx_empty_str(&self) -> StrIdx {
        self.ppx_empty_str
    }

    /// Return the shared `undefined` spelling used by PPX rewrites.
    pub fn ppx_undefined_str(&self) -> StrIdx {
        self.ppx_undefined_str
    }

    /// Return the shared concatenation operator spelling for templates.
    pub fn template_concat_str(&self) -> StrIdx {
        self.template_concat_str
    }

    /// Get the string content for a StrIdx.
    #[inline]
    pub fn get_string(&self, idx: StrIdx) -> &str {
        let raw = idx.raw();
        if raw >= SHARED_STRING_BASE {
            self.shared_strings
                .get((raw - SHARED_STRING_BASE) as usize)
                .expect("shared string read before it was pushed")
        } else if raw < self.synthetic_string_base {
            self.strings.get(idx)
        } else {
            self.synthetic_strings
                .get((raw - self.synthetic_string_base) as usize)
                .expect("typechecker synthetic string read before initialization")
        }
    }

    /// The name of `idx` when it is a file this arena's positions are in
    /// (its source file included, with or without stored locations).
    pub fn own_file_name(&self, idx: StrIdx) -> Option<&str> {
        self.position_file_names
            .contains(&idx)
            .then(|| self.get_string(idx))
    }

    /// The interned name of string `idx`, computed once per parsed string.
    #[inline]
    pub fn name(&self, idx: StrIdx) -> crate::name::Name {
        let names = self.string_names.get_or_init(|| {
            (0..self.strings.len())
                .map(|_| std::sync::OnceLock::new())
                .collect()
        });
        match names.get(idx.raw() as usize) {
            Some(slot) => *slot.get_or_init(|| crate::name::Name::new(self.get_string(idx))),
            None => crate::name::Name::new(self.get_string(idx)),
        }
    }

    /// File names referenced by source positions in this arena.
    pub fn source_file_names(&self) -> std::collections::HashMap<StrIdx, String> {
        self.position_file_names
            .iter()
            .map(|idx| (*idx, self.get_string(*idx).to_string()))
            .collect()
    }

    /// Number of strings currently stored in the arena string table.
    pub fn string_count(&self) -> usize {
        self.strings.len()
    }

    /// Copy of the interned (non-synthetic) strings, by index.
    pub fn snapshot_strings(&self) -> crate::intern::InternedStrings {
        self.strings.snapshot()
    }

    /// Prepare append-only AST storage used by typecore synthetic rewrites.
    ///
    /// Typechecking creates a few parsed AST fragments to mirror OCaml rewrites
    /// such as optional-default lowering and variant-spread expansion. This must
    /// happen before the arena is handed to `TypeCheckContext` for the primary
    /// AST and identifier arenas. Environment-dependent patterns, longidents,
    /// and strings use stable append-only storage and can grow during checking.
    /// Sparse side tables are keyed by `ExprIdx` and are only appended alongside
    /// synthetic expressions, so they do not need an unconditional reserve.
    pub fn reserve_typecheck_synthetic_capacity(&mut self) {
        self.expressions.reserve(64);
        self.patterns.reserve(64);
        self.longidents.reserve(128);
        self.strings.reserve(128);

        self.synthetic_pattern_base = self.patterns.len() as u32;
        self.synthetic_patterns = SyntheticVec::default();
        self.synthetic_longident_base = self.longidents.len() as u32;
        self.synthetic_longidents = SyntheticVec::default();
        self.synthetic_string_base = self.strings.len() as u32;
        self.synthetic_strings = elsa::sync::FrozenVec::new();
    }

    /// Append a typechecker-generated longident to storage reserved before the
    /// arena became shared.
    pub fn push_typecheck_longident(&self, longident: Longident) -> LidentIdx {
        let slot = self.synthetic_longidents.push(longident);
        LidentIdx::from_u32(self.synthetic_longident_base + slot as u32)
    }

    /// Append a string through a shared arena, at any stage. Such strings are
    /// not interned and are never marshalled.
    pub fn push_shared_string(&self, string: String) -> StrIdx {
        let slot = self.shared_strings.len();
        self.shared_strings.push(string.into_boxed_str());
        StrIdx::from_raw(SHARED_STRING_BASE + slot as u32)
    }

    /// Append a typechecker-generated string to storage reserved before the
    /// arena became shared.
    pub fn push_typecheck_string(&self, string: String) -> StrIdx {
        assert!(
            self.synthetic_string_base != u32::MAX,
            "typechecker string pushed before reserve_typecheck_synthetic_capacity"
        );
        let slot = self.synthetic_strings.len();
        self.synthetic_strings.push(string);
        StrIdx::from_raw(self.synthetic_string_base + slot as u32)
    }

    /// Append a typechecker-generated simple identifier, allocating its string
    /// in the matching reserved storage.
    pub fn push_typecheck_lident(&self, name: impl Into<String>) -> LidentIdx {
        let name = self.push_typecheck_string(name.into());
        self.push_typecheck_longident(Longident::Lident(name))
    }

    /// Append a typechecker-generated pattern to storage reserved before the
    /// arena became shared. This is a safe, append-only equivalent of OCaml's
    /// allocation during pattern rewrites.
    pub fn push_typecheck_pattern(&self, pattern: Pattern) -> PatIdx {
        let slot = self.synthetic_patterns.push(pattern);
        PatIdx::from_u32(self.synthetic_pattern_base + slot as u32)
    }

    /// Canonical spelling handle without copying an existing occurrence.
    /// Cost: O(name bytes), amortized O(1) interner insertion.
    pub fn intern_existing_string(&mut self, idx: StrIdx) -> StrIdx {
        self.strings.intern_existing(idx)
    }

    /// Look up a canonical spelling. Cost: O(name bytes), no allocation.
    pub fn find_interned_string(&self, name: &str) -> Option<StrIdx> {
        self.strings.find_interned(name)
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
    /// Intern a string literal's spellings. A literal whose source spelling is
    /// its semantic value stores one string.
    pub fn push_string_literal(&mut self, literal: &StringLiteral) -> StringConst {
        match literal {
            StringLiteral::Valid { source, semantic } => {
                let source_idx = self.intern_string(source);
                let semantic_idx = if source == semantic {
                    source_idx
                } else {
                    self.intern_string(semantic)
                };
                StringConst::Valid {
                    source: source_idx,
                    semantic: semantic_idx,
                }
            }
            StringLiteral::InvalidSource(source) => {
                StringConst::InvalidSource(self.intern_string(source))
            }
        }
    }

    /// `push_string_literal` for nodes the type checker synthesizes.
    pub fn push_typecheck_string_literal(&self, literal: &StringLiteral) -> StringConst {
        match literal {
            StringLiteral::Valid { source, semantic } => {
                let source_idx = self.push_typecheck_string(source.to_string());
                let semantic_idx = if source == semantic {
                    source_idx
                } else {
                    self.push_typecheck_string(semantic.to_string())
                };
                StringConst::Valid {
                    source: source_idx,
                    semantic: semantic_idx,
                }
            }
            StringLiteral::InvalidSource(source) => {
                StringConst::InvalidSource(self.push_typecheck_string(source.to_string()))
            }
        }
    }

    /// OCaml `Ast_helper.Const.string`.
    pub fn string_constant(&mut self, semantic: &str) -> Constant {
        Constant::String(
            self.push_string_literal(&crate::string_literal::string_from_semantic(semantic)),
        )
    }

    /// OCaml `Ast_helper.Const.char`.
    pub fn char_constant(&mut self, semantic: i32) -> Constant {
        let source = self.intern_string(&crate::string_literal::encode_char_source(semantic));
        Constant::Char { source, semantic }
    }

    /// `push_string_literal` through a shared arena
    /// ([`Self::push_shared_string`]), for nodes printers rebuild.
    pub fn push_shared_string_literal(&self, literal: &StringLiteral) -> StringConst {
        match literal {
            StringLiteral::Valid { source, semantic } => {
                let source_idx = self.push_shared_string(source.to_string());
                let semantic_idx = if source == semantic {
                    source_idx
                } else {
                    self.push_shared_string(semantic.to_string())
                };
                StringConst::Valid {
                    source: source_idx,
                    semantic: semantic_idx,
                }
            }
            StringLiteral::InvalidSource(source) => {
                StringConst::InvalidSource(self.push_shared_string(source.to_string()))
            }
        }
    }

    /// `string_constant` for nodes the type checker synthesizes.
    pub fn typecheck_string_constant(&self, semantic: &str) -> Constant {
        Constant::String(
            self.push_typecheck_string_literal(&crate::string_literal::string_from_semantic(
                semantic,
            )),
        )
    }

    /// `char_constant` for nodes the type checker synthesizes.
    pub fn typecheck_char_constant(&self, semantic: i32) -> Constant {
        let source =
            self.push_typecheck_string(crate::string_literal::encode_char_source(semantic));
        Constant::Char { source, semantic }
    }

    /// Intern a string, reusing the index of an equal existing spelling.
    pub fn intern_string(&mut self, s: &str) -> StrIdx {
        self.strings.intern(s)
    }

    /// Push a string without deduplication (for dynamic user-input strings).
    pub fn push_string(&mut self, s: impl AsRef<str>) -> StrIdx {
        self.strings.push_interned(s.as_ref())
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

    /// The bit of `loc` in `rewritten_expr_locs`: two per location index,
    /// for the location and its ghost (bit 30 of a `LocIdx`). `None` for a
    /// synthetic location of the type checker, which the mapper never sees.
    #[inline]
    fn rewritten_expr_loc_bit(loc: LocIdx) -> Option<usize> {
        (loc.0 < SYNTHETIC_LOCATION_BASE)
            .then(|| (loc.0 & 0x3FFF_FFFF) as usize * 2 + (loc.0 >> 30) as usize)
    }

    /// Mark an expression location as visited by the built-in mapper.
    ///
    /// Cost: one bit set; the bit vector grows to the location's word.
    #[inline]
    pub fn mark_rewritten_expr_loc(&mut self, loc: LocIdx) {
        let Some(bit) = Self::rewritten_expr_loc_bit(loc) else {
            return;
        };
        if bit / 64 >= self.rewritten_expr_locs.len() {
            self.rewritten_expr_locs.resize(bit / 64 + 1, 0);
        }
        self.rewritten_expr_locs[bit / 64] |= 1 << (bit % 64);
    }

    /// Returns true when the built-in mapper visited an expression at this
    /// location.
    ///
    /// Cost: one bit test.
    pub fn is_rewritten_expr_loc(&self, loc: LocIdx) -> bool {
        Self::rewritten_expr_loc_bit(loc).is_some_and(|bit| {
            self.rewritten_expr_locs
                .get(bit / 64)
                .is_some_and(|word| word & (1 << (bit % 64)) != 0)
        })
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
            Longident::Lident(str_idx) => self.get_string(*str_idx) == name,
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
        self.get_string(str_idx)
    }

    /// Convert a `Located<LidentIdx>` to `Located<Longident>`.
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
            pexp_desc: ExpressionDesc::Pexp_ident(Self::placeholder_lident_loc()),
            pexp_loc: LocIdx::default(),
            pexp_attributes: Attributes::new(),
        }
    }

    fn placeholder_pat() -> Pattern {
        Pattern {
            ppat_desc: PatternDesc::Ppat_any,
            ppat_loc: LocIdx::default(),
            ppat_attributes: Attributes::new(),
        }
    }

    fn placeholder_core_type() -> CoreType {
        CoreType {
            ptyp_desc: CoreTypeDesc::Ptyp_any,
            ptyp_loc: LocIdx::default(),
            ptyp_attributes: Attributes::new(),
        }
    }

    fn placeholder_mod_expr() -> ModuleExpr {
        ModuleExpr {
            pmod_desc: ModuleExprDesc::Pmod_ident(Self::placeholder_lident_loc()),
            pmod_loc: LocIdx::default(),
            pmod_attributes: Attributes::new(),
        }
    }

    fn placeholder_mod_type() -> ModuleType {
        ModuleType {
            pmty_desc: ModuleTypeDesc::Pmty_ident(Self::placeholder_lident_loc()),
            pmty_loc: LocIdx::default(),
            pmty_attributes: Attributes::new(),
        }
    }

    /// Push an expression into the arena and return its index.
    /// Use this instead of `Box::new(expr)` for recursive AST references.
    #[inline]
    pub fn push_expr(&mut self, expr: Expression) -> ExprIdx {
        let certificates = self.expression_certificates(&expr);
        let idx = self.expressions.push(expr);
        if certificates != 0 {
            let word = idx.0 as usize / 16;
            if word >= self.rewrite_free_exprs.len() {
                self.rewrite_free_exprs.resize(word + 1, 0);
            }
            self.rewrite_free_exprs[word] |= certificates << (4 * (idx.0 % 16));
        }
        idx
    }

    /// Both proofs are computed together, inspecting only immediate children.
    /// Bit 0 excludes attributes, pipes, types, patterns and module scopes;
    /// bit 1 additionally excludes unsuffixed integers (overflow warnings).
    fn expression_certificates(&self, expr: &Expression) -> u64 {
        if !expr.pexp_attributes.is_empty() {
            return 0;
        }
        let free = |idx| self.expr_certificates(idx);
        let all = |items: &[ExprIdx]| items.iter().fold(3, |bits, idx| bits & free(*idx));
        match &expr.pexp_desc {
            ExpressionDesc::Pexp_ident(_)
            | ExpressionDesc::Pexp_break
            | ExpressionDesc::Pexp_continue => 3,
            ExpressionDesc::Pexp_constant(c) if c.integer_digits().is_some() => 1,
            ExpressionDesc::Pexp_constant(_) => 3,
            ExpressionDesc::Pexp_apply(apply) => {
                let is_pipe = matches!(&self.get_expr(apply.funct).pexp_desc,
                    ExpressionDesc::Pexp_ident(lid) if matches!(self.get_longident(lid.txt),
                        Longident::Lident(name) if self.get_string(*name) == "->"));
                if is_pipe {
                    return 0;
                }
                self.apply_args(apply.args)
                    .iter()
                    .fold(free(apply.funct), |bits, (_, idx)| bits & free(*idx))
            }
            ExpressionDesc::Pexp_tuple(items) | ExpressionDesc::Pexp_array(items) => {
                all(self.expr_list(*items))
            }
            ExpressionDesc::Pexp_construct(_, args) => all(self.expr_list(args.txt)),
            ExpressionDesc::Pexp_variant(inner) => all(self.expr_list(inner.1.txt)),
            ExpressionDesc::Pexp_field(child, _) | ExpressionDesc::Pexp_assert(child) => {
                free(*child)
            }
            ExpressionDesc::Pexp_sequence(left, right)
            | ExpressionDesc::Pexp_while(left, right) => free(*left) & free(*right),
            ExpressionDesc::Pexp_ternary(inner) => free(inner.0) & free(inner.1) & free(inner.2),
            ExpressionDesc::Pexp_ifthenelse(inner) => {
                free(inner.0) & free(inner.1) & inner.2.map_or(3, free)
            }
            ExpressionDesc::Pexp_record((fields, spread)) => self
                .expr_field_list(*fields)
                .iter()
                .fold(spread.map_or(3, free), |bits, field| {
                    bits & free(field.expr)
                }),
            // Functions, braces (@this forwarding), awaits, raw nodes, JSX,
            // extensions and bindings remain on the full traversal paths.
            _ => 0,
        }
    }

    #[inline]
    fn expr_certificates(&self, idx: ExprIdx) -> u64 {
        self.rewrite_free_exprs
            .get(idx.0 as usize / 16)
            .map_or(0, |word| (word >> (4 * (idx.0 % 16))) & 3)
    }

    /// Record `expanded` as what the compiler reads in place of `original`.
    /// The node at `original` and every ancestor of it stay as parsed;
    /// `expanded` is a node appended after it. Recording a second expansion
    /// for the same node replaces the first.
    ///
    /// Cost: one bit set and one store; the first expansion in a page of
    /// `EXPANSION_PAGE` expressions also appends that page (256 bytes).
    pub fn set_expansion(&mut self, original: ExprIdx, expanded: ExprIdx) {
        debug_assert_ne!(original, expanded, "an expansion must be a new node");
        debug_assert_eq!(self.expr_certificates(original), 0, "a certified node has no rewrite");
        debug_assert!(original.0 < SHARED_EXPRESSION_BASE);
        let slot = original.0 as usize;
        let word = slot / 16;
        if word >= self.rewrite_free_exprs.len() {
            self.rewrite_free_exprs.resize(word + 1, 0);
        }
        self.rewrite_free_exprs[word] |= EXPANSION_BIT << (4 * (slot % 16));
        let page = slot / EXPANSION_PAGE;
        if page >= self.expansion_pages.len() {
            self.expansion_pages.resize(page + 1, 0);
        }
        if self.expansion_pages[page] == 0 {
            let len = self.expansion_targets.len();
            self.expansion_targets.resize(len + EXPANSION_PAGE, original);
            self.expansion_pages[page] = (len / EXPANSION_PAGE) as u32 + 1;
        }
        let base = (self.expansion_pages[page] as usize - 1) * EXPANSION_PAGE;
        self.expansion_targets[base + slot % EXPANSION_PAGE] = expanded;
    }

    /// The node the compiler reads for `idx`: its expansion when a built-in
    /// rewrite recorded one, otherwise `idx` itself. Readers of the tree as
    /// compiled (the checker, dependency collection, the unused-attribute
    /// sweep, the v0 mapper) call this where they turn a handle into a node;
    /// readers of the tree as written (the printer, `check::Checker`) do not.
    ///
    /// Cost: one bit test for a node without an expansion (a load, a shift
    /// and a branch); two more indexed loads for a node with one. No hashing.
    #[inline]
    pub fn expanded(&self, idx: ExprIdx) -> ExprIdx {
        let slot = idx.0 as usize;
        match self.rewrite_free_exprs.get(slot / 16) {
            Some(word) if word & (EXPANSION_BIT << (4 * (slot % 16))) != 0 => {
                let base = (self.expansion_pages[slot / EXPANSION_PAGE] as usize - 1) * EXPANSION_PAGE;
                self.expansion_targets[base + slot % EXPANSION_PAGE]
            }
            _ => idx,
        }
    }

    /// No builtin rewrite, Checker diagnostic, or nested external can occur.
    #[inline]
    pub fn expr_needs_no_rewrite(&self, idx: ExprIdx) -> bool {
        self.expr_certificates(idx) & 1 != 0
    }

    /// No unused-attribute sweep diagnostic can occur in this subtree.
    #[inline]
    pub fn expr_needs_no_attribute_sweep(&self, idx: ExprIdx) -> bool {
        self.expr_certificates(idx) & 2 != 0
    }

    /// Parents are allocated after children. A mutation invalidates both
    /// proofs for the node and all possible parents, without a reverse-edge
    /// table or tree walk. Reserved slots are never certified.
    ///
    /// Cost: the words after `idx`'s, which keep only their expansion bits.
    /// Nothing on a compile path mutates an expression after the built-in
    /// rewrites have recorded an expansion.
    fn invalidate_rewrite_free_exprs(&mut self, idx: ExprIdx) {
        let word = idx.0 as usize / 16;
        if word < self.rewrite_free_exprs.len() {
            // The proofs go; the expansions stay: their nodes still exist.
            const EXPANSION_BITS: u64 = 0x4444_4444_4444_4444;
            self.rewrite_free_exprs[word] &=
                ((1u64 << (4 * (idx.0 % 16))) - 1) | EXPANSION_BITS;
            for bits in &mut self.rewrite_free_exprs[word + 1..] {
                *bits &= EXPANSION_BITS;
            }
        }
    }
    /// Reserve an expression index using a placeholder node.
    ///
    /// This is the first step of two-phase construction (`reserve -> initialize`),
    /// used when sparse side data must be keyed by stable `ExprIdx`.
    #[inline]
    pub fn reserve_expr(&mut self) -> ExprIdx {
        self.expressions.reserve_with(Self::placeholder_expr())
    }

    /// Initialize a previously reserved expression slot.
    #[inline]
    pub fn initialize_expr(&mut self, idx: ExprIdx, expr: Expression) {
        self.invalidate_rewrite_free_exprs(idx);
        if !self.expr_overrides.is_empty() {
            self.expr_overrides.remove(&idx.0);
        }
        self.expressions.initialize(idx, expr);
    }

    /// Get an expression by index.
    /// Store an application's argument list.
    #[inline]
    pub fn push_apply_args(&mut self, args: &[(ArgLabel, ExprIdx)]) -> ApplyArgs {
        self.apply_args.push(args)
    }

    /// Store an expression index list.
    pub fn push_expr_list(&mut self, items: &[ExprIdx]) -> ExprList {
        self.expr_lists.push(items)
    }

    /// `push_expr_list` for nodes the type checker synthesizes.
    pub fn push_shared_expr_list(&self, items: &[ExprIdx]) -> ExprList {
        self.expr_lists.push_shared(items)
    }

    /// Borrow the expression indices stored in a list handle.
    pub fn expr_list(&self, list: ExprList) -> &[ExprIdx] {
        self.expr_lists.get(list)
    }

    /// Constructor arguments of a `Pexp_construct`: the argument list and the
    /// span of its parentheses.
    pub fn expr_ctor_args(&mut self, items: &[ExprIdx], loc: LocIdx) -> Located<ExprList> {
        Located::new(self.push_expr_list(items), loc)
    }

    /// Constructor arguments of a `Ppat_construct`.
    pub fn pat_ctor_args(&mut self, items: &[PatIdx], loc: LocIdx) -> Located<PatList> {
        Located::new(self.push_pat_list(items), loc)
    }

    /// `pat_ctor_args` for patterns the type checker synthesizes.
    pub fn shared_pat_ctor_args(&self, items: &[PatIdx], loc: LocIdx) -> Located<PatList> {
        Located::new(self.push_shared_pat_list(items), loc)
    }

    /// Store a pattern index list.
    pub fn push_pat_list(&mut self, items: &[PatIdx]) -> PatList {
        self.pat_lists.push(items)
    }

    /// `push_pat_list` for nodes the type checker synthesizes.
    pub fn push_shared_pat_list(&self, items: &[PatIdx]) -> PatList {
        self.pat_lists.push_shared(items)
    }

    /// Borrow the pattern indices stored in a list handle.
    pub fn pat_list(&self, list: PatList) -> &[PatIdx] {
        self.pat_lists.get(list)
    }

    /// Store a core type index list.
    pub fn push_type_list(&mut self, items: &[CoreTypeIdx]) -> TypeList {
        self.type_lists.push(items)
    }

    /// `push_type_list` for nodes the type checker synthesizes.
    pub fn push_shared_type_list(&self, items: &[CoreTypeIdx]) -> TypeList {
        self.type_lists.push_shared(items)
    }

    /// Borrow the core-type indices stored in a list handle.
    pub fn type_list(&self, list: TypeList) -> &[CoreTypeIdx] {
        self.type_lists.get(list)
    }

    /// Mark a structure value group produced by a derive.
    /// Cost: one bitmap write plus O(new words) zero initialization on growth.
    /// Across all marks, at most ceil(highest binding slot / 64) words are
    /// initialized; remarking a group never grows or scans the table.
    pub(crate) fn mark_derived_value_group(&mut self, list: VbList) {
        assert!(!list.is_empty());
        let index = list.start() as usize;
        self.derived_value_groups.resize(
            self.derived_value_groups.len().max(index / 64 + 1), 0,
        );
        self.derived_value_groups[index / 64] |= 1 << (index % 64);
    }

    /// The plan pools of derived items. Cost: O(1).
    #[inline]
    pub fn plans(&self) -> &crate::binary_ast::derive::plan::Plans {
        &self.plans
    }

    /// The plan pools, for the seam that builds plans. Cost: O(1).
    #[inline]
    pub(crate) fn plans_mut(&mut self) -> &mut crate::binary_ast::derive::plan::Plans {
        &mut self.plans
    }

    /// Provenance of a structure value group, independent of names and locations.
    /// Cost: O(1), at most one word read, with no allocation or synchronization.
    pub fn is_derived_value_group(&self, list: VbList) -> bool {
        let index = list.start() as usize;
        !list.is_empty() && self.derived_value_groups.get(index / 64)
            .is_some_and(|word| word & (1 << (index % 64)) != 0)
    }

    /// Store the value bindings of a `let`.
    pub fn push_vb_list(&mut self, items: &[ValueBinding]) -> VbList {
        self.vb_lists.push(items)
    }

    /// `push_vb_list` for nodes the type checker synthesizes.
    pub fn push_shared_vb_list(&self, items: &[ValueBinding]) -> VbList {
        self.vb_lists.push_shared(items)
    }

    /// Borrow the value bindings stored in a list handle.
    pub fn vb_list(&self, list: VbList) -> &[ValueBinding] {
        self.vb_lists.get(list)
    }

    /// Store the fields of a record expression.
    pub fn push_expr_field_list(&mut self, items: &[ExpressionRecordField]) -> ExprFieldList {
        self.expr_field_lists.push(items)
    }

    /// `push_expr_field_list` for nodes the type checker synthesizes.
    pub fn push_shared_expr_field_list(&self, items: &[ExpressionRecordField]) -> ExprFieldList {
        self.expr_field_lists.push_shared(items)
    }

    /// Borrow the record-expression fields stored in a list handle.
    pub fn expr_field_list(&self, list: ExprFieldList) -> &[ExpressionRecordField] {
        self.expr_field_lists.get(list)
    }

    /// Store the fields of a record pattern.
    pub fn push_pat_field_list(&mut self, items: &[PatternRecordField]) -> PatFieldList {
        self.pat_field_lists.push(items)
    }

    /// `push_pat_field_list` for nodes the type checker synthesizes.
    pub fn push_shared_pat_field_list(&self, items: &[PatternRecordField]) -> PatFieldList {
        self.pat_field_lists.push_shared(items)
    }

    /// Borrow the record-pattern fields stored in a list handle.
    pub fn pat_field_list(&self, list: PatFieldList) -> &[PatternRecordField] {
        self.pat_field_lists.get(list)
    }

    /// Store the cases of a `switch` or `try`.
    pub fn push_case_list(&mut self, items: &[Case]) -> CaseList {
        self.case_lists.push(items)
    }

    /// `push_case_list` for nodes the type checker synthesizes.
    pub fn push_shared_case_list(&self, items: &[Case]) -> CaseList {
        self.case_lists.push_shared(items)
    }

    /// Borrow the match cases stored in a list handle.
    pub fn case_list(&self, list: CaseList) -> &[Case] {
        self.case_lists.get(list)
    }

    /// Store the elements of a literal with spreads.
    pub fn push_spread_element_list(
        &mut self,
        items: &[crate::parser::ast::SpreadElement],
    ) -> SpreadElementList {
        self.spread_element_lists.push(items)
    }

    /// `push_spread_element_list` for nodes the type checker synthesizes.
    pub fn push_shared_spread_element_list(
        &self,
        items: &[crate::parser::ast::SpreadElement],
    ) -> SpreadElementList {
        self.spread_element_lists.push_shared(items)
    }

    /// The elements of a spread list.
    pub fn spread_element_list(
        &self,
        list: SpreadElementList,
    ) -> &[crate::parser::ast::SpreadElement] {
        self.spread_element_lists.get(list)
    }

    /// The arguments of a `Pexp_apply`, in source order.
    pub fn apply_args(&self, args: ApplyArgs) -> &[(ArgLabel, ExprIdx)] {
        self.apply_args.get(args)
    }

    /// Resolve an expression index from ordinary or shared synthetic storage.
    pub fn get_expr(&self, idx: ExprIdx) -> &Expression {
        let raw = idx.0;
        if raw < SHARED_EXPRESSION_BASE {
            self.expressions.get(idx)
        } else {
            self.shared_expressions
                .get((raw - SHARED_EXPRESSION_BASE) as usize)
                .expect("shared expression read before it was pushed")
        }
    }

    /// Read the built-in expansion at a compiler consumer's handle boundary.
    #[inline]
    pub fn get_expanded_expr(&self, idx: ExprIdx) -> &Expression {
        self.get_expr(self.expanded(idx))
    }

    /// Append an expression while the arena is shared. Such expressions have
    /// no sparse side-table entries, so they must not carry function
    /// defaults, case guards or other side-table payloads.
    pub fn push_shared_expr(&self, expr: Expression) -> ExprIdx {
        let slot = self.shared_expressions.len();
        self.shared_expressions.push(Box::new(expr));
        ExprIdx(SHARED_EXPRESSION_BASE + slot as u32)
    }

    /// `Lident` of `true`, `false`, `null` or `undefined`.
    pub fn runtime_tag_lident(&self, name: &str) -> LidentIdx {
        let index = match name {
            "true" => 0,
            "false" => 1,
            "null" => 2,
            "undefined" => 3,
            _ => unreachable!("runtime_tag_lident: {name}"),
        };
        self.runtime_tag_lidents[index]
    }

    /// The interned attribute name `as`.
    /// The name of the attribute spelling a JSX component annotation.
    pub fn jsx_component_attribute_name(
        &self,
        kind: &crate::parser::ast::JsxComponentKind,
        namespace: crate::parser::ast::JsxComponentNamespace,
    ) -> StrIdx {
        use crate::parser::ast::{JsxComponentKind, JsxComponentNamespace};
        let index = match (namespace, kind) {
            (JsxComponentNamespace::React, JsxComponentKind::Labelled(_)) => 0,
            (JsxComponentNamespace::React, JsxComponentKind::WithProps) => 1,
            (JsxComponentNamespace::Jsx, JsxComponentKind::Labelled(_)) => 2,
            (JsxComponentNamespace::Jsx, JsxComponentKind::WithProps) => 3,
        };
        self.jsx_component_attribute_names[index]
    }

    /// The interned attribute name `as`.
    pub fn as_attribute_name(&self) -> StrIdx {
        self.as_attribute_name
    }

    /// Get a mutable expression by index.
    #[inline]
    pub fn get_expr_mut(&mut self, idx: ExprIdx) -> &mut Expression {
        self.invalidate_rewrite_free_exprs(idx);
        // The caller may rewrite the payload fields; overrides no longer apply.
        if !self.expr_overrides.is_empty() {
            self.expr_overrides.remove(&idx.0);
        }
        self.expressions.get_mut(idx)
    }

    /// Store the authoritative n-ary argument list for a parser-created arrow.
    pub fn set_nary_arrow_args(
        &mut self,
        _arity: ArityIdx,
        args: Vec<crate::parser::ast::TypeArg>,
    ) {
        let first_type = args.first().expect("Ptyp_arrow has arguments").typ;
        let list = self.nary_arrow_arg_lists.push(&args);
        self.nary_arrow_args_by_first_type.insert(first_type, list);
    }

    /// Remove the n-ary parameters recorded under `first_type`, so a caller
    /// can rewrite them while also mutating the arena; put them back with
    /// [`Self::restore_nary_arrow_args`].
    pub fn take_nary_arrow_args(
        &mut self,
        first_type: CoreTypeIdx,
    ) -> Option<Vec<crate::parser::ast::TypeArg>> {
        let list = self.nary_arrow_args_by_first_type.remove(&first_type)?;
        Some(self.nary_arrow_arg_lists.get(list).to_vec())
    }

    /// Put back parameters removed by [`Self::take_nary_arrow_args`].
    pub fn restore_nary_arrow_args(
        &mut self,
        first_type: CoreTypeIdx,
        args: Vec<crate::parser::ast::TypeArg>,
    ) {
        let list = self.nary_arrow_arg_lists.push(&args);
        self.nary_arrow_args_by_first_type.insert(first_type, list);
    }

    /// The n-ary parameters recorded for an arrow whose first parameter is
    /// `arg`, when the parser grouped more than one.
    pub fn nary_arrow_args_slice(
        &self,
        arg: &crate::parser::ast::TypeArg,
    ) -> Option<&[crate::parser::ast::TypeArg]> {
        self.nary_arrow_args_by_first_type
            .get(&arg.typ)
            .map(|args| self.nary_arrow_arg_lists.get(*args))
    }

    /// Borrow recorded n-ary arrow arguments, or return the single-argument fallback.
    pub fn nary_arrow_args<'a>(
        &'a self,
        arg: &'a crate::parser::ast::TypeArg,
        arity: ArityIdx,
    ) -> std::borrow::Cow<'a, [crate::parser::ast::TypeArg]> {
        let _ = arity;
        if let Some(args) = self.nary_arrow_args_by_first_type.get(&arg.typ) {
            std::borrow::Cow::Borrowed(self.nary_arrow_arg_lists.get(*args))
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
            .filter_map(|expr| match &expr.pexp_desc {
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
        let list = self.nary_fun_param_lists.push(&params);
        self.nary_fun_params_by_first_pattern
            .insert(first_pattern, list);
        self.nary_fun_unknown_arity_by_first_pattern
            .insert(first_pattern, unknown_arity);
        let _ = arity;
    }

    /// Find the unknown-arity marker associated with a function parameter group.
    pub fn nary_fun_unknown_arity(&self, fun: &crate::parser::ast::PexpFun) -> ArityIdx {
        if self.get_arity(fun.arity).is_some() {
            self.nary_fun_unknown_arity_by_first_pattern
                .get(&fun.lhs)
                .copied()
                .or_else(|| match &self.get_expr(fun.rhs).pexp_desc {
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
    ) {
        let names = constraint
            .pvc_newtypes
            .iter()
            .map(|name| self.get_string(name.txt).to_string())
            .collect::<std::collections::HashSet<_>>();
        let source = self.get_core_type(constraint.pvc_type).clone();
        let body = match crate::parser::typ::substitute_type_vars(self, source, &names) {
            Ok(body) => body,
            Err(error_loc) => {
                // Keep the wire constraint; typing raises the error later.
                self.value_constraint_varify_errors
                    .insert(pattern, error_loc);
                self.value_constraints_by_pattern
                    .insert(pattern, constraint);
                return;
            }
        };
        self.value_constraint_varify_errors.remove(&pattern);
        let body = self.push_core_type(body);
        let poly = self.push_core_type(CoreType {
            ptyp_desc: CoreTypeDesc::Ptyp_poly(Box::new((constraint.pvc_newtypes.clone(), body))),
            ptyp_loc: loc,
            ptyp_attributes: Attributes::new(),
        });
        constraint.pvc_pattern = Some(self.push_pat(Pattern {
            ppat_desc: PatternDesc::Ppat_constraint(Box::new((pattern, poly))),
            ppat_loc: loc,
            ppat_attributes: Attributes::new(),
        }));
        let mut wrapped = self.push_expr(Expression {
            pexp_desc: ExpressionDesc::Pexp_constraint(Box::new((expression, constraint.pvc_type))),
            pexp_loc: loc,
            pexp_attributes: Attributes::new(),
        });
        for name in constraint.pvc_newtypes.iter().rev() {
            wrapped = self.push_expr(Expression {
                pexp_desc: ExpressionDesc::Pexp_newtype(Box::new((*name, wrapped))),
                pexp_loc: loc,
                pexp_attributes: Attributes::new(),
            });
        }
        constraint.pvc_expression = Some(wrapped);
        self.value_constraints_by_pattern
            .insert(pattern, constraint);
    }

    /// Enable or disable the builtin spice mapper for this compilation.
    pub fn set_builtin_spice(&mut self, enabled: bool) {
        self.builtin_spice_disabled = !enabled;
    }

    /// Let the derive seam plan items (`None`), or keep every item on the
    /// general path for `off`. Cost: O(1).
    pub fn set_derived_plans(&mut self, off: Option<crate::binary_ast::derive::GeneralReason>) {
        self.derived_plans_off = off;
    }

    /// Why the derive seam plans no item, or `None` when it plans.
    /// Cost: O(1).
    #[inline]
    pub fn derived_plans_off(&self) -> Option<crate::binary_ast::derive::GeneralReason> {
        self.derived_plans_off
    }

    /// Whether built-in Spice deriving is enabled for this parse.
    pub fn builtin_spice_enabled(&self) -> bool {
        !self.builtin_spice_disabled
    }

    /// Set the LetUnwrap experimental feature for the builtin PPX.
    pub fn set_experimental_let_unwrap(&mut self, enabled: bool) {
        self.experimental_let_unwrap = enabled;
    }

    /// Whether the LetUnwrap experimental feature is on for the builtin PPX.
    pub fn experimental_let_unwrap(&self) -> bool {
        self.experimental_let_unwrap
    }

    /// Record a nested builtin-ppx error unless an earlier one is pending.
    pub fn defer_ppx_error(&mut self, error: crate::binary_ast::ppx::PpxError) {
        if self.ppx_deferred_error.is_none() {
            self.ppx_deferred_error = Some(error);
        }
    }

    /// Take the first deferred builtin-ppx error.
    pub fn take_ppx_deferred_error(&mut self) -> Option<crate::binary_ast::ppx::PpxError> {
        self.ppx_deferred_error.take()
    }

    /// Whether `Ast_helper.Typ.varify_constructors` fails for this binding's
    /// constraint (compiler/ml/ast_helper.ml:74-78).
    pub fn value_constraint_varify_error(&self, pattern: PatIdx) -> Option<LocIdx> {
        self.value_constraint_varify_errors.get(&pattern).copied()
    }

    /// Return a value binding's locally abstract constraint, when present.
    pub fn value_constraint(&self, pattern: PatIdx) -> Option<&ValueConstraint> {
        self.value_constraints_by_pattern.get(&pattern)
    }

    /// Return the authoritative n-ary parameters, or the compact fallback.
    pub fn stored_nary_fun_params(&self, fun: &crate::parser::ast::PexpFun) -> Option<&[FunParam]> {
        self.nary_fun_params_by_first_pattern
            .get(&fun.lhs)
            .map(|params| self.nary_fun_param_lists.get(*params))
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

    /// Borrow recorded n-ary parameters, or reconstruct the single-parameter fallback.
    pub fn nary_fun_params<'a>(
        &'a self,
        fun: &'a crate::parser::ast::PexpFun,
    ) -> std::borrow::Cow<'a, [FunParam]> {
        if self.get_arity(fun.arity).is_some()
            && let Some(params) = self.nary_fun_params_by_first_pattern.get(&fun.lhs)
        {
            std::borrow::Cow::Borrowed(self.nary_fun_param_lists.get(*params))
        } else {
            let mut params = vec![FunParam {
                p_attrs: self.get_pat(fun.lhs).ppat_attributes.clone(),
                p_lbl: fun.arg_label,
                p_default: fun.default,
                p_pat: fun.lhs,
            }];
            if let Some(arity) = self.get_arity(fun.arity) {
                let mut body = fun.rhs;
                while params.len() < arity.max(1) as usize {
                    let ExpressionDesc::Pexp_fun(next) = &self.get_expr(body).pexp_desc else {
                        break;
                    };
                    params.push(FunParam {
                        p_attrs: self.get_pat(next.lhs).ppat_attributes.clone(),
                        p_lbl: next.arg_label,
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
            let ExpressionDesc::Pexp_fun(next) = &self.get_expr(body).pexp_desc else {
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
    pub fn set_fun_default(&mut self, owner: ExprIdx, value: Option<ExprIdx>) {
        self.expr_overrides.entry(owner.0).or_default().fun_default = value;
    }

    /// Get sparse function default data for a `Pexp_fun` expression node.
    pub fn fun_default(&self, owner: ExprIdx) -> Option<ExprIdx> {
        self.expr_overrides
            .get(&owner.0)
            .and_then(|o| o.fun_default)
            .or_else(|| match &self.get_expr(owner).pexp_desc {
                ExpressionDesc::Pexp_fun(inner) => inner.default,
                _ => None,
            })
    }

    /// Attach sparse case guard data to a `Pexp_match`/`Pexp_try` expression node.
    ///
    /// Guards are indexed by case position within the node's `Vec<Case>`.
    pub fn set_case_guards(&mut self, owner: ExprIdx, guards: Vec<Option<ExprIdx>>) {
        self.expr_overrides.entry(owner.0).or_default().case_guards =
            if guards.is_empty() || guards.iter().all(|g| g.is_none()) {
                None
            } else {
                Some(guards.into_boxed_slice())
            };
    }

    /// Get a sparse case guard by owner expression and case position.
    pub fn case_guard(&self, owner: ExprIdx, case_index: usize) -> Option<ExprIdx> {
        self.expr_overrides
            .get(&owner.0)
            .and_then(|o| o.case_guards.as_deref())
            .and_then(|guards| guards.get(case_index))
            .copied()
            .flatten()
            .or_else(|| match &self.get_expr(owner).pexp_desc {
                ExpressionDesc::Pexp_match((_, cases))
                | ExpressionDesc::Pexp_try((_, cases, _)) => {
                    self.case_list(*cases)
                        .get(case_index)
                        .and_then(|case| case.pc_guard)
                }
                _ => None,
            })
    }

    /// Attach sparse record spread/base expression data to a record expression node.
    pub fn set_record_spread(&mut self, owner: ExprIdx, value: Option<ExprIdx>) {
        self.expr_overrides
            .entry(owner.0)
            .or_default()
            .record_spread = value;
    }

    /// Get sparse record spread/base expression data for a `Pexp_record` expression node.
    pub fn record_spread(&self, owner: ExprIdx) -> Option<ExprIdx> {
        self.expr_overrides
            .get(&owner.0)
            .and_then(|o| o.record_spread)
            .or_else(|| match &self.get_expr(owner).pexp_desc {
                ExpressionDesc::Pexp_record(inner) => {
                    let (_, spread) = inner;
                    *spread
                }
                _ => None,
            })
    }

    /// Attach sparse else-branch expression data to an if-then-else expression node.
    pub fn set_if_else_branch(&mut self, owner: ExprIdx, value: Option<ExprIdx>) {
        self.expr_overrides
            .entry(owner.0)
            .or_default()
            .if_else_branch = value;
    }

    /// Get sparse else-branch expression data for a `Pexp_ifthenelse` expression node.
    pub fn if_else_branch(&self, owner: ExprIdx) -> Option<ExprIdx> {
        self.expr_overrides
            .get(&owner.0)
            .and_then(|o| o.if_else_branch)
            .or_else(|| match &self.get_expr(owner).pexp_desc {
                ExpressionDesc::Pexp_ifthenelse(inner) => {
                    let (_, _, else_branch) = &**inner;
                    *else_branch
                }
                _ => None,
            })
    }

    /// Attach sparse source type data to a coerce expression node.
    pub fn set_coerce_from_type(&mut self, owner: ExprIdx, value: Option<CoreTypeIdx>) {
        self.expr_overrides
            .entry(owner.0)
            .or_default()
            .coerce_from_type = value;
    }

    /// Get sparse source type data for a `Pexp_coerce` expression node.
    pub fn coerce_from_type(&self, owner: ExprIdx) -> Option<CoreTypeIdx> {
        self.expr_overrides
            .get(&owner.0)
            .and_then(|o| o.coerce_from_type)
            .or_else(|| match &self.get_expr(owner).pexp_desc {
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
        if raw < self.synthetic_pattern_base {
            self.patterns.get(idx)
        } else {
            self.synthetic_patterns
                .get((raw - self.synthetic_pattern_base) as usize)
                .expect("typechecker synthetic pattern read before initialization")
        }
    }

    /// Get a mutable pattern by index.
    #[inline]
    pub fn get_pat_mut(&mut self, idx: PatIdx) -> &mut Pattern {
        self.patterns.get_mut(idx)
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
        let raw = idx.0;
        if raw < SHARED_CORE_TYPE_BASE {
            self.core_types.get(idx)
        } else {
            self.shared_core_types
                .get((raw - SHARED_CORE_TYPE_BASE) as usize)
                .expect("shared core type read before it was pushed")
        }
    }

    /// Get a mutable core type by index; shared core types are immutable.
    #[inline]
    pub fn get_core_type_mut(&mut self, idx: CoreTypeIdx) -> &mut CoreType {
        assert!(
            idx.0 < SHARED_CORE_TYPE_BASE,
            "shared core types are immutable"
        );
        self.core_types.get_mut(idx)
    }

    /// Append a core type while the arena is shared.
    pub fn push_shared_core_type(&self, typ: CoreType) -> CoreTypeIdx {
        let slot = self.shared_core_types.len();
        self.shared_core_types.push(Box::new(typ));
        CoreTypeIdx(SHARED_CORE_TYPE_BASE + slot as u32)
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
/// A list stored back to back in one of `ParseArena`'s list pools.
///
/// Parse-tree nodes hold these 8-byte handles instead of owning a `Vec`, so
/// dropping a module's tree frees one buffer per pool instead of one
/// allocation per list. Read the items with the matching `ParseArena`
/// accessor; a handle is only meaningful for the arena that issued it.
pub struct ArenaList<T> {
    start: u32,
    len: u32,
    _items: std::marker::PhantomData<fn() -> T>,
}

impl<T> ArenaList<T> {
    /// The empty list, valid for every arena.
    pub const EMPTY: Self = Self {
        start: 0,
        len: 0,
        _items: std::marker::PhantomData,
    };

    /// Number of elements in this arena list.
    pub fn len(self) -> usize {
        self.len as usize
    }

    /// Whether this arena list has no elements.
    pub fn is_empty(self) -> bool {
        self.len == 0
    }

    /// A list of `len` items starting at `start` in a pool owned by another
    /// arena (the typed tree's [`crate::types::tast_arena::TypedArena`]).
    pub(crate) fn from_range(start: u32, len: u32) -> Self {
        Self {
            start,
            len,
            _items: std::marker::PhantomData,
        }
    }

    /// First slot of the list in its pool.
    pub(crate) fn start(self) -> u32 {
        self.start
    }
}

impl<T> Clone for ArenaList<T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T> Copy for ArenaList<T> {}

impl<T> PartialEq for ArenaList<T> {
    fn eq(&self, other: &Self) -> bool {
        (self.start, self.len) == (other.start, other.len)
    }
}

impl<T> Eq for ArenaList<T> {}

impl<T> std::hash::Hash for ArenaList<T> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        (self.start, self.len).hash(state);
    }
}

impl<T> Default for ArenaList<T> {
    fn default() -> Self {
        Self::EMPTY
    }
}

impl<T> std::fmt::Debug for ArenaList<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "ArenaList({}..+{})", self.start, self.len)
    }
}

impl<T> Serialize for ArenaList<T> {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        (self.start, self.len).serialize(serializer)
    }
}

impl<'de, T> Deserialize<'de> for ArenaList<T> {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let (start, len) = <(u32, u32)>::deserialize(deserializer)?;
        Ok(Self {
            start,
            len,
            _items: std::marker::PhantomData,
        })
    }
}

/// Arguments of a `Pexp_apply`.
pub type ApplyArgs = ArenaList<(ArgLabel, ExprIdx)>;

/// An expression index list (tuple, array and constructor arguments).
pub type ExprList = ArenaList<ExprIdx>;
/// A pattern index list.
pub type PatList = ArenaList<PatIdx>;
/// A core type index list.
pub type TypeList = ArenaList<CoreTypeIdx>;
/// The value bindings of a `let`.
pub type VbList = ArenaList<ValueBinding>;
/// The fields of a record expression.
pub type ExprFieldList = ArenaList<ExpressionRecordField>;
/// The fields of a record pattern.
pub type PatFieldList = ArenaList<PatternRecordField>;
/// The cases of a `switch` or `try`.
pub type CaseList = ArenaList<Case>;
/// The elements of a literal with spreads (`Pexp_spread`).
pub type SpreadElementList = ArenaList<crate::parser::ast::SpreadElement>;

/// Lists pushed through a shared arena reference (by the type checker) set
/// this bit in `ArenaList::start`; the rest is the slot in `ListPool::shared`.
const SHARED_LIST_FLAG: u32 = 1 << 31;

/// Append-only storage for nodes the type checker adds through a shared
/// reference. Nodes go into fixed-size chunks, so a node costs no allocation
/// of its own and references to it stay valid while more are appended.
struct SyntheticVec<T> {
    chunks: elsa::sync::FrozenVec<Box<[std::sync::OnceLock<T>]>>,
    len: std::sync::Mutex<usize>,
}

impl<T> SyntheticVec<T> {
    const CHUNK: usize = 64;

    /// Appends `value`; returns its index.
    fn push(&self, value: T) -> usize {
        let mut len = self.len.lock().unwrap_or_else(|poisoned| poisoned.into_inner());
        let index = *len;
        if index % Self::CHUNK == 0 {
            self.chunks
                .push((0..Self::CHUNK).map(|_| std::sync::OnceLock::new()).collect());
        }
        let slot = &self.chunks.get(index / Self::CHUNK).expect("chunk pushed above")
            [index % Self::CHUNK];
        if slot.set(value).is_err() {
            unreachable!("synthetic slot {index} filled twice");
        }
        *len = index + 1;
        index
    }

    fn get(&self, index: usize) -> Option<&T> {
        self.chunks.get(index / Self::CHUNK)?[index % Self::CHUNK].get()
    }
}

impl<T> Default for SyntheticVec<T> {
    fn default() -> Self {
        Self {
            chunks: elsa::sync::FrozenVec::new(),
            len: std::sync::Mutex::new(0),
        }
    }
}

impl<T: std::fmt::Debug> std::fmt::Debug for SyntheticVec<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("SyntheticVec").finish_non_exhaustive()
    }
}

/// Backing storage for one kind of `ArenaList`: one buffer for lists built
/// while the arena is exclusively borrowed, plus append-only slots for the
/// few lists built through a shared reference during type checking.
#[derive(Debug)]
struct ListPool<T> {
    items: Vec<T>,
    shared: elsa::sync::FrozenVec<Box<[T]>>,
}

impl<T> Default for ListPool<T> {
    fn default() -> Self {
        Self {
            items: Vec::new(),
            shared: elsa::sync::FrozenVec::new(),
        }
    }
}

impl<T: Clone> ListPool<T> {
    fn push(&mut self, items: &[T]) -> ArenaList<T> {
        if items.is_empty() {
            return ArenaList::EMPTY;
        }
        let start = u32::try_from(self.items.len())
            .ok()
            .filter(|start| start & SHARED_LIST_FLAG == 0)
            .expect("list pool exceeds 2^31 items");
        self.items.extend_from_slice(items);
        ArenaList {
            start,
            len: items.len() as u32,
            _items: std::marker::PhantomData,
        }
    }

    fn push_shared(&self, items: &[T]) -> ArenaList<T> {
        if items.is_empty() {
            return ArenaList::EMPTY;
        }
        let slot = self.shared.len() as u32;
        self.shared.push(items.to_vec().into_boxed_slice());
        ArenaList {
            start: SHARED_LIST_FLAG | slot,
            len: items.len() as u32,
            _items: std::marker::PhantomData,
        }
    }

    fn get(&self, list: ArenaList<T>) -> &[T] {
        if list.len == 0 {
            return &[];
        }
        if list.start & SHARED_LIST_FLAG != 0 {
            return self
                .shared
                .get((list.start & !SHARED_LIST_FLAG) as usize)
                .expect("shared list slot");
        }
        &self.items[list.start as usize..][..list.len as usize]
    }
}

/// A syntax value paired with its source-location handle.
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
    #[test]
    fn ten_thousand_ghost_views_do_not_allocate_locations() {
        let mut arena = ParseArena::new();
        let locations: Vec<_> = (0..10_000)
            .map(|_| arena.push_loc(PosIdx(0), PosIdx(0), false))
            .collect();
        let before = arena.location_count();
        let mut steps = 0;
        for source in locations {
            let ghost = arena.ghost_location(source);
            steps += 1;
            assert_eq!(arena.ghost_location(ghost), ghost);
            assert!(arena.loc_ghost(ghost));
            assert!(!arena.loc_ghost(source));
            assert_eq!(arena.loc_start_idx(ghost), arena.loc_start_idx(source));
            assert_eq!(arena.loc_end_idx(ghost), arena.loc_end_idx(source));
            assert!(arena.to_location(ghost).loc_ghost);
        }
        assert_eq!(steps, 10_000);
        assert_eq!(arena.location_count(), before);
        assert_eq!(std::mem::size_of::<InternedLocation>(), 12);
    }

    use super::*;
    use crate::parser::ast::{
        ArgLabel, Attributes, Case, ExpressionDesc, Pattern, PatternDesc, PexpFun,
    };

    fn ident_expr(arena: &mut ParseArena, name: &str) -> Expression {
        let lid = arena.push_lident(name);
        Expression {
            pexp_desc: ExpressionDesc::Pexp_ident(Located {
                txt: lid,
                loc: LocIdx::default(),
            }),
            pexp_loc: LocIdx::default(),
            pexp_attributes: Attributes::new(),
        }
    }

    #[test]
    fn typecheck_synthetic_storage_grows_without_a_fixed_limit() {
        let mut arena = ParseArena::new();
        arena.reserve_typecheck_synthetic_capacity();
        let mut patterns = Vec::new();
        let mut longidents = Vec::new();
        for index in 0..2048 {
            longidents.push(arena.push_typecheck_lident(format!("Generated{index}")));
            patterns.push(arena.push_typecheck_pattern(Pattern {
                ppat_desc: PatternDesc::Ppat_any,
                ppat_loc: LocIdx::none(),
                ppat_attributes: Attributes::new(),
            }));
        }

        assert!(matches!(
            arena.get_longident(longidents[0]),
            Longident::Lident(_)
        ));
        assert_eq!(
            arena.get_string(match arena.get_longident(longidents[2047]) {
                Longident::Lident(name) => *name,
                _ => unreachable!(),
            }),
            "Generated2047"
        );
        assert!(matches!(
            &arena.get_pat(patterns[2047]).ppat_desc,
            PatternDesc::Ppat_any
        ));
    }

    #[test]
    fn location_free_arena_allocates_no_location_side_tables() {
        let mut arena = ParseArena::with_locations(false);
        arena.reserve_for_source(100_000);
        let file = arena.intern("test.res");
        arena.set_source_file(file);
        let mut last = LocIdx::none();
        for offset in 0..10_000 {
            let start = arena.push_pos(file, 1, 0, offset);
            let loc = arena.mk_loc(start, start);
            assert_ne!(loc, last);
            assert!(!arena.loc_ghost(loc));
            assert!(arena.loc_ghost(arena.push_typecheck_ghost_loc(loc)));
            assert_eq!(arena.loc_start(loc).cnum, 0);
            last = loc;
        }
        arena.push_typecheck_location(&Location::default(), &|_| None);
        assert_eq!(arena.position_count(), 0);
        assert_eq!(arena.location_count(), 0);
        assert_eq!(arena.synthetic_positions.len(), 0);
        assert_eq!(arena.synthetic_locations.len(), 0);
        assert!(!arena.locations_required());
        arena.require_locations();
        assert!(arena.locations_required());
    }

    #[test]
    fn location_free_attributes_keep_distinct_usage_identity() {
        let mut arena = ParseArena::with_locations(false);
        let name = arena.intern("test");
        let a = arena.mk_loc(PosIdx(0), PosIdx(0));
        let b = arena.mk_loc(PosIdx(0), PosIdx(0));
        let attr = (
            Located::new(name, a),
            crate::parser::ast::Payload::PStr(Box::default()),
        );
        arena.mark_used_attribute(&attr);
        assert!(arena.is_used_attribute(a));
        assert!(!arena.is_used_attribute(b));
        assert!(arena.loc_ghost(arena.none_loc()));

        // Env usage tracking uses full Location values, not LocIdx. Omitted
        // coordinates must not merge two shadowed declarations of one name.
        let mut usage = crate::types::usage::UsageTables::default();
        let a_loc = arena.to_location(a);
        let b_loc = arena.to_location(b);
        let copied_a = arena.clone_loc(a);
        assert_eq!(arena.to_location(copied_a), a_loc);
        let restored_a = arena.from_location(&a_loc);
        assert_eq!(arena.to_location(restored_a), a_loc);
        let a_used = usage.check_value_usage("x", a_loc).unwrap();
        let b_used = usage.check_value_usage("x", b_loc).unwrap();
        usage.mark_value_used("x", b_loc);
        assert!(!usage.is_used(a_used));
        assert!(usage.is_used(b_used));
    }

    #[test]
    fn source_file_names_are_tracked_while_positions_are_added() {
        let mut arena = ParseArena::new();
        let first = arena.intern("first.res");
        let second = arena.intern("generated.res");
        arena.push_pos(first, 1, 0, 0);
        arena.from_location(&Location {
            loc_start: Position::new(second, 2, 10, 12),
            loc_end: Position::new(second, 2, 10, 20),
            loc_ghost: false,
            origin: Default::default(),
        });

        let names = arena.source_file_names();
        assert_eq!(names.get(&first).map(String::as_str), Some("first.res"));
        assert_eq!(
            names.get(&second).map(String::as_str),
            Some("generated.res")
        );
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
            &placeholder.pexp_desc,
            ExpressionDesc::Pexp_ident(_)
        ));

        let expr = ident_expr(&mut arena, "ready");
        arena.initialize_expr(slot, expr);

        let initialized = arena.get_expr(slot);
        match &initialized.pexp_desc {
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
        assert_eq!(arena.record_spread(owner), None);
        assert_eq!(arena.if_else_branch(owner), None);
        assert_eq!(arena.coerce_from_type(owner), None);

        arena.set_fun_default(owner, Some(default_expr));
        arena.set_case_guards(owner, vec![None, Some(guard_expr)]);
        arena.set_record_spread(owner, Some(default_expr));
        arena.set_if_else_branch(owner, Some(guard_expr));
        arena.set_coerce_from_type(owner, Some(from_type));

        assert_eq!(arena.fun_default(owner), Some(default_expr));
        assert_eq!(arena.case_guard(owner, 0), None);
        assert_eq!(arena.case_guard(owner, 1), Some(guard_expr));
        assert_eq!(arena.case_guard(owner, 2), None);
        assert_eq!(arena.record_spread(owner), Some(default_expr));
        assert_eq!(arena.if_else_branch(owner), Some(guard_expr));
        assert_eq!(arena.coerce_from_type(owner), Some(from_type));
    }

    #[test]
    fn test_sparse_expr_side_tables_seed_from_expr_and_fallback_after_mutation() {
        let mut arena = ParseArena::new();

        let lhs = arena.push_pat(Pattern {
            ppat_desc: PatternDesc::Ppat_any,
            ppat_loc: LocIdx::default(),
            ppat_attributes: Attributes::new(),
        });
        let rhs_expr = ident_expr(&mut arena, "rhs");
        let rhs = arena.push_expr(rhs_expr);
        let default_expr_node = ident_expr(&mut arena, "default");
        let default_expr = arena.push_expr(default_expr_node);
        let fun_owner = arena.push_expr(Expression {
            pexp_desc: ExpressionDesc::Pexp_fun(Box::new(PexpFun {
                arg_label: ArgLabel::Nolabel,
                default: Some(default_expr),
                lhs,
                rhs,
                arity: arena.static_arity_none(),
                is_async: false,
            })),
            pexp_loc: LocIdx::default(),
            pexp_attributes: Attributes::new(),
        });

        let case_lhs = arena.push_pat(Pattern {
            ppat_desc: PatternDesc::Ppat_any,
            ppat_loc: LocIdx::default(),
            ppat_attributes: Attributes::new(),
        });
        let case_rhs_node = ident_expr(&mut arena, "case_rhs");
        let case_rhs = arena.push_expr(case_rhs_node);
        let guard_expr_node = ident_expr(&mut arena, "guard");
        let guard_expr = arena.push_expr(guard_expr_node);
        let cases = arena.push_case_list(&[Case {
            pc_bar: None,
            pc_lhs: case_lhs,
            pc_guard: Some(guard_expr),
            pc_rhs: case_rhs,
        }]);
        let match_owner = arena.push_expr(Expression {
            pexp_desc: ExpressionDesc::Pexp_match((rhs, cases)),
            pexp_loc: LocIdx::default(),
            pexp_attributes: Attributes::new(),
        });

        let record_owner = arena.push_expr(Expression {
            pexp_desc: ExpressionDesc::Pexp_record((
                crate::parse_arena::ArenaList::EMPTY,
                Some(default_expr),
            )),
            pexp_loc: LocIdx::default(),
            pexp_attributes: Attributes::new(),
        });

        let if_owner = arena.push_expr(Expression {
            pexp_desc: ExpressionDesc::Pexp_ifthenelse(Box::new((rhs, case_rhs, Some(guard_expr)))),
            pexp_loc: LocIdx::default(),
            pexp_attributes: Attributes::new(),
        });

        let from_type = arena.push_core_type(ParseArena::placeholder_core_type());
        let to_type = arena.push_core_type(ParseArena::placeholder_core_type());
        let coerce_owner = arena.push_expr(Expression {
            pexp_desc: ExpressionDesc::Pexp_coerce(Box::new((rhs, Some(from_type), to_type))),
            pexp_loc: LocIdx::default(),
            pexp_attributes: Attributes::new(),
        });

        assert_eq!(arena.fun_default(fun_owner), Some(default_expr));
        assert_eq!(arena.case_guard(match_owner, 0), Some(guard_expr));
        assert_eq!(arena.record_spread(record_owner), Some(default_expr));
        assert_eq!(arena.if_else_branch(if_owner), Some(guard_expr));
        assert_eq!(arena.coerce_from_type(coerce_owner), Some(from_type));

        // get_expr_mut clears sparse cache entries; fallback to inline fields must preserve behavior.
        let _ = arena.get_expr_mut(fun_owner);
        let _ = arena.get_expr_mut(match_owner);
        let _ = arena.get_expr_mut(record_owner);
        let _ = arena.get_expr_mut(if_owner);
        let _ = arena.get_expr_mut(coerce_owner);

        assert_eq!(arena.fun_default(fun_owner), Some(default_expr));
        assert_eq!(arena.case_guard(match_owner, 0), Some(guard_expr));
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
            &arena.get_pat(pat_slot).ppat_desc,
            PatternDesc::Ppat_any
        ));
        assert!(matches!(
            &arena.get_core_type(ty_slot).ptyp_desc,
            CoreTypeDesc::Ptyp_any
        ));
        assert!(matches!(
            &arena.get_mod_expr(me_slot).pmod_desc,
            ModuleExprDesc::Pmod_ident(_)
        ));
        assert!(matches!(
            &arena.get_mod_type(mt_slot).pmty_desc,
            ModuleTypeDesc::Pmty_ident(_)
        ));
    }

    #[test]
    fn apply_args_lists_are_independent_ranges() {
        use crate::parser::ast::ArgLabel;
        let mut arena = ParseArena::new();
        let (a, b, c) = (ExprIdx(1), ExprIdx(2), ExprIdx(3));
        let first = arena.push_apply_args(&[(ArgLabel::Nolabel, a), (ArgLabel::Nolabel, b)]);
        let empty = arena.push_apply_args(&[]);
        let second = arena.push_apply_args(&[(ArgLabel::Nolabel, c)]);
        assert_eq!(first.len(), 2);
        assert!(empty.is_empty());
        assert_eq!(empty, ApplyArgs::EMPTY);
        assert!(arena.apply_args(empty).is_empty());
        let firsts: Vec<_> = arena.apply_args(first).iter().map(|(_, e)| *e).collect();
        assert_eq!(firsts, vec![a, b]);
        let seconds: Vec<_> = arena.apply_args(second).iter().map(|(_, e)| *e).collect();
        assert_eq!(seconds, vec![c]);
    }

    /// An expression without a certificate, like every node a rewrite
    /// applies to.
    fn uncertified_expr(arena: &mut ParseArena) -> ExprIdx {
        let operand = arena.push_expr(ParseArena::placeholder_expr());
        let idx = arena.push_expr(Expression {
            pexp_desc: ExpressionDesc::Pexp_await(operand),
            ..ParseArena::placeholder_expr()
        });
        assert!(!arena.expr_needs_no_rewrite(idx));
        idx
    }

    #[test]
    fn an_expansion_is_read_through_expanded_and_the_original_stays() {
        let mut arena = ParseArena::new();
        let original = uncertified_expr(&mut arena);
        let neighbour = uncertified_expr(&mut arena);
        assert_eq!(arena.expanded(original), original);
        let before = arena.get_expr(original).clone();
        let expanded = arena.push_expr(ParseArena::placeholder_expr());
        arena.set_expansion(original, expanded);
        assert_eq!(arena.expanded(original), expanded);
        assert_eq!(arena.get_expr(original), &before);
        // A neighbour in the same page, and nodes past the table's end.
        assert_eq!(arena.expanded(neighbour), neighbour);
        assert_eq!(arena.expanded(expanded), expanded);
        assert_eq!(arena.expanded(ExprIdx(1 << 20)), ExprIdx(1 << 20));
        // A certificate elsewhere in the same word is not disturbed.
        assert!(arena.expr_needs_no_rewrite(expanded));
        // The last expansion recorded for a node is the one read.
        let second = arena.push_expr(ParseArena::placeholder_expr());
        arena.set_expansion(original, second);
        assert_eq!(arena.expanded(original), second);
    }

    #[test]
    fn expansions_survive_the_invalidation_of_certificates() {
        let mut arena = ParseArena::new();
        let nodes: Vec<_> = (0..70).map(|_| uncertified_expr(&mut arena)).collect();
        let target = arena.push_expr(ParseArena::placeholder_expr());
        for &idx in &[nodes[7], nodes[8], nodes[42], nodes[69]] {
            arena.set_expansion(idx, target);
        }
        assert!(arena.expr_needs_no_rewrite(target));
        arena.get_expr_mut(nodes[0]).pexp_desc = ExpressionDesc::Pexp_break;
        assert!(!arena.expr_needs_no_rewrite(target));
        for &idx in &[nodes[7], nodes[8], nodes[42], nodes[69]] {
            assert_eq!(arena.expanded(idx), target);
        }
        assert_eq!(arena.expanded(nodes[22]), nodes[22]);
    }

    #[test]
    fn ten_thousand_expansions_take_one_page_per_sixty_four_expressions() {
        // Dense: 10,000 consecutive pairs (operand, await), each await expanded.
        let mut arena = ParseArena::new();
        let nodes: Vec<_> = (0..10_000).map(|_| uncertified_expr(&mut arena)).collect();
        let target = arena.push_expr(ParseArena::placeholder_expr());
        for &idx in &nodes {
            arena.set_expansion(idx, ExprIdx(target.0 + idx.0));
        }
        for &idx in &nodes {
            assert_eq!(arena.expanded(idx), ExprIdx(target.0 + idx.0));
            assert_eq!(arena.expanded(ExprIdx(idx.0 - 1)), ExprIdx(idx.0 - 1));
        }
        let pages = (2 * 10_000usize).div_ceil(EXPANSION_PAGE);
        assert_eq!(arena.expansion_targets.len(), pages * EXPANSION_PAGE);

        // Sparse: one expansion every 1,000 expressions costs one page each,
        // not an entry per expression.
        let mut arena = ParseArena::new();
        let nodes: Vec<_> = (0..50_000).map(|_| uncertified_expr(&mut arena)).collect();
        let target = arena.push_expr(ParseArena::placeholder_expr());
        for idx in nodes.iter().step_by(500) {
            arena.set_expansion(*idx, target);
        }
        assert_eq!(arena.expansion_targets.len(), 100 * EXPANSION_PAGE);
        // The page index ends at the last page with an expansion.
        assert_eq!(arena.expansion_pages.len(), (2 * 49_500 + 1) / EXPANSION_PAGE + 1);
    }

    #[test]
    fn a_visited_location_and_its_ghost_are_two_bits_of_one_word() {
        let mut arena = ParseArena::new();
        let (loc, ghost) = (LocIdx(5), LocIdx(5 | 0x4000_0000));
        arena.mark_rewritten_expr_loc(ghost);
        assert!(arena.is_rewritten_expr_loc(ghost));
        assert!(!arena.is_rewritten_expr_loc(loc));
        arena.mark_rewritten_expr_loc(loc);
        assert!(arena.is_rewritten_expr_loc(loc));
        assert!(!arena.is_rewritten_expr_loc(LocIdx(6)));
        // A synthetic location of the type checker is never marked.
        arena.mark_rewritten_expr_loc(LocIdx(SYNTHETIC_LOCATION_BASE + 5));
        assert!(!arena.is_rewritten_expr_loc(LocIdx(SYNTHETIC_LOCATION_BASE + 5)));
        assert_eq!(arena.rewritten_expr_locs.len(), 1);
    }

    #[test]
    fn validation_certificates_preserve_overflow_and_invalidate_parents() {
        let mut arena = ParseArena::new();
        let text = arena.intern("2147483648");
        let integer = arena.push_expr(Expression {
            pexp_desc: ExpressionDesc::Pexp_constant(Constant::Integer(text, None)),
            pexp_loc: LocIdx::default(),
            pexp_attributes: Attributes::new(),
        });
        assert!(arena.expr_needs_no_rewrite(integer));
        assert!(!arena.expr_needs_no_attribute_sweep(integer));
        let leaf = arena.push_expr(ParseArena::placeholder_expr());
        // Cross packed-word boundaries, including invalidation at offset zero.
        let mut parents = vec![leaf];
        for _ in 0..100 {
            let child = *parents.last().unwrap();
            parents.push(arena.push_expr(Expression {
                pexp_desc: ExpressionDesc::Pexp_sequence(child, leaf),
                pexp_loc: LocIdx::default(),
                pexp_attributes: Attributes::new(),
            }));
        }
        for &idx in &parents {
            assert!(arena.expr_needs_no_rewrite(idx));
            assert!(arena.expr_needs_no_attribute_sweep(idx));
        }
        arena.get_expr_mut(ExprIdx(32)).pexp_desc = ExpressionDesc::Pexp_await(leaf);
        for &idx in &parents {
            assert_eq!(arena.expr_needs_no_rewrite(idx), idx.0 < 32);
            assert_eq!(arena.expr_needs_no_attribute_sweep(idx), idx.0 < 32);
        }
        let reserved = arena.reserve_expr();
        arena.initialize_expr(reserved, ParseArena::placeholder_expr());
        assert!(!arena.expr_needs_no_rewrite(reserved));
        assert!(!arena.expr_needs_no_attribute_sweep(reserved));
    }

}

#[cfg(test)]
#[test]
fn derived_group_bitmap_growth_is_linear_at_ten_thousand_slots() {
    let mut arena = ParseArena::new();
    let mut initialized_words = 0;
    for slot in 0..10_000 {
        let before = arena.derived_value_groups.len();
        let group = VbList::from_range(slot, 1);
        arena.mark_derived_value_group(group);
        initialized_words += arena.derived_value_groups.len() - before;
        assert!(arena.is_derived_value_group(group));
        assert!(!arena.is_derived_value_group(VbList::from_range(slot + 1, 1)));
    }
    // 10,000 direct bit writes; resize initializes each word exactly once.
    assert_eq!(initialized_words, 157);
    assert_eq!(arena.derived_value_groups.len(), 157);
    for slot in 0..10_000 {
        arena.mark_derived_value_group(VbList::from_range(slot, 1));
    }
    assert_eq!(arena.derived_value_groups.len(), initialized_words);
    assert!(!arena.is_derived_value_group(VbList::EMPTY));
    // Provenance does not enlarge the handle passed through the frontend.
    assert_eq!(std::mem::size_of::<VbList>(), 8);
}
