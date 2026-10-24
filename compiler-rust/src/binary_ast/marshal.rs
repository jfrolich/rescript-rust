//! OCaml Marshal format writer
//!
//! This module implements a writer for OCaml's Marshal binary serialization format.
//! The Marshal format is used by ReScript for binary AST files (.ast, .iast).
//!
//! # Format Overview
//!
//! The Marshal format consists of:
//! 1. Magic number (4 bytes): 0x8495A6BE for small format
//! 2. Header (16 bytes): data_len, obj_count, size_32, size_64
//! 3. Payload: encoded OCaml values
//!
//! # Position Identity-Based Sharing
//!
//! OCaml's Marshal format uses pointer-based sharing - when two positions
//! are the SAME object in memory, they get a shared reference (CODE_SHARED8/16/32).
//! We mimic this using arena indices (PosIdx/LocIdx): positions with the same
//! index are considered "the same object" and get shared.
//!
//! This is critical for byte-for-byte parity with OCaml's parser output.
//!
//! # References
//!
//! - OCaml runtime: runtime/extern.c
//! - OCaml runtime: runtime/caml/intext.h

use crate::fast_hash::AHashMap as HashMap;

use crate::location::{Location, Position};
use crate::parse_arena::{ArityIdx, ExprIdx, LidentIdx, LocIdx, ParseArena, PosIdx, StrIdx};
use crate::parser::longident::Longident;

/// Magic number for small Marshal format
const MAGIC_NUMBER_SMALL: u32 = 0x8495A6BE;

/// Prefix codes for compact encoding
const PREFIX_SMALL_BLOCK: u8 = 0x80;
const PREFIX_SMALL_INT: u8 = 0x40;
const PREFIX_SMALL_STRING: u8 = 0x20;

/// Explicit opcodes
const CODE_INT8: u8 = 0x00;
const CODE_INT16: u8 = 0x01;
const CODE_INT32: u8 = 0x02;
const CODE_INT64: u8 = 0x03;
const CODE_SHARED8: u8 = 0x04;
const CODE_SHARED16: u8 = 0x05;
const CODE_SHARED32: u8 = 0x06;
const CODE_BLOCK32: u8 = 0x08;
const CODE_STRING8: u8 = 0x09;
const CODE_STRING32: u8 = 0x0A;
const CODE_DOUBLE_BIG: u8 = 0x0B;
const CODE_DOUBLE_LITTLE: u8 = 0x0C;
#[allow(dead_code)]
const CODE_BLOCK64: u8 = 0x13;
#[allow(dead_code)]
const CODE_SHARED64: u8 = 0x14;
#[allow(dead_code)]
const CODE_STRING64: u8 = 0x15;
const CODE_CUSTOM_FIXED: u8 = 0x19;

/// Sharing groups for empty `PStr []` payloads.
///
/// OCaml shares empty payloads in specific contexts due to CSE and
/// module-level constants. We mirror that by sharing within these groups.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub(crate) enum EmptyPayloadShareKind {
    ObjectTypeAttr,
    ObjectFieldAttr,
    ParserAttr,
}

impl EmptyPayloadShareKind {
    const COUNT: usize = 3;

    #[inline]
    const fn as_index(self) -> usize {
        match self {
            Self::ObjectTypeAttr => 0,
            Self::ObjectFieldAttr => 1,
            Self::ParserAttr => 2,
        }
    }
}

/// Sharing groups for single-element primitive lists in `pval_prim`.
///
/// OCaml shares some primitive lists because they are compiled as module-level
/// constants (e.g. ["#raw_expr"]). We mirror that by sharing those lists here.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub(crate) enum PrimListShareKind {
    RawExpr,
    RawStmt,
}

impl PrimListShareKind {
    const COUNT: usize = 2;

    #[inline]
    const fn as_index(self) -> usize {
        match self {
            Self::RawExpr => 0,
            Self::RawStmt => 1,
        }
    }
}

/// Sharing table keyed by `(tyvar name, LocIdx)`.
///
/// Grouped by location so lookups borrow the name and only a first insertion
/// allocates; a location rarely carries more than one tyvar name.
#[derive(Debug, Default)]
struct TyvarShareTable(HashMap<LocIdx, Vec<(String, u32)>>);

impl TyvarShareTable {
    fn get(&self, name: &str, loc: LocIdx) -> Option<u32> {
        self.0
            .get(&loc)?
            .iter()
            .find(|(n, _)| n == name)
            .map(|&(_, idx)| idx)
    }

    /// Insert or overwrite the entry for `(name, loc)`, like `HashMap::insert`.
    fn insert(&mut self, name: &str, loc: LocIdx, obj_idx: u32) {
        let entries = self.0.entry(loc).or_default();
        match entries.iter_mut().find(|(n, _)| n == name) {
            Some(entry) => entry.1 = obj_idx,
            None => entries.push((name.to_owned(), obj_idx)),
        }
    }
}

/// A self-contained marshalled value: its encoded payload plus the object and
/// heap-size counts it contributes. Shared references inside a fragment are
/// relative to its own objects, so it can be embedded verbatim into another
/// stream with [`MarshalWriter::write_fragment`].
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct MarshalFragment {
    /// Encoded payload (no marshal header).
    pub bytes: Vec<u8>,
    /// Number of shareable objects in the payload.
    pub objects: u32,
    /// Heap size in words on 32-bit platforms.
    pub size_32: u32,
    /// Heap size in words on 64-bit platforms.
    pub size_64: u32,
}

/// Writer for OCaml Marshal binary format
///
/// This struct maintains the serialization state and provides methods for
/// encoding OCaml values to the Marshal format.
///
/// # Usage
///
/// ```ignore
/// let mut writer = MarshalWriter::new();
/// writer.write_int(42);
/// writer.write_string(b"hello");
/// let bytes = writer.finish();
/// ```
#[derive(Debug)]
pub struct MarshalWriter<'a> {
    /// Debug tracing is configured once per serialization, not per AST node.
    debug_marshal: bool,

    /// The output buffer containing encoded data
    buffer: Vec<u8>,

    /// Maps StrIdx to object counter (for arena-based string sharing)
    /// Same StrIdx = same object, will be shared in output
    str_idx_table: HashMap<StrIdx, u32>,

    /// Maps PosIdx to object counter (for arena-based Position sharing)
    /// Same index = same object, will be shared in output
    position_idx_table: HashMap<PosIdx, u32>,

    /// Maps LocIdx to object counter (for arena-based Location sharing)
    /// Same index = same object, will be shared in output
    location_idx_table: HashMap<LocIdx, u32>,

    /// Maps LidentIdx to object counter (for arena-based Longident sharing)
    /// Same index = same object, will be shared in output
    lident_idx_table: HashMap<LidentIdx, u32>,

    /// Shares selected `Longident::Lident` wrapper blocks across distinct LidentIdx.
    ///
    /// OCaml sometimes reuses the same `Lident "string"` wrapper object while still
    /// rebuilding enclosing core_type records. We track these by StrIdx so wrapper
    /// sharing can match without forcing outer core_type sharing.
    string_lident_table: HashMap<StrIdx, u32>,

    /// Maps shareable Lident StrIdx to object counter (for value-based sharing).
    /// Used to share common prefixes like `Spice` that are reused by internal PPX.
    longident_lident_table: HashMap<StrIdx, u32>,

    /// Maps shareable Longident values to object counter (for value-based sharing).
    /// Used to share repeated `Spice.*` longidents constructed as constants.
    longident_value_table: HashMap<Longident, u32>,

    /// Maps the contents of `Some(s)` string options to object counter (for
    /// content-based sharing). This enables sharing of common delimiter values
    /// like Some("js"); `None` is an immediate and never shared.
    option_string_table: HashMap<String, u32>,

    /// Maps string values to object counter (for content-based sharing)
    /// Used for shared constant strings in PPX output (e.g. spice keys, delimiters).
    string_value_table: HashMap<String, u32>,

    /// Maps ArityIdx values to object counter (for index-based sharing)
    /// Same ArityIdx = same arity value in the arena = shared in output
    /// This matches OCaml's constant folding where `Some 1` literals are physically shared
    arity_idx_table: HashMap<ArityIdx, u32>,

    /// Maps (StrIdx, LocIdx) pairs to object counter (for string_loc record sharing).
    /// This enables sharing of `{txt; loc}` records in PPX-generated code where the
    /// same label record is used in multiple places (e.g., Otag label and Labelled arg label
    /// in %obj transformations). Uses arena indices for identity-based sharing.
    string_loc_table: HashMap<(StrIdx, LocIdx), u32>,

    /// Maps (LidentIdx, LocIdx) pairs to object counter (for `Longident.t loc` sharing).
    /// OCaml may reuse the same located longident record (e.g. in nested `Pexp_open`
    /// rewrites), so we mirror that pointer sharing by keying on arena indices.
    lident_loc_table: HashMap<(LidentIdx, LocIdx), u32>,

    /// Maps (label_tag, StrIdx, LocIdx) to object counter for sharing arg_label wrappers.
    /// label_tag: 0=Labelled, 1=Optional.
    arg_label_table: HashMap<(u8, StrIdx, LocIdx), u32>,

    /// Maps (LidentIdx, LocIdx) to object counter for sharing `Pmod_ident` wrappers.
    pmod_ident_table: HashMap<(LidentIdx, LocIdx), u32>,

    /// Maps (StrIdx, LocIdx) to object counter for sharing attribute tuples
    /// `(name_with_loc, payload)` in contexts where OCaml reuses them.
    attr_tuple_table: HashMap<(StrIdx, LocIdx), u32>,

    /// Maps value-description identity to marshaled object indices for `(pval_name, pval_type)`.
    /// In no-inline external wrappers, OCaml record updates preserve physical sharing of these
    /// fields between the structure primitive and the generated signature value description.
    vd_name_type_table: HashMap<(StrIdx, LocIdx, LocIdx), (u32, u32)>,

    /// Maps (StrIdx, LocIdx) to object counter for sharing entire attribute lists
    /// of the form `[(name_with_loc, PStr [])]`. OCaml shares these because
    /// module-level `let` bindings like `let ternary_attr = (...)` create a single
    /// physical object that is reused everywhere. The list `[attr]` is also shared
    /// because OCaml's CSE merges identical heap allocations.
    singleton_attr_list_table: HashMap<(StrIdx, LocIdx), u32>,

    /// Maps (tyvar_name, LocIdx) to object counter for sharing Ptyp_var core_types.
    /// In OCaml's `from_labels`, the same tyvar CoreType object is physically shared
    /// between Otag fields and Labelled args. We replicate this by sharing CoreTypes
    /// with Ptyp_var desc, empty attributes, and matching (name, loc) pairs.
    tyvar_core_type_table: TyvarShareTable,

    /// Maps (tyvar_name, LocIdx) to object counter for sharing Ptyp_var name strings.
    /// Even when OCaml rebuilds surrounding core_type wrappers, it can still reuse
    /// the same underlying tyvar name string object for the same source location.
    tyvar_name_table: TyvarShareTable,

    /// Maps Location values to object counter for content-based sharing.
    /// In OCaml, Location.none is a module-level let binding, so all references
    /// to it share the same physical pointer. Other locations that happen to be
    /// identical (e.g., from parser reuse) also share. We replicate this by
    /// sharing Location values with identical content.
    location_value_table: HashMap<Location, u32>,

    /// Maps Position values to object counter for content-based sharing.
    /// In OCaml, when loc_start == loc_end (same pointer), the marshal format
    /// emits a shared reference for the second occurrence. We replicate this
    /// by sharing Position values with identical content.
    position_value_table: HashMap<Position, u32>,

    /// Shared object indices for empty PStr payloads (`PStr []`) by sharing group.
    pstr_empty_table: [Option<u32>; EmptyPayloadShareKind::COUNT],

    /// Shared object indices for `pval_prim` single-element lists by sharing group.
    prim_list_table: [Option<u32>; PrimListShareKind::COUNT],

    /// Depth counter for JSX context while marshalling.
    jsx_depth: u32,

    /// Depth counter for extension expression context while marshalling.
    extension_depth: u32,

    /// Depth counter for `%external` expression rewrite context.
    external_ext_depth: u32,

    /// Depth counter for expression pack context (`Pexp_pack`).
    pack_depth: u32,

    /// Depth counter for expression-level `Pexp_letmodule` context.
    letmodule_expr_depth: u32,

    /// Depth counter for `Pmty_typeof` module-type context.
    module_typeof_depth: u32,

    /// Shared object indices for simple builtin core_types created via Ast_literal.No_loc.
    /// These are `Ptyp_constr` with no args, Location.none, and empty attributes.
    simple_core_type_table: HashMap<LidentIdx, u32>,

    /// Stack of shared list object indices for `[@res.template]` attribute lists
    /// inside %raw expansions. OCaml reuses the same list object when the
    /// payload expression is reused, so we mirror that by sharing the list
    /// within the raw expansion scope.
    raw_template_attr_list_stack: Vec<Option<u32>>,

    /// Shared object indices for `%external` raw letmodule expressions by location.
    /// OCaml's `%external` rewrite reuses one `raw_exp` node in both `typeof(raw_exp)`
    /// and the `else raw_exp` branch; Rust clones that node, so we restore sharing
    /// here using the extension location as identity.
    /// Only consulted inside one `%external` expression and cleared when it
    /// ends, so unrelated raw expansions at the same location (jsConverter's
    /// `_map` and `_revMap`) are never merged.
    raw_expansion_expr_table: HashMap<LocIdx, u32>,

    /// Shared object index for the canonical `internal.expansive` attribute tuple.
    /// OCaml prepends `Ast_attributes.internal_expansive` in raw/ffi rewrites,
    /// and that tuple object is reused across occurrences.
    internal_expansive_attr_tuple: Option<u32>,

    /// Optional reference to ParseArena for LocIdx marshalling.
    /// Set via `set_arena()` before marshalling AST with LocIdx fields.
    arena: Option<&'a ParseArena>,

    /// Current expression index being marshalled.
    /// Set by `ExprIdx` marshalling so expression-desc writers can consult sparse side tables.
    current_expr_idx: Option<ExprIdx>,

    /// Stack of owning case-list expressions and the next case index to serialize.
    /// Used to resolve sparse `Case.pc_guard` side-table entries while marshalling.
    case_owner_stack: Vec<(ExprIdx, usize)>,

    /// Current object counter (incremented each time we record a sharable object)
    obj_counter: u32,

    /// Size in 32-bit words (for header)
    size_32: u32,

    /// Size in 64-bit words (for header)
    size_64: u32,
}

impl Default for MarshalWriter<'_> {
    fn default() -> Self {
        Self::new()
    }
}

impl<'a> MarshalWriter<'a> {
    /// Create a new MarshalWriter
    pub fn new() -> Self {
        Self::with_capacity(4096)
    }

    /// Create a new MarshalWriter with expected capacity
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            debug_marshal: std::env::var("DEBUG_MARSHAL").is_ok(),
            buffer: Vec::with_capacity(capacity),
            str_idx_table: HashMap::new(),
            position_idx_table: HashMap::new(),
            location_idx_table: HashMap::new(),
            lident_idx_table: HashMap::new(),
            string_lident_table: HashMap::new(),
            longident_lident_table: HashMap::new(),
            longident_value_table: HashMap::new(),
            option_string_table: HashMap::new(),
            string_value_table: HashMap::new(),
            arity_idx_table: HashMap::new(),

            string_loc_table: HashMap::new(),
            lident_loc_table: HashMap::new(),
            arg_label_table: HashMap::new(),
            pmod_ident_table: HashMap::new(),
            attr_tuple_table: HashMap::new(),
            vd_name_type_table: HashMap::new(),
            singleton_attr_list_table: HashMap::new(),
            tyvar_core_type_table: TyvarShareTable::default(),
            tyvar_name_table: TyvarShareTable::default(),

            location_value_table: HashMap::new(),
            position_value_table: HashMap::new(),

            pstr_empty_table: [None; EmptyPayloadShareKind::COUNT],
            prim_list_table: [None; PrimListShareKind::COUNT],
            jsx_depth: 0,
            extension_depth: 0,
            external_ext_depth: 0,
            pack_depth: 0,
            letmodule_expr_depth: 0,
            module_typeof_depth: 0,
            simple_core_type_table: HashMap::new(),
            raw_template_attr_list_stack: Vec::new(),
            raw_expansion_expr_table: HashMap::new(),
            internal_expansive_attr_tuple: None,

            arena: None,
            current_expr_idx: None,
            case_owner_stack: Vec::new(),
            obj_counter: 0,
            size_32: 0,
            size_64: 0,
        }
    }

    /// Set the ParseArena to use for LocIdx marshalling.
    /// Must be called before marshalling AST with LocIdx fields.
    ///
    pub fn set_arena(&mut self, arena: &'a ParseArena) {
        self.arena = Some(arena);
    }

    /// Get the arena reference, panics if not set.
    pub fn get_arena(&self) -> &'a ParseArena {
        self.arena
            .expect("MarshalWriter::set_arena must be called before marshalling LocIdx")
    }

    #[inline]
    pub fn with_current_expr_idx<R>(
        &mut self,
        idx: ExprIdx,
        f: impl FnOnce(&mut MarshalWriter<'a>) -> R,
    ) -> R {
        let prev = self.current_expr_idx;
        self.current_expr_idx = Some(idx);
        let result = f(self);
        self.current_expr_idx = prev;
        result
    }

    #[inline]
    pub fn current_expr_idx(&self) -> Option<ExprIdx> {
        self.current_expr_idx
    }

    #[inline]
    pub fn enter_case_owner(&mut self, owner: ExprIdx) {
        self.case_owner_stack.push((owner, 0));
    }

    #[inline]
    pub fn exit_case_owner(&mut self) {
        self.case_owner_stack.pop();
    }

    #[inline]
    pub fn next_case_owner_index(&mut self) -> Option<(ExprIdx, usize)> {
        if let Some((owner, next_idx)) = self.case_owner_stack.last_mut() {
            let case_idx = *next_idx;
            *next_idx += 1;
            Some((*owner, case_idx))
        } else {
            None
        }
    }

    #[inline]
    pub fn enter_jsx(&mut self) {
        self.jsx_depth += 1;
    }

    #[inline]
    pub fn exit_jsx(&mut self) {
        self.jsx_depth = self.jsx_depth.saturating_sub(1);
    }

    #[inline]
    pub fn in_jsx(&self) -> bool {
        self.jsx_depth > 0
    }

    #[inline]
    pub fn enter_extension(&mut self) {
        self.extension_depth += 1;
    }

    #[inline]
    pub fn exit_extension(&mut self) {
        self.extension_depth = self.extension_depth.saturating_sub(1);
    }

    #[inline]
    pub fn in_extension(&self) -> bool {
        self.extension_depth > 0
    }

    #[inline]
    pub fn enter_external_ext(&mut self) {
        self.external_ext_depth += 1;
    }

    #[inline]
    pub fn exit_external_ext(&mut self) {
        self.external_ext_depth = self.external_ext_depth.saturating_sub(1);
        if self.external_ext_depth == 0 {
            // The shared `raw_exp` node belongs to one `%external` rewrite;
            // other raw expansions at the same location are distinct values.
            self.raw_expansion_expr_table.clear();
        }
    }

    #[inline]
    pub fn in_external_ext(&self) -> bool {
        self.external_ext_depth > 0
    }

    #[inline]
    pub fn enter_pack(&mut self) {
        self.pack_depth += 1;
    }

    #[inline]
    pub fn exit_pack(&mut self) {
        self.pack_depth = self.pack_depth.saturating_sub(1);
    }

    #[inline]
    pub fn in_pack(&self) -> bool {
        self.pack_depth > 0
    }

    #[inline]
    pub fn enter_letmodule_expr(&mut self) {
        self.letmodule_expr_depth += 1;
    }

    #[inline]
    pub fn exit_letmodule_expr(&mut self) {
        self.letmodule_expr_depth = self.letmodule_expr_depth.saturating_sub(1);
    }

    #[inline]
    pub fn in_letmodule_expr(&self) -> bool {
        self.letmodule_expr_depth > 0
    }

    #[inline]
    pub fn enter_module_typeof(&mut self) {
        self.module_typeof_depth += 1;
    }

    #[inline]
    pub fn exit_module_typeof(&mut self) {
        self.module_typeof_depth = self.module_typeof_depth.saturating_sub(1);
    }

    #[inline]
    pub fn in_module_typeof(&self) -> bool {
        self.module_typeof_depth > 0
    }

    #[inline]
    pub fn enter_raw_expansion(&mut self) {
        self.raw_template_attr_list_stack.push(None);
    }

    #[inline]
    pub fn exit_raw_expansion(&mut self) {
        self.raw_template_attr_list_stack.pop();
    }

    #[inline]
    pub fn in_raw_expansion(&self) -> bool {
        !self.raw_template_attr_list_stack.is_empty()
    }

    #[inline]
    pub fn raw_template_attr_list(&self) -> Option<u32> {
        self.raw_template_attr_list_stack.last().copied().flatten()
    }

    #[inline]
    pub fn set_raw_template_attr_list(&mut self, obj_idx: u32) {
        if let Some(slot) = self.raw_template_attr_list_stack.last_mut() {
            if slot.is_none() {
                *slot = Some(obj_idx);
            }
        }
    }

    #[inline]
    pub fn raw_expansion_expr(&self, loc: LocIdx) -> Option<u32> {
        self.raw_expansion_expr_table.get(&loc).copied()
    }

    #[inline]
    pub fn set_raw_expansion_expr(&mut self, loc: LocIdx, obj_idx: u32) {
        self.raw_expansion_expr_table.entry(loc).or_insert(obj_idx);
    }

    #[inline]
    pub fn internal_expansive_attr_tuple(&self) -> Option<u32> {
        self.internal_expansive_attr_tuple
    }

    #[inline]
    pub fn set_internal_expansive_attr_tuple(&mut self, obj_idx: u32) {
        if self.internal_expansive_attr_tuple.is_none() {
            self.internal_expansive_attr_tuple = Some(obj_idx);
        }
    }

    #[inline]
    pub(crate) fn simple_core_type_table_get(&self, key: &LidentIdx) -> Option<&u32> {
        self.simple_core_type_table.get(key)
    }

    #[inline]
    pub(crate) fn simple_core_type_table_insert(&mut self, key: LidentIdx, obj_idx: u32) {
        self.simple_core_type_table.insert(key, obj_idx);
    }

    /// Get the current object counter value
    pub fn obj_counter(&self) -> u32 {
        self.obj_counter
    }

    /// Reset the writer state for reuse.
    ///
    /// Rebuilds every sharing table from scratch so no back-reference can leak
    /// into the next stream; only the output buffer allocation and the arena
    /// reference are kept.
    pub fn reset(&mut self) {
        let mut buffer = std::mem::take(&mut self.buffer);
        buffer.clear();
        let arena = self.arena;
        *self = Self {
            buffer,
            arena,
            ..Self::with_capacity(0)
        };
    }

    // ========== Low-level byte writing ==========

    /// Write a single byte
    #[inline]
    pub fn write_u8(&mut self, b: u8) {
        self.buffer.push(b);
    }

    /// Write an i8 (as one byte, two's complement)
    #[inline]
    pub fn write_i8(&mut self, n: i8) {
        self.buffer.push(n as u8);
    }

    /// Write a big-endian i16
    #[inline]
    pub fn write_i16_be(&mut self, n: i16) {
        self.buffer.push((n >> 8) as u8);
        self.buffer.push(n as u8);
    }

    /// Write a big-endian u16
    #[inline]
    pub fn write_u16_be(&mut self, n: u16) {
        self.buffer.push((n >> 8) as u8);
        self.buffer.push(n as u8);
    }

    /// Write a big-endian i32
    #[inline]
    pub fn write_i32_be(&mut self, n: i32) {
        self.buffer.push((n >> 24) as u8);
        self.buffer.push((n >> 16) as u8);
        self.buffer.push((n >> 8) as u8);
        self.buffer.push(n as u8);
    }

    /// Write a big-endian u32
    #[inline]
    pub fn write_u32_be(&mut self, n: u32) {
        self.buffer.push((n >> 24) as u8);
        self.buffer.push((n >> 16) as u8);
        self.buffer.push((n >> 8) as u8);
        self.buffer.push(n as u8);
    }

    /// Write a big-endian i64
    #[inline]
    pub fn write_i64_be(&mut self, n: i64) {
        self.buffer.push((n >> 56) as u8);
        self.buffer.push((n >> 48) as u8);
        self.buffer.push((n >> 40) as u8);
        self.buffer.push((n >> 32) as u8);
        self.buffer.push((n >> 24) as u8);
        self.buffer.push((n >> 16) as u8);
        self.buffer.push((n >> 8) as u8);
        self.buffer.push(n as u8);
    }

    /// Write a big-endian u64
    #[inline]
    #[allow(dead_code)]
    pub fn write_u64_be(&mut self, n: u64) {
        self.buffer.push((n >> 56) as u8);
        self.buffer.push((n >> 48) as u8);
        self.buffer.push((n >> 40) as u8);
        self.buffer.push((n >> 32) as u8);
        self.buffer.push((n >> 24) as u8);
        self.buffer.push((n >> 16) as u8);
        self.buffer.push((n >> 8) as u8);
        self.buffer.push(n as u8);
    }

    /// Write raw bytes
    #[inline]
    pub fn write_bytes(&mut self, bytes: &[u8]) {
        self.buffer.extend_from_slice(bytes);
    }

    // ========== Marshal value encoding ==========

    /// Write an integer in Marshal format
    ///
    /// Uses the most compact encoding:
    /// - 0-63: single byte (PREFIX_SMALL_INT | n)
    /// - -128 to 127: CODE_INT8 + 1 byte
    /// - -32768 to 32767: CODE_INT16 + 2 bytes
    /// - -2^30 to 2^30-1: CODE_INT32 + 4 bytes
    /// - larger: CODE_INT64 + 8 bytes
    pub fn write_int(&mut self, n: i64) {
        if (0..0x40).contains(&n) {
            // Small int: single byte 0x40 | n
            self.write_u8(PREFIX_SMALL_INT + (n as u8));
        } else if (-128..128).contains(&n) {
            self.write_u8(CODE_INT8);
            self.write_i8(n as i8);
        } else if (-32768..32768).contains(&n) {
            self.write_u8(CODE_INT16);
            self.write_i16_be(n as i16);
        } else if (-(1 << 30)..(1 << 30)).contains(&n) {
            self.write_u8(CODE_INT32);
            self.write_i32_be(n as i32);
        } else {
            self.write_u8(CODE_INT64);
            self.write_i64_be(n);
        }
    }

    /// Write an OCaml `int32` custom value (`Marshal.to_string (Int32.t)`).
    ///
    /// Payload format:
    /// - CODE_CUSTOM_FIXED (0x19)
    /// - custom identifier "_i\\0"
    /// - 4-byte big-endian int32 payload
    pub fn write_custom_int32(&mut self, n: i32) {
        self.write_u8(CODE_CUSTOM_FIXED);
        self.write_bytes(b"_i\0");
        self.write_i32_be(n);

        // Int32 custom block footprint from OCaml marshal headers.
        self.size_32 += 3;
        self.size_64 += 3;
        self.obj_counter += 1;
    }

    /// Write a string in Marshal format
    ///
    /// Uses the most compact encoding:
    /// - length 0-31: PREFIX_SMALL_STRING | length, then string bytes
    /// - length 32-255: CODE_STRING8 + 1 byte length, then string bytes
    /// - length 256+: CODE_STRING32 + 4 byte length, then string bytes
    ///
    /// Note: This increments the object counter AFTER writing, as every string is a heap object.
    /// The object is assigned the index that obj_counter had before this call.
    pub fn write_string(&mut self, s: &[u8]) {
        let len = s.len();
        if len < 0x20 {
            // Small string: PREFIX_SMALL_STRING | len
            self.write_u8(PREFIX_SMALL_STRING + (len as u8));
        } else if len < 0x100 {
            self.write_u8(CODE_STRING8);
            self.write_u8(len as u8);
        } else if (len as u64) < 0x100000000u64 {
            self.write_u8(CODE_STRING32);
            self.write_u32_be(len as u32);
        } else {
            // Strings > 4GB are not supported
            panic!("String too large for Marshal format: {} bytes", len);
        }
        self.write_bytes(s);

        // Update size counters for string allocation
        // OCaml strings: 1 header word + ceil((len + 1) / word_size) data words
        // The +1 is for the null terminator padding
        self.size_32 += 1 + ((len as u32 + 4) / 4);
        self.size_64 += 1 + ((len as u32 + 8) / 8);

        // Increment object counter AFTER writing (OCaml assigns index then increments)
        self.obj_counter += 1;
    }

    /// Write a string from a Rust &str, converting from UTF-8 to Latin-1.
    ///
    /// The parser reads source files as Latin-1 (each byte → char), so string
    /// content from source uses chars in the 0-255 range stored as UTF-8.
    /// This method converts back to Latin-1 (each char → byte) to match OCaml's
    /// byte-level string representation.
    ///
    /// For raw binary data (e.g. pval_prim), use write_string() directly instead.
    pub fn write_str(&mut self, s: &str) {
        if s.is_ascii() {
            self.write_string(s.as_bytes());
            return;
        }
        let latin1_bytes: Vec<u8> = s.chars().map(|c| c as u8).collect();
        self.write_string(&latin1_bytes);
    }

    /// Write a string with content-based sharing.
    ///
    /// This is used for PPX-generated constant strings that are physically shared
    /// in OCaml (e.g. spice key literals, string delimiters). Sharing by value
    /// here matches OCaml's pointer-based sharing of those literals.
    pub fn write_str_value_shared(&mut self, s: &str) {
        if let Some(&obj_idx) = self.string_value_table.get(s) {
            let d = self.obj_counter - obj_idx;
            self.write_shared_ref(d);
            return;
        }

        // Record the object index BEFORE writing
        let obj_idx = self.obj_counter;
        self.write_str(s);
        self.string_value_table.insert(s.to_string(), obj_idx);
    }

    /// Write a string by StrIdx with arena-based sharing.
    ///
    /// If a string with the same StrIdx has been written before, writes a shared
    /// reference. Otherwise looks up the string in the arena and writes it.
    ///
    /// Same StrIdx = same object, will be shared in output.
    /// This matches OCaml's pointer-based sharing for interned strings.
    pub fn write_str_idx(&mut self, idx: StrIdx) {
        // Check if this string index was already written
        if let Some(&obj_idx) = self.str_idx_table.get(&idx) {
            let d = self.obj_counter - obj_idx;
            self.write_shared_ref(d);
            return;
        }

        // Record the object index BEFORE writing
        let obj_idx = self.obj_counter;

        let arena = self.get_arena();
        let s: &'a str = arena.get_string(idx);
        if arena.is_shareable_literal(s) && !self.string_value_table.contains_key(s) {
            self.string_value_table.insert(s.to_owned(), obj_idx);
        }
        // Latin-1 conversion (see `write_str`): source strings are read as Latin-1,
        // so non-ASCII chars (0x80-0xFF) are written back as single bytes.
        self.write_str(s);

        // Record for future sharing
        self.str_idx_table.insert(idx, obj_idx);
    }

    // ========== Arena-based position/location methods ==========

    /// Write a Position by arena index with sharing.
    ///
    /// If a Position with the same PosIdx has been written before, writes a shared
    /// reference. Otherwise looks up the position in the arena and writes it.
    ///
    /// Same index = same object, will be shared in output.
    pub fn write_pos_idx(&mut self, idx: PosIdx) -> bool {
        // Check if this position index was already written
        if let Some(&obj_idx) = self.position_idx_table.get(&idx) {
            let d = self.obj_counter - obj_idx;
            self.write_shared_ref(d);
            return false;
        }

        let pos = self.get_arena().get_position(idx);

        // Record the object index BEFORE writing
        let obj_idx = self.obj_counter;

        // Write the Position block
        self.write_block_header(0, 4);
        // Use write_str_idx for file name to enable sharing
        self.write_str_idx(pos.file_name);
        self.write_int(pos.line as i64);
        self.write_int(pos.bol as i64);
        self.write_int(pos.cnum as i64);

        // Record for future sharing
        self.position_idx_table.insert(idx, obj_idx);

        true
    }

    /// Write a Location by arena index with sharing.
    ///
    /// If a Location with the same LocIdx has been written before, writes a shared
    /// reference. Otherwise looks up the location in the arena and writes it as
    /// a new block.
    ///
    /// This matches OCaml's behavior where:
    /// - Same pointer = same object, will be shared in output
    /// - The positions within are also shared via PosIdx
    pub fn write_loc_idx(&mut self, idx: LocIdx) {
        // Check if this location index was already written
        if let Some(&obj_idx) = self.location_idx_table.get(&idx) {
            let d = self.obj_counter - obj_idx;
            self.write_shared_ref(d);
            return;
        }

        let loc = self.get_arena().get_location(idx);

        // Record the object index BEFORE writing
        let obj_idx = self.obj_counter;

        // Write the Location block
        self.write_block_header(0, 3);
        // Write start and end positions (with sharing by their indices)
        self.write_pos_idx(loc.loc_start);
        self.write_pos_idx(loc.loc_end);
        self.write_int(if loc.loc_ghost { 1 } else { 0 });

        // Record for future sharing
        self.location_idx_table.insert(idx, obj_idx);
    }

    /// Write a Position value with content-based sharing.
    ///
    /// If a Position with the same content (file_name, line, bol, cnum) has been
    /// written before, writes a shared reference. Otherwise writes it fresh and
    /// records it for future sharing.
    ///
    /// This matches OCaml's behavior where identical Position values (e.g.,
    /// loc_start == loc_end for the same location) are the same physical pointer
    /// and get shared in marshal output.
    pub fn write_position_shared(&mut self, pos: &Position) {
        if let Some(&obj_idx) = self.position_value_table.get(pos) {
            let d = self.obj_counter - obj_idx;
            self.write_shared_ref(d);
            return;
        }

        let obj_idx = self.obj_counter;
        self.write_block_header(0, 4);
        self.write_str_idx(pos.file_name);
        self.write_int(pos.line as i64);
        self.write_int(pos.bol as i64);
        self.write_int(pos.cnum as i64);

        self.position_value_table.insert(*pos, obj_idx);
    }

    /// Write a Location value with content-based sharing.
    ///
    /// If a Location with the same content has been written before, writes a
    /// shared reference. Otherwise writes it fresh and records it for future sharing.
    ///
    /// This matches OCaml's behavior where Location.none is a module-level let
    /// binding and all references share the same physical pointer. Other identical
    /// locations (e.g., from parser reuse) also share.
    ///
    /// Positions within the Location are also shared via content-based sharing,
    /// matching OCaml's behavior where loc_start and loc_end can be the same
    /// physical pointer.
    pub fn write_location_shared(&mut self, loc: &Location) {
        if let Some(&obj_idx) = self.location_value_table.get(loc) {
            let d = self.obj_counter - obj_idx;
            self.write_shared_ref(d);
            return;
        }

        let obj_idx = self.obj_counter;
        self.write_block_header(0, 3);
        self.write_position_shared(&loc.loc_start);
        self.write_position_shared(&loc.loc_end);
        self.write_int(if loc.loc_ghost { 1 } else { 0 });

        self.location_value_table.insert(*loc, obj_idx);
    }

    /// Write a `{txt; loc}` string_loc record with identity-based sharing.
    ///
    /// This writes a `block(0,2) -> [string, loc]` record and tracks it by
    /// `(StrIdx, LocIdx)` for sharing. If the same pair has been written
    /// before, writes a CODE_SHARED reference instead.
    ///
    /// This matches OCaml's pointer-identity sharing where the same `{txt; loc}`
    /// record object is used in multiple places (e.g., in %obj PPX where the
    /// same label record appears in both Otag and Labelled).
    ///
    /// When `register` is true, registers the record in the sharing table
    /// so future writes with the same indices can share it.
    /// When `register` is false, only checks the table for an existing entry
    /// (used by ArgLabel::Labelled/Optional which should only share with
    /// previously-registered Otag labels, not create new sharing entries).
    pub fn write_string_loc_shared(&mut self, txt: StrIdx, loc: LocIdx, register: bool) {
        if self
            .get_arena()
            .is_shareable_literal(self.get_arena().get_string(txt))
        {
            // For shareable literals (spice), avoid sharing the wrapper.
            self.write_block_header(0, 2);
            self.write_str_idx(txt);
            self.write_loc_idx(loc);
            return;
        }

        let key = (txt, loc);

        // Check if this string_loc pair was already written
        if let Some(&obj_idx) = self.string_loc_table.get(&key) {
            let d = self.obj_counter - obj_idx;
            self.write_shared_ref(d);
            return;
        }

        // Record the object index BEFORE writing
        let obj_idx = self.obj_counter;

        // Write the {txt; loc} block
        self.write_block_header(0, 2);
        self.write_str_idx(txt);
        self.write_loc_idx(loc);

        // Record for future sharing only if registering
        if register {
            self.string_loc_table.insert(key, obj_idx);
        }
    }

    /// Write a `Longident.t loc` record with identity-based sharing.
    ///
    /// Encodes as `block(0,2) -> [longident, loc]`, sharing by `(LidentIdx, LocIdx)`.
    pub fn write_lident_loc_shared(&mut self, txt: LidentIdx, loc: LocIdx) {
        let key = (txt, loc);
        if let Some(&obj_idx) = self.lident_loc_table.get(&key) {
            let d = self.obj_counter - obj_idx;
            self.write_shared_ref(d);
            return;
        }

        let obj_idx = self.obj_counter;
        self.write_block_header(0, 2);
        self.write_lident_idx(txt);
        self.write_loc_idx(loc);
        self.lident_loc_table.insert(key, obj_idx);
    }

    /// Look up an entry in the singleton attribute list sharing table.
    pub fn singleton_attr_list_table_get(&self, key: &(StrIdx, LocIdx)) -> Option<&u32> {
        self.singleton_attr_list_table.get(key)
    }

    /// Insert an entry into the singleton attribute list sharing table.
    pub fn singleton_attr_list_table_insert(&mut self, key: (StrIdx, LocIdx), obj_idx: u32) {
        self.singleton_attr_list_table.insert(key, obj_idx);
    }

    /// Look up an arg_label wrapper object index.
    pub fn arg_label_table_get(&self, key: &(u8, StrIdx, LocIdx)) -> Option<&u32> {
        self.arg_label_table.get(key)
    }

    /// Insert an arg_label wrapper object index.
    pub fn arg_label_table_insert(&mut self, key: (u8, StrIdx, LocIdx), obj_idx: u32) {
        self.arg_label_table.insert(key, obj_idx);
    }

    /// Look up a `Pmod_ident` wrapper object index.
    pub fn pmod_ident_table_get(&self, key: &(LidentIdx, LocIdx)) -> Option<&u32> {
        self.pmod_ident_table.get(key)
    }

    /// Insert a `Pmod_ident` wrapper object index.
    pub fn pmod_ident_table_insert(&mut self, key: (LidentIdx, LocIdx), obj_idx: u32) {
        self.pmod_ident_table.insert(key, obj_idx);
    }

    /// Look up an attribute tuple `(name_with_loc, payload)` object index.
    pub fn attr_tuple_table_get(&self, key: &(StrIdx, LocIdx)) -> Option<&u32> {
        self.attr_tuple_table.get(key)
    }

    /// Insert an attribute tuple `(name_with_loc, payload)` object index.
    pub fn attr_tuple_table_insert(&mut self, key: (StrIdx, LocIdx), obj_idx: u32) {
        self.attr_tuple_table.insert(key, obj_idx);
    }

    /// Look up cached value-description `(pval_name, pval_type)` object indices.
    pub fn vd_name_type_table_get(&self, key: &(StrIdx, LocIdx, LocIdx)) -> Option<&(u32, u32)> {
        self.vd_name_type_table.get(key)
    }

    /// Insert value-description `(pval_name, pval_type)` object indices.
    pub fn vd_name_type_table_insert(&mut self, key: (StrIdx, LocIdx, LocIdx), value: (u32, u32)) {
        self.vd_name_type_table.insert(key, value);
    }

    /// Look up a `LocIdx` object index in the location sharing table.
    pub fn location_idx_table_get(&self, key: &LocIdx) -> Option<&u32> {
        self.location_idx_table.get(key)
    }

    /// Look up a tyvar core_type in the sharing table.
    /// Used to share Ptyp_var core_types from from_labels (handle_obj).
    pub fn tyvar_core_type_table_get(&self, name: &str, loc: LocIdx) -> Option<u32> {
        self.tyvar_core_type_table.get(name, loc)
    }

    /// Insert a tyvar core_type into the sharing table.
    pub fn tyvar_core_type_table_insert(&mut self, name: &str, loc: LocIdx, obj_idx: u32) {
        self.tyvar_core_type_table.insert(name, loc, obj_idx);
    }

    /// Write a Ptyp_var name string with sharing scoped by (name, location).
    ///
    /// OCaml can rebuild surrounding wrappers while preserving the same string
    /// object for a given tyvar source location. Keying by (name, LocIdx)
    /// mirrors that behavior without global value-based sharing.
    pub fn write_tyvar_name_shared(&mut self, name: &str, loc: LocIdx) {
        if let Some(obj_idx) = self.tyvar_name_table.get(name, loc) {
            let d = self.obj_counter - obj_idx;
            self.write_shared_ref(d);
            return;
        }

        let obj_idx = self.obj_counter;
        self.write_str(name);
        self.tyvar_name_table.insert(name, loc, obj_idx);
    }

    /// Write a Longident by arena index with sharing.
    ///
    /// If a Longident with the same LidentIdx has been written before, writes a shared
    /// reference. Otherwise looks up the longident in the arena and writes it.
    ///
    /// Same index = same object, will be shared in output.
    pub fn write_lident_idx(&mut self, idx: LidentIdx) -> bool {
        // Check if this longident index was already written
        if let Some(&obj_idx) = self.lident_idx_table.get(&idx) {
            let d = self.obj_counter - obj_idx;
            self.write_shared_ref(d);
            return false;
        }

        // Share selected `Lident` wrappers by StrIdx even when they come from
        // distinct LidentIdx allocations.
        let string_lident_key = {
            let arena = self.get_arena();
            let ppx_js = arena.ppx_js_str();
            match arena.get_longident(idx) {
                Longident::Lident(name_idx)
                    if *name_idx == ppx_js || arena.get_string(*name_idx) == "string" =>
                {
                    Some(*name_idx)
                }
                _ => None,
            }
        };
        if let Some(name_idx) = string_lident_key {
            if let Some(&obj_idx) = self.string_lident_table.get(&name_idx) {
                let d = self.obj_counter - obj_idx;
                self.write_shared_ref(d);
                self.lident_idx_table.insert(idx, obj_idx);
                return false;
            }
        }

        // Record the object index BEFORE writing. This remains the object index for
        // manually-special-cased Ldot constructions below.
        let mut obj_idx = self.obj_counter;

        // For Ldot nodes created via ParseArena::push_ldot*, preserve the original
        // prefix index identity instead of recursing by value. This mirrors OCaml's
        // pointer-sharing when transformations reuse a shared prefix value.
        let ldot_with_prefix_idx = {
            let arena = self.get_arena();
            match (arena.ldot_prefix_idx(idx), arena.get_longident(idx)) {
                (Some(prefix_idx), Longident::Ldot(_, name)) => Some((prefix_idx, *name)),
                _ => None,
            }
        };
        if let Some((prefix_idx, name)) = ldot_with_prefix_idx {
            self.write_ldot_with_prefix_idx(prefix_idx, name);
            self.lident_idx_table.insert(idx, obj_idx);
            if let Some(name_idx) = string_lident_key {
                self.string_lident_table.entry(name_idx).or_insert(obj_idx);
            }
            return true;
        }

        // Special-case static longidents that share prefix nodes in OCaml.
        let arena = self.get_arena();
        let static_prefix = if idx == arena.array_set_lid() || idx == arena.array_get_lid() {
            Some(arena.array_lident())
        } else if idx == arena.belt_array_concat_many_lid() {
            Some(arena.belt_array_lident())
        } else if idx == arena.belt_list_concat_many_lid() {
            Some(arena.belt_list_lident())
        } else if idx == arena.belt_array_lident() || idx == arena.belt_list_lident() {
            Some(arena.belt_lident())
        } else {
            None
        };

        let lid = arena.get_longident(idx);
        match (static_prefix, lid) {
            (Some(prefix), Longident::Ldot(_, name)) => {
                self.write_ldot_with_prefix_idx(prefix, *name);
            }
            _ => {
                // `write_longident` may return a shared object index for value-shared roots.
                obj_idx = self.write_longident(lid);
            }
        }

        self.lident_idx_table.insert(idx, obj_idx);
        if let Some(name_idx) = string_lident_key {
            self.string_lident_table.entry(name_idx).or_insert(obj_idx);
        }

        true
    }

    /// Write `Ldot(prefix, name)` where `prefix` is referenced by LidentIdx.
    fn write_ldot_with_prefix_idx(&mut self, prefix: LidentIdx, name: StrIdx) {
        self.write_block_header(1, 2);
        self.write_lident_idx(prefix);
        self.write_str_idx(name);
    }

    /// Write a Longident value directly (internal helper).
    /// This writes the structure without any index-based sharing.
    /// Uses StrIdx-based sharing for the string components.
    fn write_longident(&mut self, lid: &Longident) -> u32 {
        let obj_idx = self.obj_counter;
        match lid {
            Longident::Lident(s) => {
                let should_share_string_lident = {
                    let arena = self.get_arena();
                    *s == arena.ppx_js_str() || arena.get_string(*s) == "string"
                };
                if should_share_string_lident {
                    if let Some(&shared_idx) = self.string_lident_table.get(s) {
                        let d = self.obj_counter - shared_idx;
                        self.write_shared_ref(d);
                        return shared_idx;
                    }
                }
                if self.get_arena().is_longident_shareable_str(*s) {
                    if let Some(&shared_idx) = self.longident_lident_table.get(s) {
                        let d = self.obj_counter - shared_idx;
                        self.write_shared_ref(d);
                        return shared_idx;
                    }
                }
                self.write_block_header(0, 1);
                self.write_str_idx(*s);
                if should_share_string_lident {
                    self.string_lident_table.entry(*s).or_insert(obj_idx);
                }
                if self.get_arena().is_longident_shareable_str(*s) {
                    self.longident_lident_table.insert(*s, obj_idx);
                }
            }
            Longident::Ldot(prefix, name) => {
                if self.longident_is_shareable_root(prefix) {
                    if let Some(&shared_idx) = self.longident_value_table.get(lid) {
                        let d = self.obj_counter - shared_idx;
                        self.write_shared_ref(d);
                        return shared_idx;
                    }
                }
                self.write_block_header(1, 2);
                self.write_longident(prefix);
                self.write_str_idx(*name);
                if self.longident_is_shareable_root(prefix) {
                    self.longident_value_table.insert(lid.clone(), obj_idx);
                }
            }
            Longident::Lapply(func, arg) => {
                self.write_block_header(2, 2);
                self.write_longident(func);
                self.write_longident(arg);
            }
        }
        obj_idx
    }

    fn longident_is_shareable_root(&self, lid: &Longident) -> bool {
        match lid {
            Longident::Lident(s) => self.get_arena().is_longident_shareable_str(*s),
            Longident::Ldot(prefix, _) => self.longident_is_shareable_root(prefix),
            Longident::Lapply(_, _) => false,
        }
    }

    /// Write a block header in Marshal format
    ///
    /// Blocks represent OCaml heap objects: records, tuples, and variant constructors
    /// with data.
    ///
    /// - tag: the block tag (0-255, typically < 16 for user types)
    /// - size: number of fields in the block
    ///
    /// Uses compact encoding for small blocks (tag < 16, size < 8).
    ///
    /// Note: This increments the object counter AFTER writing, as every block is a heap object
    /// that can potentially be referenced by shared pointers. The object is assigned the
    /// index that obj_counter had before this call.
    pub fn write_block_header(&mut self, tag: u8, size: usize) {
        if tag < 16 && size < 8 {
            // Small block: PREFIX_SMALL_BLOCK + tag + (size << 4)
            // Bits 0-3: tag (0-15)
            // Bits 4-6: size (0-7)
            // Bit 7: always 1 (from PREFIX_SMALL_BLOCK = 0x80)
            self.write_u8(PREFIX_SMALL_BLOCK + tag + ((size as u8) << 4));
        } else {
            // Large block: header = (size << 10) | (color << 8) | tag
            // OCaml's Make_header(sz, tag, color) = (sz << 10) | (color << 8) | tag
            // OCaml's marshal uses color=3 (Caml_black) for marshaled blocks
            let header = ((size as u64) << 10) | (3u64 << 8) | (tag as u64);
            if header < (1u64 << 32) {
                self.write_u8(CODE_BLOCK32);
                self.write_u32_be(header as u32);
            } else {
                self.write_u8(CODE_BLOCK64);
                self.write_u64_be(header);
            }
        }

        // Update size counters for block allocation
        // Block: 1 header word + size data words
        self.size_32 += 1 + (size as u32);
        self.size_64 += 1 + (size as u32);

        // Increment object counter AFTER writing (OCaml assigns index then increments)
        self.obj_counter += 1;
    }

    /// Write a double (64-bit float) in Marshal format
    ///
    /// OCaml uses big-endian for floats on big-endian systems and little-endian
    /// on little-endian systems. Most modern systems are little-endian.
    pub fn write_double(&mut self, f: f64) {
        // Detect endianness at compile time
        #[cfg(target_endian = "little")]
        {
            self.write_u8(CODE_DOUBLE_LITTLE);
            self.write_bytes(&f.to_le_bytes());
        }
        #[cfg(target_endian = "big")]
        {
            self.write_u8(CODE_DOUBLE_BIG);
            self.write_bytes(&f.to_be_bytes());
        }

        // Update size counters for float allocation
        // Float: 1 header word + 1 double word (8 bytes) on 64-bit
        //        1 header word + 2 words on 32-bit
        self.size_32 += 1 + 2; // 32-bit: double is 2 words
        self.size_64 += 1 + 1; // 64-bit: double is 1 word
    }

    // ========== Sharing support ==========

    /// Write a shared reference
    pub fn write_shared_ref(&mut self, d: u32) {
        if d < 0x100 {
            self.write_u8(CODE_SHARED8);
            self.write_u8(d as u8);
        } else if d < 0x10000 {
            self.write_u8(CODE_SHARED16);
            self.write_u16_be(d as u16);
        } else {
            self.write_u8(CODE_SHARED32);
            self.write_u32_be(d);
        }
    }

    // ========== Finalization ==========

    /// Get the serialized data with Marshal header prepended
    ///
    /// Returns the complete Marshal output including:
    /// - Magic number (4 bytes)
    /// - Header (16 bytes)
    /// - Payload (encoded data)
    pub fn finish(&self) -> Vec<u8> {
        let data_len = self.buffer.len() as u32;

        let mut result = Vec::with_capacity(20 + self.buffer.len());

        // Magic number
        result.push((MAGIC_NUMBER_SMALL >> 24) as u8);
        result.push((MAGIC_NUMBER_SMALL >> 16) as u8);
        result.push((MAGIC_NUMBER_SMALL >> 8) as u8);
        result.push(MAGIC_NUMBER_SMALL as u8);

        // Data length
        result.push((data_len >> 24) as u8);
        result.push((data_len >> 16) as u8);
        result.push((data_len >> 8) as u8);
        result.push(data_len as u8);

        // Object count (number of objects that can be referenced by CODE_SHARED)
        let obj_count = self.obj_counter;
        result.push((obj_count >> 24) as u8);
        result.push((obj_count >> 16) as u8);
        result.push((obj_count >> 8) as u8);
        result.push(obj_count as u8);

        // Size on 32-bit platform (words)
        result.push((self.size_32 >> 24) as u8);
        result.push((self.size_32 >> 16) as u8);
        result.push((self.size_32 >> 8) as u8);
        result.push(self.size_32 as u8);

        // Size on 64-bit platform (words)
        result.push((self.size_64 >> 24) as u8);
        result.push((self.size_64 >> 16) as u8);
        result.push((self.size_64 >> 8) as u8);
        result.push(self.size_64 as u8);

        // Payload
        result.extend_from_slice(&self.buffer);

        result
    }

    /// The written value as a self-contained [`MarshalFragment`].
    pub fn fragment(&self) -> MarshalFragment {
        MarshalFragment {
            bytes: self.buffer.clone(),
            objects: self.obj_counter,
            size_32: self.size_32,
            size_64: self.size_64,
        }
    }

    /// Embed a fragment produced by another writer as the next value.
    pub fn write_fragment(&mut self, fragment: &MarshalFragment) {
        self.buffer.extend_from_slice(&fragment.bytes);
        self.obj_counter += fragment.objects;
        self.size_32 += fragment.size_32;
        self.size_64 += fragment.size_64;
    }

    /// Get just the payload without the header (for testing)
    pub fn payload(&self) -> &[u8] {
        &self.buffer
    }

    /// Get the current payload length
    pub fn payload_len(&self) -> usize {
        self.buffer.len()
    }

    /// Write an Option<String> with content-based sharing.
    ///
    /// This enables sharing of common delimiter values like Some("js") that appear
    /// multiple times in the AST. OCaml shares these because they're often the same
    /// pointer (constant values defined at module level).
    ///
    /// - None → integer 0
    /// - Some(s) → Block(tag=0, [s]) with content-based sharing
    pub fn write_option_string(&mut self, opt: Option<&str>) {
        let Some(s) = opt else {
            // None is encoded as integer 0, not a block, so no sharing needed
            self.write_int(0);
            return;
        };

        // OCaml does not reliably share Some("json") wrappers across contexts.
        // Avoid global content-based sharing for this delimiter.
        if s == "json" {
            self.write_block_header(0, 1);
            self.write_str(s);
            return;
        }

        // `%external` rewrites use Some("") delimiters with a shared inner string
        // but fresh wrapper allocation.
        if s.is_empty() && self.in_external_ext() {
            self.write_block_header(0, 1);
            if self.arena.is_some() {
                let empty_idx = self.get_arena().ppx_empty_str();
                self.write_str_idx(empty_idx);
            } else {
                self.write_str("");
            }
            return;
        }

        if self.get_arena().is_shareable_literal(s) {
            // For shareable literals (spice), share the string itself but
            // avoid sharing the wrapper to match OCaml's pointer behavior.
            self.write_block_header(0, 1);
            self.write_str_value_shared(s);
            return;
        }

        // Check if we've written this exact Some(s) before
        if let Some(&obj_idx) = self.option_string_table.get(s) {
            let d = self.obj_counter - obj_idx;
            self.write_shared_ref(d);
            return;
        }

        // Record the object index BEFORE writing the block
        let obj_idx = self.obj_counter;

        // Write Some(s) as Block(tag=0, [s])
        self.write_block_header(0, 1);
        self.write_str(s);

        // Record for future sharing
        self.option_string_table.insert(s.to_owned(), obj_idx);
    }

    /// Write a shared `PStr []` payload for a specific sharing group.
    ///
    /// `PStr []` may be shared in OCaml depending on its origin. We mirror that by
    /// sharing empty payloads within a group:
    /// - PStr [] → Block(tag=0, [int 0]) with sharing
    pub(crate) fn write_pstr_empty_shared(&mut self, kind: EmptyPayloadShareKind) {
        let idx = kind.as_index();
        if let Some(obj_idx) = self.pstr_empty_table[idx] {
            let d = self.obj_counter - obj_idx;
            self.write_shared_ref(d);
            return;
        }

        let obj_idx = self.obj_counter;
        self.write_block_header(0, 1);
        self.write_int(0); // empty list
        self.pstr_empty_table[idx] = Some(obj_idx);
    }

    /// Write a shared static `Prim_name "#raw_expr"` block.
    pub(crate) fn write_prim_list_shared(&mut self, kind: PrimListShareKind, prim: StrIdx) {
        let idx = kind.as_index();
        if let Some(obj_idx) = self.prim_list_table[idx] {
            let d = self.obj_counter - obj_idx;
            self.write_shared_ref(d);
            return;
        }

        let obj_idx = self.obj_counter;
        self.write_block_header(0, 1);
        self.write_str_idx(prim);
        self.prim_list_table[idx] = Some(obj_idx);
    }

    /// Write an ArityIdx with index-based sharing.
    ///
    /// OCaml shares arity values via CSE (Common Subexpression Elimination):
    /// - LITERAL `Some 1` in OCaml source code gets SHARED via constant folding
    /// - COMPUTED `Some arity` (where arity is a parameter) creates FRESH objects
    ///
    /// We replicate this by using ArityIdx for sharing:
    /// - Same ArityIdx → write shared reference to previously-written object
    /// - Different ArityIdx → write fresh object (even if same value)
    ///
    /// The key is that the parser uses:
    /// - `static_arity_1()` for literal paths → same ArityIdx, will be shared
    /// - `push_arity(Some(n))` for computed paths → different ArityIdx, won't share
    ///
    /// - ArityIdx pointing to None → integer 0 (not shared, always fresh)
    /// - ArityIdx pointing to Some(n) → Block(tag=0, [n]), shared by ArityIdx
    pub fn write_arity_idx(&mut self, idx: ArityIdx) {
        // Get the actual arity value from the arena
        let arity = self.arena.and_then(|arena| arena.get_arity(idx));

        match arity {
            None => {
                // None is encoded as integer 0, no sharing needed
                self.write_int(0);
            }
            Some(n) => {
                // Check if this ArityIdx was already written
                if let Some(&obj_idx) = self.arity_idx_table.get(&idx) {
                    // Write shared reference to previously-written object
                    // Distance = current counter - recorded index
                    let d = self.obj_counter - obj_idx;
                    self.write_shared_ref(d);
                } else {
                    // Record the object index BEFORE writing the block
                    let obj_idx = self.obj_counter;

                    // Write Some(n) as Block(tag=0, [n])
                    self.write_block_header(0, 1);
                    self.write_int(n as i64);

                    // Record for future sharing (same ArityIdx → same object)
                    self.arity_idx_table.insert(idx, obj_idx);
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_small_int_0() {
        let mut w = MarshalWriter::new();
        w.write_int(0);
        assert_eq!(w.payload(), &[0x40]); // PREFIX_SMALL_INT | 0
    }

    #[test]
    fn test_small_int_42() {
        let mut w = MarshalWriter::new();
        w.write_int(42);
        assert_eq!(w.payload(), &[0x6A]); // PREFIX_SMALL_INT | 42 = 0x40 | 0x2A
    }

    #[test]
    fn test_small_int_63() {
        let mut w = MarshalWriter::new();
        w.write_int(63);
        assert_eq!(w.payload(), &[0x7F]); // PREFIX_SMALL_INT | 63 = 0x40 | 0x3F
    }

    #[test]
    fn test_int8_positive() {
        let mut w = MarshalWriter::new();
        w.write_int(64);
        assert_eq!(w.payload(), &[CODE_INT8, 64]);
    }

    #[test]
    fn test_int8_negative() {
        let mut w = MarshalWriter::new();
        w.write_int(-1);
        assert_eq!(w.payload(), &[CODE_INT8, 0xFF]); // -1 as i8
    }

    #[test]
    fn test_int8_min() {
        let mut w = MarshalWriter::new();
        w.write_int(-128);
        assert_eq!(w.payload(), &[CODE_INT8, 0x80]); // -128 as i8
    }

    #[test]
    fn test_int16_positive() {
        let mut w = MarshalWriter::new();
        w.write_int(128);
        assert_eq!(w.payload(), &[CODE_INT16, 0x00, 0x80]);
    }

    #[test]
    fn test_int16_negative() {
        let mut w = MarshalWriter::new();
        w.write_int(-129);
        // -129 as i16 in big-endian: 0xFF7F
        assert_eq!(w.payload(), &[CODE_INT16, 0xFF, 0x7F]);
    }

    #[test]
    fn test_int32() {
        let mut w = MarshalWriter::new();
        w.write_int(32768);
        // 32768 as i32 in big-endian: 0x00008000
        assert_eq!(w.payload(), &[CODE_INT32, 0x00, 0x00, 0x80, 0x00]);
    }

    #[test]
    fn test_int32_large() {
        let mut w = MarshalWriter::new();
        w.write_int(1_000_000);
        // 1_000_000 = 0x000F4240
        assert_eq!(w.payload(), &[CODE_INT32, 0x00, 0x0F, 0x42, 0x40]);
    }

    #[test]
    fn test_int64() {
        let mut w = MarshalWriter::new();
        let n: i64 = (1i64 << 30) + 1; // Just over CODE_INT32 range
        w.write_int(n);
        assert_eq!(w.payload()[0], CODE_INT64);
        assert_eq!(w.payload().len(), 9); // 1 opcode + 8 bytes
    }

    #[test]
    fn test_small_string() {
        let mut w = MarshalWriter::new();
        w.write_string(b"hello");
        // PREFIX_SMALL_STRING | 5, then "hello"
        assert_eq!(w.payload(), &[0x25, b'h', b'e', b'l', b'l', b'o']);
    }

    #[test]
    fn test_small_string_empty() {
        let mut w = MarshalWriter::new();
        w.write_string(b"");
        assert_eq!(w.payload(), &[0x20]); // PREFIX_SMALL_STRING | 0
    }

    #[test]
    fn test_small_string_max() {
        let mut w = MarshalWriter::new();
        let s = vec![b'x'; 31]; // Max small string size
        w.write_string(&s);
        assert_eq!(w.payload()[0], 0x3F); // PREFIX_SMALL_STRING | 31
        assert_eq!(w.payload().len(), 32); // 1 + 31
    }

    #[test]
    fn test_string8() {
        let mut w = MarshalWriter::new();
        let s = vec![b'x'; 32]; // Just over small string limit
        w.write_string(&s);
        assert_eq!(w.payload()[0], CODE_STRING8);
        assert_eq!(w.payload()[1], 32);
        assert_eq!(w.payload().len(), 34); // 1 opcode + 1 len + 32 data
    }

    #[test]
    fn test_string32() {
        let mut w = MarshalWriter::new();
        let s = vec![b'x'; 256]; // Over STRING8 limit
        w.write_string(&s);
        assert_eq!(w.payload()[0], CODE_STRING32);
        // Length 256 = 0x00000100
        assert_eq!(&w.payload()[1..5], &[0x00, 0x00, 0x01, 0x00]);
        assert_eq!(w.payload().len(), 261); // 1 opcode + 4 len + 256 data
    }

    #[test]
    fn test_small_block() {
        let mut w = MarshalWriter::new();
        w.write_block_header(0, 2);
        // Small block: PREFIX_SMALL_BLOCK + tag + (size << 4)
        // 0x80 + 0 + (2 << 4) = 0x80 + 0x20 = 0xA0
        assert_eq!(w.payload(), &[0xA0]);
    }

    #[test]
    fn test_small_block_tag_1_size_1() {
        let mut w = MarshalWriter::new();
        w.write_block_header(1, 1);
        // 0x80 + 1 + (1 << 4) = 0x80 + 1 + 0x10 = 0x91
        assert_eq!(w.payload(), &[0x91]);
    }

    #[test]
    fn test_small_block_max() {
        let mut w = MarshalWriter::new();
        w.write_block_header(15, 7);
        // 0x80 + 15 + (7 << 4) = 0x80 + 0x0F + 0x70 = 0xFF
        assert_eq!(w.payload(), &[0xFF]);
    }

    #[test]
    fn test_large_block_tag() {
        let mut w = MarshalWriter::new();
        w.write_block_header(16, 1); // tag too large for small block
        assert_eq!(w.payload()[0], CODE_BLOCK32);
        // header = (1 << 10) | (3 << 8) | 16 = 0x710 (size=1, color=3, tag=16)
        assert_eq!(&w.payload()[1..5], &[0x00, 0x00, 0x07, 0x10]);
    }

    #[test]
    fn test_large_block_size() {
        let mut w = MarshalWriter::new();
        w.write_block_header(0, 8); // size too large for small block
        assert_eq!(w.payload()[0], CODE_BLOCK32);
        // header = (8 << 10) | (3 << 8) | 0 = 0x2300 (size=8, color=3, tag=0)
        assert_eq!(&w.payload()[1..5], &[0x00, 0x00, 0x23, 0x00]);
    }

    #[test]
    fn test_double_little_endian() {
        let mut w = MarshalWriter::new();
        w.write_double(1.5);

        #[cfg(target_endian = "little")]
        {
            assert_eq!(w.payload()[0], CODE_DOUBLE_LITTLE);
            // 1.5 in IEEE 754: 0x3FF8000000000000
            let expected_bytes = 1.5f64.to_le_bytes();
            assert_eq!(&w.payload()[1..9], &expected_bytes);
        }
        #[cfg(target_endian = "big")]
        {
            assert_eq!(w.payload()[0], CODE_DOUBLE_BIG);
        }
    }

    #[test]
    fn test_finish_header() {
        let mut w = MarshalWriter::new();
        w.write_int(42);
        let output = w.finish();

        // Magic number: 0x8495A6BE
        assert_eq!(&output[0..4], &[0x84, 0x95, 0xA6, 0xBE]);

        // Data length: 1 byte
        assert_eq!(&output[4..8], &[0x00, 0x00, 0x00, 0x01]);

        // Object count: 0
        assert_eq!(&output[8..12], &[0x00, 0x00, 0x00, 0x00]);

        // Payload
        assert_eq!(output[20], 0x6A);
    }

    #[test]
    fn test_size_counters() {
        let mut w = MarshalWriter::new();

        // A block with 2 fields
        w.write_block_header(0, 2);
        assert_eq!(w.size_32, 3); // 1 header + 2 fields
        assert_eq!(w.size_64, 3);

        // A string of length 5 ("hello")
        w.write_string(b"hello");
        // From OCaml extern.c: size_32 += 1 + (len + 4) / 4
        //                      size_64 += 1 + (len + 8) / 8
        // For len=5: size_32 = 1 + (5 + 4) / 4 = 1 + 2 = 3
        //           size_64 = 1 + (5 + 8) / 8 = 1 + 1 = 2
        assert_eq!(w.size_32, 3 + 3); // 3 (block) + 3 (string)
        assert_eq!(w.size_64, 3 + 2); // 3 (block) + 2 (string)
    }

    #[test]
    fn test_str_idx_sharing() {
        use crate::parse_arena::ParseArena;

        let mut arena = ParseArena::default();
        let idx = arena.intern_string("test.res");

        let mut w = MarshalWriter::new();
        w.set_arena(&arena);

        // First occurrence: write the string
        w.write_str_idx(idx);
        let after_first = w.payload().len();
        assert_eq!(w.obj_counter(), 1); // String recorded

        // Second occurrence: should write shared reference
        w.write_str_idx(idx);
        let after_second = w.payload().len();
        assert_eq!(w.obj_counter(), 1); // No new object recorded

        // The second write should be much smaller (shared reference = 2 bytes)
        // First write: 1 byte prefix + 8 bytes string = 9 bytes
        // Second write: CODE_SHARED8 (1 byte) + distance (1 byte) = 2 bytes
        assert_eq!(after_first, 9); // PREFIX_SMALL_STRING | 8, then 8 chars
        assert_eq!(after_second, 11); // 9 + 2 (shared ref)

        // Verify the shared reference
        let payload = w.payload();
        assert_eq!(payload[9], CODE_SHARED8);
        assert_eq!(payload[10], 1); // Distance from current obj_counter (1) to string index (0) = 1
    }

    #[test]
    fn test_str_idx_sharing_different_strings() {
        use crate::parse_arena::ParseArena;

        let mut arena = ParseArena::default();
        let idx_a = arena.intern_string("a.res");
        let idx_b = arena.intern_string("b.res");

        let mut w = MarshalWriter::new();
        w.set_arena(&arena);

        // Write two different strings
        w.write_str_idx(idx_a);
        w.write_str_idx(idx_b);

        // Both should be recorded as objects
        assert_eq!(w.obj_counter(), 2);

        // Now reference the first one again (same StrIdx)
        w.write_str_idx(idx_a);
        // Should still be 2 objects (first one is shared)
        assert_eq!(w.obj_counter(), 2);

        // Payload should have:
        // - "a.res" (6 bytes: 0x25 + 5 chars)
        // - "b.res" (6 bytes: 0x25 + 5 chars)
        // - shared ref to "a.res" (2 bytes: CODE_SHARED8 + distance)
        assert_eq!(w.payload().len(), 14);
    }

    #[test]
    fn test_str_idx_no_sharing_for_different_idx() {
        use crate::parse_arena::ParseArena;

        let mut arena = ParseArena::default();
        // Create two different StrIdx with the same content
        let idx1 = arena.intern_string("same");
        let idx2 = arena.push_string("same".to_string()); // Different idx, same content

        let mut w = MarshalWriter::new();
        w.set_arena(&arena);

        // Write first string
        w.write_str_idx(idx1);
        assert_eq!(w.obj_counter(), 1);

        // Write second string - different idx so NO sharing, even with same content
        w.write_str_idx(idx2);
        assert_eq!(w.obj_counter(), 2);

        // Payload should have both strings written fully (no sharing)
        // "same" = 5 bytes each (0x24 + 4 chars)
        assert_eq!(w.payload().len(), 10);
    }
}
