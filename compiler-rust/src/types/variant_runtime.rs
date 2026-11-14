//! Canonical JavaScript runtime representation of variant declarations.
//!
//! This mirrors `compiler/ml/variant_runtime.ml`. Layouts live in the
//! per-compilation [`TypeContext`]; [`LayoutRef`]
//! is a stable arena index used while recursive declaration groups are being
//! completed.

use super::context::TypeContext;

/// OCaml `Variant_runtime.Instance.t`: a JavaScript class whose instances a
/// value is recognized by. `name` is the global constructor's path, such as
/// `"Date"` or `"Intl.Locale"`, and `ancestors` are the paths of its
/// superclasses that are declared too, nearest first. Arrays are recognized
/// by `Array.isArray` instead. Two instances are equal when their names and
/// ancestors are, as OCaml's `=` compares them; `blocks` only tells which
/// classes are one value.
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub enum Instance {
    /// Arrays, and which `InstanceType Array` block this value is: a
    /// constant of the code that builds it (predef.ml, variant_layout.ml
    /// `payload_kind`) or a block of an unmarshalled interface.
    Array(ShapeAllocation),
    /// Any other class.
    Class {
        /// The global constructor's path, such as `Date` or `Intl.Locale`.
        name: String,
        /// The paths of its declared superclasses, nearest first.
        ancestors: Vec<String>,
        /// Which OCaml blocks this value is.
        blocks: ClassBlocks,
    },
}

impl PartialEq for Instance {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Array(_), Self::Array(_)) => true,
            (
                Self::Class {
                    name: name1,
                    ancestors: ancestors1,
                    ..
                },
                Self::Class {
                    name: name2,
                    ancestors: ancestors2,
                    ..
                },
            ) => name1 == name2 && ancestors1 == ancestors2,
            _ => false,
        }
    }
}

impl Eq for Instance {}

impl std::hash::Hash for Instance {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        match self {
            Self::Array(_) => 0u8.hash(state),
            Self::Class {
                name, ancestors, ..
            } => {
                1u8.hash(state);
                name.hash(state);
                ancestors.hash(state);
            }
        }
    }
}

/// The physical identity of the OCaml heap blocks of an `InstanceType
/// (Class {name; ancestors})` value, which the removed `Includemod.is_big`
/// counted once each. Kinds are values in Rust, so the identity
/// is carried here and copied with the kind: a layout's untagged payload
/// kind is the block of the payload type's shape (variant_layout.ml
/// `payload_kind`), and `Variant_layout.declaration_shape` keeps the
/// superclass's list of ancestors and puts a cell holding the superclass's
/// name string in front of it. Interface digests skip it.
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct ClassBlocks {
    /// The `InstanceType` block, with the `Class` block allocated with it.
    pub block: ShapeAllocation,
    /// The name string.
    pub name: ShapeString,
    /// The cons cell and the string of each ancestor, nearest first.
    pub ancestors: Vec<(ShapeAllocation, ShapeString)>,
}

impl ClassBlocks {
    /// The blocks of a class whose name and ancestors are strings of their
    /// own.
    pub fn fresh(ancestors: usize) -> Self {
        ClassBlocks {
            block: ShapeAllocation::fresh(),
            name: ShapeString::Allocation(ShapeAllocation::fresh()),
            ancestors: (0..ancestors)
                .map(|_| {
                    (
                        ShapeAllocation::fresh(),
                        ShapeString::Allocation(ShapeAllocation::fresh()),
                    )
                })
                .collect(),
        }
    }
}

impl Instance {
    /// variant_runtime.ml `Instance.to_string`.
    pub fn as_str(&self) -> &str {
        match self {
            Self::Array(_) => "Array",
            Self::Class { name, .. } => name,
        }
    }

    /// variant_runtime.ml `Instance.is_subclass`: whether every instance of
    /// `self` is an instance of `of_` too, without the two being the same
    /// class.
    pub fn is_subclass(&self, of_: &Instance) -> bool {
        match (self, of_) {
            (Self::Class { ancestors, .. }, Self::Class { name, .. }) => ancestors.contains(name),
            _ => false,
        }
    }
}

/// OCaml `Variant_runtime.block_type`: the runtime representation of an
/// untagged block (a case with a payload).
#[derive(Debug, Clone, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub enum BlockType {
    /// `int` and `float` alike.
    Number,
    /// A string.
    String,
    /// A `bigint`.
    Bigint,
    /// A boolean.
    Boolean,
    /// An instance of a builtin class.
    Instance(Instance),
    /// A symbol.
    Symbol,
    /// A function.
    Function,
    /// An object.
    Object,
    /// A shape the payload type does not determine; never emitted.
    Unknown,
}

/// variant_runtime.ml `typeof_kinds`: the payload kinds recognized by
/// `typeof`, with the name it returns.
const TYPEOF_KINDS: [(BlockType, &str); 7] = [
    (BlockType::String, "string"),
    (BlockType::Number, "number"),
    (BlockType::Bigint, "bigint"),
    (BlockType::Boolean, "boolean"),
    (BlockType::Symbol, "symbol"),
    (BlockType::Function, "function"),
    (BlockType::Object, "object"),
];

impl BlockType {
    /// variant_runtime.ml `typeof_name`: what `typeof` returns for values of a
    /// kind it recognizes; `None` for instances and unknown payloads.
    pub fn typeof_name(&self) -> Option<&'static str> {
        TYPEOF_KINDS
            .iter()
            .find(|(kind, _)| kind == self)
            .map(|(_, name)| *name)
    }

    /// variant_runtime.ml `block_type_of_typeof`.
    pub fn of_typeof(name: &str) -> Option<BlockType> {
        TYPEOF_KINDS
            .iter()
            .find(|(_, kind)| *kind == name)
            .map(|(block_type, _)| block_type.clone())
    }
}

/// OCaml `Variant_runtime.value_shape`: what a type declaration states about
/// its values at run time, through `@notUndefined`, `@instanceOf` or
/// `@typeOf`. Each level implies the one before. The recognized kind is boxed
/// so that the common `Unstated` case keeps declarations small.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Default, serde::Serialize, serde::Deserialize)]
pub enum ValueShape {
    /// Nothing: an abbreviation has the shape of the type it abbreviates.
    #[default]
    Unstated,
    /// `@notUndefined`.
    NeverUndefined,
    /// `@instanceOf` or `@typeOf`: a payload of this kind, with the class's
    /// declared superclasses.
    RecognizedAs(Box<RecognizedShape>),
}

impl ValueShape {
    /// A `Recognized_as block_type` allocated with `blocks`.
    pub fn recognized_as(block_type: BlockType, blocks: ShapeBlocks) -> Self {
        Self::RecognizedAs(Box::new(RecognizedShape { block_type, blocks }))
    }

    /// The kind a `Recognized_as` shape states.
    pub fn block_type(&self) -> Option<&BlockType> {
        match self {
            Self::RecognizedAs(shape) => Some(&shape.block_type),
            Self::Unstated | Self::NeverUndefined => None,
        }
    }
}

/// A `Recognized_as block_type` value and the OCaml heap blocks it is made
/// of. Two shapes are equal when their kinds are, as OCaml's `=` compares
/// them; the blocks only tell which shapes are one value.
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct RecognizedShape {
    /// The kind stated.
    pub block_type: BlockType,
    /// Which `Recognized_as` block this value is.
    pub blocks: ShapeBlocks,
}

impl PartialEq for RecognizedShape {
    fn eq(&self, other: &Self) -> bool {
        self.block_type == other.block_type
    }
}

impl Eq for RecognizedShape {}

impl std::hash::Hash for RecognizedShape {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.block_type.hash(state);
    }
}

/// The physical identity of the `Recognized_as` block of a shape, which
/// the removed `Includemod.is_big` counted once. Shapes are
/// values in Rust, so the identity is carried here: a restated
/// `@notUndefined` keeps the abbreviated type's shape
/// (variant_layout.ml `declaration_shape`), and `Subst` and copied
/// declarations keep a declaration's shape (compiler/ml/subst.ml:286). The
/// blocks of a class are its [`ClassBlocks`]. It never takes part in
/// equality, and interface digests skip it.
#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct ShapeBlocks {
    /// The `Recognized_as` block.
    pub block: ShapeAllocation,
}

impl ShapeBlocks {
    /// A `Recognized_as` block no other shape holds.
    pub fn fresh() -> Self {
        ShapeBlocks {
            block: ShapeAllocation::fresh(),
        }
    }
}

/// One block of a shape, identified within its source unit or import. Copies
/// retain identity; importing a stored interface gives its allocations a new
/// namespace. A persistent dependency has the same namespace on every worker.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub struct ShapeAllocation(u64);

impl ShapeAllocation {
    /// Allocations below this are static: `Predef`'s, which it makes once,
    /// and constants of the compiler's code.
    const FIRST_FRESH: u64 = 1 << 32;

    /// A block no other shape holds.
    pub fn fresh() -> Self {
        static NEXT: std::sync::atomic::AtomicU64 =
            std::sync::atomic::AtomicU64::new(ShapeAllocation::FIRST_FRESH);
        use std::sync::atomic::Ordering::Relaxed;
        // `fetch_update` is deprecated and its replacement, `try_update`,
        // is newer than the crate's MSRV: increment without wrapping by hand.
        let mut next = NEXT.load(Relaxed);
        loop {
            let after = next.checked_add(1).expect("shape allocations exhausted");
            match NEXT.compare_exchange_weak(next, after, Relaxed, Relaxed) {
                Ok(_) => return ShapeAllocation(next),
                Err(current) => next = current,
            }
        }
    }

    /// A block allocated by a named compilation or persistent import. Static
    /// blocks keep their small IDs; dynamic blocks stay outside that range.
    pub(crate) fn in_namespace(namespace: u64, identity: u64) -> Self {
        Self(identity_in_namespace(namespace, identity) | Self::FIRST_FRESH)
    }

    /// A block of `Predef.common_initial_env`, which builds each builtin
    /// declaration once.
    pub const fn predef(index: u32) -> Self {
        ShapeAllocation(index as u64)
    }

    /// The `InstanceType Array` constant of variant_layout.ml
    /// `payload_kind`, the kind of a tuple.
    pub const TUPLE_ARRAY: ShapeAllocation = ShapeAllocation(13);

    /// The `InstanceType Array` constant of variant_layout.ml
    /// `payload_kind` for a record represented as an array (`RecordArray`).
    pub const RECORD_ARRAY: ShapeAllocation = ShapeAllocation(14);

    /// Whether this is a static block, which an import keeps.
    pub fn is_predef(self) -> bool {
        self.0 < Self::FIRST_FRESH
    }
}

/// Which string a class name or an ancestor is.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub enum ShapeString {
    /// The payload string of the `@instanceOf("...")` attribute whose name
    /// location has this allocation identity:
    /// `Ast_payload.semantic_string_of_payload` returns a string constant's
    /// own string.
    Attribute {
        /// The scope of the name location's allocation identity: the owner
        /// of the source allocations that assigned it.
        scope: u64,
        /// The name location's allocation identity within that scope.
        location: u32,
    },
    /// A string of its own.
    Allocation(ShapeAllocation),
}

impl ShapeString {
    /// The payload string of the attribute named at `loc`; a string of its
    /// own when that location has no allocation identity to share.
    pub(crate) fn attribute(ctx: &TypeContext, loc: super::DeclLoc) -> Self {
        match ctx.location_identity(loc) {
            Some(identity) => ShapeString::Attribute {
                scope: identity.scope,
                location: identity.location,
            },
            None => ShapeString::Allocation(ctx.fresh_shape_allocation()),
        }
    }
}

/// The shapes and payload kinds of an imported interface, given new
/// allocations as unmarshalling allocates new blocks. Sharing within the
/// import is kept. An attribute string follows its location's scope through
/// the same map as the location table (`DeclLocTable::remap_for_import`).
pub(crate) struct ShapeImport<'a> {
    scopes: &'a crate::fast_hash::AHashMap<u64, u64>,
    other_scopes: crate::fast_hash::AHashMap<u64, u64>,
    allocations: crate::fast_hash::AHashMap<ShapeAllocation, ShapeAllocation>,
    namespace: Option<u64>,
}

impl<'a> ShapeImport<'a> {
    pub(crate) fn new(scopes: &'a crate::fast_hash::AHashMap<u64, u64>) -> Self {
        ShapeImport {
            scopes,
            other_scopes: Default::default(),
            allocations: Default::default(),
            namespace: None,
        }
    }

    pub(crate) fn with_namespace(
        scopes: &'a crate::fast_hash::AHashMap<u64, u64>,
        namespace: Option<u64>,
    ) -> Self {
        Self {
            namespace,
            ..Self::new(scopes)
        }
    }

    /// An import whose allocations are given: the inverse of an earlier
    /// import, built from [`Self::into_maps`] with keys and values swapped.
    /// `scopes` then holds every scope the earlier import produced.
    pub(crate) fn with_allocations(
        scopes: &'a crate::fast_hash::AHashMap<u64, u64>,
        allocations: crate::fast_hash::AHashMap<ShapeAllocation, ShapeAllocation>,
    ) -> Self {
        Self {
            allocations,
            ..Self::new(scopes)
        }
    }

    /// What the import mapped, beyond the location table's scopes it was
    /// given: the scopes of attribute strings outside that table, and the
    /// allocations.
    pub(crate) fn into_maps(
        self,
    ) -> (
        crate::fast_hash::AHashMap<u64, u64>,
        crate::fast_hash::AHashMap<ShapeAllocation, ShapeAllocation>,
    ) {
        (self.other_scopes, self.allocations)
    }

    fn allocation(&mut self, allocation: ShapeAllocation) -> ShapeAllocation {
        if allocation.is_predef() {
            return allocation;
        }
        *self
            .allocations
            .entry(allocation)
            .or_insert_with(|| match self.namespace {
                Some(namespace) => ShapeAllocation::in_namespace(namespace, allocation.0),
                None => ShapeAllocation::fresh(),
            })
    }

    fn string(&mut self, string: ShapeString) -> ShapeString {
        match string {
            ShapeString::Attribute { scope, location } => {
                let scope = match self.scopes.get(&scope) {
                    Some(scope) => *scope,
                    // An attribute of a declaration the interface does not
                    // hold: still one string within the import.
                    None => *self
                        .other_scopes
                        .entry(scope)
                        .or_insert_with(|| match self.namespace {
                            Some(namespace) => identity_in_namespace(namespace, scope),
                            None => (super::decl_loc::next_table_owner() as u64) << 32,
                        }),
                };
                ShapeString::Attribute { scope, location }
            }
            ShapeString::Allocation(allocation) => {
                ShapeString::Allocation(self.allocation(allocation))
            }
        }
    }

    pub(crate) fn block_type(&mut self, block_type: &mut BlockType) {
        if let BlockType::Instance(Instance::Array(block)) = block_type {
            *block = self.allocation(*block);
        }
        if let BlockType::Instance(Instance::Class { blocks, .. }) = block_type {
            blocks.block = self.allocation(blocks.block);
            blocks.name = self.string(blocks.name);
            for (cell, string) in &mut blocks.ancestors {
                *cell = self.allocation(*cell);
                *string = self.string(*string);
            }
        }
    }

    pub(crate) fn value_shape(&mut self, shape: &mut ValueShape) {
        if let ValueShape::RecognizedAs(shape) = shape {
            shape.blocks.block = self.allocation(shape.blocks.block);
            self.block_type(&mut shape.block_type);
        }
    }

    pub(crate) fn layout(&mut self, layout: &mut Layout) {
        for case in &mut layout.constructors {
            if let ConstructorCase::Block(Block::Untagged { block_type, .. }) = case {
                self.block_type(block_type);
            }
        }
        for block_type in &mut layout.matching_facts.block_types {
            self.block_type(block_type);
        }
    }

    pub(crate) fn signature(&mut self, sig: &mut [super::decl::SignatureItem]) {
        super::decl::for_each_signature_shape(sig, &mut |shape| self.value_shape(shape));
    }
}

/// OCaml `Variant_runtime.literal_tag`: the literal value a constructor is
/// represented by, what `@as` states (or the constructor's own name when it
/// states nothing). It never describes an inferred untagged payload shape.
#[derive(Debug, Clone, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub enum LiteralTag {
    /// A string literal.
    String(String),
    /// An integer literal.
    Int(i64),
    /// A float literal, as written.
    Float(String),
    /// A bigint literal's digits.
    BigInt(String),
    /// A boolean literal.
    Bool(bool),
    /// `null`.
    Null,
    /// `undefined`.
    Undefined,
}

/// variant_runtime.ml `number_key`: `-0.` and `0.` are equal for `===`;
/// `%h` is exact for every other number.
/// Cost: O(1): bounded floating-point formatting.
fn number_key_into(x: f64, out: &mut String) {
    out.push_str("number:");
    if x == 0.0 { out.push('0'); } else { hex_float_into(x, out); }
}

/// OCaml's `Printf.sprintf "%h"` (`caml_hexstring_of_float`): `0x1p+0`,
/// `-0x1.8p-1`, `0x0.0000000000001p-1022` for a subnormal, `infinity`,
/// `nan`, and `-nan` for a NaN with its sign bit set.
#[cfg(test)]
/// Cost: O(1): bounded floating-point formatting.
pub(crate) fn ocaml_hex_float(x: f64) -> String {
    let mut out = String::new();
    hex_float_into(x, &mut out);
    out
}

/// Cost: O(1): at most thirteen mantissa nibbles.
fn hex_float_into(x: f64, out: &mut String) {
    use std::fmt::Write;
    if x.is_sign_negative() { out.push('-'); }
    if x.is_nan() { out.push_str("nan"); return; }
    if x.is_infinite() { out.push_str("infinity"); return; }
    let bits = x.to_bits();
    let biased_exp = ((bits >> 52) & 0x7ff) as i64;
    let mantissa = bits & ((1u64 << 52) - 1);
    let (lead, exp) = if biased_exp == 0 { (0, if mantissa == 0 { 0 } else { -1022 }) }
        else { (1, biased_exp - 1023) };
    write!(out, "0x{lead}").unwrap();
    if mantissa != 0 {
        out.push('.');
        let nibbles = 13 - (mantissa.trailing_zeros() / 4) as usize;
        for i in 0..nibbles {
            let digit = ((mantissa >> (4 * (12 - i))) & 15) as usize;
            out.push(b"0123456789abcdef"[digit] as char);
        }
    }
    write!(out, "p{}{exp_abs}", if exp < 0 { '-' } else { '+' }, exp_abs = exp.abs()).unwrap();
}

/// Reusable canonical-key encoding buffers for immutable literal metadata.
#[derive(Debug, Clone, Default)]
pub(crate) struct LiteralKeyScratch {
    pub(crate) output: String,
    digits: String,
    float: Vec<u8>,
}
impl LiteralKeyScratch {
    /// Cost: O(literal spelling bytes), with retained canonicalization scratch.
    pub(crate) fn encode(&mut self, tag: &LiteralTag) -> &str {
        self.output.clear();
        match tag {
            LiteralTag::Int(i) => number_key_into(f64::from(*i as i32), &mut self.output),
            LiteralTag::Float(f) => match crate::ocaml_float::float_of_string_in(f, &mut self.float) {
                Some(x) => number_key_into(x, &mut self.output),
                None => { self.output.push_str("number:"); self.output.push_str(f); }
            },
            LiteralTag::BigInt(i) => {
                let positive = crate::types::typecore::parse_bigint_literal_into(i, &mut self.digits);
                self.output.push_str("bigint:");
                if !positive && self.digits != "0" { self.output.push('-'); }
                self.output.push_str(&self.digits);
            }
            LiteralTag::String(s) => { self.output.push_str("string:"); self.output.push_str(s); }
            LiteralTag::Bool(b) => self.output.push_str(if *b { "true" } else { "false" }),
            LiteralTag::Null => self.output.push_str("null"),
            LiteralTag::Undefined => self.output.push_str("undefined"),
        }
        &self.output
    }
    #[cfg(test)]
    /// Cost: O(1): read three retained buffer capacities.
    pub(crate) fn capacities(&self) -> [usize; 3] {
        [self.output.capacity(), self.digits.capacity(), self.float.capacity()]
    }
}

impl LiteralTag {
    /// variant_runtime.ml `literal_value_key`: a key that two literals share
    /// exactly when they are the same JavaScript value, as `===` compares
    /// them. Ints are emitted as 32-bit numbers, so `1`, `1.0` and
    /// `4294967297` share one, while `1n` is a bigint.
    /// Cost: O(literal spelling bytes), producing one owned key.
    pub fn value_key(&self) -> String {
        let mut scratch = LiteralKeyScratch::default();
        scratch.encode(self);
        scratch.output
    }
}

/// variant_runtime.ml `same_literal_value`.
pub fn same_literal_value(a: &LiteralTag, b: &LiteralTag) -> bool {
    a.value_key() == b.value_key()
}

/// OCaml `Variant_runtime.tag_type`: information used to recognize a
/// constructor during matching. A literal identifies a constant or an
/// object's tag; a payload shape identifies a value represented directly by
/// its payload.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TagType {
    /// A literal value: a constant, or an object's tag field.
    Literal(LiteralTag),
    /// The runtime shape of an untagged payload.
    PayloadShape(BlockType),
}

/// OCaml `Variant_runtime.tag`: a constructor's name and its runtime
/// literal: what `@as` states, or the name itself.
#[derive(Debug, Clone, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub struct Tag {
    /// The constructor's name.
    pub name: crate::name::Name,
    /// The literal the constructor is represented by.
    pub literal: LiteralTag,
}

/// OCaml `Variant_runtime.tagged_block`.
#[derive(Debug, Clone, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub struct TaggedBlock {
    /// The constructor's tag.
    pub tag: Tag,
    /// The object field holding the tag, from `@tag`; `None` means `TAG`.
    pub tag_name: Option<String>,
}

/// OCaml `Variant_runtime.block`: an untagged payload always carries the
/// runtime shape used for dispatch. Only tagged blocks have an emitted tag
/// field.
#[derive(Debug, Clone, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub enum Block {
    /// A constructor represented as an object with a tag field.
    Tagged(TaggedBlock),
    /// A constructor represented directly by its payload.
    Untagged {
        /// The constructor's tag.
        tag: Tag,
        /// The payload's runtime shape, which matching dispatches on.
        block_type: BlockType,
    },
}

impl Block {
    /// `Tagged {tag} | Untagged {tag}`.
    pub fn tag(&self) -> &Tag {
        match self {
            Block::Tagged(TaggedBlock { tag, .. }) | Block::Untagged { tag, .. } => tag,
        }
    }

    /// Whether the constructor is represented directly by its payload.
    pub fn is_untagged(&self) -> bool {
        matches!(self, Block::Untagged { .. })
    }

    /// The payload shape an untagged block is dispatched on.
    pub fn block_type(&self) -> Option<&BlockType> {
        match self {
            Block::Untagged { block_type, .. } => Some(block_type),
            Block::Tagged(_) => None,
        }
    }
}

/// OCaml `Variant_runtime.constructor_case`: how one constructor is
/// represented.
#[derive(Debug, Clone, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub enum ConstructorCase {
    /// A nullary constructor, represented by its literal.
    Constant(Tag),
    /// A constructor with a payload.
    Block(Block),
}

/// OCaml `Variant_runtime.configuration`: the declaration's `@unboxed` and
/// `@tag` attributes.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Configuration {
    /// Whether the variant is `@unboxed`.
    pub unboxed: bool,
    /// The `@tag` field name, if any.
    pub tag_name: Option<String>,
}

/// OCaml `Variant_runtime.matching_facts`: declaration-level facts needed
/// when lowering a constructor match.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct MatchingFacts {
    /// Custom object field containing constructor tags; `None` means `TAG`.
    pub tag_name: Option<String>,
    /// Runtime shapes of the untagged payload constructors, in declaration
    /// order.
    pub block_types: Vec<BlockType>,
    /// Runtime values of all nullary constructors, in declaration order.
    pub literal_tags: Vec<LiteralTag>,
}

/// OCaml `Variant_runtime.layout`: the completed runtime representation of
/// a variant declaration, with constructors in source order.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct Layout {
    /// Whether the variant is `@unboxed`.
    pub unboxed: bool,
    /// Each constructor's representation, in source order.
    pub constructors: Vec<ConstructorCase>,
    /// Facts derived once from `constructors` for match lowering.
    pub matching_facts: MatchingFacts,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum LayoutState {
    Pending,
    Complete(Layout),
}

/// A stable reference to a variant layout, local to a compilation, in the
/// per-thread store, or in the shared pool (OCaml `layout_ref`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub struct LayoutRef(pub(crate) u32);

impl LayoutRef {
    #[inline]
    pub(crate) fn from_usize(idx: usize) -> Self {
        let raw = u32::try_from(idx).expect("variant layout index exceeds u32::MAX");
        assert!(
            raw & super::type_expr::STORE_REF_TAG == 0,
            "local variant layout index collides with the store tag"
        );
        Self(raw)
    }

    /// Reference to the `idx`-th complete layout of the per-thread store.
    #[inline]
    pub(crate) fn from_store_index(idx: usize) -> Self {
        let raw = u32::try_from(idx).expect("variant layout store index exceeds u32::MAX");
        assert!(
            raw & super::type_expr::SHARED_REF_BITS == 0,
            "variant layout store index exceeds the tag range"
        );
        Self(raw | super::type_expr::STORE_REF_TAG)
    }

    /// Layout `idx` of the process-wide shared pool.
    #[inline]
    pub(crate) fn from_shared_index(idx: u32) -> Self {
        let bits = super::type_expr::SHARED_REF_BITS;
        assert!(
            idx & bits == 0,
            "shared variant layout index exceeds the tag range"
        );
        Self(idx | bits)
    }

    #[inline]
    pub(crate) fn is_shared(self) -> bool {
        let bits = super::type_expr::SHARED_REF_BITS;
        self.0 & bits == bits
    }

    #[inline]
    pub(crate) fn shared_index(self) -> u32 {
        debug_assert!(self.is_shared());
        self.0 & !super::type_expr::SHARED_REF_BITS
    }

    /// Whether this layout lives in the per-thread store.
    #[inline]
    pub(crate) fn is_store(self) -> bool {
        self.0 & super::type_expr::STORE_REF_TAG != 0
    }

    #[inline]
    pub(crate) fn index(self) -> usize {
        debug_assert!(
            !self.is_store(),
            "store variant layout used as a local index"
        );
        self.0 as usize
    }

    #[inline]
    pub(crate) fn store_index(self) -> usize {
        debug_assert!(
            self.is_store() && !self.is_shared(),
            "non-store variant layout used as a store index"
        );
        (self.0 & !super::type_expr::STORE_REF_TAG) as usize
    }
}

/// One constructor of a variant: its layout and position.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub struct ConstructorReference {
    /// The variant's layout.
    pub variant: LayoutRef,
    /// The constructor's position in declaration order.
    pub position: usize,
}

impl Layout {
    /// variant_runtime.ml `make_layout` / `compute_matching_facts`.
    /// Cost: O(constructor count plus cloned literal/shape metadata bytes).
    pub fn new(configuration: Configuration, constructors: Vec<ConstructorCase>) -> Self {
        let mut block_types = Vec::new();
        let mut literal_tags = Vec::new();
        for case in &constructors {
            match case {
                ConstructorCase::Constant(tag) => literal_tags.push(tag.literal.clone()),
                ConstructorCase::Block(Block::Untagged { block_type, .. }) => {
                    block_types.push(block_type.clone())
                }
                ConstructorCase::Block(Block::Tagged(_)) => {}
            }
        }
        let layout = Self {
            unboxed: configuration.unboxed,
            constructors,
            matching_facts: MatchingFacts {
                tag_name: configuration.tag_name,
                block_types,
                literal_tags,
            },
        };
        #[cfg(test)]
        crate::bir::untagged_plan::differential::record(&layout);
        layout
    }

    /// variant_runtime.ml `constructor_tag`: the literal of a constant
    /// constructor, or of the tag of a tagged one.
    pub fn constructor_tag(&self, position: usize) -> &LiteralTag {
        match &self.constructors[position] {
            ConstructorCase::Constant(tag) => &tag.literal,
            ConstructorCase::Block(block) => &block.tag().literal,
        }
    }

    /// The `@unboxed` and `@tag` configuration the layout was built from.
    pub fn configuration(&self) -> Configuration {
        Configuration {
            unboxed: self.unboxed,
            tag_name: self.matching_facts.tag_name.clone(),
        }
    }
    /// The number of nullary constructors.
    pub fn num_constants(&self) -> usize {
        self.constructors
            .iter()
            .filter(|c| matches!(c, ConstructorCase::Constant(_)))
            .count()
    }
    /// The number of constructors with a payload.
    pub fn num_blocks(&self) -> usize {
        self.constructors.len() - self.num_constants()
    }
}

impl ConstructorReference {
    /// The constructor's representation.
    pub fn representation(self, ctx: &TypeContext) -> ConstructorCase {
        ctx.with_variant_layout(self.variant, |layout| {
            layout.constructors[self.position].clone()
        })
    }

    /// The constructor's index among the constructors with a payload.
    pub fn block_index(self, ctx: &TypeContext) -> usize {
        ctx.with_variant_layout(self.variant, |layout| {
            layout.constructors[..self.position]
                .iter()
                .filter(|case| matches!(case, ConstructorCase::Block(_)))
                .count()
        })
    }

    /// The number of constructors with a payload in the constructor's variant.
    pub fn num_blocks(self, ctx: &TypeContext) -> usize {
        ctx.with_variant_layout(self.variant, Layout::num_blocks)
    }
}

/// Allocate the layout of a variant with no `@unboxed`, `@tag` or `@as`:
/// each case is a constructor name and whether it has a payload.
pub fn plain_layout(
    ctx: &TypeContext,
    cases: impl IntoIterator<Item = (String, bool)>,
) -> LayoutRef {
    let constructors = cases
        .into_iter()
        .map(|(name, has_payload)| {
            // The empty list is the number 0.
            let literal = if name == "[]" {
                LiteralTag::Int(0)
            } else {
                LiteralTag::String(name.clone())
            };
            let tag = Tag { name: crate::name::Name::new(&name), literal };
            if has_payload {
                ConstructorCase::Block(Block::Tagged(TaggedBlock {
                    tag,
                    tag_name: None,
                }))
            } else {
                ConstructorCase::Constant(tag)
            }
        })
        .collect();
    ctx.alloc_complete_variant_layout(Layout::new(
        Configuration {
            unboxed: false,
            tag_name: None,
        },
        constructors,
    ))
}

#[cfg(test)]
mod hex_float_tests {
    use super::{LiteralTag, ocaml_hex_float};

    /// `Printf.sprintf "%h"` of OCaml 5.5.2 (`caml_hexstring_of_float`) on
    /// signed zeros, NaNs of either sign and other payloads, infinities, the
    /// subnormal and normal boundaries and ordinary numbers, by bit pattern.
    #[test]
    fn matches_ocaml_percent_h() {
        let mismatches = [
            (0x0000000000000000, "0x0p+0"),
            (0x8000000000000000, "-0x0p+0"),
            (0x7ff8000000000000, "nan"),
            (0xfff8000000000000, "-nan"),
            (0x7ff0000000000001, "nan"),
            (0xfff0000000000001, "-nan"),
            (0x7ff4000000000000, "nan"),
            (0x7ff0000000000000, "infinity"),
            (0xfff0000000000000, "-infinity"),
            (0x0000000000000001, "0x0.0000000000001p-1022"),
            (0x8000000000000001, "-0x0.0000000000001p-1022"),
            (0x000fffffffffffff, "0x0.fffffffffffffp-1022"),
            (0x0008000000000000, "0x0.8p-1022"),
            (0x0010000000000000, "0x1p-1022"),
            (0x8010000000000000, "-0x1p-1022"),
            (0x7fefffffffffffff, "0x1.fffffffffffffp+1023"),
            (0x3ff0000000000000, "0x1p+0"),
            (0x3ff8000000000000, "0x1.8p+0"),
            (0xbfe8000000000000, "-0x1.8p-1"),
            (0x4000000000000000, "0x1p+1"),
            (0x3fb999999999999a, "0x1.999999999999ap-4"),
            (0x0000000000000010, "0x0.000000000001p-1022"),
            (0x0001000000000000, "0x0.1p-1022"),
            (0x3ff0000000000001, "0x1.0000000000001p+0"),
        ]
        .into_iter()
        .filter(|(bits, expected)| ocaml_hex_float(f64::from_bits(*bits)) != *expected)
        .map(|(bits, expected)| (bits, expected, ocaml_hex_float(f64::from_bits(bits))))
        .collect::<Vec<_>>();
        assert!(mismatches.is_empty(), "{mismatches:x?}");
    }

    /// variant_runtime.ml `literal_value_key` (`float_of_string_opt`, then
    /// `number_key`) of OCaml 5.5.2 on float spellings: overflow and
    /// underflow, subnormals, signed zeros, underscores, hex floats, and
    /// the spellings only a PPX can give a literal.
    #[test]
    fn float_literal_keys_match_ocaml() {
        let mismatches = [
            ("1e400", "number:infinity"),
            ("-1e400", "number:-infinity"),
            ("4.9e-324", "number:0x0.0000000000001p-1022"),
            ("5e-324", "number:0x0.0000000000001p-1022"),
            ("2.2250738585072014e-308", "number:0x1p-1022"),
            ("2.225073858507201e-308", "number:0x0.fffffffffffffp-1022"),
            ("-0.0", "number:0"),
            ("0.0", "number:0"),
            ("0.", "number:0"),
            ("1_000.5", "number:0x1.f44p+9"),
            ("0x1p-1074", "number:0x0.0000000000001p-1022"),
            ("0x1.fffffffffffffp1023", "number:0x1.fffffffffffffp+1023"),
            ("1.", "number:0x1p+0"),
            ("1.e5", "number:0x1.86ap+16"),
            ("1E+5", "number:0x1.86ap+16"),
            ("0x1P4", "number:0x1p+4"),
            ("0x.8p1", "number:0x1p+0"),
            ("1e-400", "number:0"),
            ("-1e-400", "number:0"),
            ("nan", "number:nan"),
            ("-nan", "number:-nan"),
            ("infinity", "number:infinity"),
            ("-inf", "number:-infinity"),
            ("1.5_", "number:0x1.8p+0"),
            ("0x1_0p0", "number:0x1p+4"),
            ("1e1_0", "number:0x1.2a05f2p+33"),
            ("+1.5", "number:0x1.8p+0"),
            ("  1.5", "number:0x1.8p+0"),
            ("1.5e", "number:1.5e"),
        ]
        .into_iter()
        .map(|(spelling, expected)| {
            (
                spelling,
                expected,
                LiteralTag::Float(spelling.to_string()).value_key(),
            )
        })
        .filter(|(_, expected, key)| key != expected)
        .collect::<Vec<_>>();
        assert!(mismatches.is_empty(), "{mismatches:?}");
    }
}

#[cfg(test)]
mod shape_import_tests {
    use super::*;

    fn class(name: &str, blocks: ClassBlocks) -> BlockType {
        BlockType::Instance(Instance::Class {
            name: name.to_string(),
            ancestors: blocks.ancestors.iter().map(|_| "A".to_string()).collect(),
            blocks,
        })
    }

    fn class_blocks(block_type: &BlockType) -> &ClassBlocks {
        match block_type {
            BlockType::Instance(Instance::Class { blocks, .. }) => blocks,
            _ => panic!("a class"),
        }
    }

    /// An import allocates new blocks but keeps the sharing between the
    /// shapes and layouts it imports; `Predef`'s blocks are its own.
    #[test]
    fn imports_get_new_blocks_and_keep_their_sharing() {
        let a_name = ShapeString::Attribute {
            scope: 7 << 32,
            location: 1,
        };
        let a = ClassBlocks {
            block: ShapeAllocation::fresh(),
            name: a_name,
            ancestors: Vec::new(),
        };
        let cell = ShapeAllocation::fresh();
        let b = ClassBlocks {
            block: ShapeAllocation::fresh(),
            name: ShapeString::Allocation(ShapeAllocation::fresh()),
            ancestors: vec![(cell, a_name)],
        };
        let shape = ShapeBlocks::fresh();
        let mut shapes = vec![
            ValueShape::recognized_as(class("A", a.clone()), shape),
            // A restated shape.
            ValueShape::recognized_as(class("A", a.clone()), shape),
            ValueShape::recognized_as(class("B", b.clone()), ShapeBlocks::fresh()),
            ValueShape::recognized_as(
                BlockType::String,
                ShapeBlocks {
                    block: ShapeAllocation::predef(5),
                },
            ),
        ];
        let mut layout = Layout {
            unboxed: true,
            constructors: Vec::new(),
            matching_facts: MatchingFacts {
                tag_name: None,
                block_types: vec![class("A", a.clone())],
                literal_tags: Vec::new(),
            },
        };
        let original = shapes.clone();
        let scopes = [(7 << 32, 9 << 32)].into_iter().collect();
        let mut import = ShapeImport::new(&scopes);
        for shape in &mut shapes {
            import.value_shape(shape);
        }
        import.layout(&mut layout);
        let recognized = |shape: &ValueShape| match shape {
            ValueShape::RecognizedAs(shape) => (**shape).clone(),
            _ => panic!("recognized"),
        };
        let [a1, a2, b1, string] = [0, 1, 2, 3].map(|i| recognized(&shapes[i]));
        assert_eq!(shapes, original);
        assert_ne!(a1.blocks, recognized(&original[0]).blocks);
        assert_eq!(a1.blocks, a2.blocks);
        let (a1, b1) = (class_blocks(&a1.block_type), class_blocks(&b1.block_type));
        assert_ne!(a1.block, a.block);
        assert_eq!(
            a1.block,
            class_blocks(&layout.matching_facts.block_types[0]).block
        );
        assert_eq!(
            a1.name,
            ShapeString::Attribute {
                scope: 9 << 32,
                location: 1
            }
        );
        assert_eq!(b1.ancestors[0].1, a1.name);
        assert_ne!(b1.ancestors[0].0, cell);
        assert_ne!(b1.name, b.name);
        assert_eq!(string.blocks.block, ShapeAllocation::predef(5));

        let named_import = |namespace| {
            // An attribute's declaration need not be present in the signature.
            let scopes = Default::default();
            let mut import = ShapeImport::with_namespace(&scopes, Some(namespace));
            let mut shapes = original.clone();
            for shape in &mut shapes {
                import.value_shape(shape);
            }
            let a = class_blocks(&recognized(&shapes[0]).block_type).clone();
            let b = class_blocks(&recognized(&shapes[2]).block_type).clone();
            assert_eq!(a.name, b.ancestors[0].1);
            assert_eq!(
                recognized(&shapes[3]).blocks.block,
                ShapeAllocation::predef(5),
            );
            crate::binser::to_vec(&shapes).unwrap()
        };
        assert_eq!(named_import(23), named_import(23));
        assert_ne!(named_import(23), named_import(24));
    }
}

/// A stable identity within an explicitly selected allocation namespace.
pub(crate) fn identity_in_namespace(namespace: u64, identity: u64) -> u64 {
    use std::hash::{Hash, Hasher};
    let mut hash = std::collections::hash_map::DefaultHasher::new();
    (namespace, identity).hash(&mut hash);
    hash.finish()
}

#[cfg(test)]
mod trunk_literal_reference {
    // Verbatim function from be1b3a482e5a989d1a1bbecf33a9b4f1aab98fec.
    #[cfg(test)]
pub(crate) fn ocaml_hex_float(x: f64) -> String {
    if x.is_nan() {
        return if x.is_sign_negative() { "-nan" } else { "nan" }.to_string();
    }
    if x.is_infinite() {
        return if x > 0.0 { "infinity" } else { "-infinity" }.to_string();
    }
    let bits = x.to_bits();
    let sign = if bits >> 63 == 1 { "-" } else { "" };
    let biased_exp = ((bits >> 52) & 0x7ff) as i64;
    let mantissa = bits & ((1u64 << 52) - 1);
    let (lead, exp) = if biased_exp == 0 {
        // Zero or subnormal.
        (0, if mantissa == 0 { 0 } else { -1022 })
    } else {
        (1, biased_exp - 1023)
    };
    let mut frac = format!("{mantissa:013x}");
    while frac.ends_with('0') {
        frac.pop();
    }
    let frac = if frac.is_empty() {
        String::new()
    } else {
        format!(".{frac}")
    };
    let exp_sign = if exp < 0 { "-" } else { "+" };
    format!("{sign}0x{lead}{frac}p{exp_sign}{}", exp.abs())
}

    #[test]
    fn hex_float_normalization_matches_trunk() {
        fn check(value: f64) {
            let expected = ocaml_hex_float(value);
            let mut out = String::from("prefix:");
            super::hex_float_into(value, &mut out);
            assert_eq!(&out[7..], expected, "bits={:016x}", value.to_bits());
        }
        let cases = [0.0, -0.0, f64::from_bits(1), f64::from_bits((1u64 << 52) - 1),
            f64::MIN_POSITIVE, 1.0, -1.0, 0.1, f64::MAX, f64::MIN, f64::EPSILON,
            f64::INFINITY, f64::NEG_INFINITY, f64::from_bits(0x7ff8000000000000),
            f64::from_bits(0xfff8000000000000)];
        for value in cases { check(value); }
        let mut bits = 0x295a_64b8_0ce7_d13fu64;
        for _ in 0..10000 {
            bits = bits.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            check(f64::from_bits(bits));
        }
        println!("hex float trunk comparison: table=15; generated raw bit patterns=10000; all agree");
    }
}
