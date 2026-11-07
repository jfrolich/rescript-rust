//! Canonical JavaScript runtime representation of variant declarations.
//!
//! This mirrors `compiler/ml/variant_runtime.ml`. Layouts live in the
//! per-compilation [`TypeContext`](super::context::TypeContext); [`LayoutRef`]
//! is a stable arena index used while recursive declaration groups are being
//! completed.

use super::context::TypeContext;

/// OCaml `Variant_runtime.Instance.t`: a JavaScript class whose instances a
/// value is recognized by. `name` is the global constructor's path, such as
/// `"Date"` or `"Intl.Locale"`, and `ancestors` are the paths of its
/// superclasses that are declared too, nearest first. Arrays are recognized
/// by `Array.isArray` instead.
#[derive(Debug, Clone, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub enum Instance {
    Array,
    Class {
        name: String,
        ancestors: Vec<String>,
    },
}

impl Instance {
    /// variant_runtime.ml `Instance.to_string`.
    pub fn as_str(&self) -> &str {
        match self {
            Self::Array => "Array",
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
    String,
    Bigint,
    Boolean,
    Instance(Instance),
    Symbol,
    Function,
    Object,
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
    RecognizedAs(Box<BlockType>),
}

impl ValueShape {
    pub fn recognized_as(block_type: BlockType) -> Self {
        Self::RecognizedAs(Box::new(block_type))
    }
}

/// OCaml `Variant_runtime.literal_tag`: the literal value a constructor is
/// represented by, what `@as` states (or the constructor's own name when it
/// states nothing). It never describes an inferred untagged payload shape.
#[derive(Debug, Clone, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub enum LiteralTag {
    String(String),
    Int(i64),
    Float(String),
    BigInt(String),
    Bool(bool),
    Null,
    Undefined,
}

/// OCaml `float_of_string` for the spellings a literal tag can carry.
pub(crate) fn ocaml_float_of_string(s: &str) -> Option<f64> {
    if let Some(value) = crate::js_ir::printer::parse_hex_float_literal(s) {
        return Some(value);
    }
    s.replace('_', "").parse::<f64>().ok()
}

/// variant_runtime.ml `number_key`: `-0.` and `0.` are equal for `===`.
/// OCaml spells every other number exactly with `%h`; the key is internal, so
/// the exact bit pattern serves the same equality.
/// variant_runtime.ml `number_key`: `-0.` and `0.` are equal for `===`;
/// `%h` is exact for every other number.
fn number_key(x: f64) -> String {
    if x == 0.0 {
        "number:0".to_string()
    } else {
        format!("number:{}", ocaml_hex_float(x))
    }
}

/// OCaml's `Printf.sprintf "%h"` (`caml_hexstring_of_float`): `0x1p+0`,
/// `-0x1.8p-1`, `0x0.0000000000001p-1022` for a subnormal, `infinity`,
/// `nan`.
fn ocaml_hex_float(x: f64) -> String {
    if x.is_nan() {
        return "nan".to_string();
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

impl LiteralTag {
    /// variant_runtime.ml `literal_value_key`: a key that two literals share
    /// exactly when they are the same JavaScript value, as `===` compares
    /// them. Ints are emitted as 32-bit numbers, so `1`, `1.0` and
    /// `4294967297` share one, while `1n` is a bigint.
    pub fn value_key(&self) -> String {
        match self {
            Self::Int(i) => number_key(f64::from(*i as i32)),
            Self::Float(f) => match ocaml_float_of_string(f) {
                Some(x) => number_key(x),
                None => format!("number:{f}"),
            },
            Self::BigInt(i) => {
                let (positive, digits) = crate::types::typecore::parse_bigint_literal(i);
                // Bigint_utils.to_string
                let sign = if positive || digits == "0" { "" } else { "-" };
                format!("bigint:{sign}{digits}")
            }
            Self::Bool(b) => if *b { "true" } else { "false" }.to_string(),
            Self::Null => "null".to_string(),
            Self::Undefined => "undefined".to_string(),
            Self::String(s) => format!("string:{s}"),
        }
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
    Literal(LiteralTag),
    PayloadShape(BlockType),
}

/// OCaml `Variant_runtime.tag`: a constructor's name and its runtime
/// literal: what `@as` states, or the name itself.
#[derive(Debug, Clone, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub struct Tag {
    pub name: String,
    pub literal: LiteralTag,
}

/// OCaml `Variant_runtime.tagged_block`.
#[derive(Debug, Clone, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub struct TaggedBlock {
    pub tag: Tag,
    pub tag_name: Option<String>,
}

/// OCaml `Variant_runtime.block`: an untagged payload always carries the
/// runtime shape used for dispatch. Only tagged blocks have an emitted tag
/// field.
#[derive(Debug, Clone, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub enum Block {
    Tagged(TaggedBlock),
    Untagged { tag: Tag, block_type: BlockType },
}

impl Block {
    /// `Tagged {tag} | Untagged {tag}`.
    pub fn tag(&self) -> &Tag {
        match self {
            Block::Tagged(TaggedBlock { tag, .. }) | Block::Untagged { tag, .. } => tag,
        }
    }

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

#[derive(Debug, Clone, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub enum ConstructorCase {
    Constant(Tag),
    Block(Block),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Configuration {
    pub unboxed: bool,
    pub tag_name: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct MatchingFacts {
    pub tag_name: Option<String>,
    /// Runtime shapes of the untagged payload constructors, in declaration
    /// order.
    pub block_types: Vec<BlockType>,
    /// Runtime values of all nullary constructors, in declaration order.
    pub literal_tags: Vec<LiteralTag>,
}

#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct Layout {
    pub unboxed: bool,
    pub constructors: Vec<ConstructorCase>,
    pub matching_facts: MatchingFacts,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum LayoutState {
    Pending,
    Complete(Layout),
}

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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub struct ConstructorReference {
    pub variant: LayoutRef,
    pub position: usize,
}

impl Layout {
    /// variant_runtime.ml `make_layout` / `compute_matching_facts`.
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
        Self {
            unboxed: configuration.unboxed,
            constructors,
            matching_facts: MatchingFacts {
                tag_name: configuration.tag_name,
                block_types,
                literal_tags,
            },
        }
    }

    /// variant_runtime.ml `constructor_tag`: the literal of a constant
    /// constructor, or of the tag of a tagged one.
    pub fn constructor_tag(&self, position: usize) -> &LiteralTag {
        match &self.constructors[position] {
            ConstructorCase::Constant(tag) => &tag.literal,
            ConstructorCase::Block(block) => &block.tag().literal,
        }
    }

    pub fn configuration(&self) -> Configuration {
        Configuration {
            unboxed: self.unboxed,
            tag_name: self.matching_facts.tag_name.clone(),
        }
    }
    pub fn num_constants(&self) -> usize {
        self.constructors
            .iter()
            .filter(|c| matches!(c, ConstructorCase::Constant(_)))
            .count()
    }
    pub fn num_blocks(&self) -> usize {
        self.constructors.len() - self.num_constants()
    }
}

impl ConstructorReference {
    pub fn representation(self, ctx: &TypeContext) -> ConstructorCase {
        ctx.with_variant_layout(self.variant, |layout| {
            layout.constructors[self.position].clone()
        })
    }

    pub fn block_index(self, ctx: &TypeContext) -> usize {
        ctx.with_variant_layout(self.variant, |layout| {
            layout.constructors[..self.position]
                .iter()
                .filter(|case| matches!(case, ConstructorCase::Block(_)))
                .count()
        })
    }

    pub fn num_blocks(self, ctx: &TypeContext) -> usize {
        ctx.with_variant_layout(self.variant, Layout::num_blocks)
    }
}

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
            let tag = Tag { name, literal };
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
    use super::ocaml_hex_float;

    #[test]
    fn matches_ocaml_percent_h() {
        // Values printed by OCaml's `Printf.sprintf "%h"`.
        assert_eq!(ocaml_hex_float(1.0), "0x1p+0");
        assert_eq!(ocaml_hex_float(2.0), "0x1p+1");
        assert_eq!(ocaml_hex_float(1.5), "0x1.8p+0");
        assert_eq!(ocaml_hex_float(-0.5), "-0x1p-1");
        assert_eq!(ocaml_hex_float(0.1), "0x1.999999999999ap-4");
        assert_eq!(
            ocaml_hex_float(f64::from_bits(1)),
            "0x0.0000000000001p-1022"
        );
        assert_eq!(ocaml_hex_float(f64::INFINITY), "infinity");
    }
}
