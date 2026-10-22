//! Canonical JavaScript runtime representation of variant declarations.
//!
//! This mirrors `compiler/ml/variant_runtime.ml`. Layouts live in the
//! per-compilation [`TypeContext`](super::context::TypeContext); [`LayoutRef`]
//! is a stable arena index used while recursive declaration groups are being
//! completed.

use super::context::TypeContext;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub enum Instance {
    Array,
    ArrayBuffer,
    BigInt64Array,
    BigUint64Array,
    Blob,
    DataView,
    Date,
    File,
    Float32Array,
    Float64Array,
    Int16Array,
    Int32Array,
    Int8Array,
    Promise,
    RegExp,
    Uint16Array,
    Uint32Array,
    Uint8Array,
    Uint8ClampedArray,
    Set,
    Map,
    WeakSet,
    WeakMap,
}

impl Instance {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Array => "Array",
            Self::ArrayBuffer => "ArrayBuffer",
            Self::BigInt64Array => "BigInt64Array",
            Self::BigUint64Array => "BigUint64Array",
            Self::Blob => "Blob",
            Self::DataView => "DataView",
            Self::Date => "Date",
            Self::File => "File",
            Self::Float32Array => "Float32Array",
            Self::Float64Array => "Float64Array",
            Self::Int16Array => "Int16Array",
            Self::Int32Array => "Int32Array",
            Self::Int8Array => "Int8Array",
            Self::Promise => "Promise",
            Self::RegExp => "RegExp",
            Self::Uint16Array => "Uint16Array",
            Self::Uint32Array => "Uint32Array",
            Self::Uint8Array => "Uint8Array",
            Self::Uint8ClampedArray => "Uint8ClampedArray",
            Self::Set => "Set",
            Self::Map => "Map",
            Self::WeakSet => "WeakSet",
            Self::WeakMap => "WeakMap",
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub enum BlockType {
    Int,
    String,
    Float,
    Bigint,
    Boolean,
    Instance(Instance),
    Function,
    Object,
    Unknown,
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

/// OCaml `Variant_runtime.tag_type`: information used to recognize a
/// constructor during matching. A literal identifies a constant or an
/// object's tag; a payload shape identifies a value represented directly by
/// its payload.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TagType {
    Literal(LiteralTag),
    PayloadShape(BlockType),
}

/// OCaml `Variant_runtime.tag`: a constructor's name and its optional
/// explicitly declared runtime literal.
#[derive(Debug, Clone, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub struct Tag {
    pub name: String,
    pub literal: Option<LiteralTag>,
}

/// OCaml `Variant_runtime.matchable_tag`: a tag widened for matching, where
/// an untagged payload shape can take part alongside declared literals.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct MatchableTag {
    pub name: String,
    pub tag_type: Option<TagType>,
}

/// OCaml `Variant_runtime.to_matchable_tag`.
pub fn to_matchable_tag(tag: &Tag) -> MatchableTag {
    MatchableTag {
        name: tag.name.clone(),
        tag_type: tag.literal.clone().map(TagType::Literal),
    }
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
    pub block_types: Vec<BlockType>,
    pub literal_tags: Vec<LiteralTag>,
    pub has_null: bool,
    pub has_undefined: bool,
    pub has_other_literal: bool,
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
    pub fn new(configuration: Configuration, constructors: Vec<ConstructorCase>) -> Self {
        let mut block_types = Vec::new();
        let mut literal_tags = Vec::new();
        let mut has_null = false;
        let mut has_undefined = false;
        let mut has_other_literal = false;
        for case in &constructors {
            match case {
                ConstructorCase::Constant(tag) => {
                    // Without an `@as`, a nullary constructor is its own name.
                    let literal = tag
                        .literal
                        .clone()
                        .unwrap_or_else(|| LiteralTag::String(tag.name.clone()));
                    match literal {
                        LiteralTag::Null => has_null = true,
                        LiteralTag::Undefined => has_undefined = true,
                        _ => has_other_literal = true,
                    }
                    literal_tags.push(literal);
                }
                ConstructorCase::Block(block) => {
                    if let Block::Untagged { block_type, .. } = block {
                        block_types.push(block_type.clone());
                    }
                }
            }
        }
        // OCaml conses each tag onto the front of its list; build in source
        // order and reverse once to get the same order.
        block_types.reverse();
        literal_tags.reverse();
        Self {
            unboxed: configuration.unboxed,
            constructors,
            matching_facts: MatchingFacts {
                tag_name: configuration.tag_name,
                block_types,
                literal_tags,
                has_null,
                has_undefined,
                has_other_literal,
            },
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
            let tag = Tag {
                name,
                literal: None,
            };
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
