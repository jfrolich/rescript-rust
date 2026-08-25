//! Canonical JavaScript runtime representation of variant declarations.
//!
//! This mirrors `compiler/ml/variant_runtime.ml`. Layouts live in the
//! per-compilation [`TypeContext`](super::context::TypeContext); [`LayoutRef`]
//! is a stable arena index used while recursive declaration groups are being
//! completed.

use super::context::TypeContext;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
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

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
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

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TagType {
    String(String),
    Int(i32),
    Float(String),
    BigInt(String),
    Bool(bool),
    Null,
    Undefined,
    Untagged(BlockType),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Tag {
    pub name: String,
    pub tag_type: Option<TagType>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct BlockRuntime {
    pub tag: Tag,
    pub tag_name: Option<String>,
    pub untagged: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Block {
    pub runtime: BlockRuntime,
    pub block_type: Option<BlockType>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ConstructorCase {
    Constant(Tag),
    Block(Block),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Configuration {
    pub unboxed: bool,
    pub tag_name: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MatchingFacts {
    pub tag_name: Option<String>,
    pub block_types: Vec<BlockType>,
    pub literal_tags: Vec<TagType>,
    pub has_null: bool,
    pub has_undefined: bool,
    pub has_other_literal: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct LayoutRef(pub(crate) u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
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
                    let tag = tag
                        .tag_type
                        .clone()
                        .unwrap_or_else(|| TagType::String(tag.name.clone()));
                    match tag {
                        TagType::Null => has_null = true,
                        TagType::Undefined => has_undefined = true,
                        _ => has_other_literal = true,
                    }
                    literal_tags.insert(0, tag);
                }
                ConstructorCase::Block(block) => {
                    if let Some(block_type) = &block.block_type {
                        block_types.insert(0, block_type.clone());
                    }
                }
            }
        }
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
        ctx.variant_layout(self.variant).constructors[self.position].clone()
    }

    pub fn block_index(self, ctx: &TypeContext) -> usize {
        ctx.variant_layout(self.variant).constructors[..self.position]
            .iter()
            .filter(|case| matches!(case, ConstructorCase::Block(_)))
            .count()
    }

    pub fn num_blocks(self, ctx: &TypeContext) -> usize {
        ctx.variant_layout(self.variant).num_blocks()
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
                tag_type: None,
            };
            if has_payload {
                ConstructorCase::Block(Block {
                    runtime: BlockRuntime {
                        tag,
                        tag_name: None,
                        untagged: false,
                    },
                    block_type: None,
                })
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
