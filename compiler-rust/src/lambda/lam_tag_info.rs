//! Tag info - Block tag information for variants and records.
//!
//! This module defines tag information used to describe the structure
//! of heap-allocated blocks (variants, records, tuples, etc.).

use crate::ident::Ident;
use crate::parser::ast::MutableFlag;

/// Block tag information
///
/// Describes the kind of block being created, which affects code generation.
#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub enum TagInfo {
    /// Constructor block (variant)
    Constructor(Box<ConstructorTag>),

    /// Inlined record (record inside a variant)
    RecordInlined(Box<RecordInlinedTag>),

    /// Tuple
    Tuple,

    /// Polymorphic variant
    PolyVar(String),

    /// Regular record
    Record(Box<RecordTag>),

    /// Module block
    Module(Vec<String>),

    /// Module export block
    ModuleExport(Vec<Ident>),

    /// Extension block
    Extension,

    /// Some value (option type)
    Some,

    /// Some value that is not nested
    SomeNotNested,

    /// Record extension block
    RecordExt {
        fields: Vec<String>,
        mutable_flag: MutableFlag,
    },
}

// The constructor and record payloads are boxed so `TagInfo` stays at 32
// bytes and `Primitive::Pmakeblock` does not size every primitive.

/// [`TagInfo::Constructor`] payload.
#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub struct ConstructorTag {
    pub name: String,
    pub num_nonconst: i32,
    /// Untagged scalar constructors are erased during typedtree
    /// translation; they cannot form Lambda or JavaScript blocks.
    pub runtime: Box<crate::types::TaggedBlock>,
}

/// [`TagInfo::RecordInlined`] payload.
#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub struct RecordInlinedTag {
    pub name: String,
    pub num_nonconst: i32,
    /// `(name, optional)` per field.
    pub fields: Vec<(String, bool)>,
    pub logical_field_count: Option<usize>,
    pub mutable_flag: MutableFlag,
    pub runtime: Box<crate::types::VariantBlock>,
}

/// [`TagInfo::Record`] payload.
#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub struct RecordTag {
    /// `(name, optional)` per field.
    pub fields: Vec<(String, bool)>,
    pub logical_field_count: Option<usize>,
    pub mutable_flag: MutableFlag,
    /// `RecordArray`: the fields are the elements of a JavaScript array.
    pub array: bool,
}

impl TagInfo {
    /// Label used by Lambda printers now that blocks carry no numeric tag.
    pub fn tag_label(&self) -> &str {
        match self {
            TagInfo::Constructor(c) => &c.name,
            TagInfo::RecordInlined(r) => &r.name,
            _ => "0",
        }
    }

    /// Get the mutable flag for this block type
    pub fn mutable_flag(&self) -> MutableFlag {
        match self {
            TagInfo::RecordInlined(r) => r.mutable_flag,
            TagInfo::Record(r) => r.mutable_flag,
            TagInfo::RecordExt { mutable_flag, .. } => *mutable_flag,
            TagInfo::Tuple
            | TagInfo::Constructor(_)
            | TagInfo::PolyVar(_)
            | TagInfo::Module(_)
            | TagInfo::ModuleExport(_)
            | TagInfo::Extension
            | TagInfo::Some
            | TagInfo::SomeNotNested => MutableFlag::Immutable,
        }
    }

    /// Create a ref tag info (mutable record with "contents" field)
    pub fn ref_tag() -> Self {
        TagInfo::Record(Box::new(RecordTag {
            fields: vec![("contents".to_string(), false)],
            logical_field_count: None,
            mutable_flag: MutableFlag::Mutable,
            array: false,
        }))
    }

    /// Create a constructor tag info
    pub fn constructor(name: impl Into<String>, num_nonconst: i32) -> Self {
        let name = name.into();
        TagInfo::Constructor(Box::new(ConstructorTag {
            runtime: Box::new(crate::types::TaggedBlock {
                // ast_untagged_variants.ml `generated_tag`: a constructor
                // the compiler generates is represented by its name.
                tag: crate::types::VariantTag {
                    name: crate::name::Name::new(&name),
                    literal: crate::types::VariantLiteralTag::String(name.clone()),
                },
                tag_name: None,
            }),
            name,
            num_nonconst,
        }))
    }

    /// Create a tuple tag info
    pub fn tuple() -> Self {
        TagInfo::Tuple
    }

    /// Create a polyvar tag info
    pub fn poly_var(name: impl Into<String>) -> Self {
        TagInfo::PolyVar(name.into())
    }

    /// Create a record tag info
    pub fn record(fields: Vec<(String, bool)>, mutable_flag: MutableFlag) -> Self {
        TagInfo::Record(Box::new(RecordTag {
            fields,
            logical_field_count: None,
            mutable_flag,
            array: false,
        }))
    }

    /// Number of fields visible to OCaml-shape optimization decisions.
    pub fn logical_field_count(&self) -> usize {
        match self {
            TagInfo::Record(r) => r.logical_field_count.unwrap_or(r.fields.len()),
            TagInfo::RecordInlined(r) => r.logical_field_count.unwrap_or(r.fields.len()),
            _ => 0,
        }
    }

    /// `(name, optional)` per field of a record or inlined record block.
    pub fn record_fields(&self) -> Option<&[(String, bool)]> {
        match self {
            TagInfo::Record(r) => Some(&r.fields),
            TagInfo::RecordInlined(r) => Some(&r.fields),
            _ => None,
        }
    }

    /// Create a module tag info
    pub fn module(fields: Vec<String>) -> Self {
        TagInfo::Module(fields)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_tag_values() {
        let cons = TagInfo::constructor("Some", 1);
        assert!(matches!(cons, TagInfo::Constructor(_)));

        let cons2 = TagInfo::constructor("Cons", 2);
        assert!(matches!(cons2, TagInfo::Constructor(_)));

        let tuple = TagInfo::tuple();
        assert!(matches!(tuple, TagInfo::Tuple));
    }

    #[test]
    fn test_mutable_flag() {
        let immutable_record =
            TagInfo::record(vec![("x".to_string(), false)], MutableFlag::Immutable);
        assert_eq!(immutable_record.mutable_flag(), MutableFlag::Immutable);

        let ref_tag = TagInfo::ref_tag();
        assert_eq!(ref_tag.mutable_flag(), MutableFlag::Mutable);

        let tuple = TagInfo::tuple();
        assert_eq!(tuple.mutable_flag(), MutableFlag::Immutable);
    }

    #[test]
    fn test_ref_tag() {
        let ref_tag = TagInfo::ref_tag();
        match ref_tag {
            TagInfo::Record(r) => {
                assert_eq!(r.fields.len(), 1);
                assert_eq!(r.fields[0].0, "contents");
                assert!(!r.fields[0].1); // not optional
                assert_eq!(r.mutable_flag, MutableFlag::Mutable);
            }
            _ => panic!("Expected Record"),
        }
    }
}
