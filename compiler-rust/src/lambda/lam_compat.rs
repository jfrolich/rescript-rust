//! Lambda compatibility types.
//!
//! This module contains types that are shared between Lambda IR and other
//! parts of the compiler, maintaining compatibility with the OCaml types.

use crate::name::Name;

/// Comparison operators
#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum Comparison {
    /// Equal
    Eq,
    /// Not equal
    Neq,
    /// Less than
    Lt,
    /// Greater than
    Gt,
    /// Less than or equal
    Le,
    /// Greater than or equal
    Ge,
}

impl Comparison {
    /// Compare two i32 values
    pub fn cmp_int32(self, a: i32, b: i32) -> bool {
        match self {
            Comparison::Eq => a == b,
            Comparison::Neq => a != b,
            Comparison::Lt => a < b,
            Comparison::Gt => a > b,
            Comparison::Le => a <= b,
            Comparison::Ge => a >= b,
        }
    }

    /// Compare two f64 values
    pub fn cmp_float(self, a: f64, b: f64) -> bool {
        match self {
            Comparison::Eq => a == b,
            Comparison::Neq => a != b,
            Comparison::Lt => a < b,
            Comparison::Gt => a > b,
            Comparison::Le => a <= b,
            Comparison::Ge => a >= b,
        }
    }
}

/// Let binding kind
#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum LetKind {
    /// Strict evaluation (evaluated immediately)
    Strict,
    /// Alias (may be inlined)
    Alias,
    /// Strict evaluation with optional unused binding
    StrictOpt,
    /// Variable (mutable)
    Variable,
}

/// Field debug info for record/tuple field access
#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum FieldDbgInfo {
    /// Record field
    Record { name: Name },
    /// Module field
    Module { name: Name },
    /// Inlined record field
    RecordInline { name: Name },
    /// Record extension field
    RecordExtension { name: Name },
    /// Tuple field
    Tuple,
    /// Poly variant tag
    PolyVarTag,
    /// Poly variant content
    PolyVarContent,
    /// Extension field
    Extension,
    /// Variant field
    Variant,
    /// Variant TAG field
    VariantTag,
    /// List cons field
    Cons,
}

impl FieldDbgInfo {
    /// Get the field name if available
    pub fn name(&self) -> Option<&str> {
        match self {
            FieldDbgInfo::Record { name }
            | FieldDbgInfo::Module { name }
            | FieldDbgInfo::RecordInline { name }
            | FieldDbgInfo::RecordExtension { name } => Some(name.as_str()),
            FieldDbgInfo::Tuple
            | FieldDbgInfo::PolyVarTag
            | FieldDbgInfo::PolyVarContent
            | FieldDbgInfo::Extension
            | FieldDbgInfo::Variant
            | FieldDbgInfo::VariantTag
            | FieldDbgInfo::Cons => None,
        }
    }
}

/// Set field debug info for record field mutation
#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum SetFieldDbgInfo {
    /// Record set
    RecordSet(Name),
    /// Inlined record set
    RecordInlineSet(Name),
    /// Record extension set
    RecordExtensionSet(Name),
}

impl SetFieldDbgInfo {
    /// Get the field name
    pub fn name(&self) -> &str {
        match self {
            SetFieldDbgInfo::RecordSet(name)
            | SetFieldDbgInfo::RecordInlineSet(name)
            | SetFieldDbgInfo::RecordExtensionSet(name) => name.as_str(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_comparison_int32() {
        assert!(Comparison::Eq.cmp_int32(5, 5));
        assert!(!Comparison::Eq.cmp_int32(5, 6));

        assert!(Comparison::Neq.cmp_int32(5, 6));
        assert!(!Comparison::Neq.cmp_int32(5, 5));

        assert!(Comparison::Lt.cmp_int32(5, 6));
        assert!(!Comparison::Lt.cmp_int32(6, 5));

        assert!(Comparison::Gt.cmp_int32(6, 5));
        assert!(!Comparison::Gt.cmp_int32(5, 6));

        assert!(Comparison::Le.cmp_int32(5, 5));
        assert!(Comparison::Le.cmp_int32(5, 6));
        assert!(!Comparison::Le.cmp_int32(6, 5));

        assert!(Comparison::Ge.cmp_int32(5, 5));
        assert!(Comparison::Ge.cmp_int32(6, 5));
        assert!(!Comparison::Ge.cmp_int32(5, 6));
    }

    #[test]
    fn test_comparison_float() {
        assert!(Comparison::Eq.cmp_float(5.0, 5.0));
        assert!(!Comparison::Eq.cmp_float(5.0, 5.1));

        assert!(Comparison::Lt.cmp_float(5.0, 5.1));
        assert!(Comparison::Gt.cmp_float(5.1, 5.0));
    }

    #[test]
    fn test_field_dbg_info_name() {
        let record = FieldDbgInfo::Record {
            name: Name::new("field"),
        };
        assert_eq!(record.name(), Some("field"));

        let tuple = FieldDbgInfo::Tuple;
        assert_eq!(tuple.name(), None);
    }

    #[test]
    fn test_set_field_dbg_info_name() {
        let set = SetFieldDbgInfo::RecordSet(Name::new("contents"));
        assert_eq!(set.name(), "contents");
    }
}
