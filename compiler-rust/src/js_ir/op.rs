//! JavaScript operators and types.
//!
//! This module defines JavaScript-specific operators and types used
//! in the JS IR, including binary operators, property access, and
//! number representations.

use crate::lambda::lam_compat::LetKind;

/// Binary operators
#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum BinOp {
    /// Assignment (=)
    Eq,
    /// Logical or (||)
    Or,
    /// Logical and (&&)
    And,
    /// Strict equality (===)
    EqEqEq,
    /// Strict inequality (!==)
    NotEqEq,
    /// Less than (<)
    Lt,
    /// Less than or equal (<=)
    Le,
    /// Greater than (>)
    Gt,
    /// Greater than or equal (>=)
    Ge,
    /// `<`, `<=`, `>`, `>=` for operands that may be NaN (js_op.ml
    /// `Float_lt`...), so that negating them can't swap the operator:
    /// `!(a < b)` is not `a >= b` when `a` or `b` is NaN.
    FloatLt,
    /// `<=` for operands that may be NaN.
    FloatLe,
    /// `>` for operands that may be NaN.
    FloatGt,
    /// `>=` for operands that may be NaN.
    FloatGe,
    /// Bitwise not (~)
    Bnot,
    /// Bitwise or (|)
    Bor,
    /// Bitwise xor (^)
    Bxor,
    /// Bitwise and (&)
    Band,
    /// Left shift (<<)
    Lsl,
    /// Logical right shift (>>>)
    Lsr,
    /// Arithmetic right shift (>>)
    Asr,
    /// Addition (+)
    Plus,
    /// Subtraction (-)
    Minus,
    /// Multiplication (*)
    Mul,
    /// Division (/)
    Div,
    /// Modulo (%)
    Mod,
    /// Exponentiation (**)
    Pow,
    /// instanceof operator
    InstanceOf,
    /// in operator
    In,
}

impl BinOp {
    /// Get the JavaScript string representation
    pub fn to_js_string(self) -> &'static str {
        match self {
            BinOp::Eq => "=",
            BinOp::Or => "||",
            BinOp::And => "&&",
            BinOp::EqEqEq => "===",
            BinOp::NotEqEq => "!==",
            BinOp::Lt | BinOp::FloatLt => "<",
            BinOp::Le | BinOp::FloatLe => "<=",
            BinOp::Gt | BinOp::FloatGt => ">",
            BinOp::Ge | BinOp::FloatGe => ">=",
            BinOp::Bnot => "~",
            BinOp::Bor => "|",
            BinOp::Bxor => "^",
            BinOp::Band => "&",
            BinOp::Lsl => "<<",
            BinOp::Lsr => ">>>",
            BinOp::Asr => ">>",
            BinOp::Plus => "+",
            BinOp::Minus => "-",
            BinOp::Mul => "*",
            BinOp::Div => "/",
            BinOp::Mod => "%",
            BinOp::Pow => "**",
            BinOp::InstanceOf => "instanceof",
            BinOp::In => "in",
        }
    }
}

/// Module kind
#[derive(Debug, Clone, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub enum Kind {
    /// OCaml/ReScript module
    Ml,
    /// Runtime module
    Runtime,
    /// External JavaScript module
    External {
        /// The module specifier passed to `import` or `require`.
        name: String,
        /// Whether the binding is the module's default export.
        default: bool,
        /// The `with { ... }` attributes of an ES import, if any.
        import_attributes: Option<ImportAttributes>,
    },
}

/// Import attributes for ES modules
#[derive(Debug, Clone, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub struct ImportAttributes {
    /// Attribute key-value pairs in OCaml hashtable traversal order.
    pub entries: Vec<(String, String)>,
}

/// Variable property (let binding semantics)
pub type Property = LetKind;

/// Property name in object literals
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum PropertyName {
    /// Literal string property
    Lit(String),
    /// Symbol property
    Symbol,
}

impl PropertyName {
    /// Create a literal property name
    pub fn lit(s: impl Into<String>) -> Self {
        PropertyName::Lit(s.into())
    }
}

/// Float literal
#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub struct FloatLit {
    /// The float value as a string (preserves precision)
    pub f: String,
}

/// BigInt literal
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct BigIntLit {
    /// Is this a positive number?
    pub positive: bool,
    /// The value as a string
    pub value: String,
}

/// Number literal
#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub enum Number {
    /// Float number
    Float(FloatLit),
    /// Integer with optional character representation
    Int {
        /// The integer value
        i: i32,
        /// Optional character code point
        c: Option<i32>,
    },
    /// BigInt
    BigInt(BigIntLit),
}

impl Number {
    /// Create an integer number
    pub fn int(i: i32) -> Self {
        Number::Int { i, c: None }
    }

    /// Create a character number
    pub fn char(c: char) -> Self {
        Number::Int {
            i: c as i32,
            c: Some(c as i32),
        }
    }

    /// Create a float number
    pub fn float(f: impl Into<String>) -> Self {
        Number::Float(FloatLit { f: f.into() })
    }

    /// Create a bigint number
    pub fn bigint(positive: bool, value: impl Into<String>) -> Self {
        Number::BigInt(BigIntLit {
            positive,
            value: value.into(),
        })
    }
}

/// Mutable flag for arrays/objects
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default, serde::Serialize, serde::Deserialize)]
pub enum MutableFlag {
    /// Mutable
    Mutable,
    /// Immutable
    #[default]
    Immutable,
    /// Not applicable
    NA,
}

/// Used statistics for dead code elimination
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default, serde::Serialize, serde::Deserialize)]
pub enum UsedStats {
    /// Dead and pure (can be removed)
    DeadPure,
    /// Dead but has side effects
    DeadNonPure,
    /// Exported (cannot be removed)
    Exported,
    /// Used once and pure (candidate for inlining)
    OncePure,
    /// Used
    #[default]
    Used,
    /// Currently scanning (pure)
    ScanningPure,
    /// Currently scanning (non-pure)
    ScanningNonPure,
    /// Not applicable
    NA,
}

/// Identifier usage info
#[derive(Debug, Clone, Default, serde::Serialize, serde::Deserialize)]
pub struct IdentInfo {
    /// Usage statistics
    pub used_stats: UsedStats,
}

/// Length object type (for .length property)
#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum LengthObject {
    /// An array.
    Array,
    /// A string.
    String,
    /// A byte sequence.
    Bytes,
    /// A function (its `length` is its arity).
    Function,
    /// A block: a record, tuple or variant payload.
    CamlBlock,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_binop_to_string() {
        assert_eq!(BinOp::Plus.to_js_string(), "+");
        assert_eq!(BinOp::EqEqEq.to_js_string(), "===");
        assert_eq!(BinOp::And.to_js_string(), "&&");
    }

    #[test]
    fn test_number_creation() {
        let int = Number::int(42);
        match int {
            Number::Int { i: 42, c: None } => {}
            _ => panic!("Expected Int(42)"),
        }

        let char_num = Number::char('A');
        match char_num {
            Number::Int { i: 65, c: Some(65) } => {}
            _ => panic!("Expected Int(65)"),
        }

        let float = Number::float("3.14");
        match float {
            Number::Float(FloatLit { ref f }) => assert_eq!(f, "3.14"),
            _ => panic!("Expected Float"),
        }
    }
}
