//! Lambda constants - Compile-time constant values.
//!
//! This module defines constant values that can appear in Lambda IR.
//! These include primitive values like integers and strings, as well
//! as compound structures like blocks (for variants and records).

use super::lam_tag_info::TagInfo;

/// Pointer info for tracking constructor origins
#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub enum PointerInfo {
    /// No specific info
    None,
    /// Constructor with tag information
    Constructor(ConstructorTag),
    /// Option `None` shape (`Pt_shape_none` in OCaml lambda).
    ShapeNone,
    /// Assert false (for exhaustiveness)
    AssertFalse,
    /// Named pointer payload
    Some(String),
    /// Polymorphic variant tag name
    PolyVariant(String),
}

/// Constructor tag information
#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub struct ConstructorTag {
    /// Constructor name
    pub name: String,
    /// Number of constant constructors
    pub const_: i32,
    /// Number of non-constant constructors
    pub non_const: i32,
    /// Optional runtime tag payload from @as(...)
    pub runtime_tag: Option<ConstructorRuntimeTag>,
}

/// Runtime representation selected for an untagged variant constructor.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum ConstructorRuntimeTag {
    /// An integer literal.
    Int(i64),
    /// A string literal.
    String(String),
    /// A float literal, in its source text.
    Float(String),
    /// A bigint literal, in its source text.
    BigInt(String),
    /// A boolean literal.
    Bool(bool),
    /// `null`.
    Null,
    /// `undefined`.
    Undefined,
}

/// Lambda constant values
///
/// These represent compile-time constant values that can be embedded
/// directly in the generated JavaScript.
#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub enum Constant {
    /// JavaScript null
    JsNull,

    /// JavaScript undefined (with unit flag)
    JsUndefined {
        /// Is this the unit value `()`?
        is_unit: bool,
    },

    /// JavaScript true
    JsTrue,

    /// JavaScript false
    JsFalse,

    /// Integer constant
    Int {
        /// The integer value (32-bit)
        i: i32,
        /// Optional comment/info about the integer
        comment: Option<Box<PointerInfo>>,
    },

    /// Native integer constant kept at 64-bit width.
    NativeInt {
        /// The integer value (64-bit)
        i: i64,
        /// Optional comment/info about the integer
        comment: Option<Box<PointerInfo>>,
    },

    /// Nullary nominal constructor with its canonical runtime tag.
    Constructor(crate::types::VariantTag),

    /// Character constant (stored as Unicode code point)
    Char(i32),

    /// A decoded runtime string value; literal source spelling is no longer
    /// present at this layer.
    String(String),

    /// Immutable string constant (`Const_immstring` in OCaml lambda)
    ImmString(String),

    /// Float constant (stored as string to preserve precision)
    Float(String),

    /// BigInt constant
    BigInt {
        /// Is this negative?
        negative: bool,
        /// The BigInt value as a string
        value: String,
    },

    /// Pointer constant (for polyvar tags etc.)
    Pointer(String),

    /// Block constant (for variants, records, tuples)
    Block {
        /// Tag info for debugging/codegen
        tag_info: Box<TagInfo>,
        /// Block elements
        elements: Vec<Constant>,
    },

    /// Some value (for option type)
    Some(Box<Constant>),

    /// Module alias marker
    ModuleAlias,
}

impl Constant {
    /// Create an integer constant
    pub fn int(i: i32) -> Self {
        Constant::Int { i, comment: None }
    }

    /// Create an integer constant with a comment
    pub fn int_with_comment(i: i32, comment: PointerInfo) -> Self {
        Constant::Int {
            i,
            comment: Some(Box::new(comment)),
        }
    }

    /// Create a string constant (`Lambda.Lift.string`).
    pub fn string(s: impl Into<String>) -> Self {
        Constant::String(s.into())
    }

    /// `Lambda.const_string`: a compiler-generated semantic string constant,
    /// normalizing malformed filesystem or legacy bytes.
    pub fn const_string(s: &str) -> Self {
        Constant::String(crate::string_literal::normalize_semantic(s).into_owned())
    }

    /// Create an immutable string constant.
    pub fn immstring(s: impl Into<String>) -> Self {
        Constant::ImmString(s.into())
    }

    /// Create a float constant
    pub fn float(s: impl Into<String>) -> Self {
        Constant::Float(s.into())
    }

    /// Create a char constant
    pub fn char(c: char) -> Self {
        Constant::Char(c as i32)
    }

    /// Create a bigint constant
    pub fn bigint(negative: bool, value: impl Into<String>) -> Self {
        Constant::BigInt {
            negative,
            value: value.into(),
        }
    }

    /// Check if this constant is the "none" option value
    pub fn is_none(&self) -> bool {
        matches!(self, Constant::JsUndefined { is_unit: false })
    }

    /// Create the "none" option value
    pub fn none() -> Self {
        Constant::JsUndefined { is_unit: false }
    }

    /// Check if this constant requires allocation at runtime.
    ///
    /// Direct port of OCaml's `Lam_constant.is_allocating`
    /// (compiler/frontend/lam_constant.ml:104-111). Note `Const_some inner`
    /// recurses into `inner`: `Const_some (Const_string "v1")` is
    /// non-allocating because `Const_some` only inserts a JS object wrapper
    /// when the inner already requires one (the JS lowering folds nested
    /// non-allocating `Some` values into the literal). The original Rust
    /// code returned `true` for every `Constant::Some`, which blocked
    /// `field_flatten_get` from lifting non-allocating optional record
    /// fields like `{x1: ?Some("v1")}` out of the parent constant block.
    pub fn is_allocating(&self) -> bool {
        match self {
            Constant::Block { .. } => true,
            Constant::Some(inner) => inner.is_allocating(),
            Constant::JsNull
            | Constant::JsUndefined { .. }
            | Constant::JsTrue
            | Constant::JsFalse
            | Constant::Int { .. }
            | Constant::Constructor(_)
            | Constant::NativeInt { .. }
            | Constant::Char(_)
            | Constant::String(_)
            | Constant::ImmString(_)
            | Constant::Float(_)
            | Constant::BigInt { .. }
            | Constant::Pointer(_)
            | Constant::ModuleAlias => false,
        }
    }

    /// Approximate equality check (for optimization)
    pub fn eq_approx(&self, other: &Constant) -> bool {
        match (self, other) {
            (Constant::JsNull, Constant::JsNull) => true,
            (Constant::JsUndefined { is_unit: a }, Constant::JsUndefined { is_unit: b }) => a == b,
            (Constant::JsTrue, Constant::JsTrue) => true,
            (Constant::JsFalse, Constant::JsFalse) => true,
            (Constant::Int { i: a, .. }, Constant::Int { i: b, .. }) => a == b,
            (Constant::Constructor(a), Constant::Constructor(b)) => a == b,
            (Constant::NativeInt { i: a, .. }, Constant::NativeInt { i: b, .. }) => a == b,
            (Constant::Char(a), Constant::Char(b)) => a == b,
            (Constant::String(a), Constant::String(b)) => a == b,
            (Constant::ImmString(a), Constant::ImmString(b)) => a == b,
            (Constant::Float(a), Constant::Float(b)) => a == b,
            (
                Constant::BigInt {
                    negative: na,
                    value: va,
                },
                Constant::BigInt {
                    negative: nb,
                    value: vb,
                },
            ) => na == nb && va == vb,
            (Constant::Pointer(a), Constant::Pointer(b)) => a == b,
            (
                Constant::Block {
                    tag_info: ta,
                    elements: ea,
                },
                Constant::Block {
                    tag_info: tb,
                    elements: eb,
                },
            ) => {
                ta == tb
                    && ea.len() == eb.len()
                    && ea.iter().zip(eb.iter()).all(|(a, b)| a.eq_approx(b))
            }
            (Constant::Some(a), Constant::Some(b)) => a.eq_approx(b),
            (Constant::ModuleAlias, Constant::ModuleAlias) => true,
            _ => false,
        }
    }

    /// Evaluate this constant as a boolean (for constant folding)
    pub fn eval_as_bool(&self) -> bool {
        match self {
            Constant::Int { i, .. } => *i != 0,
            Constant::NativeInt { i, .. } => *i != 0,
            Constant::Constructor(tag) => match &tag.literal {
                None => tag.name != "[]",
                Some(crate::types::VariantLiteralTag::String(value)) => !value.is_empty(),
                Some(crate::types::VariantLiteralTag::Int(value)) => *value != 0,
                Some(crate::types::VariantLiteralTag::Bool(value)) => *value,
                Some(
                    crate::types::VariantLiteralTag::Null
                    | crate::types::VariantLiteralTag::Undefined,
                ) => false,
                Some(
                    crate::types::VariantLiteralTag::Float(_)
                    | crate::types::VariantLiteralTag::BigInt(_),
                ) => true,
            },
            Constant::Char(c) => *c != 0,
            Constant::JsFalse
            | Constant::JsNull
            | Constant::ModuleAlias
            | Constant::JsUndefined { .. } => false,
            Constant::JsTrue
            | Constant::String(_)
            | Constant::ImmString(_)
            | Constant::Pointer(_)
            | Constant::Float(_)
            | Constant::BigInt { .. }
            | Constant::Block { .. } => true,
            Constant::Some(inner) => inner.eval_as_bool(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_int_constant() {
        let c = Constant::int(42);
        match c {
            Constant::Int {
                i: 42,
                comment: None,
            } => {}
            _ => panic!("Expected Int(42)"),
        }
    }

    #[test]
    fn test_string_constant() {
        let c = Constant::string("hello");
        match c {
            Constant::String(s) => assert_eq!(s, "hello"),
            _ => panic!("Expected String"),
        }
    }

    #[test]
    fn test_immstring_constant() {
        let c = Constant::immstring("hello");
        match c {
            Constant::ImmString(s) => assert_eq!(s, "hello"),
            _ => panic!("Expected ImmString"),
        }
    }

    #[test]
    fn test_eq_approx() {
        assert!(Constant::int(42).eq_approx(&Constant::int(42)));
        assert!(!Constant::int(42).eq_approx(&Constant::int(43)));

        assert!(Constant::string("hello").eq_approx(&Constant::string("hello")));
        assert!(!Constant::string("hello").eq_approx(&Constant::string("world")));

        assert!(Constant::JsTrue.eq_approx(&Constant::JsTrue));
        assert!(!Constant::JsTrue.eq_approx(&Constant::JsFalse));
    }

    #[test]
    fn test_eval_as_bool() {
        assert!(Constant::JsTrue.eval_as_bool());
        assert!(!Constant::JsFalse.eval_as_bool());
        assert!(Constant::int(1).eval_as_bool());
        assert!(!Constant::int(0).eval_as_bool());
        assert!(Constant::string("hello").eval_as_bool());
        assert!(!Constant::JsNull.eval_as_bool());
    }

    #[test]
    fn test_is_allocating() {
        assert!(!Constant::int(42).is_allocating());
        assert!(!Constant::string("hello").is_allocating());
        // OCaml's `is_allocating` (lam_constant.ml:104-111) recurses into
        // `Const_some inner`, so a non-allocating inner makes the whole
        // `Some` non-allocating.
        assert!(!Constant::Some(Box::new(Constant::int(42))).is_allocating());
        assert!(
            Constant::Some(Box::new(Constant::Block {
                tag_info: Box::new(TagInfo::Tuple),
                elements: vec![Constant::int(1)],
            }))
            .is_allocating()
        );
        assert!(
            Constant::Block {
                tag_info: Box::new(TagInfo::Tuple),
                elements: vec![Constant::int(1), Constant::int(2)],
            }
            .is_allocating()
        );
    }
}
