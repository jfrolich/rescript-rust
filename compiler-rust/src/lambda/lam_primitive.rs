//! Lambda primitives - Built-in operations.
//!
//! This module defines primitive operations that are directly compiled
//! to JavaScript operations. These include arithmetic, comparisons,
//! array/string operations, and FFI calls.

use super::lam_compat::{Comparison, FieldDbgInfo, SetFieldDbgInfo};
use super::lam_tag_info::TagInfo;

/// Record representation for optimization purposes
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RecordRepresentation {
    /// Regular record
    Regular,
    /// Inlined record (variant payload)
    Inlined {
        tag: i32,
        name: String,
        num_nonconsts: i32,
    },
    /// Extension record
    Extension,
}

/// Raw JavaScript code info
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct JsRawInfo {
    /// The JavaScript code
    pub code: String,
    /// Is this a statement or expression?
    pub is_stmt: bool,
}

/// String delimiter for external constant arguments.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExternalArgDelim {
    None,
    StarJ,
    NoQuotes,
    BackQuotes,
}

/// Constant preserved from external argument metadata.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExternalArgConst {
    IntLit(i64),
    StringLit(String, ExternalArgDelim),
}

/// OCaml external argument label metadata.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ExternalArgLabel {
    Label,
    Empty,
    Optional,
}

/// OCaml object-field label metadata for `@obj` externals.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExternalObjLabel {
    Empty,
    Label {
        name: String,
    },
    Optional {
        name: String,
        for_sure_no_nested_option: bool,
    },
}

/// OCaml external argument attribute metadata.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExternalArgAttr {
    PolyVarString {
        descr: Vec<(String, String)>,
    },
    PolyVar {
        descr: Option<Vec<(String, String)>>,
    },
    Int(Vec<(String, i64)>),
    ArgCst(ExternalArgConst),
    ExternUnit,
    Nothing,
    Ignore,
    Unwrap,
}

/// External argument specification.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExternalArgSpec {
    pub arg_type: ExternalArgAttr,
    pub arg_label: ExternalArgLabel,
}

impl ExternalArgSpec {
    pub fn dummy() -> Self {
        Self {
            arg_type: ExternalArgAttr::Nothing,
            arg_label: ExternalArgLabel::Empty,
        }
    }
}

/// `@obj` external field specification.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExternalObjSpec {
    pub obj_arg_type: ExternalArgAttr,
    pub obj_arg_label: ExternalObjLabel,
}

/// Import attributes attached to an external module binding.
pub type ImportAttributes = Vec<(String, String)>;

/// Module bind name hint for imported externals.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExternalModuleBindName {
    HintName(String),
    Nothing,
}

/// Imported external module metadata preserved from marshaled FFI info.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExternalModuleName {
    pub bundle: String,
    pub module_bind_name: ExternalModuleBindName,
    pub import_attributes: Option<ImportAttributes>,
}

/// OCaml external-spec metadata preserved for JS lowering.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExternalSpec {
    JsVar {
        name: String,
        external_module_name: Option<ExternalModuleName>,
        scopes: Vec<String>,
    },
    JsModuleAsVar(ExternalModuleName),
    JsModuleAsFn {
        external_module_name: ExternalModuleName,
        splice: bool,
    },
    JsModuleAsClass(ExternalModuleName),
    JsCall {
        name: String,
        external_module_name: Option<ExternalModuleName>,
        splice: bool,
        scopes: Vec<String>,
        tagged_template: bool,
    },
    JsSend {
        name: String,
        splice: bool,
        js_send_scopes: Vec<String>,
    },
    JsNew {
        name: String,
        external_module_name: Option<ExternalModuleName>,
        splice: bool,
        scopes: Vec<String>,
    },
    JsSet {
        js_set_name: String,
        js_set_scopes: Vec<String>,
    },
    JsGet {
        js_get_name: String,
        js_get_scopes: Vec<String>,
    },
    JsGetIndex {
        js_get_index_scopes: Vec<String>,
    },
    JsSetIndex {
        js_set_index_scopes: Vec<String>,
    },
}

/// External FFI specification
#[derive(Debug, Clone, PartialEq)]
pub struct ExternalFfiSpec {
    /// Minimal raw-ffi classification kept for optimized-lambda lowering.
    pub kind: ExternalFfiKind,
    /// OCaml external-spec metadata used by the backend after optimized lambda.
    pub spec: Option<ExternalSpec>,
    /// OCaml `@obj` field metadata preserved across lowering.
    pub obj_params: Option<Vec<ExternalObjSpec>>,
    /// How the fully applied call result should be wrapped.
    pub return_wrapper: ExternalReturnWrapper,
    /// Optional inline constant preserved from marshaled external ffi metadata.
    pub inline_constant: Option<super::lam_constant::Constant>,
}

/// Raw FFI kind preserved across the raw-lambda boundary.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ExternalFfiKind {
    Default,
    ObjCreate,
    Normal,
}

/// Result wrapping preserved for external calls.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ExternalReturnWrapper {
    Identity,
    NullToOpt,
    NullUndefinedToOpt,
    ReplacedWithUnit,
}

/// Primitive operations
///
/// These are built-in operations that compile directly to JavaScript.
#[derive(Debug, Clone, PartialEq)]
pub enum Primitive {
    // ==================== Block Operations ====================
    /// Make a block (tuple, record, variant)
    Pmakeblock(i32, TagInfo, Mutable),

    /// Get a field from a block
    Pfield(i32, FieldDbgInfo),

    /// Set a field in a block
    Psetfield(i32, SetFieldDbgInfo),

    /// Duplicate a record
    Pduprecord,

    /// Tagged template literal: `[tag, strings_array, values_array]`.
    PtaggedTemplate,

    // ==================== External Call ====================
    /// JavaScript FFI call
    PjsCall {
        prim_name: String,
        arg_types: Vec<ExternalArgSpec>,
        ffi: ExternalFfiSpec,
        dynamic_import: bool,
        transformed_jsx: bool,
    },

    /// Create a JavaScript object
    PjsObjectCreate(Vec<ExternalObjSpec>),

    // ==================== Exceptions ====================
    /// Raise an exception
    Praise,

    // ==================== Object Primitives ====================
    /// Object comparison
    Pobjcomp(Comparison),
    /// Object ordering
    Pobjorder,
    /// Object min
    Pobjmin,
    /// Object max
    Pobjmax,
    /// Get object tag
    Pobjtag,
    /// Get object size
    Pobjsize,

    // ==================== Boolean Primitives ====================
    /// Boolean and (short-circuit)
    Psequand,
    /// Boolean or (short-circuit)
    Psequor,
    /// Boolean not
    Pnot,
    /// Boolean comparison
    Pboolcomp(Comparison),
    /// Boolean ordering
    Pboolorder,
    /// Boolean min
    Pboolmin,
    /// Boolean max
    Pboolmax,

    // ==================== Integer Primitives ====================
    /// Is integer (vs block)
    Pisint,
    /// Integer negation
    Pnegint,
    /// Integer addition
    Paddint,
    /// Integer subtraction
    Psubint,
    /// Integer multiplication
    Pmulint,
    /// Integer division
    Pdivint,
    /// Integer modulo
    Pmodint,
    /// Integer power
    Ppowint,
    /// Bitwise and
    Pandint,
    /// Bitwise or
    Porint,
    /// Bitwise xor
    Pxorint,
    /// Bitwise not
    Pnotint,
    /// Left shift
    Plslint,
    /// Logical right shift
    Plsrint,
    /// Arithmetic right shift
    Pasrint,
    /// Add offset to integer
    Poffsetint(i32),
    /// Add offset to reference
    Poffsetref(i32),
    /// Integer comparison
    Pintcomp(Comparison),
    /// Integer ordering
    Pintorder,
    /// Integer min
    Pintmin,
    /// Integer max
    Pintmax,

    // ==================== Float Primitives ====================
    /// Integer of float
    Pintoffloat,
    /// Float of integer
    Pfloatofint,
    /// Float negation
    Pnegfloat,
    /// Float addition
    Paddfloat,
    /// Float subtraction
    Psubfloat,
    /// Float multiplication
    Pmulfloat,
    /// Float division
    Pdivfloat,
    /// Float modulo
    Pmodfloat,
    /// Float power
    Ppowfloat,
    /// Float comparison
    Pfloatcomp(Comparison),
    /// Float ordering
    Pfloatorder,
    /// Float min
    Pfloatmin,
    /// Float max
    Pfloatmax,

    // ==================== BigInt Primitives ====================
    /// BigInt negation
    Pnegbigint,
    /// BigInt addition
    Paddbigint,
    /// BigInt subtraction
    Psubbigint,
    /// BigInt multiplication
    Pmulbigint,
    /// BigInt division
    Pdivbigint,
    /// BigInt modulo
    Pmodbigint,
    /// BigInt power
    Ppowbigint,
    /// BigInt bitwise and
    Pandbigint,
    /// BigInt bitwise or
    Porbigint,
    /// BigInt bitwise xor
    Pxorbigint,
    /// BigInt bitwise not
    Pnotbigint,
    /// BigInt left shift
    Plslbigint,
    /// BigInt arithmetic right shift
    Pasrbigint,
    /// BigInt comparison
    Pbigintcomp(Comparison),
    /// BigInt ordering
    Pbigintorder,
    /// BigInt min
    Pbigintmin,
    /// BigInt max
    Pbigintmax,

    // ==================== String Primitives ====================
    /// String length
    Pstringlength,
    /// String char at (unsafe)
    Pstringrefu,
    /// String char at (safe)
    Pstringrefs,
    /// String concatenation
    Pstringadd,
    /// String comparison
    Pstringcomp(Comparison),
    /// String ordering
    Pstringorder,
    /// String min
    Pstringmin,
    /// String max
    Pstringmax,

    // ==================== Array Primitives ====================
    /// Make array
    Pmakearray,
    /// Array length
    Parraylength,
    /// Array get (unsafe)
    Parrayrefu,
    /// Array set (unsafe)
    Parraysetu,
    /// Array get (safe)
    Parrayrefs,
    /// Array set (safe)
    Parraysets,

    // ==================== List Primitives ====================
    /// Make list
    Pmakelist,

    // ==================== Dict Primitives ====================
    /// Make dict
    Pmakedict,
    /// Dict has key
    PdictHas,

    // ==================== Promise Primitives ====================
    /// Await promise
    Pawait,

    // ==================== Misc Primitives ====================
    /// Identity
    Pidentity,
    /// Ignore value, return unit
    Pignore,
    /// Check if polyvar block
    PisPolyVarBlock,
    /// Check if out of range
    Pisout(i32),
    /// JavaScript comparison
    Pjscomp(Comparison),
    /// Apply function
    PjsApply,
    /// Runtime apply
    PjsRuntimeApply,
    /// Debugger statement
    Pdebugger,
    /// Unsafe downgrade (method call)
    PjsUnsafeDowngrade { name: String, setter: bool },
    /// Initialize module
    PinitMod,
    /// Update module
    PupdateMod,
    /// Raw JavaScript code
    PrawJsCode(JsRawInfo),
    /// Make function with arity
    PjsFnMake(i32),
    /// Make unit function
    PjsFnMakeUnit,
    /// Method
    PjsFnMethod,
    /// Null to option
    PnullToOpt,
    /// Null or undefined to option
    PnullUndefinedToOpt,
    /// Is null
    PisNull,
    /// Is undefined
    PisUndefined,
    /// Is null or undefined
    PisNullUndefined,
    /// Null constant (raw lambda only, 0 args)
    Pnull,
    /// Undefined constant (raw lambda only, 0 args)
    Pundefined,
    /// Dynamic import
    Pimport,
    /// Typeof
    Ptypeof,
    /// Function arity
    PfnArity,
    /// Wrap exception
    PwrapExn,
    /// Create extension
    PcreateExtension(String),
    /// Compare an extensible-constructor block against an extension slot
    PextensionSlotEq,
    /// Is not none
    PisNotNone,
    /// Value from option
    PvalFromOption,
    /// Value from option (not nested)
    PvalFromOptionNotNest,
    /// Some
    Psome,
    /// Some (not nested)
    PsomeNotNest,
    /// Hash
    Phash,
    /// Hash mix string
    PhashMixstring,
    /// Hash mix int
    PhashMixint,
    /// Hash final mix
    PhashFinalmix,
}

/// Mutable flag
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Mutable {
    Mutable,
    Immutable,
}

impl Primitive {
    /// Check if two primitives are approximately equal (for optimization).
    ///
    /// 1:1 port of `Lam_primitive.eq_primitive_approx`
    /// (`compiler/core/lam_primitive.ml:197-301`). The "simple" arm at
    /// lines 199-232 in OCaml uses `rhs = lhs` (structural equality) for
    /// every nullary primitive listed there; the remaining variants get
    /// per-payload checks. `Praw_js_code _` always returns false
    /// (lam_primitive.ml:301) — ReScript treats raw JS as opaque.
    pub fn eq_approx(&self, other: &Primitive) -> bool {
        use Primitive::*;
        match self {
            // lam_primitive.ml:199-232 — the big "rhs = lhs" simple list.
            // Every nullary primitive in OCaml's eq_primitive_approx that
            // matches this arm. Mapped to Rust enum variant names.
            PwrapExn
            | Praise
            | Pobjorder
            | Pobjmin
            | Pobjmax
            | Pobjtag
            | Pobjsize
            | Psequand
            | Psequor
            | Pnot
            | Pboolorder
            | Pboolmin
            | Pboolmax
            | Pisint
            | Pnegint
            | Paddint
            | Psubint
            | Pmulint
            | Pdivint
            | Pmodint
            | Ppowint
            | Pnotint
            | Pandint
            | Porint
            | Pxorint
            | Plslint
            | Plsrint
            | Pasrint
            | Pintorder
            | Pintmin
            | Pintmax
            | Pintoffloat
            | Pfloatofint
            | Pnegfloat
            | Paddfloat
            | Psubfloat
            | Pmulfloat
            | Pdivfloat
            | Pmodfloat
            | Ppowfloat
            | Pfloatorder
            | Pfloatmin
            | Pfloatmax
            | Pnegbigint
            | Paddbigint
            | Psubbigint
            | Pmulbigint
            | Pdivbigint
            | Pmodbigint
            | Ppowbigint
            | Pnotbigint
            | Pandbigint
            | Porbigint
            | Pxorbigint
            | Plslbigint
            | Pasrbigint
            | Pbigintorder
            | Pbigintmin
            | Pbigintmax
            | Pstringlength
            | Pstringrefu
            | Pstringrefs
            | Pstringadd
            | Pstringorder
            | Pstringmin
            | Pstringmax
            | Pmakelist
            | Pmakedict
            | PdictHas
            | Pawait
            | PjsApply
            | PjsRuntimeApply
            | PvalFromOption
            | PvalFromOptionNotNest
            | PnullToOpt
            | PnullUndefinedToOpt
            | PisNull
            | PisNotNone
            | Psome
            | PsomeNotNest
            | PisUndefined
            | PisNullUndefined
            | Pimport
            | Ptypeof
            | PfnArity
            | PisPolyVarBlock
            | Pdebugger
            | PinitMod
            | PupdateMod
            | Pduprecord
            | PtaggedTemplate
            | Pmakearray
            | Parraylength
            | Parrayrefu
            | Parraysetu
            | Parrayrefs
            | Parraysets
            | PjsFnMakeUnit
            | PjsFnMethod
            | Phash
            | PhashMixstring
            | PhashMixint
            | PhashFinalmix => self == other,

            // Rust-only nullary primitives that have no OCaml counterpart in
            // the eq_primitive_approx switch. They are still nullary; treat
            // them like the simple list — `self == other` matches when both
            // are the same constructor. This is the safe and consistent
            // generalization (no payload to compare differently).
            Pidentity | Pignore | PextensionSlotEq | Pnull | Pundefined => self == other,

            // lam_primitive.ml:233-236
            PcreateExtension(a) => match other {
                PcreateExtension(b) => a == b,
                _ => false,
            },
            // lam_primitive.ml:237-240
            Pisout(l) => match other {
                Pisout(r) => l == r,
                _ => false,
            },
            // lam_primitive.ml:242-245
            Pfield(n0, info0) => match other {
                Pfield(n1, info1) => n0 == n1 && info0 == info1,
                _ => false,
            },
            // lam_primitive.ml:246-249
            Psetfield(i0, info0) => match other {
                Psetfield(i1, info1) => i0 == i1 && info0 == info1,
                _ => false,
            },
            // lam_primitive.ml:250-254
            Pmakeblock(i0, info0, flag0) => match other {
                Pmakeblock(i1, info1, flag1) => i0 == i1 && flag0 == flag1 && info0 == info1,
                _ => false,
            },
            // lam_primitive.ml:255-260: Pjs_call only checks
            // prim_name + arg_types + ffi + dynamic_import
            // (NOT transformed_jsx).
            PjsCall {
                prim_name,
                arg_types,
                ffi,
                dynamic_import,
                transformed_jsx: _,
            } => match other {
                PjsCall {
                    prim_name: pn,
                    arg_types: at,
                    ffi: f,
                    dynamic_import: di,
                    transformed_jsx: _,
                } => prim_name == pn && arg_types == at && ffi == f && dynamic_import == di,
                _ => false,
            },
            // lam_primitive.ml:261-264
            PjsObjectCreate(obj0) => match other {
                PjsObjectCreate(obj1) => obj0 == obj1,
                _ => false,
            },
            // lam_primitive.ml:265-268
            Pobjcomp(c) => matches!(other, Pobjcomp(c2) if c == c2),
            // lam_primitive.ml:269-272
            Pintcomp(c) => matches!(other, Pintcomp(c2) if c == c2),
            // lam_primitive.ml:273-276
            Pfloatcomp(c) => matches!(other, Pfloatcomp(c2) if c == c2),
            // lam_primitive.ml:277-280
            Pbigintcomp(c) => matches!(other, Pbigintcomp(c2) if c == c2),
            // lam_primitive.ml:281-284
            Pjscomp(c) => matches!(other, Pjscomp(c2) if c == c2),
            // Rust groups Pstringcomp / Pboolcomp under the comparison rule,
            // mirroring the OCaml comparison treatment.
            Pstringcomp(c) => matches!(other, Pstringcomp(c2) if c == c2),
            Pboolcomp(c) => matches!(other, Pboolcomp(c2) if c == c2),
            // lam_primitive.ml:285-288
            Poffsetint(i0) => match other {
                Poffsetint(i1) => i0 == i1,
                _ => false,
            },
            // lam_primitive.ml:289-292
            Poffsetref(i0) => match other {
                Poffsetref(i1) => i0 == i1,
                _ => false,
            },
            // lam_primitive.ml:293-296
            PjsUnsafeDowngrade { name, setter } => match other {
                PjsUnsafeDowngrade {
                    name: n1,
                    setter: s1,
                } => name == n1 && setter == s1,
                _ => false,
            },
            // lam_primitive.ml:297-300
            PjsFnMake(i) => match other {
                PjsFnMake(i1) => i == i1,
                _ => false,
            },
            // lam_primitive.ml:301
            PrawJsCode(_) => false,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_primitive_eq_approx() {
        assert!(Primitive::Paddint.eq_approx(&Primitive::Paddint));
        assert!(!Primitive::Paddint.eq_approx(&Primitive::Psubint));

        assert!(
            Primitive::Pintcomp(Comparison::Eq).eq_approx(&Primitive::Pintcomp(Comparison::Eq))
        );
        assert!(
            !Primitive::Pintcomp(Comparison::Eq).eq_approx(&Primitive::Pintcomp(Comparison::Neq))
        );

        assert!(Primitive::Poffsetint(5).eq_approx(&Primitive::Poffsetint(5)));
        assert!(!Primitive::Poffsetint(5).eq_approx(&Primitive::Poffsetint(10)));
    }

    #[test]
    fn test_raw_js_never_equal() {
        let raw1 = Primitive::PrawJsCode(JsRawInfo {
            code: "console.log(1)".to_string(),
            is_stmt: true,
        });
        let raw2 = Primitive::PrawJsCode(JsRawInfo {
            code: "console.log(1)".to_string(),
            is_stmt: true,
        });
        assert!(!raw1.eq_approx(&raw2));
    }
}
