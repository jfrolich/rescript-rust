//! Lambda primitives - Built-in operations.
//!
//! This module defines primitive operations that are directly compiled
//! to JavaScript operations. These include arithmetic, comparisons,
//! array/string operations, and FFI calls.

use super::lam_compat::{Comparison, FieldDbgInfo, SetFieldDbgInfo};
use super::lam_tag_info::TagInfo;

/// Raw JavaScript code info
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct JsRawInfo {
    /// The JavaScript code
    pub code: String,
    /// Is this a statement or expression?
    pub is_stmt: bool,
}

pub use crate::types::external_ffi_types::{
    Attr, Cst, DeclKind, ExternalDecl, ExternalModuleName, ImportAttributes, Label,
    LabelNoname, ModuleBindName, ModuleSource, ObjParam, Param,
};

/// `Lambda.import_source`: the target of a dynamic `import`, resolved at
/// translation. The argument of the import primitive is a module reference,
/// never an expression.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ImportSource {
    /// A ReScript module, or a value/submodule reached from one (`path = []`:
    /// the module itself). The JS export name for a nested `path` is resolved
    /// where the cmj tables live, at emission.
    ImportModule {
        module_: crate::ident::Ident,
        path: Vec<String>,
    },
    /// An external's module: `path` is the access path inside the module
    /// (`@scope` segments then the name; `[]` means the module itself).
    ImportExternal {
        module_: ExternalModuleName,
        path: Vec<String>,
    },
}

impl ImportSource {
    /// `Ffi_debug.import_source`.
    pub fn debug_string(&self) -> String {
        use crate::types::external_ffi_types::debug::{module_name, quote};
        let path = |p: &[String]| {
            format!("[{}]", p.iter().map(|s| quote(s)).collect::<Vec<_>>().join(";"))
        };
        match self {
            ImportSource::ImportModule { module_, path: p } => {
                format!("Import_module({},{})", module_.name(), path(p))
            }
            ImportSource::ImportExternal { module_, path: p } => {
                format!("Import_external({},{})", module_name(module_), path(p))
            }
        }
    }
}

/// Primitive operations
///
/// These are built-in operations that compile directly to JavaScript.
#[derive(Debug, Clone, PartialEq)]
pub enum Primitive {
    // ==================== Block Operations ====================
    /// Make a block (tuple, record, variant)
    Pmakeblock(TagInfo, Mutable),

    /// Get a field from a block
    Pfield(i32, FieldDbgInfo),

    /// Set a field in a block
    Psetfield(i32, SetFieldDbgInfo),

    /// Duplicate a record
    Pduprecord,

    /// Copy an object while excluding the listed runtime field names.
    PrecordRest(Vec<String>),

    /// A JavaScript tagged template operation. For `sql`id = ${id}``, the
    /// payload is `["id = "; ""]` and the arguments are `[sql; id]`. Segment
    /// text remains raw and may contain invalid escapes.
    PtaggedTemplate(Vec<String>),

    /// An ordinary backquoted-template operation: the source and semantic
    /// forms of each segment; the arguments are the interpolated values.
    Ptemplate(Vec<crate::string_literal::TemplateSegment>),

    // ==================== External Call ====================
    /// JavaScript FFI call
    /// JS FFI calls, expanded from the external's spec at translation.
    PjsCall {
        prim_name: String,
        arg_types: Vec<Param>,
        ffi: Box<ExternalDecl>,
        transformed_jsx: bool,
    },

    /// Create a JavaScript object
    PjsObjectCreate(Vec<ObjParam>),

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
    /// JavaScript comparison
    Pjscomp(Comparison),
    /// Apply function
    PjsApply,
    /// Runtime apply
    PjsRuntimeApply,
    /// Debugger statement
    Pdebugger,
    /// Object property read: `obj["name"]`.
    PjsObjectGet(String),
    /// Object property write: `obj["name"] = v`.
    PjsObjectSet(String),
    /// Initialize module
    PinitMod,
    /// Update module
    PupdateMod,
    /// Raw JavaScript code
    PrawJsCode(JsRawInfo),
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
    /// Dynamic import of a translation-resolved source
    Pimport(Box<ImportSource>),
    /// Typeof
    Ptypeof,
    /// Function arity
    PfnArity,
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
            Praise
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
            | Ptypeof
            | PfnArity
            | PisPolyVarBlock
            | Pdebugger
            | PinitMod
            | PupdateMod
            | Pduprecord
            | PrecordRest(_)
            | PtaggedTemplate(_)
            | Ptemplate(_)
            | Pmakearray
            | Parraylength
            | Parrayrefu
            | Parraysetu
            | Parrayrefs
            | Parraysets
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
            Pidentity | Pignore | PextensionSlotEq => self == other,

            // lam_primitive.ml:233-236
            PcreateExtension(a) => match other {
                PcreateExtension(b) => a == b,
                _ => false,
            },
            // lam_primitive.ml:237-240
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
            Pmakeblock(info0, flag0) => match other {
                Pmakeblock(info1, flag1) => flag0 == flag1 && info0 == info1,
                _ => false,
            },
            // lam_primitive.ml:250-254: Pjs_call only checks
            // prim_name + arg_types + ffi (NOT transformed_jsx).
            PjsCall {
                prim_name,
                arg_types,
                ffi,
                transformed_jsx: _,
            } => match other {
                PjsCall {
                    prim_name: pn,
                    arg_types: at,
                    ffi: f,
                    transformed_jsx: _,
                } => prim_name == pn && arg_types == at && ffi == f,
                _ => false,
            },
            // lam_primitive.ml:255-258
            Pimport(src) => matches!(other, Pimport(src2) if src == src2),
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
            // lam_primitive.ml:289-292
            PjsObjectGet(name) => match other {
                PjsObjectGet(rhs_name) => name == rhs_name,
                _ => false,
            },
            PjsObjectSet(name) => match other {
                PjsObjectSet(rhs_name) => name == rhs_name,
                _ => false,
            },
            // Expanded when raw lambda is lowered; never compared in Lam.
            // lam_primitive.ml:298
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
