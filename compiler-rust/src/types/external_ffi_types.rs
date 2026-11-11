//! Digested external declarations.
//!
//! Mirrors `compiler/ml/external_arg_spec.ml` and
//! `compiler/ml/external_ffi_types.ml`: the frontend digests an external's
//! FFI attributes into these structures (`Parsetree.Prim_ffi`), the type
//! checker stores them in the primitive description, and translation expands
//! them into `Pjs_call` / `Pjs_object_create`.

use serde::{Deserialize, Serialize};

// ============================================================================
// External_arg_spec
// ============================================================================

/// `External_arg_spec.cst`.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Cst {
    /// An integer constant.
    ArgIntLit(i64),
    /// A string constant.
    ArgStringLit(String),
    /// A JSON constant, as written.
    ArgJsonLit(String),
}

/// `External_arg_spec.attr`.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Attr {
    /// A polymorphic variant argument passed as a string (`@string`).
    PolyVarString {
        /// Each tag and the string it is passed as.
        descr: Vec<(String, String)>,
    },
    /// A polymorphic variant argument.
    PolyVar {
        /// Each tag and the string it is passed as, when `@as` names them.
        descr: Option<Vec<(String, String)>>,
    },
    /// A polymorphic variant argument passed as an integer (`@int`), with each
    /// tag's integer.
    Int(Vec<(String, i64)>),
    /// A constant argument (`@as`), passed without a source argument.
    ArgCst(Cst),
    /// A `unit` argument, which is not passed.
    ExternUnit,
    /// An ordinary argument, passed as is.
    Nothing,
    /// An argument dropped from the call (`@ignore`).
    Ignore,
    /// A polymorphic variant whose payload is passed instead (`@unwrap`).
    Unwrap,
}

/// `External_arg_spec.label_noname`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum LabelNoname {
    /// A labeled argument.
    ArgLabel,
    /// A positional argument.
    ArgEmpty,
    /// An optional argument.
    ArgOptional,
}

/// `External_arg_spec.label`.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Label {
    /// An argument that is not an object field.
    ObjEmpty,
    /// A field of the created object.
    ObjLabel {
        /// The field's name.
        name: String,
    },
    /// An optional field, set only when the argument is `Some`.
    ObjOptional {
        /// The field's name.
        name: String,
        /// Whether the argument's value needs no unwrapping because it cannot be a
        /// nested option.
        for_sure_no_nested_option: bool,
    },
}

/// `External_arg_spec.obj_param`.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct ObjParam {
    /// How the argument is converted.
    pub obj_arg_type: Attr,
    /// The object field it becomes.
    pub obj_arg_label: Label,
}

/// `External_arg_spec.param`.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Param {
    /// How the argument is converted.
    pub arg_type: Attr,
    /// How the argument is passed.
    pub arg_label: LabelNoname,
}

impl Param {
    /// `External_arg_spec.dummy`.
    pub fn dummy() -> Self {
        Param {
            arg_type: Attr::Nothing,
            arg_label: LabelNoname::ArgEmpty,
        }
    }
}

// ============================================================================
// External_ffi_types
// ============================================================================

/// `External_ffi_types.module_bind_name`.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum ModuleBindName {
    /// An explicit name to bind the imported module to.
    PhintName(String),
    /// No explicit name.
    PhintNothing,
}

/// `External_ffi_types.import_attributes`, ordered as written.
pub type ImportAttributes = Vec<(String, String)>;

/// `External_ffi_types.external_module_name`.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct ExternalModuleName {
    /// The imported module's path.
    pub bundle: String,
    /// The name to bind it to.
    pub module_bind_name: ModuleBindName,
    /// The `with` attributes of the import, ordered as written.
    pub import_attributes: Option<ImportAttributes>,
}

/// `External_ffi_types.module_source`.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum ModuleSource {
    /// `@module("...")` payload forms.
    ModuleNamed(ExternalModuleName),
    /// Bare `@module`: the external is the module itself, under its
    /// primitive name.
    ModuleItself,
}

/// `External_ffi_types.decl_kind`.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum DeclKind {
    /// `@val`, or no attribute: a value or function.
    DeclVal {
        /// The JavaScript name.
        name: String,
    },
    /// `@send`: a method call on the first argument.
    DeclSend {
        /// The method name.
        name: String,
    },
    /// `@new`: a constructor call.
    DeclNew {
        /// The class name.
        name: String,
    },
    /// `@get`: a property read.
    DeclGet {
        /// The property name.
        name: String,
    },
    /// `@set`: a property write.
    DeclSet {
        /// The property name.
        name: String,
    },
    /// `@get_index`: read an element by key.
    DeclGetIndex,
    /// `@set_index`: write an element by key.
    DeclSetIndex,
}

/// `External_ffi_types.external_decl`.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct ExternalDecl {
    /// What the external calls or reads.
    pub kind: DeclKind,
    /// The module it comes from (`@module`), if any.
    pub module_: Option<ModuleSource>,
    /// The `@scope` path it is reached through.
    pub scopes: Vec<String>,
    /// Whether the last argument is spread (`@variadic`).
    pub variadic: bool,
    /// Counted (non-`@ignore`) declared parameters.
    pub effective_arity: i64,
}

/// `External_ffi_types.return_wrapper`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum ReturnWrapper {
    /// No `@return` attribute.
    ReturnUnset,
    /// `@return(identity)`.
    ReturnIdentity,
    /// `@return(null_to_opt)`: map `null` to `None`.
    ReturnNullToOpt,
    /// `@return(nullable)`: map `null` and `undefined` to `None`.
    ReturnNullUndefinedToOpt,
}

/// `External_ffi_types.inline_const`.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum InlineConst {
    /// A decoded runtime string value.
    ConstString(String),
    /// A boolean.
    ConstBool(bool),
    /// An `int`.
    ConstInt(i32),
    /// A `bigint`.
    ConstBigint {
        /// Whether the value is positive (written without a minus sign).
        positive: bool,
        /// The decimal digits.
        digits: String,
    },
    /// A float, as written.
    ConstFloat(String),
}

/// `External_ffi_types.t`.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum ExternalFfi {
    /// A function call or property access, with its parameters, return
    /// conversion and declaration.
    FfiBs(Vec<Param>, ReturnWrapper, ExternalDecl),
    /// An object literal (`@obj`), with one parameter per field.
    FfiObjCreate(Vec<ObjParam>),
}

#[cfg(test)]
impl ExternalDecl {
    /// A plain global `@val` call, for tests that need some FFI call.
    pub fn test_val(name: &str, effective_arity: i64) -> Self {
        ExternalDecl {
            kind: DeclKind::DeclVal {
                name: name.to_string(),
            },
            module_: None,
            scopes: vec![],
            variadic: false,
            effective_arity,
        }
    }
}

/// `External_ffi_types.inclusion_compatible impl intf`: can an
/// implementation's spec satisfy an interface's spec during signature
/// inclusion? Object-creation specs compare optional fields by name only.
pub fn inclusion_compatible(impl_: &ExternalFfi, intf: &ExternalFfi) -> bool {
    match (impl_, intf) {
        (ExternalFfi::FfiObjCreate(params1), ExternalFfi::FfiObjCreate(params2)) => {
            // Ext_list.for_all2_no_exn: false on a length mismatch.
            params1.len() == params2.len()
                && params1.iter().zip(params2).all(|(a, b)| {
                    a.obj_arg_type == b.obj_arg_type
                        && match (&a.obj_arg_label, &b.obj_arg_label) {
                            (
                                Label::ObjOptional { name: n1, .. },
                                Label::ObjOptional { name: n2, .. },
                            ) => n1 == n2,
                            (l1, l2) => l1 == l2,
                        }
                })
        }
        _ => impl_ == intf,
    }
}

// ============================================================================
// Ffi_debug: the fork's textual rendering for the sexp debugging printers
// (compiler/ml/ffi_debug.ml).
// ============================================================================

/// The fork's textual rendering of the FFI types for the sexp debugging
/// printers (`compiler/ml/ffi_debug.ml`).
pub mod debug {
    use super::*;

    fn list<T>(xs: &[T], f: impl Fn(&T) -> String) -> String {
        let items: Vec<String> = xs.iter().map(f).collect();
        format!("[{}]", items.join(";"))
    }

    /// OCaml `Printf.sprintf "%S"`. String constants carry OCaml's bytes one
    /// char per byte (the typedtree's Latin-1 convention); any other char
    /// stands for its UTF-8 bytes.
    pub fn quote(s: &str) -> String {
        let mut bytes = Vec::with_capacity(s.len());
        for ch in s.chars() {
            match u8::try_from(u32::from(ch)) {
                Ok(b) => bytes.push(b),
                Err(_) => bytes.extend_from_slice(ch.encode_utf8(&mut [0u8; 4]).as_bytes()),
            }
        }
        let mut out = String::with_capacity(bytes.len() + 2);
        out.push('"');
        for b in bytes {
            match b {
                b'"' => out.push_str("\\\""),
                b'\\' => out.push_str("\\\\"),
                b'\n' => out.push_str("\\n"),
                b'\t' => out.push_str("\\t"),
                b'\r' => out.push_str("\\r"),
                b'\x08' => out.push_str("\\b"),
                b' '..=b'~' => out.push(b as char),
                _ => out.push_str(&format!("\\{:03}", b)),
            }
        }
        out.push('"');
        out
    }

    fn bool_(b: bool) -> &'static str {
        if b { "true" } else { "false" }
    }

    fn pairs(xs: &[(String, String)]) -> String {
        list(xs, |(a, b)| format!("({},{})", quote(a), quote(b)))
    }

    fn attr(a: &Attr) -> String {
        match a {
            Attr::PolyVarString { descr } => format!("Poly_var_string{}", pairs(descr)),
            Attr::PolyVar { descr: None } => "Poly_var".to_string(),
            Attr::PolyVar { descr: Some(d) } => format!("Poly_var{}", pairs(d)),
            Attr::Int(xs) => format!("Int{}", list(xs, |(a, i)| format!("({},{})", quote(a), i))),
            Attr::ArgCst(Cst::ArgIntLit(i)) => format!("Arg_int_lit({i})"),
            Attr::ArgCst(Cst::ArgStringLit(s)) => format!("Arg_string_lit({})", quote(s)),
            Attr::ArgCst(Cst::ArgJsonLit(s)) => format!("Arg_json_lit({})", quote(s)),
            Attr::ExternUnit => "Extern_unit".to_string(),
            Attr::Nothing => "Nothing".to_string(),
            Attr::Ignore => "Ignore".to_string(),
            Attr::Unwrap => "Unwrap".to_string(),
        }
    }

    fn label_noname(l: LabelNoname) -> &'static str {
        match l {
            LabelNoname::ArgLabel => "Arg_label",
            LabelNoname::ArgEmpty => "Arg_empty",
            LabelNoname::ArgOptional => "Arg_optional",
        }
    }

    fn label(l: &Label) -> String {
        match l {
            Label::ObjEmpty => "Obj_empty".to_string(),
            Label::ObjLabel { name } => format!("Obj_label({})", quote(name)),
            Label::ObjOptional {
                name,
                for_sure_no_nested_option,
            } => format!(
                "Obj_optional({},{})",
                quote(name),
                bool_(*for_sure_no_nested_option)
            ),
        }
    }

    /// Render an external module name.
    pub fn module_name(m: &ExternalModuleName) -> String {
        let bind = match &m.module_bind_name {
            ModuleBindName::PhintName(s) => format!("Phint_name({})", quote(s)),
            ModuleBindName::PhintNothing => "Phint_nothing".to_string(),
        };
        let attrs = match &m.import_attributes {
            None => "None".to_string(),
            Some(a) => pairs(a),
        };
        format!("{{{},{},{}}}", quote(&m.bundle), bind, attrs)
    }

    fn kind(k: &DeclKind) -> String {
        match k {
            DeclKind::DeclVal { name } => format!("Decl_val({})", quote(name)),
            DeclKind::DeclSend { name } => format!("Decl_send({})", quote(name)),
            DeclKind::DeclNew { name } => format!("Decl_new({})", quote(name)),
            DeclKind::DeclGet { name } => format!("Decl_get({})", quote(name)),
            DeclKind::DeclSet { name } => format!("Decl_set({})", quote(name)),
            DeclKind::DeclGetIndex => "Decl_get_index".to_string(),
            DeclKind::DeclSetIndex => "Decl_set_index".to_string(),
        }
    }

    fn decl(d: &ExternalDecl) -> String {
        let module_ = match &d.module_ {
            None => "None".to_string(),
            Some(ModuleSource::ModuleItself) => "Module_itself".to_string(),
            Some(ModuleSource::ModuleNamed(m)) => format!("Module_named{}", module_name(m)),
        };
        format!(
            "{{{},{},{},{},{}}}",
            kind(&d.kind),
            module_,
            list(&d.scopes, |s| quote(s)),
            bool_(d.variadic),
            d.effective_arity
        )
    }

    fn return_wrapper(r: ReturnWrapper) -> &'static str {
        match r {
            ReturnWrapper::ReturnUnset => "Return_unset",
            ReturnWrapper::ReturnIdentity => "Return_identity",
            ReturnWrapper::ReturnNullToOpt => "Return_null_to_opt",
            ReturnWrapper::ReturnNullUndefinedToOpt => "Return_null_undefined_to_opt",
        }
    }

    /// Render an external's FFI specification.
    pub fn spec(s: &ExternalFfi) -> String {
        match s {
            ExternalFfi::FfiBs(params, ret, d) => format!(
                "Ffi_bs({},{},{})",
                list(params, |p| format!(
                    "{}:{}",
                    attr(&p.arg_type),
                    label_noname(p.arg_label)
                )),
                return_wrapper(*ret),
                decl(d)
            ),
            ExternalFfi::FfiObjCreate(params) => format!(
                "Ffi_obj_create{}",
                list(params, |p| format!(
                    "{}:{}",
                    attr(&p.obj_arg_type),
                    label(&p.obj_arg_label)
                ))
            ),
        }
    }

    /// Render an inline constant.
    pub fn inline_const(c: &InlineConst) -> String {
        match c {
            InlineConst::ConstString(s) => format!("Const_string({})", quote(s)),
            InlineConst::ConstBool(b) => format!("Const_bool({})", bool_(*b)),
            InlineConst::ConstInt(i) => format!("Const_int({i})"),
            InlineConst::ConstBigint { positive, digits } => {
                format!("Const_bigint({},{})", bool_(*positive), quote(digits))
            }
            InlineConst::ConstFloat(f) => format!("Const_float({})", quote(f)),
        }
    }
}
