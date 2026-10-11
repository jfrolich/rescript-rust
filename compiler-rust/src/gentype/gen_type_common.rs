// Port of compiler/gentype/GenTypeCommon.ml:1-236.
// This Stage 1 GenType port is intentionally not wired into the crate yet.

use std::collections::{BTreeMap, BTreeSet};
use std::path::{MAIN_SEPARATOR, Path};

use crate::ident::Ident as CompilerIdent;

pub type StringMap<V> = BTreeMap<String, V>;
pub type StringSet = BTreeSet<String>;

pub mod doc_string {
    #![allow(non_upper_case_globals)]

    pub type T = Option<String>;

    pub fn render(t: &T) -> String {
        match t {
            None => String::new(),
            Some(s) if s.is_empty() => String::new(),
            Some(doc_string) => format!("/** {} */\n", doc_string.trim()),
        }
    }

    pub const empty: T = None;

    pub fn has_content(doc_string: &T) -> bool {
        doc_string.is_some()
    }
}

pub fn log_not_implemented(x: &str) {
    if crate::gentype::debug::not_implemented.load(std::sync::atomic::Ordering::Relaxed) {
        crate::gentype::log_::item(&format!("Not Implemented: {x}\n"));
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum Optional {
    Mandatory,
    Optional,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum Mutable {
    Immutable,
    Mutable,
}

#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum LabelJs {
    NullLabel,
    UndefinedLabel,
    BoolLabel(bool),
    FloatLabel(String),
    IntLabel(String),
    StringLabel(String),
}

#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct Case {
    pub label_js: LabelJs,
}

pub fn is_js_safe_property_name(name: &str) -> bool {
    name.is_empty()
        || (matches!(name.as_bytes().first(), Some(b'A'..=b'z'))
            && name.bytes().all(|c| matches!(c, b'A'..=b'z' | b'0'..=b'9')))
}

pub fn is_number(s: &str) -> bool {
    let len = s.len();
    len > 0
        && match len > 1 {
            true => s.as_bytes()[0] > b'0',
            false => true,
        }
        && s.bytes().all(|c| c.is_ascii_digit())
}

pub fn label_js_to_string(case: &Case) -> String {
    match &case.label_js {
        LabelJs::NullLabel => "null".to_string(),
        LabelJs::UndefinedLabel => "undefined".to_string(),
        LabelJs::BoolLabel(b) => b.to_string(),
        LabelJs::FloatLabel(s) => s.clone(),
        LabelJs::IntLabel(i) => i.clone(),
        LabelJs::StringLabel(s) => crate::gentype::emit_text::quotes(s),
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum ClosedFlag {
    Open,
    Closed,
    Inline,
}

#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum Type {
    Array(Box<Type>, Mutable),
    Dict(Box<Type>),
    Function(Function),
    Ident(Ident),
    Null(Box<Type>),
    Nullable(Box<Type>),
    Object(ClosedFlag, Fields),
    Option(Box<Type>),
    Promise(Box<Type>),
    Tuple(Vec<Type>),
    TypeVar(String),
    Variant(Variant),
}

pub type Fields = Vec<Field>;

#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct ArgType {
    pub a_name: String,
    pub a_type: Type,
}

#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct Field {
    pub mutable_: Mutable,
    pub name_js: String,
    pub optional: Optional,
    pub type_: Type,
    pub doc_string: doc_string::T,
}

#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct Function {
    pub arg_types: Vec<ArgType>,
    pub ret_type: Box<Type>,
    pub type_vars: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct Ident {
    pub builtin: bool,
    pub name: String,
    pub type_args: Vec<Type>,
}

#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct Variant {
    pub inherits: Vec<Type>,
    pub no_payloads: Vec<Case>,
    pub payloads: Vec<Payload>,
    pub polymorphic: bool,
    pub tag: Option<String>,
    pub unboxed: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct Payload {
    pub case: Case,
    pub t: Type,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Label {
    Nolabel,
    Label(String),
    OptLabel(String),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Dep {
    External(String),
    Internal(crate::gentype::resolved_name::T),
    Dot(Box<Dep>, String),
}

pub mod scoped_package {
    use super::CompilerIdent;

    // Taken from ext_namespace.ml in BuckleScript.
    pub fn namespace_of_package_name(s: &str) -> String {
        let mut buf = String::with_capacity(s.len());

        let mut capital = true;
        for ch in s.chars() {
            match ch {
                'a'..='z' | 'A'..='Z' | '0'..='9' => {
                    if capital {
                        buf.extend(ch.to_uppercase());
                    } else {
                        buf.push(ch);
                    }
                    capital = false;
                }
                '/' | '-' => capital = true,
                _ => {}
            }
        }

        buf
    }

    /// @demo/some-library -> DemoSomelibrary
    pub fn package_name_to_generated_module_name(package_name: &str) -> Option<String> {
        match package_name.contains('/') {
            true => Some(namespace_of_package_name(package_name)),
            false => None,
        }
    }

    pub fn is_generated_module(id: &CompilerIdent, config: &crate::gentype::config::T) -> bool {
        config.bs_dependencies.iter().any(|package_name| {
            package_name_to_generated_module_name(package_name).as_deref() == Some(id.name())
        })
    }

    /// (Common, DemoSomelibrary) -> Common-DemoSomelibrary
    pub fn add_generated_module(s: &str, generated_module: &CompilerIdent) -> String {
        format!("{}-{}", s, generated_module.name())
    }

    /// Common-DemoSomelibrary -> Common
    pub fn remove_generated_module(s: &str) -> String {
        match s.split('-').collect::<Vec<_>>().as_slice() {
            [name, _scope] => (*name).to_string(),
            _ => s.to_string(),
        }
    }
}

pub fn dep_to_string(dep: &Dep) -> String {
    match dep {
        Dep::External(name) => scoped_package::remove_generated_module(name),
        Dep::Internal(resolved_name) => crate::gentype::resolved_name::to_string(resolved_name),
        Dep::Dot(d, s) => format!("{}_{}", dep_to_string(d), s),
    }
}

pub fn dep_to_resolved_name(dep: &Dep) -> crate::gentype::resolved_name::T {
    match dep {
        Dep::External(name) => crate::gentype::resolved_name::from_string(name),
        Dep::Internal(resolved_name) => resolved_name.clone(),
        Dep::Dot(p, s) => crate::gentype::resolved_name::dot(s, &dep_to_resolved_name(p)),
    }
}

pub fn create_variant(
    inherits: Vec<Type>,
    no_payloads: Vec<Case>,
    payloads: Vec<Payload>,
    polymorphic: bool,
    tag: Option<String>,
    unboxed: bool,
) -> Type {
    Type::Variant(Variant {
        inherits,
        no_payloads,
        payloads,
        polymorphic,
        tag,
        unboxed,
    })
}

pub fn ident(name: &str) -> Type {
    ident_with(true, Vec::new(), name)
}

pub fn ident_with(builtin: bool, type_args: Vec<Type>, name: &str) -> Type {
    Type::Ident(Ident {
        builtin,
        name: name.to_string(),
        type_args,
    })
}

fn unwrap_uppercase_exotic(name: &str) -> &str {
    let bytes = name.as_bytes();
    if bytes.len() >= 3 && bytes[0] == b'\\' && bytes[1] == b'"' && bytes[bytes.len() - 1] == b'"' {
        &name[2..name.len() - 1]
    } else {
        name
    }
}

pub fn sanitize_type_name(name: &str) -> String {
    unwrap_uppercase_exotic(name)
        .chars()
        .map(|c| match c {
            '\'' => '_',
            c => c,
        })
        .collect()
}

pub fn unknown() -> Type {
    ident("unknown")
}

pub fn bigint_t() -> Type {
    ident("BigInt")
}

pub fn boolean_t() -> Type {
    ident("boolean")
}

pub fn date_t() -> Type {
    ident("Date")
}

pub fn map_t(x: Type, y: Type) -> Type {
    ident_with(true, vec![x, y], "Map")
}

pub fn number_t() -> Type {
    ident("number")
}

pub fn regexp_t() -> Type {
    ident("RegExp")
}

pub fn set_t(x: Type) -> Type {
    ident_with(true, vec![x], "Set")
}

pub fn string_t() -> Type {
    ident("string")
}

pub fn unit_t() -> Type {
    ident("void")
}

pub fn weakmap_t(x: Type, y: Type) -> Type {
    ident_with(true, vec![x, y], "WeakMap")
}

pub fn weakset_t(x: Type) -> Type {
    ident_with(true, vec![x], "WeakSet")
}

pub mod node_filename {
    use super::{MAIN_SEPARATOR, Path};

    // Force "/" separator.
    pub const dir_sep: &str = "/";

    pub mod path {
        use super::{MAIN_SEPARATOR, dir_sep};

        pub type T = String;

        pub fn normalize(path: &str) -> T {
            match MAIN_SEPARATOR == '\\' {
                true => path.split('\\').collect::<Vec<_>>().join(dir_sep),
                false => path.to_string(),
            }
        }

        pub fn concat(dirname: &str, filename: &str) -> T {
            fn is_dir_sep(s: &str, i: usize) -> bool {
                let c = s.as_bytes()[i];
                c == b'/' || c == b'\\' || c == b':'
            }

            let l = dirname.len();
            if l == 0 || is_dir_sep(dirname, l - 1) {
                format!("{dirname}{filename}")
            } else {
                format!("{dirname}{dir_sep}{filename}")
            }
        }

        pub fn to_string(path: &T) -> String {
            path.clone()
        }
    }

    pub fn concat(dirname: &str, filename: &str) -> String {
        path::to_string(&path::concat(&path::normalize(dirname), filename))
    }

    pub fn basename(path: &str) -> String {
        Path::new(path)
            .file_name()
            .and_then(|s| s.to_str())
            .unwrap_or(path)
            .to_string()
    }
}
