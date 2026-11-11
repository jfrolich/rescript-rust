// Port of compiler/gentype/GenTypeCommon.ml:1-236.

use std::collections::{BTreeMap, BTreeSet};
use std::path::{MAIN_SEPARATOR, Path};

use crate::ident::Ident as CompilerIdent;

/// A map keyed by name, iterated in name order.
pub type StringMap<V> = BTreeMap<String, V>;
/// A set of names, iterated in name order.
pub type StringSet = BTreeSet<String>;

/// Doc comments carried from the source to the generated file.
pub mod doc_string {
    #![allow(non_upper_case_globals)]

    /// A doc comment's text, if there is one.
    pub type T = Option<String>;

    /// The doc comment as a `/** ... */` line, or nothing.
    pub fn render(t: &T) -> String {
        match t {
            None => String::new(),
            Some(s) if s.is_empty() => String::new(),
            Some(doc_string) => format!("/** {} */\n", doc_string.trim()),
        }
    }

    /// No doc comment.
    pub const empty: T = None;

    /// Whether there is a doc comment.
    pub fn has_content(doc_string: &T) -> bool {
        doc_string.is_some()
    }
}

/// Log, when that debug flag is on, a construct gentype does not translate.
pub fn log_not_implemented(x: &str) {
    if crate::gentype::debug::not_implemented.load(std::sync::atomic::Ordering::Relaxed) {
        crate::gentype::log_::item(&format!("Not Implemented: {x}\n"));
    }
}

/// Whether a record field may be left out.
#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum Optional {
    /// The field is required.
    Mandatory,
    /// The field is optional (`?`).
    Optional,
}

/// Whether a field can be assigned.
#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum Mutable {
    /// A read-only field.
    Immutable,
    /// A `mutable` field.
    Mutable,
}

/// The runtime value of a variant case.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum LabelJs {
    /// `null` (`@as(null)`).
    NullLabel,
    /// `undefined` (`@as(undefined)`).
    UndefinedLabel,
    /// A boolean.
    BoolLabel(bool),
    /// A number literal, as written.
    FloatLabel(String),
    /// An integer literal, as written.
    IntLabel(String),
    /// A string.
    StringLabel(String),
}

/// A variant case.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct Case {
    /// The case's runtime value.
    pub label_js: LabelJs,
}

/// Whether `name` can be written as a property name without quotes.
pub fn is_js_safe_property_name(name: &str) -> bool {
    name.is_empty()
        || (matches!(name.as_bytes().first(), Some(b'A'..=b'z'))
            && name.bytes().all(|c| matches!(c, b'A'..=b'z' | b'0'..=b'9')))
}

/// Whether `s` is a decimal integer without leading zeros.
pub fn is_number(s: &str) -> bool {
    let len = s.len();
    len > 0
        && match len > 1 {
            true => s.as_bytes()[0] > b'0',
            false => true,
        }
        && s.bytes().all(|c| c.is_ascii_digit())
}

/// The case's runtime value as TypeScript source.
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

/// Whether an object type admits more fields.
#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum ClosedFlag {
    /// An open object type (`{..}`).
    Open,
    /// A closed object type.
    Closed,
    /// An inline record argument of a variant case.
    Inline,
}

/// A TypeScript type, as gentype emits it.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum Type {
    /// An array, read-only unless mutable.
    Array(Box<Type>, Mutable),
    /// A dictionary with values of this type.
    Dict(Box<Type>),
    /// A function.
    Function(Function),
    /// A named type, with its arguments.
    Ident(Ident),
    /// A type that may be `null`.
    Null(Box<Type>),
    /// A type that may be `null` or `undefined`.
    Nullable(Box<Type>),
    /// An object type with these fields.
    Object(ClosedFlag, Fields),
    /// A type that may be `undefined`.
    Option(Box<Type>),
    /// A promise of this type.
    Promise(Box<Type>),
    /// A tuple.
    Tuple(Vec<Type>),
    /// A type variable.
    TypeVar(String),
    /// A variant.
    Variant(Variant),
}

/// An object type's fields.
pub type Fields = Vec<Field>;

/// A function argument.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct ArgType {
    /// The argument's name.
    pub a_name: String,
    /// The argument's type.
    pub a_type: Type,
}

/// An object type's field.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct Field {
    /// Whether the field can be assigned.
    pub mutable_: Mutable,
    /// The field's name in JavaScript.
    pub name_js: String,
    /// Whether the field may be left out.
    pub optional: Optional,
    /// The field's type.
    pub type_: Type,
    /// The field's doc comment.
    pub doc_string: doc_string::T,
}

/// A function type.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct Function {
    /// The arguments.
    pub arg_types: Vec<ArgType>,
    /// The result type.
    pub ret_type: Box<Type>,
    /// The type variables the function is generic over.
    pub type_vars: Vec<String>,
}

/// A named type applied to arguments.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct Ident {
    /// Whether the name is a TypeScript type rather than one gentype declares or imports.
    pub builtin: bool,
    /// The type's name.
    pub name: String,
    /// The type arguments.
    pub type_args: Vec<Type>,
}

/// A variant type.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct Variant {
    /// The polymorphic variants this one includes.
    pub inherits: Vec<Type>,
    /// The cases without a payload.
    pub no_payloads: Vec<Case>,
    /// The cases with a payload.
    pub payloads: Vec<Payload>,
    /// Whether the variant is polymorphic.
    pub polymorphic: bool,
    /// The field holding the case, from `@tag`.
    pub tag: Option<String>,
    /// Whether the variant is `@unboxed`.
    pub unboxed: bool,
}

/// A variant case with a payload.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct Payload {
    /// The case.
    pub case: Case,
    /// The payload's type.
    pub t: Type,
}

/// A function argument's label.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Label {
    /// An unlabelled argument.
    Nolabel,
    /// A labelled argument (`~name`).
    Label(String),
    /// An optional argument (`~name=?`).
    OptLabel(String),
}

/// A type a translated type depends on, which may need to be imported.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Dep {
    /// A type of another module, by module name.
    External(String),
    /// A type of this module.
    Internal(crate::gentype::resolved_name::T),
    /// A type inside a submodule of the given dependency.
    Dot(Box<Dep>, String),
}

/// Generated modules of scoped packages (`@scope/name`).
pub mod scoped_package {
    use super::CompilerIdent;

    // Taken from ext_namespace.ml in BuckleScript.
    /// The module name a package name is turned into: alphanumeric runs
    /// capitalized and joined, dropping `@`, `/` and `-`.
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

    /// Whether `id` is the generated module of one of the configured dependencies.
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

/// The dependency as a name in the generated file.
pub fn dep_to_string(dep: &Dep) -> String {
    match dep {
        Dep::External(name) => scoped_package::remove_generated_module(name),
        Dep::Internal(resolved_name) => crate::gentype::resolved_name::to_string(resolved_name),
        Dep::Dot(d, s) => format!("{}_{}", dep_to_string(d), s),
    }
}

/// The dependency as a resolved name.
pub fn dep_to_resolved_name(dep: &Dep) -> crate::gentype::resolved_name::T {
    match dep {
        Dep::External(name) => crate::gentype::resolved_name::from_string(name),
        Dep::Internal(resolved_name) => resolved_name.clone(),
        Dep::Dot(p, s) => crate::gentype::resolved_name::dot(s, &dep_to_resolved_name(p)),
    }
}

/// A variant type from its parts.
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

/// A built-in TypeScript type without arguments.
pub fn ident(name: &str) -> Type {
    ident_with(true, Vec::new(), name)
}

/// A named type, built-in or not, applied to `type_args`.
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

/// `name` as a TypeScript type name: exotic `\"...\"` names unwrapped and `'`
/// replaced by `_`.
pub fn sanitize_type_name(name: &str) -> String {
    unwrap_uppercase_exotic(name)
        .chars()
        .map(|c| match c {
            '\'' => '_',
            c => c,
        })
        .collect()
}

/// TypeScript's `unknown`.
pub fn unknown() -> Type {
    ident("unknown")
}

/// TypeScript's `bigint`.
pub fn bigint_t() -> Type {
    ident("bigint")
}

/// TypeScript's `boolean`.
pub fn boolean_t() -> Type {
    ident("boolean")
}

/// TypeScript's `Date`.
pub fn date_t() -> Type {
    ident("Date")
}

/// TypeScript's `Map<x, y>`.
pub fn map_t(x: Type, y: Type) -> Type {
    ident_with(true, vec![x, y], "Map")
}

/// TypeScript's `number`.
pub fn number_t() -> Type {
    ident("number")
}

/// TypeScript's `RegExp`.
pub fn regexp_t() -> Type {
    ident("RegExp")
}

/// TypeScript's `Set<x>`.
pub fn set_t(x: Type) -> Type {
    ident_with(true, vec![x], "Set")
}

/// TypeScript's `string`.
pub fn string_t() -> Type {
    ident("string")
}

/// The type of ReScript's `unit`, `void`.
pub fn unit_t() -> Type {
    ident("void")
}

/// TypeScript's `WeakMap<x, y>`.
pub fn weakmap_t(x: Type, y: Type) -> Type {
    ident_with(true, vec![x, y], "WeakMap")
}

/// TypeScript's `WeakSet<x>`.
pub fn weakset_t(x: Type) -> Type {
    ident_with(true, vec![x], "WeakSet")
}

/// OCaml's `Filename`, with `/` as the directory separator on every platform.
pub mod node_filename {
    use super::{MAIN_SEPARATOR, Path};

    // Force "/" separator.
    /// The directory separator.
    pub const DIR_SEP: &str = "/";

    /// Paths with `/` separators.
    pub mod path {
        use super::{DIR_SEP, MAIN_SEPARATOR};

        /// A path.
        pub type T = String;

        /// `path` with Windows separators replaced by `/`.
        pub fn normalize(path: &str) -> T {
            match MAIN_SEPARATOR == '\\' {
                true => path.split('\\').collect::<Vec<_>>().join(DIR_SEP),
                false => path.to_string(),
            }
        }

        /// `Filename.concat`: `filename` inside directory `dirname`.
        pub fn concat(dirname: &str, filename: &str) -> T {
            fn is_dir_sep(s: &str, i: usize) -> bool {
                let c = s.as_bytes()[i];
                c == b'/' || c == b'\\' || c == b':'
            }

            let l = dirname.len();
            if l == 0 || is_dir_sep(dirname, l - 1) {
                format!("{dirname}{filename}")
            } else {
                format!("{dirname}{DIR_SEP}{filename}")
            }
        }

        /// The path as a string.
        pub fn to_string(path: &T) -> String {
            path.clone()
        }
    }

    /// `filename` inside directory `dirname`, normalized to `/` separators.
    pub fn concat(dirname: &str, filename: &str) -> String {
        path::to_string(&path::concat(&path::normalize(dirname), filename))
    }

    /// The last component of `path`.
    pub fn basename(path: &str) -> String {
        Path::new(path)
            .file_name()
            .and_then(|s| s.to_str())
            .unwrap_or(path)
            .to_string()
    }
}
