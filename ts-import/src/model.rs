//! The ReScript declarations an import produces, and how they print.
//!
//! The converter builds these values from TypeScript's types; the compiler
//! then parses the printed text like any other ReScript source, so every rule
//! about records, variants and externals is enforced by the ordinary type
//! checker, not by this crate.

use std::fmt::Write;

/// A ReScript type expression.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Ty {
    /// A type constructor with arguments: `string`, `array<float>`,
    /// `Map.t<string, user>`.
    App(String, Vec<Ty>),
    /// A type variable, without the quote.
    Var(String),
    Tuple(Vec<Ty>),
    Fn(Vec<Param>, Box<Ty>),
    /// A closed polymorphic variant whose tags are JavaScript literals.
    Poly(Vec<Tag>),
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Param {
    /// `Some` for an optional argument, printed as `~name: ty=?`.
    pub optional: Option<String>,
    pub ty: Ty,
}

/// A JavaScript literal used as a polymorphic variant tag or an `@as` payload.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Tag {
    Str(String),
    /// The literal as JavaScript prints it.
    Num(String),
    Bool(bool),
    Null,
    Undefined,
}

impl Ty {
    pub fn name(name: &str) -> Ty {
        Ty::App(name.to_string(), Vec::new())
    }
    pub fn app(name: &str, args: Vec<Ty>) -> Ty {
        Ty::App(name.to_string(), args)
    }
    pub fn unknown() -> Ty {
        Ty::name("unknown")
    }
    pub fn is_unit(&self) -> bool {
        matches!(self, Ty::App(name, args) if name == "unit" && args.is_empty())
    }

    /// Calls `visit` with the name of every type constructor in the type.
    pub fn for_each_name(&self, visit: &mut dyn FnMut(&str)) {
        match self {
            Ty::App(name, args) => {
                visit(name);
                for arg in args {
                    arg.for_each_name(visit);
                }
            }
            Ty::Var(_) | Ty::Poly(_) => {}
            Ty::Tuple(items) => {
                for item in items {
                    item.for_each_name(visit);
                }
            }
            Ty::Fn(params, ret) => {
                for param in params {
                    param.ty.for_each_name(visit);
                }
                ret.for_each_name(visit);
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Field {
    pub name: String,
    /// The JavaScript property name when it differs from `name`.
    pub js_name: Option<String>,
    pub optional: bool,
    /// Type variables the field quantifies over itself: `'u. ...`.
    pub poly: Vec<String>,
    pub ty: Ty,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Payload {
    None,
    Ty(Ty),
    Record(Vec<Field>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Ctor {
    pub name: String,
    pub tag: Option<Tag>,
    pub payload: Payload,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DeclKind {
    Record(Vec<Field>),
    /// `tag` is the discriminant property of a tagged union; without it the
    /// variant is `@unboxed` when a constructor carries a payload.
    Variant { tag: Option<String>, ctors: Vec<Ctor> },
    Alias(Ty),
    /// A type ReScript code can pass around but not look into.
    Abstract,
}

/// A type declaration.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Decl {
    pub name: String,
    pub params: Vec<String>,
    pub kind: DeclKind,
    /// The TypeScript type this stands for, for the generated doc comment.
    pub ts: Option<String>,
}

impl Decl {
    pub fn for_each_name(&self, visit: &mut dyn FnMut(&str)) {
        let fields = |fields: &[Field], visit: &mut dyn FnMut(&str)| {
            for field in fields {
                field.ty.for_each_name(visit);
            }
        };
        match &self.kind {
            DeclKind::Record(record) => fields(record, visit),
            DeclKind::Variant { ctors, .. } => {
                for ctor in ctors {
                    match &ctor.payload {
                        Payload::None => {}
                        Payload::Ty(ty) => ty.for_each_name(visit),
                        Payload::Record(record) => fields(record, visit),
                    }
                }
            }
            DeclKind::Alias(ty) => ty.for_each_name(visit),
            DeclKind::Abstract => {}
        }
    }
}

/// An `external` binding.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct External {
    pub name: String,
    /// Attributes in order, without the `@`: `module("./a.ts")`, `new`.
    pub attrs: Vec<String>,
    pub ty: Ty,
    pub js_name: String,
    pub ts: Option<String>,
}

/// One generated structure item.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Item {
    /// Declarations that refer to each other are one `type rec` group.
    Types(Vec<Decl>),
    External(External),
    Module(String, Vec<Item>),
}

/// The reserved words of ReScript (`Token::lookup_keyword` in the parser).
const KEYWORDS: &[&str] = &[
    "and", "as", "assert", "await", "break", "constraint", "continue", "else", "exception",
    "external", "false", "for", "if", "in", "include", "let", "module", "mutable", "of", "open",
    "private", "rec", "switch", "true", "try", "type", "when", "while",
];

/// The type names the generated code uses unqualified. A declaration with
/// one of these names would hide the type from everything after it.
const BUILTIN_TYPES: &[&str] = &[
    "array", "bigint", "bool", "char", "dict", "exn", "float", "int", "list", "null", "nullable",
    "option", "promise", "ref", "result", "string", "undefined", "unit", "unknown",
];

pub fn is_builtin_type(name: &str) -> bool {
    BUILTIN_TYPES.contains(&name)
}

pub fn is_keyword(name: &str) -> bool {
    KEYWORDS.contains(&name)
}

fn is_lower_ident(name: &str) -> bool {
    let mut chars = name.chars();
    match chars.next() {
        Some(first) if first.is_ascii_lowercase() || first == '_' => {}
        _ => return false,
    }
    name != "_" && chars.all(|ch| ch.is_ascii_alphanumeric() || ch == '_') && !is_keyword(name)
}

/// A value, type, field or label name made from any JavaScript name.
pub fn lower_ident(name: &str) -> String {
    let mut out = String::new();
    let mut upper_next = false;
    for ch in name.chars() {
        if ch.is_ascii_alphanumeric() || ch == '_' {
            if upper_next && !out.is_empty() {
                out.push(ch.to_ascii_uppercase());
            } else {
                out.push(ch);
            }
            upper_next = false;
        } else {
            upper_next = true;
        }
    }
    // `HTMLElement` becomes `htmlElement`, `User` becomes `user`, `URL` `url`.
    let bytes = out.as_bytes();
    let run = bytes.iter().take_while(|byte| byte.is_ascii_uppercase()).count();
    if run > 0 {
        let lower = if run > 1 && run < bytes.len() && bytes[run].is_ascii_lowercase() {
            run - 1
        } else {
            run
        };
        out = format!("{}{}", out[..lower].to_ascii_lowercase(), &out[lower..]);
    }
    if out.is_empty() || out == "_" {
        out = "x".to_string();
    }
    if out.as_bytes()[0].is_ascii_digit() {
        out.insert(0, 'n');
    }
    if is_keyword(&out) {
        out.push('_');
    }
    out
}

/// A constructor or module name made from any JavaScript name or literal.
pub fn upper_ident(name: &str) -> String {
    let mut out = String::new();
    let mut upper_next = true;
    for ch in name.chars() {
        if ch.is_ascii_alphanumeric() {
            if upper_next {
                out.push(ch.to_ascii_uppercase());
            } else {
                out.push(ch);
            }
            upper_next = false;
        } else {
            upper_next = true;
        }
    }
    if out.is_empty() {
        return "Empty".to_string();
    }
    if out.as_bytes()[0].is_ascii_digit() {
        out.insert(0, 'N');
    }
    out
}

/// A string literal in ReScript syntax.
pub fn string_literal(text: &str) -> String {
    let mut out = String::with_capacity(text.len() + 2);
    out.push('"');
    for ch in text.chars() {
        match ch {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            ch if (ch as u32) < 0x20 => {
                let _ = write!(out, "\\u{:04x}", ch as u32);
            }
            ch => out.push(ch),
        }
    }
    out.push('"');
    out
}

fn print_tag_as(tag: &Tag) -> String {
    match tag {
        Tag::Str(text) => string_literal(text),
        Tag::Num(text) => text.clone(),
        Tag::Bool(value) => value.to_string(),
        Tag::Null => "null".to_string(),
        Tag::Undefined => "undefined".to_string(),
    }
}

fn print_poly_tag(tag: &Tag) -> String {
    match tag {
        Tag::Str(text) => {
            let plain = !text.is_empty()
                && text.chars().all(|ch| ch.is_ascii_alphanumeric() || ch == '_')
                && !text.as_bytes()[0].is_ascii_digit()
                && !is_keyword(text);
            if plain { format!("#{text}") } else { format!("#{}", string_literal(text)) }
        }
        Tag::Num(text) => format!("#{text}"),
        Tag::Bool(value) => format!("#{value}"),
        Tag::Null => "#null".to_string(),
        Tag::Undefined => "#undefined".to_string(),
    }
}

pub fn print_ty(ty: &Ty) -> String {
    let mut out = String::new();
    write_ty(ty, &mut out);
    out
}

fn write_ty(ty: &Ty, out: &mut String) {
    match ty {
        Ty::App(name, args) => {
            out.push_str(name);
            if !args.is_empty() {
                out.push('<');
                for (index, arg) in args.iter().enumerate() {
                    if index > 0 {
                        out.push_str(", ");
                    }
                    write_ty(arg, out);
                }
                out.push('>');
            }
        }
        Ty::Var(name) => {
            out.push('\'');
            out.push_str(name);
        }
        Ty::Tuple(items) => {
            out.push('(');
            for (index, item) in items.iter().enumerate() {
                if index > 0 {
                    out.push_str(", ");
                }
                write_ty(item, out);
            }
            out.push(')');
        }
        Ty::Fn(params, ret) => {
            let bare = params.len() == 1
                && params[0].optional.is_none()
                && matches!(params[0].ty, Ty::App(..) | Ty::Var(_) | Ty::Poly(_));
            if bare {
                write_ty(&params[0].ty, out);
            } else if params.is_empty() {
                out.push_str("unit");
            } else {
                out.push('(');
                for (index, param) in params.iter().enumerate() {
                    if index > 0 {
                        out.push_str(", ");
                    }
                    match &param.optional {
                        Some(label) => {
                            let _ = write!(out, "~{label}: ");
                            write_ty(&param.ty, out);
                            out.push_str("=?");
                        }
                        None => write_ty(&param.ty, out),
                    }
                }
                out.push(')');
            }
            out.push_str(" => ");
            write_ty(ret, out);
        }
        Ty::Poly(tags) => {
            out.push('[');
            for (index, tag) in tags.iter().enumerate() {
                if index > 0 {
                    out.push_str(" | ");
                }
                out.push_str(&print_poly_tag(tag));
            }
            out.push(']');
        }
    }
}

fn write_fields(fields: &[Field], indent: &str, out: &mut String) {
    out.push_str("{\n");
    for field in fields {
        out.push_str(indent);
        out.push_str("  ");
        if let Some(js_name) = &field.js_name {
            let _ = write!(out, "@as({}) ", string_literal(js_name));
        }
        out.push_str(&field.name);
        if field.optional {
            out.push('?');
        }
        out.push_str(": ");
        if !field.poly.is_empty() {
            for var in &field.poly {
                let _ = write!(out, "'{var} ");
            }
            out.pop();
            out.push_str(". ");
        }
        write_ty(&field.ty, out);
        out.push_str(",\n");
    }
    out.push_str(indent);
    out.push('}');
}

fn write_doc(ts: &Option<String>, indent: &str, out: &mut String) {
    if let Some(ts) = ts {
        let one_line: String = ts.split_whitespace().collect::<Vec<_>>().join(" ");
        let text = one_line.replace("*/", "* /");
        let _ = writeln!(out, "{indent}/** TypeScript: `{text}` */");
    }
}

fn write_decl_body(decl: &Decl, indent: &str, out: &mut String) {
    out.push_str(&decl.name);
    if !decl.params.is_empty() {
        out.push('<');
        for (index, param) in decl.params.iter().enumerate() {
            if index > 0 {
                out.push_str(", ");
            }
            out.push('\'');
            out.push_str(param);
        }
        out.push('>');
    }
    match &decl.kind {
        DeclKind::Abstract => {}
        DeclKind::Alias(ty) => {
            out.push_str(" = ");
            write_ty(ty, out);
        }
        DeclKind::Record(fields) => {
            out.push_str(" = ");
            write_fields(fields, indent, out);
        }
        DeclKind::Variant { ctors, .. } => {
            out.push_str(" =");
            for ctor in ctors {
                let _ = write!(out, "\n{indent}  | ");
                if let Some(tag) = &ctor.tag {
                    let _ = write!(out, "@as({}) ", print_tag_as(tag));
                }
                out.push_str(&ctor.name);
                match &ctor.payload {
                    Payload::None => {}
                    Payload::Ty(ty) => {
                        out.push('(');
                        write_ty(ty, out);
                        out.push(')');
                    }
                    Payload::Record(fields) => {
                        out.push('(');
                        write_fields(fields, &format!("{indent}  "), out);
                        out.push(')');
                    }
                }
            }
        }
    }
}

fn decl_attrs(decl: &Decl) -> String {
    match &decl.kind {
        DeclKind::Variant { tag: Some(tag), .. } => format!("@tag({}) ", string_literal(tag)),
        DeclKind::Variant { tag: None, ctors } => {
            if ctors.iter().any(|ctor| !matches!(ctor.payload, Payload::None)) {
                "@unboxed ".to_string()
            } else {
                String::new()
            }
        }
        _ => String::new(),
    }
}

fn write_items(items: &[Item], indent: &str, out: &mut String) {
    for item in items {
        match item {
            Item::Types(decls) => {
                let rec = decls.len() > 1 || {
                    let mut own = false;
                    decls[0].for_each_name(&mut |name| own |= name == decls[0].name);
                    own
                };
                for (index, decl) in decls.iter().enumerate() {
                    write_doc(&decl.ts, indent, out);
                    out.push_str(indent);
                    out.push_str(&decl_attrs(decl));
                    if index == 0 {
                        out.push_str(if rec { "type rec " } else { "type " });
                    } else {
                        out.push_str("and ");
                    }
                    write_decl_body(decl, indent, out);
                    out.push('\n');
                }
            }
            Item::External(external) => {
                write_doc(&external.ts, indent, out);
                // The attributes on a line of their own, as the formatter
                // prints a long external.
                if !external.attrs.is_empty() {
                    out.push_str(indent);
                    for (index, attr) in external.attrs.iter().enumerate() {
                        let _ = write!(out, "{}@{attr}", if index == 0 { "" } else { " " });
                    }
                    out.push('\n');
                }
                let _ = writeln!(
                    out,
                    "{indent}external {}: {} = {}",
                    external.name,
                    print_ty(&external.ty),
                    string_literal(&external.js_name)
                );
            }
            Item::Module(name, items) => {
                let _ = writeln!(out, "{indent}module {name} = {{");
                write_items(items, &format!("{indent}  "), out);
                let _ = writeln!(out, "{indent}}}");
            }
        }
    }
}

/// The items as ReScript source, one declaration after another.
pub fn print_items(items: &[Item]) -> String {
    let mut out = String::new();
    write_items(items, "", &mut out);
    out
}

/// A decl's right-hand side, used to recognise two anonymous TypeScript types
/// with the same shape.
pub fn shape_key(decl: &Decl) -> String {
    let mut out = decl_attrs(decl);
    let unnamed = Decl { name: String::new(), ts: None, ..decl.clone() };
    write_decl_body(&unnamed, "", &mut out);
    out
}

pub fn is_plain_field_name(name: &str) -> bool {
    is_lower_ident(name)
}
