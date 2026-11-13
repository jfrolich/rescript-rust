//! `rescript-tools doc`: the documentation of a module as JSON, a port of
//! `Tools.extract_docs` (tools/src/tools.ml:402-622).
//!
//! The JSON is what `RescriptTools.Docgen` (packages/@rescript/runtime)
//! decodes. OCaml reads the module from its `.cmt`; here the session
//! type-checks it from source against the published interfaces.
//!
//! An item that another module declares (an item of an `include`, of a
//! module alias) is documented at the position its declaration has in the
//! published interface, as OCaml reads it from the `.cmi`. The project must
//! therefore be built with source locations, which a build leaves out by
//! default; without them such an item is at line 0.

use super::json::Json;
use super::session::ProjectSession;
use super::shared::{decl_to_string, path_ident_to_string, type_to_string, unwrap_if_option};
use super::shared_types::{
    Constructor, ConstructorArgs, Field, File, Loc, Module, ModuleItemKind, QueryEnv, Structure,
    Type, TypeKind,
};
use crate::types::printtyp::{OutArgLabel, OutIdent, OutType, Printtyp, print_out_type_doc};
use crate::types::{TypeContext, TypeDesc, TypeExprRef};
use std::collections::HashSet;
use std::path::{Path, PathBuf};

struct FieldDoc {
    field_name: String,
    docstrings: Vec<String>,
    signature: String,
    optional: bool,
    deprecated: Option<String>,
}

struct ConstructorDoc {
    constructor_name: String,
    docstrings: Vec<String>,
    signature: String,
    deprecated: Option<String>,
    /// The fields of an inline record payload.
    inline_record: Option<Vec<FieldDoc>>,
}

/// `type_doc`: a type, structured where the docs decoder reads its parts.
enum TypeDoc {
    Constructor {
        path: String,
        generic_parameters: Vec<TypeDoc>,
    },
    Variable {
        name: String,
        weak: bool,
    },
    Tuple(Vec<TypeDoc>),
    Function(ValueSignature),
    Rendered(String),
}

struct SignatureParameter {
    label: Option<String>,
    optional: bool,
    typ: TypeDoc,
}

struct ValueSignature {
    parameters: Vec<SignatureParameter>,
    return_type: Box<TypeDoc>,
}

struct Source {
    filepath: String,
    line: i32,
    col: i32,
}

enum Detail {
    Record(Vec<FieldDoc>),
    Variant(Vec<ConstructorDoc>),
    Signature(ValueSignature),
}

enum DocItem {
    Value {
        id: String,
        docstring: Vec<String>,
        signature: String,
        name: String,
        deprecated: Option<String>,
        detail: Option<Detail>,
        source: Source,
    },
    Type {
        id: String,
        docstring: Vec<String>,
        signature: String,
        name: String,
        deprecated: Option<String>,
        detail: Option<Detail>,
        source: Source,
    },
    Module(DocsForModule),
    ModuleType {
        id: String,
        docstring: Vec<String>,
        deprecated: Option<String>,
        name: String,
        source: Source,
        items: Vec<DocItem>,
    },
    ModuleAlias {
        id: String,
        docstring: Vec<String>,
        name: String,
        source: Source,
        items: Vec<DocItem>,
    },
}

struct DocsForModule {
    id: String,
    docstring: Vec<String>,
    deprecated: Option<String>,
    name: String,
    moduletypeid: Option<String>,
    source: Source,
    items: Vec<DocItem>,
}

fn push_deprecated(fields: &mut Vec<(String, Json)>, deprecated: &Option<String>) {
    if let Some(d) = deprecated {
        fields.push(("deprecated".to_string(), Json::str(d.as_str())));
    }
}

fn fields_json(fields: Vec<(&str, Json)>) -> Vec<(String, Json)> {
    fields
        .into_iter()
        .map(|(k, v)| (k.to_string(), v))
        .collect()
}

/// `stringify_docstrings`.
fn docstrings_json(docstrings: &[String]) -> Json {
    Json::List(docstrings.iter().map(|d| Json::str(d.trim())).collect())
}

/// `stringify_field_doc`.
fn field_doc_json(field: &FieldDoc) -> Json {
    let mut fields = fields_json(vec![
        ("name", Json::str(field.field_name.as_str())),
        ("optional", Json::Bool(field.optional)),
        ("docstrings", docstrings_json(&field.docstrings)),
        ("signature", Json::str(field.signature.as_str())),
    ]);
    push_deprecated(&mut fields, &field.deprecated);
    Json::Assoc(fields)
}

/// `stringify_type_doc`.
fn type_doc_json(typ: &TypeDoc) -> Json {
    match typ {
        TypeDoc::Constructor {
            path,
            generic_parameters,
        } => Json::assoc([
            ("kind", Json::str("constructor")),
            ("path", Json::str(path.as_str())),
            (
                "genericTypeParameters",
                Json::List(generic_parameters.iter().map(type_doc_json).collect()),
            ),
        ]),
        TypeDoc::Variable { name, weak } => Json::assoc([
            ("kind", Json::str("variable")),
            ("name", Json::str(name.as_str())),
            ("weak", Json::Bool(*weak)),
        ]),
        TypeDoc::Tuple(elements) => Json::assoc([
            ("kind", Json::str("tuple")),
            (
                "elements",
                Json::List(elements.iter().map(type_doc_json).collect()),
            ),
        ]),
        TypeDoc::Function(signature) => {
            let mut fields = vec![("kind".to_string(), Json::str("function"))];
            fields.extend(value_signature_json(signature));
            Json::Assoc(fields)
        }
        TypeDoc::Rendered(signature) => Json::assoc([
            ("kind", Json::str("rendered")),
            ("signature", Json::str(signature.as_str())),
        ]),
    }
}

/// `stringify_value_signature`.
fn value_signature_json(signature: &ValueSignature) -> Vec<(String, Json)> {
    let parameters = signature
        .parameters
        .iter()
        .map(|parameter| {
            let mut fields = Vec::new();
            if let Some(label) = &parameter.label {
                fields.push(("label".to_string(), Json::str(label.as_str())));
            }
            fields.push(("optional".to_string(), Json::Bool(parameter.optional)));
            fields.push(("type".to_string(), type_doc_json(&parameter.typ)));
            Json::Assoc(fields)
        })
        .collect();
    fields_json(vec![
        ("parameters", Json::List(parameters)),
        ("returnType", type_doc_json(&signature.return_type)),
    ])
}

/// `stringify_detail`.
fn detail_json(detail: &Detail) -> Json {
    match detail {
        Detail::Record(field_docs) => Json::assoc([
            ("kind", Json::str("record")),
            (
                "items",
                Json::List(field_docs.iter().map(field_doc_json).collect()),
            ),
        ]),
        Detail::Variant(constructor_docs) => Json::assoc([
            ("kind", Json::str("variant")),
            (
                "items",
                Json::List(
                    constructor_docs
                        .iter()
                        .map(|constructor| {
                            let mut fields = fields_json(vec![
                                ("name", Json::str(constructor.constructor_name.as_str())),
                                ("docstrings", docstrings_json(&constructor.docstrings)),
                                ("signature", Json::str(constructor.signature.as_str())),
                            ]);
                            push_deprecated(&mut fields, &constructor.deprecated);
                            if let Some(field_docs) = &constructor.inline_record {
                                fields.push((
                                    "payload".to_string(),
                                    Json::assoc([
                                        ("kind", Json::str("inlineRecord")),
                                        (
                                            "fields",
                                            Json::List(
                                                field_docs.iter().map(field_doc_json).collect(),
                                            ),
                                        ),
                                    ]),
                                ));
                            }
                            Json::Assoc(fields)
                        })
                        .collect(),
                ),
            ),
        ]),
        Detail::Signature(signature) => Json::assoc([
            ("kind", Json::str("signature")),
            ("details", Json::Assoc(value_signature_json(signature))),
        ]),
    }
}

/// `stringify_source`.
fn source_json(source: &Source) -> Json {
    Json::assoc([
        ("filepath", Json::str(source.filepath.as_str())),
        ("line", Json::Int(source.line.into())),
        ("col", Json::Int(source.col.into())),
    ])
}

fn items_json(items: &[DocItem]) -> Json {
    Json::List(items.iter().map(doc_item_json).collect())
}

/// `stringify_doc_item`.
fn doc_item_json(item: &DocItem) -> Json {
    match item {
        DocItem::Value {
            id,
            docstring,
            signature,
            name,
            deprecated,
            detail,
            source,
        }
        | DocItem::Type {
            id,
            docstring,
            signature,
            name,
            deprecated,
            detail,
            source,
        } => {
            let (kind, signature) = match item {
                DocItem::Value { .. } => ("value", signature.trim()),
                _ => ("type", signature.as_str()),
            };
            let mut fields = fields_json(vec![
                ("id", Json::str(id.as_str())),
                ("kind", Json::str(kind)),
                ("name", Json::str(name.as_str())),
                ("signature", Json::str(signature)),
                ("docstrings", docstrings_json(docstring)),
                ("source", source_json(source)),
            ]);
            push_deprecated(&mut fields, deprecated);
            if let Some(detail) = detail {
                fields.push(("detail".to_string(), detail_json(detail)));
            }
            Json::Assoc(fields)
        }
        DocItem::Module(m) => {
            let mut fields = fields_json(vec![
                ("id", Json::str(m.id.as_str())),
                ("name", Json::str(m.name.as_str())),
                ("kind", Json::str("module")),
                ("docstrings", docstrings_json(&m.docstring)),
                ("source", source_json(&m.source)),
                ("items", items_json(&m.items)),
            ]);
            push_deprecated(&mut fields, &m.deprecated);
            if let Some(path) = &m.moduletypeid {
                fields.push(("moduletypeid".to_string(), Json::str(path.as_str())));
            }
            Json::Assoc(fields)
        }
        DocItem::ModuleType {
            id,
            docstring,
            deprecated,
            name,
            source,
            items,
        } => {
            let mut fields = fields_json(vec![
                ("id", Json::str(id.as_str())),
                ("name", Json::str(name.as_str())),
                ("kind", Json::str("moduleType")),
                ("docstrings", docstrings_json(docstring)),
                ("source", source_json(source)),
                ("items", items_json(items)),
            ]);
            push_deprecated(&mut fields, deprecated);
            Json::Assoc(fields)
        }
        DocItem::ModuleAlias {
            id,
            docstring,
            name,
            source,
            items,
        } => Json::assoc([
            ("id", Json::str(id.as_str())),
            ("kind", Json::str("moduleAlias")),
            ("name", Json::str(name.as_str())),
            ("docstrings", docstrings_json(docstring)),
            ("source", source_json(source)),
            ("items", items_json(items)),
        ]),
    }
}

/// `stringify_docs_for_module`.
fn docs_for_module_json(docs: &DocsForModule) -> Json {
    let mut fields = fields_json(vec![
        ("name", Json::str(docs.name.as_str())),
        ("docstrings", docstrings_json(&docs.docstring)),
        ("source", source_json(&docs.source)),
        ("items", items_json(&docs.items)),
    ]);
    push_deprecated(&mut fields, &docs.deprecated);
    Json::Assoc(fields)
}

/// `Shared_types.ident`: a module path, outermost first, joined with dots.
fn ident<'a>(path: impl Iterator<Item = &'a String>) -> String {
    path.map(|s| if s.is_empty() { "\"\"" } else { s.as_str() })
        .collect::<Vec<_>>()
        .join(".")
}

/// The id of a module path given innermost first (OCaml's
/// `module_path |> List.rev |> ident`).
fn module_path_id(module_path: &[String]) -> String {
    ident(module_path.iter().rev())
}

/// `make_id`: `identifier` inside the module path given innermost first.
fn make_id(module_path: &[String], identifier: &str) -> String {
    let identifier = identifier.to_string();
    ident(module_path.iter().rev().chain(std::iter::once(&identifier)))
}

/// `Ext_ident.unwrap_uppercase_exotic`: `\"Name"` without the quoting.
fn unwrap_uppercase_exotic(name: &str) -> &str {
    let bytes = name.as_bytes();
    let len = bytes.len();
    if len >= 3 && bytes[0] == b'\\' && bytes[1] == b'"' && bytes[len - 1] == b'"' {
        &name[2..len - 1]
    } else {
        name
    }
}

/// `Files.path_eq`: case-insensitive on Windows and macOS.
fn path_eq(a: &str, b: &str) -> bool {
    if cfg!(target_os = "linux") {
        a == b
    } else {
        a.eq_ignore_ascii_case(b)
    }
}

/// `Files.remove_extra_dots`.
fn remove_extra_dots(path: &str) -> String {
    let path = path.replace("/./", "/");
    match path.strip_prefix("./../") {
        Some(rest) => format!("../{rest}"),
        None => path,
    }
}

/// `Files.split`: `Str.split`, which drops empty fields at both ends.
fn split<'a>(sep: &str, s: &'a str) -> Vec<&'a str> {
    let parts: Vec<&str> = s.split(sep).collect();
    let start = parts
        .iter()
        .position(|p| !p.is_empty())
        .unwrap_or(parts.len());
    let end = parts
        .iter()
        .rposition(|p| !p.is_empty())
        .map_or(start, |i| i + 1);
    parts[start..end].to_vec()
}

const DIR_SEP: &str = std::path::MAIN_SEPARATOR_STR;

/// `Files.relpath`.
fn relpath(base: &str, path: &str) -> String {
    if base.len() <= path.len()
        && path.is_char_boundary(base.len())
        && path_eq(&path[..base.len()], base)
    {
        let rest = &path[base.len()..];
        let rest = rest.strip_prefix(DIR_SEP).unwrap_or(rest);
        remove_extra_dots(rest)
    } else {
        let base_parts = split(DIR_SEP, base);
        let path_parts = split(DIR_SEP, path);
        let mut bp: &[&str] = &base_parts;
        let mut pp: &[&str] = &path_parts;
        loop {
            match (bp.first(), pp.first()) {
                (Some(&"."), _) => bp = &bp[1..],
                (_, Some(&".")) => pp = &pp[1..],
                (Some(a), Some(b)) if path_eq(a, b) => {
                    bp = &bp[1..];
                    pp = &pp[1..];
                }
                _ => break,
            }
        }
        let mut parts: Vec<&str> = if bp.is_empty() {
            vec!["."]
        } else {
            bp.iter().map(|_| "..").collect()
        };
        parts.extend_from_slice(pp);
        remove_extra_dots(&parts.join(DIR_SEP))
    }
}

/// A path relative to the package root, with `/` separators.
fn source_filepath(root_path: &str, path: &str) -> String {
    split(DIR_SEP, &relpath(root_path, path)).join("/")
}

/// `get_source`: where a location in `file_path` starts.
fn get_source(root_path: &str, file_path: &str, loc: &Loc) -> Source {
    let (line, col) = loc.start.line_col();
    Source {
        filepath: source_filepath(root_path, file_path),
        line: line + 1,
        col: col + 1,
    }
}

/// `string_of_out_ident`.
fn string_of_out_ident(ident: &OutIdent) -> String {
    match ident {
        OutIdent::Oide_ident(name) => name.clone(),
        OutIdent::Oide_dot(path, name) => format!("{}.{name}", string_of_out_ident(path)),
        OutIdent::Oide_apply(functor, argument) => format!(
            "{}({})",
            string_of_out_ident(functor),
            string_of_out_ident(argument)
        ),
    }
}

/// `type_doc_of_out_type`.
fn type_doc_of_out_type(typ: &OutType) -> TypeDoc {
    match typ {
        OutType::Otyp_constr(path, generic_parameters) => TypeDoc::Constructor {
            path: string_of_out_ident(path),
            generic_parameters: generic_parameters
                .iter()
                .map(type_doc_of_out_type)
                .collect(),
        },
        OutType::Otyp_var(weak, name) => TypeDoc::Variable {
            name: name.clone(),
            weak: *weak,
        },
        OutType::Otyp_tuple(elements) => {
            TypeDoc::Tuple(elements.iter().map(type_doc_of_out_type).collect())
        }
        OutType::Otyp_arrow(parameters, return_type) => {
            TypeDoc::Function(value_signature_of_arrow(parameters, return_type))
        }
        // `render_out_type`.
        _ => TypeDoc::Rendered(print_out_type_doc(typ).to_string(80)),
    }
}

/// `value_signature_of_arrow`.
fn value_signature_of_arrow(
    parameters: &[(OutArgLabel, OutType)],
    return_type: &OutType,
) -> ValueSignature {
    ValueSignature {
        parameters: parameters
            .iter()
            .map(|(label, typ)| {
                let (label, optional) = match label {
                    OutArgLabel::Nolabel => (None, false),
                    OutArgLabel::Labelled(label) => (Some(label.clone()), false),
                    OutArgLabel::Optional(label) => (Some(label.clone()), true),
                };
                SignatureParameter {
                    label,
                    optional,
                    typ: type_doc_of_out_type(typ),
                }
            })
            .collect(),
        return_type: Box::new(type_doc_of_out_type(return_type)),
    }
}

/// `value_detail`.
fn value_detail(types: &TypeContext, typ: TypeExprRef) -> Option<Detail> {
    let mut printtyp = Printtyp::new(types);
    printtyp.reset_and_mark_loops(typ);
    match printtyp.tree_of_typexp(false, typ) {
        OutType::Otyp_arrow(parameters, return_type) => Some(Detail::Signature(
            value_signature_of_arrow(&parameters, &return_type),
        )),
        _ => None,
    }
}

/// `field_to_field_doc`.
fn field_doc(types: &TypeContext, field: &Field) -> FieldDoc {
    FieldDoc {
        field_name: field.fname.txt.clone(),
        docstrings: field.docstring.clone(),
        optional: field.optional,
        signature: type_to_string(types, field.typ, 60),
        deprecated: field.deprecated.clone(),
    }
}

/// `Completion_back_end.show_constructor`.
fn show_constructor(types: &TypeContext, constructor: &Constructor) -> String {
    let mut out = constructor.cname.txt.clone();
    match &constructor.args {
        ConstructorArgs::Args(args) if args.is_empty() => {}
        ConstructorArgs::InlineRecord(fields) => {
            let fields: Vec<String> = fields
                .iter()
                .map(|field| {
                    let typ = if field.optional {
                        unwrap_if_option(types, field.typ)
                    } else {
                        field.typ
                    };
                    format!(
                        "{}{}: {}",
                        field.fname.txt,
                        if field.optional { "?" } else { "" },
                        type_to_string(types, typ, 60)
                    )
                })
                .collect();
            out.push_str("({");
            out.push_str(&fields.join(", "));
            out.push_str("})");
        }
        ConstructorArgs::Args(args) => {
            let args: Vec<String> = args
                .iter()
                .map(|(typ, _)| type_to_string(types, *typ, 60))
                .collect();
            out.push('(');
            out.push_str(&args.join(", "));
            out.push(')');
        }
    }
    if let Some(res) = constructor.res {
        out.push('\n');
        out.push_str(&type_to_string(types, res, 60));
    }
    out
}

/// A record or variant a type stands for.
enum ExtractedType<'s> {
    Record(&'s [Field]),
    Variant(&'s [Constructor]),
}

/// `Type_utils.extract_type`, narrowed to the records and variants
/// `type_detail` reads. The docs extraction calls it without type argument
/// context, so a type variable never resolves (type_utils.ml:503-543), and
/// the other kinds it extracts end up as no detail.
fn extract_type<'s>(
    session: &'s ProjectSession<'_>,
    env: &QueryEnv,
    t: TypeExprRef,
) -> Option<(QueryEnv, ExtractedType<'s>)> {
    let types = session.types(env.file);
    match &*types.get_desc(t) {
        TypeDesc::Tlink(t1) | TypeDesc::Tsubst(t1) => extract_type(session, env, *t1),
        TypeDesc::Tpoly { body, vars } if vars.is_empty() => extract_type(session, env, *body),
        TypeDesc::Tconstr { path, args, .. } => {
            let builtin = path.as_pident().is_some_and(|id| {
                matches!(
                    (id.name(), args.len()),
                    ("option" | "promise" | "array" | "dict", 1)
                        | ("result", 2)
                        | ("bool" | "string" | "exn", 0)
                )
            });
            if builtin {
                return None;
            }
            let (env, declared) = super::references::dig_constructor(session, env, path)?;
            match (&declared.item.decl.type_manifest, &declared.item.kind) {
                (Some(t1), _) => extract_type(session, &env, *t1),
                (None, TypeKind::Variant(constructors)) => {
                    Some((env, ExtractedType::Variant(constructors)))
                }
                (None, TypeKind::Record(fields)) => Some((env, ExtractedType::Record(fields))),
                _ => None,
            }
        }
        _ => None,
    }
}

/// `type_detail`: the fields of a record, the constructors of a variant.
fn type_detail(session: &ProjectSession<'_>, env: &QueryEnv, typ: &Type) -> Option<Detail> {
    let types = session.types(env.file);
    // `Type_utils.extract_type_from_resolved_type`.
    let (types, extracted) = match &typ.kind {
        TypeKind::Record(fields) => (types, ExtractedType::Record(fields)),
        TypeKind::Variant(constructors) => (types, ExtractedType::Variant(constructors)),
        TypeKind::Tuple(_) => return None,
        TypeKind::Abstract(_) | TypeKind::Open => {
            let (env, extracted) = extract_type(session, env, typ.decl.type_manifest?)?;
            (session.types(env.file), extracted)
        }
    };
    Some(match extracted {
        ExtractedType::Record(fields) => {
            Detail::Record(fields.iter().map(|field| field_doc(types, field)).collect())
        }
        ExtractedType::Variant(constructors) => Detail::Variant(
            constructors
                .iter()
                .map(|c| ConstructorDoc {
                    constructor_name: c.cname.txt.clone(),
                    docstrings: c.docstring.clone(),
                    signature: show_constructor(types, c),
                    deprecated: c.deprecated.clone(),
                    inline_record: match &c.args {
                        ConstructorArgs::InlineRecord(fields) => {
                            Some(fields.iter().map(|field| field_doc(types, field)).collect())
                        }
                        ConstructorArgs::Args(_) => None,
                    },
                })
                .collect(),
        ),
    })
}

/// What the extraction of one entry point reads.
struct Extraction<'a, 's, 'p> {
    session: &'s ProjectSession<'p>,
    /// The entry point's file.
    entry: &'a File,
    /// The root of the entry point's package.
    root_path: String,
}

/// A file being documented: the entry point, or a file a module alias of
/// the file `through` names.
struct Documented<'a> {
    file: &'a File,
    through: Option<&'a Documented<'a>>,
}

impl Documented<'_> {
    /// Whether `file` is this file or one of those it was reached through.
    fn contains(&self, file: &File) -> bool {
        self.file.module == file.module || self.through.is_some_and(|d| d.contains(file))
    }
}

fn trimmed(docstrings: &[String]) -> Vec<String> {
    docstrings.iter().map(|d| d.trim().to_string()).collect()
}

fn concat(a: &[String], b: &[String]) -> Vec<String> {
    a.iter().chain(b).cloned().collect()
}

impl Extraction<'_, '_, '_> {
    /// `extract_docs_for_module`: the module `structure` of the file `at`,
    /// at `module_path` (innermost first).
    fn module(
        &self,
        at: &Documented<'_>,
        module_path: &[String],
        structure: &Structure,
    ) -> DocsForModule {
        let session = self.session;
        let file = at.file;
        // Only a type-checked file has values and types; the file of a
        // namespace module, which has no type context, has aliases only.
        let types = || session.types(file.module);
        // OCaml keeps the entry point's environment for the types of an
        // aliased file (tools.ml:442), so a type there whose manifest is a
        // type of that file is looked up in the entry point and gets no
        // detail, or another type's. Here it is looked up in its own file.
        let env = QueryEnv::from_file(file);
        let items: Vec<DocItem> = structure
            .items
            .iter()
            .filter_map(|item| {
                let name = unwrap_uppercase_exotic(&item.name);
                let source = get_source(&self.root_path, &item.file, &item.loc);
                match &item.kind {
                    ModuleItemKind::Value(typ) => Some(DocItem::Value {
                        id: make_id(module_path, name),
                        docstring: trimmed(&item.docstring),
                        signature: format!("let {name}: {}", type_to_string(types(), *typ, 60)),
                        name: name.to_string(),
                        deprecated: item.deprecated.clone(),
                        detail: value_detail(types(), *typ),
                        source,
                    }),
                    ModuleItemKind::Type(typ, _) => Some(DocItem::Type {
                        id: make_id(module_path, name),
                        docstring: trimmed(&item.docstring),
                        signature: decl_to_string(
                            types(),
                            name,
                            &typ.decl,
                            crate::types::decl::RecStatus::TrecNot,
                            false,
                        ),
                        name: name.to_string(),
                        deprecated: item.deprecated.clone(),
                        detail: type_detail(session, &env, typ),
                        source,
                    }),
                    ModuleItemKind::Module {
                        type_: Module::Ident(p),
                        is_module_type: false,
                    } => {
                        // `module Whatever = OtherModule`.
                        let alias_to_module = path_ident_to_string(p);
                        let root = module_path.last().map(String::as_str).unwrap_or_default();
                        let id = format!("{root}.{name}");
                        let (items, internal_docstrings) =
                            match super::resolve_path::Session::file_for_module(
                                session,
                                &alias_to_module,
                            ) {
                                // A namespace module aliases every module of
                                // its package, so an alias of it in one of
                                // them leads back to that module (OCaml does
                                // not return). Its items are not repeated.
                                Some(alias_file) if !at.contains(alias_file) => {
                                    let docs = self.module(
                                        &Documented {
                                            file: alias_file,
                                            through: Some(at),
                                        },
                                        std::slice::from_ref(&id),
                                        &alias_file.structure,
                                    );
                                    (docs.items, docs.docstring)
                                }
                                Some(_) | None => (Vec::new(), Vec::new()),
                            };
                        Some(DocItem::ModuleAlias {
                            id,
                            name: name.to_string(),
                            source,
                            items,
                            docstring: trimmed(&concat(&item.docstring, &internal_docstrings)),
                        })
                    }
                    ModuleItemKind::Module {
                        type_: Module::Structure(m),
                        is_module_type,
                    } => {
                        // `module Whatever = {}` or `module type Whatever = {}`.
                        let module_path = prepend(&m.name, module_path);
                        let docs = self.module(at, &module_path, m);
                        let id = module_path_id(&module_path);
                        let docstring = concat(&item.docstring, &m.docstring);
                        Some(if *is_module_type {
                            DocItem::ModuleType {
                                id,
                                name: m.name.clone(),
                                docstring,
                                deprecated: item.deprecated.clone(),
                                source,
                                items: docs.items,
                            }
                        } else {
                            DocItem::Module(DocsForModule {
                                id,
                                name: m.name.clone(),
                                moduletypeid: None,
                                docstring,
                                deprecated: item.deprecated.clone(),
                                source,
                                items: docs.items,
                            })
                        })
                    }
                    ModuleItemKind::Module {
                        type_: Module::Constraint(implementation, interface),
                        ..
                    } => match (&**implementation, &**interface) {
                        // `module Whatever: { <interface> } = { <impl> }`:
                        // the interface.
                        (Module::Structure(_), Module::Structure(interface)) => {
                            Some(DocItem::Module(self.module(
                                at,
                                &prepend(&interface.name, module_path),
                                interface,
                            )))
                        }
                        // `module M: T = { <impl> }`.
                        (Module::Structure(m), Module::Ident(p)) => {
                            let docs = self.module(at, &prepend(&m.name, module_path), m);
                            // `T` is `File.T` when its first name is a
                            // file's module, and a module type of the entry
                            // point otherwise.
                            let in_another_file = p.head_opt().is_some_and(|head| {
                                super::resolve_path::Session::file_for_module(session, head.name())
                                    .is_some()
                            });
                            let module_type_id_path = if in_another_file {
                                Vec::new()
                            } else {
                                module_path.last().cloned().into_iter().collect()
                            };
                            Some(DocItem::Module(DocsForModule {
                                moduletypeid: Some(make_id(&module_type_id_path, &p.name())),
                                ..docs
                            }))
                        }
                        _ => None,
                    },
                    ModuleItemKind::Module { .. } => None,
                }
            })
            .collect();
        // Keep only the last of the values bound to one id: the others are
        // shadowed.
        let mut values_seen = HashSet::new();
        let mut items: Vec<DocItem> = items
            .into_iter()
            .rev()
            .filter(|item| match item {
                DocItem::Value { id, .. } => values_seen.insert(id.clone()),
                _ => true,
            })
            .collect();
        items.reverse();
        DocsForModule {
            id: module_path_id(module_path),
            docstring: trimmed(&structure.docstring),
            name: structure.name.clone(),
            moduletypeid: None,
            deprecated: structure.deprecated.clone(),
            // OCaml places every module it documents this way at the start
            // of the entry point.
            source: Source {
                filepath: source_filepath(&self.root_path, &self.entry.uri),
                line: 1,
                col: 1,
            },
            items,
        }
    }
}

fn prepend(name: &str, module_path: &[String]) -> Vec<String> {
    std::iter::once(name.to_string())
        .chain(module_path.iter().cloned())
        .collect()
}

/// The root of the package `path` is in: the nearest directory holding a
/// `rescript.json` or `bsconfig.json` (`Find_files.find_project_root`).
fn package_root(path: &Path) -> Option<PathBuf> {
    path.ancestors()
        .skip(1)
        .find(|dir| dir.join("rescript.json").exists() || dir.join("bsconfig.json").exists())
        .map(Path::to_path_buf)
}

/// `Tools.extract_docs`: the documentation of `entry_point_file` as JSON, or
/// why there is none.
pub fn extract_docs(
    session: &ProjectSession<'_>,
    cwd: &Path,
    entry_point_file: &str,
) -> Result<Json, String> {
    let path = if Path::new(entry_point_file).is_relative() {
        let joined = cwd.join(entry_point_file);
        joined
            .canonicalize()
            .unwrap_or(joined)
            .to_string_lossy()
            .into_owned()
    } else {
        entry_point_file.to_string()
    };
    // An implementation with an interface is documented by its interface.
    let path = match path.strip_suffix(".res") {
        Some(stem) => {
            let interface = format!("{stem}.resi");
            if Path::new(&interface).exists() {
                interface
            } else {
                path
            }
        }
        None if path.ends_with(".resi") => path,
        None => {
            return Err(format!(
                "error: failed to read {path}, expected an .res or .resi file"
            ));
        }
    };
    let failed = || format!("error: failed to generate doc for {path}, try to build the project");
    let full = session
        .full_from_path(Path::new(&path))
        .ok_or_else(failed)?;
    // The root as the build spells it, which the file names of locations
    // are relative to: `path` may reach the file through a symbolic link.
    let root_path = package_root(Path::new(&full.file.uri)).ok_or_else(failed)?;
    let extraction = Extraction {
        session,
        entry: &full.file,
        root_path: root_path.to_string_lossy().into_owned(),
    };
    let docs = extraction.module(
        &Documented {
            file: &full.file,
            through: None,
        },
        std::slice::from_ref(&full.file.module_name),
        &full.file.structure,
    );
    Ok(docs_for_module_json(&docs))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn relpath_strips_the_base() {
        assert_eq!(relpath("/a/b", "/a/b/src/X.res"), "src/X.res");
        assert_eq!(relpath("/a/b", "/a/c/X.res"), "../c/X.res");
        assert_eq!(relpath("/a/b", "/a/b"), "");
    }

    #[test]
    fn ids_join_the_outermost_first() {
        let path = vec!["Inner".to_string(), "Root".to_string()];
        assert_eq!(module_path_id(&path), "Root.Inner");
        assert_eq!(make_id(&path, "x"), "Root.Inner.x");
        assert_eq!(make_id(&[], "T"), "T");
        assert_eq!(make_id(&["".to_string()], "x"), "\"\".x");
    }

    #[test]
    fn exotic_names_are_unwrapped() {
        assert_eq!(unwrap_uppercase_exotic("\\\"Exotic Name\""), "Exotic Name");
        assert_eq!(unwrap_uppercase_exotic("plain"), "plain");
    }
}
