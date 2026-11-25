//! A port of analysis/src/process_attributes.ml.
//!
//! OCaml reads `Parsetree.attributes` everywhere. Rust has two forms: the
//! parse tree's (resolved through its arena) and the portable copies type
//! declarations carry (`types::decl::Attribute`); [`Attrs`] reads either.

use super::shared_types::{Declared, Extent, Located, ModulePath, ModulePathList};
use crate::ast_payload::payload_expression;
use crate::parse_arena::{ExprIdx, ParseArena};
use crate::parser::ast::{Attribute, ExpressionDesc, Payload};
use crate::parser::longident::Longident;
use crate::types::decl;

/// Attributes in either of their Rust forms.
#[derive(Clone, Copy)]
pub enum Attrs<'a> {
    /// Parse-tree attributes, with the arena their names and payloads live in.
    Parsed(&'a [Attribute], &'a ParseArena),
    /// The attributes stored on a type declaration.
    Decl(&'a [decl::Attribute]),
}

/// The location of a template with an invalid escape (only a PPX makes
/// one), where `Ast_payload.semantic_string_of_expression` raises
/// (ast_payload.ml:39-51): in the parse tree or a declaration's attribute.
#[derive(Debug, Clone, Copy)]
pub enum InvalidEscape {
    /// The template is in the parse tree.
    Parsed(crate::parse_arena::LocIdx),
    /// The template is in a declaration's attribute.
    Decl(crate::types::DeclLoc),
}

/// The first error a reader raises while a module is processed. OCaml's
/// raise ends the analysis command (nothing catches it); the session turns
/// this into the command's error once the module is built.
#[derive(Default)]
pub struct Raised(std::cell::Cell<Option<InvalidEscape>>);

impl Raised {
    /// The value a reader returned, keeping its error if it raised.
    pub fn read<T>(&self, read: Result<Option<T>, InvalidEscape>) -> Option<T> {
        match read {
            Ok(value) => value,
            Err(error) => {
                if self.0.get().is_none() {
                    self.0.set(Some(error));
                }
                None
            }
        }
    }

    /// The first error raised.
    pub fn get(&self) -> Option<InvalidEscape> {
        self.0.get()
    }

    /// The docstring and deprecation of a declaration with `attributes`.
    pub fn declared_attributes(&self, attributes: Attrs<'_>) -> DeclaredAttributes {
        // process_attributes.ml:41-52: ocamlopt builds the record right to
        // left, reading the docstring first.
        let docstring = self
            .read(find_doc_attribute(attributes))
            .into_iter()
            .collect();
        let deprecated = self.read(reversed_deprecated(attributes));
        DeclaredAttributes {
            docstring,
            deprecated,
        }
    }
}

/// What a declaration's attributes say about it, as `Declared` records it.
pub struct DeclaredAttributes {
    /// Its `@doc` comments.
    pub docstring: Vec<String>,
    /// Its `@deprecated` message.
    pub deprecated: Option<String>,
}

/// `Ast_payload.semantic_string_of_expression`.
fn string_constant(arena: &ParseArena, e: ExprIdx) -> Result<Option<String>, InvalidEscape> {
    crate::ast_payload::semantic_string_of_expression(arena, arena.get_expr(e))
        .map_err(|error| InvalidEscape::Parsed(error.loc))
}

/// `Utils.flatten_long_ident` without its options.
pub fn flatten_long_ident(arena: &ParseArena, lid: &Longident) -> ModulePathList {
    match lid {
        Longident::Lident(txt) => vec![arena.get_string(*txt).to_string()],
        Longident::Ldot(lid, txt) => {
            let mut path = flatten_long_ident(arena, lid);
            path.push(arena.get_string(*txt).to_string());
            path
        }
        Longident::Lapply(..) => Vec::new(),
    }
}

/// process_attributes.ml `find_doc_attribute` reads doc comments only from
/// `@res.doc`.
fn is_doc_name(name: &str) -> bool {
    name == "res.doc"
}

/// `find_doc_attribute`: the first `res.doc` payload that is a string,
/// raising where its reader raises.
pub fn find_doc_attribute(attrs: Attrs<'_>) -> Result<Option<String>, InvalidEscape> {
    match attrs {
        Attrs::Parsed(attrs, arena) => {
            for (name, payload) in attrs {
                if !is_doc_name(arena.get_string(name.txt)) {
                    continue;
                }
                if let Some(doc) = crate::ast_payload::semantic_string_of_payload(arena, payload)
                    .map_err(|error| InvalidEscape::Parsed(error.loc))?
                {
                    return Ok(Some(doc));
                }
            }
            Ok(None)
        }
        Attrs::Decl(attrs) => {
            for attr in attrs {
                if !is_doc_name(&attr.attr_name.txt) {
                    continue;
                }
                if let Some(doc) = attr
                    .attr_payload
                    .semantic_string()
                    .map_err(InvalidEscape::Decl)?
                {
                    return Ok(Some(doc.to_string()));
                }
            }
            Ok(None)
        }
    }
}

/// `find_deprecated_attribute`, raising where its reader raises.
pub fn find_deprecated_attribute(attrs: Attrs<'_>) -> Result<Option<String>, InvalidEscape> {
    match attrs {
        Attrs::Parsed(attrs, arena) => {
            let Some((_, payload)) = attrs.iter().find(|attr| is_parsed_deprecated(arena, attr))
            else {
                return Ok(None);
            };
            parsed_deprecated_reason(arena, payload)
        }
        Attrs::Decl(attrs) => match attrs.iter().find(|a| is_decl_deprecated(a)) {
            Some(attr) => decl_deprecated_reason(attr),
            None => Ok(None),
        },
    }
}

fn is_parsed_deprecated(arena: &ParseArena, (name, _): &Attribute) -> bool {
    arena.get_string(name.txt) == "deprecated"
}

fn is_decl_deprecated(attr: &decl::Attribute) -> bool {
    attr.attr_name.txt == "deprecated"
}

/// The reason of a found `@deprecated` attribute, read as the compiler reads
/// it for its warning (`Builtin_attributes.deprecated_of_attrs_with_migrate`,
/// compiler/ml/builtin_attributes.ml:68-106): a record's first `reason`
/// that is a string, and a record without one is not deprecated; any other
/// payload is deprecated with its string, or with an empty message.
fn parsed_deprecated_reason(
    arena: &ParseArena,
    payload: &Payload,
) -> Result<Option<String>, InvalidEscape> {
    if let Some(e) = payload_expression(payload)
        && let ExpressionDesc::Pexp_record(record) =
            &crate::ast_payload::unwrap_braces(arena, arena.get_expr(e)).pexp_desc
    {
        for field in arena.expr_field_list(record.0) {
            if let Longident::Lident(txt) = arena.get_longident(field.lid.txt)
                && arena.get_string(*txt) == "reason"
                && let Some(msg) = string_constant(arena, field.expr)?
            {
                return Ok(Some(msg));
            }
        }
        return Ok(None);
    }
    // `string_of_opt_payload`.
    let reason = crate::ast_payload::semantic_string_of_payload(arena, payload)
        .map_err(|error| InvalidEscape::Parsed(error.loc))?;
    Ok(Some(reason.unwrap_or_default()))
}

/// The reason of a found `@deprecated` declaration attribute, as the
/// compiler reads it (see [`parsed_deprecated_reason`]).
fn decl_deprecated_reason(attr: &decl::Attribute) -> Result<Option<String>, InvalidEscape> {
    attr.attr_payload
        .deprecated_with_migrate()
        .map(|deprecated| deprecated.map(|(reason, _)| reason.to_string()))
        .map_err(InvalidEscape::Decl)
}

/// `find_editor_complete_from_attribute`.
pub fn find_editor_complete_from_attribute(attrs: Attrs<'_>) -> Vec<ModulePathList> {
    let mut module_paths: Vec<ModulePathList> = Vec::new();
    match attrs {
        Attrs::Parsed(attrs, arena) => {
            for (name, payload) in attrs {
                if arena.get_string(name.txt) != "editor.completeFrom" {
                    continue;
                }
                let Some(e) = payload_expression(payload) else {
                    continue;
                };
                let items: Vec<ExprIdx> = match &arena.get_expr(e).pexp_desc {
                    ExpressionDesc::Pexp_array(items) => arena.expr_list(*items).to_vec(),
                    _ => vec![e],
                };
                let mut from_array: Vec<ModulePathList> = items
                    .iter()
                    .filter_map(|item| match &arena.get_expr(*item).pexp_desc {
                        ExpressionDesc::Pexp_construct(lid, args) if args.txt.is_empty() => {
                            Some(flatten_long_ident(arena, arena.get_longident(lid.txt)))
                        }
                        _ => None,
                    })
                    .collect();
                from_array.append(&mut module_paths);
                module_paths = from_array;
            }
        }
        Attrs::Decl(attrs) => {
            for attr in attrs {
                if attr.attr_name.txt != "editor.completeFrom" {
                    continue;
                }
                if let decl::AttributePayload::Ident(path) = &attr.attr_payload {
                    let mut from_array = vec![path.split('.').map(str::to_string).collect()];
                    from_array.append(&mut module_paths);
                    module_paths = from_array;
                }
            }
        }
    }
    module_paths
}

/// `find_deprecated_attribute (List.rev attributes)`.
fn reversed_deprecated(attrs: Attrs<'_>) -> Result<Option<String>, InvalidEscape> {
    match attrs {
        Attrs::Parsed(attrs, arena) => {
            match attrs
                .iter()
                .rev()
                .find(|attr| is_parsed_deprecated(arena, attr))
            {
                Some((_, payload)) => parsed_deprecated_reason(arena, payload),
                None => Ok(None),
            }
        }
        Attrs::Decl(attrs) => match attrs.iter().rev().find(|a| is_decl_deprecated(a)) {
            Some(attr) => decl_deprecated_reason(attr),
            None => Ok(None),
        },
    }
}

/// `new_declared`.
pub fn new_declared<T>(
    item: T,
    extent: Extent,
    name: Located<String>,
    stamp: i32,
    module_path: ModulePath,
    is_exported: bool,
    attributes: DeclaredAttributes,
) -> Declared<T> {
    let DeclaredAttributes {
        docstring,
        deprecated,
    } = attributes;
    Declared {
        name,
        stamp,
        extent_loc: extent.loc,
        extent_file: extent.file,
        is_exported,
        module_path,
        deprecated,
        docstring,
        item,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The reason the analysis reads from each `@@deprecated` of `source`.
    fn deprecated_reasons(source: &str) -> Vec<Option<String>> {
        let mut parser = crate::parser::Parser::new("Deprecated.res", source);
        let items = crate::parser::module::parse_structure(&mut parser);
        assert!(!parser.has_errors());
        let arena = parser.into_arena();
        items
            .iter()
            .map(|item| match &item.pstr_desc {
                crate::parser::ast::StructureItemDesc::Pstr_attribute(attribute) => {
                    let attributes = [(**attribute).clone()];
                    find_deprecated_attribute(Attrs::Parsed(&attributes, &arena)).unwrap()
                }
                other => panic!("{other:?}"),
            })
            .collect()
    }

    /// As the compiler reads it for its warning: a record without `reason`
    /// is not deprecated, its first `reason` is the message, and any other
    /// payload is deprecated.
    #[test]
    fn deprecated_reads_as_the_compiler_reads_it() {
        assert_eq!(
            deprecated_reasons(
                "@@deprecated(\"old\")\n\
                 @@deprecated\n\
                 @@deprecated({reason: \"first\", reason: \"second\"})\n\
                 @@deprecated({migrate: f()})\n\
                 @@deprecated(42)\n"
            ),
            vec![
                Some("old".to_string()),
                Some(String::new()),
                Some("first".to_string()),
                None,
                Some(String::new()),
            ]
        );
    }
}
