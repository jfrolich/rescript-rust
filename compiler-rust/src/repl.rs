//! What a read-eval-print loop needs from the compiler.
//!
//! A loop compiles each input as a file of its own, with the files of the
//! earlier inputs opened, and runs its JavaScript once. Two things are not
//! in an ordinary compilation's result:
//!
//! - [`prepare`] finds what an input is made of: a last item that is an
//!   expression is bound to `it`, so that it has a value to print, and the
//!   `open`s are listed, so that the loop can keep them open.
//! - [`describe_signature`] says what an input defined: every item as source
//!   text, and for a value the run-time shape of its type, which is what
//!   turns a JavaScript value back into ReScript (`Some(3)` is `3` at run
//!   time, `Circle(1.)` an object tagged `TAG`).

use ahash::AHashMap;
use serde_json::{Value, json};

use crate::parser::ast::StructureItemDesc;
use crate::parser::{Parser, module};
use crate::types::context::TypeContext;
use crate::types::ctype;
use crate::types::decl::{
    ConstructorArguments, LabelDeclaration, RecordRepresentation, SignatureItem, TypeKind,
};
use crate::types::env::Env;
use crate::types::predef;
use crate::types::printtyp::{OutSigItem, Printtyp, print_out_sig_item};
use crate::types::type_expr::{RowField, TypeDesc, TypeExprRef};
use crate::types::variant_runtime::{Block, ConstructorCase, LiteralTag, Tag};

/// The name an input's last expression is bound to.
pub const RESULT_NAME: &str = "it";

/// What is written before an input's last expression.
pub const BINDING: &str = "let it = ";

/// An input, ready to compile.
pub struct Prepared {
    /// The input, with `let it = ` before a last item that is an expression.
    pub source: String,
    /// Where the binding was added, as a line and a column counted from
    /// one: a position after it on that line is `BINDING.len()` further
    /// than in the input.
    pub result_at: Option<(usize, usize)>,
    /// The text of each top-level `open`, in order.
    pub opens: Vec<String>,
}

/// Parse `source` (as the compiler reads it: one character per byte) and
/// prepare it. `None` when it does not parse: compiling it as it is gives
/// the error.
pub fn prepare(source: &str, filename: &str) -> Option<Prepared> {
    let mut parser = Parser::new(filename, source);
    let structure = module::parse_structure(&mut parser);
    if parser.has_errors() {
        return None;
    }
    let arena = parser.arena();
    let characters: Vec<char> = source.chars().collect();
    let range = |item: &crate::parser::ast::StructureItem| {
        let start = arena.loc_start(item.pstr_loc).cnum.max(0) as usize;
        let end = arena.loc_end(item.pstr_loc).cnum.max(0) as usize;
        (start.min(characters.len()), end.min(characters.len()))
    };
    let opens = structure
        .iter()
        .filter(|item| matches!(item.pstr_desc, StructureItemDesc::Pstr_open(_)))
        .map(|item| {
            let (start, end) = range(item);
            characters[start..end].iter().collect()
        })
        .collect();
    let result_start = structure
        .last()
        .filter(|item| matches!(item.pstr_desc, StructureItemDesc::Pstr_eval(_)))
        .map(|item| range(item).0);
    let source = match result_start {
        Some(start) => {
            let mut text: String = characters[..start].iter().collect();
            text.push_str(BINDING);
            text.extend(&characters[start..]);
            text
        }
        None => source.to_string(),
    };
    let result_at = result_start.map(|start| {
        let before = &characters[..start];
        let line_start = before
            .iter()
            .rposition(|character| *character == '\n')
            .map_or(0, |newline| newline + 1);
        let line = before
            .iter()
            .filter(|character| **character == '\n')
            .count()
            + 1;
        (line, start - line_start + 1)
    });
    Some(Prepared {
        source,
        result_at,
        opens,
    })
}

/// The items of `signature` as
/// `{items: [{kind, name, text, shape?}], defs: [...]}`: `text` is the item
/// as an interface would declare it, `shape` (of a value) the run-time shape
/// of its type, with `{k: "ref", id}` for an index into `defs`.
pub(crate) fn describe_signature(
    ctx: &TypeContext,
    env: &Env,
    signature: &[SignatureItem],
) -> Value {
    let mut printer = Printtyp::new(ctx);
    printer.set_printing_env(Box::new(move |name| {
        env.find_type_with_path(name).ok().map(|(path, _)| path)
    }));
    let trees = printer.tree_of_signature(signature);

    let mut shapes = Shapes {
        ctx,
        env,
        defs: Vec::new(),
        known: AHashMap::new(),
    };
    // A name that is bound twice has the type of its last binding.
    let value_types: AHashMap<&str, TypeExprRef> = signature
        .iter()
        .filter_map(|item| match item {
            SignatureItem::SigValue(id, description) => Some((id.name(), description.val_type)),
            _ => None,
        })
        .collect();

    let items: Vec<Value> = trees
        .iter()
        .filter_map(|tree| {
            let (kind, name) = match tree {
                OutSigItem::Osig_value(value) => ("value", value.name.clone()),
                OutSigItem::Osig_type(declaration, _) => ("type", declaration.name.clone()),
                OutSigItem::Osig_module(name, _, _) => ("module", name.clone()),
                OutSigItem::Osig_modtype(name, _) => ("moduleType", name.clone()),
                OutSigItem::Osig_typext(extension, _) => ("exception", extension.name.clone()),
                OutSigItem::Osig_ellipsis | OutSigItem::Osig_class => return None,
            };
            let mut item = serde_json::Map::new();
            item.insert("kind".into(), kind.into());
            item.insert("text".into(), print_out_sig_item(tree).into());
            if kind == "value"
                && let Some(ty) = value_types.get(name.as_str())
            {
                item.insert("shape".into(), shapes.of(*ty, 0));
            }
            item.insert("name".into(), name.into());
            Some(Value::Object(item))
        })
        .collect();
    json!({ "items": items, "defs": shapes.defs })
}

/// Deeper than this, a value is shown as JavaScript.
const MAX_DEPTH: usize = 48;

struct Shapes<'a> {
    ctx: &'a TypeContext,
    env: &'a Env,
    /// The shapes of the records and variants met, by index.
    defs: Vec<Value>,
    /// The index of a record or variant type, by its path and arguments.
    known: AHashMap<String, usize>,
}

impl Shapes<'_> {
    fn other(&self, ty: TypeExprRef) -> Value {
        json!({ "k": "other", "name": crate::macros::reflect::print_type(self.ctx, ty) })
    }

    fn of(&mut self, ty: TypeExprRef, depth: usize) -> Value {
        if depth > MAX_DEPTH {
            return self.other(ty);
        }
        let ctx = self.ctx;
        let expanded = ctx.repr(ctype::expand_head(ctx, self.env, ty));
        let desc = ctx.get_desc(expanded);
        match &*desc {
            TypeDesc::Tconstr { path, args, .. } => {
                let args: Vec<TypeExprRef> = ctx.type_list(*args).iter().collect();
                let simple = [
                    (predef::path_int(), "int"),
                    (predef::path_float(), "float"),
                    (predef::path_string(), "string"),
                    (predef::path_bool(), "bool"),
                    (predef::path_unit(), "unit"),
                    (predef::path_bigint(), "bigint"),
                    (predef::path_char(), "char"),
                ];
                for (predefined, kind) in &simple {
                    if path.same(predefined) {
                        return json!({ "k": kind });
                    }
                }
                let containers = [
                    (predef::path_option(), "option"),
                    (predef::path_array(), "array"),
                    (predef::path_list(), "list"),
                    (predef::path_dict(), "dict"),
                    (predef::path_promise(), "promise"),
                ];
                for (predefined, kind) in &containers {
                    if path.same(predefined) && args.len() == 1 {
                        return json!({ "k": kind, "of": self.of(args[0], depth + 1) });
                    }
                }
                if path.same(&predef::path_result()) && args.len() == 2 {
                    return json!({
                        "k": "result",
                        "ok": self.of(args[0], depth + 1),
                        "error": self.of(args[1], depth + 1),
                    });
                }
                self.declared(expanded, path, &args, depth)
            }
            TypeDesc::Ttuple(elements) => {
                let of: Vec<Value> = ctx
                    .type_list(*elements)
                    .iter()
                    .map(|element| self.of(element, depth + 1))
                    .collect();
                json!({ "k": "tuple", "of": of })
            }
            TypeDesc::Tarrow { .. } => json!({ "k": "fn" }),
            TypeDesc::Tpoly { body, .. } => self.of(*body, depth + 1),
            TypeDesc::Tvariant(row) => {
                let row = ctx.row_desc(*row);
                let cases: Vec<Value> = row
                    .row_fields
                    .iter()
                    .filter_map(|(label, field)| {
                        let of = match field {
                            RowField::Rpresent(Some(arg)) => self.of(*arg, depth + 1),
                            RowField::Rpresent(None) => Value::Null,
                            RowField::Reither { constant: true, .. } => Value::Null,
                            RowField::Reither { types, .. } => match types.first() {
                                Some(arg) => self.of(*arg, depth + 1),
                                None => Value::Null,
                            },
                            _ => return None,
                        };
                        Some(json!({ "name": label.to_string(), "of": of }))
                    })
                    .collect();
                json!({ "k": "poly", "cases": cases })
            }
            _ => self.other(ty),
        }
    }

    /// A type with a declaration: a record or a variant is described once,
    /// in `defs`, so that a type that mentions itself ends.
    fn declared(
        &mut self,
        ty: TypeExprRef,
        path: &crate::types::path::Path,
        args: &[TypeExprRef],
        depth: usize,
    ) -> Value {
        let ctx = self.ctx;
        let Some(decl) = crate::types::typemod::find_type_decl_for_path(self.env, ctx, path) else {
            return self.other(ty);
        };
        if !matches!(
            decl.type_kind,
            TypeKind::TypeRecord(..) | TypeKind::TypeVariant(..)
        ) {
            return self.other(ty);
        }
        let key = format!(
            "{}<{}>",
            path.name(),
            args.iter()
                .map(|arg| crate::macros::reflect::print_type(ctx, *arg))
                .collect::<Vec<_>>()
                .join(", ")
        );
        if let Some(id) = self.known.get(&key) {
            return json!({ "k": "ref", "id": id });
        }
        let id = self.defs.len();
        self.known.insert(key, id);
        self.defs.push(Value::Null);
        let params = &decl.type_params;
        let def = match &decl.type_kind {
            TypeKind::TypeRecord(labels, representation) => json!({
                "k": "record",
                "unboxed": matches!(representation, RecordRepresentation::RecordUnboxed(_)),
                "fields": self.fields(params, args, labels, depth),
            }),
            TypeKind::TypeVariant(constructors, layout) => {
                let layout = ctx.variant_layout(*layout);
                let cases: Vec<Value> = constructors
                    .iter()
                    .zip(layout.constructors.iter())
                    .map(|(constructor, case)| {
                        let (arguments, fields) = match &constructor.cd_args {
                            ConstructorArguments::CstrTuple(types) => (
                                types
                                    .iter()
                                    .map(|member| {
                                        let member = crate::macros::reflect::member_type(
                                            ctx, params, args, *member,
                                        );
                                        self.of(member, depth + 1)
                                    })
                                    .collect::<Vec<Value>>(),
                                Value::Null,
                            ),
                            ConstructorArguments::CstrRecord(labels) => (
                                Vec::new(),
                                Value::Array(self.fields(params, args, labels, depth)),
                            ),
                        };
                        let (constant, tag, tag_name, untagged) = match case {
                            ConstructorCase::Constant(tag) => (true, tag, None, false),
                            ConstructorCase::Block(Block::Tagged(block)) => {
                                (false, &block.tag, block.tag_name.clone(), false)
                            }
                            ConstructorCase::Block(Block::Untagged { tag, .. }) => {
                                (false, tag, None, true)
                            }
                        };
                        json!({
                            "name": constructor.cd_id.name(),
                            "constant": constant,
                            "tag": literal(tag),
                            "tagName": tag_name.unwrap_or_else(|| "TAG".into()),
                            "untagged": untagged,
                            "args": arguments,
                            "fields": fields,
                        })
                    })
                    .collect();
                json!({ "k": "variant", "unboxed": layout.unboxed, "cases": cases })
            }
            _ => unreachable!("checked above"),
        };
        self.defs[id] = def;
        json!({ "k": "ref", "id": id })
    }

    fn fields(
        &mut self,
        params: &[TypeExprRef],
        args: &[TypeExprRef],
        labels: &[LabelDeclaration],
        depth: usize,
    ) -> Vec<Value> {
        labels
            .iter()
            .map(|label| {
                let name = label.ld_id.name().to_string();
                let member =
                    crate::macros::reflect::member_type(self.ctx, params, args, label.ld_type);
                let shape = self.of(member, depth + 1);
                // An optional field holds the value itself, not an option.
                let shape = match (&shape, label.ld_optional) {
                    (Value::Object(object), true) if object.get("k") == Some(&json!("option")) => {
                        object.get("of").cloned().unwrap_or(shape.clone())
                    }
                    _ => shape,
                };
                json!({
                    "name": name,
                    "js": label.ld_runtime_name.clone().unwrap_or(name.clone()),
                    "optional": label.ld_optional,
                    "of": shape,
                })
            })
            .collect()
    }
}

/// The value a constructor is at run time, or the value of its tag: what
/// `@as` states, and the constructor's name when it states nothing.
fn literal(tag: &Tag) -> Value {
    match &tag.literal {
        None => json!({ "t": "string", "v": tag.name.to_string() }),
        Some(LiteralTag::String(text)) => json!({ "t": "string", "v": text }),
        Some(LiteralTag::Int(number)) => json!({ "t": "number", "v": number }),
        Some(LiteralTag::Float(text)) => json!({ "t": "number", "v": text.parse::<f64>().ok() }),
        Some(LiteralTag::BigInt(text)) => json!({ "t": "bigint", "v": text }),
        Some(LiteralTag::Bool(value)) => json!({ "t": "boolean", "v": value }),
        Some(LiteralTag::Null) => json!({ "t": "null" }),
        Some(LiteralTag::Undefined) => json!({ "t": "undefined" }),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_last_expression_is_bound() {
        let prepared = prepare("let x = 1\n  x + 1\n", "Input.res").unwrap();
        assert_eq!(prepared.source, "let x = 1\n  let it = x + 1\n");
        assert_eq!(prepared.result_at, Some((2, 3)));
        assert!(prepared.opens.is_empty());
    }

    #[test]
    fn declarations_are_left_as_written() {
        let source = "open Belt\ntype t = A\nConsole.log(1)\nlet x = A\nopen! Stdlib.Array\n";
        let prepared = prepare(source, "Input.res").unwrap();
        assert_eq!(prepared.source, source);
        assert_eq!(prepared.result_at, None);
        assert_eq!(prepared.opens, ["open Belt", "open! Stdlib.Array"]);
    }

    #[test]
    fn an_input_that_does_not_parse_is_not_prepared() {
        assert!(prepare("let x = (", "Input.res").is_none());
    }
}
