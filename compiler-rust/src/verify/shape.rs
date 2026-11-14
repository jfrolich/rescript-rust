//! Describes a type's values the way they are at run time (docs/verify/law.md).
//!
//! `rescript verify` makes values of a law's parameter types and of a spec's
//! actions, and prints the ones that break a check. Both need to know, for each type, which values
//! it has and what each is in JavaScript: a constructor's tag, a field's
//! name. A shape is that description as JSON, read by the runner
//! (rewatch/src/verify/runner.mjs).
//!
//! A shape is built from the type and the declarations it names:
//!
//! - `{"k":"int"}`, and likewise `float`, `string`, `bool`, `unit`,
//!   `bigint`, `char`;
//! - `{"k":"option","of":S}`, and likewise `array`, `list`, `dict`;
//! - `{"k":"tuple","of":[S]}`;
//! - `{"k":"poly","cases":[{"n":name,"arg":S?}]}` for a polymorphic variant;
//! - `{"k":"opaque"}` for a part of a type that is only printed
//!   ([`for_printing`]) and has no shape;
//! - `{"k":"named","id":id}` for a record or variant, whose definition is in
//!   the table under `id` (so a recursive type refers to itself):
//!   `{"k":"record","name","repr","fields":[{"n","js","opt","s"}]}` or
//!   `{"k":"variant","name","cases":[{"n","lit","tagName"?,"untagged"?,
//!   "args"?,"fields"?}]}`.
//!
//! The representation of a variant comes from the layout the backend
//! compiles constructors with (`types::variant_runtime::Layout`), so the two
//! cannot disagree.

use std::collections::HashMap;

use serde_json::{Map, Value, json};

use crate::types::asttypes::PrivateFlag;
use crate::types::context::TypeContext;
use crate::types::decl::{
    ConstructorArguments, LabelDeclaration, RecordRepresentation, TypeDeclaration, TypeKind,
};
use crate::types::type_expr::TypeDesc;
use crate::types::variant_runtime::{Block, ConstructorCase, LiteralTag};
use crate::types::{Env, Path, TypeExprRef, predef};

/// The definitions of the records and variants the shapes of one item name.
#[derive(Debug, Clone, Default)]
pub struct Definitions {
    /// By id, in the order they were first named.
    defs: Vec<(String, Option<Value>)>,
}

impl Definitions {
    /// The table as a JSON object.
    pub fn into_json(self) -> Value {
        let mut map = Map::new();
        for (id, def) in self.defs {
            map.insert(id, def.unwrap_or(Value::Null));
        }
        Value::Object(map)
    }

    /// The definition under an id, once it is complete.
    pub fn get(&self, id: &str) -> Option<&Value> {
        self.defs[self.position(id)?].1.as_ref()
    }

    /// The table as JSON text.
    pub fn to_json(&self) -> String {
        self.clone().into_json().to_string()
    }

    fn position(&self, id: &str) -> Option<usize> {
        self.defs.iter().position(|(known, _)| known == id)
    }

    /// How many values a shape has, or `None` when there are more than
    /// `limit` (numbers, text, collections and recursive types have no
    /// bound). Cost: one visit of each shape node the shape reaches.
    pub fn count(&self, shape: &Value, limit: u64) -> Option<u64> {
        self.count_in(shape, limit, &mut Vec::new())
    }

    fn count_in(&self, shape: &Value, limit: u64, open: &mut Vec<String>) -> Option<u64> {
        let within = |n: u64| (n <= limit).then_some(n);
        match shape["k"].as_str()? {
            "bool" => Some(2),
            "unit" => Some(1),
            "option" => within(1 + self.count_in(&shape["of"], limit, open)?),
            "tuple" => self.count_product(parts(&shape["of"]), limit, open),
            "poly" => {
                let mut total = 0u64;
                for case in parts(&shape["cases"]) {
                    total = within(match case.get("arg") {
                        Some(arg) => total + self.count_in(arg, limit, open)?,
                        None => total + 1,
                    })?;
                }
                Some(total)
            }
            "named" => {
                let id = shape["id"].as_str()?;
                if open.iter().any(|entered| entered == id) {
                    return None;
                }
                let definition = self.defs[self.position(id)?].1.as_ref()?;
                open.push(id.to_string());
                let total = self.count_definition(definition, limit, open);
                open.pop();
                total
            }
            _ => None,
        }
    }

    fn count_product<'v>(
        &self,
        shapes: impl Iterator<Item = &'v Value>,
        limit: u64,
        open: &mut Vec<String>,
    ) -> Option<u64> {
        let mut total = 1u64;
        for shape in shapes {
            total = total.checked_mul(self.count_in(shape, limit, open)?)?;
            if total > limit {
                return None;
            }
        }
        Some(total)
    }

    fn count_definition(
        &self,
        definition: &Value,
        limit: u64,
        open: &mut Vec<String>,
    ) -> Option<u64> {
        let fields = |fields: &Value, open: &mut Vec<String>| {
            self.count_product(parts(fields).map(|field| &field["s"]), limit, open)
        };
        if definition["k"] == "record" {
            return fields(&definition["fields"], open);
        }
        let mut total = 0u64;
        for case in parts(&definition["cases"]) {
            total += if let Some(args) = case.get("args") {
                self.count_product(parts(args), limit, open)?
            } else if let Some(record) = case.get("fields") {
                fields(record, open)?
            } else {
                1
            };
            if total > limit {
                return None;
            }
        }
        Some(total)
    }
}

/// The items of a JSON array.
fn parts(value: &Value) -> impl Iterator<Item = &Value> {
    value.as_array().into_iter().flatten()
}

/// Why values of a type cannot be made.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Unsupported(pub String);

/// The shape of a type. Cost: one visit of each type node and of each
/// declaration instance the type reaches.
pub fn of_type(
    ctx: &TypeContext,
    env: &Env,
    ty: TypeExprRef,
    definitions: &mut Definitions,
) -> Result<Value, Unsupported> {
    Walk {
        ctx,
        env,
        definitions,
        printing: false,
    }
    .ty(ty, &HashMap::new())
}

/// The shape of a type whose values are only printed, never made: a part
/// that has no shape (an abstract type, a function) is `{"k":"opaque"}`.
pub fn for_printing(
    ctx: &TypeContext,
    env: &Env,
    ty: TypeExprRef,
    definitions: &mut Definitions,
) -> Value {
    Walk {
        ctx,
        env,
        definitions,
        printing: true,
    }
    .ty(ty, &HashMap::new())
    .unwrap_or_else(|_| scalar("opaque"))
}

struct Walk<'a> {
    ctx: &'a TypeContext,
    env: &'a Env,
    definitions: &'a mut Definitions,
    /// Whether a part without a shape is opaque, not an error.
    printing: bool,
}

/// The shapes a declaration's parameters stand for where it is used.
type Parameters = HashMap<TypeExprRef, Value>;

fn scalar(kind: &str) -> Value {
    json!({ "k": kind })
}

impl Walk<'_> {
    fn ty(&mut self, ty: TypeExprRef, parameters: &Parameters) -> Result<Value, Unsupported> {
        match self.described(ty, parameters) {
            Err(_) if self.printing => Ok(scalar("opaque")),
            result => result,
        }
    }

    fn described(
        &mut self,
        ty: TypeExprRef,
        parameters: &Parameters,
    ) -> Result<Value, Unsupported> {
        let ctx = self.ctx;
        let ty = ctx.repr(ty);
        let (path, args) = match &*ctx.borrow_desc(ty) {
            TypeDesc::Tvar(_) | TypeDesc::Tunivar(_) => {
                // A law about every type is tested at `int`.
                return Ok(parameters
                    .get(&ty)
                    .cloned()
                    .unwrap_or_else(|| scalar("int")));
            }
            TypeDesc::Tpoly { body, .. } => return self.ty(*body, parameters),
            TypeDesc::Ttuple(parts) => {
                let parts: Vec<TypeExprRef> = ctx.type_list(*parts).iter().collect();
                let parts = parts
                    .into_iter()
                    .map(|part| self.ty(part, parameters))
                    .collect::<Result<Vec<_>, _>>()?;
                return Ok(json!({ "k": "tuple", "of": parts }));
            }
            TypeDesc::Tarrow { .. } => {
                return Err(Unsupported(
                    "it has a function in it, and functions cannot be generated yet".to_string(),
                ));
            }
            TypeDesc::Tvariant(row) => {
                let row = ctx.row_desc(*row);
                let row = crate::types::btype::row_repr(ctx, &row);
                let mut cases = Vec::new();
                for (label, field) in row.row_fields.iter() {
                    match field {
                        crate::types::RowField::Rpresent(None) => {
                            cases.push(json!({ "n": label.to_string() }));
                        }
                        crate::types::RowField::Rpresent(Some(payload)) => {
                            let arg = self.ty(*payload, parameters)?;
                            cases.push(json!({ "n": label.to_string(), "arg": arg }));
                        }
                        _ => {}
                    }
                }
                if cases.is_empty() {
                    return Err(Unsupported(
                        "it is a polymorphic variant with no case that is always present"
                            .to_string(),
                    ));
                }
                return Ok(json!({ "k": "poly", "cases": cases }));
            }
            TypeDesc::Tconstr { path, args, .. } => {
                let args: Vec<TypeExprRef> = ctx.type_list(*args).iter().collect();
                (*path, args)
            }
            _ => {
                return Err(Unsupported(
                    "it has an object or a first-class module in it".to_string(),
                ));
            }
        };
        self.constr(&path, &args, parameters)
    }

    fn constr(
        &mut self,
        path: &Path,
        args: &[TypeExprRef],
        parameters: &Parameters,
    ) -> Result<Value, Unsupported> {
        for (predefined, kind) in [
            (predef::path_int(), "int"),
            (predef::path_float(), "float"),
            (predef::path_string(), "string"),
            (predef::path_bool(), "bool"),
            (predef::path_unit(), "unit"),
            (predef::path_bigint(), "bigint"),
            (predef::path_char(), "char"),
        ] {
            if path.same(&predefined) {
                return Ok(scalar(kind));
            }
        }
        let args = args
            .iter()
            .map(|arg| self.ty(*arg, parameters))
            .collect::<Result<Vec<_>, _>>()?;
        for (predefined, kind) in [
            (predef::path_option(), "option"),
            (predef::path_array(), "array"),
            (predef::path_list(), "list"),
            (predef::path_dict(), "dict"),
        ] {
            if path.same(&predefined) {
                return Ok(
                    json!({ "k": kind, "of": args.first().cloned().unwrap_or(Value::Null) }),
                );
            }
        }
        if path.same(&predef::path_promise()) {
            return Err(Unsupported("it has a promise in it".to_string()));
        }
        if path.same(&predef::path_exn()) {
            return Err(Unsupported("it has an exception in it".to_string()));
        }
        let name = path.name();
        let Ok(declaration) = self.env.lookup_type(path) else {
            return Err(Unsupported(format!("the type `{name}` is not known here")));
        };
        let declaration: TypeDeclaration = declaration.clone();
        let mut own = Parameters::new();
        for (parameter, arg) in declaration.type_params.iter().zip(&args) {
            own.insert(self.ctx.repr(*parameter), arg.clone());
        }
        let private = declaration.type_private == PrivateFlag::Private;
        match &declaration.type_kind {
            TypeKind::TypeAbstract => match declaration.type_manifest {
                Some(manifest) if !private => self.ty(manifest, &own),
                _ => Err(Unsupported(format!(
                    "`{name}` is an abstract type: only its module can make its values"
                ))),
            },
            TypeKind::TypeOpen => Err(Unsupported(format!(
                "`{name}` is an extensible type, whose constructors are not all known"
            ))),
            TypeKind::TypeRecord(..) | TypeKind::TypeVariant(..) if private => Err(Unsupported(
                format!("`{name}` is a private type: only its module can make its values"),
            )),
            TypeKind::TypeRecord(labels, representation) => {
                let id = instance_id(&name, &args);
                let Some(slot) = self.enter(&id) else {
                    return Ok(json!({ "k": "named", "id": id }));
                };
                let fields = self.fields(labels, &own)?;
                let repr = match representation {
                    RecordRepresentation::RecordArray => "array",
                    RecordRepresentation::RecordUnboxed(_) => "unboxed",
                    _ => "object",
                };
                self.definitions.defs[slot].1 = Some(json!({
                    "k": "record",
                    "name": path.last(),
                    "repr": repr,
                    "fields": fields,
                }));
                Ok(json!({ "k": "named", "id": id }))
            }
            TypeKind::TypeVariant(constructors, layout) => {
                let id = instance_id(&name, &args);
                let Some(slot) = self.enter(&id) else {
                    return Ok(json!({ "k": "named", "id": id }));
                };
                let layout = self.ctx.variant_layout(*layout);
                let mut cases = Vec::new();
                for (constructor, case) in constructors.iter().zip(&layout.constructors) {
                    let constructor_name = constructor.cd_id.name();
                    if constructor.cd_res.is_some() {
                        return Err(Unsupported(format!(
                            "`{name}` is a GADT: the constructor `{constructor_name}` fixes its type arguments"
                        )));
                    }
                    let mut entry = Map::new();
                    entry.insert("n".to_string(), json!(constructor_name));
                    match case {
                        ConstructorCase::Constant(tag) => {
                            entry.insert("lit".to_string(), literal(&tag.literal));
                        }
                        ConstructorCase::Block(Block::Tagged(block)) => {
                            entry.insert("lit".to_string(), literal(&block.tag.literal));
                            entry.insert(
                                "tagName".to_string(),
                                json!(block.tag_name.as_deref().unwrap_or("TAG")),
                            );
                        }
                        ConstructorCase::Block(Block::Untagged { .. }) => {
                            entry.insert("untagged".to_string(), json!(true));
                        }
                    }
                    match &constructor.cd_args {
                        ConstructorArguments::CstrTuple(types) if types.is_empty() => {}
                        ConstructorArguments::CstrTuple(types) => {
                            let types = types
                                .iter()
                                .map(|ty| self.ty(*ty, &own))
                                .collect::<Result<Vec<_>, _>>()?;
                            entry.insert("args".to_string(), json!(types));
                        }
                        ConstructorArguments::CstrRecord(labels) => {
                            let fields = self.fields(labels, &own)?;
                            entry.insert("fields".to_string(), json!(fields));
                        }
                    }
                    cases.push(Value::Object(entry));
                }
                self.definitions.defs[slot].1 = Some(json!({
                    "k": "variant",
                    "name": path.last(),
                    "cases": cases,
                }));
                Ok(json!({ "k": "named", "id": id }))
            }
        }
    }

    /// Starts the definition `id`, or returns `None` when it is known or
    /// being built (a recursive type).
    fn enter(&mut self, id: &str) -> Option<usize> {
        if self.definitions.position(id).is_some() {
            return None;
        }
        self.definitions.defs.push((id.to_string(), None));
        Some(self.definitions.defs.len() - 1)
    }

    fn fields(
        &mut self,
        labels: &[LabelDeclaration],
        parameters: &Parameters,
    ) -> Result<Vec<Value>, Unsupported> {
        labels
            .iter()
            .map(|label| {
                let name = label.ld_id.name();
                Ok(json!({
                    "n": name,
                    "js": label.ld_runtime_name.as_deref().unwrap_or(name),
                    "opt": label.ld_optional,
                    "s": self.ty(label.ld_type, parameters)?,
                }))
            })
            .collect()
    }
}

/// A declaration at given type arguments: `tree<int>` and `tree<string>` are
/// two definitions.
fn instance_id(name: &str, args: &[Value]) -> String {
    if args.is_empty() {
        return name.to_string();
    }
    let args: Vec<String> = args.iter().map(short).collect();
    format!("{name}<{}>", args.join(", "))
}

/// A shape as a type argument is written, for definition ids.
fn short(shape: &Value) -> String {
    let kind = shape["k"].as_str().unwrap_or("?");
    match kind {
        "named" => shape["id"].as_str().unwrap_or("?").to_string(),
        "option" | "array" | "list" | "dict" => format!("{kind}<{}>", short(&shape["of"])),
        "tuple" => {
            let parts: Vec<String> = shape["of"]
                .as_array()
                .map(|parts| parts.iter().map(short).collect())
                .unwrap_or_default();
            format!("({})", parts.join(", "))
        }
        "poly" => shape.to_string(),
        scalar => scalar.to_string(),
    }
}

/// A constructor's runtime literal as JSON. `undefined` and bigints have no
/// JSON form of their own.
fn literal(tag: &LiteralTag) -> Value {
    match tag {
        LiteralTag::String(text) => json!(text),
        LiteralTag::Int(number) => json!(number),
        LiteralTag::Float(text) => text
            .parse::<f64>()
            .ok()
            .and_then(serde_json::Number::from_f64)
            .map(Value::Number)
            .unwrap_or_else(|| json!({ "float": text })),
        LiteralTag::BigInt(digits) => json!({ "bigint": digits }),
        LiteralTag::Bool(value) => json!(value),
        LiteralTag::Null => Value::Null,
        LiteralTag::Undefined => json!({ "undefined": true }),
    }
}
