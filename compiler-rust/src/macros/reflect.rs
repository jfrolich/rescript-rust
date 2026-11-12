//! Answers to a macro's questions about types.
//!
//! A macro holds a type as source text plus a handle: an index into the
//! [`TypeTable`] of the expansion that is running. `Type.info` sends the
//! handle back and gets one level of structure; nested types are handles
//! again, so a recursive type needs no special case and nothing is described
//! that the macro does not look at.
//!
//! The JSON written here is the run-time representation of `Macro.Type.info`
//! (packages/@rescript/runtime/Macro.res): a constructor without payload is
//! its name, one with a payload is an object tagged `TAG`.

use serde_json::{Value, json};

use crate::types::context::TypeContext;
use crate::types::ctype;
use crate::types::decl::{
    Attribute, AttributePayload, ConstructorArguments, LabelDeclaration, TypeKind,
};
use crate::types::env::Env;
use crate::types::path::Path;
use crate::types::predef;
use crate::types::type_expr::{RowField, TypeDesc, TypeExprRef};
use crate::types::variant_runtime::LiteralTag;

/// What a running expansion has handed to the macro: the types, and the
/// ranges of the text being expanded that it got as code.
#[derive(Default)]
pub struct TypeTable {
    types: Vec<TypeExprRef>,
    origins: Vec<(u32, u32)>,
}

impl TypeTable {
    pub fn get(&self, id: usize) -> Option<TypeExprRef> {
        self.types.get(id).copied()
    }

    /// The id of the text at `range`, for the `$o` of a code argument.
    pub fn origin(&mut self, range: (u32, u32)) -> usize {
        self.origins.push(range);
        self.origins.len() - 1
    }

    pub fn origins(&self) -> &[(u32, u32)] {
        &self.origins
    }

    fn add(&mut self, ctx: &TypeContext, ty: TypeExprRef) -> usize {
        let repr = ctx.repr(ty);
        if let Some(index) = self.types.iter().position(|known| ctx.repr(*known) == repr) {
            return index;
        }
        self.types.push(ty);
        self.types.len() - 1
    }
}

/// The source text of a type, as it is written where the macro is used.
pub fn print_type(ctx: &TypeContext, ty: TypeExprRef) -> String {
    let mut printer = crate::types::printtyp::Printtyp::new(ctx);
    printer.reset_and_mark_loops(ty);
    printer.type_expr(ty)
}

/// Whether inference has not settled `ty` at all.
pub fn is_unknown(ctx: &TypeContext, ty: TypeExprRef) -> bool {
    matches!(
        &*ctx.get_desc(ctx.repr(ty)),
        TypeDesc::Tvar(_) | TypeDesc::Tunivar(_)
    )
}

/// A type as the macro holds it: `{c: source, id: handle}`.
pub fn type_ref(ctx: &TypeContext, table: &mut TypeTable, ty: TypeExprRef) -> Value {
    json!({ "c": print_type(ctx, ty), "id": table.add(ctx, ty) })
}

fn attributes(attrs: &[Attribute]) -> Value {
    Value::Array(
        attrs
            .iter()
            .map(|attr| {
                let mut out = serde_json::Map::new();
                out.insert("name".into(), Value::String(attr.attr_name.txt.clone()));
                if let AttributePayload::Str(payload) = &attr.attr_payload {
                    out.insert("payload".into(), Value::String(payload.clone()));
                }
                Value::Object(out)
            })
            .collect(),
    )
}

/// Attributes a macro reads as data: everything except the ones the
/// compiler interprets itself.
fn user_attributes(attrs: &[Attribute]) -> Value {
    let user: Vec<Attribute> = attrs
        .iter()
        .filter(|attr| {
            !matches!(
                attr.attr_name.txt.as_str(),
                "as" | "res.optional" | "ns.optional" | "res.doc" | "ocaml.doc" | "deprecated"
            )
        })
        .cloned()
        .collect();
    attributes(&user)
}

fn tag_text(tag: &LiteralTag) -> String {
    match tag {
        LiteralTag::String(s) => s.clone(),
        LiteralTag::Int(i) => i.to_string(),
        LiteralTag::Float(f) | LiteralTag::BigInt(f) => f.clone(),
        LiteralTag::Bool(b) => b.to_string(),
        LiteralTag::Null => "null".into(),
        LiteralTag::Undefined => "undefined".into(),
    }
}

/// The type of a declaration's member (a field, a constructor argument) at
/// the instance `args` of the declaration's parameters.
fn member_type(
    ctx: &TypeContext,
    params: &[TypeExprRef],
    args: &[TypeExprRef],
    member: TypeExprRef,
) -> TypeExprRef {
    if params.is_empty() || params.len() != args.len() {
        return member;
    }
    let (fresh_params, fresh_member) = ctype::instance_parameterized_type(ctx, params, member);
    let mut state = ctype::UnifyState::default();
    for (param, arg) in fresh_params.iter().zip(args) {
        if ctype::unify(ctx, &mut state, *param, *arg).is_err() {
            return member;
        }
    }
    fresh_member
}

fn field(
    ctx: &TypeContext,
    table: &mut TypeTable,
    params: &[TypeExprRef],
    args: &[TypeExprRef],
    label: &LabelDeclaration,
) -> Value {
    let name = label.ld_id.name().to_string();
    let js_name = label
        .ld_runtime_name
        .clone()
        .unwrap_or_else(|| name.clone());
    let ty = member_type(ctx, params, args, label.ld_type);
    json!({
        "name": name,
        "jsName": js_name,
        "typ": type_ref(ctx, table, ty),
        "optional": label.ld_optional,
        "mutable_": label.ld_mutable == crate::types::asttypes::MutableFlag::Mutable,
        "attrs": user_attributes(&label.ld_attributes),
    })
}

fn tagged(tag: &str, fields: Value) -> Value {
    let mut out = serde_json::Map::new();
    out.insert("TAG".into(), Value::String(tag.into()));
    if let Value::Object(fields) = fields {
        out.extend(fields);
    }
    Value::Object(out)
}

fn unary(ctx: &TypeContext, table: &mut TypeTable, tag: &str, args: &[TypeExprRef]) -> Value {
    match args.first() {
        Some(arg) => tagged(tag, json!({ "_0": type_ref(ctx, table, *arg) })),
        None => Value::String("Unknown".into()),
    }
}

/// `Macro.Type.info` of `ty`.
pub fn type_info(ctx: &TypeContext, env: &Env, table: &mut TypeTable, ty: TypeExprRef) -> Value {
    type_info_at(ctx, env, table, ty, 0)
}

fn type_info_at(
    ctx: &TypeContext,
    env: &Env,
    table: &mut TypeTable,
    ty: TypeExprRef,
    depth: usize,
) -> Value {
    let ty = ctx.repr(ctype::expand_head(ctx, env, ty));
    let desc = ctx.get_desc(ty);
    match &*desc {
        TypeDesc::Tconstr { path, args, .. } => {
            let args: Vec<TypeExprRef> = ctx.type_list(*args).iter().collect();
            constructor_info(ctx, env, table, path, &args, depth)
        }
        TypeDesc::Ttuple(elements) => {
            let elements: Vec<Value> = ctx
                .type_list(*elements)
                .iter()
                .map(|element| type_ref(ctx, table, element))
                .collect();
            tagged("Tuple", json!({ "_0": elements }))
        }
        TypeDesc::Tarrow { args, ret } => {
            let params: Vec<Value> = ctx
                .type_args(*args)
                .iter()
                .map(|arg| type_ref(ctx, table, arg.typ))
                .collect();
            tagged(
                "Function",
                json!({ "params": params, "result": type_ref(ctx, table, *ret) }),
            )
        }
        TypeDesc::Tpoly { body, .. } if depth < 8 => {
            type_info_at(ctx, env, table, *body, depth + 1)
        }
        TypeDesc::Tvariant(row) => {
            let row = ctx.row_desc(*row);
            let constructors: Vec<Value> = row
                .row_fields
                .iter()
                .filter_map(|(label, field)| {
                    let args = match field {
                        RowField::Rpresent(Some(arg)) => vec![type_ref(ctx, table, *arg)],
                        RowField::Rpresent(None) => vec![],
                        _ => return None,
                    };
                    let name = label.to_string();
                    Some(json!({
                        "name": format!("#{name}"),
                        "jsName": name,
                        "args": args,
                        "fields": [],
                        "attrs": [],
                    }))
                })
                .collect();
            tagged("PolyVariant", json!({ "constructors": constructors }))
        }
        _ => Value::String("Unknown".into()),
    }
}

fn constructor_info(
    ctx: &TypeContext,
    env: &Env,
    table: &mut TypeTable,
    path: &Path,
    args: &[TypeExprRef],
    _depth: usize,
) -> Value {
    let simple = [
        (predef::path_int(), "Int"),
        (predef::path_float(), "Float"),
        (predef::path_string(), "String"),
        (predef::path_bool(), "Bool"),
        (predef::path_unit(), "Unit"),
        (predef::path_bigint(), "BigInt"),
        (predef::path_char(), "Char"),
    ];
    for (predefined, name) in &simple {
        if path.same(predefined) {
            return Value::String((*name).into());
        }
    }
    let containers = [
        (predef::path_option(), "Option"),
        (predef::path_array(), "Array"),
        (predef::path_list(), "List"),
        (predef::path_dict(), "Dict"),
        (predef::path_promise(), "Promise"),
    ];
    for (predefined, name) in &containers {
        if path.same(predefined) {
            return unary(ctx, table, name, args);
        }
    }
    if path.same(&predef::path_result()) && args.len() == 2 {
        return tagged(
            "Result",
            json!({ "_0": type_ref(ctx, table, args[0]), "_1": type_ref(ctx, table, args[1]) }),
        );
    }

    let name = path.name();
    let Some(decl) = crate::types::typemod::find_type_decl_for_path(env, ctx, path) else {
        return tagged("Abstract", json!({ "name": name }));
    };
    let params = &decl.type_params;
    match &decl.type_kind {
        TypeKind::TypeRecord(labels, _) => {
            let fields: Vec<Value> = labels
                .iter()
                .map(|label| field(ctx, table, params, args, label))
                .collect();
            tagged(
                "Record",
                json!({ "name": name, "fields": fields, "attrs": user_attributes(&decl.type_attributes) }),
            )
        }
        TypeKind::TypeVariant(constructors, _) => {
            let constructors: Vec<Value> = constructors
                .iter()
                .map(|constructor| {
                    let name = constructor.cd_id.name().to_string();
                    let js_name = constructor
                        .cd_runtime_tag
                        .as_ref()
                        .map(tag_text)
                        .unwrap_or_else(|| name.clone());
                    let (constructor_args, fields) = match &constructor.cd_args {
                        ConstructorArguments::CstrTuple(types) => (
                            types
                                .iter()
                                .map(|ty| type_ref(ctx, table, member_type(ctx, params, args, *ty)))
                                .collect::<Vec<Value>>(),
                            Vec::new(),
                        ),
                        ConstructorArguments::CstrRecord(labels) => (
                            Vec::new(),
                            labels
                                .iter()
                                .map(|label| field(ctx, table, params, args, label))
                                .collect::<Vec<Value>>(),
                        ),
                    };
                    json!({
                        "name": name,
                        "jsName": js_name,
                        "args": constructor_args,
                        "fields": fields,
                        "attrs": user_attributes(&constructor.cd_attributes),
                    })
                })
                .collect();
            tagged(
                "Variant",
                json!({ "name": name, "constructors": constructors, "attrs": user_attributes(&decl.type_attributes) }),
            )
        }
        _ => tagged("Abstract", json!({ "name": name })),
    }
}

/// The shape `%Macro.eval` needs to write a value of type `ty` as a literal
/// (read by `reify` in host.js).
pub fn value_shape(ctx: &TypeContext, env: &Env, ty: TypeExprRef, depth: usize) -> Value {
    let unsupported = |ctx: &TypeContext, ty| json!({ "k": "other", "name": print_type(ctx, ty) });
    if depth > 32 {
        return unsupported(ctx, ty);
    }
    let expanded = ctx.repr(ctype::expand_head(ctx, env, ty));
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
            ];
            for (predefined, kind) in &simple {
                if path.same(predefined) {
                    return json!({ "k": kind });
                }
            }
            let containers = [
                (predef::path_array(), "array"),
                (predef::path_option(), "option"),
                (predef::path_dict(), "dict"),
            ];
            for (predefined, kind) in &containers {
                if path.same(predefined) && args.len() == 1 {
                    return json!({ "k": kind, "of": value_shape(ctx, env, args[0], depth + 1) });
                }
            }
            let Some(decl) = crate::types::typemod::find_type_decl_for_path(env, ctx, path) else {
                return unsupported(ctx, ty);
            };
            match &decl.type_kind {
                TypeKind::TypeRecord(labels, _) => {
                    let fields: Vec<Value> = labels
                        .iter()
                        .map(|label| {
                            let name = label.ld_id.name().to_string();
                            let field_type =
                                member_type(ctx, &decl.type_params, &args, label.ld_type);
                            // An optional field holds the value itself, not an option.
                            let shape = value_shape(ctx, env, field_type, depth + 1);
                            let shape = match (&shape, label.ld_optional) {
                                (Value::Object(object), true)
                                    if object.get("k") == Some(&json!("option")) =>
                                {
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
                        .collect();
                    json!({ "k": "record", "fields": fields })
                }
                _ => unsupported(ctx, ty),
            }
        }
        TypeDesc::Ttuple(elements) => {
            let of: Vec<Value> = ctx
                .type_list(*elements)
                .iter()
                .map(|element| value_shape(ctx, env, element, depth + 1))
                .collect();
            json!({ "k": "tuple", "of": of })
        }
        _ => unsupported(ctx, ty),
    }
}
