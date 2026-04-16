//! Compile-time metaprogramming infrastructure.
//!
//! This module implements Zig-style comptime for ReScript:
//! - TypeInfo: runtime-inspectable type structure
//! - ComptimeValue: values known at compile time
//! - Specialization engine: partial evaluation of @comptime functions

use std::collections::HashMap;

use super::context::TypeContext;
use super::ctype;
use super::decl::{ConstructorArguments, TypeKind};
use super::env::Env;
use super::path::Path;
use super::predef;
use super::type_expr::{TypeDesc, TypeExprRef};
use super::typedtree;

use crate::parse_arena::LocIdx;

// ── Comptime Function Registration ─────────────────────────────────────────

/// A registered @comptime function.
///
/// The function body is NOT type-checked at definition time because it
/// contains comptime-only expressions (@typeInfo, inline for) that require
/// concrete types. The parse tree body index is stored and the body is
/// type-checked at each call site after the partial evaluator resolves
/// comptime expressions with concrete type information.
#[derive(Debug, Clone)]
pub struct ComptimeFunction {
    /// Parse tree expression index of the function body.
    pub body_expr_idx: crate::parse_arena::ExprIdx,
    /// Parameter names and which are comptime.
    pub params: Vec<ComptimeParam>,
    /// Function name (for error messages).
    pub name: String,
}

/// A registered @comptime.derive handler.
/// Stores the parse tree of the function body. When the derive triggers,
/// the partial evaluator walks this parse tree with @typeInfo(T) resolved
/// to the concrete type's TypeInfo, picks switch branches, unrolls inline for,
/// and produces ReScript source code that gets spliced after the type declaration.
#[derive(Debug, Clone)]
pub struct DeriveRegistration {
    /// The parse tree body of the derive function (stored as ExprIdx into the arena).
    /// When the derive triggers, this is walked with concrete TypeInfo substituted.
    pub parse_body_source: String,
    /// Function name.
    pub name: String,
}

/// Walk a comptime function body (as source) with concrete TypeInfo substituted.
/// This is the core of the derive system:
/// 1. Resolve @typeInfo(T) to the concrete TypeInfo
/// 2. Match switch patterns (Record, Variant, etc.)
/// 3. Unroll inline for over fields/constructors
/// 4. Produce ReScript source code
///
/// For now, this implements the common derive patterns directly.
/// When the full parse-tree-walking partial evaluator is built,
/// this will walk the actual parse tree instead.
pub fn evaluate_derive_body(
    type_info: &TypeInfo,
    type_name: &str,
    handler: &DeriveRegistration,
) -> Result<String, String> {
    // The handler's source describes the transformation.
    // For now, we can't walk arbitrary parse trees, so we check
    // if the handler was registered and use the TypeInfo-driven
    // source generation that implements what the user's function
    // body would do.
    //
    // This is a temporary bridge: the user writes the comptime function,
    // the compiler stores its registration, and uses TypeInfo-driven
    // generation to produce the same output. Once the parse tree walker
    // works, this will actually evaluate the user's code.
    let _ = handler; // Will be used when parse tree walking works

    // For now, generate based on TypeInfo structure
    // (this produces the same output as the user's function would)
    Err(format!(
        "Derive handler '{}' registered but parse tree evaluation not yet implemented",
        handler.name
    ))
}

/// A parameter of a comptime function.
#[derive(Debug, Clone)]
pub struct ComptimeParam {
    /// Parameter name.
    pub name: String,
    /// Whether this parameter is comptime.
    pub is_comptime: bool,
    /// Whether this is a type parameter (comptime T: type).
    pub is_type: bool,
}

/// Default fuel for comptime evaluation.
pub const DEFAULT_FUEL: usize = 100_000;

// ── TypeInfo ────────────────────────────────────────────────────────────────

/// Runtime-inspectable type structure, produced by `@typeInfo(T)`.
#[derive(Debug, Clone, PartialEq)]
pub enum TypeInfo {
    Int,
    Float,
    String,
    Bool,
    Unit,
    Char,
    Bigint,
    Array {
        element: Box<TypeInfo>,
    },
    Option {
        inner: Box<TypeInfo>,
    },
    Tuple {
        elements: Vec<TypeInfo>,
    },
    Record {
        name: std::string::String,
        fields: Vec<FieldInfo>,
        unboxed: bool,
    },
    Variant {
        name: std::string::String,
        constructors: Vec<ConstructorInfo>,
        unboxed: bool,
    },
    Function {
        args: Vec<TypeInfo>,
        return_type: Box<TypeInfo>,
    },
    External {
        name: std::string::String,
    },
    Opaque {
        name: std::string::String,
    },
    Unknown {
        description: std::string::String,
    },
}

/// A record field.
#[derive(Debug, Clone, PartialEq)]
pub struct FieldInfo {
    pub name: std::string::String,
    pub typ: TypeInfo,
    pub mutable: bool,
    pub optional: bool,
    pub attributes: Vec<(std::string::String, std::string::String)>,
}

/// A variant constructor.
#[derive(Debug, Clone, PartialEq)]
pub struct ConstructorInfo {
    pub name: std::string::String,
    pub args: Vec<TypeInfo>,
    pub attributes: Vec<(std::string::String, std::string::String)>,
}

// ── ComptimeValue ───────────────────────────────────────────────────────────

/// A value known at compile time.
#[derive(Debug, Clone, PartialEq)]
pub enum ComptimeValue {
    /// A type (for `comptime T: type` parameters).
    Type(TypeInfo),
    /// An integer literal.
    Int(i64),
    /// A float literal.
    Float(f64),
    /// A string literal.
    String(std::string::String),
    /// A boolean.
    Bool(bool),
    /// Unit value.
    Unit,
    /// An array of comptime values (for inline for).
    Array(Vec<ComptimeValue>),
    /// A record of comptime values.
    Record(Vec<(std::string::String, ComptimeValue)>),
    /// A variant constructor.
    Variant(std::string::String, Option<Box<ComptimeValue>>),
}

// ── build_type_info ─────────────────────────────────────────────────────────

/// Build a TypeInfo from a compiler type expression.
///
/// Resolves aliases, identifies primitives, and inspects user-defined types
/// (records, variants) through their declarations in the type context.
pub fn build_type_info<'a>(
    ctx: &'a TypeContext<'a>,
    env: &Env,
    ty: TypeExprRef,
    visited: &mut Vec<TypeExprRef>,
) -> TypeInfo {
    // Resolve aliases and links
    let ty = ctype::expand_head(ctx, env, ty);
    let ty = ctx.repr(ty);

    // Cycle detection
    if visited.contains(&ty) {
        return TypeInfo::Unknown {
            description: "recursive type".to_string(),
        };
    }
    visited.push(ty);

    let desc = ctx.get_desc(ty);
    let result = match &*desc {
        TypeDesc::Tconstr { path, args, .. } => build_type_info_from_constr(ctx, env, path, args, visited),

        TypeDesc::Ttuple(elements) => TypeInfo::Tuple {
            elements: elements
                .iter()
                .map(|t| build_type_info(ctx, env, *t, visited))
                .collect(),
        },

        TypeDesc::Tarrow { arg, ret, .. } => {
            let mut args = vec![build_type_info(ctx, env, arg.typ, visited)];
            // Collect all arrow arguments
            let mut current_ret = *ret;
            loop {
                let ret_repr = ctx.repr(current_ret);
                let ret_desc = ctx.get_desc(ret_repr);
                match &*ret_desc {
                    TypeDesc::Tarrow { arg: next_arg, ret: next_ret, .. } => {
                        args.push(build_type_info(ctx, env, next_arg.typ, visited));
                        current_ret = *next_ret;
                    }
                    _ => break,
                }
            }
            TypeInfo::Function {
                args,
                return_type: Box::new(build_type_info(ctx, env, current_ret, visited)),
            }
        }

        TypeDesc::Tvar(_) | TypeDesc::Tunivar(_) => TypeInfo::Unknown {
            description: "type variable".to_string(),
        },

        TypeDesc::Tpoly { body, .. } => build_type_info(ctx, env, *body, visited),

        TypeDesc::Tvariant(_) => TypeInfo::Unknown {
            description: "polymorphic variant".to_string(),
        },

        TypeDesc::Tobject { .. } => TypeInfo::Unknown {
            description: "object type".to_string(),
        },

        TypeDesc::Tlink(inner) => build_type_info(ctx, env, *inner, visited),
        TypeDesc::Tsubst(inner) => build_type_info(ctx, env, *inner, visited),

        TypeDesc::Tnil | TypeDesc::Tfield { .. } | TypeDesc::Tpackage { .. } => {
            TypeInfo::Unknown {
                description: format!("{:?}", &*desc),
            }
        }
    };

    visited.pop();
    result
}

/// Build TypeInfo from a Tconstr (type constructor application).
fn build_type_info_from_constr<'a>(
    ctx: &'a TypeContext<'a>,
    env: &Env,
    path: &Path,
    args: &[TypeExprRef],
    visited: &mut Vec<TypeExprRef>,
) -> TypeInfo {
    // Check primitive types by path
    if path.same(&predef::path_int()) {
        return TypeInfo::Int;
    }
    if path.same(&predef::path_float()) {
        return TypeInfo::Float;
    }
    if path.same(&predef::path_string()) {
        return TypeInfo::String;
    }
    if path.same(&predef::path_bool()) {
        return TypeInfo::Bool;
    }
    if path.same(&predef::path_unit()) {
        return TypeInfo::Unit;
    }
    if path.same(&predef::path_char()) {
        return TypeInfo::Char;
    }
    if path.same(&predef::path_bigint()) {
        return TypeInfo::Bigint;
    }
    if path.same(&predef::path_array()) {
        let element = args
            .first()
            .map(|t| build_type_info(ctx, env, *t, visited))
            .unwrap_or(TypeInfo::Unknown {
                description: "array element".to_string(),
            });
        return TypeInfo::Array {
            element: Box::new(element),
        };
    }
    if path.same(&predef::path_option()) {
        let inner = args
            .first()
            .map(|t| build_type_info(ctx, env, *t, visited))
            .unwrap_or(TypeInfo::Unknown {
                description: "option inner".to_string(),
            });
        return TypeInfo::Option {
            inner: Box::new(inner),
        };
    }

    // Look up user-defined type declaration
    let type_name = path.name().to_string();

    // Try to find the type declaration by stamp (from the path's ident)
    let decl = match path {
        Path::Pident(id) => ctx.find_type_decl_by_stamp(id.stamp()),
        _ => ctx.find_type_decl_by_path(&path.to_string()),
    };

    if let Some(decl) = decl {
        let is_unboxed = decl.type_unboxed.unboxed;
        match &decl.type_kind {
            TypeKind::TypeRecord(labels, _) => {
                let fields = labels
                    .iter()
                    .map(|ld| {
                        let field_ty = build_type_info(ctx, env, ld.ld_type, visited);
                        let attributes = extract_attributes(&ld.ld_attributes);
                        FieldInfo {
                            name: ld.ld_id.name().to_string(),
                            typ: field_ty,
                            mutable: ld.ld_mutable == super::asttypes::MutableFlag::Mutable,
                            optional: ld.ld_optional,
                            attributes,
                        }
                    })
                    .collect();
                TypeInfo::Record {
                    name: type_name,
                    fields,
                    unboxed: is_unboxed,
                }
            }
            TypeKind::TypeVariant(constrs) => {
                let constructors = constrs
                    .iter()
                    .map(|cd| {
                        let args = match &cd.cd_args {
                            ConstructorArguments::CstrTuple(tys) => tys
                                .iter()
                                .map(|t| build_type_info(ctx, env, *t, visited))
                                .collect(),
                            ConstructorArguments::CstrRecord(labels) => labels
                                .iter()
                                .map(|ld| build_type_info(ctx, env, ld.ld_type, visited))
                                .collect(),
                        };
                        let attributes = extract_attributes(&cd.cd_attributes);
                        ConstructorInfo {
                            name: cd.cd_id.name().to_string(),
                            args,
                            attributes,
                        }
                    })
                    .collect();
                TypeInfo::Variant {
                    name: type_name,
                    constructors,
                    unboxed: is_unboxed,
                }
            }
            TypeKind::TypeAbstract => {
                // Check for manifest (alias)
                if let Some(manifest) = decl.type_manifest {
                    build_type_info(ctx, env, manifest, visited)
                } else {
                    TypeInfo::Opaque {
                        name: type_name,
                    }
                }
            }
            TypeKind::TypeOpen => TypeInfo::Unknown {
                description: format!("open type {}", type_name),
            },
        }
    } else {
        // No declaration found — try manifest if the type has one via env lookup
        TypeInfo::External {
            name: type_name,
        }
    }
}

/// Extract attributes as (name, value) pairs from compiler attributes.
/// TODO: Proper attribute extraction requires arena access for StrIdx resolution.
fn extract_attributes(_attrs: &[crate::types::decl::Attribute]) -> Vec<(std::string::String, std::string::String)> {
    // For now, return empty — full attribute extraction needs ParseArena
    Vec::new()
}

// ── Comptime Pattern Matching ───────────────────────────────────────────────

/// Try to match a ComptimeValue against a TypeInfo variant pattern.
/// Returns bindings if matched.
pub fn match_typeinfo_pattern(
    value: &TypeInfo,
    pattern_name: &str,
) -> Option<HashMap<std::string::String, ComptimeValue>> {
    let mut bindings = HashMap::new();
    match (pattern_name, value) {
        ("Int", TypeInfo::Int) => Some(bindings),
        ("Float", TypeInfo::Float) => Some(bindings),
        ("String", TypeInfo::String) => Some(bindings),
        ("Bool", TypeInfo::Bool) => Some(bindings),
        ("Unit", TypeInfo::Unit) => Some(bindings),
        ("Char", TypeInfo::Char) => Some(bindings),
        ("Bigint", TypeInfo::Bigint) => Some(bindings),
        ("Array", TypeInfo::Array { element }) => {
            bindings.insert(
                "element".to_string(),
                ComptimeValue::Type(*element.clone()),
            );
            Some(bindings)
        }
        ("Option", TypeInfo::Option { inner }) => {
            bindings.insert("inner".to_string(), ComptimeValue::Type(*inner.clone()));
            Some(bindings)
        }
        ("Record", TypeInfo::Record { name, fields, unboxed }) => {
            let field_values: Vec<ComptimeValue> = fields
                .iter()
                .map(|f| {
                    ComptimeValue::Record(vec![
                        ("name".to_string(), ComptimeValue::String(f.name.clone())),
                        ("typ".to_string(), ComptimeValue::Type(f.typ.clone())),
                        (
                            "mutable".to_string(),
                            ComptimeValue::Bool(f.mutable),
                        ),
                        (
                            "optional".to_string(),
                            ComptimeValue::Bool(f.optional),
                        ),
                    ])
                })
                .collect();
            bindings.insert("fields".to_string(), ComptimeValue::Array(field_values));
            bindings.insert("name".to_string(), ComptimeValue::String(name.clone()));
            bindings.insert("unboxed".to_string(), ComptimeValue::Bool(*unboxed));
            Some(bindings)
        }
        ("Variant", TypeInfo::Variant { name, constructors, unboxed }) => {
            let ctor_values: Vec<ComptimeValue> = constructors
                .iter()
                .map(|c| {
                    let arg_types: Vec<ComptimeValue> = c
                        .args
                        .iter()
                        .map(|t| ComptimeValue::Type(t.clone()))
                        .collect();
                    ComptimeValue::Record(vec![
                        ("name".to_string(), ComptimeValue::String(c.name.clone())),
                        ("args".to_string(), ComptimeValue::Array(arg_types)),
                    ])
                })
                .collect();
            bindings.insert(
                "constructors".to_string(),
                ComptimeValue::Array(ctor_values),
            );
            bindings.insert("name".to_string(), ComptimeValue::String(name.clone()));
            bindings.insert("unboxed".to_string(), ComptimeValue::Bool(*unboxed));
            Some(bindings)
        }
        ("Function", TypeInfo::Function { args, return_type }) => {
            let arg_values: Vec<ComptimeValue> = args
                .iter()
                .map(|t| ComptimeValue::Type(t.clone()))
                .collect();
            bindings.insert("args".to_string(), ComptimeValue::Array(arg_values));
            bindings.insert(
                "return_type".to_string(),
                ComptimeValue::Type(*return_type.clone()),
            );
            Some(bindings)
        }
        _ => None,
    }
}

// ── Partial Evaluator ───────────────────────────────────────────────────────
//
// The partial evaluator walks the typed tree of a @comptime function with
// comptime bindings. It resolves:
//   - @typeInfo(T) → concrete TypeInfo value from TypeContext
//   - switch on comptime value → picks matching branch
//   - inline for → unrolls loop body per element
//   - @field(value, name) → generates Texp_field node
//   - recursive @comptime calls → re-specializes with new type arg
//   - runtime expressions → kept as-is in output
//
// The result is a specialized typed tree with no comptime residue.

// ── Source Generation (temporary) ───────────────────────────────────────────
//
// These functions generate ReScript source code from TypeInfo.
// They are used by the test suite and will be replaced when the
// proper typed-tree-level partial evaluator is complete.
// They demonstrate the OUTPUT that the partial evaluator should produce.

/// Generate specialized source code from TypeInfo (for testing).
pub fn generate_specialized_source(
    type_info: &TypeInfo,
    runtime_value_name: &str,
    fuel: &mut usize,
) -> Result<String, String> {
    if *fuel == 0 {
        return Err("Comptime fuel exhausted".to_string());
    }
    *fuel -= 1;

    match type_info {
        TypeInfo::String => {
            Ok(format!("Js.Json.string({})", runtime_value_name))
        }
        TypeInfo::Int => {
            Ok(format!("Js.Json.number(Int.toFloat({}))", runtime_value_name))
        }
        TypeInfo::Float => {
            Ok(format!("Js.Json.number({})", runtime_value_name))
        }
        TypeInfo::Bool => {
            Ok(format!("Js.Json.boolean({})", runtime_value_name))
        }
        TypeInfo::Record { fields, .. } => {
            let mut lines = Vec::new();
            lines.push("{".to_string());
            lines.push("  let obj = Js.Dict.empty()".to_string());
            for field in fields {
                let field_value = format!("{}.{}", runtime_value_name, field.name);
                let encoded = generate_specialized_source(
                    &field.typ,
                    &field_value,
                    fuel,
                )?;
                if field.optional {
                    lines.push(format!(
                        "  switch {}.{} {{ | Some(v) => Js.Dict.set(obj, \"{}\", {}) | None => () }}",
                        runtime_value_name,
                        field.name,
                        field.name,
                        generate_specialized_source(
                            &field.typ,
                            "v",
                            fuel,
                        )?
                    ));
                } else {
                    lines.push(format!(
                        "  Js.Dict.set(obj, \"{}\", {})",
                        field.name, encoded
                    ));
                }
            }
            lines.push("  Js.Json.object_(obj)".to_string());
            lines.push("}".to_string());
            Ok(lines.join("\n"))
        }
        TypeInfo::Array { element } => {
            let inner = generate_specialized_source(
                element,
                "v",
                fuel,
            )?;
            Ok(format!(
                "{}->Array.map(v => {})->Js.Json.array",
                runtime_value_name, inner
            ))
        }
        TypeInfo::Option { inner } => {
            let inner_encoded = generate_specialized_source(
                inner,
                "v",
                fuel,
            )?;
            Ok(format!(
                "switch {} {{ | Some(v) => {} | None => Js.Json.null }}",
                runtime_value_name, inner_encoded
            ))
        }
        TypeInfo::Variant { constructors, .. } => {
            let mut arms = Vec::new();
            for ctor in constructors {
                let arm = if ctor.args.is_empty() {
                    // No-arg constructor: | Point => { TAG: "Point" }
                    format!(
                        "  | {} => {{\n    let obj = Js.Dict.empty()\n    Js.Dict.set(obj, \"TAG\", Js.Json.string(\"{}\"))\n    Js.Json.object_(obj)\n  }}",
                        ctor.name, ctor.name
                    )
                } else {
                    // Constructor with args — encode each arg
                    let mut lines = Vec::new();
                    lines.push(format!("  | {}(payload) => {{", ctor.name));
                    lines.push("    let obj = Js.Dict.empty()".to_string());
                    lines.push(format!(
                        "    Js.Dict.set(obj, \"TAG\", Js.Json.string(\"{}\"))",
                        ctor.name
                    ));
                    for (i, arg_type) in ctor.args.iter().enumerate() {
                        let arg_name = if ctor.args.len() == 1 {
                            "payload".to_string()
                        } else {
                            format!("payload_{}", i)
                        };
                        let encoded = generate_specialized_source(
                            arg_type,
                            &arg_name,
                            fuel,
                        )?;
                        lines.push(format!(
                            "    Js.Dict.set(obj, \"_{}\", {})",
                            i, encoded
                        ));
                    }
                    lines.push("    Js.Json.object_(obj)".to_string());
                    lines.push("  }".to_string());
                    lines.join("\n")
                };
                arms.push(arm);
            }
            Ok(format!(
                "switch {} {{\n{}\n}}",
                runtime_value_name,
                arms.join("\n")
            ))
        }
        TypeInfo::Unknown { description } if description == "recursive type" => {
            // For recursive types, generate a placeholder that indicates
            // a recursive encoder call would be needed.
            // In a full implementation, this would call the encoder function
            // by name. For now, use a JSON string placeholder.
            Ok(format!("Js.Json.string(\"[recursive: {}]\")", runtime_value_name))
        }
        TypeInfo::Tuple { elements } => {
            let mut items = Vec::new();
            for (i, elem) in elements.iter().enumerate() {
                let (_, part) = match i {
                    0 => ("fst", generate_specialized_source(elem, &format!("fst({})", runtime_value_name), fuel)?),
                    1 => ("snd", generate_specialized_source(elem, &format!("snd({})", runtime_value_name), fuel)?),
                    _ => ("", generate_specialized_source(elem, &format!("/* tuple_{} */", i), fuel)?),
                };
                items.push(part);
            }
            Ok(format!("[{}]->Js.Json.array", items.join(", ")))
        }
        _ => {
            Err(format!("Cannot encode type: {:?}", type_info))
        }
    }
}

/// Generate a complete specialized function for a comptime encode call.
/// Returns ReScript source for a let binding that can be spliced into the module.
pub fn generate_encode_binding(
    func_name: &str,
    type_info: &TypeInfo,
    type_name: &str,
) -> Result<String, String> {
    let mut fuel = DEFAULT_FUEL;
    let body = generate_specialized_source(
        type_info,
        "value",
        &mut fuel,
    )?;
    Ok(format!(
        "let {}_specialized = (value: {}) => {}",
        func_name, type_name, body
    ))
}

// ── Utility functions for tests ──────────────────────────────────────────────

/// Generate keyOf source (test utility — demonstrates expected partial evaluator output).
pub fn generate_key_of_source(type_info: &TypeInfo, type_name: &str) -> Result<String, String> {
    match type_info {
        TypeInfo::Record { fields, .. } => {
            let cases: Vec<String> = fields
                .iter()
                .map(|f| {
                    let mut chars = f.name.chars();
                    let capitalized = match chars.next() {
                        Some(c) => c.to_uppercase().collect::<String>() + chars.as_str(),
                        None => String::new(),
                    };
                    format!("  | @as(\"{}\") {}", f.name, capitalized)
                })
                .collect();
            Ok(format!("type {}_key =\n{}", type_name, cases.join("\n")))
        }
        _ => Err("@keyOf requires a record type".to_string()),
    }
}

/// Generate partial source (test utility — demonstrates expected partial evaluator output).
pub fn generate_partial_source(type_info: &TypeInfo, type_name: &str) -> Result<String, String> {
    match type_info {
        TypeInfo::Record { fields, .. } => {
            let field_decls: Vec<String> = fields
                .iter()
                .map(|f| {
                    let type_str = type_info_to_rescript_type(&f.typ);
                    format!("  {}?: {}", f.name, type_str)
                })
                .collect();
            Ok(format!(
                "type {}_partial = {{\n{},\n}}",
                type_name,
                field_decls.join(",\n")
            ))
        }
        _ => Err("@partial requires a record type".to_string()),
    }
}

/// Convert a TypeInfo to a ReScript type syntax string.
pub fn type_info_to_rescript_type(info: &TypeInfo) -> String {
    match info {
        TypeInfo::Int => "int".to_string(),
        TypeInfo::Float => "float".to_string(),
        TypeInfo::String => "string".to_string(),
        TypeInfo::Bool => "bool".to_string(),
        TypeInfo::Unit => "unit".to_string(),
        TypeInfo::Char => "char".to_string(),
        TypeInfo::Bigint => "bigint".to_string(),
        TypeInfo::Array { element } => format!("array<{}>", type_info_to_rescript_type(element)),
        TypeInfo::Option { inner } => format!("option<{}>", type_info_to_rescript_type(inner)),
        TypeInfo::Tuple { elements } => {
            let parts: Vec<String> = elements.iter().map(type_info_to_rescript_type).collect();
            format!("({})", parts.join(", "))
        }
        TypeInfo::Record { name, .. } => name.clone(),
        TypeInfo::Variant { name, .. } => name.clone(),
        TypeInfo::Function { args, return_type } => {
            let arg_parts: Vec<String> = args.iter().map(type_info_to_rescript_type).collect();
            format!("({}) => {}", arg_parts.join(", "), type_info_to_rescript_type(return_type))
        }
        TypeInfo::External { name } | TypeInfo::Opaque { name } => name.clone(),
        TypeInfo::Unknown { description } => format!("/* {} */ unknown", description),
    }
}

/// Environment for comptime specialization.
pub struct SpecEnv {
    /// Comptime bindings: name → value.
    pub bindings: HashMap<String, ComptimeValue>,
    /// Fuel remaining (decremented per step to prevent infinite loops).
    pub fuel: usize,
}

impl SpecEnv {
    pub fn new(bindings: HashMap<String, ComptimeValue>) -> Self {
        Self {
            bindings,
            fuel: DEFAULT_FUEL,
        }
    }

    fn step(&mut self) -> Result<(), String> {
        if self.fuel == 0 {
            return Err("Comptime evaluation exceeded fuel limit (possible infinite loop)".to_string());
        }
        self.fuel -= 1;
        Ok(())
    }
}

/// Specialize a typed tree expression with comptime bindings.
///
/// This is the core partial evaluator. It walks the typed tree and:
/// - Substitutes comptime-known variables with their values
/// - Eliminates switch branches based on comptime match results
/// - Unrolls inline for over comptime arrays
/// - Recursively specializes comptime function calls
///
/// Returns a specialized typed tree expression, or an error.
pub fn specialize_expression(
    expr: &typedtree::Expression,
    env: &mut SpecEnv,
    ctx: &TypeContext<'_>,
    type_env: &Env,
) -> Result<typedtree::Expression, String> {
    env.step()?;

    let specialized_desc = match &expr.exp_desc {
        // Variable reference — check if it's a comptime binding
        typedtree::ExpressionDesc::Texp_ident(path, lid, vd) => {
            let name = path.name();
            if let Some(value) = env.bindings.get(&name) {
                // Substitute with comptime value as a constant
                match comptime_value_to_constant(value) {
                    Some(constant) => typedtree::ExpressionDesc::Texp_constant(constant),
                    None => {
                        // Can't convert to constant — leave as is
                        typedtree::ExpressionDesc::Texp_ident(
                            path.clone(),
                            lid.clone(),
                            vd.clone(),
                        )
                    }
                }
            } else {
                // Not a comptime binding — leave as is
                expr.exp_desc.clone()
            }
        }

        // Constant — pass through
        typedtree::ExpressionDesc::Texp_constant(_) => expr.exp_desc.clone(),

        // Let binding — specialize the value and body
        typedtree::ExpressionDesc::Texp_let(rec_flag, bindings, body) => {
            let spec_bindings: Vec<_> = bindings
                .iter()
                .map(|vb| {
                    let spec_expr = specialize_expression(&vb.vb_expr, env, ctx, type_env)?;
                    Ok(typedtree::ValueBinding {
                        vb_expr: spec_expr,
                        ..vb.clone()
                    })
                })
                .collect::<Result<_, String>>()?;
            let spec_body = specialize_expression(body, env, ctx, type_env)?;
            typedtree::ExpressionDesc::Texp_let(
                *rec_flag,
                spec_bindings,
                Box::new(spec_body),
            )
        }

        // Application — specialize function and arguments
        typedtree::ExpressionDesc::Texp_apply {
            funct,
            args,
            partial,
            transformed_jsx,
        } => {
            let spec_funct = specialize_expression(funct, env, ctx, type_env)?;
            let spec_args: Vec<_> = args
                .iter()
                .map(|arg| {
                    let spec_expression = match &arg.expression {
                        Some(e) => Some(specialize_expression(e, env, ctx, type_env)?),
                        None => None,
                    };
                    Ok(typedtree::ApplyArg {
                        label: arg.label.clone(),
                        expression: spec_expression,
                    })
                })
                .collect::<Result<_, String>>()?;
            typedtree::ExpressionDesc::Texp_apply {
                funct: Box::new(spec_funct),
                args: spec_args,
                partial: *partial,
                transformed_jsx: *transformed_jsx,
            }
        }

        // Match/switch — check if the scrutinee is comptime-known
        typedtree::ExpressionDesc::Texp_match(scrutinee, cases, exception_cases, partial) => {
            let spec_scrutinee = specialize_expression(scrutinee, env, ctx, type_env)?;

            // Try to evaluate scrutinee to a comptime value
            if let Some(cv) = try_eval_to_comptime(&spec_scrutinee, env) {
                // Try to match against case patterns
                for case in cases {
                    if let Some(new_bindings) =
                        match_case_pattern(&case.c_lhs, &cv)
                    {
                        let mut branch_env = SpecEnv {
                            bindings: env.bindings.clone(),
                            fuel: env.fuel,
                        };
                        branch_env.bindings.extend(new_bindings);
                        let result = specialize_expression(
                            &case.c_rhs,
                            &mut branch_env,
                            ctx,
                            type_env,
                        );
                        env.fuel = branch_env.fuel;
                        if let Ok(specialized) = result {
                            return Ok(specialized);
                        }
                    }
                }
                // No match found — leave as is
                typedtree::ExpressionDesc::Texp_match(
                    Box::new(spec_scrutinee),
                    cases.clone(),
                    exception_cases.clone(),
                    *partial,
                )
            } else {
                // Scrutinee not comptime — specialize each branch
                let spec_cases: Vec<_> = cases
                    .iter()
                    .map(|case| {
                        let spec_rhs = specialize_expression(&case.c_rhs, env, ctx, type_env)?;
                        Ok(typedtree::Case {
                            c_rhs: spec_rhs,
                            ..case.clone()
                        })
                    })
                    .collect::<Result<_, String>>()?;
                typedtree::ExpressionDesc::Texp_match(
                    Box::new(spec_scrutinee),
                    spec_cases,
                    exception_cases.clone(),
                    *partial,
                )
            }
        }

        // Sequence — specialize both sides
        typedtree::ExpressionDesc::Texp_sequence(e1, e2) => {
            let s1 = specialize_expression(e1, env, ctx, type_env)?;
            let s2 = specialize_expression(e2, env, ctx, type_env)?;
            typedtree::ExpressionDesc::Texp_sequence(Box::new(s1), Box::new(s2))
        }

        // If-then-else — specialize condition and branches
        typedtree::ExpressionDesc::Texp_ifthenelse(cond, then_branch, else_branch) => {
            let spec_cond = specialize_expression(cond, env, ctx, type_env)?;
            let spec_then = specialize_expression(then_branch, env, ctx, type_env)?;
            let spec_else = else_branch
                .as_ref()
                .map(|e| specialize_expression(e, env, ctx, type_env))
                .transpose()?;
            typedtree::ExpressionDesc::Texp_ifthenelse(
                Box::new(spec_cond),
                Box::new(spec_then),
                spec_else.map(Box::new),
            )
        }

        // Tuple — specialize all elements
        typedtree::ExpressionDesc::Texp_tuple(elements) => {
            let spec_elements: Vec<_> = elements
                .iter()
                .map(|e| specialize_expression(e, env, ctx, type_env))
                .collect::<Result<_, _>>()?;
            typedtree::ExpressionDesc::Texp_tuple(spec_elements)
        }

        // Record — specialize field values
        typedtree::ExpressionDesc::Texp_record { fields, extended_expression } => {
            // Clone and specialize each field expression
            let spec_fields: Vec<_> = fields
                .iter()
                .map(|(lid, desc, def, opt)| {
                    let spec_def = match def {
                        typedtree::RecordLabelDefinition::Kept(_) => def.clone(),
                        typedtree::RecordLabelDefinition::Overridden(lid2, field_expr) => {
                            match specialize_expression(field_expr, env, ctx, type_env) {
                                Ok(spec) => typedtree::RecordLabelDefinition::Overridden(
                                    lid2.clone(),
                                    spec,
                                ),
                                Err(_) => def.clone(),
                            }
                        }
                    };
                    (lid.clone(), desc.clone(), spec_def, *opt)
                })
                .collect();
            let spec_ext = extended_expression
                .as_ref()
                .map(|e| specialize_expression(e, env, ctx, type_env))
                .transpose()?;
            typedtree::ExpressionDesc::Texp_record {
                fields: spec_fields,
                extended_expression: spec_ext.map(Box::new),
            }
        }

        // Field access — pass through (with specialized base)
        typedtree::ExpressionDesc::Texp_field(base, lid, desc) => {
            let spec_base = specialize_expression(base, env, ctx, type_env)?;
            typedtree::ExpressionDesc::Texp_field(Box::new(spec_base), lid.clone(), desc.clone())
        }

        // Constructor — specialize arguments
        typedtree::ExpressionDesc::Texp_construct(lid, desc, args) => {
            let spec_args: Vec<_> = args
                .iter()
                .map(|e| specialize_expression(e, env, ctx, type_env))
                .collect::<Result<_, _>>()?;
            typedtree::ExpressionDesc::Texp_construct(lid.clone(), desc.clone(), spec_args)
        }

        // Everything else — clone as is
        _ => expr.exp_desc.clone(),
    };

    Ok(typedtree::Expression {
        exp_desc: specialized_desc,
        exp_loc: expr.exp_loc,
        exp_extra: expr.exp_extra.clone(),
        exp_type: expr.exp_type,
        exp_env: expr.exp_env.clone(),
        exp_attributes: expr.exp_attributes.clone(),
    })
}

/// Try to evaluate a typed expression to a ComptimeValue.
fn try_eval_to_comptime(
    expr: &typedtree::Expression,
    env: &SpecEnv,
) -> Option<ComptimeValue> {
    match &expr.exp_desc {
        typedtree::ExpressionDesc::Texp_constant(c) => {
            match c {
                typedtree::Constant::Int(n) => Some(ComptimeValue::Int(*n)),
                typedtree::Constant::String(s, _) => Some(ComptimeValue::String(s.clone())),
                typedtree::Constant::Float(s) => s.parse::<f64>().ok().map(ComptimeValue::Float),
                typedtree::Constant::Char(c) => Some(ComptimeValue::Int(*c as i64)),
                _ => None,
            }
        }
        typedtree::ExpressionDesc::Texp_construct(_, cstr_desc, args) if args.is_empty() => {
            // Boolean-like constructors
            let name = cstr_desc.cstr_name.clone();
            match name.as_str() {
                "true" => Some(ComptimeValue::Bool(true)),
                "false" => Some(ComptimeValue::Bool(false)),
                _ => Some(ComptimeValue::Variant(name, None)),
            }
        }
        typedtree::ExpressionDesc::Texp_ident(path, _, _) => {
            // Check comptime bindings
            env.bindings.get(&path.name()).cloned()
        }
        _ => None,
    }
}

/// Try to match a typed tree pattern against a ComptimeValue.
/// Returns variable bindings if matched.
fn match_case_pattern(
    pattern: &typedtree::Pattern,
    value: &ComptimeValue,
) -> Option<HashMap<String, ComptimeValue>> {
    match &pattern.pat_desc {
        // Wildcard matches everything
        typedtree::PatternDesc::Tpat_any => Some(HashMap::new()),

        // Variable binding
        typedtree::PatternDesc::Tpat_var(id, _) => {
            let mut bindings = HashMap::new();
            bindings.insert(id.name().to_string(), value.clone());
            Some(bindings)
        }

        // Constructor pattern — match variant name
        typedtree::PatternDesc::Tpat_construct(_, cstr_desc, args) => {
            if let ComptimeValue::Type(type_info) = value {
                // Match TypeInfo variant names (Int, Float, String, Record, etc.)
                let pattern_name = &cstr_desc.cstr_name;
                if let Some(mut bindings) = match_typeinfo_pattern(type_info, pattern_name) {
                    // Bind the constructor arguments if present
                    if args.len() == 1 {
                        // Single argument — match against the record of bindings
                        if let typedtree::PatternDesc::Tpat_record(fields, _) = &args[0].pat_desc {
                            for (_field_lid, lbl_desc, field_pat, _optional) in fields {
                                let field_name = &lbl_desc.lbl_name;
                                if let Some(field_value) = bindings.remove(field_name.as_str()) {
                                    if let typedtree::PatternDesc::Tpat_var(id, _) = &field_pat.pat_desc {
                                        bindings.insert(id.name().to_string(), field_value);
                                    }
                                }
                            }
                        }
                    }
                    Some(bindings)
                } else {
                    None
                }
            } else if let ComptimeValue::Variant(name, payload) = value {
                let pattern_name = &cstr_desc.cstr_name;
                if pattern_name == name {
                    let mut bindings = HashMap::new();
                    if let (Some(payload), Some(arg_pat)) = (payload, args.first()) {
                        if let Some(sub_bindings) = match_case_pattern(arg_pat, payload) {
                            bindings.extend(sub_bindings);
                        }
                    }
                    Some(bindings)
                } else {
                    None
                }
            } else {
                None
            }
        }

        // Record pattern — destructure comptime record
        typedtree::PatternDesc::Tpat_record(fields, _) => {
            if let ComptimeValue::Record(entries) = value {
                let mut bindings = HashMap::new();
                for (_field_lid, lbl_desc, field_pat, _optional) in fields {
                    let field_name = &lbl_desc.lbl_name;
                    if let Some((_, fv)) = entries.iter().find(|(n, _)| n == field_name) {
                        if let Some(sub_bindings) = match_case_pattern(field_pat, fv) {
                            bindings.extend(sub_bindings);
                        } else {
                            return None;
                        }
                    }
                }
                Some(bindings)
            } else {
                None
            }
        }

        // Alias pattern — match and bind
        typedtree::PatternDesc::Tpat_alias(inner, id, _) => {
            let mut bindings = match_case_pattern(inner, value)?;
            bindings.insert(id.name().to_string(), value.clone());
            Some(bindings)
        }

        // Or pattern — try left then right
        typedtree::PatternDesc::Tpat_or(left, right, _) => {
            match_case_pattern(left, value).or_else(|| match_case_pattern(right, value))
        }

        _ => None,
    }
}

/// Convert a ComptimeValue to a typed tree Constant.
fn comptime_value_to_constant(value: &ComptimeValue) -> Option<typedtree::Constant> {
    match value {
        ComptimeValue::Int(n) => Some(typedtree::Constant::Int(*n)),
        ComptimeValue::Float(f) => Some(typedtree::Constant::Float(f.to_string())),
        ComptimeValue::String(s) => Some(typedtree::Constant::String(s.clone(), None)),
        ComptimeValue::Bool(_) => None, // Booleans are constructors, not constants
        ComptimeValue::Unit => None,
        _ => None,
    }
}
