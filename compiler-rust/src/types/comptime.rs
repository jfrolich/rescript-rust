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
