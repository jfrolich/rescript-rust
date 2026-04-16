//! Compile-time metaprogramming infrastructure.
//!
//! The comptime system works by expanding `@typeInfo(T)` into a literal
//! value of the predefined `typeInfo` type. The compiler's existing
//! optimizer handles switch elimination, constant folding, and dead
//! branch removal — no special partial evaluator needed.
//!
//! This module provides:
//! - TypeInfo/FieldInfo/ConstructorInfo: Rust representations of type structure
//! - build_type_info: constructs TypeInfo from the compiler's type context
//! - ComptimeFunction: registration of @comptime functions

use super::context::TypeContext;
use super::ctype;
use super::decl::{ConstructorArguments, TypeKind};
use super::env::Env;
use super::path::Path;
use super::predef;
use super::type_expr::{TypeDesc, TypeExprRef};

// ── Comptime Function Registration ─────────────────────────────────────────

/// A registered @comptime function.
///
/// The function body is stored as a parse tree index. At call sites,
/// the compiler inlines the body with @typeInfo(T) expanded to a
/// literal value. The optimizer handles the rest.
#[derive(Debug, Clone)]
pub struct ComptimeFunction {
    /// Parse tree expression index of the function body.
    pub body_expr_idx: crate::parse_arena::ExprIdx,
    /// Parameter names and which are comptime.
    pub params: Vec<ComptimeParam>,
    /// Function name (for error messages).
    pub name: String,
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

/// Default fuel for comptime evaluation (prevents infinite recursion).
pub const DEFAULT_FUEL: usize = 100_000;

// ── TypeInfo ────────────────────────────────────────────────────────────────

/// Type structure information, produced by `@typeInfo(T)`.
///
/// This is the Rust representation. It maps to the predefined `typeInfo`
/// variant type in the ReScript type system. When `@typeInfo(T)` is
/// encountered, the compiler constructs a TypeInfo from the type context
/// and expands it to a literal value of the predefined type.
#[derive(Debug, Clone, PartialEq)]
pub enum TypeInfo {
    Int,
    Float,
    String,
    Bool,
    Unit,
    Char,
    Bigint,
    Array { element: Box<TypeInfo> },
    Option { inner: Box<TypeInfo> },
    Tuple { elements: Vec<TypeInfo> },
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
    External { name: std::string::String },
    Opaque { name: std::string::String },
    Unknown { description: std::string::String },
}

/// A record field descriptor.
#[derive(Debug, Clone, PartialEq)]
pub struct FieldInfo {
    pub name: std::string::String,
    pub typ: TypeInfo,
    pub mutable: bool,
    pub optional: bool,
    pub attributes: Vec<(std::string::String, std::string::String)>,
}

/// A variant constructor descriptor.
#[derive(Debug, Clone, PartialEq)]
pub struct ConstructorInfo {
    pub name: std::string::String,
    pub args: Vec<TypeInfo>,
    pub attributes: Vec<(std::string::String, std::string::String)>,
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
        TypeDesc::Tconstr { path, args, .. } => {
            build_type_info_from_constr(ctx, env, path, args, visited)
        }

        TypeDesc::Ttuple(elements) => TypeInfo::Tuple {
            elements: elements
                .iter()
                .map(|t| build_type_info(ctx, env, *t, visited))
                .collect(),
        },

        TypeDesc::Tarrow { arg, ret, .. } => {
            let mut args = vec![build_type_info(ctx, env, arg.typ, visited)];
            let mut current_ret = *ret;
            loop {
                let ret_repr = ctx.repr(current_ret);
                let ret_desc = ctx.get_desc(ret_repr);
                match &*ret_desc {
                    TypeDesc::Tarrow {
                        arg: next_arg,
                        ret: next_ret,
                        ..
                    } => {
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
                    .map(|ld| FieldInfo {
                        name: ld.ld_id.name().to_string(),
                        typ: build_type_info(ctx, env, ld.ld_type, visited),
                        mutable: ld.ld_mutable
                            == super::asttypes::MutableFlag::Mutable,
                        optional: ld.ld_optional,
                        attributes: vec![],
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
                        ConstructorInfo {
                            name: cd.cd_id.name().to_string(),
                            args,
                            attributes: vec![],
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
                if let Some(manifest) = decl.type_manifest {
                    build_type_info(ctx, env, manifest, visited)
                } else {
                    TypeInfo::Opaque { name: type_name }
                }
            }
            TypeKind::TypeOpen => TypeInfo::Unknown {
                description: format!("open type {}", type_name),
            },
        }
    } else {
        TypeInfo::External { name: type_name }
    }
}
