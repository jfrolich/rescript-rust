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

use std::collections::{HashMap, HashSet};

use super::context::TypeContext;
use super::ctype;
use super::decl::{ConstructorArguments, ConstructorDescription, ConstructorKind, TypeKind};
use super::env::Env;
use super::path::Path;
use super::predef;
use super::type_expr::{TypeDesc, TypeExprRef};
use super::typedtree;
use crate::ident::Ident;

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
    /// Whether this is @comptime.inline (evaluated in JS engine).
    pub is_inline: bool,
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

// ── Monomorphization Cache ────────────────────────────────────────────────

/// Cache for comptime function monomorphization.
///
/// Each unique (function_name, type_key) pair produces one specialized
/// function. Recursive types terminate because re-entering the same
/// pair during specialization emits a self-reference instead of
/// expanding again.
pub struct MonomorphCache {
    /// Completed specializations: (func_name, type_key) → generated name.
    completed: HashMap<(String, TypeInfo), String>,
    /// In-progress specializations (for recursion detection).
    in_progress: HashSet<(String, TypeInfo)>,
    /// Generated function bodies to emit as structure items.
    pub generated: Vec<GeneratedFunction>,
}

/// A monomorphized function to be emitted as a let binding.
pub struct GeneratedFunction {
    /// Generated name (e.g. "encode$user").
    pub name: String,
    /// Identifier for the let binding.
    pub ident: Ident,
    /// The specialized function body.
    pub body: typedtree::Expression,
    /// Parameter name for the runtime argument.
    pub param_name: String,
    /// Identifier for the runtime parameter (must match body's references).
    pub param_ident: Ident,
    /// Type of the runtime parameter.
    pub param_type: TypeExprRef,
    /// Return type of the function.
    pub return_type: TypeExprRef,
    /// Whether this function calls itself (needs rec).
    pub recursive: bool,
}

impl MonomorphCache {
    pub fn new() -> Self {
        Self {
            completed: HashMap::new(),
            in_progress: HashSet::new(),
            generated: Vec::new(),
        }
    }

    /// Check if a specialization is already completed.
    /// Returns the generated function name if so.
    pub fn lookup(&self, func_name: &str, type_key: &TypeInfo) -> Option<&str> {
        self.completed
            .get(&(func_name.to_string(), type_key.clone()))
            .map(|s| s.as_str())
    }

    /// Check if a specialization is currently in progress (recursion).
    pub fn is_in_progress(&self, func_name: &str, type_key: &TypeInfo) -> bool {
        self.in_progress
            .contains(&(func_name.to_string(), type_key.clone()))
    }

    /// Mark a specialization as in-progress. Returns the generated name.
    pub fn begin(&mut self, func_name: &str, type_key: &TypeInfo) -> String {
        let generated_name = make_monomorph_name(func_name, type_key);
        self.in_progress
            .insert((func_name.to_string(), type_key.clone()));
        generated_name
    }

    /// Complete a specialization: move from in-progress to completed.
    pub fn complete(
        &mut self,
        func_name: &str,
        type_key: &TypeInfo,
        generated_name: String,
        func: GeneratedFunction,
    ) {
        self.in_progress
            .remove(&(func_name.to_string(), type_key.clone()));
        self.completed
            .insert((func_name.to_string(), type_key.clone()), generated_name);
        self.generated.push(func);
    }
}

/// Generate a name for a monomorphized function.
/// e.g. "encode" + Record{name: "user", ...} → "encode$user"
pub fn make_monomorph_name(func_name: &str, type_key: &TypeInfo) -> String {
    let type_suffix = match type_key {
        TypeInfo::Int => "int".to_string(),
        TypeInfo::Float => "float".to_string(),
        TypeInfo::String => "string".to_string(),
        TypeInfo::Bool => "bool".to_string(),
        TypeInfo::Unit => "unit".to_string(),
        TypeInfo::Char => "char".to_string(),
        TypeInfo::Bigint => "bigint".to_string(),
        TypeInfo::Array { element } => {
            format!(
                "array_{}",
                make_monomorph_name("", element).trim_start_matches('$')
            )
        }
        TypeInfo::Option { inner } => {
            format!(
                "option_{}",
                make_monomorph_name("", inner).trim_start_matches('$')
            )
        }
        TypeInfo::Tuple { elements } => {
            let parts: Vec<String> = elements
                .iter()
                .map(|e| {
                    make_monomorph_name("", e)
                        .trim_start_matches('$')
                        .to_string()
                })
                .collect();
            format!("tuple_{}", parts.join("_"))
        }
        TypeInfo::Record { name, .. } => name.clone(),
        TypeInfo::Variant { name, .. } => name.clone(),
        TypeInfo::Function { .. } => "fn".to_string(),
        TypeInfo::External { name } => name.clone(),
        TypeInfo::Opaque { name } => name.clone(),
        TypeInfo::Unknown { .. } => "unknown".to_string(),
    };
    if func_name.is_empty() {
        format!("${type_suffix}")
    } else {
        format!("{func_name}${type_suffix}")
    }
}

// ── Type-builder evaluator ──────────────────────────────────────────────────

/// Result of evaluating a type-builder expression.
#[derive(Debug, Clone)]
pub enum TypeBuilderResult {
    /// A variant TypeKind with these constructors (no args).
    Variant(Vec<String>),
    /// A record TypeKind with these fields.
    Record(Vec<RecordFieldSpec>),
}

/// Description of a single variant case (from @variantCase).
#[derive(Debug, Clone)]
pub struct VariantCaseSpec {
    pub name: String,
    // Future: pub as_: Option<String>, pub payload: Option<TypeInfo>, etc.
}

/// Description of a single record field (from @recordField).
#[derive(Debug, Clone)]
pub struct RecordFieldSpec {
    pub name: String,
    pub typ: TypeInfo,
    pub optional: bool,
    pub mutable_: bool,
}

// ── TypeInfo ────────────────────────────────────────────────────────────────

/// Type structure information, produced by `@typeInfo(T)`.
///
/// This is the Rust representation. It maps to the predefined `typeInfo`
/// variant type in the ReScript type system. When `@typeInfo(T)` is
/// encountered, the compiler constructs a TypeInfo from the type context
/// and expands it to a literal value of the predefined type.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
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

/// A record field descriptor.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct FieldInfo {
    pub name: std::string::String,
    pub typ: TypeInfo,
    pub mutable: bool,
    pub optional: bool,
    pub attributes: Vec<(std::string::String, std::string::String)>,
}

/// A variant constructor descriptor.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ConstructorInfo {
    pub name: std::string::String,
    pub args: Vec<TypeInfo>,
    pub attributes: Vec<(std::string::String, std::string::String)>,
}

// ── build_type_info ─────────────────────────────────────────────────────────

/// Convert a TypeInfo back to a TypeExprRef.
/// Looks up user-defined types by name in the environment.
pub fn type_info_to_type_expr<'a>(
    ctx: &'a TypeContext,
    env: &Env,
    ti: &TypeInfo,
) -> Option<TypeExprRef> {
    match ti {
        TypeInfo::Int => Some(ctx.new_constr(predef::path_int(), vec![])),
        TypeInfo::Float => Some(ctx.new_constr(predef::path_float(), vec![])),
        TypeInfo::String => Some(ctx.new_constr(predef::path_string(), vec![])),
        TypeInfo::Bool => Some(ctx.new_constr(predef::path_bool(), vec![])),
        TypeInfo::Unit => Some(ctx.new_constr(predef::path_unit(), vec![])),
        TypeInfo::Char => Some(ctx.new_constr(predef::path_char(), vec![])),
        TypeInfo::Bigint => Some(ctx.new_constr(predef::path_bigint(), vec![])),
        TypeInfo::Array { element } => {
            let e = type_info_to_type_expr(ctx, env, element)?;
            Some(ctx.new_constr(predef::path_array(), vec![e]))
        }
        TypeInfo::Option { inner } => {
            let e = type_info_to_type_expr(ctx, env, inner)?;
            Some(ctx.new_constr(predef::path_option(), vec![e]))
        }
        TypeInfo::Record { name, .. } | TypeInfo::Variant { name, .. } => {
            match env.find_type_with_id(name) {
                Ok((id, _)) => Some(ctx.new_constr(Path::Pident(id.clone()), vec![])),
                Err(_) => None,
            }
        }
        TypeInfo::External { name } | TypeInfo::Opaque { name } => {
            match env.find_type_with_id(name) {
                Ok((id, _)) => Some(ctx.new_constr(Path::Pident(id.clone()), vec![])),
                Err(_) => None,
            }
        }
        _ => None,
    }
}

/// Build a TypeInfo from a compiler type expression.
///
/// Resolves aliases, identifies primitives, and inspects user-defined types
/// (records, variants) through their declarations in the type context.
pub fn build_type_info<'a>(
    ctx: &'a TypeContext,
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

        TypeDesc::Tarrow { args, ret } => {
            let mut args = args
                .iter()
                .map(|arg| build_type_info(ctx, env, arg.typ, visited))
                .collect::<Vec<_>>();
            let mut current_ret = *ret;
            loop {
                let ret_repr = ctx.repr(current_ret);
                let ret_desc = ctx.get_desc(ret_repr);
                match &*ret_desc {
                    TypeDesc::Tarrow {
                        args: next_args,
                        ret: next_ret,
                    } => {
                        args.extend(
                            next_args
                                .iter()
                                .map(|arg| build_type_info(ctx, env, arg.typ, visited)),
                        );
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

        TypeDesc::Tnil | TypeDesc::Tfield { .. } | TypeDesc::Tpackage { .. } => TypeInfo::Unknown {
            description: format!("{:?}", &*desc),
        },
    };

    visited.pop();
    result
}

/// Build TypeInfo from a Tconstr (type constructor application).
fn build_type_info_from_constr<'a>(
    ctx: &'a TypeContext,
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
        let is_unboxed = decl.type_representation == crate::types::TypeRepresentation::Unboxed;
        match &decl.type_kind {
            TypeKind::TypeRecord(labels, _) => {
                let fields = labels
                    .iter()
                    .map(|ld| FieldInfo {
                        name: ld.ld_id.name().to_string(),
                        typ: build_type_info(ctx, env, ld.ld_type, visited),
                        mutable: ld.ld_mutable == super::asttypes::MutableFlag::Mutable,
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
            TypeKind::TypeVariant(constrs, _) => {
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
// ── TypeInfo → Typed Tree Expression ─────────────────────────────────────────

fn type_info_constructor_description<'a>(
    ctor_name: &str,
    ctx: &'a TypeContext,
    env: &Env,
) -> Option<ConstructorDescription> {
    // `typeInfo` is a Rust-only compiler-internal predef. It is intentionally
    // not registered in the source-visible constructor table; build the same
    // description shape as compiler/ml/env.ml:1655-1680 `store_type` would
    // expose for normal variants without making these constructors visible to
    // compiler/ml/typecore.ml:990-1010 disambiguation.
    let type_info_ident = predef::ident_type_info();
    let decl = env.find_type_by_ident(&type_info_ident).ok()?;
    let TypeKind::TypeVariant(constrs, _) = &decl.type_kind else {
        return None;
    };

    let layout = decl.variant_layout_ref()?;
    for (position, cd) in constrs.iter().enumerate() {
        if cd.cd_id.name() != ctor_name {
            continue;
        }

        let (cstr_args, cstr_arity) = match &cd.cd_args {
            ConstructorArguments::CstrTuple(args) => (args.clone(), args.len() as i32),
            ConstructorArguments::CstrRecord(labels) => {
                let args: Vec<TypeExprRef> = labels.iter().map(|l| l.ld_type).collect();
                (args.clone(), args.len() as i32)
            }
        };
        let cstr_res = cd.cd_res.unwrap_or_else(|| {
            ctx.new_generic_constr(predef::path_type_info(), decl.type_params.clone())
        });
        let cstr_existentials = super::env::constructor_existentials(ctx, &cstr_args, cd.cd_res);

        return Some(ConstructorDescription {
            cstr_name: cd.cd_id.name().to_string(),
            cstr_res,
            cstr_existentials,
            cstr_args,
            cstr_arity,
            cstr_kind: ConstructorKind::Ordinary(super::variant_runtime::ConstructorReference {
                variant: layout,
                position,
            }),
            cstr_generalized: cd.cd_res.is_some(),
            cstr_private: decl.type_private,
            cstr_loc: cd.cd_loc,
            cstr_attributes: super::decl::constructor_description_attrs_for_variant(constrs, cd),
            cstr_inlined: None,
        });
    }

    None
}

/// Construct a typed tree Expression representing a `typeInfo` literal value.
/// This is called when `@typeInfo(expr)` is encountered during type checking.
pub fn type_info_to_typed_expr<'a>(
    info: &TypeInfo,
    ctx: &'a TypeContext,
    env: &Env,
    loc: crate::parse_arena::LocIdx,
) -> Option<typedtree::Expression> {
    let type_info_ty = ctx.new_constr(predef::path_type_info(), vec![]);
    let env_ref = ctx.store_typed_env(env);

    // Map TypeInfo variant to constructor name
    let ctor_name = match info {
        TypeInfo::Int => "Int",
        TypeInfo::Float => "Float",
        TypeInfo::String => "String",
        TypeInfo::Bool => "Bool",
        TypeInfo::Unit => "Unit",
        TypeInfo::Char => "Char",
        TypeInfo::Bigint => "Bigint",
        TypeInfo::Record { .. } => "Record",
        TypeInfo::Variant { .. } => "Variant",
        TypeInfo::Array { .. } => "Array",
        TypeInfo::Option { .. } => "Option",
        TypeInfo::Function { .. } => "Function",
        TypeInfo::External { .. } => "External",
        TypeInfo::Opaque { .. } => "Opaque",
        TypeInfo::Tuple { .. } => "TiUnknown", // Tuples map to TiUnknown for now
        TypeInfo::Unknown { .. } => "TiUnknown",
    };

    let cstr_desc = type_info_constructor_description(ctor_name, ctx, env)?;

    // For simple constructors (no args), just construct the value
    let lid_loc = crate::parse_arena::Located {
        txt: crate::parse_arena::LidentIdx(0), // placeholder
        loc: crate::parse_arena::LocIdx::none(),
    };

    // Build constructor arguments for constructors with payloads
    let args = match info {
        // No-arg constructors
        TypeInfo::Int
        | TypeInfo::Float
        | TypeInfo::String
        | TypeInfo::Bool
        | TypeInfo::Unit
        | TypeInfo::Char
        | TypeInfo::Bigint
        | TypeInfo::Tuple { .. }
        | TypeInfo::Unknown { .. } => {
            vec![]
        }
        // Record({name, fields, unboxed}) — construct inline record
        TypeInfo::Record {
            name,
            fields,
            unboxed,
        } => {
            // Build field info array
            let field_exprs: Vec<typedtree::Expression> = fields
                .iter()
                .map(|f| build_field_info_expr(f, ctx, env, loc))
                .collect();
            let fields_arr = typedtree::Expression::new(
                typedtree::ExpressionDesc::Texp_array(field_exprs),
                loc,
                ctx.new_constr(
                    predef::path_array(),
                    vec![ctx.new_constr(predef::path_field_info(), vec![])],
                ),
                env_ref,
                crate::parser::ast::Attributes::new(),
            );
            let name_expr = make_string_expr(name, ctx, env, loc);
            let unboxed_expr = make_bool_expr(*unboxed, ctx, env, loc);
            // Inline record: the single arg is a record expression
            // For now, wrap the fields as a tuple (the type checker will handle it)
            vec![typedtree::Expression::new(
                typedtree::ExpressionDesc::Texp_tuple(vec![name_expr, fields_arr, unboxed_expr]),
                loc,
                ctx.new_var(None),
                env_ref,
                crate::parser::ast::Attributes::new(),
            )]
        }
        TypeInfo::Array { element } => {
            let inner = type_info_to_typed_expr(element, ctx, env, loc)?;
            vec![typedtree::Expression::new(
                typedtree::ExpressionDesc::Texp_tuple(vec![inner]),
                loc,
                ctx.new_var(None),
                env_ref,
                crate::parser::ast::Attributes::new(),
            )]
        }
        TypeInfo::Option { inner } => {
            let inner_expr = type_info_to_typed_expr(inner, ctx, env, loc)?;
            vec![typedtree::Expression::new(
                typedtree::ExpressionDesc::Texp_tuple(vec![inner_expr]),
                loc,
                ctx.new_var(None),
                env_ref,
                crate::parser::ast::Attributes::new(),
            )]
        }
        _ => vec![],
    };

    Some(typedtree::Expression::new(
        typedtree::ExpressionDesc::Texp_construct(lid_loc, cstr_desc, args),
        loc,
        type_info_ty,
        env_ref,
        crate::parser::ast::Attributes::new(),
    ))
}

/// Build a typed expression for a fieldInfo record value.
fn build_field_info_expr<'a>(
    field: &FieldInfo,
    ctx: &'a TypeContext,
    env: &Env,
    loc: crate::parse_arena::LocIdx,
) -> typedtree::Expression {
    let env_ref = ctx.store_typed_env(env);
    let name_expr = make_string_expr(&field.name, ctx, env, loc);
    let typ_expr = type_info_to_typed_expr(&field.typ, ctx, env, loc)
        .unwrap_or_else(|| make_string_expr("unknown", ctx, env, loc));
    let optional_expr = make_bool_expr(field.optional, ctx, env, loc);
    let mutable_expr = make_bool_expr(field.mutable, ctx, env, loc);

    // Return as a tuple for now (proper record construction needs LabelDescription)
    typedtree::Expression::new(
        typedtree::ExpressionDesc::Texp_tuple(vec![
            name_expr,
            typ_expr,
            optional_expr,
            mutable_expr,
        ]),
        loc,
        ctx.new_constr(predef::path_field_info(), vec![]),
        env_ref,
        crate::parser::ast::Attributes::new(),
    )
}

/// Make a typed string constant expression.
pub fn make_string_expr<'a>(
    s: &str,
    ctx: &'a TypeContext,
    env: &Env,
    loc: crate::parse_arena::LocIdx,
) -> typedtree::Expression {
    typedtree::Expression::new(
        typedtree::ExpressionDesc::Texp_constant(typedtree::Constant::String(s.to_string(), None)),
        loc,
        ctx.new_constr(predef::path_string(), vec![]),
        ctx.store_typed_env(env),
        crate::parser::ast::Attributes::new(),
    )
}

/// Make a typed boolean expression.
pub fn make_bool_expr<'a>(
    b: bool,
    ctx: &'a TypeContext,
    env: &Env,
    loc: crate::parse_arena::LocIdx,
) -> typedtree::Expression {
    let bool_ty = ctx.new_constr(predef::path_bool(), vec![]);
    let env_ref = ctx.store_typed_env(env);
    let ctor_name = if b { "true" } else { "false" };
    let cstr_desc = match env.find_constructor(ctor_name) {
        Ok(desc) => desc.clone(),
        Err(_) => {
            return typedtree::Expression::new(
                typedtree::ExpressionDesc::Texp_constant(typedtree::Constant::Int(if b {
                    1
                } else {
                    0
                })),
                loc,
                bool_ty,
                env_ref,
                crate::parser::ast::Attributes::new(),
            );
        }
    };
    let lid_loc = crate::parse_arena::Located {
        txt: crate::parse_arena::LidentIdx(0),
        loc: crate::parse_arena::LocIdx::none(),
    };
    typedtree::Expression::new(
        typedtree::ExpressionDesc::Texp_construct(lid_loc, cstr_desc, vec![]),
        loc,
        bool_ty,
        env_ref,
        crate::parser::ast::Attributes::new(),
    )
}

// ── ComptimeValue ───────────────────────────────────────────────────────────

/// A value known at compile time.
#[derive(Debug, Clone)]
pub enum ComptimeValue {
    /// A typed expression to substitute (for @comptime parameter inlining).
    TypedExpr(typedtree::Expression),
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
            bindings.insert("element".to_string(), ComptimeValue::Type(*element.clone()));
            Some(bindings)
        }
        ("Option", TypeInfo::Option { inner }) => {
            bindings.insert("inner".to_string(), ComptimeValue::Type(*inner.clone()));
            Some(bindings)
        }
        (
            "Record",
            TypeInfo::Record {
                name,
                fields,
                unboxed,
            },
        ) => {
            let field_values: Vec<ComptimeValue> = fields
                .iter()
                .map(|f| {
                    ComptimeValue::Record(vec![
                        ("name".to_string(), ComptimeValue::String(f.name.clone())),
                        ("typ".to_string(), ComptimeValue::Type(f.typ.clone())),
                        ("mutable".to_string(), ComptimeValue::Bool(f.mutable)),
                        ("optional".to_string(), ComptimeValue::Bool(f.optional)),
                    ])
                })
                .collect();
            bindings.insert("fields".to_string(), ComptimeValue::Array(field_values));
            bindings.insert("name".to_string(), ComptimeValue::String(name.clone()));
            bindings.insert("unboxed".to_string(), ComptimeValue::Bool(*unboxed));
            Some(bindings)
        }
        (
            "Variant",
            TypeInfo::Variant {
                name,
                constructors,
                unboxed,
            },
        ) => {
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
            return Err(
                "Comptime evaluation exceeded fuel limit (possible infinite loop)".to_string(),
            );
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
    ctx: &TypeContext,
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
                        typedtree::ExpressionDesc::Texp_ident(path.clone(), lid.clone(), vd.clone())
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
            typedtree::ExpressionDesc::Texp_let(*rec_flag, spec_bindings, Box::new(spec_body))
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
                    if let Some(new_bindings) = match_case_pattern(&case.c_lhs, &cv) {
                        let mut branch_env = SpecEnv {
                            bindings: env.bindings.clone(),
                            fuel: env.fuel,
                        };
                        branch_env.bindings.extend(new_bindings);
                        let result =
                            specialize_expression(&case.c_rhs, &mut branch_env, ctx, type_env);
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
        typedtree::ExpressionDesc::Texp_record {
            fields,
            extended_expression,
        } => {
            // Clone and specialize each field expression
            let spec_fields: Vec<_> = fields
                .iter()
                .map(|(lid, desc, def, opt)| {
                    let spec_def = match def {
                        typedtree::RecordLabelDefinition::Kept(_) => def.clone(),
                        typedtree::RecordLabelDefinition::OmittedOptionalNone(_, _) => def.clone(),
                        typedtree::RecordLabelDefinition::Overridden(lid2, field_expr) => {
                            match specialize_expression(field_expr, env, ctx, type_env) {
                                Ok(spec) => {
                                    typedtree::RecordLabelDefinition::Overridden(lid2.clone(), spec)
                                }
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
        typedtree::ExpressionDesc::Texp_record_sparse {
            fields,
            all_labels,
            omitted_loc,
            extended_expression,
        } => {
            // Intentional Rust performance representation: preserve the sparse
            // record wrapper while specializing only explicit field
            // expressions. Later typedtree/lambda boundaries expand the
            // carried `all_labels` table to the full field list from OCaml
            // compiler/ml/typecore.ml:2833-2842.
            let spec_fields: Vec<_> = fields
                .iter()
                .map(|(lid, desc, def, opt)| {
                    let spec_def = match def {
                        typedtree::RecordLabelDefinition::Kept(_)
                        | typedtree::RecordLabelDefinition::OmittedOptionalNone(_, _) => {
                            def.clone()
                        }
                        typedtree::RecordLabelDefinition::Overridden(lid2, field_expr) => {
                            match specialize_expression(field_expr, env, ctx, type_env) {
                                Ok(spec) => {
                                    typedtree::RecordLabelDefinition::Overridden(lid2.clone(), spec)
                                }
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
            typedtree::ExpressionDesc::Texp_record_sparse {
                fields: spec_fields,
                all_labels: all_labels.clone(),
                omitted_loc: *omitted_loc,
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
fn try_eval_to_comptime(expr: &typedtree::Expression, env: &SpecEnv) -> Option<ComptimeValue> {
    match &expr.exp_desc {
        typedtree::ExpressionDesc::Texp_constant(c) => match c {
            typedtree::Constant::Int(n) => Some(ComptimeValue::Int(*n)),
            typedtree::Constant::String(s, _) => Some(ComptimeValue::String(s.clone())),
            typedtree::Constant::Float(s) => s.parse::<f64>().ok().map(ComptimeValue::Float),
            typedtree::Constant::Char(c) => Some(ComptimeValue::Int(*c as i64)),
            _ => None,
        },
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
                        if let typedtree::PatternDesc::Tpat_record(fields, _, _) = &args[0].pat_desc
                        {
                            for (_field_lid, lbl_desc, field_pat, _optional) in fields {
                                let field_name = &lbl_desc.lbl_name;
                                if let Some(field_value) = bindings.remove(field_name.as_str()) {
                                    if let typedtree::PatternDesc::Tpat_var(id, _) =
                                        &field_pat.pat_desc
                                    {
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
        typedtree::PatternDesc::Tpat_record(fields, _, _) => {
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
