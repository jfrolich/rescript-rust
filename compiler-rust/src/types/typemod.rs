//! Module type checking for ReScript.
//!
//! This module handles type checking of:
//! - Module expressions (`ModuleExpr`)
//! - Structures (module bodies)
//! - Signatures (module types)
//! - Functor application and coercion

#![allow(unused_variables)]
#![allow(dead_code)]

use crate::ident::Ident;
use crate::intern::StrIdx;
use crate::location::Location;
use crate::parse_arena::{LocIdx, Located, ParseArena};
use crate::parser::ast::RecFlag;
use crate::parser::ast::{
    ModuleExpr as ParsedModuleExpr, ModuleExprDesc as ParsedModuleExprDesc,
    StructureItem as ParsedStructureItem, StructureItemDesc as ParsedStructureItemDesc,
};
use crate::parser::longident::Longident;
use crate::types::Path;
use crate::types::env::Env;
use crate::types::type_expr::TypeExprRef;
use crate::types::typecore::{TypeCheckContext, TypeCoreError, type_binding, type_expression, transl_type};
use crate::types::typedtree::{
    EnvRef, Expression, IncludeDeclaration, ModuleBinding, ModuleCoercion, ModuleExpr,
    ModuleExprDesc, ModuleType, ModuleTypeDeclaration, OpenDeclaration, Structure,
    StructureItem, StructureItemDesc, TypeExtension, ValueBinding,
    TypedTypeDeclaration, TypedTypeKind, TypedConstructorDeclaration, TypedConstructorArguments,
    TypedLabelDeclaration, TypedCoreType, TypedCoreTypeDesc,
};
use crate::types::Variance as TypesVariance;
use crate::parser::ast::Variance as ParserVariance;
use std::collections::HashSet;

// ============================================================================
// Helper Functions for Path Conversion
// ============================================================================

/// Convert a Longident to a Path.
fn path_from_longident<'a>(lid: &Longident, get_str: impl Fn(StrIdx) -> &'a str + Copy) -> Path {
    match lid {
        Longident::Lident(name) => Path::pident(Ident::create_local(get_str(*name))),
        Longident::Ldot(prefix, name) => {
            let prefix_path = path_from_longident(prefix, get_str);
            Path::pdot(prefix_path, get_str(*name))
        }
        Longident::Lapply(functor, arg) => {
            let functor_path = path_from_longident(functor, get_str);
            let arg_path = path_from_longident(arg, get_str);
            Path::papply(functor_path, arg_path)
        }
    }
}

// ============================================================================
// Module Type Checking Results
// ============================================================================

/// Result type for module type checking operations.
pub type TypeModResult<T> = Result<T, TypeModError>;

/// Errors that can occur during module type checking.
#[derive(Debug, Clone)]
pub enum TypeModError {
    /// Core type checking error.
    CoreError(TypeCoreError),
    /// Module not found.
    ModuleNotFound(String),
    /// Signature mismatch.
    SignatureMismatch { expected: String, found: String },
    /// Functor application error.
    FunctorApplicationError(String),
    /// Invalid module expression.
    InvalidModuleExpr(Location),
}

impl From<TypeCoreError> for TypeModError {
    fn from(err: TypeCoreError) -> Self {
        TypeModError::CoreError(err)
    }
}

// ============================================================================
// Signature Simplification
// ============================================================================

/// Check if a structure has duplicate value names (like OCaml's simplify_signature).
/// Returns true if there are duplicates, meaning the structure should be wrapped
/// in Tmod_constraint with Tmodtype_implicit.
fn structure_has_duplicate_value_names(structure: &Structure) -> bool {
    let mut seen = HashSet::new();
    for item in structure.str_items.iter().rev() {
        match &item.str_desc {
            StructureItemDesc::Tstr_value(_, bindings) => {
                for vb in bindings {
                    if let crate::types::typedtree::PatternDesc::Tpat_var(id, _) = &vb.vb_pat.pat_desc {
                        if !seen.insert(id.name().to_string()) {
                            return true;
                        }
                    }
                }
            }
            StructureItemDesc::Tstr_primitive(vd) => {
                if !seen.insert(vd.val_name.txt.clone()) {
                    return true;
                }
            }
            _ => {}
        }
    }
    false
}

// ============================================================================
// Module Expression Type Checking
// ============================================================================

/// Type check a module expression.
pub fn type_module_expr<'a>(
    tctx: &mut TypeCheckContext<'a>,
    env: &Env,
    arena: &'a ParseArena,
    mod_expr: &ParsedModuleExpr,
) -> TypeModResult<ModuleExpr> {
    let loc = mod_expr.pmod_loc;

    match &mod_expr.pmod_desc {
        ParsedModuleExprDesc::Pmod_ident(lid) => {
            // Module identifier: M
            // Look up the module path in the environment
            let path = path_from_longident(tctx.resolve_lid(lid.txt), |idx| arena.get_string(idx));

            Ok(ModuleExpr {
                mod_desc: ModuleExprDesc::Tmod_ident(path, lid.clone()),
                mod_loc: loc,
                mod_type: ModuleType::placeholder(),
                mod_env: EnvRef(0),
                mod_attributes: mod_expr.pmod_attributes.clone(),
            })
        }

        ParsedModuleExprDesc::Pmod_structure(items) => {
            // Module structure: { ... }
            let (structure, new_env) = type_structure(tctx, env, arena, items)?;

            // Like OCaml: if simplify_signature would shrink the signature
            // (duplicate value names), wrap in Tmod_constraint implicit
            let needs_constraint = structure_has_duplicate_value_names(&structure);

            let md = ModuleExpr {
                mod_desc: ModuleExprDesc::Tmod_structure(structure),
                mod_loc: loc,
                mod_type: ModuleType::placeholder(),
                mod_env: EnvRef(0),
                mod_attributes: vec![],
            };

            if needs_constraint {
                Ok(ModuleExpr {
                    mod_desc: ModuleExprDesc::Tmod_constraint(
                        Box::new(md),
                        ModuleType::placeholder(),
                        crate::types::typedtree::ModuleTypeConstraint::Tmodtype_implicit,
                        ModuleCoercion::Tcoerce_none,
                    ),
                    mod_loc: loc,
                    mod_type: ModuleType::placeholder(),
                    mod_env: EnvRef(0),
                    mod_attributes: mod_expr.pmod_attributes.clone(),
                })
            } else {
                Ok(ModuleExpr {
                    mod_desc: md.mod_desc,
                    mod_loc: loc,
                    mod_type: ModuleType::placeholder(),
                    mod_env: EnvRef(0),
                    mod_attributes: mod_expr.pmod_attributes.clone(),
                })
            }
        }

        ParsedModuleExprDesc::Pmod_functor(name, param_type, body) => {
            // Functor: (X: S) => ME
            let param_id = Ident::create_local(arena.get_string(name.txt));

            // Type check the functor body
            // In a full implementation, we would extend the environment with the parameter
            let typed_body = type_module_expr(tctx, env, arena, body)?;

            // Translate parameter type if present
            let typed_param_type = match param_type {
                Some(pt) => Some(Box::new(transl_modtype(tctx, env, arena, pt)?)),
                None => None,
            };

            Ok(ModuleExpr {
                mod_desc: ModuleExprDesc::Tmod_functor(
                    param_id,
                    Located { txt: arena.get_string(name.txt).to_string(), loc: name.loc },
                    typed_param_type,
                    Box::new(typed_body),
                ),
                mod_loc: loc,
                mod_type: ModuleType::placeholder(),
                mod_env: EnvRef(0),
                mod_attributes: mod_expr.pmod_attributes.clone(),
            })
        }

        ParsedModuleExprDesc::Pmod_apply(functor, arg) => {
            // Functor application: F(M)
            let typed_functor = type_module_expr(tctx, env, arena, functor)?;
            let typed_arg = type_module_expr(tctx, env, arena, arg)?;

            Ok(ModuleExpr {
                mod_desc: ModuleExprDesc::Tmod_apply(
                    Box::new(typed_functor),
                    Box::new(typed_arg),
                    ModuleCoercion::Tcoerce_none,
                ),
                mod_loc: loc,
                mod_type: ModuleType::placeholder(),
                mod_env: EnvRef(0),
                mod_attributes: mod_expr.pmod_attributes.clone(),
            })
        }

        ParsedModuleExprDesc::Pmod_constraint(mod_expr_inner, mod_type) => {
            // Constrained module: (ME: MT)
            let typed_mod = type_module_expr(tctx, env, arena, mod_expr_inner)?;
            let typed_mty = transl_modtype(tctx, env, arena, mod_type)?;

            Ok(ModuleExpr {
                mod_desc: ModuleExprDesc::Tmod_constraint(
                    Box::new(typed_mod),
                    ModuleType::placeholder(),
                    crate::types::typedtree::ModuleTypeConstraint::Tmodtype_explicit(Box::new(typed_mty)),
                    ModuleCoercion::Tcoerce_none,
                ),
                mod_loc: loc,
                mod_type: ModuleType::placeholder(),
                mod_env: EnvRef(0),
                mod_attributes: mod_expr.pmod_attributes.clone(),
            })
        }

        ParsedModuleExprDesc::Pmod_unpack(expr) => {
            // Unpack: unpack(E)
            let typed_expr = type_expression(tctx.type_ctx, arena, env, expr)?;

            Ok(ModuleExpr {
                mod_desc: ModuleExprDesc::Tmod_unpack(typed_expr, ModuleType::placeholder()),
                mod_loc: loc,
                mod_type: ModuleType::placeholder(),
                mod_env: EnvRef(0),
                mod_attributes: mod_expr.pmod_attributes.clone(),
            })
        }

        ParsedModuleExprDesc::Pmod_extension(_ext) => {
            // Extension: [%id]
            // Extensions are typically handled by preprocessors
            let placeholder_lid = arena.placeholder_located(loc);
            Ok(ModuleExpr {
                mod_desc: ModuleExprDesc::Tmod_ident(
                    Path::pident(Ident::create_local("extension")),
                    placeholder_lid,
                ),
                mod_loc: loc,
                mod_type: ModuleType::placeholder(),
                mod_env: EnvRef(0),
                mod_attributes: mod_expr.pmod_attributes.clone(),
            })
        }
    }
}

// ============================================================================
// Module Type Translation
// ============================================================================

/// Translate a parsed module type to a typed module type.
/// This creates the structural tree needed for sexp output.
fn transl_modtype<'a>(
    tctx: &mut TypeCheckContext<'a>,
    env: &Env,
    arena: &'a ParseArena,
    smty: &crate::parser::ast::ModuleType,
) -> TypeModResult<crate::types::typedtree::ModuleType> {
    use crate::parser::ast::ModuleTypeDesc as PMtyDesc;
    use crate::types::typedtree::{ModuleType as TMty, ModuleTypeDesc as TMtyDesc};

    let loc = smty.pmty_loc;
    let attrs = smty.pmty_attributes.clone();

    let desc = match &smty.pmty_desc {
        PMtyDesc::Pmty_ident(lid) => {
            let longident = tctx.resolve_lid(lid.txt);
            let path = path_from_longident(longident, |idx| arena.get_string(idx));
            TMtyDesc::Tmty_ident(path, lid.clone())
        }
        PMtyDesc::Pmty_signature(sig_items) => {
            let typed_sig = transl_signature(tctx, env, arena, sig_items)?;
            TMtyDesc::Tmty_signature(typed_sig)
        }
        PMtyDesc::Pmty_functor(name, param_type, result_type) => {
            let param_id = Ident::create_local(arena.get_string(name.txt));
            let typed_param = match param_type {
                Some(pt) => Some(Box::new(transl_modtype(tctx, env, arena, pt)?)),
                None => None,
            };
            let typed_result = transl_modtype(tctx, env, arena, result_type)?;
            TMtyDesc::Tmty_functor(
                param_id,
                Located { txt: arena.get_string(name.txt).to_string(), loc: name.loc },
                typed_param,
                Box::new(typed_result),
            )
        }
        PMtyDesc::Pmty_with(body, _constraints) => {
            let typed_body = transl_modtype(tctx, env, arena, body)?;
            // TODO: translate with constraints
            TMtyDesc::Tmty_with(Box::new(typed_body), vec![])
        }
        PMtyDesc::Pmty_typeof(me) => {
            let typed_me = type_module_expr(tctx, env, arena, me)?;
            TMtyDesc::Tmty_typeof(Box::new(typed_me))
        }
        PMtyDesc::Pmty_alias(lid) => {
            let longident = tctx.resolve_lid(lid.txt);
            let path = path_from_longident(longident, |idx| arena.get_string(idx));
            TMtyDesc::Tmty_alias(path, lid.clone())
        }
        PMtyDesc::Pmty_extension(_) => {
            TMtyDesc::Tmty_placeholder
        }
    };

    Ok(TMty {
        mty_desc: desc,
        mty_loc: loc,
        mty_attributes: attrs,
    })
}

/// Translate a parsed signature into a typed signature.
pub fn transl_signature<'a>(
    tctx: &mut TypeCheckContext<'a>,
    env: &Env,
    arena: &'a ParseArena,
    items: &[crate::parser::ast::SignatureItem],
) -> TypeModResult<crate::types::typedtree::TypedSignature> {
    use crate::parser::ast::SignatureItemDesc as PSigDesc;
    use crate::types::typedtree::{
        TypedSignatureItem, TypedSignatureItemDesc as TSigDesc,
        TypedModuleDeclaration, EnvRef,
    };

    let mut typed_items = Vec::new();

    for item in items {
        let loc = item.psig_loc;
        let desc = match &item.psig_desc {
            PSigDesc::Psig_value(vd) => {
                let name_str = arena.get_string(vd.pval_name.txt).to_string();
                let id = Ident::create_local(&name_str);
                // Use transl_type_scheme pattern: begin_def/end_def/generalize
                let ctx = tctx.type_ctx;
                ctx.begin_def();
                let (typed_ctype, val_ty) = transl_type(tctx, env, &vd.pval_type)?;
                ctx.end_def();
                crate::types::ctype::generalize(ctx, val_ty);
                let encoded = crate::binary_ast::ppx::encode_external(vd, arena);
                TSigDesc::Tsig_value(crate::types::typedtree::TypedValueDescription {
                    val_id: id,
                    val_name: Located { txt: name_str, loc: vd.pval_name.loc },
                    val_desc: typed_ctype,
                    val_prim: encoded.pval_prim,
                    val_loc: loc,
                    val_attributes: encoded.pval_attributes,
                })
            }
            PSigDesc::Psig_type(rec_flag, decls) => {
                let typed_decls = transl_sig_type_declarations(tctx, env, arena, decls)?;
                TSigDesc::Tsig_type(*rec_flag, typed_decls)
            }
            PSigDesc::Psig_module(md) => {
                let name_str = arena.get_string(md.pmd_name.txt).to_string();
                let id = Ident::create_local(&name_str);
                let typed_mty = transl_modtype(tctx, env, arena, &md.pmd_type)?;
                TSigDesc::Tsig_module(TypedModuleDeclaration {
                    md_id: id,
                    md_name: Located { txt: name_str, loc: md.pmd_name.loc },
                    md_type: typed_mty,
                    md_attributes: md.pmd_attributes.clone(),
                    md_loc: md.pmd_loc,
                })
            }
            PSigDesc::Psig_modtype(mtd) => {
                let name_str = arena.get_string(mtd.pmtd_name.txt).to_string();
                let id = Ident::create_local(&name_str);
                let typed_mty = match &mtd.pmtd_type {
                    Some(mt) => Some(transl_modtype(tctx, env, arena, mt)?),
                    None => None,
                };
                TSigDesc::Tsig_modtype(crate::types::typedtree::ModuleTypeDeclaration {
                    mtd_id: id,
                    mtd_name: Located { txt: name_str, loc: mtd.pmtd_name.loc },
                    mtd_type: typed_mty,
                    mtd_attributes: mtd.pmtd_attributes.clone(),
                    mtd_loc: mtd.pmtd_loc,
                })
            }
            PSigDesc::Psig_open(od) => {
                let longident = tctx.resolve_lid(od.popen_lid.txt);
                let path = path_from_longident(longident, |idx| arena.get_string(idx));
                TSigDesc::Tsig_open(crate::types::typedtree::OpenDeclaration {
                    open_path: path,
                    open_txt: od.popen_lid.clone(),
                    open_override: od.popen_override,
                    open_attributes: od.popen_attributes.clone(),
                    open_loc: od.popen_loc,
                })
            }
            PSigDesc::Psig_attribute(attr) => {
                TSigDesc::Tsig_attribute(attr.clone())
            }
            // For unsupported signature items, use Tsig_attribute as placeholder
            _ => {
                TSigDesc::Tsig_attribute((
                    Located { txt: crate::intern::StrIdx(0), loc: LocIdx(0) },
                    crate::parser::ast::Payload::PStr(vec![]),
                ))
            }
        };

        typed_items.push(TypedSignatureItem {
            sig_desc: desc,
            sig_env: EnvRef(0),
            sig_loc: loc,
        });
    }

    Ok(crate::types::typedtree::TypedSignature {
        sig_items: typed_items,
    })
}

// ============================================================================
// Config Processing
// ============================================================================

/// Check if a structure starts with @@config(no_export) or @@config({no_export: ...}).
/// Returns true if the no_export config is detected.
fn has_no_export_config(arena: &ParseArena, items: &[ParsedStructureItem]) -> bool {
    use crate::parser::ast::{ExpressionDesc, Payload};

    for item in items {
        match &item.pstr_desc {
            ParsedStructureItemDesc::Pstr_attribute((name, payload)) => {
                let attr_name = arena.get_string(name.txt);
                if attr_name == "config" {
                    // Check if payload contains no_export
                    if let Payload::PStr(str_items) = payload {
                        for si in str_items {
                            match &si.pstr_desc {
                                ParsedStructureItemDesc::Pstr_eval(expr, _) => {
                                    match &expr.pexp_desc {
                                        // @@config(no_export)
                                        ExpressionDesc::Pexp_ident(lid) => {
                                            let longident = arena.get_longident(lid.txt);
                                            let lid_name = arena.get_string(longident.last_idx());
                                            if lid_name == "no_export" {
                                                return true;
                                            }
                                        }
                                        // @@config({no_export: ...})
                                        ExpressionDesc::Pexp_record(fields, _) => {
                                            for field in fields {
                                                let longident = arena.get_longident(field.lid.txt);
                                                let field_name = arena.get_string(longident.last_idx());
                                                if field_name == "no_export" {
                                                    return true;
                                                }
                                            }
                                        }
                                        _ => {}
                                    }
                                }
                                _ => {}
                            }
                        }
                    }
                }
                // Continue checking (@@config might not be the first attribute)
            }
            _ => break, // Stop at first non-attribute item
        }
    }
    false
}

// ============================================================================
// Structure Type Checking
// ============================================================================

/// Type check a structure (module body).
pub fn type_structure<'a>(
    tctx: &mut TypeCheckContext<'a>,
    env: &Env,
    arena: &'a ParseArena,
    items: &[ParsedStructureItem],
) -> TypeModResult<(Structure, Env)> {
    // Check for @@config(no_export) and apply the no_export transformation
    // like OCaml's js_implementation.ml no_export function.
    if has_no_export_config(arena, items) && !items.is_empty() {
        return type_structure_no_export(tctx, env, arena, items);
    }

    let mut typed_items = Vec::new();
    let mut current_env = env.clone();

    for item in items {
        let (typed_item, new_env) = type_structure_item(tctx, &current_env, arena, item)?;
        typed_items.push(typed_item);
        current_env = new_env;
    }

    let structure = Structure {
        str_items: typed_items,
        str_type: vec![], // Signature would be computed here
        str_final_env: EnvRef(0),
    };

    Ok((structure, current_env))
}

/// Apply no_export wrapping: wraps entire structure in
/// Tstr_include(Tmod_constraint(Tmod_structure(items), explicit(Tmty_signature([]))))
fn type_structure_no_export<'a>(
    tctx: &mut TypeCheckContext<'a>,
    env: &Env,
    arena: &'a ParseArena,
    items: &[ParsedStructureItem],
) -> TypeModResult<(Structure, Env)> {
    let loc = items[0].pstr_loc;

    // Type check all items normally first
    let mut typed_items = Vec::new();
    let mut current_env = env.clone();

    for item in items {
        let (typed_item, new_env) = type_structure_item(tctx, &current_env, arena, item)?;
        typed_items.push(typed_item);
        current_env = new_env;
    }

    let inner_structure = Structure {
        str_items: typed_items,
        str_type: vec![],
        str_final_env: EnvRef(0),
    };

    // Build: Tmod_structure(inner_structure)
    let mod_structure = ModuleExpr {
        mod_desc: ModuleExprDesc::Tmod_structure(inner_structure),
        mod_loc: loc,
        mod_type: ModuleType::placeholder(),
        mod_env: EnvRef(0),
        mod_attributes: vec![],
    };

    // Build: Tmod_constraint(Tmod_structure(...), explicit(Tmty_signature([])))
    let empty_sig = crate::types::typedtree::ModuleType {
        mty_desc: crate::types::typedtree::ModuleTypeDesc::Tmty_signature(
            crate::types::typedtree::TypedSignature { sig_items: vec![] }
        ),
        mty_loc: loc,
        mty_attributes: vec![],
    };
    let mod_constraint = ModuleExpr {
        mod_desc: ModuleExprDesc::Tmod_constraint(
            Box::new(mod_structure),
            ModuleType::placeholder(),
            crate::types::typedtree::ModuleTypeConstraint::Tmodtype_explicit(Box::new(empty_sig)),
            ModuleCoercion::Tcoerce_none,
        ),
        mod_loc: loc,
        mod_type: ModuleType::placeholder(),
        mod_env: EnvRef(0),
        mod_attributes: vec![],
    };

    // Build: Tstr_include(include_declaration(...))
    let include_item = StructureItem {
        str_desc: StructureItemDesc::Tstr_include(IncludeDeclaration {
            incl_mod: mod_constraint,
            incl_type: vec![],
            incl_attributes: vec![],
            incl_loc: loc,
        }),
        str_loc: loc,
        str_env: EnvRef(0),
    };

    let structure = Structure {
        str_items: vec![include_item],
        str_type: vec![],
        str_final_env: EnvRef(0),
    };

    Ok((structure, current_env))
}

/// Type check a structure item.
fn type_structure_item<'a>(
    tctx: &mut TypeCheckContext<'a>,
    env: &Env,
    arena: &'a ParseArena,
    item: &ParsedStructureItem,
) -> TypeModResult<(StructureItem, Env)> {
    let loc = item.pstr_loc;

    match &item.pstr_desc {
        ParsedStructureItemDesc::Pstr_eval(expr, attrs) => {
            // Evaluated expression: E
            let typed_expr = type_expression(tctx.type_ctx, arena, env, expr)?;

            let desc = StructureItemDesc::Tstr_eval(typed_expr, attrs.clone());
            Ok((
                StructureItem {
                    str_desc: desc,
                    str_loc: loc,
                    str_env: EnvRef(0),
                },
                env.clone(),
            ))
        }

        ParsedStructureItemDesc::Pstr_value(rec_flag, bindings) => {
            // Value binding: let P = E
            let typed_bindings = type_value_bindings(tctx, env, arena, *rec_flag, bindings)?;

            // Extend environment with new bindings
            let new_env = extend_env_with_bindings(env, arena, &typed_bindings);

            let desc = StructureItemDesc::Tstr_value(*rec_flag, typed_bindings);
            Ok((
                StructureItem {
                    str_desc: desc,
                    str_loc: loc,
                    str_env: EnvRef(0),
                },
                new_env,
            ))
        }

        ParsedStructureItemDesc::Pstr_primitive(vd) => {
            // Primitive declaration: external f : t = "..."
            let name_str = arena.get_string(vd.pval_name.txt).to_string();
            let id = Ident::create_local(&name_str);

            // Translate the type annotation using transl_type_scheme pattern:
            // begin_def/end_def/generalize to keep Ttyp_any type vars as Tvar None
            let ctx = tctx.type_ctx;
            ctx.begin_def();
            let (typed_ctype, val_ty) = transl_type(tctx, env, &vd.pval_type)?;
            ctx.end_def();
            crate::types::ctype::generalize(ctx, val_ty);

            // Encode external FFI attributes into prim blob (matching OCaml's PPX encoding)
            let encoded = crate::binary_ast::ppx::encode_external(vd, arena);

            let desc = StructureItemDesc::Tstr_primitive(crate::types::typedtree::TypedValueDescription {
                val_id: id,
                val_name: Located { txt: name_str, loc: vd.pval_name.loc },
                val_desc: typed_ctype,
                val_prim: encoded.pval_prim,
                val_loc: loc,
                val_attributes: encoded.pval_attributes,
            });
            Ok((
                StructureItem {
                    str_desc: desc,
                    str_loc: loc,
                    str_env: EnvRef(0),
                },
                env.clone(),
            ))
        }

        ParsedStructureItemDesc::Pstr_type(rec_flag, decls) => {
            // Type declaration: type t = ...
            let ctx = tctx.type_ctx;
            let mut new_env = env.clone();
            let mut typed_tree_decls: Vec<TypedTypeDeclaration> = Vec::new();
            let mut internal_decls_for_generalize: Vec<crate::types::TypeDeclaration> = Vec::new();

            // OCaml: Ctype.begin_def() before translating type declarations
            ctx.begin_def();

            for decl in decls {
                let type_name = decl.ptype_name.txt;
                let type_name_str = arena.get_string(type_name);
                let type_id = Ident::create_persistent(type_name_str);

                // Create the type path for self-reference
                let type_path = Path::pident(type_id.clone());

                // Convert type parameters: (CoreType, Variance) -> (TypedCoreType, Variance)
                let mut typ_params: Vec<(TypedCoreType, TypesVariance)> = Vec::new();
                let mut internal_type_params: Vec<TypeExprRef> = Vec::new();
                for (core_type, parser_var) in &decl.ptype_params {
                    let (typed_core_type, type_ref) = transl_type(tctx, env, core_type)?;
                    internal_type_params.push(type_ref);
                    let types_var = match parser_var {
                        ParserVariance::Covariant => TypesVariance::covariant(),
                        ParserVariance::Contravariant => TypesVariance::contravariant(),
                        ParserVariance::Invariant => TypesVariance::invariant(),
                    };
                    typ_params.push((typed_core_type, types_var));
                }
                let type_arity = internal_type_params.len() as i32;

                // Convert type constraints
                let mut typ_cstrs: Vec<(TypedCoreType, TypedCoreType, LocIdx)> = Vec::new();
                for (ct1, ct2, cstr_loc) in &decl.ptype_cstrs {
                    let (typed_ct1, _) = transl_type(tctx, env, ct1)?;
                    let (typed_ct2, _) = transl_type(tctx, env, ct2)?;
                    typ_cstrs.push((typed_ct1, typed_ct2, *cstr_loc));
                }

                // Convert manifest type (type alias)
                let typ_manifest = match &decl.ptype_manifest {
                    Some(manifest) => {
                        let (typed_manifest, _) = transl_type(tctx, env, manifest)?;
                        Some(typed_manifest)
                    }
                    None => None,
                };

                // Convert the type kind - create both internal and typed tree versions
                let (internal_type_kind, typed_tree_kind, constructors) = match &decl.ptype_kind {
                    crate::parser::ast::TypeKind::Ptype_abstract => {
                        (crate::types::TypeKind::TypeAbstract, TypedTypeKind::Ttype_abstract, vec![])
                    }
                    crate::parser::ast::TypeKind::Ptype_variant(cstrs) => {
                        // OCaml copies @unboxed and @tag attributes from the type decl
                        // to each constructor (copy_tag_attr_from_decl in typedecl.ml)
                        let tag_attrs: Vec<_> = decl.ptype_attributes.iter()
                            .filter(|attr| {
                                let name = arena.get_string(attr.0.txt);
                                name == "unboxed" || name == "tag"
                            })
                            .cloned()
                            .collect();

                        let mut internal_cstrs = Vec::new();
                        let mut typed_tree_cstrs = Vec::new();
                        let mut cstr_descs = Vec::new();
                        let num_consts = cstrs.iter().filter(|c| matches!(c.pcd_args, crate::parser::ast::ConstructorArguments::Pcstr_tuple(ref args) if args.is_empty())).count() as i32;
                        let num_nonconsts = cstrs.len() as i32 - num_consts;

                        let mut const_tag = 0i32;
                        let mut block_tag = 0i32;

                        for cstr in cstrs {
                            let cstr_name_str = arena.get_string(cstr.pcd_name.txt);
                            let cstr_id = Ident::create_persistent(cstr_name_str);
                            let is_constant = matches!(cstr.pcd_args, crate::parser::ast::ConstructorArguments::Pcstr_tuple(ref args) if args.is_empty());

                            // Convert constructor arguments using transl_type
                            let (cstr_args, internal_cd_args, typed_tree_cd_args) = match &cstr.pcd_args {
                                crate::parser::ast::ConstructorArguments::Pcstr_tuple(types) => {
                                    let mut typed_args: Vec<TypeExprRef> = Vec::new();
                                    let mut typed_tree_args: Vec<TypedCoreType> = Vec::new();
                                    for core_type in types {
                                        let (typed_core_type, type_ref) = transl_type(tctx, env, core_type)?;
                                        typed_args.push(type_ref);
                                        typed_tree_args.push(typed_core_type);
                                    }
                                    (typed_args.clone(), crate::types::ConstructorArguments::CstrTuple(typed_args), TypedConstructorArguments::Cstr_tuple(typed_tree_args))
                                }
                                crate::parser::ast::ConstructorArguments::Pcstr_record(labels) => {
                                    let mut typed_labels: Vec<TypedLabelDeclaration> = Vec::new();
                                    let mut internal_labels: Vec<crate::types::LabelDeclaration> = Vec::new();
                                    for lbl in labels {
                                        let (typed_core_type, type_ref) = transl_type(tctx, env, &lbl.pld_type)?;
                                        // OCaml wraps optional label types in option
                                        let (typed_core_type, type_ref) = if lbl.pld_optional {
                                            let option_path = Path::pident(Ident::create_persistent("option"));
                                            let option_type_ref = ctx.new_constr(option_path.clone(), vec![type_ref]);
                                            let option_lid = crate::parse_arena::Located {
                                                txt: arena.placeholder_lid(),
                                                loc: lbl.pld_type.ptyp_loc,
                                            };
                                            let option_typed = TypedCoreType {
                                                ctyp_desc: TypedCoreTypeDesc::Ttyp_constr(
                                                    option_path,
                                                    option_lid,
                                                    vec![typed_core_type],
                                                ),
                                                ctyp_type: option_type_ref,
                                                ctyp_env: EnvRef(0),
                                                ctyp_loc: lbl.pld_type.ptyp_loc,
                                                ctyp_attributes: vec![],
                                            };
                                            (option_typed, option_type_ref)
                                        } else {
                                            (typed_core_type, type_ref)
                                        };
                                        let mutable_flag = match lbl.pld_mutable {
                                            crate::parser::ast::MutableFlag::Immutable => crate::types::MutableFlag::Immutable,
                                            crate::parser::ast::MutableFlag::Mutable => crate::types::MutableFlag::Mutable,
                                        };
                                        // OCaml wraps label types in Tpoly for potential generalization
                                        let poly_type_ref = ctx.new_poly(type_ref, vec![]);
                                        let lbl_name_str = arena.get_string(lbl.pld_name.txt);
                                        internal_labels.push(crate::types::LabelDeclaration {
                                            ld_id: Ident::create_persistent(lbl_name_str),
                                            ld_mutable: mutable_flag,
                                            ld_optional: lbl.pld_optional,
                                            ld_type: poly_type_ref,
                                            ld_loc: arena.to_location(lbl.pld_loc),
                                            ld_attributes: vec![],
                                        });
                                        // OCaml wraps label types in Ttyp_poly for typed tree
                                        let poly_typed_core_type = TypedCoreType {
                                            ctyp_desc: TypedCoreTypeDesc::Ttyp_poly(vec![], Box::new(typed_core_type.clone())),
                                            ctyp_type: poly_type_ref,
                                            ctyp_env: typed_core_type.ctyp_env,
                                            ctyp_loc: typed_core_type.ctyp_loc.clone(),
                                            ctyp_attributes: vec![],
                                        };
                                        typed_labels.push(TypedLabelDeclaration {
                                            ld_id: Ident::create_persistent(lbl_name_str),
                                            ld_name: crate::parse_arena::Located {
                                                txt: lbl_name_str.to_string(),
                                                loc: lbl.pld_name.loc,
                                            },
                                            ld_mutable: lbl.pld_mutable.clone(),
                                            ld_optional: lbl.pld_optional,
                                            ld_type: poly_typed_core_type,
                                            ld_loc: lbl.pld_loc,
                                            ld_attributes: lbl.pld_attributes.clone(),
                                        });
                                    }
                                    (vec![], crate::types::ConstructorArguments::CstrRecord(internal_labels), TypedConstructorArguments::Cstr_record(typed_labels))
                                }
                            };

                            // Determine the tag
                            let tag = if is_constant {
                                let t = const_tag;
                                const_tag += 1;
                                crate::types::ConstructorTag::CstrConstant(t)
                            } else {
                                let t = block_tag;
                                block_tag += 1;
                                crate::types::ConstructorTag::CstrBlock(t)
                            };

                            // Create the result type: Tconstr(type_path, type_params)
                            let res_ty = ctx.new_constr(type_path.clone(), internal_type_params.clone());

                            // For inline records, create a synthetic type declaration and
                            // set cstr_args to [Tconstr(path, type_params)] matching OCaml's datarepr.ml
                            let (cstr_args, cstr_inlined) = if let crate::types::ConstructorArguments::CstrRecord(ref lbls) = internal_cd_args {
                                // Build path: Pdot(Pident(type_name), cstr_name)
                                let inline_path = Path::pdot(type_path.clone(), cstr_name_str.to_string());
                                // Create synthetic inline type declaration
                                let inline_decl = crate::types::TypeDeclaration {
                                    type_params: internal_type_params.clone(),
                                    type_arity,
                                    type_kind: crate::types::TypeKind::TypeRecord(
                                        lbls.clone(),
                                        crate::types::RecordRepresentation::RecordInlined {
                                            tag: block_tag - 1, // use the tag just assigned
                                            name: cstr_name_str.to_string(),
                                            num_nonconsts,
                                            attrs: vec![], // simplified - parser attrs vs types attrs
                                        },
                                    ),
                                    type_private: crate::types::PrivateFlag::Public,
                                    type_manifest: None,
                                    type_variance: internal_type_params.iter().map(|_| TypesVariance::full()).collect(),
                                    type_newtype_level: None,
                                    type_loc: Location::none(),
                                    type_attributes: vec![],
                                    type_immediate: false,
                                    type_unboxed: crate::types::UnboxedStatus::default(),
                                    type_inlined_types: vec![],
                                };
                                // cstr_args: single Tconstr pointing to the inline record path
                                let inline_constr = ctx.new_constr(inline_path, internal_type_params.clone());
                                (vec![inline_constr], Some(Box::new(inline_decl)))
                            } else {
                                (cstr_args, None)
                            };

                            // Create internal constructor declaration
                            internal_cstrs.push(crate::types::ConstructorDeclaration {
                                cd_id: cstr_id.clone(),
                                cd_args: internal_cd_args,
                                cd_res: None,
                                cd_loc: arena.to_location(cstr.pcd_loc),
                                cd_attributes: vec![],
                            });

                            // Create typed tree constructor declaration
                            typed_tree_cstrs.push(TypedConstructorDeclaration {
                                cd_id: cstr_id.clone(),
                                cd_name: crate::parse_arena::Located {
                                    txt: cstr_name_str.to_string(),
                                    loc: cstr.pcd_name.loc,
                                },
                                cd_args: typed_tree_cd_args,
                                cd_res: None,
                                cd_loc: cstr.pcd_loc,
                                cd_attributes: {
                                    let mut attrs = tag_attrs.clone();
                                    attrs.extend(cstr.pcd_attributes.clone());
                                    attrs
                                },
                            });

                            // Create constructor description for the environment
                            let cstr_arity = cstr_args.len() as i32;
                            cstr_descs.push((cstr_id, crate::types::ConstructorDescription {
                                cstr_name: cstr_name_str.to_string(),
                                cstr_res: res_ty,
                                cstr_existentials: vec![],
                                cstr_args,
                                cstr_arity,
                                cstr_tag: tag,
                                cstr_consts: num_consts,
                                cstr_nonconsts: num_nonconsts,
                                cstr_generalized: false,
                                cstr_private: crate::types::PrivateFlag::Public,
                                cstr_loc: arena.to_location(cstr.pcd_loc),
                                cstr_attributes: vec![],
                                cstr_inlined,
                            }));
                        }

                        (crate::types::TypeKind::TypeVariant(internal_cstrs), TypedTypeKind::Ttype_variant(typed_tree_cstrs), cstr_descs)
                    }
                    crate::parser::ast::TypeKind::Ptype_record(labels) => {
                        let mut internal_labels: Vec<crate::types::LabelDeclaration> = Vec::new();
                        let mut typed_tree_labels: Vec<TypedLabelDeclaration> = Vec::new();
                        for lbl in labels {
                            let lbl_name_str = arena.get_string(lbl.pld_name.txt);
                            let (typed_core_type, type_ref) = transl_type(tctx, env, &lbl.pld_type)?;
                            // OCaml wraps optional label types in option (typedecl.ml lines 616-628)
                            let (typed_core_type, type_ref) = if lbl.pld_optional {
                                let option_path = Path::pident(Ident::create_persistent("option"));
                                let option_type_ref = ctx.new_constr(option_path.clone(), vec![type_ref]);
                                let option_lid = crate::parse_arena::Located {
                                    txt: arena.placeholder_lid(),
                                    loc: lbl.pld_type.ptyp_loc,
                                };
                                let option_typed = TypedCoreType {
                                    ctyp_desc: TypedCoreTypeDesc::Ttyp_constr(
                                        option_path,
                                        option_lid,
                                        vec![typed_core_type],
                                    ),
                                    ctyp_type: option_type_ref,
                                    ctyp_env: EnvRef(0),
                                    ctyp_loc: lbl.pld_type.ptyp_loc,
                                    ctyp_attributes: vec![],
                                };
                                (option_typed, option_type_ref)
                            } else {
                                (typed_core_type, type_ref)
                            };
                            let mutable_flag = match lbl.pld_mutable {
                                crate::parser::ast::MutableFlag::Immutable => crate::types::MutableFlag::Immutable,
                                crate::parser::ast::MutableFlag::Mutable => crate::types::MutableFlag::Mutable,
                            };
                            // OCaml wraps label types in Tpoly for potential generalization
                            let poly_type_ref = ctx.new_poly(type_ref, vec![]);
                            internal_labels.push(crate::types::LabelDeclaration {
                                ld_id: Ident::create_persistent(lbl_name_str),
                                ld_mutable: mutable_flag,
                                ld_optional: lbl.pld_optional,
                                ld_type: poly_type_ref,
                                ld_loc: arena.to_location(lbl.pld_loc),
                                ld_attributes: vec![],
                            });
                            // OCaml wraps label types in Ttyp_poly for typed tree
                            let poly_typed_core_type = TypedCoreType {
                                ctyp_desc: TypedCoreTypeDesc::Ttyp_poly(vec![], Box::new(typed_core_type.clone())),
                                ctyp_type: poly_type_ref,
                                ctyp_env: typed_core_type.ctyp_env,
                                ctyp_loc: typed_core_type.ctyp_loc,
                                ctyp_attributes: vec![],
                            };
                            typed_tree_labels.push(TypedLabelDeclaration {
                                ld_id: Ident::create_persistent(lbl_name_str),
                                ld_name: crate::parse_arena::Located {
                                    txt: lbl_name_str.to_string(),
                                    loc: lbl.pld_name.loc,
                                },
                                ld_mutable: lbl.pld_mutable.clone(),
                                ld_optional: lbl.pld_optional,
                                ld_type: poly_typed_core_type,
                                ld_loc: lbl.pld_loc,
                                ld_attributes: lbl.pld_attributes.clone(),
                            });
                        }
                        // Expand record type spreads in typed tree only: replace "..." labels with
                        // actual fields from the spread target record type.
                        // Internal labels are kept unchanged to avoid issues with lambda conversion.
                        //
                        // Following OCaml's record_type_spread.ml mk_lbl pattern:
                        // The spread's core_type structure (inner Ttyp_poly) is preserved,
                        // only the outer ctyp_type is replaced with the actual field type.
                        let has_spread = typed_tree_labels.iter().any(|l| l.ld_name.txt == "...");
                        let expanded_typed = if has_spread {
                            // Recursively collect expanded fields from a type's internal labels.
                            // This handles chained spreads like type c = {...b} where b = {...a, y: string}.
                            fn collect_fields(
                                ctx: &crate::types::TypeContext<'_>,
                                env: &Env,
                                fields: &[crate::types::LabelDeclaration],
                            ) -> Vec<crate::types::LabelDeclaration> {
                                let mut result = Vec::new();
                                for field in fields {
                                    if field.ld_id.name() == "..." {
                                        // This is a spread — follow the type reference
                                        let spread_ty = {
                                            let ty = ctx.repr(field.ld_type);
                                            let desc = ctx.get_desc(ty);
                                            match &*desc {
                                                crate::types::TypeDesc::Tpoly { body, .. } => ctx.repr(*body),
                                                _ => ty,
                                            }
                                        };
                                        let spread_desc = ctx.get_desc(spread_ty);
                                        if let crate::types::TypeDesc::Tconstr { path, .. } = &*spread_desc {
                                            let type_name = match path {
                                                Path::Pident(id) => id.name().to_string(),
                                                Path::Pdot(_, name, _) => name.clone(),
                                                _ => String::new(),
                                            };
                                            if let Ok(type_decl) = env.find_type(&type_name) {
                                                if let crate::types::TypeKind::TypeRecord(ref inner_fields, _) = type_decl.type_kind {
                                                    result.extend(collect_fields(ctx, env, inner_fields));
                                                    continue;
                                                }
                                            }
                                        }
                                        // Couldn't expand — keep as-is
                                        result.push(field.clone());
                                    } else {
                                        result.push(field.clone());
                                    }
                                }
                                result
                            }

                            let mut expanded: Vec<TypedLabelDeclaration> = Vec::new();
                            for tl in typed_tree_labels.into_iter() {
                                if tl.ld_name.txt == "..." {
                                    // Extract the concrete type from the spread's Tpoly wrapper
                                    let spread_ty = {
                                        let ty = ctx.repr(tl.ld_type.ctyp_type);
                                        let desc = ctx.get_desc(ty);
                                        match &*desc {
                                            crate::types::TypeDesc::Tpoly { body, .. } => ctx.repr(*body),
                                            _ => ty,
                                        }
                                    };
                                    let spread_desc = ctx.get_desc(spread_ty);
                                    let mut did_expand = false;
                                    if let crate::types::TypeDesc::Tconstr { path, .. } = &*spread_desc {
                                        let type_name = match path {
                                            Path::Pident(id) => id.name().to_string(),
                                            Path::Pdot(_, name, _) => name.clone(),
                                            _ => String::new(),
                                        };
                                        if let Ok(type_decl) = new_env.find_type(&type_name) {
                                            if let crate::types::TypeKind::TypeRecord(ref fields, _) = type_decl.type_kind {
                                                // Recursively expand any nested spreads
                                                let resolved_fields = collect_fields(ctx, &new_env, fields);
                                                did_expand = true;
                                                for field in &resolved_fields {
                                                    // field.ld_type is Tpoly(actual_type, []) — unwrap for outer.
                                                    let actual_field_type = {
                                                        let ty = ctx.repr(field.ld_type);
                                                        let desc = ctx.get_desc(ty);
                                                        match &*desc {
                                                            crate::types::TypeDesc::Tpoly { body, .. } => *body,
                                                            _ => ty,
                                                        }
                                                    };
                                                    let typed_ld_type = match &tl.ld_type.ctyp_desc {
                                                        TypedCoreTypeDesc::Ttyp_poly(vars, inner_ctyp) => {
                                                            // Inner core_type: keep as-is from spread source
                                                            // Outer Ttyp_poly: replace ctyp_type with actual field type
                                                            TypedCoreType {
                                                                ctyp_desc: TypedCoreTypeDesc::Ttyp_poly(vars.clone(), inner_ctyp.clone()),
                                                                ctyp_type: actual_field_type,
                                                                ..tl.ld_type.clone()
                                                            }
                                                        }
                                                        _ => {
                                                            TypedCoreType {
                                                                ctyp_type: actual_field_type,
                                                                ..tl.ld_type.clone()
                                                            }
                                                        }
                                                    };
                                                    let parser_mutable = match &field.ld_mutable {
                                                        crate::types::MutableFlag::Immutable => crate::parser::ast::MutableFlag::Immutable,
                                                        crate::types::MutableFlag::Mutable => crate::parser::ast::MutableFlag::Mutable,
                                                    };
                                                    expanded.push(TypedLabelDeclaration {
                                                        ld_id: field.ld_id.clone(),
                                                        ld_name: crate::parse_arena::Located {
                                                            txt: field.ld_id.name().to_string(),
                                                            loc: tl.ld_loc,
                                                        },
                                                        ld_mutable: parser_mutable,
                                                        ld_optional: field.ld_optional,
                                                        ld_type: typed_ld_type,
                                                        ld_loc: tl.ld_loc,
                                                        ld_attributes: vec![],
                                                    });
                                                }
                                            }
                                        }
                                    }
                                    if !did_expand {
                                        expanded.push(tl);
                                    }
                                } else {
                                    expanded.push(tl);
                                }
                            }
                            expanded
                        } else {
                            typed_tree_labels
                        };
                        (crate::types::TypeKind::TypeRecord(internal_labels, crate::types::RecordRepresentation::RecordRegular), TypedTypeKind::Ttype_record(expanded_typed), vec![])
                    }
                    crate::parser::ast::TypeKind::Ptype_open => {
                        (crate::types::TypeKind::TypeOpen, TypedTypeKind::Ttype_open, vec![])
                    }
                };

                // Create internal type declaration for the environment
                let internal_decl = crate::types::TypeDeclaration {
                    type_params: internal_type_params,
                    type_arity,
                    type_kind: internal_type_kind,
                    type_private: crate::types::PrivateFlag::Public,
                    type_manifest: None,
                    type_variance: typ_params.iter().map(|(_, v)| *v).collect(),
                    type_newtype_level: None,
                    type_loc: arena.to_location(decl.ptype_loc),
                    type_attributes: vec![],
                    type_immediate: false,
                    type_unboxed: crate::types::UnboxedStatus::default(),
                    type_inlined_types: vec![],
                };

                // Save for generalization after the loop
                internal_decls_for_generalize.push(internal_decl.clone());

                // Add type to environment
                new_env.add_type(type_id.clone(), internal_decl.clone());

                // Add constructors to environment, and add inline record labels
                for (cstr_id, cstr_desc) in constructors {
                    // For inline records, add the labels to the environment
                    if let Some(ref inlined_decl) = cstr_desc.cstr_inlined {
                        if let crate::types::TypeKind::TypeRecord(ref labels, ref repres) = inlined_decl.type_kind {
                            // Build the inline record type path: Pdot(type_path, cstr_name)
                            let inline_path = Path::pdot(type_path.clone(), cstr_desc.cstr_name.clone());
                            let ty_res = ctx.new_constr(inline_path, inlined_decl.type_params.clone());
                            for (pos, ld) in labels.iter().enumerate() {
                                let lbl_desc = crate::types::LabelDescription {
                                    lbl_name: ld.ld_id.name().to_string(),
                                    lbl_res: ty_res,
                                    lbl_arg: ld.ld_type,
                                    lbl_mut: ld.ld_mutable.clone(),
                                    lbl_optional: ld.ld_optional,
                                    lbl_pos: pos as i32,
                                    lbl_all: crate::types::LabelArrayRef(0),
                                    lbl_repres: repres.clone(),
                                    lbl_private: crate::types::PrivateFlag::Public,
                                    lbl_loc: ld.ld_loc.clone(),
                                    lbl_attributes: ld.ld_attributes.clone(),
                                };
                                new_env.add_label(ld.ld_id.clone(), lbl_desc);
                            }
                        }
                    }
                    new_env.add_constructor(cstr_id, cstr_desc);
                }

                // Add record labels to environment
                if let crate::types::TypeKind::TypeRecord(ref labels, ref repres) = internal_decl.type_kind {
                    // Create the record type reference: Tconstr(type_path, type_params)
                    let ty_res = ctx.new_constr(type_path.clone(), internal_decl.type_params.clone());
                    for (pos, ld) in labels.iter().enumerate() {
                        let lbl_desc = crate::types::LabelDescription {
                            lbl_name: ld.ld_id.name().to_string(),
                            lbl_res: ty_res,
                            lbl_arg: ld.ld_type,
                            lbl_mut: ld.ld_mutable.clone(),
                            lbl_optional: ld.ld_optional,
                            lbl_pos: pos as i32,
                            lbl_all: crate::types::LabelArrayRef(0), // Placeholder for now
                            lbl_repres: repres.clone(),
                            lbl_private: crate::types::PrivateFlag::Public,
                            lbl_loc: ld.ld_loc.clone(),
                            lbl_attributes: ld.ld_attributes.clone(),
                        };
                        new_env.add_label(ld.ld_id.clone(), lbl_desc);
                    }
                }

                // Convert private flag
                let typ_private = match decl.ptype_private {
                    crate::parser::ast::PrivateFlag::Public => crate::parser::ast::PrivateFlag::Public,
                    crate::parser::ast::PrivateFlag::Private => crate::parser::ast::PrivateFlag::Private,
                };

                // Create typed tree type declaration
                let typed_tree_decl = TypedTypeDeclaration {
                    typ_id: type_id,
                    typ_name: crate::parse_arena::Located {
                        txt: type_name_str.to_string(),
                        loc: decl.ptype_name.loc,
                    },
                    typ_params,
                    typ_type: internal_decl,
                    typ_cstrs,
                    typ_kind: typed_tree_kind,
                    typ_private,
                    typ_manifest,
                    typ_loc: decl.ptype_loc,
                    typ_attributes: decl.ptype_attributes.clone(),
                };

                typed_tree_decls.push(typed_tree_decl);
            }

            // OCaml: Ctype.end_def() + generalize_decl for each declaration
            ctx.end_def();
            for decl in &internal_decls_for_generalize {
                // generalize type_params
                for &param in &decl.type_params {
                    crate::types::ctype::generalize(ctx, param);
                }
                // generalize all types in type_kind
                crate::types::btype::iter_type_expr_kind(&decl.type_kind, |ty| {
                    crate::types::ctype::generalize(ctx, ty);
                });
                // generalize type_manifest if present
                if let Some(manifest) = decl.type_manifest {
                    crate::types::ctype::generalize(ctx, manifest);
                }
            }

            let desc = StructureItemDesc::Tstr_type(*rec_flag, typed_tree_decls);
            Ok((
                StructureItem {
                    str_desc: desc,
                    str_loc: loc,
                    str_env: EnvRef(0),
                },
                new_env,
            ))
        }

        ParsedStructureItemDesc::Pstr_typext(ext) => {
            // Type extension: type t += ...
            let path = path_from_longident(tctx.resolve_lid(ext.ptyext_path.txt), |idx| arena.get_string(idx));

            // Translate constructors
            let mut typed_constructors = Vec::new();
            for ec in &ext.ptyext_constructors {
                let name_str = arena.get_string(ec.pext_name.txt).to_string();
                let id = Ident::create_local(&name_str);

                let (typed_args, typed_ret) = match &ec.pext_kind {
                    crate::parser::ast::ExtensionConstructorKind::Pext_decl(args, ret) => {
                        let typed_args = match args {
                            crate::parser::ast::ConstructorArguments::Pcstr_tuple(types) => {
                                let mut typed = Vec::new();
                                for ty in types {
                                    let (typed_ct, _ty_ref) = transl_type(tctx, env, ty)?;
                                    typed.push(typed_ct);
                                }
                                crate::types::typedtree::ConstructorArgument::Cstr_tuple(typed)
                            }
                            crate::parser::ast::ConstructorArguments::Pcstr_record(_lds) => {
                                crate::types::typedtree::ConstructorArgument::Cstr_tuple(vec![])
                            }
                        };
                        let typed_ret = match ret {
                            Some(ct) => {
                                let (typed_ct, _) = transl_type(tctx, env, ct)?;
                                Some(typed_ct)
                            }
                            None => None,
                        };
                        (typed_args, typed_ret)
                    }
                    crate::parser::ast::ExtensionConstructorKind::Pext_rebind(_lid) => {
                        (crate::types::typedtree::ConstructorArgument::Cstr_tuple(vec![]), None)
                    }
                };

                typed_constructors.push(crate::types::typedtree::ExtensionConstructor {
                    ext_id: id,
                    ext_name: crate::parse_arena::Located {
                        txt: name_str,
                        loc: ec.pext_name.loc,
                    },
                    ext_type: crate::types::ExtensionConstructor {
                        ext_type_path: path.clone(),
                        ext_type_params: vec![],
                        ext_args: crate::types::ConstructorArguments::CstrTuple(vec![]),
                        ext_ret_type: None,
                        ext_private: crate::types::PrivateFlag::Public,
                        ext_loc: arena.to_location(loc),
                        ext_attributes: vec![],
                        ext_is_exception: false,
                    },
                    ext_kind: crate::types::typedtree::ExtensionConstructorKind::Text_decl(
                        typed_args,
                        typed_ret,
                    ),
                    ext_loc: ec.pext_loc,
                    ext_attributes: ec.pext_attributes.clone(),
                });
            }

            // Translate params
            let mut typed_params = Vec::new();
            for (ct, v) in &ext.ptyext_params {
                let (typed_ct, _) = transl_type(tctx, env, ct)?;
                let variance = match v {
                    ParserVariance::Covariant => TypesVariance::covariant(),
                    ParserVariance::Contravariant => TypesVariance::contravariant(),
                    ParserVariance::Invariant => TypesVariance::null(),
                };
                typed_params.push((typed_ct, variance));
            }

            let desc = StructureItemDesc::Tstr_typext(TypeExtension {
                tyext_path: path,
                tyext_txt: ext.ptyext_path.clone(),
                tyext_params: typed_params,
                tyext_constructors: typed_constructors,
                tyext_private: ext.ptyext_private,
                tyext_loc: loc,
                tyext_attributes: ext.ptyext_attributes.clone(),
            });
            Ok((
                StructureItem {
                    str_desc: desc,
                    str_loc: loc,
                    str_env: EnvRef(0),
                },
                env.clone(),
            ))
        }

        ParsedStructureItemDesc::Pstr_exception(ext_constr) => {
            // Exception declaration: exception C
            let name_str = arena.get_string(ext_constr.pext_name.txt).to_string();
            let id = Ident::create_local(&name_str);

            // Translate constructor arguments
            let (typed_args, _ext_ret) = match &ext_constr.pext_kind {
                crate::parser::ast::ExtensionConstructorKind::Pext_decl(args, ret) => {
                    let typed_args = match args {
                        crate::parser::ast::ConstructorArguments::Pcstr_tuple(types) => {
                            let mut typed = Vec::new();
                            for ty in types {
                                let (typed_ct, _ty_ref) = transl_type(tctx, env, ty)?;
                                typed.push(typed_ct);
                            }
                            crate::types::typedtree::ConstructorArgument::Cstr_tuple(typed)
                        }
                        crate::parser::ast::ConstructorArguments::Pcstr_record(_lds) => {
                            // TODO: translate record constructor arguments
                            crate::types::typedtree::ConstructorArgument::Cstr_tuple(vec![])
                        }
                    };
                    let typed_ret = match ret {
                        Some(ct) => {
                            let (typed_ct, _) = transl_type(tctx, env, ct)?;
                            Some(typed_ct)
                        }
                        None => None,
                    };
                    (typed_args, typed_ret)
                }
                crate::parser::ast::ExtensionConstructorKind::Pext_rebind(_lid) => {
                    (crate::types::typedtree::ConstructorArgument::Cstr_tuple(vec![]), None)
                }
            };

            let desc =
                StructureItemDesc::Tstr_exception(crate::types::typedtree::ExtensionConstructor {
                    ext_id: id,
                    ext_name: crate::parse_arena::Located {
                        txt: name_str,
                        loc: ext_constr.pext_name.loc,
                    },
                    ext_type: crate::types::ExtensionConstructor {
                        ext_type_path: Path::pident(Ident::create_local("exn")),
                        ext_type_params: vec![],
                        ext_args: crate::types::ConstructorArguments::CstrTuple(vec![]),
                        ext_ret_type: None,
                        ext_private: crate::types::PrivateFlag::Public,
                        ext_loc: arena.to_location(loc),
                        ext_attributes: vec![],
                        ext_is_exception: true,
                    },
                    ext_kind: crate::types::typedtree::ExtensionConstructorKind::Text_decl(
                        typed_args,
                        _ext_ret,
                    ),
                    ext_loc: loc,
                    ext_attributes: ext_constr.pext_attributes.clone(),
                });
            Ok((
                StructureItem {
                    str_desc: desc,
                    str_loc: loc,
                    str_env: EnvRef(0),
                },
                env.clone(),
            ))
        }

        ParsedStructureItemDesc::Pstr_module(mb) => {
            // Module binding: module M = ME
            let typed_mod = type_module_expr(tctx, env, arena, &mb.pmb_expr)?;
            let mod_name_str = arena.get_string(mb.pmb_name.txt);
            let mod_id = Ident::create_local(mod_name_str);

            let desc = StructureItemDesc::Tstr_module(ModuleBinding {
                mb_id: mod_id,
                mb_name: Located { txt: mod_name_str.to_string(), loc: mb.pmb_name.loc },
                mb_expr: typed_mod,
                mb_attributes: mb.pmb_attributes.clone(),
                mb_loc: mb.pmb_loc,
            });
            Ok((
                StructureItem {
                    str_desc: desc,
                    str_loc: loc,
                    str_env: EnvRef(0),
                },
                env.clone(),
            ))
        }

        ParsedStructureItemDesc::Pstr_recmodule(mbs) => {
            // Recursive modules: module rec M = ...
            let mut typed_bindings = Vec::new();
            for mb in mbs {
                let typed_mod = type_module_expr(tctx, env, arena, &mb.pmb_expr)?;
                let mod_name_str = arena.get_string(mb.pmb_name.txt);
                let mod_id = Ident::create_local(mod_name_str);
                typed_bindings.push(ModuleBinding {
                    mb_id: mod_id,
                    mb_name: Located { txt: mod_name_str.to_string(), loc: mb.pmb_name.loc },
                    mb_expr: typed_mod,
                    mb_attributes: mb.pmb_attributes.clone(),
                    mb_loc: mb.pmb_loc,
                });
            }

            let desc = StructureItemDesc::Tstr_recmodule(typed_bindings);
            Ok((
                StructureItem {
                    str_desc: desc,
                    str_loc: loc,
                    str_env: EnvRef(0),
                },
                env.clone(),
            ))
        }

        ParsedStructureItemDesc::Pstr_modtype(mtd) => {
            // Module type declaration: module type S = MT
            let mtd_name_str = arena.get_string(mtd.pmtd_name.txt);
            let mtd_id = Ident::create_local(mtd_name_str);

            let typed_mty = match &mtd.pmtd_type {
                Some(mt) => Some(transl_modtype(tctx, env, arena, mt)?),
                None => None,
            };

            let desc = StructureItemDesc::Tstr_modtype(ModuleTypeDeclaration {
                mtd_id,
                mtd_name: Located { txt: mtd_name_str.to_string(), loc: mtd.pmtd_name.loc },
                mtd_type: typed_mty,
                mtd_attributes: mtd.pmtd_attributes.clone(),
                mtd_loc: mtd.pmtd_loc,
            });
            Ok((
                StructureItem {
                    str_desc: desc,
                    str_loc: loc,
                    str_env: EnvRef(0),
                },
                env.clone(),
            ))
        }

        ParsedStructureItemDesc::Pstr_open(open_desc) => {
            // Open declaration: open M
            let path = path_from_longident(tctx.resolve_lid(open_desc.popen_lid.txt), |idx| arena.get_string(idx));

            let desc = StructureItemDesc::Tstr_open(OpenDeclaration {
                open_path: path,
                open_txt: open_desc.popen_lid.clone(),
                open_override: open_desc.popen_override,
                open_loc: loc,
                open_attributes: open_desc.popen_attributes.clone(),
            });
            Ok((
                StructureItem {
                    str_desc: desc,
                    str_loc: loc,
                    str_env: EnvRef(0),
                },
                env.clone(),
            ))
        }

        ParsedStructureItemDesc::Pstr_include(incl) => {
            // Include declaration: include ME
            let typed_mod = type_module_expr(tctx, env, arena, &incl.pincl_mod)?;

            let desc = StructureItemDesc::Tstr_include(IncludeDeclaration {
                incl_mod: typed_mod,
                incl_type: vec![],
                incl_attributes: incl.pincl_attributes.clone(),
                incl_loc: incl.pincl_loc,
            });
            Ok((
                StructureItem {
                    str_desc: desc,
                    str_loc: loc,
                    str_env: EnvRef(0),
                },
                env.clone(),
            ))
        }

        ParsedStructureItemDesc::Pstr_attribute(attr) => {
            // Attribute: @@attr
            let desc = StructureItemDesc::Tstr_attribute(attr.clone());
            Ok((
                StructureItem {
                    str_desc: desc,
                    str_loc: loc,
                    str_env: EnvRef(0),
                },
                env.clone(),
            ))
        }

        ParsedStructureItemDesc::Pstr_extension(_ext, _attrs) => {
            // Extension: [%%id]
            // Extensions like %%raw are expanded by the PPX pass before type checking.
            // If we get here, the extension wasn't expanded. Return a placeholder.
            let ctx = tctx.type_ctx;
            let unit_ty = ctx.new_tuple(vec![]);
            let desc = StructureItemDesc::Tstr_eval(
                Expression::new(
                    crate::types::typedtree::ExpressionDesc::Texp_constant(
                        crate::types::typedtree::Constant::Int(0),
                    ),
                    loc.clone(),
                    unit_ty,
                    EnvRef(0),
                    vec![],
                ),
                vec![],
            );
            Ok((
                StructureItem {
                    str_desc: desc,
                    str_loc: loc,
                    str_env: EnvRef(0),
                },
                env.clone(),
            ))
        }
    }
}

// ============================================================================
// Helper Functions
// ============================================================================

/// Type check value bindings in a structure.
fn type_value_bindings<'a>(
    tctx: &mut TypeCheckContext<'a>,
    env: &Env,
    arena: &'a ParseArena,
    rec_flag: RecFlag,
    bindings: &[crate::parser::ast::ValueBinding],
) -> TypeModResult<Vec<ValueBinding>> {
    // type_binding takes all bindings at once and returns (Vec<ValueBinding>, Env)
    let (typed_bindings, _new_env) = type_binding(tctx.type_ctx, arena, env, rec_flag, bindings)?;
    Ok(typed_bindings)
}

/// Extend environment with value bindings.
fn extend_env_with_bindings(env: &Env, arena: &ParseArena, bindings: &[ValueBinding]) -> Env {
    let mut new_env = env.clone();

    for binding in bindings {
        // Extract variable names from the pattern and add them to the environment
        // This is a simplified implementation - full version would handle all pattern types
        if let crate::types::typedtree::PatternDesc::Tpat_var(id, _) = &binding.vb_pat.pat_desc {
            let val_desc = crate::types::ValueDescription {
                val_type: binding.vb_pat.pat_type,
                val_kind: crate::types::ValueKind::ValReg,
                val_loc: arena.to_location(binding.vb_loc),
                val_attributes: vec![],
                val_path: None,
            };
            new_env.add_value(id.clone(), val_desc);
        }
    }

    new_env
}

// ============================================================================
// Signature Type Declaration Translation
// ============================================================================

/// Translate type declarations in a signature.
/// Simplified version of the Pstr_type handler for use in signature items.
fn transl_sig_type_declarations<'a>(
    tctx: &mut TypeCheckContext<'a>,
    env: &Env,
    arena: &'a ParseArena,
    decls: &[crate::parser::ast::TypeDeclaration],
) -> TypeModResult<Vec<TypedTypeDeclaration>> {
    let ctx = tctx.type_ctx;
    let mut typed_tree_decls = Vec::new();

    for decl in decls {
        let type_name = decl.ptype_name.txt;
        let type_name_str = arena.get_string(type_name);
        let type_id = Ident::create_persistent(type_name_str);
        let type_path = Path::pident(type_id.clone());

        // Convert type parameters
        let mut typ_params: Vec<(TypedCoreType, TypesVariance)> = Vec::new();
        let mut internal_type_params: Vec<TypeExprRef> = Vec::new();
        for (core_type, parser_var) in &decl.ptype_params {
            let (typed_core_type, type_ref) = transl_type(tctx, env, core_type)?;
            internal_type_params.push(type_ref);
            let types_var = match parser_var {
                ParserVariance::Covariant => TypesVariance::covariant(),
                ParserVariance::Contravariant => TypesVariance::contravariant(),
                ParserVariance::Invariant => TypesVariance::invariant(),
            };
            typ_params.push((typed_core_type, types_var));
        }

        // Convert manifest type (type alias)
        let typ_manifest = match &decl.ptype_manifest {
            Some(manifest) => {
                let (typed_manifest, _) = transl_type(tctx, env, manifest)?;
                Some(typed_manifest)
            }
            None => None,
        };

        // For signatures, keep type kind simple (abstract or basic)
        let typed_tree_kind = TypedTypeKind::Ttype_abstract;

        let typ_private = decl.ptype_private;

        // Create minimal internal type declaration
        let internal_decl = crate::types::TypeDeclaration {
            type_params: internal_type_params,
            type_arity: decl.ptype_params.len() as i32,
            type_kind: crate::types::TypeKind::TypeAbstract,
            type_private: match typ_private {
                crate::parser::ast::PrivateFlag::Public => crate::types::PrivateFlag::Public,
                crate::parser::ast::PrivateFlag::Private => crate::types::PrivateFlag::Private,
            },
            type_manifest: None,
            type_variance: vec![],
            type_newtype_level: None,
            type_loc: arena.to_location(decl.ptype_loc),
            type_attributes: vec![],
            type_immediate: false,
            type_unboxed: crate::types::UnboxedStatus { unboxed: false, default: false },
            type_inlined_types: vec![],
        };

        typed_tree_decls.push(TypedTypeDeclaration {
            typ_id: type_id,
            typ_name: crate::parse_arena::Located {
                txt: type_name_str.to_string(),
                loc: decl.ptype_name.loc,
            },
            typ_params,
            typ_type: internal_decl,
            typ_cstrs: vec![],
            typ_kind: typed_tree_kind,
            typ_private: typ_private,
            typ_manifest,
            typ_loc: decl.ptype_loc,
            typ_attributes: decl.ptype_attributes.clone(),
        });
    }

    Ok(typed_tree_decls)
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_type_module_error_conversion() {
        let core_error = TypeCoreError::MultiplyBoundVariable("x".to_string());
        let mod_error: TypeModError = core_error.into();
        match mod_error {
            TypeModError::CoreError(_) => {}
            _ => panic!("Expected CoreError"),
        }
    }
}
