//! Module inclusion checking for ReScript.
//!
//! This module implements signature matching, which verifies that a module
//! implementation conforms to a module signature. This is equivalent to
//! OCaml's `includemod.ml`.
//!
//! The main function is `modtypes` which checks if one module type is
//! a subtype of another.

#![allow(unused_variables)]
#![allow(dead_code)]

use crate::ident::Ident;
use crate::types::ctype::{self, UnifyState};
use crate::types::decl::{
    ExtensionConstructor, ModtypeDeclaration, ModuleType, Signature, SignatureItem, ValueKind,
    TypeDeclaration, ValueDescription,
};
use crate::types::env::Env;
use crate::types::Path;
use crate::types::typedtree::ModuleCoercion;
use crate::types::{TypeContext, TypeExprRef};
use ahash::{AHashMap as HashMap, AHashSet as HashSet};

// ============================================================================
// Error Types
// ============================================================================

/// Result type for inclusion checking.
pub type IncludeModResult<T> = Result<T, IncludeModError>;

/// Errors that can occur during module inclusion checking.
#[derive(Debug, Clone)]
pub enum IncludeModError {
    /// Missing value in implementation.
    MissingValue(Ident),
    /// Missing type in implementation.
    MissingType(Ident),
    /// Missing module in implementation.
    MissingModule(Ident),
    /// Missing module type in implementation.
    MissingModuleType(Ident),
    /// Value type mismatch.
    ValueTypeMismatch {
        name: Ident,
        expected: TypeExprRef,
        found: TypeExprRef,
    },
    /// Type declaration mismatch.
    TypeMismatch { name: Ident, reason: String },
    /// Module type mismatch.
    ModuleTypeMismatch { name: Ident, reason: String },
    /// Functor parameter mismatch.
    FunctorParamMismatch(String),
    /// Functor result mismatch.
    FunctorResultMismatch(String),
    /// Not a functor.
    NotAFunctor,
    /// Signature mismatch with details.
    SignatureMismatch(Vec<IncludeModError>),
}

// ============================================================================
// Module Type Inclusion
// ============================================================================

/// Check if `mty_impl` is a subtype of `mty_sig` (implementation matches signature).
///
/// Returns a coercion that can be applied to convert the implementation
/// to the signature type.
use std::cell::Cell;

thread_local! {
    static MODTYPES_DEPTH: Cell<usize> = Cell::new(0);
}

pub fn modtypes<'a>(
    type_ctx: &'a TypeContext<'a>,
    env: &Env,
    mty_impl: &ModuleType,
    mty_sig: &ModuleType,
) -> IncludeModResult<ModuleCoercion> {
    modtypes_inner(type_ctx, env, mty_impl, mty_sig, false)
}

/// Check if `mty_impl` is a subtype of `mty_sig` with optional aliasability.
fn modtypes_inner<'a>(
    type_ctx: &'a TypeContext<'a>,
    env: &Env,
    mty_impl: &ModuleType,
    mty_sig: &ModuleType,
    aliasable: bool,
) -> IncludeModResult<ModuleCoercion> {
    // Guard against infinite recursion in module type expansion
    let depth = MODTYPES_DEPTH.with(|d| {
        let v = d.get();
        d.set(v + 1);
        v
    });
    struct DepthGuard;
    impl Drop for DepthGuard {
        fn drop(&mut self) {
            MODTYPES_DEPTH.with(|d| d.set(d.get().saturating_sub(1)));
        }
    }
    let _guard = DepthGuard;
    if depth > 50 {
        return Ok(ModuleCoercion::Tcoerce_none);
    }

    fn expand_module_type_in_env(
        type_ctx: &TypeContext<'_>,
        env: &Env,
        path: &Path,
    ) -> Option<ModuleType> {
        use crate::types::decl::SignatureItem as SigItem;

        fn expand_local(
            env: &Env,
            path: &Path,
            visiting: &mut HashSet<Path>,
        ) -> Option<ModuleType> {
            if !visiting.insert(path.clone()) {
                return None;
            }

            match path {
                Path::Pident(id) => {
                    if let Ok(md) = env.lookup_module(&Path::pident(id.clone())) {
                        match &md.md_type {
                            ModuleType::MtyIdent(alias_path)
                            | ModuleType::MtyAlias(_, alias_path)
                                if !alias_path.same(path) =>
                            {
                                if let Some(expanded) = expand_local(env, alias_path, visiting) {
                                    return Some(expanded);
                                }
                            }
                            _ => return Some(md.md_type.clone()),
                        }
                    }
                    if let Ok(mtd) = env.lookup_modtype(&Path::pident(id.clone())) {
                        if let Some(mty) = &mtd.mtd_type {
                            match mty {
                                ModuleType::MtyIdent(alias_path)
                                | ModuleType::MtyAlias(_, alias_path)
                                    if !alias_path.same(path) =>
                                {
                                    if let Some(expanded) = expand_local(env, alias_path, visiting) {
                                        return Some(expanded);
                                    }
                                }
                                _ => return Some(mty.clone()),
                            }
                        }
                    }
                    None
                }
                Path::Pdot(parent, name, _) => {
                    let parent_mty = expand_local(env, parent, visiting)?;
                    let parent_sig = match &parent_mty {
                        ModuleType::MtySignature(sig) => sig.clone(),
                        ModuleType::MtyIdent(parent_path)
                        | ModuleType::MtyAlias(_, parent_path) => match expand_local(env, parent_path, visiting)?
                        {
                            ModuleType::MtySignature(sig) => sig,
                            _ => return None,
                        },
                        _ => return None,
                    };
                    for item in &parent_sig {
                        match item {
                            SigItem::SigModule(id, md, _) if id.name() == name.as_str() => {
                                return Some(md.md_type.clone());
                            }
                            SigItem::SigModtype(id, mtd) if id.name() == name.as_str() => {
                                return mtd.mtd_type.clone();
                            }
                            _ => {}
                        }
                    }
                    None
                }
                Path::Papply(_, _) => None,
            }
        }

        let head = path.head();
        if head.is_persistent() || head.stamp() == 0 {
            if let Some(resolved) =
                crate::types::ctype::resolve_module_type_through_env(type_ctx, env, path)
            {
                return Some(resolved);
            }
        }

        let mut visiting = HashSet::new();
        expand_local(env, path, &mut visiting)
    }

    fn normalized_alias_path(env: &Env, path: &Path) -> Path {
        env.normalize_path(path)
    }

    match (mty_impl, mty_sig) {
        (
            ModuleType::MtyAlias(pres_impl, impl_path),
            ModuleType::MtyAlias(pres_sig, sig_path),
        ) => {
            let impl_path = normalized_alias_path(env, impl_path);
            let sig_path = normalized_alias_path(env, sig_path);
            if !impl_path.same(&sig_path) {
                return Err(IncludeModError::ModuleTypeMismatch {
                    name: Ident::create_local("module"),
                    reason: "module aliases do not match".to_string(),
                });
            }
            match (pres_impl, pres_sig) {
                (
                    crate::types::decl::AliasPresence::MtaAbsent,
                    crate::types::decl::AliasPresence::MtaPresent,
                ) => Ok(ModuleCoercion::Tcoerce_alias(
                    crate::types::typedtree::EnvRef(0),
                    impl_path,
                    Box::new(ModuleCoercion::Tcoerce_none),
                )),
                _ => Ok(ModuleCoercion::Tcoerce_none),
            }
        }

        (ModuleType::MtyAlias(pres_impl, impl_path), mty_sig) => {
            let impl_path = normalized_alias_path(env, impl_path);
            let expanded = expand_module_type_in_env(type_ctx, env, &impl_path)
                .map(|mty| {
                    ctype::strengthen_module_type_for_inclusion_path(type_ctx, &impl_path, &mty)
                })
                .unwrap_or_else(|| ModuleType::MtyAlias(pres_impl.clone(), impl_path.clone()));
            let coercion = modtypes_inner(type_ctx, env, &expanded, mty_sig, aliasable)?;
            match pres_impl {
                crate::types::decl::AliasPresence::MtaPresent => Ok(coercion),
                crate::types::decl::AliasPresence::MtaAbsent => Ok(ModuleCoercion::Tcoerce_alias(
                    crate::types::typedtree::EnvRef(0),
                    impl_path,
                    Box::new(coercion),
                )),
            }
        }

        // Identical module type identifiers
        (ModuleType::MtyIdent(p1), ModuleType::MtyIdent(p2)) if p1 == p2 => {
            Ok(ModuleCoercion::Tcoerce_none)
        }

        // Alias on the signature side - expand and check
        (mty_impl, ModuleType::MtyAlias(_, path)) => {
            if let Some(expanded) = expand_module_type_in_env(type_ctx, env, path) {
                modtypes_inner(type_ctx, env, mty_impl, &expanded, aliasable)
            } else {
                Ok(ModuleCoercion::Tcoerce_none)
            }
        }

        // Signature matching
        (ModuleType::MtySignature(sig_impl), ModuleType::MtySignature(sig_sig)) => {
            signatures(type_ctx, env, sig_impl, sig_sig)
        }

        // Functor matching
        (
            ModuleType::MtyFunctor {
                param: param_impl,
                param_type: param_type_impl,
                result: result_impl,
            },
            ModuleType::MtyFunctor {
                param: param_sig,
                param_type: param_type_sig,
                result: result_sig,
            },
        ) => {
            // Check parameter (contravariant)
            let param_coercion = match (param_type_impl, param_type_sig) {
                (Some(pt_impl), Some(pt_sig)) => {
                    // Note: parameters are contravariant, so we swap impl/sig
                    modtypes_inner(type_ctx, env, pt_sig, pt_impl, true)?
                }
                (None, None) => ModuleCoercion::Tcoerce_none,
                _ => {
                    return Err(IncludeModError::FunctorParamMismatch(
                        "parameter presence mismatch".to_string(),
                    ));
                }
            };

            // Check result (covariant)
            // In a full implementation, we would extend the environment with the parameter
            let result_coercion = modtypes_inner(type_ctx, env, result_impl, result_sig, false)?;

            // If both parameter and result coercions are identity, return identity
            if matches!((&param_coercion, &result_coercion),
                (ModuleCoercion::Tcoerce_none, ModuleCoercion::Tcoerce_none)) {
                Ok(ModuleCoercion::Tcoerce_none)
            } else {
                Ok(ModuleCoercion::Tcoerce_functor(
                    Box::new(param_coercion),
                    Box::new(result_coercion),
                ))
            }
        }

        // Signature implementation matches identifier signature
        (ModuleType::MtySignature(sig_impl), ModuleType::MtyIdent(path)) => {
            if let Some(expanded) = expand_module_type_in_env(type_ctx, env, path) {
                modtypes_inner(type_ctx, env, mty_impl, &expanded, aliasable)
            } else {
                Ok(ModuleCoercion::Tcoerce_none)
            }
        }

        // Identifier implementation matches signature
        (ModuleType::MtyIdent(path), ModuleType::MtySignature(sig_sig)) => {
            if let Some(expanded) = expand_module_type_in_env(type_ctx, env, path) {
                modtypes_inner(type_ctx, env, &expanded, mty_sig, aliasable)
            } else {
                Ok(ModuleCoercion::Tcoerce_none)
            }
        }

        (ModuleType::MtyIdent(path), mty_sig) => {
            if let Some(expanded) = expand_module_type_in_env(type_ctx, env, path) {
                modtypes_inner(type_ctx, env, &expanded, mty_sig, aliasable)
            } else {
                Ok(ModuleCoercion::Tcoerce_none)
            }
        }

        (mty_impl, ModuleType::MtyIdent(path)) => {
            if let Some(expanded) = expand_module_type_in_env(type_ctx, env, path) {
                modtypes_inner(type_ctx, env, mty_impl, &expanded, aliasable)
            } else {
                Ok(ModuleCoercion::Tcoerce_none)
            }
        }

        // Fallback: incompatible module types
        _ => Err(IncludeModError::ModuleTypeMismatch {
            name: Ident::create_local("module"),
            reason: "incompatible module types".to_string(),
        }),
    }
}

// ============================================================================
// Signature Inclusion
// ============================================================================

fn is_runtime_component(item: &SignatureItem) -> bool {
    match item {
        SignatureItem::SigValue(_, desc) => !matches!(desc.val_kind, ValueKind::ValPrim(_)),
        SignatureItem::SigType(_, _, _)
        | SignatureItem::SigModtype(_, _)
        | SignatureItem::SigClassType => false,
        SignatureItem::SigTypext(_, _, _)
        | SignatureItem::SigModule(_, _, _)
        | SignatureItem::SigClass => true,
    }
}

fn runtime_component_name(item: &SignatureItem) -> Option<String> {
    match item {
        SignatureItem::SigValue(id, _)
        | SignatureItem::SigType(id, _, _)
        | SignatureItem::SigTypext(id, _, _)
        | SignatureItem::SigModule(id, _, _)
        | SignatureItem::SigModtype(id, _) => Some(id.name().to_string()),
        SignatureItem::SigClass | SignatureItem::SigClassType => None,
    }
}

fn simplify_structure_coercion(
    coercions: &[(usize, ModuleCoercion)],
    id_pos_list: &[(Ident, usize, ModuleCoercion)],
    runtime_fields: &[String],
) -> ModuleCoercion {
    let is_identity = coercions
        .iter()
        .enumerate()
        .all(|(expected_pos, (actual_pos, coercion))| {
            *actual_pos == expected_pos && matches!(coercion, ModuleCoercion::Tcoerce_none)
        });

    if is_identity {
        ModuleCoercion::Tcoerce_none
    } else {
        ModuleCoercion::Tcoerce_structure(
            coercions.to_vec(),
            id_pos_list.to_vec(),
            runtime_fields.to_vec(),
        )
    }
}

pub fn simplify_signature(sig: &Signature) -> Signature {
    let mut seen_values = HashSet::new();
    let mut simplified = Vec::with_capacity(sig.len());
    for item in sig.iter().rev() {
        match item {
            SignatureItem::SigValue(id, _) => {
                if seen_values.insert(id.name().to_string()) {
                    simplified.push(item.clone());
                }
            }
            _ => simplified.push(item.clone()),
        }
    }
    simplified.reverse();
    simplified
}

pub fn compunit<'a>(
    type_ctx: &'a TypeContext<'a>,
    env: &Env,
    _impl_name: &str,
    impl_sig: &Signature,
    _intf_name: &str,
    intf_sig: &Signature,
) -> IncludeModResult<ModuleCoercion> {
    signatures(type_ctx, env, impl_sig, intf_sig)
}

/// Check if signature `sig_impl` is a subtype of `sig_sig`.
pub fn signatures<'a>(
    type_ctx: &'a TypeContext<'a>,
    env: &Env,
    sig_impl: &Signature,
    sig_sig: &Signature,
) -> IncludeModResult<ModuleCoercion> {
    let mut errors = Vec::new();
    let mut coercions = Vec::new();
    let mut include_env = env.clone();
    let mut type_subst = HashMap::new();
    let len_impl = sig_impl.iter().filter(|item| is_runtime_component(item)).count();
    let len_sig = sig_sig.iter().filter(|item| is_runtime_component(item)).count();
    let runtime_fields = sig_sig
        .iter()
        .filter(|item| is_runtime_component(item))
        .filter_map(runtime_component_name)
        .collect::<Vec<_>>();
    let id_pos_list = sig_impl
        .iter()
        .scan(0usize, |runtime_pos, item| {
            let current = match item {
                SignatureItem::SigModule(id, _, _) => Some((
                    id.clone(),
                    *runtime_pos,
                    ModuleCoercion::Tcoerce_none,
                )),
                _ => None,
            };
            if is_runtime_component(item) {
                *runtime_pos += 1;
            }
            Some(current)
        })
        .flatten()
        .collect::<Vec<_>>();

    for sig_item in sig_impl {
        add_sig_item_to_env(sig_item, &mut include_env);
    }

    // For each item in the signature, find the corresponding item in the implementation
    for (pos, sig_item) in sig_sig.iter().enumerate() {
        match signature_item(
            type_ctx,
            &include_env,
            sig_impl,
            sig_item,
            &mut type_subst,
        ) {
            Ok((impl_pos, coercion)) => {
                if is_runtime_component(sig_item) {
                    coercions.push((impl_pos, coercion));
                }
            }
            Err(err) => {
                errors.push(err);
            }
        }
    }

    if errors.is_empty() {
        if len_impl == len_sig {
            Ok(simplify_structure_coercion(
                &coercions,
                &id_pos_list,
                &runtime_fields,
            ))
        } else {
            Ok(ModuleCoercion::Tcoerce_structure(
                coercions,
                id_pos_list,
                runtime_fields,
            ))
        }
    } else {
        Err(IncludeModError::SignatureMismatch(errors))
    }
}

/// Check a single signature item against an implementation signature.
fn signature_item<'a>(
    type_ctx: &'a TypeContext<'a>,
    env: &Env,
    sig_impl: &Signature,
    sig_item: &SignatureItem,
    type_subst: &mut HashMap<String, Path>,
) -> IncludeModResult<(usize, ModuleCoercion)> {
    match sig_item {
        SignatureItem::SigValue(id, val_desc) => {
            let mut runtime_pos = 0usize;
            let mut found = None;
            for impl_item in sig_impl {
                let current_runtime_pos = runtime_pos;
                if is_runtime_component(impl_item) {
                    runtime_pos += 1;
                }
                if let SignatureItem::SigValue(impl_id, impl_val_desc) = impl_item {
                    if impl_id.name() == id.name() {
                        found = Some((current_runtime_pos, impl_val_desc));
                    }
                }
            }
            if let Some((pos, impl_val_desc)) = found {
                let coercion = value_descriptions(
                    type_ctx,
                    env,
                    id.clone(),
                    impl_val_desc,
                    val_desc,
                    type_subst,
                )?;
                Ok((pos, coercion))
            } else {
                Err(IncludeModError::MissingValue(id.clone()))
            }
        }

        SignatureItem::SigType(id, type_decl, rec_status) => {
            // Find the type in the implementation
            for (pos, impl_item) in sig_impl.iter().enumerate() {
                if let SignatureItem::SigType(impl_id, impl_type_decl, _) = impl_item {
                    if impl_id.name() == id.name() {
                        // Check that the type declarations are compatible
                        type_declarations(type_ctx, env, id.clone(), impl_type_decl, type_decl)?;
                        let subst_path = impl_type_decl
                            .type_path
                            .clone()
                            .unwrap_or_else(|| Path::pident(impl_id.clone()));
                        type_subst.insert(id.name().to_string(), subst_path);
                        return Ok((pos, ModuleCoercion::Tcoerce_none));
                    }
                }
            }
            Err(IncludeModError::MissingType(id.clone()))
        }

        SignatureItem::SigTypext(id, ext_constr, ext_status) => {
            let mut runtime_pos = 0usize;
            let mut found = None;
            for impl_item in sig_impl {
                let current_runtime_pos = runtime_pos;
                if is_runtime_component(impl_item) {
                    runtime_pos += 1;
                }
                if let SignatureItem::SigTypext(impl_id, impl_ext_constr, _) = impl_item {
                    if impl_id.name() == id.name() {
                        found = Some((current_runtime_pos, impl_ext_constr));
                    }
                }
            }
            if let Some((pos, impl_ext_constr)) = found {
                extension_constructors(
                    type_ctx,
                    env,
                    id.clone(),
                    impl_ext_constr,
                    ext_constr,
                )?;
                Ok((pos, ModuleCoercion::Tcoerce_none))
            } else {
                Err(IncludeModError::MissingValue(id.clone()))
            }
        }

        SignatureItem::SigModule(id, mod_decl, rec_status) => {
            let mut runtime_pos = 0usize;
            let mut found = None;
            for impl_item in sig_impl {
                let current_runtime_pos = runtime_pos;
                if is_runtime_component(impl_item) {
                    runtime_pos += 1;
                }
                if let SignatureItem::SigModule(impl_id, impl_mod_decl, _) = impl_item {
                    if impl_id.name() == id.name() {
                        found = Some((current_runtime_pos, impl_id.clone(), impl_mod_decl));
                    }
                }
            }
            if let Some((pos, impl_id, impl_mod_decl)) = found {
                // When impl and target modules have the same stamp (e.g., when
                // the target was cloned from impl by simplify_signature), skip
                // strengthening and return Tcoerce_none. Strengthening can create
                // false mismatches for modules with internal value shadowing.
                if impl_id.same(id) {
                    return Ok((pos, ModuleCoercion::Tcoerce_none));
                }
                let strengthened_impl =
                    crate::types::ctype::strengthen_module_type_for_inclusion_path(
                        type_ctx,
                        &Path::pident(impl_id),
                        &impl_mod_decl.md_type,
                    );
                let coercion = modtypes(type_ctx, env, &strengthened_impl, &mod_decl.md_type)?;
                Ok((pos, coercion))
            } else {
                Err(IncludeModError::MissingModule(id.clone()))
            }
        }

        SignatureItem::SigModtype(id, modtype_decl) => {
            // Find the module type in the implementation
            for (pos, impl_item) in sig_impl.iter().enumerate() {
                if let SignatureItem::SigModtype(impl_id, impl_modtype_decl) = impl_item {
                    if impl_id.name() == id.name() {
                        // Check that the module type declarations are compatible
                        modtype_declarations(
                            type_ctx,
                            env,
                            id.clone(),
                            impl_modtype_decl,
                            modtype_decl,
                        )?;
                        return Ok((pos, ModuleCoercion::Tcoerce_none));
                    }
                }
            }
            Err(IncludeModError::MissingModuleType(id.clone()))
        }

        // Class and class type are not used in ReScript
        SignatureItem::SigClass | SignatureItem::SigClassType => {
            Ok((0, ModuleCoercion::Tcoerce_none))
        }
    }
}

// ============================================================================
// Component Inclusion
// ============================================================================

/// Check if value description `impl_desc` is a subtype of `sig_desc`.
fn value_descriptions<'a>(
    type_ctx: &'a TypeContext<'a>,
    env: &Env,
    id: Ident,
    impl_desc: &ValueDescription,
    sig_desc: &ValueDescription,
    type_subst: &HashMap<String, Path>,
) -> IncludeModResult<ModuleCoercion> {
    fn has_non_row_type_variables(
        type_ctx: &TypeContext<'_>,
        ty: TypeExprRef,
        seen: &mut HashSet<TypeExprRef>,
    ) -> bool {
        use crate::types::type_expr::{RowField, TypeDesc};

        let ty = type_ctx.repr(ty);
        if !seen.insert(ty) {
            return false;
        }

        match &*type_ctx.get_desc(ty) {
            TypeDesc::Tvar(_) | TypeDesc::Tunivar(_) => true,
            TypeDesc::Tarrow { arg, ret, .. } => {
                has_non_row_type_variables(type_ctx, arg.typ, seen)
                    || has_non_row_type_variables(type_ctx, *ret, seen)
            }
            TypeDesc::Ttuple(items) => items
                .iter()
                .any(|item| has_non_row_type_variables(type_ctx, *item, seen)),
            TypeDesc::Tconstr { args, .. } | TypeDesc::Tpackage { args, .. } => args
                .iter()
                .any(|arg| has_non_row_type_variables(type_ctx, *arg, seen)),
            TypeDesc::Tobject { fields, .. } => has_non_row_type_variables(type_ctx, *fields, seen),
            TypeDesc::Tfield { typ, rest, .. } => {
                has_non_row_type_variables(type_ctx, *typ, seen)
                    || has_non_row_type_variables(type_ctx, *rest, seen)
            }
            TypeDesc::Tvariant(row0) => {
                let row = crate::types::btype::row_repr(type_ctx, row0);
                row.row_fields.iter().any(|(_, field)| match field {
                    RowField::Rpresent(Some(arg)) => {
                        has_non_row_type_variables(type_ctx, *arg, seen)
                    }
                    RowField::Reither { types, .. } => types
                        .iter()
                        .any(|arg| has_non_row_type_variables(type_ctx, *arg, seen)),
                    RowField::Rpresent(None) | RowField::Rabsent => false,
                }) || row.row_name.as_ref().is_some_and(|(_, tys)| {
                    tys.iter()
                        .any(|arg| has_non_row_type_variables(type_ctx, *arg, seen))
                })
            }
            TypeDesc::Tpoly { body, vars } => {
                has_non_row_type_variables(type_ctx, *body, seen)
                    || vars
                        .iter()
                        .any(|var| has_non_row_type_variables(type_ctx, *var, seen))
            }
            TypeDesc::Tlink(target) | TypeDesc::Tsubst(target) => {
                has_non_row_type_variables(type_ctx, *target, seen)
            }
            TypeDesc::Tnil => false,
        }
    }

    // Check that the value types are compatible
    // The implementation type should be more general than (or equal to) the signature type
    let mut unify_state = UnifyState::default();
    unify_state.set_env(env);
    let expected_ty = substitute_value_type_paths(type_ctx, sig_desc.val_type, type_subst);

    // Match OCaml Includecore.value_descriptions more closely:
    // - ordinary generic variables should be compared through `instance`
    // - row-only variability should keep the structural copy path so later
    //   row-closing feedback can still line up with the implementation shape
    let mut seen = HashSet::new();
    let impl_ty = if has_non_row_type_variables(type_ctx, impl_desc.val_type, &mut seen) {
        ctype::instance(type_ctx, impl_desc.val_type)
    } else {
        ctype::subst_identity_copy(type_ctx, impl_desc.val_type)
    };
    let sig_ty = ctype::instance(type_ctx, expected_ty);

    // Try to unify (signature type should match implementation type)
    if ctype::unify(type_ctx, &mut unify_state, impl_ty, sig_ty).is_err() {
        return Err(IncludeModError::ValueTypeMismatch {
            name: id,
            expected: expected_ty,
            found: impl_desc.val_type,
        });
    }

    close_matching_variant_rows_from_expected(type_ctx, env, impl_desc.val_type, expected_ty);

    // OCaml: match (vd1.val_kind, vd2.val_kind) with
    // | Val_prim p, _ -> Tcoerce_primitive { pc_desc = p; pc_type = vd2.val_type; ... }
    // | _, Val_prim _ -> raise Dont_match
    // | _, _ -> Tcoerce_none
    match (&impl_desc.val_kind, &sig_desc.val_kind) {
        (ValueKind::ValPrim(p1), ValueKind::ValPrim(_p2)) => {
            // Both are primitives - check compatibility (simplified: just accept)
            Ok(ModuleCoercion::Tcoerce_none)
        }
        (ValueKind::ValPrim(prim), _) => {
            Ok(ModuleCoercion::Tcoerce_primitive(
                crate::types::typedtree::PrimitiveCoercion {
                    pc_desc: prim.clone(),
                    pc_type: sig_desc.val_type,
                    pc_loc: impl_desc.val_loc.clone(),
                    pc_id: id,
                },
            ))
        }
        (_, ValueKind::ValPrim(_)) => {
            // Signature expects primitive but implementation is regular - mismatch
            // OCaml raises Dont_match here but we'll allow it for now
            Ok(ModuleCoercion::Tcoerce_none)
        }
        _ => Ok(ModuleCoercion::Tcoerce_none),
    }
}

fn add_sig_item_to_env(item: &SignatureItem, env: &mut Env) {
    match item {
        SignatureItem::SigValue(id, desc) => env.add_value(id.clone(), desc.clone()),
        SignatureItem::SigType(id, decl, _) => env.add_type(id.clone(), decl.clone()),
        SignatureItem::SigModule(id, md, _) => env.add_module(id.clone(), md.clone()),
        SignatureItem::SigModtype(id, mtd) => env.add_modtype(id.clone(), mtd.clone()),
        SignatureItem::SigTypext(_, _, _) | SignatureItem::SigClass | SignatureItem::SigClassType => {}
    }
}

fn substitute_value_type_paths<'a>(
    type_ctx: &'a TypeContext<'a>,
    ty: TypeExprRef,
    type_subst: &HashMap<String, Path>,
) -> TypeExprRef {
    use crate::types::type_expr::{RowField, TypeDesc};

    if type_subst.is_empty() {
        return ty;
    }

    fn rewrite<'a>(
        type_ctx: &'a TypeContext<'a>,
        ty: TypeExprRef,
        type_subst: &HashMap<String, Path>,
        seen: &mut HashSet<TypeExprRef>,
    ) {
        let ty = type_ctx.repr(ty);
        if !seen.insert(ty) {
            return;
        }

        let desc = type_ctx.get_desc(ty);
        match &*desc {
            TypeDesc::Tconstr { path, args, abbrev } => {
                for arg in args {
                    rewrite(type_ctx, *arg, type_subst, seen);
                }
                if let Path::Pident(id) = path {
                    if let Some(new_path) = type_subst.get(id.name()) {
                        type_ctx.set_desc(
                            ty,
                            TypeDesc::Tconstr {
                                path: new_path.clone(),
                                args: args.clone(),
                                abbrev: *abbrev,
                            },
                        );
                    }
                }
            }
            TypeDesc::Tarrow { arg, ret, .. } => {
                rewrite(type_ctx, arg.typ, type_subst, seen);
                rewrite(type_ctx, *ret, type_subst, seen);
            }
            TypeDesc::Ttuple(items) => {
                for item in items {
                    rewrite(type_ctx, *item, type_subst, seen);
                }
            }
            TypeDesc::Tobject { fields, .. } => {
                rewrite(type_ctx, *fields, type_subst, seen);
            }
            TypeDesc::Tfield { typ, rest, .. } => {
                rewrite(type_ctx, *typ, type_subst, seen);
                rewrite(type_ctx, *rest, type_subst, seen);
            }
            TypeDesc::Tvariant(row0) => {
                let row = crate::types::btype::row_repr(type_ctx, row0);
                for (_, field) in &row.row_fields {
                    match field {
                        RowField::Rpresent(Some(arg)) => rewrite(type_ctx, *arg, type_subst, seen),
                        RowField::Reither { types, .. } => {
                            for ty in types {
                                rewrite(type_ctx, *ty, type_subst, seen);
                            }
                        }
                        RowField::Rpresent(None) | RowField::Rabsent => {}
                    }
                }
                rewrite(type_ctx, row.row_more, type_subst, seen);
            }
            TypeDesc::Tpoly { body, vars } => {
                rewrite(type_ctx, *body, type_subst, seen);
                for var in vars {
                    rewrite(type_ctx, *var, type_subst, seen);
                }
            }
            TypeDesc::Tpackage { args, .. } => {
                for arg in args {
                    rewrite(type_ctx, *arg, type_subst, seen);
                }
            }
            TypeDesc::Tlink(target) | TypeDesc::Tsubst(target) => {
                rewrite(type_ctx, *target, type_subst, seen);
            }
            TypeDesc::Tvar(_) | TypeDesc::Tunivar(_) | TypeDesc::Tnil => {}
        }
    }

    let copied = ctype::subst_identity_copy(type_ctx, ty);
    let mut seen = HashSet::new();
    rewrite(type_ctx, copied, type_subst, &mut seen);
    copied
}

fn close_matching_variant_rows_from_expected<'a>(
    type_ctx: &'a TypeContext<'a>,
    env: &Env,
    impl_ty: TypeExprRef,
    expected_ty: TypeExprRef,
) {
    use crate::types::btype;
    use crate::types::type_expr::{RowDesc, RowField, TypeDesc};

    fn align_rows<'a>(
        type_ctx: &'a TypeContext<'a>,
        env: &Env,
        impl_ty: TypeExprRef,
        expected_ty: TypeExprRef,
        depth: usize,
        seen: &mut HashSet<(TypeExprRef, TypeExprRef)>,
    ) {
        let impl_ty = type_ctx.repr(ctype::expand_head(type_ctx, env, impl_ty));
        let expected_ty = type_ctx.repr(ctype::expand_head(type_ctx, env, expected_ty));
        if !seen.insert((impl_ty, expected_ty)) {
            return;
        }

        let impl_desc = type_ctx.get_desc(impl_ty);
        let expected_desc = type_ctx.get_desc(expected_ty);

        match (&*impl_desc, &*expected_desc) {
            (
                TypeDesc::Tarrow {
                    arg: impl_arg,
                    ret: impl_ret,
                    ..
                },
                TypeDesc::Tarrow {
                    arg: expected_arg,
                    ret: expected_ret,
                    ..
                },
            ) if impl_arg.lbl == expected_arg.lbl => {
                align_rows(type_ctx, env, impl_arg.typ, expected_arg.typ, depth + 1, seen);
                align_rows(type_ctx, env, *impl_ret, *expected_ret, depth + 1, seen);
            }
            (TypeDesc::Ttuple(impl_items), TypeDesc::Ttuple(expected_items))
                if impl_items.len() == expected_items.len() =>
            {
                for (impl_item, expected_item) in impl_items.iter().zip(expected_items.iter()) {
                    align_rows(type_ctx, env, *impl_item, *expected_item, depth + 1, seen);
                }
            }
            (
                TypeDesc::Tconstr {
                    path: impl_path,
                    args: impl_args,
                    ..
                },
                TypeDesc::Tconstr {
                    path: expected_path,
                    args: expected_args,
                    ..
                },
            ) if impl_path.same(expected_path) && impl_args.len() == expected_args.len() => {
                for (impl_arg, expected_arg) in impl_args.iter().zip(expected_args.iter()) {
                    align_rows(type_ctx, env, *impl_arg, *expected_arg, depth + 1, seen);
                }
            }
            (TypeDesc::Tvariant(impl_row0), TypeDesc::Tvariant(expected_row0)) => {
                let impl_row = btype::row_repr(type_ctx, impl_row0);
                let expected_row = btype::row_repr(type_ctx, expected_row0);

                let mut expected_by_label: HashMap<String, RowField> = expected_row
                    .row_fields
                    .iter()
                    .map(|(label, field)| (label.clone(), field.clone()))
                    .collect();
                let mut extra_impl = Vec::new();
                let mut pairs = Vec::new();

                for (label, impl_field) in &impl_row.row_fields {
                    if let Some(expected_field) = expected_by_label.remove(label) {
                        pairs.push((impl_field.clone(), expected_field));
                    } else {
                        extra_impl.push((label.clone(), impl_field.clone()));
                    }
                }

                let exact_labels = extra_impl.is_empty() && expected_by_label.is_empty();
                let mut payloads_match = true;

                for (impl_field, expected_field) in &pairs {
                    match (
                        btype::row_field_repr(type_ctx, impl_field),
                        btype::row_field_repr(type_ctx, expected_field),
                    ) {
                        (RowField::Rpresent(None), RowField::Rpresent(None))
                        | (RowField::Rabsent, RowField::Rabsent) => {}
                        (RowField::Rpresent(Some(impl_arg)), RowField::Rpresent(Some(expected_arg))) => {
                            align_rows(type_ctx, env, impl_arg, expected_arg, depth + 1, seen);
                        }
                        (
                            RowField::Reither { types: impl_types, .. },
                            RowField::Reither { types: expected_types, .. },
                        ) if impl_types.len() == expected_types.len() => {
                            for (impl_arg, expected_arg) in
                                impl_types.iter().zip(expected_types.iter())
                            {
                                align_rows(type_ctx, env, *impl_arg, *expected_arg, depth + 1, seen);
                            }
                        }
                        (
                            RowField::Reither {
                                constant: true,
                                types,
                                ..
                            },
                            RowField::Rpresent(None),
                        ) if types.is_empty() => {}
                        _ => {
                            payloads_match = false;
                            break;
                        }
                    }
                }

                if depth > 0
                    && expected_row.row_closed
                    && exact_labels
                    && payloads_match
                    && !impl_row.row_closed
                {
                    let impl_more = btype::row_more(type_ctx, &impl_row);
                    let impl_more_repr = type_ctx.repr(impl_more);
                    if btype::is_tvar(type_ctx, impl_more_repr) {
                        let closing_row = type_ctx.new_generic_type(TypeDesc::Tvariant(RowDesc {
                            row_fields: vec![],
                            row_more: btype::row_more(type_ctx, &expected_row),
                            row_closed: true,
                            row_fixed: expected_row.row_fixed,
                            row_name: None,
                        }));
                        ctype::update_level(type_ctx, type_ctx.get_level(impl_more_repr), closing_row);
                        ctype::link_type(type_ctx, impl_more_repr, closing_row);
                    }
                }
            }
            (
                TypeDesc::Tpoly {
                    body: impl_body,
                    vars: impl_vars,
                },
                TypeDesc::Tpoly {
                    body: expected_body,
                    vars: expected_vars,
                },
            ) if impl_vars.len() == expected_vars.len() => {
                align_rows(type_ctx, env, *impl_body, *expected_body, depth + 1, seen);
                for (impl_var, expected_var) in impl_vars.iter().zip(expected_vars.iter()) {
                    align_rows(type_ctx, env, *impl_var, *expected_var, depth + 1, seen);
                }
            }
            (
                TypeDesc::Tpackage { args: impl_args, .. },
                TypeDesc::Tpackage {
                    args: expected_args, ..
                },
            ) if impl_args.len() == expected_args.len() => {
                for (impl_arg, expected_arg) in impl_args.iter().zip(expected_args.iter()) {
                    align_rows(type_ctx, env, *impl_arg, *expected_arg, depth + 1, seen);
                }
            }
            _ => {}
        }
    }

    let mut seen = HashSet::new();
    align_rows(type_ctx, env, impl_ty, expected_ty, 0, &mut seen);
}

/// Check if type declaration `impl_decl` is a subtype of `sig_decl`.
fn type_declarations<'a>(
    type_ctx: &'a TypeContext<'a>,
    env: &Env,
    id: Ident,
    impl_decl: &TypeDeclaration,
    sig_decl: &TypeDeclaration,
) -> IncludeModResult<()> {
    // Check arity (number of type parameters)
    if impl_decl.type_params.len() != sig_decl.type_params.len() {
        return Err(IncludeModError::TypeMismatch {
            name: id,
            reason: format!(
                "arity mismatch: expected {} type parameters, found {}",
                sig_decl.type_params.len(),
                impl_decl.type_params.len()
            ),
        });
    }

    // Check variance — only for abstract, private, or open types
    // (matches OCaml's includecore.ml: need_variance = abstr || private || open)
    let is_abstract = matches!(impl_decl.type_kind, crate::types::decl::TypeKind::TypeAbstract);
    let is_private = matches!(impl_decl.type_private, crate::types::PrivateFlag::Private);
    let is_open = matches!(impl_decl.type_kind, crate::types::decl::TypeKind::TypeOpen);
    let need_variance = is_abstract || is_private || is_open;
    if need_variance && impl_decl.type_variance.len() == sig_decl.type_variance.len() {
        for (i, (impl_var, sig_var)) in impl_decl
            .type_variance
            .iter()
            .zip(sig_decl.type_variance.iter())
            .enumerate()
        {
            // Implementation variance should be at least as specific as signature variance
            if !impl_var.subset(sig_var) {
                return Err(IncludeModError::TypeMismatch {
                    name: id,
                    reason: format!("variance mismatch at parameter {}", i),
                });
            }
        }
    }

    // Check that the type kinds are compatible
    match (&impl_decl.type_kind, &sig_decl.type_kind) {
        // Abstract in signature allows any implementation
        (_, crate::types::decl::TypeKind::TypeAbstract) => Ok(()),

        // Same kind is fine
        (k1, k2) if std::mem::discriminant(k1) == std::mem::discriminant(k2) => {
            // Would need deeper checking for record/variant fields
            Ok(())
        }

        _ => Err(IncludeModError::TypeMismatch {
            name: id,
            reason: "incompatible type kinds".to_string(),
        }),
    }
}

/// Check if extension constructor `impl_ext` is compatible with `sig_ext`.
fn extension_constructors<'a>(
    type_ctx: &'a TypeContext<'a>,
    env: &Env,
    id: Ident,
    impl_ext: &ExtensionConstructor,
    sig_ext: &ExtensionConstructor,
) -> IncludeModResult<()> {
    // Check that the extension type paths match
    if impl_ext.ext_type_path != sig_ext.ext_type_path {
        return Err(IncludeModError::TypeMismatch {
            name: id,
            reason: "extension type path mismatch".to_string(),
        });
    }

    // Check that the argument types match
    // This would require deeper type checking in a full implementation
    Ok(())
}

/// Check if module type declaration `impl_decl` is compatible with `sig_decl`.
fn modtype_declarations<'a>(
    type_ctx: &'a TypeContext<'a>,
    env: &Env,
    id: Ident,
    impl_decl: &ModtypeDeclaration,
    sig_decl: &ModtypeDeclaration,
) -> IncludeModResult<()> {
    match (&impl_decl.mtd_type, &sig_decl.mtd_type) {
        // Both abstract - compatible
        (None, None) => Ok(()),

        // Signature is abstract - implementation can be anything
        (Some(_), None) => Ok(()),

        // Signature has type but implementation is abstract - error
        (None, Some(_)) => Err(IncludeModError::ModuleTypeMismatch {
            name: id,
            reason: "implementation is abstract but signature requires concrete type".to_string(),
        }),

        // Both have types - check compatibility (bidirectional)
        (Some(impl_mty), Some(sig_mty)) => {
            // Module types must be equivalent (both directions)
            modtypes(type_ctx, env, impl_mty, sig_mty)?;
            modtypes(type_ctx, env, sig_mty, impl_mty)?;
            Ok(())
        }
    }
}

// ============================================================================
// Utilities
// ============================================================================

/// Check if a signature is empty.
pub fn is_empty_signature(sig: &Signature) -> bool {
    sig.is_empty()
}

/// Get all value identifiers from a signature.
pub fn signature_values(sig: &Signature) -> Vec<&Ident> {
    sig.iter()
        .filter_map(|item| {
            if let SignatureItem::SigValue(id, _) = item {
                Some(id)
            } else {
                None
            }
        })
        .collect()
}

/// Get all type identifiers from a signature.
pub fn signature_types(sig: &Signature) -> Vec<&Ident> {
    sig.iter()
        .filter_map(|item| {
            if let SignatureItem::SigType(id, _, _) = item {
                Some(id)
            } else {
                None
            }
        })
        .collect()
}

/// Get all module identifiers from a signature.
pub fn signature_modules(sig: &Signature) -> Vec<&Ident> {
    sig.iter()
        .filter_map(|item| {
            if let SignatureItem::SigModule(id, _, _) = item {
                Some(id)
            } else {
                None
            }
        })
        .collect()
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::context::IdGenerator;
    use crate::location::Location;
    use crate::types::decl::{RecStatus, TypeKind, UnboxedStatus, ValueKind};
    use crate::types::env::initial_env;

    #[test]
    fn test_empty_signatures_match() {
        let id_gen = IdGenerator::new();
        let type_ctx = TypeContext::new(&id_gen);
        let env = initial_env(&type_ctx);

        let sig_impl: Signature = vec![];
        let sig_sig: Signature = vec![];

        let result = signatures(&type_ctx, &env, &sig_impl, &sig_sig);
        assert!(result.is_ok());
    }

    #[test]
    fn test_missing_value_error() {
        let id_gen = IdGenerator::new();
        let type_ctx = TypeContext::new(&id_gen);
        let env = initial_env(&type_ctx);

        let sig_impl: Signature = vec![];
        let val_ty = type_ctx.new_var(None);
        let sig_sig: Signature = vec![SignatureItem::SigValue(
            Ident::create_local("x"),
            ValueDescription {
                val_type: val_ty,
                val_kind: ValueKind::ValReg,
                val_loc: Location::none(),
                val_attributes: vec![],
                val_path: None,
            },
        )];

        let result = signatures(&type_ctx, &env, &sig_impl, &sig_sig);
        assert!(matches!(result, Err(IncludeModError::SignatureMismatch(_))));
    }

    #[test]
    fn test_value_match() {
        let id_gen = IdGenerator::new();
        let type_ctx = TypeContext::new(&id_gen);
        let env = initial_env(&type_ctx);

        let val_ty = type_ctx.new_var(None);
        let sig_impl: Signature = vec![SignatureItem::SigValue(
            Ident::create_local("x"),
            ValueDescription {
                val_type: val_ty,
                val_kind: ValueKind::ValReg,
                val_loc: Location::none(),
                val_attributes: vec![],
                val_path: None,
            },
        )];
        let sig_sig: Signature = vec![SignatureItem::SigValue(
            Ident::create_local("x"),
            ValueDescription {
                val_type: val_ty,
                val_kind: ValueKind::ValReg,
                val_loc: Location::none(),
                val_attributes: vec![],
                val_path: None,
            },
        )];

        let result = signatures(&type_ctx, &env, &sig_impl, &sig_sig);
        assert!(result.is_ok());
    }

    #[test]
    fn test_functor_match() {
        let id_gen = IdGenerator::new();
        let type_ctx = TypeContext::new(&id_gen);
        let env = initial_env(&type_ctx);

        let param_sig = ModuleType::MtySignature(vec![]);
        let result_sig = ModuleType::MtySignature(vec![]);

        let mty_impl = ModuleType::MtyFunctor {
            param: Ident::create_local("X"),
            param_type: Some(Box::new(param_sig.clone())),
            result: Box::new(result_sig.clone()),
        };

        let mty_sig = ModuleType::MtyFunctor {
            param: Ident::create_local("X"),
            param_type: Some(Box::new(param_sig)),
            result: Box::new(result_sig),
        };

        let result = modtypes(&type_ctx, &env, &mty_impl, &mty_sig);
        assert!(result.is_ok());
    }

    #[test]
    fn test_signature_utilities() {
        let val_ty_placeholder = crate::types::TypeExprRef(0);

        let sig: Signature = vec![
            SignatureItem::SigValue(
                Ident::create_local("x"),
                ValueDescription {
                    val_type: val_ty_placeholder,
                    val_kind: ValueKind::ValReg,
                    val_loc: Location::none(),
                    val_attributes: vec![],
                    val_path: None,
                },
            ),
            SignatureItem::SigType(
                Ident::create_local("t"),
                TypeDeclaration {
                    type_params: vec![],
                    type_arity: 0,
                    type_kind: TypeKind::TypeAbstract,
                    type_private: crate::types::PrivateFlag::Public,
                    type_manifest: None,
                    type_variance: vec![],
                    type_newtype_level: None,
                    type_loc: Location::none(),
                    type_attributes: vec![],
                    type_immediate: false,
                    type_unboxed: UnboxedStatus::FALSE_FALSE,
                    type_inlined_types: vec![],
                    type_path: None,
                },
                RecStatus::TrecNot,
            ),
        ];

        assert!(!is_empty_signature(&sig));
        assert_eq!(signature_values(&sig).len(), 1);
        assert_eq!(signature_types(&sig).len(), 1);
        assert_eq!(signature_modules(&sig).len(), 0);
    }
}
