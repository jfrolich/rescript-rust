//! Basic type operations.
//!
//! This module provides fundamental operations on types that are used
//! throughout the type checker. It includes:
//!
//! - Type representative (union-find with path compression)
//! - Type traversal utilities
//! - Row field operations
//! - Type copying utilities
//!
//! These operations are the building blocks for more complex type
//! operations like unification and generalization.

use super::context::TypeContext;
use super::decl::{ConstructorArguments, TypeKind};
use super::path::Path;
use super::type_expr::{
    AbbrevMemo, AbbrevMemoRef, GENERIC_LEVEL, LOWEST_LEVEL, PIVOT_LEVEL, RowDesc, RowField,
    RowFieldRef, TypeDesc, TypeExprRef,
};
use std::borrow::Cow;

// ============================================================================
// Type Level Constants
// ============================================================================

/// Check if a type is at the generic level.
pub fn is_generic(ctx: &TypeContext, t: TypeExprRef) -> bool {
    ctx.get_level(t) == GENERIC_LEVEL
}

/// Check if a type's level is >= lowest_level (not marked).
pub fn is_unmarked(ctx: &TypeContext, t: TypeExprRef) -> bool {
    ctx.get_level(t) >= LOWEST_LEVEL
}

// ============================================================================
// Type Predicates
// ============================================================================

/// Check if a type is a type variable (Tvar).
pub fn is_tvar(ctx: &TypeContext, t: TypeExprRef) -> bool {
    let t = ctx.repr(t);
    matches!(*ctx.borrow_desc(t), TypeDesc::Tvar(_))
}

/// Check if a type is a universal type variable (Tunivar).
pub fn is_tunivar(ctx: &TypeContext, t: TypeExprRef) -> bool {
    let t = ctx.repr(t);
    matches!(*ctx.borrow_desc(t), TypeDesc::Tunivar(_))
}

/// Check if a type is a type constructor (Tconstr).
pub fn is_tconstr(ctx: &TypeContext, t: TypeExprRef) -> bool {
    let t = ctx.repr(t);
    matches!(*ctx.borrow_desc(t), TypeDesc::Tconstr { .. })
}

// ============================================================================
// Row Field Operations
// ============================================================================

/// Get the representative of a row field.
///
/// This follows the `link` chain in `Reither` fields.
pub fn row_field_repr(ctx: &TypeContext, field: &RowField) -> RowField {
    row_field_repr_aux(ctx, &[], field)
}

pub fn row_field_is_absent(ctx: &TypeContext, field: &RowField) -> bool {
    match field {
        RowField::Reither { link, .. } => ctx
            .get_row_field(*link)
            .is_some_and(|linked| row_field_is_absent(ctx, &linked)),
        RowField::Rabsent => true,
        _ => false,
    }
}

pub fn row_field_is_reither(ctx: &TypeContext, field: &RowField) -> bool {
    match field {
        RowField::Reither { link, .. } => ctx
            .get_row_field(*link)
            .map_or(true, |linked| row_field_is_reither(ctx, &linked)),
        _ => false,
    }
}

pub fn row_field_unmatched_reither_link(
    ctx: &TypeContext,
    field: &RowField,
) -> Option<RowFieldRef> {
    match field {
        RowField::Reither { matched, link, .. } => match ctx.get_row_field(*link) {
            Some(linked) => row_field_unmatched_reither_link(ctx, &linked),
            None if !*matched => Some(*link),
            None => None,
        },
        _ => None,
    }
}

fn row_field_repr_aux(ctx: &TypeContext, tl: &[TypeExprRef], field: &RowField) -> RowField {
    match field {
        RowField::Reither {
            constant,
            types,
            matched,
            link,
        } => {
            // Follow link if set (like OCaml's {contents = Some fi} pattern)
            if let Some(linked) = ctx.get_row_field(*link) {
                let mut combined = tl.to_vec();
                combined.extend(types.iter().copied());
                return row_field_repr_aux(ctx, &combined, &linked);
            }
            let mut combined_types = tl.to_vec();
            combined_types.extend(types.iter().copied());
            RowField::Reither {
                constant: *constant,
                types: combined_types,
                matched: *matched,
                link: *link,
            }
        }
        RowField::Rpresent(Some(_)) if !tl.is_empty() => RowField::Rpresent(Some(tl[0])),
        other => other.clone(),
    }
}

/// Get the "more" type variable from a row.
///
/// This follows variant type chains to find the underlying type variable.
pub fn row_more(ctx: &TypeContext, row: &RowDesc) -> TypeExprRef {
    let more = ctx.repr(row.row_more);
    match &*ctx.borrow_desc(more) {
        TypeDesc::Tvariant(inner_row) => row_more(ctx, inner_row),
        _ => more,
    }
}

/// Get the row representative.
///
/// Flattens nested variant rows by combining their fields.
pub fn row_repr(ctx: &TypeContext, row: &RowDesc) -> RowDesc {
    row_repr_aux(ctx, &[], row)
}

pub fn row_repr_ref<'row>(ctx: &TypeContext, row: &'row RowDesc) -> Cow<'row, RowDesc> {
    let more = ctx.repr(row.row_more);
    let desc = ctx.borrow_desc(more);
    if matches!(&*desc, TypeDesc::Tvariant(_)) {
        drop(desc);
        Cow::Owned(row_repr(ctx, row))
    } else {
        Cow::Borrowed(row)
    }
}

fn row_repr_aux(
    ctx: &TypeContext,
    ll: &[super::decl::SharedVec<(crate::types::asttypes::Label, RowField)>],
    row: &RowDesc,
) -> RowDesc {
    // OCaml btype.ml `row_repr_aux`: follow `row_more` through nested
    // `Tvariant`s, prepending each non-empty field list to `ll`, then return
    // `rev_concat row.row_fields ll`. Collect the lists outermost first
    // instead of re-prepending, which yields the same concatenation order.
    let mut outer: Vec<super::decl::SharedVec<(crate::types::asttypes::Label, RowField)>> =
        ll.iter().rev().cloned().collect();
    let mut current = row.clone();
    loop {
        let more = ctx.repr(current.row_more);
        let inner = match &*ctx.borrow_desc(more) {
            TypeDesc::Tvariant(inner_row) => Some(inner_row.clone()),
            _ => None,
        };
        match inner {
            Some(inner_row) => {
                if !current.row_fields.is_empty() {
                    outer.push(current.row_fields.clone());
                }
                current = *inner_row;
            }
            None => break,
        }
    }
    if outer.is_empty() {
        return current;
    }
    let mut combined_fields = Vec::new();
    for fields in &outer {
        combined_fields.extend(fields.iter().cloned());
    }
    combined_fields.extend(current.row_fields.iter().cloned());
    RowDesc {
        row_fields: combined_fields.into(),
        row_more: current.row_more,
        row_closed: current.row_closed,
        row_fixed: current.row_fixed,
        row_name: current.row_name,
    }
}

/// Get a specific field from a row by its tag.
pub fn row_field(ctx: &TypeContext, tag: &str, row: &RowDesc) -> RowField {
    // First check the current row's fields
    for (field_tag, field) in &row.row_fields {
        if field_tag == tag {
            return row_field_repr(ctx, field);
        }
    }

    // Check nested variant
    let more = ctx.repr(row.row_more);
    match &*ctx.borrow_desc(more) {
        TypeDesc::Tvariant(inner_row) => row_field(ctx, tag, inner_row),
        _ => RowField::Rabsent,
    }
}

/// Check if a row is fixed.
pub fn row_fixed(ctx: &TypeContext, row: &RowDesc) -> bool {
    if row.row_fixed {
        return true;
    }

    let more = ctx.repr(row.row_more);
    match &*ctx.borrow_desc(more) {
        TypeDesc::Tvariant(inner_row) => row_fixed(ctx, inner_row),
        TypeDesc::Tvar(_) | TypeDesc::Tnil => false,
        TypeDesc::Tunivar(_) | TypeDesc::Tconstr { .. } => true,
        _ => false,
    }
}

/// Check if a row is static (closed with no Reither fields).
pub fn static_row(ctx: &TypeContext, row: &RowDesc) -> bool {
    let row = row_repr_ref(ctx, row);
    row.row_closed
        && row
            .row_fields
            .iter()
            .all(|(_, f)| !row_field_is_reither(ctx, f))
}

// ============================================================================
// Type Traversal
// ============================================================================

/// Iterate over all type expressions in a row.
pub fn iter_row<F>(ctx: &TypeContext, row: &RowDesc, mut f: F)
where
    F: FnMut(TypeExprRef),
{
    for (_, field) in &row.row_fields {
        match row_field_repr(ctx, field) {
            RowField::Rpresent(Some(ty)) => f(ty),
            RowField::Reither { types, .. } => {
                for ty in types {
                    f(ty);
                }
            }
            _ => {}
        }
    }

    enum MoreAction {
        Variant(RowDesc),
        RowNameTypes,
        None,
    }

    let more = ctx.repr(row.row_more);
    let action = {
        let desc = ctx.borrow_desc(more);
        match &*desc {
            TypeDesc::Tvariant(inner_row) => MoreAction::Variant(*inner_row.clone()),
            TypeDesc::Tvar(_)
            | TypeDesc::Tunivar(_)
            | TypeDesc::Tsubst(_)
            | TypeDesc::Tconstr { .. }
            | TypeDesc::Tnil => MoreAction::RowNameTypes,
            _ => MoreAction::None,
        }
    };

    match action {
        MoreAction::Variant(inner_row) => iter_row(ctx, &inner_row, f),
        MoreAction::RowNameTypes => {
            if let Some((_, types)) = &row.row_name {
                for ty in types {
                    f(*ty);
                }
            }
        }
        MoreAction::None => {}
    }
}

/// Iterate over all immediate child type expressions.
pub fn iter_type_expr<F>(ctx: &TypeContext, ty: TypeExprRef, mut f: F)
where
    F: FnMut(TypeExprRef),
{
    // Extract children first, then process them
    enum Children {
        None,
        One(TypeExprRef),
        Two(TypeExprRef, TypeExprRef),
        Many(smallvec::SmallVec<[TypeExprRef; 8]>),
        Variant(RowDesc, TypeExprRef),
        Poly(TypeExprRef, smallvec::SmallVec<[TypeExprRef; 8]>),
    }

    let children = {
        let desc = ctx.borrow_desc(ty);
        match &*desc {
            TypeDesc::Tvar(_) => Children::None,
            // compiler/ml/btype.ml:258-260 visits every n-ary parameter, then the return.
            TypeDesc::Tarrow { args, ret } => {
                let mut children = args
                    .iter()
                    .map(|arg| arg.typ)
                    .collect::<smallvec::SmallVec<[TypeExprRef; 8]>>();
                children.push(*ret);
                Children::Many(children)
            }
            TypeDesc::Ttuple(types) => Children::Many(types.iter().copied().collect()),
            TypeDesc::Tconstr { args, .. } => Children::Many(args.iter().copied().collect()),
            TypeDesc::Tobject { fields } => Children::One(*fields),
            TypeDesc::Tvariant(row) => {
                let row_clone = row.clone();
                let more = row.row_more;
                Children::Variant(*row_clone, more)
            }
            TypeDesc::Tfield { typ, rest, .. } => Children::Two(*typ, *rest),
            TypeDesc::Tnil => Children::None,
            TypeDesc::Tlink(t) => Children::One(*t),
            TypeDesc::Tsubst(t) => Children::One(*t),
            TypeDesc::Tunivar(_) => Children::None,
            TypeDesc::Tpoly { body, vars } => Children::Poly(*body, vars.iter().copied().collect()),
            TypeDesc::Tpackage { args, .. } => Children::Many(args.iter().copied().collect()),
        }
    };

    // Now process children without holding the borrow
    match children {
        Children::None => {}
        Children::One(t) => f(t),
        Children::Two(t1, t2) => {
            f(t1);
            f(t2);
        }
        Children::Many(types) => {
            for t in types {
                f(t);
            }
        }
        Children::Variant(row, _more) => {
            iter_row(ctx, &row, &mut f);
            f(row_more(ctx, &row));
        }
        Children::Poly(body, vars) => {
            f(body);
            for v in vars {
                f(v);
            }
        }
    }
}

/// Iterate over abbreviation memo.
pub fn iter_abbrev<F>(ctx: &TypeContext, memo: AbbrevMemoRef, f: F)
where
    F: FnMut(TypeExprRef),
{
    let mut current = memo;
    let mut f = f;
    for _ in 0..256 {
        match ctx.get_abbrev_memo(current) {
            AbbrevMemo::Mnil => return,
            AbbrevMemo::Mcons {
                abbrev,
                expansion,
                next,
                ..
            } => {
                f(abbrev);
                f(expansion);
                current = next;
            }
            AbbrevMemo::Mlink(next) => {
                current = next;
            }
        }
    }
}

// ============================================================================
// Type Kind Traversal
// ============================================================================

/// Iterate over constructor arguments.
pub fn iter_type_expr_cstr_args<F>(args: &ConstructorArguments, mut f: F)
where
    F: FnMut(TypeExprRef),
{
    match args {
        ConstructorArguments::CstrTuple(types) => {
            for t in types {
                f(*t);
            }
        }
        ConstructorArguments::CstrRecord(labels) => {
            for label in labels {
                f(label.ld_type);
            }
        }
    }
}

/// Iterate over type kind.
pub fn iter_type_expr_kind<F>(kind: &TypeKind, mut f: F)
where
    F: FnMut(TypeExprRef),
{
    match kind {
        TypeKind::TypeAbstract => {}
        TypeKind::TypeVariant(constructors, _) => {
            for cstr in constructors {
                iter_type_expr_cstr_args(&cstr.cd_args, &mut f);
                if let Some(res) = cstr.cd_res {
                    f(res);
                }
            }
        }
        TypeKind::TypeRecord(labels, _) => {
            for label in labels {
                f(label.ld_type);
            }
        }
        TypeKind::TypeOpen => {}
    }
}

// ============================================================================
// Type Marking (for traversal)
// ============================================================================

/// Mark a type by negating its level around pivot_level.
pub fn mark_type(ctx: &TypeContext, ty: TypeExprRef) {
    let ty = ctx.repr(ty);
    let level = ctx.get_level(ty);
    if level >= LOWEST_LEVEL {
        ctx.set_level(ty, PIVOT_LEVEL - level);
        iter_type_expr(ctx, ty, |t| mark_type(ctx, t));
    }
}

/// Mark just the type node (not its children).
pub fn mark_type_node(ctx: &TypeContext, ty: TypeExprRef) {
    let ty = ctx.repr(ty);
    let level = ctx.get_level(ty);
    if level >= LOWEST_LEVEL {
        ctx.set_level(ty, PIVOT_LEVEL - level);
    }
}

/// Mark type parameters (children only).
pub fn mark_type_params(ctx: &TypeContext, ty: TypeExprRef) {
    iter_type_expr(ctx, ty, |t| mark_type(ctx, t));
}

/// Unmark a type by reversing the mark operation.
pub fn unmark_type(ctx: &TypeContext, ty: TypeExprRef) {
    let ty = ctx.repr(ty);
    let level = ctx.get_level(ty);
    if level < LOWEST_LEVEL {
        ctx.set_level(ty, PIVOT_LEVEL - level);
        iter_type_expr(ctx, ty, |t| unmark_type(ctx, t));
    }
}

// ============================================================================
// Proxy and Row Utilities
// ============================================================================

/// Get the proxy for a type (used for object types).
pub fn proxy(ctx: &TypeContext, ty: TypeExprRef) -> TypeExprRef {
    let ty0 = ctx.repr(ty);

    // Extract what we need in a separate scope
    enum ProxyAction {
        VariantRow(RowDesc),
        ObjectFields(TypeExprRef),
        Return,
    }

    let action = {
        let desc = ctx.borrow_desc(ty0);
        match &*desc {
            TypeDesc::Tvariant(row) => {
                // Clone the row to check static_row outside the borrow
                ProxyAction::VariantRow(*row.clone())
            }
            TypeDesc::Tobject { fields, .. } => ProxyAction::ObjectFields(*fields),
            _ => ProxyAction::Return,
        }
    };

    match action {
        ProxyAction::VariantRow(row) => {
            if !static_row(ctx, &row) {
                row_more(ctx, &row)
            } else {
                ty0
            }
        }
        ProxyAction::ObjectFields(fields) => proxy_obj(ctx, fields, ty0),
        ProxyAction::Return => ty0,
    }
}

fn proxy_obj(ctx: &TypeContext, ty: TypeExprRef, original: TypeExprRef) -> TypeExprRef {
    let desc = ctx.borrow_desc(ty);
    match &*desc {
        TypeDesc::Tfield { rest, .. } => {
            let rest = *rest;
            drop(desc);
            proxy_obj(ctx, rest, original)
        }
        TypeDesc::Tlink(t) => {
            let t = *t;
            drop(desc);
            proxy_obj(ctx, t, original)
        }
        TypeDesc::Tvar(_) | TypeDesc::Tunivar(_) | TypeDesc::Tconstr { .. } => ty,
        TypeDesc::Tnil => original,
        _ => original,
    }
}

/// Get the row type from a type.
pub fn row_of_type(ctx: &TypeContext, t: TypeExprRef) -> TypeExprRef {
    let t = ctx.repr(t);

    // Extract what we need in a separate scope
    enum RowAction {
        ObjectFields(TypeExprRef),
        VariantRow(RowDesc),
        Return,
    }

    let action = {
        let desc = ctx.borrow_desc(t);
        match &*desc {
            TypeDesc::Tobject { fields, .. } => RowAction::ObjectFields(*fields),
            TypeDesc::Tvariant(row) => RowAction::VariantRow(*row.clone()),
            _ => RowAction::Return,
        }
    };

    match action {
        RowAction::ObjectFields(fields) => get_row(ctx, fields),
        RowAction::VariantRow(row) => row_more(ctx, &row),
        RowAction::Return => t,
    }
}

fn get_row(ctx: &TypeContext, t: TypeExprRef) -> TypeExprRef {
    let t = ctx.repr(t);
    let desc = ctx.borrow_desc(t);
    match &*desc {
        TypeDesc::Tfield { rest, .. } => {
            let rest = *rest;
            drop(desc);
            get_row(ctx, rest)
        }
        _ => t,
    }
}

/// Check if a type has a constructor row.
pub fn has_constr_row(ctx: &TypeContext, t: TypeExprRef) -> bool {
    !is_tconstr(ctx, t) && is_tconstr(ctx, row_of_type(ctx, t))
}

/// Check if a string is a row name (ends with "#row").
pub fn is_row_name(s: &str) -> bool {
    s.len() >= 4 && s.ends_with("#row")
}

/// Check if a type is a constructor row type.
pub fn is_constr_row(ctx: &TypeContext, t: TypeExprRef, allow_ident: bool) -> bool {
    let desc = ctx.borrow_desc(t);
    match &*desc {
        TypeDesc::Tconstr { path, .. } => match path {
            Path::Pident(id) if allow_ident => is_row_name(id.name()),
            Path::Pdot(_, s, _) => is_row_name(s),
            _ => false,
        },
        _ => false,
    }
}

// ============================================================================
// Hash Variant
// ============================================================================

/// Hash a variant tag name to an integer.
///
/// This is used for polymorphic variant tag representation.
pub fn hash_variant(s: &str) -> i32 {
    let mut accu: u32 = 0;
    // Iterate over characters and use their Latin-1 byte values (lower 8 bits).
    // OCaml strings are byte sequences, and multi-byte UTF-8 chars get stored as
    // individual Latin-1 codepoints (one char per original byte). Using .chars()
    // and masking to u8 correctly handles both ASCII and Latin-1-encoded labels.
    for c in s.chars() {
        accu = accu.wrapping_mul(223).wrapping_add((c as u32) & 0xFF);
    }
    // Reduce to 31 bits
    accu &= (1 << 31) - 1;
    // Make it signed for 64-bit architectures
    if accu > 0x3FFFFFFF {
        (accu as i64 - (1_i64 << 31)) as i32
    } else {
        accu as i32
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::context::IdGenerator;

    #[test]
    fn test_is_tvar() {
        let id_gen = IdGenerator::new();
        let ctx = TypeContext::new(std::sync::Arc::new(id_gen));

        let tvar = ctx.new_var(Some("a".to_string()));
        assert!(is_tvar(&ctx, tvar));

        let tuple = ctx.new_tuple(vec![tvar]);
        assert!(!is_tvar(&ctx, tuple));
    }

    #[test]
    fn test_hash_variant() {
        // Test some known hash values
        assert_eq!(hash_variant("None"), 870530776);
        assert_eq!(hash_variant("Some"), 925978388);

        // Hash should be deterministic
        assert_eq!(hash_variant("foo"), hash_variant("foo"));

        // Different strings should have different hashes (usually)
        assert_ne!(hash_variant("foo"), hash_variant("bar"));
    }

    #[test]
    fn test_is_row_name() {
        assert!(is_row_name("foo#row"));
        assert!(is_row_name("#row"));
        assert!(!is_row_name("row"));
        assert!(!is_row_name("foo"));
        assert!(!is_row_name(""));
    }

    #[test]
    fn test_mark_unmark() {
        let id_gen = IdGenerator::new();
        let ctx = TypeContext::new(std::sync::Arc::new(id_gen));

        let tvar = ctx.new_var(None);
        let original_level = ctx.get_level(tvar);

        mark_type_node(&ctx, tvar);
        assert!(ctx.get_level(tvar) < LOWEST_LEVEL);

        unmark_type(&ctx, tvar);
        assert_eq!(ctx.get_level(tvar), original_level);
    }

    #[test]
    fn test_iter_type_expr_tuple() {
        let id_gen = IdGenerator::new();
        let ctx = TypeContext::new(std::sync::Arc::new(id_gen));

        let t1 = ctx.new_var(None);
        let t2 = ctx.new_var(None);
        let tuple = ctx.new_tuple(vec![t1, t2]);

        let mut visited = Vec::new();
        iter_type_expr(&ctx, tuple, |t| visited.push(t));

        assert_eq!(visited.len(), 2);
        assert!(visited.contains(&t1));
        assert!(visited.contains(&t2));
    }

    #[test]
    fn test_iter_type_expr_arrow() {
        let id_gen = IdGenerator::new();
        let ctx = TypeContext::new(std::sync::Arc::new(id_gen));

        let t1 = ctx.new_var(None);
        let t2 = ctx.new_var(None);
        let arrow = ctx.new_arrow_simple(t1, t2);

        let mut visited = Vec::new();
        iter_type_expr(&ctx, arrow, |t| visited.push(t));

        assert_eq!(visited.len(), 2);
    }
}
