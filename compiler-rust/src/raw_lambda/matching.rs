//! Pattern matching compilation — Layer 1: Core types and infrastructure.
//!
//! This is a 1:1 port of OCaml's `matching.ml` lines 1-374.
//! It defines the core data structures (matrix, context, jumps, pattern_matching)
//! and the operations on them used by the pattern matching compiler.

#![allow(dead_code)]

use std::cell::{Cell as StdCell, RefCell};
use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::collections::HashMap;

use crate::ident::{Ident, IdentFlags};
use crate::lambda::LetKind;
use crate::location::Location;
use crate::parse_arena::LocIdx;
use crate::parser::ast::Attributes;
use crate::raw_lambda::{RawApply, RawLambda, RawLambdaSwitch, RawPrimInfo};
use crate::raw_lambda::print::RawLambdaPrinter;
use crate::types::typedtree::{Constant, EnvRef, Pattern, PatternDesc};
use crate::types::type_expr::TypeExprRef;
use crate::types::decl::{ConstructorTag, ConstructorDescription, LabelDescription, RecordRepresentation};
use crate::types::asttypes::MutableFlag;
use crate::types::type_expr::{RowDesc, RowField};
use crate::types::btype;
use crate::types::context::TypeContext;
use crate::types::typedtree::Partial;
use crate::lambda::{Comparison, Primitive, FieldDbgInfo, SwitchNames, TagInfo};
use crate::lambda::primitive::Mutable;
use crate::raw_lambda::typeopt::{constructor_has_optional_shape, has_untagged, type_cannot_contain_undefined};

// ============================================================================
// Omega (wildcard) helpers — ported from parmatch.ml
// ============================================================================

/// Create a wildcard pattern (`_`).
/// Equivalent to OCaml's `omega = make_pat Tpat_any Ctype.none Env.empty`.
fn omega() -> Pattern {
    Pattern::new(
        PatternDesc::Tpat_any,
        LocIdx::none(),
        TypeExprRef(0),
        EnvRef(0),
        Attributes::new(),
    )
}

/// Create a list of n wildcard patterns.
/// Equivalent to OCaml's `omegas n`.
fn omegas(n: usize) -> Vec<Pattern> {
    (0..n).map(|_| omega()).collect()
}

/// Create a list of wildcards with the same length as `l`.
fn omega_list(l: &[Pattern]) -> Vec<Pattern> {
    l.iter().map(|_| omega()).collect()
}

// ============================================================================
// Pattern helper functions — ported from parmatch.ml
// ============================================================================

/// Make a pattern with given desc, type, and env.
fn make_pat(desc: PatternDesc, ty: TypeExprRef, env: EnvRef) -> Pattern {
    Pattern::new(desc, LocIdx::none(), ty, env, Attributes::new())
}

/// Compare two typed constants.
/// Equivalent to OCaml's `const_compare`.
fn const_compare(c1: &Constant, c2: &Constant) -> std::cmp::Ordering {
    use std::cmp::Ordering;
    match (c1, c2) {
        (Constant::Float(f1), Constant::Float(f2)) => {
            let v1: f64 = f1.parse().unwrap_or(0.0);
            let v2: f64 = f2.parse().unwrap_or(0.0);
            v1.partial_cmp(&v2).unwrap_or(Ordering::Equal)
        }
        (Constant::BigInt(s1, b1), Constant::BigInt(s2, b2)) => {
            // Simple comparison: sign first, then digits
            match (s1, s2) {
                (true, false) => Ordering::Less,    // negative < positive
                (false, true) => Ordering::Greater,
                _ => b1.cmp(b2),
            }
        }
        (Constant::String(s1, _), Constant::String(s2, _)) => s1.cmp(s2),
        (Constant::Int(i1), Constant::Int(i2)) => i1.cmp(i2),
        (Constant::Char(c1), Constant::Char(c2)) => c1.cmp(c2),
        _ => {
            // Fall back to debug-based comparison for mixed types.
            let d1 = format!("{:?}", c1);
            let d2 = format!("{:?}", c2);
            d1.cmp(&d2)
        }
    }
}

/// Check if two constructor tags are equal.
fn equal_tag(t1: &ConstructorTag, t2: &ConstructorTag) -> bool {
    match (t1, t2) {
        (ConstructorTag::CstrConstant(i1), ConstructorTag::CstrConstant(i2)) => i1 == i2,
        (ConstructorTag::CstrBlock(i1), ConstructorTag::CstrBlock(i2)) => i1 == i2,
        (ConstructorTag::CstrUnboxed, ConstructorTag::CstrUnboxed) => true,
        (ConstructorTag::CstrExtension(p1), ConstructorTag::CstrExtension(p2)) => {
            p1.same(p2)
        }
        _ => false,
    }
}

/// Check if one pattern is less specific than another (le_pat p q means
/// everything matched by q is also matched by p).
/// Equivalent to OCaml's `le_pat`.
fn le_pat(p: &Pattern, q: &Pattern) -> bool {
    match (&p.pat_desc, &q.pat_desc) {
        (PatternDesc::Tpat_var(..) | PatternDesc::Tpat_any, _) => true,
        (PatternDesc::Tpat_alias(p, _, _), _) => le_pat(p, q),
        (_, PatternDesc::Tpat_alias(q, _, _)) => le_pat(p, q),
        (PatternDesc::Tpat_constant(c1), PatternDesc::Tpat_constant(c2)) => {
            const_compare(c1, c2) == std::cmp::Ordering::Equal
        }
        (
            PatternDesc::Tpat_construct(_, c1, ps),
            PatternDesc::Tpat_construct(_, c2, qs),
        ) => equal_tag(&c1.cstr_tag, &c2.cstr_tag) && le_pats(ps, qs),
        (
            PatternDesc::Tpat_variant(l1, Some(p1), _),
            PatternDesc::Tpat_variant(l2, Some(p2), _),
        ) => l1 == l2 && le_pat(p1, p2),
        (
            PatternDesc::Tpat_variant(l1, None, _),
            PatternDesc::Tpat_variant(l2, None, _),
        ) => l1 == l2,
        (PatternDesc::Tpat_variant(..), PatternDesc::Tpat_variant(..)) => false,
        (PatternDesc::Tpat_tuple(ps), PatternDesc::Tpat_tuple(qs)) => le_pats(ps, qs),
        (PatternDesc::Tpat_array(ps), PatternDesc::Tpat_array(qs)) => {
            ps.len() == qs.len() && le_pats(ps, qs)
        }
        // Omit record and satisfiable fallback for now — conservative false.
        _ => false,
    }
}

/// Check if patterns ps are pairwise le_pat to qs.
fn le_pats(ps: &[Pattern], qs: &[Pattern]) -> bool {
    match (ps.first(), qs.first()) {
        (Some(p), Some(q)) => le_pat(p, q) && le_pats(&ps[1..], &qs[1..]),
        _ => true,
    }
}

/// Get minimal elements under a partial order `le`.
/// Equivalent to OCaml's `get_mins`.
fn get_mins<T: Clone>(le: impl Fn(&T, &T) -> bool, ps: Vec<T>) -> Vec<T> {
    fn select_rec<T: Clone>(le: &impl Fn(&T, &T) -> bool, r: Vec<T>, ps: &[T]) -> Vec<T> {
        match ps.split_first() {
            None => r,
            Some((p, rest)) => {
                if rest.iter().any(|p0| le(p0, p)) {
                    select_rec(le, r, rest)
                } else {
                    let mut r = r;
                    r.push(p.clone());
                    select_rec(le, r, rest)
                }
            }
        }
    }
    let first_pass = select_rec(&le, Vec::new(), &ps);
    select_rec(&le, Vec::new(), &first_pass)
}

/// Raised when patterns are incompatible in lub.
struct Empty;

/// Least upper bound of two patterns (the most specific pattern that
/// matches everything matched by either p or q).
/// Returns Err(Empty) when p and q are incompatible.
fn lub(p: &Pattern, q: &Pattern) -> Result<Pattern, Empty> {
    match (&p.pat_desc, &q.pat_desc) {
        (PatternDesc::Tpat_alias(p, _, _), _) => lub(p, q),
        (_, PatternDesc::Tpat_alias(q, _, _)) => lub(p, q),
        (PatternDesc::Tpat_any | PatternDesc::Tpat_var(..), _) => Ok(q.clone()),
        (_, PatternDesc::Tpat_any | PatternDesc::Tpat_var(..)) => Ok(p.clone()),
        (PatternDesc::Tpat_or(p1, p2, _), _) => orlub(p1, p2, q),
        (_, PatternDesc::Tpat_or(q1, q2, _)) => orlub(q1, q2, p),
        (PatternDesc::Tpat_constant(c1), PatternDesc::Tpat_constant(c2))
            if const_compare(c1, c2) == std::cmp::Ordering::Equal =>
        {
            Ok(p.clone())
        }
        (PatternDesc::Tpat_tuple(ps), PatternDesc::Tpat_tuple(qs)) => {
            let rs = lubs(ps, qs)?;
            Ok(make_pat(PatternDesc::Tpat_tuple(rs), p.pat_type, p.pat_env))
        }
        (
            PatternDesc::Tpat_construct(lid, c1, ps1),
            PatternDesc::Tpat_construct(_, c2, ps2),
        ) if equal_tag(&c1.cstr_tag, &c2.cstr_tag) => {
            let rs = lubs(ps1, ps2)?;
            Ok(make_pat(
                PatternDesc::Tpat_construct(lid.clone(), c1.clone(), rs),
                p.pat_type,
                p.pat_env,
            ))
        }
        (
            PatternDesc::Tpat_variant(l1, Some(p1), row),
            PatternDesc::Tpat_variant(l2, Some(p2), _),
        ) if l1 == l2 => {
            let r = lub(p1, p2)?;
            Ok(make_pat(
                PatternDesc::Tpat_variant(l1.clone(), Some(Box::new(r)), *row),
                p.pat_type,
                p.pat_env,
            ))
        }
        (
            PatternDesc::Tpat_variant(l1, None, _),
            PatternDesc::Tpat_variant(l2, None, _),
        ) if l1 == l2 => Ok(p.clone()),
        (
            PatternDesc::Tpat_record(l1, closed),
            PatternDesc::Tpat_record(l2, _),
        ) => {
            let rs = record_lubs(l1, l2)?;
            Ok(make_pat(
                PatternDesc::Tpat_record(rs, *closed),
                p.pat_type,
                p.pat_env,
            ))
        }
        (PatternDesc::Tpat_array(ps), PatternDesc::Tpat_array(qs))
            if ps.len() == qs.len() =>
        {
            let rs = lubs(ps, qs)?;
            Ok(make_pat(PatternDesc::Tpat_array(rs), p.pat_type, p.pat_env))
        }
        _ => Err(Empty),
    }
}

fn orlub(p1: &Pattern, p2: &Pattern, q: &Pattern) -> Result<Pattern, Empty> {
    match lub(p1, q) {
        Ok(r1) => match lub(p2, q) {
            Ok(r2) => Ok(Pattern {
                pat_desc: PatternDesc::Tpat_or(Box::new(r1), Box::new(r2), None),
                ..q.clone()
            }),
            Err(Empty) => Ok(r1),
        },
        Err(Empty) => lub(p2, q),
    }
}

/// Record field lub.
fn record_lubs(
    l1: &[(crate::parse_arena::Located<crate::parse_arena::LidentIdx>, crate::types::LabelDescription, Pattern, bool)],
    l2: &[(crate::parse_arena::Located<crate::parse_arena::LidentIdx>, crate::types::LabelDescription, Pattern, bool)],
) -> Result<Vec<(crate::parse_arena::Located<crate::parse_arena::LidentIdx>, crate::types::LabelDescription, Pattern, bool)>, Empty> {
    type RecordField = (crate::parse_arena::Located<crate::parse_arena::LidentIdx>, crate::types::LabelDescription, Pattern, bool);

    fn lub_rec(l1: &[RecordField], l2: &[RecordField]) -> Result<Vec<RecordField>, Empty> {
        match (l1.split_first(), l2.split_first()) {
            (None, _) => Ok(l2.to_vec()),
            (_, None) => Ok(l1.to_vec()),
            (Some(((lid1, lbl1, p1, o1), rem1)), Some(((lid2, lbl2, p2, o2), rem2))) => {
                if lbl1.lbl_pos < lbl2.lbl_pos {
                    let mut rest = lub_rec(rem1, l2)?;
                    rest.insert(0, (lid1.clone(), lbl1.clone(), p1.clone(), *o1));
                    Ok(rest)
                } else if lbl2.lbl_pos < lbl1.lbl_pos {
                    let mut rest = lub_rec(l1, rem2)?;
                    rest.insert(0, (lid2.clone(), lbl2.clone(), p2.clone(), *o2));
                    Ok(rest)
                } else {
                    if o1 != o2 {
                        return Err(Empty);
                    }
                    let p = lub(p1, p2)?;
                    let mut rest = lub_rec(rem1, rem2)?;
                    rest.insert(0, (lid1.clone(), lbl1.clone(), p, *o1));
                    Ok(rest)
                }
            }
        }
    }
    lub_rec(l1, l2)
}

fn lubs(ps: &[Pattern], qs: &[Pattern]) -> Result<Vec<Pattern>, Empty> {
    match (ps.split_first(), qs.split_first()) {
        (Some((p, ps_rest)), Some((q, qs_rest))) => {
            let head = lub(p, q)?;
            let mut tail = lubs(ps_rest, qs_rest)?;
            tail.insert(0, head);
            Ok(tail)
        }
        _ => Ok(Vec::new()),
    }
}

/// Normalize a pattern: replace all sub-pattern arguments with omega.
/// Equivalent to OCaml's `normalize_pat`.
fn normalize_pat(q: &Pattern) -> Pattern {
    match &q.pat_desc {
        PatternDesc::Tpat_any | PatternDesc::Tpat_constant(_) => q.clone(),
        PatternDesc::Tpat_var(..) => make_pat(PatternDesc::Tpat_any, q.pat_type, q.pat_env),
        PatternDesc::Tpat_alias(p, _, _) => normalize_pat(p),
        PatternDesc::Tpat_tuple(args) => make_pat(
            PatternDesc::Tpat_tuple(omega_list(args)),
            q.pat_type,
            q.pat_env,
        ),
        PatternDesc::Tpat_construct(lid, c, args) => make_pat(
            PatternDesc::Tpat_construct(lid.clone(), c.clone(), omega_list(args)),
            q.pat_type,
            q.pat_env,
        ),
        PatternDesc::Tpat_variant(l, arg, row) => make_pat(
            PatternDesc::Tpat_variant(
                l.clone(),
                arg.as_ref().map(|_| Box::new(omega())),
                *row,
            ),
            q.pat_type,
            q.pat_env,
        ),
        PatternDesc::Tpat_array(args) => make_pat(
            PatternDesc::Tpat_array(omega_list(args)),
            q.pat_type,
            q.pat_env,
        ),
        PatternDesc::Tpat_record(largs, closed) => make_pat(
            PatternDesc::Tpat_record(
                largs
                    .iter()
                    .map(|(lid, lbl, _, opt)| (lid.clone(), lbl.clone(), omega(), *opt))
                    .collect(),
                *closed,
            ),
            q.pat_type,
            q.pat_env,
        ),
        PatternDesc::Tpat_or(..) => {
            panic!("Parmatch.normalize_pat: Tpat_or")
        }
    }
}

/// Read n arguments from `r`, returning (args, rest).
fn read_args<T: Clone>(xs: &[T], r: &[Pattern]) -> (Vec<Pattern>, Vec<Pattern>) {
    if xs.is_empty() {
        return (Vec::new(), r.to_vec());
    }
    assert!(
        !r.is_empty(),
        "Parmatch.read_args: not enough arguments"
    );
    let (mut args, rest) = read_args(&xs[1..], &r[1..]);
    args.insert(0, r[0].clone());
    (args, rest)
}

/// Set the arguments of a normalized pattern, optionally erasing mutable fields.
/// Equivalent to OCaml's `do_set_args`.
fn do_set_args(erase_mutable: bool, q: &Pattern, r: &[Pattern]) -> Vec<Pattern> {
    match &q.pat_desc {
        PatternDesc::Tpat_tuple(pats) => {
            let (args, rest) = read_args(pats.as_slice(), r);
            let mut result = vec![make_pat(
                PatternDesc::Tpat_tuple(args),
                q.pat_type,
                q.pat_env,
            )];
            result.extend(rest);
            result
        }
        PatternDesc::Tpat_record(fields, closed) => {
            let (args, rest) = read_args(fields.as_slice(), r);
            let new_fields: Vec<_> = fields
                .iter()
                .zip(args.iter())
                .map(|((lid, lbl, _, opt), arg)| {
                    if erase_mutable && matches!(lbl.lbl_mut, MutableFlag::Mutable) {
                        (lid.clone(), lbl.clone(), omega(), *opt)
                    } else {
                        (lid.clone(), lbl.clone(), arg.clone(), *opt)
                    }
                })
                .collect();
            let mut result = vec![make_pat(
                PatternDesc::Tpat_record(new_fields, *closed),
                q.pat_type,
                q.pat_env,
            )];
            result.extend(rest);
            result
        }
        PatternDesc::Tpat_construct(lid, c, pats) => {
            let (args, rest) = read_args(pats.as_slice(), r);
            let mut result = vec![make_pat(
                PatternDesc::Tpat_construct(lid.clone(), c.clone(), args),
                q.pat_type,
                q.pat_env,
            )];
            result.extend(rest);
            result
        }
        PatternDesc::Tpat_variant(l, opt_omega, row) => {
            let (arg, rest) = match (opt_omega, r) {
                (Some(_), [a, rest @ ..]) => (Some(Box::new(a.clone())), rest.to_vec()),
                (None, _) => (None, r.to_vec()),
                _ => panic!("Parmatch.set_args: variant"),
            };
            let mut result = vec![make_pat(
                PatternDesc::Tpat_variant(l.clone(), arg, *row),
                q.pat_type,
                q.pat_env,
            )];
            result.extend(rest);
            result
        }
        PatternDesc::Tpat_array(pats) => {
            let (args, rest) = read_args(pats.as_slice(), r);
            let mut result = vec![make_pat(
                PatternDesc::Tpat_array(args),
                q.pat_type,
                q.pat_env,
            )];
            result.extend(rest);
            result
        }
        PatternDesc::Tpat_constant(_) | PatternDesc::Tpat_any => {
            let mut result = vec![q.clone()];
            result.extend_from_slice(r);
            result
        }
        _ => panic!("Parmatch.set_args"),
    }
}

/// `set_args q r` — set actual arguments of the matching pattern.
fn set_args(q: &Pattern, r: &[Pattern]) -> Vec<Pattern> {
    do_set_args(false, q, r)
}

/// `set_args_erase_mutable q r` — like set_args but replaces mutable fields with omega.
fn set_args_erase_mutable(q: &Pattern, r: &[Pattern]) -> Vec<Pattern> {
    do_set_args(true, q, r)
}

/// Expand record pattern to all fields (filling missing with omega).
/// OCaml's `all_record_args` uses `lbl_all` to get ALL labels, then fills
/// missing ones with omega. Since Rust's `lbl_all` is a placeholder, we
/// resolve via the TypeContext when available.
fn all_record_args(
    ctx_ref: Option<&TypeContext<'_>>,
    pat_type: TypeExprRef,
    pat_env: EnvRef,
    lbls: &[(crate::parse_arena::Located<crate::parse_arena::LidentIdx>, crate::types::LabelDescription, Pattern, bool)],
) -> Vec<(crate::parse_arena::Located<crate::parse_arena::LidentIdx>, crate::types::LabelDescription, Pattern, bool)> {
    if lbls.is_empty() {
        return Vec::new();
    }

    let first_lbl = &lbls[0].1;

    // Try to resolve all labels from the type
    let all_labels = ctx_ref.and_then(|ctx| {
        resolve_labels_from_type(ctx, first_lbl.lbl_res, pat_env)
            .or_else(|| resolve_labels_from_type(ctx, pat_type, pat_env))
    });

    match all_labels {
        Some(all_labels) => {
            // Build a full array with omega for missing fields
            let dummy_loc = crate::parse_arena::Located {
                txt: crate::parse_arena::LidentIdx(0),
                loc: LocIdx::none(),
            };
            let mut result: Vec<_> = all_labels.iter().map(|lbl| {
                (dummy_loc.clone(), lbl.clone(), omega(), first_lbl.lbl_optional)
            }).collect();
            // Fill in the actual patterns from the provided fields
            for (id, lbl, pat, opt) in lbls {
                if (lbl.lbl_pos as usize) < result.len() {
                    result[lbl.lbl_pos as usize] = (id.clone(), lbl.clone(), pat.clone(), *opt);
                }
            }
            result
        }
        None => {
            // Fallback: return fields as-is (old behavior)
            lbls.to_vec()
        }
    }
}

/// Check if two constructors may be equal (considering extension types).
fn may_equal_constr(
    c1: &crate::types::ConstructorDescription,
    c2: &crate::types::ConstructorDescription,
) -> bool {
    match (&c1.cstr_tag, &c2.cstr_tag) {
        (ConstructorTag::CstrExtension(_), ConstructorTag::CstrExtension(_)) => {
            c1.cstr_arity == c2.cstr_arity
        }
        (t1, t2) => equal_tag(t1, t2),
    }
}

/// Compatibility predicate: may_compat p q returns false when p and q
/// never admit a common instance.
fn may_compat(p: &Pattern, q: &Pattern) -> bool {
    match (&p.pat_desc, &q.pat_desc) {
        (PatternDesc::Tpat_any | PatternDesc::Tpat_var(..), _)
        | (_, PatternDesc::Tpat_any | PatternDesc::Tpat_var(..)) => true,
        (PatternDesc::Tpat_alias(p, _, _), _) => may_compat(p, q),
        (_, PatternDesc::Tpat_alias(q, _, _)) => may_compat(p, q),
        (PatternDesc::Tpat_or(p1, p2, _), _) => may_compat(p1, q) || may_compat(p2, q),
        (_, PatternDesc::Tpat_or(q1, q2, _)) => may_compat(p, q1) || may_compat(p, q2),
        (
            PatternDesc::Tpat_construct(_, c1, ps1),
            PatternDesc::Tpat_construct(_, c2, ps2),
        ) => may_equal_constr(c1, c2) && may_compats(ps1, ps2),
        (PatternDesc::Tpat_constant(c1), PatternDesc::Tpat_constant(c2)) => {
            const_compare(c1, c2) == std::cmp::Ordering::Equal
        }
        (
            PatternDesc::Tpat_variant(l1, op1, _),
            PatternDesc::Tpat_variant(l2, op2, _),
        ) => {
            l1 == l2
                && match (op1, op2) {
                    (Some(p1), Some(p2)) => may_compat(p1, p2),
                    (None, None) => true,
                    _ => false,
                }
        }
        (PatternDesc::Tpat_tuple(ps), PatternDesc::Tpat_tuple(qs)) => may_compats(ps, qs),
        (PatternDesc::Tpat_array(ps), PatternDesc::Tpat_array(qs)) => {
            ps.len() == qs.len() && may_compats(ps, qs)
        }
        (PatternDesc::Tpat_record(l1, _), PatternDesc::Tpat_record(l2, _)) => {
            // Check compatible fields only
            may_compats_record(l1, l2)
        }
        _ => true,
    }
}

fn may_compats(ps: &[Pattern], qs: &[Pattern]) -> bool {
    ps.iter().zip(qs.iter()).all(|(p, q)| may_compat(p, q))
}

fn may_compats_record(
    l1: &[(crate::parse_arena::Located<crate::parse_arena::LidentIdx>, crate::types::LabelDescription, Pattern, bool)],
    l2: &[(crate::parse_arena::Located<crate::parse_arena::LidentIdx>, crate::types::LabelDescription, Pattern, bool)],
) -> bool {
    // For each field present in both, check compatibility
    for (_, lbl1, p1, _) in l1 {
        for (_, lbl2, p2, _) in l2 {
            if lbl1.lbl_pos == lbl2.lbl_pos && !may_compat(p1, p2) {
                return false;
            }
        }
    }
    true
}

// ============================================================================
// Matrix type — pattern list list
// ============================================================================

/// A pattern matrix: each row is a list of patterns.
pub type Matrix = Vec<Vec<Pattern>>;

/// Prepend an omega (wildcard) column to each row of a matrix.
pub fn add_omega_column(pss: &Matrix) -> Matrix {
    pss.iter()
        .map(|ps| {
            let mut row = vec![omega()];
            row.extend(ps.iter().cloned());
            row
        })
        .collect()
}

// ============================================================================
// Context type
// ============================================================================

/// A context: a pair of pattern lists (left, right) where columns are
/// partitioned into left and right parts.
#[derive(Debug, Clone)]
pub struct Ctx {
    pub left: Vec<Pattern>,
    pub right: Vec<Pattern>,
}

/// Check if context c1 is less-or-equal to c2.
pub fn le_ctx(c1: &Ctx, c2: &Ctx) -> bool {
    le_pats(&c1.left, &c2.left) && le_pats(&c1.right, &c2.right)
}

/// Shift the first element of `right` to the front of `left`.
pub fn lshift(ctx: &Ctx) -> Ctx {
    match ctx.right.split_first() {
        Some((x, xs)) => Ctx {
            left: {
                let mut l = vec![x.clone()];
                l.extend(ctx.left.iter().cloned());
                l
            },
            right: xs.to_vec(),
        },
        None => panic!("lshift: empty right"),
    }
}

/// Shift an omega to the front of `left`, dropping the first element of `right`.
pub fn lforget(ctx: &Ctx) -> Ctx {
    match ctx.right.split_first() {
        Some((_, xs)) => Ctx {
            left: {
                let mut l = vec![omega()];
                l.extend(ctx.left.iter().cloned());
                l
            },
            right: xs.to_vec(),
        },
        None => panic!("lforget: empty right"),
    }
}

/// Check if a slice is small enough (length <= n).
fn small_enough(n: usize, slice: &[Ctx]) -> bool {
    slice.len() <= n
}

/// Shift left for a list of contexts, with pruning when too large.
pub fn ctx_lshift(ctx: &[Ctx]) -> Vec<Ctx> {
    if small_enough(31, ctx) {
        ctx.iter().map(lshift).collect()
    } else {
        // Context pruning
        let forgotten: Vec<Ctx> = ctx.iter().map(lforget).collect();
        get_mins(le_ctx, forgotten)
    }
}

/// Shift the first element of `left` to the front of `right`.
pub fn rshift(ctx: &Ctx) -> Ctx {
    match ctx.left.split_first() {
        Some((p, ps)) => Ctx {
            left: ps.to_vec(),
            right: {
                let mut r = vec![p.clone()];
                r.extend(ctx.right.iter().cloned());
                r
            },
        },
        None => panic!("rshift: empty left"),
    }
}

/// Right-shift all contexts.
pub fn ctx_rshift(ctx: &[Ctx]) -> Vec<Ctx> {
    ctx.iter().map(rshift).collect()
}

/// Split off the first n elements from a pattern list.
/// Returns (first_n, rest).
fn nchars(n: usize, ps: &[Pattern]) -> (Vec<Pattern>, Vec<Pattern>) {
    if n == 0 {
        return (Vec::new(), ps.to_vec());
    }
    match ps.split_first() {
        Some((p, rem)) => {
            let (mut chars, cdrs) = nchars(n - 1, rem);
            chars.insert(0, p.clone());
            (chars, cdrs)
        }
        None => panic!("nchars: not enough patterns"),
    }
}

/// Right-shift n elements from left to right.
pub fn rshift_num(n: usize, ctx: &Ctx) -> Ctx {
    let (shifted, left) = nchars(n, &ctx.left);
    let mut right = shifted;
    right.extend(ctx.right.iter().cloned());
    Ctx { left, right }
}

/// Right-shift n elements for all contexts.
pub fn ctx_rshift_num(n: usize, ctx: &[Ctx]) -> Vec<Ctx> {
    ctx.iter().map(|c| rshift_num(n, c)).collect()
}

/// Recombination of contexts: take the first element from left,
/// and set its arguments from right, erasing mutable fields.
/// e.g. `(_,_)::p1::p2::rem -> (p1,p2)::rem`
pub fn combine(ctx: &Ctx) -> Ctx {
    match ctx.left.split_first() {
        Some((p, ps)) => {
            let result = set_args_erase_mutable(p, &ctx.right);
            // The first element of result is the combined pattern;
            // the rest is the remaining right.
            Ctx {
                left: ps.to_vec(),
                right: result,
            }
        }
        None => panic!("combine: empty left"),
    }
}

/// Combine all contexts.
pub fn ctx_combine(ctx: &[Ctx]) -> Vec<Ctx> {
    ctx.iter().map(combine).collect()
}

/// Number of columns in a matrix (length of first row, or 0 if empty).
pub fn ncols(pss: &Matrix) -> usize {
    match pss.first() {
        Some(ps) => ps.len(),
        None => 0,
    }
}

// ============================================================================
// NoMatch / OrPat exceptions (represented as Result/enum in Rust)
// ============================================================================

/// Errors that can occur during pattern matching filtering.
enum MatchError {
    /// Pattern doesn't match.
    NoMatch,
    /// Pattern is an or-pattern that needs expansion.
    OrPat,
}

// ============================================================================
// filter_matrix — filter a matrix according to a matcher function
// ============================================================================

/// Filter a pattern matrix using a matcher function.
/// The matcher takes a pattern and the rest of the row, and returns
/// the filtered row or an error.
///
/// Equivalent to OCaml's `filter_matrix`.
pub fn filter_matrix(
    matcher: &dyn Fn(&Pattern, &[Pattern]) -> Result<Vec<Pattern>, MatchError>,
    pss: &Matrix,
) -> Matrix {
    fn filter_rec(
        matcher: &dyn Fn(&Pattern, &[Pattern]) -> Result<Vec<Pattern>, MatchError>,
        pss: &[Vec<Pattern>],
    ) -> Matrix {
        match pss.split_first() {
            None => Vec::new(),
            Some((row, rem)) => {
                if row.is_empty() {
                    // Empty rows shouldn't appear here — fatal error in OCaml.
                    panic!("Matching.filter_matrix: empty row");
                }
                let p = &row[0];
                let ps = &row[1..];
                match &p.pat_desc {
                    PatternDesc::Tpat_alias(p_inner, _, _) => {
                        let mut new_row = vec![(**p_inner).clone()];
                        new_row.extend(ps.iter().cloned());
                        let mut new_pss = vec![new_row];
                        new_pss.extend(rem.iter().cloned());
                        filter_rec(matcher, &new_pss)
                    }
                    PatternDesc::Tpat_var(..) => {
                        let mut new_row = vec![omega()];
                        new_row.extend(ps.iter().cloned());
                        let mut new_pss = vec![new_row];
                        new_pss.extend(rem.iter().cloned());
                        filter_rec(matcher, &new_pss)
                    }
                    _ => {
                        let mut rest = filter_rec(matcher, rem);
                        match matcher(p, ps) {
                            Ok(filtered_row) => {
                                rest.insert(0, filtered_row);
                                rest
                            }
                            Err(MatchError::NoMatch) => rest,
                            Err(MatchError::OrPat) => match &p.pat_desc {
                                PatternDesc::Tpat_or(p1, p2, _) => {
                                    let mut row1 = vec![(**p1).clone()];
                                    row1.extend(ps.iter().cloned());
                                    let mut row2 = vec![(**p2).clone()];
                                    row2.extend(ps.iter().cloned());
                                    let mut expanded = filter_rec(matcher, &[row1, row2]);
                                    expanded.extend(rest);
                                    expanded
                                }
                                _ => panic!("filter_matrix: OrPat on non-or pattern"),
                            },
                        }
                    }
                }
            }
        }
    }
    filter_rec(matcher, pss)
}

// ============================================================================
// make_default — build default environment by filtering
// ============================================================================

/// Default environment entry: (matrix, exit_number).
pub type DefaultEnv = Vec<(Matrix, i32)>;

/// Build default environment by filtering each matrix with the given matcher.
/// Equivalent to OCaml's `make_default`.
pub fn make_default(
    matcher: &dyn Fn(&Pattern, &[Pattern]) -> Result<Vec<Pattern>, MatchError>,
    env: &DefaultEnv,
) -> DefaultEnv {
    fn make_rec(
        matcher: &dyn Fn(&Pattern, &[Pattern]) -> Result<Vec<Pattern>, MatchError>,
        env: &[(Matrix, i32)],
    ) -> DefaultEnv {
        match env.split_first() {
            None => Vec::new(),
            Some(((pss, i), rem)) => {
                // Check for terminal: [[]] case
                if pss.len() == 1 && pss[0].is_empty() {
                    return vec![(vec![Vec::new()], *i)];
                }
                let rest = make_rec(matcher, rem);
                let filtered = filter_matrix(matcher, pss);
                if filtered.is_empty() {
                    rest
                } else if !filtered.is_empty()
                    && filtered.iter().any(|row| row.is_empty())
                {
                    let mut result = vec![(vec![Vec::new()], *i)];
                    result.extend(rest);
                    result
                } else {
                    let mut result = vec![(filtered, *i)];
                    result.extend(rest);
                    result
                }
            }
        }
    }
    make_rec(matcher, env)
}

// ============================================================================
// ctx_matcher — build a context matcher from a pattern
// ============================================================================

/// Build a matcher function from a pattern, for use with filter_ctx.
/// Returns a closure that, given a pattern q and remaining patterns,
/// returns (to_left_pattern, expanded_right) or Err(NoMatch).
///
/// Equivalent to OCaml's `ctx_matcher`.
pub fn ctx_matcher(
    p: &Pattern,
) -> Box<dyn Fn(&Pattern, &[Pattern]) -> Result<(Pattern, Vec<Pattern>), MatchError> + '_> {
    let p = normalize_pat(p);
    match &p.pat_desc {
        PatternDesc::Tpat_construct(_, cstr, pats) => {
            let cstr = cstr.clone();
            let omegas_vec = pats.clone();
            let p = p.clone();
            Box::new(move |q: &Pattern, rem: &[Pattern]| match &q.pat_desc {
                PatternDesc::Tpat_construct(_, cstr2, args)
                    if may_equal_constr(&cstr, cstr2) =>
                {
                    let mut result = args.clone();
                    result.extend(rem.iter().cloned());
                    Ok((p.clone(), result))
                }
                PatternDesc::Tpat_any => {
                    let mut result = omegas_vec.clone();
                    result.extend(rem.iter().cloned());
                    Ok((p.clone(), result))
                }
                _ => Err(MatchError::NoMatch),
            })
        }
        PatternDesc::Tpat_constant(cst) => {
            let cst = cst.clone();
            let p = p.clone();
            Box::new(move |q: &Pattern, rem: &[Pattern]| match &q.pat_desc {
                PatternDesc::Tpat_constant(cst2)
                    if const_compare(&cst, cst2) == std::cmp::Ordering::Equal =>
                {
                    Ok((p.clone(), rem.to_vec()))
                }
                PatternDesc::Tpat_any => Ok((p.clone(), rem.to_vec())),
                _ => Err(MatchError::NoMatch),
            })
        }
        PatternDesc::Tpat_variant(lab, Some(omega_pat), _) => {
            let lab = lab.clone();
            let omega_pat = (**omega_pat).clone();
            let p = p.clone();
            Box::new(move |q: &Pattern, rem: &[Pattern]| match &q.pat_desc {
                PatternDesc::Tpat_variant(lab2, Some(arg), _) if lab == *lab2 => {
                    let mut result = vec![(**arg).clone()];
                    result.extend(rem.iter().cloned());
                    Ok((p.clone(), result))
                }
                PatternDesc::Tpat_any => {
                    let mut result = vec![omega_pat.clone()];
                    result.extend(rem.iter().cloned());
                    Ok((p.clone(), result))
                }
                _ => Err(MatchError::NoMatch),
            })
        }
        PatternDesc::Tpat_variant(lab, None, _) => {
            let lab = lab.clone();
            let p = p.clone();
            Box::new(move |q: &Pattern, rem: &[Pattern]| match &q.pat_desc {
                PatternDesc::Tpat_variant(lab2, None, _) if lab == *lab2 => {
                    Ok((p.clone(), rem.to_vec()))
                }
                PatternDesc::Tpat_any => Ok((p.clone(), rem.to_vec())),
                _ => Err(MatchError::NoMatch),
            })
        }
        PatternDesc::Tpat_array(pats) => {
            let len = pats.len();
            let omegas_vec = pats.clone();
            let p = p.clone();
            Box::new(move |q: &Pattern, rem: &[Pattern]| match &q.pat_desc {
                PatternDesc::Tpat_array(args) if args.len() == len => {
                    let mut result = args.clone();
                    result.extend(rem.iter().cloned());
                    Ok((p.clone(), result))
                }
                PatternDesc::Tpat_any => {
                    let mut result = omegas_vec.clone();
                    result.extend(rem.iter().cloned());
                    Ok((p.clone(), result))
                }
                _ => Err(MatchError::NoMatch),
            })
        }
        PatternDesc::Tpat_tuple(pats) => {
            let len = pats.len();
            let omegas_vec = pats.clone();
            let p = p.clone();
            Box::new(move |q: &Pattern, rem: &[Pattern]| match &q.pat_desc {
                PatternDesc::Tpat_tuple(args) if args.len() == len => {
                    let mut result = args.clone();
                    result.extend(rem.iter().cloned());
                    Ok((p.clone(), result))
                }
                PatternDesc::Tpat_any => {
                    let mut result = omegas_vec.clone();
                    result.extend(rem.iter().cloned());
                    Ok((p.clone(), result))
                }
                _ => Err(MatchError::NoMatch),
            })
        }
        PatternDesc::Tpat_record(fields, _) if !fields.is_empty() => {
            let fields = fields.clone();
            let p = p.clone();
            Box::new(move |q: &Pattern, rem: &[Pattern]| match &q.pat_desc {
                PatternDesc::Tpat_record(fields2, _) if !fields2.is_empty() => {
                    let expanded = all_record_args(None, q.pat_type, q.pat_env, fields2);
                    let mut result: Vec<Pattern> = expanded
                        .iter()
                        .map(|(_, _, p, _)| p.clone())
                        .collect();
                    result.extend(rem.iter().cloned());
                    Ok((p.clone(), result))
                }
                PatternDesc::Tpat_any => {
                    let mut result: Vec<Pattern> = fields
                        .iter()
                        .map(|(_, _, p, _)| p.clone())
                        .collect();
                    result.extend(rem.iter().cloned());
                    Ok((p.clone(), result))
                }
                _ => Err(MatchError::NoMatch),
            })
        }
        _ => panic!("Matching.ctx_matcher: unsupported pattern"),
    }
}

// ============================================================================
// filter_ctx — filter a context list using a ctx_matcher
// ============================================================================

/// Filter contexts using a matcher built from pattern q.
/// Equivalent to OCaml's `filter_ctx`.
pub fn filter_ctx(q: &Pattern, ctx: &[Ctx]) -> Vec<Ctx> {
    let matcher = ctx_matcher(q);

    fn filter_rec(
        matcher: &dyn Fn(&Pattern, &[Pattern]) -> Result<(Pattern, Vec<Pattern>), MatchError>,
        ctx: &[Ctx],
    ) -> Vec<Ctx> {
        match ctx.split_first() {
            None => Vec::new(),
            Some((l, rem)) => {
                match l.right.split_first() {
                    None => panic!("Matching.filter_ctx: empty right"),
                    Some((p, ps)) => match &p.pat_desc {
                        PatternDesc::Tpat_or(p1, p2, _) => {
                            let ctx1 = Ctx {
                                left: l.left.clone(),
                                right: {
                                    let mut r = vec![(**p1).clone()];
                                    r.extend(ps.iter().cloned());
                                    r
                                },
                            };
                            let ctx2 = Ctx {
                                left: l.left.clone(),
                                right: {
                                    let mut r = vec![(**p2).clone()];
                                    r.extend(ps.iter().cloned());
                                    r
                                },
                            };
                            let mut expanded = vec![ctx1, ctx2];
                            expanded.extend(rem.iter().cloned());
                            filter_rec(matcher, &expanded)
                        }
                        PatternDesc::Tpat_alias(p_inner, _, _) => {
                            let ctx_new = Ctx {
                                left: l.left.clone(),
                                right: {
                                    let mut r = vec![(**p_inner).clone()];
                                    r.extend(ps.iter().cloned());
                                    r
                                },
                            };
                            let mut expanded = vec![ctx_new];
                            expanded.extend(rem.iter().cloned());
                            filter_rec(matcher, &expanded)
                        }
                        PatternDesc::Tpat_var(..) => {
                            let ctx_new = Ctx {
                                left: l.left.clone(),
                                right: {
                                    let mut r = vec![omega()];
                                    r.extend(ps.iter().cloned());
                                    r
                                },
                            };
                            let mut expanded = vec![ctx_new];
                            expanded.extend(rem.iter().cloned());
                            filter_rec(matcher, &expanded)
                        }
                        _ => {
                            let mut rest = filter_rec(matcher, rem);
                            match matcher(p, ps) {
                                Ok((to_left, right)) => {
                                    let mut left = vec![to_left];
                                    left.extend(l.left.iter().cloned());
                                    rest.insert(0, Ctx { left, right });
                                    rest
                                }
                                Err(_) => rest,
                            }
                        }
                    },
                }
            }
        }
    }

    filter_rec(&*matcher, ctx)
}

// ============================================================================
// select_columns, ctx_lub, ctx_match
// ============================================================================

/// Select columns from pattern rows and combine with context.
/// Equivalent to OCaml's `select_columns`.
pub fn select_columns(pss: &Matrix, ctx: &[Ctx]) -> Vec<Ctx> {
    let n = ncols(pss);
    let mut result = Vec::new();
    for ps in pss.iter().rev() {
        for c in ctx.iter().rev() {
            let (transfert, right) = nchars(n, &c.right);
            match lubs_checked(&transfert, ps) {
                Ok(lub_result) => {
                    let mut left = lub_result;
                    left.extend(c.left.iter().cloned());
                    result.push(Ctx { left, right });
                }
                Err(Empty) => { /* skip incompatible */ }
            }
        }
    }
    result.reverse();
    result
}

/// Helper: lubs that returns Result.
fn lubs_checked(ps: &[Pattern], qs: &[Pattern]) -> Result<Vec<Pattern>, Empty> {
    lubs(ps, qs)
}

/// Least upper bound of a pattern with contexts.
/// Equivalent to OCaml's `ctx_lub`.
pub fn ctx_lub(p: &Pattern, ctx: &[Ctx]) -> Vec<Ctx> {
    let mut result = Vec::new();
    for c in ctx.iter().rev() {
        match c.right.split_first() {
            Some((q, rem)) => match lub(p, q) {
                Ok(r) => {
                    let mut right = vec![r];
                    right.extend(rem.iter().cloned());
                    result.push(Ctx {
                        left: c.left.clone(),
                        right,
                    });
                }
                Err(Empty) => { /* skip */ }
            },
            None => panic!("Matching.ctx_lub: empty right"),
        }
    }
    result.reverse();
    result
}

/// Check if any context's right side may be compatible with any row in pss.
/// Equivalent to OCaml's `ctx_match`.
pub fn ctx_match(ctx: &[Ctx], pss: &Matrix) -> bool {
    ctx.iter().any(|c| {
        pss.iter()
            .any(|ps| may_compats(&c.right, ps))
    })
}

// ============================================================================
// Jumps — mapping from exit numbers to context lists
// ============================================================================

/// Jump table: sorted list of (exit_number, context_list) pairs,
/// sorted in descending order by exit number.
pub type Jumps = Vec<(i32, Vec<Ctx>)>;

/// Extract the contexts for exit number i, returning (extracted, remaining).
pub fn jumps_extract(i: i32, jumps: &Jumps) -> (Vec<Ctx>, Jumps) {
    match jumps.split_first() {
        None => (Vec::new(), Vec::new()),
        Some(((j, pss), rem)) => {
            if i == *j {
                (pss.clone(), rem.to_vec())
            } else if *j < i {
                (Vec::new(), jumps.to_vec())
            } else {
                let (r, mut remaining) = jumps_extract(i, &rem.to_vec());
                remaining.insert(0, (*j, pss.clone()));
                (r, remaining)
            }
        }
    }
}

/// Remove the entry for exit number i.
pub fn jumps_remove(i: i32, jumps: &Jumps) -> Jumps {
    match jumps.split_first() {
        None => Vec::new(),
        Some(((j, _), rem)) if i == *j => rem.to_vec(),
        Some((x, rem)) => {
            let mut result = vec![x.clone()];
            result.extend(jumps_remove(i, &rem.to_vec()));
            result
        }
    }
}

/// Empty jump table.
pub fn jumps_empty() -> Jumps {
    Vec::new()
}

/// Check if a jump table is empty.
pub fn jumps_is_empty(jumps: &Jumps) -> bool {
    jumps.is_empty()
}

/// Create a singleton jump table (or empty if ctx is empty).
pub fn jumps_singleton(i: i32, ctx: Vec<Ctx>) -> Jumps {
    if ctx.is_empty() {
        Vec::new()
    } else {
        vec![(i, ctx)]
    }
}

/// Add contexts for exit number i to the jump table.
/// Maintains descending sort order and merges with get_mins when
/// the exit number already exists.
pub fn jumps_add(i: i32, pss: Vec<Ctx>, mut jumps: Jumps) -> Jumps {
    if pss.is_empty() {
        return jumps;
    }
    fn add(i: i32, pss: Vec<Ctx>, jumps: &[(i32, Vec<Ctx>)]) -> Jumps {
        match jumps.split_first() {
            None => vec![(i, pss)],
            Some(((j, qss), rem)) => {
                if *j > i {
                    let mut result = vec![(j.clone(), qss.clone())];
                    result.extend(add(i, pss, rem));
                    result
                } else if *j < i {
                    let mut result = vec![(i, pss)];
                    result.extend(jumps.to_vec());
                    result
                } else {
                    // Same exit number: merge with get_mins
                    let mut combined = pss;
                    combined.extend(qss.iter().cloned());
                    let mut result = vec![(i, get_mins(le_ctx, combined))];
                    result.extend(rem.to_vec());
                    result
                }
            }
        }
    }
    add(i, pss, &jumps)
}

/// Union of two jump tables.
/// Maintains descending sort order and merges contexts with get_mins.
pub fn jumps_union(env1: &Jumps, env2: &Jumps) -> Jumps {
    match (env1.split_first(), env2.split_first()) {
        (None, _) => env2.clone(),
        (_, None) => env1.clone(),
        (Some(((i1, pss1), rem1)), Some(((i2, pss2), rem2))) => {
            if i1 == i2 {
                let mut combined = pss1.clone();
                combined.extend(pss2.iter().cloned());
                let mut result = vec![(*i1, get_mins(le_ctx, combined))];
                result.extend(jumps_union(&rem1.to_vec(), &rem2.to_vec()));
                result
            } else if i1 > i2 {
                let mut result = vec![(*i1, pss1.clone())];
                result.extend(jumps_union(&rem1.to_vec(), env2));
                result
            } else {
                let mut result = vec![(*i2, pss2.clone())];
                result.extend(jumps_union(env1, &rem2.to_vec()));
                result
            }
        }
    }
}

/// Merge adjacent pairs of jump tables (used by jumps_unions).
fn merge(envs: Vec<Jumps>) -> Vec<Jumps> {
    if envs.len() < 2 {
        return envs;
    }
    let mut result = Vec::new();
    let mut iter = envs.into_iter();
    loop {
        match (iter.next(), iter.next()) {
            (Some(e1), Some(e2)) => result.push(jumps_union(&e1, &e2)),
            (Some(e1), None) => {
                result.push(e1);
                break;
            }
            (None, _) => break,
        }
    }
    result
}

/// Union of a list of jump tables (using balanced merge).
pub fn jumps_unions(envs: Vec<Jumps>) -> Jumps {
    match envs.len() {
        0 => Vec::new(),
        1 => envs.into_iter().next().unwrap(),
        _ => jumps_unions(merge(envs)),
    }
}

/// Map a function over the context lists in a jump table.
pub fn jumps_map(f: impl Fn(Vec<Ctx>) -> Vec<Ctx>, env: &Jumps) -> Jumps {
    env.iter()
        .map(|(i, pss)| (*i, f(pss.clone())))
        .collect()
}

// ============================================================================
// Pattern matching before compilation
// ============================================================================

/// Pattern matching before any compilation.
/// Equivalent to OCaml's `pattern_matching`.
#[derive(Clone)]
pub struct PatternMatching {
    /// Cases: list of (pattern_row, action).
    pub cases: Vec<(Vec<Pattern>, RawLambda)>,
    /// Arguments to match against: (expression, let_kind).
    pub args: Vec<(RawLambda, LetKind)>,
    /// Default: mapping from matrices to exit numbers.
    pub default: DefaultEnv,
}

// ============================================================================
// Pattern matching after or-pat and mixture rule application
// ============================================================================

/// Pattern matching after application of both the or-pat rule and the
/// mixture rule.
#[derive(Clone)]
pub struct PmOrCompiled {
    /// The body pattern matching.
    pub body: PatternMatching,
    /// Handlers for or-patterns: (matrix, exit_number, idents, pattern_matching).
    pub handlers: Vec<(Matrix, i32, Vec<Ident>, PatternMatching)>,
    /// The or-pattern matrix.
    pub or_matrix: Matrix,
}

/// Half-compiled pattern matching.
#[derive(Clone)]
pub enum PmHalfCompiled {
    /// Or-pattern compiled.
    PmOr(PmOrCompiled),
    /// Variable case.
    PmVar(PmVarCompiled),
    /// Simple pattern matching.
    Pm(PatternMatching),
}

/// Variable case in half-compiled pattern matching.
#[derive(Clone)]
pub struct PmVarCompiled {
    /// The inner half-compiled pattern matching.
    pub inside: Box<PmHalfCompiled>,
    /// The variable argument.
    pub var_arg: RawLambda,
}

/// Half-compiled pattern matching with associated info.
pub struct PmHalfCompiledInfo {
    /// The half-compiled pattern matching.
    pub me: PmHalfCompiled,
    /// The associated matrix.
    pub matrix: Matrix,
    /// The top-level default environment.
    pub top_default: DefaultEnv,
}

// ============================================================================
// Layer 2: Catch/exit and action sharing
// ============================================================================
// Ported from OCaml's matching.ml lines 442-587.

// ============================================================================
// Lambda.make_key — normalize a RawLambda for structural comparison
// ============================================================================

/// Maximum size for make_key normalization (matches OCaml's max_raw = 32).
const MAX_RAW: i32 = 32;

/// Normalize a RawLambda for structural comparison.
/// - Alias lets are substituted (variable replaced by its definition)
/// - Other let-bound variables get sequential normalized names
/// - Locations are cleared
/// Returns None if the lambda is too complex (functions, letrec, loops, etc.)
///
/// Equivalent to OCaml's `Lambda.make_key`.
fn make_key(e: &RawLambda) -> Option<RawLambda> {
    let mut count = 0i32;
    fn tr_rec(
        env: &HashMap<Ident, RawLambda>,
        e: &RawLambda,
        count: &mut i32,
        next_id: &mut i32,
    ) -> Option<RawLambda> {
        *count += 1;
        if *count > MAX_RAW {
            return None; // Too big
        }
        match e {
            RawLambda::Lvar(id) => {
                if let Some(replacement) = env.get(id) {
                    Some(replacement.clone())
                } else {
                    Some(e.clone())
                }
            }
            RawLambda::Lconst(crate::lambda::Constant::String { .. }) => {
                // Mutable constants are not shared
                None
            }
            RawLambda::Lconst(_) => Some(e.clone()),
            RawLambda::LglobalModule(_, _) => Some(e.clone()),
            RawLambda::Lapply(ap) => {
                let func = tr_rec(env, &ap.ap_func, count, next_id)?;
                let args = tr_recs(env, &ap.ap_args, count, next_id)?;
                Some(RawLambda::Lapply(RawApply {
                    ap_func: Box::new(func),
                    ap_args: args,
                    ..ap.clone()
                }))
            }
            RawLambda::Llet(LetKind::Alias, x, ex, body) => {
                // Ignore aliases -> substitute
                let ex = tr_rec(env, ex, count, next_id)?;
                let mut new_env = env.clone();
                new_env.insert(x.clone(), ex);
                tr_rec(&new_env, body, count, next_id)
            }
            RawLambda::Llet(kind, x, ex, body)
                if matches!(
                    (kind, body.as_ref()),
                    (LetKind::Strict | LetKind::StrictOpt, RawLambda::Lvar(v)) if v.same(x)
                ) =>
            {
                // Llet (Strict|StrictOpt, x, ex, Lvar v) when v same x -> tr_rec ex
                tr_rec(env, ex, count, next_id)
            }
            RawLambda::Llet(kind, x, ex, body) => {
                // Because of side effects, keep other lets with normalized names
                let ex_norm = tr_rec(env, ex, count, next_id)?;
                let y = Ident::new(x.name(), *next_id, IdentFlags::NONE);
                *next_id += 1;
                let mut new_env = env.clone();
                new_env.insert(x.clone(), RawLambda::Lvar(y.clone()));
                let body_norm = tr_rec(&new_env, body, count, next_id)?;
                Some(RawLambda::Llet(*kind, y, Box::new(ex_norm), Box::new(body_norm)))
            }
            RawLambda::Lprim(info) => {
                let args = tr_recs(env, &info.args, count, next_id)?;
                Some(RawLambda::Lprim(RawPrimInfo {
                    primitive: info.primitive.clone(),
                    args,
                    loc: Location::none(),
                }))
            }
            RawLambda::Lswitch(scrut, sw) => {
                let scrut_norm = tr_rec(env, scrut, count, next_id)?;
                let sw_norm = tr_sw(env, sw, count, next_id)?;
                Some(RawLambda::Lswitch(Box::new(scrut_norm), sw_norm))
            }
            RawLambda::LstringSwitch(scrut, cases, default) => {
                let scrut_norm = tr_rec(env, scrut, count, next_id)?;
                let mut norm_cases = Vec::new();
                for (s, act) in cases {
                    norm_cases.push((s.clone(), tr_rec(env, act, count, next_id)?));
                }
                let norm_default = tr_opt(env, default.as_deref(), count, next_id)?;
                Some(RawLambda::LstringSwitch(
                    Box::new(scrut_norm),
                    norm_cases,
                    norm_default.map(Box::new),
                ))
            }
            RawLambda::LstaticRaise(i, es) => {
                let args = tr_recs(env, es, count, next_id)?;
                Some(RawLambda::LstaticRaise(*i, args))
            }
            RawLambda::LstaticCatch(e1, xs, e2) => {
                let e1_norm = tr_rec(env, e1, count, next_id)?;
                let e2_norm = tr_rec(env, e2, count, next_id)?;
                Some(RawLambda::LstaticCatch(
                    Box::new(e1_norm),
                    xs.clone(),
                    Box::new(e2_norm),
                ))
            }
            RawLambda::LtryWith(e1, x, e2) => {
                let e1_norm = tr_rec(env, e1, count, next_id)?;
                let e2_norm = tr_rec(env, e2, count, next_id)?;
                Some(RawLambda::LtryWith(
                    Box::new(e1_norm),
                    x.clone(),
                    Box::new(e2_norm),
                ))
            }
            RawLambda::LifThenElse(cond, ifso, ifnot) => {
                let cond_norm = tr_rec(env, cond, count, next_id)?;
                let ifso_norm = tr_rec(env, ifso, count, next_id)?;
                let ifnot_norm = tr_rec(env, ifnot, count, next_id)?;
                Some(RawLambda::LifThenElse(
                    Box::new(cond_norm),
                    Box::new(ifso_norm),
                    Box::new(ifnot_norm),
                ))
            }
            RawLambda::Lsequence(e1, e2) => {
                let e1_norm = tr_rec(env, e1, count, next_id)?;
                let e2_norm = tr_rec(env, e2, count, next_id)?;
                Some(RawLambda::Lsequence(Box::new(e1_norm), Box::new(e2_norm)))
            }
            RawLambda::Lassign(x, e) => {
                let e_norm = tr_rec(env, e, count, next_id)?;
                Some(RawLambda::Lassign(x.clone(), Box::new(e_norm)))
            }
            RawLambda::Lsend(m, e1, _loc) => {
                let e1_norm = tr_rec(env, e1, count, next_id)?;
                Some(RawLambda::Lsend(m.clone(), Box::new(e1_norm), Location::none()))
            }
            // Functions, letrec, loops are not simple
            RawLambda::Lletrec(..) | RawLambda::Lfunction(..)
            | RawLambda::Lfor(..) | RawLambda::Lwhile(..) => None,
        }
    }

    fn tr_recs(
        env: &HashMap<Ident, RawLambda>,
        es: &[RawLambda],
        count: &mut i32,
        next_id: &mut i32,
    ) -> Option<Vec<RawLambda>> {
        es.iter().map(|e| tr_rec(env, e, count, next_id)).collect()
    }

    fn tr_sw(
        env: &HashMap<Ident, RawLambda>,
        sw: &RawLambdaSwitch,
        count: &mut i32,
        next_id: &mut i32,
    ) -> Option<RawLambdaSwitch> {
        let mut consts = Vec::new();
        for (tag, act) in &sw.sw_consts {
            consts.push((*tag, tr_rec(env, act, count, next_id)?));
        }
        let mut blocks = Vec::new();
        for (tag, act) in &sw.sw_blocks {
            blocks.push((*tag, tr_rec(env, act, count, next_id)?));
        }
        let fail = tr_opt(env, sw.sw_failaction.as_deref(), count, next_id)?;
        Some(RawLambdaSwitch {
            sw_consts_full: sw.sw_consts_full,
            sw_consts: consts,
            sw_blocks_full: sw.sw_blocks_full,
            sw_blocks: blocks,
            sw_failaction: fail.map(Box::new),
            sw_names: sw.sw_names.clone(),
        })
    }

    fn tr_opt(
        env: &HashMap<Ident, RawLambda>,
        e: Option<&RawLambda>,
        count: &mut i32,
        next_id: &mut i32,
    ) -> Option<Option<RawLambda>> {
        match e {
            None => Some(None),
            Some(e) => Some(Some(tr_rec(env, e, count, next_id)?)),
        }
    }

    let mut next_id = 0i32;
    tr_rec(&HashMap::new(), e, &mut count, &mut next_id)
}

/// Convert a RawLambda to a string key for comparison purposes.
/// Returns None if the lambda cannot be normalized.
fn make_key_string(e: &RawLambda) -> Option<String> {
    make_key(e).map(|k| format!("{}", RawLambdaPrinter::new(&k)))
}

// ============================================================================
// StoreExp — Action deduplication using make_key
// ============================================================================
// Ported from OCaml's Switch.Store, specialized for lambda/RawLambda.

/// Whether an action should be shared or is a singleton.
#[derive(Debug, Clone)]
pub enum SharedAction {
    Shared(RawLambda),
    Single(RawLambda),
}

/// Action store for deduplicating lambda actions.
/// Equivalent to OCaml's `StoreExp` (Switch.Store specialized for lambda).
///
/// Uses string keys (from `make_key` normalization) for comparison,
/// since RawLambda doesn't implement PartialEq/Ord.
pub struct StoreExp {
    /// Map from normalized key string -> (shared, index).
    map: BTreeMap<String, (bool, usize)>,
    /// Next index to assign.
    next: usize,
    /// Accumulated actions in reverse order: (must_share, action).
    acts: Vec<(bool, RawLambda)>,
}

impl StoreExp {
    /// Create a new empty store.
    /// Equivalent to OCaml's `mk_store`.
    pub fn mk_store() -> Self {
        StoreExp {
            map: BTreeMap::new(),
            next: 0,
            acts: Vec::new(),
        }
    }

    /// Internal: add an action unconditionally (no dedup).
    fn add(&mut self, must_share: bool, act: RawLambda) -> usize {
        let i = self.next;
        self.acts.push((must_share, act));
        self.next = i + 1;
        i
    }

    /// Internal: store an action, deduplicating if possible.
    fn store(&mut self, must_share: bool, act: RawLambda) -> usize {
        match make_key_string(&act) {
            Some(key) => {
                if let Some(&(shared, i)) = self.map.get(&key) {
                    if !shared {
                        self.map.insert(key, (true, i));
                    }
                    i
                } else {
                    let i = self.add(must_share, act);
                    self.map.insert(key, (must_share, i));
                    i
                }
            }
            None => self.add(must_share, act),
        }
    }

    /// Store an action (not forced shared).
    /// Equivalent to OCaml's `act_store`.
    pub fn act_store(&mut self, act: RawLambda) -> usize {
        self.store(false, act)
    }

    /// Store an action that must be shared.
    /// Equivalent to OCaml's `act_store_shared`.
    pub fn act_store_shared(&mut self, act: RawLambda) -> usize {
        self.store(true, act)
    }

    /// Get the actions array with sharing info.
    /// Actions that were stored multiple times or marked as must-share
    /// are wrapped in `Shared`; others are `Single`.
    /// Equivalent to OCaml's `act_get_shared`.
    pub fn act_get_shared(&self) -> Vec<SharedAction> {
        // Build initial array from acts list (reversed in OCaml via List.rev_map)
        let mut result: Vec<SharedAction> = self
            .acts
            .iter()
            .map(|(shared, act)| {
                if *shared {
                    SharedAction::Shared(act.clone())
                } else {
                    SharedAction::Single(act.clone())
                }
            })
            .collect();

        // Mark any action that was found in the map as shared (even if not must_share)
        for (_, &(shared, i)) in self.map.iter() {
            if shared {
                if let Some(SharedAction::Single(act)) = result.get(i) {
                    let act = act.clone();
                    result[i] = SharedAction::Shared(act);
                }
            }
        }

        result
    }
}

// ============================================================================
// make_exit — Lstaticraise(i, [])
// ============================================================================

/// Create a static raise with no arguments.
/// Equivalent to OCaml's `make_exit`.
pub fn make_exit(i: i32) -> RawLambda {
    RawLambda::LstaticRaise(i, Vec::new())
}

// ============================================================================
// make_catch — Introduce catch if worth it
// ============================================================================

/// Introduce a catch around `k(d)`, if `d` is not already a simple exit.
/// If `d` is already `Lstaticraise(_, [])`, just returns `k(d)`.
/// Otherwise, allocates a new exit number, returns `Lstaticcatch(k(exit(e)), (e,[]), d)`.
///
/// Equivalent to OCaml's `make_catch`.
pub fn make_catch(
    d: RawLambda,
    next_raise_count: &mut i32,
    k: impl FnOnce(RawLambda) -> RawLambda,
) -> RawLambda {
    match &d {
        RawLambda::LstaticRaise(_, args) if args.is_empty() => k(d),
        _ => {
            *next_raise_count += 1;
            let e = *next_raise_count;
            RawLambda::LstaticCatch(
                Box::new(k(make_exit(e))),
                (e, Vec::new()),
                Box::new(d),
            )
        }
    }
}

// ============================================================================
// as_simple_exit — Check if lambda is just an exit
// ============================================================================

/// Check if a lambda is just a static raise (possibly wrapped in alias lets).
/// Returns the exit number if so.
///
/// Equivalent to OCaml's `as_simple_exit`.
pub fn as_simple_exit(lam: &RawLambda) -> Option<i32> {
    match lam {
        RawLambda::LstaticRaise(i, args) if args.is_empty() => Some(*i),
        RawLambda::Llet(LetKind::Alias, _, _, e) => as_simple_exit(e),
        _ => None,
    }
}

// ============================================================================
// make_catch_delayed — Delayed catch with next_raise_count
// ============================================================================

/// Create a delayed catch: returns (exit_number, wrapper_fn).
/// If the handler is already a simple exit, the wrapper is the identity.
/// Otherwise, allocates a new exit number and returns a wrapper that
/// wraps the body in `Lstaticcatch(body, (i,[]), handler)` (or just returns
/// `handler` if body is `Lstaticraise(i, _)`).
///
/// Equivalent to OCaml's `make_catch_delayed`.
pub fn make_catch_delayed(
    handler: RawLambda,
    next_raise_count: &mut i32,
) -> (i32, Box<dyn FnOnce(RawLambda) -> RawLambda>) {
    match as_simple_exit(&handler) {
        Some(i) => (i, Box::new(|act| act)),
        None => {
            *next_raise_count += 1;
            let i = *next_raise_count;
            (
                i,
                Box::new(move |body: RawLambda| match &body {
                    RawLambda::LstaticRaise(j, _) if *j == i => handler,
                    _ => RawLambda::LstaticCatch(
                        Box::new(body),
                        (i, Vec::new()),
                        Box::new(handler),
                    ),
                }),
            )
        }
    }
}

// ============================================================================
// raw_action — Extract raw (normalized) action
// ============================================================================

/// Extract the raw (normalized) form of a lambda action.
/// If normalization succeeds, returns the normalized form; otherwise returns
/// the original.
///
/// Equivalent to OCaml's `raw_action`.
fn raw_action(l: &RawLambda) -> RawLambda {
    match make_key(l) {
        Some(k) => k,
        None => l.clone(),
    }
}

// ============================================================================
// tr_raw — Transform raw action with catch (raises on failure)
// ============================================================================

/// Normalize a lambda action. Returns None if normalization fails
/// (equivalent to OCaml's `tr_raw` which raises Exit on failure).
fn tr_raw(act: &RawLambda) -> Option<RawLambda> {
    make_key(act)
}

/// Convert a normalized RawLambda to a string for comparison.
fn lambda_to_string(lam: &RawLambda) -> String {
    format!("{}", RawLambdaPrinter::new(lam))
}

// ============================================================================
// same_actions — Check if all actions in a list are the same
// ============================================================================

/// Check if all actions in a case list are the same lambda.
/// Returns `Some(act)` with the first action if all are equal,
/// `None` otherwise.
///
/// Equivalent to OCaml's `same_actions`.
pub fn same_actions(cases: &[(Vec<Pattern>, RawLambda)]) -> Option<RawLambda> {
    match cases {
        [] => None,
        [(_, act)] => Some(act.clone()),
        [(_, act0), rem @ ..] => {
            let raw_act0 = tr_raw(act0)?;
            let raw_act0_str = lambda_to_string(&raw_act0);
            for (_, act) in rem {
                let raw_act = tr_raw(act)?;
                if lambda_to_string(&raw_act) != raw_act0_str {
                    return None;
                }
            }
            Some(act0.clone())
        }
    }
}

// ============================================================================
// up_ok_action — Check if swapping two actions is safe
// ============================================================================

/// Check if two actions are equivalent (safe to swap).
/// Returns true if both can be normalized and their normalized forms are equal.
///
/// Equivalent to OCaml's `up_ok_action`.
fn up_ok_action(act1: &RawLambda, act2: &RawLambda) -> bool {
    match (tr_raw(act1), tr_raw(act2)) {
        (Some(raw1), Some(raw2)) => lambda_to_string(&raw1) == lambda_to_string(&raw2),
        _ => false,
    }
}

// ============================================================================
// up_ok — Check if swapping two clauses is safe
// ============================================================================

/// Check if a clause `(ps, act_p)` can be moved past all clauses in `l`.
/// Safe to swap if either the actions are equivalent or the patterns
/// are incompatible.
///
/// Equivalent to OCaml's `up_ok`.
fn up_ok(ps: &[Pattern], act_p: &RawLambda, l: &[(Vec<Pattern>, RawLambda)]) -> bool {
    l.iter().all(|(qs, act_q)| {
        up_ok_action(act_p, act_q) || !may_compats(ps, qs)
    })
}

// ============================================================================
// simplify_or — Simplify or-patterns
// ============================================================================

/// Exception used internally by simplify_or to propagate variable patterns up.
enum VarPat {
    Var(Pattern),
}

/// Simplify an or-pattern:
/// - `_|p` becomes `_` (propagated as Var)
/// - Records are expanded to all fields
/// - Aliases are preserved around or-patterns
///
/// Equivalent to OCaml's `simplify_or`.
fn simplify_or(ctx_ref: Option<&TypeContext<'_>>, p: &Pattern) -> Pattern {
    fn simpl_rec(ctx_ref: Option<&TypeContext<'_>>, p: &Pattern) -> Result<Pattern, VarPat> {
        match &p.pat_desc {
            PatternDesc::Tpat_any | PatternDesc::Tpat_var(..) => {
                Err(VarPat::Var(p.clone()))
            }
            PatternDesc::Tpat_alias(q, id, s) => {
                match simpl_rec(ctx_ref, q) {
                    Ok(q_simplified) => Ok(Pattern {
                        pat_desc: PatternDesc::Tpat_alias(
                            Box::new(q_simplified),
                            id.clone(),
                            s.clone(),
                        ),
                        ..p.clone()
                    }),
                    Err(VarPat::Var(q_var)) => Err(VarPat::Var(Pattern {
                        pat_desc: PatternDesc::Tpat_alias(
                            Box::new(q_var),
                            id.clone(),
                            s.clone(),
                        ),
                        ..p.clone()
                    })),
                }
            }
            PatternDesc::Tpat_or(p1, p2, o) => {
                let q1 = simpl_rec(ctx_ref, p1)?; // propagates Var if p1 is variable
                match simpl_rec(ctx_ref, p2) {
                    Ok(q2) => Ok(Pattern {
                        pat_desc: PatternDesc::Tpat_or(
                            Box::new(q1),
                            Box::new(q2),
                            o.clone(),
                        ),
                        ..p.clone()
                    }),
                    Err(VarPat::Var(q2)) => Err(VarPat::Var(Pattern {
                        pat_desc: PatternDesc::Tpat_or(
                            Box::new(q1),
                            Box::new(q2),
                            o.clone(),
                        ),
                        ..p.clone()
                    })),
                }
            }
            PatternDesc::Tpat_record(lbls, closed) => {
                let all_lbls = all_record_args(ctx_ref, p.pat_type, p.pat_env, lbls);
                Ok(Pattern {
                    pat_desc: PatternDesc::Tpat_record(all_lbls, *closed),
                    ..p.clone()
                })
            }
            _ => Ok(p.clone()),
        }
    }

    match simpl_rec(ctx_ref, p) {
        Ok(p) => p,
        Err(VarPat::Var(p)) => p,
    }
}

// ============================================================================
// simplify_cases — Simplify all cases (swap optimization)
// ============================================================================

/// Bind a variable to an argument in an action.
/// Equivalent to OCaml's `Lambda.bind Alias id arg action`.
fn bind(kind: LetKind, id: &Ident, arg: &RawLambda, action: RawLambda) -> RawLambda {
    match arg {
        RawLambda::Lvar(v) if v.same(id) => action,
        _ => RawLambda::Llet(kind, id.clone(), Box::new(arg.clone()), Box::new(action)),
    }
}

/// Simplify the first column of a match:
/// - Variables are replaced with omega and bound in the action
/// - Aliases are removed and replaced by bindings in actions
/// - Records are expanded to all fields
/// - Or-patterns are simplified (but not removed)
///
/// Equivalent to OCaml's `simplify_cases`.
pub fn simplify_cases(
    ctx_ref: Option<&TypeContext<'_>>,
    args: &[(RawLambda, LetKind)],
    cls: Vec<(Vec<Pattern>, RawLambda)>,
) -> Vec<(Vec<Pattern>, RawLambda)> {
    assert!(!args.is_empty(), "simplify_cases: empty args");

    let (ref arg, _) = args[0];

    fn simplify(
        ctx_ref: Option<&TypeContext<'_>>,
        arg: &RawLambda,
        mut cls: Vec<(Vec<Pattern>, RawLambda)>,
    ) -> Vec<(Vec<Pattern>, RawLambda)> {
        if cls.is_empty() {
            return Vec::new();
        }

        let (pats, action) = cls.remove(0);
        assert!(!pats.is_empty(), "simplify_cases: empty pattern row");

        let pat = &pats[0];
        let patl = &pats[1..];

        match &pat.pat_desc {
            PatternDesc::Tpat_var(id, _) => {
                let new_action = bind(LetKind::Alias, id, arg, action);
                let mut row = vec![omega()];
                row.extend(patl.iter().cloned());
                let mut result = vec![(row, new_action)];
                result.extend(simplify(ctx_ref, arg, cls));
                result
            }
            PatternDesc::Tpat_any => {
                let mut result = vec![(pats, action)];
                result.extend(simplify(ctx_ref, arg, cls));
                result
            }
            PatternDesc::Tpat_alias(p, id, _) => {
                let new_action = bind(LetKind::Alias, id, arg, action);
                let mut new_pats = vec![(**p).clone()];
                new_pats.extend(patl.iter().cloned());
                cls.insert(0, (new_pats, new_action));
                simplify(ctx_ref, arg, cls)
            }
            PatternDesc::Tpat_record(lbls, _) if lbls.is_empty() => {
                let mut row = vec![omega()];
                row.extend(patl.iter().cloned());
                let mut result = vec![(row, action)];
                result.extend(simplify(ctx_ref, arg, cls));
                result
            }
            PatternDesc::Tpat_record(lbls, closed) => {
                let all_lbls = all_record_args(ctx_ref, pat.pat_type, pat.pat_env, lbls);
                let full_pat = Pattern {
                    pat_desc: PatternDesc::Tpat_record(all_lbls, *closed),
                    ..pat.clone()
                };
                let mut row = vec![full_pat];
                row.extend(patl.iter().cloned());
                let mut result = vec![(row, action)];
                result.extend(simplify(ctx_ref, arg, cls));
                result
            }
            PatternDesc::Tpat_or(..) => {
                let pat_simple = simplify_or(ctx_ref, pat);
                match &pat_simple.pat_desc {
                    PatternDesc::Tpat_or(..) => {
                        let mut row = vec![pat_simple];
                        row.extend(patl.iter().cloned());
                        let mut result = vec![(row, action)];
                        result.extend(simplify(ctx_ref, arg, cls));
                        result
                    }
                    _ => {
                        // Simplified away the or — re-process
                        let mut new_pats = vec![pat_simple];
                        new_pats.extend(patl.iter().cloned());
                        cls.insert(0, (new_pats, action));
                        simplify(ctx_ref, arg, cls)
                    }
                }
            }
            _ => {
                let mut result = vec![(pats, action)];
                result.extend(simplify(ctx_ref, arg, cls));
                result
            }
        }
    }

    simplify(ctx_ref, arg, cls)
}

// ============================================================================
// what_is_cases — Determine what kind of patterns are in cases
// ============================================================================

/// Determine what kind of pattern the first non-wildcard case has.
/// Returns the first non-wildcard pattern, or omega if all are wildcards.
///
/// Equivalent to OCaml's `what_is_cases`.
pub fn what_is_cases(cases: &[(Vec<Pattern>, RawLambda)]) -> Pattern {
    match cases.split_first() {
        None => omega(),
        Some(((pats, _), rem)) => {
            assert!(!pats.is_empty(), "what_is_cases: empty pattern row");
            match &pats[0].pat_desc {
                PatternDesc::Tpat_any => what_is_cases(rem),
                PatternDesc::Tpat_var(..) | PatternDesc::Tpat_or(..) | PatternDesc::Tpat_alias(..) => {
                    panic!("what_is_cases: applies to simplified matchings only")
                }
                _ => pats[0].clone(),
            }
        }
    }
}

// ============================================================================
// as_matrix, cons_default, default_compat — Default environment helpers
// ============================================================================
// Ported from OCaml's matching.ml lines 588-607.

/// Convert cases to a pattern matrix (taking the minimal rows under le_pats).
/// Equivalent to OCaml's `as_matrix`.
pub fn as_matrix(cases: &[(Vec<Pattern>, RawLambda)]) -> Matrix {
    let rows: Vec<Vec<Pattern>> = cases.iter().map(|(ps, _)| ps.clone()).collect();
    get_mins(|a: &Vec<Pattern>, b: &Vec<Pattern>| le_pats(a, b), rows)
}

/// Prepend a matrix entry to the default environment, skipping empty matrices.
/// Equivalent to OCaml's `cons_default`.
pub fn cons_default(matrix: Matrix, raise_num: i32, default: DefaultEnv) -> DefaultEnv {
    if matrix.is_empty() {
        default
    } else {
        let mut result = vec![(matrix, raise_num)];
        result.extend(default);
        result
    }
}

/// Filter a default environment for entries compatible with pattern p.
/// For each entry (pss, i), keep only rows whose first pattern is compatible
/// with p, and drop the first column.
///
/// Equivalent to OCaml's `default_compat`.
pub fn default_compat(p: &Pattern, def: &DefaultEnv) -> DefaultEnv {
    def.iter()
        .rev()
        .fold(Vec::new(), |r, (pss, i)| {
            let qss: Vec<Vec<Pattern>> = pss
                .iter()
                .filter_map(|qs| {
                    match qs.split_first() {
                        Some((q, rem)) if may_compat(p, q) => Some(rem.to_vec()),
                        _ => None,
                    }
                })
                .collect();
            if qss.is_empty() {
                r
            } else {
                let mut result = vec![(qss, *i)];
                result.extend(r);
                result
            }
        })
}

// ============================================================================
// Layer 3: Default environments and or-patterns
// Ported from OCaml's matching.ml lines 612-657
// ============================================================================

/// Type alias for the set of identifiers (equivalent to OCaml's IdentSet).
type IdentSet = BTreeSet<Ident>;

/// Recursively extract all variables bound in a pattern.
/// Equivalent to OCaml's `extract_vars`.
pub fn extract_vars(r: IdentSet, p: &Pattern) -> IdentSet {
    match &p.pat_desc {
        PatternDesc::Tpat_var(id, _) => {
            let mut r = r;
            r.insert(id.clone());
            r
        }
        PatternDesc::Tpat_alias(p, id, _) => {
            let mut r = r;
            r.insert(id.clone());
            extract_vars(r, p)
        }
        PatternDesc::Tpat_tuple(pats) => {
            pats.iter().fold(r, |r, p| extract_vars(r, p))
        }
        PatternDesc::Tpat_record(lpats, _) => {
            lpats.iter().fold(r, |r, (_, _, p, _)| extract_vars(r, p))
        }
        PatternDesc::Tpat_construct(_, _, pats) => {
            pats.iter().fold(r, |r, p| extract_vars(r, p))
        }
        PatternDesc::Tpat_array(pats) => {
            pats.iter().fold(r, |r, p| extract_vars(r, p))
        }
        PatternDesc::Tpat_variant(_, Some(p), _) => extract_vars(r, p),
        PatternDesc::Tpat_or(p, _, _) => extract_vars(r, p),
        PatternDesc::Tpat_constant(_)
        | PatternDesc::Tpat_any
        | PatternDesc::Tpat_variant(_, None, _) => r,
    }
}

/// Error raised when an or-pattern cannot be flattened because
/// an aliased variable needs a binding but no argument is available.
/// Equivalent to OCaml's `Cannot_flatten` exception.
#[derive(Debug)]
pub struct CannotFlatten;

/// Create an alpha-renaming environment mapping each id in `ids` to either
/// the match argument (if id is in aliases) or a fresh ident with the same name.
/// Raises `CannotFlatten` if an alias id has no argument.
/// Equivalent to OCaml's `mk_alpha_env`.
pub fn mk_alpha_env(
    arg: &Option<Ident>,
    aliases: &[Ident],
    ids: &IdentSet,
) -> Result<Vec<(Ident, Ident)>, CannotFlatten> {
    ids.iter()
        .map(|id| {
            let new_id = if aliases.contains(id) {
                match arg {
                    Some(v) => v.clone(),
                    None => return Err(CannotFlatten),
                }
            } else {
                Ident::create_local(id.name())
            };
            Ok((id.clone(), new_id))
        })
        .collect()
}

// ---------------------------------------------------------------------------
// Alpha-renaming for patterns (local copy, mirrors Typedtree.alpha_pat)
// ---------------------------------------------------------------------------

/// Look up an identifier in the alpha-renaming environment.
fn alpha_pat_id<'a>(env: &'a [(Ident, Ident)], id: &Ident) -> Option<&'a Ident> {
    env.iter()
        .find_map(|(from, to)| if from.same(id) { Some(to) } else { None })
}

/// Apply an alpha-renaming environment to a pattern.
/// Equivalent to OCaml's `Typedtree.alpha_pat`.
fn alpha_pat(env: &[(Ident, Ident)], pat: &Pattern) -> Pattern {
    match &pat.pat_desc {
        PatternDesc::Tpat_var(id, name) => {
            let pat_desc = alpha_pat_id(env, id)
                .map(|new_id| PatternDesc::Tpat_var(new_id.clone(), name.clone()))
                .unwrap_or(PatternDesc::Tpat_any);
            Pattern {
                pat_desc,
                ..pat.clone()
            }
        }
        PatternDesc::Tpat_alias(inner, id, name) => {
            let new_inner = alpha_pat(env, inner);
            if let Some(new_id) = alpha_pat_id(env, id) {
                Pattern {
                    pat_desc: PatternDesc::Tpat_alias(
                        Box::new(new_inner),
                        new_id.clone(),
                        name.clone(),
                    ),
                    ..pat.clone()
                }
            } else {
                new_inner
            }
        }
        PatternDesc::Tpat_tuple(items) => Pattern {
            pat_desc: PatternDesc::Tpat_tuple(
                items.iter().map(|item| alpha_pat(env, item)).collect(),
            ),
            ..pat.clone()
        },
        PatternDesc::Tpat_construct(lid, cstr, args) => Pattern {
            pat_desc: PatternDesc::Tpat_construct(
                lid.clone(),
                cstr.clone(),
                args.iter().map(|arg| alpha_pat(env, arg)).collect(),
            ),
            ..pat.clone()
        },
        PatternDesc::Tpat_variant(label, arg, row) => Pattern {
            pat_desc: PatternDesc::Tpat_variant(
                label.clone(),
                arg.as_ref().map(|arg| Box::new(alpha_pat(env, arg))),
                *row,
            ),
            ..pat.clone()
        },
        PatternDesc::Tpat_record(fields, closed) => Pattern {
            pat_desc: PatternDesc::Tpat_record(
                fields
                    .iter()
                    .map(|(lid, lbl, field_pat, opt)| {
                        (lid.clone(), lbl.clone(), alpha_pat(env, field_pat), *opt)
                    })
                    .collect(),
                *closed,
            ),
            ..pat.clone()
        },
        PatternDesc::Tpat_array(items) => Pattern {
            pat_desc: PatternDesc::Tpat_array(
                items.iter().map(|item| alpha_pat(env, item)).collect(),
            ),
            ..pat.clone()
        },
        PatternDesc::Tpat_or(left, right, row) => Pattern {
            pat_desc: PatternDesc::Tpat_or(
                Box::new(alpha_pat(env, left)),
                Box::new(alpha_pat(env, right)),
                row.clone(),
            ),
            ..pat.clone()
        },
        _ => pat.clone(),
    }
}

/// Expand an or-pattern into separate cases with alpha-renamed variables.
///
/// `arg`: optional binding for alias variables
/// `patl`: surrounding pattern context
/// `mk_action`: closure that builds an action given a list of fresh idents
/// `rem`: accumulator of already-expanded cases
/// `vars`: set of variables that need alpha-renaming
/// `aliases`: accumulated alias identifiers from Tpat_alias wrappers
/// `pat`: the pattern being exploded
///
/// Equivalent to OCaml's `explode_or_pat`.
pub fn explode_or_pat<F>(
    arg: &Option<Ident>,
    patl: &[Pattern],
    mk_action: &F,
    rem: Vec<(Vec<Pattern>, RawLambda)>,
    vars: &IdentSet,
    aliases: &[Ident],
    pat: &Pattern,
) -> Result<Vec<(Vec<Pattern>, RawLambda)>, CannotFlatten>
where
    F: Fn(&[Ident]) -> RawLambda,
{
    match &pat.pat_desc {
        PatternDesc::Tpat_or(p1, p2, _) => {
            let rem = explode_or_pat(arg, patl, mk_action, rem, vars, aliases, p2)?;
            explode_or_pat(arg, patl, mk_action, rem, vars, aliases, p1)
        }
        PatternDesc::Tpat_alias(p, id, _) => {
            let mut new_aliases = vec![id.clone()];
            new_aliases.extend_from_slice(aliases);
            explode_or_pat(arg, patl, mk_action, rem, vars, &new_aliases, p)
        }
        PatternDesc::Tpat_var(x, _) => {
            let mut x_aliases = vec![x.clone()];
            x_aliases.extend_from_slice(aliases);
            let env = mk_alpha_env(arg, &x_aliases, vars)?;
            let new_ids: Vec<Ident> = env.iter().map(|(_, id)| id.clone()).collect();
            let mut row = vec![omega()];
            row.extend_from_slice(patl);
            let mut result = vec![(row, mk_action(&new_ids))];
            result.extend(rem);
            Ok(result)
        }
        _ => {
            let env = mk_alpha_env(arg, aliases, vars)?;
            let new_ids: Vec<Ident> = env.iter().map(|(_, id)| id.clone()).collect();
            let mut row = vec![alpha_pat(&env, pat)];
            row.extend_from_slice(patl);
            let mut result = vec![(row, mk_action(&new_ids))];
            result.extend(rem);
            Ok(result)
        }
    }
}

/// Compute the free variables of a pattern matching's actions.
/// Equivalent to OCaml's `pm_free_variables`.
pub fn pm_free_variables(pm: &PatternMatching) -> IdentSet {
    // OCaml uses IdentSet.union (free_variables act) r folded right over cases.
    // We use raw_free_variables (HashSet-based) and convert to BTreeSet.
    pm.cases.iter().rev().fold(BTreeSet::new(), |mut r, (_, act)| {
        let fv = raw_lambda_free_variables(act);
        r.extend(fv);
        r
    })
}

/// Compute free variables of a RawLambda expression.
/// Local helper equivalent to Lambda.free_variables, matching
/// the raw_free_variables in convert.rs.
fn raw_lambda_free_variables(lam: &RawLambda) -> IdentSet {
    fn collect(lam: &RawLambda, fv: &mut IdentSet) {
        match lam {
            RawLambda::Lvar(id) => {
                fv.insert(id.clone());
            }
            RawLambda::LglobalModule(_, _) | RawLambda::Lconst(_) => {}
            RawLambda::Lapply(apply) => {
                collect(&apply.ap_func, fv);
                for arg in &apply.ap_args {
                    collect(arg, fv);
                }
            }
            RawLambda::Lfunction(func) => {
                collect(&func.body, fv);
                for param in &func.params {
                    fv.remove(param);
                }
            }
            RawLambda::Llet(_, id, arg, body) => {
                collect(arg, fv);
                collect(body, fv);
                fv.remove(id);
            }
            RawLambda::Lletrec(bindings, body) => {
                collect(body, fv);
                for (_, expr) in bindings {
                    collect(expr, fv);
                }
                for (id, _) in bindings {
                    fv.remove(id);
                }
            }
            RawLambda::Lprim(info) => {
                for arg in &info.args {
                    collect(arg, fv);
                }
            }
            RawLambda::Lswitch(arg, sw) => {
                collect(arg, fv);
                for (_, lam) in &sw.sw_consts {
                    collect(lam, fv);
                }
                for (_, lam) in &sw.sw_blocks {
                    collect(lam, fv);
                }
                if let Some(fail) = &sw.sw_failaction {
                    collect(fail, fv);
                }
            }
            RawLambda::LstringSwitch(arg, cases, default) => {
                collect(arg, fv);
                for (_, lam) in cases {
                    collect(lam, fv);
                }
                if let Some(default) = default {
                    collect(default, fv);
                }
            }
            RawLambda::LstaticRaise(_, args) => {
                for arg in args {
                    collect(arg, fv);
                }
            }
            RawLambda::LstaticCatch(body, (_, vars), handler) => {
                collect(body, fv);
                collect(handler, fv);
                for var in vars {
                    fv.remove(var);
                }
            }
            RawLambda::LtryWith(body, exn, handler) => {
                collect(body, fv);
                collect(handler, fv);
                fv.remove(exn);
            }
            RawLambda::LifThenElse(cond, then_br, else_br) => {
                collect(cond, fv);
                collect(then_br, fv);
                collect(else_br, fv);
            }
            RawLambda::Lsequence(first, second) => {
                collect(first, fv);
                collect(second, fv);
            }
            RawLambda::Lwhile(cond, body) => {
                collect(cond, fv);
                collect(body, fv);
            }
            RawLambda::Lfor(id, lo, hi, _, body) => {
                collect(lo, fv);
                collect(hi, fv);
                collect(body, fv);
                fv.remove(id);
            }
            RawLambda::Lassign(id, expr) => {
                fv.insert(id.clone());
                collect(expr, fv);
            }
            RawLambda::Lsend(_, obj, _) => {
                collect(obj, fv);
            }
        }
    }

    let mut fv = BTreeSet::new();
    collect(lam, &mut fv);
    fv
}

// ============================================================================
// Layer 4: Grouping and splitting
// ============================================================================
// Ported from OCaml's matching.ml lines 659-1090.
// This layer implements the pattern grouping predicates, or-pattern
// operations, and the split/precompile functions that prepare pattern
// matchings for compilation.

// ============================================================================
// is_guarded — Check if an action has a guard (anticipated staticraise)
// ============================================================================
// Ported from OCaml's lambda.ml lines 603-606.

/// Check if a lambda action is guarded (contains `if ... then ... else staticraise(0, [])`).
/// Equivalent to OCaml's `Lambda.is_guarded`.
fn is_guarded(lam: &RawLambda) -> bool {
    match lam {
        RawLambda::LifThenElse(_, _, else_br) => {
            matches!(else_br.as_ref(), RawLambda::LstaticRaise(0, args) if args.is_empty())
        }
        RawLambda::Llet(_, _, _, body) => is_guarded(body),
        _ => false,
    }
}

// ============================================================================
// Group predicates (lines 659-700)
// ============================================================================

/// Extract the constructor description from a construct pattern.
/// Equivalent to OCaml's `pat_as_constr`.
fn pat_as_constr(p: &Pattern) -> &crate::types::ConstructorDescription {
    match &p.pat_desc {
        PatternDesc::Tpat_construct(_, cstr, _) => cstr,
        _ => panic!("Matching.pat_as_constr"),
    }
}

/// Group predicate for constant patterns.
/// Equivalent to OCaml's `group_constant`.
fn group_constant(p: &Pattern) -> bool {
    matches!(&p.pat_desc, PatternDesc::Tpat_constant(_))
}

/// Group predicate for constructor patterns.
/// Equivalent to OCaml's `group_constructor`.
fn group_constructor(p: &Pattern) -> bool {
    matches!(&p.pat_desc, PatternDesc::Tpat_construct(_, _, _))
}

/// Group predicate for variant patterns.
/// Equivalent to OCaml's `group_variant`.
fn group_variant(p: &Pattern) -> bool {
    matches!(&p.pat_desc, PatternDesc::Tpat_variant(_, _, _))
}

/// Group predicate for variable/wildcard patterns.
/// Equivalent to OCaml's `group_var`.
fn group_var(p: &Pattern) -> bool {
    matches!(&p.pat_desc, PatternDesc::Tpat_any)
}

/// Group predicate for tuple patterns (including wildcard).
/// Equivalent to OCaml's `group_tuple`.
fn group_tuple(p: &Pattern) -> bool {
    matches!(&p.pat_desc, PatternDesc::Tpat_tuple(_) | PatternDesc::Tpat_any)
}

/// Group predicate for record patterns (including wildcard).
/// Equivalent to OCaml's `group_record`.
fn group_record(p: &Pattern) -> bool {
    matches!(&p.pat_desc, PatternDesc::Tpat_record(_, _) | PatternDesc::Tpat_any)
}

/// Group predicate for array patterns.
/// Equivalent to OCaml's `group_array`.
fn group_array(p: &Pattern) -> bool {
    matches!(&p.pat_desc, PatternDesc::Tpat_array(_))
}

/// Get the appropriate group predicate for a pattern.
/// Equivalent to OCaml's `get_group`.
fn get_group(p: &Pattern) -> fn(&Pattern) -> bool {
    match &p.pat_desc {
        PatternDesc::Tpat_any => group_var,
        PatternDesc::Tpat_constant(_) => group_constant,
        PatternDesc::Tpat_construct(_, _, _) => group_constructor,
        PatternDesc::Tpat_tuple(_) => group_tuple,
        PatternDesc::Tpat_record(_, _) => group_record,
        PatternDesc::Tpat_array(_) => group_array,
        PatternDesc::Tpat_variant(_, _, _) => group_variant,
        _ => panic!("Matching.get_group"),
    }
}

/// Check if a pattern is an or-pattern.
/// Equivalent to OCaml's `is_or`.
fn is_or(p: &Pattern) -> bool {
    matches!(&p.pat_desc, PatternDesc::Tpat_or(_, _, _))
}

// ============================================================================
// Or-pattern operations (lines 708-773)
// ============================================================================

/// Condition (a) for appending to the Or matrix: p and q are incompatible.
/// Equivalent to OCaml's `conda`.
fn conda(p: &Pattern, q: &Pattern) -> bool {
    !may_compat(p, q)
}

/// Condition (b) for appending: action is not guarded and qs <= ps.
/// Equivalent to OCaml's `condb`.
fn condb(act: &RawLambda, ps: &[Pattern], qs: &[Pattern]) -> bool {
    !is_guarded(act) && le_pats(qs, ps)
}

/// Check if p can be appended/inserted into the or-matrix l, given
/// surrounding patterns ps.
/// Equivalent to OCaml's `or_ok`.
fn or_ok(p: &Pattern, ps: &[Pattern], l: &[(Vec<Pattern>, RawLambda)]) -> bool {
    l.iter().all(|(row, act)| {
        match row.split_first() {
            Some((q, qs)) if is_or(q) => conda(p, q) || condb(act, ps, qs),
            _ => true,
        }
    })
}

/// Check if two patterns are equivalent (each le the other).
/// Equivalent to OCaml's `equiv_pat`.
fn equiv_pat(p: &Pattern, q: &Pattern) -> bool {
    le_pat(p, q) && le_pat(q, p)
}

/// Get equivalent or-patterns from the front of the list.
/// Returns (equivalent_clauses, remaining_clauses).
/// Equivalent to OCaml's `get_equiv`.
fn get_equiv(
    p: &Pattern,
    l: &[(Vec<Pattern>, RawLambda)],
) -> (Vec<(Vec<Pattern>, RawLambda)>, Vec<(Vec<Pattern>, RawLambda)>) {
    match l.split_first() {
        Some((cl, rem)) => {
            match cl.0.first() {
                Some(q) if equiv_pat(p, q) => {
                    let (mut others, rem) = get_equiv(p, rem);
                    others.insert(0, cl.clone());
                    (others, rem)
                }
                _ => (Vec::new(), l.to_vec()),
            }
        }
        None => (Vec::new(), Vec::new()),
    }
}

/// Insert or append a pattern in the Or matrix.
/// Returns (updated_ors, updated_no).
/// Equivalent to OCaml's `insert_or_append`.
fn insert_or_append(
    p: &Pattern,
    ps: &[Pattern],
    act: &RawLambda,
    ors: Vec<(Vec<Pattern>, RawLambda)>,
    no: Vec<(Vec<Pattern>, RawLambda)>,
) -> (Vec<(Vec<Pattern>, RawLambda)>, Vec<(Vec<Pattern>, RawLambda)>) {
    fn attempt(
        seen: Vec<(Vec<Pattern>, RawLambda)>,
        rest: &[(Vec<Pattern>, RawLambda)],
        p: &Pattern,
        ps: &[Pattern],
        act: &RawLambda,
        ors: &[(Vec<Pattern>, RawLambda)],
        no: &[(Vec<Pattern>, RawLambda)],
    ) -> (Vec<(Vec<Pattern>, RawLambda)>, Vec<(Vec<Pattern>, RawLambda)>) {
        match rest.split_first() {
            Some((cl, rem)) => {
                let (q_head, qs) = match cl.0.split_first() {
                    Some((q, qs)) => (q, qs),
                    None => panic!("insert_or_append: empty pattern row"),
                };
                let act_q = &cl.1;
                if is_or(q_head) {
                    if may_compat(p, q_head) {
                        if extract_vars(BTreeSet::new(), p).is_empty()
                            && extract_vars(BTreeSet::new(), q_head).is_empty()
                            && equiv_pat(p, q_head)
                        {
                            // attempt insert, for equivalent orpats with no variables
                            let (_, not_e) = get_equiv(q_head, rem);
                            if or_ok(p, ps, &not_e)
                                && seen.iter().all(|seen_cl| {
                                    match seen_cl.0.first() {
                                        Some(q) => !may_compat(p, q),
                                        None => panic!("insert_or_append: empty seen row"),
                                    }
                                })
                            {
                                // insert
                                let mut new_p_row = vec![p.clone()];
                                new_p_row.extend_from_slice(ps);
                                let mut result: Vec<(Vec<Pattern>, RawLambda)> = Vec::new();
                                // List.rev_append seen ((p :: ps, act) :: cl :: rem)
                                for item in seen.into_iter().rev() {
                                    result.push(item);
                                }
                                result.push((new_p_row, act.clone()));
                                result.push(cl.clone());
                                result.extend_from_slice(rem);
                                return (result, no.to_vec());
                            } else {
                                // fail to insert or append
                                let mut new_p_row = vec![p.clone()];
                                new_p_row.extend_from_slice(ps);
                                let mut new_no = vec![(new_p_row, act.clone())];
                                new_no.extend_from_slice(no);
                                return (ors.to_vec(), new_no);
                            }
                        } else if condb(act_q, ps, qs) {
                            // check condition (b) for append
                            let mut new_seen = seen;
                            new_seen.insert(0, cl.clone());
                            return attempt(new_seen, rem, p, ps, act, ors, no);
                        } else {
                            let mut new_p_row = vec![p.clone()];
                            new_p_row.extend_from_slice(ps);
                            let mut new_no = vec![(new_p_row, act.clone())];
                            new_no.extend_from_slice(no);
                            return (ors.to_vec(), new_no);
                        }
                    } else {
                        // p # q, go on with append/insert
                        let mut new_seen = seen;
                        new_seen.insert(0, cl.clone());
                        return attempt(new_seen, rem, p, ps, act, ors, no);
                    }
                } else {
                    // q is not an or-pat, go on with append/insert
                    let mut new_seen = seen;
                    new_seen.insert(0, cl.clone());
                    return attempt(new_seen, rem, p, ps, act, ors, no);
                }
            }
            None => {
                // [] in fact — success in appending
                let mut new_p_row = vec![p.clone()];
                new_p_row.extend_from_slice(ps);
                let mut result = vec![(new_p_row, act.clone())];
                result.extend(ors.iter().cloned());
                // Wait — OCaml does (p :: ps, act) :: ors which prepends.
                // But actually: the seen list is empty at this point (all consumed),
                // and OCaml returns ((p :: ps, act) :: ors, no).
                // But ors here is the ORIGINAL ors, not what we've been iterating.
                // Actually, we're iterating ors itself. At this point we've consumed
                // all of ors (rest is empty), so ors should be reconstructed.
                // Let me re-read the OCaml...
                //
                // attempt [] ors  -- seen=[], iterating over ors
                // when we hit None (end of ors list):
                //   ((p :: ps, act) :: ors, no)
                // But ors here is the CLOSURE variable, the original ors!
                // So we prepend to the original ors list.
                //
                // Wait no, in OCaml the `ors` in the closure is the original parameter.
                // The function `attempt seen = function ...` iterates over its argument,
                // which IS ors (called as `attempt [] ors`).
                // When it reaches [], it returns ((p::ps, act) :: ors, no) using
                // the OUTER ors binding. But the outer ors IS the same list being iterated.
                // So this is: prepend new clause to ors.
                return (result, no.to_vec());
            }
        }
    }

    attempt(Vec::new(), &ors, p, ps, act, &ors, &no)
}

// ============================================================================
// Rebuild functions (lines 777-793)
// ============================================================================

/// Reconstruct a matrix from a half-compiled pattern matching.
/// Equivalent to OCaml's `rebuild_matrix`.
fn rebuild_matrix(pmh: &PmHalfCompiled) -> Matrix {
    match pmh {
        PmHalfCompiled::Pm(pm) => as_matrix(&pm.cases),
        PmHalfCompiled::PmOr(por) => por.or_matrix.clone(),
        PmHalfCompiled::PmVar(x) => add_omega_column(&rebuild_matrix(&x.inside)),
    }
}

/// Reconstruct default information from half-compiled pm list.
/// Equivalent to OCaml's `rebuild_default`.
fn rebuild_default(nexts: &[(i32, PmHalfCompiled)], def: DefaultEnv) -> DefaultEnv {
    match nexts.split_first() {
        None => def,
        Some(((e, pmh), rem)) => {
            let mut result = vec![(add_omega_column(&rebuild_matrix(pmh)), *e)];
            result.extend(rebuild_default(rem, def));
            result
        }
    }
}

/// Wrap nexts with PmVar nodes.
/// Equivalent to OCaml's `rebuild_nexts`.
fn rebuild_nexts(
    arg: &RawLambda,
    nexts: Vec<(i32, PmHalfCompiled)>,
    k: Vec<(i32, PmHalfCompiled)>,
) -> Vec<(i32, PmHalfCompiled)> {
    // List.fold_right (\(e, pm) k -> (e, PmVar {inside = pm; var_arg = arg}) :: k) nexts k
    nexts.into_iter().rev().fold(k, |mut acc, (e, pm)| {
        acc.insert(0, (e, PmHalfCompiled::PmVar(PmVarCompiled {
            inside: Box::new(pm),
            var_arg: arg.clone(),
        })));
        acc
    })
}

// ============================================================================
// Split functions (lines 814-1090)
// ============================================================================

/// Split a matching, directed first by or-patterns, then by tests/variable transitions.
/// Equivalent to OCaml's `split_or`.
fn split_or(
    ctx_ref: Option<&TypeContext<'_>>,
    argo: &Option<Ident>,
    cls: Vec<(Vec<Pattern>, RawLambda)>,
    args: &[(RawLambda, LetKind)],
    def: DefaultEnv,
    next_raise: &mut i32,
) -> (PmHalfCompiledInfo, Vec<(i32, PmHalfCompiled)>) {
    let cls = simplify_cases(ctx_ref, args, cls);

    do_split_or(argo, Vec::new(), Vec::new(), Vec::new(), &cls, args, &def, next_raise)
}

/// Inner do_split for split_or.
fn do_split_or(
    argo: &Option<Ident>,
    before: Vec<(Vec<Pattern>, RawLambda)>,
    ors: Vec<(Vec<Pattern>, RawLambda)>,
    no: Vec<(Vec<Pattern>, RawLambda)>,
    rest: &[(Vec<Pattern>, RawLambda)],
    args: &[(RawLambda, LetKind)],
    def: &DefaultEnv,
    next_raise: &mut i32,
) -> (PmHalfCompiledInfo, Vec<(i32, PmHalfCompiled)>) {
    match rest.split_first() {
        None => {
            let before = rev_vec(before);
            let ors = rev_vec(ors);
            let no = rev_vec(no);
            cons_next_or(argo, before, ors, &no, args, def, next_raise)
        }
        Some((cl, rem)) => {
            match cl.0.split_first() {
                Some((p, ps)) => {
                    let act = &cl.1;
                    if up_ok(&cl.0, act, &no) {
                        if is_or(p) {
                            let (new_ors, new_no) = insert_or_append(p, ps, act, ors, no);
                            do_split_or(argo, before, new_ors, new_no, rem, args, def, next_raise)
                        } else if up_ok(&cl.0, act, &ors) {
                            let mut new_before = before;
                            new_before.insert(0, cl.clone());
                            do_split_or(argo, new_before, ors, no, rem, args, def, next_raise)
                        } else if or_ok(p, ps, &ors) {
                            let mut new_ors = ors;
                            new_ors.insert(0, cl.clone());
                            do_split_or(argo, before, new_ors, no, rem, args, def, next_raise)
                        } else {
                            let mut new_no = no;
                            new_no.insert(0, cl.clone());
                            do_split_or(argo, before, ors, new_no, rem, args, def, next_raise)
                        }
                    } else {
                        let mut new_no = no;
                        new_no.insert(0, cl.clone());
                        do_split_or(argo, before, ors, new_no, rem, args, def, next_raise)
                    }
                }
                None => panic!("split_or: empty pattern row"),
            }
        }
    }
}

/// cons_next helper for split_or.
fn cons_next_or(
    argo: &Option<Ident>,
    yes: Vec<(Vec<Pattern>, RawLambda)>,
    yesor: Vec<(Vec<Pattern>, RawLambda)>,
    no: &[(Vec<Pattern>, RawLambda)],
    args: &[(RawLambda, LetKind)],
    def: &DefaultEnv,
    next_raise: &mut i32,
) -> (PmHalfCompiledInfo, Vec<(i32, PmHalfCompiled)>) {
    if no.is_empty() {
        precompile_or(argo, yes, yesor, args, def.clone(), Vec::new(), next_raise)
    } else {
        let (info, nexts) = do_split_or(
            argo,
            Vec::new(),
            Vec::new(),
            Vec::new(),
            no,
            args,
            def,
            next_raise,
        );
        let idef = {
            *next_raise += 1;
            *next_raise
        };
        let new_def = cons_default(info.matrix.clone(), idef, def.clone());
        let mut new_nexts = vec![(idef, info.me)];
        new_nexts.extend(nexts);
        precompile_or(argo, yes, yesor, args, new_def, new_nexts, next_raise)
    }
}

/// Ultra-naive splitting, close to semantics, used for extension constructors.
/// Equivalent to OCaml's `split_naive`.
fn split_naive(
    cls: &[(Vec<Pattern>, RawLambda)],
    args: &[(RawLambda, LetKind)],
    def: DefaultEnv,
    k: Vec<(i32, PmHalfCompiled)>,
    next_raise: &mut i32,
) -> (PmHalfCompiledInfo, Vec<(i32, PmHalfCompiled)>) {
    match cls.split_first() {
        None => panic!("split_naive: empty cases"),
        Some((cl, rem)) => {
            match cl.0.first() {
                Some(p) if group_constructor(p) => {
                    split_exc(pat_as_constr(p), vec![cl.clone()], rem, args, def, k, next_raise)
                }
                Some(_) => {
                    split_noexc(vec![cl.clone()], rem, args, def, k, next_raise)
                }
                None => panic!("split_naive: empty pattern row"),
            }
        }
    }
}

/// Split on extension constructors (naive).
fn split_exc(
    cstr0: &crate::types::ConstructorDescription,
    yes: Vec<(Vec<Pattern>, RawLambda)>,
    rest: &[(Vec<Pattern>, RawLambda)],
    args: &[(RawLambda, LetKind)],
    def: DefaultEnv,
    k: Vec<(i32, PmHalfCompiled)>,
    next_raise: &mut i32,
) -> (PmHalfCompiledInfo, Vec<(i32, PmHalfCompiled)>) {
    match rest.split_first() {
        None => {
            let yes = rev_vec(yes);
            (
                PmHalfCompiledInfo {
                    me: PmHalfCompiled::Pm(PatternMatching {
                        cases: yes.clone(),
                        args: args.to_vec(),
                        default: def.clone(),
                    }),
                    matrix: as_matrix(&yes),
                    top_default: def,
                },
                k,
            )
        }
        Some((cl, rem)) => {
            match cl.0.first() {
                Some(p) if group_constructor(p) => {
                    let cstr = pat_as_constr(p);
                    if equal_tag(&cstr.cstr_tag, &cstr0.cstr_tag) {
                        let mut new_yes = yes;
                        new_yes.insert(0, cl.clone());
                        split_exc(cstr0, new_yes, rem, args, def, k, next_raise)
                    } else {
                        let yes = rev_vec(yes);
                        let (info, nexts) = split_exc(cstr, vec![cl.clone()], rem, args, def.clone(), k, next_raise);
                        let idef = {
                            *next_raise += 1;
                            *next_raise
                        };
                        let new_def = cons_default(info.matrix.clone(), idef, def);
                        let mut new_nexts = vec![(idef, info.me)];
                        new_nexts.extend(nexts);
                        (
                            PmHalfCompiledInfo {
                                me: PmHalfCompiled::Pm(PatternMatching {
                                    cases: yes.clone(),
                                    args: args.to_vec(),
                                    default: new_def.clone(),
                                }),
                                matrix: as_matrix(&yes),
                                top_default: new_def,
                            },
                            new_nexts,
                        )
                    }
                }
                Some(_) => {
                    let yes = rev_vec(yes);
                    let (info, nexts) = split_noexc(vec![cl.clone()], rem, args, def.clone(), k, next_raise);
                    let idef = {
                        *next_raise += 1;
                        *next_raise
                    };
                    let new_def = cons_default(info.matrix.clone(), idef, def);
                    let mut new_nexts = vec![(idef, info.me)];
                    new_nexts.extend(nexts);
                    (
                        PmHalfCompiledInfo {
                            me: PmHalfCompiled::Pm(PatternMatching {
                                cases: yes.clone(),
                                args: args.to_vec(),
                                default: new_def.clone(),
                            }),
                            matrix: as_matrix(&yes),
                            top_default: new_def,
                        },
                        new_nexts,
                    )
                }
                None => panic!("split_exc: empty pattern row"),
            }
        }
    }
}

/// Split on non-extension constructors (naive).
fn split_noexc(
    yes: Vec<(Vec<Pattern>, RawLambda)>,
    rest: &[(Vec<Pattern>, RawLambda)],
    args: &[(RawLambda, LetKind)],
    def: DefaultEnv,
    k: Vec<(i32, PmHalfCompiled)>,
    next_raise: &mut i32,
) -> (PmHalfCompiledInfo, Vec<(i32, PmHalfCompiled)>) {
    match rest.split_first() {
        None => {
            let yes = rev_vec(yes);
            precompile_var(args, yes, def, k, next_raise)
        }
        Some((cl, rem)) => {
            match cl.0.first() {
                Some(p) if group_constructor(p) => {
                    let yes = rev_vec(yes);
                    let (info, nexts) = split_exc(
                        pat_as_constr(p),
                        vec![cl.clone()],
                        rem,
                        args,
                        def.clone(),
                        k,
                        next_raise,
                    );
                    let idef = {
                        *next_raise += 1;
                        *next_raise
                    };
                    precompile_var(
                        args,
                        yes,
                        cons_default(info.matrix.clone(), idef, def),
                        {
                            let mut new_nexts = vec![(idef, info.me)];
                            new_nexts.extend(nexts);
                            new_nexts
                        },
                        next_raise,
                    )
                }
                Some(_) => {
                    let mut new_yes = yes;
                    new_yes.insert(0, cl.clone());
                    split_noexc(new_yes, rem, args, def, k, next_raise)
                }
                None => panic!("split_noexc: empty pattern row"),
            }
        }
    }
}

/// Split on constructors using group predicates.
/// Equivalent to OCaml's `split_constr`.
fn split_constr(
    cls: &[(Vec<Pattern>, RawLambda)],
    args: &[(RawLambda, LetKind)],
    def: DefaultEnv,
    k: Vec<(i32, PmHalfCompiled)>,
    next_raise: &mut i32,
) -> (PmHalfCompiledInfo, Vec<(i32, PmHalfCompiled)>) {
    let ex_pat = what_is_cases(cls);
    match &ex_pat.pat_desc {
        PatternDesc::Tpat_any => {
            precompile_var(args, cls.to_vec(), def, k, next_raise)
        }
        PatternDesc::Tpat_construct(_, cstr, _)
            if matches!(&cstr.cstr_tag, ConstructorTag::CstrExtension(_)) =>
        {
            split_naive(cls, args, def, k, next_raise)
        }
        _ => {
            let group = get_group(&ex_pat);
            match cls.split_first() {
                Some((cl, rem)) => {
                    match cl.0.first() {
                        Some(p) if group(p) => {
                            split_ex(group, vec![cl.clone()], Vec::new(), rem, args, def, k, next_raise)
                        }
                        _ => {
                            split_noex(group, vec![cl.clone()], Vec::new(), rem, args, def, k, next_raise)
                        }
                    }
                }
                None => panic!("split_constr: empty cases"),
            }
        }
    }
}

/// split_ex: raise constructor rows up.
fn split_ex(
    group: fn(&Pattern) -> bool,
    yes: Vec<(Vec<Pattern>, RawLambda)>,
    no: Vec<(Vec<Pattern>, RawLambda)>,
    rest: &[(Vec<Pattern>, RawLambda)],
    args: &[(RawLambda, LetKind)],
    def: DefaultEnv,
    k: Vec<(i32, PmHalfCompiled)>,
    next_raise: &mut i32,
) -> (PmHalfCompiledInfo, Vec<(i32, PmHalfCompiled)>) {
    match rest.split_first() {
        None => {
            let yes = rev_vec(yes);
            let no = rev_vec(no);
            match no.split_first() {
                None => {
                    (
                        PmHalfCompiledInfo {
                            me: PmHalfCompiled::Pm(PatternMatching {
                                cases: yes.clone(),
                                args: args.to_vec(),
                                default: def.clone(),
                            }),
                            matrix: as_matrix(&yes),
                            top_default: def,
                        },
                        k,
                    )
                }
                Some((no_cl, no_rem)) => {
                    if yes.is_empty() {
                        // Could not succeed in raising up a constr matching up
                        split_noex(group, vec![no_cl.clone()], Vec::new(), no_rem, args, def, k, next_raise)
                    } else {
                        let (info, nexts) = split_noex(
                            group,
                            vec![no_cl.clone()],
                            Vec::new(),
                            no_rem,
                            args,
                            def.clone(),
                            k,
                            next_raise,
                        );
                        let idef = {
                            *next_raise += 1;
                            *next_raise
                        };
                        let new_def = cons_default(info.matrix.clone(), idef, def);
                        let mut new_nexts = vec![(idef, info.me)];
                        new_nexts.extend(nexts);
                        (
                            PmHalfCompiledInfo {
                                me: PmHalfCompiled::Pm(PatternMatching {
                                    cases: yes.clone(),
                                    args: args.to_vec(),
                                    default: new_def.clone(),
                                }),
                                matrix: as_matrix(&yes),
                                top_default: new_def,
                            },
                            new_nexts,
                        )
                    }
                }
            }
        }
        Some((cl, rem)) => {
            match cl.0.first() {
                Some(p) if group(p) && up_ok(&cl.0, &cl.1, &no) => {
                    let mut new_yes = yes;
                    new_yes.insert(0, cl.clone());
                    split_ex(group, new_yes, no, rem, args, def, k, next_raise)
                }
                _ => {
                    let mut new_no = no;
                    new_no.insert(0, cl.clone());
                    split_ex(group, yes, new_no, rem, args, def, k, next_raise)
                }
            }
        }
    }
}

/// split_noex: raise non-constructor rows up.
fn split_noex(
    group: fn(&Pattern) -> bool,
    yes: Vec<(Vec<Pattern>, RawLambda)>,
    no: Vec<(Vec<Pattern>, RawLambda)>,
    rest: &[(Vec<Pattern>, RawLambda)],
    args: &[(RawLambda, LetKind)],
    def: DefaultEnv,
    k: Vec<(i32, PmHalfCompiled)>,
    next_raise: &mut i32,
) -> (PmHalfCompiledInfo, Vec<(i32, PmHalfCompiled)>) {
    match rest.split_first() {
        None => {
            let yes = rev_vec(yes);
            let no = rev_vec(no);
            match no.split_first() {
                None => {
                    precompile_var(args, yes, def, k, next_raise)
                }
                Some((no_cl, no_rem)) => {
                    let (info, nexts) = split_ex(
                        group,
                        vec![no_cl.clone()],
                        Vec::new(),
                        no_rem,
                        args,
                        def.clone(),
                        k,
                        next_raise,
                    );
                    let idef = {
                        *next_raise += 1;
                        *next_raise
                    };
                    precompile_var(
                        args,
                        yes,
                        cons_default(info.matrix.clone(), idef, def),
                        {
                            let mut new_nexts = vec![(idef, info.me)];
                            new_nexts.extend(nexts);
                            new_nexts
                        },
                        next_raise,
                    )
                }
            }
        }
        Some((_cl, _rem)) if rest.len() == 1 => {
            // Check for the special case: last row is all variables and yes is non-empty
            let cl = &rest[0];
            if cl.0.iter().all(|p| group_var(p)) && !yes.is_empty() {
                // This enables an extra division in some frequent cases:
                // last row is made of variables only
                let mut new_no = no;
                new_no.insert(0, cl.clone());
                split_noex(group, yes, new_no, &[], args, def, k, next_raise)
            } else {
                // Fall through to normal case
                let cl = &rest[0];
                match cl.0.first() {
                    Some(p) if !group(p) && up_ok(&cl.0, &cl.1, &no) => {
                        let mut new_yes = yes;
                        new_yes.insert(0, cl.clone());
                        split_noex(group, new_yes, no, &[], args, def, k, next_raise)
                    }
                    _ => {
                        let mut new_no = no;
                        new_no.insert(0, cl.clone());
                        split_noex(group, yes, new_no, &[], args, def, k, next_raise)
                    }
                }
            }
        }
        Some((cl, rem)) => {
            match cl.0.first() {
                Some(p) if !group(p) && up_ok(&cl.0, &cl.1, &no) => {
                    let mut new_yes = yes;
                    new_yes.insert(0, cl.clone());
                    split_noex(group, new_yes, no, rem, args, def, k, next_raise)
                }
                _ => {
                    let mut new_no = no;
                    new_no.insert(0, cl.clone());
                    split_noex(group, yes, new_no, rem, args, def, k, next_raise)
                }
            }
        }
    }
}

/// Precompile variable patterns: if the match argument is a variable,
/// split further on the second column.
/// Equivalent to OCaml's `precompile_var`.
fn precompile_var(
    args: &[(RawLambda, LetKind)],
    cls: Vec<(Vec<Pattern>, RawLambda)>,
    def: DefaultEnv,
    k: Vec<(i32, PmHalfCompiled)>,
    next_raise: &mut i32,
) -> (PmHalfCompiledInfo, Vec<(i32, PmHalfCompiled)>) {
    match args {
        [] => panic!("precompile_var: empty args"),
        [_, arg_rest @ ..] if !arg_rest.is_empty() => {
            // Check if second arg is Lvar
            match &arg_rest[0].0 {
                RawLambda::Lvar(v) => {
                    if cls.len() == 1 {
                        // as split as it can
                        dont_precompile_var(args, cls, def, k)
                    } else {
                        // Precompile: strip first pattern from each case
                        let var_cls: Vec<(Vec<Pattern>, RawLambda)> = cls
                            .iter()
                            .map(|(ps, act)| {
                                match ps.split_first() {
                                    Some((_, rest)) => (rest.to_vec(), act.clone()),
                                    None => panic!("precompile_var: empty pattern row"),
                                }
                            })
                            .collect();
                        let var_def = make_default(
                            &|_p: &Pattern, rem: &[Pattern]| Ok(rem.to_vec()),
                            &def,
                        );
                        let av = arg_rest[0].0.clone();
                        let (first_info, nexts) = split_or(
                            None, // TypeContext not available in do_split_or
                            &Some(v.clone()),
                            var_cls,
                            arg_rest,
                            var_def,
                            next_raise,
                        );

                        // Compute top information
                        if nexts.is_empty() {
                            // If you need
                            dont_precompile_var(args, cls, def, k)
                        } else {
                            let rfirst = PmHalfCompiledInfo {
                                me: PmHalfCompiled::PmVar(PmVarCompiled {
                                    inside: Box::new(first_info.me),
                                    var_arg: av.clone(),
                                }),
                                matrix: add_omega_column(&first_info.matrix),
                                top_default: rebuild_default(&nexts, def),
                            };
                            let rnexts = rebuild_nexts(&av, nexts, k);
                            (rfirst, rnexts)
                        }
                    }
                }
                _ => dont_precompile_var(args, cls, def, k),
            }
        }
        _ => dont_precompile_var(args, cls, def, k),
    }
}

/// Don't precompile: just wrap the cases in a PatternMatching.
/// Equivalent to OCaml's `dont_precompile_var`.
fn dont_precompile_var(
    args: &[(RawLambda, LetKind)],
    cls: Vec<(Vec<Pattern>, RawLambda)>,
    def: DefaultEnv,
    k: Vec<(i32, PmHalfCompiled)>,
) -> (PmHalfCompiledInfo, Vec<(i32, PmHalfCompiled)>) {
    (
        PmHalfCompiledInfo {
            me: PmHalfCompiled::Pm(PatternMatching {
                cases: cls.clone(),
                args: args.to_vec(),
                default: def.clone(),
            }),
            matrix: as_matrix(&cls),
            top_default: def,
        },
        k,
    )
}

/// Precompile or-patterns.
/// Equivalent to OCaml's `precompile_or`.
fn precompile_or(
    argo: &Option<Ident>,
    cls: Vec<(Vec<Pattern>, RawLambda)>,
    ors: Vec<(Vec<Pattern>, RawLambda)>,
    args: &[(RawLambda, LetKind)],
    def: DefaultEnv,
    k: Vec<(i32, PmHalfCompiled)>,
    next_raise: &mut i32,
) -> (PmHalfCompiledInfo, Vec<(i32, PmHalfCompiled)>) {
    if ors.is_empty() {
        return split_constr(&cls, args, def, k, next_raise);
    }

    // do_cases processes the or-pattern list
    let (end_body, handlers) = do_cases_or(argo, &ors, args, &def, next_raise);

    let matrix = as_matrix(&[cls.as_slice(), ors.as_slice()].concat());
    let body = PatternMatching {
        cases: [cls, end_body].concat(),
        args: args.to_vec(),
        default: def.clone(),
    };
    (
        PmHalfCompiledInfo {
            me: PmHalfCompiled::PmOr(PmOrCompiled {
                body,
                handlers,
                or_matrix: matrix.clone(),
            }),
            matrix,
            top_default: def,
        },
        k,
    )
}

/// Process or-pattern cases for precompile_or.
/// Equivalent to the inner `do_cases` in OCaml's `precompile_or`.
fn do_cases_or(
    argo: &Option<Ident>,
    ors: &[(Vec<Pattern>, RawLambda)],
    args: &[(RawLambda, LetKind)],
    def: &DefaultEnv,
    next_raise: &mut i32,
) -> (Vec<(Vec<Pattern>, RawLambda)>, Vec<(Matrix, i32, Vec<Ident>, PatternMatching)>) {
    match ors.split_first() {
        None => (Vec::new(), Vec::new()),
        Some((cl, rem)) => {
            match cl.0.first() {
                Some(orp) if is_or(orp) => {
                    let patl = &cl.0[1..];
                    let action = &cl.1;

                    let (others, rem) = get_equiv(orp, rem);

                    let orpm_cases = {
                        let mut cases = vec![(patl.to_vec(), action.clone())];
                        cases.extend(others.iter().map(|(ps, act)| {
                            match ps.split_first() {
                                Some((_, rest)) => (rest.to_vec(), act.clone()),
                                None => panic!("do_cases_or: empty pattern row"),
                            }
                        }));
                        cases
                    };
                    let orpm_args = match args.split_first() {
                        Some((_, r)) => r.to_vec(),
                        None => panic!("do_cases_or: empty args"),
                    };
                    let orpm = PatternMatching {
                        cases: orpm_cases,
                        args: orpm_args,
                        default: default_compat(orp, def),
                    };

                    let vars: Vec<Ident> = {
                        let orp_vars = extract_vars(BTreeSet::new(), orp);
                        let pm_fv = pm_free_variables(&orpm);
                        orp_vars.intersection(&pm_fv).cloned().collect()
                    };

                    let or_num = {
                        *next_raise += 1;
                        *next_raise
                    };
                    let new_patl = omega_list(patl);

                    let mk_new_action = |vs: &[Ident]| -> RawLambda {
                        RawLambda::LstaticRaise(
                            or_num,
                            vs.iter().map(|v| RawLambda::Lvar(v.clone())).collect(),
                        )
                    };

                    let (body, handlers) = do_cases_or(argo, &rem, args, def, next_raise);

                    let exploded = explode_or_pat(
                        argo,
                        &new_patl,
                        &mk_new_action,
                        body,
                        &vars.iter().cloned().collect(),
                        &[],
                        orp,
                    );

                    let new_body = match exploded {
                        Ok(b) => b,
                        Err(_) => panic!("do_cases_or: Cannot_flatten"),
                    };

                    let mat = vec![vec![orp.clone()]];
                    let mut new_handlers = vec![(mat, or_num, vars, orpm)];
                    new_handlers.extend(handlers);
                    (new_body, new_handlers)
                }
                _ => {
                    // Not an or-pattern head
                    let (mut new_ord, new_to_catch) = do_cases_or(argo, rem, args, def, next_raise);
                    new_ord.insert(0, cl.clone());
                    (new_ord, new_to_catch)
                }
            }
        }
    }
}

/// Top-level split_precompile.
/// Equivalent to OCaml's `split_precompile`.
pub fn split_precompile(
    ctx_ref: Option<&TypeContext<'_>>,
    argo: &Option<Ident>,
    pm: &PatternMatching,
    next_raise: &mut i32,
) -> (PmHalfCompiled, Vec<(i32, PmHalfCompiled)>) {
    let (info, nexts) = split_or(ctx_ref, argo, pm.cases.clone(), &pm.args, pm.default.clone(), next_raise);
    (info.me, nexts)
}

/// Reverse a vector — equivalent to OCaml's `List.rev`.
///
/// Items in `do_split_or` and `insert_or_append` are prepended (via `insert(0,...)`
/// or by building new vectors with the new item first), matching OCaml's `::` prepend
/// semantics. The final `List.rev` call restores the original order.
fn rev_vec<T>(mut v: Vec<T>) -> Vec<T> {
    v.reverse();
    v
}

// ============================================================================
// Layer 5: General divide functions (lines 1094-1131)
// ============================================================================

/// Add a case to a pattern matching.
/// Equivalent to OCaml's `add_line`.
fn add_line(
    patl_action: (Vec<Pattern>, RawLambda),
    mut pm: PatternMatching,
) -> PatternMatching {
    pm.cases.insert(0, patl_action);
    pm
}

/// A cell: a pattern matching with its context list and pattern.
/// Equivalent to OCaml's `cell`.
struct MatchCell {
    pm: PatternMatching,
    ctx: Vec<Ctx>,
    pat: Pattern,
}

/// Add a case to the appropriate cell in a division, creating a new cell if needed.
/// Equivalent to OCaml's `add`.
fn add<K>(
    make_matching_fun: impl FnOnce(&[(RawLambda, LetKind)]) -> MatchCell,
    mut division: Vec<(K, MatchCell)>,
    eq_key: impl Fn(&K, &K) -> bool,
    key: K,
    patl_action: (Vec<Pattern>, RawLambda),
    args: &[(RawLambda, LetKind)],
) -> Vec<(K, MatchCell)> {
    // Try to find existing entry with matching key
    if let Some(pos) = division.iter().position(|(k, _)| eq_key(&key, k)) {
        division[pos].1.pm.cases.insert(0, patl_action);
        division
    } else {
        let mut cell = make_matching_fun(args);
        cell.pm.cases = vec![patl_action];
        division.insert(0, (key, cell));
        division
    }
}

/// Divide a pattern matching by the first pattern column, grouping by key.
/// Equivalent to OCaml's `divide`.
fn divide<K>(
    make: impl Fn(&Pattern, &DefaultEnv, &[Ctx], &[(RawLambda, LetKind)]) -> MatchCell + Clone,
    eq_key: impl Fn(&K, &K) -> bool + Clone,
    get_key: impl Fn(&Pattern) -> K + Clone,
    get_args: impl Fn(&Pattern, &[Pattern]) -> Vec<Pattern> + Clone,
    ctx: &[Ctx],
    pm: &PatternMatching,
) -> Vec<(K, MatchCell)> {
    fn divide_rec<K>(
        cases: &[(Vec<Pattern>, RawLambda)],
        make: &dyn Fn(&Pattern, &DefaultEnv, &[Ctx], &[(RawLambda, LetKind)]) -> MatchCell,
        eq_key: &dyn Fn(&K, &K) -> bool,
        get_key: &dyn Fn(&Pattern) -> K,
        get_args: &dyn Fn(&Pattern, &[Pattern]) -> Vec<Pattern>,
        default: &DefaultEnv,
        ctx: &[Ctx],
        args: &[(RawLambda, LetKind)],
    ) -> Vec<(K, MatchCell)> {
        match cases.split_first() {
            Some(((patl, action), rem)) => {
                match patl.split_first() {
                    Some((p, rest_patl)) => {
                        let this_match = divide_rec(rem, make, eq_key, get_key, get_args, default, ctx, args);
                        let key = get_key(p);
                        let mut new_patl = get_args(p, rest_patl);
                        // get_args returns args @ rest_patl, which is the new pattern list
                        add(
                            |a| make(p, default, ctx, a),
                            this_match,
                            |a, b| eq_key(a, b),
                            key,
                            (new_patl, action.clone()),
                            args,
                        )
                    }
                    None => Vec::new(),
                }
            }
            None => Vec::new(),
        }
    }

    divide_rec(
        &pm.cases,
        &|p, def, ctx, args| make.clone()(p, def, ctx, args),
        &|a, b| eq_key.clone()(a, b),
        &|p| get_key.clone()(p),
        &|p, rest| get_args.clone()(p, rest),
        &pm.default,
        ctx,
        &pm.args,
    )
}

/// Divide a pattern matching into a single cell (no grouping by key).
/// Equivalent to OCaml's `divide_line`.
fn divide_line(
    make_ctx: impl Fn(&[Ctx]) -> Vec<Ctx>,
    make: impl Fn(&DefaultEnv, &[(RawLambda, LetKind)]) -> PatternMatching,
    get_args: impl Fn(&Pattern, &[Pattern]) -> Vec<Pattern>,
    pat: Pattern,
    ctx: &[Ctx],
    pm: &PatternMatching,
) -> MatchCell {
    fn divide_rec(
        cases: &[(Vec<Pattern>, RawLambda)],
        get_args: &dyn Fn(&Pattern, &[Pattern]) -> Vec<Pattern>,
        make: &dyn Fn(&DefaultEnv, &[(RawLambda, LetKind)]) -> PatternMatching,
        default: &DefaultEnv,
        args: &[(RawLambda, LetKind)],
    ) -> PatternMatching {
        match cases.split_first() {
            Some(((patl, action), rem)) => {
                match patl.split_first() {
                    Some((p, rest_patl)) => {
                        let this_match = divide_rec(rem, get_args, make, default, args);
                        let new_patl = get_args(p, rest_patl);
                        add_line((new_patl, action.clone()), this_match)
                    }
                    None => make(default, args),
                }
            }
            None => make(default, args),
        }
    }

    MatchCell {
        pm: divide_rec(&pm.cases, &get_args, &make, &pm.default, &pm.args),
        ctx: make_ctx(ctx),
        pat,
    }
}

// ============================================================================
// Layer 6: Per-type pattern matchers (lines 1148-1516)
// ============================================================================

// --- Constants (lines 1148-1177) ---

/// Matcher for constant patterns.
/// Equivalent to OCaml's `matcher_const`.
fn matcher_const(
    cst: &Constant,
    p: &Pattern,
    rem: &[Pattern],
) -> Result<Vec<Pattern>, MatchError> {
    match &p.pat_desc {
        PatternDesc::Tpat_or(p1, p2, _) => {
            match matcher_const(cst, p1, rem) {
                Ok(r) => Ok(r),
                Err(MatchError::NoMatch) => matcher_const(cst, p2, rem),
                Err(e) => Err(e),
            }
        }
        PatternDesc::Tpat_constant(c1)
            if const_compare(c1, cst) == std::cmp::Ordering::Equal =>
        {
            Ok(rem.to_vec())
        }
        PatternDesc::Tpat_any => Ok(rem.to_vec()),
        _ => Err(MatchError::NoMatch),
    }
}

/// Get the key (constant) from a constant pattern.
/// Equivalent to OCaml's `get_key_constant`.
fn get_key_constant(caller: &str, p: &Pattern) -> Constant {
    match &p.pat_desc {
        PatternDesc::Tpat_constant(cst) => cst.clone(),
        _ => {
            eprintln!("BAD: {}", caller);
            // pretty_pat p; -- omitted
            panic!("get_key_constant: not a constant pattern");
        }
    }
}

/// Get the arguments from a constant pattern (none — just the remainder).
/// Equivalent to OCaml's `get_args_constant`.
fn get_args_constant(_p: &Pattern, rem: &[Pattern]) -> Vec<Pattern> {
    rem.to_vec()
}

/// Make a constant matching cell.
/// Equivalent to OCaml's `make_constant_matching`.
fn make_constant_matching(
    p: &Pattern,
    def: &DefaultEnv,
    ctx: &[Ctx],
    args: &[(RawLambda, LetKind)],
) -> MatchCell {
    match args.split_first() {
        None => panic!("Matching.make_constant_matching"),
        Some((_, argl)) => {
            let key = get_key_constant("make", p);
            let def = make_default(
                &|p2, rem| matcher_const(&key, p2, rem),
                def,
            );
            let ctx = filter_ctx(p, ctx);
            MatchCell {
                pm: PatternMatching {
                    cases: Vec::new(),
                    args: argl.to_vec(),
                    default: def,
                },
                ctx,
                pat: normalize_pat(p),
            }
        }
    }
}

/// Divide a pattern matching by constant values.
/// Equivalent to OCaml's `divide_constant`.
fn divide_constant(ctx: &[Ctx], m: &PatternMatching) -> Vec<(Constant, MatchCell)> {
    divide(
        make_constant_matching,
        |c, d| const_compare(c, d) == std::cmp::Ordering::Equal,
        |p| get_key_constant("divide", p),
        get_args_constant,
        ctx,
        m,
    )
}

// --- Constructors (lines 1180-1289) ---

/// Make field access arguments for a constructor.
/// Equivalent to OCaml's `make_field_args`.
fn make_field_args(
    fld_info: FieldDbgInfo,
    loc: Location,
    binding_kind: LetKind,
    arg: &RawLambda,
    first_pos: i32,
    last_pos: i32,
    argl: &[(RawLambda, LetKind)],
) -> Vec<(RawLambda, LetKind)> {
    let mut result = Vec::new();
    for pos in first_pos..=last_pos {
        result.push((
            RawLambda::Lprim(RawPrimInfo {
                primitive: Primitive::Pfield(pos, fld_info.clone()),
                args: vec![arg.clone()],
                loc: loc.clone(),
            }),
            binding_kind,
        ));
    }
    result.extend(argl.iter().cloned());
    result
}

/// Get the key (tag) from a constructor pattern.
/// Equivalent to OCaml's `get_key_constr`.
fn get_key_constr(p: &Pattern) -> ConstructorTag {
    match &p.pat_desc {
        PatternDesc::Tpat_construct(_, cstr, _) => cstr.cstr_tag.clone(),
        _ => panic!("get_key_constr: not a construct pattern"),
    }
}

/// Get the arguments from a constructor pattern.
/// Equivalent to OCaml's `get_args_constr`.
fn get_args_constr(p: &Pattern, rem: &[Pattern]) -> Vec<Pattern> {
    match &p.pat_desc {
        PatternDesc::Tpat_construct(_, _, args) => {
            let mut result = args.clone();
            result.extend(rem.iter().cloned());
            result
        }
        _ => panic!("get_args_constr: not a construct pattern"),
    }
}

/// Matcher for constructor patterns.
/// Equivalent to OCaml's `matcher_constr`.
///
/// NB: matcher_constr applies to default matrices.
/// In that context, matching by constructors of extensible
/// types degrades to arity checking, due to potential rebinding.
/// This comparison is performed by Types.may_equal_constr.
fn matcher_constr(
    cstr: &ConstructorDescription,
    p: &Pattern,
    rem: &[Pattern],
) -> Result<Vec<Pattern>, MatchError> {
    match cstr.cstr_arity {
        0 => matcher_constr_arity0(cstr, p, rem),
        1 => matcher_constr_arity1(cstr, p, rem),
        _ => matcher_constr_arityN(cstr, p, rem),
    }
}

/// Matcher for 0-arity constructor.
fn matcher_constr_arity0(
    cstr: &ConstructorDescription,
    q: &Pattern,
    rem: &[Pattern],
) -> Result<Vec<Pattern>, MatchError> {
    match &q.pat_desc {
        PatternDesc::Tpat_or(p1, p2, _) => {
            match matcher_constr_arity0(cstr, p1, rem) {
                Ok(r) => Ok(r),
                Err(MatchError::NoMatch) => matcher_constr_arity0(cstr, p2, rem),
                Err(e) => Err(e),
            }
        }
        PatternDesc::Tpat_construct(_, cstr2, args)
            if args.is_empty() && may_equal_constr(cstr, cstr2) =>
        {
            Ok(rem.to_vec())
        }
        PatternDesc::Tpat_any => Ok(rem.to_vec()),
        _ => Err(MatchError::NoMatch),
    }
}

/// Matcher for 1-arity constructor.
fn matcher_constr_arity1(
    cstr: &ConstructorDescription,
    q: &Pattern,
    rem: &[Pattern],
) -> Result<Vec<Pattern>, MatchError> {
    match &q.pat_desc {
        PatternDesc::Tpat_or(p1, p2, _) => {
            let r1 = matcher_constr_arity1(cstr, p1, rem).ok();
            let r2 = matcher_constr_arity1(cstr, p2, rem).ok();
            match (r1, r2) {
                (None, None) => Err(MatchError::NoMatch),
                (Some(r1), None) => Ok(r1),
                (None, Some(r2)) => Ok(r2),
                (Some(r1), Some(r2)) => {
                    match (r1.first(), r2.first()) {
                        (Some(a1), Some(a2)) => {
                            let or_pat = Pattern {
                                pat_desc: PatternDesc::Tpat_or(
                                    Box::new(a1.clone()),
                                    Box::new(a2.clone()),
                                    None,
                                ),
                                pat_loc: LocIdx::none(),
                                pat_extra: Vec::new(),
                                pat_type: a1.pat_type,
                                pat_env: a1.pat_env,
                                pat_attributes: Attributes::new(),
                            };
                            let mut result = vec![or_pat];
                            result.extend(rem.iter().cloned());
                            Ok(result)
                        }
                        _ => panic!("matcher_constr_arity1: unexpected empty result"),
                    }
                }
            }
        }
        PatternDesc::Tpat_construct(_, cstr2, args)
            if args.len() == 1 && may_equal_constr(cstr, cstr2) =>
        {
            let mut result = vec![args[0].clone()];
            result.extend(rem.iter().cloned());
            Ok(result)
        }
        PatternDesc::Tpat_any => {
            let mut result = vec![omega()];
            result.extend(rem.iter().cloned());
            Ok(result)
        }
        _ => Err(MatchError::NoMatch),
    }
}

/// Matcher for N-arity constructor (N >= 2).
fn matcher_constr_arityN(
    cstr: &ConstructorDescription,
    q: &Pattern,
    rem: &[Pattern],
) -> Result<Vec<Pattern>, MatchError> {
    match &q.pat_desc {
        PatternDesc::Tpat_or(_, _, _) => Err(MatchError::OrPat),
        PatternDesc::Tpat_construct(_, cstr2, args)
            if may_equal_constr(cstr, cstr2) =>
        {
            let mut result = args.clone();
            result.extend(rem.iter().cloned());
            Ok(result)
        }
        PatternDesc::Tpat_any => {
            let mut result = omegas(cstr.cstr_arity as usize);
            result.extend(rem.iter().cloned());
            Ok(result)
        }
        _ => Err(MatchError::NoMatch),
    }
}

/// Helper: get runtime name from label attributes (OCaml's Lambda.find_name).
fn label_runtime_name_matching(lbl: &LabelDescription) -> String {
    for attr in &lbl.lbl_attributes {
        if attr.attr_name.txt == "as" {
            if let crate::types::decl::AttributePayload::Str(name) = &attr.attr_payload {
                return name.clone();
            }
        }
    }
    lbl.lbl_name.clone()
}

/// Create field debug info for a record label (equivalent to OCaml's Lambda.fld_record).
fn fld_record(lbl: &LabelDescription) -> FieldDbgInfo {
    FieldDbgInfo::Record {
        name: label_runtime_name_matching(lbl),
        mutable_flag: match lbl.lbl_mut {
            MutableFlag::Mutable => crate::parser::ast::MutableFlag::Mutable,
            MutableFlag::Immutable => crate::parser::ast::MutableFlag::Immutable,
        },
    }
}

/// Create field debug info for an inlined record label (equivalent to OCaml's Lambda.fld_record_inline).
fn fld_record_inline(lbl: &LabelDescription) -> FieldDbgInfo {
    FieldDbgInfo::RecordInline {
        name: label_runtime_name_matching(lbl),
    }
}

/// Create field debug info for a record extension label (equivalent to OCaml's Lambda.fld_record_extension).
fn fld_record_extension(lbl: &LabelDescription) -> FieldDbgInfo {
    FieldDbgInfo::RecordExtension {
        name: label_runtime_name_matching(lbl),
    }
}

/// Make a constructor matching cell.
/// Equivalent to OCaml's `make_constr_matching`.
fn make_constr_matching(
    ctx_ref: &TypeContext<'_>,
    p: &Pattern,
    def: &DefaultEnv,
    ctx: &[Ctx],
    args: &[(RawLambda, LetKind)],
) -> MatchCell {
    match args.split_first() {
        None => panic!("Matching.make_constr_matching"),
        Some(((arg, _mut), argl)) => {
            let cstr = pat_as_constr(p);
            let untagged = has_untagged(&cstr.cstr_attributes);
            let newargs = if cstr.cstr_inlined.is_some()
                || (untagged && !cstr.cstr_args.is_empty())
            {
                let mut result = vec![(arg.clone(), LetKind::Alias)];
                result.extend(argl.iter().cloned());
                result
            } else {
                match &cstr.cstr_tag {
                    ConstructorTag::CstrBlock(_)
                        if constructor_has_optional_shape(cstr)
                            || (cstr.cstr_name == "Some" && cstr.cstr_consts == 1 && cstr.cstr_nonconsts == 1 && cstr.cstr_arity == 1) =>
                    {
                        let from_option = match &p.pat_desc {
                            PatternDesc::Tpat_construct(_, _, args_inner)
                                if args_inner.len() == 1 =>
                            {
                                let pat = &args_inner[0];
                                let env_opt =
                                    ctx_ref.get_typed_env(pat.pat_env);
                                let can_skip = env_opt
                                    .map(|env| {
                                        type_cannot_contain_undefined(
                                            ctx_ref,
                                            env.as_ref(),
                                            pat.pat_type,
                                        )
                                    })
                                    .unwrap_or(false);
                                if can_skip {
                                    Primitive::PvalFromOptionNotNest
                                } else {
                                    Primitive::PvalFromOption
                                }
                            }
                            _ => Primitive::PvalFromOption,
                        };
                        let mut result = vec![(
                            RawLambda::Lprim(RawPrimInfo {
                                primitive: from_option,
                                args: vec![arg.clone()],
                                loc: Location::none(),
                            }),
                            LetKind::Alias,
                        )];
                        result.extend(argl.iter().cloned());
                        result
                    }
                    ConstructorTag::CstrConstant(_) | ConstructorTag::CstrBlock(_) => {
                        let fld_info = if cstr.cstr_name == "::" {
                            FieldDbgInfo::Cons
                        } else {
                            FieldDbgInfo::Variant
                        };
                        make_field_args(
                            fld_info,
                            Location::none(),
                            LetKind::Alias,
                            arg,
                            0,
                            cstr.cstr_arity - 1,
                            argl,
                        )
                    }
                    ConstructorTag::CstrUnboxed => {
                        let mut result = vec![(arg.clone(), LetKind::Alias)];
                        result.extend(argl.iter().cloned());
                        result
                    }
                    ConstructorTag::CstrExtension(_) => {
                        make_field_args(
                            FieldDbgInfo::Extension,
                            Location::none(),
                            LetKind::Alias,
                            arg,
                            1,
                            cstr.cstr_arity,
                            argl,
                        )
                    }
                }
            };
            let cstr_clone = cstr.clone();
            MatchCell {
                pm: PatternMatching {
                    cases: Vec::new(),
                    args: newargs,
                    default: make_default(
                        &|p2, rem| matcher_constr(&cstr_clone, p2, rem),
                        def,
                    ),
                },
                ctx: filter_ctx(p, ctx),
                pat: normalize_pat(p),
            }
        }
    }
}

/// Divide a pattern matching by constructor.
/// Equivalent to OCaml's `divide_constructor`.
fn divide_constructor(
    ctx_ref: &TypeContext<'_>,
    ctx: &[Ctx],
    pm: &PatternMatching,
) -> Vec<(ConstructorTag, MatchCell)> {
    divide(
        |p, def, ctx_inner, args| make_constr_matching(ctx_ref, p, def, ctx_inner, args),
        |a, b| equal_tag(a, b),
        get_key_constr,
        get_args_constr,
        ctx,
        pm,
    )
}

// --- Variants (lines 1293-1362) ---

/// Matcher for constant variant patterns.
/// Equivalent to OCaml's `matcher_variant_const`.
fn matcher_variant_const(
    lab: &str,
    p: &Pattern,
    rem: &[Pattern],
) -> Result<Vec<Pattern>, MatchError> {
    match &p.pat_desc {
        PatternDesc::Tpat_or(p1, p2, _) => {
            match matcher_variant_const(lab, p1, rem) {
                Ok(r) => Ok(r),
                Err(MatchError::NoMatch) => matcher_variant_const(lab, p2, rem),
                Err(e) => Err(e),
            }
        }
        PatternDesc::Tpat_variant(lab1, _, _) if lab1 == lab => Ok(rem.to_vec()),
        PatternDesc::Tpat_any => Ok(rem.to_vec()),
        _ => Err(MatchError::NoMatch),
    }
}

/// Make a variant matching cell for constant variants.
/// Equivalent to OCaml's `make_variant_matching_constant`.
fn make_variant_matching_constant(
    p: &Pattern,
    lab: &str,
    def: &DefaultEnv,
    ctx: &[Ctx],
    args: &[(RawLambda, LetKind)],
) -> MatchCell {
    match args.split_first() {
        None => panic!("Matching.make_variant_matching_constant"),
        Some((_, argl)) => {
            let lab_owned = lab.to_string();
            let def = make_default(
                &|p2, rem| matcher_variant_const(&lab_owned, p2, rem),
                def,
            );
            let ctx = filter_ctx(p, ctx);
            MatchCell {
                pm: PatternMatching {
                    cases: Vec::new(),
                    args: argl.to_vec(),
                    default: def,
                },
                ctx,
                pat: normalize_pat(p),
            }
        }
    }
}

/// Matcher for non-constant variant patterns.
/// Equivalent to OCaml's `matcher_variant_nonconst`.
fn matcher_variant_nonconst(
    lab: &str,
    p: &Pattern,
    rem: &[Pattern],
) -> Result<Vec<Pattern>, MatchError> {
    match &p.pat_desc {
        PatternDesc::Tpat_or(_, _, _) => Err(MatchError::OrPat),
        PatternDesc::Tpat_variant(lab1, Some(arg), _) if lab1 == lab => {
            let mut result = vec![(**arg).clone()];
            result.extend(rem.iter().cloned());
            Ok(result)
        }
        PatternDesc::Tpat_any => {
            let mut result = vec![omega()];
            result.extend(rem.iter().cloned());
            Ok(result)
        }
        _ => Err(MatchError::NoMatch),
    }
}

/// Make a variant matching cell for non-constant variants.
/// Equivalent to OCaml's `make_variant_matching_nonconst`.
fn make_variant_matching_nonconst(
    p: &Pattern,
    lab: &str,
    def: &DefaultEnv,
    ctx: &[Ctx],
    args: &[(RawLambda, LetKind)],
) -> MatchCell {
    match args.split_first() {
        None => panic!("Matching.make_variant_matching_nonconst"),
        Some(((arg, _mut), argl)) => {
            let lab_owned = lab.to_string();
            let def = make_default(
                &|p2, rem| matcher_variant_nonconst(&lab_owned, p2, rem),
                def,
            );
            let ctx = filter_ctx(p, ctx);
            let mut new_args = vec![(
                RawLambda::Lprim(RawPrimInfo {
                    primitive: Primitive::Pfield(1, FieldDbgInfo::PolyVarContent),
                    args: vec![arg.clone()],
                    loc: Location::none(),
                }),
                LetKind::Alias,
            )];
            new_args.extend(argl.iter().cloned());
            MatchCell {
                pm: PatternMatching {
                    cases: Vec::new(),
                    args: new_args,
                    default: def,
                },
                ctx,
                pat: normalize_pat(p),
            }
        }
    }
}

/// Divide a pattern matching by variant tag.
/// Equivalent to OCaml's `divide_variant`.
fn divide_variant(
    ctx_ref: &TypeContext<'_>,
    row: &RowDesc,
    ctx: &[Ctx],
    pm: &PatternMatching,
) -> Vec<((String, ConstructorTag), MatchCell)> {
    let row = btype::row_repr(ctx_ref, row);

    fn divide_rec(
        ctx_ref: &TypeContext<'_>,
        row: &RowDesc,
        cases: &[(Vec<Pattern>, RawLambda)],
        def: &DefaultEnv,
        ctx: &[Ctx],
        al: &[(RawLambda, LetKind)],
    ) -> Vec<((String, ConstructorTag), MatchCell)> {
        match cases.split_first() {
            Some(((patl, action), rem)) => {
                match patl.split_first() {
                    Some((p, rest_patl)) => {
                        match &p.pat_desc {
                            PatternDesc::Tpat_variant(lab, pato, _) => {
                                let variants = divide_rec(ctx_ref, row, rem, def, ctx, al);

                                // Check if this label is absent in the row
                                let is_absent = match row.row_fields.iter().find(|(l, _)| l == lab)
                                {
                                    Some((_, field)) => {
                                        matches!(
                                            btype::row_field_repr(ctx_ref, field),
                                            RowField::Rabsent
                                        )
                                    }
                                    None => true,
                                };

                                if is_absent {
                                    return variants;
                                }

                                let tag = btype::hash_variant(lab);
                                let eq_key = |a: &(String, ConstructorTag),
                                              b: &(String, ConstructorTag)|
                                 -> bool {
                                    a.0 == b.0 && equal_tag(&a.1, &b.1)
                                };

                                match pato {
                                    None => {
                                        let key =
                                            (lab.clone(), ConstructorTag::CstrConstant(tag));
                                        add(
                                            |a| {
                                                make_variant_matching_constant(
                                                    p, lab, def, ctx, a,
                                                )
                                            },
                                            variants,
                                            eq_key,
                                            key,
                                            (rest_patl.to_vec(), action.clone()),
                                            al,
                                        )
                                    }
                                    Some(pat_inner) => {
                                        let key =
                                            (lab.clone(), ConstructorTag::CstrBlock(tag));
                                        let mut new_patl =
                                            vec![(**pat_inner).clone()];
                                        new_patl.extend(rest_patl.iter().cloned());
                                        add(
                                            |a| {
                                                make_variant_matching_nonconst(
                                                    p, lab, def, ctx, a,
                                                )
                                            },
                                            variants,
                                            eq_key,
                                            key,
                                            (new_patl, action.clone()),
                                            al,
                                        )
                                    }
                                }
                            }
                            _ => Vec::new(),
                        }
                    }
                    None => Vec::new(),
                }
            }
            None => Vec::new(),
        }
    }

    divide_rec(ctx_ref, &row, &pm.cases, &pm.default, ctx, &pm.args)
}

// --- Variables (lines 1370-1378) ---

/// Get the arguments from a variable pattern (none — just the remainder).
/// Equivalent to OCaml's `get_args_var`.
fn get_args_var(_p: &Pattern, rem: &[Pattern]) -> Vec<Pattern> {
    rem.to_vec()
}

/// Matcher version of get_args_var for make_default.
fn matcher_get_args_var(
    _p: &Pattern,
    rem: &[Pattern],
) -> Result<Vec<Pattern>, MatchError> {
    Ok(rem.to_vec())
}

/// Make a variable matching.
/// Equivalent to OCaml's `make_var_matching`.
fn make_var_matching(def: &DefaultEnv, args: &[(RawLambda, LetKind)]) -> PatternMatching {
    match args.split_first() {
        None => panic!("Matching.make_var_matching"),
        Some((_, argl)) => PatternMatching {
            cases: Vec::new(),
            args: argl.to_vec(),
            default: make_default(&matcher_get_args_var, def),
        },
    }
}

/// Divide a pattern matching by variable.
/// Equivalent to OCaml's `divide_var`.
fn divide_var(ctx: &[Ctx], pm: &PatternMatching) -> MatchCell {
    divide_line(ctx_lshift, make_var_matching, get_args_var, omega(), ctx, pm)
}

// --- Tuples (lines 1382-1413) ---

/// Get the arguments from a tuple pattern.
/// Equivalent to OCaml's `get_args_tuple`.
fn get_args_tuple(arity: usize, p: &Pattern, rem: &[Pattern]) -> Vec<Pattern> {
    match &p.pat_desc {
        PatternDesc::Tpat_any => {
            let mut result = omegas(arity);
            result.extend(rem.iter().cloned());
            result
        }
        PatternDesc::Tpat_tuple(args) => {
            let mut result = args.clone();
            result.extend(rem.iter().cloned());
            result
        }
        _ => panic!("get_args_tuple: not a tuple or any pattern"),
    }
}

/// Matcher for tuple patterns.
/// Equivalent to OCaml's `matcher_tuple`.
fn matcher_tuple(
    arity: usize,
    p: &Pattern,
    rem: &[Pattern],
) -> Result<Vec<Pattern>, MatchError> {
    match &p.pat_desc {
        PatternDesc::Tpat_or(_, _, _) => Err(MatchError::OrPat),
        PatternDesc::Tpat_any | PatternDesc::Tpat_var(..) => {
            let mut result = omegas(arity);
            result.extend(rem.iter().cloned());
            Ok(result)
        }
        PatternDesc::Tpat_tuple(args) if args.len() == arity => {
            let mut result = args.clone();
            result.extend(rem.iter().cloned());
            Ok(result)
        }
        _ => Err(MatchError::NoMatch),
    }
}

/// Make a tuple matching.
/// Equivalent to OCaml's `make_tuple_matching`.
fn make_tuple_matching(
    loc: Location,
    arity: usize,
    def: &DefaultEnv,
    args: &[(RawLambda, LetKind)],
) -> PatternMatching {
    match args.split_first() {
        None => panic!("Matching.make_tuple_matching"),
        Some(((arg, _mut), argl)) => {
            let mut new_args = Vec::new();
            for pos in 0..arity {
                new_args.push((
                    RawLambda::Lprim(RawPrimInfo {
                        primitive: Primitive::Pfield(pos as i32, FieldDbgInfo::Tuple),
                        args: vec![arg.clone()],
                        loc: loc.clone(),
                    }),
                    LetKind::Alias,
                ));
            }
            new_args.extend(argl.iter().cloned());
            PatternMatching {
                cases: Vec::new(),
                args: new_args,
                default: make_default(
                    &|p2, rem| matcher_tuple(arity, p2, rem),
                    def,
                ),
            }
        }
    }
}

/// Divide a pattern matching by tuple.
/// Equivalent to OCaml's `divide_tuple`.
fn divide_tuple(arity: usize, p: &Pattern, ctx: &[Ctx], pm: &PatternMatching) -> MatchCell {
    divide_line(
        |c| filter_ctx(p, c),
        |def, args| make_tuple_matching(Location::none(), arity, def, args),
        |pat, rem| get_args_tuple(arity, pat, rem),
        p.clone(),
        ctx,
        pm,
    )
}

// --- Records (lines 1417-1476) ---

/// Build a list of patterns for record matching, filling in omegas for missing fields.
/// Equivalent to OCaml's `record_matching_line`.
fn record_matching_line(
    num_fields: usize,
    lbl_pat_list: &[(impl std::any::Any, LabelDescription, Pattern, bool)],
) -> Vec<Pattern> {
    let mut patv: Vec<Pattern> = (0..num_fields).map(|_| omega()).collect();
    for (_, lbl, pat, _) in lbl_pat_list {
        patv[lbl.lbl_pos as usize] = pat.clone();
    }
    patv
}

/// Build a record matching line from a Tpat_record pattern's fields.
/// This version takes the typed record fields directly.
fn record_matching_line_from_fields(
    num_fields: usize,
    fields: &[(crate::types::typedtree::Loc<crate::parse_arena::LidentIdx>, LabelDescription, Pattern, bool)],
) -> Vec<Pattern> {
    // Determine the actual size needed: max of num_fields and any label position + 1.
    let max_pos = fields.iter().map(|(_, lbl, _, _)| lbl.lbl_pos as usize + 1).max().unwrap_or(0);
    let size = std::cmp::max(num_fields, max_pos);
    let mut patv: Vec<Pattern> = (0..size).map(|_| omega()).collect();
    for (_, lbl, pat, _) in fields {
        patv[lbl.lbl_pos as usize] = pat.clone();
    }
    patv
}

/// Get the arguments from a record pattern.
/// Equivalent to OCaml's `get_args_record`.
fn get_args_record(num_fields: usize, p: &Pattern, rem: &[Pattern]) -> Vec<Pattern> {
    match &p.pat_desc {
        PatternDesc::Tpat_any => {
            let mut result = record_matching_line_from_fields(num_fields, &[]);
            result.extend(rem.iter().cloned());
            result
        }
        PatternDesc::Tpat_record(lbl_pat_list, _) => {
            let mut result = record_matching_line_from_fields(num_fields, lbl_pat_list);
            result.extend(rem.iter().cloned());
            result
        }
        _ => panic!("get_args_record: not a record or any pattern"),
    }
}

/// Matcher for record patterns.
/// Equivalent to OCaml's `matcher_record`.
fn matcher_record(
    num_fields: usize,
    p: &Pattern,
    rem: &[Pattern],
) -> Result<Vec<Pattern>, MatchError> {
    match &p.pat_desc {
        PatternDesc::Tpat_or(_, _, _) => Err(MatchError::OrPat),
        PatternDesc::Tpat_any | PatternDesc::Tpat_var(..) => {
            let mut result = record_matching_line_from_fields(num_fields, &[]);
            result.extend(rem.iter().cloned());
            Ok(result)
        }
        PatternDesc::Tpat_record(fields, _) if fields.is_empty() && num_fields == 0 => {
            Ok(rem.to_vec())
        }
        PatternDesc::Tpat_record(lbl_pat_list, _) => {
            // Check that the first label's lbl_all length matches num_fields.
            // In OCaml: Array.length lbl.lbl_all = num_fields
            // In Rust, lbl_all is a LabelArrayRef placeholder. We check using
            // the all_labels array passed to divide_record instead.
            // For the matcher, we trust the caller's num_fields is correct.
            if !lbl_pat_list.is_empty() {
                let mut result = record_matching_line_from_fields(num_fields, lbl_pat_list);
                result.extend(rem.iter().cloned());
                Ok(result)
            } else {
                Err(MatchError::NoMatch)
            }
        }
        _ => Err(MatchError::NoMatch),
    }
}

/// Make a record matching.
/// Equivalent to OCaml's `make_record_matching`.
fn make_record_matching(
    loc: Location,
    all_labels: &[LabelDescription],
    def: &DefaultEnv,
    args: &[(RawLambda, LetKind)],
) -> PatternMatching {
    match args.split_first() {
        None => panic!("Matching.make_record_matching"),
        Some(((arg, _mut), argl)) => {
            let mut new_args = Vec::new();
            for lbl in all_labels.iter() {
                let access = match &lbl.lbl_repres {
                    RecordRepresentation::RecordFloatUnused => {
                        panic!("Record_float_unused")
                    }
                    RecordRepresentation::RecordRegular => {
                        RawLambda::Lprim(RawPrimInfo {
                            primitive: Primitive::Pfield(
                                lbl.lbl_pos,
                                fld_record(lbl),
                            ),
                            args: vec![arg.clone()],
                            loc: loc.clone(),
                        })
                    }
                    RecordRepresentation::RecordInlined { .. } => {
                        RawLambda::Lprim(RawPrimInfo {
                            primitive: Primitive::Pfield(
                                lbl.lbl_pos,
                                fld_record_inline(lbl),
                            ),
                            args: vec![arg.clone()],
                            loc: loc.clone(),
                        })
                    }
                    RecordRepresentation::RecordUnboxed(_) => arg.clone(),
                    RecordRepresentation::RecordExtension => {
                        RawLambda::Lprim(RawPrimInfo {
                            primitive: Primitive::Pfield(
                                lbl.lbl_pos + 1,
                                fld_record_extension(lbl),
                            ),
                            args: vec![arg.clone()],
                            loc: loc.clone(),
                        })
                    }
                };
                let str_kind = match lbl.lbl_mut {
                    MutableFlag::Immutable => LetKind::Alias,
                    MutableFlag::Mutable => LetKind::StrictOpt,
                };
                new_args.push((access, str_kind));
            }
            new_args.extend(argl.iter().cloned());
            let nfields = all_labels.len();
            let def = make_default(
                &|p2, rem| matcher_record(nfields, p2, rem),
                def,
            );
            PatternMatching {
                cases: Vec::new(),
                args: new_args,
                default: def,
            }
        }
    }
}

/// Divide a pattern matching by record fields.
/// Equivalent to OCaml's `divide_record`.
fn divide_record(
    all_labels: &[LabelDescription],
    p: &Pattern,
    ctx: &[Ctx],
    pm: &PatternMatching,
) -> MatchCell {
    let num_fields = all_labels.len();
    divide_line(
        |c| filter_ctx(p, c),
        |def, args| make_record_matching(Location::none(), all_labels, def, args),
        |pat, rem| get_args_record(num_fields, pat, rem),
        p.clone(),
        ctx,
        pm,
    )
}

// --- Arrays (lines 1480-1516) ---

/// Get the key (length) from an array pattern.
/// Equivalent to OCaml's `get_key_array`.
fn get_key_array(p: &Pattern) -> usize {
    match &p.pat_desc {
        PatternDesc::Tpat_array(patl) => patl.len(),
        _ => panic!("get_key_array: not an array pattern"),
    }
}

/// Get the arguments from an array pattern.
/// Equivalent to OCaml's `get_args_array`.
fn get_args_array(p: &Pattern, rem: &[Pattern]) -> Vec<Pattern> {
    match &p.pat_desc {
        PatternDesc::Tpat_array(patl) => {
            let mut result = patl.clone();
            result.extend(rem.iter().cloned());
            result
        }
        _ => panic!("get_args_array: not an array pattern"),
    }
}

/// Matcher for array patterns.
/// Equivalent to OCaml's `matcher_array`.
fn matcher_array(
    len: usize,
    p: &Pattern,
    rem: &[Pattern],
) -> Result<Vec<Pattern>, MatchError> {
    match &p.pat_desc {
        PatternDesc::Tpat_or(_, _, _) => Err(MatchError::OrPat),
        PatternDesc::Tpat_array(args) if args.len() == len => {
            let mut result = args.clone();
            result.extend(rem.iter().cloned());
            Ok(result)
        }
        PatternDesc::Tpat_any => {
            let mut result = omegas(len);
            result.extend(rem.iter().cloned());
            Ok(result)
        }
        _ => Err(MatchError::NoMatch),
    }
}

/// Make an array matching cell.
/// Equivalent to OCaml's `make_array_matching`.
fn make_array_matching(
    p: &Pattern,
    def: &DefaultEnv,
    ctx: &[Ctx],
    args: &[(RawLambda, LetKind)],
) -> MatchCell {
    match args.split_first() {
        None => panic!("Matching.make_array_matching"),
        Some(((arg, _mut), argl)) => {
            let len = get_key_array(p);
            let mut new_args = Vec::new();
            for pos in 0..len {
                new_args.push((
                    RawLambda::Lprim(RawPrimInfo {
                        primitive: Primitive::Parrayrefu,
                        args: vec![
                            arg.clone(),
                            RawLambda::Lconst(crate::lambda::Constant::Int {
                                i: pos as i32,
                                comment: None,
                            }),
                        ],
                        loc: Location::none(),
                    }),
                    LetKind::StrictOpt,
                ));
            }
            new_args.extend(argl.iter().cloned());
            let def = make_default(
                &|p2, rem| matcher_array(len, p2, rem),
                def,
            );
            let ctx = filter_ctx(p, ctx);
            MatchCell {
                pm: PatternMatching {
                    cases: Vec::new(),
                    args: new_args,
                    default: def,
                },
                ctx,
                pat: normalize_pat(p),
            }
        }
    }
}

/// Divide a pattern matching by array length.
/// Equivalent to OCaml's `divide_array`.
fn divide_array(ctx: &[Ctx], pm: &PatternMatching) -> Vec<(usize, MatchCell)> {
    divide(
        make_array_matching,
        |a, b| a == b,
        get_key_array,
        get_args_array,
        ctx,
        pm,
    )
}

// ============================================================================
// Layer 7: String matching — OCaml matching.ml lines 1532-1659
// ============================================================================

/// Threshold for switching from dichotomic tree to sequential tests.
/// Equivalent to OCaml's `strings_test_threshold`.
const STRINGS_TEST_THRESHOLD: usize = 8;

/// Bind a switch argument to a variable if it's not already a variable.
/// Equivalent to OCaml's `bind_sw`.
fn bind_sw(arg: RawLambda, k: impl FnOnce(RawLambda) -> RawLambda) -> RawLambda {
    match &arg {
        RawLambda::Lvar(_) => k(arg),
        _ => {
            let id = Ident::create_local("switch");
            let var = RawLambda::Lvar(id.clone());
            let body = k(var);
            RawLambda::Llet(LetKind::Strict, id, Box::new(arg), Box::new(body))
        }
    }
}

/// Build a sequential string equality test sequence.
/// Equivalent to OCaml's `make_string_test_sequence`.
fn make_string_test_sequence(
    loc: Location,
    arg: RawLambda,
    sw: Vec<(String, RawLambda)>,
    d: Option<RawLambda>,
) -> RawLambda {
    let (d, sw) = match d {
        None => {
            let mut sw = sw;
            assert!(!sw.is_empty());
            let (_, d) = sw.remove(0);
            (d, sw)
        }
        Some(d) => (d, sw),
    };
    bind_sw(arg, |arg| {
        // fold_right: iterate from the end
        let mut result = d;
        for (s, lam) in sw.into_iter().rev() {
            result = RawLambda::LifThenElse(
                Box::new(RawLambda::Lprim(RawPrimInfo {
                    primitive: Primitive::Pstringcomp(Comparison::Neq),
                    args: vec![
                        arg.clone(),
                        RawLambda::Lconst(crate::lambda::Constant::ImmString(s)),
                    ],
                    loc: loc.clone(),
                })),
                Box::new(result),
                Box::new(lam),
            );
        }
        result
    })
}

/// Split a list into three parts: before middle, middle element, after middle.
/// Equivalent to OCaml's `split`.
fn split<T>(k: usize, xs: Vec<T>) -> (Vec<T>, T, Vec<T>) {
    assert!(!xs.is_empty());
    let mut iter = xs.into_iter();
    if k <= 1 {
        let x0 = iter.next().unwrap();
        let rest: Vec<T> = iter.collect();
        (Vec::new(), x0, rest)
    } else {
        let x0 = iter.next().unwrap();
        let rest: Vec<T> = iter.collect();
        let (mut xs, y0, ys) = split(k - 2, rest);
        xs.insert(0, x0);
        (xs, y0, ys)
    }
}

/// Zero lambda constant.
/// Equivalent to OCaml's `zero_lam`.
fn zero_lam() -> RawLambda {
    RawLambda::Lconst(crate::lambda::Constant::int(0))
}

/// Three-way test on an integer value (less than, equal, greater than zero).
/// Equivalent to OCaml's `tree_way_test`.
fn tree_way_test(loc: Location, arg: RawLambda, lt: RawLambda, eq: RawLambda, gt: RawLambda) -> RawLambda {
    RawLambda::LifThenElse(
        Box::new(RawLambda::Lprim(RawPrimInfo {
            primitive: Primitive::Pintcomp(Comparison::Lt),
            args: vec![arg.clone(), zero_lam()],
            loc: loc.clone(),
        })),
        Box::new(lt),
        Box::new(RawLambda::LifThenElse(
            Box::new(RawLambda::Lprim(RawPrimInfo {
                primitive: Primitive::Pintcomp(Comparison::Lt),
                args: vec![zero_lam(), arg],
                loc,
            })),
            Box::new(gt),
            Box::new(eq),
        )),
    )
}

/// Build a dichotomic string test tree.
/// Equivalent to OCaml's `do_make_string_test_tree`.
fn do_make_string_test_tree(
    loc: Location,
    arg: RawLambda,
    sw: Vec<(String, RawLambda)>,
    delta: usize,
    d: Option<RawLambda>,
) -> RawLambda {
    let len = sw.len();
    if len <= STRINGS_TEST_THRESHOLD + delta {
        make_string_test_sequence(loc, arg, sw, d)
    } else {
        let (lt, (s, act), gt) = split(len, sw);
        bind_sw(
            RawLambda::Lprim(RawPrimInfo {
                primitive: Primitive::Pstringcomp(Comparison::Eq),
                args: vec![
                    arg.clone(),
                    RawLambda::Lconst(crate::lambda::Constant::ImmString(s)),
                ],
                loc: loc.clone(),
            }),
            |r| {
                tree_way_test(
                    loc.clone(),
                    r,
                    do_make_string_test_tree(loc.clone(), arg.clone(), lt, delta, d.clone()),
                    act,
                    do_make_string_test_tree(loc.clone(), arg.clone(), gt, delta, d.clone()),
                )
            },
        )
    }
}

/// Expand a string switch into a test tree.
/// Entry point for string matching.
/// Equivalent to OCaml's `expand_stringswitch`.
pub fn expand_stringswitch(
    loc: Location,
    arg: RawLambda,
    sw: Vec<(String, RawLambda)>,
    d: Option<RawLambda>,
    next_raise_count: &mut i32,
) -> RawLambda {
    match d {
        None => bind_sw(arg, |arg| {
            do_make_string_test_tree(loc, arg, sw, 0, None)
        }),
        Some(e) => bind_sw(arg, |arg| {
            make_catch(e, next_raise_count, |d| {
                do_make_string_test_tree(loc, arg, sw, 1, Some(d))
            })
        }),
    }
}

// ============================================================================
// Generic test trees — Sharing (OCaml matching.ml lines 1609-1659)
// ============================================================================

/// Process shared actions for tree-based matching.
/// Returns `(wrapper_fn, processed_sw, processed_d)`.
/// The wrapper_fn wraps the result with catch handlers.
///
/// Equivalent to OCaml's `share_actions_tree`.
fn share_actions_tree(
    sw: Vec<(Constant, RawLambda)>,
    d: Option<RawLambda>,
    next_raise_count: &mut i32,
) -> (Vec<(i32, RawLambda)>, Vec<(Constant, RawLambda)>, Option<RawLambda>) {
    let mut store = StoreExp::mk_store();

    // Default action is always shared
    let d_idx = match &d {
        None => None,
        Some(d) => Some(store.act_store_shared(d.clone())),
    };

    // Store all other actions
    let sw_indices: Vec<(Constant, usize)> = sw
        .into_iter()
        .map(|(cst, act)| (cst, store.act_store(act)))
        .collect();

    // Retrieve all actions, including potential default
    let acts = store.act_get_shared();

    // Process shared actions — OCaml's handle_shared
    let mut handlers: Vec<(i32, Box<dyn FnOnce(RawLambda) -> RawLambda>)> = Vec::new();
    let resolved_acts: Vec<RawLambda> = acts
        .into_iter()
        .map(|act| match act {
            SharedAction::Single(a) => a,
            SharedAction::Shared(a) => {
                let (i, h) = make_catch_delayed(a, next_raise_count);
                handlers.push((i, h));
                make_exit(i)
            }
        })
        .collect();

    // Reconstruct default and switch list
    let d = match d_idx {
        None => None,
        Some(idx) => Some(resolved_acts[idx].clone()),
    };
    let sw: Vec<(Constant, RawLambda)> = sw_indices
        .into_iter()
        .map(|(cst, j)| (cst, resolved_acts[j].clone()))
        .collect();

    // Build the handler wrappers as (exit_id, handler_body) pairs
    // OCaml composes: hs := fun act -> h(ohs(act))
    // This means the FIRST handler added is the INNERMOST catch.
    // We collect (i, h) pairs where h is the catch wrapper.
    let handler_pairs: Vec<(i32, RawLambda)> = handlers
        .into_iter()
        .map(|(i, h)| {
            // h is a FnOnce that wraps body in LstaticCatch if needed.
            // We need to extract the handler body from it.
            // Actually, make_catch_delayed returns (i, wrapper).
            // To get the handler body, we can call h with a static raise as body
            // and it will wrap with LstaticCatch(body, (i, []), handler_body).
            // But that's roundabout. Let's rethink.

            // Actually, we need to store the wrapper functions and apply them
            // to the final result. Let's return them directly.
            // The caller will apply them in order.

            // For now, call the wrapper with a dummy to extract the handler.
            // h(Lstaticraise(i, [])) returns handler directly.
            // h(anything_else) returns LstaticCatch(anything_else, (i, []), handler).
            let dummy = RawLambda::Lconst(crate::lambda::Constant::int(0));
            let wrapped = h(dummy);
            match wrapped {
                RawLambda::LstaticCatch(_, (exit_id, _), handler) => (exit_id, *handler),
                // If h was identity (handler was already a simple exit), this won't be reached
                // because make_catch_delayed returns identity for simple exits, so the action
                // would have been the exit itself, not going through Shared path.
                other => (i, other),
            }
        })
        .collect();

    (handler_pairs, sw, d)
}

/// Apply handler wrappers to a result lambda.
/// The handlers are applied in forward order (first handler = innermost).
/// Equivalent to OCaml's `!hs result`.
fn apply_handlers(mut result: RawLambda, handlers: Vec<(i32, RawLambda)>) -> RawLambda {
    // OCaml composes: hs := fun act -> h(ohs(act))
    // First handler added is innermost, last is outermost.
    // Each wrapper h wraps the body in LstaticCatch(body, (i,[]), handler_body).
    // So iterating forward: first handler wraps result first (innermost),
    // then each subsequent handler wraps around (outermost).
    for (exit_id, handler) in handlers.into_iter() {
        match &result {
            RawLambda::LstaticRaise(j, args) if *j == exit_id && args.is_empty() => {
                result = handler;
            }
            _ => {
                result = RawLambda::LstaticCatch(
                    Box::new(result),
                    (exit_id, Vec::new()),
                    Box::new(handler),
                );
            }
        }
    }
    result
}

/// Remove duplicate entries from a sorted (constant, lambda) list.
/// Keeps the first occurrence of each constant.
/// Equivalent to OCaml's `uniq_lambda_list`.
fn uniq_lambda_list(sw: Vec<(Constant, RawLambda)>) -> Vec<(Constant, RawLambda)> {
    if sw.len() <= 1 {
        return sw;
    }
    let mut result: Vec<(Constant, RawLambda)> = Vec::new();
    let mut iter = sw.into_iter();
    let first = iter.next().unwrap();
    result.push(first);
    for (c2, lam2) in iter {
        let last_c = &result.last().unwrap().0;
        if const_compare(last_c, &c2) == std::cmp::Ordering::Equal {
            // Duplicate — skip (keep the first, which is already in result)
            // OCaml keeps p1 (first) and drops the second
        } else {
            result.push((c2, lam2));
        }
    }
    result
}

/// Sort a (constant, lambda) list by constant value, then remove duplicates.
/// Equivalent to OCaml's `sort_lambda_list`.
fn sort_lambda_list(mut l: Vec<(Constant, RawLambda)>) -> Vec<(Constant, RawLambda)> {
    l.sort_by(|(x, _), (y, _)| const_compare(x, y));
    uniq_lambda_list(l)
}

// ============================================================================
// Layer 8: Integer/switch matching — OCaml matching.ml lines 1661-1941
// ============================================================================

/// Cut a list at position n, returning (first_n_elements, rest).
/// Equivalent to OCaml's `cut`.
fn cut<T>(n: usize, l: Vec<T>) -> (Vec<T>, Vec<T>) {
    if n == 0 {
        return (Vec::new(), l);
    }
    assert!(!l.is_empty(), "cut: list too short");
    let mut iter = l.into_iter();
    let mut first = Vec::with_capacity(n);
    for _ in 0..n {
        first.push(iter.next().expect("cut: list too short"));
    }
    let rest: Vec<T> = iter.collect();
    (first, rest)
}

/// Sequential equality tests with a fail action.
/// Equivalent to OCaml's `do_tests_fail`.
fn do_tests_fail(
    loc: Location,
    fail: RawLambda,
    tst: Primitive,
    arg: RawLambda,
    cases: &[(Constant, RawLambda)],
) -> RawLambda {
    if cases.is_empty() {
        return fail;
    }
    let (c, act) = &cases[0];
    let rest = &cases[1..];
    RawLambda::LifThenElse(
        Box::new(RawLambda::Lprim(RawPrimInfo {
            primitive: tst.clone(),
            args: vec![arg.clone(), typed_const_to_lambda_const(c)],
            loc: loc.clone(),
        })),
        Box::new(do_tests_fail(loc, fail, tst, arg, rest)),
        Box::new(act.clone()),
    )
}

/// Sequential equality tests without a fail action.
/// Equivalent to OCaml's `do_tests_nofail`.
fn do_tests_nofail(
    loc: Location,
    tst: Primitive,
    arg: RawLambda,
    cases: &[(Constant, RawLambda)],
) -> RawLambda {
    assert!(!cases.is_empty(), "Matching.do_tests_nofail");
    if cases.len() == 1 {
        return cases[0].1.clone();
    }
    let (c, act) = &cases[0];
    let rest = &cases[1..];
    RawLambda::LifThenElse(
        Box::new(RawLambda::Lprim(RawPrimInfo {
            primitive: tst.clone(),
            args: vec![arg.clone(), typed_const_to_lambda_const(c)],
            loc: loc.clone(),
        })),
        Box::new(do_tests_nofail(loc, tst, arg, rest)),
        Box::new(act.clone()),
    )
}

/// Convert a typedtree constant to a lambda constant wrapped in Lconst.
/// Equivalent to OCaml's `Lconst(Const_base c)`.
fn typed_const_to_lambda_const(c: &Constant) -> RawLambda {
    let lc = match c {
        Constant::Int(i) => crate::lambda::Constant::int(*i as i32),
        Constant::Char(c) => crate::lambda::Constant::Char(*c),
        Constant::String(s, _) => crate::lambda::Constant::String {
            s: s.clone(),
            delim: None,
        },
        Constant::Float(f) => crate::lambda::Constant::Float(f.clone()),
        Constant::BigInt(positive, v) => crate::lambda::Constant::BigInt {
            negative: !*positive,
            value: v.clone(),
        },
    };
    RawLambda::Lconst(lc)
}

/// Build a test sequence for constant matching.
/// Uses dichotomic splitting when there are enough cases and a less-than test is available.
/// Equivalent to OCaml's `make_test_sequence`.
fn make_test_sequence(
    loc: Location,
    fail: Option<RawLambda>,
    tst: Primitive,
    lt_tst: Primitive,
    arg: RawLambda,
    const_lambda_list: Vec<(Constant, RawLambda)>,
    next_raise_count: &mut i32,
) -> RawLambda {
    let const_lambda_list = sort_lambda_list(const_lambda_list);
    let (handlers, const_lambda_list, fail) =
        share_actions_tree(const_lambda_list, fail, next_raise_count);

    fn make_test_seq_inner(
        loc: &Location,
        fail: &Option<RawLambda>,
        tst: &Primitive,
        lt_tst: &Primitive,
        arg: &RawLambda,
        const_lambda_list: &[(Constant, RawLambda)],
    ) -> RawLambda {
        if const_lambda_list.len() >= 4 && !matches!(lt_tst, Primitive::Pignore) {
            split_sequence(loc, fail, tst, lt_tst, arg, const_lambda_list)
        } else {
            match fail {
                None => do_tests_nofail(loc.clone(), tst.clone(), arg.clone(), const_lambda_list),
                Some(fail) => do_tests_fail(loc.clone(), fail.clone(), tst.clone(), arg.clone(), const_lambda_list),
            }
        }
    }

    fn split_sequence(
        loc: &Location,
        fail: &Option<RawLambda>,
        tst: &Primitive,
        lt_tst: &Primitive,
        arg: &RawLambda,
        const_lambda_list: &[(Constant, RawLambda)],
    ) -> RawLambda {
        let mid = const_lambda_list.len() / 2;
        let (list1, list2) = const_lambda_list.split_at(mid);
        let pivot_const = &list2[0].0;
        RawLambda::LifThenElse(
            Box::new(RawLambda::Lprim(RawPrimInfo {
                primitive: lt_tst.clone(),
                args: vec![arg.clone(), typed_const_to_lambda_const(pivot_const)],
                loc: loc.clone(),
            })),
            Box::new(make_test_seq_inner(loc, fail, tst, lt_tst, arg, list1)),
            Box::new(make_test_seq_inner(loc, fail, tst, lt_tst, arg, list2)),
        )
    }

    let result = make_test_seq_inner(&loc, &fail, &tst, &lt_tst, &arg, &const_lambda_list);
    apply_handlers(result, handlers)
}

// ============================================================================
// SArg module — Switch module arguments (OCaml matching.ml lines 1708-1758)
// ============================================================================
// The SArg module in OCaml provides the primitives needed by Switch.Make.
// In Rust, the switch.rs module already has these functions built in.
// The functions below provide matching.ml-level wrappers.

/// SArg: make a primitive application.
/// Equivalent to OCaml's `SArg.make_prim`.
fn sarg_make_prim(p: Primitive, args: Vec<RawLambda>) -> RawLambda {
    RawLambda::Lprim(RawPrimInfo {
        primitive: p,
        args,
        loc: Location::none(),
    })
}

/// SArg: add an offset to an argument.
/// Equivalent to OCaml's `SArg.make_offset`.
fn sarg_make_offset(arg: RawLambda, n: i32) -> RawLambda {
    if n == 0 {
        arg
    } else {
        RawLambda::Lprim(RawPrimInfo {
            primitive: Primitive::Poffsetint(n),
            args: vec![arg],
            loc: Location::none(),
        })
    }
}

/// SArg: bind a variable.
/// Equivalent to OCaml's `SArg.bind`.
fn sarg_bind(arg: RawLambda, body: impl FnOnce(RawLambda) -> RawLambda) -> RawLambda {
    match &arg {
        RawLambda::Lvar(v) => {
            let newarg = arg.clone();
            let result = body(newarg);
            RawLambda::Llet(LetKind::Alias, v.clone(), Box::new(arg), Box::new(result))
        }
        _ => {
            let newvar = Ident::create_local("switcher");
            let newarg = RawLambda::Lvar(newvar.clone());
            let result = body(newarg);
            RawLambda::Llet(LetKind::Alias, newvar, Box::new(arg), Box::new(result))
        }
    }
}

/// SArg: make a constant integer.
/// Equivalent to OCaml's `SArg.make_const`.
fn sarg_make_const(i: i32) -> RawLambda {
    RawLambda::Lconst(crate::lambda::Constant::int(i))
}

/// SArg: make an `isout` test.
/// Equivalent to OCaml's `SArg.make_isout`.
fn sarg_make_isout(h: RawLambda, arg: RawLambda) -> RawLambda {
    RawLambda::Lprim(RawPrimInfo {
        primitive: Primitive::Pisout(match &h {
            RawLambda::Lconst(crate::lambda::Constant::Int { i, .. }) => *i,
            _ => 0,
        }),
        args: vec![arg],
        loc: Location::none(),
    })
}

/// SArg: make an `isin` test.
/// Equivalent to OCaml's `SArg.make_isin`.
fn sarg_make_isin(h: RawLambda, arg: RawLambda) -> RawLambda {
    RawLambda::Lprim(RawPrimInfo {
        primitive: Primitive::Pnot,
        args: vec![sarg_make_isout(h, arg)],
        loc: Location::none(),
    })
}

/// SArg: make an if-then-else.
/// Equivalent to OCaml's `SArg.make_if`.
fn sarg_make_if(cond: RawLambda, ifso: RawLambda, ifnot: RawLambda) -> RawLambda {
    RawLambda::LifThenElse(Box::new(cond), Box::new(ifso), Box::new(ifnot))
}

/// SArg: make a switch.
/// Equivalent to OCaml's `SArg.make_switch`.
fn sarg_make_switch(
    _loc: Location,
    arg: RawLambda,
    cases: &[usize],
    acts: &[RawLambda],
    offset: i32,
    sw_names: Option<SwitchNames>,
) -> RawLambda {
    let mut l: Vec<(i32, RawLambda)> = Vec::new();
    for i in (0..cases.len()).rev() {
        l.push((offset + i as i32, acts[cases[i]].clone()));
    }
    l.reverse();
    RawLambda::Lswitch(
        Box::new(arg),
        RawLambdaSwitch {
            sw_consts_full: false,
            sw_consts: l,
            sw_blocks_full: false,
            sw_blocks: Vec::new(),
            sw_failaction: None,
            sw_names,
        },
    )
}

// ============================================================================
// Action sharing for Lswitch argument (OCaml matching.ml lines 1761-1833)
// ============================================================================

/// Deduplicate switch actions by wrapping shared actions in catch/exit.
/// Equivalent to OCaml's `share_actions_sw`.
pub fn share_actions_sw(
    sw: RawLambdaSwitch,
    next_raise_count: &mut i32,
) -> (Vec<(i32, RawLambda)>, RawLambdaSwitch) {
    let mut store = StoreExp::mk_store();

    // Store fail action as shared
    let fail_idx = match &sw.sw_failaction {
        None => None,
        Some(fail) => Some(store.act_store_shared(*fail.clone())),
    };

    // Store const and block actions
    let consts: Vec<(i32, usize)> = sw
        .sw_consts
        .iter()
        .map(|(i, e)| (*i, store.act_store(e.clone())))
        .collect();
    let blocks: Vec<(i32, usize)> = sw
        .sw_blocks
        .iter()
        .map(|(i, e)| (*i, store.act_store(e.clone())))
        .collect();

    // Get shared actions
    let acts = store.act_get_shared();

    // Process shared actions (handle_shared pattern)
    let mut handlers: Vec<(i32, RawLambda)> = Vec::new();
    let resolved_acts: Vec<RawLambda> = acts
        .into_iter()
        .map(|act| match act {
            SharedAction::Single(a) => a,
            SharedAction::Shared(a) => {
                let (i, h) = make_catch_delayed(a.clone(), next_raise_count);
                // Extract handler body from the wrapper function
                let dummy = RawLambda::Lconst(crate::lambda::Constant::int(0));
                let wrapped = h(dummy);
                match wrapped {
                    RawLambda::LstaticCatch(_, (exit_id, _), handler) => {
                        handlers.push((exit_id, *handler));
                        make_exit(exit_id)
                    }
                    _ => {
                        // h was identity — the action is already a simple exit.
                        // Use the original action directly; the exit already
                        // targets an existing handler, no new wrapper needed.
                        make_exit(i)
                    }
                }
            }
        })
        .collect();

    // Reconstruct fail
    let fail = match fail_idx {
        None => None,
        Some(idx) => Some(Box::new(resolved_acts[idx].clone())),
    };

    let new_sw = RawLambdaSwitch {
        sw_consts_full: sw.sw_consts_full,
        sw_consts: consts
            .into_iter()
            .map(|(i, j)| (i, resolved_acts[j].clone()))
            .collect(),
        sw_blocks_full: sw.sw_blocks_full,
        sw_blocks: blocks
            .into_iter()
            .map(|(i, j)| (i, resolved_acts[j].clone()))
            .collect(),
        sw_failaction: fail,
        sw_names: sw.sw_names,
    };

    (handlers, new_sw)
}

/// Reintroduce fail action in switch argument.
/// When a static exit appears >= 3 times in the cases and there's no failaction,
/// extract it as the failaction to reduce switch size.
/// Equivalent to OCaml's `reintroduce_fail`.
pub fn reintroduce_fail(sw: RawLambdaSwitch) -> RawLambdaSwitch {
    if sw.sw_failaction.is_some() {
        return sw;
    }

    let mut counts: HashMap<i32, i32> = HashMap::new();
    let seen = |counts: &mut HashMap<i32, i32>, lam: &RawLambda| {
        if let Some(i) = as_simple_exit(lam) {
            let old = counts.get(&i).copied().unwrap_or(0);
            counts.insert(i, old + 1);
        }
    };

    for (_, l) in &sw.sw_consts {
        seen(&mut counts, l);
    }
    for (_, l) in &sw.sw_blocks {
        seen(&mut counts, l);
    }

    let mut i_max: i32 = -1;
    let mut max: i32 = -1;
    for (&i, &c) in &counts {
        if c > max || (c == max && i > i_max) {
            i_max = i;
            max = c;
        }
    }

    if max >= 3 {
        let default = i_max;
        let remove = |ls: Vec<(i32, RawLambda)>| -> Vec<(i32, RawLambda)> {
            ls.into_iter()
                .filter(|(_, lam)| match as_simple_exit(lam) {
                    Some(j) => j != default,
                    None => true,
                })
                .collect()
        };
        RawLambdaSwitch {
            sw_consts_full: sw.sw_consts_full,
            sw_consts: remove(sw.sw_consts),
            sw_blocks_full: sw.sw_blocks_full,
            sw_blocks: remove(sw.sw_blocks),
            sw_failaction: Some(Box::new(make_exit(default))),
            sw_names: sw.sw_names,
        }
    } else {
        sw
    }
}

// ============================================================================
// Switcher = Switch.Make(SArg) — uses switch.rs (OCaml matching.ml line 1835)
// ============================================================================

// The Switcher module is already ported in switch.rs.
// The following functions provide the matching.ml-level interface.

/// Get the last key from a sorted list of (int, lambda) pairs.
/// Equivalent to OCaml's `last`.
fn last_key(def: i32, l: &[(i32, RawLambda)]) -> i32 {
    match l.last() {
        None => def,
        Some((x, _)) => *x,
    }
}

/// Get the edge values (low, high) from a sorted list.
/// Equivalent to OCaml's `get_edges`.
fn get_edges(low: i32, high: i32, l: &[(i32, RawLambda)]) -> (i32, i32) {
    match l.first() {
        None => (low, high),
        Some((x, _)) => (*x, last_key(high, l)),
    }
}

/// Convert a sorted int-lambda list with a fail action into intervals.
/// Equivalent to OCaml's `as_interval_canfail`.
fn as_interval_canfail(
    fail: RawLambda,
    low: i32,
    high: i32,
    l: &[(i32, RawLambda)],
) -> (Vec<(i32, i32, usize)>, StoreExp) {
    let mut store = StoreExp::mk_store();

    let fail_idx = store.act_store(fail);
    assert_eq!(fail_idx, 0); // fail has action index 0

    fn nofail_rec(
        cur_low: i32,
        cur_high: i32,
        cur_act: usize,
        rest: &[(i32, RawLambda)],
        high: i32,
        store: &mut StoreExp,
    ) -> Vec<(i32, i32, usize)> {
        if rest.is_empty() {
            if cur_high == high {
                vec![(cur_low, cur_high, cur_act)]
            } else {
                vec![(cur_low, cur_high, cur_act), (cur_high + 1, high, 0)]
            }
        } else {
            let (i, ref act_i) = rest[0];
            let act_index = store.act_store(act_i.clone());
            if cur_high + 1 == i {
                if act_index == cur_act {
                    nofail_rec(cur_low, i, cur_act, &rest[1..], high, store)
                } else if act_index == 0 {
                    let mut r = vec![(cur_low, i - 1, cur_act)];
                    r.extend(fail_rec(i, i, &rest[1..], high, store));
                    r
                } else {
                    let mut r = vec![(cur_low, i - 1, cur_act)];
                    r.extend(nofail_rec(i, i, act_index, &rest[1..], high, store));
                    r
                }
            } else if act_index == 0 {
                let mut r = vec![(cur_low, cur_high, cur_act)];
                r.extend(fail_rec(cur_high + 1, cur_high + 1, rest, high, store));
                r
            } else {
                let mut r = vec![
                    (cur_low, cur_high, cur_act),
                    (cur_high + 1, i - 1, 0),
                ];
                r.extend(nofail_rec(i, i, act_index, &rest[1..], high, store));
                r
            }
        }
    }

    fn fail_rec(
        cur_low: i32,
        cur_high: i32,
        rest: &[(i32, RawLambda)],
        high: i32,
        store: &mut StoreExp,
    ) -> Vec<(i32, i32, usize)> {
        if rest.is_empty() {
            vec![(cur_low, cur_high, 0)]
        } else {
            let (i, ref act_i) = rest[0];
            let index = store.act_store(act_i.clone());
            if index == 0 {
                fail_rec(cur_low, i, &rest[1..], high, store)
            } else {
                let mut r = vec![(cur_low, i - 1, 0)];
                r.extend(nofail_rec(i, i, index, &rest[1..], high, store));
                r
            }
        }
    }

    let intervals = if l.is_empty() {
        vec![(low, high, 0)]
    } else {
        let (i, ref act_i) = l[0];
        let index = store.act_store(act_i.clone());
        if index == 0 {
            fail_rec(low, i, &l[1..], high, &mut store)
        } else if low < i {
            let mut r = vec![(low, i - 1, 0)];
            r.extend(nofail_rec(i, i, index, &l[1..], high, &mut store));
            r
        } else {
            nofail_rec(i, i, index, &l[1..], high, &mut store)
        }
    };

    (intervals, store)
}

/// Convert a sorted int-lambda list (no fail action) into intervals.
/// Equivalent to OCaml's `as_interval_nofail`.
fn as_interval_nofail(l: &[(i32, RawLambda)]) -> (Vec<(i32, i32, usize)>, StoreExp) {
    let mut store = StoreExp::mk_store();

    fn some_hole(l: &[(i32, RawLambda)]) -> bool {
        if l.len() <= 1 {
            return false;
        }
        l.windows(2).any(|w| w[1].0 > w[0].0 + 1)
    }

    fn i_rec(
        cur_low: i32,
        cur_high: i32,
        cur_act: usize,
        rest: &[(i32, RawLambda)],
        store: &mut StoreExp,
    ) -> Vec<(i32, i32, usize)> {
        if rest.is_empty() {
            vec![(cur_low, cur_high, cur_act)]
        } else {
            let (i, ref act) = rest[0];
            let act_index = store.act_store(act.clone());
            if act_index == cur_act {
                i_rec(cur_low, i, cur_act, &rest[1..], store)
            } else {
                let mut r = vec![(cur_low, cur_high, cur_act)];
                r.extend(i_rec(i, i, act_index, &rest[1..], store));
                r
            }
        }
    }

    assert!(!l.is_empty());
    let (i, ref act) = l[0];
    let has_hole = some_hole(&l[1..]);
    let act_index = if has_hole {
        store.act_store_shared(act.clone())
    } else {
        store.act_store(act.clone())
    };
    assert_eq!(act_index, 0);
    let inters = i_rec(i, i, act_index, &l[1..], &mut store);

    (inters, store)
}

/// Sort an int-lambda list by key.
/// Equivalent to OCaml's `sort_int_lambda_list`.
fn sort_int_lambda_list(mut l: Vec<(i32, RawLambda)>) -> Vec<(i32, RawLambda)> {
    l.sort_by(|(i1, _), (i2, _)| i1.cmp(i2));
    l
}

/// Convert an int-lambda list into intervals for the switch compiler.
/// Equivalent to OCaml's `as_interval`.
fn as_interval(
    fail: Option<RawLambda>,
    low: i32,
    high: i32,
    l: Vec<(i32, RawLambda)>,
) -> ((i32, i32), (Vec<(i32, i32, usize)>, StoreExp)) {
    let l = sort_int_lambda_list(l);
    let edges = get_edges(low, high, &l);
    let result = match fail {
        None => as_interval_nofail(&l),
        Some(act) => as_interval_canfail(act, low, high, &l),
    };
    (edges, result)
}

/// Compile an integer switch using the switch module.
/// Equivalent to OCaml's `call_switcher`.
pub fn call_switcher(
    loc: Location,
    fail: Option<RawLambda>,
    arg: RawLambda,
    low: i32,
    high: i32,
    int_lambda_list: Vec<(i32, RawLambda)>,
    sw_names: Option<SwitchNames>,
    next_raise_count: &mut i32,
) -> RawLambda {
    let (edges, (cases, store)) = as_interval(fail, low, high, int_lambda_list);

    // Convert StoreExp to switch::ActionStore, preserving sharing info.
    // zyva will handle the shared action processing (abstract_shared).
    let acts = store.act_get_shared();
    let mut action_store = crate::raw_lambda::switch::ActionStore::new();
    for act in acts {
        match act {
            SharedAction::Single(a) => { action_store.act_store(a); }
            SharedAction::Shared(a) => { action_store.act_store_shared(a); }
        }
    }

    // Call the switch compiler — it handles shared actions internally via abstract_shared
    crate::raw_lambda::switch::zyva(
        edges,
        arg,
        &cases,
        &action_store,
        sw_names,
        &mut || {
            *next_raise_count += 1;
            *next_raise_count
        },
    )
}

// ============================================================================
// Layer 9: Combine functions — OCaml matching.ml lines 1945-2349
// ============================================================================

/// Construct a pattern by or-ing together a list of patterns.
/// Equivalent to OCaml's `list_as_pat`.
fn list_as_pat(pats: &[Pattern]) -> Pattern {
    match pats {
        [] => panic!("Matching.list_as_pat"),
        [pat] => pat.clone(),
        [pat, rest @ ..] => Pattern {
            pat_desc: PatternDesc::Tpat_or(
                Box::new(pat.clone()),
                Box::new(list_as_pat(rest)),
                None,
            ),
            ..pat.clone()
        },
    }
}

/// Complete the list of constructors not yet seen in the match.
/// Returns patterns for all constructors NOT in `pats`.
/// Equivalent to OCaml's `complete_pats_constrs`.
///
/// This requires environment lookups to get all constructors of a type.
/// We use a simplified approach: extract constructor info from the first pattern.
fn complete_pats_constrs(
    ctx_ref: &TypeContext<'_>,
    pats: &[Pattern],
) -> Vec<Pattern> {
    match pats.first() {
        None => panic!("complete_pats_constrs: empty list"),
        Some(p) => {
            let cstr = pat_as_constr(p);
            let all_tags: Vec<ConstructorTag> = pats.iter().map(|p| get_key_constr(p)).collect();

            // Build a set of seen tags
            let mut seen_const = vec![false; cstr.cstr_consts as usize];
            let mut seen_nonconst = vec![false; cstr.cstr_nonconsts as usize];
            for tag in &all_tags {
                match tag {
                    ConstructorTag::CstrConstant(i) => {
                        if (*i as usize) < seen_const.len() {
                            seen_const[*i as usize] = true;
                        }
                    }
                    ConstructorTag::CstrBlock(i) => {
                        if (*i as usize) < seen_nonconst.len() {
                            seen_nonconst[*i as usize] = true;
                        }
                    }
                    _ => {}
                }
            }

            // Get all constructors of the type from the environment
            let env_opt = ctx_ref.get_typed_env(p.pat_env);
            let all_constrs: Vec<ConstructorDescription> = if let Some(env) = env_opt {
                // Try to find the type declaration and its constructors
                match &cstr.cstr_res {
                    ty => {
                        // Try to expand the type and find its constructors
                        get_variant_constructors_from_env(ctx_ref, env.as_ref(), *ty)
                    }
                }
            } else {
                Vec::new()
            };

            if !all_constrs.is_empty() {
                // Filter to unseen constructors, preserving const before nonconst order
                let mut const_others = Vec::new();
                let mut nonconst_others = Vec::new();
                for cnstr in &all_constrs {
                    let is_unseen = match &cnstr.cstr_tag {
                        ConstructorTag::CstrConstant(i) => {
                            (*i as usize) < seen_const.len() && !seen_const[*i as usize]
                        }
                        ConstructorTag::CstrBlock(i) => {
                            (*i as usize) < seen_nonconst.len() && !seen_nonconst[*i as usize]
                        }
                        _ => false,
                    };
                    if is_unseen {
                        if cnstr.cstr_arity == 0 {
                            const_others.push(cnstr);
                        } else {
                            nonconst_others.push(cnstr);
                        }
                    }
                }

                // Build patterns: pat_of_constr for each unseen constructor
                let mut result = Vec::new();
                for cnstr in const_others.iter().chain(nonconst_others.iter()) {
                    result.push(pat_of_constr(p, cnstr));
                }
                result
            } else {
                // Type lookup failed — synthesize unseen constructors from the
                // cstr_consts/cstr_nonconsts counts and the seen tags.
                // This handles external module types (e.g., list from stdlib).
                let mut result = Vec::new();
                for i in 0..cstr.cstr_consts {
                    if (i as usize) < seen_const.len() && !seen_const[i as usize] {
                        let synth_cstr = ConstructorDescription {
                            cstr_name: String::new(),
                            cstr_tag: ConstructorTag::CstrConstant(i),
                            cstr_arity: 0,
                            cstr_consts: cstr.cstr_consts,
                            cstr_nonconsts: cstr.cstr_nonconsts,
                            ..cstr.clone()
                        };
                        result.push(pat_of_constr(p, &synth_cstr));
                    }
                }
                for i in 0..cstr.cstr_nonconsts {
                    if (i as usize) < seen_nonconst.len() && !seen_nonconst[i as usize] {
                        // Synthesize a non-constant constructor with arity 1
                        // (we don't know the real arity, but 1 is sufficient for
                        // the pattern to be recognized as non-constant)
                        let synth_cstr = ConstructorDescription {
                            cstr_name: String::new(),
                            cstr_tag: ConstructorTag::CstrBlock(i),
                            cstr_arity: 1,
                            cstr_consts: cstr.cstr_consts,
                            cstr_nonconsts: cstr.cstr_nonconsts,
                            ..cstr.clone()
                        };
                        result.push(pat_of_constr(p, &synth_cstr));
                    }
                }
                result
            }
        }
    }
}

/// Create a pattern from a constructor description, using the example pattern for type info.
/// Equivalent to OCaml's `pat_of_constr`.
fn pat_of_constr(ex_pat: &Pattern, cstr: &ConstructorDescription) -> Pattern {
    Pattern {
        pat_desc: PatternDesc::Tpat_construct(
            crate::parse_arena::Located {
                txt: crate::parse_arena::LidentIdx(0), // dummy
                loc: LocIdx::none(),
            },
            cstr.clone(),
            omegas(cstr.cstr_arity as usize),
        ),
        ..ex_pat.clone()
    }
}

/// Get variant constructors from the environment for a given result type.
/// Simplified version of OCaml's `get_variant_constructors`.
fn get_variant_constructors_from_env(
    ctx_ref: &TypeContext<'_>,
    _env: &crate::types::env::Env,
    result_type: TypeExprRef,
) -> Vec<ConstructorDescription> {
    use crate::types::type_expr::TypeDesc;

    // Expand the type to find the constructor path
    let ty = ctx_ref.repr(result_type);
    let desc = ctx_ref.get_desc(ty);
    match &*desc {
        TypeDesc::Tconstr { path, .. } => {
            let path_name = path.name();
            // Look up the type declaration
            if let Some(decl) = ctx_ref.find_type_decl_by_path(&path_name) {
                match &decl.type_kind {
                    crate::types::decl::TypeKind::TypeVariant(cds) => {
                        // Build constructor descriptions from the variant
                        let cstr_arity = |args: &crate::types::decl::ConstructorArguments| -> i32 {
                            match args {
                                crate::types::decl::ConstructorArguments::CstrTuple(v) => v.len() as i32,
                                crate::types::decl::ConstructorArguments::CstrRecord(v) => v.len() as i32,
                            }
                        };
                        let nconsts = cds.iter().filter(|cd| cstr_arity(&cd.cd_args) == 0).count() as i32;
                        let nnonconsts = cds.len() as i32 - nconsts;
                        let mut const_idx = 0i32;
                        let mut nonconst_idx = 0i32;
                        cds.iter()
                            .map(|cd| {
                                let arity = cstr_arity(&cd.cd_args);
                                let tag = if arity == 0 {
                                    let t = ConstructorTag::CstrConstant(const_idx);
                                    const_idx += 1;
                                    t
                                } else {
                                    let t = ConstructorTag::CstrBlock(nonconst_idx);
                                    nonconst_idx += 1;
                                    t
                                };
                                let args_vec = match &cd.cd_args {
                                    crate::types::decl::ConstructorArguments::CstrTuple(v) => v.clone(),
                                    crate::types::decl::ConstructorArguments::CstrRecord(v) => {
                                        v.iter().map(|ld| ld.ld_type).collect()
                                    }
                                };
                                ConstructorDescription {
                                    cstr_name: cd.cd_id.name().to_string(),
                                    cstr_res: result_type,
                                    cstr_existentials: Vec::new(),
                                    cstr_args: args_vec,
                                    cstr_arity: arity,
                                    cstr_tag: tag,
                                    cstr_consts: nconsts,
                                    cstr_nonconsts: nnonconsts,
                                    cstr_generalized: false,
                                    cstr_private: crate::types::asttypes::PrivateFlag::Public,
                                    cstr_loc: Location::none(),
                                    cstr_attributes: Vec::new(),
                                    cstr_inlined: None,
                                }
                            })
                            .collect()
                    }
                    _ => Vec::new(),
                }
            } else {
                Vec::new()
            }
        }
        _ => Vec::new(),
    }
}

/// Compute negative fail action (jump to default).
/// Returns (optional fail lambda, jumps).
/// Equivalent to OCaml's `mk_failaction_neg`.
fn mk_failaction_neg(
    partial: &Partial,
    ctx: &[Ctx],
    def: &DefaultEnv,
) -> (Option<RawLambda>, Jumps) {
    match partial {
        Partial::Partial => match def.first() {
            Some((_, idef)) => (
                Some(RawLambda::LstaticRaise(*idef, Vec::new())),
                jumps_singleton(*idef, ctx.to_vec()),
            ),
            None => {
                // Act as Total: if no default matrix exists, the switch cannot fail
                (None, jumps_empty())
            }
        },
        Partial::Total => (None, jumps_empty()),
    }
}

/// Compute positive fail action (enumerating missing constructors).
/// Returns (optional fail lambda, additional cases, jumps).
/// Equivalent to OCaml's `mk_failaction_pos`.
fn mk_failaction_pos(
    ctx_ref: &TypeContext<'_>,
    partial: &Partial,
    seen: &[Pattern],
    ctx: &[Ctx],
    defs: &DefaultEnv,
) -> (Option<RawLambda>, Vec<(ConstructorTag, RawLambda)>, Jumps) {
    let fail_pats = complete_pats_constrs(ctx_ref, seen);
    if fail_pats.len() < 32 {
        let to_test: Vec<(Pattern, Vec<Ctx>)> = fail_pats
            .iter()
            .map(|pat| (pat.clone(), ctx_lub(pat, ctx)))
            .collect();

        let (fail, jmps) = scan_def(ctx, Vec::new(), to_test, defs);
        (None, fail, jmps)
    } else {
        // Too many non-matched constructors -> reduced information
        let (fail, jumps) = mk_failaction_neg(partial, ctx, defs);
        (fail, Vec::new(), jumps)
    }
}

/// Scan default environment to build per-constructor fail actions.
/// Returns (key-action list, jumps).
/// Equivalent to OCaml's inner `scan_def` in `mk_failaction_pos`.
fn scan_def(
    ctx: &[Ctx],
    env: Vec<(Vec<Pattern>, i32)>,
    to_test: Vec<(Pattern, Vec<Ctx>)>,
    defs: &[(Matrix, i32)],
) -> (Vec<(ConstructorTag, RawLambda)>, Jumps) {
    if to_test.is_empty() || defs.is_empty() {
        // Fold env to build (klist, jumps)
        let mut klist: Vec<(ConstructorTag, RawLambda)> = Vec::new();
        let mut jumps = jumps_empty();
        for (pats, i) in env.iter().rev() {
            let action = RawLambda::LstaticRaise(*i, Vec::new());
            for pat in pats.iter().rev() {
                klist.insert(0, (get_key_constr(pat), action.clone()));
            }
            // OCaml: jumps_add i (ctx_lub (list_as_pat pats) ctx) jumps
            // Track the exit jump using the outer context.
            // We use ctx directly rather than ctx_lub to avoid context
            // shape issues (ctx_lub can produce empty right vectors
            // when the synthesized patterns don't match the context
            // structure, leading to panics in lshift).
            if !ctx.is_empty() {
                jumps = jumps_add(*i, ctx.to_vec(), jumps);
            }
        }
        (klist, jumps)
    } else {
        match defs.split_first() {
            None => scan_def(ctx, env, Vec::new(), &[]),
            Some(((pss, idef), rem)) => {
                let (now, later): (Vec<_>, Vec<_>) = to_test
                    .into_iter()
                    .partition(|(_, p_ctx)| ctx_match(p_ctx, pss));
                if now.is_empty() {
                    scan_def(ctx, env, later, rem)
                } else {
                    let pats: Vec<Pattern> = now.into_iter().map(|(p, _)| p).collect();
                    let mut new_env = vec![(pats, *idef)];
                    new_env.extend(env);
                    scan_def(ctx, new_env, later, rem)
                }
            }
        }
    }
}

/// Overloaded version of `same_actions` for tagged lists (ConstructorTag, lambda).
/// Checks if all actions in a case list are the same.
fn same_actions_tagged<K>(cases: &[(K, RawLambda)]) -> Option<RawLambda> {
    match cases {
        [] => None,
        [(_, act)] => Some(act.clone()),
        [(_, act0), rem @ ..] => {
            let raw_act0 = tr_raw(act0)?;
            let raw_act0_str = lambda_to_string(&raw_act0);
            for (_, act) in rem {
                let raw_act = tr_raw(act)?;
                if lambda_to_string(&raw_act) != raw_act0_str {
                    return None;
                }
            }
            Some(act0.clone())
        }
    }
}

/// Share actions for tree-based string matching.
/// Like share_actions_tree but for (String, RawLambda) pairs.
fn share_actions_tree_string(
    sw: Vec<(String, RawLambda)>,
    d: Option<RawLambda>,
    next_raise_count: &mut i32,
) -> (
    Box<dyn FnOnce(RawLambda) -> RawLambda>,
    Vec<(String, RawLambda)>,
    Option<RawLambda>,
) {
    let mut store = StoreExp::mk_store();

    let d_idx = match &d {
        None => None,
        Some(d) => Some(store.act_store_shared(d.clone())),
    };

    let sw_indices: Vec<(String, usize)> = sw
        .into_iter()
        .map(|(s, act)| (s, store.act_store(act)))
        .collect();

    let acts = store.act_get_shared();

    // Process shared actions — handle_shared
    let mut handlers: Vec<(i32, Box<dyn FnOnce(RawLambda) -> RawLambda>)> = Vec::new();
    let resolved_acts: Vec<RawLambda> = acts
        .into_iter()
        .map(|act| match act {
            SharedAction::Single(a) => a,
            SharedAction::Shared(a) => {
                let (i, h) = make_catch_delayed(a, next_raise_count);
                handlers.push((i, h));
                make_exit(i)
            }
        })
        .collect();

    let d = match d_idx {
        None => None,
        Some(idx) => Some(resolved_acts[idx].clone()),
    };
    let sw: Vec<(String, RawLambda)> = sw_indices
        .into_iter()
        .map(|(s, j)| (s, resolved_acts[j].clone()))
        .collect();

    // Build composed wrapper function
    let hs: Box<dyn FnOnce(RawLambda) -> RawLambda> = handlers.into_iter().fold(
        Box::new(|x: RawLambda| x) as Box<dyn FnOnce(RawLambda) -> RawLambda>,
        |ohs, (_, h)| {
            Box::new(move |act: RawLambda| h(ohs(act)))
        },
    );

    (hs, sw, d)
}

/// Combine constant matching results.
/// Equivalent to OCaml's `combine_constant`.
fn combine_constant(
    names: Option<SwitchNames>,
    loc: Location,
    arg: RawLambda,
    cst: &Constant,
    partial: &Partial,
    ctx: &[Ctx],
    def: &DefaultEnv,
    c_div: (Vec<(Constant, RawLambda)>, Jumps, Vec<Pattern>),
    next_raise_count: &mut i32,
) -> (RawLambda, Jumps) {
    let (const_lambda_list, total, _pats) = c_div;
    let (fail, local_jumps) = mk_failaction_neg(partial, ctx, def);
    let lambda1 = match cst {
        Constant::Int(_) => {
            let int_lambda_list: Vec<(i32, RawLambda)> = const_lambda_list
                .into_iter()
                .map(|(c, l)| match c {
                    Constant::Int(n) => (n as i32, l),
                    _ => panic!("combine_constant: expected Const_int"),
                })
                .collect();
            call_switcher(
                loc,
                fail,
                arg,
                i32::MIN,
                i32::MAX,
                int_lambda_list,
                names,
                next_raise_count,
            )
        }
        Constant::Char(_) => {
            let int_lambda_list: Vec<(i32, RawLambda)> = const_lambda_list
                .into_iter()
                .map(|(c, l)| match c {
                    Constant::Char(ch) => (ch as i32, l),
                    _ => panic!("combine_constant: expected Const_char"),
                })
                .collect();
            call_switcher(
                loc,
                fail,
                arg,
                0,
                i32::MAX,
                int_lambda_list,
                names,
                next_raise_count,
            )
        }
        Constant::String(_, _) => {
            let const_lambda_list = sort_lambda_list(const_lambda_list);
            let sw: Vec<(String, RawLambda)> = const_lambda_list
                .into_iter()
                .map(|(c, act)| match c {
                    Constant::String(s, _) => (s, act),
                    _ => panic!("combine_constant: expected Const_string"),
                })
                .collect();
            let (hs, sw, fail) = share_actions_tree_string(sw, fail, next_raise_count);
            hs(RawLambda::LstringSwitch(
                Box::new(arg),
                sw,
                fail.map(Box::new),
            ))
        }
        Constant::Float(_) => make_test_sequence(
            loc,
            fail,
            Primitive::Pfloatcomp(Comparison::Neq),
            Primitive::Pfloatcomp(Comparison::Lt),
            arg,
            const_lambda_list,
            next_raise_count,
        ),
        Constant::BigInt(_, _) => make_test_sequence(
            loc,
            fail,
            Primitive::Pbigintcomp(Comparison::Neq),
            Primitive::Pbigintcomp(Comparison::Lt),
            arg,
            const_lambda_list,
            next_raise_count,
        ),
    };
    (lambda1, jumps_union(&local_jumps, &total))
}

/// Split case list into constant and non-constant constructor cases.
/// Equivalent to OCaml's `split_cases`.
fn split_cases(
    tag_lambda_list: Vec<(ConstructorTag, RawLambda)>,
) -> (Vec<(i32, RawLambda)>, Vec<(i32, RawLambda)>) {
    let mut consts = Vec::new();
    let mut nonconsts = Vec::new();
    for (cstr, act) in tag_lambda_list {
        match cstr {
            ConstructorTag::CstrConstant(n) => consts.push((n, act)),
            ConstructorTag::CstrBlock(n) => nonconsts.push((n, act)),
            ConstructorTag::CstrUnboxed => nonconsts.push((0, act)),
            ConstructorTag::CstrExtension(_) => {
                // Extension constructors are handled by get_extension_cases,
                // not split_cases. If we reach here, skip them.
                continue;
            }
        }
    }
    consts.sort_by_key(|(i, _)| *i);
    nonconsts.sort_by_key(|(i, _)| *i);
    (consts, nonconsts)
}

/// Split variant case list into constant and non-constant.
/// Equivalent to OCaml's `split_variant_cases`.
fn split_variant_cases(
    tag_lambda_list: Vec<((String, ConstructorTag), RawLambda)>,
) -> (
    Vec<(i32, (String, RawLambda))>,
    Vec<(i32, (String, RawLambda))>,
) {
    let mut consts = Vec::new();
    let mut nonconsts = Vec::new();
    for ((name, cstr), act) in tag_lambda_list {
        match cstr {
            ConstructorTag::CstrConstant(n) => consts.push((n, (name, act))),
            ConstructorTag::CstrBlock(n) => nonconsts.push((n, (name, act))),
            ConstructorTag::CstrUnboxed => panic!("split_variant_cases: unboxed"),
            ConstructorTag::CstrExtension(_) => panic!("split_variant_cases: extension"),
        }
    }
    consts.sort_by_key(|(i, _)| *i);
    nonconsts.sort_by_key(|(i, _)| *i);
    (consts, nonconsts)
}

/// Get extension constructor cases.
/// Equivalent to OCaml's `get_extension_cases`.
fn get_extension_cases(
    tag_lambda_list: Vec<(ConstructorTag, RawLambda)>,
) -> Vec<(crate::types::path::Path, RawLambda)> {
    tag_lambda_list
        .into_iter()
        .map(|(cstr, act)| match cstr {
            ConstructorTag::CstrExtension(path) => (path, act),
            _ => panic!("get_extension_cases: not an extension constructor"),
        })
        .collect()
}

/// Translate a path to a RawLambda access expression.
/// Equivalent to OCaml's `transl_normal_path`.
fn transl_normal_path(path: &crate::types::path::Path) -> RawLambda {
    use crate::types::path::Path;
    match path {
        Path::Pident(id) => {
            if id.is_global() {
                RawLambda::LglobalModule(id.clone(), false)
            } else {
                RawLambda::Lvar(id.clone())
            }
        }
        Path::Pdot(p, s, pos) => RawLambda::Lprim(RawPrimInfo {
            primitive: Primitive::Pfield(
                *pos,
                FieldDbgInfo::Module { name: s.clone() },
            ),
            args: vec![transl_normal_path(p)],
            loc: Location::none(),
        }),
        Path::Papply(_, _) => panic!("transl_normal_path: Papply"),
    }
}

/// Translate an extension path to a RawLambda.
/// Equivalent to OCaml's `transl_extension_path`.
fn transl_extension_path(
    ctx_ref: &TypeContext<'_>,
    env: EnvRef,
    path: &crate::types::path::Path,
) -> RawLambda {
    // OCaml: transl_extension_path = transl_value_path = fun env path ->
    //   transl_normal_path (Env.normalize_path_prefix env path)
    if let Some(typed_env) = ctx_ref.get_typed_env(env) {
        let normalized = typed_env.normalize_path_prefix(path);
        transl_normal_path(&normalized)
    } else {
        transl_normal_path(path)
    }
}

/// Combine constructor matching results.
/// Equivalent to OCaml's `combine_constructor`.
fn combine_constructor(
    ctx_ref: &TypeContext<'_>,
    sw_names: Option<SwitchNames>,
    loc: Location,
    arg: RawLambda,
    ex_pat: &Pattern,
    cstr: &ConstructorDescription,
    partial: &Partial,
    ctx: &[Ctx],
    def: &DefaultEnv,
    c_div: (Vec<(ConstructorTag, RawLambda)>, Jumps, Vec<Pattern>),
    next_raise_count: &mut i32,
) -> (RawLambda, Jumps) {
    let (tag_lambda_list, total1, pats) = c_div;

    if cstr.cstr_consts < 0 {
        // Special cases for extensions
        let (fail, local_jumps) = mk_failaction_neg(partial, ctx, def);
        let lambda1 = {
            let extension_cases = get_extension_cases(tag_lambda_list);
            let (default, extension_cases) = match fail {
                None => match extension_cases.split_first() {
                    Some(((_, act), rem)) => (act.clone(), rem.to_vec()),
                    None => panic!("combine_constructor: no extension cases"),
                },
                Some(fail) => (fail, extension_cases),
            };
            if extension_cases.is_empty() {
                default
            } else {
                let tag = Ident::create_local("tag");
                let tests = extension_cases.iter().rev().fold(default, |rem, (path, act)| {
                    let ext = transl_extension_path(ctx_ref, ex_pat.pat_env, path);
                    RawLambda::LifThenElse(
                        Box::new(RawLambda::Lprim(RawPrimInfo {
                            primitive: Primitive::PextensionSlotEq,
                            args: vec![RawLambda::Lvar(tag.clone()), ext],
                            loc: loc.clone(),
                        })),
                        Box::new(act.clone()),
                        Box::new(rem),
                    )
                });
                RawLambda::Llet(
                    LetKind::Alias,
                    tag,
                    Box::new(arg),
                    Box::new(tests),
                )
            }
        };
        (lambda1, jumps_union(&local_jumps, &total1))
    } else {
        // Regular concrete type
        let ncases = tag_lambda_list.len() as i32;
        let nconstrs = cstr.cstr_consts + cstr.cstr_nonconsts;
        let sig_complete = ncases == nconstrs;
        let (fail_opt, fails, local_jumps) = if sig_complete {
            (None, Vec::new(), jumps_empty())
        } else {
            mk_failaction_pos(ctx_ref, partial, &pats, ctx, def)
        };

        let mut tag_lambda_list = tag_lambda_list;
        // Prepend fails to tag_lambda_list
        let mut combined = fails;
        combined.extend(tag_lambda_list);
        tag_lambda_list = combined;

        let (consts, nonconsts) = split_cases(tag_lambda_list.clone());
        let lambda1 = match (&fail_opt, same_actions_tagged(&tag_lambda_list)) {
            (None, Some(act)) => act, // Identical actions, no failure
            _ => {
                match (
                    cstr.cstr_consts,
                    cstr.cstr_nonconsts,
                    consts.as_slice(),
                    nonconsts.as_slice(),
                ) {
                    (1, 1, [(0, act1)], [(0, act2)])
                        if cstr.cstr_name == "::"
                            || cstr.cstr_name == "[]"
                            || constructor_has_optional_shape(cstr)
                            || (cstr.cstr_name == "Some" && cstr.cstr_consts == 1 && cstr.cstr_nonconsts == 1) =>
                    {
                        // Typically, match on lists or options
                        let is_option = constructor_has_optional_shape(cstr)
                            || (cstr.cstr_name == "Some" && cstr.cstr_consts == 1 && cstr.cstr_nonconsts == 1);
                        let test_arg = if is_option {
                            RawLambda::Lprim(RawPrimInfo {
                                primitive: Primitive::PisNotNone,
                                args: vec![arg.clone()],
                                loc: loc.clone(),
                            })
                        } else {
                            RawLambda::Lprim(RawPrimInfo {
                                primitive: Primitive::Pjscomp(Comparison::Neq),
                                args: vec![
                                    arg.clone(),
                                    RawLambda::Lconst(crate::lambda::Constant::int(0)),
                                ],
                                loc: loc.clone(),
                            })
                        };
                        RawLambda::LifThenElse(
                            Box::new(test_arg),
                            Box::new(act2.clone()),
                            Box::new(act1.clone()),
                        )
                    }
                    (2, 0, [(i1, act1), (_, act2)], [])
                        if cstr.cstr_name == "true" || cstr.cstr_name == "false" =>
                    {
                        if *i1 == 0 {
                            RawLambda::LifThenElse(
                                Box::new(arg),
                                Box::new(act2.clone()),
                                Box::new(act1.clone()),
                            )
                        } else {
                            RawLambda::LifThenElse(
                                Box::new(arg),
                                Box::new(act1.clone()),
                                Box::new(act2.clone()),
                            )
                        }
                    }
                    (_n, _, _, _) => {
                        let act0 = match (&fail_opt, nonconsts.as_slice()) {
                            (Some(a), []) => Some(a.clone()),
                            (Some(_), _) => {
                                if nonconsts.len() == cstr.cstr_nonconsts as usize {
                                    same_actions_tagged(&nonconsts)
                                } else {
                                    None
                                }
                            }
                            (None, _) => same_actions_tagged(&nonconsts),
                        };
                        // Emit a switch
                        let _ = act0; // OCaml has dead code paths here (false guards)
                        let sw = RawLambdaSwitch {
                            sw_consts_full: false,
                            sw_consts: consts,
                            sw_blocks_full: false,
                            sw_blocks: nonconsts,
                            sw_failaction: fail_opt.map(Box::new),
                            sw_names,
                        };
                        let (handlers, sw) = share_actions_sw(sw, next_raise_count);
                        let sw = reintroduce_fail(sw);
                        let result = RawLambda::Lswitch(Box::new(arg), sw);
                        apply_handlers(result, handlers)
                    }
                }
            }
        };
        (lambda1, jumps_union(&local_jumps, &total1))
    }
}

/// Convert a polyvar int_lambda_list by grouping entries with the same action.
/// Equivalent to OCaml's `Polyvar_pattern_match.convert`.
///
/// Groups entries that have the same lambda action together, producing a list
/// of `(hash_names, action)` pairs sorted by first occurrence (stamp).
fn convert_polyvar_list(xs: &[(i32, (String, RawLambda))]) -> Vec<(Vec<(i32, String)>, RawLambda)> {
    // Group by action equality using string-based comparison (like OCaml's make_key).
    // Each entry gets a stamp (its original index) for stable sorting.
    struct Entry {
        stamp: usize,
        hash_names: Vec<(i32, String)>,
        act: RawLambda,
        key: Option<String>,
    }

    let mut entries: Vec<Entry> = Vec::new();

    for (i, (hash, (name, act))) in xs.iter().enumerate() {
        // Use debug format as a key for structural comparison
        let key = format!("{:?}", act);
        // Try to find an existing entry with the same action key
        let found_idx = entries.iter().position(|e| {
            match (&e.key, &key) {
                (Some(k1), k2) => k1 == k2,
                _ => false,
            }
        });
        if let Some(idx) = found_idx {
            entries[idx].hash_names.push((*hash, name.clone()));
        } else {
            entries.push(Entry {
                stamp: i,
                hash_names: vec![(*hash, name.clone())],
                act: act.clone(),
                key: Some(key),
            });
        }
    }

    entries.sort_by_key(|e| e.stamp);
    entries.into_iter().map(|e| (e.hash_names, e.act)).collect()
}

/// Create a disjunction of equality tests for polyvar hash values.
/// Equivalent to OCaml's `Polyvar_pattern_match.or_list`.
fn or_list_polyvar(arg: &RawLambda, hash_names: &[(i32, String)]) -> RawLambda {
    let (first_hash, first_name) = &hash_names[0];
    let init = RawLambda::Lprim(RawPrimInfo {
        primitive: Primitive::Pintcomp(Comparison::Eq),
        args: vec![
            arg.clone(),
            RawLambda::Lconst(crate::lambda::constant::Constant::Pointer(format!("{}a", first_hash))),
        ],
        loc: Location::none(),
    });
    hash_names[1..].iter().fold(init, |acc, (hash, _name)| {
        RawLambda::Lprim(RawPrimInfo {
            primitive: Primitive::Psequor,
            args: vec![
                acc,
                RawLambda::Lprim(RawPrimInfo {
                    primitive: Primitive::Pintcomp(Comparison::Eq),
                    args: vec![
                        arg.clone(),
                        RawLambda::Lconst(crate::lambda::constant::Constant::Pointer(format!("{}a", hash))),
                    ],
                    loc: Location::none(),
                }),
            ],
            loc: Location::none(),
        })
    })
}

/// Build an if-chain from converted polyvar list.
/// Used by both make_test_sequence_variant_constant and call_switcher_variant_constant.
fn polyvar_if_chain(
    fail: Option<RawLambda>,
    arg: &RawLambda,
    int_lambda_list: &[(i32, (String, RawLambda))],
) -> RawLambda {
    let converted = convert_polyvar_list(int_lambda_list);
    match (converted.split_first(), &fail) {
        (Some(((_, default_act), rest)), &None) => {
            // No fail: first action is default, rest are if-then-else
            rest.iter().rev().fold(default_act.clone(), |acc, (hash_names, act)| {
                let predicate = or_list_polyvar(arg, hash_names);
                RawLambda::LifThenElse(Box::new(predicate), Box::new(act.clone()), Box::new(acc))
            })
        }
        (_, &Some(ref fail_act)) => {
            // With fail: fail is default, all entries are if-then-else
            converted.iter().rev().fold(fail_act.clone(), |acc, (hash_names, act)| {
                let predicate = or_list_polyvar(arg, hash_names);
                RawLambda::LifThenElse(Box::new(predicate), Box::new(act.clone()), Box::new(acc))
            })
        }
        (None, &None) => panic!("polyvar_if_chain: empty list with no fail"),
    }
}

/// Make a test sequence for variant constant matching.
/// Equivalent to OCaml's `Polyvar_pattern_match.make_test_sequence_variant_constant`.
fn make_test_sequence_variant_constant(
    fail: Option<RawLambda>,
    arg: RawLambda,
    int_lambda_list: &[(i32, (String, RawLambda))],
    _next_raise_count: &mut i32,
) -> RawLambda {
    polyvar_if_chain(fail, &arg, int_lambda_list)
}

/// Call switcher for variant constant matching.
/// Equivalent to OCaml's `Polyvar_pattern_match.call_switcher_variant_constant`.
fn call_switcher_variant_constant(
    _loc: Location,
    fail: Option<RawLambda>,
    arg: RawLambda,
    int_lambda_list: &[(i32, (String, RawLambda))],
    _names: Option<SwitchNames>,
    _next_raise_count: &mut i32,
) -> RawLambda {
    polyvar_if_chain(fail, &arg, int_lambda_list)
}

/// Call switcher for variant non-constant (block) matching.
/// Equivalent to OCaml's `Polyvar_pattern_match.call_switcher_variant_constr`.
fn call_switcher_variant_constr(
    loc: Location,
    fail: Option<RawLambda>,
    arg: RawLambda,
    int_lambda_list: &[(i32, (String, RawLambda))],
    names: Option<SwitchNames>,
    next_raise_count: &mut i32,
) -> RawLambda {
    let v = Ident::create_local("variant");
    RawLambda::Llet(
        LetKind::Alias,
        v.clone(),
        Box::new(RawLambda::Lprim(RawPrimInfo {
            primitive: Primitive::Pfield(0, FieldDbgInfo::PolyVarTag),
            args: vec![arg],
            loc: loc.clone(),
        })),
        Box::new(call_switcher_variant_constant(
            loc,
            fail,
            RawLambda::Lvar(v),
            int_lambda_list,
            names,
            next_raise_count,
        )),
    )
}

/// Combine variant matching results.
/// Equivalent to OCaml's `combine_variant`.
fn combine_variant(
    ctx_ref: &TypeContext<'_>,
    names: Option<SwitchNames>,
    loc: Location,
    row: &RowDesc,
    arg: RawLambda,
    partial: &Partial,
    ctx: &[Ctx],
    def: &DefaultEnv,
    c_div: (Vec<((String, ConstructorTag), RawLambda)>, Jumps, Vec<Pattern>),
    next_raise_count: &mut i32,
) -> (RawLambda, Jumps) {
    let (tag_lambda_list, total1, _pats) = c_div;
    let row = btype::row_repr(ctx_ref, row);
    let mut num_constr: usize = 0;
    if row.row_closed {
        for (_, f) in &row.row_fields {
            match btype::row_field_repr(ctx_ref, f) {
                RowField::Rabsent => {}
                RowField::Reither { constant: true, ref types, .. } if !types.is_empty() => {}
                _ => num_constr += 1,
            }
        }
    } else {
        num_constr = usize::MAX;
    }

    let test_int_or_block = |arg: RawLambda, if_int: RawLambda, if_block: RawLambda| -> RawLambda {
        RawLambda::LifThenElse(
            Box::new(RawLambda::Lprim(RawPrimInfo {
                primitive: Primitive::PisPolyVarBlock,
                args: vec![arg],
                loc: loc.clone(),
            })),
            Box::new(if_block),
            Box::new(if_int),
        )
    };

    let sig_complete = tag_lambda_list.len() == num_constr;
    let one_action = same_actions_tagged(&tag_lambda_list);

    let (fail, local_jumps) = if sig_complete
        || matches!(partial, Partial::Total)
    {
        (None, jumps_empty())
    } else {
        mk_failaction_neg(partial, ctx, def)
    };

    let (consts, nonconsts) = split_variant_cases(tag_lambda_list);
    let lambda1 = match (&fail, &one_action) {
        (None, Some(act)) => act.clone(),
        _ => match (consts.as_slice(), nonconsts.as_slice()) {
            ([(_, (_, act1))], [(_, (_, act2))]) if fail.is_none() => {
                test_int_or_block(arg, act1.clone(), act2.clone())
            }
            (_, []) => {
                // One can compare integers and pointers
                make_test_sequence_variant_constant(
                    fail,
                    arg,
                    &consts,
                    next_raise_count,
                )
            }
            ([], _) => {
                let lam = call_switcher_variant_constr(
                    loc.clone(),
                    fail.clone(),
                    arg.clone(),
                    &nonconsts,
                    names,
                    next_raise_count,
                );
                // One must not dereference integers
                match fail {
                    None => lam,
                    Some(fail) => test_int_or_block(arg, fail, lam),
                }
            }
            _ => {
                let lam_const = call_switcher_variant_constant(
                    loc.clone(),
                    fail.clone(),
                    arg.clone(),
                    &consts,
                    names.clone(),
                    next_raise_count,
                );
                let lam_nonconst = call_switcher_variant_constr(
                    loc.clone(),
                    fail,
                    arg.clone(),
                    &nonconsts,
                    names,
                    next_raise_count,
                );
                test_int_or_block(arg, lam_const, lam_nonconst)
            }
        },
    };
    (lambda1, jumps_union(&local_jumps, &total1))
}

/// Combine array matching results.
/// Equivalent to OCaml's `combine_array`.
fn combine_array(
    names: Option<SwitchNames>,
    loc: Location,
    arg: RawLambda,
    partial: &Partial,
    ctx: &[Ctx],
    def: &DefaultEnv,
    c_div: (Vec<(usize, RawLambda)>, Jumps, Vec<Pattern>),
    next_raise_count: &mut i32,
) -> (RawLambda, Jumps) {
    let (len_lambda_list, total1, _pats) = c_div;
    let (fail, local_jumps) = mk_failaction_neg(partial, ctx, def);
    let lambda1 = {
        let newvar = Ident::create_local("len");
        let int_lambda_list: Vec<(i32, RawLambda)> = len_lambda_list
            .into_iter()
            .map(|(len, act)| (len as i32, act))
            .collect();
        let switch_result = call_switcher(
            loc.clone(),
            fail,
            RawLambda::Lvar(newvar.clone()),
            0,
            i32::MAX,
            int_lambda_list,
            names,
            next_raise_count,
        );
        bind(
            LetKind::Alias,
            &newvar,
            &RawLambda::Lprim(RawPrimInfo {
                primitive: Primitive::Parraylength,
                args: vec![arg],
                loc,
            }),
            switch_result,
        )
    };
    (lambda1, jumps_union(&local_jumps, &total1))
}

// ============================================================================
// Layer 10: Compile functions — OCaml matching.ml lines 2351-2606
// ============================================================================

/// Exception raised when all cases in a compile are unreachable.
/// Equivalent to OCaml's `Unused` exception.
#[derive(Debug)]
struct Unused;

/// Compile a list of divided cells.
/// Returns (key-action list, total jumps, pattern list).
/// Equivalent to OCaml's `compile_list`.
fn compile_list<K: Clone>(
    compile_fun: &mut dyn FnMut(&[Ctx], &PatternMatching) -> Result<(RawLambda, Jumps), Unused>,
    division: Vec<(K, MatchCell)>,
) -> Result<(Vec<(K, RawLambda)>, Jumps, Vec<Pattern>), Unused> {
    let mut result_list: Vec<(K, RawLambda)> = Vec::new();
    let mut totals: Vec<Jumps> = Vec::new();
    let mut new_pats: Vec<Pattern> = Vec::new();

    for (key, cell) in division {
        if cell.ctx.is_empty() {
            continue;
        }
        match compile_fun(&cell.ctx, &cell.pm) {
            Ok((lambda1, total1)) => {
                result_list.push((key, lambda1));
                totals.push(jumps_map(|c| ctx_combine(&c), &total1));
                new_pats.push(cell.pat);
            }
            Err(Unused) => {
                // Skip unused cases
            }
        }
    }

    let total = jumps_unions(totals);
    Ok((result_list, total, new_pats))
}

/// Compile or-pattern handlers.
/// Equivalent to OCaml's `compile_orhandlers`.
fn compile_orhandlers(
    compile_fun: &mut dyn FnMut(&[Ctx], &PatternMatching) -> Result<(RawLambda, Jumps), Unused>,
    lambda1: RawLambda,
    total1: Jumps,
    ctx: &[Ctx],
    to_catch: Vec<(Matrix, i32, Vec<Ident>, PatternMatching)>,
) -> (RawLambda, Jumps) {
    let mut r = lambda1;
    let mut total_r = total1;

    for (mat, i, vars, pm) in to_catch {
        let ctx_i = select_columns(&mat, ctx);
        match compile_fun(&ctx_i, &pm) {
            Ok((handler_i, total_i)) => {
                match &raw_action(&r) {
                    RawLambda::LstaticRaise(j, args) if *j == i => {
                        // Direct substitution
                        r = vars
                            .iter()
                            .zip(args.iter())
                            .rev()
                            .fold(handler_i, |body, (var, arg)| {
                                bind(LetKind::Alias, var, arg, body)
                            });
                        total_r = jumps_map(
                            |c| ctx_rshift_num(ncols(&mat), &c),
                            &total_i,
                        );
                    }
                    _ => {
                        r = RawLambda::LstaticCatch(
                            Box::new(r),
                            (i, vars),
                            Box::new(handler_i),
                        );
                        total_r = jumps_union(
                            &jumps_remove(i, &total_r),
                            &jumps_map(
                                |c| ctx_rshift_num(ncols(&mat), &c),
                                &total_i,
                            ),
                        );
                    }
                }
            }
            Err(Unused) => {
                r = RawLambda::LstaticCatch(
                    Box::new(r),
                    (i, vars),
                    Box::new(lambda_unit()),
                );
            }
        }
    }

    (r, total_r)
}

/// Compile a test (divide + combine pattern).
/// Equivalent to OCaml's `compile_test`.
fn compile_test<K: Clone>(
    compile_fun: &mut dyn FnMut(&[Ctx], &PatternMatching) -> Result<(RawLambda, Jumps), Unused>,
    partial: &Partial,
    divide_fn: &dyn Fn(&[Ctx], &PatternMatching) -> Vec<(K, MatchCell)>,
    combine_fn: &mut dyn FnMut(&[Ctx], &DefaultEnv, (Vec<(K, RawLambda)>, Jumps, Vec<Pattern>)) -> (RawLambda, Jumps),
    ctx: &[Ctx],
    to_match: &PatternMatching,
) -> Result<(RawLambda, Jumps), Unused> {
    let division = divide_fn(ctx, to_match);
    let c_div = compile_list(compile_fun, division)?;
    match &c_div {
        (list, _, _) if list.is_empty() => {
            match mk_failaction_neg(partial, ctx, &to_match.default) {
                (None, _) => Err(Unused),
                (Some(l), total) => Ok((l, total)),
            }
        }
        _ => Ok(combine_fn(ctx, &to_match.default, c_div)),
    }
}

/// Check if v approximately appears in lam.
/// Equivalent to OCaml's `approx_present`.
fn approx_present(v: &Ident, lam: &RawLambda) -> bool {
    match lam {
        RawLambda::Lconst(_) => false,
        RawLambda::LstaticRaise(_, args) => args.iter().any(|a| approx_present(v, a)),
        RawLambda::Lprim(info) => info.args.iter().any(|a| approx_present(v, a)),
        RawLambda::Llet(LetKind::Alias, _, l1, l2) => {
            approx_present(v, l1) || approx_present(v, l2)
        }
        RawLambda::Lvar(vv) => v.same(vv),
        _ => true,
    }
}

/// Lower a binding into the appropriate branch.
/// Equivalent to OCaml's `lower_bind`.
fn lower_bind(v: &Ident, arg: &RawLambda, lam: RawLambda) -> RawLambda {
    match &lam {
        RawLambda::LifThenElse(cond, ifso, ifnot) => {
            let pcond = approx_present(v, cond);
            let pso = approx_present(v, ifso);
            let pnot = approx_present(v, ifnot);
            match (pcond, pso, pnot) {
                (false, false, false) => lam,
                (false, true, false) => RawLambda::LifThenElse(
                    cond.clone(),
                    Box::new(lower_bind(v, arg, (**ifso).clone())),
                    ifnot.clone(),
                ),
                (false, false, true) => RawLambda::LifThenElse(
                    cond.clone(),
                    ifso.clone(),
                    Box::new(lower_bind(v, arg, (**ifnot).clone())),
                ),
                _ => bind(LetKind::Alias, v, arg, lam),
            }
        }
        RawLambda::Lswitch(ls, sw) if sw.sw_consts.len() == 1 && sw.sw_blocks.is_empty() && !approx_present(v, ls) => {
            let (i, act) = &sw.sw_consts[0];
            let new_act = lower_bind(v, arg, act.clone());
            RawLambda::Lswitch(
                ls.clone(),
                RawLambdaSwitch {
                    sw_consts: vec![(*i, new_act)],
                    ..(*sw).clone()
                },
            )
        }
        RawLambda::Lswitch(ls, sw) if sw.sw_consts.is_empty() && sw.sw_blocks.len() == 1 && !approx_present(v, ls) => {
            let (i, act) = &sw.sw_blocks[0];
            let new_act = lower_bind(v, arg, act.clone());
            RawLambda::Lswitch(
                ls.clone(),
                RawLambdaSwitch {
                    sw_blocks: vec![(*i, new_act)],
                    ..(*sw).clone()
                },
            )
        }
        RawLambda::Llet(LetKind::Alias, vv, lv, l) => {
            if approx_present(v, lv) {
                bind(LetKind::Alias, v, arg, lam)
            } else {
                RawLambda::Llet(
                    LetKind::Alias,
                    vv.clone(),
                    lv.clone(),
                    Box::new(lower_bind(v, arg, (**l).clone())),
                )
            }
        }
        RawLambda::Lvar(u) if u.same(v) && u.name() == "*sth*" => {
            arg.clone() // eliminate let *sth* = from_option x in *sth*
        }
        _ => bind(LetKind::Alias, v, arg, lam),
    }
}

/// Bind with check — try to lower alias bindings.
/// Equivalent to OCaml's `bind_check`.
fn bind_check(str_kind: LetKind, v: &Ident, arg: &RawLambda, lam: RawLambda) -> RawLambda {
    match (&str_kind, arg) {
        (_, RawLambda::Lvar(_)) => bind(str_kind, v, arg, lam),
        (LetKind::Alias, _) => lower_bind(v, arg, lam),
        _ => bind(str_kind, v, arg, lam),
    }
}

/// Compile the default/exit case.
/// Equivalent to OCaml's `comp_exit`.
fn comp_exit(ctx: &[Ctx], m: &PatternMatching) -> Result<(RawLambda, Jumps), Unused> {
    match m.default.first() {
        Some((_, i)) => Ok((
            RawLambda::LstaticRaise(*i, Vec::new()),
            jumps_singleton(*i, ctx.to_vec()),
        )),
        None => panic!("Matching.comp_exit"),
    }
}

/// Compile a match with multiple handlers (for split results).
/// Equivalent to OCaml's `comp_match_handlers`.
fn comp_match_handlers(
    comp_fun: &mut dyn FnMut(&Partial, &[Ctx], &RawLambda, &PmHalfCompiled) -> Result<(RawLambda, Jumps), Unused>,
    partial: &Partial,
    ctx: &[Ctx],
    arg: &RawLambda,
    first_match: PmHalfCompiled,
    next_matchs: Vec<(i32, PmHalfCompiled)>,
) -> Result<(RawLambda, Jumps), Unused> {
    if next_matchs.is_empty() {
        return comp_fun(partial, ctx, arg, &first_match);
    }

    match comp_fun(&Partial::Partial, ctx, arg, &first_match) {
        Ok((first_lam, total)) => {
            c_rec(comp_fun, partial, ctx, arg, first_lam, total, &next_matchs)
        }
        Err(Unused) => {
            match next_matchs.split_first() {
                None => Err(Unused),
                Some(((_, x), xs)) => {
                    comp_match_handlers(comp_fun, partial, ctx, arg, x.clone(), xs.to_vec())
                }
            }
        }
    }
}

/// Inner recursive function for comp_match_handlers.
fn c_rec(
    comp_fun: &mut dyn FnMut(&Partial, &[Ctx], &RawLambda, &PmHalfCompiled) -> Result<(RawLambda, Jumps), Unused>,
    partial: &Partial,
    ctx: &[Ctx],
    arg: &RawLambda,
    body: RawLambda,
    total_body: Jumps,
    rest: &[(i32, PmHalfCompiled)],
) -> Result<(RawLambda, Jumps), Unused> {
    match rest.split_first() {
        None => Ok((body, total_body)),
        Some(((i, pm), rem)) => {
            let (ctx_i, total_rem) = jumps_extract(*i, &total_body);
            if ctx_i.is_empty() {
                c_rec(comp_fun, partial, ctx, arg, body, total_body, rem)
            } else {
                let this_partial = if rem.is_empty() { partial.clone() } else { Partial::Partial };
                match comp_fun(&this_partial, &ctx_i, arg, pm) {
                    Ok((li, total_i)) => c_rec(
                        comp_fun,
                        partial,
                        ctx,
                        arg,
                        RawLambda::LstaticCatch(
                            Box::new(body),
                            (*i, Vec::new()),
                            Box::new(li),
                        ),
                        jumps_union(&total_i, &total_rem),
                        rem,
                    ),
                    Err(Unused) => c_rec(
                        comp_fun,
                        partial,
                        ctx,
                        arg,
                        RawLambda::LstaticCatch(
                            Box::new(body),
                            (*i, Vec::new()),
                            Box::new(lambda_unit()),
                        ),
                        total_rem,
                        rem,
                    ),
                }
            }
        }
    }
}

/// Find a reasonable name for the match variable from the first pattern.
/// Equivalent to OCaml's `name_pattern`.
fn name_pattern(default: &str, cases: &[(Vec<Pattern>, RawLambda)]) -> Ident {
    for (pats, _) in cases {
        if let Some(pat) = pats.first() {
            if let Some(id) = id_of_pattern(pat) {
                return id;
            }
        }
    }
    Ident::create_local(default)
}

/// Extract an identifier from a pattern (for naming purposes).
/// Equivalent to OCaml's `Typecore.id_of_pattern`.
fn id_of_pattern(pat: &Pattern) -> Option<Ident> {
    match &pat.pat_desc {
        PatternDesc::Tpat_var(id, _) => Some(id.clone()),
        PatternDesc::Tpat_alias(_, id, _) => Some(id.clone()),
        PatternDesc::Tpat_construct(_, _, args) if args.len() == 1 => {
            match &args[0].pat_desc {
                PatternDesc::Tpat_var(id, _) | PatternDesc::Tpat_alias(_, id, _) => {
                    Some(Ident::create_local(id.name()))
                }
                _ => None,
            }
        }
        _ => None,
    }
}

/// Convert arg to a variable (bind if not already a variable).
/// Equivalent to OCaml's `arg_to_var`.
fn arg_to_var(arg: &RawLambda, cls: &[(Vec<Pattern>, RawLambda)]) -> (Ident, RawLambda) {
    match arg {
        RawLambda::Lvar(v) => (v.clone(), arg.clone()),
        _ => {
            let v = name_pattern("match", cls);
            (v.clone(), RawLambda::Lvar(v))
        }
    }
}

/// Lambda unit value.
/// Equivalent to OCaml's `Lambda.lambda_unit`.
fn lambda_unit() -> RawLambda {
    RawLambda::Lconst(crate::lambda::Constant::JsUndefined { is_unit: true })
}

/// Patch a guarded action: replace the guard's static raise(0,[]) with the patch lambda.
/// Equivalent to OCaml's `Lambda.patch_guarded`.
fn patch_guarded(patch: RawLambda, lam: &RawLambda) -> RawLambda {
    match lam {
        RawLambda::LifThenElse(cond, body, else_br) => {
            match else_br.as_ref() {
                RawLambda::LstaticRaise(0, args) if args.is_empty() => {
                    RawLambda::LifThenElse(cond.clone(), body.clone(), Box::new(patch))
                }
                _ => panic!("patch_guarded: unexpected else branch"),
            }
        }
        RawLambda::Llet(kind, id, lam_inner, body) => RawLambda::Llet(
            *kind,
            id.clone(),
            lam_inner.clone(),
            Box::new(patch_guarded(patch, body)),
        ),
        _ => panic!("patch_guarded: unexpected lambda"),
    }
}

/// The main compilation function.
/// Input:
///   repr=used for inserting debug events (unused in ReScript)
///   partial=exhaustiveness information
///   ctx=a context
///   m=a pattern matching
/// Output: a lambda term, a jump summary
///
/// Equivalent to OCaml's `compile_match`.
fn compile_match(
    ctx_ref: &TypeContext<'_>,
    _repr: Option<()>,
    partial: &Partial,
    ctx: &[Ctx],
    m: &PatternMatching,
    next_raise_count: &mut i32,
) -> Result<(RawLambda, Jumps), Unused> {
    match (m.cases.as_slice(), m.args.as_slice()) {
        ([], []) => comp_exit(ctx, m),
        ([(pats, action), rem @ ..], _) if pats.is_empty() => {
            if is_guarded(action) {
                let remaining = PatternMatching {
                    cases: rem.to_vec(),
                    args: m.args.clone(),
                    default: m.default.clone(),
                };
                let (lambda, total) = compile_match(ctx_ref, None, partial, ctx, &remaining, next_raise_count)?;
                Ok((patch_guarded(lambda, action), total))
            } else {
                Ok((action.clone(), jumps_empty()))
            }
        }
        (_, [(arg, str_kind), argl @ ..]) => {
            let (v, newarg) = arg_to_var(arg, &m.cases);
            let new_args = {
                let mut a = vec![(newarg.clone(), LetKind::Alias)];
                a.extend(argl.iter().cloned());
                a
            };
            let new_pm = PatternMatching {
                cases: m.cases.clone(),
                args: new_args,
                default: m.default.clone(),
            };
            let (first_match, rem) = split_precompile(Some(ctx_ref), &Some(v.clone()), &new_pm, next_raise_count);

            let mut comp_fn = |partial: &Partial, ctx: &[Ctx], arg: &RawLambda, pmh: &PmHalfCompiled| -> Result<(RawLambda, Jumps), Unused> {
                do_compile_matching(ctx_ref, partial, ctx, arg, pmh, next_raise_count)
            };

            let (lam, total) = comp_match_handlers(
                &mut comp_fn,
                partial,
                ctx,
                &newarg,
                first_match,
                rem,
            )?;
            Ok((bind_check(*str_kind, &v, arg, lam), total))
        }
        (cases, []) if !cases.is_empty() => {
            // Cases exist but no args — shouldn't happen normally.
            // Return the first non-guarded action if available.
            for (_, act) in cases {
                if !is_guarded(act) {
                    return Ok((act.clone(), jumps_empty()));
                }
            }
            Err(Unused)
        }
        _ => panic!("Matching.compile_match"),
    }
}

/// Main dispatch for compiling half-compiled pattern matchings.
/// Equivalent to OCaml's `do_compile_matching`.
fn do_compile_matching(
    ctx_ref: &TypeContext<'_>,
    partial: &Partial,
    ctx: &[Ctx],
    arg: &RawLambda,
    pmh: &PmHalfCompiled,
    next_raise_count: &mut i32,
) -> Result<(RawLambda, Jumps), Unused> {
    match pmh {
        PmHalfCompiled::Pm(pm) => {
            let pat = what_is_cases(&pm.cases);
            match &pat.pat_desc {
                PatternDesc::Tpat_any => {
                    compile_no_test(
                        ctx_ref,
                        &|ctx, pm| divide_var(ctx, pm),
                        &|ctx| ctx_rshift(ctx),
                        partial,
                        ctx,
                        pm,
                        next_raise_count,
                    )
                }
                PatternDesc::Tpat_tuple(patl) => {
                    let arity = patl.len();
                    let norm_pat = normalize_pat(&pat);
                    compile_no_test(
                        ctx_ref,
                        &move |ctx, pm| divide_tuple(arity, &norm_pat, ctx, pm),
                        &|ctx| ctx_combine(ctx),
                        partial,
                        ctx,
                        pm,
                        next_raise_count,
                    )
                }
                PatternDesc::Tpat_record(fields, _) if !fields.is_empty() => {
                    let all_labels = resolve_all_record_labels(ctx_ref, &pat, fields);
                    let norm_pat = normalize_pat(&pat);
                    compile_no_test(
                        ctx_ref,
                        &move |ctx, pm| divide_record(&all_labels, &norm_pat, ctx, pm),
                        &|ctx| ctx_combine(ctx),
                        partial,
                        ctx,
                        pm,
                        next_raise_count,
                    )
                }
                PatternDesc::Tpat_constant(cst) => {
                    let names: Option<SwitchNames> = None;
                    let loc = Location::none();
                    let arg_clone = arg.clone();
                    let cst_clone = cst.clone();
                    compile_test_wrapper(
                        ctx_ref,
                        partial,
                        &|ctx, pm| divide_constant(ctx, pm),
                        &|ctx, def, c_div, nrc| {
                            combine_constant(
                                names.clone(),
                                loc.clone(),
                                arg_clone.clone(),
                                &cst_clone,
                                partial,
                                ctx,
                                def,
                                c_div,
                                nrc,
                            )
                        },
                        ctx,
                        pm,
                        next_raise_count,
                    )
                }
                PatternDesc::Tpat_construct(_, cstr, _) => {
                    let sw_names = names_from_construct_pattern(ctx_ref, &pat);
                    let loc = Location::none();
                    let arg_clone = arg.clone();
                    let ex_pat = pat.clone();
                    let cstr_clone = cstr.clone();
                    compile_test_wrapper(
                        ctx_ref,
                        partial,
                        &|ctx, pm| divide_constructor(ctx_ref, ctx, pm),
                        &|ctx, def, c_div, nrc| {
                            combine_constructor(
                                ctx_ref,
                                sw_names.clone(),
                                loc.clone(),
                                arg_clone.clone(),
                                &ex_pat,
                                &cstr_clone,
                                partial,
                                ctx,
                                def,
                                c_div,
                                nrc,
                            )
                        },
                        ctx,
                        pm,
                        next_raise_count,
                    )
                }
                PatternDesc::Tpat_array(_) => {
                    let names: Option<SwitchNames> = None;
                    let loc = Location::none();
                    let arg_clone = arg.clone();
                    compile_test_wrapper(
                        ctx_ref,
                        partial,
                        &|ctx, pm| divide_array(ctx, pm),
                        &|ctx, def, c_div, nrc| {
                            combine_array(
                                names.clone(),
                                loc.clone(),
                                arg_clone.clone(),
                                partial,
                                ctx,
                                def,
                                c_div,
                                nrc,
                            )
                        },
                        ctx,
                        pm,
                        next_raise_count,
                    )
                }
                PatternDesc::Tpat_variant(_, _, _row_ref) => {
                    let names: Option<SwitchNames> = None;
                    let loc = Location::none();
                    let arg_clone = arg.clone();
                    let row_desc = extract_row_from_type(ctx_ref, pat.pat_type);
                    let row_desc2 = row_desc.clone();
                    compile_test_wrapper(
                        ctx_ref,
                        partial,
                        &move |ctx, pm| divide_variant(ctx_ref, &row_desc, ctx, pm),
                        &|ctx, def, c_div, nrc| {
                            combine_variant(
                                ctx_ref,
                                names.clone(),
                                loc.clone(),
                                &row_desc2,
                                arg_clone.clone(),
                                partial,
                                ctx,
                                def,
                                c_div,
                                nrc,
                            )
                        },
                        ctx,
                        pm,
                        next_raise_count,
                    )
                }
                _ => panic!("do_compile_matching: unexpected pattern"),
            }
        }
        PmHalfCompiled::PmVar(PmVarCompiled { inside, var_arg }) => {
            let (lam, total) = do_compile_matching(
                ctx_ref,
                partial,
                &ctx_lshift(ctx),
                var_arg,
                inside,
                next_raise_count,
            )?;
            Ok((lam, jumps_map(|c| ctx_rshift(&c), &total)))
        }
        PmHalfCompiled::PmOr(PmOrCompiled { body, handlers, .. }) => {
            let (lam, total) = compile_match(ctx_ref, None, partial, ctx, body, next_raise_count)?;
            let mut compile_fn = |ctx: &[Ctx], pm: &PatternMatching| -> Result<(RawLambda, Jumps), Unused> {
                compile_match(ctx_ref, None, partial, ctx, pm, next_raise_count)
            };
            Ok(compile_orhandlers(&mut compile_fn, lam, total, ctx, handlers.clone()))
        }
    }
}

/// Compile without test (divide_line + compile_match).
/// Equivalent to OCaml's `compile_no_test`.
fn compile_no_test(
    ctx_ref: &TypeContext<'_>,
    divide_fn: &dyn Fn(&[Ctx], &PatternMatching) -> MatchCell,
    up_ctx: &dyn Fn(&[Ctx]) -> Vec<Ctx>,
    partial: &Partial,
    ctx: &[Ctx],
    to_match: &PatternMatching,
    next_raise_count: &mut i32,
) -> Result<(RawLambda, Jumps), Unused> {
    let cell = divide_fn(ctx, to_match);
    let (lambda, total) = compile_match(ctx_ref, None, partial, &cell.ctx, &cell.pm, next_raise_count)?;
    Ok((lambda, jumps_map(|c| up_ctx(&c), &total)))
}

/// Shared mutable counter for next_raise_count.
/// Uses interior mutability to allow multiple closures to share access.
/// This is safe because pattern matching compilation is single-threaded.
struct RaiseCounter(*mut i32);

impl RaiseCounter {
    fn new(r: &mut i32) -> Self {
        RaiseCounter(r as *mut i32)
    }

    fn get_mut(&self) -> &mut i32 {
        unsafe { &mut *self.0 }
    }
}

// Safety: pattern matching compilation is single-threaded
unsafe impl Send for RaiseCounter {}
unsafe impl Sync for RaiseCounter {}

/// Wrapper for compile_test that handles the type-specific divide and combine.
/// This replaces the OCaml pattern of passing `compile_match repr partial` as a function.
///
/// We inline compile_test here to avoid borrow conflicts with next_raise_count
/// being captured by both compile_fn and combine_fn closures.
fn compile_test_wrapper<K: Clone>(
    ctx_ref: &TypeContext<'_>,
    partial: &Partial,
    divide_fn: &dyn Fn(&[Ctx], &PatternMatching) -> Vec<(K, MatchCell)>,
    combine_fn: &dyn Fn(&[Ctx], &DefaultEnv, (Vec<(K, RawLambda)>, Jumps, Vec<Pattern>), &mut i32) -> (RawLambda, Jumps),
    ctx: &[Ctx],
    pm: &PatternMatching,
    next_raise_count: &mut i32,
) -> Result<(RawLambda, Jumps), Unused> {
    // Use a raw pointer to allow sharing next_raise_count between closures.
    // This is safe because compilation is single-threaded.
    let rc = RaiseCounter::new(next_raise_count);

    // Step 1: divide
    let division = divide_fn(ctx, pm);

    // Step 2: compile_list
    let c_div = {
        let mut compile_fn = |ctx: &[Ctx], pm: &PatternMatching| -> Result<(RawLambda, Jumps), Unused> {
            compile_match(ctx_ref, None, partial, ctx, pm, rc.get_mut())
        };
        compile_list(&mut compile_fn, division)?
    };

    // Step 3: combine
    match &c_div {
        (list, _, _) if list.is_empty() => {
            match mk_failaction_neg(partial, ctx, &pm.default) {
                (None, _) => Err(Unused),
                (Some(l), total) => Ok((l, total)),
            }
        }
        _ => Ok(combine_fn(ctx, &pm.default, c_div, rc.get_mut())),
    }
}

/// Extract all record label descriptions from a Tpat_record pattern's fields.
/// Sorted by field position (lbl_pos).
fn get_all_labels_from_record_fields(
    fields: &[(crate::types::typedtree::Loc<crate::parse_arena::LidentIdx>, LabelDescription, Pattern, bool)],
) -> Vec<LabelDescription> {
    let mut labels: Vec<LabelDescription> = fields.iter().map(|(_, lbl, _, _)| lbl.clone()).collect();
    labels.sort_by_key(|l| l.lbl_pos);
    labels
}

/// Resolve ALL record labels from the record type, not just those mentioned in the pattern.
/// This is the equivalent of OCaml's `lbl.lbl_all` which points to all labels of the record type.
/// We look up the type declaration via the TypeContext to get all labels.
fn resolve_all_record_labels(
    ctx_ref: &TypeContext<'_>,
    pat: &Pattern,
    fields: &[(crate::types::typedtree::Loc<crate::parse_arena::LidentIdx>, LabelDescription, Pattern, bool)],
) -> Vec<LabelDescription> {
    if fields.is_empty() {
        return Vec::new();
    }

    let first_lbl = &fields[0].1;

    // Try to resolve via the record type (lbl_res)
    if let Some(all_labels) = resolve_labels_from_type(ctx_ref, first_lbl.lbl_res, pat.pat_env) {
        return all_labels;
    }

    // Try via pat_type
    if let Some(all_labels) = resolve_labels_from_type(ctx_ref, pat.pat_type, pat.pat_env) {
        return all_labels;
    }

    // Fallback: return only mentioned fields (old behavior)
    get_all_labels_from_record_fields(fields)
}

/// Look up all LabelDescription entries for a record type.
fn resolve_labels_from_type(
    ctx_ref: &TypeContext<'_>,
    record_ty: TypeExprRef,
    env_ref: EnvRef,
) -> Option<Vec<LabelDescription>> {
    use crate::types::type_expr::TypeDesc;

    let ty = ctx_ref.repr(record_ty);
    let desc = ctx_ref.get_desc(ty);
    let (path, _args) = match &*desc {
        TypeDesc::Tconstr { path, args, .. } => (path.clone(), args.clone()),
        _ => return None,
    };
    drop(desc);

    // Try env lookup first
    let env = ctx_ref.get_typed_env(env_ref)?;
    if let Ok(decl) = env.lookup_type(&path) {
        if let crate::types::TypeKind::TypeRecord(ref labels, ref repr) = decl.type_kind {
            return Some(build_label_descriptions(labels, repr, decl.type_private));
        }
    }

    // Try type_ctx stores
    if let Some(decl) = ctx_ref.find_type_decl_by_path(&path.name()) {
        if let crate::types::TypeKind::TypeRecord(ref labels, ref repr) = decl.type_kind {
            return Some(build_label_descriptions(labels, repr, decl.type_private));
        }
    }
    if let Some(decl) = ctx_ref.find_type_decl(&path.last()) {
        if let crate::types::TypeKind::TypeRecord(ref labels, ref repr) = decl.type_kind {
            return Some(build_label_descriptions(labels, repr, decl.type_private));
        }
    }

    // Try stamp-based lookup
    if let crate::types::Path::Pident(ref id) = path {
        if id.stamp() != 0 {
            if let Some(decl) = ctx_ref.find_type_decl_by_stamp(id.stamp()) {
                if let crate::types::TypeKind::TypeRecord(ref labels, ref repr) = decl.type_kind {
                    return Some(build_label_descriptions(labels, repr, decl.type_private));
                }
            }
        }
    }

    // Handle inline records: path is Pdot(parent_type, constructor_name, _)
    // Look up the parent type declaration and find the constructor's inline record
    if let crate::types::Path::Pdot(ref parent_path, ref cstr_name, _) = path {
        // Try to find the parent type declaration
        let parent_decl = env.lookup_type(parent_path).ok().cloned()
            .or_else(|| ctx_ref.find_type_decl_by_path(&parent_path.name()).map(|d| d.clone()))
            .or_else(|| ctx_ref.find_type_decl(&parent_path.last()).map(|d| d.clone()))
            .or_else(|| {
                if let crate::types::Path::Pident(ref id) = **parent_path {
                    if id.stamp() != 0 {
                        ctx_ref.find_type_decl_by_stamp(id.stamp()).map(|d| d.clone())
                    } else {
                        None
                    }
                } else {
                    None
                }
            });
        if let Some(parent_decl) = parent_decl {
            if let crate::types::TypeKind::TypeVariant(ref constrs) = parent_decl.type_kind {
                for cd in constrs {
                    if cd.cd_id.name() == cstr_name.as_str() {
                        if let crate::types::ConstructorArguments::CstrRecord(ref labels) = cd.cd_args {
                            // Determine the block tag for this constructor
                            let mut block_tag = 0i32;
                            let num_nonconsts = constrs.iter().filter(|c| {
                                !matches!(c.cd_args, crate::types::ConstructorArguments::CstrTuple(ref args) if args.is_empty())
                            }).count() as i32;
                            for c in constrs {
                                if c.cd_id.name() == cstr_name.as_str() {
                                    break;
                                }
                                let is_constant = matches!(
                                    c.cd_args,
                                    crate::types::ConstructorArguments::CstrTuple(ref args) if args.is_empty()
                                );
                                if !is_constant {
                                    block_tag += 1;
                                }
                            }
                            let repr = RecordRepresentation::RecordInlined {
                                tag: block_tag,
                                name: cstr_name.clone(),
                                num_nonconsts,
                                attrs: cd.cd_attributes.clone(),
                            };
                            return Some(build_label_descriptions(labels, &repr, parent_decl.type_private));
                        }
                    }
                }
            }
        }
    }

    None
}

fn build_label_descriptions(
    labels: &[crate::types::decl::LabelDeclaration],
    repr: &RecordRepresentation,
    private: crate::types::asttypes::PrivateFlag,
) -> Vec<LabelDescription> {
    labels.iter().enumerate().map(|(pos, ld)| {
        LabelDescription {
            lbl_name: ld.ld_id.name().to_string(),
            lbl_res: TypeExprRef(0), // Not used by matching
            lbl_arg: ld.ld_type,
            lbl_mut: ld.ld_mutable,
            lbl_optional: ld.ld_optional,
            lbl_pos: pos as i32,
            lbl_all: crate::types::decl::LabelArrayRef(0),
            lbl_repres: repr.clone(),
            lbl_private: private,
            lbl_loc: ld.ld_loc.clone(),
            lbl_attributes: ld.ld_attributes.clone(),
        }
    }).collect()
}

/// Extract a RowDesc from a type expression (for variant matching).
/// Follows type links to find the Tvariant row.
fn extract_row_from_type(ctx_ref: &TypeContext<'_>, ty: TypeExprRef) -> RowDesc {
    use crate::types::type_expr::TypeDesc;
    let ty = ctx_ref.repr(ty);
    let desc = ctx_ref.get_desc(ty);
    match &*desc {
        TypeDesc::Tvariant(row) => row.clone(),
        _ => {
            // Return an empty row as fallback
            RowDesc {
                row_fields: Vec::new(),
                row_more: TypeExprRef(0),
                row_closed: true,
                row_fixed: false,
                row_name: None,
            }
        }
    }
}

/// Placeholder for names_from_construct_pattern.
/// In OCaml this is set by Lam_compile; for now returns None.
fn names_from_construct_pattern(
    _ctx_ref: &TypeContext<'_>,
    _pat: &Pattern,
) -> Option<SwitchNames> {
    None
}

// ============================================================================
// Layer 11: Entry points — OCaml matching.ml lines 2631-2978
// ============================================================================

/// Find if a predicate holds for any sub-pattern description.
/// Equivalent to OCaml's `find_in_pat`.
fn find_in_pat(pred: &dyn Fn(&PatternDesc) -> bool, p: &Pattern) -> bool {
    if pred(&p.pat_desc) {
        return true;
    }
    match &p.pat_desc {
        PatternDesc::Tpat_alias(p, _, _) | PatternDesc::Tpat_variant(_, Some(p), _) => {
            find_in_pat(pred, p)
        }
        PatternDesc::Tpat_tuple(ps) | PatternDesc::Tpat_construct(_, _, ps) | PatternDesc::Tpat_array(ps) => {
            ps.iter().any(|p| find_in_pat(pred, p))
        }
        PatternDesc::Tpat_record(lpats, _) => {
            lpats.iter().any(|(_, _, p, _)| find_in_pat(pred, p))
        }
        PatternDesc::Tpat_or(p, q, _) => find_in_pat(pred, p) || find_in_pat(pred, q),
        PatternDesc::Tpat_constant(_)
        | PatternDesc::Tpat_var(_, _)
        | PatternDesc::Tpat_any
        | PatternDesc::Tpat_variant(_, None, _) => false,
    }
}

/// Check if a pattern description accesses mutable record fields.
/// Equivalent to OCaml's `have_mutable_field`.
fn have_mutable_field(p: &PatternDesc) -> bool {
    match p {
        PatternDesc::Tpat_record(lps, _) => lps.iter().any(|(_, lbl, _, _)| {
            matches!(lbl.lbl_mut, MutableFlag::Mutable)
        }),
        _ => false,
    }
}

/// Check if a pattern accesses mutable fields anywhere.
/// Equivalent to OCaml's `is_mutable`.
fn is_mutable(p: &Pattern) -> bool {
    find_in_pat(&have_mutable_field, p)
}

/// Downgrade Total to Partial when needed.
/// Equivalent to OCaml's `check_partial` (single pattern version).
fn check_partial_single(
    pat_act_list: &[(Pattern, RawLambda)],
    partial: Partial,
) -> Partial {
    match partial {
        Partial::Partial => Partial::Partial,
        Partial::Total => {
            if pat_act_list.is_empty()
                || pat_act_list
                    .iter()
                    .any(|(pat, lam)| is_mutable(pat) && is_guarded(lam))
            {
                Partial::Partial
            } else {
                Partial::Total
            }
        }
    }
}

/// Downgrade Total to Partial when needed (list of patterns version).
/// Equivalent to OCaml's `check_partial_list`.
fn check_partial_list(
    pat_act_list: &[(Vec<Pattern>, RawLambda)],
    partial: Partial,
) -> Partial {
    match partial {
        Partial::Partial => Partial::Partial,
        Partial::Total => {
            if pat_act_list.is_empty()
                || pat_act_list.iter().any(|(pats, lam)| {
                    pats.iter().any(|p| is_mutable(p)) && is_guarded(lam)
                })
            {
                Partial::Partial
            } else {
                Partial::Total
            }
        }
    }
}

/// Create a starting context of n wildcards.
/// Equivalent to OCaml's `start_ctx`.
fn start_ctx(n: usize) -> Vec<Ctx> {
    vec![Ctx {
        left: Vec::new(),
        right: omegas(n),
    }]
}

/// Check total: add a catch handler if jumps are not empty.
/// Equivalent to OCaml's `check_total`.
fn check_total(
    total: &Jumps,
    lambda: RawLambda,
    i: i32,
    handler_fun: impl FnOnce() -> RawLambda,
) -> RawLambda {
    if jumps_is_empty(total) {
        lambda
    } else {
        RawLambda::LstaticCatch(
            Box::new(lambda),
            (i, Vec::new()),
            Box::new(handler_fun()),
        )
    }
}

/// Compile a matching with error handler.
/// Equivalent to OCaml's `compile_matching`.
pub fn compile_matching(
    ctx_ref: &TypeContext<'_>,
    handler_fun: impl FnOnce() -> RawLambda,
    arg: RawLambda,
    pat_act_list: Vec<(Pattern, RawLambda)>,
    partial: Partial,
    next_raise_count: &mut i32,
) -> RawLambda {
    let partial = check_partial_single(&pat_act_list, partial);
    match partial {
        Partial::Partial => {
            *next_raise_count += 1;
            let raise_num = *next_raise_count;
            let pm = PatternMatching {
                cases: pat_act_list
                    .into_iter()
                    .map(|(pat, act)| (vec![pat], act))
                    .collect(),
                args: vec![(arg, LetKind::Strict)],
                default: vec![(vec![vec![omega()]], raise_num)],
            };
            match compile_match(ctx_ref, None, &partial, &start_ctx(1), &pm, next_raise_count) {
                Ok((lambda, total)) => check_total(&total, lambda, raise_num, handler_fun),
                Err(Unused) => panic!("compile_matching: Unused"),
            }
        }
        Partial::Total => {
            let pm = PatternMatching {
                cases: pat_act_list
                    .into_iter()
                    .map(|(pat, act)| (vec![pat], act))
                    .collect(),
                args: vec![(arg, LetKind::Strict)],
                default: Vec::new(),
            };
            match compile_match(ctx_ref, None, &partial, &start_ctx(1), &pm, next_raise_count) {
                Ok((lambda, total)) => {
                    assert!(jumps_is_empty(&total));
                    lambda
                }
                Err(Unused) => {
                    // Shouldn't happen for Total matches, but handle gracefully
                    // by returning a unit value as placeholder.
                    lambda_unit()
                }
            }
        }
    }
}

/// Build a match failure exception raise.
/// Equivalent to OCaml's `partial_function`.
pub fn partial_function(_ctx_ref: &TypeContext<'_>, loc: Location) -> RawLambda {
    let line = loc.loc_start.line;
    let char_pos = loc.loc_start.column();
    // File name is stored as StrIdx; we use "" as placeholder since we can't
    // resolve it without the parse arena. The actual file name will be resolved
    // when this is called from convert.rs which has arena access.
    let fname = String::new();

    let match_failure_ident = Ident::new(
        "Match_failure",
        17, // PREDEF_MATCH_FAILURE_STAMP
        IdentFlags::PREDEF_EXN.with_global(),
    );
    let exn = RawLambda::LglobalModule(match_failure_ident, false);
    let payload = RawLambda::Lconst(crate::lambda::Constant::Block {
        tag: 0,
        tag_info: TagInfo::Tuple,
        elements: vec![
            crate::lambda::Constant::string(fname),
            crate::lambda::Constant::int(line),
            crate::lambda::Constant::int(char_pos),
        ],
    });

    RawLambda::Lprim(RawPrimInfo {
        primitive: Primitive::Praise,
        args: vec![RawLambda::Lprim(RawPrimInfo {
            primitive: Primitive::Pmakeblock(0, TagInfo::Extension, Mutable::Immutable),
            args: vec![exn, payload],
            loc: loc.clone(),
        })],
        loc,
    })
}

/// Compile a match for a function body.
/// Equivalent to OCaml's `for_function`.
pub fn for_function(
    ctx_ref: &TypeContext<'_>,
    loc: Location,
    param: RawLambda,
    pat_act_list: Vec<(Pattern, RawLambda)>,
    partial: Partial,
    next_raise_count: &mut i32,
) -> RawLambda {
    let loc_clone = loc.clone();
    compile_matching(
        ctx_ref,
        || partial_function(ctx_ref, loc_clone),
        param,
        pat_act_list,
        partial,
        next_raise_count,
    )
}

/// Compile a match for a try-with handler.
/// Equivalent to OCaml's `for_trywith`.
pub fn for_trywith(
    ctx_ref: &TypeContext<'_>,
    param: RawLambda,
    pat_act_list: Vec<(Pattern, RawLambda)>,
    next_raise_count: &mut i32,
) -> RawLambda {
    let param_clone = param.clone();
    compile_matching(
        ctx_ref,
        || RawLambda::Lprim(RawPrimInfo {
            primitive: Primitive::Praise,
            args: vec![param_clone],
            loc: Location::none(),
        }),
        param,
        pat_act_list,
        Partial::Partial,
        next_raise_count,
    )
}

/// Simple let matching.
/// Equivalent to OCaml's `simple_for_let`.
pub fn simple_for_let(
    ctx_ref: &TypeContext<'_>,
    loc: Location,
    param: RawLambda,
    pat: Pattern,
    body: RawLambda,
    next_raise_count: &mut i32,
) -> RawLambda {
    let loc_clone = loc.clone();
    compile_matching(
        ctx_ref,
        || partial_function(ctx_ref, loc_clone),
        param,
        vec![(pat, body)],
        Partial::Partial,
        next_raise_count,
    )
}

/// Compile a let binding match (with optimization for simple cases).
/// Equivalent to OCaml's `for_let`.
pub fn for_let(
    ctx_ref: &TypeContext<'_>,
    loc: Location,
    param: RawLambda,
    pat: &Pattern,
    body: RawLambda,
    next_raise_count: &mut i32,
) -> RawLambda {
    match &pat.pat_desc {
        PatternDesc::Tpat_any => {
            // Eliminates a useless variable
            RawLambda::Lsequence(Box::new(param), Box::new(body))
        }
        PatternDesc::Tpat_var(id, _) => {
            // Fast path
            RawLambda::Llet(LetKind::Strict, id.clone(), Box::new(param), Box::new(body))
        }
        _ => simple_for_let(ctx_ref, loc, param, pat.clone(), body, next_raise_count),
    }
}

/// Compile a tupled function match.
/// Equivalent to OCaml's `for_tupled_function`.
pub fn for_tupled_function(
    ctx_ref: &TypeContext<'_>,
    loc: Location,
    paraml: &[Ident],
    pats_act_list: Vec<(Vec<Pattern>, RawLambda)>,
    partial: Partial,
    next_raise_count: &mut i32,
) -> RawLambda {
    let partial = check_partial_list(&pats_act_list, partial);
    *next_raise_count += 1;
    let raise_num = *next_raise_count;
    let omegas_row: Vec<Vec<Pattern>> = vec![paraml.iter().map(|_| omega()).collect()];
    let pm = PatternMatching {
        cases: pats_act_list,
        args: paraml
            .iter()
            .map(|id| (RawLambda::Lvar(id.clone()), LetKind::Strict))
            .collect(),
        default: vec![(omegas_row, raise_num)],
    };
    match compile_match(
        ctx_ref,
        None,
        &partial,
        &start_ctx(paraml.len()),
        &pm,
        next_raise_count,
    ) {
        Ok((lambda, total)) => {
            let loc_clone = loc.clone();
            check_total(&total, lambda, raise_num, || {
                partial_function(ctx_ref, loc_clone)
            })
        }
        Err(Unused) => partial_function(ctx_ref, loc),
    }
}

/// Cannot_flatten exception — used by flatten_pattern.
struct CannotFlattenExn;

/// Flatten a pattern into its tuple components.
/// Equivalent to OCaml's `flatten_pattern`.
fn flatten_pattern(size: usize, p: &Pattern) -> Result<Vec<Pattern>, CannotFlattenExn> {
    match &p.pat_desc {
        PatternDesc::Tpat_tuple(args) => Ok(args.clone()),
        PatternDesc::Tpat_any => Ok(omegas(size)),
        _ => Err(CannotFlattenExn),
    }
}

/// Flatten a pattern line (possibly through or-patterns and aliases).
/// Equivalent to OCaml's `flatten_pat_line`.
fn flatten_pat_line(
    size: usize,
    p: &Pattern,
    k: Vec<Vec<Pattern>>,
) -> Result<Vec<Vec<Pattern>>, CannotFlattenExn> {
    match &p.pat_desc {
        PatternDesc::Tpat_any => {
            let mut result = vec![omegas(size)];
            result.extend(k);
            Ok(result)
        }
        PatternDesc::Tpat_tuple(args) => {
            let mut result = vec![args.clone()];
            result.extend(k);
            Ok(result)
        }
        PatternDesc::Tpat_or(p1, p2, _) => {
            let k = flatten_pat_line(size, p2, k)?;
            flatten_pat_line(size, p1, k)
        }
        PatternDesc::Tpat_alias(p, _, _) => flatten_pat_line(size, p, k),
        _ => Err(CannotFlattenExn),
    }
}

/// Flatten all cases.
/// Equivalent to OCaml's `flatten_cases`.
fn flatten_cases(
    size: usize,
    cases: &[(Vec<Pattern>, RawLambda)],
) -> Result<Vec<(Vec<Pattern>, RawLambda)>, CannotFlattenExn> {
    cases
        .iter()
        .map(|(ps, action)| match ps.as_slice() {
            [p] => Ok((flatten_pattern(size, p)?, action.clone())),
            _ => Err(CannotFlattenExn),
        })
        .collect()
}

/// Flatten a matrix.
/// Equivalent to OCaml's `flatten_matrix`.
fn flatten_matrix(size: usize, pss: &Matrix) -> Result<Matrix, CannotFlattenExn> {
    pss.iter().rev().try_fold(Vec::new(), |r, ps| match ps.as_slice() {
        [p] => flatten_pat_line(size, p, r),
        _ => Err(CannotFlattenExn),
    })
}

/// Flatten default environment.
/// Equivalent to OCaml's `flatten_def`.
fn flatten_def(size: usize, def: &DefaultEnv) -> Result<DefaultEnv, CannotFlattenExn> {
    def.iter()
        .map(|(pss, i)| Ok((flatten_matrix(size, pss)?, *i)))
        .collect()
}

/// Flatten a pattern matching.
/// Equivalent to OCaml's `flatten_pm`.
fn flatten_pm(
    size: usize,
    args: Vec<(RawLambda, LetKind)>,
    pm: &PatternMatching,
) -> Result<PatternMatching, CannotFlattenExn> {
    Ok(PatternMatching {
        args,
        cases: flatten_cases(size, &pm.cases)?,
        default: flatten_def(size, &pm.default)?,
    })
}

/// Flatten a precompiled pattern matching.
/// Equivalent to OCaml's `flatten_precompiled`.
fn flatten_precompiled(
    size: usize,
    args: Vec<(RawLambda, LetKind)>,
    pmh: PmHalfCompiled,
) -> Result<PmHalfCompiled, CannotFlattenExn> {
    match pmh {
        PmHalfCompiled::Pm(pm) => Ok(PmHalfCompiled::Pm(flatten_pm(size, args, &pm)?)),
        PmHalfCompiled::PmOr(PmOrCompiled {
            body,
            handlers,
            or_matrix,
        }) => {
            let flat_body = flatten_pm(size, args, &body)?;
            let flat_handlers: Vec<_> = handlers
                .into_iter()
                .map(|(mat, i, vars, pm)| {
                    let flat_mat = flatten_matrix(size, &mat)?;
                    Ok((flat_mat, i, vars, pm))
                })
                .collect::<Result<_, CannotFlattenExn>>()?;
            let flat_or_matrix = flatten_matrix(size, &or_matrix)?;
            Ok(PmHalfCompiled::PmOr(PmOrCompiled {
                body: flat_body,
                handlers: flat_handlers,
                or_matrix: flat_or_matrix,
            }))
        }
        PmHalfCompiled::PmVar(_) => panic!("flatten_precompiled: PmVar"),
    }
}

/// Compiled_flattened: a comp_fun argument to comp_match_handlers.
/// Hence it needs a fourth argument (arg), which it ignores.
/// Equivalent to OCaml's `compile_flattened`.
fn compile_flattened(
    ctx_ref: &TypeContext<'_>,
    partial: &Partial,
    ctx: &[Ctx],
    _arg: &RawLambda,
    pmh: &PmHalfCompiled,
    next_raise_count: &mut i32,
) -> Result<(RawLambda, Jumps), Unused> {
    match pmh {
        PmHalfCompiled::Pm(pm) => {
            compile_match(ctx_ref, None, partial, ctx, pm, next_raise_count)
        }
        PmHalfCompiled::PmOr(PmOrCompiled { body, handlers, .. }) => {
            let (lam, total) =
                compile_match(ctx_ref, None, partial, ctx, body, next_raise_count)?;
            let mut compile_fn = |ctx: &[Ctx], pm: &PatternMatching| -> Result<(RawLambda, Jumps), Unused> {
                compile_match(ctx_ref, None, partial, ctx, pm, next_raise_count)
            };
            Ok(compile_orhandlers(&mut compile_fn, lam, total, ctx, handlers.clone()))
        }
        PmHalfCompiled::PmVar(_) => panic!("compile_flattened: PmVar"),
    }
}

/// Compile a multiple-match expression (tuple patterns on arguments).
/// Equivalent to OCaml's `do_for_multiple_match`.
pub fn do_for_multiple_match(
    ctx_ref: &TypeContext<'_>,
    loc: Location,
    paraml: Vec<RawLambda>,
    pat_act_list: Vec<(Pattern, RawLambda)>,
    partial: Partial,
    next_raise_count: &mut i32,
) -> RawLambda {
    let partial = check_partial_single(&pat_act_list, partial);
    let (raise_num, pm1) = match &partial {
        Partial::Partial => {
            *next_raise_count += 1;
            let raise_num = *next_raise_count;
            (
                raise_num,
                PatternMatching {
                    cases: pat_act_list
                        .iter()
                        .map(|(pat, act)| (vec![pat.clone()], act.clone()))
                        .collect(),
                    args: vec![(
                        RawLambda::Lprim(RawPrimInfo {
                            primitive: Primitive::Pmakeblock(
                                0,
                                TagInfo::Tuple,
                                Mutable::Immutable,
                            ),
                            args: paraml.clone(),
                            loc: loc.clone(),
                        }),
                        LetKind::Strict,
                    )],
                    default: vec![(vec![vec![omega()]], raise_num)],
                },
            )
        }
        Partial::Total => (
            -1,
            PatternMatching {
                cases: pat_act_list
                    .iter()
                    .map(|(pat, act)| (vec![pat.clone()], act.clone()))
                    .collect(),
                args: vec![(
                    RawLambda::Lprim(RawPrimInfo {
                        primitive: Primitive::Pmakeblock(
                            0,
                            TagInfo::Tuple,
                            Mutable::Immutable,
                        ),
                        args: paraml.clone(),
                        loc: loc.clone(),
                    }),
                    LetKind::Strict,
                )],
                default: Vec::new(),
            },
        ),
    };

    // Try flatten optimization first
    let result = (|| -> Result<RawLambda, CannotFlattenExn> {
        let (next, nexts) = split_precompile(Some(ctx_ref), &None, &pm1, next_raise_count);

        let size = paraml.len();

        // Debug: print what split_precompile produced
        let idl: Vec<Ident> = paraml.iter().map(|_| Ident::create_local("match")).collect();
        let args: Vec<(RawLambda, LetKind)> = idl
            .iter()
            .map(|id| (RawLambda::Lvar(id.clone()), LetKind::Alias))
            .collect();

        let flat_next = flatten_precompiled(size, args.clone(), next)?;
        let flat_nexts: Vec<(i32, PmHalfCompiled)> = nexts
            .into_iter()
            .map(|(e, pm)| {
                let flat = flatten_precompiled(size, args.clone(), pm)?;
                Ok((e, flat))
            })
            .collect::<Result<_, CannotFlattenExn>>()?;

        let mut compile_fn = |partial: &Partial, ctx: &[Ctx], arg: &RawLambda, pmh: &PmHalfCompiled| -> Result<(RawLambda, Jumps), Unused> {
            compile_flattened(ctx_ref, partial, ctx, arg, pmh, next_raise_count)
        };

        let dummy_arg = RawLambda::Lconst(crate::lambda::Constant::int(0));
        let (lam, total) = comp_match_handlers(
            &mut compile_fn,
            &partial,
            &start_ctx(size),
            &dummy_arg,
            flat_next,
            flat_nexts,
        )
        .map_err(|_| CannotFlattenExn)?;

        let result = idl.iter().zip(paraml.iter()).rev().fold(
            match &partial {
                Partial::Partial => {
                    let loc_clone = loc.clone();
                    check_total(&total, lam, raise_num, || {
                        partial_function(ctx_ref, loc_clone)
                    })
                }
                Partial::Total => {
                    assert!(jumps_is_empty(&total));
                    lam
                }
            },
            |body, (id, param)| bind(LetKind::Strict, id, param, body),
        );
        Ok(result)
    })();

    match result {
        Ok(lam) => lam,
        Err(CannotFlattenExn) => {
            // Fallback: compile without flattening
            match compile_match(ctx_ref, None, &partial, &start_ctx(1), &pm1, next_raise_count) {
                Ok((lambda, total)) => match &partial {
                    Partial::Partial => {
                        let loc_clone = loc.clone();
                        check_total(&total, lambda, raise_num, || {
                            partial_function(ctx_ref, loc_clone)
                        })
                    }
                    Partial::Total => {
                        assert!(jumps_is_empty(&total));
                        lambda
                    }
                },
                Err(Unused) => panic!("do_for_multiple_match: Unused"),
            }
        }
    }
}

/// Extract a variable from a param, binding if needed.
/// Equivalent to OCaml's `param_to_var`.
fn param_to_var(param: &RawLambda) -> (Ident, Option<RawLambda>) {
    match param {
        RawLambda::Lvar(v) => (v.clone(), None),
        _ => (Ident::create_local("match"), Some(param.clone())),
    }
}

/// Optionally bind a variable.
/// Equivalent to OCaml's `bind_opt`.
fn bind_opt(v_eo: (Ident, Option<RawLambda>), k: RawLambda) -> RawLambda {
    match v_eo {
        (_, None) => k,
        (v, Some(e)) => bind(LetKind::Strict, &v, &e, k),
    }
}

/// Compile a multiple match expression.
/// Equivalent to OCaml's `for_multiple_match`.
pub fn for_multiple_match(
    ctx_ref: &TypeContext<'_>,
    loc: Location,
    paraml: Vec<RawLambda>,
    pat_act_list: Vec<(Pattern, RawLambda)>,
    partial: Partial,
    next_raise_count: &mut i32,
) -> RawLambda {
    let v_paraml: Vec<(Ident, Option<RawLambda>)> = paraml.iter().map(param_to_var).collect();
    let new_paraml: Vec<RawLambda> = v_paraml.iter().map(|(v, _)| RawLambda::Lvar(v.clone())).collect();
    let inner = do_for_multiple_match(ctx_ref, loc, new_paraml, pat_act_list, partial, next_raise_count);
    v_paraml.into_iter().rev().fold(inner, |body, v_eo| bind_opt(v_eo, body))
}
