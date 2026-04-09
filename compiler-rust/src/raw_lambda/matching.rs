//! Pattern matching compilation — Layer 1: Core types and infrastructure.
//!
//! This is a 1:1 port of OCaml's `matching.ml` lines 1-374.
//! It defines the core data structures (matrix, context, jumps, pattern_matching)
//! and the operations on them used by the pattern matching compiler.

#![allow(dead_code)]

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
use crate::types::decl::ConstructorTag;
use crate::types::asttypes::MutableFlag;

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
/// Simplified version of OCaml's `all_record_args`.
fn all_record_args(
    lbls: &[(crate::parse_arena::Located<crate::parse_arena::LidentIdx>, crate::types::LabelDescription, Pattern, bool)],
) -> Vec<(crate::parse_arena::Located<crate::parse_arena::LidentIdx>, crate::types::LabelDescription, Pattern, bool)> {
    // For now, just return the fields as-is. The full OCaml version
    // expands to all labels using lbl_all, but that requires the label
    // array store. This is sufficient for the matching algorithm.
    lbls.to_vec()
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
                    let expanded = all_record_args(fields2);
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
pub struct PmOrCompiled {
    /// The body pattern matching.
    pub body: PatternMatching,
    /// Handlers for or-patterns: (matrix, exit_number, idents, pattern_matching).
    pub handlers: Vec<(Matrix, i32, Vec<Ident>, PatternMatching)>,
    /// The or-pattern matrix.
    pub or_matrix: Matrix,
}

/// Half-compiled pattern matching.
pub enum PmHalfCompiled {
    /// Or-pattern compiled.
    PmOr(PmOrCompiled),
    /// Variable case.
    PmVar(PmVarCompiled),
    /// Simple pattern matching.
    Pm(PatternMatching),
}

/// Variable case in half-compiled pattern matching.
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
fn simplify_or(p: &Pattern) -> Pattern {
    fn simpl_rec(p: &Pattern) -> Result<Pattern, VarPat> {
        match &p.pat_desc {
            PatternDesc::Tpat_any | PatternDesc::Tpat_var(..) => {
                Err(VarPat::Var(p.clone()))
            }
            PatternDesc::Tpat_alias(q, id, s) => {
                match simpl_rec(q) {
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
                let q1 = simpl_rec(p1)?; // propagates Var if p1 is variable
                match simpl_rec(p2) {
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
                let all_lbls = all_record_args(lbls);
                Ok(Pattern {
                    pat_desc: PatternDesc::Tpat_record(all_lbls, *closed),
                    ..p.clone()
                })
            }
            _ => Ok(p.clone()),
        }
    }

    match simpl_rec(p) {
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
    args: &[(RawLambda, LetKind)],
    cls: Vec<(Vec<Pattern>, RawLambda)>,
) -> Vec<(Vec<Pattern>, RawLambda)> {
    assert!(!args.is_empty(), "simplify_cases: empty args");

    let (ref arg, _) = args[0];

    fn simplify(
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
                result.extend(simplify(arg, cls));
                result
            }
            PatternDesc::Tpat_any => {
                let mut result = vec![(pats, action)];
                result.extend(simplify(arg, cls));
                result
            }
            PatternDesc::Tpat_alias(p, id, _) => {
                let new_action = bind(LetKind::Alias, id, arg, action);
                let mut new_pats = vec![(**p).clone()];
                new_pats.extend(patl.iter().cloned());
                cls.insert(0, (new_pats, new_action));
                simplify(arg, cls)
            }
            PatternDesc::Tpat_record(lbls, _) if lbls.is_empty() => {
                let mut row = vec![omega()];
                row.extend(patl.iter().cloned());
                let mut result = vec![(row, action)];
                result.extend(simplify(arg, cls));
                result
            }
            PatternDesc::Tpat_record(lbls, closed) => {
                let all_lbls = all_record_args(lbls);
                let full_pat = Pattern {
                    pat_desc: PatternDesc::Tpat_record(all_lbls, *closed),
                    ..pat.clone()
                };
                let mut row = vec![full_pat];
                row.extend(patl.iter().cloned());
                let mut result = vec![(row, action)];
                result.extend(simplify(arg, cls));
                result
            }
            PatternDesc::Tpat_or(..) => {
                let pat_simple = simplify_or(pat);
                match &pat_simple.pat_desc {
                    PatternDesc::Tpat_or(..) => {
                        let mut row = vec![pat_simple];
                        row.extend(patl.iter().cloned());
                        let mut result = vec![(row, action)];
                        result.extend(simplify(arg, cls));
                        result
                    }
                    _ => {
                        // Simplified away the or — re-process
                        let mut new_pats = vec![pat_simple];
                        new_pats.extend(patl.iter().cloned());
                        cls.insert(0, (new_pats, action));
                        simplify(arg, cls)
                    }
                }
            }
            _ => {
                let mut result = vec![(pats, action)];
                result.extend(simplify(arg, cls));
                result
            }
        }
    }

    simplify(arg, cls)
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
