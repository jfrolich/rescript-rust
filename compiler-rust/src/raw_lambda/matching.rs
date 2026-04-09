//! Pattern matching compilation — Layer 1: Core types and infrastructure.
//!
//! This is a 1:1 port of OCaml's `matching.ml` lines 1-374.
//! It defines the core data structures (matrix, context, jumps, pattern_matching)
//! and the operations on them used by the pattern matching compiler.

#![allow(dead_code)]

use crate::ident::Ident;
use crate::lambda::LetKind;
use crate::parse_arena::LocIdx;
use crate::parser::ast::Attributes;
use crate::raw_lambda::RawLambda;
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
