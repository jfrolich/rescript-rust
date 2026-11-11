//! Variable substitution over the Lambda arena.
//!
//! Bound variables of the term must not be in the domain of the substitution
//! and its image must not be captured by them (callers alpha-rename first).

use ahash::AHashMap as HashMap;

use crate::ident::Ident;
use crate::lambda::arena::{Lam, LamArena, Node};

/// A substitution of identifiers by Lambda terms.
pub type Subst = HashMap<Ident, Lam>;

/// `Lambda_traverse.subst_lambda` (lambda_traverse.ml:235-241): replace
/// variables and rebuild, through the smart constructors of
/// `shallow_map_sharing`, only the nodes whose children changed.
pub fn subst_lambda(a: &mut LamArena, s: &Subst, lam: Lam) -> Lam {
    match a.node(lam) {
        Node::Var(id) => s.get(&a.ident(id)).copied().unwrap_or(lam),
        _ => a.shallow_map(lam, &mut |a, x| subst_lambda(a, s, x)),
    }
}

/// Substitution that rebuilds through plain constructors only (no folding),
/// as the raw `Lam_subst.subst` does. Shared subtrees without a substituted
/// variable keep their handle, which is the same term the raw rebuild would
/// produce.
pub fn subst(a: &mut LamArena, s: &Subst, lam: Lam) -> Lam {
    if s.is_empty() {
        return lam;
    }
    subst_raw(a, s, lam)
}

fn subst_raw(a: &mut LamArena, s: &Subst, lam: Lam) -> Lam {
    match a.node(lam) {
        Node::Var(id) => s.get(&a.ident(id)).copied().unwrap_or(lam),
        Node::Apply { func, args, info } => {
            let nf = subst_raw(a, s, func);
            let (nargs, changed) = a.map_list(args, &mut |a, x| subst_raw(a, s, x));
            if nf == func && !changed {
                lam
            } else {
                a.apply_raw_with(nf, nargs, info)
            }
        }
        Node::Prim { args, info } => {
            let (nargs, changed) = a.map_list(args, &mut |a, x| subst_raw(a, s, x));
            if changed {
                a.prim_raw_with(info, nargs)
            } else {
                lam
            }
        }
        Node::Switch {
            scrut,
            actions,
            info,
        } => {
            let ns = subst_raw(a, s, scrut);
            let (nactions, changed) = a.map_list(actions, &mut |a, x| subst_raw(a, s, x));
            if ns == scrut && !changed {
                lam
            } else {
                a.switch_raw(ns, nactions, info)
            }
        }
        Node::StringSwitch {
            scrut,
            actions,
            info,
        } => {
            let ns = subst_raw(a, s, scrut);
            let (nactions, changed) = a.map_list(actions, &mut |a, x| subst_raw(a, s, x));
            if ns == scrut && !changed {
                lam
            } else {
                a.string_switch_raw(ns, nactions, info)
            }
        }
        Node::If { cond, then_, else_ } => {
            let nc = subst_raw(a, s, cond);
            let nt = subst_raw(a, s, then_);
            let ne = subst_raw(a, s, else_);
            if nc == cond && nt == then_ && ne == else_ {
                lam
            } else {
                a.if_raw(nc, nt, ne)
            }
        }
        Node::Sequence(x, y) => {
            let nx = subst_raw(a, s, x);
            let ny = subst_raw(a, s, y);
            if nx == x && ny == y {
                lam
            } else {
                a.seq_raw(nx, ny)
            }
        }
        // The remaining constructors are plain in `shallow_map` too.
        _ => a.shallow_map(lam, &mut |a, x| subst_raw(a, s, x)),
    }
}
