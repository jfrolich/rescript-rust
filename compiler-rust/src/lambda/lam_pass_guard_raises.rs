//! `Lam_pass_guard_raises.guard_raises` over the Lambda arena.
//!
//! `if a then raise e else c` becomes `(if a then raise e else ()); c`, so
//! the continuation is not nested inside a branch. It runs as the last
//! Lambda pass: rewriting inside `Lam.if_` would leave static raises without
//! their catch.

use crate::lambda::arena::{Lam, LamArena, Node};
use crate::lambda::lam_primitive::Primitive;

/// Applies the rewrite described in the module docs to `lam`.
pub fn guard_raises(a: &mut LamArena, lam: Lam) -> Lam {
    if let Node::If { cond, then_, else_ } = a.node(lam)
        && matches!(a.as_prim(then_), Some((Primitive::Praise, _, _)))
        && !a.is_const(else_)
    {
        let cond = guard_raises(a, cond);
        let rest = guard_raises(a, else_);
        let unit = a.unit();
        let guard = a.if_(cond, then_, unit);
        return a.seq(guard, rest);
    }
    // A constant alternative is already as flat as it gets.
    a.shallow_map(lam, &mut guard_raises)
}
