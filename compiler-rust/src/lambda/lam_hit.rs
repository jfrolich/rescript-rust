//! `Lam_hit.hit_variable` over the Lambda arena.

use crate::ident::Ident;
use crate::lambda::arena::{Lam, LamArena, Node};

/// Does `fv` occur (read or assigned) anywhere in `lam`?
pub fn hit_variable(a: &LamArena, fv: &Ident, lam: Lam) -> bool {
    let hit_list = |xs: &[Lam]| xs.iter().any(|x| hit_variable(a, fv, *x));
    match a.node(lam) {
        Node::Var(id) => a.ident(id) == *fv,
        Node::Assign { id, value } => a.ident(id) == *fv || hit_variable(a, fv, value),
        Node::StaticCatch { body, handler, .. }
        | Node::TryWith { body, handler, .. }
        | Node::TryFinally {
            body,
            finally: handler,
        } => hit_variable(a, fv, body) || hit_variable(a, fv, handler),
        Node::Function { body, .. } => hit_variable(a, fv, body),
        Node::Let { value, body, .. } => hit_variable(a, fv, value) || hit_variable(a, fv, body),
        Node::LetRec { values, body, .. } => hit_variable(a, fv, body) || hit_list(a.list(values)),
        Node::For { kids, .. } => hit_list(a.list(kids)),
        Node::ForOf { iter, body, .. } | Node::ForAwaitOf { iter, body, .. } => {
            hit_variable(a, fv, iter) || hit_variable(a, fv, body)
        }
        Node::Const(_) | Node::GlobalModule(_) | Node::Break | Node::Continue => false,
        Node::Apply { func, args, .. } => hit_variable(a, fv, func) || hit_list(a.list(args)),
        Node::Prim { args, .. } | Node::StaticRaise { args, .. } => hit_list(a.list(args)),
        Node::Switch { scrut, actions, .. } | Node::StringSwitch { scrut, actions, .. } => {
            hit_variable(a, fv, scrut) || hit_list(a.list(actions))
        }
        Node::If { cond, then_, else_ } => {
            hit_variable(a, fv, cond) || hit_variable(a, fv, then_) || hit_variable(a, fv, else_)
        }
        Node::Sequence(x, y) | Node::While(x, y) => {
            hit_variable(a, fv, x) || hit_variable(a, fv, y)
        }
    }
}
