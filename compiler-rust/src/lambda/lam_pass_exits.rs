//! `Lam_pass_exits.simplify_exits` and `Lam_exit_count` over the Lambda
//! arena.

use ahash::AHashMap as HashMap;

use crate::context::IdGenerator;
use crate::ident::Ident;
use crate::lambda::arena::{IdentSpan, Lam, LamArena, Node};
use crate::lambda::lam_analysis::EXIT_INLINE_SIZE;
use crate::lambda::lam_analysis::size_upto;
use crate::lambda::lam_compat::LetKind;
use crate::lambda::lam_subst::{Subst, subst_lambda};

/// `Lam_exit_count.collection`: occurrence count per exit label
/// (lam_exit_count.ml:25).
pub type Collection = HashMap<i32, u32>;

/// `Lam_exit_count.count_exit` (lam_exit_count.ml:28).
pub fn count_exit(exits: &Collection, i: i32) -> u32 {
    *exits.get(&i).unwrap_or(&0)
}

struct CountResult {
    exits: Collection,
    has_static_catch: bool,
}

/// `Lam_exit_count.count_helper` (lam_exit_count.ml:51-110).
pub fn count_helper(a: &LamArena, lam: Lam) -> Collection {
    let mut result = CountResult {
        exits: HashMap::new(),
        has_static_catch: false,
    };
    count(a, &mut result, lam);
    result.exits
}

fn count(a: &LamArena, r: &mut CountResult, lam: Lam) {
    match a.node(lam) {
        // lam_exit_count.ml:55-57
        Node::StaticRaise { label, args } => {
            *r.exits.entry(label).or_insert(0) += 1;
            for x in a.list(args) {
                count(a, r, *x);
            }
        }
        // lam_exit_count.ml:58-60
        Node::StaticCatch {
            body,
            handler,
            info,
        } => {
            r.has_static_catch = true;
            count(a, r, body);
            if count_exit(&r.exits, a.catch_payload(info).label) > 0 {
                count(a, r, handler);
            }
        }
        // lam_exit_count.ml:70-72: body before value.
        Node::Let { value, body, .. } => {
            count(a, r, body);
            count(a, r, value);
        }
        // lam_exit_count.ml:77-81, 100-107: the default first, twice when
        // neither table is full.
        Node::Switch {
            scrut,
            actions,
            info,
        } => {
            let acts = a.switch_actions(info, actions);
            if let Some(fail) = acts.fail {
                let p = a.switch_payload(info);
                count(a, r, fail);
                if !p.consts_full && !p.blocks_full {
                    count(a, r, fail);
                }
            }
            count(a, r, scrut);
            for x in acts.consts.iter().chain(acts.blocks) {
                count(a, r, *x);
            }
        }
        _ => a.iter_children(lam, |x| count(a, r, x)),
    }
}

/// `Lam_pass_exits.no_bounded_variables` (lam_pass_exits.ml:32-58).
pub fn no_bounded_variables(a: &LamArena, lam: Lam) -> bool {
    let all = |xs: &[Lam]| xs.iter().all(|x| no_bounded_variables(a, *x));
    match a.node(lam) {
        Node::Var(_) | Node::Const(_) | Node::GlobalModule(_) | Node::Break | Node::Continue => {
            true
        }
        Node::Assign { value, .. } => no_bounded_variables(a, value),
        Node::Apply { func, args, .. } => no_bounded_variables(a, func) && all(a.list(args)),
        Node::Prim { args, .. } | Node::StaticRaise { args, .. } => all(a.list(args)),
        Node::Switch { scrut, actions, .. } | Node::StringSwitch { scrut, actions, .. } => {
            no_bounded_variables(a, scrut) && all(a.list(actions))
        }
        Node::If { cond, then_, else_ } => {
            no_bounded_variables(a, cond)
                && no_bounded_variables(a, then_)
                && no_bounded_variables(a, else_)
        }
        Node::Sequence(x, y) | Node::While(x, y) => {
            no_bounded_variables(a, x) && no_bounded_variables(a, y)
        }
        Node::StaticCatch {
            body,
            handler,
            info,
        } => {
            a.catch_payload(info).params.is_empty()
                && no_bounded_variables(a, body)
                && no_bounded_variables(a, handler)
        }
        Node::Function { body, info } => a.params(info).is_empty() && no_bounded_variables(a, body),
        Node::For { .. }
        | Node::ForOf { .. }
        | Node::ForAwaitOf { .. }
        | Node::TryWith { .. }
        | Node::TryFinally { .. }
        | Node::Let { .. } => false,
        Node::LetRec { values, body, .. } => {
            a.list_len(values) == 0 && no_bounded_variables(a, body)
        }
    }
}

/// `subst_tbl = (Ident.t list * lam_subst) Hash_int.t` (lam_pass_exits.ml:86).
type SubstTbl = HashMap<i32, (IdentSpan, Lam)>;

/// `Lam_pass_exits.subst_helper` (lam_pass_exits.ml:153-205).
fn subst_helper(
    a: &mut LamArena,
    subst: &mut SubstTbl,
    counts: &Collection,
    id_gen: &IdGenerator,
    lam: Lam,
) -> Lam {
    match a.node(lam) {
        // lam_pass_exits.ml:157-183
        Node::StaticCatch {
            body,
            handler,
            info,
        } => {
            let p = a.catch_payload(info);
            let i = p.label;
            let i_occur = count_exit(counts, i);
            if i_occur == 0 {
                return subst_helper(a, subst, counts, id_gen, body);
            }
            if matches!(a.node(handler), Node::Var(_) | Node::Const(_)) || (i_occur == 1 && i >= 0)
            {
                let handler = subst_helper(a, subst, counts, id_gen, handler);
                subst.insert(i, (p.params, handler));
                return subst_helper(a, subst, counts, id_gen, body);
            }
            let handler2 = subst_helper(a, subst, counts, id_gen, handler);
            // ok_to_inline (lam_pass_exits.ml:173-179)
            let ok_to_inline = i >= 0 && no_bounded_variables(a, handler2) && {
                let lam_size = size_upto(a, EXIT_INLINE_SIZE, handler2);
                (i_occur <= 2 && lam_size < EXIT_INLINE_SIZE) || lam_size < 5
            };
            if ok_to_inline {
                subst.insert(i, (p.params, handler2));
                subst_helper(a, subst, counts, id_gen, body)
            } else {
                let body2 = subst_helper(a, subst, counts, id_gen, body);
                if body2 == body && handler2 == handler {
                    lam
                } else {
                    a.static_catch_with(body2, info, handler2)
                }
            }
        }
        // lam_pass_exits.ml:184-203
        Node::StaticRaise { label, args } => {
            if a.list_len(args) == 0 {
                return match subst.get(&label) {
                    Some((_, handler)) => *handler,
                    None => lam,
                };
            }
            let (nargs, changed) =
                a.map_list(args, &mut |a, x| subst_helper(a, subst, counts, id_gen, x));
            let Some(&(xs, handler)) = subst.get(&label) else {
                return if changed {
                    a.static_raise_with(label, nargs)
                } else {
                    lam
                };
            };
            // Rename xs to fresh ys (lam_pass_exits.ml:193-197).
            let xs: smallvec::SmallVec<[Ident; 4]> = a.idents(xs).iter().copied().collect();
            let ys: smallvec::SmallVec<[Ident; 4]> = xs.iter().map(|x| x.rename(id_gen)).collect();
            let mut env: Subst = HashMap::new();
            for (x, y) in xs.iter().zip(&ys) {
                let v = a.var(*y);
                env.insert(*x, v);
            }
            let mut result = subst_lambda(a, &env, handler);
            let ls = a.list_vec(nargs);
            // fold_right2 ys ls' body (fun y l r -> Lambda.let_ Strict y l r)
            for (y, l) in ys.into_iter().zip(ls).rev() {
                result = a.let_(LetKind::Strict, y, l, result);
            }
            result
        }
        // lam_pass_exits.ml:204
        _ => a.shallow_map(lam, &mut |a, x| subst_helper(a, subst, counts, id_gen, x)),
    }
}

/// `Lam_pass_exits.simplify_exits` (lam_pass_exits.ml:241-243). Without a
/// static catch, `subst_helper` cannot record a substitution and rebuilds
/// nothing, so the input is the result.
pub fn simplify_exits(a: &mut LamArena, lam: Lam, id_gen: &IdGenerator) -> Lam {
    let mut result = CountResult {
        exits: HashMap::new(),
        has_static_catch: false,
    };
    count(a, &mut result, lam);
    if !result.has_static_catch {
        return lam;
    }
    let mut subst = SubstTbl::new();
    subst_helper(a, &mut subst, &result.exits, id_gen, lam)
}
