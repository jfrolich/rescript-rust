//! Direct port of `compiler/core/lam_pass_exits.ml` and
//! `compiler/core/lam_exit_count.ml`.
//!
//! Inlines/eliminates static exits ("catch / raise") in lambda IR, mirroring
//! OCaml's `Lam_pass_exits.simplify_exits` exactly. Each clause cites the
//! OCaml file and line number that justifies it.

use crate::lambda::lambda_traverse::{Mapped, shallow_map_sharing};
use ahash::AHashMap as HashMap;

use crate::context::IdGenerator;
use crate::ident::Ident;
use crate::lambda::lam_analysis::{EXIT_INLINE_SIZE, size_upto};
#[cfg(test)]
use crate::lambda::lam_beta_reduce::max_ident_stamp_in_lambda;
use crate::lambda::lam_compat::LetKind;
use crate::lambda::lam_subst::subst_lambda;
use crate::lambda::{Lambda, LambdaSwitch};

/// `Lam_exit_count.collection`: occurrence count per exit label
/// (lam_exit_count.ml:25).
pub type Collection = HashMap<i32, u32>;

/// `Lam_exit_count.count_exit` (lam_exit_count.ml:28).
pub fn count_exit(exits: &Collection, i: i32) -> u32 {
    *exits.get(&i).unwrap_or(&0)
}

fn incr_exit(exits: &mut Collection, i: i32) {
    *exits.entry(i).or_insert(0) += 1;
}

/// `Lam_exit_count.count_helper` (lam_exit_count.ml:51-110): single traversal
/// that builds the occurrence table. `Lstaticcatch` skips counting the
/// handler if the body has no occurrences of its label
/// (lam_exit_count.ml:58-60).
pub fn count_helper(lam: &Lambda) -> Collection {
    count_helper_with_catches(lam).exits
}

struct CountResult {
    exits: Collection,
    has_static_catch: bool,
}

fn count_helper_with_catches(lam: &Lambda) -> CountResult {
    let mut result = CountResult {
        exits: HashMap::new(),
        has_static_catch: false,
    };
    count(&mut result, lam);
    result
}

fn count(result: &mut CountResult, lam: &Lambda) {
    match lam {
        // lam_exit_count.ml:55-57
        Lambda::LstaticRaise(i, ls) => {
            incr_exit(&mut result.exits, *i);
            for l in ls {
                count(result, l);
            }
        }
        // lam_exit_count.ml:58-60
        Lambda::LstaticCatch(l1, (i, _), l2) => {
            result.has_static_catch = true;
            count(result, l1);
            if count_exit(&result.exits, *i) > 0 {
                count(result, l2);
            }
        }
        // lam_exit_count.ml:61-64
        Lambda::LstringSwitch(l, sw, d) => {
            count(result, l);
            for (_, body) in sw {
                count(result, body);
            }
            if let Some(d) = d {
                count(result, d);
            }
        }
        // lam_exit_count.ml:65
        Lambda::LglobalModule(_) | Lambda::Lvar(_) | Lambda::Lconst(_) => {}
        // lam_exit_count.ml:66-68
        Lambda::Lapply(apply) => {
            count(result, &apply.ap_func);
            for arg in &apply.ap_args {
                count(result, arg);
            }
        }
        // lam_exit_count.ml:69
        Lambda::Lfunction(func) => count(result, &func.body),
        // lam_exit_count.ml:70-72: count body before value (matches OCaml
        // ordering, which only matters for hash-collision iteration order).
        Lambda::Llet(_, _, l1, l2) => {
            count(result, l2);
            count(result, l1);
        }
        // lam_exit_count.ml:73-75
        Lambda::Lletrec(bindings, body) => {
            for (_, expr) in bindings {
                count(result, expr);
            }
            count(result, body);
        }
        // lam_exit_count.ml:76
        Lambda::Lprim(info) => {
            for arg in &info.args {
                count(result, arg);
            }
        }
        // lam_exit_count.ml:77-81 + count_default (lam_exit_count.ml:100-107)
        Lambda::Lswitch(l, sw) => {
            count_default(result, sw);
            count(result, l);
            for (_, body) in &sw.sw_consts {
                count(result, body);
            }
            for (_, body) in &sw.sw_blocks {
                count(result, body);
            }
        }
        // lam_exit_count.ml:82-84
        Lambda::LtryWith(l1, _, l2) => {
            count(result, l1);
            count(result, l2);
        }
        // lam_exit_count.ml:85-88
        Lambda::LifThenElse(l1, l2, l3) => {
            count(result, l1);
            count(result, l2);
            count(result, l3);
        }
        // lam_exit_count.ml:89-91
        Lambda::Lsequence(l1, l2) => {
            count(result, l1);
            count(result, l2);
        }
        // lam_exit_count.ml:92-94
        Lambda::Lwhile(l1, l2) => {
            count(result, l1);
            count(result, l2);
        }
        // lam_exit_count.ml:95-98
        Lambda::Lfor(_, l1, l2, _, l3) => {
            count(result, l1);
            count(result, l2);
            count(result, l3);
        }
        // lam_exit_count.ml after #7887: Lfor_of / Lfor_await_of.
        Lambda::Lfor_of(_, l1, l2) | Lambda::Lfor_await_of(_, l1, l2) => {
            count(result, l1);
            count(result, l2);
        }
        // lam_exit_count.ml:99
        Lambda::Lassign(_, l) => count(result, l),
        // OCaml `Lam_exit_count.count_helper` after #8348:
        // `Lbreak | Lcontinue -> ()`.
        Lambda::Lbreak | Lambda::Lcontinue => {}
    }
}

fn count_default(result: &mut CountResult, sw: &LambdaSwitch) {
    if let Some(failaction) = sw.sw_failaction.as_deref() {
        // lam_exit_count.ml:104-107: when the switch is not exhaustive, the
        // default is reached via either the consts or the blocks predicate,
        // so it gets counted twice.
        if !sw.sw_consts_full && !sw.sw_blocks_full {
            count(result, failaction);
            count(result, failaction);
        } else {
            count(result, failaction);
        }
    }
}

/// `Lam_pass_exits.no_bounded_variables` (lam_pass_exits.ml:32-58): conservative
/// check that the lambda contains no binding constructs. Used to gate
/// inlining of handlers without alpha-renaming.
pub fn no_bounded_variables(l: &Lambda) -> bool {
    match l {
        // lam_pass_exits.ml:34-35
        Lambda::Lvar(_) | Lambda::Lconst(_) => true,
        // lam_pass_exits.ml:36
        Lambda::Lassign(_, e) => no_bounded_variables(e),
        // lam_pass_exits.ml:37-38
        Lambda::Lapply(apply) => {
            no_bounded_variables(&apply.ap_func) && apply.ap_args.iter().all(no_bounded_variables)
        }
        // lam_pass_exits.ml:39
        Lambda::LglobalModule(_) => true,
        // lam_pass_exits.ml:40
        Lambda::Lprim(info) => info.args.iter().all(no_bounded_variables),
        // lam_pass_exits.ml:41-43
        Lambda::Lswitch(arg, sw) => {
            no_bounded_variables(arg)
                && sw.sw_consts.iter().all(|(_, x)| no_bounded_variables(x))
                && sw.sw_blocks.iter().all(|(_, x)| no_bounded_variables(x))
                && sw.sw_failaction.as_deref().is_none_or(no_bounded_variables)
        }
        // lam_pass_exits.ml:44-45
        Lambda::LstringSwitch(arg, cases, default) => {
            no_bounded_variables(arg)
                && cases.iter().all(|(_, x)| no_bounded_variables(x))
                && default.as_deref().is_none_or(no_bounded_variables)
        }
        // lam_pass_exits.ml:46
        Lambda::LstaticRaise(_, args) => args.iter().all(no_bounded_variables),
        // lam_pass_exits.ml:47-49
        Lambda::LifThenElse(e1, e2, e3) => {
            no_bounded_variables(e1) && no_bounded_variables(e2) && no_bounded_variables(e3)
        }
        // lam_pass_exits.ml:50
        Lambda::Lsequence(e1, e2) => no_bounded_variables(e1) && no_bounded_variables(e2),
        // lam_pass_exits.ml:51
        Lambda::Lwhile(e1, e2) => no_bounded_variables(e1) && no_bounded_variables(e2),
        // lam_pass_exits.ml:52-53
        Lambda::LstaticCatch(e1, (_, vars), e2) => {
            vars.is_empty() && no_bounded_variables(e1) && no_bounded_variables(e2)
        }
        // lam_pass_exits.ml:54
        Lambda::Lfunction(func) => func.params.is_empty() && no_bounded_variables(&func.body),
        // lam_pass_exits.ml:55-58
        Lambda::Lfor(_, _, _, _, _) => false,
        // lam_pass_exits.ml after #7887: for_of / for_await_of bind a variable, so false.
        Lambda::Lfor_of(_, _, _) | Lambda::Lfor_await_of(_, _, _) => false,
        Lambda::LtryWith(_, _, _) => false,
        Lambda::Llet(_, _, _, _) => false,
        Lambda::Lletrec(decl, body) => decl.is_empty() && no_bounded_variables(body),
        // OCaml `Lam_pass_exits.no_bounded_variables` after #8348:
        // `Lbreak | Lcontinue -> true`.
        Lambda::Lbreak | Lambda::Lcontinue => true,
    }
}

/// Substitution table value: bound vars + handler lambda.
/// (`subst_tbl = (Ident.t list * lam_subst) Hash_int.t` lam_pass_exits.ml:86)
type SubstTbl = HashMap<i32, (Vec<Ident>, Lambda)>;

/// `Lam_pass_exits.subst_helper` (compiler/core/lam_pass_exits.ml:153-205).
///
/// Returns the simplified lambda and whether it differs from the input,
/// standing in for OCaml's physical-equality checks: unchanged nodes are kept
/// as they are and every other node goes through
/// `Lambda_traverse.shallow_map_sharing`, which rebuilds through the smart
/// constructors only when a child changed.
fn subst_helper_owned(
    subst: &mut SubstTbl,
    counts: &Collection,
    id_gen: &IdGenerator,
    lam: Lambda,
) -> Mapped {
    match lam {
        // lam_pass_exits.ml:157-183: Lstaticcatch (l1, (i, xs), l2)
        Lambda::LstaticCatch(l1, (i, xs), l2) => {
            let i_occur = count_exit(counts, i);
            // (0, _) -> simplif l1
            if i_occur == 0 {
                return (subst_helper_owned(subst, counts, id_gen, *l1).0, true);
            }
            // (_, Lvar _) | (_, Lconst _) and (1, _) when i >= 0
            if matches!(l2.as_ref(), Lambda::Lvar(_) | Lambda::Lconst(_))
                || (i_occur == 1 && i >= 0)
            {
                let simplified_l2 = subst_helper_owned(subst, counts, id_gen, *l2).0;
                subst.insert(i, (xs, simplified_l2));
                return (subst_helper_owned(subst, counts, id_gen, *l1).0, true);
            }
            let (simplified_l2, c2) = subst_helper_owned(subst, counts, id_gen, *l2);
            // ok_to_inline (lam_pass_exits.ml:173-179)
            let ok_to_inline = if i >= 0 && no_bounded_variables(&simplified_l2) {
                let lam_size = size_upto(EXIT_INLINE_SIZE, &simplified_l2);
                (i_occur <= 2 && lam_size < EXIT_INLINE_SIZE) || lam_size < 5
            } else {
                false
            };
            if ok_to_inline {
                subst.insert(i, (xs, simplified_l2));
                (subst_helper_owned(subst, counts, id_gen, *l1).0, true)
            } else {
                let (l1, c1) = subst_helper_owned(subst, counts, id_gen, *l1);
                (Lambda::static_catch(l1, i, xs, simplified_l2), c1 || c2)
            }
        }
        // lam_pass_exits.ml:184-187: Lstaticraise (i, [])
        Lambda::LstaticRaise(i, ls) if ls.is_empty() => match subst.get(&i) {
            Some((_, handler)) => (handler.clone(), true),
            None => (Lambda::LstaticRaise(i, ls), false),
        },
        // lam_pass_exits.ml:188-203: Lstaticraise (i, ls)
        Lambda::LstaticRaise(i, ls) => {
            let mut changed = false;
            let ls: Vec<Lambda> = ls
                .into_iter()
                .map(|l| {
                    let (l, c) = subst_helper_owned(subst, counts, id_gen, l);
                    changed |= c;
                    l
                })
                .collect();
            if let Some((xs, handler)) = subst.get(&i) {
                // Rename xs to fresh ys (lam_pass_exits.ml:193-197).
                let ys: Vec<Ident> = xs.iter().map(|x| x.rename(id_gen)).collect();
                let mut env = HashMap::new();
                for (x, y) in xs.iter().zip(ys.iter()) {
                    env.insert(*x, Lambda::Lvar(*y));
                }
                let body = subst_lambda(&env, handler.clone());
                // fold_right2 ys ls' body (fun y l r -> Lambda.let_ Strict y l r)
                let mut result = body;
                for (y, l) in ys.into_iter().zip(ls.into_iter()).rev() {
                    result = Lambda::let_(LetKind::Strict, y, l, result);
                }
                (result, true)
            } else if changed {
                (Lambda::static_raise(i, ls), true)
            } else {
                (Lambda::LstaticRaise(i, ls), false)
            }
        }
        // lam_pass_exits.ml:204
        lam => shallow_map_sharing(lam, &mut |inner| {
            subst_helper_owned(subst, counts, id_gen, inner)
        }),
    }
}

/// `Lam_pass_exits.simplify_exits` (lam_pass_exits.ml:241-243).
///
/// Uses `id_gen` for the `Ident.rename` calls in the `Lstaticraise` arm
/// (lam_pass_exits.ml:193). OCaml's `Ident.rename` reads from a single
/// global mutable counter, so the caller should thread a pipeline-wide
/// `IdGenerator` to avoid collisions with later beta-reduction renames.
pub fn simplify_exits(lam: &Lambda, id_gen: &IdGenerator) -> Lambda {
    simplify_exits_owned(lam.clone(), id_gen)
}

/// Owned variant of `Lam_pass_exits.simplify_exits` (lam_pass_exits.ml:241-243).
///
/// If there is no `Lstaticcatch`, `subst_helper` cannot insert a substitution
/// entry (lam_pass_exits.ml:157-183), and every later arm only rebuilds the
/// same constructors while preserving `Lstaticraise` nodes (lam_pass_exits.ml:
/// 184-239). Returning the owned input in that case is therefore the same
/// transformation without a full-tree clone.
pub fn simplify_exits_owned(lam: Lambda, id_gen: &IdGenerator) -> Lambda {
    // OCaml always starts with `Lam_exit_count.count_helper` and then
    // `subst_helper` (lam_pass_exits.ml:241-243). Rust keeps the owned
    // no-catch fast path, but records that invariant while doing the same
    // counting walk (lam_exit_count.ml:51-110) instead of running a separate
    // pre-scan that OCaml does not have.
    let CountResult {
        exits,
        has_static_catch,
    } = count_helper_with_catches(&lam);
    if !has_static_catch {
        return lam;
    }
    let mut subst: SubstTbl = HashMap::new();
    subst_helper_owned(&mut subst, &exits, id_gen, lam).0
}

/// Standalone entry point that seeds its own `IdGenerator` from the lambda's
/// max stamp — used by tests that don't have a pipeline-level counter.
#[cfg(test)]
pub fn simplify_exits_standalone(lam: &Lambda) -> Lambda {
    let id_gen = IdGenerator::with_start_stamp(max_ident_stamp_in_lambda(lam));
    simplify_exits(lam, &id_gen)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lambda::lam_compat::LetKind;

    #[test]
    fn unused_catch_dropped() {
        // catch <body without raise 1> with (1) <handler> => body
        let body = Lambda::unit();
        let handler = Lambda::true_();
        let lam = Lambda::LstaticCatch(Box::new(body.clone()), (1, vec![]), Box::new(handler));
        let simplified = simplify_exits_standalone(&lam);
        assert!(
            simplified.is_unit(),
            "expected unit body, got {simplified:?}"
        );
    }

    #[test]
    fn single_use_catch_inlined() {
        // catch (raise 1) with (1) Lconst true => Lconst true
        let raise = Lambda::LstaticRaise(1, vec![]);
        let handler = Lambda::true_();
        let lam = Lambda::LstaticCatch(Box::new(raise), (1, vec![]), Box::new(handler.clone()));
        let simplified = simplify_exits_standalone(&lam);
        assert!(matches!(
            simplified,
            Lambda::Lconst(crate::lambda::Constant::JsTrue)
        ));
    }

    #[test]
    fn raise_with_arg_substitutes_let() {
        // catch (raise 1 [Lconst 7]) with (1 x) Lvar x => let x' = 7 in Lvar x'
        let x = Ident::create_local("x");
        let raise = Lambda::LstaticRaise(1, vec![Lambda::Lconst(crate::lambda::Constant::int(7))]);
        let handler = Lambda::Lvar(x);
        let lam = Lambda::LstaticCatch(Box::new(raise), (1, vec![x]), Box::new(handler));
        let simplified = simplify_exits_standalone(&lam);
        match simplified {
            Lambda::Llet(LetKind::Strict, _, _, body) => {
                assert!(matches!(*body, Lambda::Lvar(_)));
            }
            other => panic!("expected let, got {:?}", other),
        }
    }
}
