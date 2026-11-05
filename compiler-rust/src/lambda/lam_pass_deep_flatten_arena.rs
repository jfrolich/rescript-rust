//! `Lam_pass_deep_flatten.deep_flatten` over the Lambda arena.
//!
//! Flattens nested `let` chains and pulls the fields of named immutable
//! blocks out into single bindings.

use ahash::AHashMap as HashMap;

use crate::context::IdGenerator;
use crate::ident::Ident;
use crate::lambda::arena::{IdentId, Lam, LamArena, LamList, Node};
use crate::lambda::lam_compat::LetKind;
use crate::lambda::lam_hit_arena::hit_variable;
use crate::lambda::lam_primitive::{Mutable, Primitive};
use crate::lambda::lam_util_arena::{refine_let, refine_let_original};
use crate::lambda::LamLoc;

enum Group {
    Single(LetKind, Ident, Lam),
    Recursive(IdentId, LamList),
    Nop(Lam),
}

/// `Lam_pass_deep_flatten.deep_flatten`
/// (compiler/core/lam_pass_deep_flatten.ml:96-266), with the caller's
/// `Ident.currentstamp`.
pub fn deep_flatten(a: &mut LamArena, lam: Lam, id_gen: &IdGenerator) -> Lam {
    aux(a, lam, id_gen)
}

/// lam_pass_deep_flatten.ml:108: fold the groups back through
/// `Lam_util.refine_let`, last group innermost.
fn lambda_of_groups(a: &mut LamArena, groups: Vec<Group>, result: Lam) -> Lam {
    groups
        .into_iter()
        .rev()
        .fold(result, |acc, group| match group {
            Group::Single(kind, id, lam) => refine_let(a, kind, id, lam, acc),
            Group::Recursive(ids, values) => a.letrec_with(ids, values, acc),
            Group::Nop(lam) => a.seq(lam, acc),
        })
}

/// `let projected = Pfield(i, tuple)` chains at the head of `lam`, if `id`
/// occurs nowhere after them (lam_pass_deep_flatten.ml:31-34).
fn eliminate_tuple(a: &LamArena, id: &Ident, mut lam: Lam) -> Option<(HashMap<i32, Ident>, Lam)> {
    let mut mapping = HashMap::new();
    loop {
        if let Node::Let {
            kind: LetKind::Alias,
            id: projected,
            value,
            body,
        } = a.node(lam)
            && let Some((Primitive::Pfield(index, _), [tuple], _)) = a.as_prim(value)
            && a.as_var(*tuple).is_some_and(|t| t.same(id))
        {
            mapping.insert(*index, a.ident(projected));
            lam = body;
            continue;
        }
        return if hit_variable(a, id, lam) {
            None
        } else {
            Some((mapping, lam))
        };
    }
}

/// `let x = <immutable block or variable> in ... in apply f args`: the
/// residue of beta-reducing an immediately applied function.
fn rhs_is_beta_residue(a: &LamArena, lam: Lam) -> bool {
    match a.node(lam) {
        Node::Let {
            kind: LetKind::Alias | LetKind::Strict | LetKind::StrictOpt,
            value,
            body,
            ..
        } if matches!(
            a.as_prim(value),
            Some((Primitive::Pmakeblock(_, Mutable::Immutable), _, _))
        ) || matches!(a.node(value), Node::Var(_)) =>
        {
            rhs_is_beta_residue(a, body)
        }
        Node::Apply { .. } => true,
        _ => false,
    }
}

/// lam_pass_deep_flatten.ml `regroups_binding`: whether `flatten`
/// restructures this binding.
fn regroups_binding(a: &LamArena, kind: LetKind, id: &Ident, arg: Lam) -> bool {
    if rhs_is_beta_residue(a, arg) {
        return false;
    }
    match a.node(arg) {
        Node::Let { .. } | Node::Sequence(..) | Node::LetRec { .. } => true,
        Node::Prim { .. } => match a.as_prim(arg).expect("checked primitive") {
            (Primitive::PnullToOpt | Primitive::PnullUndefinedToOpt, args, _) => {
                !matches!(args, [x] if matches!(a.node(*x), Node::Var(_)))
            }
            (Primitive::Pmakeblock(_, Mutable::Immutable), _, _) => {
                matches!(id.name(), "match" | "include" | "param")
                    && matches!(kind, LetKind::Alias | LetKind::Strict | LetKind::StrictOpt)
            }
            _ => false,
        },
        _ => false,
    }
}

fn flatten(a: &mut LamArena, acc: &mut Vec<Group>, mut lam: Lam, id_gen: &IdGenerator) -> Lam {
    loop {
        match a.node(lam) {
            Node::Let {
                kind,
                id,
                value,
                body,
            } if rhs_is_beta_residue(a, value) => {
                // Keep beta-reduction residue local so `Lam_pass_lets_dce`
                // can substitute its single-use arguments back into the call.
                let value = aux(a, value, id_gen);
                acc.push(Group::Single(kind, a.ident(id), value));
                lam = body;
            }
            Node::Let {
                kind,
                id: id_ref,
                value,
                body,
            } => {
                let id = a.ident(id_ref);
                if let Node::Prim { args, info } = a.node(value)
                    && matches!(
                        a.prim_payload(info).primitive,
                        Primitive::PnullToOpt | Primitive::PnullUndefinedToOpt
                    )
                    && let [arg] = a.list(args)
                {
                    let arg = *arg;
                    if matches!(a.node(arg), Node::Var(_)) {
                        let res = aux(a, value, id_gen);
                        acc.push(Group::Single(kind, id, res));
                        lam = body;
                        continue;
                    }
                    // lam_pass_deep_flatten.ml:126-141 uses `Ident.rename id`
                    // from the shared stamp source.
                    let new_id = id.rename(id_gen);
                    let primitive = a.prim_payload(info).primitive.clone();
                    let v = a.var(new_id);
                    let wrapped = a.prim(primitive, &[v], LamLoc::NONE);
                    let inner = a.let_(LetKind::Alias, id, wrapped, body);
                    lam = a.let_(kind, new_id, arg, inner);
                    continue;
                }
                let res = flatten(a, acc, value, id_gen);
                let named_module_block = matches!(id.name(), "match" | "include" | "param")
                    && matches!(kind, LetKind::Alias | LetKind::Strict | LetKind::StrictOpt)
                    && matches!(
                        a.as_prim(res),
                        Some((Primitive::Pmakeblock(_, Mutable::Immutable), _, _))
                    );
                if named_module_block
                    && let Some((mapping, stripped)) = eliminate_tuple(a, &id, body)
                {
                    let (_, args, _) = a.as_prim(res).expect("checked block");
                    for (index, arg) in args.iter().enumerate() {
                        acc.push(match mapping.get(&(index as i32)) {
                            Some(projected) => Group::Single(kind, *projected, *arg),
                            None => Group::Nop(*arg),
                        });
                    }
                    lam = stripped;
                    continue;
                }
                acc.push(Group::Single(kind, id, res));
                lam = body;
            }
            Node::LetRec { ids, values, body } => {
                let (values, _) = a.map_list(values, &mut |a, x| aux(a, x, id_gen));
                acc.push(Group::Recursive(ids, values));
                lam = body;
            }
            Node::Sequence(first, second) => {
                let res = flatten(a, acc, first, id_gen);
                // `Lam_group.nop_cons` drops pure heads (lam_group.ml:36-39).
                if !matches!(
                    a.node(res),
                    Node::Var(_) | Node::Const(_) | Node::Function { .. }
                ) {
                    acc.push(Group::Nop(res));
                }
                lam = second;
            }
            _ => return aux(a, lam, id_gen),
        }
    }
}

/// lam_pass_deep_flatten.ml `aux`: `let`/`let rec` are regrouped, every other
/// node goes through `shallow_map_sharing`.
fn aux(a: &mut LamArena, lam: Lam, id_gen: &IdGenerator) -> Lam {
    match a.node(lam) {
        // `Lam_util.refine_let ~original:lam ~kind:str id (aux arg) (aux body)`;
        // OCaml evaluates the arguments right to left.
        Node::Let {
            kind,
            id,
            value,
            body,
        } if !regroups_binding(a, kind, &a.ident(id), value) => {
            let body = aux(a, body, id_gen);
            let value = aux(a, value, id_gen);
            let id = a.ident(id);
            refine_let_original(a, lam, kind, id, value, body)
        }
        Node::Let { .. } => {
            let mut groups = Vec::new();
            let result = flatten(a, &mut groups, lam, id_gen);
            lambda_of_groups(a, groups, result)
        }
        Node::LetRec { ids, values, body } => {
            let (nvalues, changed) = a.map_list(values, &mut |a, x| aux(a, x, id_gen));
            let nbody = aux(a, body, id_gen);
            if !changed && nbody == body {
                lam
            } else {
                a.letrec_with(ids, nvalues, nbody)
            }
        }
        _ => a.shallow_map(lam, &mut |a, x| aux(a, x, id_gen)),
    }
}
