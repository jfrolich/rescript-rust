//! `lam_pass_deep_flatten.rs`: the first diagnostic-only level L round.
//! The explicit continuations below are the `aux`/`flatten` call stack;
//! groups belong to one invocation of `flatten`, not to the whole sweep.
use crate::bir::engine::{Changed, Engine, Facts, OpMask, Order, Round};
use crate::bir::*;
use crate::lambda::LamLoc;
use crate::lambda::lam_compat::FieldDbgInfo;
use crate::lambda::lam_primitive::{Mutable, Primitive};
use std::collections::BTreeMap;

/// `aux` matches lets and recursive groups (legacy lines 222-252); sequences
/// are candidates only while `flatten` threads groups through them (198-210).
/// The stateful order preserves body-before-value in ordinary lets (230-231),
/// value-before-body while regrouping (164), and left-to-right shallow_map.
/// Rebuilds use shallow_map's constructors, including if/seq in today's code.
/// No ident_tbl is read and no old subtree is read after an edit: current
/// facts, no snapshots. `rule` is unused by the stateful driver.
pub static FLATTEN: Round = Round {
    name: "deep_flatten",
    mask: OpMask::LET.or(OpMask::LETREC),
    order: Order::Stateful(run),
    renorm: OpMask::SHALLOW_MAP.or(OpMask::IF).or(OpMask::SEQ),
    facts: Facts::Current,
    guard: None,
    rule: |_, _| Changed::No,
};

// Release the old binding shell only after its kept children were detached.
// The placeholder owns no variables; the final fill retains the root handle.
fn vacate(e: &mut Engine<'_>, n: NodeId) {
    let value = e.intern_const(Constant::Undefined(true));
    e.put(n, View::Const { value }, 0);
}

fn fired(e: &mut Engine<'_>, name: &'static str) {
    *e.stats.rules.entry(name).or_default() += 1;
}
fn immutable(b: &Bir, n: NodeId) -> bool {
    matches!(b.view(n), View::Prim { primitive, .. }
        if matches!(b.primitive(primitive).primitive, Primitive::Pmakeblock(_, Mutable::Immutable)))
}
fn variable(b: &Bir, n: NodeId, var: VarId) -> bool {
    matches!(b.view(n), View::Var { var: v } if v == var)
}

/// Legacy `rhs_is_beta_residue`, lines 75-94 (OCaml's beta residue guard).
/// Compute once, bottom-up: testing each suffix of a 10,000-let residue by
/// walking it would be quadratic. The decisions concern untouched inputs.
fn beta_table(e: &Engine<'_>, root: NodeId) -> Vec<bool> {
    let mut out = Vec::new();
    let mut work = vec![(root, false)];
    while let Some((n, done)) = work.pop() {
        if !done && !e.summary(n).intersects(OpMask::LET) {
            out.resize(out.len().max(n.index() + 1), false);
            out[n.index()] = e.bir().node(n).op() == Op::Apply;
            continue;
        }
        if !done {
            work.push((n, true));
            work.extend(e.bir().view(n).children().into_iter().map(|c| (c, false)));
            continue;
        }
        out.resize(out.len().max(n.index() + 1), false);
        out[n.index()] = match e.bir().view(n) {
            View::Apply { .. } => true,
            View::Let {
                value: Some(v),
                body,
                ..
            } => {
                e.bir().node(n).aux() <= 2
                    && (immutable(e.bir(), v) || e.bir().node(v).op() == Op::Var)
                    && out[body.index()]
            }
            _ => false,
        };
    }
    out
}

/// Legacy `regroups_binding`, lines 98-120; OCaml regroups_binding.
fn regroups(e: &Engine<'_>, n: NodeId, beta: &[bool]) -> bool {
    let View::Let {
        var,
        value: Some(v),
        ..
    } = e.bir().view(n)
    else {
        return false;
    };
    if beta.get(v.index()).copied().unwrap_or(false) {
        return false;
    }
    match e.bir().view(v) {
        View::Let { .. } | View::LetRec { .. } | View::Seq { .. } => true,
        View::Prim { args, primitive } => match &e.bir().primitive(primitive).primitive {
            Primitive::PnullToOpt | Primitive::PnullUndefinedToOpt => {
                !matches!(args, [x] if e.bir().node(*x).op() == Op::Var)
            }
            Primitive::Pmakeblock(_, Mutable::Immutable) => named(e, n, var),
            _ => false,
        },
        _ => false,
    }
}
fn named(e: &Engine<'_>, n: NodeId, var: VarId) -> bool {
    e.bir().node(n).aux() <= 2
        && matches!(
            e.bir().vars().name(var).as_str(),
            "match" | "include" | "param"
        )
}

/// Legacy `Lam_hit.hit_variable`, used by eliminate_tuple (lines 62-66)
/// and refine_let (lam_util.rs:110-115). A candidate scan, not a whole-unit
/// fact. Assignment targets count as occurrences too.
fn hit(e: &Engine<'_>, root: NodeId, var: VarId) -> bool {
    let mut work = vec![root];
    while let Some(n) = work.pop() {
        match e.bir().view(n) {
            View::Var { var: v } | View::Assign { var: v, .. } if v == var => return true,
            _ => work.extend(e.bir().view(n).children()),
        }
    }
    false
}

/// Legacy eliminate_tuple, lines 45-70; lam_pass_deep_flatten.ml:31-34.
/// Ordered map lookup only; duplicate indices retain the last projection.
fn eliminate_tuple(
    e: &Engine<'_>,
    var: VarId,
    mut body: NodeId,
) -> Option<(BTreeMap<i32, VarId>, NodeId)> {
    let mut mapping = BTreeMap::new();
    loop {
        if let View::Let {
            var: projected,
            value: Some(value),
            body: next,
        } = e.bir().view(body)
            && e.bir().node(body).aux() == 1
            && let View::Prim {
                args: [tuple],
                primitive,
            } = e.bir().view(value)
            && let Primitive::Pfield(index, _) = e.bir().primitive(primitive).primitive
            && variable(e.bir(), *tuple, var)
        {
            mapping.insert(index, projected);
            body = next;
            continue;
        }
        return (!hit(e, body, var)).then_some((mapping, body));
    }
}

/// Legacy is_safe_to_alias (lam_util.rs:15-32; lam_util.ml:79-98).
fn safe_alias(e: &Engine<'_>, mut n: NodeId) -> bool {
    loop {
        match e.bir().view(n) {
            View::Var { .. } | View::Const { .. } => return true,
            View::Prim { args, primitive } => match (&e.bir().primitive(primitive).primitive, args)
            {
                (Primitive::Ptemplate(segments), []) => return segments.len() == 1,
                (Primitive::Pfield(_, FieldDbgInfo::Module { .. }), [x]) => {
                    return matches!(e.bir().node(*x).op(), Op::Global | Op::Var);
                }
                (Primitive::PsomeNotNest, [x]) => n = *x,
                _ => return false,
            },
            _ => return false,
        }
    }
}

/// Legacy no_side_effects, lam_analysis.rs:215-265. Bir PURE is deliberately
/// more conservative; using it here would retain Strict instead of StrictOpt.
fn pure(e: &Engine<'_>, root: NodeId) -> bool {
    use crate::lambda::lam_constant::Constant as C;
    let mut work = vec![root];
    while let Some(n) = work.pop() {
        match e.bir().view(n) {
            View::Var { .. } | View::Const { .. } | View::Fun { .. } | View::Global { .. } => {
                continue;
            }
            View::Prim { args, primitive } => {
                let second = args.get(1).and_then(|n| match e.bir().view(*n) {
                    View::Const { value } => match e.bir().constant(value) {
                        Constant::Int(i)
                        | Constant::DecoratedInt {
                            value: i,
                            native: false,
                            ..
                        } => Some(C::int(*i as i32)),
                        Constant::NativeInt(i)
                        | Constant::DecoratedInt {
                            value: i,
                            native: true,
                            ..
                        } => Some(C::NativeInt {
                            i: *i,
                            comment: None,
                        }),
                        Constant::BigInt(s) => {
                            let text = e.bir().text(*s);
                            Some(C::BigInt {
                                negative: text.starts_with('-'),
                                value: text.trim_start_matches(['-', '+']).to_owned(),
                            })
                        }
                        _ => None,
                    },
                    _ => None,
                });
                if !crate::lambda::lam_analysis::is_pure_primitive(
                    &e.bir().primitive(primitive).primitive,
                    second.as_ref(),
                ) {
                    return false;
                }
            }
            View::Let { .. }
            | View::LetRec { .. }
            | View::Try { .. }
            | View::TryFinally { .. }
            | View::If { .. }
            | View::Seq { .. } => {}
            _ => return false,
        }
        work.extend(e.bir().view(n).children());
    }
    true
}

/// Legacy refine_let_parts, lam_util.rs:66-140 (lam_util.ml:68-138).
fn refine(e: &mut Engine<'_>, n: NodeId) -> Changed {
    let View::Let {
        var,
        value: Some(value),
        body,
    } = e.bir().view(n)
    else {
        return Changed::No;
    };
    if variable(e.bir(), body, var) {
        e.promote(n, value);
        fired(e, "refine-return");
        return Changed::Yes;
    }
    match e.bir().view(body) {
        View::Prim {
            args: [arg],
            primitive,
        } if variable(e.bir(), *arg, var)
            && !matches!(
                e.bir().primitive(primitive).primitive,
                Primitive::Pmakeblock(..) | Primitive::Pjsx(_)
            ) =>
        {
            e.detach(value);
            e.put(
                n,
                View::Prim {
                    args: &[value],
                    primitive,
                },
                0,
            );
            e.normalise(n);
            fired(e, "refine-prim");
            return Changed::Yes;
        }
        View::Apply {
            callee,
            args: [arg],
            info,
        } if variable(e.bir(), *arg, var) && !hit(e, callee, var) => {
            e.detach(value);
            e.detach(callee);
            e.put(
                n,
                View::Apply {
                    callee,
                    args: &[value],
                    info,
                },
                0,
            );
            fired(e, "refine-call");
            return Changed::Yes;
        }
        _ => {}
    }
    let kind = e.bir().node(n).aux();
    let next = if matches!(kind, 0 | 2) && safe_alias(e, value) {
        1
    } else if kind == 0 && pure(e, value) {
        2
    } else {
        kind
    };
    if next == kind {
        return Changed::No;
    }
    e.detach(value);
    e.detach(body);
    vacate(e, n);
    e.put(
        n,
        View::Let {
            var,
            value: Some(value),
            body,
        },
        next,
    );
    fired(e, "refine-kind");
    Changed::Yes
}

enum Group {
    Single(u16, VarId, NodeId),
    Recursive(VarId, Vec<NodeId>),
    Nop(NodeId),
}
enum Work {
    Aux(NodeId),
    Finish(NodeId, u64, bool),
    Flat(NodeId, usize),
    Return(NodeId),
    Binding(NodeId, NodeId, usize, bool),
    Rec(NodeId, usize),
    Sequence(NodeId, usize),
    Fold(NodeId, usize),
}

/// Null conversion arm, legacy lines 142-162; OCaml:126-141. Allocate the
/// rename before entering its argument, and keep the shared counter order.
fn null_binding(e: &mut Engine<'_>, n: NodeId, beta: &mut Vec<bool>) -> bool {
    let View::Let {
        var,
        value: Some(value),
        body,
    } = e.bir().view(n)
    else {
        return false;
    };
    let View::Prim {
        args: [arg],
        primitive,
    } = e.bir().view(value)
    else {
        return false;
    };
    let arg = *arg;
    let p = &e.bir().primitive(primitive).primitive;
    if !matches!(p, Primitive::PnullToOpt | Primitive::PnullUndefinedToOpt)
        || e.bir().node(arg).op() == Op::Var
    {
        return false;
    }
    let primitive = e.intern_prim(p.clone(), LamLoc::NONE);
    let kind = e.bir().node(n).aux();
    let weight = e.weight(n);
    let fresh = e.rename_var(var);
    e.detach(arg);
    e.detach(body);
    vacate(e, n);
    let v = e.node(View::Var { var: fresh }, 0, weight);
    let wrapped = e.node(
        View::Prim {
            args: &[v],
            primitive,
        },
        0,
        weight,
    );
    let inner = e.node(
        View::Let {
            var,
            value: Some(wrapped),
            body,
        },
        1,
        weight,
    );
    // Allocation reuses freed slots. Never interpret a new primitive's slot
    // as the beta-residue decision of its previous occupant.
    for created in [v, wrapped, inner] {
        beta.resize(beta.len().max(created.index() + 1), false);
        beta[created.index()] = false;
    }
    e.put(
        n,
        View::Let {
            var: fresh,
            value: Some(arg),
            body: inner,
        },
        kind,
    );
    fired(e, "null-binding");
    true
}

/// Flatten's named block arm, legacy lines 165-187 (OCaml:142-213).
fn block_binding(
    e: &mut Engine<'_>,
    n: NodeId,
    value: NodeId,
    groups: &mut Vec<Group>,
) -> Option<NodeId> {
    let View::Let { var, body, .. } = e.bir().view(n) else {
        unreachable!()
    };
    if !named(e, n, var) || !immutable(e.bir(), value) {
        return None;
    }
    let (mapping, stripped) = eliminate_tuple(e, var, body)?;
    let View::Prim { args, .. } = e.bir().view(value) else {
        unreachable!()
    };
    let args = args.to_vec();
    let kind = e.bir().node(n).aux();
    for (i, arg) in args.into_iter().enumerate() {
        e.detach(arg);
        groups.push(match mapping.get(&(i as i32)) {
            Some(var) => Group::Single(kind, *var, arg),
            None => Group::Nop(arg),
        });
    }
    e.release(value);
    fired(e, "named-block");
    Some(stripped)
}

/// Legacy lambda_of_groups, lines 32-41 (OCaml:108). Each group is folded
/// once. Detached children retain their original use weight.
fn fold(e: &mut Engine<'_>, root: NodeId, groups: Vec<Group>, mut result: NodeId) {
    let weight = e.weight(root);
    vacate(e, root);
    for group in groups.into_iter().rev() {
        result = match group {
            Group::Single(kind, var, value) => {
                let n = e.node(
                    View::Let {
                        var,
                        value: Some(value),
                        body: result,
                    },
                    kind,
                    weight,
                );
                refine(e, n);
                n
            }
            Group::Recursive(first, values) => e.node(
                View::LetRec {
                    first,
                    values: &values,
                    body: result,
                },
                0,
                weight,
            ),
            Group::Nop(first) => {
                let n = e.node(
                    View::Seq {
                        first,
                        second: result,
                    },
                    0,
                    weight,
                );
                e.normalise(n);
                n
            }
        };
    }
    e.fill(root, result);
}

/// aux's non-regrouping let arm, legacy:222-234; OCaml:96-266.
fn aux_binding(work: &mut Vec<Work>, n: NodeId, value: NodeId, body: NodeId, revision: u64) {
    work.push(Work::Finish(n, revision, true));
    work.push(Work::Aux(value));
    work.push(Work::Aux(body));
}

/// aux's regrouping let arm, legacy:235-239; OCaml:96-266.
fn aux_regroup(work: &mut Vec<Work>, groups: &mut Vec<Vec<Group>>, n: NodeId) {
    let index = groups.len();
    groups.push(Vec::new());
    work.push(Work::Fold(n, index));
    work.push(Work::Flat(n, index));
}

/// aux's let-rec arm, legacy:240-249; OCaml:96-266.
fn aux_recursive(e: &Engine<'_>, work: &mut Vec<Work>, n: NodeId, revision: u64) {
    aux_shallow(e, work, n, revision);
}

/// aux's shallow_map arm, legacy:250; OCaml:96-266.
fn aux_shallow(e: &Engine<'_>, work: &mut Vec<Work>, n: NodeId, revision: u64) {
    work.push(Work::Finish(n, revision, false));
    work.extend(e.bir().view(n).children().into_iter().rev().map(Work::Aux));
}

/// flatten's beta-residue arm, legacy:127-138; OCaml beta residue guard.
fn flatten_residue(e: &mut Engine<'_>, work: &mut Vec<Work>, value: NodeId) {
    fired(e, "beta-residue");
    work.push(Work::Return(value));
    work.push(Work::Aux(value));
}

/// flatten's ordinary let arm, legacy:139-190; OCaml:126-213.
fn flatten_binding(work: &mut Vec<Work>, value: NodeId, index: usize) {
    work.push(Work::Flat(value, index));
}

/// flatten's recursive arm, legacy:192-197; OCaml:96-266.
fn flatten_recursive(work: &mut Vec<Work>, n: NodeId, values: &[NodeId], index: usize) {
    work.push(Work::Rec(n, index));
    work.extend(values.iter().rev().copied().map(Work::Aux));
}

/// flatten's sequence arm, legacy:198-210; lam_group.ml:36-39.
fn flatten_sequence(work: &mut Vec<Work>, first: NodeId, second: NodeId, index: usize) {
    work.push(Work::Sequence(second, index));
    work.push(Work::Flat(first, index));
}

/// flatten's terminal arm, legacy:211; OCaml:96-266.
fn flatten_terminal(work: &mut Vec<Work>, n: NodeId) {
    work.push(Work::Return(n));
    work.push(Work::Aux(n));
}

/// Stateful, nonrecursive translation of aux (legacy lines 219-255;
/// OCaml:96-266). Ordinary lets visit body then value; flatten visits value
/// then body while carrying groups; recursive values and shallow-map children
/// retain their source order. No two whole-tree Pre/Post sweeps can reproduce
/// both orders and the time at which a null conversion allocates its rename.
fn run(e: &mut Engine<'_>, root: NodeId) -> Changed {
    let mut beta = beta_table(e, root);
    let mut work = vec![Work::Aux(root)];
    let mut groups: Vec<Vec<Group>> = Vec::new();
    let mut result = root;
    let mut revision = 0;
    while let Some(task) = work.pop() {
        match task {
            Work::Aux(n) => {
                if !e.enter_candidate(n, FLATTEN.mask) {
                    continue;
                }
                match e.bir().view(n) {
                    View::Let {
                        value: Some(value),
                        body,
                        ..
                    } if !regroups(e, n, &beta) => {
                        aux_binding(&mut work, n, value, body, revision);
                    }
                    View::Let { .. } => {
                        aux_regroup(&mut work, &mut groups, n);
                    }
                    View::LetRec { .. } => aux_recursive(e, &mut work, n, revision),
                    _ => aux_shallow(e, &mut work, n, revision),
                }
            }
            Work::Finish(n, before, is_let) => {
                if is_let {
                    if refine(e, n) == Changed::Yes {
                        revision += 1;
                    }
                } else if before != revision
                    && FLATTEN.renorm.intersects(OpMask::of(e.bir().node(n).op()))
                {
                    if e.normalise(n) == Changed::Yes {
                        revision += 1;
                    }
                }
                e.finish_candidate(n);
            }
            Work::Flat(n, index) => {
                e.stats.entered += 1;
                match e.bir().view(n) {
                    View::Let {
                        value: Some(value),
                        body,
                        ..
                    } => {
                        let residue = beta.get(value.index()).copied().unwrap_or(false);
                        if !residue && null_binding(e, n, &mut beta) {
                            revision += 1;
                            work.push(Work::Flat(n, index));
                            continue;
                        }
                        work.push(Work::Binding(n, body, index, residue));
                        if residue {
                            flatten_residue(e, &mut work, value);
                        } else {
                            flatten_binding(&mut work, value, index);
                        }
                    }
                    View::LetRec { values, .. } => {
                        flatten_recursive(&mut work, n, values, index);
                    }
                    View::Seq { first, second } => {
                        flatten_sequence(&mut work, first, second, index);
                    }
                    _ => flatten_terminal(&mut work, n),
                }
            }
            Work::Return(n) => {
                e.detach(n);
                result = n;
            }
            Work::Binding(n, body, index, residue) => {
                if !residue && let Some(stripped) = block_binding(e, n, result, &mut groups[index])
                {
                    work.push(Work::Flat(stripped, index));
                } else {
                    let View::Let { var, .. } = e.bir().view(n) else {
                        unreachable!()
                    };
                    groups[index].push(Group::Single(e.bir().node(n).aux(), var, result));
                    fired(e, "binding");
                    work.push(Work::Flat(body, index));
                }
            }
            Work::Rec(n, index) => {
                let View::LetRec {
                    first,
                    values,
                    body,
                } = e.bir().view(n)
                else {
                    unreachable!()
                };
                let values = values.to_vec();
                for &v in &values {
                    e.detach(v);
                }
                groups[index].push(Group::Recursive(first, values));
                fired(e, "recursive-group");
                work.push(Work::Flat(body, index));
            }
            Work::Sequence(second, index) => {
                if matches!(e.bir().node(result).op(), Op::Var | Op::Const | Op::Fun) {
                    e.release(result);
                    fired(e, "pure-sequence-head");
                } else {
                    groups[index].push(Group::Nop(result));
                    fired(e, "sequence-head");
                }
                work.push(Work::Flat(second, index));
            }
            Work::Fold(n, index) => {
                fold(e, n, std::mem::take(&mut groups[index]), result);
                revision += 1;
                e.finish_candidate(n);
            }
        }
    }
    if revision == 0 {
        Changed::No
    } else {
        Changed::Yes
    }
}

/// The s-expression printer intentionally omits stamps. The round's
/// diagnostic comparison additionally checks every identity, including
/// imported binders, by name, stamp and flags in deterministic tree order.
pub(crate) fn identities(
    a: &crate::lambda::arena::LamArena,
    root: crate::lambda::arena::Lam,
) -> Vec<(crate::name::Name, i32, crate::ident::IdentFlags)> {
    use crate::lambda::arena::Node as L;
    let mut result = Vec::new();
    let mut work = vec![root];
    while let Some(n) = work.pop() {
        let mut add =
            |id: crate::ident::Ident| result.push((id.name_atom(), id.stamp(), id.flags()));
        match a.node(n) {
            L::Var(id)
            | L::GlobalModule(id)
            | L::Let { id, .. }
            | L::TryWith { id, .. }
            | L::For { id, .. }
            | L::ForOf { id, .. }
            | L::ForAwaitOf { id, .. }
            | L::Assign { id, .. } => add(a.ident(id)),
            L::Function { info, .. } => {
                for &id in a.params(info) {
                    add(id);
                }
            }
            L::LetRec { ids, values, .. } => {
                for &id in a.ident_run(ids, a.list_len(values)) {
                    add(id);
                }
            }
            L::StaticCatch { info, .. } => {
                for &id in a.idents(a.catch_payload(info).params) {
                    add(id);
                }
            }
            L::Const(_)
            | L::Apply { .. }
            | L::Prim { .. }
            | L::Switch { .. }
            | L::StringSwitch { .. }
            | L::StaticRaise { .. }
            | L::TryFinally { .. }
            | L::If { .. }
            | L::Sequence(..)
            | L::While(..)
            | L::Break
            | L::Continue => {}
        }
        work.extend(crate::bir::bridge::children(a, a.node(n)).into_iter().rev());
    }
    result
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bir::bridge::{export_lambda, import_lambda};
    use crate::bir::engine::testing::{id, prim};
    use crate::lambda::arena::{Lam, LamArena};
    use crate::lambda::lam_compat::LetKind;
    use crate::lambda::lam_constant::Constant as C;

    fn compare(mut a: LamArena, root: Lam) -> crate::bir::engine::Stats {
        let mut imported = import_lambda(&a, root).unwrap();
        let gen_ = crate::context::IdGenerator::new();
        let stamp = a.ident_stamp_bound();
        gen_.set_current_stamp(stamp);
        let expected = crate::lambda::lam_pass_deep_flatten::deep_flatten(&mut a, root, &gen_);
        let stats = {
            let mut e = Engine::new(&mut imported.arena);
            e.set_current_stamp(stamp as u32);
            e.run(&FLATTEN, imported.root);
            e.stats
        };
        for &(var, source) in &stats.renames {
            imported.register_rename(var, source).unwrap();
        }
        imported.arena.validate(Some(imported.root), false).unwrap();
        let actual = export_lambda(&imported).unwrap();
        assert_eq!(
            identities(&actual.arena, actual.root),
            identities(&a, expected)
        );
        let mut before = Vec::new();
        let mut after = Vec::new();
        crate::lambda::sexp_lambda::print_lambda(&a.export(expected), &mut before).unwrap();
        crate::lambda::sexp_lambda::print_lambda(&actual.to_tree(), &mut after).unwrap();
        assert_eq!(
            String::from_utf8(after).unwrap(),
            String::from_utf8(before).unwrap()
        );
        stats
    }

    #[test]
    fn named_block_eliminates_projections_and_keeps_unprojected_effects() {
        use crate::lambda::lam_tag_info::TagInfo;
        for escapes in [false, true] {
            let mut a = LamArena::new();
            let tuple = id("match", 1);
            let projected = id("projected", 2);
            let left = crate::bir::engine::testing::call(&mut a, "left", 10);
            let right = crate::bir::engine::testing::call(&mut a, "right", 11);
            let block = prim(
                &mut a,
                Primitive::Pmakeblock(TagInfo::Tuple, Mutable::Immutable),
                &[left, right],
            );
            let v = a.var(tuple);
            let field = prim(&mut a, Primitive::Pfield(0, FieldDbgInfo::Tuple), &[v]);
            let result = a.var(if escapes { tuple } else { projected });
            let body = a.let_(LetKind::Alias, projected, field, result);
            let root = a.let_(LetKind::Strict, tuple, block, body);
            let stats = compare(a, root);
            assert_eq!(
                stats.rules.get("named-block").copied().unwrap_or(0),
                u64::from(!escapes)
            );
        }
    }

    #[test]
    fn beta_residue_stays_local_and_recursive_values_are_visited() {
        let mut a = LamArena::new();
        let x = id("x", 1);
        let y = id("y", 2);
        let source = a.var(id("source", 10));
        let call = crate::bir::engine::testing::call(&mut a, "callee", 11);
        let residue = a.let_(LetKind::Strict, y, source, call);
        let body = a.unit();
        let value = a.let_(LetKind::Strict, x, residue, body);
        let result = a.unit();
        let root = a.letrec(&[(id("recursive", 3), value)], result);
        compare(a, root);
    }

    #[test]
    fn three_nested_values_and_effectful_sequence_heads() {
        let mut a = LamArena::new();
        let mut value = crate::bir::engine::testing::call(&mut a, "call", 20);
        for stamp in 1..=3 {
            let head = crate::bir::engine::testing::call(&mut a, "head", 21);
            let seq = a.seq_raw(head, value);
            let body = a.unit();
            value = a.let_(LetKind::Strict, id("bound", stamp), seq, body);
        }
        compare(a, value);
    }

    #[test]
    fn ordinary_let_allocates_in_body_before_value() {
        let mut a = LamArena::new();
        let make = |a: &mut LamArena, stamp| {
            let call = crate::bir::engine::testing::call(a, "f", 30);
            let value = prim(a, Primitive::PnullUndefinedToOpt, &[call]);
            let body = a.var(id("temporary", stamp));
            a.let_(LetKind::Strict, id("temporary", stamp), value, body)
        };
        let left = make(&mut a, 1);
        let value = prim(&mut a, Primitive::PsomeNotNest, &[left]);
        let body = make(&mut a, 2);
        let root = a.let_(LetKind::Strict, id("outer", 3), value, body);
        let stats = compare(a, root);
        assert_eq!(stats.renames.len(), 2);
    }

    #[test]
    fn nullable_variable_and_refine_primitive_and_call() {
        for shape in 0..3 {
            let mut a = LamArena::new();
            let x = id("x", 1);
            let v = a.var(id("source", 2));
            let value = prim(&mut a, Primitive::PnullToOpt, &[v]);
            let use_ = a.var(x);
            let body = match shape {
                0 => prim(&mut a, Primitive::Pnot, &[use_]),
                1 => {
                    let f = a.var(id("f", 3));
                    a.apply_raw(
                        f,
                        &[use_],
                        crate::lambda::ApInfo {
                            loc: LamLoc::NONE,
                            status: crate::lambda::ApplyStatus::Uncurry,
                        },
                    )
                }
                _ => use_,
            };
            let root = a.let_(LetKind::Strict, x, value, body);
            assert!(compare(a, root).renames.is_empty());
        }
    }

    #[test]
    fn linear_steps_on_ten_thousand_deep_and_wide_nodes() {
        use crate::lambda::lam_tag_info::TagInfo;
        for wide in [false, true] {
            let mut a = LamArena::new();
            let mut root = a.unit();
            let mut args = Vec::new();
            for stamp in 1..=10_000 {
                let body = a.unit();
                let value = if wide { a.unit() } else { root };
                let n = a.let_(LetKind::Strict, id("x", stamp), value, body);
                if wide {
                    args.push(n);
                } else {
                    root = n;
                }
            }
            if wide {
                root = prim(
                    &mut a,
                    Primitive::Pmakeblock(TagInfo::Tuple, Mutable::Immutable),
                    &args,
                );
            }
            let mut imported = crate::bir::engine::testing::import(&a, root);
            let steps = {
                let mut e = Engine::new(&mut imported.arena);
                e.run(&FLATTEN, imported.root);
                e.steps()
            };
            let nodes = if wide { 30_001 } else { 20_001 };
            assert!(steps <= 90 * nodes, "wide={wide}, steps={steps}");
            imported.arena.validate(Some(imported.root), false).unwrap();
            eprintln!("flatten wide={wide}: {steps} steps");
        }
    }

    #[test]
    fn summary_miss_is_not_entered() {
        let mut a = LamArena::new();
        let call = crate::bir::engine::testing::call(&mut a, "f", 1);
        let mut imported = import_lambda(&a, call).unwrap();
        let mut e = Engine::new(&mut imported.arena);
        assert_eq!(e.run(&FLATTEN, imported.root), Changed::No);
        assert_eq!(e.stats.entered, 0);
        assert_eq!(e.stats.pruned, 1);
    }

    #[test]
    fn ordinary_let_refinement() {
        for kind in [
            LetKind::Strict,
            LetKind::Alias,
            LetKind::StrictOpt,
            LetKind::Variable,
        ] {
            let mut a = LamArena::new();
            let x = id("x", 1);
            let value = a.const_(C::int(3));
            let body = a.var(x);
            let root = a.let_(kind, x, value, body);
            compare(a, root);
        }
    }

    #[test]
    fn nested_let_sequence_and_recursive_value() {
        for shape in 0..3 {
            let mut a = LamArena::new();
            let x = id("x", 1);
            let y = id("y", 2);
            let one = a.const_(C::int(1));
            let two = a.const_(C::int(2));
            let value = match shape {
                0 => a.let_(LetKind::Strict, y, one, two),
                1 => a.seq_raw(one, two),
                _ => a.letrec(&[(y, one)], two),
            };
            let body = a.var(x);
            let root = a.let_(LetKind::Strict, x, value, body);
            compare(a, root);
        }
    }

    #[test]
    fn fresh_identifiers_follow_body_before_value_under_a_function() {
        let mut a = LamArena::new();
        let x = id("x", 1);
        let y = id("y", 2);
        let make = |a: &mut LamArena, id_| {
            let call = crate::bir::engine::testing::call(a, "f", 10);
            let value = prim(a, Primitive::PnullToOpt, &[call]);
            let body = a.var(id_);
            a.let_(LetKind::Strict, id_, value, body)
        };
        let left = make(&mut a, x);
        let right = make(&mut a, y);
        let pair = prim(&mut a, Primitive::Paddint, &[left, right]);
        let root = a.function_(
            0,
            &[],
            pair,
            crate::lambda::FunctionAttribute::default(),
            LamLoc::NONE,
        );
        let stats = compare(a, root);
        assert_eq!(stats.renames.len(), 2);
    }
}
