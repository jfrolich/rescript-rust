//! Static-exit simplification, beside the legacy pipeline.
//! `lam_pass_exits.rs::subst_helper` / compiler/core/lam_pass_exits.ml:153-205.
use crate::bir::engine::{Changed, Engine, Facts, OpMask, Order, Round, Shell};
use crate::bir::*;
use crate::lambda::lam_compat::FieldDbgInfo;
use crate::lambda::lam_primitive::Primitive;
use crate::lambda::lam_tag_info::TagInfo;
use std::collections::BTreeMap;

/// Only Catch enables the round (simplify_exits' has_static_catch test).
/// Inside the round, EXIT|CATCH prunes substitution descent. Counts are taken
/// before edits. No ident_tbl or as-of-start subtree is read: Current, no guard.
/// Stateful is necessary: visit handler, install substitution, then visit body;
/// raises visit arguments before allocating fresh parameters. Pre/Post cannot
/// thread this table. Rebuilt shallow_map ancestors use today's constructors.
pub static EXITS: Round = Round {
    name: "simplify_exits",
    mask: OpMask::CATCH,
    order: Order::Stateful(run),
    renorm: OpMask::SHALLOW_MAP.or(OpMask::IF).or(OpMask::SEQ),
    facts: Facts::Current,
    guard: None,
    rule: |_, _| Changed::No,
};

/// The maintained CatchHeader::uses includes unreachable handlers, unlike
/// lam_exit_count.ml:58-60. Compute the ordered legacy count once, explicitly.
/// Maintaining this fact would require conditional handler activation, not
/// just incrementing/decrementing every Exit's weighted structural count.
pub(crate) fn count(b: &Bir, root: NodeId) -> BTreeMap<u32, u32> {
    enum Work {
        Node(NodeId),
        Handler(u32, NodeId),
    }
    let mut counts = BTreeMap::new();
    let mut work = vec![Work::Node(root)];
    while let Some(task) = work.pop() {
        let n = match task {
            Work::Handler(label, handler) => {
                if counts.get(&label).copied().unwrap_or(0) == 0 {
                    continue;
                }
                handler
            }
            Work::Node(n) => n,
        };
        match b.view(n) {
            // lam_exit_count.ml:55-57: count the raise before its arguments.
            View::Exit { label, args } => {
                *counts.entry(label).or_default() += 1;
                work.extend(args.iter().rev().copied().map(Work::Node));
            }
            // lam_exit_count.ml:58-60: body before conditionally live handler.
            View::Catch {
                body,
                handler,
                header,
            } => {
                work.push(Work::Handler(b.catch(header).label, handler));
                work.push(Work::Node(body));
            }
            // lam_exit_count.ml:70-72: body before value, NOT shallow_map order.
            View::Let { value, body, .. } => {
                work.extend(value.map(Work::Node));
                work.push(Work::Node(body));
            }
            // lam_exit_count.ml:100-107: default first, twice if both incomplete.
            View::Switch {
                scrutinee,
                actions,
                header,
            } => {
                let h = b.switch(header);
                let cases = actions.len() - usize::from(h.has_default);
                work.extend(actions[..cases].iter().rev().copied().map(Work::Node));
                work.push(Work::Node(scrutinee));
                if h.has_default {
                    let default = actions[cases];
                    work.push(Work::Node(default));
                    if !h.consts_full && !h.blocks_full {
                        work.push(Work::Node(default));
                    }
                }
            }
            _ => work.extend(b.view(n).children().into_iter().rev().map(Work::Node)),
        }
    }
    counts
}

/// lam_pass_exits.ml:32-58. This syntactic property is not Bir purity.
fn no_bounded_variables(b: &Bir, root: NodeId) -> bool {
    let mut work = vec![root];
    while let Some(n) = work.pop() {
        match b.view(n) {
            View::Let { .. }
            | View::Try { .. }
            | View::TryFinally { .. }
            | View::For { .. }
            | View::ForOf { .. }
            | View::ForAwaitOf { .. } => return false,
            View::LetRec { values, .. } if !values.is_empty() => return false,
            View::Fun { header, .. } if b.function(header).params.len != 0 => return false,
            View::Catch { header, .. } if b.catch(header).params.len != 0 => return false,
            _ => work.extend(b.view(n).children()),
        }
    }
    true
}

/// `size_upto` (SizeCounter::lam/constant in lam_analysis.rs): the size of
/// `root` if below `limit`, `limit` otherwise; the walk stops there. Unlike a
/// node count, applications/functions/sequences have no own cost.
pub(crate) fn size_upto(b: &Bir, root: NodeId, limit: usize) -> usize {
    enum Item {
        Node(NodeId),
        Constant(ConstId),
    }
    let mut work = vec![Item::Node(root)];
    let mut total = 0;
    while let Some(item) = work.pop() {
        match item {
            Item::Constant(c) => match b.constant(c) {
                Constant::Some(c) => work.push(Item::Constant(*c)),
                Constant::Block { tag, fields } => {
                    let fields = b.constant_fields(*fields);
                    if matches!(tag, TagInfo::Record(_) | TagInfo::RecordInlined(_)) {
                        total += tag.logical_field_count().saturating_sub(fields.len());
                    }
                    work.extend(fields.iter().copied().map(Item::Constant));
                }
                _ => total += 1,
            },
            Item::Node(n) => {
                match b.view(n) {
                    View::Const { value } => {
                        work.push(Item::Constant(value));
                        continue;
                    }
                    View::LetRec { .. }
                    | View::Switch { .. }
                    | View::StrSwitch { .. }
                    | View::Catch { .. }
                    | View::Try { .. }
                    | View::TryFinally { .. }
                    | View::While { .. }
                    | View::For { .. }
                    | View::ForOf { .. }
                    | View::ForAwaitOf { .. } => return limit,
                    View::Apply { .. } | View::Fun { .. } | View::Seq { .. } => {}
                    View::Prim { primitive, args } => match &b.primitive(primitive).primitive {
                        Primitive::Pfield(_, FieldDbgInfo::Module { .. }) if matches!(args, [x] if matches!(b.node(*x).op(), Op::Global | Op::Var)) =>
                        {
                            total += 1;
                            if total >= limit {
                                return limit;
                            }
                            continue;
                        }
                        Primitive::Praise | Primitive::PisNotNone if args.len() == 1 => {}
                        Primitive::PrawJsCode(_) => return limit,
                        Primitive::Pmakeblock(
                            tag @ (TagInfo::Record(_) | TagInfo::RecordInlined(_)),
                            _,
                        ) => total += 1 + tag.logical_field_count().saturating_sub(args.len()),
                        Primitive::PjsObjectCreate(params) => {
                            let logical = params
                                .iter()
                                .filter(|p| {
                                    !matches!(
                                        p.obj_arg_type,
                                        crate::types::external_ffi_types::Attr::ArgCst(_)
                                    )
                                })
                                .count();
                            total += 1 + logical.saturating_sub(args.len());
                        }
                        _ => total += 1,
                    },
                    _ => total += 1,
                }
                work.extend(b.view(n).children().into_iter().map(Item::Node));
            }
        }
        if total >= limit {
            return limit;
        }
    }
    total
}

fn fired(e: &mut Engine<'_>, name: &'static str) {
    *e.stats.rules.entry(name).or_default() += 1;
}

struct Handler {
    params: Vec<VarId>,
    tree: Option<NodeId>,
    single: bool,
}
enum Work {
    Enter(NodeId),
    Finish(NodeId, u64, Shell),
    Handler(NodeId, u32, bool, u64),
    Raise(NodeId, Option<Shell>),
}

/// StaticCatch arm, legacy subst_helper:157-183. The decision based on the
/// original handler precedes simplifying it; the small-body test follows it.
fn catch(
    e: &mut Engine<'_>,
    n: NodeId,
    counts: &BTreeMap<u32, u32>,
    work: &mut Vec<Work>,
    revision: &mut u64,
) {
    let View::Catch {
        body,
        handler,
        header,
    } = e.bir().view(n)
    else {
        unreachable!()
    };
    let label = e.bir().catch(header).label;
    let uses = counts.get(&label).copied().unwrap_or(0);
    if uses == 0 {
        e.promote(n, body);
        fired(e, "drop-catch");
        *revision += 1;
        work.push(Work::Enter(n));
    } else {
        let immediate = matches!(e.bir().node(handler).op(), Op::Var | Op::Const)
            || (uses == 1 && label as i32 >= 0);
        work.push(Work::Handler(n, uses, immediate, *revision));
        work.push(Work::Enter(handler));
    }
}

/// subst_lambda replaces Var only (not Assign's target), rebuilding changed
/// ancestors through shallow_map. No binders are renamed here.
fn substitute(e: &mut Engine<'_>, root: NodeId, params: &BTreeMap<VarId, VarId>) {
    let mut work = vec![(root, false, 0)];
    let mut revision = 0;
    while let Some((n, done, before)) = work.pop() {
        if done {
            if before != revision && EXITS.renorm.intersects(OpMask::of(e.bir().node(n).op())) {
                e.normalise(n);
            }
            e.finish_candidate(n);
        } else if let View::Var { var } = e.bir().view(n) {
            if let Some(&var) = params.get(&var) {
                let weight = e.weight(n);
                let replacement = e.node(View::Var { var }, 0, weight);
                e.replace(n, replacement);
                revision += 1;
            }
        } else {
            work.push((n, true, revision));
            work.extend(
                e.bir()
                    .view(n)
                    .children()
                    .into_iter()
                    .rev()
                    .map(|c| (c, false, 0)),
            );
        }
    }
}

/// StaticRaise arm, legacy subst_helper:184-203. Argument rewrites finish
/// before fresh ys are allocated left to right; strict lets fold right to left.
fn raise(
    e: &mut Engine<'_>,
    n: NodeId,
    table: &BTreeMap<u32, usize>,
    handlers: &mut [Handler],
    revision: &mut u64,
) {
    let View::Exit { label, args } = e.bir().view(n) else {
        unreachable!()
    };
    let Some(&index) = table.get(&label) else {
        return;
    };
    let args = args.to_vec();
    let h = &mut handlers[index];
    let mut tree = if h.single {
        h.tree.take().expect("single-use handler used twice")
    } else {
        e.copy_exit_handler(h.tree.unwrap())
    };
    if !args.is_empty() {
        let fresh: Vec<_> = h.params.iter().map(|&v| e.rename_var(v)).collect();
        let params = h
            .params
            .iter()
            .copied()
            .zip(fresh.iter().copied())
            .collect();
        substitute(e, tree, &params);
        let weight = e.weight(n);
        for (&var, arg) in fresh.iter().zip(args).rev() {
            e.detach(arg);
            tree = e.node(
                View::Let {
                    var,
                    value: Some(arg),
                    body: tree,
                },
                0,
                weight,
            );
        }
        fired(e, "inline-arguments");
    } else {
        fired(e, "inline-empty");
    }
    e.replace(n, tree);
    *revision += 1;
}

/// Default arm, legacy subst_helper:204: shallow_map order, then smart
/// constructors only when a descendant changed.
fn shallow(e: &mut Engine<'_>, n: NodeId, work: &mut Vec<Work>, revision: u64) {
    let children = e.bir().view(n).children();
    let shell = e.open_shell(n);
    work.push(Work::Finish(n, revision, shell));
    work.extend(children.into_iter().rev().map(Work::Enter));
}

fn run(e: &mut Engine<'_>, root: NodeId) -> Changed {
    let counts = count(e.bir(), root);
    let mut table = BTreeMap::new();
    let mut handlers: Vec<Handler> = Vec::new();
    let mut work = vec![Work::Enter(root)];
    let mut revision = 0;
    while let Some(task) = work.pop() {
        match task {
            Work::Enter(n) => {
                if !e.enter_candidate(n, OpMask::CATCH.or(OpMask::EXIT)) {
                    continue;
                }
                match e.bir().view(n) {
                    View::Catch { .. } => catch(e, n, &counts, &mut work, &mut revision),
                    View::Exit { args, .. } => {
                        let args = args.to_vec();
                        let shell = (!args.is_empty()).then(|| e.open_shell(n));
                        work.push(Work::Raise(n, shell));
                        work.extend(args.into_iter().rev().map(Work::Enter));
                    }
                    _ => shallow(e, n, &mut work, revision),
                }
            }
            Work::Finish(n, before, shell) => {
                e.close_shell(n, shell);
                if revision != before && EXITS.renorm.intersects(OpMask::of(e.bir().node(n).op())) {
                    e.normalise(n);
                }
                e.finish_candidate(n);
            }
            Work::Handler(n, uses, immediate, before) => {
                let View::Catch {
                    body,
                    handler,
                    header,
                } = e.bir().view(n)
                else {
                    unreachable!()
                };
                let h = *e.bir().catch(header);
                let small = !immediate
                    && h.label as i32 >= 0
                    && no_bounded_variables(e.bir(), handler)
                    && {
                        let size = size_upto(e.bir(), handler, 7);
                        (uses <= 2 && size < 7) || size < 5
                    };
                if immediate || small {
                    let single = uses == 1;
                    e.detach(handler);
                    table.insert(h.label, handlers.len());
                    handlers.push(Handler {
                        params: h.params.iter().collect(),
                        tree: Some(handler),
                        single,
                    });
                    e.promote(n, body);
                    fired(
                        e,
                        if small {
                            "inline-small"
                        } else {
                            "inline-direct"
                        },
                    );
                    revision += 1;
                    work.push(Work::Enter(n));
                } else {
                    fired(e, "keep-catch");
                    let shell = e.open_shell(n);
                    work.push(Work::Finish(n, before, shell));
                    work.push(Work::Enter(body));
                }
            }
            Work::Raise(n, shell) => {
                if let Some(shell) = shell {
                    e.close_shell(n, shell);
                }
                raise(e, n, &table, &mut handlers, &mut revision);
                e.finish_candidate(n);
            }
        }
    }
    for h in handlers {
        if let Some(tree) = h.tree {
            e.release(tree);
        }
    }
    if revision == 0 {
        Changed::No
    } else {
        Changed::Yes
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bir::bridge::{export_lambda, import_lambda};
    use crate::bir::engine::testing::{id, prim};
    use crate::lambda::arena::{Lam, LamArena};
    use crate::lambda::lam_compat::LetKind;
    use crate::lambda::lam_constant::Constant as C;

    fn compare(a: LamArena, root: Lam) -> crate::bir::engine::Stats {
        let tree = a.export(root);
        let mut a = LamArena::new();
        let root = a.import(&tree);
        let mut imported = import_lambda(&a, root).unwrap();
        let counts = count(&imported.arena, imported.root);
        let expected_counts = crate::lambda::lam_pass_exits::count_helper(&a, root);
        assert_eq!(
            counts,
            expected_counts
                .into_iter()
                .map(|(l, c)| (l as u32, c))
                .collect()
        );
        let generator = crate::context::IdGenerator::new();
        let stamp = a.ident_stamp_bound();
        generator.set_current_stamp(stamp);
        let expected = crate::lambda::lam_pass_exits::simplify_exits(&mut a, root, &generator);
        let stats = {
            let mut e = Engine::new(&mut imported.arena);
            e.set_current_stamp(stamp as u32);
            e.run(&EXITS, imported.root);
            e.stats
        };
        for &(var, source) in &stats.renames {
            imported.register_rename(var, source).unwrap();
        }
        imported.arena.validate(Some(imported.root), false).unwrap();
        let actual = export_lambda(&imported).unwrap();
        assert_eq!(
            super::super::flatten::identities(&a, expected),
            super::super::flatten::identities(&actual.arena, actual.root)
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
    fn unused_handlers_make_structural_counts_different() {
        let mut a = LamArena::new();
        let one = a.const_(C::int(1));
        let raise = a.static_raise(1, &[]);
        let dead = a.static_catch(one, 2, &[], raise);
        let root = a.static_catch(dead, 1, &[], one);
        let tree = a.export(root);
        let mut a = LamArena::new();
        let root = a.import(&tree);
        let imported = import_lambda(&a, root).unwrap();
        let View::Catch { header, .. } = imported.arena.view(imported.root) else {
            unreachable!()
        };
        assert_eq!(imported.arena.catch(header).uses(), 1);
        assert_eq!(count(&imported.arena, imported.root).get(&1), None);
        assert_eq!(compare(a, root).rules["drop-catch"], 2);
    }

    #[test]
    fn catch_decisions_and_raise_arguments() {
        for label in [-1, 1] {
            for uses in [0, 1, 2, 3] {
                for shape in 0..5 {
                    let mut a = LamArena::new();
                    let x = id("x", 1);
                    let y = id("y", 2);
                    let one = a.const_(C::int(1));
                    let vx = a.var(x);
                    let vy = a.var(y);
                    let handler = match shape {
                        0 => one,
                        1 => vx,
                        2 => prim(&mut a, Primitive::Paddint, &[vx, vy]),
                        3 => a.let_(LetKind::Strict, id("local", 3), one, vx),
                        _ => {
                            let sum = prim(&mut a, Primitive::Paddint, &[vx, vy]);
                            let sum = prim(&mut a, Primitive::Paddint, &[sum, sum]);
                            prim(&mut a, Primitive::Paddint, &[sum, sum])
                        }
                    };
                    let mut body = one;
                    for _ in 0..uses {
                        let raise = a.static_raise(label, &[one, one]);
                        body = a.seq_raw(raise, body);
                    }
                    let root = a.static_catch(body, label, &[x, y], handler);
                    compare(a, root);
                }
            }
        }
    }

    #[test]
    fn nested_handler_and_outer_raise() {
        let mut a = LamArena::new();
        let x = id("x", 1);
        let y = id("y", 2);
        let one = a.const_(C::int(1));
        let vx = a.var(x);
        let outer = a.static_raise(1, &[vx]);
        let body = a.static_raise(2, &[one]);
        let inner = a.static_catch(body, 2, &[x], outer);
        let vy = a.var(y);
        let root = a.static_catch(inner, 1, &[y], vy);
        assert_eq!(compare(a, root).renames.len(), 2);
    }

    #[test]
    fn handler_parameter_used_inside_a_function_is_captured_after_substitution() {
        let mut a = LamArena::new();
        let x = id("x", 1);
        let y = id("y", 2);
        let vx = a.var(x);
        let vy = a.var(y);
        let sum = prim(&mut a, Primitive::Paddint, &[vx, vy]);
        let handler = a.function_(
            1,
            &[y],
            sum,
            Default::default(),
            crate::lambda::LamLoc::NONE,
        );
        let one = a.const_(C::int(1));
        let body = a.static_raise(1, &[one]);
        let root = a.static_catch(body, 1, &[x], handler);
        assert_eq!(compare(a, root).renames.len(), 1);
    }

    #[test]
    fn empty_raise_and_binder_free_function_copy() {
        for function in [false, true] {
            let mut a = LamArena::new();
            let one = a.const_(C::int(1));
            let handler = if function {
                a.function_(0, &[], one, Default::default(), crate::lambda::LamLoc::NONE)
            } else {
                one
            };
            let raise = a.static_raise(1, &[]);
            let body = a.seq_raw(raise, raise);
            let root = a.static_catch(body, 1, &[], handler);
            assert_eq!(compare(a, root).rules["inline-empty"], 2);
        }
    }

    #[test]
    fn no_catch_enters_no_nodes() {
        let mut a = LamArena::new();
        let one = a.const_(C::int(1));
        assert_eq!(compare(a, one).entered, 0);
    }

    #[test]
    fn switch_default_is_counted_before_branches_and_twice() {
        for full in [false, true] {
            let mut a = LamArena::new();
            let scrut = a.var(id("scrut", 10));
            let branch = a.static_raise(1, &[]);
            let default = a.static_raise(1, &[]);
            let info = a.add_switch(
                full,
                [crate::lambda::SwitchKey::Int(0)],
                false,
                [],
                true,
                crate::lambda::SwitchDispatch::Direct,
            );
            let actions = a.add_list(&[branch, default]);
            let body = a.switch_raw(scrut, actions, info);
            let handler = a.const_(C::int(42));
            let root = a.static_catch(body, 1, &[], handler);
            assert_eq!(
                crate::lambda::lam_pass_exits::count_helper(&a, root)[&1],
                if full { 2 } else { 3 }
            );
            compare(a, root);
        }
    }

    #[test]
    fn ten_thousand_deep_catches_and_wide_switch() {
        for wide in [false, true] {
            let mut a = LamArena::new();
            let mut root = a.unit();
            if wide {
                let scrut = a.var(id("scrut", 1));
                let actions: Vec<_> = (0..10_000).map(|_| a.static_raise(1, &[])).collect();
                let info = a.add_switch(
                    true,
                    (0..10_000).map(crate::lambda::SwitchKey::Int),
                    true,
                    [],
                    false,
                    crate::lambda::SwitchDispatch::Direct,
                );
                let actions = a.add_list(&actions);
                let body = a.switch_raw(scrut, actions, info);
                root = a.static_catch(body, 1, &[], root);
            } else {
                for label in 1..=10_000 {
                    let handler = a.unit();
                    root = a.static_catch(root, label, &[], handler);
                }
            }
            let mut imported = crate::bir::engine::testing::import(&a, root);
            let steps = {
                let mut e = Engine::new(&mut imported.arena);
                e.run(&EXITS, imported.root);
                e.steps()
            };
            let nodes = if wide { 10_004 } else { 20_001 };
            assert!(steps <= 120 * nodes, "wide={wide}, steps={steps}");
            imported.arena.validate(Some(imported.root), false).unwrap();
            eprintln!("exits wide={wide}: {steps} steps");
        }
    }

    #[test]
    fn shadowed_labels_have_a_specific_bridge_fallback() {
        let mut a = LamArena::new();
        let one = a.const_(C::int(1));
        let raise = a.static_raise(1, &[]);
        let inner = a.static_catch(raise, 1, &[], one);
        let root = a.static_catch(inner, 1, &[], one);
        assert!(matches!(
            import_lambda(&a, root),
            Err(crate::bir::bridge::Unsupported("reused static catch label"))
        ));
    }
}
