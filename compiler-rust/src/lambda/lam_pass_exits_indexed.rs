//! Indexed port of `lam_exit_count.ml`, `lam_subst.ml`, and
//! `lam_pass_exits.ml`. This is an inactive migration pass: one owning context
//! keeps the canonical root, append-only arena, and ID-bearing metadata.

use ahash::AHashMap;

use crate::context::IdGenerator;
use crate::ident::Ident;
use crate::lambda::indexed::{IndexedLambda, IndexedLambdaContext, NodeId, NodeSnapshot, NodeView};
use crate::lambda::lam_analysis::EXIT_INLINE_SIZE;
use crate::lambda::lam_compat::LetKind;
use crate::lambda::lam_constant::Constant;
use crate::lambda::lam_indexed_helpers::{
    VariableSubstitution, append_rebuilt, map_children, substitute,
};
use crate::lambda::lam_pass_collect_indexed::indexed_size;
use crate::lambda::lam_primitive::Primitive;

pub(crate) type ExitCounts = AHashMap<i32, u32>;
struct ExitSubstitutions {
    entries: AHashMap<i32, (Vec<Ident>, NodeId)>,
    #[cfg(test)]
    peak_unique_nodes: usize,
}

impl ExitSubstitutions {
    fn new() -> Self {
        Self {
            entries: AHashMap::new(),
            #[cfg(test)]
            peak_unique_nodes: 0,
        }
    }

    fn get(&self, exit: &i32) -> Option<&(Vec<Ident>, NodeId)> {
        self.entries.get(exit)
    }

    fn insert(&mut self, store: &IndexedLambda, exit: i32, value: (Vec<Ident>, NodeId)) {
        self.entries.insert(exit, value);
        #[cfg(test)]
        {
            let roots = self
                .entries
                .values()
                .map(|(_, handler)| *handler)
                .collect::<Vec<_>>();
            self.peak_unique_nodes = self
                .peak_unique_nodes
                .max(store.reachable_unique_nodes(&roots));
        }
    }
}

fn increment(counts: &mut ExitCounts, exit: i32) {
    *counts.entry(exit).or_insert(0) += 1;
}

fn count_exit(counts: &ExitCounts, exit: i32) -> u32 {
    counts.get(&exit).copied().unwrap_or(0)
}

/// Exact traversal order from `compiler/core/lam_exit_count.ml:51-110`.
pub(crate) fn count_exits(store: &IndexedLambda, root: NodeId) -> ExitCounts {
    fn count(store: &IndexedLambda, node: NodeId, counts: &mut ExitCounts) {
        match store.view(node) {
            NodeView::StaticRaise(exit, args) => {
                increment(counts, exit);
                for arg in args {
                    count(store, *arg, counts);
                }
            }
            NodeView::StaticCatch(body, exit, _, handler) => {
                count(store, body, counts);
                if count_exit(counts, exit) > 0 {
                    count(store, handler, counts);
                }
            }
            NodeView::StringSwitch(scrutinee, cases, default) => {
                count(store, scrutinee, counts);
                for (_, body) in cases {
                    count(store, *body, counts);
                }
                if let Some(default) = default {
                    count(store, default, counts);
                }
            }
            NodeView::Var(_)
            | NodeView::GlobalModule(_)
            | NodeView::Const(_)
            | NodeView::Break
            | NodeView::Continue => {}
            NodeView::Apply(function, args, _, _) => {
                count(store, function, counts);
                for arg in args {
                    count(store, *arg, counts);
                }
            }
            NodeView::Function(_, _, body, _, _) => count(store, body, counts),
            NodeView::Let(_, _, value, body) => {
                // OCaml deliberately visits the body before the value.
                count(store, body, counts);
                count(store, value, counts);
            }
            NodeView::LetRec(bindings, body) => {
                for (_, value) in bindings {
                    count(store, *value, counts);
                }
                count(store, body, counts);
            }
            NodeView::Prim(_, args, _) => {
                for arg in args {
                    count(store, *arg, counts);
                }
            }
            NodeView::Switch {
                scrutinee,
                consts_full,
                consts,
                blocks_full,
                blocks,
                fail_action,
                ..
            } => {
                if let Some(fail) = fail_action {
                    count(store, fail, counts);
                    if !consts_full && !blocks_full {
                        count(store, fail, counts);
                    }
                }
                count(store, scrutinee, counts);
                for (_, body) in consts {
                    count(store, *body, counts);
                }
                for (_, body) in blocks {
                    count(store, *body, counts);
                }
            }
            NodeView::TryWith(body, _, handler) => {
                count(store, body, counts);
                count(store, handler, counts);
            }
            NodeView::IfThenElse(a, b, c) | NodeView::For(_, a, b, _, c) => {
                count(store, a, counts);
                count(store, b, counts);
                count(store, c, counts);
            }
            NodeView::Sequence(a, b)
            | NodeView::While(a, b)
            | NodeView::ForOf(_, a, b)
            | NodeView::ForAwaitOf(_, a, b) => {
                count(store, a, counts);
                count(store, b, counts);
            }
            NodeView::Assign(_, value) => count(store, value, counts),
        }
    }
    let mut counts = ExitCounts::new();
    count(store, root, &mut counts);
    counts
}

/// `Lam_pass_exits.no_bounded_variables`, preserving short-circuit order.
pub(crate) fn no_bounded_variables(store: &IndexedLambda, node: NodeId) -> bool {
    match store.view(node) {
        NodeView::Var(_)
        | NodeView::GlobalModule(_)
        | NodeView::Const(_)
        | NodeView::Break
        | NodeView::Continue => true,
        NodeView::Assign(_, value) => no_bounded_variables(store, value),
        NodeView::Apply(function, args, _, _) => {
            no_bounded_variables(store, function)
                && args.iter().all(|node| no_bounded_variables(store, *node))
        }
        NodeView::Prim(_, args, _) | NodeView::StaticRaise(_, args) => {
            args.iter().all(|node| no_bounded_variables(store, *node))
        }
        NodeView::Switch {
            scrutinee,
            consts,
            blocks,
            fail_action,
            ..
        } => {
            no_bounded_variables(store, scrutinee)
                && consts
                    .iter()
                    .all(|(_, node)| no_bounded_variables(store, *node))
                && blocks
                    .iter()
                    .all(|(_, node)| no_bounded_variables(store, *node))
                && fail_action.is_none_or(|node| no_bounded_variables(store, node))
        }
        NodeView::StringSwitch(scrutinee, cases, default) => {
            no_bounded_variables(store, scrutinee)
                && cases
                    .iter()
                    .all(|(_, node)| no_bounded_variables(store, *node))
                && default.is_none_or(|node| no_bounded_variables(store, node))
        }
        NodeView::IfThenElse(a, b, c) => {
            no_bounded_variables(store, a)
                && no_bounded_variables(store, b)
                && no_bounded_variables(store, c)
        }
        NodeView::Sequence(a, b) | NodeView::While(a, b) => {
            no_bounded_variables(store, a) && no_bounded_variables(store, b)
        }
        NodeView::StaticCatch(body, _, params, handler) => {
            params.is_empty()
                && no_bounded_variables(store, body)
                && no_bounded_variables(store, handler)
        }
        NodeView::Function(_, params, body, _, _) => {
            params.is_empty() && no_bounded_variables(store, body)
        }
        NodeView::LetRec(bindings, body) => {
            bindings.is_empty() && no_bounded_variables(store, body)
        }
        NodeView::Let(_, _, _, _)
        | NodeView::TryWith(_, _, _)
        | NodeView::For(_, _, _, _, _)
        | NodeView::ForOf(_, _, _)
        | NodeView::ForAwaitOf(_, _, _) => false,
    }
}

fn simplify(
    store: &mut IndexedLambda,
    counts: &ExitCounts,
    substitutions: &mut ExitSubstitutions,
    id_gen: &IdGenerator,
    node: NodeId,
) -> NodeId {
    match store.snapshot(node) {
        NodeSnapshot::StaticCatch(body, exit, params, handler) => {
            let occurrences = count_exit(counts, exit);
            if occurrences == 0 {
                return simplify(store, counts, substitutions, id_gen, body);
            }
            if matches!(store.view(handler), NodeView::Var(_) | NodeView::Const(_))
                || occurrences == 1 && exit >= 0
            {
                let handler = simplify(store, counts, substitutions, id_gen, handler);
                substitutions.insert(store, exit, (params, handler));
                return simplify(store, counts, substitutions, id_gen, body);
            }
            let handler = simplify(store, counts, substitutions, id_gen, handler);
            let inline = exit >= 0 && no_bounded_variables(store, handler) && {
                let size = indexed_size(store, handler);
                occurrences <= 2 && size < EXIT_INLINE_SIZE || size < 5
            };
            if inline {
                substitutions.insert(store, exit, (params, handler));
                simplify(store, counts, substitutions, id_gen, body)
            } else {
                let body = simplify(store, counts, substitutions, id_gen, body);
                store.append(NodeSnapshot::StaticCatch(body, exit, params, handler))
            }
        }
        NodeSnapshot::StaticRaise(exit, args) if args.is_empty() => substitutions
            .get(&exit)
            .map(|(_, handler)| *handler)
            .unwrap_or(node),
        NodeSnapshot::StaticRaise(exit, args) => {
            let args: Vec<_> = args
                .into_iter()
                .map(|x| simplify(store, counts, substitutions, id_gen, x))
                .collect();
            let Some((params, handler)) = substitutions.get(&exit).cloned() else {
                return store.append(NodeSnapshot::StaticRaise(exit, args));
            };
            let renamed: Vec<_> = params.iter().map(|id| id.rename(id_gen)).collect();
            let env: VariableSubstitution = params
                .iter()
                .cloned()
                .zip(
                    renamed
                        .iter()
                        .cloned()
                        .map(|id| store.append(NodeSnapshot::Var(id))),
                )
                .collect();
            let mut result = substitute(store, &env, handler);
            for (id, arg) in renamed.into_iter().zip(args).rev() {
                result = store.append(NodeSnapshot::Let(LetKind::Strict, id, arg, result));
            }
            result
        }
        NodeSnapshot::Var(_)
        | NodeSnapshot::Const(_)
        | NodeSnapshot::GlobalModule(_)
        | NodeSnapshot::Break
        | NodeSnapshot::Continue => node,
        // lam_pass_exits.ml:204 `Lambda_traverse.shallow_map_sharing`:
        // rebuild through the smart constructors only when a child changed.
        snapshot => {
            let mut changed = false;
            let mapped = map_children(store, snapshot, |store, child| {
                let mapped = simplify(store, counts, substitutions, id_gen, child);
                changed |= mapped != child;
                mapped
            });
            if !changed {
                return node;
            }
            append_rebuilt(store, mapped)
        }
    }
}

impl IndexedLambdaContext {
    /// Runs indexed exit simplification over the canonical root and appends
    /// replacements to the same store. Existing metadata IDs remain valid.
    pub fn simplify_exits(&mut self, id_gen: &IdGenerator) {
        let root = self.current_root();
        let counts = count_exits(self.store(), root);
        let mut substitutions = ExitSubstitutions::new();
        let rewritten = simplify(self.store_mut(), &counts, &mut substitutions, id_gen, root);
        self.replace_root(rewritten);
        #[cfg(test)]
        self.record_substitution_table_peak(substitutions.peak_unique_nodes);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ident::IdentFlags;
    use crate::lambda::lam_compile_context::{IdKind, LamStats};
    use crate::lambda::lam_pass_collect as tree_collect;
    use crate::lambda::lam_pass_collect_indexed::IndexedIdKind;
    use crate::lambda::lam_pass_exits as tree;
    use crate::lambda::{DirectionFlag, Lambda, LambdaSwitch, SwitchDispatch, SwitchKey};
    use crate::location::Location;

    fn id(name: &str, stamp: i32) -> Ident {
        Ident::new(name, stamp, IdentFlags::NONE)
    }

    fn simplify_indexed(lambda: Lambda, start_stamp: i32) -> Lambda {
        let mut context = IndexedLambdaContext::from_lambda(lambda, []);
        context.simplify_exits(&IdGenerator::with_start_stamp(start_stamp));
        context.materialize()
    }

    fn assert_exit_parity(lambda: Lambda, start_stamp: i32) -> IndexedLambdaContext {
        let tree_gen = IdGenerator::with_start_stamp(start_stamp);
        let indexed_gen = IdGenerator::with_start_stamp(start_stamp);
        let expected = tree::simplify_exits(&lambda, &tree_gen);
        let mut context = IndexedLambdaContext::from_lambda(lambda, []);
        context.simplify_exits(&indexed_gen);
        assert_eq!(
            format!("{expected:#?}"),
            format!("{:#?}", context.materialize())
        );
        assert_eq!(tree_gen.current_stamp(), indexed_gen.current_stamp());
        context
    }

    #[test]
    fn exit_count_and_bounded_analysis_match_tree_across_control_families() {
        let x = id("x", 1);
        let raise = || Lambda::LstaticRaise(7, vec![Lambda::Lvar(x.clone())]);
        let switch = Lambda::Lswitch(
            Box::new(raise()),
            Box::new(LambdaSwitch {
                sw_consts_full: false,
                sw_consts: vec![(SwitchKey::Int(0), raise())],
                sw_blocks_full: false,
                sw_blocks: vec![(SwitchKey::Int(1), raise())],
                sw_failaction: Some(Box::new(raise())),
                sw_dispatch: SwitchDispatch::Direct,
            }),
        );
        let lambda = Lambda::Lsequence(
            Box::new(Lambda::LstringSwitch(
                Box::new(raise()),
                vec![("a".into(), switch)],
                Some(Box::new(raise())),
            )),
            Box::new(Lambda::LtryWith(
                Box::new(Lambda::LifThenElse(
                    Box::new(raise()),
                    Box::new(raise()),
                    Box::new(raise()),
                )),
                x.clone(),
                Box::new(Lambda::Lfor(
                    x.clone(),
                    Box::new(raise()),
                    Box::new(raise()),
                    DirectionFlag::Upto,
                    Box::new(Lambda::Lfor_of(
                        x.clone(),
                        Box::new(raise()),
                        Box::new(Lambda::Lfor_await_of(
                            x.clone(),
                            Box::new(raise()),
                            Box::new(Lambda::Lassign(x.clone(), Box::new(raise()))),
                        )),
                    )),
                )),
            )),
        );
        let indexed = IndexedLambda::from_lambda(lambda.clone());
        assert_eq!(
            tree::count_helper(&lambda),
            count_exits(&indexed, indexed.root())
        );
        assert_eq!(
            tree::no_bounded_variables(&lambda),
            no_bounded_variables(&indexed, indexed.root())
        );

        let skipped = Lambda::LstaticCatch(
            Box::new(Lambda::unit()),
            (9, vec![]),
            Box::new(Lambda::LstaticRaise(7, vec![])),
        );
        let indexed = IndexedLambda::from_lambda(skipped.clone());
        assert_eq!(
            tree::count_helper(&skipped),
            count_exits(&indexed, indexed.root())
        );
    }

    #[test]
    fn simplify_exits_matches_tree_for_elimination_inlining_and_freshening() {
        let x = id("x", 10);
        let y = id("y", 11);
        let samples = [
            Lambda::LstaticCatch(
                Box::new(Lambda::unit()),
                (1, vec![]),
                Box::new(Lambda::true_()),
            ),
            Lambda::LstaticCatch(
                Box::new(Lambda::LstaticRaise(2, vec![])),
                (2, vec![]),
                Box::new(Lambda::true_()),
            ),
            Lambda::LstaticCatch(
                Box::new(Lambda::LstaticRaise(
                    3,
                    vec![Lambda::Lconst(Constant::int(4))],
                )),
                (3, vec![x.clone()]),
                Box::new(Lambda::Lvar(x.clone())),
            ),
            Lambda::LstaticCatch(
                Box::new(Lambda::Lsequence(
                    Box::new(Lambda::LstaticRaise(4, vec![Lambda::Lvar(y.clone())])),
                    Box::new(Lambda::LstaticRaise(4, vec![Lambda::Lvar(y.clone())])),
                )),
                (4, vec![x.clone()]),
                Box::new(Lambda::Lsequence(
                    Box::new(Lambda::Lvar(x.clone())),
                    Box::new(Lambda::Lconst(Constant::int(1))),
                )),
            ),
            Lambda::LstaticCatch(
                Box::new(Lambda::Lsequence(
                    Box::new(Lambda::LstaticRaise(-1, vec![])),
                    Box::new(Lambda::LstaticRaise(-1, vec![])),
                )),
                (-1, vec![]),
                Box::new(Lambda::Lsequence(
                    Box::new(Lambda::unit()),
                    Box::new(Lambda::unit()),
                )),
            ),
            Lambda::LstaticCatch(
                Box::new(Lambda::LstaticCatch(
                    Box::new(Lambda::LstaticRaise(61, vec![])),
                    (61, vec![]),
                    Box::new(Lambda::LstaticRaise(60, vec![])),
                )),
                (60, vec![]),
                Box::new(Lambda::true_()),
            ),
            Lambda::LstaticCatch(
                Box::new(Lambda::Lsequence(
                    Box::new(Lambda::LstaticRaise(6, vec![])),
                    Box::new(Lambda::LstaticRaise(6, vec![])),
                )),
                (6, vec![]),
                Box::new(Lambda::Llet(
                    LetKind::Strict,
                    x.clone(),
                    Box::new(Lambda::unit()),
                    Box::new(Lambda::Lvar(x.clone())),
                )),
            ),
        ];
        for sample in samples {
            assert_exit_parity(sample, 30);
        }
    }

    #[test]
    fn rewritten_children_use_the_same_smart_constructor_decisions() {
        let loc = crate::location::Location::none();
        let caught = |body: Lambda, handler: Lambda| {
            Lambda::LstaticCatch(Box::new(body), (70, vec![]), Box::new(handler))
        };
        let raise = || Lambda::LstaticRaise(70, vec![]);
        let eta_param = id("eta", 5);
        // `lam_pass_exits.ml:168-183` simplifies the handler before storing
        // it, and `lam_subst.ml:30-66` then applies smart constructors while
        // replacing catch parameters only with fresh variables.
        let parameter = id("parameter", 9);
        assert_exit_parity(
            Lambda::LstaticCatch(
                Box::new(Lambda::LstaticRaise(72, vec![Lambda::unit()])),
                (72, vec![parameter.clone()]),
                Box::new(Lambda::Lsequence(
                    Box::new(Lambda::Lprim(Box::new(crate::lambda::PrimInfo {
                        primitive: Primitive::Pnot,
                        args: vec![Lambda::true_()],
                        loc: loc.clone(),
                    }))),
                    Box::new(Lambda::Lvar(parameter)),
                )),
            ),
            80,
        );

        let raw_unchanged_sibling = Lambda::Lsequence(
            Box::new(Lambda::Lprim(Box::new(crate::lambda::PrimInfo {
                primitive: Primitive::Pnot,
                args: vec![Lambda::true_()],
                loc: loc.clone(),
            }))),
            Box::new(Lambda::LstaticCatch(
                Box::new(Lambda::unit()),
                (71, vec![]),
                Box::new(Lambda::true_()),
            )),
        );
        assert_exit_parity(raw_unchanged_sibling, 80);

        let cases = [
            caught(
                Lambda::LifThenElse(
                    Box::new(raise()),
                    Box::new(Lambda::true_()),
                    Box::new(Lambda::false_()),
                ),
                Lambda::true_(),
            ),
            caught(
                Lambda::Lprim(Box::new(crate::lambda::PrimInfo {
                    primitive: Primitive::Pnot,
                    args: vec![raise()],
                    loc: loc.clone(),
                })),
                Lambda::true_(),
            ),
            caught(
                Lambda::Lswitch(
                    Box::new(raise()),
                    Box::new(LambdaSwitch {
                        sw_consts_full: true,
                        sw_consts: vec![(SwitchKey::Int(1), Lambda::true_())],
                        sw_blocks_full: true,
                        sw_blocks: vec![],
                        sw_failaction: Some(Box::new(Lambda::false_())),
                        sw_dispatch: SwitchDispatch::Direct,
                    }),
                ),
                Lambda::Lconst(Constant::int(1)),
            ),
            caught(
                Lambda::LstringSwitch(
                    Box::new(raise()),
                    vec![("yes".into(), Lambda::true_())],
                    Some(Box::new(Lambda::false_())),
                ),
                Lambda::Lconst(Constant::string("yes")),
            ),
            caught(
                Lambda::LifThenElse(
                    Box::new(raise()),
                    Box::new(Lambda::true_()),
                    Box::new(Lambda::false_()),
                ),
                Lambda::Lprim(Box::new(crate::lambda::PrimInfo {
                    primitive: Primitive::Pnot,
                    args: vec![Lambda::Lvar(id("boolean", 6))],
                    loc: loc.clone(),
                })),
            ),
            caught(
                Lambda::LifThenElse(
                    Box::new(raise()),
                    Box::new(Lambda::unit()),
                    Box::new(Lambda::Lconst(Constant::int_with_comment(
                        0,
                        crate::lambda::lam_constant::PointerInfo::AssertFalse,
                    ))),
                ),
                Lambda::Lvar(id("condition", 7)),
            ),
            caught(
                Lambda::Lapply(Box::new(crate::lambda::Apply {
                    ap_func: Box::new(raise()),
                    ap_args: vec![Lambda::true_()],
                    ap_info: crate::lambda::ApInfo {
                        loc: loc.clone(),
                        inlined: crate::lambda::InlineAttribute::Default,
                        status: crate::lambda::ApplyStatus::Na,
                    },
                    ap_transformed_jsx: false,
                })),
                Lambda::function_(
                    1,
                    vec![eta_param.clone()],
                    Lambda::Lprim(Box::new(crate::lambda::PrimInfo {
                        primitive: Primitive::Pnot,
                        args: vec![Lambda::Lvar(eta_param)],
                        loc: loc.clone(),
                    })),
                    crate::lambda::FunctionAttribute::default(), crate::location::Location::none(),
                ),
            ),
            caught(
                Lambda::Lapply(Box::new(crate::lambda::Apply {
                    ap_func: Box::new(raise()),
                    ap_args: vec![Lambda::true_()],
                    ap_info: crate::lambda::ApInfo {
                        loc: loc.clone(),
                        inlined: crate::lambda::InlineAttribute::Default,
                        status: crate::lambda::ApplyStatus::Na,
                    },
                    ap_transformed_jsx: false,
                })),
                Lambda::function_(
                    1,
                    vec![id("wrapped", 8)],
                    Lambda::Lprim(Box::new(crate::lambda::PrimInfo {
                        primitive: Primitive::PnullToOpt,
                        args: vec![Lambda::Lprim(Box::new(crate::lambda::PrimInfo {
                            primitive: Primitive::Pnot,
                            args: vec![Lambda::Lvar(id("wrapped", 8))],
                            loc: loc.clone(),
                        }))],
                        loc: loc.clone(),
                    })),
                    crate::lambda::FunctionAttribute::default(), crate::location::Location::none(),
                ),
            ),
            caught(
                Lambda::Lsequence(Box::new(raise()), Box::new(Lambda::unit())),
                Lambda::Lprim(Box::new(crate::lambda::PrimInfo {
                    primitive: Primitive::PnullToOpt,
                    args: vec![Lambda::Lvar(id("v", 4))],
                    loc,
                })),
            ),
        ];
        for case in cases {
            assert_exit_parity(case, 80);
        }
    }

    #[test]
    fn substitution_keeps_jsx_and_shares_unchanged_nodes_like_ocaml() {
        let parameter = id("parameter", 180);
        let outer_loc = Location::new_for_error("subst.res", 20, 30);
        let inner_loc = Location::new_for_error("subst.res", 10, 15);
        let handler = Lambda::Lapply(Box::new(crate::lambda::Apply {
            ap_func: Box::new(Lambda::Lvar(id("g", 181))),
            ap_args: vec![Lambda::Lapply(Box::new(crate::lambda::Apply {
                ap_func: Box::new(Lambda::Lvar(id("h", 182))),
                ap_args: vec![Lambda::Lvar(parameter.clone())],
                ap_info: crate::lambda::ApInfo {
                    loc: inner_loc.clone(),
                    inlined: crate::lambda::InlineAttribute::Never,
                    status: crate::lambda::ApplyStatus::Uncurry,
                },
                ap_transformed_jsx: true,
            }))],
            ap_info: crate::lambda::ApInfo {
                loc: outer_loc.clone(),
                inlined: crate::lambda::InlineAttribute::Always,
                status: crate::lambda::ApplyStatus::InferFull,
            },
            ap_transformed_jsx: true,
        }));
        let result = simplify_indexed(
            Lambda::LstaticCatch(
                Box::new(Lambda::LstaticRaise(93, vec![Lambda::unit()])),
                (93, vec![parameter]),
                Box::new(handler),
            ),
            200,
        );
        let Lambda::Llet(_, _, _, body) = result else {
            panic!("expected fresh argument let")
        };
        let Lambda::Lapply(outer) = *body else {
            panic!("expected outer application")
        };
        // lambda_traverse.ml `shallow_map_sharing` rebuilds a changed
        // application with its `ap_transformed_jsx`.
        assert!(outer.ap_transformed_jsx);
        assert_eq!(outer.ap_info.loc, outer_loc);
        assert_eq!(outer.ap_info.status, crate::lambda::ApplyStatus::InferFull);
        let [Lambda::Lapply(inner)] = outer.ap_args.as_slice() else {
            panic!("expected nested application")
        };
        assert!(inner.ap_transformed_jsx);
        assert_eq!(inner.ap_info.loc, inner_loc);
        assert_eq!(inner.ap_info.status, crate::lambda::ApplyStatus::Uncurry);

        let raw = Lambda::Lsequence(
            Box::new(Lambda::Lprim(Box::new(crate::lambda::PrimInfo {
                primitive: Primitive::Pnot,
                args: vec![Lambda::true_()],
                loc: Location::none(),
            }))),
            Box::new(Lambda::Lapply(Box::new(crate::lambda::Apply {
                ap_func: Box::new(Lambda::Lvar(id("empty", 183))),
                ap_args: vec![],
                ap_info: crate::lambda::ApInfo {
                    loc: Location::none(),
                    inlined: crate::lambda::InlineAttribute::Default,
                    status: crate::lambda::ApplyStatus::Na,
                },
                ap_transformed_jsx: true,
            }))),
        );
        let mut store = IndexedLambda::from_lambda(raw);
        let root = store.root();
        // `subst_lambda` with nothing to replace keeps every node.
        let rewritten = substitute(&mut store, &VariableSubstitution::new(), root);
        assert_eq!(rewritten, root);
    }

    #[test]
    fn direct_and_nested_wrapper_eta_match_reference_order_and_fallback_metadata() {
        let wrappers = [
            Primitive::PnullToOpt,
            Primitive::PnullUndefinedToOpt,
            Primitive::PisNull,
            Primitive::PisNullUndefined,
            Primitive::Ptypeof,
        ];
        for (index, wrapper) in wrappers.into_iter().enumerate() {
            for nested in [false, true] {
                let body_loc = Location::new_for_error("eta.res", 1, 2);
                let apply_loc = Location::new_for_error("eta.res", 10, 20);
                let left = id("left", 200 + index as i32 * 2);
                let right = id("right", 201 + index as i32 * 2);
                let inner = if nested {
                    Lambda::Lprim(Box::new(crate::lambda::PrimInfo {
                        primitive: Primitive::Pidentity,
                        args: vec![Lambda::Lvar(left.clone()), Lambda::Lvar(right.clone())],
                        loc: body_loc.clone(),
                    }))
                } else {
                    Lambda::Lvar(left.clone())
                };
                let body_args = if nested {
                    vec![inner]
                } else {
                    vec![inner, Lambda::Lvar(right.clone())]
                };
                let function = Lambda::function_(
                    2,
                    vec![left, right],
                    Lambda::Lprim(Box::new(crate::lambda::PrimInfo {
                        primitive: wrapper.clone(),
                        args: body_args,
                        loc: body_loc,
                    })),
                    crate::lambda::FunctionAttribute::default(), crate::location::Location::none(),
                );
                let apply = Lambda::Lapply(Box::new(crate::lambda::Apply {
                    ap_func: Box::new(Lambda::LstaticRaise(91, vec![])),
                    ap_args: vec![
                        Lambda::Lconst(Constant::int(1)),
                        Lambda::Lconst(Constant::int(2)),
                    ],
                    ap_info: crate::lambda::ApInfo {
                        loc: apply_loc.clone(),
                        inlined: crate::lambda::InlineAttribute::Never,
                        status: crate::lambda::ApplyStatus::Uncurry,
                    },
                    ap_transformed_jsx: true,
                }));
                let input = Lambda::LstaticCatch(Box::new(apply), (91, vec![]), Box::new(function));
                if nested {
                    assert_exit_parity(input, 300);
                } else {
                    // OCaml `lam.ml:160-172` lets direct wrappers reach the
                    // generic eta arm. Current recursive Rust returns early
                    // from its broader wrapper match.
                    let result = simplify_indexed(input, 300);
                    let Lambda::Lprim(info) = result else {
                        panic!("expected direct wrapper eta")
                    };
                    assert_eq!(info.primitive, wrapper);
                    assert_eq!(info.loc, apply_loc);
                    assert!(matches!(
                        info.args.as_slice(),
                        [
                            Lambda::Lconst(Constant::Int { i: 1, .. }),
                            Lambda::Lconst(Constant::Int { i: 2, .. })
                        ]
                    ));
                }
            }
        }

        let parameter = id("fallback", 250);
        let attr = crate::lambda::FunctionAttribute {
            async_: true,
            inline: crate::lambda::InlineAttribute::Never,
            is_a_functor: true,
            return_unit: true,
            directive: Some("use server".into()),
            one_unit_arg: true,
        };
        let function = Lambda::function_(
            7,
            vec![parameter.clone()],
            Lambda::Lprim(Box::new(crate::lambda::PrimInfo {
                primitive: Primitive::Ptypeof,
                args: vec![Lambda::Lconst(Constant::int(0))],
                loc: Location::none(),
            })),
            attr, crate::location::Location::none(),
        );
        let result = simplify_indexed(
            Lambda::LstaticCatch(
                Box::new(Lambda::Lapply(Box::new(crate::lambda::Apply {
                    ap_func: Box::new(Lambda::LstaticRaise(92, vec![])),
                    ap_args: vec![Lambda::Lvar(parameter)],
                    ap_info: crate::lambda::ApInfo {
                        loc: Location::none(),
                        inlined: crate::lambda::InlineAttribute::Always,
                        status: crate::lambda::ApplyStatus::InferFull,
                    },
                    ap_transformed_jsx: true,
                }))),
                (92, vec![]),
                Box::new(function),
            ),
            300,
        );
        let Lambda::Lapply(apply) = result else {
            panic!("expected eta fallback application")
        };
        assert!(apply.ap_transformed_jsx);
        assert_eq!(apply.ap_info.status, crate::lambda::ApplyStatus::InferFull);
        let Lambda::Lfunction(function) = *apply.ap_func else {
            panic!("expected function metadata")
        };
        assert_eq!(function.arity, 7);
        assert!(function.attr.async_ && function.attr.is_a_functor && function.attr.one_unit_arg);
        assert_eq!(function.attr.directive.as_deref(), Some("use server"));
    }

    #[test]
    fn unsupported_switch_constants_do_not_select_the_default() {
        for constant in [
            Constant::JsTrue,
            Constant::string("value"),
            Constant::Float("1.5".into()),
        ] {
            for default in [None, Some(Box::new(Lambda::false_()))] {
                let switch = Lambda::Lswitch(
                    Box::new(Lambda::Lconst(constant.clone())),
                    Box::new(LambdaSwitch {
                        sw_consts_full: false,
                        sw_consts: vec![],
                        sw_blocks_full: false,
                        sw_blocks: vec![],
                        sw_failaction: default,
                        sw_dispatch: SwitchDispatch::Direct,
                    }),
                );
                let catch = Lambda::LstaticCatch(
                    Box::new(Lambda::unit()),
                    (90, vec![]),
                    Box::new(Lambda::true_()),
                );
                let result =
                    simplify_indexed(Lambda::Lsequence(Box::new(switch), Box::new(catch)), 100);
                let Lambda::Lsequence(first, _) = result else {
                    panic!("expected sequence")
                };
                assert!(
                    matches!(*first, Lambda::Lswitch(_, _)),
                    "unsupported constant selected default"
                );
            }
        }
    }

    #[test]
    fn no_catch_keeps_nodes_and_rebuilds_use_reference_smart_constructors() {
        let loc = Location::none();
        let not_true = || {
            Lambda::Lprim(Box::new(crate::lambda::PrimInfo {
                primitive: Primitive::Pnot,
                args: vec![Lambda::true_()],
                loc: loc.clone(),
            }))
        };
        // `Lambda_traverse.shallow_map_sharing` keeps unchanged nodes, so
        // `simplify_exits` leaves `not true` alone; a rebuild folds it.
        assert!(matches!(simplify_indexed(not_true(), 0), Lambda::Lprim(_)));
        assert!(matches!(rebuild_indexed(not_true()), Lambda::Lconst(Constant::JsFalse)));
        let result = simplify_indexed(
            Lambda::Lsequence(
                Box::new(not_true()),
                Box::new(Lambda::LstaticRaise(99, vec![])),
            ),
            0,
        );
        assert!(matches!(result, Lambda::Lsequence(first, second)
            if matches!(*first, Lambda::Lprim(_))
                && matches!(*second, Lambda::LstaticRaise(99, ref args) if args.is_empty())));
    }

    /// Rebuild the root through the indexed smart constructors.
    fn rebuild_indexed(lambda: Lambda) -> Lambda {
        let mut store = IndexedLambda::from_lambda(lambda);
        let root = store.root();
        let snapshot = store.snapshot(root);
        let rebuilt = append_rebuilt(&mut store, snapshot);
        store.materialize_node(rebuilt)
    }

    #[test]
    fn inherited_smart_constructor_debt_follows_ocaml_reference() {
        use crate::types::VariantTag;
        for tag_type in [
            crate::types::VariantLiteralTag::Float("1.0".into()),
            crate::types::VariantLiteralTag::BigInt("1".into()),
        ] {
            let condition = Constant::Constructor(VariantTag {
                name: "C".into(),
                literal: Some(tag_type),
            });
            let result = rebuild_indexed(
                Lambda::LifThenElse(
                    Box::new(Lambda::Lconst(condition)),
                    Box::new(Lambda::true_()),
                    Box::new(Lambda::false_()),
                ),
            );
            assert!(matches!(result, Lambda::LifThenElse(_, _, _)));
        }

        let int_tag = VariantTag {
            name: "One".into(),
            literal: Some(crate::types::VariantLiteralTag::Int(1)),
        };
        let result = rebuild_indexed(
            Lambda::Lswitch(
                Box::new(Lambda::Lconst(Constant::int(1))),
                Box::new(LambdaSwitch {
                    sw_consts_full: true,
                    sw_consts: vec![(
                        SwitchKey::Constructor(crate::types::VariantConstructorCase::Constant(
                            int_tag,
                        )),
                        Lambda::true_(),
                    )],
                    sw_blocks_full: true,
                    sw_blocks: vec![],
                    sw_failaction: Some(Box::new(Lambda::false_())),
                    sw_dispatch: SwitchDispatch::Direct,
                }),
            ),
        );
        assert!(matches!(result, Lambda::Lconst(Constant::JsTrue)));

        let commented = rebuild_indexed(
            Lambda::Lswitch(
                Box::new(Lambda::Lconst(Constant::int_with_comment(
                    1,
                    crate::lambda::lam_constant::PointerInfo::Some("commented".into()),
                ))),
                Box::new(LambdaSwitch {
                    sw_consts_full: true,
                    sw_consts: vec![(
                        SwitchKey::Constructor(crate::types::VariantConstructorCase::Constant(
                            VariantTag {
                                name: "One".into(),
                                literal: Some(crate::types::VariantLiteralTag::Int(1)),
                            },
                        )),
                        Lambda::true_(),
                    )],
                    sw_blocks_full: true,
                    sw_blocks: vec![],
                    sw_failaction: Some(Box::new(Lambda::false_())),
                    sw_dispatch: SwitchDispatch::Direct,
                }),
            ),
        );
        assert!(matches!(commented, Lambda::Lconst(Constant::JsFalse)));

        for (operation, expected) in [
            (crate::lambda::Comparison::Eq, Constant::JsFalse),
            (crate::lambda::Comparison::Neq, Constant::JsTrue),
        ] {
            let left = Constant::Constructor(VariantTag {
                name: "A".into(),
                literal: None,
            });
            let right = Constant::Constructor(VariantTag {
                name: "B".into(),
                literal: None,
            });
            let result = rebuild_indexed(
                Lambda::Lprim(Box::new(crate::lambda::PrimInfo {
                    primitive: Primitive::Pintcomp(operation),
                    args: vec![Lambda::Lconst(left), Lambda::Lconst(right)],
                    loc: Location::none(),
                })),
            );
            assert_eq!(
                format!("{result:?}"),
                format!("{:?}", Lambda::Lconst(expected))
            );
        }
    }

    #[test]
    fn simplify_exits_rewrites_all_control_families_in_source_order() {
        let x = id("x", 1);
        let mut lambda = Lambda::LstaticCatch(
            Box::new(Lambda::LstaticRaise(20, vec![])),
            (20, vec![]),
            Box::new(Lambda::LglobalModule(id("M", 0))),
        );
        lambda = Lambda::Lassign(x.clone(), Box::new(lambda));
        lambda = Lambda::Lfor_await_of(
            x.clone(),
            Box::new(Lambda::Lvar(x.clone())),
            Box::new(lambda),
        );
        lambda = Lambda::Lfor_of(
            x.clone(),
            Box::new(Lambda::Lvar(x.clone())),
            Box::new(lambda),
        );
        lambda = Lambda::Lfor(
            x.clone(),
            Box::new(Lambda::Lvar(x.clone())),
            Box::new(Lambda::Lconst(Constant::int(3))),
            DirectionFlag::Upto,
            Box::new(lambda),
        );
        lambda = Lambda::LifThenElse(
            Box::new(Lambda::Lvar(x.clone())),
            Box::new(lambda),
            Box::new(Lambda::unit()),
        );
        lambda = Lambda::LtryWith(Box::new(lambda), id("exn", 2), Box::new(Lambda::unit()));
        lambda = Lambda::LstringSwitch(
            Box::new(Lambda::Lvar(x.clone())),
            vec![("case".into(), lambda)],
            Some(Box::new(Lambda::unit())),
        );
        lambda = Lambda::Lswitch(
            Box::new(Lambda::Lvar(x)),
            Box::new(LambdaSwitch {
                sw_consts_full: true,
                sw_consts: vec![(SwitchKey::Int(0), lambda)],
                sw_blocks_full: true,
                sw_blocks: vec![],
                sw_failaction: None,
                sw_dispatch: SwitchDispatch::Direct,
            }),
        );
        assert_exit_parity(lambda, 40);
    }

    #[test]
    fn shared_raise_occurrences_are_freshened_independently() {
        let x = id("x", 1);
        let mut store = IndexedLambda::from_lambda(Lambda::LstaticRaise(30, vec![Lambda::unit()]));
        let shared_raise = store.root();
        let body = store.append(NodeSnapshot::Sequence(shared_raise, shared_raise));
        let handler = store.append(NodeSnapshot::Var(x.clone()));
        let root = store.append(NodeSnapshot::StaticCatch(body, 30, vec![x], handler));
        store.set_root(root);
        let mut context = IndexedLambdaContext::from_store(store, []);
        let id_gen = IdGenerator::with_start_stamp(100);
        context.simplify_exits(&id_gen);
        let Lambda::Lsequence(first, second) = context.materialize() else {
            panic!("expected sequence");
        };
        let (Lambda::Llet(_, first_id, _, _), Lambda::Llet(_, second_id, _, _)) = (*first, *second)
        else {
            panic!("expected independently substituted lets");
        };
        assert_ne!(first_id, second_id);
        assert_eq!(id_gen.current_stamp(), 102);
    }

    #[test]
    fn storage_metrics_partition_large_child_and_case_payloads() {
        let loc = Location::none();
        let cases = (0..32)
            .map(|case| {
                // A dead catch in each payload makes the pass rewrite it
                // (shallow_map_sharing only rebuilds changed nodes).
                let args = (0..16)
                    .map(|value| {
                        let constant = Lambda::Lconst(Constant::int(case * 16 + value));
                        if value == 0 {
                            Lambda::LstaticCatch(
                                Box::new(constant),
                                (1000 + case, vec![]),
                                Box::new(Lambda::unit()),
                            )
                        } else {
                            constant
                        }
                    })
                    .collect::<Vec<_>>();
                (
                    SwitchKey::Int(case),
                    Lambda::Lprim(Box::new(crate::lambda::PrimInfo {
                        primitive: Primitive::Pmakearray,
                        args,
                        loc: loc.clone(),
                    })),
                )
            })
            .collect::<Vec<_>>();
        let lambda = Lambda::Lswitch(
            Box::new(Lambda::Lvar(id("scrutinee", 400))),
            Box::new(LambdaSwitch {
                sw_consts_full: true,
                sw_consts: cases,
                sw_blocks_full: true,
                sw_blocks: vec![],
                sw_failaction: None,
                sw_dispatch: SwitchDispatch::Direct,
            }),
        );
        let mut context = IndexedLambdaContext::from_lambda(lambda, []);
        context.simplify_exits(&IdGenerator::with_start_stamp(500));
        let metrics = context.storage_measurements();
        assert!(metrics.current_live_side_payload_shallow_bytes > 32 * 16 * 4);
        assert!(metrics.superseded_unreachable_side_payload_shallow_bytes > 32 * 16 * 4);
        assert_eq!(metrics.metadata_retained_only_side_payload_shallow_bytes, 0);
        assert_eq!(
            metrics.current_live_side_payload_shallow_bytes
                + metrics.metadata_retained_only_side_payload_shallow_bytes
                + metrics.superseded_unreachable_side_payload_shallow_bytes,
            metrics.side_payload_shallow_occupied_bytes
        );
        assert!(
            metrics.side_payload_shallow_capacity_bytes
                >= metrics.side_payload_shallow_occupied_bytes
        );
    }

    #[test]
    fn collect_exits_collect_keeps_one_store_and_identifier_frontier() {
        let x = id("x", 1);
        let f = id("f", 2);
        let lambda = Lambda::Llet(
            LetKind::Strict,
            f.clone(),
            Box::new(Lambda::function_(
                1,
                vec![x.clone()],
                Lambda::LstaticCatch(
                    Box::new(Lambda::LstaticRaise(12, vec![Lambda::unit()])),
                    (12, vec![x.clone()]),
                    Box::new(Lambda::Lvar(x)),
                ),
                crate::lambda::FunctionAttribute {
                    inline: crate::lambda::InlineAttribute::Always,
                    ..crate::lambda::FunctionAttribute::default()
                }, crate::location::Location::none(),
            )),
            Box::new(Lambda::Lvar(f.clone())),
        );
        let mut tree_meta = LamStats::new(vec![f.clone()]);
        tree_collect::collect_info(&mut tree_meta, &lambda);
        let tree_gen = IdGenerator::with_start_stamp(50);
        let expected = tree::simplify_exits(&lambda, &tree_gen);
        tree_collect::collect_info(&mut tree_meta, &expected);
        let mut context = IndexedLambdaContext::from_lambda(lambda, [f.clone()]);
        context.collect_info();
        let retained_before = context
            .metadata()
            .ident_tbl
            .values()
            .filter(|kind| {
                matches!(
                    kind,
                    IndexedIdKind::FunctionId {
                        lambda: Some(_),
                        ..
                    }
                )
            })
            .count();
        let allocations_before = context.node_count();
        let indexed_gen = IdGenerator::with_start_stamp(50);
        context.simplify_exits(&indexed_gen);
        let retained_before_recollect = context.storage_measurements();
        assert!(retained_before_recollect.metadata_retained_only_side_payload_shallow_bytes > 0);
        assert_eq!(context.substitution_table_peak_unique_nodes(), 1);
        context.collect_info();
        assert_eq!(
            format!("{expected:#?}"),
            format!("{:#?}", context.materialize())
        );
        assert_eq!(tree_gen.current_stamp(), indexed_gen.current_stamp());
        assert!(retained_before > 0);
        assert!(context.node_count() > allocations_before);
        match (
            tree_meta.ident_tbl.get(&f),
            context.metadata().ident_tbl.get(&f),
        ) {
            (
                Some(IdKind::FunctionId {
                    arity: tree_arity,
                    lambda: Some((tree_lambda, tree_rec)),
                }),
                Some(IndexedIdKind::FunctionId {
                    arity: indexed_arity,
                    lambda: Some((indexed_lambda, indexed_rec)),
                }),
            ) => {
                assert_eq!(tree_arity, indexed_arity);
                assert_eq!(tree_rec, indexed_rec);
                assert_eq!(
                    format!("{tree_lambda:#?}"),
                    format!("{:#?}", context.store().materialize_node(*indexed_lambda))
                );
            }
            kinds => panic!("collect metadata differs after exits: {kinds:?}"),
        }
        assert!(
            context
                .metadata()
                .ident_tbl
                .values()
                .any(|kind| matches!(kind, IndexedIdKind::FunctionId { .. }))
        );

        let first = context.storage_measurements();
        assert_eq!(first.node_allocations, 11);
        assert_eq!(first.node_allocations, context.node_count());
        assert_eq!(first.current_root_edge_visits, 5);
        assert_eq!(first.current_root_unique_nodes, 6);
        assert_eq!(first.metadata_unique_nodes, 4);
        assert_eq!(first.live_unique_nodes, 6);
        assert_eq!(first.superseded_nodes, 5);
        assert_eq!(
            first.superseded_nodes,
            first.node_allocations - first.live_unique_nodes
        );
        assert!(first.hot_node_capacity_bytes >= first.hot_node_occupied_bytes);
        assert!(
            first.side_payload_shallow_capacity_bytes >= first.side_payload_shallow_occupied_bytes
        );
        assert!(!first.nested_heap_bytes_included);
        assert_eq!(
            first.current_live_side_payload_shallow_bytes
                + first.metadata_retained_only_side_payload_shallow_bytes
                + first.superseded_unreachable_side_payload_shallow_bytes,
            first.side_payload_shallow_occupied_bytes
        );

        // Without a catch nothing changes, so `shallow_map_sharing` keeps
        // every node.
        context.simplify_exits(&indexed_gen);
        let second = context.storage_measurements();
        assert_eq!(second.node_allocations, first.node_allocations);
        assert_eq!(
            second.current_root_unique_nodes,
            first.current_root_unique_nodes
        );
        assert_eq!(second.superseded_nodes, first.superseded_nodes);
    }
}
