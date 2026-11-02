//! Indexed occurrence counting for `compiler/core/lam_pass_count.ml`.

use ahash::AHashMap;

use crate::ident::Ident;
use crate::lambda::indexed::{IndexedLambda, NodeId, NodeSnapshot, NodeView};
use crate::lambda::lam_beta_reduce_indexed::no_names_beta_reduce;
use crate::lambda::lam_compat::LetKind;
use crate::lambda::lam_pass_count::{OccurrenceTable, UsedInfo};

type LocalTable = AHashMap<Ident, usize>;

pub(crate) fn collect_occurs(store: &mut IndexedLambda, root: NodeId) -> OccurrenceTable {
    fn add_one_use(occ: &mut OccurrenceTable, local: &LocalTable, id: &Ident) {
        if let Some(index) = local.get(id).copied() {
            occ.values[index].times += 1;
        } else if let Some(index) = occ.entries.get(id).copied() {
            occ.absorb(
                index,
                UsedInfo {
                    times: 1,
                    captured: true,
                },
            );
        }
    }

    fn inherit_use(occ: &mut OccurrenceTable, local: &LocalTable, id: &Ident, bound: &Ident) {
        let inherited = occ.get(bound);
        if let Some(index) = local.get(id).copied() {
            occ.absorb(index, inherited);
        } else if let Some(index) = occ.entries.get(id).copied() {
            occ.absorb(
                index,
                UsedInfo {
                    captured: true,
                    ..inherited
                },
            );
        }
    }

    fn with_binding(
        occ: &mut OccurrenceTable,
        local: &mut LocalTable,
        id: &Ident,
        f: impl FnOnce(&mut OccurrenceTable, &mut LocalTable),
    ) {
        let index = occ.bind(id);
        let previous = local.insert(*id, index);
        f(occ, local);
        match previous {
            Some(previous) => {
                local.insert(*id, previous);
            }
            None => {
                local.remove(id);
            }
        }
    }

    fn count(
        store: &mut IndexedLambda,
        occ: &mut OccurrenceTable,
        local: &mut LocalTable,
        node: NodeId,
    ) {
        match store.snapshot(node) {
            NodeSnapshot::Function(_, _, body, _, _) => {
                count(store, occ, &mut LocalTable::new(), body)
            }
            NodeSnapshot::For(_, from, to, _, body) => {
                count(store, occ, local, from);
                count(store, occ, local, to);
                count(store, occ, &mut LocalTable::new(), body);
            }
            NodeSnapshot::ForOf(_, iterable, body)
            | NodeSnapshot::ForAwaitOf(_, iterable, body) => {
                count(store, occ, local, iterable);
                count(store, occ, &mut LocalTable::new(), body);
            }
            NodeSnapshot::While(condition, body) => {
                let empty = &mut LocalTable::new();
                count(store, occ, empty, condition);
                count(store, occ, empty, body);
            }
            NodeSnapshot::Var(id) => add_one_use(occ, local, &id),
            NodeSnapshot::Let(_, id, value, body)
                if matches!(store.view(value), NodeView::Var(_)) =>
            {
                let NodeView::Var(source) = store.view(value) else {
                    unreachable!()
                };
                let source = *source;
                with_binding(occ, local, &id, |occ, local| count(store, occ, local, body));
                inherit_use(occ, local, &source, &id);
            }
            NodeSnapshot::Let(kind, id, value, body) => {
                with_binding(occ, local, &id, |occ, local| count(store, occ, local, body));
                if kind == LetKind::Strict || occ.used(&id) {
                    count(store, occ, local, value);
                }
            }
            NodeSnapshot::Assign(_, value) => count(store, occ, local, value),
            NodeSnapshot::Prim(_, args, _) | NodeSnapshot::StaticRaise(_, args) => {
                for node in args {
                    count(store, occ, local, node);
                }
            }
            NodeSnapshot::LetRec(bindings, body) => {
                for (_, node) in bindings {
                    count(store, occ, local, node);
                }
                count(store, occ, local, body);
            }
            NodeSnapshot::Apply(function, args, _) => {
                if let NodeSnapshot::Function(_, params, body, attr, _) = store.snapshot(function)
                    && params.len() == args.len()
                    && !attr.async_
                    && attr.directive.is_none()
                {
                    let reduced = no_names_beta_reduce(store, &params, body, &args);
                    count(store, occ, local, reduced);
                } else {
                    count(store, occ, local, function);
                    for node in args {
                        count(store, occ, local, node);
                    }
                }
            }
            NodeSnapshot::Switch {
                scrutinee,
                consts_full,
                consts,
                blocks_full,
                blocks,
                fail_action,
                ..
            } => {
                if let Some(fail) = fail_action {
                    if !consts_full && !blocks_full {
                        count(store, occ, local, fail);
                        count(store, occ, local, fail);
                    } else {
                        assert!(!consts_full || !blocks_full);
                        count(store, occ, local, fail);
                    }
                }
                count(store, occ, local, scrutinee);
                for (_, node) in consts {
                    count(store, occ, local, node);
                }
                for (_, node) in blocks {
                    count(store, occ, local, node);
                }
            }
            NodeSnapshot::StringSwitch(scrutinee, cases, default) => {
                count(store, occ, local, scrutinee);
                for (_, node) in cases {
                    count(store, occ, local, node);
                }
                if let Some(node) = default {
                    count(store, occ, local, node);
                }
            }
            NodeSnapshot::StaticCatch(body, _, _, handler)
            | NodeSnapshot::TryWith(body, _, handler) => {
                count(store, occ, local, body);
                count(store, occ, local, handler);
            }
            NodeSnapshot::IfThenElse(a, b, c) => {
                count(store, occ, local, a);
                count(store, occ, local, b);
                count(store, occ, local, c);
            }
            NodeSnapshot::Sequence(a, b) => {
                count(store, occ, local, a);
                count(store, occ, local, b);
            }
            NodeSnapshot::GlobalModule(_)
            | NodeSnapshot::Const(_)
            | NodeSnapshot::Break
            | NodeSnapshot::Continue => {}
        }
    }

    let mut occ = OccurrenceTable::default();
    count(store, &mut occ, &mut LocalTable::new(), root);
    occ
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ident::IdentFlags;
    use crate::lambda::{Constant, FunctionAttribute, Lambda, SwitchDispatch};

    fn id(name: &str, stamp: i32) -> Ident {
        Ident::new(name, stamp, IdentFlags::NONE)
    }

    #[test]
    fn nested_scopes_keep_distinct_identity_counts() {
        let outer = id("value", 1);
        let inner = id("value", 2);
        let input = Lambda::let_(
            LetKind::Strict,
            outer,
            Lambda::const_(Constant::int(0)),
            Lambda::seq(
                Lambda::let_(
                    LetKind::Strict,
                    inner,
                    Lambda::var(outer),
                    Lambda::seq(Lambda::var(inner), Lambda::var(inner)),
                ),
                Lambda::var(outer),
            ),
        );
        let mut store = IndexedLambda::from_lambda(input);
        let root = store.root();
        let occurrences = collect_occurs(&mut store, root);
        assert_eq!(occurrences.get(&outer).times, 3);
        assert!(!occurrences.get(&outer).captured);
        assert_eq!(occurrences.get(&inner).times, 2);
        assert!(!occurrences.get(&inner).captured);
    }

    #[test]
    fn shared_child_is_counted_for_each_parent_edge() {
        let value = id("value", 1);
        let input = Lambda::let_(
            LetKind::Strict,
            value,
            Lambda::const_(Constant::int(0)),
            Lambda::var(value),
        );
        let mut store = IndexedLambda::from_lambda(input);
        let NodeView::Let(kind, id, init, body) = store.view(store.root()) else {
            panic!("expected let")
        };
        let (kind, id, init, body) = (kind, *id, init, body);
        let body = store.append_sequence(body, body);
        let root = store.append(NodeSnapshot::Let(kind, id, init, body));
        let occurrences = collect_occurs(&mut store, root);
        assert_eq!(occurrences.get(&value).times, 2);
        assert!(!occurrences.get(&value).captured);
    }

    fn switch_default_input(consts_full: bool, blocks_full: bool) -> (Ident, IndexedLambda) {
        let value = id("value", 1);
        let input = Lambda::let_(
            LetKind::Strict,
            value,
            Lambda::const_(Constant::int(0)),
            Lambda::Lswitch(
                Box::new(Lambda::const_(Constant::int(0))),
                Box::new(crate::lambda::LambdaSwitch {
                    sw_consts_full: consts_full,
                    sw_consts: vec![],
                    sw_blocks_full: blocks_full,
                    sw_blocks: vec![],
                    sw_failaction: Some(Box::new(Lambda::var(value))),
                    sw_dispatch: SwitchDispatch::Direct,
                }),
            ),
        );
        (value, IndexedLambda::from_lambda(input))
    }

    #[test]
    fn one_open_switch_table_counts_default_once() {
        for (consts_full, blocks_full) in [(true, false), (false, true)] {
            let (value, mut store) = switch_default_input(consts_full, blocks_full);
            let root = store.root();
            let occurrences = collect_occurs(&mut store, root);
            assert_eq!(occurrences.get(&value).times, 1);
        }
    }

    #[test]
    #[should_panic]
    fn both_full_switch_tables_reject_fail_action() {
        let (_, mut store) = switch_default_input(true, true);
        let root = store.root();
        collect_occurs(&mut store, root);
    }

    #[test]
    fn counts_capture_alias_inheritance_and_switch_default_edges() {
        let outer = id("outer", 1);
        let alias = id("alias", 2);
        let parameter = id("parameter", 3);
        let input = Lambda::let_(
            LetKind::Strict,
            outer,
            Lambda::const_(Constant::int(0)),
            Lambda::let_(
                LetKind::Alias,
                alias,
                Lambda::var(outer),
                Lambda::function_(
                    1,
                    vec![parameter],
                    Lambda::Lswitch(
                        Box::new(Lambda::const_(Constant::int(0))),
                        Box::new(crate::lambda::LambdaSwitch {
                            sw_consts_full: false,
                            sw_consts: vec![],
                            sw_blocks_full: false,
                            sw_blocks: vec![],
                            sw_failaction: Some(Box::new(Lambda::var(alias))),
                            sw_dispatch: SwitchDispatch::Direct,
                        }),
                    ),
                    FunctionAttribute::default(),
                    crate::location::Location::none(),
                ),
            ),
        );
        let mut store = IndexedLambda::from_lambda(input);
        let root = store.root();
        let occurrences = collect_occurs(&mut store, root);
        assert_eq!(occurrences.get(&alias).times, 2);
        assert!(occurrences.get(&alias).captured);
        assert_eq!(occurrences.get(&outer).times, 2);
        assert!(occurrences.get(&outer).captured);
    }
}
