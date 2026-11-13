//! Record duplication and rest; C: try_compile_record_spread, P: compile_primitive_js.
use super::*;
use crate::bir::j::plain;
use crate::bir::{JsId, JsPayload, ListId, PropertyKey};
use crate::lambda::{LamLoc, lam_primitive::Primitive};

/// Decoded record-copy operands; source nodes live in a list pool.
pub(super) struct Record {
    operands: ListId,
    info: JsId,
    loc: LamLoc,
}

#[derive(Default)]
pub(super) struct Scratch {
    operands: Vec<NodeId>,
    pub(super) keys: Vec<PropertyKey>,
    pub(super) values: Vec<NodeId>,
}

impl State {
    /// C: try_compile_record_spread / collect_record_spread_overrides.
    /// O(k + field-name bytes) for k consecutive writes, with one inspection
    /// per spine node. No initializer or override expression is walked here.
    pub(super) fn record_copy(
        &mut self,
        var: VarId,
        value: NodeId,
        mut body: NodeId,
    ) -> Option<Record> {
        let View::Prim {
            primitive,
            args: [init],
        } = self.source.view(value)
        else {
            return None;
        };
        if !matches!(
            self.arena.primitive(primitive).primitive,
            Primitive::Pduprecord
        ) {
            return None;
        }
        let loc = self.arena.primitive(primitive).loc;
        let init = *init;
        let mut scratch = std::mem::take(&mut self.object_scratch);
        let operands = &mut scratch.operands;
        let keys = &mut scratch.keys;
        debug_assert!(operands.is_empty() && keys.is_empty());
        operands.push(init);
        keys.push(PropertyKey::RecordSpread);
        let result = (|| {
        loop {
            self.primitive_steps += 1;
            match self.source.view(body) {
                View::Var { var: end } if end == var => break,
                View::Seq { first, second } => {
                    self.primitive_steps += 2;
                    let View::Prim {
                        primitive,
                        args: [target, value],
                    } = self.source.view(first)
                    else {
                        return None;
                    };
                    let Primitive::Psetfield(_, field) = &self.arena.primitive(primitive).primitive
                    else {
                        return None;
                    };
                    if !matches!(self.source.view(*target), View::Var { var: target } if target == var)
                    {
                        return None;
                    }
                    operands.push(*value);
                    use crate::lambda::SetFieldDbgInfo::*;
                    let name = match field {
                        RecordSet(name) | RecordInlineSet(name) | RecordExtensionSet(name) => *name,
                    };
                    keys.push(PropertyKey::Literal(self.arena.intern_text(name.as_str())));
                    body = second;
                }
                _ => return None,
            }
        }
        keys[1..].reverse();
        let info = self.arena.object_info(keys);
        let operands = self.source.lists.push(operands);
        Some(Record { operands, info, loc })
        })();
        scratch.operands.clear(); scratch.keys.clear();
        self.object_scratch = scratch;
        result
    }

    /// C: try_compile_record_spread. O(k) child scheduling, in source order.
    pub(super) fn record_children(&self, cx: Cx, record: &Record, into: &mut Vec<(Cx, NodeId)>) {
        into.extend(self.source.lists.get(record.operands).iter().map(|&node| {
            (
                Cx {
                    cont: Cont::Value(Tail::No),
                    ..cx
                },
                node,
            )
        }));
    }

    /// C: try_compile_record_spread. O(k + s), where k is the number of
    /// operands and s the emitted statement slots. Concatenate, do not hold
    /// arguments: the legacy record-copy form deliberately does not sequence.
    pub(super) fn finish_record(
        &mut self,
        cx: Cx,
        record: Record,
        children: impl Iterator<Item = Probed>,
    ) -> Probed {
        let mut start = None;
        let mut values = std::mem::take(&mut self.object_scratch.values);
        debug_assert!(values.is_empty());
        for child in children {
            self.primitive_steps += 1;
            let Probed::Out(out) = child else {
                unreachable!("record operand realized")
            };
            start.get_or_insert(out.stmts.start);
            values.push(out.value.expect("record operand value"));
        }
        values[1..].reverse();
        let value = plain::node(
            &mut self.arena,
            View::JObject {
                values: &values,
                info: record.info,
            },
            0,
        );
        values.clear();
        self.object_scratch.values = values;
        if self
            .locations
            .as_ref()
            .and_then(|locations| locations.get(record.loc))
            .is_some_and(|loc| !loc.loc_ghost && loc.loc_start.cnum >= 0)
        {
            self.arena.set_cold(
                value,
                crate::bir::Cold {
                    loc: record.loc,
                    comment: None,
                },
            );
            let mut flags = self.arena.node(value).flags();
            flags.0 |= crate::bir::NodeFlags::JS_LOC_PRESENT;
            self.arena.nodes[value.index()].set_flags(flags);
        }
        self.primitive_result(
            cx,
            self.statements.since(Span {
                start: start.expect("record initializer"),
                len: 0,
            }),
            value,
        )
    }

    /// P: compile_primitive_js Pduprecord. O(1), one spread object.
    pub(super) fn duplicate_record(&mut self, source: NodeId) -> NodeId {
        let info = self
            .arena
            .object_info(&[PropertyKey::RecordSpread]);
        plain::node(
            &mut self.arena,
            View::JObject {
                values: &[source],
                info,
            },
            0,
        )
    }

    /// P: compile_primitive_js PrecordRest. O(k + label bytes) for k excluded
    /// fields; store labels once in the arena's cold rest descriptor.
    pub(super) fn record_rest(&mut self, source: NodeId, excluded: &[String]) -> NodeId {
        let start = self.arena.pools.rest_fields.len() as u32;
        for name in excluded {
            self.primitive_steps += 1;
            let name = self.arena.intern_text(name);
            self.arena.pools.rest_fields.push(crate::bir::RestField { name, binding: None });
        }
        let info = self.arena.js_info(JsPayload::Rest(crate::bir::RestSpan {
            start, len: excluded.len() as u32,
        }));
        plain::node(
            &mut self.arena,
            View::JRecordRest {
                value: source,
                info,
            },
            0,
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ident::IdentFlags;
    use crate::lambda::{SetFieldDbgInfo, arena::LamArena};

    #[test]
    fn record_resume_size() {
        assert_eq!(std::mem::size_of::<Record>(), 12);
    }

    #[test]
    fn record_primitives_all_continuations() {
        for primitive in [
            Primitive::Pduprecord,
            Primitive::PrecordRest(vec![]),
            Primitive::PrecordRest(vec!["a".into(), "b".into()]),
        ] {
            let mut a = LamArena::new();
            let source = a.var(Ident::new("source", 10, IdentFlags::NONE));
            let root = a.prim_raw(primitive, &[source], LamLoc::NONE);
            super::super::oracle_tests::compare(a, root);
        }
    }

    #[test]
    fn record_copy_all_continuations() {
        for count in [0, 3] {
            let (a, root) = copy(count);
            super::super::oracle_tests::compare(a, root);
        }
    }

    fn copy(count: usize) -> (LamArena, crate::lambda::arena::Lam) {
        let mut a = LamArena::new();
        let id = Ident::new("copy", 11, IdentFlags::NONE);
        let source = a.var(Ident::new("source", 10, IdentFlags::NONE));
        let init = a.prim_raw(Primitive::Pduprecord, &[source], LamLoc::NONE);
        let mut body = a.var(id);
        for i in (0..count).rev() {
            let target = a.var(id);
            let value = a.var(Ident::new("value", 12, IdentFlags::NONE));
            let set = a.prim_raw(
                Primitive::Psetfield(
                    i as i32,
                    SetFieldDbgInfo::RecordSet(crate::name::Name::new(&format!("field{i}"))),
                ),
                &[target, value],
                LamLoc::NONE,
            );
            body = a.seq_raw(set, body);
        }
        let root = a.let_(LetKind::Strict, id, init, body);
        (a, root)
    }

    #[test]
    fn top_level_copy_matches_shared_tail() {
        let (a, root) = copy(3);
        let mut compiler = crate::lambda::lam_compile::LambdaCompiler::new();
        let (_, check) =
            compiler.compile_deps_program_with_lower_check::<true>(a, root, Default::default());
        crate::bir::shadow::check_lower(check.unwrap(), "RecordCopy.res", false).unwrap();
    }

    #[test]
    fn ten_thousand_record_rest_exclusions_are_linear() {
        let mut a = LamArena::new();
        let source = a.var(Ident::new("source", 10, IdentFlags::NONE));
        let root = a.prim_raw(
            Primitive::PrecordRest(vec!["field".into(); 10_000]),
            &[source],
            LamLoc::NONE,
        );
        let input = crate::bir::bridge::import_lambda(&a, root).unwrap();
        let root = input.root;
        let mut state = State::new(input);
        let out = state.probe(Cx::value(), root).unwrap();
        assert_eq!(state.source_steps, 2);
        assert_eq!(state.primitive_steps, 10_002);
        let lowered = state.complete(Cx::value(), out);
        lowered
            .program
            .arena
            .validate(Some(lowered.program.root))
            .unwrap();
    }

    #[test]
    fn rejected_record_candidates_clear_retained_storage() {
        let (a, root) = copy(1);
        let input = crate::bir::bridge::import_lambda(&a, root).unwrap();
        let root = input.root;
        let mut state = State::new(input);
        let View::Let { var, value: Some(value), body } = state.source.view(root) else { panic!() };
        // The initializer is valid, but its own Prim is not an override spine.
        assert!(state.record_copy(var, value, value).is_none());
        let before = (state.object_scratch.operands.capacity(), state.object_scratch.keys.capacity());
        let allocations = allocation_counter::measure(|| {
            for _ in 0..10_000 { assert!(state.record_copy(var, value, value).is_none()); }
        });
        assert_eq!(allocations.count_total, 0, "{allocations:?}");
        assert_eq!((state.object_scratch.operands.capacity(), state.object_scratch.keys.capacity()), before);
        assert!(state.object_scratch.operands.is_empty() && state.object_scratch.keys.is_empty());
        assert!(state.record_copy(var, value, body).is_some());
        assert!(state.object_scratch.operands.is_empty() && state.object_scratch.keys.is_empty());
    }

    #[test]
    fn ten_thousand_record_overrides_lower_without_allocations() {
        let (a, root) = copy(10_000);
        let input = crate::bir::bridge::import_lambda(&a, root).unwrap();
        let root = input.root;
        let mut state = State::new(input);
        let run = |s: &mut State| {
            let out = s.probe(Cx::returning(), root).unwrap();
            let out = s.realize(Cx::returning(), out);
            for node in s.statements.statements(out.stmts) { s.arena.release(node); }
            if let Some(value) = out.value { s.arena.release(value); }
            s.statements.kill(out.stmts);
        };
        let lists = state.arena.lists.storage_shape().0;
        let source_lists = state.source.lists.storage_shape().0;
        let keys = state.arena.pools.property_keys.len();
        run(&mut state);
        state.arena.lists.reserve_test_growth(state.arena.lists.storage_shape().0 - lists);
        state.source.lists.reserve_test_growth(state.source.lists.storage_shape().0 - source_lists);
        state.arena.pools.property_keys.reserve(state.arena.pools.property_keys.len() - keys);
        state.arena.pools.js.reserve(1);
        state.free.reserve_repeat();
        let capacities = |s: &State| {
            [s.object_scratch.operands.capacity(), s.object_scratch.keys.capacity(), s.object_scratch.values.capacity(),
                s.arena.nodes.capacity(), s.arena.parents.capacity(), s.arena.free_nodes.capacity(), s.arena.release_stack.capacity(),
                s.arena.lists.storage_shape().1, s.source.lists.storage_shape().1, s.arena.pools.property_keys.capacity(),
                s.arena.pools.js.capacity(), s.traversal.work.capacity(), s.traversal.values.capacity(), s.traversal.children.capacity()]
        };
        let before = capacities(&state);
        let free_before = state.free.capacities();
        let statements_before = state.statements.capacities();
        let source = state.source_steps;
        let primitive = state.primitive_steps;
        let allocations = allocation_counter::measure(|| run(&mut state));
        assert_eq!(allocations.count_total, 0, "{allocations:?}");
        assert_eq!(capacities(&state), before);
        assert_eq!(state.free.capacities(), free_before);
        assert_eq!(state.statements.capacities(), statements_before);
        assert_eq!(state.source_steps - source, 10_002);
        assert_eq!(state.primitive_steps - primitive, 40_002);
        assert!(state.object_scratch.operands.is_empty() && state.object_scratch.keys.is_empty() && state.object_scratch.values.is_empty());
    }

    #[test]
    fn ten_thousand_record_overrides_are_linear() {
        let (a, root) = copy(10_000);
        let input = crate::bir::bridge::import_lambda(&a, root).unwrap();
        let root = input.root;
        let mut state = State::new(input);
        let out = state.probe(Cx::value(), root).unwrap();
        assert_eq!(state.source_steps, 10_002);
        assert_eq!(state.primitive_steps, 40_002);
        let lowered = state.complete(Cx::value(), out);
        lowered
            .program
            .arena
            .validate(Some(lowered.program.root))
            .unwrap();
    }
}
