//! H12: K:60 compile_constant, K:34 compile_some_constant, K:26 nested_some_none.
use super::State;
use crate::bir::{Cold, ConstId, Constant, JsPayload, NodeId, View};
use crate::lambda::LamLoc;
use crate::lambda::lam_constant::{ConstructorRuntimeTag, PointerInfo};
use crate::types::VariantLiteralTag;

pub(super) enum Work {
    Enter(ConstId),
    Block(ConstId, u32),
    Some,
}
impl State {
    /// H12: K:48 compile_runtime_int. Large constructor integers print as floats.
    fn runtime_int(&mut self, n: i64) -> NodeId {
        if i32::try_from(n).is_ok() {
            self.number(Constant::Int(n))
        } else {
            self.float(&n.to_string())
        }
    }
    /// H12: K:60 compile_constant, numeric leaf with preserved spelling.
    fn number(&mut self, value: Constant) -> NodeId {
        let value = self.arena.intern_const(value);
        self.pure_expression(View::JNumber { value }, 0)
    }
    /// H12: K:60 compile_constant, float payload has already been validated by import.
    fn float(&mut self, spelling: &str) -> NodeId {
        let value = self
            .arena
            .intern_float(spelling)
            .expect("valid imported float");
        self.pure_expression(View::JNumber { value }, 0)
    }
    /// H12: K:60 compile_constant, decoded string bytes are not re-escaped here.
    fn string(&mut self, text: &str) -> NodeId {
        let text = self.arena.intern_text(text);
        self.pure_expression(View::JStr { text }, 0)
    }
    /// N7: K:55 commented_number; decoration remains until the printer migration.
    fn comment(&mut self, node: NodeId, text: &str) -> NodeId {
        let comment = Some(self.arena.intern_text(text));
        self.arena.set_cold(
            node,
            Cold {
                loc: LamLoc::NONE,
                comment,
            },
        );
        node
    }
    /// H12: K:60 compile_constant. An explicit stack also handles deeply nested
    /// constant blocks and options; each constant occurrence is visited once.
    pub(super) fn constant(&mut self, root: ConstId) -> NodeId {
        let mut work = std::mem::take(&mut self.constant_work);
        let mut values = std::mem::take(&mut self.constant_values);
        let mut children = std::mem::take(&mut self.constant_children);
        work.push(Work::Enter(root));
        while let Some(task) = work.pop() {
            match task {
                Work::Enter(id) => {
                    self.constant_steps += 1;
                    // Compound metadata remains immutable in the source pool.
                    if let Constant::Block { fields, .. } = self.arena.constant(id) {
                        let fields = self.arena.constant_fields(*fields);
                        work.push(Work::Block(id, fields.len() as u32));
                        work.extend(fields.iter().rev().copied().map(Work::Enter));
                        continue;
                    }
                    let constant = self.arena.constant(id).clone();
                    let mut none = false;
                    let value = match constant {
                        Constant::Block { .. } => unreachable!("compound scheduled before leaf decoding"),
                        Constant::Some(inner) => {
                            work.push(Work::Some);
                            work.push(Work::Enter(inner));
                            continue;
                        }
                        Constant::Null => self.pure_expression(View::JNull, 0),
                        Constant::Undefined(unit) => {
                            none = true;
                            self.pure_expression(View::JUndefined, u16::from(unit))
                        }
                        Constant::ModuleAlias => {
                            none = true;
                            self.pure_expression(View::JUndefined, 0)
                        }
                        Constant::Bool(b) => self.pure_expression(View::JBool, u16::from(b)),
                        Constant::Int(n) => self.number(Constant::Int(n)),
                        Constant::NativeInt(n) => self.float(&n.to_string()),
                        Constant::Char(n) => self.number(Constant::Char(n)),
                        Constant::Float(_) | Constant::BigInt(_) => {
                            self.pure_expression(View::JNumber { value: id }, 0)
                        }
                        Constant::String(text)
                        | Constant::ImmString(text)
                        | Constant::Pointer(text) => self.pure_expression(View::JStr { text }, 0),
                        Constant::Constructor(tag) => {
                            if tag.name == "[]" {
                                let value = self.number(Constant::Int(0));
                                self.comment(value, &tag.name)
                            } else {
                                match tag.literal {
                                    VariantLiteralTag::Int(n) => {
                                        self.number(Constant::Int(i64::from(n as i32)))
                                    }
                                    VariantLiteralTag::String(s) => self.string(&s),
                                    VariantLiteralTag::Float(s) => self.float(&s),
                                    VariantLiteralTag::BigInt(s) => {
                                        let (positive, digits) =
                                            crate::types::typecore::parse_bigint_literal(&s);
                                        let text = self.arena.intern_text(&format!(
                                            "{}{digits}",
                                            if positive { "+" } else { "-" }
                                        ));
                                        self.number(Constant::BigInt(text))
                                    }
                                    VariantLiteralTag::Bool(b) => {
                                        self.pure_expression(View::JBool, u16::from(b))
                                    }
                                    VariantLiteralTag::Null => self.pure_expression(View::JNull, 0),
                                    VariantLiteralTag::Undefined => {
                                        none = true;
                                        self.pure_expression(View::JUndefined, 0)
                                    }
                                }
                            }
                        }
                        Constant::DecoratedInt {
                            value,
                            native,
                            comment,
                        } => {
                            if let PointerInfo::Constructor(tag) = &comment {
                                if !native {
                                    let node = match &tag.runtime_tag {
                                        Some(ConstructorRuntimeTag::Int(n)) => self.runtime_int(*n),
                                        Some(ConstructorRuntimeTag::String(s)) => self.string(s),
                                        Some(ConstructorRuntimeTag::Float(s)) => self.float(s),
                                        Some(ConstructorRuntimeTag::BigInt(s)) => {
                                            let text = self.arena.intern_text(&format!("+{s}"));
                                            self.number(Constant::BigInt(text))
                                        }
                                        Some(ConstructorRuntimeTag::Bool(b)) => {
                                            self.pure_expression(View::JBool, u16::from(*b))
                                        }
                                        Some(ConstructorRuntimeTag::Null) => {
                                            self.pure_expression(View::JNull, 0)
                                        }
                                        Some(ConstructorRuntimeTag::Undefined) => {
                                            self.pure_expression(View::JUndefined, 0)
                                        }
                                        None if tag.name != "[]" => self.string(&tag.name),
                                        None => {
                                            let node = self.number(Constant::Int(value));
                                            self.comment(node, &tag.name)
                                        }
                                    };
                                    values.push((node, false));
                                    continue;
                                }
                            }
                            let node = if native {
                                self.float(&value.to_string())
                            } else {
                                self.number(Constant::Int(value))
                            };
                            match comment {
                                PointerInfo::None | PointerInfo::ShapeNone => node,
                                PointerInfo::Constructor(tag) => self.comment(node, &tag.name),
                                PointerInfo::AssertFalse => self.comment(node, "assert_false"),
                                PointerInfo::Some(s) | PointerInfo::PolyVariant(s) => {
                                    self.comment(node, &s)
                                }
                            }
                        }
                    };
                    values.push((value, none));
                }
                Work::Block(source, count) => {
                    let start = values.len() - count as usize;
                    children.extend(values.drain(start..).map(|(node, _)| node));
                    let info = self.arena.js_info(JsPayload::ConstantBlock(source));
                    let node = self.pure_expression(
                        View::JBlockLit {
                            values: &children,
                            info,
                        },
                        2,
                    );
                    children.clear();
                    values.push((node, false));
                }
                Work::Some => {
                    let (mut value, none) = values.pop().expect("constant option child");
                    if none && self.arena.node(value).op() == crate::bir::Op::JUndefined {
                        self.arena.release(value);
                        value = self.pure_expression(View::JUndefined, 0);
                    }
                    let node = self.pure_expression(View::JOptional { value }, u16::from(!none));
                    values.push((node, none));
                }
            }
        }
        assert_eq!(values.len(), 1);
        let result = values.pop().expect("constant result").0;
        self.constant_work = work;
        self.constant_values = values;
        self.constant_children = children;
        result
    }
}

#[cfg(test)]
mod allocation_tests {
    use super::*;
    use crate::bir::lower::Cx;
    use crate::lambda::{arena::LamArena, lam_constant::Constant as C, lam_primitive::{Primitive, Mutable}, TagInfo};

    #[test]
    fn ten_thousand_owned_block_tags_lower_without_allocations() {
        for kind in 0..3 {
            let mut a = LamArena::new();
            let tag = TagInfo::constructor("ConstructorWithOwnedShape", 1);
            let root = if kind == 0 {
                let elements = (0..10_000).map(|i| C::Block { tag_info: Box::new(tag.clone()), elements: vec![C::Int { i, comment: None }] }).collect();
                a.const_(C::Block { tag_info: Box::new(TagInfo::Tuple), elements })
            } else {
                let blocks: Vec<_> = (0..10_000).map(|i| {
                    let head = a.const_(C::Int { i, comment: None });
                    if kind == 1 { a.prim_raw(Primitive::Pmakeblock(tag.clone(), Mutable::Immutable), &[head], LamLoc::NONE) }
                    else { let tail = a.const_(C::Int { i: 0, comment: None }); a.prim_raw(Primitive::Pmakelist, &[head, tail], LamLoc::NONE) }
                }).collect();
                a.prim_raw(Primitive::Pmakearray, &blocks, LamLoc::NONE)
            };
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
            let infos = state.arena.pools.js.len();
            run(&mut state);
            if kind != 0 { assert_eq!(state.arena.pools.js.len() - infos, 1, "one unit shape, not a relocated allocation per block"); }
            state.arena.lists.reserve_test_growth(state.arena.lists.storage_shape().0 - lists);
            state.arena.pools.js.reserve(state.arena.pools.js.len() - infos);
            state.free.reserve_repeat();
            let capacities = |s: &State| [s.arena.nodes.capacity(), s.arena.parents.capacity(), s.arena.free_nodes.capacity(),
                s.arena.release_stack.capacity(), s.arena.lists.storage_shape().1, s.arena.pools.js.capacity(),
                s.arena.pools.block_index.capacity(), s.arena.pools.block_key_bytes.capacity(), s.arena.pools.block_key_scratch.capacity(),
                s.constant_work.capacity(), s.constant_values.capacity(), s.constant_children.capacity(),
                s.argument_outputs.capacity(), s.argument_values.capacity(), s.traversal.work.capacity(),
                s.traversal.values.capacity(), s.traversal.children.capacity()];
            let before = capacities(&state); let free_before = state.free.capacities();
            let statements_before = state.statements.capacities(); let visits = state.source_steps;
            let steps = state.constant_steps; let primitives = state.primitive_steps;
            let allocations = allocation_counter::measure(|| run(&mut state));
            println!("owned block kind={kind}: {allocations:?}, visits={}, constants={}, primitives={}", state.source_steps-visits, state.constant_steps-steps, state.primitive_steps-primitives);
            assert_eq!(allocations.count_total, 0);
            assert_eq!(capacities(&state), before); assert_eq!(state.free.capacities(), free_before);
            assert_eq!(state.statements.capacities(), statements_before);
            assert!(state.constant_work.is_empty() && state.constant_values.is_empty() && state.constant_children.is_empty());
            let (expected_source, expected_constants, expected_primitives) = [(1, 20_001, 0), (20_001, 10_000, 30_001), (30_001, 20_000, 40_001)][kind];
            assert_eq!(state.source_steps - visits, expected_source);
            assert_eq!(state.constant_steps - steps, expected_constants);
            assert_eq!(state.primitive_steps - primitives, expected_primitives);
        }
        assert_eq!(std::mem::size_of::<Work>(), 12);
    }
}
