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
#[derive(Clone, Copy)]
struct TextSpan {
    start: u32,
    len: u32,
}
impl TextSpan {
    /// Cost: O(B) amortized for B appended spelling bytes; returns the new text span.
    fn append(text: &str, storage: &mut String) -> Self {
        let start = u32::try_from(storage.len()).expect("constant spelling pool");
        storage.push_str(text);
        Self {
            start,
            len: u32::try_from(text.len()).expect("constant spelling length"),
        }
    }
    /// Cost: O(1): borrows the recorded byte range without copying its spelling.
    fn get(self, storage: &str) -> &str {
        &storage[self.start as usize..(self.start + self.len) as usize]
    }
}
#[derive(Clone, Copy)]
enum LeafValue {
    Number(ConstId),
    Int(i64),
    FloatInt(i64),
    String(TextSpan),
    InternedString(crate::bir::StrId),
    Float(TextSpan),
    BigInt(TextSpan, bool),
    Bool(bool),
    Null,
    Undefined(bool),
}
struct Leaf {
    value: LeafValue,
    comment: Option<TextSpan>,
    none: bool,
}
/// Snapshot scalar values and spelling ranges, never an owned source payload.
/// Cost: O(B): copies B constructor-literal/comment bytes into scratch; scalar tags and
/// already-interned strings take O(1). Does not visit compound constant children.
fn leaf(arena: &crate::bir::Bir, id: ConstId, text: &mut String) -> Leaf {
    use LeafValue as V;
    debug_assert!(text.is_empty());
    let mut comment = None;
    let mut none = false;
    let value = match arena.constant(id) {
        Constant::Block { .. } | Constant::Some(_) => {
            unreachable!("compound constant scheduled separately")
        }
        Constant::Int(_) | Constant::Char(_) | Constant::Float(_) | Constant::BigInt(_) => {
            V::Number(id)
        }
        Constant::NativeInt(n) => V::FloatInt(*n),
        Constant::String(s) | Constant::ImmString(s) | Constant::Pointer(s) => {
            V::InternedString(*s)
        }
        Constant::Null => V::Null,
        Constant::Undefined(unit) => {
            none = true;
            V::Undefined(*unit)
        }
        Constant::ModuleAlias => {
            none = true;
            V::Undefined(false)
        }
        Constant::Bool(b) => V::Bool(*b),
        Constant::Constructor(tag) if tag.name == "[]" => {
            comment = Some(TextSpan::append(&tag.name, text));
            V::Int(0)
        }
        Constant::Constructor(tag) => match &tag.literal {
            VariantLiteralTag::Int(n) => V::Int(i64::from(*n as i32)),
            VariantLiteralTag::String(s) => V::String(TextSpan::append(s, text)),
            VariantLiteralTag::Float(s) => V::Float(TextSpan::append(s, text)),
            VariantLiteralTag::BigInt(s) => V::BigInt(TextSpan::append(s, text), true),
            VariantLiteralTag::Bool(b) => V::Bool(*b),
            VariantLiteralTag::Null => V::Null,
            VariantLiteralTag::Undefined => {
                none = true;
                V::Undefined(false)
            }
        },
        Constant::DecoratedInt {
            value,
            native,
            comment: decoration,
        } => {
            if let PointerInfo::Constructor(tag) = decoration {
                if !native {
                    // Decorated constructor undefined is not an option-none marker.
                    let value = match &tag.runtime_tag {
                        Some(ConstructorRuntimeTag::Int(n)) if i32::try_from(*n).is_ok() => {
                            V::Int(*n)
                        }
                        Some(ConstructorRuntimeTag::Int(n)) => V::FloatInt(*n),
                        Some(ConstructorRuntimeTag::String(s)) => {
                            V::String(TextSpan::append(s, text))
                        }
                        Some(ConstructorRuntimeTag::Float(s)) => {
                            V::Float(TextSpan::append(s, text))
                        }
                        Some(ConstructorRuntimeTag::BigInt(s)) => {
                            V::BigInt(TextSpan::append(s, text), false)
                        }
                        Some(ConstructorRuntimeTag::Bool(b)) => V::Bool(*b),
                        Some(ConstructorRuntimeTag::Null) => V::Null,
                        Some(ConstructorRuntimeTag::Undefined) => V::Undefined(false),
                        None if tag.name != "[]" => V::String(TextSpan::append(&tag.name, text)),
                        None => {
                            comment = Some(TextSpan::append(&tag.name, text));
                            V::Int(*value)
                        }
                    };
                    return Leaf {
                        value,
                        comment,
                        none: false,
                    };
                }
            }
            comment = match decoration {
                PointerInfo::None | PointerInfo::ShapeNone => None,
                PointerInfo::Constructor(tag) => Some(TextSpan::append(&tag.name, text)),
                PointerInfo::AssertFalse => Some(TextSpan::append("assert_false", text)),
                PointerInfo::Some(s) | PointerInfo::PolyVariant(s) => {
                    Some(TextSpan::append(s, text))
                }
            };
            if *native {
                V::FloatInt(*value)
            } else {
                V::Int(*value)
            }
        }
    };
    Leaf {
        value,
        comment,
        none,
    }
}
impl State {
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
    /// Cost: O(C + E + B): visits C constant occurrences and E child edges with enter/rebuild
    /// frames, normalizes/copies B spelling bytes, and pushes the resulting J nodes and
    /// operand runs. Repeated constant handles count as separate occurrences.
    pub(super) fn constant(&mut self, root: ConstId) -> NodeId {
        let mut work = std::mem::take(&mut self.constant_work);
        let mut values = std::mem::take(&mut self.constant_values);
        let mut children = std::mem::take(&mut self.constant_children);
        let mut text = std::mem::take(&mut self.constant_text);
        let mut encoding = std::mem::take(&mut self.constant_encoding);
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
                    if let Constant::Some(inner) = self.arena.constant(id) {
                        work.push(Work::Some);
                        work.push(Work::Enter(*inner));
                        continue;
                    }
                    let Leaf {
                        value,
                        comment,
                        none,
                    } = leaf(&self.arena, id, &mut text);
                    let mut value = match value {
                        LeafValue::Number(value) => {
                            self.pure_expression(View::JNumber { value }, 0)
                        }
                        LeafValue::Int(n) => self.number(Constant::Int(n)),
                        LeafValue::FloatInt(n) => {
                            use std::fmt::Write;
                            write!(&mut encoding, "{n}").unwrap();
                            self.float(&encoding)
                        }
                        LeafValue::String(s) => self.string(s.get(&text)),
                        LeafValue::InternedString(text) => {
                            self.pure_expression(View::JStr { text }, 0)
                        }
                        LeafValue::Float(s) => self.float(s.get(&text)),
                        LeafValue::BigInt(s, normalize) => {
                            if normalize {
                                let positive = crate::types::typecore::parse_bigint_literal_into(
                                    s.get(&text),
                                    &mut encoding,
                                );
                                encoding.insert(0, if positive { '+' } else { '-' });
                            } else {
                                encoding.push('+');
                                encoding.push_str(s.get(&text));
                            }
                            let text = self.arena.intern_text(&encoding);
                            self.number(Constant::BigInt(text))
                        }
                        LeafValue::Bool(b) => self.pure_expression(View::JBool, u16::from(b)),
                        LeafValue::Null => self.pure_expression(View::JNull, 0),
                        LeafValue::Undefined(unit) => {
                            self.pure_expression(View::JUndefined, u16::from(unit))
                        }
                    };
                    if let Some(comment) = comment {
                        value = self.comment(value, comment.get(&text));
                    }
                    text.clear();
                    encoding.clear();
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
        self.constant_text = text;
        self.constant_encoding = encoding;
        result
    }
}

#[cfg(test)]
mod allocation_tests {
    use super::*;
    use crate::bir::lower::Cx;
    use crate::lambda::{
        TagInfo,
        arena::LamArena,
        lam_constant::Constant as C,
        lam_primitive::{Mutable, Primitive},
    };

    #[test]
    fn nominal_and_decorated_undefined_keep_distinct_option_markers() {
        use crate::lambda::lam_constant::ConstructorTag;
        for decorated in [false, true] {
            let leaf = if decorated {
                C::Int {
                    i: 0,
                    comment: Some(Box::new(PointerInfo::Constructor(ConstructorTag {
                        name: "Undefined".into(),
                        const_: 1,
                        non_const: 0,
                        runtime_tag: Some(ConstructorRuntimeTag::Undefined),
                    }))),
                }
            } else {
                C::Constructor(crate::types::VariantTag {
                    name: "Undefined".into(),
                    literal: VariantLiteralTag::Undefined,
                })
            };
            let mut a = LamArena::new();
            let root = a.const_(C::Some(Box::new(C::Some(Box::new(leaf)))));
            super::super::oracle_tests::compare(a, root);
        }
    }

    #[test]
    fn ten_thousand_owned_constant_leaves_lower_without_allocations() {
        use crate::lambda::lam_constant::ConstructorTag;
        let mut a = LamArena::new();
        let leaves: Vec<_> = (0..10_000)
            .map(|i| {
                let runtime = |runtime_tag| {
                    Some(Box::new(PointerInfo::Constructor(ConstructorTag {
                        name: "RuntimeConstructor".into(),
                        const_: 1,
                        non_const: 0,
                        runtime_tag: Some(runtime_tag),
                    })))
                };
                let literal = |literal| {
                    C::Constructor(crate::types::VariantTag {
                        name: "NominalConstructor".into(),
                        literal,
                    })
                };
                let constant = match i % 8 {
                    0 => literal(VariantLiteralTag::String(format!("owned literal {i}"))),
                    1 => literal(VariantLiteralTag::Float(format!("{i}.25"))),
                    2 => literal(VariantLiteralTag::BigInt(format!("-0x{i:x}"))),
                    3 => C::Int {
                        i,
                        comment: runtime(ConstructorRuntimeTag::Int(i64::MAX - i64::from(i))),
                    },
                    4 => C::Int {
                        i,
                        comment: runtime(ConstructorRuntimeTag::BigInt(format!("{i}"))),
                    },
                    5 => C::NativeInt {
                        i: i64::from(i),
                        comment: Some(Box::new(PointerInfo::Some(format!("native comment {i}")))),
                    },
                    6 => C::Int {
                        i,
                        comment: Some(Box::new(PointerInfo::PolyVariant(format!(
                            "poly comment {i}"
                        )))),
                    },
                    _ => C::Int {
                        i,
                        comment: runtime(ConstructorRuntimeTag::String(format!(
                            "runtime string {i}"
                        ))),
                    },
                };
                a.const_(constant)
            })
            .collect();
        let root = a.prim_raw(Primitive::Pmakearray, &leaves, LamLoc::NONE);
        let input = crate::bir::bridge::import_lambda(&a, root).unwrap();
        let root = input.root;
        let mut state = State::new(input);
        let run = |s: &mut State| {
            let out = s.probe(Cx::returning(), root).unwrap();
            let out = s.realize(Cx::returning(), out);
            for node in s.statements.statements(out.stmts) {
                s.arena.release(node);
            }
            if let Some(value) = out.value {
                s.arena.release(value);
            }
            s.statements.kill(out.stmts);
        };
        let lists = state.arena.lists.storage_shape().0;
        let cold = state.arena.pools.cold.len();
        run(&mut state);
        state
            .arena
            .lists
            .reserve_test_growth(state.arena.lists.storage_shape().0 - lists);
        state
            .arena
            .pools
            .cold
            .reserve(state.arena.pools.cold.len() - cold);
        state.free.reserve_repeat();
        state.arena.js_scope.as_mut().unwrap().reserve_repeat();
        let capacities = |s: &State| {
            [
                s.arena.nodes.capacity(),
                s.arena.parents.capacity(),
                s.arena.free_nodes.capacity(),
                s.arena.release_stack.capacity(),
                s.arena.lists.storage_shape().1,
                s.arena.pools.cold.capacity(),
                s.arena.pools.consts.capacity(),
                s.arena.pools.const_keys.capacity(),
                s.arena.pools.const_key_bytes.capacity(),
                s.arena.pools.const_key_scratch.capacity(),
                s.arena.pools.const_index.capacity(),
                s.arena.pools.strings.capacity(),
                s.arena.pools.floats.capacity(),
                s.arena.pools.text_index.capacity(),
                s.constant_text.capacity(),
                s.constant_encoding.capacity(),
                s.constant_work.capacity(),
                s.constant_values.capacity(),
                s.argument_outputs.capacity(),
                s.argument_values.capacity(),
                s.traversal.work.capacity(),
                s.traversal.values.capacity(),
                s.traversal.children.capacity(),
            ]
        };
        let before = capacities(&state);
        let free_before = state.free.capacities();
        let stmts = state.statements.capacities();
        let visits = state.source_steps;
        let constants = state.constant_steps;
        let primitives = state.primitive_steps;
        let scope_before = state.arena.js_scope.as_ref().unwrap().capacities();
        let allocations = allocation_counter::measure(|| run(&mut state));
        assert_eq!(state.arena.js_scope.as_ref().unwrap().capacities(), scope_before);
        assert_eq!(allocations.count_total, 0, "{allocations:?}");
        assert_eq!(capacities(&state), before);
        assert_eq!(state.free.capacities(), free_before);
        assert_eq!(state.statements.capacities(), stmts);
        assert_eq!(
            (
                state.source_steps - visits,
                state.constant_steps - constants,
                state.primitive_steps - primitives
            ),
            (10_001, 10_000, 10_001)
        );
        assert!(state.constant_text.is_empty() && state.constant_encoding.is_empty());
        assert_eq!(std::mem::size_of::<LeafValue>(), 16);
        assert_eq!(std::mem::size_of::<TextSpan>(), 8);
    }

    #[test]
    fn ten_thousand_owned_block_tags_lower_without_allocations() {
        for kind in 0..4 {
            let mut a = LamArena::new();
            let tag = TagInfo::constructor("ConstructorWithOwnedShape", 1);
            let root = if kind == 3 {
                let exports = (0..10_000).map(|i| crate::ident::Ident::new("field", i + 1, crate::ident::IdentFlags::NONE)).collect();
                let elements = (0..10_000).map(|i| C::Int { i, comment: None }).collect();
                a.const_(C::Block { tag_info: Box::new(TagInfo::ModuleExport(exports)), elements })
            } else if kind == 0 {
                let elements = (0..10_000)
                    .map(|i| C::Block {
                        tag_info: Box::new(tag.clone()),
                        elements: vec![C::Int { i, comment: None }],
                    })
                    .collect();
                a.const_(C::Block {
                    tag_info: Box::new(TagInfo::Tuple),
                    elements,
                })
            } else {
                let blocks: Vec<_> = (0..10_000)
                    .map(|i| {
                        let head = a.const_(C::Int { i, comment: None });
                        if kind == 1 {
                            a.prim_raw(
                                Primitive::Pmakeblock(tag.clone(), Mutable::Immutable),
                                &[head],
                                LamLoc::NONE,
                            )
                        } else {
                            let tail = a.const_(C::Int {
                                i: 0,
                                comment: None,
                            });
                            a.prim_raw(Primitive::Pmakelist, &[head, tail], LamLoc::NONE)
                        }
                    })
                    .collect();
                a.prim_raw(Primitive::Pmakearray, &blocks, LamLoc::NONE)
            };
            let input = crate::bir::bridge::import_lambda(&a, root).unwrap();
            let root = input.root;
            let mut state = State::new(input);
            let run = |s: &mut State| {
                let out = s.probe(Cx::returning(), root).unwrap();
                let out = s.realize(Cx::returning(), out);
                for node in s.statements.statements(out.stmts) {
                    s.arena.release(node);
                }
                if let Some(value) = out.value {
                    s.arena.release(value);
                }
                s.statements.kill(out.stmts);
            };
            let lists = state.arena.lists.storage_shape().0;
            let infos = state.arena.pools.js.len();
            run(&mut state);
            if kind != 0 {
                assert_eq!(
                    state.arena.pools.js.len() - infos,
                    1,
                    "one unit shape, not a relocated allocation per block"
                );
            }
            state
                .arena
                .lists
                .reserve_test_growth(state.arena.lists.storage_shape().0 - lists);
            state
                .arena
                .pools
                .js
                .reserve(state.arena.pools.js.len() - infos);
            state.free.reserve_repeat();
        state.arena.js_scope.as_mut().unwrap().reserve_repeat();
            let capacities = |s: &State| {
                [
                    s.arena.nodes.capacity(),
                    s.arena.parents.capacity(),
                    s.arena.free_nodes.capacity(),
                    s.arena.release_stack.capacity(),
                    s.arena.lists.storage_shape().1,
                    s.arena.pools.js.capacity(),
                    s.arena.pools.block_index.capacity(),
                    s.arena.pools.block_key_bytes.capacity(),
                    s.arena.pools.block_key_scratch.capacity(),
                    s.constant_work.capacity(),
                    s.constant_values.capacity(),
                    s.constant_children.capacity(),
                    s.argument_outputs.capacity(),
                    s.argument_values.capacity(),
                    s.traversal.work.capacity(),
                    s.traversal.values.capacity(),
                    s.traversal.children.capacity(),
                ]
            };
            let before = capacities(&state);
            let free_before = state.free.capacities();
            let statements_before = state.statements.capacities();
            let visits = state.source_steps;
            let steps = state.constant_steps;
            let primitives = state.primitive_steps;
            let scope_before = state.arena.js_scope.as_ref().unwrap().capacities();
        let allocations = allocation_counter::measure(|| run(&mut state));
        assert_eq!(state.arena.js_scope.as_ref().unwrap().capacities(), scope_before);
            println!(
                "owned block kind={kind}: {allocations:?}, visits={}, constants={}, primitives={}",
                state.source_steps - visits,
                state.constant_steps - steps,
                state.primitive_steps - primitives
            );
            assert_eq!(allocations.count_total, 0);
            assert_eq!(capacities(&state), before);
            assert_eq!(state.free.capacities(), free_before);
            assert_eq!(state.statements.capacities(), statements_before);
            assert!(
                state.constant_work.is_empty()
                    && state.constant_values.is_empty()
                    && state.constant_children.is_empty()
            );
            let (expected_source, expected_constants, expected_primitives) = [
                (1, 20_001, 0),
                (20_001, 10_000, 30_001),
                (30_001, 20_000, 40_001),
                (1, 10_001, 0),
            ][kind];
            assert_eq!(state.source_steps - visits, expected_source);
            assert_eq!(state.constant_steps - steps, expected_constants);
            assert_eq!(state.primitive_steps - primitives, expected_primitives);
        }
        assert_eq!(std::mem::size_of::<Work>(), 12);
    }
}
