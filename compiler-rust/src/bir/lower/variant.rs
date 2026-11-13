//! Named constructor dispatch (V: compile_named_variant_switch_*_statements).
//! Each side uses the common switch planner; source bodies are scheduled once.
use super::switch::{Form, Kind, Switch};
use super::*;
use crate::bir::j::{norm, plain};
use crate::bir::{CaseKey, SwitchHeader, SwitchId};
use crate::lambda::{SwitchCaseTag as Tag, SwitchDispatch, SwitchKey};
use crate::types::{VariantConstructorCase as Case, VariantLiteralTag as Literal};

/// Handle passed through SourceProbe; cold dispatch state stays in a pool.
#[derive(Clone, Copy)]
pub(super) struct Variant(pub u32);

/// A named side and the run emitted when its scheduled bodies finish.
struct Side {
    frame: Switch,
    count: usize,
    run: Span,
    block: bool,
}

#[derive(Clone, Copy)]
struct Imported { keys: crate::bir::KeySpan, tag_name: crate::bir::StrId }
#[derive(Default)]
pub(super) struct Metadata {
    switches: Vec<Option<Imported>>,
    numbers: Vec<[Option<crate::bir::ConstId>; 2]>,
}
/// Import immutable spelling/number descriptors into unit pools, never plans.
pub(super) fn prepare(arena: &mut Bir) -> Metadata {
    let switches = std::mem::take(&mut arena.pools.switches);
    let mut keys = std::mem::take(&mut arena.pools.switch_keys);
    let mut metadata = Metadata::default();
    let mut bigint = String::new();
    for h in &switches {
        let SwitchDispatch::Variant(facts) = &h.dispatch else { metadata.switches.push(None); continue };
        let view = SwitchHeader { keys: &keys[h.keys.start as usize..(h.keys.start + h.keys.len) as usize],
            clauses: &[], constants: h.constants, consts_full: h.consts_full, blocks_full: h.blocks_full,
            has_default: h.has_default, dispatch: &h.dispatch };
        if is_untagged(&view) { metadata.switches.push(None); continue; }
        let tag_name = arena.intern_text(facts.tag_name.as_deref().unwrap_or("TAG"));
        let start = keys.len() as u32;
        for i in 0..h.keys.len as usize {
            let key = &keys[h.keys.start as usize + i];
            let literal = match key {
                CaseKey::Lambda(SwitchKey::Constructor(Case::Constant(tag))) => &tag.literal,
                CaseKey::Lambda(SwitchKey::Constructor(Case::Block(block))) => &block.tag().literal,
                _ => unreachable!("variant constructor key"),
            };
            let key = match literal {
                Literal::String(s) => CaseKey::String(arena.intern_text(s)),
                Literal::Float(s) => {
                    let text = arena.intern_text(s);
                    let value = arena.intern_float(s).expect("valid constructor float");
                    metadata.numbers.resize(arena.pools.strings.len(), [None; 2]);
                    metadata.numbers[text.index()][0] = Some(value);
                    CaseKey::Float(text)
                }
                Literal::BigInt(s) => {
                    let text = arena.intern_text(s);
                    let positive = crate::types::typecore::parse_bigint_literal_into(s, &mut bigint);
                    bigint.insert(0, if positive { '+' } else { '-' });
                    let canonical = arena.intern_text(&bigint);
                    let value = arena.intern_const(crate::bir::Constant::BigInt(canonical));
                    bigint.clear();
                    metadata.numbers.resize(arena.pools.strings.len(), [None; 2]);
                    metadata.numbers[text.index()][1] = Some(value);
                    CaseKey::BigInt(text)
                }
                Literal::Int(i) => CaseKey::JavaScript(Tag::Int(i64::from(*i as i32))),
                Literal::Bool(b) => CaseKey::JavaScript(Tag::Bool(*b)),
                Literal::Null => CaseKey::JavaScript(Tag::Null),
                Literal::Undefined => CaseKey::JavaScript(Tag::Undefined),
            };
            keys.push(key);
        }
        metadata.switches.push(Some(Imported { keys: crate::bir::KeySpan { start, len: h.keys.len }, tag_name }));
    }
    arena.pools.switches = switches;
    arena.pools.switch_keys = keys;
    metadata
}

#[derive(Default)]
struct Sides([Option<Side>; 2]);
impl Sides {
    fn push(&mut self, side: Side) {
        let slot = self.0.iter_mut().find(|side| side.is_none()).expect("at most two named sides");
        *slot = Some(side);
    }
    fn len(&self) -> usize { usize::from(self.0[0].is_some()) + usize::from(self.0[1].is_some()) }
    fn iter(&self) -> impl Iterator<Item = &Side> { self.0.iter().flatten() }
}
impl std::ops::Index<usize> for Sides {
    type Output = Side;
    fn index(&self, index: usize) -> &Side { self.0[index].as_ref().expect("initialized named side") }
}
impl std::ops::IndexMut<usize> for Sides {
    fn index_mut(&mut self, index: usize) -> &mut Side { self.0[index].as_mut().expect("initialized named side") }
}

/// One named dispatch, never copied down a walk.
pub(super) struct Plan {
    scrutinee: NodeId,
    cont: Cont,
    start: Span,
    target: Option<VarId>,
    value: Option<NodeId>,
    sides: Sides,
    active: usize,
    mixed: bool,
    head: u32,
    tag_name: crate::bir::StrId,
    literals: u8,
}

/// V: untagged_switch precondition. O(keys), borrowed metadata only.
pub(super) fn is_untagged(h: &SwitchHeader<'_>) -> bool {
    let SwitchDispatch::Variant(facts) = &h.dispatch else {
        return false;
    };
    let n = h.constants as usize;
    !facts.block_types.is_empty()
        && ((h.consts_full && n == 0) || !(h.blocks_full && n == h.keys.len()))
        && h.keys[..n].iter().all(|k| {
            matches!(
                k,
                CaseKey::Lambda(SwitchKey::Constructor(Case::Constant(_)))
            )
        })
        && h.keys[n..].iter().all(|k| {
            matches!(
                k,
                CaseKey::Lambda(SwitchKey::Constructor(Case::Block(
                    crate::types::VariantBlock::Untagged { .. }
                )))
            )
        })
}

impl State {
    /// V: compile_named_variant_switch_*_statements / uses_named_variant_switch.
    /// O(keys + fingerprint/grouping work), with two bounded side plans.
    pub(super) fn named_variant(
        &mut self,
        cx: Cx,
        scrutinee: NodeId,
        operands: crate::bir::ListId,
        header: SwitchId,
    ) -> Result<Variant, Unsupported> {
        let h = self.arena.switch(header);
        let n = h.constants as usize;
        let total = h.keys.len();
        let const_full = h.consts_full;
        let block_full = h.blocks_full;
        let default = h
            .has_default
            .then(|| self.source.lists.get(operands)[total]);
        let SwitchDispatch::Variant(facts) = &h.dispatch else {
            unreachable!("named representation")
        };
        let literals = facts.literal_tags.iter().fold(0, |bits, tag| {
            bits | match tag {
                Literal::Null => 1,
                Literal::Undefined => 2,
                _ => 4,
            }
        });
        let imported = self.named_metadata.switches[header.index()].expect("imported named metadata");
        let tag_name = imported.tag_name;
        let start = self.statements.mark();
        let binding = match cx.cont {
            Cont::Value(_) => Some((LetKind::Strict, self.fresh_variable("tmp"))),
            Cont::Declare(kind, var) => Some((kind, var)),
            _ => None,
        };
        if let Some((kind, var)) = binding {
            let statement = plain::node(
                &mut self.arena,
                View::SDecl { var, value: None },
                kind as u16 | ((crate::js_ir::op::UsedStats::Used as u16) << 2),
            );
            self.statements.push(statement);
        }
        let target = binding.map(|(_, var)| var);
        let body_cx = Cx {
            cont: target.map_or(cx.cont, Cont::Assign),
            ..cx
        };
        let selected = if total == 0 || n == total && block_full {
            Some(false)
        } else if n == 0 && const_full {
            Some(true)
        } else {
            None
        };
        let mut sides = Sides::default();
        for block in [false, true] {
            if selected.is_some_and(|selected| selected != block) {
                continue;
            }
            let range = if block { n..total } else { 0..n };
            let full = if block { block_full } else { const_full };
            let fallback = if full { None } else { default };
            let actions = self.source.lists.slice_append(operands, range.start, range.len(), fallback);
            let side_header = self.arena.switch_record(crate::bir::SwitchRecord {
                keys: crate::bir::KeySpan { start: imported.keys.start + range.start as u32, len: range.len() as u32 },
                clauses: crate::bir::ClauseSpan { start: 0, len: 0 },
                constants: range.len() as u32,
                consts_full: full,
                blocks_full: false,
                has_default: fallback.is_some(),
                dispatch: SwitchDispatch::Direct,
            });
            let frame = self.plan_switch(body_cx, scrutinee, actions, side_header, Kind::Named)?;
            let side = self.switch_plan(frame);
            sides.push(Side {
                frame,
                count: side.groups.bodies.len as usize + usize::from(side.default.is_some()),
                run: Span::default(),
                block,
            });
        }
        let frame = Variant(self.variants.len() as u32);
        self.variants.push(Some(Plan {
            scrutinee,
            cont: cx.cont,
            start,
            target,
            value: None,
            sides,
            active: 0,
            mixed: selected.is_none(),
            head: 0,
            tag_name,
            literals,
        }));
        Ok(frame)
    }

    /// V: switch_case_expr. O(literal spelling), one owned J literal.
    pub(super) fn switch_key_expression(&mut self, key: &CaseKey) -> NodeId {
        match key {
            CaseKey::String(text) => plain::node(&mut self.arena, View::JStr { text: *text }, 0),
            CaseKey::Float(text) | CaseKey::BigInt(text) => {
                let slot = usize::from(matches!(key, CaseKey::BigInt(_)));
                let value = self.named_metadata.numbers[text.index()][slot].expect("imported numeric constructor");
                plain::node(&mut self.arena, View::JNumber { value }, 0)
            }
            CaseKey::Lambda(SwitchKey::Int(i)) => plain::int(&mut self.arena, *i),
            CaseKey::JavaScript(tag) => match tag {
                Tag::String(s) => plain::string(&mut self.arena, s),
                Tag::Int(i) if i32::try_from(*i).is_ok() => plain::int(&mut self.arena, *i as i32),
                Tag::Int(i) => {
                    use std::fmt::Write;
                    let mut spelling = std::mem::take(&mut self.switch_spelling);
                    debug_assert!(spelling.is_empty());
                    write!(&mut spelling, "{i}").unwrap();
                    let value = self.arena.intern_float(&spelling).unwrap();
                    spelling.clear(); self.switch_spelling = spelling;
                    plain::node(&mut self.arena, View::JNumber { value }, 0)
                }
                Tag::Float(s) => {
                    let value = self.arena.intern_float(s).unwrap();
                    plain::node(&mut self.arena, View::JNumber { value }, 0)
                }
                Tag::BigInt(s) => {
                    let mut spelling = std::mem::take(&mut self.switch_spelling);
                    debug_assert!(spelling.is_empty());
                    let positive = crate::types::typecore::parse_bigint_literal_into(s, &mut spelling);
                    spelling.insert(0, if positive { '+' } else { '-' });
                    let text = self.arena.intern_text(&spelling);
                    spelling.clear(); self.switch_spelling = spelling;
                    let value = self.arena.intern_const(crate::bir::Constant::BigInt(text));
                    plain::node(&mut self.arena, View::JNumber { value }, 0)
                }
                Tag::Bool(b) => plain::boolean(&mut self.arena, *b),
                Tag::Null => plain::node(&mut self.arena, View::JNull, 0),
                Tag::Undefined => plain::node(&mut self.arena, View::JUndefined, 0),
            },
            _ => unreachable!("lowered switch key"),
        }
    }

    /// V: named_variant_switch_needs_bound_scrutinee. O(1): the mixed shape
    /// selected at entry needs at most one binding, even for a pure expression.
    fn bind_named_scrutinee(&mut self, plan: &mut Plan, value: NodeId) {
        plan.value = Some(
            if plan.mixed && !matches!(self.arena.view(value), View::Var { .. }) {
                let var = self.fresh_variable("tmp");
                let statement =
                    crate::bir::j::declare(&mut self.arena, LetKind::Strict, var, value);
                self.statements.push(statement);
                self.pure_expression(View::Var { var }, 0)
            } else {
                value
            },
        );
    }

    /// Read the shared scrutinee without cloning a tree. O(1).
    fn named_scrutinee(&mut self, plan: &mut Plan) -> NodeId {
        let value = plan.value.unwrap();
        if plan.mixed {
            let View::Var { var } = self.arena.view(value) else {
                unreachable!("bound mixed scrutinee")
            };
            self.pure_expression(View::Var { var }, 0)
        } else {
            plan.value.take().unwrap()
        }
    }

    /// C: source child order, constants then blocks. O(number of groups).
    pub(super) fn variant_children(&self, cx: Cx, frame: Variant, into: &mut Vec<(Cx, NodeId)>) {
        let plan = self.variants[frame.0 as usize].as_ref().unwrap();
        into.push((
            Cx {
                cont: Cont::Value(Tail::No),
                ..cx
            },
            plan.scrutinee,
        ));
        for side in plan.sides.iter() {
            let p = self.switch_plan(side.frame);
            let body_cx = Cx {
                cont: plan.target.map_or(cx.cont, Cont::Assign),
                switch_depth: cx.switch_depth + u32::from(p.form == Form::General),
                ..cx
            };
            into.extend(
                self.grouped_bodies(&p.groups)
                    .iter()
                    .chain(p.default.iter())
                    .map(|&n| (body_cx, n)),
            );
        }
    }

    /// Finish a side and activate the next before its first source child.
    /// O(1) side transitions (at most two), plus the common switch costs.
    fn advance_variant(&mut self, cx: Cx, plan: &mut Plan, finish: bool) {
        let cx = Cx {
            cont: plan.target.map_or(plan.cont, Cont::Assign),
            ..cx
        };
        if finish {
            let side = &mut plan.sides[plan.active];
            let Probed::Out(out) = self.finish_switch(cx, side.frame) else {
                unreachable!("switch never probes")
            };
            if let Some(value) = out.value {
                self.arena.release(value);
            }
            side.run = out.stmts;
            plan.active += 1;
        }
        while plan.active < plan.sides.len() {
            let side = &plan.sides[plan.active];
            let frame = side.frame;
            let block = side.block;
            let has_keys = !self
                .arena
                .switch(self.switch_plan(frame).header)
                .keys
                .is_empty();
            let value = if has_keys {
                let value = self.named_scrutinee(plan);
                if block {
                    plain::node(
                        &mut self.arena,
                        View::JDot {
                            object: value,
                            property: plan.tag_name,
                            position: crate::js_ir::arena::FieldPos::NONE,
                        },
                        0,
                    )
                } else {
                    value
                }
            } else {
                plain::node(&mut self.arena, View::JUndefined, 0)
            };
            let start = self.statements.mark();
            let head = if self.switch_plan(frame).form != Form::General {
                self.statements.reserve()
            } else {
                0
            };
            let p = self.switches[frame.0 as usize].as_mut().unwrap();
            p.start = start;
            p.head = head;
            p.value = Some(value);
            if plan.sides[plan.active].count > 0 {
                break;
            }
            let Probed::Out(out) = self.finish_switch(cx, frame) else {
                unreachable!()
            };
            if let Some(value) = out.value {
                self.arena.release(value);
            }
            plan.sides[plan.active].run = out.stmts;
            plan.active += 1;
        }
    }

    /// Consume one source child in its scheduled continuation. O(1), plus
    /// the common group's statement transfer at its last child.
    pub(super) fn variant_child(
        &mut self,
        cx: Cx,
        frame: Variant,
        index: usize,
        child: Probed,
    ) -> Probed {
        let mut plan = self.variants[frame.0 as usize].take().unwrap();
        if index == 0 {
            let out = self.realize(cx, child);
            self.bind_named_scrutinee(&mut plan, out.value.unwrap());
            if plan.mixed {
                plan.head = self.statements.reserve();
            }
            self.advance_variant(cx, &mut plan, false);
        } else {
            let before: usize = plan.sides.iter().take(plan.active).map(|s| s.count).sum();
            let local = index - before;
            let side = &plan.sides[plan.active];
            self.switch_child(cx, side.frame, local, child);
            if local == side.count {
                self.advance_variant(cx, &mut plan, true);
            }
        }
        self.variants[frame.0 as usize] = Some(plan);
        Probed::Out(Out {
            stmts: self.statements.mark(),
            value: None,
            finished: Finished::False,
        })
    }

    /// V: is_int_tag. O(1), using literal-kind facts recorded at entry.
    fn named_literal_test(&mut self, plan: &mut Plan) -> NodeId {
        let flags = plan.literals;
        let eq = |state: &mut Self, plan: &mut Plan, null| {
            let left = state.named_scrutinee(plan);
            let right = plain::node(
                &mut state.arena,
                if null { View::JNull } else { View::JUndefined },
                0,
            );
            norm::je4_bin(&mut state.arena, crate::js_ir::BinOp::EqEqEq, left, right)
        };
        if flags & 4 == 0 && flags & 3 != 0 {
            if flags & 3 == 3 {
                let a = eq(self, plan, true);
                let b = eq(self, plan, false);
                return norm::je4_bin(&mut self.arena, crate::js_ir::BinOp::Or, a, b);
            }
            return eq(self, plan, flags & 1 != 0);
        }
        let null = (flags & 1 != 0).then(|| eq(self, plan, true));
        let value = self.named_scrutinee(plan);
        let typeof_ = plain::node(&mut self.arena, View::JTypeof { value }, 0);
        let object = plain::string(&mut self.arena, "object");
        let test = norm::je4_bin(
            &mut self.arena,
            crate::js_ir::BinOp::NotEqEq,
            typeof_,
            object,
        );
        if let Some(null) = null {
            norm::je4_bin(&mut self.arena, crate::js_ir::BinOp::Or, null, test)
        } else {
            test
        }
    }

    /// V: dispatch_named_variant_branches / compile_effect_if. O(statements
    /// consumed by J-S3); the two branch runs enter child lists once.
    pub(super) fn finish_variant(&mut self, cx: Cx, frame: Variant) -> Probed {
        let mut plan = self.variants[frame.0 as usize].take().unwrap();
        while self.variants.last().is_some_and(Option::is_none) {
            self.variants.pop();
        }
        if plan.mixed {
            let test = self.named_literal_test(&mut plan);
            let statement = self.if_statement(test, plan.sides[0].run, plan.sides[1].run);
            if matches!(cx.cont, Cont::Effect(Tail::No))
                && matches!(self.arena.view(statement), View::SBlock { statements } if statements.is_empty())
            {
                self.arena.release(statement);
            } else {
                self.place(plan.head, statement);
            }
        }
        if let Some(value) = plan.value {
            self.arena.release(value);
        }
        if matches!(cx.cont, Cont::Effect(Tail::Return(_))) {
            self.unnest(plan.start.start);
        }
        let value = match cx.cont {
            Cont::Value(_) => Some(self.pure_expression(
                View::Var {
                    var: plan.target.unwrap(),
                },
                0,
            )),
            Cont::Effect(Tail::No) => Some(plain::node(&mut self.arena, View::JUndefined, 0)),
            _ => None,
        };
        Probed::Out(Out {
            stmts: self.statements.since(plan.start),
            value,
            finished: Finished::False,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lambda::{
        LamLoc, arena::LamArena, lam_constant::Constant as C, lam_primitive::Primitive as P,
    };

    fn check(
        counts: [usize; 2],
        full: [bool; 2],
        default: bool,
        effect: bool,
        shared: bool,
        literal: Literal,
        scrutinee_call: bool,
    ) {
        let [constants, blocks] = counts;
        let mut a = LamArena::new();
        let mut x = a.var(Ident::new("x", 10, crate::ident::IdentFlags::NONE));
        if scrutinee_call {
            x = a.prim_raw(P::PinitMod, &[x], LamLoc::NONE);
        }
        let make_keys = |count, block| {
            (0..count)
                .map(|i| {
                    let tag = crate::types::VariantTag {
                        name: crate::name::Name::new(&format!("C{i}")),
                        literal: if i == 0 {
                            literal.clone()
                        } else {
                            Literal::String(format!("C{i}"))
                        },
                    };
                    SwitchKey::Constructor(if block {
                        Case::Block(crate::types::VariantBlock::Tagged(
                            crate::types::variant_runtime::TaggedBlock {
                                tag,
                                tag_name: Some("kind".into()),
                            },
                        ))
                    } else {
                        Case::Constant(tag)
                    })
                })
                .collect::<Vec<_>>()
        };
        let const_keys = make_keys(constants, false);
        let block_keys = make_keys(blocks, true);
        let actions: Vec<_> = (0..constants + blocks + usize::from(default))
            .map(|i| {
                let value = a.const_(C::Int {
                    i: if shared { 42 } else { i as i32 },
                    comment: None,
                });
                if effect {
                    a.prim_raw(P::PinitMod, &[value], LamLoc::NONE)
                } else {
                    value
                }
            })
            .collect();
        let actions = a.add_list(&actions);
        let info = a.add_switch(
            full[0],
            const_keys,
            full[1],
            block_keys,
            default,
            SwitchDispatch::Variant(crate::types::VariantMatchingFacts {
                tag_name: Some("kind".into()),
                literal_tags: vec![literal, Literal::String("other".into())],
                block_types: vec![],
            }),
        );
        let root = a.switch_raw(x, actions, info);
        super::super::oracle_tests::compare(a, root);
    }

    #[test]
    fn named_forms_in_every_continuation() {
        for constants in 0..=3 {
            for blocks in 0..=3 {
                for full in [[false, false], [true, false], [false, true], [true, true]] {
                    for default in [false, true] {
                        for shared in [false, true] {
                            for effect in [false, true] {
                                check(
                                    [constants, blocks],
                                    full,
                                    default,
                                    effect,
                                    shared,
                                    Literal::String("C0".into()),
                                    false,
                                );
                            }
                        }
                    }
                }
            }
        }
    }
    #[test]
    fn named_literal_tags_and_bound_scrutinees() {
        for literal in [
            Literal::Null,
            Literal::Undefined,
            Literal::Int(42),
            Literal::Bool(false),
            Literal::Float("1.5".into()),
            Literal::BigInt("123n".into()),
        ] {
            check([2, 2], [false, false], true, true, false, literal, true);
        }
    }
    #[test]
    fn ten_thousand_named_cases_and_nested_sides_are_linear() {
        for nested in [false, true] {
            let mut a = LamArena::new();
            let tag = crate::types::VariantTag {
                name: crate::name::Name::new("C"),
                literal: Literal::String("C".into()),
            };
            let key = SwitchKey::Constructor(Case::Constant(tag));
            let facts = crate::types::VariantMatchingFacts {
                tag_name: None,
                literal_tags: vec![Literal::String("C".into())],
                block_types: vec![],
            };
            let mut root = a.const_(C::Int {
                i: 42,
                comment: None,
            });
            if nested {
                let info = a.add_switch(
                    true,
                    [key],
                    true,
                    std::iter::empty(),
                    false,
                    SwitchDispatch::Variant(facts),
                );
                for _ in 0..10_000 {
                    let x = a.var(Ident::new("x", 10, crate::ident::IdentFlags::NONE));
                    let actions = a.add_list(&[root]);
                    root = a.switch_raw(x, actions, info);
                }
            } else {
                let actions: Vec<_> = (0..10_000)
                    .map(|i| a.const_(C::Int { i, comment: None }))
                    .collect();
                let actions = a.add_list(&actions);
                let info = a.add_switch(
                    true,
                    (0..10_000).map(|_| key.clone()),
                    true,
                    std::iter::empty(),
                    false,
                    SwitchDispatch::Variant(facts),
                );
                let x = a.var(Ident::new("x", 10, crate::ident::IdentFlags::NONE));
                root = a.switch_raw(x, actions, info);
            }
            let input = crate::bir::bridge::import_lambda(&a, root).unwrap();
            let root = input.root;
            let mut state = State::new(input);
            let out = state.probe(Cx::returning(), root).unwrap();
            assert_eq!(state.source_steps, if nested { 20_001 } else { 10_002 });
            assert_eq!(state.switch_visits, if nested { 0 } else { 10_000 });
            assert_eq!(state.switch_comparisons, 0);
            state.complete(Cx::returning(), out);
        }
    }

    fn named_fixture(per_side: usize, numeric: bool) -> (LamArena, crate::lambda::arena::Lam) {
        let mut a = LamArena::new();
        let mut constants = Vec::new(); let mut blocks = Vec::new(); let mut literals = Vec::new();
        for i in 0..per_side {
            let literal = if numeric { Literal::Float("1".into()) } else { Literal::String(format!("C{i}")) };
            literals.push(literal.clone());
            constants.push(SwitchKey::Constructor(Case::Constant(crate::types::VariantTag {
                name: crate::name::Name::new(&format!("C{i}")), literal,
            })));
            blocks.push(SwitchKey::Constructor(Case::Block(crate::types::VariantBlock::Tagged(
                crate::types::variant_runtime::TaggedBlock {
                    tag: crate::types::VariantTag { name: crate::name::Name::new(&format!("B{i}")),
                        literal: if numeric { Literal::BigInt("1".into()) } else { Literal::String(format!("B{i}")) } },
                    tag_name: Some("kind".into()),
                }))));
        }
        let actions: Vec<_> = (0..2*per_side+1).map(|i| a.const_(C::String(format!("body{i}")))).collect();
        let actions = a.add_list(&actions);
        let info = a.add_switch(false, constants, false, blocks, true,
            SwitchDispatch::Variant(crate::types::VariantMatchingFacts {
                tag_name: Some("kind".into()), literal_tags: literals, block_types: vec![],
            }));
        let x = a.var(Ident::new("x", 10, crate::ident::IdentFlags::NONE));
        let root = a.switch_raw(x, actions, info);
        (a, root)
    }

    #[test]
    fn numeric_constructor_spelling_does_not_merge_float_and_bigint_values() {
        let (a, root) = named_fixture(1, true);
        super::super::oracle_tests::compare(a, root);
    }

    #[test]
    fn ten_thousand_named_cases_lower_without_allocations() {
        for (count, numeric) in [(5_000, false), (1, true)] {
        let (a, root) = named_fixture(count, numeric);
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
        let keys = state.arena.pools.switch_keys.len();
        let headers = state.arena.pools.switches.len();
        run(&mut state);
        state.arena.lists.reserve_test_growth(state.arena.lists.storage_shape().0 - lists);
        state.source.lists.reserve_test_growth(state.source.lists.storage_shape().0 - source_lists);
        state.arena.pools.switch_keys.reserve(state.arena.pools.switch_keys.len() - keys);
        state.arena.pools.switches.reserve(state.arena.pools.switches.len() - headers);
        state.arena.pools.switch_clauses.reserve(state.arena.pools.switch_clauses.len());
        state.group_indices.reserve(state.group_indices.len()); state.group_nodes.reserve(state.group_nodes.len());
        state.switch_output_nodes.reserve(state.switch_output_nodes.len());
        state.switch_output_clauses.reserve(state.switch_output_clauses.len());
        state.free.reserve_repeat();
        let capacities = |s: &State| [s.arena.nodes.capacity(), s.arena.parents.capacity(), s.arena.free_nodes.capacity(),
            s.arena.release_stack.capacity(), s.arena.lists.storage_shape().1, s.source.lists.storage_shape().1,
            s.arena.pools.switch_keys.capacity(), s.arena.pools.switch_clauses.capacity(), s.arena.pools.switches.capacity(),
            s.group_indices.capacity(), s.group_nodes.capacity(), s.group_heads.capacity(), s.group_order.capacity(), s.group_table.capacity(),
            s.switch_output_nodes.capacity(), s.switch_output_clauses.capacity(), s.switches.capacity(), s.variants.capacity(),
            s.named_metadata.switches.capacity(), s.named_metadata.numbers.capacity(), s.switch_spelling.capacity(),
            s.traversal.work.capacity(), s.traversal.values.capacity(), s.traversal.children.capacity()];
        let before = capacities(&state);
        let free_before = state.free.capacities(); let statements_before = state.statements.capacities();
        let visits = state.source_steps; let groups = state.switch_group_steps;
        let allocations = allocation_counter::measure(|| run(&mut state));
        println!("named whole Lambda: {allocations:?}; visits={}, grouping={}", state.source_steps-visits, state.switch_group_steps-groups);
        assert_eq!(allocations.count_total, 0);
        assert_eq!(capacities(&state), before); assert_eq!(state.free.capacities(), free_before);
        assert_eq!(state.statements.capacities(), statements_before);
        assert_eq!(state.source_steps - visits, count * 2 + 4);
        assert_eq!(state.switch_group_steps - groups, if numeric { 2 } else { count * 4 });
        }
    }

    #[test]
    fn named_pool_sizes() {
        assert_eq!(std::mem::size_of::<Variant>(), 4);
        assert_eq!(std::mem::size_of::<Side>(), 24);
        assert_eq!(std::mem::size_of::<Sides>(), 48);
        assert_eq!(std::mem::size_of::<Imported>(), 12);
        assert_eq!(std::mem::size_of::<Plan>(), 112);
    }
}
