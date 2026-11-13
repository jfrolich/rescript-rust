//! Named constructor dispatch (V: compile_named_variant_switch_*_statements).
//! Each side uses the common switch planner; source bodies are scheduled once.
use super::switch::{Form, Kind, Switch};
use super::*;
use crate::bir::j::{norm, plain};
use crate::bir::{CaseKey, SwitchHeader, SwitchInput, SwitchId};
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

/// One named dispatch, never copied down a walk.
pub(super) struct Plan {
    scrutinee: NodeId,
    cont: Cont,
    start: Span,
    target: Option<VarId>,
    value: Option<NodeId>,
    sides: Vec<Side>,
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
        let tag_name = facts.tag_name.as_deref().unwrap_or("TAG").to_owned();
        let keys: Vec<_> = h
            .keys
            .iter()
            .map(|key| {
                let tag = match key {
                    CaseKey::Lambda(SwitchKey::Constructor(Case::Constant(tag))) => tag,
                    CaseKey::Lambda(SwitchKey::Constructor(Case::Block(block))) => block.tag(),
                    _ => unreachable!("constructor key in named switch"),
                };
                CaseKey::JavaScript(Self::literal_tag(&tag.literal))
            })
            .collect();
        let mut keys = [keys, Vec::new()];
        keys[1] = keys[0].split_off(n);
        let tag_name = self.arena.intern_text(&tag_name);
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
        let mut sides = Vec::with_capacity(2);
        for block in [false, true] {
            if selected.is_some_and(|selected| selected != block) {
                continue;
            }
            let range = if block { n..total } else { 0..n };
            let full = if block { block_full } else { const_full };
            let fallback = if full { None } else { default };
            let actions: Vec<_> = range
                .clone()
                .map(|i| self.source.lists.get(operands)[i])
                .chain(fallback)
                .collect();
            let actions = self.source.lists.push(&actions);
            let side_header = self.arena.switch_header(SwitchInput {
                keys: std::mem::take(&mut keys[usize::from(block)]),
                clauses: Vec::new(),
                constants: if block { (total - n) as u32 } else { n as u32 },
                consts_full: full,
                blocks_full: false,
                has_default: fallback.is_some(),
                dispatch: SwitchDispatch::Direct,
            });
            let frame = self.plan_switch(body_cx, scrutinee, actions, side_header, Kind::Named)?;
            let side = self.switch_plan(frame);
            sides.push(Side {
                frame,
                count: side.bodies.len() + usize::from(side.default.is_some()),
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

    /// V: literal_tag_value. O(literal spelling), copied only into owned J keys.
    pub(super) fn literal_tag(tag: &Literal) -> Tag {
        match tag {
            Literal::String(s) => Tag::String(s.clone()),
            Literal::Int(i) => Tag::Int(i64::from(*i as i32)),
            Literal::Float(s) => Tag::Float(s.clone()),
            Literal::BigInt(s) => Tag::BigInt(s.clone()),
            Literal::Bool(b) => Tag::Bool(*b),
            Literal::Null => Tag::Null,
            Literal::Undefined => Tag::Undefined,
        }
    }

    /// V: switch_case_expr. O(literal spelling), one owned J literal.
    pub(super) fn switch_key_expression(&mut self, key: &CaseKey) -> NodeId {
        match key {
            CaseKey::String(text) => plain::node(&mut self.arena, View::JStr { text: *text }, 0),
            CaseKey::Lambda(SwitchKey::Int(i)) => plain::int(&mut self.arena, *i),
            CaseKey::JavaScript(tag) => match tag {
                Tag::String(s) => plain::string(&mut self.arena, s),
                Tag::Int(i) if i32::try_from(*i).is_ok() => plain::int(&mut self.arena, *i as i32),
                Tag::Int(i) => {
                    let value = self.arena.intern_float(&i.to_string()).unwrap();
                    plain::node(&mut self.arena, View::JNumber { value }, 0)
                }
                Tag::Float(s) => {
                    let value = self.arena.intern_float(s).unwrap();
                    plain::node(&mut self.arena, View::JNumber { value }, 0)
                }
                Tag::BigInt(s) => {
                    let (positive, digits) = crate::types::typecore::parse_bigint_literal(s);
                    let text = self
                        .arena
                        .intern_text(&format!("{}{digits}", if positive { '+' } else { '-' }));
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
        for side in &plan.sides {
            let p = self.switch_plan(side.frame);
            let body_cx = Cx {
                cont: plan.target.map_or(cx.cont, Cont::Assign),
                switch_depth: cx.switch_depth + u32::from(p.form == Form::General),
                ..cx
            };
            into.extend(
                p.bodies
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
            let before: usize = plan.sides[..plan.active].iter().map(|s| s.count).sum();
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

    #[test]
    fn named_pool_sizes() {
        assert_eq!(std::mem::size_of::<Variant>(), 4);
        assert_eq!(std::mem::size_of::<Side>(), 24);
        assert_eq!(std::mem::size_of::<Plan>(), 88);
    }
}
