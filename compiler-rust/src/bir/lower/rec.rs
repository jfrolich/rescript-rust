//! Recursive binding groups (BACKEND_LOWERING 5.3).
use super::*;
use crate::bir::{ListId, Op};
use crate::lambda::{lam_primitive::Primitive, TagInfo};

/// A group's source handle and pooled member slice; no per-group allocation.
#[derive(Clone, Copy)]
pub(super) struct Group {
    node: NodeId,
    base: u32,
    start: Span,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Mode { Declare, SelfInit, Update }

/// One dense row per binding. Completed statements are list-pool handles.
pub(super) struct Member {
    source: NodeId,
    var: VarId,
    code: Option<ListId>,
    placeholder: Option<NodeId>,
    end: u32,
    finished: Finished,
    mode: Mode,
}

impl State {
    /// O(m + a + newly indexed source slots): stable function/value partition
    /// and one inspection of each makeblock's a direct arguments. Membership
    /// in the group is a VarId interval test, never a scan of other members.
    pub(super) fn recursive_group(&mut self, node: NodeId) -> Result<Group, Unsupported> {
        let View::LetRec { values, first, .. } = self.source.view(node) else { unreachable!() };
        let base = self.rec_members.len() as u32;
        let count = values.len();
        let first = first.0;
        for functions in [true, false] {
            for i in 0..count {
                self.rec_steps += 1;
                let View::LetRec { values, .. } = self.source.view(node) else { unreachable!() };
                let source = values[i];
                if (self.source.node(source).op() == Op::Fun) != functions { continue; }
                let var = VarId(first + i as u32);
                let mode = self.recursive_mode(source, var, first, count as u32);
                if functions { self.register_tail_function(source, var); }
                self.rec_members.push(Member { source, var, code: None, placeholder: None,
                    end: 0, finished: Finished::False, mode });
            }
        }
        Ok(Group { node, base, start: self.statements.mark() })
    }

    /// O(a) for a block's direct arguments; constant for every other member.
    fn recursive_mode(&mut self, source: NodeId, own: VarId, first: u32, count: u32) -> Mode {
        let View::Prim { primitive, args } = self.source.view(source) else { return Mode::Declare };
        let Primitive::Pmakeblock(tag, _) = &self.arena.primitive(primitive).primitive else { return Mode::Declare };
        let mut simple = true;
        let mut self_only = match tag {
            TagInfo::Record(r) => r.fields.len() >= args.len(),
            TagInfo::RecordInlined(r) => r.num_nonconst == 1 && r.fields.len() >= args.len(),
            TagInfo::Constructor(c) => c.num_nonconst == 1,
            _ => false,
        };
        for &arg in args {
            self.rec_steps += 1;
            simple &= matches!(self.source.view(arg), View::Fun { .. } | View::Const { .. });
            self_only &= match self.source.view(arg) {
                View::Const { .. } => true,
                View::Var { var } => var == own || var.0 < first || var.0 - first >= count,
                _ => false,
            };
        }
        if simple { Mode::Declare } else if self_only { Mode::SelfInit } else { Mode::Update }
    }

    /// O(m): schedule the stable partition last first, then the body.
    pub(super) fn recursive_children(&self, cx: Cx, group: Group, into: &mut Vec<(Cx, NodeId)>) {
        let View::LetRec { values, body, .. } = self.source.view(group.node) else { unreachable!() };
        for member in self.rec_members[group.base as usize..group.base as usize + values.len()].iter().rev() {
            let cont = if member.mode == Mode::Declare { Cont::Declare(LetKind::Alias, member.var) }
                else { Cont::Value(Tail::No) };
            into.push((Cx { cont, ..cx }, member.source));
        }
        into.push((cx, body));
    }

    /// O(1) shape selection and construction; tag data remains borrowed.
    fn recursive_dummy(&mut self, tag: &TagInfo) -> NodeId {
        if matches!(tag, TagInfo::Tuple | TagInfo::ModuleExport(_))
            || matches!(tag, TagInfo::Record(r) if r.array) {
            self.pure_expression(View::JArray { values: &[] }, 1)
        } else {
            let info = self.arena.js_info(crate::bir::JsPayload::Object(Vec::new()));
            self.pure_expression(View::JObject { values: &[], info }, 0)
        }
    }

    /// O(a + field-name bytes): turn the self block's already lowered fields
    /// into writes. Moving the primitive pool permits borrowing field names
    /// across J construction without cloning a tag or allocating field strings.
    fn recursive_block(&mut self, member: usize, value: NodeId) {
        let row = &self.rec_members[member];
        let (var, mode, source) = (row.var, row.mode, row.source);
        let View::Prim { primitive, .. } = self.source.view(source) else { unreachable!() };
        let prims = std::mem::take(&mut self.arena.pools.prims);
        let Primitive::Pmakeblock(tag, _) = &prims[primitive.index()].primitive else { unreachable!() };
        if mode == Mode::Update {
            let target = self.pure_expression(View::Var { var }, 0);
            let call = self.primitive_runtime("Primitive_object", "updateDummy", &[target, value]);
            self.drop_pure_effect(call);
            let dummy = self.recursive_dummy(tag);
            self.rec_members[member].placeholder = Some(crate::bir::j::declare(&mut self.arena, LetKind::Variable, var, dummy));
        } else {
            let dummy = self.recursive_dummy(tag);
            let declaration = crate::bir::j::declare(&mut self.arena, LetKind::Variable, var, dummy);
            self.statements.push(declaration);
            let View::JBlockLit { values, .. } = self.arena.view(value) else { unreachable!("recursive self block") };
            let count = values.len();
            for index in 0..count {
                self.rec_steps += 1;
                let View::JBlockLit { values, .. } = self.arena.view(value) else { unreachable!() };
                let field_value = values[index];
                self.arena.detach(field_value);
                let target = self.pure_expression(View::Var { var }, 0);
                let mut numbered = [0u8; 24];
                let field = match tag {
                    TagInfo::Record(r) => r.fields[index].0.as_str(),
                    TagInfo::RecordInlined(r) => r.fields[index].0.as_str(),
                    TagInfo::Constructor(c) if c.name == "::" && index < 2 => if index == 0 { "hd" } else { "tl" },
                    TagInfo::Constructor(_) => {
                        use std::io::Write;
                        let mut cursor = std::io::Cursor::new(&mut numbered[..]);
                        write!(&mut cursor, "_{index}").expect("field index fits stack buffer");
                        let len = cursor.position() as usize;
                        std::str::from_utf8(&numbered[..len]).expect("decimal field")
                    }
                    _ => unreachable!("self-init classification"),
                };
                let set = self.primitive_set_field(index as i32, field, target, field_value);
                self.drop_pure_effect(set);
            }
            self.arena.release(value);
        }
        self.arena.pools.prims = prims;
    }

    /// O(s + a) to seal one member's s statements and initialize a self block
    /// of a fields. The last member emits all pooled lists once in group order.
    pub(super) fn recursive_child(&mut self, cx: Cx, group: Group, index: usize, child: Probed) -> Probed {
        let View::LetRec { values, .. } = self.source.view(group.node) else { unreachable!() };
        let count = values.len();
        if index == count { return child; }
        let member = group.base as usize + count - 1 - index;
        let mut out = self.realize(cx, child);
        if self.rec_members[member].mode != Mode::Declare {
            let value = out.value.take().unwrap_or_else(|| self.pure_expression(View::JUndefined, 0));
            self.recursive_block(member, value);
            // Legacy updateDummy/self initialization always produces a normal
            // block output, even when the block value's prelude was finished.
            out.finished = Finished::False;
        }
        let span = self.statements.since(Span { start: out.stmts.start, len: 0 });
        let list = self.statements.take_list(&mut self.arena, span);
        self.rec_members[member].code = Some(list);
        self.rec_members[member].finished = out.finished;
        if index + 1 == count {
            let mut finished = Finished::False;
            for i in group.base as usize..group.base as usize + count {
                self.rec_steps += 1;
                if let Some(declaration) = self.rec_members[i].placeholder.take() { self.statements.push(declaration); }
            }
            for i in group.base as usize..group.base as usize + count {
                self.rec_steps += 1;
                let list = self.rec_members[i].code.take().unwrap();
                for k in 0..self.arena.lists.get(list).len() {
                    self.rec_steps += 1;
                    let statement = self.arena.lists.get(list)[k];
                    if finished == Finished::True { self.arena.release(statement); }
                    else { self.statements.push(statement); }
                }
                if self.rec_members[i].finished == Finished::True { finished = Finished::True; }
            }
            self.rec_members[group.base as usize].finished = finished;
            self.rec_members[group.base as usize].end = self.statements.mark().start;
        }
        Probed::Out(Out { stmts: self.statements.mark(), value: None, finished: Finished::False })
    }

    /// O(deferred realization + discarded body size): append the body using
    /// the ordinary output algebra; no member list is scanned again.
    pub(super) fn finish_recursive(&mut self, cx: Cx, group: Group, children: impl Iterator<Item = Probed>) -> Probed {
        let body = children.last().expect("recursive body");
        let mut out = self.realize(cx, body);
        if let Some(first) = self.rec_members.get(group.base as usize) {
            let prefix = Out { stmts: Span { start: group.start.start, len: first.end - group.start.start },
                value: None, finished: first.finished };
            let keep = matches!(cx.cont, Cont::Value(_)).then(|| out.value.take()).flatten();
            let value = out.value;
            out = self.append_outputs(prefix, out, value);
            if keep.is_some() { out.value = keep; }
        }
        self.rec_members.truncate(group.base as usize);
        Probed::Out(out)
    }
}
#[cfg(test)]
mod tests {
    use super::*;
    use crate::ident::IdentFlags;
    use crate::lambda::{arena::LamArena, ApInfo, ApplyStatus, FunctionAttribute, LamLoc};
    use crate::lambda::lam_constant::Constant;

    #[test]
    fn group_size() {
        assert_eq!(std::mem::size_of::<Group>(), 16);
        assert_eq!(std::mem::size_of::<Member>(), 32);
        assert_eq!(std::mem::size_of::<Mode>(), 1);
    }

    #[test]
    fn recursive_function_groups_in_every_continuation() {
        for mutual in [false, true] {
            let mut a = LamArena::new();
            let f = Ident::new("f", 1, IdentFlags::NONE);
            let g = Ident::new("g", 2, IdentFlags::NONE);
            let mut bindings = Vec::new();
            for (name, callee) in if mutual { vec![(f, g), (g, f)] } else { vec![(f, f)] } {
                let callee = a.var(callee);
                let call = a.apply_raw(callee, &[], ApInfo { status: ApplyStatus::InferFull, loc: LamLoc::NONE });
                let end = a.const_(Constant::JsNull);
                let body = a.seq_raw(call, end);
                let fun = a.function_(0, &[], body, FunctionAttribute::default(), LamLoc::NONE);
                bindings.push((name, fun));
            }
            let body = a.var(f);
            let root = a.letrec(&bindings, body);
            super::super::oracle_tests::compare(a, root);
        }
    }

    #[test]
    fn recursive_values_and_mixed_groups_match_legacy() {
        use crate::lambda::lam_primitive::Mutable;
        for shape in 0..6 {
            let mut a = LamArena::new();
            let x = Ident::new("a", 1, IdentFlags::NONE);
            let y = Ident::new("b", 2, IdentFlags::NONE);
            let f = Ident::new("f", 3, IdentFlags::NONE);
            let one = a.const_(Constant::int(1));
            let two = a.const_(Constant::int(2));
            let vx = a.var(x);
            let vy = a.var(y);
            let vf = a.var(f);
            let fun = a.function_(0, &[], vx, FunctionAttribute::default(), LamLoc::NONE);
            let tag = TagInfo::record(vec![("value".into(), false), ("next".into(), false), ("peer".into(), false)], crate::parser::ast::MutableFlag::Immutable);
            let xvalue = match shape {
                0 => a.prim_raw(Primitive::Pmakeblock(tag.clone(), Mutable::Immutable), &[one, vx, vx], LamLoc::NONE),
                1 => a.prim_raw(Primitive::Pmakeblock(tag.clone(), Mutable::Immutable), &[one, vf, vx], LamLoc::NONE),
                2 => a.prim_raw(Primitive::Pmakeblock(TagInfo::Tuple, Mutable::Immutable), &[one, vx], LamLoc::NONE),
                3 => one,
                _ => {
                    let next = a.function_(0, &[], vy, FunctionAttribute::default(), LamLoc::NONE);
                    a.prim_raw(Primitive::Pmakeblock(tag.clone(), Mutable::Immutable), &[one, next, vy], LamLoc::NONE)
                }
            };
            let next = a.function_(0, &[], vx, FunctionAttribute::default(), LamLoc::NONE);
            let yvalue = a.prim_raw(Primitive::Pmakeblock(tag, Mutable::Immutable), &[two, next, vx], LamLoc::NONE);
            let bindings = if shape == 0 || shape == 2 { vec![(x, xvalue)] }
                else if shape == 1 { vec![(x, xvalue), (f, fun)] }
                else if shape == 4 { vec![(x, xvalue), (y, yvalue)] }
                else { vec![(x, xvalue), (y, yvalue), (f, fun)] };
            let root = a.letrec(&bindings, vx);
            super::super::oracle_tests::compare(a, root);
        }
    }

    #[test]
    fn ten_thousand_value_members_are_linear() {
        let mut a = LamArena::new();
        let mut bindings = Vec::with_capacity(10_000);
        for i in 0..10_000 {
            let id = Ident::new("member", i + 1, IdentFlags::NONE);
            let value = a.const_(Constant::int(i));
            bindings.push((id, value));
        }
        let body = a.const_(Constant::JsNull);
        let root = a.letrec(&bindings, body);
        let input = crate::bir::bridge::import_lambda(&a, root).unwrap();
        let root = input.root;
        let mut state = State::new(input);
        let output = state.probe(Cx::value(), root).unwrap();
        assert_eq!(state.source_steps, 10_002);
        assert_eq!(state.rec_steps, 50_000);
        eprintln!("10,000 recursive values: source={}, member steps={}", state.source_steps, state.rec_steps);
        let lowered = state.complete(Cx::value(), output);
        lowered.program.arena.validate(Some(lowered.program.root)).unwrap();
    }

    #[test]
    fn ten_thousand_members_are_lowered_once() {
        let mut a = LamArena::new();
        let mut bindings = Vec::with_capacity(10_000);
        for i in 0..10_000 {
            let id = Ident::new("member", i + 1, IdentFlags::NONE);
            let body = a.const_(Constant::JsNull);
            let function = a.function_(0, &[], body, FunctionAttribute::default(), LamLoc::NONE);
            bindings.push((id, function));
        }
        let body = a.const_(Constant::JsNull);
        let root = a.letrec(&bindings, body);
        let input = crate::bir::bridge::import_lambda(&a, root).unwrap();
        let root = input.root;
        let mut state = State::new(input);
        let output = state.probe(Cx::value(), root).unwrap();
        assert_eq!(state.source_steps, 20_002);
        let lowered = state.complete(Cx::value(), output);
        lowered.program.arena.validate(Some(lowered.program.root)).unwrap();
    }

}
