//! Self tail calls as loops (BACKEND_LOWERING 5.1).
use super::*;
use crate::bir::{FuncId, FuncHeader, VarSpan};

/// One function's loop state, indexed by LoopRef; parameters retain L identity.
#[derive(Clone, Copy)]
pub(super) struct Frame {
    var: VarId,
    params: VarSpan,
    triggered: bool,
}

impl State {
    /// Amortized O(1) per recursive member, plus O(new source slots) when the
    /// dense function table first grows. The construction fact selects the
    /// loop continuation; no body is inspected or lowered twice.
    pub(super) fn register_tail_function(&mut self, function: NodeId, var: VarId) {
        if !self.source.has_self_tail_call(function) { return; }
        let View::Fun { header, .. } = self.source.view(function) else { unreachable!() };
        let params = if self.arena.function_attributes(header).one_unit_arg {
            VarSpan::default()
        } else { self.arena.function(header).params };
        let frame = LoopRef(self.tail_frames.len() as u32);
        self.tail_frames.push(Frame { var, params, triggered: false });
        self.tail_functions.resize(self.source.nodes.len(), None);
        self.tail_functions[function.index()] = Some(frame);
    }

    /// O(1): match the callee only in the enclosing function's tail continuation.
    pub(super) fn self_call(&self, cx: Cx, callee: NodeId) -> Option<LoopRef> {
        let (Cont::Effect(Tail::Return(Ret::Named { loop_: Some(frame), .. }))
            | Cont::Value(Tail::Return(Ret::Named { loop_: Some(frame), .. }))) = cx.cont else { return None };
        matches!(self.source.view(callee), View::Var { var } if var == self.tail_frames[frame.0 as usize].var).then_some(frame)
    }

    /// O(a + newly indexed variables + newly interned name bytes): release
    /// the callee, create copies in parameter order, then emit assignments in
    /// reverse order. Table growth and names are paid once per variable/copy.
    /// Arguments read iteration bindings, not the copies being assigned.
    pub(super) fn finish_self_call(&mut self, frame: LoopRef, statements: Span, values: &[NodeId]) -> Probed {
        let params = self.tail_frames[frame.0 as usize].params;
        self.tail_frames[frame.0 as usize].triggered = true;
        self.tail_copies.resize(self.arena.vars.len(), None);
        let mut assignments = std::mem::take(&mut self.tail_assignments);
        for (i, &value) in values.iter().enumerate() {
            self.tail_arguments += 1;
            if i == 0 || i > params.len() { self.arena.release(value); continue; }
            let param = VarId(params.start + i as u32 - 1);
            if matches!(self.arena.view(value), View::Var { var } if var == param) {
                self.arena.release(value);
                continue;
            }
            let copy = if let Some(copy) = self.tail_copies[param.index()] { copy } else {
                let mut name = std::mem::take(&mut self.tail_name);
                name.clear();
                name.push('_');
                name.push_str(self.arena.vars.name(param).as_str());
                let copy = self.fresh_variable(&name);
                name.clear();
                self.tail_name = name;
                self.tail_copies[param.index()] = Some(copy);
                copy
            };
            assignments.push(crate::bir::j::assign(&mut self.arena, copy, value));
        }
        for statement in assignments.drain(..).rev() { self.statements.push(statement); }
        self.tail_assignments = assignments;
        let jump = self.arena.new_node(View::SContinue { label: None }, 0);
        self.statements.push(jump);
        Probed::Out(Out { stmts: self.statements.since(Span { start: statements.start, len: 0 }), value: None, finished: Finished::True })
    }

    /// O(p log p + s): sort only copied parameters, emit their iteration-local
    /// aliases and wrap the already-lowered body. Each statement moves once.
    pub(super) fn loop_function_body(&mut self, frame: LoopRef, header: FuncId, body: NodeId) -> NodeId {
        let frame = self.tail_frames[frame.0 as usize];
        if !frame.triggered { return body; }
        let start = self.arena.vars.function_params.len() as u32;
        let mut ordered = std::mem::take(&mut self.tail_order);
        for param in frame.params.iter() {
            self.tail_parameters += 1;
            let copy = self.tail_copies.get(param.index()).copied().flatten();
            self.arena.vars.function_params.push(copy.unwrap_or(param));
            if copy.is_some() { ordered.push(param); }
        }
        self.arena.vars.funcs[header.index()].params = VarSpan { start, len: frame.params.len };
        self.arena.vars.funcs[header.index()].flags |= FuncHeader::INDIRECT_PARAMS;
        ordered.sort_unstable_by(|&a, &b| {
            self.tail_sort_comparisons += 1;
            let vars = &self.arena.vars;
            vars.order(b).cmp(&vars.order(a))
                .then_with(|| vars.name(b).as_str().len().cmp(&vars.name(a).as_str().len()))
                .then_with(|| vars.name(b).as_str().cmp(vars.name(a).as_str()))
        });
        let mark = self.statements.mark();
        for param in ordered.drain(..) {
            let copy = self.tail_copies[param.index()].unwrap();
            let value = self.pure_expression(View::Var { var: copy }, 0);
            let statement = crate::bir::j::declare(&mut self.arena, LetKind::Alias, param, value);
            self.statements.push(statement);
        }
        self.tail_order = ordered;
        let View::SBlock { statements } = self.arena.view(body) else { unreachable!() };
        let count = statements.len();
        for i in 0..count {
            self.tail_body_statements += 1;
            let View::SBlock { statements } = self.arena.view(body) else { unreachable!() };
            let statement = statements[i];
            self.arena.detach(statement);
            self.statements.push(statement);
        }
        self.arena.release(body);
        let list = self.statements.take_list(&mut self.arena, self.statements.since(mark));
        let body = self.arena.block_from_list(list);
        let condition = self.pure_expression(View::JBool, 1);
        let loop_ = self.arena.new_node(View::SWhile { condition, body, label: None }, 0);
        self.arena.new_node(View::SBlock { statements: &[loop_] }, 0)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn tail_copy_spelling_discards_preexisting_scratch() {
        let mut a = crate::lambda::arena::LamArena::new();
        let f = ident("f", 1);
        let x = ident("x", 2);
        let arg = a.const_(crate::lambda::lam_constant::Constant::JsNull);
        let body = call(&mut a, f, &[arg]);
        let root = wrap(&mut a, f, &[x], body);
        let input = crate::bir::bridge::import_lambda(&a, root).unwrap();
        let root = input.root;
        let mut state = State::new(input);
        state.tail_name.push_str("stale_field");
        let output = state.probe(Cx::value(), root).unwrap();
        assert!(state.tail_name.is_empty());
        assert!(state.idents.iter().any(|id| id.name() == "_x"));
        let lowered = state.complete(Cx::value(), output);
        lowered.program.arena.validate(Some(lowered.program.root)).unwrap();
    }

    #[test]
    fn frame_size() {
        assert_eq!(std::mem::size_of::<Frame>(), 16);
        assert_eq!(std::mem::size_of::<super::super::call::Call>(), 4);
        assert_eq!(std::mem::size_of::<super::super::call::Plan>(), 40);
    }

    #[test]
    fn self_tail_calls_sequence_condition_and_argument_counts() {
        use crate::lambda::{arena::LamArena, ApInfo, ApplyStatus, FunctionAttribute, LamLoc};
        use crate::lambda::lam_constant::Constant;
        use crate::ident::IdentFlags;
        for shape in 0..3 {
            for argc in 0..4 {
                let mut a = LamArena::new();
                let f = Ident::new("f", 1, IdentFlags::NONE);
                let x = Ident::new("x", 2, IdentFlags::NONE);
                let y = Ident::new("y", 3, IdentFlags::NONE);
                let callee = a.var(f);
                let args: Vec<_> = (0..argc).map(|i| if i == 0 { a.var(y) } else { a.var(x) }).collect();
                let call = a.apply_raw(callee, &args, ApInfo { status: ApplyStatus::InferFull, loc: LamLoc::NONE });
                let body = match shape {
                    0 => call,
                    1 => { let head = a.const_(Constant::JsNull); a.seq_raw(head, call) },
                    _ => { let test = a.var(x); let end = a.var(y); a.if_raw(test, call, end) },
                };
                let fun = a.function_(2, &[x, y], body, FunctionAttribute::default(), LamLoc::NONE);
                let end = a.var(f);
                let root = a.letrec(&[(f, fun)], end);
                super::super::oracle_tests::compare(a, root);
            }
        }
    }


    fn ident(name: &str, stamp: i32) -> Ident {
        Ident::new(name, stamp, crate::ident::IdentFlags::NONE)
    }
    fn call(a: &mut crate::lambda::arena::LamArena, f: Ident, args: &[crate::lambda::arena::Lam]) -> crate::lambda::arena::Lam {
        let f = a.var(f);
        a.apply_raw(f, args, crate::lambda::ApInfo { status: crate::lambda::ApplyStatus::InferFull, loc: crate::lambda::LamLoc::NONE })
    }
    fn wrap(a: &mut crate::lambda::arena::LamArena, f: Ident, params: &[Ident], body: crate::lambda::arena::Lam) -> crate::lambda::arena::Lam {
        let function = a.function_(params.len() as i32, params, body, Default::default(), crate::lambda::LamLoc::NONE);
        let end = a.var(f);
        a.letrec(&[(f, function)], end)
    }

    #[test]
    fn captured_iteration_parameters_and_nested_recursive_groups() {
        use crate::lambda::{arena::LamArena, LamLoc, FunctionAttribute};
        use crate::lambda::lam_primitive::Primitive as P;
        for nested in [false, true] {
            let mut a = LamArena::new();
            let (f, i, acc, fs, later, inner, n) = (ident("loop", 1), ident("i", 2), ident("acc", 3), ident("fs", 4), ident("later", 5), ident("inner", 6), ident("n", 7));
            let left = a.var(i);
            let right = a.var(acc);
            let captured = a.prim_raw(P::Paddint, &[left, right], LamLoc::NONE);
            let closure = a.function_(0, &[], captured, FunctionAttribute::default(), LamLoc::NONE);
            let effect = call(&mut a, later, &[closure]);
            let one = a.const_(crate::lambda::lam_constant::Constant::int(1));
            let old_i = a.var(i);
            let next_i = a.prim_raw(P::Psubint, &[old_i, one], LamLoc::NONE);
            let old_acc = a.var(acc);
            let old_i = a.var(i);
            let next_acc = a.prim_raw(P::Paddint, &[old_acc, old_i], LamLoc::NONE);
            let fs_arg = a.var(fs);
            let again = call(&mut a, f, &[next_i, next_acc, fs_arg]);
            let again = a.seq_raw(effect, again);
            let test = a.var(i);
            let result = a.var(acc);
            let mut body = a.if_raw(test, again, result);
            if nested {
                let arg = a.var(n);
                let self_call = call(&mut a, inner, &[arg]);
                let captured = a.var(i);
                let test = a.var(n);
                let inner_body = a.if_raw(test, self_call, captured);
                let function = a.function_(1, &[n], inner_body, Default::default(), LamLoc::NONE);
                body = a.letrec(&[(inner, function)], body);
            }
            let root = wrap(&mut a, f, &[i, acc, fs], body);
            super::super::oracle_tests::compare(a, root);
        }
    }

    #[test]
    fn self_tail_calls_in_switch_cases_and_static_catch_handlers() {
        use crate::lambda::{arena::LamArena, SwitchDispatch, SwitchKey};
        for shape in 0..3 {
            let mut a = LamArena::new();
            let (f, x) = (ident("f", 1), ident("x", 2));
            let arg = a.const_(crate::lambda::lam_constant::Constant::int(1));
            let again = call(&mut a, f, &[arg]);
            let value = a.var(x);
            let test = a.var(x);
            let body = if shape == 0 {
                let actions = a.add_list(&[again, value]);
                let info = a.add_switch(true, [SwitchKey::Int(0), SwitchKey::Int(1)], false, [], false, SwitchDispatch::Direct);
                a.switch_raw(test, actions, info)
            } else {
                let exit = a.static_raise(1, &[]);
                let body = if shape == 1 { a.if_raw(test, exit, value) } else {
                    let actions = a.add_list(&[exit, value]);
                    let info = a.add_switch(true, [SwitchKey::Int(0), SwitchKey::Int(1)], false, [], false, SwitchDispatch::Direct);
                    a.switch_raw(test, actions, info)
                };
                a.static_catch(body, 1, &[], again)
            };
            let root = wrap(&mut a, f, &[x], body);
            super::super::oracle_tests::compare(a, root);
        }
    }


    #[test]
    fn q3_unit_branch_must_return_from_the_loop() {
        use crate::lambda::{arena::LamArena, FunctionAttribute, LamLoc};
        let mut a = LamArena::new();
        let (f, c) = (ident("f", 1), ident("c", 2));
        let t = a.unit();
        let e = a.unit();
        let condition = a.var(c);
        let branch = a.if_raw(condition, t, e);
        let arg = a.var(c);
        let again = call(&mut a, f, &[arg]);
        let condition = a.var(c);
        let body = a.if_raw(condition, branch, again);
        let attr = FunctionAttribute { return_unit: true, ..FunctionAttribute::default() };
        let function = a.function_(1, &[c], body, attr, LamLoc::NONE);
        let end = a.var(f);
        let root = a.letrec(&[(f, function)], end);
        super::super::oracle_tests::compare(a, root);
    }


    fn conditional_shape(a: &mut crate::lambda::arena::LamArena, shape: usize, stamp: i32) -> crate::lambda::arena::Lam {
        use crate::lambda::{LamLoc, SwitchDispatch, SwitchKey};
        use crate::lambda::lam_primitive::Primitive as P;
        let x = ident("x", 2);
        let value = a.var(x);
        match shape {
            0 => value,
            1 | 2 => {
                let effect = call(a, ident("effect", 10), &[value]);
                let result = a.var(x);
                if shape == 1 { a.seq_raw(effect, result) }
                else { a.let_(LetKind::Strict, ident("bound", stamp), effect, result) }
            }
            3 => {
                let test = a.var(x);
                let other = a.unit();
                a.if_raw(test, value, other)
            }
            4 => {
                let other = a.var(ident("y", 3));
                a.prim_raw(P::Psequand, &[value, other], LamLoc::NONE)
            }
            5 => call(a, ident("f", 1), &[value]),
            6 => {
                let exit = a.static_raise(stamp, &[]);
                a.static_catch(exit, stamp, &[], value)
            }
            _ => {
                let other = a.unit();
                let actions = a.add_list(&[value, other]);
                let info = a.add_switch(true, [SwitchKey::Int(0), SwitchKey::Int(1)], false, [], false, SwitchDispatch::Direct);
                let test = a.var(x);
                a.switch_raw(test, actions, info)
            }
        }
    }

    #[test]
    fn r6_generated_conditionals_match_legacy_in_loop_functions() {
        use crate::lambda::{arena::LamArena, LamLoc};
        use crate::lambda::lam_primitive::Primitive as P;
        for condition in 0..3 {
            for yes in 0..8 {
                for no in 0..8 {
                    let mut a = LamArena::new();
                    let test = a.var(ident("x", 2));
                    let test = match condition {
                        0 => test,
                        1 => { let y = a.var(ident("y", 3)); a.prim_raw(P::Psequand, &[test, y], LamLoc::NONE) },
                        _ => { let effect = call(&mut a, ident("effect", 10), &[]); a.let_(LetKind::Strict, ident("test", 11), effect, test) },
                    };
                    let then_ = conditional_shape(&mut a, yes, 20);
                    let else_ = conditional_shape(&mut a, no, 30);
                    let branch = a.if_raw(test, then_, else_);
                    let arg = a.var(ident("x", 2));
                    let again = call(&mut a, ident("f", 1), &[arg]);
                    let test = a.var(ident("x", 2));
                    let body = a.if_raw(test, branch, again);
                    let root = wrap(&mut a, ident("f", 1), &[ident("x", 2)], body);
                    eprintln!("R6 shape condition={condition} yes={yes} no={no}");
                    super::super::oracle_tests::compare(a, root);
                }
            }
        }
    }


    #[test]
    fn ten_thousand_switch_self_calls_and_non_tail_function_are_lowered_once() {
        use crate::lambda::{arena::LamArena, SwitchDispatch, SwitchKey};
        use crate::lambda::lam_constant::Constant;
        for tail in [false, true] {
            let mut a = LamArena::new();
            let (f, x) = (ident("f", 1), ident("x", 2));
            let mut actions = Vec::with_capacity(10_000);
            for i in 0..10_000 {
                let argument = a.const_(Constant::int(i));
                let recursive = call(&mut a, f, &[argument]);
                actions.push(if tail { recursive } else { call(&mut a, ident("consume", 3), &[recursive]) });
            }
            let actions = a.add_list(&actions);
            let info = a.add_switch(true, (0..10_000).map(SwitchKey::Int), false, [], false, SwitchDispatch::Direct);
            let scrutinee = a.var(x);
            let body = a.switch_raw(scrutinee, actions, info);
            let root = wrap(&mut a, f, &[x], body);
            let input = crate::bir::bridge::import_lambda(&a, root).unwrap();
            let nodes = input.arena.nodes.len();
            let root = input.root;
            let mut state = State::new(input);
            let output = state.probe(Cx::value(), root).unwrap();
            assert_eq!(state.source_steps, nodes);
            assert_eq!(state.tail_frames.len(), usize::from(tail));
            assert_eq!(state.tail_arguments, if tail { 20_000 } else { 0 });
            assert_eq!(state.tail_parameters, usize::from(tail));
            assert_eq!(state.tail_sort_comparisons, 0);
            assert!(state.tail_body_statements <= 2);
            eprintln!("tail={tail}: source visits={}, tail arguments={}, parameters={}, body statements={}, sort comparisons={}",
                state.source_steps, state.tail_arguments, state.tail_parameters, state.tail_body_statements, state.tail_sort_comparisons);
            let lowered = state.complete(Cx::value(), output);
            lowered.program.arena.validate(Some(lowered.program.root)).unwrap();
        }
    }


    #[test]
    fn self_calls_in_try_bodies_stay_calls_but_handlers_may_jump() {
        use crate::lambda::arena::LamArena;
        use crate::lambda::lam_constant::Constant;
        for handler_recurses in [false, true] {
            let mut a = LamArena::new();
            let (f, x) = (ident("f", 1), ident("x", 2));
            let argument = a.var(x);
            let protected = call(&mut a, f, &[argument]);
            let handler = if handler_recurses {
                let argument = a.const_(Constant::int(0));
                call(&mut a, f, &[argument])
            } else { a.var(x) };
            let body = a.try_(protected, ident("exn", 3), handler);
            let root = wrap(&mut a, f, &[x], body);
            super::super::oracle_tests::compare(a.clone(), root);
            let input = crate::bir::bridge::import_lambda(&a, root).unwrap();
            let root = input.root;
            let mut state = State::new(input);
            let output = state.probe(Cx::value(), root).unwrap();
            assert_eq!(state.tail_frames.len(), usize::from(handler_recurses));
            let lowered = state.complete(Cx::value(), output);
            let b = &lowered.program.arena;
            let calls = b.nodes.iter().filter(|n| matches!(n.op(), crate::bir::Op::JCall)).count();
            let jumps = b.nodes.iter().filter(|n| matches!(n.op(), crate::bir::Op::SContinue)).count();
            assert_eq!(calls, 1, "the protected self call must remain inside try");
            assert_eq!(jumps, usize::from(handler_recurses));
            b.validate(Some(lowered.program.root)).unwrap();
        }
    }


    #[test]
    fn value_return_self_call_matches_legacy_jump() {
        use crate::lambda::{arena::LamArena, lam_compile::{LambdaCompiler, TailLoopState}};
        use crate::js_ir::arena::{JsDepsProgram, JsProgram};
        let mut a = LamArena::new();
        let (f, x) = (ident("f", 1), ident("x", 2));
        let argument = a.const_(crate::lambda::lam_constant::Constant::int(3));
        let body = call(&mut a, f, &[argument]);
        let root = wrap(&mut a, f, &[x], body);
        let input = crate::bir::bridge::import_lambda(&a, root).unwrap();
        let View::LetRec { first, values, .. } = input.arena.view(input.root) else { panic!() };
        let function = values[0];
        let View::Fun { body: source_body, .. } = input.arena.view(function) else { panic!() };
        let mut state = State::new(input);
        state.register_tail_function(function, first);
        let cx = Cx::new(Cont::Value(Tail::Return(Ret::Named { loop_: Some(LoopRef(0)), in_catch: false })));
        let output = state.probe(cx, source_body).unwrap();
        let lowered = state.complete(cx, output);
        assert_eq!(lowered.finished, Finished::True);
        let actual = crate::bir::bridge_j::export_js(&lowered.program).unwrap();
        let mut compiler = LambdaCompiler::new();
        let mut frame = TailLoopState { tail_targets: vec![f], params: vec![x], new_params: Default::default(), triggered: false };
        let mut block = compiler.compile_tail_loop_return_block(&mut a, body, &mut frame);
        assert!(frame.triggered);
        // The migration exporter retains the final Out value as a sentinel.
        let unit = crate::js_ir::build::exp::undefined(false, &mut compiler.j);
        block.push(compiler.j.stmt(crate::js_ir::arena::StmtKind::Exp(unit)));
        let expected = JsDepsProgram { program: JsProgram::new_in(block, vec![], compiler.j), modules: vec![], side_effect: None };
        let print = |p: &JsDepsProgram| crate::js_ir::print_deps_program_with_directives_and_options(p, None, &[], false, false, false);
        assert_eq!(print(&actual), print(&expected));
    }

    #[test]
    fn self_call_sequences_effectful_arguments_before_copy_assignments() {
        use crate::lambda::arena::LamArena;
        let mut a = LamArena::new();
        let (f, x, y) = (ident("f", 1), ident("x", 2), ident("y", 3));
        let x_arg = a.var(x);
        let first = call(&mut a, ident("effect", 10), &[x_arg]);
        let value = call(&mut a, ident("effect", 10), &[]);
        let result = a.var(x);
        let second = a.let_(LetKind::Strict, ident("held", 11), value, result);
        let body = call(&mut a, f, &[first, second]);
        let root = wrap(&mut a, f, &[x, y], body);
        super::super::oracle_tests::compare(a, root);
    }

    #[test]
    fn ten_thousand_self_call_arguments_lower_without_allocations() {
        use crate::lambda::arena::LamArena;
        let mut a = LamArena::new();
        let f = ident("f", 1);
        let params: Vec<_> = (0..10_000).map(|i| ident("p", i + 2)).collect();
        let args: Vec<_> = params.iter().rev().map(|&p| a.var(p)).collect();
        let body = call(&mut a, f, &args);
        let root = wrap(&mut a, f, &params, body);
        let input = crate::bir::bridge::import_lambda(&a, root).unwrap();
        let root = input.root;
        let mut state = State::new(input);
        let View::LetRec { values, first, .. } = state.source.view(root) else { unreachable!() };
        let function = values[0];
        let View::Fun { body, .. } = state.source.view(function) else { unreachable!() };
        // Establish the enclosing function, then lower the entire Lambda call,
        // including every argument, holding, sequencing, assignments and release.
        state.register_tail_function(function, first);
        let cx = Cx { cont: Cont::Effect(Tail::Return(Ret::Named { loop_: Some(LoopRef(0)), in_catch: false })), ..Cx::returning() };
        let run = |s: &mut State| {
            let output = s.probe(cx, body).unwrap();
            let output = s.realize(cx, output);
            for node in s.statements.statements(output.stmts) { s.arena.release(node); }
            if let Some(value) = output.value { s.arena.release(value); }
            s.statements.kill(output.stmts);
        };
        let lists = state.arena.lists.storage_shape().0;
        let source_lists = state.source.lists.storage_shape().0;
        run(&mut state);
        state.source.lists.reserve_test_growth(state.source.lists.storage_shape().0 - source_lists);
        state.arena.lists.reserve_test_growth(state.arena.lists.storage_shape().0 - lists);
        state.free.reserve_repeat();
        state.arena.js_scope.as_mut().unwrap().reserve_repeat();
        state.tail_copies.reserve(state.arena.vars.len() - state.tail_copies.len());
        let capacities = |s: &State| [s.arena.nodes.capacity(), s.arena.parents.capacity(),
            s.arena.free_nodes.capacity(), s.arena.release_stack.capacity(), s.arena.lists.storage_shape().1,
            s.traversal.work.capacity(), s.traversal.values.capacity(), s.traversal.children.capacity(),
            s.tail_assignments.capacity(), s.tail_copies.capacity(), s.tail_name.capacity(),
            s.call_reversed.capacity(), s.source.lists.storage_shape().1, s.calls.capacity(),
            s.argument_outputs.capacity(), s.argument_values.capacity(), s.arena.vars.name.capacity()];
        let before = capacities(&state);
        let visits = state.source_steps;
        let arguments = state.tail_arguments;
        let scope_before = state.arena.js_scope.as_ref().unwrap().capacities();
        let allocations = allocation_counter::measure(|| run(&mut state));
        assert_eq!(state.arena.js_scope.as_ref().unwrap().capacities(), scope_before);
        println!("whole self call: {allocations:?}");
        assert_eq!(allocations.count_total, 0);
        assert_eq!(capacities(&state), before);
        assert_eq!(state.source_steps - visits, 10_002);
        assert_eq!(state.tail_arguments - arguments, 10_001);
    }

    #[test]
    fn ten_thousand_parameter_copies_have_bounded_sort_and_single_emission() {
        use crate::lambda::arena::LamArena;
        let mut a = LamArena::new();
        let f = ident("f", 1);
        let params: Vec<_> = (0..10_000).map(|i| ident("p", i + 2)).collect();
        let args: Vec<_> = params.iter().rev().map(|&p| a.var(p)).collect();
        let body = call(&mut a, f, &args);
        let root = wrap(&mut a, f, &params, body);
        let input = crate::bir::bridge::import_lambda(&a, root).unwrap();
        let nodes = input.arena.nodes.len();
        let root = input.root;
        let mut state = State::new(input);
        let output = state.probe(Cx::value(), root).unwrap();
        assert_eq!(state.source_steps, nodes);
        assert_eq!(state.tail_arguments, 10_001);
        assert_eq!(state.tail_parameters, 10_000);
        assert_eq!(state.tail_body_statements, 10_001);
        assert!(state.tail_sort_comparisons <= 200_000);
        eprintln!("10,000 parameters: visits={}, arguments={}, parameters={}, body statements={}, sort comparisons={}",
            state.source_steps, state.tail_arguments, state.tail_parameters, state.tail_body_statements, state.tail_sort_comparisons);
        let lowered = state.complete(Cx::value(), output);
        lowered.program.arena.validate(Some(lowered.program.root)).unwrap();
    }

}
