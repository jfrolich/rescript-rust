//! Continuations for the level-L to level-J lowering (BACKEND_LOWERING §1).
//! Context references are indices, never references into growing state pools.
mod expr;
mod konst;
#[cfg(test)]
mod oracle_tests;
pub mod out;

use super::bridge::Unsupported;
use super::{Bir, NodeId, VarId, View};
use crate::ident::Ident;
use crate::lambda::lam_compat::LetKind;
pub use out::{Finished, Free, FreeId, FreePool, Out, Probed, Span, StatementStack};

/// K7: C:3989 compile_recursive_function_expr, function-local return record.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LoopRef(pub u32);
/// K12: C:6092 with_static_jump_handler, visible jump-stack height.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct JumpTop(pub u32);
/// K11: C:2044 push_loop, visible loop-frame height.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct LoopTop(pub u32);

/// K1–K7: the continuation, independent of the traversal machinery.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Cont {
    /// Evaluate for effects, optionally returning.
    Effect(Tail),
    /// Produce a value, optionally recognizing tail calls.
    Value(Tail),
    /// Bind the result with its declaration kind.
    Declare(LetKind, VarId),
    /// Assign the result to an existing variable.
    Assign(VarId),
}
/// K1/K6: C:1529 compile_expr and C:3067 compile_return_output.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Tail {
    /// Not in tail position.
    No,
    /// Tail position with return policy.
    Return(Ret),
}
/// K7/K8/K14: C:3543 with_try_body_context and C:3091 compile_staticcatch_in_return.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Ret {
    /// Tail position protected by an exception handler.
    InTry,
    /// Ordinary function return and optional self-call loop.
    Named {
        /// Enclosing function loop record, if any.
        loop_: Option<LoopRef>,
        /// Whether a static catch encloses this return.
        in_catch: bool,
    },
}
/// K1–K14: context passed by value, including function and control boundaries.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Cx {
    /// Requested output continuation.
    pub cont: Cont,
    /// Visible jump-stack height.
    pub jumps: JumpTop,
    /// Switches since the nearest loop.
    pub switch_depth: u32,
    /// Visible loop-frame height.
    pub loops: LoopTop,
    /// Enclosing function returns unit.
    pub return_unit: bool,
}
impl Cx {
    /// K10: C:1997 with_function_scope; no control state crosses a function.
    pub fn new(cont: Cont) -> Self {
        Self {
            cont,
            jumps: JumpTop(0),
            switch_depth: 0,
            loops: LoopTop(0),
            return_unit: false,
        }
    }
    /// K1: C:1529 compile_expr (V).
    pub fn value() -> Self {
        Self::new(Cont::Value(Tail::No))
    }
    /// K2: C:4603 compile_effect_output (E, value retained).
    pub fn effect() -> Self {
        Self::new(Cont::Effect(Tail::No))
    }
    /// K4: C:2411 compile_let_binding_output (D).
    pub fn declare(kind: LetKind, var: VarId) -> Self {
        Self::new(Cont::Declare(kind, var))
    }
    /// K5: C:5331 compile_assign_to_target_output (A).
    pub fn assign(var: VarId) -> Self {
        Self::new(Cont::Assign(var))
    }
    /// K6: C:3067 compile_return_output (R).
    pub fn returning() -> Self {
        Self::new(Cont::Effect(Tail::Return(Ret::Named {
            loop_: None,
            in_catch: false,
        })))
    }
}

/// K1/K2/K6: deferred, already-lowered operands, not a second L tree.
/// The caller has lowered expression operands exactly once before probing.
pub enum ProbeInput {
    /// An already-lowered expression or statement result.
    Output(Out),
    /// A retained effect value followed by a probed child.
    Seq {
        /// Already-lowered effect value.
        first: NodeId,
        /// Result of probing the tail.
        second: Probed,
    },
    /// An already-lowered condition and its probed branches.
    Cond {
        /// Already-lowered test value.
        test: NodeId,
        /// Probed true branch.
        then_: Probed,
        /// Probed false branch.
        else_: Probed,
    },
}

/// K2/K6: C:4715 append_effect_output and C:5144 compile_if_return_output.
/// Construction policy is supplied by J constructors, not by the output algebra.
pub trait Realizer {
    /// K1/K6: C:6658 return_compiled; convert one lowered value.
    fn leaf(&mut self, cx: Cx, value: NodeId) -> Out;
    /// K2: C:4715 append_effect_output; combine an effect and a tail.
    fn seq(&mut self, cx: Cx, first: NodeId, second: Out) -> Out;
    /// K6: C:5144 compile_if_return_output; combine lowered branches.
    fn cond(&mut self, cx: Cx, test: NodeId, then_: Out, else_: Out) -> Out;
}

/// One source visit either completes an output or schedules child occurrences.
pub enum ProbePlan<R> {
    /// This source node has already been lowered.
    Ready(Probed),
    /// Resume after the children, without re-reading the source node.
    Children(R),
}

/// Source dispatch for the single-pass probe. Resume records contain decoded
/// operands, not source trees. The output algebra does not prescribe constructs.
pub trait ProbeRules {
    /// Decoded operands required after visiting children.
    type Resume;
    /// K1: C:1529 compile_expr; inspect and lower a source node exactly once.
    fn enter(
        &mut self,
        cx: Cx,
        node: NodeId,
    ) -> Result<ProbePlan<Self::Resume>, super::bridge::Unsupported>;
    /// K1/K2: C:1529 compile_expr / C:4603 compile_effect_output; child order.
    fn children(&self, cx: Cx, resume: &Self::Resume, into: &mut Vec<(Cx, NodeId)>);
    /// K4/K2: C:2411 compile_let_binding_output / C:4603 compile_effect_output.
    /// Consume a child's result before entering its next sibling when required.
    fn child(&mut self, _cx: Cx, _resume: &Self::Resume, _index: usize, output: Probed) -> Probed {
        output
    }
    /// K0/K2: C:119 append / C:4715 append_effect_output; combine child outputs.
    fn finish(
        &mut self,
        cx: Cx,
        resume: Self::Resume,
        children: impl Iterator<Item = Probed>,
    ) -> Result<Probed, super::bridge::Unsupported>;
}

/// Explicit source traversal, separate from realization of deferred J operands.
#[derive(Default)]
pub struct SourceProbe {
    /// Source occurrences offered to dispatch (one per incoming tree edge).
    pub steps: usize,
}
impl SourceProbe {
    /// K1/K6: C:1529 compile_expr / C:5144 compile_if_return_output.
    /// A source node is entered once. Finish frames receive the saved operands
    /// and child outputs, never a request to compile the same child again.
    pub fn probe(
        &mut self,
        rules: &mut impl ProbeRules,
        cx: Cx,
        node: NodeId,
    ) -> Result<Probed, super::bridge::Unsupported> {
        enum Work<R> {
            Enter(Cx, NodeId),
            Finish(Cx, R, usize),
            Child(Cx, usize, usize),
        }
        let mut work = vec![Work::Enter(cx, node)];
        let mut values = Vec::new();
        let mut children = Vec::new();
        while let Some(task) = work.pop() {
            match task {
                Work::Enter(cx, node) => {
                    self.steps += 1;
                    match rules.enter(cx, node)? {
                        ProbePlan::Ready(value) => values.push(value),
                        ProbePlan::Children(resume) => {
                            rules.children(cx, &resume, &mut children);
                            let parent = work.len();
                            work.push(Work::Finish(cx, resume, children.len()));
                            for (index, (cx, node)) in children.drain(..).enumerate().rev() {
                                work.push(Work::Child(cx, parent, index));
                                work.push(Work::Enter(cx, node));
                            }
                        }
                    }
                }
                Work::Child(cx, parent, index) => {
                    let Work::Finish(_, resume, _) = &work[parent] else {
                        unreachable!("parent resume frame")
                    };
                    let child = values.pop().expect("completed source child");
                    values.push(rules.child(cx, resume, index, child));
                }
                Work::Finish(cx, resume, count) => {
                    let start = values
                        .len()
                        .checked_sub(count)
                        .expect("source probe children");
                    let value = rules.finish(cx, resume, values.drain(start..))?;
                    values.push(value);
                }
            }
        }
        assert_eq!(values.len(), 1);
        Ok(values.pop().expect("source probe output"))
    }
}

/// N1: C:663 compile_deps_program_in_arena. The final statement is a plain
/// SExp carrying Out::value for the migration exporter, not an emitted effect.
pub(crate) struct Lowered {
    pub program: super::bridge_j::Imported,
    pub finished: Finished,
}

/// N1: C:663 compile_deps_program_in_arena; one fresh J arena for this migration cut.
pub(crate) fn lower(input: super::bridge::Imported) -> Result<Lowered, Unsupported> {
    let root = input.root;
    let mut state = State::new(input);
    let probed = state.probe(Cx::value(), root)?;
    Ok(state.complete(Cx::value(), probed))
}

struct State {
    source: Bir,
    arena: Bir,
    idents: Vec<Ident>,
    statements: StatementStack,
    free: FreePool,
    source_steps: usize,
}
impl State {
    /// N1: C:481 new. Transfer cold pools, while source hot nodes/list operands
    /// remain readable. Variables retain source identities, never global stamps.
    fn new(mut input: super::bridge::Imported) -> Self {
        let mut arena = Bir::default();
        arena.begin_bulk();
        arena.pools = std::mem::take(&mut input.arena.pools);
        arena.func_owners.resize(arena.pools.funcs.len(), None);
        for i in 0..input.arena.vars.len() {
            let var = VarId(i as u32);
            let made = arena.new_var_id(input.arena.vars.name(var), input.arena.vars.order(var));
            assert_eq!(made, var);
            arena.vars.flags[i] = input.arena.vars.flags[i];
        }
        arena.pools.j_modules = input
            .globals
            .iter()
            .map(|&id| crate::js_ir::ModuleId {
                id,
                kind: crate::js_ir::op::Kind::Ml,
                dynamic_import: false,
            })
            .collect();
        Self {
            source: input.arena,
            arena,
            idents: input.idents,
            statements: StatementStack::default(),
            free: FreePool::default(),
            source_steps: 0,
        }
    }
    /// H13: A:28 delay_safe; K1: C:1529 compile_expr. The supported literal,
    /// variable, module and function expressions are strictly pure by construction.
    /// Delay safety reads child flags or the variable's final ASSIGNED/JS_GLOBAL facts.
    fn pure_expression(&mut self, view: View<'_>, aux: u16) -> NodeId {
        let delay_safe = if let View::Var { var } = view {
            let flags = self.arena.vars.flags(var);
            !flags.contains(super::VarFlags::ASSIGNED)
                && !flags.contains(super::VarFlags::JS_GLOBAL)
        } else if let View::JFun { .. } = view {
            true
        } else {
            view.children().iter().all(|&child| {
                self.arena
                    .node(child)
                    .flags()
                    .contains(super::NodeFlags::DELAY_SAFE)
            })
        };
        let node = self.arena.new_node(view, aux);
        let mut flags = self.arena.node(node).flags();
        flags.0 |= super::NodeFlags::STRICT;
        if delay_safe {
            flags.0 |= super::NodeFlags::DELAY_SAFE;
        }
        self.arena.nodes[node.index()].set_flags(flags);
        node
    }
    /// K1: C:1529 compile_expr. SourceProbe owns the depth-independent traversal.
    fn probe(&mut self, cx: Cx, node: NodeId) -> Result<Probed, Unsupported> {
        let mut traversal = SourceProbe::default();
        let output = traversal.probe(self, cx, node);
        self.source_steps += traversal.steps;
        output
    }
    /// K2/K6: C:4715 append_effect_output / C:5144 compile_if_return_output.
    fn realize(&mut self, cx: Cx, probed: Probed) -> Out {
        let mut free = std::mem::take(&mut self.free);
        let out = free.realize(cx, probed, self);
        self.free = free;
        out
    }
    /// N1: C:663 compile_deps_program_in_arena. Export transports the last value
    /// in a plain sentinel SExp removed before export extraction and coercion.
    fn complete(mut self, cx: Cx, probed: Probed) -> Lowered {
        let out = self.realize(cx, probed);
        let value = out
            .value
            .unwrap_or_else(|| self.pure_expression(View::JUndefined, 0));
        let value = self.arena.new_node(View::SExp { value }, 0);
        self.statements.push(value);
        let run = self.statements.since(Span {
            start: out.stmts.start,
            len: 0,
        });
        let list = self.statements.take_list(&mut self.arena, run);
        let root = self.arena.block_from_list(list);
        self.arena.finish_bulk(root);
        Lowered {
            program: super::bridge_j::Imported::from_lowering(self.arena, root, self.idents),
            finished: out.finished,
        }
    }
}

impl ProbeRules for State {
    type Resume = expr::Resume;
    /// K1/H12: C:1529 compile_expr and K:60 compile_constant.
    fn enter(&mut self, _cx: Cx, node: NodeId) -> Result<ProbePlan<Self::Resume>, Unsupported> {
        let value = match self.source.view(node) {
            View::Var { var } => self.pure_expression(View::Var { var }, 0),
            View::Global { module } => self.pure_expression(
                View::JQualified {
                    module,
                    member: None,
                },
                0,
            ),
            View::Const { value } => self.constant(value),
            View::Apply { .. } => return Err(Unsupported("apply")),
            View::Fun { body, header } => {
                return Ok(ProbePlan::Children(expr::Resume::Fun { body, header }));
            }
            View::Let { var, value, body } => {
                let kind = match self.source.node(node).aux() & 3 {
                    0 => LetKind::Strict,
                    1 => LetKind::Alias,
                    2 => LetKind::StrictOpt,
                    3 => LetKind::Variable,
                    _ => unreachable!("masked let kind"),
                };
                return Ok(ProbePlan::Children(expr::Resume::Let {
                    var,
                    kind,
                    value,
                    body,
                }));
            }
            View::Seq { first, second } => {
                return Ok(ProbePlan::Children(expr::Resume::Seq { first, second }));
            }
            View::LetRec { .. } => return Err(Unsupported("let rec")),
            View::Prim { primitive, .. } => {
                use crate::lambda::lam_primitive::Primitive;
                let reason = match &self.arena.primitive(primitive).primitive {
                    Primitive::Psequand | Primitive::Psequor => "short circuit",
                    Primitive::PjsCall(_)
                    | Primitive::PjsApply
                    | Primitive::PjsObjectCreate(_)
                    | Primitive::PjsObjectGet(_)
                    | Primitive::PjsObjectSet(_)
                    | Primitive::PjsFnMethod => "external",
                    Primitive::Pjsx(_) => "jsx",
                    Primitive::Pimport(_) => "import",
                    Primitive::Pawait => "await",
                    Primitive::Pduprecord => "record copy",
                    Primitive::PrecordRest(_) => "record rest",
                    _ => "prim",
                };
                return Err(Unsupported(reason));
            }
            View::If { .. } => return Err(Unsupported("if")),
            View::Switch { .. } => return Err(Unsupported("switch")),
            View::StrSwitch { .. } => return Err(Unsupported("string switch")),
            View::Catch { .. } | View::Exit { .. } => return Err(Unsupported("static catch")),
            View::Try { .. } | View::TryFinally { .. } => return Err(Unsupported("try")),
            View::While { .. }
            | View::For { .. }
            | View::ForOf { .. }
            | View::ForAwaitOf { .. }
            | View::Break
            | View::Continue => return Err(Unsupported("loop")),
            View::Assign { .. } => return Err(Unsupported("assign")),
            View::JBin { .. }
            | View::JNot { .. }
            | View::JBnot { .. }
            | View::JTypeof { .. }
            | View::JIn { .. }
            | View::JCond { .. }
            | View::JSeq { .. }
            | View::JCall { .. }
            | View::JFlatCall { .. }
            | View::JNew { .. }
            | View::JIndex { .. }
            | View::JDot { .. }
            | View::JLength { .. }
            | View::JIsNullish { .. }
            | View::JStrAppend { .. }
            | View::JFun { .. }
            | View::JObject { .. }
            | View::JArray { .. }
            | View::JBlockLit { .. }
            | View::JOptional { .. }
            | View::JJsx { .. }
            | View::JTemplate { .. }
            | View::JTagged { .. }
            | View::JRaw { .. }
            | View::JAwait { .. }
            | View::JSpread { .. }
            | View::JQualified { .. }
            | View::JNumber { .. }
            | View::JStr { .. }
            | View::JBool
            | View::JNull
            | View::JUndefined
            | View::JJson { .. }
            | View::JRecordRest { .. }
            | View::SBlock { .. }
            | View::SDecl { .. }
            | View::SExp { .. }
            | View::SIf { .. }
            | View::SWhile { .. }
            | View::SForRangeExisting { .. }
            | View::SForRange { .. }
            | View::SForOf { .. }
            | View::SForAwaitOf { .. }
            | View::SSwitch { .. }
            | View::SReturn { .. }
            | View::SThrow { .. }
            | View::STry { .. }
            | View::SBreak { .. }
            | View::SContinue { .. }
            | View::SDebugger
            | View::SRest { .. } => unreachable!("expected level-L source"),
        };
        Ok(ProbePlan::Ready(Probed::Free(
            self.free.push(Free::Leaf(value)),
        )))
    }
    /// K4/K2/K10: C:2411 compile_let_binding_output / C:4603 compile_effect_output / C:1997 with_function_scope.
    fn children(&self, cx: Cx, resume: &Self::Resume, into: &mut Vec<(Cx, NodeId)>) {
        self.expression_children(cx, resume, into);
    }
    /// K4/K2: C:2411 compile_let_binding_output / C:4603 compile_effect_output.
    fn child(&mut self, cx: Cx, resume: &Self::Resume, index: usize, output: Probed) -> Probed {
        self.expression_child(cx, resume, index, output)
    }
    /// K0/K2/K10: C:119 append / C:4715 append_effect_output / C:562 function_expr.
    fn finish(
        &mut self,
        cx: Cx,
        resume: Self::Resume,
        children: impl Iterator<Item = Probed>,
    ) -> Result<Probed, Unsupported> {
        Ok(self.finish_expression(cx, resume, children))
    }
}

impl Realizer for State {
    /// K4/K5/K6: C:6648 declare_compiled, C:6667 assign_compiled, C:6658 return_compiled.
    fn leaf(&mut self, cx: Cx, value: NodeId) -> Out {
        let start = self.statements.mark();
        let mut finished = Finished::False;
        let value = match cx.cont {
            Cont::Value(Tail::No) | Cont::Value(Tail::Return(_)) | Cont::Effect(Tail::No) => {
                Some(value)
            }
            Cont::Declare(kind, var) => {
                let stmt = self.arena.new_node(
                    View::SDecl {
                        var,
                        value: Some(value),
                    },
                    kind as u16 | ((crate::js_ir::op::UsedStats::Used as u16) << 2),
                );
                self.statements.push(stmt);
                None
            }
            Cont::Assign(var) => {
                let left = self.pure_expression(View::Var { var }, 0);
                let value = self.arena.new_node(
                    View::JBin { left, right: value },
                    crate::js_ir::BinOp::Eq as u16,
                );
                let stmt = self.arena.new_node(View::SExp { value }, 0);
                self.statements.push(stmt);
                None
            }
            Cont::Effect(Tail::Return(_)) => {
                let stmt = self.arena.new_node(View::SReturn { value }, 0);
                self.statements.push(stmt);
                finished = Finished::True;
                None
            }
        };
        Out {
            stmts: self.statements.since(start),
            value,
            finished,
        }
    }
    /// K2: C:4715 append_effect_output. The retained head has no effects in
    /// this slice; its already-lowered J subtree is released, never recompiled.
    fn seq(&mut self, _: Cx, first: NodeId, second: Out) -> Out {
        self.drop_pure_effect(first);
        second
    }
    /// K6: C:5144 compile_if_return_output; If remains explicitly unsupported.
    fn cond(&mut self, _: Cx, _: NodeId, _: Out, _: Out) -> Out {
        unreachable!("conditional is unsupported")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::mem::size_of;

    #[test]
    fn context_sizes() {
        assert_eq!(size_of::<LoopRef>(), 4);
        assert_eq!(size_of::<JumpTop>(), 4);
        assert_eq!(size_of::<LoopTop>(), 4);
        assert_eq!(size_of::<Ret>(), 12);
        assert_eq!(size_of::<Tail>(), 12);
        assert_eq!(size_of::<Cont>(), 16);
        assert_eq!(size_of::<Cx>(), 32);
    }

    #[test]
    fn five_contexts_start_at_control_boundaries() {
        let var = VarId(0);
        let contexts = [
            Cx::value(),
            Cx::effect(),
            Cx::declare(LetKind::Strict, var),
            Cx::assign(var),
            Cx::returning(),
        ];
        for cx in contexts {
            assert_eq!(cx.jumps, JumpTop(0));
            assert_eq!(cx.loops, LoopTop(0));
            assert_eq!(cx.switch_depth, 0);
            assert!(!cx.return_unit);
        }
    }
    #[test]
    fn source_probe_visits_ten_thousand_nested_nodes_once() {
        struct Rules<'a> {
            source: &'a super::super::Bir,
            seen: Vec<u8>,
        }
        impl ProbeRules for Rules<'_> {
            type Resume = (NodeId, NodeId);
            fn enter(
                &mut self,
                _: Cx,
                node: NodeId,
            ) -> Result<ProbePlan<Self::Resume>, super::super::bridge::Unsupported> {
                self.seen[node.index()] += 1;
                match self.source.view(node) {
                    super::super::View::Seq { first, second } => {
                        Ok(ProbePlan::Children((first, second)))
                    }
                    super::super::View::Const { .. } => Ok(ProbePlan::Ready(Probed::Out(Out {
                        stmts: Span::default(),
                        value: Some(node),
                        finished: Finished::False,
                    }))),
                    other => panic!("unexpected test source: {other:?}"),
                }
            }
            fn children(
                &self,
                cx: Cx,
                &(first, second): &Self::Resume,
                into: &mut Vec<(Cx, NodeId)>,
            ) {
                into.extend([(cx, first), (cx, second)]);
            }
            fn finish(
                &mut self,
                _: Cx,
                _: Self::Resume,
                mut children: impl Iterator<Item = Probed>,
            ) -> Result<Probed, super::super::bridge::Unsupported> {
                assert!(children.next().is_some());
                Ok(children.next().unwrap())
            }
        }
        for first_position in [false, true] {
            let mut source = super::super::Bir::default();
            source.begin_bulk();
            let constant = source.intern_const(super::super::Constant::Null);
            let mut root = source.new_node(super::super::View::Const { value: constant }, 0);
            for _ in 0..10_000 {
                let leaf = source.new_node(super::super::View::Const { value: constant }, 0);
                let (first, second) = if first_position {
                    (root, leaf)
                } else {
                    (leaf, root)
                };
                root = source.new_node(super::super::View::Seq { first, second }, 0);
            }
            source.finish_bulk(root);
            let mut rules = Rules {
                source: &source,
                seen: vec![0; source.nodes.len()],
            };
            let mut probe = SourceProbe::default();
            probe.probe(&mut rules, Cx::value(), root).unwrap();
            assert_eq!(probe.steps, 20_001);
            assert!(rules.seen.iter().all(|&visits| visits == 1));
        }
        assert_eq!(std::mem::size_of::<SourceProbe>(), 8);
        assert_eq!(std::mem::size_of::<ProbePlan<()>>(), 20);
    }
}
