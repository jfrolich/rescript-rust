//! Continuations for the level-L to level-J lowering (BACKEND_LOWERING §1).
//! Context references are indices, never references into growing state pools.
pub mod out;

use super::{NodeId, VarId};
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
                            work.push(Work::Finish(cx, resume, children.len()));
                            work.extend(
                                children
                                    .drain(..)
                                    .rev()
                                    .map(|(cx, node)| Work::Enter(cx, node)),
                            );
                        }
                    }
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

/// N1: C:663 compile_deps_program_in_arena. Initial harness cut: no source
/// construct is supported until the subsequent construct commits.
pub(crate) fn lower(
    _input: super::bridge::Imported,
) -> Result<Lowered, super::bridge::Unsupported> {
    Err(super::bridge::Unsupported("lowering not implemented"))
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
