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
}
