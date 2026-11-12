//! Continuations for the level-L to level-J lowering (BACKEND_LOWERING §1).
//! Context references are indices, never references into growing state pools.
pub(crate) mod out;

use super::{NodeId, VarId};
use crate::lambda::lam_compat::LetKind;
pub(crate) use out::{Finished, Free, FreeId, FreePool, Out, Probed, Span, StatementStack};

/// K7: C:3989 compile_recursive_function_expr, function-local return record.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct LoopRef(pub(crate) u32);
/// K12: C:6092 with_static_jump_handler, visible jump-stack height.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct JumpTop(pub(crate) u32);
/// K11: C:2044 push_loop, visible loop-frame height.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct LoopTop(pub(crate) u32);

/// K1–K7: the continuation, independent of the traversal machinery.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Cont {
    Effect(Tail),
    Value(Tail),
    Declare(LetKind, VarId),
    Assign(VarId),
}
/// K1/K6: C:1529 compile_expr and C:3067 compile_return_output.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Tail {
    No,
    Return(Ret),
}
/// K7/K8/K14: C:3543 with_try_body_context and C:3091 compile_staticcatch_in_return.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Ret {
    InTry,
    Named {
        loop_: Option<LoopRef>,
        in_catch: bool,
    },
}
/// K1–K14: context passed by value, including function and control boundaries.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Cx {
    pub(crate) cont: Cont,
    pub(crate) jumps: JumpTop,
    pub(crate) switch_depth: u32,
    pub(crate) loops: LoopTop,
    pub(crate) return_unit: bool,
}
impl Cx {
    /// K10: C:1997 with_function_scope; no control state crosses a function.
    pub(crate) fn new(cont: Cont) -> Self {
        Self {
            cont,
            jumps: JumpTop(0),
            switch_depth: 0,
            loops: LoopTop(0),
            return_unit: false,
        }
    }
    /// K1: C:1529 compile_expr (V).
    pub(crate) fn value() -> Self {
        Self::new(Cont::Value(Tail::No))
    }
    /// K2: C:4603 compile_effect_output (E, value retained).
    pub(crate) fn effect() -> Self {
        Self::new(Cont::Effect(Tail::No))
    }
    /// K4: C:2411 compile_let_binding_output (D).
    pub(crate) fn declare(kind: LetKind, var: VarId) -> Self {
        Self::new(Cont::Declare(kind, var))
    }
    /// K5: C:5331 compile_assign_to_target_output (A).
    pub(crate) fn assign(var: VarId) -> Self {
        Self::new(Cont::Assign(var))
    }
    /// K6: C:3067 compile_return_output (R).
    pub(crate) fn returning() -> Self {
        Self::new(Cont::Effect(Tail::Return(Ret::Named {
            loop_: None,
            in_catch: false,
        })))
    }
}

/// K1/K2/K6: deferred, already-lowered operands, not a second L tree.
/// The caller has lowered expression operands exactly once before probing.
pub(crate) enum ProbeInput {
    Output(Out),
    Seq {
        first: NodeId,
        second: Probed,
    },
    Cond {
        test: NodeId,
        then_: Probed,
        else_: Probed,
    },
}

/// K2/K6: C:4715 append_effect_output and C:5144 compile_if_return_output.
/// Construction policy is supplied by J constructors, not by the output algebra.
pub(crate) trait Realizer {
    fn leaf(&mut self, cx: Cx, value: NodeId) -> Out;
    fn seq(&mut self, cx: Cx, first: NodeId, second: Out) -> Out;
    fn cond(&mut self, cx: Cx, test: NodeId, then_: Out, else_: Out) -> Out;
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
