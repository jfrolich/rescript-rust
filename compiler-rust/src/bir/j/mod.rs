//! J construction for the first lowering slice. Plain constructors stay plain;
//! only reachable normalization rows live in `norm`.
pub mod norm;
pub mod facts;
pub mod equal;

use super::{Bir, NodeFlags, NodeId, VarFlags, VarId, View};
use crate::lambda::lam_compat::LetKind;

/// H13: A:28 delay_safe; strict-pure expression construction for Var, Global,
/// Const and Fun. Read child facts rather than walking expression subtrees.
pub(crate) fn pure_expression(bir: &mut Bir, view: View<'_>, aux: u16) -> NodeId {
    let delay_safe = if let View::Var { var } = view {
        let flags = bir.vars.flags(var);
        !flags.contains(VarFlags::ASSIGNED) && !flags.contains(VarFlags::JS_GLOBAL)
    } else if let View::JFun { .. } = view {
        true
    } else {
        view.children()
            .iter()
            .all(|&child| bir.node(child).flags().contains(NodeFlags::DELAY_SAFE))
    };
    let node = bir.new_node(view, aux);
    let mut flags = bir.node(node).flags();
    flags.0 |= NodeFlags::STRICT;
    if delay_safe {
        flags.0 |= NodeFlags::DELAY_SAFE;
    }
    bir.nodes[node.index()].set_flags(flags);
    node
}

/// K4: C:6648 declare_compiled. Plain declaration; no section-6 rewrite applies.
pub(crate) fn declare(bir: &mut Bir, kind: LetKind, var: VarId, value: NodeId) -> NodeId {
    bir.new_node(
        View::SDecl {
            var,
            value: Some(value),
        },
        kind as u16 | ((crate::js_ir::op::UsedStats::Used as u16) << 2),
    )
}

/// K5: C:6667 assign_compiled. J-E4 does not rewrite assignment, and J-S1's
/// numeric/undefined/comma triggers cannot match the assignment expression.
pub(crate) fn assign(bir: &mut Bir, var: VarId, value: NodeId) -> NodeId {
    let left = pure_expression(bir, View::Var { var }, 0);
    let value = bir.new_node(
        View::JBin { left, right: value },
        crate::js_ir::BinOp::Eq as u16,
    );
    bir.new_node(View::SExp { value }, 0)
}

/// K6: C:6658 return_compiled. Return is a plain statement constructor.
pub(crate) fn return_value(bir: &mut Bir, value: NodeId) -> NodeId {
    bir.new_node(View::SReturn { value }, 0)
}

#[cfg(test)]
mod facts_tests;
