//! J construction for the first lowering slice. Plain constructors stay plain;
//! only reachable normalization rows live in `norm`.
pub mod norm;

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
    let runs_no_code = if let View::Var { var } = view {
        !bir.vars.flags(var).contains(VarFlags::JS_GLOBAL)
            || !bir.vars.name(var).as_str().contains('.')
    } else {
        matches!(view, View::JQualified { .. } | View::JBool | View::JStr { .. }
            | View::JNumber { .. })
    };
    let node = bir.new_node(view, aux);
    let mut flags = bir.node(node).flags();
    flags.0 = (flags.0 & !NodeFlags::RUNS_NO_CODE) | NodeFlags::STRICT;
    if runs_no_code { flags.0 |= NodeFlags::RUNS_NO_CODE; }
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

/// A:90 runs_no_code and E:15 strict purity for a member read. Delay safety
/// is deliberately absent: even a pure read may observe a later write.
pub(crate) fn member(bir: &mut Bir, object: NodeId, property: super::StrId, position: crate::js_ir::arena::FieldPos, aux: u16) -> NodeId {
    let child = bir.node(object).flags();
    let node = bir.new_node(View::JDot { object, property, position }, aux);
    let mut flags = bir.node(node).flags();
    if child.contains(NodeFlags::STRICT) { flags.0 |= NodeFlags::STRICT; }
    if position.get().is_some() && child.contains(NodeFlags::RUNS_NO_CODE) {
        flags.0 |= NodeFlags::RUNS_NO_CODE;
    }
    bir.nodes[node.index()].set_flags(flags);
    node
}

#[cfg(test)]
mod sequencing_tests {
    use super::*;
    use crate::js_ir::arena::FieldPos;

    #[test]
    fn cached_runs_no_code_distinguishes_properties_and_record_fields() {
        for assigned in [false, true] {
            for global in [false, true] {
                for name in ["local", "global.member"] {
                    let mut bir = Bir::default();
                    let var = bir.new_var_id(crate::name::Name::new(name), 1);
                    if assigned { bir.vars.flags[var.index()].0 |= VarFlags::ASSIGNED; }
                    if global { bir.vars.flags[var.index()].0 |= VarFlags::JS_GLOBAL; }
                    let value = pure_expression(&mut bir, View::Var { var }, 0);
                    let flags = bir.node(value).flags();
                    assert_eq!(flags.contains(NodeFlags::DELAY_SAFE), !assigned && !global);
                    let runs = !global || !name.contains('.');
                    assert_eq!(flags.contains(NodeFlags::RUNS_NO_CODE), runs);
                    let property = bir.intern_text("field");
                    let field = member(&mut bir, value, property, FieldPos::new(Some(0)), 0);
                    assert_eq!(bir.node(field).flags().contains(NodeFlags::RUNS_NO_CODE), runs);
                    assert!(!bir.node(field).flags().contains(NodeFlags::DELAY_SAFE));
                    let getter = member(&mut bir, field, property, FieldPos::NONE, 0);
                    assert!(!bir.node(getter).flags().contains(NodeFlags::RUNS_NO_CODE));
                    bir.validate(Some(getter), false).unwrap();
                }
            }
        }
    }
}
