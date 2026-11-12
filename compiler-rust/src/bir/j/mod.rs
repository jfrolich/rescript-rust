//! J construction: plain typed nodes, cached facts, and section-6 normalisers.
pub mod norm;
pub mod plain;
mod logic;
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
    let node = plain::node(bir, view, aux);
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

#[cfg(test)]
mod norm_tests;

/// Per-arena logical-normalisation measurements. No process-global counters.
#[derive(Default, Debug, Clone, Copy, serde::Serialize)]
pub struct Stats {
    /// Top-level J-E9 attempts, including the negated-test arm of J-E7.
    pub and_attempts: usize,
    /// Top-level J-E10 attempts.
    pub or_attempts: usize,
    /// Maximum inspected logical steps/pairs of a J-E9 attempt.
    pub max_and_steps: usize,
    /// Maximum inspected logical steps/pairs of a J-E10 attempt.
    pub max_or_steps: usize,
}

/// Optional corpus measurements, emitted only when a J tree is exported. Equal
/// snapshots share a filename; maxima are independent of worker scheduling.
pub(crate) fn write_stats(stats: Stats) -> std::io::Result<()> {
    use std::io::Write;
    let Some(directory) = std::env::var_os("RESCRIPT_J_NORMALISATION_STATS") else { return Ok(()); };
    let directory = std::path::Path::new(&directory);
    std::fs::create_dir_all(directory)?;
    let file = directory.join(format!("{}-{}-{}-{}.json", stats.and_attempts, stats.or_attempts, stats.max_and_steps, stats.max_or_steps));
    match std::fs::OpenOptions::new().write(true).create_new(true).open(file) {
        Ok(mut file) => file.write_all(&serde_json::to_vec(&stats)?),
        Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => Ok(()),
        Err(e) => Err(e),
    }
}

/// A:90/E:15: a member read is strict-pure when its object is, but is not
/// delay-safe: it can observe a later write. Sequencing uses runs_no_code.
pub(crate) fn member(bir: &mut Bir, object: NodeId, property: super::StrId, position: crate::js_ir::arena::FieldPos, aux: u16) -> NodeId {
    plain::node(bir, View::JDot { object, property, position }, aux)
}
#[cfg(test)]
mod sequencing_tests {
    use super::*;
    use crate::js_ir::arena::FieldPos;

    #[test]
    fn runs_no_code_distinguishes_properties_and_record_fields() {
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
                    assert_eq!(facts::runs_no_code(&bir, value), runs);
                    assert!(flags.contains(NodeFlags::J_SUBEXPR));
                    let property = bir.intern_text("field");
                    let field = member(&mut bir, value, property, FieldPos::new(Some(0)), 0);
                    assert_eq!(facts::runs_no_code(&bir, field), runs);
                    assert!(!bir.node(field).flags().contains(NodeFlags::J_SUBEXPR));
                    assert!(!bir.node(field).flags().contains(NodeFlags::DELAY_SAFE));
                    let getter = member(&mut bir, field, property, FieldPos::NONE, 0);
                    assert!(!facts::runs_no_code(&bir, getter));
                    bir.validate(Some(getter), false).unwrap();
                }
            }
        }
    }
}

#[cfg(test)]
mod sequencing_depth_tests {
    use super::*;
    #[test]
    fn ten_thousand_record_fields_have_linear_sequencing_inspection() {
        let mut b = Bir::default();
        b.begin_bulk();
        let var = b.new_var_id(crate::name::Name::new("record"), 1);
        let mut root = pure_expression(&mut b, View::Var { var }, 0);
        let property = b.intern_text("field");
        for _ in 0..10_000 {
            root = member(&mut b, root, property, crate::js_ir::arena::FieldPos::new(Some(0)), 0);
        }
        b.steps.set(0);
        assert!(facts::runs_no_code(&b, root));
        assert!(b.steps.get() <= 30_003);
        b.finish_bulk(root);
        b.validate(Some(root), false).unwrap();
    }
}
