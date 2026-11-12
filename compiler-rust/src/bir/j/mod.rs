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
