//! H1: C:1144 compile_apply_call_inner, local application lowering.
use super::*;
use crate::bir::ApplyId;
use crate::lambda::ApplyStatus;

/// C:1144 compile_apply_call_inner: operands saved before their single visit.
pub(super) struct Call {
    pub operands: Vec<NodeId>,
    pub status: ApplyStatus,
}

impl State {
    /// C:1144 compile_apply_call_inner: flatten Na spines without repeatedly
    /// copying the growing argument prefix. Arguments retain left-to-right order.
    pub(super) fn application(
        &mut self,
        mut callee: NodeId,
        args: &[NodeId],
        info: ApplyId,
    ) -> Call {
        let status = self.arena.pools.apply[info.index()].status;
        let mut groups = vec![args.to_vec()];
        if status == ApplyStatus::Na {
            while let View::Apply {
                callee: inner,
                args,
                info,
            } = self.source.view(callee)
            {
                if self.arena.pools.apply[info.index()].status != ApplyStatus::Na {
                    break;
                }
                self.source_steps += 1;
                groups.push(args.to_vec());
                callee = inner;
            }
        }
        let mut operands = Vec::with_capacity(1 + groups.iter().map(Vec::len).sum::<usize>());
        operands.push(callee);
        for group in groups.into_iter().rev() {
            operands.extend(group);
        }
        Call { operands, status }
    }

    /// C:320 call_info_of_apply_status. Local calls never consult export arity.
    fn call_info_of_apply_status(status: ApplyStatus) -> crate::js_ir::CallInfo {
        use crate::js_ir::{CallArity, CallInfo, CallKind};
        let (kind, arity) = match status {
            ApplyStatus::InferFull => (CallKind::MlCall, CallArity::Full),
            ApplyStatus::Na => (CallKind::MlCall, CallArity::Na),
            ApplyStatus::Uncurry => (CallKind::Na, CallArity::Full),
        };
        CallInfo {
            kind,
            arity,
            ..CallInfo::default()
        }
    }

    /// C:1129 compile_apply_call, C:6648 declare_compiled, C:6667
    /// assign_compiled, C:6658 return_compiled: one call, then continuation.
    pub(super) fn finish_application(
        &mut self,
        cx: Cx,
        call: Call,
        children: impl Iterator<Item = Probed>,
    ) -> Probed {
        let outputs = children
            .map(|child| match child {
                Probed::Out(out) => out,
                Probed::Free(_) => unreachable!("argument realized before its next sibling"),
            })
            .collect();
        let (statements, values) = self.sequence_arguments(false, outputs);
        let info = self.arena.js_info(crate::bir::JsPayload::Call(
            Self::call_info_of_apply_status(call.status),
        ));
        let value = self.arena.new_node(
            View::JCall {
                callee: values[0],
                args: &values[1..],
                info,
            },
            0,
        );
        if !self.statements.has_statements(statements) {
            // Holes carry no effects; pop them before returning a free value.
            self.statements.remove_empty(statements);
            self.probe_leaf(cx, value)
        } else {
            let out = self.leaf(cx, value);
            Probed::Out(Out {
                stmts: self.statements.since(Span {
                    start: statements.start,
                    len: 0,
                }),
                ..out
            })
        }
    }
}
