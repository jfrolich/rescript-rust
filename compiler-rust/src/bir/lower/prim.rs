//! P: compile_primitive: lower arguments once, sequence, then convert the result.
use super::*;
use crate::bir::PrimId;
use crate::bir::j::norm;
use crate::js_ir::op::LengthObject;
use crate::lambda::lam_primitive::Primitive;

pub(super) struct Prim {
    pub primitive: PrimId,
    pub operands: Vec<NodeId>,
}

impl State {
    /// P: compile_primitive_js, length arms. J-E2 owns literal folding.
    pub(super) fn finish_primitive(
        &mut self,
        cx: Cx,
        prim: Prim,
        children: impl Iterator<Item = Probed>,
    ) -> Probed {
        let outputs = children.map(|child| match child {
            Probed::Out(out) => out,
            Probed::Free(_) => unreachable!("argument realized before its next sibling"),
        }).collect();
        let (statements, values) = self.sequence_arguments(false, outputs);
        let value = match self.arena.primitive(prim.primitive).primitive {
            Primitive::Pstringlength => norm::je2_length(&mut self.arena, values[0], LengthObject::String),
            Primitive::Parraylength => norm::je2_length(&mut self.arena, values[0], LengthObject::Array),
            _ => unreachable!("primitive admitted by dispatch"),
        };
        self.primitive_result(cx, statements, value)
    }

    /// C: declare_compiled, assign_compiled, return_compiled: conv after sequencing.
    fn primitive_result(&mut self, cx: Cx, statements: Span, value: NodeId) -> Probed {
        if !self.statements.has_statements(statements) {
            self.statements.remove_empty(statements);
            self.probe_leaf(cx, value)
        } else {
            let out = self.leaf(cx, value);
            Probed::Out(Out {
                stmts: self.statements.since(Span { start: statements.start, len: 0 }),
                ..out
            })
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lambda::{arena::LamArena, lam_constant::Constant, LamLoc};

    #[test]
    fn lengths_match_legacy_in_every_continuation() {
        for primitive in [Primitive::Pstringlength, Primitive::Parraylength] {
            for literal in [false, true] {
                let mut a = LamArena::new();
                let arg = if literal {
                    a.const_(Constant::String("a😀z".into()))
                } else {
                    a.var(Ident::new("value", 10, crate::ident::IdentFlags::NONE))
                };
                let root = a.prim_raw(primitive.clone(), &[arg], LamLoc::NONE);
                super::super::oracle_tests::compare(a, root);
            }
        }
    }
}
