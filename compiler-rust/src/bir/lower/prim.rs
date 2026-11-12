//! P: compile_primitive: lower arguments once, sequence, then convert the result.
use super::*;
use crate::bir::PrimId;
use crate::bir::j::{norm, plain};
use crate::js_ir::op::LengthObject;
use crate::lambda::lam_primitive::Primitive;

pub(super) struct Prim {
    pub primitive: PrimId,
    pub operands: Vec<NodeId>,
}

impl State {
    pub(super) fn supported_primitive(primitive: &Primitive) -> bool {
        matches!(primitive, Primitive::Pstringlength | Primitive::Parraylength | Primitive::PfnArity
            | Primitive::Pstringadd | Primitive::Pnot | Primitive::Pidentity | Primitive::Pfloatofint
            | Primitive::Pignore | Primitive::Ptypeof | Primitive::PrawJsCode(_)
            | Primitive::PcreateExtension(_) | Primitive::PinitMod | Primitive::PupdateMod
            | Primitive::Praise | Primitive::Pdebugger)
    }

    /// C: runtime_call_expr / X: pure_runtime_call_expr. Runtime imports retain
    /// encounter order; purity annotations are comments, not purity facts.
    fn primitive_runtime(&mut self, name: &str, member: &str, args: &[NodeId]) -> NodeId {
        let module = match self.arena.pools.j_modules.iter().position(|m|
            m.id.name() == name && matches!(m.kind, crate::js_ir::Kind::Runtime)) {
            Some(i) => crate::bir::ImportId(i as u32),
            None => {
                let module = crate::bir::ImportId(self.arena.pools.imports.len() as u32);
                let path = self.arena.intern_text(name);
                self.arena.pools.imports.push(crate::bir::Import { name: crate::name::Name::new(name), path });
                self.arena.pools.j_modules.push(crate::js_ir::ModuleId {
                    id: Ident::create_persistent(name), kind: crate::js_ir::Kind::Runtime, dynamic_import: false,
                });
                module
            }
        };
        let member = Some(self.arena.intern_text(member));
        let callee = plain::node(&mut self.arena, View::JQualified { module, member }, 0);
        let info = self.arena.js_info(crate::bir::JsPayload::Call(crate::js_ir::CallInfo {
            kind: crate::js_ir::CallKind::BuiltinRuntime, arity: crate::js_ir::CallArity::Full, ..Default::default()
        }));
        plain::node(&mut self.arena, View::JCall { callee, args, info }, 0)
    }

    /// P: compile_primitive_js / compile_debugger source locations on statements.
    fn primitive_statement(&mut self, statement: NodeId, loc: crate::lambda::LamLoc) {
        if self.locations.as_ref().and_then(|locations| locations.get(loc))
            .is_some_and(|loc| !loc.loc_ghost && loc.loc_start.cnum >= 0) {
            self.arena.set_cold(statement, crate::bir::Cold { loc, comment: None });
            let mut flags = self.arena.node(statement).flags();
            flags.0 |= crate::bir::NodeFlags::JS_LOC_PRESENT;
            self.arena.nodes[statement.index()].set_flags(flags);
        }
        self.statements.push(statement);
    }

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
        let payload = self.arena.primitive(prim.primitive).clone();
        let primitive = payload.primitive;
        let value = match primitive {
            // P: compile_primitive_js, PfnArity.
            Primitive::PfnArity => match values.first() {
                Some(&value) => norm::je2_length(&mut self.arena, value, LengthObject::Function),
                None => plain::node(&mut self.arena, View::JUndefined, 0),
            },
            // P: compile_primitive_js, strings and booleans.
            Primitive::Pstringadd => norm::je1_string_append(&mut self.arena, values[0], values[1]),
            Primitive::Pnot => norm::je8_not(&mut self.arena, values[0]),
            // P: compile_primitive_js, identity group.
            Primitive::Pidentity | Primitive::Pfloatofint => values.first().copied()
                .unwrap_or_else(|| plain::node(&mut self.arena, View::JUndefined, 0)),
            Primitive::Pignore => {
                let value = values.first().copied().unwrap_or_else(|| plain::node(&mut self.arena, View::JUndefined, 0));
                let unit = plain::node(&mut self.arena, View::JUndefined, 1);
                plain::seq(&mut self.arena, value, unit)
            }
            Primitive::Ptypeof => norm::jm9_typeof(&mut self.arena, values[0]),
            Primitive::PrawJsCode(info) => {
                let text = self.arena.intern_text(info.code.trim());
                plain::node(&mut self.arena, View::JRaw { text }, u16::from(info.is_stmt))
            }
            Primitive::PcreateExtension(name) => {
                let name = plain::string(&mut self.arena, &name);
                let call = self.primitive_runtime("Primitive_exceptions", "create", &[name]);
                let comment = Some(self.arena.intern_text("@__PURE__"));
                self.arena.set_cold(call, crate::bir::Cold { loc: crate::lambda::LamLoc::NONE, comment });
                call
            }
            Primitive::PinitMod => self.primitive_runtime("Primitive_module", "init", &values),
            Primitive::PupdateMod => self.primitive_runtime("Primitive_module", "update", &values),
            // P: compile_debugger lowers each argument for effects before debugger.
            Primitive::Pdebugger => {
                for value in values { self.arena.release(value); }
                let statement = plain::node(&mut self.arena, View::SDebugger, 0);
                self.primitive_statement(statement, payload.loc);
                plain::node(&mut self.arena, View::JUndefined, 1)
            }
            // P: compile_primitive_js, Praise; conversion never binds a thrown value.
            Primitive::Praise => {
                let value = values.first().copied().unwrap_or_else(|| plain::node(&mut self.arena, View::JUndefined, 0));
                let statement = plain::node(&mut self.arena, View::SThrow { value }, 0);
                self.primitive_statement(statement, payload.loc);
                let value = match cx.cont {
                    Cont::Value(_) | Cont::Effect(Tail::No) => Some(plain::node(&mut self.arena, View::JUndefined, 0)),
                    _ => None,
                };
                return Probed::Out(Out { stmts: self.statements.since(Span { start: statements.start, len: 0 }), value, finished: Finished::True });
            }
            Primitive::Pstringlength => norm::je2_length(&mut self.arena, values[0], LengthObject::String),
            Primitive::Parraylength => norm::je2_length(&mut self.arena, values[0], LengthObject::Array),
            _ => unreachable!("primitive admitted by dispatch"),
        };
        self.primitive_result(cx, self.statements.since(Span { start: statements.start, len: 0 }), value)
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
    fn simple_primitive_arms_match_legacy() {
        use Primitive::*;
        for (primitive, arity) in [
            (PfnArity, 1), (Pstringadd, 2), (Pnot, 1), (Pidentity, 1),
            (Pfloatofint, 1), (Pignore, 1), (Ptypeof, 1),
            (PcreateExtension("Example".into()), 0), (PinitMod, 2), (PupdateMod, 3),
            (Praise, 1), (Pdebugger, 1),
            (PrawJsCode(crate::lambda::lam_primitive::JsRawInfo { code: "  value()  ".into(), is_stmt: false }), 0),
        ] {
            for literal in [false, true] {
                let mut a = LamArena::new();
                let args: Vec<_> = (0..arity).map(|i| if literal {
                    a.const_(Constant::String("text".into()))
                } else {
                    a.var(Ident::new(&format!("value{i}"), 10 + i, crate::ident::IdentFlags::NONE))
                }).collect();
                let root = a.prim_raw(primitive.clone(), &args, LamLoc::NONE);
                super::super::oracle_tests::compare(a, root);
            }
        }
    }

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
