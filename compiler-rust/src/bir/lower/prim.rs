//! P: compile_primitive: lower arguments once, sequence, then convert the result.
use super::*;
use crate::bir::PrimId;
use crate::bir::j::{norm, plain};
use crate::js_ir::op::LengthObject;
use crate::js_ir::BinOp;
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
            | Primitive::Praise | Primitive::Pdebugger
            | Primitive::Paddint | Primitive::Psubint | Primitive::Pmulint | Primitive::Pdivint | Primitive::Pmodint | Primitive::Ppowint | Primitive::Pandint | Primitive::Porint | Primitive::Pxorint | Primitive::Plslint | Primitive::Paddfloat | Primitive::Psubfloat | Primitive::Pmulfloat | Primitive::Pdivfloat | Primitive::Pmodfloat | Primitive::Ppowfloat | Primitive::Paddbigint | Primitive::Psubbigint | Primitive::Pmulbigint | Primitive::Ppowbigint | Primitive::Pandbigint | Primitive::Porbigint | Primitive::Pxorbigint | Primitive::Plslbigint | Primitive::Pasrbigint | Primitive::Pasrint | Primitive::Pnotint | Primitive::Pnotbigint | Primitive::Pintoffloat | Primitive::Pnegint | Primitive::Pnegfloat | Primitive::Pnegbigint | Primitive::Plsrint | Primitive::Pdivbigint | Primitive::Pmodbigint)
    }

    fn primitive_int(&self, node: NodeId) -> Option<i32> {
        if let View::JNumber { value } = self.arena.view(node) {
            match self.arena.constant(value) {
                crate::bir::Constant::Int(n) => Some(*n as i32),
                crate::bir::Constant::Char(n) => Some(*n as i32),
                _ => None,
            }
        } else { None }
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
            // P: compile_primitive_js, arithmetic arms; J-M3–M13 own the folds.
            Primitive::Paddint => norm::jm4_int32_add_sub(&mut self.arena, false, values[0], values[1]),
            Primitive::Psubint => norm::jm4_int32_add_sub(&mut self.arena, true, values[0], values[1]),
            Primitive::Pmulint => norm::jm5_int32_mul(&mut self.arena, values[0], values[1]),
            Primitive::Pdivint => norm::jm13_int32_div(&mut self.arena, self.check_div_by_zero, values[0], values[1]),
            Primitive::Pmodint => norm::jm13_int32_mod(&mut self.arena, self.check_div_by_zero, values[0], values[1]),
            Primitive::Ppowint => norm::jm6_int32_pow(&mut self.arena, values[0], values[1]),
            Primitive::Pandint => norm::jm8_int32_band(&mut self.arena, values[0], values[1]),
            Primitive::Porint => norm::jm3_int32_bor(&mut self.arena, values[0], values[1]),
            Primitive::Pxorint => norm::jm8_int32_bxor(&mut self.arena, values[0], values[1]),
            Primitive::Plslint => norm::jm7_int32_lsl(&mut self.arena, values[0], values[1]),
            Primitive::Paddfloat => norm::je4_bin(&mut self.arena, BinOp::Plus, values[0], values[1]),
            Primitive::Psubfloat => norm::je4_bin(&mut self.arena, BinOp::Minus, values[0], values[1]),
            Primitive::Pmulfloat => norm::je4_bin(&mut self.arena, BinOp::Mul, values[0], values[1]),
            Primitive::Pdivfloat => norm::je4_bin(&mut self.arena, BinOp::Div, values[0], values[1]),
            Primitive::Pmodfloat => norm::je4_bin(&mut self.arena, BinOp::Mod, values[0], values[1]),
            Primitive::Ppowfloat => norm::je4_bin(&mut self.arena, BinOp::Pow, values[0], values[1]),
            Primitive::Paddbigint => norm::je4_bin(&mut self.arena, BinOp::Plus, values[0], values[1]),
            Primitive::Psubbigint => norm::je4_bin(&mut self.arena, BinOp::Minus, values[0], values[1]),
            Primitive::Pmulbigint => norm::je4_bin(&mut self.arena, BinOp::Mul, values[0], values[1]),
            Primitive::Ppowbigint => norm::je4_bin(&mut self.arena, BinOp::Pow, values[0], values[1]),
            Primitive::Pandbigint => norm::je4_bin(&mut self.arena, BinOp::Band, values[0], values[1]),
            Primitive::Porbigint => norm::je4_bin(&mut self.arena, BinOp::Bor, values[0], values[1]),
            Primitive::Pxorbigint => norm::je4_bin(&mut self.arena, BinOp::Bxor, values[0], values[1]),
            Primitive::Plslbigint => norm::je4_bin(&mut self.arena, BinOp::Lsl, values[0], values[1]),
            Primitive::Pasrbigint => norm::je4_bin(&mut self.arena, BinOp::Asr, values[0], values[1]),
            Primitive::Pasrint => norm::je4_bin(&mut self.arena, BinOp::Asr, values[0], values[1]),
            Primitive::Pnotint => norm::jm10_int_bnot(&mut self.arena, values[0]),
            Primitive::Pnotbigint => norm::jm10_int_bnot(&mut self.arena, values[0]),
            Primitive::Pintoffloat => norm::jm3_to_int32(&mut self.arena, values[0]),
            Primitive::Pnegint => { let zero = plain::int(&mut self.arena, 0); norm::jm4_int32_add_sub(&mut self.arena, true, zero, values[0]) },
            Primitive::Pnegfloat => { let value = self.arena.intern_float("0.").unwrap(); let zero = plain::node(&mut self.arena, View::JNumber { value }, 0); norm::je4_bin(&mut self.arena, BinOp::Minus, zero, values[0]) },
            Primitive::Pnegbigint => { let text = self.arena.intern_text("+0"); let value = self.arena.intern_const(crate::bir::Constant::BigInt(text)); let zero = plain::node(&mut self.arena, View::JNumber { value }, 0); norm::je4_bin(&mut self.arena, BinOp::Minus, zero, values[0]) },
            Primitive::Plsrint => {
                if self.primitive_int(values[1]) == Some(0) {
                    self.arena.release(values[1]); values[0]
                } else {
                    let value = norm::jm8_int32_lsr(&mut self.arena, values[0], values[1]);
                    norm::jm3_to_int32(&mut self.arena, value)
                }
            },
            Primitive::Pdivbigint => if self.check_div_by_zero { self.primitive_runtime("Primitive_bigint", "div", &values) } else { norm::je4_bin(&mut self.arena, BinOp::Div, values[0], values[1]) },
            Primitive::Pmodbigint => if self.check_div_by_zero { self.primitive_runtime("Primitive_bigint", "mod_", &values) } else { norm::je4_bin(&mut self.arena, BinOp::Mod, values[0], values[1]) },
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
    fn arithmetic_arms_match_legacy_with_and_without_checks() {
        use Primitive::*;
        for (primitive, arity) in [
            (Paddint, 2),
            (Psubint, 2),
            (Pmulint, 2),
            (Pdivint, 2),
            (Pmodint, 2),
            (Ppowint, 2),
            (Pandint, 2),
            (Porint, 2),
            (Pxorint, 2),
            (Plslint, 2),
            (Paddfloat, 2),
            (Psubfloat, 2),
            (Pmulfloat, 2),
            (Pdivfloat, 2),
            (Pmodfloat, 2),
            (Ppowfloat, 2),
            (Paddbigint, 2),
            (Psubbigint, 2),
            (Pmulbigint, 2),
            (Ppowbigint, 2),
            (Pandbigint, 2),
            (Porbigint, 2),
            (Pxorbigint, 2),
            (Plslbigint, 2),
            (Pasrbigint, 2),
            (Pasrint, 2),
            (Pnotint, 1),
            (Pnotbigint, 1),
            (Pintoffloat, 1),
            (Pnegint, 1),
            (Pnegfloat, 1),
            (Pnegbigint, 1),
            (Plsrint, 2),
            (Pdivbigint, 2),
            (Pmodbigint, 2),
] {
            for literal in [false, true] {
                // The legacy literal LSR helper requires a count in 0..32.
                let divisors = if matches!(primitive, Plsrint) { [0, 2, 31] } else { [0, 2, -1] };
                for divisor in divisors {
                    for checks in [false, true] {
                        let mut a = LamArena::new();
                        let args: Vec<_> = (0..arity).map(|i| if literal {
                            a.const_(Constant::Int { i: if i == 0 { i32::MIN } else { divisor }, comment: None })
                        } else { a.var(Ident::new(&format!("arg{i}"), 10 + i, crate::ident::IdentFlags::NONE)) }).collect();
                        let root = a.prim_raw(primitive.clone(), &args, LamLoc::NONE);
                        super::super::oracle_tests::compare_with_checks(a, root, checks);
                    }
                }
            }
        }
    }

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
