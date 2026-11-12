//! P: compile_primitive: lower arguments once, sequence, then convert the result.
use super::*;
use crate::bir::PrimId;
use crate::bir::j::{norm, plain};
use crate::js_ir::op::LengthObject;
use crate::js_ir::BinOp;
use crate::lambda::lam_primitive::Primitive;

pub(super) struct Prim {
    pub primitive: PrimId,
    pub source: NodeId,
    pub operands: Vec<NodeId>,
}

impl State {
    pub(super) fn primitive_int(&self, node: NodeId) -> Option<i32> {
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
    pub(super) fn primitive_runtime(&mut self, name: &str, member: &str, args: &[NodeId]) -> NodeId {
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
    ) -> Result<Probed, Unsupported> {
        let outputs = children.map(|child| match child {
            Probed::Out(out) => out,
            Probed::Free(_) => unreachable!("argument realized before its next sibling"),
        }).collect();
        let (statements, values) = self.sequence_arguments(false, outputs);
        let payload = self.arena.primitive(prim.primitive).clone();
        let primitive = payload.primitive;
        // P: compile_flat_make_field. Cache module-path membership per source
        // occurrence, so a deep chain is inspected once, not walked per field.
        if let Primitive::Pfield(_, crate::lambda::FieldDbgInfo::Module { name }) = &primitive {
            if let [arg] = prim.operands.as_slice() {
                let nested = self.module_paths[arg.index()];
                if nested && name.as_str() == "make" { return Err(Unsupported("flat make")); }
                self.module_paths[prim.source.index()] = nested || matches!(self.source.view(*arg), View::Global { .. });
            }
        }
        let value = match primitive {
            // P: compile_primitive_js, dictionaries: extract only literal-key
            // tuple entries, exactly as the legacy filter_map does.
            Primitive::Pmakedict => {
                let entries = if let [array] = values.as_slice() {
                    if let View::JArray { values: items } = self.arena.view(*array) {
                        Some(items.iter().filter_map(|&item| {
                            if let View::JBlockLit { values: [key, value], .. } = self.arena.view(item) {
                                if let View::JStr { text } = self.arena.view(*key) { return Some((crate::bir::PropertyKey::Literal(text), *value)); }
                            }
                            None
                        }).collect::<Vec<_>>())
                    } else { None }
                } else { None };
                let result = if let Some(entries) = entries {
                    let (keys, kept): (Vec<_>, Vec<_>) = entries.into_iter().unzip();
                    for &value in &kept { self.arena.detach(value); }
                    let info = self.arena.js_info(crate::bir::JsPayload::Object(keys));
                    plain::node(&mut self.arena, View::JObject { values: &kept, info }, 0)
                } else { plain::node(&mut self.arena, View::JUndefined, 0) };
                for value in values { self.arena.release(value); }
                result
            }
            Primitive::PdictSpread => {
                let mut keys = Vec::new();
                let mut kept = Vec::new();
                for arg in values {
                    let entries = if let View::JObject { info, values } = self.arena.view(arg) {
                        let crate::bir::JsPayload::Object(props) = self.arena.javascript(info) else { unreachable!() };
                        props.iter().all(|p| matches!(p, crate::bir::PropertyKey::Literal(_) | crate::bir::PropertyKey::Symbol))
                            .then(|| (props.clone(), values.to_vec()))
                    } else { None };
                    if let Some((props, values)) = entries {
                        for &value in &values { self.arena.detach(value); }
                        self.arena.release(arg);
                        keys.extend(props); kept.extend(values);
                    } else { keys.push(crate::bir::PropertyKey::Spread); kept.push(arg); }
                }
                let info = self.arena.js_info(crate::bir::JsPayload::Object(keys));
                plain::node(&mut self.arena, View::JObject { values: &kept, info }, 0)
            }
            Primitive::PdictHas => {
                if let [object, property] = values.as_slice() {
                    plain::node(&mut self.arena, View::JIn { left: *property, right: *object }, 0)
                } else {
                    for value in values { self.arena.release(value); }
                    plain::node(&mut self.arena, View::JUndefined, 0)
                }
            }
            Primitive::ParraySpread => self.primitive_runtime("Primitive_array", "spread", &values),
            Primitive::PlistSpread => self.primitive_runtime("Primitive_list", "spread", &values),
            // P: compile_primitive_js, hashing runtime entry points.
            Primitive::Phash => self.primitive_runtime("Primitive_hash", "hash", &values),
            Primitive::PhashMixint => self.primitive_runtime("Primitive_hash", "hash_mix_int", &values),
            Primitive::PhashMixstring => self.primitive_runtime("Primitive_hash", "hash_mix_string", &values),
            Primitive::PhashFinalmix => self.primitive_runtime("Primitive_hash", "hash_final_mix", &values),
            // P: compile_primitive_js, blocks and fields (K: compile_field_access).
            Primitive::Pmakeblock(tag, mutable) => {
                let info = self.arena.js_info(crate::bir::JsPayload::Block(tag));
                plain::node(&mut self.arena, View::JBlockLit { values: &values, info },
                    if matches!(mutable, crate::lambda::lam_primitive::Mutable::Mutable) { 0 } else { 1 })
            }
            Primitive::Pmakelist => {
                let info = self.arena.js_info(crate::bir::JsPayload::Block(crate::lambda::TagInfo::constructor("::", 1)));
                plain::node(&mut self.arena, View::JBlockLit { values: &values, info }, 0)
            }
            Primitive::Pmakearray => plain::node(&mut self.arena, View::JArray { values: &values }, 0),
            Primitive::Pfield(idx, info) => self.primitive_field(idx, info, values[0]),
            Primitive::Psetfield(idx, info) => self.primitive_set_field(idx, info.name(), values[0], values[1]),
            Primitive::Pobjtag => {
                let property = self.arena.intern_text("TAG");
                plain::node(&mut self.arena, View::JDot { object: values[0], property, position: crate::js_ir::arena::FieldPos::NONE }, 1)
            }
            Primitive::Pobjsize => {
                let length = norm::je2_length(&mut self.arena, values[0], LengthObject::CamlBlock);
                norm::jm3_to_int32(&mut self.arena, length)
            }
            Primitive::PisPolyVarBlock => {
                let typeof_ = plain::node(&mut self.arena, View::JTypeof { value: values[0] }, 0);
                let object = plain::string(&mut self.arena, "object");
                plain::bin(&mut self.arena, BinOp::EqEqEq, typeof_, object)
            }
            // P: compile_primitive_js, indexing. Both string forms are checked.
            Primitive::Pstringrefs | Primitive::Pstringrefu => self.primitive_runtime("Primitive_string", "getChar", &values),
            Primitive::Parrayrefs => self.primitive_runtime("Primitive_array", "get", &values),
            Primitive::Parrayrefu => {
                if let [object, index] = values.as_slice() {
                    plain::node(&mut self.arena, View::JIndex { object: *object, index: *index }, 0)
                } else { for v in values { self.arena.release(v); } plain::node(&mut self.arena, View::JUndefined, 0) }
            }
            Primitive::Parraysetu => {
                if let [object, index, value] = values.as_slice() {
                    let target = plain::node(&mut self.arena, View::JIndex { object: *object, index: *index }, 0);
                    let assignment = norm::je4_bin(&mut self.arena, BinOp::Eq, target, *value);
                    let unit = plain::node(&mut self.arena, View::JUndefined, 0);
                    plain::seq(&mut self.arena, assignment, unit)
                } else { for v in values { self.arena.release(v); } plain::node(&mut self.arena, View::JUndefined, 0) }
            }
            // P: compile_primitive_js, template arms; J-M12 preserves raw spelling.
            Primitive::Ptemplate(segments) => norm::jm12_interpolated_template(&mut self.arena, segments, values),
            Primitive::PtaggedTemplate(segments) => {
                let parts = segments.into_iter().map(|s| crate::bir::TemplatePart { raw: self.arena.intern_text(&s), cooked: None }).collect();
                let info = self.arena.js_info(crate::bir::JsPayload::Tagged(parts));
                plain::node(&mut self.arena, View::JTagged { tag: values[0], values: &values[1..], info }, 0)
            }
            // X: some_expr / optional_block. Identity is a shape test, not purity.
            Primitive::Psome | Primitive::PsomeNotNest => {
                let value = values[0];
                let identity = matches!(primitive, Primitive::PsomeNotNest)
                    || matches!(self.arena.view(value), View::JNull | View::JObject { .. } | View::JNumber { .. }
                        | View::JBlockLit { .. } | View::JArray { .. } | View::JStr { .. })
                    || matches!(self.arena.view(value), View::JTemplate { .. }) && self.arena.node(value).aux() == 1;
                plain::node(&mut self.arena, View::JOptional { value }, u16::from(identity))
            }
            // X: val_from_option_expr.
            Primitive::PvalFromOption => {
                if let View::JOptional { value } = self.arena.view(values[0]) {
                    self.arena.detach(value); self.arena.release(values[0]); value
                } else { self.primitive_runtime("Primitive_option", "valFromOption", &values) }
            }
            Primitive::PvalFromOptionNotNest => values[0],
            // X: is_not_none_expr, intentionally drops even effectful Some payloads.
            Primitive::PisNotNone => match self.arena.view(values[0]) {
                View::JUndefined => { self.arena.release(values[0]); plain::boolean(&mut self.arena, false) }
                View::JOptional { .. } => { self.arena.release(values[0]); plain::boolean(&mut self.arena, true) }
                _ => {
                    let undefined = plain::node(&mut self.arena, View::JUndefined, 0);
                    norm::je4_bin(&mut self.arena, BinOp::NotEqEq, values[0], undefined)
                }
            },
            // X: is_null_expr / is_undefined_expr / is_null_or_undefined_expr.
            Primitive::PisNull | Primitive::PisUndefined => {
                let nullish = plain::node(&mut self.arena, if matches!(primitive, Primitive::PisNull) { View::JNull } else { View::JUndefined }, 0);
                norm::je4_bin(&mut self.arena, BinOp::EqEqEq, values[0], nullish)
            }
            Primitive::PisNullUndefined => norm::je3_is_null_or_undefined(&mut self.arena, values[0]),
            // X: null_to_opt_expr / null_undefined_to_opt_expr. Only leaf operands
            // are duplicated, so this costs constant work per primitive.
            Primitive::PnullToOpt | Primitive::PnullUndefinedToOpt => {
                let nullable = matches!(primitive, Primitive::PnullUndefinedToOpt);
                if matches!(self.arena.view(values[0]), View::Var { .. } | View::JUndefined | View::JNull) {
                    let copy = match self.arena.view(values[0]) {
                        View::Var { var } => plain::node(&mut self.arena, View::Var { var }, 0),
                        View::JUndefined => { let aux = self.arena.node(values[0]).aux(); plain::node(&mut self.arena, View::JUndefined, aux) },
                        View::JNull => plain::node(&mut self.arena, View::JNull, 0),
                        _ => unreachable!("inline option operand is a leaf"),
                    };
                    let test = if nullable { norm::je3_is_null_or_undefined(&mut self.arena, copy) } else {
                        let null = plain::node(&mut self.arena, View::JNull, 0);
                        norm::je4_bin(&mut self.arena, BinOp::EqEqEq, copy, null)
                    };
                    let undefined = plain::node(&mut self.arena, View::JUndefined, 0);
                    let some = plain::node(&mut self.arena, View::JOptional { value: values[0] }, 0);
                    norm::je7_cond(&mut self.arena, test, undefined, some)
                } else { self.primitive_runtime("Primitive_option", if nullable { "fromNullable" } else { "fromNull" }, &values) }
            }
            // P: compile_primitive_js, comparison arms.
            Primitive::Pintcomp(cmp) => self.primitive_int_comparison(cmp, values[0], values[1]),
            Primitive::Pboolcomp(cmp) => self.primitive_bool_comparison(cmp, values[0], values[1]),
            Primitive::Pstringcomp(cmp) => self.primitive_literal_comparison(cmp, values[0], values[1], false),
            Primitive::Pbigintcomp(cmp) => self.primitive_literal_comparison(cmp, values[0], values[1], true),
            Primitive::Pobjcomp(cmp) => self.primitive_object_comparison(cmp, values[0], values[1]),
            Primitive::Pfloatcomp(cmp @ (crate::lambda::lam_compat::Comparison::Eq | crate::lambda::lam_compat::Comparison::Neq)) => self.primitive_int_comparison(cmp, values[0], values[1]),
            Primitive::Pfloatcomp(cmp) | Primitive::Pjscomp(cmp) => norm::je4_bin(&mut self.arena, super::prim_cmp::comparison_op(cmp, true), values[0], values[1]),
            Primitive::Pobjorder => self.primitive_runtime("Primitive_object", "compare", &values),
            Primitive::Pobjmin => self.primitive_min_max("object", false, values[0], values[1]),
            Primitive::Pobjmax => self.primitive_min_max("object", true, values[0], values[1]),
            Primitive::Pboolorder => if let (Some(l), Some(r)) = (self.primitive_bool(values[0]), self.primitive_bool(values[1])) {
                self.arena.release(values[0]); self.arena.release(values[1]); plain::int(&mut self.arena, l.cmp(&r) as i32)
            } else { self.primitive_runtime("Primitive_bool", "compare", &values) },
            Primitive::Pboolmin => self.primitive_min_max("bool", false, values[0], values[1]),
            Primitive::Pboolmax => self.primitive_min_max("bool", true, values[0], values[1]),
            Primitive::Pintorder => self.primitive_runtime("Primitive_int", "compare", &values),
            Primitive::Pintmin => self.primitive_min_max("int", false, values[0], values[1]),
            Primitive::Pintmax => self.primitive_min_max("int", true, values[0], values[1]),
            Primitive::Pfloatorder => self.primitive_runtime("Primitive_float", "compare", &values),
            Primitive::Pfloatmin => self.primitive_min_max("float", false, values[0], values[1]),
            Primitive::Pfloatmax => self.primitive_min_max("float", true, values[0], values[1]),
            Primitive::Pbigintorder => self.primitive_runtime("Primitive_bigint", "compare", &values),
            Primitive::Pbigintmin => self.primitive_min_max("bigint", false, values[0], values[1]),
            Primitive::Pbigintmax => self.primitive_min_max("bigint", true, values[0], values[1]),
            Primitive::Pstringorder => self.primitive_runtime("Primitive_string", "compare", &values),
            Primitive::Pstringmin => self.primitive_min_max("string", false, values[0], values[1]),
            Primitive::Pstringmax => self.primitive_min_max("string", true, values[0], values[1]),
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
                return Ok(Probed::Out(Out { stmts: self.statements.since(Span { start: statements.start, len: 0 }), value, finished: Finished::True }));
            }
            Primitive::Pstringlength => norm::je2_length(&mut self.arena, values[0], LengthObject::String),
            Primitive::Parraylength => norm::je2_length(&mut self.arena, values[0], LengthObject::Array),
            Primitive::Psequand | Primitive::Psequor | Primitive::PjsCall(_)
            | Primitive::PjsApply | Primitive::PjsObjectCreate(_) | Primitive::PjsObjectGet(_)
            | Primitive::PjsObjectSet(_) | Primitive::PjsFnMethod | Primitive::Pjsx(_)
            | Primitive::Pimport(_) | Primitive::Pawait | Primitive::Pduprecord | Primitive::PrecordRest(_) => unreachable!("unsupported primitive rejected by dispatch"),
            Primitive::PextensionSlotEq => unreachable!("PextensionSlotEq is lowered in raw_lambda::lower"),
        };
        Ok(self.primitive_result(cx, self.statements.since(Span { start: statements.start, len: 0 }), value))
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
    fn option_arms_match_legacy() {
        use Primitive::*;
        for primitive in [Psome, PsomeNotNest, PvalFromOption, PvalFromOptionNotNest, PisNotNone, PnullToOpt, PnullUndefinedToOpt, PisNull, PisUndefined, PisNullUndefined] {
            for shape in 0..9 {
                let mut a = LamArena::new();
                let arg = match shape {
                    0 => a.const_(Constant::JsNull),
                    1 => a.const_(Constant::JsUndefined { is_unit: false }),
                    2 => a.const_(Constant::JsTrue),
                    3 => a.const_(Constant::String("text".into())),
                    4 => a.const_(Constant::Int { i: 3, comment: None }),
                    5 => a.const_(Constant::Block { tag_info: Box::new(crate::lambda::TagInfo::Tuple), elements: vec![] }),
                    _ => a.var(Ident::new("value", 10, crate::ident::IdentFlags::NONE)),
                };
                let arg = if shape >= 7 { a.prim_raw(PinitMod, &[arg], LamLoc::NONE) } else { arg };
                let arg = if shape == 8 { a.prim_raw(Psome, &[arg], LamLoc::NONE) } else { arg };
                let root = a.prim_raw(primitive.clone(), &[arg], LamLoc::NONE);
                super::super::oracle_tests::compare(a, root);
            }
        }
    }

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
