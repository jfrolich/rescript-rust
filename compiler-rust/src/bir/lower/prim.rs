//! P: compile_primitive: lower arguments once, sequence, then convert the result.
use super::*;
use crate::bir::PrimId;
use crate::bir::j::{norm, plain};
use crate::js_ir::BinOp;
use crate::js_ir::op::LengthObject;
use crate::lambda::lam_primitive::Primitive;

pub(super) struct Prim {
    pub primitive: PrimId,
    pub operands: crate::bir::ListId,
}

impl State {
    /// O(1): inspect a numeric leaf and its interned constant.
    pub(super) fn primitive_int(&self, node: NodeId) -> Option<i32> {
        if let View::JNumber { value } = self.arena.view(node) {
            match self.arena.constant(value) {
                crate::bir::Constant::Int(n) => Some(*n as i32),
                crate::bir::Constant::Char(n) => Some(*n as i32),
                _ => None,
            }
        } else {
            None
        }
    }

    /// C: runtime_call_expr / X: pure_runtime_call_expr. Runtime imports retain
    /// encounter order; purity annotations are comments, not purity facts.
    /// O(r + a + text bytes), with r runtime modules (bounded by the primitive
    /// runtime inventory) and a operands; no expression subtree is walked.
    pub(super) fn primitive_runtime(
        &mut self,
        name: &str,
        member: &str,
        args: &[NodeId],
    ) -> NodeId {
        let module = match self
            .arena
            .pools
            .j_modules
            .iter()
            .position(|m| m.id.name() == name && matches!(m.kind, crate::js_ir::Kind::Runtime))
        {
            Some(i) => crate::bir::ImportId(i as u32),
            None => {
                let module = crate::bir::ImportId(self.arena.pools.imports.len() as u32);
                let path = self.arena.intern_text(name);
                self.arena.pools.imports.push(crate::bir::Import {
                    name: crate::name::Name::new(name),
                    path,
                });
                self.arena.pools.j_modules.push(crate::js_ir::ModuleId {
                    id: Ident::create_persistent(name),
                    kind: crate::js_ir::Kind::Runtime,
                    dynamic_import: false,
                });
                module
            }
        };
        let member = Some(self.arena.intern_text(member));
        let callee = plain::node(&mut self.arena, View::JQualified { module, member }, 0);
        let info = self
            .arena
            .js_info(crate::bir::JsPayload::Call(crate::js_ir::CallInfo {
                kind: crate::js_ir::CallKind::BuiltinRuntime,
                arity: crate::js_ir::CallArity::Full,
                ..Default::default()
            }));
        plain::node(&mut self.arena, View::JCall { callee, args, info }, 0)
    }

    /// P: compile_primitive_js / compile_debugger source locations on statements.
    /// O(1): one location lookup and one statement push.
    fn primitive_statement(&mut self, statement: NodeId, loc: crate::lambda::LamLoc) {
        if self
            .locations
            .as_ref()
            .and_then(|locations| locations.get(loc))
            .is_some_and(|loc| !loc.loc_ghost && loc.loc_start.cnum >= 0)
        {
            self.arena
                .set_cold(statement, crate::bir::Cold { loc, comment: None });
            let mut flags = self.arena.node(statement).flags();
            flags.0 |= crate::bir::NodeFlags::JS_LOC_PRESENT;
            self.arena.nodes[statement.index()].set_flags(flags);
        }
        self.statements.push(statement);
    }

    /// P: compile_primitive_js. O(a + emitted metadata bytes), plus sequencing
    /// holds and the named J-rule costs. Arguments are decoded once; dictionary
    /// extraction visits each immediate entry once. The payload pool is borrowed
    /// while the output arena is mutated; moving its Vec header costs O(1).
    pub(super) fn finish_primitive(
        &mut self,
        cx: Cx,
        prim: Prim,
        children: impl Iterator<Item = Probed>,
    ) -> Result<Probed, Unsupported> {
        let payloads = std::mem::take(&mut self.arena.pools.prims);
        let payload = &payloads[prim.primitive.index()];
        let result = self.finish_primitive_payload(cx, prim, payload, children);
        self.arena.pools.prims = payloads;
        result
    }

    /// P: compile_primitive_js. O(a + emitted metadata bytes + J-rule costs).
    /// Borrow source metadata; only metadata owned by the output is copied.
    fn finish_primitive_payload(
        &mut self,
        cx: Cx,
        prim: Prim,
        payload: &crate::bir::PrimPayload,
        children: impl Iterator<Item = Probed>,
    ) -> Result<Probed, Unsupported> {
        let outputs = children
            .map(|child| match child {
                Probed::Out(out) => out,
                Probed::Free(_) => unreachable!("argument realized before its next sibling"),
            })
            .collect();
        let outputs = match &payload.primitive {
            Primitive::PjsCall(call) => self.hold_external_args(cx, &call.arg_types, outputs),
            Primitive::PjsObjectCreate(specs) => self.hold_external_obj_args(cx, specs, outputs),
            Primitive::PjsObjectGet(_) => {
                let mut outputs: smallvec::SmallVec<[Out; 4]> = outputs;
                if outputs.len() == 1 {
                    let arg = outputs.pop().unwrap();
                    outputs.push(self.hold_external_receiver(cx, arg));
                }
                outputs
            }
            _ => outputs,
        };
        let (statements, values) = self.sequence_arguments(false, outputs);
        self.primitive_steps += values.len() + 1;
        let primitive = &payload.primitive;
        let value = match primitive {
            // P: compile_primitive_js, dictionaries: extract only literal-key
            // tuple entries, exactly as the legacy filter_map does.
            Primitive::Pmakedict => {
                let entries = if let [array] = values.as_slice() {
                    if let View::JArray { values: items } = self.arena.view(*array) {
                        Some(
                            items
                                .iter()
                                .filter_map(|&item| {
                                    self.primitive_steps += 1;
                                    if let View::JBlockLit {
                                        values: [key, value],
                                        ..
                                    } = self.arena.view(item)
                                    {
                                        if let View::JStr { text } = self.arena.view(*key) {
                                            return Some((
                                                crate::bir::PropertyKey::Literal(text),
                                                *value,
                                            ));
                                        }
                                    }
                                    None
                                })
                                .collect::<Vec<_>>(),
                        )
                    } else {
                        None
                    }
                } else {
                    None
                };
                let result = if let Some(entries) = entries {
                    let (keys, kept): (Vec<_>, Vec<_>) = entries.into_iter().unzip();
                    for &value in &kept {
                        self.arena.detach(value);
                    }
                    let info = self.arena.js_info(crate::bir::JsPayload::Object(keys));
                    plain::node(
                        &mut self.arena,
                        View::JObject {
                            values: &kept,
                            info,
                        },
                        0,
                    )
                } else {
                    plain::node(&mut self.arena, View::JUndefined, 0)
                };
                for value in values {
                    self.arena.release(value);
                }
                result
            }
            Primitive::PdictSpread => {
                let mut keys = Vec::new();
                let mut kept = Vec::new();
                for arg in values {
                    self.primitive_steps += 1;
                    let start = kept.len();
                    let flatten = if let View::JObject { info, values } = self.arena.view(arg) {
                        let crate::bir::JsPayload::Object(props) = self.arena.javascript(info)
                        else {
                            unreachable!()
                        };
                        let literal = props.iter().all(|p| {
                            matches!(
                                p,
                                crate::bir::PropertyKey::Literal(_)
                                    | crate::bir::PropertyKey::Symbol
                            )
                        });
                        if literal {
                            keys.extend_from_slice(props);
                            kept.extend_from_slice(values);
                        }
                        literal
                    } else {
                        false
                    };
                    if flatten {
                        for &value in &kept[start..] {
                            self.arena.detach(value);
                        }
                        self.arena.release(arg);
                    } else {
                        keys.push(crate::bir::PropertyKey::Spread);
                        kept.push(arg);
                    }
                }
                let info = self.arena.js_info(crate::bir::JsPayload::Object(keys));
                plain::node(
                    &mut self.arena,
                    View::JObject {
                        values: &kept,
                        info,
                    },
                    0,
                )
            }
            Primitive::PdictHas => {
                if let [object, property] = values.as_slice() {
                    plain::node(
                        &mut self.arena,
                        View::JIn {
                            left: *property,
                            right: *object,
                        },
                        0,
                    )
                } else {
                    for value in values {
                        self.arena.release(value);
                    }
                    plain::node(&mut self.arena, View::JUndefined, 0)
                }
            }
            Primitive::ParraySpread => self.primitive_runtime("Primitive_array", "spread", &values),
            Primitive::PlistSpread => self.primitive_runtime("Primitive_list", "spread", &values),
            // P: compile_primitive_js, hashing runtime entry points.
            Primitive::Phash => self.primitive_runtime("Primitive_hash", "hash", &values),
            Primitive::PhashMixint => {
                self.primitive_runtime("Primitive_hash", "hash_mix_int", &values)
            }
            Primitive::PhashMixstring => {
                self.primitive_runtime("Primitive_hash", "hash_mix_string", &values)
            }
            Primitive::PhashFinalmix => {
                self.primitive_runtime("Primitive_hash", "hash_final_mix", &values)
            }
            // P: compile_primitive_js, blocks and fields (K: compile_field_access).
            Primitive::Pmakeblock(tag, mutable) => {
                let info = self.arena.js_info(crate::bir::JsPayload::Block(tag.clone()));
                plain::node(
                    &mut self.arena,
                    View::JBlockLit {
                        values: &values,
                        info,
                    },
                    if matches!(mutable, crate::lambda::lam_primitive::Mutable::Mutable) {
                        1
                    } else {
                        0
                    },
                )
            }
            Primitive::Pmakelist => {
                let info = self.arena.js_info(crate::bir::JsPayload::Block(
                    crate::lambda::TagInfo::constructor("::", 1),
                ));
                plain::node(
                    &mut self.arena,
                    View::JBlockLit {
                        values: &values,
                        info,
                    },
                    1,
                )
            }
            Primitive::Pmakearray => {
                plain::node(&mut self.arena, View::JArray { values: &values }, 1)
            }
            Primitive::Pfield(idx, info) => self.primitive_field(*idx, info, values[0]),
            Primitive::Psetfield(idx, info) => {
                self.primitive_set_field(*idx, info.name(), values[0], values[1])
            }
            Primitive::Pobjtag => {
                let property = self.arena.intern_text("TAG");
                plain::node(
                    &mut self.arena,
                    View::JDot {
                        object: values[0],
                        property,
                        position: crate::js_ir::arena::FieldPos::NONE,
                    },
                    1,
                )
            }
            Primitive::Pobjsize => {
                let length = norm::je2_length(&mut self.arena, values[0], LengthObject::CamlBlock);
                norm::jm3_to_int32(&mut self.arena, length)
            }
            Primitive::PisPolyVarBlock => {
                // P:642 / E:653 folds typeof before comparing the type name.
                let typeof_ = norm::jm9_typeof(&mut self.arena, values[0]);
                let object = plain::string(&mut self.arena, "object");
                norm::je4_bin(&mut self.arena, BinOp::EqEqEq, typeof_, object)
            }
            // P: compile_primitive_js, indexing. Both string forms are checked.
            Primitive::Pstringrefs | Primitive::Pstringrefu => {
                self.primitive_runtime("Primitive_string", "getChar", &values)
            }
            Primitive::Parrayrefs => self.primitive_runtime("Primitive_array", "get", &values),
            Primitive::Parrayrefu => {
                if let [object, index] = values.as_slice() {
                    plain::node(
                        &mut self.arena,
                        View::JIndex {
                            object: *object,
                            index: *index,
                        },
                        0,
                    )
                } else {
                    for v in values {
                        self.arena.release(v);
                    }
                    plain::node(&mut self.arena, View::JUndefined, 0)
                }
            }
            Primitive::Parraysetu => {
                if let [object, index, value] = values.as_slice() {
                    let target = plain::node(
                        &mut self.arena,
                        View::JIndex {
                            object: *object,
                            index: *index,
                        },
                        0,
                    );
                    let assignment = norm::je4_bin(&mut self.arena, BinOp::Eq, target, *value);
                    let unit = plain::node(&mut self.arena, View::JUndefined, 0);
                    plain::seq(&mut self.arena, assignment, unit)
                } else {
                    for v in values {
                        self.arena.release(v);
                    }
                    plain::node(&mut self.arena, View::JUndefined, 0)
                }
            }
            // P: compile_primitive_js, template arms; J-M12 preserves raw spelling.
            Primitive::Ptemplate(segments) => {
                norm::jm12_interpolated_template(&mut self.arena, segments.clone(), values.into_vec())
            }
            Primitive::PtaggedTemplate(segments) => {
                let parts = segments
                    .iter()
                    .map(|s| crate::bir::TemplatePart {
                        raw: self.arena.intern_text(s),
                        cooked: None,
                    })
                    .collect();
                let info = self.arena.js_info(crate::bir::JsPayload::Tagged(parts));
                plain::node(
                    &mut self.arena,
                    View::JTagged {
                        tag: values[0],
                        values: &values[1..],
                        info,
                    },
                    0,
                )
            }
            // X: some_expr / optional_block. Identity is a shape test, not purity.
            Primitive::Psome | Primitive::PsomeNotNest => {
                let value = values[0];
                let identity = matches!(primitive, Primitive::PsomeNotNest)
                    || matches!(
                        self.arena.view(value),
                        View::JNull
                            | View::JObject { .. }
                            | View::JNumber { .. }
                            | View::JBlockLit { .. }
                            | View::JArray { .. }
                            | View::JStr { .. }
                    )
                    || matches!(self.arena.view(value), View::JTemplate { .. })
                        && self.arena.node(value).aux() == 1;
                plain::node(
                    &mut self.arena,
                    View::JOptional { value },
                    u16::from(identity),
                )
            }
            // X: val_from_option_expr.
            Primitive::PvalFromOption => {
                if let View::JOptional { value } = self.arena.view(values[0]) {
                    self.arena.detach(value);
                    self.arena.release(values[0]);
                    value
                } else {
                    self.primitive_runtime("Primitive_option", "valFromOption", &values)
                }
            }
            Primitive::PvalFromOptionNotNest => values[0],
            // X: is_not_none_expr, intentionally drops even effectful Some payloads.
            Primitive::PisNotNone => match self.arena.view(values[0]) {
                View::JUndefined => {
                    self.arena.release(values[0]);
                    plain::boolean(&mut self.arena, false)
                }
                View::JOptional { .. } => {
                    self.arena.release(values[0]);
                    plain::boolean(&mut self.arena, true)
                }
                _ => {
                    let undefined = plain::node(&mut self.arena, View::JUndefined, 0);
                    norm::je4_bin(&mut self.arena, BinOp::NotEqEq, values[0], undefined)
                }
            },
            // X: is_null_expr / is_undefined_expr / is_null_or_undefined_expr.
            Primitive::PisNull | Primitive::PisUndefined => {
                let nullish = plain::node(
                    &mut self.arena,
                    if matches!(primitive, Primitive::PisNull) {
                        View::JNull
                    } else {
                        View::JUndefined
                    },
                    0,
                );
                norm::je4_bin(&mut self.arena, BinOp::EqEqEq, values[0], nullish)
            }
            Primitive::PisNullUndefined => {
                norm::je3_is_null_or_undefined(&mut self.arena, values[0])
            }
            // X: null_to_opt_expr / null_undefined_to_opt_expr. Only leaf operands
            // are duplicated, so this costs constant work per primitive.
            Primitive::PnullToOpt | Primitive::PnullUndefinedToOpt => {
                let nullable = matches!(primitive, Primitive::PnullUndefinedToOpt);
                if matches!(
                    self.arena.view(values[0]),
                    View::Var { .. } | View::JUndefined | View::JNull
                ) {
                    let copy = match self.arena.view(values[0]) {
                        View::Var { var } => plain::node(&mut self.arena, View::Var { var }, 0),
                        View::JUndefined => {
                            let aux = self.arena.node(values[0]).aux();
                            plain::node(&mut self.arena, View::JUndefined, aux)
                        }
                        View::JNull => plain::node(&mut self.arena, View::JNull, 0),
                        _ => unreachable!("inline option operand is a leaf"),
                    };
                    let test = if nullable {
                        norm::je3_is_null_or_undefined(&mut self.arena, copy)
                    } else {
                        let null = plain::node(&mut self.arena, View::JNull, 0);
                        norm::je4_bin(&mut self.arena, BinOp::EqEqEq, copy, null)
                    };
                    let undefined = plain::node(&mut self.arena, View::JUndefined, 0);
                    let some =
                        plain::node(&mut self.arena, View::JOptional { value: values[0] }, 0);
                    norm::je7_cond(&mut self.arena, test, undefined, some)
                } else {
                    self.primitive_runtime(
                        "Primitive_option",
                        if nullable { "fromNullable" } else { "fromNull" },
                        &values,
                    )
                }
            }
            // P: compile_primitive_js, comparison arms.
            Primitive::Pintcomp(cmp) => self.primitive_int_comparison(*cmp, values[0], values[1]),
            Primitive::Pboolcomp(cmp) => self.primitive_bool_comparison(*cmp, values[0], values[1]),
            Primitive::Pstringcomp(cmp) => {
                self.primitive_literal_comparison(*cmp, values[0], values[1], false)
            }
            Primitive::Pbigintcomp(cmp) => {
                self.primitive_literal_comparison(*cmp, values[0], values[1], true)
            }
            Primitive::Pobjcomp(cmp) => self.primitive_object_comparison(*cmp, values[0], values[1]),
            Primitive::Pfloatcomp(
                cmp @ (crate::lambda::lam_compat::Comparison::Eq
                | crate::lambda::lam_compat::Comparison::Neq),
            ) => self.primitive_int_comparison(*cmp, values[0], values[1]),
            Primitive::Pfloatcomp(cmp) | Primitive::Pjscomp(cmp) => norm::je4_bin(
                &mut self.arena,
                super::prim_cmp::comparison_op(*cmp, true),
                values[0],
                values[1],
            ),
            Primitive::Pobjorder => self.primitive_runtime("Primitive_object", "compare", &values),
            Primitive::Pobjmin => self.primitive_min_max("object", false, values[0], values[1]),
            Primitive::Pobjmax => self.primitive_min_max("object", true, values[0], values[1]),
            Primitive::Pboolorder => {
                if let (Some(l), Some(r)) = (
                    self.primitive_bool(values[0]),
                    self.primitive_bool(values[1]),
                ) {
                    self.arena.release(values[0]);
                    self.arena.release(values[1]);
                    plain::int(&mut self.arena, l.cmp(&r) as i32)
                } else {
                    self.primitive_runtime("Primitive_bool", "compare", &values)
                }
            }
            Primitive::Pboolmin => self.primitive_min_max("bool", false, values[0], values[1]),
            Primitive::Pboolmax => self.primitive_min_max("bool", true, values[0], values[1]),
            Primitive::Pintorder => self.primitive_runtime("Primitive_int", "compare", &values),
            Primitive::Pintmin => self.primitive_min_max("int", false, values[0], values[1]),
            Primitive::Pintmax => self.primitive_min_max("int", true, values[0], values[1]),
            Primitive::Pfloatorder => self.primitive_runtime("Primitive_float", "compare", &values),
            Primitive::Pfloatmin => self.primitive_min_max("float", false, values[0], values[1]),
            Primitive::Pfloatmax => self.primitive_min_max("float", true, values[0], values[1]),
            Primitive::Pbigintorder => {
                self.primitive_runtime("Primitive_bigint", "compare", &values)
            }
            Primitive::Pbigintmin => self.primitive_min_max("bigint", false, values[0], values[1]),
            Primitive::Pbigintmax => self.primitive_min_max("bigint", true, values[0], values[1]),
            Primitive::Pstringorder => {
                self.primitive_runtime("Primitive_string", "compare", &values)
            }
            Primitive::Pstringmin => self.primitive_min_max("string", false, values[0], values[1]),
            Primitive::Pstringmax => self.primitive_min_max("string", true, values[0], values[1]),
            // P: compile_primitive_js, arithmetic arms; J-M3–M13 own the folds.
            Primitive::Paddint => {
                norm::jm4_int32_add_sub(&mut self.arena, false, values[0], values[1])
            }
            Primitive::Psubint => {
                norm::jm4_int32_add_sub(&mut self.arena, true, values[0], values[1])
            }
            Primitive::Pmulint => norm::jm5_int32_mul(&mut self.arena, values[0], values[1]),
            Primitive::Pdivint => norm::jm13_int32_div(
                &mut self.arena,
                self.check_div_by_zero,
                values[0],
                values[1],
            ),
            Primitive::Pmodint => norm::jm13_int32_mod(
                &mut self.arena,
                self.check_div_by_zero,
                values[0],
                values[1],
            ),
            Primitive::Ppowint => norm::jm6_int32_pow(&mut self.arena, values[0], values[1]),
            Primitive::Pandint => norm::jm8_int32_band(&mut self.arena, values[0], values[1]),
            Primitive::Porint => norm::jm3_int32_bor(&mut self.arena, values[0], values[1]),
            Primitive::Pxorint => norm::jm8_int32_bxor(&mut self.arena, values[0], values[1]),
            Primitive::Plslint => norm::jm7_int32_lsl(&mut self.arena, values[0], values[1]),
            Primitive::Paddfloat => {
                norm::je4_bin(&mut self.arena, BinOp::Plus, values[0], values[1])
            }
            Primitive::Psubfloat => {
                norm::je4_bin(&mut self.arena, BinOp::Minus, values[0], values[1])
            }
            Primitive::Pmulfloat => {
                norm::je4_bin(&mut self.arena, BinOp::Mul, values[0], values[1])
            }
            Primitive::Pdivfloat => {
                norm::je4_bin(&mut self.arena, BinOp::Div, values[0], values[1])
            }
            Primitive::Pmodfloat => {
                norm::je4_bin(&mut self.arena, BinOp::Mod, values[0], values[1])
            }
            Primitive::Ppowfloat => {
                norm::je4_bin(&mut self.arena, BinOp::Pow, values[0], values[1])
            }
            Primitive::Paddbigint => {
                norm::je4_bin(&mut self.arena, BinOp::Plus, values[0], values[1])
            }
            Primitive::Psubbigint => {
                norm::je4_bin(&mut self.arena, BinOp::Minus, values[0], values[1])
            }
            Primitive::Pmulbigint => {
                norm::je4_bin(&mut self.arena, BinOp::Mul, values[0], values[1])
            }
            Primitive::Ppowbigint => {
                norm::je4_bin(&mut self.arena, BinOp::Pow, values[0], values[1])
            }
            Primitive::Pandbigint => {
                norm::je4_bin(&mut self.arena, BinOp::Band, values[0], values[1])
            }
            Primitive::Porbigint => {
                norm::je4_bin(&mut self.arena, BinOp::Bor, values[0], values[1])
            }
            Primitive::Pxorbigint => {
                norm::je4_bin(&mut self.arena, BinOp::Bxor, values[0], values[1])
            }
            Primitive::Plslbigint => {
                norm::je4_bin(&mut self.arena, BinOp::Lsl, values[0], values[1])
            }
            Primitive::Pasrbigint => {
                norm::je4_bin(&mut self.arena, BinOp::Asr, values[0], values[1])
            }
            Primitive::Pasrint => norm::je4_bin(&mut self.arena, BinOp::Asr, values[0], values[1]),
            Primitive::Pnotint => norm::jm10_int_bnot(&mut self.arena, values[0]),
            Primitive::Pnotbigint => norm::jm10_int_bnot(&mut self.arena, values[0]),
            Primitive::Pintoffloat => norm::jm3_to_int32(&mut self.arena, values[0]),
            Primitive::Pnegint => {
                let zero = plain::int(&mut self.arena, 0);
                norm::jm4_int32_add_sub(&mut self.arena, true, zero, values[0])
            }
            Primitive::Pnegfloat => {
                let value = self.arena.intern_float("0.").unwrap();
                let zero = plain::node(&mut self.arena, View::JNumber { value }, 0);
                norm::je4_bin(&mut self.arena, BinOp::Minus, zero, values[0])
            }
            Primitive::Pnegbigint => {
                let text = self.arena.intern_text("+0");
                let value = self.arena.intern_const(crate::bir::Constant::BigInt(text));
                let zero = plain::node(&mut self.arena, View::JNumber { value }, 0);
                norm::je4_bin(&mut self.arena, BinOp::Minus, zero, values[0])
            }
            Primitive::Plsrint => {
                if self.primitive_int(values[1]) == Some(0) {
                    self.arena.release(values[1]);
                    values[0]
                } else {
                    let value = norm::jm8_int32_lsr(&mut self.arena, values[0], values[1]);
                    norm::jm3_to_int32(&mut self.arena, value)
                }
            }
            Primitive::Pdivbigint => {
                if self.check_div_by_zero {
                    self.primitive_runtime("Primitive_bigint", "div", &values)
                } else {
                    norm::je4_bin(&mut self.arena, BinOp::Div, values[0], values[1])
                }
            }
            Primitive::Pmodbigint => {
                if self.check_div_by_zero {
                    self.primitive_runtime("Primitive_bigint", "mod_", &values)
                } else {
                    norm::je4_bin(&mut self.arena, BinOp::Mod, values[0], values[1])
                }
            }
            // P: compile_primitive_js, PfnArity.
            Primitive::PfnArity => match values.first() {
                Some(&value) => norm::je2_length(&mut self.arena, value, LengthObject::Function),
                None => plain::node(&mut self.arena, View::JUndefined, 0),
            },
            // P: compile_primitive_js, strings and booleans.
            Primitive::Pstringadd => norm::je1_string_append(&mut self.arena, values[0], values[1]),
            Primitive::Pnot => norm::je8_not(&mut self.arena, values[0]),
            // P: compile_primitive_js, identity group.
            Primitive::Pidentity | Primitive::Pfloatofint => values
                .first()
                .copied()
                .unwrap_or_else(|| plain::node(&mut self.arena, View::JUndefined, 0)),
            Primitive::Pignore => {
                let value = values
                    .first()
                    .copied()
                    .unwrap_or_else(|| plain::node(&mut self.arena, View::JUndefined, 0));
                let unit = plain::node(&mut self.arena, View::JUndefined, 1);
                plain::seq(&mut self.arena, value, unit)
            }
            Primitive::Ptypeof => norm::jm9_typeof(&mut self.arena, values[0]),
            Primitive::PrawJsCode(info) => {
                let text = self.arena.intern_text(info.code.trim());
                plain::node(
                    &mut self.arena,
                    View::JRaw { text },
                    u16::from(info.is_stmt),
                )
            }
            Primitive::PcreateExtension(name) => {
                let name = plain::string(&mut self.arena, name);
                let call = self.primitive_runtime("Primitive_exceptions", "create", &[name]);
                let comment = Some(self.arena.intern_text("@__PURE__"));
                self.arena.set_cold(
                    call,
                    crate::bir::Cold {
                        loc: crate::lambda::LamLoc::NONE,
                        comment,
                    },
                );
                call
            }
            Primitive::PinitMod => self.primitive_runtime("Primitive_module", "init", &values),
            Primitive::PupdateMod => self.primitive_runtime("Primitive_module", "update", &values),
            // P: compile_debugger lowers each argument for effects before debugger.
            Primitive::Pdebugger => {
                for value in values {
                    self.arena.release(value);
                }
                let statement = plain::node(&mut self.arena, View::SDebugger, 0);
                self.primitive_statement(statement, payload.loc);
                plain::node(&mut self.arena, View::JUndefined, 1)
            }
            // P: compile_primitive_js, Praise; conversion never binds a thrown value.
            Primitive::Praise => {
                let value = values
                    .first()
                    .copied()
                    .unwrap_or_else(|| plain::node(&mut self.arena, View::JUndefined, 0));
                let statement = plain::node(&mut self.arena, View::SThrow { value }, 0);
                self.primitive_statement(statement, payload.loc);
                let value = match cx.cont {
                    Cont::Value(_) | Cont::Effect(Tail::No) => {
                        Some(plain::node(&mut self.arena, View::JUndefined, 0))
                    }
                    _ => None,
                };
                return Ok(Probed::Out(Out {
                    stmts: self.statements.since(Span {
                        start: statements.start,
                        len: 0,
                    }),
                    value,
                    finished: Finished::True,
                }));
            }
            Primitive::Pjsx(jsx) => self.compile_jsx(jsx, values),
            Primitive::Pimport(source) => self.compile_import(source),
            Primitive::Pduprecord => self.duplicate_record(values[0]),
            Primitive::PrecordRest(excluded) => self.record_rest(values[0], excluded),
            // P: compile_primitive_js, Pawait. O(1): one owned J node.
            Primitive::Pawait => plain::node(&mut self.arena, View::JAwait { value: values[0] }, 0),
            Primitive::Pstringlength => {
                norm::je2_length(&mut self.arena, values[0], LengthObject::String)
            }
            Primitive::Parraylength => {
                norm::je2_length(&mut self.arena, values[0], LengthObject::Array)
            }
            Primitive::PjsCall(call) => self.compile_js_call(cx, prim.primitive, call, values),
            Primitive::PjsApply => match values.split_first() {
                Some((&callee, args)) => self.call_node(callee, args, Default::default()),
                None => plain::node(&mut self.arena, View::JUndefined, 0),
            },
            Primitive::PjsObjectCreate(specs) => self.compile_js_object_create(cx, specs, values),
            Primitive::PjsFnMethod => {
                let mut values = values.into_iter();
                let value = values.next().unwrap_or_else(|| plain::node(&mut self.arena, View::JUndefined, 0));
                for unused in values { self.arena.release(unused); }
                if let View::JFun { header, .. } = self.arena.view(value) {
                    self.arena.pools.funcs[header.index()].flags |= crate::bir::FuncHeader::METHOD;
                }
                value
            }
            Primitive::PjsObjectGet(name) | Primitive::PjsObjectSet(name) => {
                match (primitive, values.as_slice()) {
                    (Primitive::PjsObjectGet(_), &[receiver]) => self.static_member(receiver, name),
                    (Primitive::PjsObjectSet(_), &[receiver, value]) => {
                        let target = self.static_member(receiver, name);
                        let assign = plain::bin(&mut self.arena, BinOp::Eq, target, value);
                        let unit = plain::node(&mut self.arena, View::JUndefined, 1);
                        plain::seq(&mut self.arena, assign, unit)
                    }
                    _ => {
                        for value in values { self.arena.release(value); }
                        plain::node(&mut self.arena, View::JUndefined, 0)
                    }
                }
            }
            Primitive::Psequand
            | Primitive::Psequor
            => {
                unreachable!("unsupported primitive rejected by dispatch")
            }
            Primitive::PextensionSlotEq => {
                unreachable!("PextensionSlotEq is lowered in raw_lambda::lower")
            }
        };
        // C: primitive_uses_default_compilation / with_source_loc. Preserve
        // a child's existing location when a normalizer returns that child.
        let located = match primitive {
            Primitive::Pdebugger => false,
            Primitive::Pfield(_,crate::lambda::FieldDbgInfo::Module { .. }) =>
                !matches!(self.source.lists.get(prim.operands),[arg] if matches!(self.source.view(*arg),View::Global { .. })),
            _ => true,
        };
        if located && !self.arena.node(value).flags().contains(crate::bir::NodeFlags::JS_LOC_PRESENT)
            && self.locations.as_ref().and_then(|t|t.get(payload.loc)).is_some_and(|loc| !loc.loc_ghost && loc.loc_start.cnum >= 0) {
            let comment = self.arena.cold(value).and_then(|c|c.comment);
            self.arena.set_cold(value,crate::bir::Cold { loc:payload.loc,comment });
            let mut flags = self.arena.node(value).flags(); flags.0 |= crate::bir::NodeFlags::JS_LOC_PRESENT;
            self.arena.nodes[value.index()].set_flags(flags);
        }
        Ok(self.primitive_result(
            cx,
            self.statements.since(Span {
                start: statements.start,
                len: 0,
            }),
            value,
        ))
    }

    /// C: declare_compiled, assign_compiled, return_compiled: conv after sequencing.
    /// O(s) to inspect the s statement slots, then O(1) conversion.
    pub(super) fn primitive_result(&mut self, cx: Cx, statements: Span, value: NodeId) -> Probed {
        if !self.statements.has_statements(statements) {
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lambda::{LamLoc, arena::LamArena, lam_constant::Constant};

    #[test]
    fn interned_payload_is_reusable_after_lowering() {
        let mut a = LamArena::new();
        let primitive = Primitive::PrawJsCode(crate::lambda::lam_primitive::JsRawInfo {
            code: "payload()".into(),
            is_stmt: false,
        });
        let first = a.prim_raw(primitive.clone(), &[], LamLoc::NONE);
        let second = a.prim_raw(primitive, &[], LamLoc::NONE);
        let root = a.prim_raw(Primitive::Pmakearray, &[first, second], LamLoc::NONE);
        super::super::oracle_tests::compare(a, root);
    }

    #[test]
    fn primitive_resume_is_two_handles() {
        assert_eq!(std::mem::size_of::<Prim>(), 8);
        assert_eq!(std::mem::size_of::<ModuleConstants>(), 16);
        assert_eq!(std::mem::size_of::<crate::bir::ListId>(), 4);
    }

    fn named_case(primitive: &Primitive, check: impl FnOnce()) {
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(check));
        assert!(result.is_ok(), "primitive {primitive:?} failed its oracle case");
    }

    #[test]
    fn option_arms_match_legacy() {
        use Primitive::*;
        for primitive in [
            Psome,
            PsomeNotNest,
            PvalFromOption,
            PvalFromOptionNotNest,
            PisNotNone,
            PnullToOpt,
            PnullUndefinedToOpt,
            PisNull,
            PisUndefined,
            PisNullUndefined,
        ] {
            for shape in 0..9 {
                let mut a = LamArena::new();
                let arg = match shape {
                    0 => a.const_(Constant::JsNull),
                    1 => a.const_(Constant::JsUndefined { is_unit: false }),
                    2 => a.const_(Constant::JsTrue),
                    3 => a.const_(Constant::String("text".into())),
                    4 => a.const_(Constant::Int {
                        i: 3,
                        comment: None,
                    }),
                    5 => a.const_(Constant::Block {
                        tag_info: Box::new(crate::lambda::TagInfo::Tuple),
                        elements: vec![],
                    }),
                    _ => a.var(Ident::new("value", 10, crate::ident::IdentFlags::NONE)),
                };
                let arg = if shape >= 7 {
                    a.prim_raw(PinitMod, &[arg], LamLoc::NONE)
                } else {
                    arg
                };
                let arg = if shape == 8 {
                    a.prim_raw(Psome, &[arg], LamLoc::NONE)
                } else {
                    arg
                };
                let root = a.prim_raw(primitive.clone(), &[arg], LamLoc::NONE);
                named_case(&primitive, || super::super::oracle_tests::compare(a, root));
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
                let divisors = if matches!(primitive, Plsrint) {
                    [0, 2, 31]
                } else {
                    [0, 2, -1]
                };
                for divisor in divisors {
                    for checks in [false, true] {
                        let mut a = LamArena::new();
                        let args: Vec<_> = (0..arity)
                            .map(|i| {
                                if literal {
                                    a.const_(Constant::Int {
                                        i: if i == 0 { i32::MIN } else { divisor },
                                        comment: None,
                                    })
                                } else {
                                    a.var(Ident::new(
                                        format!("arg{i}"),
                                        10 + i,
                                        crate::ident::IdentFlags::NONE,
                                    ))
                                }
                            })
                            .collect();
                        let root = a.prim_raw(primitive.clone(), &args, LamLoc::NONE);
                        named_case(&primitive, || super::super::oracle_tests::compare_with_checks(a, root, checks));
                    }
                }
            }
        }
    }

    #[test]
    fn simple_primitive_arms_match_legacy() {
        use Primitive::*;
        for (primitive, arity) in [
            (PfnArity, 1),
            (Pstringadd, 2),
            (Pnot, 1),
            (Pidentity, 1),
            (Pfloatofint, 1),
            (Pignore, 1),
            (Ptypeof, 1),
            (PcreateExtension("Example".into()), 0),
            (PinitMod, 2),
            (PupdateMod, 3),
            (Praise, 1),
            (Pdebugger, 1),
            (
                PrawJsCode(crate::lambda::lam_primitive::JsRawInfo {
                    code: "  value()  ".into(),
                    is_stmt: false,
                }),
                0,
            ),
        ] {
            for literal in [false, true] {
                let mut a = LamArena::new();
                let args: Vec<_> = (0..arity)
                    .map(|i| {
                        if literal {
                            a.const_(Constant::String("text".into()))
                        } else {
                            a.var(Ident::new(
                                format!("value{i}"),
                                10 + i,
                                crate::ident::IdentFlags::NONE,
                            ))
                        }
                    })
                    .collect();
                let root = a.prim_raw(primitive.clone(), &args, LamLoc::NONE);
                named_case(&primitive, || super::super::oracle_tests::compare(a, root));
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
                named_case(&primitive, || super::super::oracle_tests::compare(a, root));
            }
        }
    }
}

#[cfg(test)]
mod await_tests {
    use super::*;
    use crate::lambda::{LamLoc, arena::LamArena};

    #[test]
    fn ten_thousand_awaits_are_linear() {
        let mut a = LamArena::new();
        let mut root = a.var(Ident::new("promise", 10, crate::ident::IdentFlags::NONE));
        for _ in 0..10_000 { root = a.prim_raw(Primitive::Pawait, &[root], LamLoc::NONE); }
        let input = crate::bir::bridge::import_lambda(&a, root).unwrap();
        let root = input.root;
        let mut state = State::new(input);
        let out = state.probe(Cx::value(), root).unwrap();
        assert_eq!(state.source_steps, 10_001);
        assert_eq!(state.sequence_steps, 10_000);
        assert_eq!(state.primitive_steps, 20_000);
        let lowered = state.complete(Cx::value(), out);
        lowered.program.arena.validate(Some(lowered.program.root)).unwrap();
    }

    #[test]
    fn await_all_continuations_and_conditional_match_legacy() {
        for conditional in [false, true] {
            let mut a = LamArena::new();
            let value = a.var(Ident::new("promise", 10, crate::ident::IdentFlags::NONE));
            let awaited = a.prim_raw(Primitive::Pawait, &[value], LamLoc::NONE);
            let root = if conditional {
                let test = a.var(Ident::new("test", 11, crate::ident::IdentFlags::NONE));
                let other = a.var(Ident::new("other", 12, crate::ident::IdentFlags::NONE));
                a.if_(test, awaited, other)
            } else { awaited };
            super::super::oracle_tests::compare(a, root);
        }
    }
}

#[cfg(test)]
mod inventory_tests {
    use super::*;
    use Primitive::*;
    use crate::lambda::{LamLoc, arena::LamArena};

    // One table generates both the individually named oracle tests and the
    // exhaustive inventory. Adding a Primitive variant cannot compile until
    // it has a test row or an explicit unsupported dispatch classification.
    macro_rules! primitive_cases {
        (cases { $($pattern:pat => $name:ident($value:expr, $arity:expr);)* }
         unsupported { $($unsupported:pat),* $(,)? }) => {
            fn inventory(primitive: &Primitive) -> Option<&'static str> {
                match primitive {
                    $($pattern => Some(stringify!($name)),)*
                    $($unsupported => None,)*
                }
            }
            $(
                #[test]
                fn $name() {
                    let primitive = $value;
                    assert_eq!(inventory(&primitive), Some(stringify!($name)));
                    let mut arena = LamArena::new();
                    let args: Vec<_> = (0..$arity).map(|i| {
                        arena.var(Ident::new(format!("arg{i}"), 10 + i, crate::ident::IdentFlags::NONE))
                    }).collect();
                    let root = arena.prim_raw(primitive, &args, LamLoc::NONE);
                    super::super::oracle_tests::compare(arena, root);
                }
            )*
        };
    }

    fn minimal_jsx() -> crate::lambda::lam_primitive::JsxElement {
        use crate::lambda::lam_primitive::{JsxElement, ExternalDecl, DeclKind};
        JsxElement {
            jsx_name: "jsx".into(),
            jsx_ffi: ExternalDecl {
                kind: DeclKind::DeclVal { name: "jsx".into() },
                module_: None,
                scopes: vec!["React".into()],
                variadic: false,
                effective_arity: 3,
            },
            jsx_multi: false,
            jsx_fragment: false,
            jsx_spread: false,
            jsx_props: vec![],
            jsx_children: None,
            jsx_key: false,
        }
    }

    fn minimal_import() -> crate::lambda::lam_primitive::ImportSource {
        use crate::lambda::lam_primitive::{ImportSource, ExternalModuleName, ModuleBindName};
        ImportSource::ImportExternal {
            module_: ExternalModuleName {
                bundle: "example".into(),
                module_bind_name: ModuleBindName::PhintNothing,
                import_attributes: None,
            },
            path: vec![],
        }
    }

    primitive_cases! { cases {
        PjsCall(..) => pjs_call(PjsCall(Box::new(crate::lambda::lam_primitive::JsCall {
            prim_name: "call".into(),
            arg_types: vec![],
            ffi: crate::lambda::lam_primitive::ExternalDecl {
                kind: crate::lambda::lam_primitive::DeclKind::DeclVal { name: "call".into() },
                module_: None,
                scopes: vec![],
                variadic: false,
                effective_arity: 0,
            },
        })), 0);
        PjsObjectCreate(..) => pjs_object_create(PjsObjectCreate(vec![]), 0);
        PjsApply => pjs_apply(PjsApply, 2);
        PjsObjectGet(..) => pjs_object_get(PjsObjectGet("field".into()), 1);
        PjsObjectSet(..) => pjs_object_set(PjsObjectSet("field".into()), 2);
        PjsFnMethod => pjs_fn_method(PjsFnMethod, 1);
        Pmakeblock(..) => pmakeblock(Pmakeblock(crate::lambda::TagInfo::Tuple, crate::lambda::lam_primitive::Mutable::Immutable), 2);
        Pfield(..) => pfield(Pfield(0, crate::lambda::FieldDbgInfo::Tuple), 1);
        Psetfield(..) => psetfield(Psetfield(0, crate::lambda::SetFieldDbgInfo::RecordSet(crate::name::Name::new("field"))), 2);
        Pduprecord => pduprecord(Pduprecord, 1);
        PrecordRest(..) => precord_rest(PrecordRest(vec!["field".into()]), 1);
        PtaggedTemplate(..) => ptagged_template(PtaggedTemplate(vec!["segment".into()]), 1);
        Ptemplate(..) => ptemplate(Ptemplate(vec![crate::string_literal::template_from_semantic("segment")]), 0);
        Pjsx(..) => pjsx(Pjsx(Box::new(minimal_jsx())), 1);
        Praise => praise(Praise, 1);
        Pobjcomp(..) => pobjcomp(Pobjcomp(crate::lambda::Comparison::Eq), 2);
        Pobjorder => pobjorder(Pobjorder, 2);
        Pobjmin => pobjmin(Pobjmin, 2);
        Pobjmax => pobjmax(Pobjmax, 2);
        Pobjtag => pobjtag(Pobjtag, 1);
        Pobjsize => pobjsize(Pobjsize, 1);
        Psequand => psequand(Psequand, 2);
        Psequor => psequor(Psequor, 2);
        Pnot => pnot(Pnot, 1);
        Pboolcomp(..) => pboolcomp(Pboolcomp(crate::lambda::Comparison::Eq), 2);
        Pboolorder => pboolorder(Pboolorder, 2);
        Pboolmin => pboolmin(Pboolmin, 2);
        Pboolmax => pboolmax(Pboolmax, 2);
        Pnegint => pnegint(Pnegint, 1);
        Paddint => paddint(Paddint, 2);
        Psubint => psubint(Psubint, 2);
        Pmulint => pmulint(Pmulint, 2);
        Pdivint => pdivint(Pdivint, 2);
        Pmodint => pmodint(Pmodint, 2);
        Ppowint => ppowint(Ppowint, 2);
        Pandint => pandint(Pandint, 2);
        Porint => porint(Porint, 2);
        Pxorint => pxorint(Pxorint, 2);
        Pnotint => pnotint(Pnotint, 1);
        Plslint => plslint(Plslint, 2);
        Plsrint => plsrint(Plsrint, 2);
        Pasrint => pasrint(Pasrint, 2);
        Pintcomp(..) => pintcomp(Pintcomp(crate::lambda::Comparison::Eq), 2);
        Pintorder => pintorder(Pintorder, 2);
        Pintmin => pintmin(Pintmin, 2);
        Pintmax => pintmax(Pintmax, 2);
        Pintoffloat => pintoffloat(Pintoffloat, 1);
        Pfloatofint => pfloatofint(Pfloatofint, 1);
        Pnegfloat => pnegfloat(Pnegfloat, 1);
        Paddfloat => paddfloat(Paddfloat, 2);
        Psubfloat => psubfloat(Psubfloat, 2);
        Pmulfloat => pmulfloat(Pmulfloat, 2);
        Pdivfloat => pdivfloat(Pdivfloat, 2);
        Pmodfloat => pmodfloat(Pmodfloat, 2);
        Ppowfloat => ppowfloat(Ppowfloat, 2);
        Pfloatcomp(..) => pfloatcomp(Pfloatcomp(crate::lambda::Comparison::Eq), 2);
        Pfloatorder => pfloatorder(Pfloatorder, 2);
        Pfloatmin => pfloatmin(Pfloatmin, 2);
        Pfloatmax => pfloatmax(Pfloatmax, 2);
        Pnegbigint => pnegbigint(Pnegbigint, 1);
        Paddbigint => paddbigint(Paddbigint, 2);
        Psubbigint => psubbigint(Psubbigint, 2);
        Pmulbigint => pmulbigint(Pmulbigint, 2);
        Pdivbigint => pdivbigint(Pdivbigint, 2);
        Pmodbigint => pmodbigint(Pmodbigint, 2);
        Ppowbigint => ppowbigint(Ppowbigint, 2);
        Pandbigint => pandbigint(Pandbigint, 2);
        Porbigint => porbigint(Porbigint, 2);
        Pxorbigint => pxorbigint(Pxorbigint, 2);
        Pnotbigint => pnotbigint(Pnotbigint, 1);
        Plslbigint => plslbigint(Plslbigint, 2);
        Pasrbigint => pasrbigint(Pasrbigint, 2);
        Pbigintcomp(..) => pbigintcomp(Pbigintcomp(crate::lambda::Comparison::Eq), 2);
        Pbigintorder => pbigintorder(Pbigintorder, 2);
        Pbigintmin => pbigintmin(Pbigintmin, 2);
        Pbigintmax => pbigintmax(Pbigintmax, 2);
        Pstringlength => pstringlength(Pstringlength, 1);
        Pstringrefu => pstringrefu(Pstringrefu, 2);
        Pstringrefs => pstringrefs(Pstringrefs, 2);
        Pstringadd => pstringadd(Pstringadd, 2);
        Pstringcomp(..) => pstringcomp(Pstringcomp(crate::lambda::Comparison::Eq), 2);
        Pstringorder => pstringorder(Pstringorder, 2);
        Pstringmin => pstringmin(Pstringmin, 2);
        Pstringmax => pstringmax(Pstringmax, 2);
        Pmakearray => pmakearray(Pmakearray, 2);
        Parraylength => parraylength(Parraylength, 1);
        Parrayrefu => parrayrefu(Parrayrefu, 2);
        Parraysetu => parraysetu(Parraysetu, 3);
        Parrayrefs => parrayrefs(Parrayrefs, 2);
        Pmakelist => pmakelist(Pmakelist, 2);
        Pmakedict => pmakedict(Pmakedict, 1);
        PdictSpread => pdict_spread(PdictSpread, 1);
        ParraySpread => parray_spread(ParraySpread, 1);
        PlistSpread => plist_spread(PlistSpread, 1);
        PdictHas => pdict_has(PdictHas, 2);
        Pawait => pawait(Pawait, 1);
        Pidentity => pidentity(Pidentity, 1);
        Pignore => pignore(Pignore, 1);
        PisPolyVarBlock => pis_poly_var_block(PisPolyVarBlock, 1);
        Pjscomp(..) => pjscomp(Pjscomp(crate::lambda::Comparison::Eq), 2);
        Pdebugger => pdebugger(Pdebugger, 1);
        PinitMod => pinit_mod(PinitMod, 2);
        PupdateMod => pupdate_mod(PupdateMod, 3);
        PrawJsCode(..) => praw_js_code(PrawJsCode(crate::lambda::lam_primitive::JsRawInfo { code: "value()".into(), is_stmt: false }), 0);
        PnullToOpt => pnull_to_opt(PnullToOpt, 1);
        PnullUndefinedToOpt => pnull_undefined_to_opt(PnullUndefinedToOpt, 1);
        PisNull => pis_null(PisNull, 1);
        PisUndefined => pis_undefined(PisUndefined, 1);
        PisNullUndefined => pis_null_undefined(PisNullUndefined, 1);
        Pimport(..) => pimport(Pimport(Box::new(minimal_import())), 0);
        Ptypeof => ptypeof(Ptypeof, 1);
        PfnArity => pfn_arity(PfnArity, 1);
        PcreateExtension(..) => pcreate_extension(PcreateExtension("Example".into()), 0);
        PisNotNone => pis_not_none(PisNotNone, 1);
        PvalFromOption => pval_from_option(PvalFromOption, 1);
        PvalFromOptionNotNest => pval_from_option_not_nest(PvalFromOptionNotNest, 1);
        Psome => psome(Psome, 1);
        PsomeNotNest => psome_not_nest(PsomeNotNest, 1);
        Phash => phash(Phash, 1);
        PhashMixstring => phash_mixstring(PhashMixstring, 2);
        PhashMixint => phash_mixint(PhashMixint, 2);
        PhashFinalmix => phash_finalmix(PhashFinalmix, 1);
    }
        // Extension-slot equality is lowered before Bir import.
        unsupported { PextensionSlotEq }
    }
}
