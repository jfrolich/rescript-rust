//! P: compile_primitive: lower arguments once, sequence, then convert the result.
use super::*;
use crate::bir::PrimId;
use crate::emit::row::Kind;
use super::js::Mark;
use crate::js_ir::BinOp;
use crate::js_ir::op::LengthObject;
use crate::lambda::lam_primitive::Primitive;

pub(super) struct Prim {
    pub primitive: PrimId,
    pub operands: crate::bir::ListId,
}

impl<B: super::js_stmt::JsStmt> State<'_, B> {
    /// O(1): inspect a numeric leaf and its interned constant.
    pub(super) fn primitive_int(&self, node: NodeId) -> Option<i32> {
        self.js.int(&self.arena, B::at(node))
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
        B::node(self.runtime(name, member, args))
    }

    /// `primitive_runtime` on a handle: the operands of `args` pushed in
    /// order, then [`Self::runtime_call`]. O(r + a + text bytes), as
    /// `primitive_runtime`.
    fn runtime(&mut self, name: &str, member: &str, args: &[NodeId]) -> B::E {
        let mark = self.push_values(args);
        self.runtime_call(name, member, mark)
    }

    /// C: runtime_call_expr: `name.member(...)` over the operands pushed
    /// since `mark`. O(r + a + text bytes), with r runtime modules (bounded
    /// by the primitive runtime inventory) and a operands since `mark`.
    fn runtime_call(&mut self, name: &str, member: &str, mark: Mark) -> B::E {
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
        let callee = self.js.qualified(&mut self.arena, module, member);
        let info = self
            .arena
            .js_info(crate::bir::JsPayload::Call(crate::js_ir::CallInfo {
                kind: crate::js_ir::CallKind::BuiltinRuntime,
                arity: crate::js_ir::CallArity::Full,
                ..Default::default()
            }));
        self.js.call(&mut self.arena, callee, mark, info)
    }

    /// The nodes of `values` pushed as operands, in order; returns the mark
    /// of the first. O(values): one move each, no allocation in a warm unit.
    fn push_values(&mut self, values: &[NodeId]) -> Mark {
        let mark = self.js.mark();
        for &value in values {
            self.js.push(B::from_node(value));
        }
        mark
    }

    /// `values[0] op values[1]` by J-E4. O(1) beside the cost of the J-E4
    /// row; no operand is walked here.
    fn bin_of(&mut self, op: BinOp, values: &[NodeId]) -> B::E {
        self.js.bin(&mut self.arena, op, B::from_node(values[0]), B::from_node(values[1]))
    }

    /// The first value, or `undefined` when there is none. O(1).
    fn first_value(&mut self, values: &[NodeId]) -> B::E {
        match values.first() {
            Some(&value) => B::from_node(value),
            None => self.js.undefined(&mut self.arena, false),
        }
    }

    /// P: compile_primitive_js / compile_debugger source locations on statements.
    /// O(1): one location lookup and one statement push.
    fn primitive_statement(&mut self, mut statement: B::S, loc: crate::lambda::LamLoc) {
        if self
            .locations
            .and_then(|locations| locations.get(loc))
            .is_some_and(|loc| !loc.loc_ghost && loc.loc_start.cnum >= 0)
        {
            self.js.locate_stmt(&mut self.arena, &mut statement, loc);
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
        let mut outputs = std::mem::take(&mut self.argument_outputs);
        outputs.extend(children.map(|child| match child {
            Probed::Out(out) => out,
            Probed::Free(_) => unreachable!("argument realized before its next sibling"),
        }));
        match &payload.primitive {
            Primitive::PjsCall(call) => self.hold_external_args(cx, &call.arg_types, &mut outputs),
            Primitive::PjsObjectCreate(specs) => self.hold_external_obj_args(cx, specs, &mut outputs),
            Primitive::PjsObjectGet(_) if outputs.len() == 1 => {
                let arg = outputs.pop().unwrap();
                outputs.push(self.hold_external_receiver(cx, arg));
            }
            _ => {}
        }
        let mut values = std::mem::take(&mut self.argument_values);
        let statements = self.sequence_arguments(false, &outputs, &mut values);
        outputs.clear();
        self.argument_outputs = outputs;
        let result = self.finish_primitive_values(cx, prim, payload, statements, &mut values);
        values.clear();
        self.argument_values = values;
        result
    }

    /// O(arguments + emitted metadata + J-rule work): consume sequenced roots
    /// from the caller's reusable buffer, without taking its backing allocation.
    fn finish_primitive_values(
        &mut self, cx: Cx, prim: Prim, payload: &crate::bir::PrimPayload,
        statements: Span, values: &mut Vec<NodeId>,
    ) -> Result<Probed, Unsupported> {
        self.primitive_steps += values.len() + 1;
        let primitive = &payload.primitive;
        let mut value = match primitive {
            // P: compile_primitive_js, dictionaries: extract only literal-key
            // tuple entries, exactly as the legacy filter_map does.
            Primitive::Pmakedict => {
                let mut keys = std::mem::take(&mut self.object_scratch.keys);
                let mut kept = std::mem::take(&mut self.object_scratch.values);
                debug_assert!(keys.is_empty() && kept.is_empty());
                let array = match values.as_slice() {
                    &[array] if self.js.kind(&self.arena, B::at(array)) == Kind::Array => Some(array),
                    _ => None,
                };
                let result = if let Some(array) = array {
                    let count = self.js.unpack_rev(&mut self.arena, B::from_node(array));
                    for _ in 0..count {
                        self.primitive_steps += 1;
                        let item = self.js.pop();
                        let r = B::of(&item);
                        let key = if self.js.kind(&self.arena, r) == Kind::BlockLit
                            && self.js.arity(&self.arena, r) == 2
                        {
                            self.js.str_of(&self.arena, self.js.operand(&self.arena, r, 0))
                        } else {
                            None
                        };
                        match key {
                            Some(text) => {
                                keys.push(crate::bir::PropertyKey::Literal(text));
                                kept.push(B::node(self.js.keep_operand(&mut self.arena, item, 1)));
                            }
                            None => self.js.release(&mut self.arena, item),
                        }
                    }
                    let info = self.arena.object_info(&keys);
                    let mark = self.push_values(&kept);
                    self.js.object(&mut self.arena, mark, info)
                } else {
                    for value in values.drain(..) {
                        self.js.release(&mut self.arena, B::from_node(value));
                    }
                    self.js.undefined(&mut self.arena, false)
                };
                keys.clear(); kept.clear();
                self.object_scratch.keys = keys;
                self.object_scratch.values = kept;
                result
            }
            Primitive::PdictSpread => {
                let mut keys = std::mem::take(&mut self.object_scratch.keys);
                let mut kept = std::mem::take(&mut self.object_scratch.values);
                debug_assert!(keys.is_empty() && kept.is_empty());
                for arg in values.drain(..) {
                    self.primitive_steps += 1;
                    let r = B::at(arg);
                    let literal = self.js.kind(&self.arena, r) == Kind::Object && {
                        let info = self.js.info_of(&self.arena, r).expect("an object's keys");
                        let crate::bir::JsPayload::Object(props) = self.arena.javascript(info)
                        else {
                            unreachable!()
                        };
                        let props = self.arena.property_keys(*props);
                        let literal = props.iter().all(|p| {
                            matches!(
                                p,
                                crate::bir::PropertyKey::Literal(_)
                                    | crate::bir::PropertyKey::Symbol
                            )
                        });
                        if literal {
                            keys.extend_from_slice(props);
                        }
                        literal
                    };
                    if literal {
                        let count = self.js.unpack_rev(&mut self.arena, B::from_node(arg));
                        for _ in 0..count {
                            kept.push(B::node(self.js.pop()));
                        }
                    } else {
                        keys.push(crate::bir::PropertyKey::Spread);
                        kept.push(arg);
                    }
                }
                let info = self.arena.object_info(&keys);
                let mark = self.push_values(&kept);
                let result = self.js.object(&mut self.arena, mark, info);
                keys.clear(); kept.clear();
                self.object_scratch.keys = keys;
                self.object_scratch.values = kept;
                result
            }
            Primitive::PdictHas => {
                if let &[object, property] = values.as_slice() {
                    self.js.in_(&mut self.arena, B::from_node(property), B::from_node(object))
                } else {
                    for value in values.drain(..) {
                        self.js.release(&mut self.arena, B::from_node(value));
                    }
                    self.js.undefined(&mut self.arena, false)
                }
            }
            Primitive::ParraySpread => self.runtime("Primitive_array", "spread", values),
            Primitive::PlistSpread => self.runtime("Primitive_list", "spread", values),
            // P: compile_primitive_js, hashing runtime entry points.
            Primitive::Phash => self.runtime("Primitive_hash", "hash", values),
            Primitive::PhashMixint => self.runtime("Primitive_hash", "hash_mix_int", values),
            Primitive::PhashMixstring => {
                self.runtime("Primitive_hash", "hash_mix_string", values)
            }
            Primitive::PhashFinalmix => self.runtime("Primitive_hash", "hash_final_mix", values),
            // P: compile_primitive_js, blocks and fields (K: compile_field_access).
            Primitive::Pmakeblock(tag, mutable) => {
                let info = self.arena.block_info(tag);
                let mark = self.push_values(values);
                let mutable = matches!(mutable, crate::lambda::lam_primitive::Mutable::Mutable);
                self.js.block(&mut self.arena, mark, info, u8::from(mutable))
            }
            Primitive::Pmakelist => {
                let info = *self.list_block_info.get_or_insert_with(|| self.arena.js_info(crate::bir::JsPayload::Block(
                    crate::lambda::TagInfo::constructor("::", 1),
                )));
                let mark = self.push_values(values);
                self.js.block(&mut self.arena, mark, info, 1)
            }
            Primitive::Pmakearray => {
                let mark = self.push_values(values);
                self.js.array(&mut self.arena, mark, 1)
            }
            Primitive::Pfield(idx, info) => self.primitive_field(*idx, info, B::from_node(values[0])),
            Primitive::Psetfield(idx, info) => {
                self.primitive_set_field(*idx, info.name(), B::from_node(values[0]), B::from_node(values[1]))
            }
            Primitive::Pobjtag => {
                let property = self.arena.intern_text("TAG");
                self.js.dot(
                    &mut self.arena,
                    B::from_node(values[0]),
                    property,
                    crate::js_ir::arena::FieldPos::NONE,
                    true,
                )
            }
            Primitive::Pobjsize => {
                let length = self.js.length(&mut self.arena, B::from_node(values[0]), LengthObject::CamlBlock);
                self.js.to_int32(&mut self.arena, length)
            }
            Primitive::PisPolyVarBlock => {
                // P:642 / E:653 folds typeof before comparing the type name.
                let typeof_ = self.js.typeof_(&mut self.arena, B::from_node(values[0]));
                let object = self.js.string(&mut self.arena, "object");
                self.js.bin(&mut self.arena, BinOp::EqEqEq, typeof_, object)
            }
            // P: compile_primitive_js, indexing. Both string forms are checked.
            Primitive::Pstringrefs | Primitive::Pstringrefu => {
                self.runtime("Primitive_string", "getChar", values)
            }
            Primitive::Parrayrefs => self.runtime("Primitive_array", "get", values),
            Primitive::Parrayrefu => {
                if let &[object, index] = values.as_slice() {
                    self.js.index(&mut self.arena, B::from_node(object), B::from_node(index))
                } else {
                    for v in values.drain(..) {
                        self.js.release(&mut self.arena, B::from_node(v));
                    }
                    self.js.undefined(&mut self.arena, false)
                }
            }
            Primitive::Parraysetu => {
                if let &[object, index, value] = values.as_slice() {
                    let target = self.js.index(&mut self.arena, B::from_node(object), B::from_node(index));
                    let assignment = self.js.bin(&mut self.arena, BinOp::Eq, target, B::from_node(value));
                    let unit = self.js.undefined(&mut self.arena, false);
                    self.js.seq(&mut self.arena, assignment, unit)
                } else {
                    for v in values.drain(..) {
                        self.js.release(&mut self.arena, B::from_node(v));
                    }
                    self.js.undefined(&mut self.arena, false)
                }
            }
            // P: compile_primitive_js, template arms; J-M12 preserves raw spelling.
            Primitive::Ptemplate(segments) => {
                let mark = self.push_values(values);
                self.js.template(&mut self.arena, segments, mark)
            }
            Primitive::PtaggedTemplate(segments) => {
                let start = self.arena.pools.template_parts.len() as u32;
                for s in segments {
                    let raw = self.arena.intern_text(s);
                    self.arena.pools.template_parts.push(crate::bir::TemplatePart { raw, cooked: None });
                }
                let info = self.arena.js_info(crate::bir::JsPayload::Tagged(crate::bir::TemplateSpan { start, len: segments.len() as u32 }));
                let tag = B::from_node(values[0]);
                let mark = self.push_values(&values[1..]);
                self.js.tagged(&mut self.arena, tag, mark, info)
            }
            // X: some_expr / optional_block. Identity is a shape test, not purity.
            Primitive::Psome | Primitive::PsomeNotNest => {
                let value = B::at(values[0]);
                let identity = matches!(primitive, Primitive::PsomeNotNest)
                    || match self.js.kind(&self.arena, value) {
                        Kind::Null
                        | Kind::Object
                        | Kind::Number
                        | Kind::BlockLit
                        | Kind::Array
                        | Kind::Str => true,
                        Kind::Template => self.js.aux(&self.arena, value) == 1,
                        _ => false,
                    };
                self.js.optional(&mut self.arena, B::from_node(values[0]), identity)
            }
            // X: val_from_option_expr.
            Primitive::PvalFromOption => {
                if self.js.kind(&self.arena, B::at(values[0])) == Kind::Optional {
                    self.js.keep_operand(&mut self.arena, B::from_node(values[0]), 0)
                } else {
                    self.runtime("Primitive_option", "valFromOption", values)
                }
            }
            Primitive::PvalFromOptionNotNest => B::from_node(values[0]),
            // X: is_not_none_expr, intentionally drops even effectful Some payloads.
            Primitive::PisNotNone => match self.js.kind(&self.arena, B::at(values[0])) {
                Kind::Undefined => {
                    self.js.release(&mut self.arena, B::from_node(values[0]));
                    self.js.boolean(&mut self.arena, false)
                }
                Kind::Optional => {
                    self.js.release(&mut self.arena, B::from_node(values[0]));
                    self.js.boolean(&mut self.arena, true)
                }
                _ => {
                    let undefined = self.js.undefined(&mut self.arena, false);
                    self.js.bin(&mut self.arena, BinOp::NotEqEq, B::from_node(values[0]), undefined)
                }
            },
            // X: is_null_expr / is_undefined_expr / is_null_or_undefined_expr.
            Primitive::PisNull | Primitive::PisUndefined => {
                let nullish = if matches!(primitive, Primitive::PisNull) {
                    self.js.null(&mut self.arena)
                } else {
                    self.js.undefined(&mut self.arena, false)
                };
                self.js.bin(&mut self.arena, BinOp::EqEqEq, B::from_node(values[0]), nullish)
            }
            Primitive::PisNullUndefined => {
                self.js.is_nullish(&mut self.arena, B::from_node(values[0]))
            }
            // X: null_to_opt_expr / null_undefined_to_opt_expr. Only leaf operands
            // are duplicated, so this costs constant work per primitive.
            Primitive::PnullToOpt | Primitive::PnullUndefinedToOpt => {
                let nullable = matches!(primitive, Primitive::PnullUndefinedToOpt);
                let value = B::at(values[0]);
                if matches!(
                    self.js.kind(&self.arena, value),
                    Kind::Var | Kind::Undefined | Kind::Null
                ) {
                    let copy = self.js.copy_leaf(&mut self.arena, value);
                    let test = if nullable {
                        self.js.is_nullish(&mut self.arena, copy)
                    } else {
                        let null = self.js.null(&mut self.arena);
                        self.js.bin(&mut self.arena, BinOp::EqEqEq, copy, null)
                    };
                    let undefined = self.js.undefined(&mut self.arena, false);
                    let some = self.js.optional(&mut self.arena, B::from_node(values[0]), false);
                    self.js.cond(&mut self.arena, test, undefined, some)
                } else {
                    self.runtime(
                        "Primitive_option",
                        if nullable { "fromNullable" } else { "fromNull" },
                        values,
                    )
                }
            }
            // P: compile_primitive_js, comparison arms.
            Primitive::Pintcomp(cmp) => self.primitive_int_comparison(*cmp, B::from_node(values[0]), B::from_node(values[1])),
            Primitive::Pboolcomp(cmp) => self.primitive_bool_comparison(*cmp, B::from_node(values[0]), B::from_node(values[1])),
            Primitive::Pstringcomp(cmp) => {
                self.primitive_literal_comparison(*cmp, B::from_node(values[0]), B::from_node(values[1]), false)
            }
            Primitive::Pbigintcomp(cmp) => {
                self.primitive_literal_comparison(*cmp, B::from_node(values[0]), B::from_node(values[1]), true)
            }
            Primitive::Pobjcomp(cmp) => self.primitive_object_comparison(*cmp, B::from_node(values[0]), B::from_node(values[1])),
            Primitive::Pfloatcomp(
                cmp @ (crate::lambda::lam_compat::Comparison::Eq
                | crate::lambda::lam_compat::Comparison::Neq),
            ) => self.primitive_int_comparison(*cmp, B::from_node(values[0]), B::from_node(values[1])),
            Primitive::Pfloatcomp(cmp) | Primitive::Pjscomp(cmp) => self.js.bin(
                &mut self.arena,
                super::prim_cmp::comparison_op(*cmp, true),
                B::from_node(values[0]),
                B::from_node(values[1]),
            ),
            Primitive::Pobjorder => self.runtime("Primitive_object", "compare", values),
            Primitive::Pobjmin => self.primitive_min_max("object", false, B::from_node(values[0]), B::from_node(values[1])),
            Primitive::Pobjmax => self.primitive_min_max("object", true, B::from_node(values[0]), B::from_node(values[1])),
            Primitive::Pboolorder => {
                if let (Some(l), Some(r)) = (
                    self.primitive_bool(values[0]),
                    self.primitive_bool(values[1]),
                ) {
                    self.js.release(&mut self.arena, B::from_node(values[0]));
                    self.js.release(&mut self.arena, B::from_node(values[1]));
                    self.js.int_literal(&mut self.arena, l.cmp(&r) as i32)
                } else {
                    self.runtime("Primitive_bool", "compare", values)
                }
            }
            Primitive::Pboolmin => self.primitive_min_max("bool", false, B::from_node(values[0]), B::from_node(values[1])),
            Primitive::Pboolmax => self.primitive_min_max("bool", true, B::from_node(values[0]), B::from_node(values[1])),
            Primitive::Pintorder => self.runtime("Primitive_int", "compare", values),
            Primitive::Pintmin => self.primitive_min_max("int", false, B::from_node(values[0]), B::from_node(values[1])),
            Primitive::Pintmax => self.primitive_min_max("int", true, B::from_node(values[0]), B::from_node(values[1])),
            Primitive::Pfloatorder => self.runtime("Primitive_float", "compare", values),
            Primitive::Pfloatmin => self.primitive_min_max("float", false, B::from_node(values[0]), B::from_node(values[1])),
            Primitive::Pfloatmax => self.primitive_min_max("float", true, B::from_node(values[0]), B::from_node(values[1])),
            Primitive::Pbigintorder => self.runtime("Primitive_bigint", "compare", values),
            Primitive::Pbigintmin => self.primitive_min_max("bigint", false, B::from_node(values[0]), B::from_node(values[1])),
            Primitive::Pbigintmax => self.primitive_min_max("bigint", true, B::from_node(values[0]), B::from_node(values[1])),
            Primitive::Pstringorder => self.runtime("Primitive_string", "compare", values),
            Primitive::Pstringmin => self.primitive_min_max("string", false, B::from_node(values[0]), B::from_node(values[1])),
            Primitive::Pstringmax => self.primitive_min_max("string", true, B::from_node(values[0]), B::from_node(values[1])),
            // P: compile_primitive_js, arithmetic arms; J-M3–M13 own the folds.
            Primitive::Paddint => {
                self.js.int_add(&mut self.arena, false, B::from_node(values[0]), B::from_node(values[1]))
            }
            Primitive::Psubint => {
                self.js.int_add(&mut self.arena, true, B::from_node(values[0]), B::from_node(values[1]))
            }
            Primitive::Pmulint => self.js.int_mul(&mut self.arena, B::from_node(values[0]), B::from_node(values[1])),
            Primitive::Pdivint => self.js.int_div(
                &mut self.arena,
                self.check_div_by_zero,
                B::from_node(values[0]),
                B::from_node(values[1]),
            ),
            Primitive::Pmodint => self.js.int_mod(
                &mut self.arena,
                self.check_div_by_zero,
                B::from_node(values[0]),
                B::from_node(values[1]),
            ),
            Primitive::Ppowint => self.js.int_pow(&mut self.arena, B::from_node(values[0]), B::from_node(values[1])),
            Primitive::Pandint => self.js.int_and(&mut self.arena, B::from_node(values[0]), B::from_node(values[1])),
            Primitive::Porint => self.js.int_or(&mut self.arena, B::from_node(values[0]), B::from_node(values[1])),
            Primitive::Pxorint => self.js.int_xor(&mut self.arena, B::from_node(values[0]), B::from_node(values[1])),
            Primitive::Plslint => self.js.int_lsl(&mut self.arena, B::from_node(values[0]), B::from_node(values[1])),
            Primitive::Paddfloat | Primitive::Paddbigint => self.bin_of(BinOp::Plus, values),
            Primitive::Psubfloat | Primitive::Psubbigint => self.bin_of(BinOp::Minus, values),
            Primitive::Pmulfloat | Primitive::Pmulbigint => self.bin_of(BinOp::Mul, values),
            Primitive::Pdivfloat => self.bin_of(BinOp::Div, values),
            Primitive::Pmodfloat => self.bin_of(BinOp::Mod, values),
            Primitive::Ppowfloat | Primitive::Ppowbigint => self.bin_of(BinOp::Pow, values),
            Primitive::Pandbigint => self.bin_of(BinOp::Band, values),
            Primitive::Porbigint => self.bin_of(BinOp::Bor, values),
            Primitive::Pxorbigint => self.bin_of(BinOp::Bxor, values),
            Primitive::Plslbigint => self.bin_of(BinOp::Lsl, values),
            Primitive::Pasrbigint | Primitive::Pasrint => self.bin_of(BinOp::Asr, values),
            Primitive::Pnotint | Primitive::Pnotbigint => {
                self.js.bnot(&mut self.arena, B::from_node(values[0]))
            }
            Primitive::Pintoffloat => self.js.to_int32(&mut self.arena, B::from_node(values[0])),
            Primitive::Pnegint => {
                let zero = self.js.int_literal(&mut self.arena, 0);
                self.js.int_add(&mut self.arena, true, zero, B::from_node(values[0]))
            }
            Primitive::Pnegfloat => {
                let value = self.arena.intern_float("0.").unwrap();
                let zero = self.js.number(&mut self.arena, value);
                self.js.bin(&mut self.arena, BinOp::Minus, zero, B::from_node(values[0]))
            }
            Primitive::Pnegbigint => {
                let text = self.arena.intern_text("+0");
                let value = self.arena.intern_const(crate::bir::Constant::BigInt(text));
                let zero = self.js.number(&mut self.arena, value);
                self.js.bin(&mut self.arena, BinOp::Minus, zero, B::from_node(values[0]))
            }
            Primitive::Plsrint => {
                if self.primitive_int(values[1]) == Some(0) {
                    self.js.release(&mut self.arena, B::from_node(values[1]));
                    B::from_node(values[0])
                } else {
                    let value = self.js.int_lsr(&mut self.arena, B::from_node(values[0]), B::from_node(values[1]));
                    self.js.to_int32(&mut self.arena, value)
                }
            }
            Primitive::Pdivbigint => {
                if self.check_div_by_zero {
                    self.runtime("Primitive_bigint", "div", values)
                } else {
                    self.bin_of(BinOp::Div, values)
                }
            }
            Primitive::Pmodbigint => {
                if self.check_div_by_zero {
                    self.runtime("Primitive_bigint", "mod_", values)
                } else {
                    self.bin_of(BinOp::Mod, values)
                }
            }
            // P: compile_primitive_js, PfnArity.
            Primitive::PfnArity => match values.first() {
                Some(&value) => self.js.length(&mut self.arena, B::from_node(value), LengthObject::Function),
                None => self.js.undefined(&mut self.arena, false),
            },
            // P: compile_primitive_js, strings and booleans.
            Primitive::Pstringadd => self.js.append(&mut self.arena, B::from_node(values[0]), B::from_node(values[1])),
            Primitive::Pnot => self.js.not(&mut self.arena, B::from_node(values[0])),
            // P: compile_primitive_js, identity group.
            Primitive::Pidentity | Primitive::Pfloatofint => self.first_value(values),
            Primitive::Pignore => {
                let value = self.first_value(values);
                let unit = self.js.undefined(&mut self.arena, true);
                self.js.seq(&mut self.arena, value, unit)
            }
            Primitive::Ptypeof => self.js.typeof_(&mut self.arena, B::from_node(values[0])),
            Primitive::PrawJsCode(info) => {
                let text = self.arena.intern_text(info.code.trim());
                self.js.raw(&mut self.arena, text, info.is_stmt)
            }
            Primitive::PcreateExtension(name) => {
                let mark = self.js.mark();
                let name = self.js.string(&mut self.arena, name);
                self.js.push(name);
                let mut call = self.runtime_call("Primitive_exceptions", "create", mark);
                let comment = self.arena.intern_text("@__PURE__");
                self.js.comment(&mut self.arena, &mut call, comment);
                call
            }
            Primitive::PinitMod => self.runtime("Primitive_module", "init", values),
            Primitive::PupdateMod => self.runtime("Primitive_module", "update", values),
            // P: compile_debugger lowers each argument for effects before debugger.
            Primitive::Pdebugger => {
                for value in values.drain(..) {
                    self.js.release(&mut self.arena, B::from_node(value));
                }
                let statement = self.js.debugger(&mut self.arena);
                self.primitive_statement(statement, payload.loc);
                self.js.undefined(&mut self.arena, true)
            }
            // P: compile_primitive_js, Praise; conversion never binds a thrown value.
            Primitive::Praise => {
                let value = self.first_value(values);
                let statement = self.js.throw(&mut self.arena, value);
                self.primitive_statement(statement, payload.loc);
                let value = match cx.cont {
                    Cont::Value(_) | Cont::Effect(Tail::No) => {
                        Some(B::node(self.js.undefined(&mut self.arena, false)))
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
            Primitive::Pjsx(jsx) => B::from_node(self.compile_jsx(jsx, values.drain(..))),
            Primitive::Pimport(source) => B::from_node(self.compile_import(source)),
            Primitive::Pduprecord => B::from_node(self.duplicate_record(values[0])),
            Primitive::PrecordRest(excluded) => B::from_node(self.record_rest(values[0], excluded)),
            // P: compile_primitive_js, Pawait. O(1): one owned J node.
            Primitive::Pawait => self.js.await_(&mut self.arena, B::from_node(values[0])),
            Primitive::Pstringlength => {
                self.js.length(&mut self.arena, B::from_node(values[0]), LengthObject::String)
            }
            Primitive::Parraylength => {
                self.js.length(&mut self.arena, B::from_node(values[0]), LengthObject::Array)
            }
            Primitive::PjsCall(call) => {
                let values = self.arena.lists.push(values);
                B::from_node(self.compile_js_call(cx, prim.primitive, call, values))
            },
            Primitive::PjsApply => match values.split_first() {
                Some((&callee, args)) => {
                    let info = self.arena.js_info(crate::bir::JsPayload::Call(Default::default()));
                    let mark = self.push_values(args);
                    self.js.call(&mut self.arena, B::from_node(callee), mark, info)
                }
                None => self.js.undefined(&mut self.arena, false),
            },
            Primitive::PjsObjectCreate(specs) => {
                let values = self.arena.lists.push(values);
                B::from_node(self.compile_js_object_create(cx, specs, values))
            },
            Primitive::PjsFnMethod => {
                let value = self.first_value(values);
                for unused in values.drain(..).skip(1) {
                    self.js.release(&mut self.arena, B::from_node(unused));
                }
                if let Some(header) = self.js.function_of(&self.arena, B::of(&value)) {
                    self.arena.vars.funcs[header.index()].flags |= crate::bir::FuncHeader::METHOD;
                }
                value
            }
            Primitive::PjsObjectGet(name) | Primitive::PjsObjectSet(name) => {
                match (primitive, values.as_slice()) {
                    (Primitive::PjsObjectGet(_), &[receiver]) => {
                        B::from_node(self.static_member(receiver, name))
                    }
                    (Primitive::PjsObjectSet(_), &[receiver, value]) => {
                        let target = B::from_node(self.static_member(receiver, name));
                        let assign = self.js.bin_plain(&mut self.arena, BinOp::Eq, target, B::from_node(value));
                        let unit = self.js.undefined(&mut self.arena, true);
                        self.js.seq(&mut self.arena, assign, unit)
                    }
                    _ => {
                        for value in values.drain(..) {
                            self.js.release(&mut self.arena, B::from_node(value));
                        }
                        self.js.undefined(&mut self.arena, false)
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
        if located && !self.js.located(&self.arena, B::of(&value))
            && self.locations.and_then(|t|t.get(payload.loc)).is_some_and(|loc| !loc.loc_ghost && loc.loc_start.cnum >= 0) {
            self.js.locate(&mut self.arena, &mut value, payload.loc);
        }
        Ok(self.primitive_result(
            cx,
            self.statements.since(Span {
                start: statements.start,
                len: 0,
            }),
            B::node(value),
        ))
    }

    /// C: declare_compiled, assign_compiled, return_compiled: conv after sequencing.
    /// O(s) to inspect the s statement slots, then O(1) conversion.
    pub(super) fn primitive_result(&mut self, cx: Cx, statements: Span, value: NodeId) -> Probed {
        if !self.statements.has_statements(statements) {
            self.statements.remove_empty(statements);
            self.probe_leaf(cx, value)
        } else {
            let out = self.leaf(cx, B::from_node(value));
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

#[cfg(test)]
mod dictionary_allocations {
    use super::*;
    use crate::lambda::{LamLoc, arena::LamArena, lam_constant::Constant as C, lam_primitive::Mutable};

    #[test]
    fn ten_thousand_dictionary_entries_and_spreads_lower_without_allocations() {
        for spread in [false, true] {
            let mut a = LamArena::new();
            let entries: Vec<_> = (0..10_000).map(|i| {
                let key = a.const_(C::String(format!("key{i}")));
                let value = a.const_(C::String(format!("value{i}")));
                let pair = a.prim_raw(Primitive::Pmakeblock(crate::lambda::TagInfo::Tuple, Mutable::Immutable), &[key, value], LamLoc::NONE);
                if spread {
                    let array = a.prim_raw(Primitive::Pmakearray, &[pair], LamLoc::NONE);
                    a.prim_raw(Primitive::Pmakedict, &[array], LamLoc::NONE)
                } else { pair }
            }).collect();
            let root = if spread { a.prim_raw(Primitive::PdictSpread, &entries, LamLoc::NONE) } else {
                let array = a.prim_raw(Primitive::Pmakearray, &entries, LamLoc::NONE);
                a.prim_raw(Primitive::Pmakedict, &[array], LamLoc::NONE)
            };
            let input = crate::bir::bridge::import_lambda(&a, root).unwrap();
            let root = input.root;
            let mut state = State::new(input);
            let run = |s: &mut State<'_>| {
                let out = s.probe(Cx::returning(), root).unwrap();
                let out = s.realize(Cx::returning(), out);
                for node in s.statements.statements(out.stmts) { s.arena.release(node); }
                if let Some(value) = out.value { s.arena.release(value); }
                s.statements.kill(out.stmts);
            };
            let lists = state.arena.lists.storage_shape().0;
            let properties = state.arena.pools.property_keys.len();
            let infos = state.arena.pools.js.len();
            run(&mut state);
            state.arena.lists.reserve_test_growth(state.arena.lists.storage_shape().0 - lists);
            state.arena.pools.property_keys.reserve(state.arena.pools.property_keys.len() - properties);
            state.arena.pools.js.reserve(state.arena.pools.js.len() - infos);
            state.free.reserve_repeat();
        state.arena.js_scope.as_mut().unwrap().reserve_repeat();
            let capacities = |s: &State<'_>| [s.arena.nodes.capacity(), s.arena.parents.capacity(), s.arena.free_nodes.capacity(),
                s.arena.release_stack.capacity(), s.arena.lists.storage_shape().1, s.arena.pools.property_keys.capacity(),
                s.arena.pools.js.capacity(), s.object_scratch.keys.capacity(), s.object_scratch.values.capacity(),
                s.argument_outputs.capacity(), s.argument_values.capacity(), s.traversal.work.capacity(),
                s.traversal.values.capacity(), s.traversal.children.capacity()];
            let before = capacities(&state); let free_before = state.free.capacities();
            let statements_before = state.statements.capacities(); let visits = state.source_steps;
            let steps = state.primitive_steps;
            let scope_before = state.arena.js_scope.as_ref().unwrap().capacities();
        let allocations = allocation_counter::measure(|| run(&mut state));
        assert_eq!(state.arena.js_scope.as_ref().unwrap().capacities(), scope_before);
            println!("dictionary spread={spread}: {allocations:?}, visits={}, primitives={}", state.source_steps-visits, state.primitive_steps-steps);
            assert_eq!(allocations.count_total, 0);
            assert_eq!(capacities(&state), before); assert_eq!(state.free.capacities(), free_before);
            assert_eq!(state.statements.capacities(), statements_before);
            assert!(state.object_scratch.keys.is_empty() && state.object_scratch.values.is_empty());
            assert_eq!(state.source_steps - visits, if spread { 50_001 } else { 30_002 });
            assert_eq!(state.primitive_steps - steps, if spread { 100_001 } else { 50_003 });
        }
    }
}

#[cfg(test)]
mod template_allocations {
    use super::*;
    use crate::lambda::{LamLoc, arena::LamArena, lam_constant::Constant as C};
    use crate::string_literal::template_from_source;

    #[test]
    fn ten_thousand_template_operands_lower_without_allocations() {
        for mode in 0..3 {
            let mut a = LamArena::new();
            let mut args: Vec<_> = (0..10_000).map(|i| {
                if mode == 0 || i % 3 == 0 { a.const_(C::String(format!("{{literal{i}}}"))) }
                else if i % 3 == 1 { a.prim_raw(Primitive::Ptemplate(vec![template_from_source("nested\\n").unwrap()]), &[], LamLoc::NONE) }
                else { a.var(Ident::new("dynamic", i + 1, crate::ident::IdentFlags::NONE)) }
            }).collect();
            let primitive = if mode == 2 {
                let tag = a.var(Ident::new("tag", 20_000, crate::ident::IdentFlags::NONE));
                args.insert(0, tag);
                Primitive::PtaggedTemplate(vec!["$".to_owned(); 10_001])
            } else { Primitive::Ptemplate(vec![template_from_source("$").unwrap(); 10_001]) };
            let root = a.prim_raw(primitive, &args, LamLoc::NONE);
            let input = crate::bir::bridge::import_lambda(&a, root).unwrap();
            let root = input.root; let mut state = State::new(input);
            let run = |s: &mut State<'_>| {
                let out = s.probe(Cx::returning(), root).unwrap(); let out = s.realize(Cx::returning(), out);
                for node in s.statements.statements(out.stmts) { s.arena.release(node); }
                if let Some(value) = out.value { s.arena.release(value); }
                s.statements.kill(out.stmts);
            };
            let lists = state.arena.lists.storage_shape().0;
            let parts = state.arena.pools.template_parts.len(); let infos = state.arena.pools.js.len();
            run(&mut state);
            state.arena.lists.reserve_test_growth(state.arena.lists.storage_shape().0 - lists);
            state.arena.pools.template_parts.reserve(state.arena.pools.template_parts.len() - parts);
            state.arena.pools.js.reserve(state.arena.pools.js.len() - infos);
            state.free.reserve_repeat();
        state.arena.js_scope.as_mut().unwrap().reserve_repeat();
            let capacities = |s: &State<'_>| [s.arena.nodes.capacity(), s.arena.parents.capacity(), s.arena.free_nodes.capacity(),
                s.arena.release_stack.capacity(), s.arena.lists.storage_shape().1, s.arena.pools.template_parts.capacity(),
                s.arena.pools.js.capacity(), s.arena.pools.text.capacity(), s.arena.pools.strings.capacity(),
                s.arena.pools.text_index.capacity(), s.arena.j_template_scratch.kept.capacity(),
                s.argument_outputs.capacity(), s.argument_values.capacity(), s.traversal.work.capacity(),
                s.traversal.values.capacity(), s.traversal.children.capacity()];
            let before = capacities(&state); let text_before = state.arena.j_template_scratch.text.capacities();
            let free_before = state.free.capacities(); let stmts = state.statements.capacities();
            let visits = state.source_steps; let primitives = state.primitive_steps; let steps = state.arena.j_template_scratch.steps;
            let scope_before = state.arena.js_scope.as_ref().unwrap().capacities();
        let allocations = allocation_counter::measure(|| run(&mut state));
        assert_eq!(state.arena.js_scope.as_ref().unwrap().capacities(), scope_before);
            println!("template mode={mode}: {allocations:?}; source={}, primitive={}, normalization={}", state.source_steps-visits, state.primitive_steps-primitives, state.arena.j_template_scratch.steps-steps);
            assert_eq!(allocations.count_total, 0);
            assert_eq!(capacities(&state), before); assert_eq!(state.arena.j_template_scratch.text.capacities(), text_before);
            assert_eq!(state.free.capacities(), free_before); assert_eq!(state.statements.capacities(), stmts);
            assert!(state.arena.j_template_scratch.kept.is_empty());
            let expected = [(10_001, 10_001, 10_000), (10_001, 13_334, 10_000), (10_002, 13_335, 0)][mode];
            assert_eq!((state.source_steps - visits, state.primitive_steps - primitives, state.arena.j_template_scratch.steps - steps), expected);
        }
        assert_eq!(std::mem::size_of::<crate::bir::TemplateSpan>(), 8);
    }
}
