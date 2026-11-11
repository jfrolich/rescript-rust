//! Primitive operation compilation.
//!
//! Port of `lam_compile_primitive.ml`.
//! Extracted from `lam_compile.rs` for organization.

use super::js_exp_make::{
    bool_literal, both_bigint_literals, both_bool_literals, both_float_literals, both_int_literals,
    both_string_literals, compare_bigint_literals, compare_bool_literals, compare_string_literals,
    comparison_to_binop, comparison_to_float_binop, comparison_to_runtime_member,
    compile_int_equality, compile_nullish_strict_comparison, compile_raw_comparison, int_bnot,
    int_expr, int_literal, int32_add, int32_band, int32_bor, int32_bxor, int32_lsl, int32_lsr,
    int32_minus, int32_mul, int32_pow, is_nullish_literal, is_optional_block, is_type_object_expr,
    is_zero_int, js_expr_no_side_effects, js_seq, ocaml_typeof_expr, runtime_compare_call_args,
    to_int32,
};
use super::lam_compile::{Compiled, LambdaCompiler, OutputFinished};
use crate::ident::Ident;
use crate::js_ir::arena::{Block, Expr, ExprKind, JsArena, PropName};
use crate::js_ir::build::{exp as JE, stmt as JS};
use crate::js_ir::op::{LengthObject, MutableFlag, Number};
use crate::js_ir::{BinOp, CallInfo};
use crate::lambda::LamLoc;
use crate::lambda::TagInfo;
use crate::lambda::arena::{Lam, LamArena, LamList, PrimId, View};
use crate::lambda::lam_compat::{Comparison, FieldDbgInfo};
use crate::lambda::lam_primitive::{Mutable, Primitive};

/// Compiled primitive arguments; primitives take at most a few.
pub(crate) type PrimArgs = super::lam_compile_arguments::ArgValues;

impl LambdaCompiler {
    pub(crate) fn compile_primitive(
        &mut self,
        a: &mut LamArena,
        info: PrimId,
        args: LamList,
    ) -> Compiled {
        if let Some(compiled) = self.compile_flat_make_field(a, info, args) {
            return compiled;
        }

        let p = a.prim_payload(info);
        if matches!(p.primitive, Primitive::Pdebugger) {
            let loc = p.loc;
            return self.compile_debugger(a, args, &loc);
        }
        if let (Primitive::PjsObjectGet(property), [obj]) = (&p.primitive, a.list(args)) {
            let (property, obj) = (property.clone(), *obj);
            return self.compile_js_object_get(a, &property, obj);
        }
        // The arguments are compiled before the primitive is read again, so
        // that it can be borrowed from the arena instead of copied.
        let args = a.list_small(args);
        let compiled = self.compile_each_argument(a, args);
        let p = a.prim_payload(info);
        let compiled = match &p.primitive {
            Primitive::PjsCall(call) => self.hold_external_args(&call.arg_types, compiled),
            Primitive::PjsObjectCreate(obj_params) => {
                self.hold_external_obj_args(obj_params, compiled)
            }
            _ => compiled,
        };
        let (prelude, compiled_args) = self.sequence_arguments(false, compiled);
        self.compile_primitive_js(&p.primitive, compiled_args, prelude, &p.loc)
    }

    /// Evaluate debugger's unit argument for effects before emitting the statement.
    fn compile_debugger(&mut self, a: &mut LamArena, args: LamList, loc: &LamLoc) -> Compiled {
        let mut prelude = Vec::new();
        for arg in a.list_small(args) {
            prelude.extend(self.compile_effect_block_output(a, arg).block);
        }
        let statement = JS::debugger(&mut self.j);
        let loc = self.source_loc(loc);
        prelude.push(self.j.with_stmt_loc(statement, loc));
        Compiled {
            prelude,
            expr: JE::undefined(true, &mut self.j),
            finished: OutputFinished::False,
        }
    }

    /// Hold an effectful property receiver after its prelude unless it can be duplicated.
    fn compile_js_object_get(&mut self, a: &mut LamArena, property: &str, obj: Lam) -> Compiled {
        let Compiled {
            mut prelude,
            expr: obj,
            ..
        } = self.compile_expr(a, obj);
        let expr = if prelude.is_empty()
            || super::lam_compile_arguments::is_okay_to_duplicate(&self.j, obj)
        {
            self.static_index(obj, property)
        } else {
            let tmp = self.fresh_tmp_ident();
            prelude.push(super::lam_compile_arguments::define_strict_variable(
                tmp,
                obj,
                &mut self.j,
            ));
            let obj = JE::var(tmp, &mut self.j);
            self.static_index(obj, property)
        };
        Compiled {
            prelude,
            expr,
            finished: OutputFinished::False,
        }
    }

    /// lam_compile.ml `flat_make_field`: every nested `make` is also exported
    /// under a flat name (see `Translmod.implementation`), so a read
    /// `Pfield "make" (Pfield "B" (Pfield "A" (Lglobal_module Other)))` is
    /// emitted as `Other.A$B$make` rather than through the module objects.
    /// The same holds below a local bound to the awaited module,
    /// `let d = await import(Other)`. Other reads are left to the caller.
    pub(crate) fn compile_flat_make_field(
        &mut self,
        a: &LamArena,
        info: PrimId,
        args: LamList,
    ) -> Option<Compiled> {
        enum Base {
            Global(Ident),
            Awaited(Ident),
        }
        fn extract_field_path<'a>(
            a: &'a LamArena,
            awaited_units: &ahash::AHashSet<Ident>,
            prim: &'a Primitive,
            args: &[Lam],
            segments: &mut smallvec::SmallVec<[&'a str; 4]>,
        ) -> Option<Base> {
            let Primitive::Pfield(_, FieldDbgInfo::Module { name }) = prim else {
                return None;
            };
            let [arg] = args else {
                return None;
            };
            segments.push(name);
            match a.view(*arg) {
                View::Prim(prim, args, _) => {
                    extract_field_path(a, awaited_units, prim, args, segments)
                }
                View::GlobalModule(id) => Some(Base::Global(id)),
                View::Var(id) if awaited_units.contains(&id) => Some(Base::Awaited(id)),
                _ => None,
            }
        }
        let mut reversed = smallvec::SmallVec::new();
        let base = extract_field_path(
            a,
            &self.awaited_units,
            &a.prim_payload(info).primitive,
            a.list(args),
            &mut reversed,
        )?;
        reversed.reverse();
        let name = crate::lambda::flat_make_name(&reversed)?;
        let expr = match base {
            // `E.ml_var_dot id name`
            Base::Global(id) => JE::qualified(
                crate::js_ir::ModuleId {
                    id,
                    kind: crate::js_ir::Kind::Ml,
                    dynamic_import: false,
                },
                Some(name),
                &mut self.j,
            ),
            // `E.dot (E.var id) name`
            Base::Awaited(id) => {
                let base = JE::var(id, &mut self.j);
                JE::static_index(base, &name, None, &mut self.j)
            }
        };
        Some(Compiled {
            prelude: Vec::new(),
            expr,
            finished: OutputFinished::False,
        })
    }

    /// Lower already-compiled arguments. The caller owns traversal of the
    /// Lambda arguments.
    /// This is the Js_of_lam_primitive boundary in
    /// compiler/core/lam_compile_primitive.ml, not a Lambda compatibility step.
    pub(crate) fn compile_primitive_js(
        &mut self,
        prim: &Primitive,
        mut compiled_args: PrimArgs,
        mut prelude: Block,
        loc: &LamLoc,
    ) -> Compiled {
        use Primitive::*;
        let expr = match prim {
            Pstringlength => JE::length(
                take_arg(&mut compiled_args, 0),
                LengthObject::String,
                &mut self.j,
            ),
            Parraylength => JE::length(
                take_arg(&mut compiled_args, 0),
                LengthObject::Array,
                &mut self.j,
            ),
            // lam_compile_primitive.ml `Ptagged_template strings`:
            // `[tag; value0; ...]` plus raw source segments -> tag`...`.
            PtaggedTemplate(strings) => {
                let mut args = std::mem::take(&mut compiled_args).into_iter();
                let tag = args.next().expect("a tagged template has a tag");
                let values: Vec<Expr> = args.collect();
                let strings = self.j.tagged_id(strings.clone());
                let values = self.j.expr_list(&values);
                JE::new(ExprKind::TaggedTemplate(tag, strings, values), &mut self.j)
            }
            // `Ptemplate [segment] when args = []` / `Ptemplate segments`.
            Ptemplate(segments) if segments.len() == 1 && compiled_args.is_empty() => {
                let t = self.j.template_id(segments[0].clone());
                JE::new(ExprKind::TemplateLiteral(t), &mut self.j)
            }
            Ptemplate(segments) => crate::lambda::js_exp_make::interpolated_template(
                segments.clone(),
                std::mem::take(&mut compiled_args).into_vec(),
                &mut self.j,
            ),
            // OCaml lam_compile_primitive.ml:87-90 lowers Pjs_apply to a
            // direct call of the first argument with the remaining arguments.
            PjsApply => {
                let mut args = std::mem::take(&mut compiled_args).into_iter();
                match args.next() {
                    Some(func) => {
                        let args: Vec<Expr> = args.collect();
                        JE::call(func, &args, CallInfo::default(), &mut self.j)
                    }
                    None => JE::undefined(false, &mut self.j),
                }
            }
            // OCaml lam_compile_primitive.ml:136 lowers Pfn_arity to
            // function_length, i.e. `.length` on the function value.
            PfnArity => match first_arg(compiled_args) {
                Some(func) => JE::length(func, LengthObject::Function, &mut self.j),
                None => JE::undefined(false, &mut self.j),
            },
            Pstringrefs | Pstringrefu => {
                self.runtime_call_expr("Primitive_string", "getChar", compiled_args.into_vec())
            }
            Parrayrefu => match <[Expr; 2]>::try_from(compiled_args.as_slice()) {
                Ok([array, index]) => JE::new(ExprKind::ArrayIndex(array, index), &mut self.j),
                _ => JE::undefined(false, &mut self.j),
            },
            Parrayrefs => {
                self.runtime_call_expr("Primitive_array", "get", compiled_args.into_vec())
            }
            Parraysetu => match <[Expr; 3]>::try_from(compiled_args.as_slice()) {
                Ok([array, index, value]) => {
                    let target = JE::new(ExprKind::ArrayIndex(array, index), &mut self.j);
                    let assign = JE::bin(BinOp::Eq, target, value, &mut self.j);
                    let unit = JE::undefined(false, &mut self.j);
                    JE::new(ExprKind::Seq(assign, unit), &mut self.j)
                }
                _ => JE::undefined(false, &mut self.j),
            },
            Paddint => int32_add(
                take_arg(&mut compiled_args, 0),
                take_arg(&mut compiled_args, 1),
                &mut self.j,
            ),
            Paddfloat => JE::bin(
                BinOp::Plus,
                take_arg(&mut compiled_args, 0),
                take_arg(&mut compiled_args, 1),
                &mut self.j,
            ),
            Paddbigint => JE::bin(
                BinOp::Plus,
                take_arg(&mut compiled_args, 0),
                take_arg(&mut compiled_args, 1),
                &mut self.j,
            ),
            Psubint => int32_minus(
                take_arg(&mut compiled_args, 0),
                take_arg(&mut compiled_args, 1),
                &mut self.j,
            ),
            Psubfloat => JE::bin(
                BinOp::Minus,
                take_arg(&mut compiled_args, 0),
                take_arg(&mut compiled_args, 1),
                &mut self.j,
            ),
            Psubbigint => JE::bin(
                BinOp::Minus,
                take_arg(&mut compiled_args, 0),
                take_arg(&mut compiled_args, 1),
                &mut self.j,
            ),
            Pmulint => int32_mul(
                take_arg(&mut compiled_args, 0),
                take_arg(&mut compiled_args, 1),
                &mut self.j,
            ),
            Pmulfloat => JE::bin(
                BinOp::Mul,
                take_arg(&mut compiled_args, 0),
                take_arg(&mut compiled_args, 1),
                &mut self.j,
            ),
            Pmulbigint => JE::bin(
                BinOp::Mul,
                take_arg(&mut compiled_args, 0),
                take_arg(&mut compiled_args, 1),
                &mut self.j,
            ),
            Pdivint => self.int32_div_expr(
                take_arg(&mut compiled_args, 0),
                take_arg(&mut compiled_args, 1),
            ),
            Pdivfloat => JE::bin(
                BinOp::Div,
                take_arg(&mut compiled_args, 0),
                take_arg(&mut compiled_args, 1),
                &mut self.j,
            ),
            Pdivbigint => self.bigint_div_expr(
                take_arg(&mut compiled_args, 0),
                take_arg(&mut compiled_args, 1),
            ),
            Pmodint => self.int32_mod_expr(
                take_arg(&mut compiled_args, 0),
                take_arg(&mut compiled_args, 1),
            ),
            Pmodfloat => JE::bin(
                BinOp::Mod,
                take_arg(&mut compiled_args, 0),
                take_arg(&mut compiled_args, 1),
                &mut self.j,
            ),
            Pmodbigint => self.bigint_mod_expr(
                take_arg(&mut compiled_args, 0),
                take_arg(&mut compiled_args, 1),
            ),
            Ppowint => int32_pow(
                take_arg(&mut compiled_args, 0),
                take_arg(&mut compiled_args, 1),
                &mut self.j,
            ),
            Ppowfloat => JE::bin(
                BinOp::Pow,
                take_arg(&mut compiled_args, 0),
                take_arg(&mut compiled_args, 1),
                &mut self.j,
            ),
            Ppowbigint => JE::bin(
                BinOp::Pow,
                take_arg(&mut compiled_args, 0),
                take_arg(&mut compiled_args, 1),
                &mut self.j,
            ),
            Pobjcomp(cmp) => self.compile_object_comparison(
                *cmp,
                take_arg(&mut compiled_args, 0),
                take_arg(&mut compiled_args, 1),
            ),
            Pboolcomp(cmp) => self.compile_bool_comparison(
                *cmp,
                take_arg(&mut compiled_args, 0),
                take_arg(&mut compiled_args, 1),
            ),
            Pintcomp(cmp) | Pfloatcomp(cmp @ (Comparison::Eq | Comparison::Neq)) => self
                .compile_int_comparison(
                    *cmp,
                    take_arg(&mut compiled_args, 0),
                    take_arg(&mut compiled_args, 1),
                ),
            Pfloatcomp(cmp) => JE::bin(
                comparison_to_float_binop(*cmp),
                take_arg(&mut compiled_args, 0),
                take_arg(&mut compiled_args, 1),
                &mut self.j,
            ),
            Pbigintcomp(cmp) => self.compile_bigint_comparison(
                *cmp,
                take_arg(&mut compiled_args, 0),
                take_arg(&mut compiled_args, 1),
            ),
            // js_exp_make.ml `js_comp`: the operands may be of any type, so
            // they may be NaN.
            Pjscomp(cmp) => JE::bin(
                comparison_to_float_binop(*cmp),
                take_arg(&mut compiled_args, 0),
                take_arg(&mut compiled_args, 1),
                &mut self.j,
            ),
            Pstringcomp(cmp) => self.compile_string_comparison(
                *cmp,
                take_arg(&mut compiled_args, 0),
                take_arg(&mut compiled_args, 1),
            ),
            Pobjorder => {
                self.runtime_call_expr("Primitive_object", "compare", compiled_args.into_vec())
            }
            Pobjmin => self.runtime_call_expr("Primitive_object", "min", compiled_args.into_vec()),
            Pobjmax => self.runtime_call_expr("Primitive_object", "max", compiled_args.into_vec()),
            Pobjtag => {
                let tag = self.j.str("TAG");
                JE::new(
                    ExprKind::CamlBlockTag(take_arg(&mut compiled_args, 0), tag),
                    &mut self.j,
                )
            }
            // OCaml js_exp_make.ml:1374-1375 wraps Caml_block length in
            // to_int32, unlike array/string/function length.
            Pobjsize => to_int32(
                JE::length(
                    take_arg(&mut compiled_args, 0),
                    LengthObject::CamlBlock,
                    &mut self.j,
                ),
                &mut self.j,
            ),
            Pboolorder => match (
                bool_literal(&self.j, compiled_args[0]),
                bool_literal(&self.j, compiled_args[1]),
            ) {
                (Some(left), Some(right)) => int_expr(left.cmp(&right) as i32, &mut self.j),
                _ => self.runtime_call_expr("Primitive_bool", "compare", compiled_args.into_vec()),
            },
            Pboolmin => self.compile_typed_min_max(
                "Primitive_bool",
                "min",
                comparison_to_float_binop(Comparison::Lt),
                take_arg(&mut compiled_args, 0),
                take_arg(&mut compiled_args, 1),
                both_bool_literals,
            ),
            Pboolmax => self.compile_typed_min_max(
                "Primitive_bool",
                "max",
                comparison_to_float_binop(Comparison::Gt),
                take_arg(&mut compiled_args, 0),
                take_arg(&mut compiled_args, 1),
                both_bool_literals,
            ),
            Pintorder => {
                self.runtime_call_expr("Primitive_int", "compare", compiled_args.into_vec())
            }
            Pintmin => self.compile_typed_min_max(
                "Primitive_int",
                "min",
                comparison_to_float_binop(Comparison::Lt),
                take_arg(&mut compiled_args, 0),
                take_arg(&mut compiled_args, 1),
                both_int_literals,
            ),
            Pintmax => self.compile_typed_min_max(
                "Primitive_int",
                "max",
                comparison_to_float_binop(Comparison::Gt),
                take_arg(&mut compiled_args, 0),
                take_arg(&mut compiled_args, 1),
                both_int_literals,
            ),
            Pfloatorder => {
                self.runtime_call_expr("Primitive_float", "compare", compiled_args.into_vec())
            }
            Pfloatmin => self.compile_typed_min_max(
                "Primitive_float",
                "min",
                comparison_to_float_binop(Comparison::Lt),
                take_arg(&mut compiled_args, 0),
                take_arg(&mut compiled_args, 1),
                both_float_literals,
            ),
            Pfloatmax => self.compile_typed_min_max(
                "Primitive_float",
                "max",
                comparison_to_float_binop(Comparison::Gt),
                take_arg(&mut compiled_args, 0),
                take_arg(&mut compiled_args, 1),
                both_float_literals,
            ),
            Pbigintorder => {
                self.runtime_call_expr("Primitive_bigint", "compare", compiled_args.into_vec())
            }
            Pbigintmin => self.compile_typed_min_max(
                "Primitive_bigint",
                "min",
                comparison_to_binop(Comparison::Lt),
                take_arg(&mut compiled_args, 0),
                take_arg(&mut compiled_args, 1),
                both_bigint_literals,
            ),
            Pbigintmax => self.compile_typed_min_max(
                "Primitive_bigint",
                "max",
                comparison_to_binop(Comparison::Gt),
                take_arg(&mut compiled_args, 0),
                take_arg(&mut compiled_args, 1),
                both_bigint_literals,
            ),
            Pstringorder => {
                self.runtime_call_expr("Primitive_string", "compare", compiled_args.into_vec())
            }
            Pstringmin => self.compile_typed_min_max(
                "Primitive_string",
                "min",
                comparison_to_float_binop(Comparison::Lt),
                take_arg(&mut compiled_args, 0),
                take_arg(&mut compiled_args, 1),
                both_string_literals,
            ),
            Pstringmax => self.compile_typed_min_max(
                "Primitive_string",
                "max",
                comparison_to_float_binop(Comparison::Gt),
                take_arg(&mut compiled_args, 0),
                take_arg(&mut compiled_args, 1),
                both_string_literals,
            ),
            Phash => self.runtime_call_expr("Primitive_hash", "hash", compiled_args.into_vec()),
            PhashMixint => {
                self.runtime_call_expr("Primitive_hash", "hash_mix_int", compiled_args.into_vec())
            }
            PhashMixstring => self.runtime_call_expr(
                "Primitive_hash",
                "hash_mix_string",
                compiled_args.into_vec(),
            ),
            PhashFinalmix => {
                self.runtime_call_expr("Primitive_hash", "hash_final_mix", compiled_args.into_vec())
            }
            Psequand => JE::bin(
                BinOp::And,
                take_arg(&mut compiled_args, 0),
                take_arg(&mut compiled_args, 1),
                &mut self.j,
            ),
            Psequor => JE::bin(
                BinOp::Or,
                take_arg(&mut compiled_args, 0),
                take_arg(&mut compiled_args, 1),
                &mut self.j,
            ),
            Pnot => JE::not(take_arg(&mut compiled_args, 0), &mut self.j),
            Pnegint => int32_minus(
                int_expr(0, &mut self.j),
                take_arg(&mut compiled_args, 0),
                &mut self.j,
            ),
            // `Pnegfloat` must emit `0. - x` (not `0 - x`) so the printer
            // rule at `js_dump.ml` / `printer.rs:1520-1531` produces `- x`
            // with the OCaml-style space. Mirrors
            // `lam_compile_primitive.ml:179`: `E.float_minus E.zero_float_lit`.
            Pnegfloat => JE::bin(
                BinOp::Minus,
                JE::number(Number::float("0."), &mut self.j),
                take_arg(&mut compiled_args, 0),
                &mut self.j,
            ),
            Pnegbigint => JE::bin(
                BinOp::Minus,
                JE::number(Number::bigint(true, "0"), &mut self.j),
                take_arg(&mut compiled_args, 0),
                &mut self.j,
            ),
            Pnotint => int_bnot(take_arg(&mut compiled_args, 0), &mut self.j),
            Pnotbigint => int_bnot(take_arg(&mut compiled_args, 0), &mut self.j),
            Pandint => int32_band(
                take_arg(&mut compiled_args, 0),
                take_arg(&mut compiled_args, 1),
                &mut self.j,
            ),
            Pandbigint => JE::bin(
                BinOp::Band,
                take_arg(&mut compiled_args, 0),
                take_arg(&mut compiled_args, 1),
                &mut self.j,
            ),
            Porint => int32_bor(
                take_arg(&mut compiled_args, 0),
                take_arg(&mut compiled_args, 1),
                &mut self.j,
            ),
            Porbigint => JE::bin(
                BinOp::Bor,
                take_arg(&mut compiled_args, 0),
                take_arg(&mut compiled_args, 1),
                &mut self.j,
            ),
            Pxorint => int32_bxor(
                take_arg(&mut compiled_args, 0),
                take_arg(&mut compiled_args, 1),
                &mut self.j,
            ),
            Pxorbigint => JE::bin(
                BinOp::Bxor,
                take_arg(&mut compiled_args, 0),
                take_arg(&mut compiled_args, 1),
                &mut self.j,
            ),
            Plslint => int32_lsl(
                take_arg(&mut compiled_args, 0),
                take_arg(&mut compiled_args, 1),
                &mut self.j,
            ),
            Plslbigint => JE::bin(
                BinOp::Lsl,
                take_arg(&mut compiled_args, 0),
                take_arg(&mut compiled_args, 1),
                &mut self.j,
            ),
            Plsrint => {
                // OCaml `Plsrint` returns the left operand directly for a
                // literal zero shift, otherwise wraps the logical shift in
                // `to_int32` (`compiler/core/lam_compile_primitive.ml:264-267`).
                if is_zero_int(&self.j, compiled_args[1]) {
                    take_arg(&mut compiled_args, 0)
                } else {
                    to_int32(
                        int32_lsr(
                            take_arg(&mut compiled_args, 0),
                            take_arg(&mut compiled_args, 1),
                            &mut self.j,
                        ),
                        &mut self.j,
                    )
                }
            }
            Pasrint => JE::bin(
                BinOp::Asr,
                take_arg(&mut compiled_args, 0),
                take_arg(&mut compiled_args, 1),
                &mut self.j,
            ),
            Pasrbigint => JE::bin(
                BinOp::Asr,
                take_arg(&mut compiled_args, 0),
                take_arg(&mut compiled_args, 1),
                &mut self.j,
            ),
            PisPolyVarBlock => is_type_object_expr(take_arg(&mut compiled_args, 0), &mut self.j),
            Pmakearray => JE::array(&compiled_args, MutableFlag::Mutable, &mut self.j),
            Pmakedict => match compiled_args
                .as_slice()
                .first()
                .filter(|_| compiled_args.len() == 1)
                .and_then(|arg| match self.j.ek(*arg) {
                    ExprKind::Array(items, _) => Some(items),
                    _ => None,
                }) {
                Some(items) => {
                    let props: Vec<(crate::js_ir::arena::PropName, Expr)> = self
                        .j
                        .exprs(items)
                        .iter()
                        .filter_map(|item| match self.j.ek(*item) {
                            ExprKind::CamlBlock(fields, _, _) => match self.j.exprs(fields) {
                                [key, value] => match self.j.ek(*key) {
                                    ExprKind::Str(txt) => {
                                        Some((crate::js_ir::arena::PropName::Lit(txt), *value))
                                    }
                                    _ => None,
                                },
                                _ => None,
                            },
                            _ => None,
                        })
                        .collect();
                    let props = self.j.prop_list(&props);
                    JE::new(ExprKind::Object(props), &mut self.j)
                }
                _ => JE::undefined(false, &mut self.j),
            },
            ParraySpread => self.runtime_call_expr("Primitive_array", "spread", compiled_args.into_vec()),
            PlistSpread => self.runtime_call_expr("Primitive_list", "spread", compiled_args.into_vec()),
            PdictSpread => {
                let mut entries = Vec::new();
                for arg in compiled_args {
                    match self.j.ek(arg) {
                        ExprKind::Object(props)
                            if self.j.props(props).iter().all(|(name, _)| {
                                matches!(name, PropName::Lit(_) | PropName::Symbol)
                            }) =>
                        {
                            entries.extend_from_slice(self.j.props(props));
                        }
                        _ => entries.push((PropName::Spread, arg)),
                    }
                }
                let entries = self.j.prop_list(&entries);
                self.j.expr(ExprKind::Object(entries))
            }
            PdictHas => match <[Expr; 2]>::try_from(compiled_args.as_slice()) {
                Ok([obj, prop]) => JE::new(ExprKind::In(prop, obj), &mut self.j),
                _ => {
                    self.report_diagnostic(
                        loc,
                        "Invalid external \"%dict_has\" type signature. Expected to have two arguments.",
                    );
                    JE::undefined(false, &mut self.j)
                }
            },
            Pduprecord => match <[Expr; 1]>::try_from(compiled_args.as_slice()) {
                Ok([source]) => {
                    let props = self
                        .j
                        .prop_list(&[(crate::js_ir::arena::PropName::RecordSpread, source)]);
                    JE::new(ExprKind::Object(props), &mut self.j)
                }
                _ => JE::undefined(false, &mut self.j),
            },
            PrecordRest(excluded) => match <[Expr; 1]>::try_from(compiled_args.as_slice()) {
                Ok([source]) => {
                    let fields = self.j.rest_id(
                        excluded
                            .iter()
                            .map(|label| crate::js_ir::RecordRestField {
                                label: label.clone(),
                                ident: None,
                            })
                            .collect(),
                    );
                    JE::new(ExprKind::RecordRest(fields, source), &mut self.j)
                }
                _ => JE::undefined(false, &mut self.j),
            },
            Pstringadd => JE::string_append(
                take_arg(&mut compiled_args, 0),
                take_arg(&mut compiled_args, 1),
                &mut self.j,
            ),
            PinitMod => {
                self.runtime_call_expr("Primitive_module", "init", compiled_args.into_vec())
            }
            PupdateMod => {
                self.runtime_call_expr("Primitive_module", "update", compiled_args.into_vec())
            }
            PnullToOpt => self.null_to_opt_expr(take_arg(&mut compiled_args, 0)),
            PnullUndefinedToOpt => self.null_undefined_to_opt_expr(take_arg(&mut compiled_args, 0)),
            PisNotNone => self.is_not_none_expr(take_arg(&mut compiled_args, 0)),
            PisNull => self.is_null_expr(take_arg(&mut compiled_args, 0)),
            PisUndefined => self.is_undefined_expr(take_arg(&mut compiled_args, 0)),
            PisNullUndefined => self.is_null_or_undefined_expr(take_arg(&mut compiled_args, 0)),
            PvalFromOption => self.val_from_option_expr(take_arg(&mut compiled_args, 0)),
            PvalFromOptionNotNest => take_arg(&mut compiled_args, 0),
            Psome => self.some_expr(take_arg(&mut compiled_args, 0)),
            PsomeNotNest => self.optional_block(take_arg(&mut compiled_args, 0), true),
            Pfield(idx, info) => self.compile_field_access(*idx, info, compiled_args[0]),
            Psetfield(idx, info) => {
                let target = self.compile_set_field(*idx, info, compiled_args[0], compiled_args[1]);
                let unit = JE::undefined(false, &mut self.j);
                JE::new(ExprKind::Seq(target, unit), &mut self.j)
            }
            Pmakeblock(tag_info, mutable_flag) => {
                let js_mutable = match mutable_flag {
                    Mutable::Mutable => MutableFlag::Mutable,
                    Mutable::Immutable => MutableFlag::Immutable,
                };
                JE::caml_block(&compiled_args, js_mutable, tag_info.clone(), &mut self.j)
            }
            // OCaml lam_compile_primitive.ml:560-564 builds the mutable list
            // constructor block used by the runtime.
            Pmakelist => JE::caml_block(
                &compiled_args,
                MutableFlag::Mutable,
                TagInfo::constructor("::", 1),
                &mut self.j,
            ),
            PrawJsCode(info) => {
                let raw = self.j.raw_id(crate::js_ir::JsRawInfo {
                    code: info.code.trim().to_string(),
                    is_stmt: info.is_stmt,
                });
                JE::new(ExprKind::RawJsCode(raw), &mut self.j)
            }
            Pdebugger => {
                let statement = JS::debugger(&mut self.j);
                let source_loc = self.source_loc(loc);
                prelude.push(self.j.with_stmt_loc(statement, source_loc));
                JE::undefined(false, &mut self.j)
            }
            Praise => {
                let expr =
                    first_arg(compiled_args).unwrap_or_else(|| JE::undefined(false, &mut self.j));
                let statement = JS::throw(expr, &mut self.j);
                let source_loc = self.source_loc(loc);
                prelude.push(self.j.with_stmt_loc(statement, source_loc));
                JE::undefined(false, &mut self.j)
            }
            Pidentity | Pfloatofint => {
                first_arg(compiled_args).unwrap_or_else(|| JE::undefined(false, &mut self.j))
            }
            Pignore => {
                let value =
                    first_arg(compiled_args).unwrap_or_else(|| JE::undefined(false, &mut self.j));
                let unit = JE::undefined(true, &mut self.j);
                JE::new(ExprKind::Seq(value, unit), &mut self.j)
            }
            Ptypeof => ocaml_typeof_expr(take_arg(&mut compiled_args, 0), &mut self.j),
            Pintoffloat => to_int32(take_arg(&mut compiled_args, 0), &mut self.j),
            Pawait => JE::new(
                ExprKind::Await(take_arg(&mut compiled_args, 0)),
                &mut self.j,
            ),
            PcreateExtension(name) => {
                let name = JE::string(name, &mut self.j);
                self.pure_runtime_call_expr("Primitive_exceptions", "create", vec![name])
            }
            PjsObjectCreate(obj_params) => {
                self.compile_js_object_create(obj_params, compiled_args.into_vec(), &mut prelude)
            }
            PjsFnMethod => match first_arg(compiled_args).map(|expr| (expr, self.j.ek(expr))) {
                // lam_compile.ml:1727-1729: `with_source_loc loc (E.method_ ...)`
                // with the method function's own location.
                Some((expr, ExprKind::Fun(f))) => {
                    let info = self.j.fun(f);
                    let f = self.j.fun_id(crate::js_ir::arena::FunInfo {
                        is_method: true,
                        ..info
                    });
                    self.j.rekind_expr(expr, ExprKind::Fun(f))
                }
                Some((expr, _)) => expr,
                None => JE::undefined(false, &mut self.j),
            },
            PjsObjectGet(name) | PjsObjectSet(name) => {
                let mut args = std::mem::take(&mut compiled_args).into_iter();
                match (
                    matches!(prim, PjsObjectSet(_)),
                    args.next(),
                    args.next(),
                    args.next(),
                ) {
                    (false, Some(receiver), None, None) => self.static_index(receiver, name),
                    (true, Some(receiver), Some(value), None) => {
                        let target = self.static_index(receiver, name);
                        let assign = JE::bin(BinOp::Eq, target, value, &mut self.j);
                        let unit = JE::undefined(true, &mut self.j);
                        JE::new(ExprKind::Seq(assign, unit), &mut self.j)
                    }
                    _ => JE::undefined(false, &mut self.j),
                }
            }
            Pjsx(jsx) => self.compile_jsx(jsx, compiled_args.into_vec()),
            Pimport(source) => self.compile_import(loc, source),
            PjsCall(call) => {
                self.compile_js_call(&call.prim_name, &call.arg_types, &call.ffi, compiled_args.into_vec())
            }
            PextensionSlotEq => unreachable!("PextensionSlotEq is lowered in raw_lambda::lower"),
        };

        let finished = if matches!(prim, Praise) {
            OutputFinished::True
        } else {
            OutputFinished::False
        };
        Compiled {
            prelude,
            expr,
            finished,
        }
    }

    fn compile_object_comparison(&mut self, cmp: Comparison, left: Expr, right: Expr) -> Expr {
        match cmp {
            Comparison::Eq | Comparison::Neq
                if is_nullish_literal(&self.j, left).is_some()
                    || is_nullish_literal(&self.j, right).is_some() =>
            {
                compile_nullish_strict_comparison(cmp, left, right, &mut self.j)
            }
            _ => self.runtime_call_expr(
                "Primitive_object",
                comparison_to_runtime_member(cmp),
                vec![left, right],
            ),
        }
    }

    fn compile_bool_comparison(&mut self, cmp: Comparison, left: Expr, right: Expr) -> Expr {
        match (bool_literal(&self.j, left), bool_literal(&self.j, right)) {
            (Some(lhs), Some(rhs)) => JE::bool(compare_bool_literals(cmp, lhs, rhs), &mut self.j),
            (Some(true), _) | (_, Some(false)) => match cmp {
                Comparison::Lt => js_seq(
                    if matches!(bool_literal(&self.j, left), Some(true)) {
                        right
                    } else {
                        left
                    },
                    JE::bool(false, &mut self.j),
                    &mut self.j,
                ),
                Comparison::Ge => js_seq(
                    if matches!(bool_literal(&self.j, left), Some(true)) {
                        right
                    } else {
                        left
                    },
                    JE::bool(true, &mut self.j),
                    &mut self.j,
                ),
                Comparison::Eq | Comparison::Neq | Comparison::Le | Comparison::Gt => {
                    compile_raw_comparison(cmp, left, right, &mut self.j)
                }
            },
            (_, Some(true)) | (Some(false), _) => match cmp {
                Comparison::Le => js_seq(
                    if matches!(bool_literal(&self.j, right), Some(true)) {
                        left
                    } else {
                        right
                    },
                    JE::bool(true, &mut self.j),
                    &mut self.j,
                ),
                Comparison::Gt => js_seq(
                    if matches!(bool_literal(&self.j, right), Some(true)) {
                        left
                    } else {
                        right
                    },
                    JE::bool(false, &mut self.j),
                    &mut self.j,
                ),
                Comparison::Eq | Comparison::Neq | Comparison::Lt | Comparison::Ge => {
                    compile_raw_comparison(cmp, left, right, &mut self.j)
                }
            },
            _ => compile_raw_comparison(cmp, left, right, &mut self.j),
        }
    }

    fn compile_int_comparison(&mut self, cmp: Comparison, left: Expr, right: Expr) -> Expr {
        if let (Some(lhs), Some(rhs)) = (int_literal(&self.j, left), int_literal(&self.j, right)) {
            return JE::bool(cmp.cmp_int32(lhs, rhs), &mut self.j);
        }

        // OCaml's Js_exp_make.int_comp strips Runtime.compare(..., ...) when
        // the RHS is the integer literal 0, so compare(x, y) > 0 lowers to x > y.
        if int_literal(&self.j, right) == Some(0) {
            if let Some((compare_left, compare_right)) = runtime_compare_call_args(&self.j, left) {
                return self.compile_int_comparison(
                    cmp,
                    compare_left.clone(),
                    compare_right.clone(),
                );
            }
        }

        match cmp {
            Comparison::Eq => {
                if ((is_optional_block(&self.j, left)
                    && matches!(self.j.ek(right), ExprKind::Undefined { .. }))
                    || (matches!(self.j.ek(left), ExprKind::Undefined { .. })
                        && is_optional_block(&self.j, right)))
                    && js_expr_no_side_effects(&self.j, left)
                    && js_expr_no_side_effects(&self.j, right)
                {
                    return JE::bool(false, &mut self.j);
                }

                compile_int_equality(left, right, &mut self.j)
            }
            Comparison::Neq => {
                if ((is_optional_block(&self.j, left)
                    && matches!(self.j.ek(right), ExprKind::Undefined { .. }))
                    || (matches!(self.j.ek(left), ExprKind::Undefined { .. })
                        && is_optional_block(&self.j, right))
                    || (matches!(self.j.ek(left), ExprKind::CamlBlock(_, _, _))
                        && matches!(self.j.ek(right), ExprKind::Number(_)))
                    || (matches!(self.j.ek(left), ExprKind::Number(_))
                        && matches!(self.j.ek(right), ExprKind::CamlBlock(_, _, _))))
                    && js_expr_no_side_effects(&self.j, left)
                    && js_expr_no_side_effects(&self.j, right)
                {
                    return JE::bool(true, &mut self.j);
                }

                // OCaml's `Js_exp_make.int_comp` falls through to
                // `bin NotEqEq e0 e1` for the non-special Cneq cases — and
                // OCaml's `bin` has no NotEqEq case, so the construction is
                // effectively raw. `Expression::bin`'s `fold_strict_comparison`
                // would fold `3 !== null` to `true` via the nullish-impossible
                // rule, diverging from OCaml. Use a raw `Bin` here.
                JE::raw_bin(comparison_to_binop(cmp), left, right, &mut self.j)
            }
            Comparison::Lt | Comparison::Le | Comparison::Gt | Comparison::Ge => {
                compile_raw_comparison(cmp, left, right, &mut self.j)
            }
        }
    }

    fn compile_string_comparison(&mut self, cmp: Comparison, left: Expr, right: Expr) -> Expr {
        match compare_string_literals(&self.j, left, right) {
            Some(equal) => match cmp {
                Comparison::Eq => JE::bool(equal, &mut self.j),
                Comparison::Neq => JE::bool(!equal, &mut self.j),
                Comparison::Lt | Comparison::Le | Comparison::Gt | Comparison::Ge => {
                    compile_raw_comparison(cmp, left, right, &mut self.j)
                }
            },
            None => compile_raw_comparison(cmp, left, right, &mut self.j),
        }
    }

    fn compile_bigint_comparison(&mut self, cmp: Comparison, left: Expr, right: Expr) -> Expr {
        match compare_bigint_literals(&self.j, left, right) {
            Some(equal) => match cmp {
                Comparison::Eq => JE::bool(equal, &mut self.j),
                Comparison::Neq => JE::bool(!equal, &mut self.j),
                Comparison::Lt | Comparison::Le | Comparison::Gt | Comparison::Ge => {
                    compile_raw_comparison(cmp, left, right, &mut self.j)
                }
            },
            None => compile_raw_comparison(cmp, left, right, &mut self.j),
        }
    }

    fn compile_typed_min_max(
        &mut self,
        module_name: &str,
        member: &str,
        compare: BinOp,
        left: Expr,
        right: Expr,
        literal_fast_path: fn(&JsArena, Expr, Expr) -> bool,
    ) -> Expr {
        if literal_fast_path(&self.j, left, right) {
            let test = JE::bin(compare, left, right, &mut self.j);
            JE::cond(test, left, right, &mut self.j)
        } else {
            self.runtime_call_expr(module_name, member, vec![left, right])
        }
    }
}

/// Move argument `index` out of `args`, which the calling arm uses once.
/// Consume the argument list, returning its first element if any.
fn first_arg(args: PrimArgs) -> Option<Expr> {
    args.into_iter().next()
}

fn take_arg(args: &mut [Expr], index: usize) -> Expr {
    args[index]
}
