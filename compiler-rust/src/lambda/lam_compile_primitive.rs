//! Primitive operation compilation.
//!
//! Port of `lam_compile_primitive.ml`.
//! Extracted from `lam_compile.rs` for organization.

use super::js_exp_make::{
    bool_literal, both_bigint_literals, both_bool_literals, both_float_literals, both_int_literals,
    both_string_literals, compare_bigint_literals, compare_bool_literals, compare_int_literals,
    compare_string_literals, comparison_to_binop, comparison_to_runtime_member,
    compile_int_equality, compile_nullish_strict_comparison, compile_raw_comparison, int_bnot,
    int_expr, int_literal, int32_add, int32_band, int32_bor, int32_bxor, int32_lsl, int32_lsr,
    int32_minus, int32_mul, int32_offset, int32_pow, is_nullish_literal, is_optional_block,
    is_out_expr, is_type_number_expr, is_type_object_expr, is_zero_int, js_expr_no_side_effects,
    js_seq, ocaml_typeof_expr, poly_var_tag_access, poly_var_value_access, range_exclusion_or,
    runtime_compare_call_args, runtime_member_for_eta_wrapped_primitive, strict_eq_int, to_int32,
};
use super::lam_compile::{Compiled, LambdaCompiler, call_info_of_apply_status};
use crate::ident::Ident;
use crate::js_ir::op::{LengthObject, MutableFlag, Number, PropertyName};
use crate::js_ir::{
    BinOp, Block, CallInfo, Expression, ExpressionDesc, Statement, StatementDesc, VIdent,
    VariableDeclaration,
};
use crate::lambda::lam_compat::{Comparison, FieldDbgInfo, LetKind, SetFieldDbgInfo};
use crate::lambda::lam_constant::Constant;
use crate::lambda::lam_primitive::{ExternalSpec, Mutable, Primitive};
use crate::lambda::{Lambda, TagInfo};
use crate::location::Location;

impl LambdaCompiler {
    pub(crate) fn compile_primitive(
        &mut self,
        prim: &Primitive,
        args: &[Lambda],
        loc: &Location,
    ) -> Compiled {
        if matches!(prim, Primitive::Pimport) {
            return self.compile_import_primitive(loc, args);
        }

        // compiler/core/lam_compile.ml:293-325: nested module field reads may
        // name a flat root export recorded in the dependency CMJ.
        fn external_field_path<'a>(
            prim: &'a Primitive,
            args: &'a [Lambda],
            segments: &mut Vec<String>,
        ) -> Option<(&'a Ident, bool)> {
            let Primitive::Pfield(_, FieldDbgInfo::Module { name }) = prim else {
                return None;
            };
            segments.push(name.clone());
            match args {
                [Lambda::LglobalModule(id, dynamic_import)] => Some((id, *dynamic_import)),
                [Lambda::Lprim(info)] => external_field_path(&info.primitive, &info.args, segments),
                _ => None,
            }
        }
        if matches!(prim, Primitive::Pfield(_, FieldDbgInfo::Module { .. })) {
            let mut reversed = Vec::new();
            if let Some((id, dynamic_import)) = external_field_path(prim, args, &mut reversed) {
                reversed.reverse();
                if reversed.len() >= 2
                    && let Some(export_name) =
                        self.module_path_resolver.as_ref().and_then(|resolver| {
                            resolver.module_cmj_hoisted_export(id.name(), &reversed)
                        })
                {
                    return Compiled {
                        prelude: Vec::new(),
                        expr: Expression::qualified(
                            crate::js_ir::ModuleId {
                                id: id.clone(),
                                kind: crate::js_ir::Kind::Ml,
                                dynamic_import,
                            },
                            Some(export_name),
                        ),
                    };
                }
            }
        }

        use Primitive::*;
        let mut prelude = vec![];
        let mut compiled_args = Vec::new();
        for arg in args {
            let compiled = self.compile_expr(arg);
            prelude.extend(compiled.prelude);
            compiled_args.push(compiled.expr);
        }

        let expr = match prim {
            Pstringlength => Expression::length(compiled_args[0].clone(), LengthObject::String),
            Parraylength => Expression::length(compiled_args[0].clone(), LengthObject::Array),
            // Upstream compiler/core/lam_compile_primitive.ml:91-101.
            PtaggedTemplate => match compiled_args.as_slice() {
                [
                    tag,
                    Expression {
                        desc: ExpressionDesc::Array(strings, _),
                        ..
                    },
                    Expression {
                        desc: ExpressionDesc::Array(values, _),
                        ..
                    },
                ] => Expression::new(ExpressionDesc::TaggedTemplate(
                    Box::new(tag.clone()),
                    strings.clone(),
                    values.clone(),
                )),
                _ => unreachable!("tagged-template primitive operands are two arrays"),
            },
            // OCaml lam_compile_primitive.ml:87-90 lowers Pjs_apply to a
            // direct call of the first argument with the remaining arguments.
            PjsApply => match compiled_args.split_first() {
                Some((func, args)) => {
                    Expression::call(func.clone(), args.to_vec(), CallInfo::default())
                }
                None => Expression::undefined(false),
            },
            // OCaml lam_compile_primitive.ml:136 lowers Pfn_arity to
            // function_length, i.e. `.length` on the function value.
            PfnArity => match compiled_args.first() {
                Some(func) => Expression::length(func.clone(), LengthObject::Function),
                None => Expression::undefined(false),
            },
            Pstringrefs | Pstringrefu => {
                self.runtime_call_expr("Primitive_string", "getChar", compiled_args)
            }
            Parrayrefu => match compiled_args.as_slice() {
                [array, index] => Expression::new(ExpressionDesc::ArrayIndex(
                    Box::new(array.clone()),
                    Box::new(index.clone()),
                )),
                _ => Expression::undefined(false),
            },
            Parrayrefs => self.runtime_call_expr("Primitive_array", "get", compiled_args),
            Parraysetu => match compiled_args.as_slice() {
                [array, index, value] => Expression::new(ExpressionDesc::Seq(
                    Box::new(Expression::bin(
                        BinOp::Eq,
                        Expression::new(ExpressionDesc::ArrayIndex(
                            Box::new(array.clone()),
                            Box::new(index.clone()),
                        )),
                        value.clone(),
                    )),
                    Box::new(Expression::undefined(false)),
                )),
                _ => Expression::undefined(false),
            },
            Parraysets => self.runtime_call_expr("Primitive_array", "set", compiled_args),
            Paddint => int32_add(compiled_args[0].clone(), compiled_args[1].clone()),
            Paddfloat => Expression::bin(
                BinOp::Plus,
                compiled_args[0].clone(),
                compiled_args[1].clone(),
            ),
            Paddbigint => Expression::bin(
                BinOp::Plus,
                compiled_args[0].clone(),
                compiled_args[1].clone(),
            ),
            Psubint => int32_minus(compiled_args[0].clone(), compiled_args[1].clone()),
            Psubfloat => Expression::bin(
                BinOp::Minus,
                compiled_args[0].clone(),
                compiled_args[1].clone(),
            ),
            Psubbigint => Expression::bin(
                BinOp::Minus,
                compiled_args[0].clone(),
                compiled_args[1].clone(),
            ),
            Pmulint => int32_mul(compiled_args[0].clone(), compiled_args[1].clone()),
            Pmulfloat => Expression::bin(
                BinOp::Mul,
                compiled_args[0].clone(),
                compiled_args[1].clone(),
            ),
            Pmulbigint => Expression::bin(
                BinOp::Mul,
                compiled_args[0].clone(),
                compiled_args[1].clone(),
            ),
            Pdivint => self.int32_div_expr(compiled_args[0].clone(), compiled_args[1].clone()),
            Pdivfloat => Expression::bin(
                BinOp::Div,
                compiled_args[0].clone(),
                compiled_args[1].clone(),
            ),
            Pdivbigint => self.bigint_div_expr(compiled_args[0].clone(), compiled_args[1].clone()),
            Pmodint => self.int32_mod_expr(compiled_args[0].clone(), compiled_args[1].clone()),
            Pmodfloat => Expression::bin(
                BinOp::Mod,
                compiled_args[0].clone(),
                compiled_args[1].clone(),
            ),
            Pmodbigint => self.bigint_mod_expr(compiled_args[0].clone(), compiled_args[1].clone()),
            Ppowint => int32_pow(compiled_args[0].clone(), compiled_args[1].clone()),
            Ppowfloat => Expression::bin(
                BinOp::Pow,
                compiled_args[0].clone(),
                compiled_args[1].clone(),
            ),
            Ppowbigint => Expression::bin(
                BinOp::Pow,
                compiled_args[0].clone(),
                compiled_args[1].clone(),
            ),
            Pobjcomp(cmp) => self.compile_object_comparison(
                *cmp,
                compiled_args[0].clone(),
                compiled_args[1].clone(),
            ),
            Pboolcomp(cmp) => self.compile_bool_comparison(
                *cmp,
                compiled_args[0].clone(),
                compiled_args[1].clone(),
            ),
            Pintcomp(cmp) | Pfloatcomp(cmp) => self.compile_int_comparison(
                *cmp,
                compiled_args[0].clone(),
                compiled_args[1].clone(),
            ),
            Pbigintcomp(cmp) => self.compile_bigint_comparison(
                *cmp,
                compiled_args[0].clone(),
                compiled_args[1].clone(),
            ),
            Pjscomp(cmp) => {
                compile_raw_comparison(*cmp, compiled_args[0].clone(), compiled_args[1].clone())
            }
            Pstringcomp(cmp) => self.compile_string_comparison(
                *cmp,
                compiled_args[0].clone(),
                compiled_args[1].clone(),
            ),
            Pobjorder => self.runtime_call_expr("Primitive_object", "compare", compiled_args),
            Pobjmin => self.runtime_call_expr("Primitive_object", "min", compiled_args),
            Pobjmax => self.runtime_call_expr("Primitive_object", "max", compiled_args),
            Pobjtag => Expression::new(ExpressionDesc::CamlBlockTag(
                Box::new(compiled_args[0].clone()),
                "TAG".to_string(),
            )),
            // OCaml js_exp_make.ml:1374-1375 wraps Caml_block length in
            // to_int32, unlike array/string/function length.
            Pobjsize => to_int32(Expression::length(
                compiled_args[0].clone(),
                LengthObject::CamlBlock,
            )),
            Pboolorder => match (
                bool_literal(&compiled_args[0]),
                bool_literal(&compiled_args[1]),
            ) {
                (Some(left), Some(right)) => {
                    let result = match left.cmp(&right) {
                        std::cmp::Ordering::Less => -1,
                        std::cmp::Ordering::Equal => 0,
                        std::cmp::Ordering::Greater => 1,
                    };
                    int_expr(result)
                }
                _ => self.runtime_call_expr("Primitive_bool", "compare", compiled_args),
            },
            Pboolmin => self.compile_typed_min_max(
                "Primitive_bool",
                "min",
                Comparison::Lt,
                compiled_args[0].clone(),
                compiled_args[1].clone(),
                both_bool_literals,
            ),
            Pboolmax => self.compile_typed_min_max(
                "Primitive_bool",
                "max",
                Comparison::Gt,
                compiled_args[0].clone(),
                compiled_args[1].clone(),
                both_bool_literals,
            ),
            Pintorder => self.runtime_call_expr("Primitive_int", "compare", compiled_args),
            Pintmin => self.compile_typed_min_max(
                "Primitive_int",
                "min",
                Comparison::Lt,
                compiled_args[0].clone(),
                compiled_args[1].clone(),
                both_int_literals,
            ),
            Pintmax => self.compile_typed_min_max(
                "Primitive_int",
                "max",
                Comparison::Gt,
                compiled_args[0].clone(),
                compiled_args[1].clone(),
                both_int_literals,
            ),
            Pfloatorder => self.runtime_call_expr("Primitive_float", "compare", compiled_args),
            Pfloatmin => self.compile_typed_min_max(
                "Primitive_float",
                "min",
                Comparison::Lt,
                compiled_args[0].clone(),
                compiled_args[1].clone(),
                both_float_literals,
            ),
            Pfloatmax => self.compile_typed_min_max(
                "Primitive_float",
                "max",
                Comparison::Gt,
                compiled_args[0].clone(),
                compiled_args[1].clone(),
                both_float_literals,
            ),
            Pbigintorder => self.runtime_call_expr("Primitive_bigint", "compare", compiled_args),
            Pbigintmin => self.compile_typed_min_max(
                "Primitive_bigint",
                "min",
                Comparison::Lt,
                compiled_args[0].clone(),
                compiled_args[1].clone(),
                both_bigint_literals,
            ),
            Pbigintmax => self.compile_typed_min_max(
                "Primitive_bigint",
                "max",
                Comparison::Gt,
                compiled_args[0].clone(),
                compiled_args[1].clone(),
                both_bigint_literals,
            ),
            Pstringorder => self.runtime_call_expr("Primitive_string", "compare", compiled_args),
            Pstringmin => self.compile_typed_min_max(
                "Primitive_string",
                "min",
                Comparison::Lt,
                compiled_args[0].clone(),
                compiled_args[1].clone(),
                both_string_literals,
            ),
            Pstringmax => self.compile_typed_min_max(
                "Primitive_string",
                "max",
                Comparison::Gt,
                compiled_args[0].clone(),
                compiled_args[1].clone(),
                both_string_literals,
            ),
            Phash => self.runtime_call_expr("Primitive_hash", "hash", compiled_args),
            PhashMixint => self.runtime_call_expr("Primitive_hash", "hash_mix_int", compiled_args),
            PhashMixstring => {
                self.runtime_call_expr("Primitive_hash", "hash_mix_string", compiled_args)
            }
            PhashFinalmix => {
                self.runtime_call_expr("Primitive_hash", "hash_final_mix", compiled_args)
            }
            Psequand => Expression::bin(
                BinOp::And,
                compiled_args[0].clone(),
                compiled_args[1].clone(),
            ),
            Psequor => Expression::bin(
                BinOp::Or,
                compiled_args[0].clone(),
                compiled_args[1].clone(),
            ),
            Pnot => Expression::not(compiled_args[0].clone()),
            Pnegint => int32_minus(int_expr(0), compiled_args[0].clone()),
            // `Pnegfloat` must emit `0. - x` (not `0 - x`) so the printer
            // rule at `js_dump.ml` / `printer.rs:1520-1531` produces `- x`
            // with the OCaml-style space. Mirrors
            // `lam_compile_primitive.ml:179`: `E.float_minus E.zero_float_lit`.
            Pnegfloat => Expression::bin(
                BinOp::Minus,
                Expression::number(Number::float("0.")),
                compiled_args[0].clone(),
            ),
            Pnegbigint => Expression::bin(
                BinOp::Minus,
                Expression::number(Number::bigint(true, "0")),
                compiled_args[0].clone(),
            ),
            Pnotint => int_bnot(compiled_args[0].clone()),
            Pnotbigint => int_bnot(compiled_args[0].clone()),
            Pandint => int32_band(compiled_args[0].clone(), compiled_args[1].clone()),
            Pandbigint => Expression::bin(
                BinOp::Band,
                compiled_args[0].clone(),
                compiled_args[1].clone(),
            ),
            Porint => int32_bor(compiled_args[0].clone(), compiled_args[1].clone()),
            Porbigint => Expression::bin(
                BinOp::Bor,
                compiled_args[0].clone(),
                compiled_args[1].clone(),
            ),
            Pxorint => int32_bxor(compiled_args[0].clone(), compiled_args[1].clone()),
            Pxorbigint => Expression::bin(
                BinOp::Bxor,
                compiled_args[0].clone(),
                compiled_args[1].clone(),
            ),
            Plslint => int32_lsl(compiled_args[0].clone(), compiled_args[1].clone()),
            Plslbigint => Expression::bin(
                BinOp::Lsl,
                compiled_args[0].clone(),
                compiled_args[1].clone(),
            ),
            Plsrint => {
                // OCaml `Plsrint` returns the left operand directly for a
                // literal zero shift, otherwise wraps the logical shift in
                // `to_int32` (`compiler/core/lam_compile_primitive.ml:264-267`).
                if is_zero_int(&compiled_args[1]) {
                    compiled_args[0].clone()
                } else {
                    to_int32(int32_lsr(
                        compiled_args[0].clone(),
                        compiled_args[1].clone(),
                    ))
                }
            }
            Pasrint => Expression::bin(
                BinOp::Asr,
                compiled_args[0].clone(),
                compiled_args[1].clone(),
            ),
            Pasrbigint => Expression::bin(
                BinOp::Asr,
                compiled_args[0].clone(),
                compiled_args[1].clone(),
            ),
            Poffsetint(offset) => int32_offset(compiled_args[0].clone(), *offset),
            Poffsetref(offset) => {
                // OCaml lowers through `Js_of_lam_block.field
                // Lambda.ref_field_info`, so the `contents` access keeps
                // record field position metadata
                // (compiler/core/lam_compile_primitive.ml:342-348).
                let field = self.compile_field_access(
                    0,
                    &FieldDbgInfo::Record {
                        name: "contents".to_string(),
                    },
                    &compiled_args[0],
                );
                Expression::new(ExpressionDesc::Seq(
                    Box::new(Expression::bin(
                        BinOp::Eq,
                        field.clone(),
                        int32_offset(field, *offset),
                    )),
                    Box::new(Expression::undefined(false)),
                ))
            }
            Pisint => is_type_number_expr(compiled_args[0].clone()),
            PisPolyVarBlock => is_type_object_expr(compiled_args[0].clone()),
            Pisout(offset) => match compiled_args.as_slice() {
                [range, value] => is_out_expr(int32_offset(value.clone(), *offset), range.clone()),
                _ => Expression::undefined(false),
            },
            Pmakearray => Expression::array(compiled_args, MutableFlag::Mutable),
            Pmakedict => match compiled_args.as_slice() {
                [
                    Expression {
                        desc: ExpressionDesc::Array(items, _),
                        ..
                    },
                ] => {
                    let props = items
                        .iter()
                        .filter_map(|item| match &item.desc {
                            ExpressionDesc::CamlBlock(fields, _, _, _)
                                if matches!(
                                    fields.as_slice(),
                                    [
                                        Expression {
                                            desc: ExpressionDesc::Str { .. },
                                            ..
                                        },
                                        _
                                    ]
                                ) =>
                            {
                                let [
                                    Expression {
                                        desc: ExpressionDesc::Str { txt, .. },
                                        ..
                                    },
                                    value,
                                ] = fields.as_slice()
                                else {
                                    unreachable!("checked by matches! above");
                                };
                                Some((PropertyName::lit(txt.clone()), value.clone()))
                            }
                            _ => None,
                        })
                        .collect();
                    Expression::new(ExpressionDesc::Object(None, props))
                }
                _ => Expression::undefined(false),
            },
            PdictHas => match compiled_args.as_slice() {
                [obj, prop] => Expression::new(ExpressionDesc::In(
                    Box::new(prop.clone()),
                    Box::new(obj.clone()),
                )),
                _ => {
                    self.report_diagnostic(
                        loc,
                        "Invalid external \"%dict_has\" type signature. Expected to have two arguments.",
                    );
                    Expression::undefined(false)
                }
            },
            Pduprecord => match compiled_args.as_slice() {
                [source] => Expression::new(ExpressionDesc::Object(
                    Some(Box::new(source.clone())),
                    vec![],
                )),
                _ => Expression::undefined(false),
            },
            PrecordRest(excluded) => match compiled_args.as_slice() {
                [source] => Expression::new(ExpressionDesc::RecordRest(
                    excluded
                        .iter()
                        .map(|label| crate::js_ir::RecordRestField {
                            label: label.clone(),
                            ident: None,
                        })
                        .collect(),
                    Box::new(source.clone()),
                )),
                _ => Expression::undefined(false),
            },
            Pstringadd => {
                Expression::string_append(compiled_args[0].clone(), compiled_args[1].clone())
            }
            PinitMod => self.runtime_call_expr("Primitive_module", "init", compiled_args),
            PupdateMod => self.runtime_call_expr("Primitive_module", "update", compiled_args),
            PnullToOpt => self.null_to_opt_expr(compiled_args[0].clone()),
            PnullUndefinedToOpt => self.null_undefined_to_opt_expr(compiled_args[0].clone()),
            PisNotNone => self.is_not_none_expr(compiled_args[0].clone()),
            PisNull => self.is_null_expr(compiled_args[0].clone()),
            PisUndefined => self.is_undefined_expr(compiled_args[0].clone()),
            PisNullUndefined => self.is_null_or_undefined_expr(compiled_args[0].clone()),
            PvalFromOption => self.val_from_option_expr(compiled_args[0].clone()),
            PvalFromOptionNotNest => compiled_args[0].clone(),
            Psome => self.some_expr(compiled_args[0].clone()),
            PsomeNotNest => self.optional_block(compiled_args[0].clone(), true),
            Pfield(idx, info) => self.compile_field_access(*idx, info, &compiled_args[0]),
            Psetfield(idx, info) => {
                let target =
                    self.compile_set_field(*idx, info, &compiled_args[0], &compiled_args[1]);
                Expression::new(ExpressionDesc::Seq(
                    Box::new(target),
                    Box::new(Expression::undefined(false)),
                ))
            }
            Pmakeblock(tag, tag_info, mutable_flag) => {
                let js_mutable = match mutable_flag {
                    Mutable::Mutable => MutableFlag::Mutable,
                    Mutable::Immutable => MutableFlag::Immutable,
                };
                Expression::new(ExpressionDesc::CamlBlock(
                    compiled_args,
                    js_mutable,
                    Box::new(Expression::number(Number::int(*tag))),
                    tag_info.clone(),
                ))
            }
            // OCaml lam_compile_primitive.ml:560-564 builds the mutable list
            // constructor block used by the runtime.
            Pmakelist => Expression::new(ExpressionDesc::CamlBlock(
                compiled_args,
                MutableFlag::Mutable,
                Box::new(Expression::number(Number::int(0))),
                TagInfo::constructor("::", 1, 0),
            )),
            PrawJsCode(info) => {
                Expression::new(ExpressionDesc::RawJsCode(crate::js_ir::JsRawInfo {
                    code: info.code.trim().to_string(),
                    is_stmt: info.is_stmt,
                }))
            }
            Pdebugger => {
                let mut statement = Statement::debugger();
                statement.source_loc = self.source_loc(loc);
                prelude.push(statement);
                Expression::undefined(false)
            }
            Praise => {
                let expr = compiled_args
                    .first()
                    .cloned()
                    .unwrap_or_else(|| Expression::undefined(false));
                let mut statement = Statement::throw(expr);
                statement.source_loc = self.source_loc(loc);
                prelude.push(statement);
                Expression::undefined(false)
            }
            Pidentity => compiled_args
                .first()
                .cloned()
                .unwrap_or_else(|| Expression::undefined(false)),
            Pignore => Expression::new(ExpressionDesc::Seq(
                Box::new(
                    compiled_args
                        .first()
                        .cloned()
                        .unwrap_or_else(|| Expression::undefined(false)),
                ),
                Box::new(Expression::undefined(true)),
            )),
            Ptypeof => ocaml_typeof_expr(compiled_args[0].clone()),
            Pintoffloat => to_int32(compiled_args[0].clone()),
            Pfloatofint => compiled_args
                .first()
                .cloned()
                .unwrap_or_else(|| Expression::undefined(false)),
            Pawait => Expression::new(ExpressionDesc::Await(Box::new(compiled_args[0].clone()))),
            PwrapExn => {
                self.runtime_call_expr("Primitive_exceptions", "internalToException", compiled_args)
            }
            PcreateExtension(name) => self.pure_runtime_call_expr(
                "Primitive_exceptions",
                "create",
                vec![Expression::string(name.clone())],
            ),
            PjsObjectCreate(obj_params) => {
                self.compile_js_object_create(obj_params, compiled_args, &mut prelude)
            }
            PjsFnMethod => match compiled_args.first().cloned() {
                Some(Expression {
                    source_loc,
                    desc:
                        ExpressionDesc::Fun {
                            params,
                            body,
                            env,
                            return_unit,
                            async_,
                            directive,
                            ..
                        },
                    comment,
                }) => Expression {
                    source_loc: None,
                    desc: ExpressionDesc::Fun {
                        is_method: true,
                        params,
                        body,
                        env,
                        return_unit,
                        async_,
                        directive,
                    },
                    comment,
                },
                Some(expr) => expr,
                None => Expression::undefined(false),
            },
            PjsUnsafeDowngrade { name, setter } => match (*setter, compiled_args.as_slice()) {
                (false, [receiver]) => self.static_index(receiver.clone(), name),
                (true, [receiver, value]) => Expression::new(ExpressionDesc::Seq(
                    Box::new(Expression::bin(
                        BinOp::Eq,
                        self.static_index(receiver.clone(), name),
                        value.clone(),
                    )),
                    Box::new(Expression::undefined(true)),
                )),
                _ => Expression::undefined(false),
            },
            Pimport => self.compile_import(loc, compiled_args),
            PjsCall {
                prim_name,
                arg_types,
                ffi,
                dynamic_import,
                transformed_jsx,
            } => self.compile_js_call(
                loc,
                prim_name,
                arg_types,
                ffi,
                *dynamic_import,
                *transformed_jsx,
                compiled_args,
                &mut prelude,
            ),
            Pnull => Expression::null(),
            Pundefined => Expression::undefined(false),
            _ => Expression::undefined(false),
        };

        Compiled { prelude, expr }
    }

    fn compile_object_comparison(
        &self,
        cmp: Comparison,
        left: Expression,
        right: Expression,
    ) -> Expression {
        match cmp {
            Comparison::Eq | Comparison::Neq
                if is_nullish_literal(&left).is_some() || is_nullish_literal(&right).is_some() =>
            {
                compile_nullish_strict_comparison(cmp, left, right)
            }
            _ => self.runtime_call_expr(
                "Primitive_object",
                comparison_to_runtime_member(cmp),
                vec![left, right],
            ),
        }
    }

    fn compile_bool_comparison(
        &self,
        cmp: Comparison,
        left: Expression,
        right: Expression,
    ) -> Expression {
        match (bool_literal(&left), bool_literal(&right)) {
            (Some(lhs), Some(rhs)) => Expression::bool(compare_bool_literals(cmp, lhs, rhs)),
            (Some(true), _) | (_, Some(false)) => match cmp {
                Comparison::Lt => js_seq(
                    if matches!(bool_literal(&left), Some(true)) {
                        right
                    } else {
                        left
                    },
                    Expression::bool(false),
                ),
                Comparison::Ge => js_seq(
                    if matches!(bool_literal(&left), Some(true)) {
                        right
                    } else {
                        left
                    },
                    Expression::bool(true),
                ),
                Comparison::Eq | Comparison::Neq | Comparison::Le | Comparison::Gt => {
                    compile_raw_comparison(cmp, left, right)
                }
            },
            (_, Some(true)) | (Some(false), _) => match cmp {
                Comparison::Le => js_seq(
                    if matches!(bool_literal(&right), Some(true)) {
                        left
                    } else {
                        right
                    },
                    Expression::bool(true),
                ),
                Comparison::Gt => js_seq(
                    if matches!(bool_literal(&right), Some(true)) {
                        left
                    } else {
                        right
                    },
                    Expression::bool(false),
                ),
                Comparison::Eq | Comparison::Neq | Comparison::Lt | Comparison::Ge => {
                    compile_raw_comparison(cmp, left, right)
                }
            },
            _ => compile_raw_comparison(cmp, left, right),
        }
    }

    fn compile_int_comparison(
        &self,
        cmp: Comparison,
        left: Expression,
        right: Expression,
    ) -> Expression {
        if let (Some(lhs), Some(rhs)) = (int_literal(&left), int_literal(&right)) {
            return Expression::bool(compare_int_literals(cmp, lhs, rhs));
        }

        // OCaml's Js_exp_make.int_comp strips Runtime.compare(..., ...) when
        // the RHS is the integer literal 0, so compare(x, y) > 0 lowers to x > y.
        if int_literal(&right) == Some(0) {
            if let Some((compare_left, compare_right)) = runtime_compare_call_args(&left) {
                return self.compile_int_comparison(
                    cmp,
                    compare_left.clone(),
                    compare_right.clone(),
                );
            }
        }

        match cmp {
            Comparison::Eq => {
                if ((is_optional_block(&left)
                    && matches!(&right.desc, ExpressionDesc::Undefined { .. }))
                    || (matches!(&left.desc, ExpressionDesc::Undefined { .. })
                        && is_optional_block(&right)))
                    && js_expr_no_side_effects(&left)
                    && js_expr_no_side_effects(&right)
                {
                    return Expression::bool(false);
                }

                compile_int_equality(left, right)
            }
            Comparison::Neq => {
                if ((is_optional_block(&left)
                    && matches!(&right.desc, ExpressionDesc::Undefined { .. }))
                    || (matches!(&left.desc, ExpressionDesc::Undefined { .. })
                        && is_optional_block(&right))
                    || (matches!(&left.desc, ExpressionDesc::CamlBlock(_, _, _, _))
                        && matches!(&right.desc, ExpressionDesc::Number(_)))
                    || (matches!(&left.desc, ExpressionDesc::Number(_))
                        && matches!(&right.desc, ExpressionDesc::CamlBlock(_, _, _, _))))
                    && js_expr_no_side_effects(&left)
                    && js_expr_no_side_effects(&right)
                {
                    return Expression::bool(true);
                }

                // OCaml's `Js_exp_make.int_comp` falls through to
                // `bin NotEqEq e0 e1` for the non-special Cneq cases — and
                // OCaml's `bin` has no NotEqEq case, so the construction is
                // effectively raw. `Expression::bin`'s `fold_strict_comparison`
                // would fold `3 !== null` to `true` via the nullish-impossible
                // rule, diverging from OCaml. Use a raw `Bin` here.
                crate::js_ir::raw_bin_expression(comparison_to_binop(cmp), left, right)
            }
            Comparison::Lt | Comparison::Le | Comparison::Gt | Comparison::Ge => {
                compile_raw_comparison(cmp, left, right)
            }
        }
    }

    fn compile_string_comparison(
        &self,
        cmp: Comparison,
        left: Expression,
        right: Expression,
    ) -> Expression {
        match compare_string_literals(&left, &right) {
            Some(equal) => match cmp {
                Comparison::Eq => Expression::bool(equal),
                Comparison::Neq => Expression::bool(!equal),
                Comparison::Lt | Comparison::Le | Comparison::Gt | Comparison::Ge => {
                    compile_raw_comparison(cmp, left, right)
                }
            },
            None => compile_raw_comparison(cmp, left, right),
        }
    }

    fn compile_bigint_comparison(
        &self,
        cmp: Comparison,
        left: Expression,
        right: Expression,
    ) -> Expression {
        match compare_bigint_literals(&left, &right) {
            Some(equal) => match cmp {
                Comparison::Eq => Expression::bool(equal),
                Comparison::Neq => Expression::bool(!equal),
                Comparison::Lt | Comparison::Le | Comparison::Gt | Comparison::Ge => {
                    compile_raw_comparison(cmp, left, right)
                }
            },
            None => compile_raw_comparison(cmp, left, right),
        }
    }

    fn compile_typed_min_max(
        &self,
        module_name: &str,
        member: &str,
        compare: Comparison,
        left: Expression,
        right: Expression,
        literal_fast_path: fn(&Expression, &Expression) -> bool,
    ) -> Expression {
        if literal_fast_path(&left, &right) {
            Expression::cond(
                Expression::bin(comparison_to_binop(compare), left.clone(), right.clone()),
                left,
                right,
            )
        } else {
            self.runtime_call_expr(module_name, member, vec![left, right])
        }
    }
}
