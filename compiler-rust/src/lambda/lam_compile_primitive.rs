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
    is_type_number_expr, is_type_object_expr, is_zero_int, js_expr_no_side_effects,
    js_seq, ocaml_typeof_expr, poly_var_tag_access, poly_var_value_access,
    runtime_compare_call_args, runtime_member_for_eta_wrapped_primitive, to_int32,
};
use super::lam_compile::{Compiled, LambdaCompiler, call_info_of_apply_status};
use super::lam_compile_input::{LambdaInputView, LambdaInputs};
use crate::ident::Ident;
use crate::js_ir::op::{LengthObject, MutableFlag, Number, PropertyName};
use crate::js_ir::{
    BinOp, Block, CallInfo, Expression, ExpressionDesc, Statement, StatementDesc, VIdent,
    VariableDeclaration,
};
use crate::lambda::lam_compat::{Comparison, FieldDbgInfo, LetKind, SetFieldDbgInfo};
use crate::lambda::lam_constant::Constant;
use crate::lambda::lam_primitive::{Mutable, Primitive};
use crate::lambda::{Lambda, TagInfo};
use crate::location::Location;

impl LambdaCompiler {
    pub(crate) fn compile_primitive(
        &mut self,
        prim: &Primitive,
        args: &[Lambda],
        loc: &Location,
    ) -> Compiled {
        if let Some(compiled) =
            self.compile_hoisted_external_field(prim, LambdaInputs::Recursive(args))
        {
            return compiled;
        }

        let mut prelude = vec![];
        let mut compiled_args = Vec::new();
        for arg in args {
            let compiled = self.compile_expr(arg);
            prelude.extend(compiled.prelude);
            compiled_args.push(compiled.expr);
        }
        self.compile_primitive_js(prim, compiled_args, prelude, loc)
    }

    /// Descriptor lookup happens before argument compilation, as in
    /// compiler/core/lam_compile.ml:284-302 and 1734-1757. The cursor is used
    /// only during this read; no store borrow crosses recursive compilation.
    pub(crate) fn compile_hoisted_external_field(
        &mut self,
        prim: &Primitive,
        args: LambdaInputs<'_>,
    ) -> Option<Compiled> {
        fn external_field_path<'a>(
            prim: &'a Primitive,
            args: LambdaInputs<'a>,
            segments: &mut Vec<String>,
        ) -> Option<&'a Ident> {
            let Primitive::Pfield(_, FieldDbgInfo::Module { name }) = prim else {
                return None;
            };
            segments.push(name.clone());
            if args.len() != 1 {
                return None;
            }
            match args.first()?.view() {
                LambdaInputView::GlobalModule(id) => Some(id),
                LambdaInputView::Prim(prim, args, _) => external_field_path(prim, args, segments),
                _ => None,
            }
        }
        let mut reversed = Vec::new();
        let id = external_field_path(prim, args, &mut reversed)?;
        if reversed.len() < 2 {
            return None;
        }
        reversed.reverse();
        let export_name = self
            .module_path_resolver
            .as_ref()?
            .module_cmj_hoisted_export(id.name(), &reversed)?;
        Some(Compiled {
            prelude: Vec::new(),
            expr: Expression::qualified(
                crate::js_ir::ModuleId {
                    id: id.clone(),
                    kind: crate::js_ir::Kind::Ml,
                    dynamic_import: false,
                },
                Some(export_name),
            ),
        })
    }

    /// Lower already-compiled arguments. The recursive or indexed caller owns
    /// traversal and releases Lambda-store borrows before invoking this helper.
    /// This is the Js_of_lam_primitive boundary in
    /// compiler/core/lam_compile_primitive.ml, not a Lambda compatibility step.
    pub(crate) fn compile_primitive_js(
        &mut self,
        prim: &Primitive,
        mut compiled_args: Vec<Expression>,
        mut prelude: Block,
        loc: &Location,
    ) -> Compiled {
        use Primitive::*;
        let expr = match prim {
            Pstringlength => {
                Expression::length(take_arg(&mut compiled_args, 0), LengthObject::String)
            }
            Parraylength => {
                Expression::length(take_arg(&mut compiled_args, 0), LengthObject::Array)
            }
            // lam_compile_primitive.ml `Ptagged_template strings`:
            // `[tag; value0; ...]` plus raw source segments -> tag`...`.
            PtaggedTemplate(strings) => {
                let mut args = std::mem::take(&mut compiled_args).into_iter();
                let tag = args.next().expect("a tagged template has a tag");
                Expression::new(ExpressionDesc::TaggedTemplate(Box::new(tag), strings.clone(), args.collect()))
            }
            // `Ptemplate [segment] when args = []` / `Ptemplate segments`.
            Ptemplate(segments) if segments.len() == 1 && compiled_args.is_empty() => {
                Expression::new(ExpressionDesc::TemplateLiteral(segments[0].clone()))
            }
            Ptemplate(segments) => {
                crate::lambda::js_exp_make::interpolated_template(segments.clone(), std::mem::take(&mut compiled_args))
            }
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
            Paddint => int32_add(
                take_arg(&mut compiled_args, 0),
                take_arg(&mut compiled_args, 1),
            ),
            Paddfloat => Expression::bin(
                BinOp::Plus,
                take_arg(&mut compiled_args, 0),
                take_arg(&mut compiled_args, 1),
            ),
            Paddbigint => Expression::bin(
                BinOp::Plus,
                take_arg(&mut compiled_args, 0),
                take_arg(&mut compiled_args, 1),
            ),
            Psubint => int32_minus(
                take_arg(&mut compiled_args, 0),
                take_arg(&mut compiled_args, 1),
            ),
            Psubfloat => Expression::bin(
                BinOp::Minus,
                take_arg(&mut compiled_args, 0),
                take_arg(&mut compiled_args, 1),
            ),
            Psubbigint => Expression::bin(
                BinOp::Minus,
                take_arg(&mut compiled_args, 0),
                take_arg(&mut compiled_args, 1),
            ),
            Pmulint => int32_mul(
                take_arg(&mut compiled_args, 0),
                take_arg(&mut compiled_args, 1),
            ),
            Pmulfloat => Expression::bin(
                BinOp::Mul,
                take_arg(&mut compiled_args, 0),
                take_arg(&mut compiled_args, 1),
            ),
            Pmulbigint => Expression::bin(
                BinOp::Mul,
                take_arg(&mut compiled_args, 0),
                take_arg(&mut compiled_args, 1),
            ),
            Pdivint => self.int32_div_expr(
                take_arg(&mut compiled_args, 0),
                take_arg(&mut compiled_args, 1),
            ),
            Pdivfloat => Expression::bin(
                BinOp::Div,
                take_arg(&mut compiled_args, 0),
                take_arg(&mut compiled_args, 1),
            ),
            Pdivbigint => self.bigint_div_expr(
                take_arg(&mut compiled_args, 0),
                take_arg(&mut compiled_args, 1),
            ),
            Pmodint => self.int32_mod_expr(
                take_arg(&mut compiled_args, 0),
                take_arg(&mut compiled_args, 1),
            ),
            Pmodfloat => Expression::bin(
                BinOp::Mod,
                take_arg(&mut compiled_args, 0),
                take_arg(&mut compiled_args, 1),
            ),
            Pmodbigint => self.bigint_mod_expr(
                take_arg(&mut compiled_args, 0),
                take_arg(&mut compiled_args, 1),
            ),
            Ppowint => int32_pow(
                take_arg(&mut compiled_args, 0),
                take_arg(&mut compiled_args, 1),
            ),
            Ppowfloat => Expression::bin(
                BinOp::Pow,
                take_arg(&mut compiled_args, 0),
                take_arg(&mut compiled_args, 1),
            ),
            Ppowbigint => Expression::bin(
                BinOp::Pow,
                take_arg(&mut compiled_args, 0),
                take_arg(&mut compiled_args, 1),
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
            Pintcomp(cmp) | Pfloatcomp(cmp) => self.compile_int_comparison(
                *cmp,
                take_arg(&mut compiled_args, 0),
                take_arg(&mut compiled_args, 1),
            ),
            Pbigintcomp(cmp) => self.compile_bigint_comparison(
                *cmp,
                take_arg(&mut compiled_args, 0),
                take_arg(&mut compiled_args, 1),
            ),
            Pjscomp(cmp) => compile_raw_comparison(
                *cmp,
                take_arg(&mut compiled_args, 0),
                take_arg(&mut compiled_args, 1),
            ),
            Pstringcomp(cmp) => self.compile_string_comparison(
                *cmp,
                take_arg(&mut compiled_args, 0),
                take_arg(&mut compiled_args, 1),
            ),
            Pobjorder => self.runtime_call_expr("Primitive_object", "compare", compiled_args),
            Pobjmin => self.runtime_call_expr("Primitive_object", "min", compiled_args),
            Pobjmax => self.runtime_call_expr("Primitive_object", "max", compiled_args),
            Pobjtag => Expression::new(ExpressionDesc::CamlBlockTag(
                Box::new(take_arg(&mut compiled_args, 0)),
                "TAG".to_string(),
            )),
            // OCaml js_exp_make.ml:1374-1375 wraps Caml_block length in
            // to_int32, unlike array/string/function length.
            Pobjsize => to_int32(Expression::length(
                take_arg(&mut compiled_args, 0),
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
                take_arg(&mut compiled_args, 0),
                take_arg(&mut compiled_args, 1),
                both_bool_literals,
            ),
            Pboolmax => self.compile_typed_min_max(
                "Primitive_bool",
                "max",
                Comparison::Gt,
                take_arg(&mut compiled_args, 0),
                take_arg(&mut compiled_args, 1),
                both_bool_literals,
            ),
            Pintorder => self.runtime_call_expr("Primitive_int", "compare", compiled_args),
            Pintmin => self.compile_typed_min_max(
                "Primitive_int",
                "min",
                Comparison::Lt,
                take_arg(&mut compiled_args, 0),
                take_arg(&mut compiled_args, 1),
                both_int_literals,
            ),
            Pintmax => self.compile_typed_min_max(
                "Primitive_int",
                "max",
                Comparison::Gt,
                take_arg(&mut compiled_args, 0),
                take_arg(&mut compiled_args, 1),
                both_int_literals,
            ),
            Pfloatorder => self.runtime_call_expr("Primitive_float", "compare", compiled_args),
            Pfloatmin => self.compile_typed_min_max(
                "Primitive_float",
                "min",
                Comparison::Lt,
                take_arg(&mut compiled_args, 0),
                take_arg(&mut compiled_args, 1),
                both_float_literals,
            ),
            Pfloatmax => self.compile_typed_min_max(
                "Primitive_float",
                "max",
                Comparison::Gt,
                take_arg(&mut compiled_args, 0),
                take_arg(&mut compiled_args, 1),
                both_float_literals,
            ),
            Pbigintorder => self.runtime_call_expr("Primitive_bigint", "compare", compiled_args),
            Pbigintmin => self.compile_typed_min_max(
                "Primitive_bigint",
                "min",
                Comparison::Lt,
                take_arg(&mut compiled_args, 0),
                take_arg(&mut compiled_args, 1),
                both_bigint_literals,
            ),
            Pbigintmax => self.compile_typed_min_max(
                "Primitive_bigint",
                "max",
                Comparison::Gt,
                take_arg(&mut compiled_args, 0),
                take_arg(&mut compiled_args, 1),
                both_bigint_literals,
            ),
            Pstringorder => self.runtime_call_expr("Primitive_string", "compare", compiled_args),
            Pstringmin => self.compile_typed_min_max(
                "Primitive_string",
                "min",
                Comparison::Lt,
                take_arg(&mut compiled_args, 0),
                take_arg(&mut compiled_args, 1),
                both_string_literals,
            ),
            Pstringmax => self.compile_typed_min_max(
                "Primitive_string",
                "max",
                Comparison::Gt,
                take_arg(&mut compiled_args, 0),
                take_arg(&mut compiled_args, 1),
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
                take_arg(&mut compiled_args, 0),
                take_arg(&mut compiled_args, 1),
            ),
            Psequor => Expression::bin(
                BinOp::Or,
                take_arg(&mut compiled_args, 0),
                take_arg(&mut compiled_args, 1),
            ),
            Pnot => Expression::not(take_arg(&mut compiled_args, 0)),
            Pnegint => int32_minus(int_expr(0), take_arg(&mut compiled_args, 0)),
            // `Pnegfloat` must emit `0. - x` (not `0 - x`) so the printer
            // rule at `js_dump.ml` / `printer.rs:1520-1531` produces `- x`
            // with the OCaml-style space. Mirrors
            // `lam_compile_primitive.ml:179`: `E.float_minus E.zero_float_lit`.
            Pnegfloat => Expression::bin(
                BinOp::Minus,
                Expression::number(Number::float("0.")),
                take_arg(&mut compiled_args, 0),
            ),
            Pnegbigint => Expression::bin(
                BinOp::Minus,
                Expression::number(Number::bigint(true, "0")),
                take_arg(&mut compiled_args, 0),
            ),
            Pnotint => int_bnot(take_arg(&mut compiled_args, 0)),
            Pnotbigint => int_bnot(take_arg(&mut compiled_args, 0)),
            Pandint => int32_band(
                take_arg(&mut compiled_args, 0),
                take_arg(&mut compiled_args, 1),
            ),
            Pandbigint => Expression::bin(
                BinOp::Band,
                take_arg(&mut compiled_args, 0),
                take_arg(&mut compiled_args, 1),
            ),
            Porint => int32_bor(
                take_arg(&mut compiled_args, 0),
                take_arg(&mut compiled_args, 1),
            ),
            Porbigint => Expression::bin(
                BinOp::Bor,
                take_arg(&mut compiled_args, 0),
                take_arg(&mut compiled_args, 1),
            ),
            Pxorint => int32_bxor(
                take_arg(&mut compiled_args, 0),
                take_arg(&mut compiled_args, 1),
            ),
            Pxorbigint => Expression::bin(
                BinOp::Bxor,
                take_arg(&mut compiled_args, 0),
                take_arg(&mut compiled_args, 1),
            ),
            Plslint => int32_lsl(
                take_arg(&mut compiled_args, 0),
                take_arg(&mut compiled_args, 1),
            ),
            Plslbigint => Expression::bin(
                BinOp::Lsl,
                take_arg(&mut compiled_args, 0),
                take_arg(&mut compiled_args, 1),
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
                take_arg(&mut compiled_args, 0),
                take_arg(&mut compiled_args, 1),
            ),
            Pasrbigint => Expression::bin(
                BinOp::Asr,
                take_arg(&mut compiled_args, 0),
                take_arg(&mut compiled_args, 1),
            ),
            Pisint => is_type_number_expr(take_arg(&mut compiled_args, 0)),
            PisPolyVarBlock => is_type_object_expr(take_arg(&mut compiled_args, 0)),
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
                            ExpressionDesc::CamlBlock(fields, _, _)
                                if matches!(
                                    fields.as_slice(),
                                    [
                                        Expression {
                                            desc: ExpressionDesc::Str(_),
                                            ..
                                        },
                                        _
                                    ]
                                ) =>
                            {
                                let [
                                    Expression {
                                        desc: ExpressionDesc::Str(txt),
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
            Pstringadd => Expression::string_append(
                take_arg(&mut compiled_args, 0),
                take_arg(&mut compiled_args, 1),
            ),
            PinitMod => self.runtime_call_expr("Primitive_module", "init", compiled_args),
            PupdateMod => self.runtime_call_expr("Primitive_module", "update", compiled_args),
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
            Pfield(idx, info) => self.compile_field_access(*idx, info, &compiled_args[0]),
            Psetfield(idx, info) => {
                let target =
                    self.compile_set_field(*idx, info, &compiled_args[0], &compiled_args[1]);
                Expression::new(ExpressionDesc::Seq(
                    Box::new(target),
                    Box::new(Expression::undefined(false)),
                ))
            }
            Pmakeblock(tag_info, mutable_flag) => {
                let js_mutable = match mutable_flag {
                    Mutable::Mutable => MutableFlag::Mutable,
                    Mutable::Immutable => MutableFlag::Immutable,
                };
                Expression::new(ExpressionDesc::CamlBlock(
                    compiled_args,
                    js_mutable,
                    Box::new(tag_info.clone()),
                ))
            }
            // OCaml lam_compile_primitive.ml:560-564 builds the mutable list
            // constructor block used by the runtime.
            Pmakelist => Expression::new(ExpressionDesc::CamlBlock(
                compiled_args,
                MutableFlag::Mutable,
                Box::new(TagInfo::constructor("::", 1)),
            )),
            PrawJsCode(info) => {
                Expression::new(ExpressionDesc::RawJsCode(crate::js_ir::JsRawInfo {
                    code: info.code.trim().to_string(),
                    is_stmt: info.is_stmt,
                }))
            }
            Pdebugger => {
                let mut statement = Statement::debugger();
                statement.source_loc = (self.source_loc(loc)).map(Box::new);
                prelude.push(statement);
                Expression::undefined(false)
            }
            Praise => {
                let expr = compiled_args
                    .first()
                    .cloned()
                    .unwrap_or_else(|| Expression::undefined(false));
                let mut statement = Statement::throw(expr);
                statement.source_loc = (self.source_loc(loc)).map(Box::new);
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
            Ptypeof => ocaml_typeof_expr(take_arg(&mut compiled_args, 0)),
            Pintoffloat => to_int32(take_arg(&mut compiled_args, 0)),
            Pfloatofint => compiled_args
                .first()
                .cloned()
                .unwrap_or_else(|| Expression::undefined(false)),
            Pawait => Expression::new(ExpressionDesc::Await(Box::new(take_arg(
                &mut compiled_args,
                0,
            )))),
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
            PjsObjectGet(name) | PjsObjectSet(name) => match (
                matches!(prim, PjsObjectSet(_)),
                compiled_args.as_slice(),
            ) {
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
            Pimport(source) => self.compile_import(loc, source),
            PjsCall {
                prim_name,
                arg_types,
                ffi,
                transformed_jsx,
            } => self.compile_js_call(prim_name, arg_types, ffi, *transformed_jsx, compiled_args),
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
                    || (matches!(&left.desc, ExpressionDesc::CamlBlock(_, _, _))
                        && matches!(&right.desc, ExpressionDesc::Number(_)))
                    || (matches!(&left.desc, ExpressionDesc::Number(_))
                        && matches!(&right.desc, ExpressionDesc::CamlBlock(_, _, _))))
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

/// Move argument `index` out of `args`, which the calling arm uses once.
fn take_arg(args: &mut [Expression], index: usize) -> Expression {
    std::mem::replace(&mut args[index], Expression::undefined(false))
}
