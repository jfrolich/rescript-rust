//! Lambda -> JS IR compilation.
//!
//! This module provides a straightforward lowering from Lambda IR into the
//! JavaScript IR used by the Rust compiler backend. The implementation favors
//! clarity over aggressive optimization; it is intended as a correct baseline
//! that can be extended with more advanced codegen passes.

use std::collections::HashSet;

use crate::context::IdGenerator;
use crate::ident::Ident;
use crate::js_ir::op::{
    IdentInfo, ImportAttributes as JsImportAttributes, Kind, LengthObject, MutableFlag, Number,
    PropertyName,
};
use crate::js_ir::printer::is_js_keyword_or_global;
use crate::js_ir::{
    BinOp, Block, CallInfo, CaseClause, Delim, DepsProgram, Expression, ExpressionDesc,
    ForDirection, ModuleId, ModulePathResolver, Program, Statement, StatementDesc, StringClause,
    VariableDeclaration,
};
use crate::lambda::analysis;
use crate::lambda::compat::{Comparison, FieldDbgInfo, LetKind};
use crate::lambda::constant::{Constant, StringDelim};
use crate::lambda::primitive::{
    ExternalArgAttr, ExternalArgConst, ExternalArgDelim, ExternalArgLabel, ExternalArgSpec,
    ExternalModuleBindName, ExternalModuleName, ExternalObjLabel, ExternalObjSpec, ExternalSpec,
    Mutable, Primitive,
};
use crate::lambda::{Apply, Lambda, LambdaSwitch, TagInfo};

/// Compilation result for an expression: prelude statements plus a value expression.
#[derive(Debug, Clone)]
struct Compiled {
    prelude: Block,
    expr: Expression,
}

/// Lambda compiler to JS IR.
pub struct LambdaCompiler {
    id_gen: IdGenerator,
    module_path_resolver: Option<ModulePathResolver>,
}

impl Default for LambdaCompiler {
    fn default() -> Self {
        Self::new()
    }
}

impl LambdaCompiler {
    /// Create a new compiler.
    pub fn new() -> Self {
        Self {
            id_gen: IdGenerator::new(),
            module_path_resolver: None,
        }
    }

    /// Create a compiler with module import resolution context.
    pub fn with_module_path_resolver(module_path_resolver: Option<ModulePathResolver>) -> Self {
        Self {
            id_gen: IdGenerator::new(),
            module_path_resolver,
        }
    }

    /// Compile a Lambda expression into a JS IR program.
    pub fn compile_program(&mut self, lam: &Lambda) -> Program {
        self.compile_deps_program(lam).program
    }

    /// Compile a Lambda expression into a JS IR program with module metadata.
    pub fn compile_deps_program(&mut self, lam: &Lambda) -> DepsProgram {
        let simplified = crate::lambda::simplify::simplify_for_js_backend(lam);
        let compiled = self.compile_expr(&simplified);
        let mut block = compiled.prelude;
        let exports = match compiled.expr.desc {
            ExpressionDesc::CamlBlock(_, _, _, TagInfo::ModuleExport(exports)) => exports,
            ExpressionDesc::Undefined { .. } => vec![],
            _ => {
                push_effect_expression(&mut block, compiled.expr);
                vec![]
            }
        };

        let mut deps = apply_external_shadow_pass(apply_js_flatten_pass(DepsProgram {
            program: Program::new(block, exports),
            modules: vec![],
            side_effect: module_side_effect_reason(&simplified),
        }));
        deps.modules = self.collect_required_modules(&deps.program.block);
        deps
    }

    fn compile_expr(&mut self, lam: &Lambda) -> Compiled {
        match lam {
            Lambda::Lvar(id) => Compiled {
                prelude: vec![],
                expr: Expression::var(id.clone()),
            },
            Lambda::LglobalModule(id, dynamic_import) => {
                let module = ModuleId {
                    id: id.clone(),
                    kind: Kind::Ml,
                    dynamic_import: *dynamic_import,
                };
                Compiled {
                    prelude: vec![],
                    expr: Expression::qualified(module, None),
                }
            }
            Lambda::Lconst(cst) => Compiled {
                prelude: vec![],
                expr: Self::compile_constant(cst),
            },
            Lambda::Lapply(Apply {
                ap_func,
                ap_args,
                ap_info: _,
                ap_transformed_jsx: _,
            }) => {
                let mut prelude = vec![];
                let func = self.compile_expr(ap_func);
                prelude.extend(func.prelude);
                let mut args = Vec::new();
                for arg in ap_args {
                    let compiled = self.compile_expr(arg);
                    prelude.extend(compiled.prelude);
                    args.push(compiled.expr);
                }
                let call = Expression::call(func.expr, args, CallInfo::default());
                if prelude.is_empty() {
                    Compiled {
                        prelude,
                        expr: call,
                    }
                } else {
                    let tmp = self.fresh_ident("call");
                    prelude.push(Statement::variable(VariableDeclaration {
                        ident: tmp.clone(),
                        value: Some(call),
                        property: LetKind::Strict,
                        ident_info: IdentInfo::default(),
                    }));
                    Compiled {
                        prelude,
                        expr: Expression::var(tmp),
                    }
                }
            }
            Lambda::Lfunction(func) => {
                let params = func.params.clone();
                let expr = Expression::new(ExpressionDesc::Fun {
                    is_method: false,
                    params,
                    body: self.compile_return_block(&func.body),
                    env: Default::default(),
                    return_unit: func.attr.return_unit,
                    async_: func.attr.async_,
                    directive: func.attr.directive.clone(),
                });
                Compiled {
                    prelude: vec![],
                    expr,
                }
            }
            Lambda::Llet(kind, id, value, body) => {
                let mut prelude = vec![];
                let value_compiled = self.compile_expr(value);
                prelude.extend(value_compiled.prelude);
                prelude.push(Statement::variable(VariableDeclaration {
                    ident: id.clone(),
                    value: Some(value_compiled.expr),
                    property: *kind,
                    ident_info: IdentInfo::default(),
                }));
                let body_compiled = self.compile_expr(body);
                prelude.extend(body_compiled.prelude);
                Compiled {
                    prelude,
                    expr: body_compiled.expr,
                }
            }
            Lambda::Lletrec(bindings, body) => {
                let mut prelude = vec![];
                for (id, _) in bindings {
                    prelude.push(Statement::variable(VariableDeclaration {
                        ident: id.clone(),
                        value: None,
                        property: LetKind::Strict,
                        ident_info: IdentInfo::default(),
                    }));
                }
                for (id, expr) in bindings {
                    let compiled = self.compile_expr(expr);
                    prelude.extend(compiled.prelude);
                    let assign =
                        Expression::bin(BinOp::Eq, Expression::var(id.clone()), compiled.expr);
                    prelude.push(Statement::exp(assign));
                }
                let body_compiled = self.compile_expr(body);
                prelude.extend(body_compiled.prelude);
                Compiled {
                    prelude,
                    expr: body_compiled.expr,
                }
            }
            Lambda::Lprim(info) => self.compile_primitive(&info.primitive, &info.args),
            Lambda::Lswitch(scrut, switch) => self.compile_switch(scrut, switch),
            Lambda::LstringSwitch(scrut, cases, default) => {
                self.compile_string_switch(scrut, cases, default.as_deref())
            }
            Lambda::LstaticRaise(_id, args) => {
                let expr = if let Some(arg) = args.first() {
                    self.compile_expr(arg).expr
                } else {
                    Expression::undefined(false)
                };
                Compiled {
                    prelude: vec![Statement::throw(expr)],
                    expr: Expression::undefined(false),
                }
            }
            Lambda::LstaticCatch(body, _handler, _handler_body) => self.compile_expr(body),
            Lambda::LtryWith(body, exn, handler) => {
                let body_block = self.compile_block(body);
                let handler_block = self.compile_block(handler);
                let try_stmt = Statement::new(StatementDesc::Try(
                    body_block,
                    Some((exn.clone(), handler_block)),
                    None,
                ));
                Compiled {
                    prelude: vec![try_stmt],
                    expr: Expression::undefined(false),
                }
            }
            Lambda::LifThenElse(cond, then_, else_) => {
                let cond_compiled = self.compile_expr(cond);
                let then_compiled = self.compile_expr(then_);
                let else_compiled = self.compile_expr(else_);
                let mut prelude = cond_compiled.prelude;
                if then_compiled.prelude.is_empty() && else_compiled.prelude.is_empty() {
                    Compiled {
                        prelude,
                        expr: Expression::cond(
                            cond_compiled.expr,
                            then_compiled.expr,
                            else_compiled.expr,
                        ),
                    }
                } else {
                    let tmp = self.fresh_ident("ifres");
                    prelude.push(Statement::variable(VariableDeclaration {
                        ident: tmp.clone(),
                        value: None,
                        property: LetKind::Strict,
                        ident_info: IdentInfo::default(),
                    }));
                    let mut then_block = then_compiled.prelude;
                    then_block.push(Statement::exp(Expression::bin(
                        BinOp::Eq,
                        Expression::var(tmp.clone()),
                        then_compiled.expr,
                    )));
                    let mut else_block = else_compiled.prelude;
                    else_block.push(Statement::exp(Expression::bin(
                        BinOp::Eq,
                        Expression::var(tmp.clone()),
                        else_compiled.expr,
                    )));
                    prelude.push(Statement::if_(cond_compiled.expr, then_block, else_block));
                    Compiled {
                        prelude,
                        expr: Expression::var(tmp),
                    }
                }
            }
            Lambda::Lsequence(a, b) => {
                let first = self.compile_expr(a);
                let second = self.compile_expr(b);
                self.append_effect_output(first, second)
            }
            Lambda::Lwhile(cond, body) => {
                let cond_expr = self.compile_expr(cond).expr;
                let body_block = self.compile_block(body);
                Compiled {
                    prelude: vec![Statement::while_(cond_expr, body_block)],
                    expr: Expression::undefined(false),
                }
            }
            Lambda::Lfor(var, start, end, dir, body) => {
                let start_expr = self.compile_expr(start).expr;
                let end_expr = self.compile_expr(end).expr;
                let dir = match dir {
                    crate::lambda::DirectionFlag::Upto => ForDirection::Upto,
                    crate::lambda::DirectionFlag::Downto => ForDirection::Downto,
                };
                let body_block = self.compile_block(body);
                let stmt = Statement::new(StatementDesc::ForRange(
                    Some(start_expr),
                    end_expr,
                    var.clone(),
                    dir,
                    body_block,
                ));
                Compiled {
                    prelude: vec![stmt],
                    expr: Expression::undefined(false),
                }
            }
            Lambda::Lassign(id, value) => {
                let compiled = self.compile_expr(value);
                let prelude = compiled.prelude;
                let assign = Expression::bin(BinOp::Eq, Expression::var(id.clone()), compiled.expr);
                Compiled {
                    prelude,
                    expr: assign,
                }
            }
        }
    }

    fn compile_block(&mut self, lam: &Lambda) -> Block {
        self.compile_effect_block(lam)
    }

    fn compile_effect_block(&mut self, lam: &Lambda) -> Block {
        match lam {
            Lambda::Lsequence(first, second) => {
                let mut block = self.compile_effect_block(first);
                block.extend(self.compile_effect_block(second));
                block
            }
            _ => {
                let compiled = self.compile_expr(lam);
                let mut block = compiled.prelude;
                push_effect_expression(&mut block, compiled.expr);
                block
            }
        }
    }

    fn compile_return_block(&mut self, lam: &Lambda) -> Block {
        match lam {
            Lambda::Lsequence(first, second) => {
                let mut block = self.compile_effect_block(first);
                block.extend(self.compile_return_block(second));
                block
            }
            _ => {
                let compiled = self.compile_expr(lam);
                let mut block = compiled.prelude;
                block.push(Statement::return_(compiled.expr));
                block
            }
        }
    }

    fn append_effect_output(&self, first: Compiled, second: Compiled) -> Compiled {
        let first_is_pure = js_expr_no_side_effects(&first.expr);
        if first.prelude.is_empty() {
            if first_is_pure {
                return second;
            }
            if second.prelude.is_empty() {
                return Compiled {
                    prelude: vec![],
                    expr: Expression::new(ExpressionDesc::Seq(
                        Box::new(first.expr),
                        Box::new(second.expr),
                    )),
                };
            }
        }

        let mut prelude = first.prelude;
        if !first_is_pure {
            push_effect_expression(&mut prelude, first.expr);
        }
        prelude.extend(second.prelude);
        Compiled {
            prelude,
            expr: second.expr,
        }
    }

    fn compile_switch(&mut self, scrut: &Lambda, switch: &LambdaSwitch) -> Compiled {
        let scrut_compiled = self.compile_expr(scrut);
        let mut prelude = scrut_compiled.prelude;
        let tmp = self.fresh_ident("switch");
        prelude.push(Statement::variable(VariableDeclaration {
            ident: tmp.clone(),
            value: None,
            property: LetKind::Strict,
            ident_info: IdentInfo::default(),
        }));

        let mut cases = Vec::new();
        for (tag, body) in &switch.sw_consts {
            let mut body_block = self.compile_block(body);
            body_block.push(Statement::break_());
            cases.push((
                *tag,
                crate::js_ir::CaseClause {
                    body: body_block,
                    should_break: false,
                    comment: None,
                },
            ));
        }

        let default_block = switch.sw_failaction.as_ref().map(|fallback| {
            let mut block = self.compile_block(fallback);
            block.push(Statement::break_());
            block
        });

        prelude.push(Statement::new(StatementDesc::IntSwitch(
            scrut_compiled.expr,
            cases,
            default_block,
        )));

        Compiled {
            prelude,
            expr: Expression::var(tmp),
        }
    }

    fn compile_string_switch(
        &mut self,
        scrut: &Lambda,
        cases: &[(String, Lambda)],
        default: Option<&Lambda>,
    ) -> Compiled {
        let scrut_compiled = self.compile_expr(scrut);
        let mut prelude = scrut_compiled.prelude;
        let tmp = self.fresh_ident("switch");
        prelude.push(Statement::variable(VariableDeclaration {
            ident: tmp.clone(),
            value: None,
            property: LetKind::Strict,
            ident_info: IdentInfo::default(),
        }));

        let mut clauses = Vec::new();
        for (tag, body) in cases {
            let mut body_block = self.compile_block(body);
            body_block.push(Statement::break_());
            clauses.push(crate::js_ir::StringClause {
                tag_type: tag.clone(),
                clause: crate::js_ir::CaseClause {
                    body: body_block,
                    should_break: false,
                    comment: None,
                },
            });
        }

        let default_block = default.map(|fallback| {
            let mut block = self.compile_block(fallback);
            block.push(Statement::break_());
            block
        });

        prelude.push(Statement::new(StatementDesc::StringSwitch(
            scrut_compiled.expr,
            clauses,
            default_block,
        )));

        Compiled {
            prelude,
            expr: Expression::var(tmp),
        }
    }

    fn dynamic_import_body(&self, lam: &Lambda) -> Option<Lambda> {
        let call = match lam {
            Lambda::Lfunction(func) => match func.body.as_ref() {
                Lambda::Lprim(prim) => prim,
                Lambda::Lsequence(first, second)
                    if matches!(
                        second.as_ref(),
                        Lambda::Lconst(Constant::JsUndefined { .. })
                    ) =>
                {
                    match first.as_ref() {
                        Lambda::Lprim(prim) => prim,
                        _ => return None,
                    }
                }
                _ => return None,
            },
            _ => return None,
        };

        match &call.primitive {
            Primitive::PjsCall {
                prim_name,
                arg_types,
                ffi,
                transformed_jsx,
                ..
            } => Some(Lambda::prim(
                Primitive::PjsCall {
                    prim_name: prim_name.clone(),
                    arg_types: arg_types.clone(),
                    ffi: ffi.clone(),
                    dynamic_import: true,
                    transformed_jsx: *transformed_jsx,
                },
                call.args.clone(),
                call.loc.clone(),
            )),
            _ => None,
        }
    }

    fn compile_import_primitive(&mut self, args: &[Lambda]) -> Compiled {
        let target = match args {
            [arg] => self.dynamic_import_body(arg).unwrap_or_else(|| arg.clone()),
            _ => {
                let mut prelude = vec![];
                let mut compiled_args = Vec::new();
                for arg in args {
                    let compiled = self.compile_expr(arg);
                    prelude.extend(compiled.prelude);
                    compiled_args.push(compiled.expr);
                }
                return Compiled {
                    prelude,
                    expr: self.compile_import(compiled_args),
                };
            }
        };

        let compiled = self.compile_expr(&target);
        let prelude = compiled.prelude;
        let expr = self.compile_import(vec![compiled.expr]);
        Compiled { prelude, expr }
    }

    fn compile_primitive(&mut self, prim: &Primitive, args: &[Lambda]) -> Compiled {
        if matches!(prim, Primitive::Pimport) {
            return self.compile_import_primitive(args);
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
            Pstringlength => Expression::new(ExpressionDesc::Length(
                Box::new(compiled_args[0].clone()),
                LengthObject::String,
            )),
            Parraylength => Expression::new(ExpressionDesc::Length(
                Box::new(compiled_args[0].clone()),
                LengthObject::Array,
            )),
            Paddint => int32_add(compiled_args[0].clone(), compiled_args[1].clone()),
            Paddfloat => Expression::bin(
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
            Pmulint => int32_mul(compiled_args[0].clone(), compiled_args[1].clone()),
            Pmulfloat => Expression::bin(
                BinOp::Mul,
                compiled_args[0].clone(),
                compiled_args[1].clone(),
            ),
            Pdivint => int32_div(compiled_args[0].clone(), compiled_args[1].clone()),
            Pdivfloat => Expression::bin(
                BinOp::Div,
                compiled_args[0].clone(),
                compiled_args[1].clone(),
            ),
            Pmodint => int32_mod(compiled_args[0].clone(), compiled_args[1].clone()),
            Pmodfloat => Expression::bin(
                BinOp::Mod,
                compiled_args[0].clone(),
                compiled_args[1].clone(),
            ),
            Ppowint => to_int32(Expression::bin(
                BinOp::Pow,
                compiled_args[0].clone(),
                compiled_args[1].clone(),
            )),
            Ppowfloat => {
                // Math.pow(base, exponent)
                let math = Expression::var(Ident::create_persistent("Math"));
                let pow = Expression::new(ExpressionDesc::StaticIndex(
                    Box::new(math),
                    "pow".to_string(),
                    None,
                ));
                Expression::call(pow, compiled_args, CallInfo::default())
            }
            Pboolcomp(cmp) | Pintcomp(cmp) | Pfloatcomp(cmp) | Pbigintcomp(cmp)
            | Pstringcomp(cmp) | Pjscomp(cmp) => {
                let op = comparison_to_binop(*cmp);
                Expression::bin(op, compiled_args[0].clone(), compiled_args[1].clone())
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
            Pnot => Expression::new(ExpressionDesc::JsNot(Box::new(compiled_args[0].clone()))),
            Pnegint => int32_minus(int_expr(0), compiled_args[0].clone()),
            Pnegfloat => Expression::bin(BinOp::Minus, int_expr(0), compiled_args[0].clone()),
            Pnotint => int_bnot(compiled_args[0].clone()),
            Pandint => Expression::bin(
                BinOp::Band,
                compiled_args[0].clone(),
                compiled_args[1].clone(),
            ),
            Porint => Expression::bin(
                BinOp::Bor,
                compiled_args[0].clone(),
                compiled_args[1].clone(),
            ),
            Pxorint => Expression::bin(
                BinOp::Bxor,
                compiled_args[0].clone(),
                compiled_args[1].clone(),
            ),
            Plslint => Expression::bin(
                BinOp::Lsl,
                compiled_args[0].clone(),
                compiled_args[1].clone(),
            ),
            Plsrint => int32_lsr(compiled_args[0].clone(), compiled_args[1].clone()),
            Pasrint => Expression::bin(
                BinOp::Asr,
                compiled_args[0].clone(),
                compiled_args[1].clone(),
            ),
            Poffsetint(offset) => int32_offset(compiled_args[0].clone(), *offset),
            Pmakearray => Expression::array(compiled_args, MutableFlag::Mutable),
            Pstringadd => Expression::new(ExpressionDesc::StringAppend(
                Box::new(compiled_args[0].clone()),
                Box::new(compiled_args[1].clone()),
            )),
            PnullToOpt => Expression::cond(
                self.is_null_expr(compiled_args[0].clone()),
                Expression::undefined(false),
                self.optional_block(compiled_args[0].clone(), false),
            ),
            PnullUndefinedToOpt => Expression::cond(
                Expression::new(ExpressionDesc::IsNullOrUndefined(Box::new(
                    compiled_args[0].clone(),
                ))),
                Expression::undefined(false),
                self.optional_block(compiled_args[0].clone(), false),
            ),
            PisNotNone => self.is_not_none_expr(compiled_args[0].clone()),
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
            PrawJsCode(info) => {
                Expression::new(ExpressionDesc::RawJsCode(crate::js_ir::JsRawInfo {
                    code: info.code.clone(),
                    is_stmt: info.is_stmt,
                }))
            }
            Pdebugger => {
                prelude.push(Statement::debugger());
                Expression::undefined(false)
            }
            Praise => {
                let expr = compiled_args
                    .first()
                    .cloned()
                    .unwrap_or_else(|| Expression::undefined(false));
                prelude.push(Statement::throw(expr));
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
            Ptypeof => Expression::new(ExpressionDesc::Typeof(Box::new(compiled_args[0].clone()))),
            Pintoffloat => to_int32(compiled_args[0].clone()),
            Pfloatofint => compiled_args
                .first()
                .cloned()
                .unwrap_or_else(|| Expression::undefined(false)),
            Pawait => Expression::new(ExpressionDesc::Await(Box::new(compiled_args[0].clone()))),
            PjsObjectCreate(obj_params) => {
                self.compile_js_object_create(obj_params, compiled_args, &mut prelude)
            }
            PjsFnMake(_) | PjsFnMakeUnit => compiled_args
                .first()
                .cloned()
                .unwrap_or_else(|| Expression::undefined(false)),
            PjsFnMethod => match compiled_args.first().cloned() {
                Some(Expression {
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
            Pimport => self.compile_import(compiled_args),
            PjsCall {
                prim_name,
                arg_types,
                ffi,
                dynamic_import,
                ..
            } => self.compile_js_call(
                prim_name,
                arg_types,
                ffi,
                *dynamic_import,
                compiled_args,
                &mut prelude,
            ),
            Pnull => Expression::null(),
            Pundefined => Expression::undefined(false),
            _ => Expression::undefined(false),
        };

        Compiled { prelude, expr }
    }

    fn compile_constant(cst: &Constant) -> Expression {
        match cst {
            Constant::JsNull => Expression::null(),
            Constant::JsUndefined { is_unit } => Expression::undefined(*is_unit),
            Constant::JsTrue => Expression::bool(true),
            Constant::JsFalse => Expression::bool(false),
            Constant::Int { i, comment } => {
                let _ = comment;
                Expression::number(Number::int(*i))
            }
            Constant::NativeInt { i, comment } => {
                let _ = comment;
                Expression::number(Number::float(i.to_string()))
            }
            Constant::Char(c) => Expression::number(Number::Int { i: *c, c: Some(*c) }),
            Constant::String { s, delim } => {
                let delim = match delim {
                    Some(StringDelim::Backtick) => Delim::BackQuotes,
                    Some(StringDelim::Plain)
                    | Some(StringDelim::StarJ)
                    | Some(StringDelim::NoQuotes)
                    | None => Delim::None,
                };
                Expression::new(ExpressionDesc::Str {
                    delim,
                    txt: s.clone(),
                })
            }
            Constant::ImmString(s) => Expression::new(ExpressionDesc::Str {
                delim: Delim::None,
                txt: s.clone(),
            }),
            Constant::Float(f) => Expression::number(Number::float(f.clone())),
            Constant::BigInt { negative, value } => {
                Expression::number(Number::bigint(!negative, value.clone()))
            }
            Constant::Pointer(name) => Expression::string(name.clone()),
            Constant::Block {
                tag,
                tag_info,
                elements,
            } => {
                let elems = elements.iter().map(Self::compile_constant).collect();
                Expression::new(ExpressionDesc::CamlBlock(
                    elems,
                    MutableFlag::Immutable,
                    Box::new(Expression::number(Number::int(*tag))),
                    tag_info.clone(),
                ))
            }
            Constant::Some(inner) => {
                let inner = Self::compile_constant(inner);
                Expression::new(ExpressionDesc::OptionalBlock(Box::new(inner), true))
            }
            Constant::ModuleAlias => Expression::undefined(false),
        }
    }

    fn compile_field_access(
        &self,
        idx: i32,
        info: &FieldDbgInfo,
        target: &Expression,
    ) -> Expression {
        match info {
            FieldDbgInfo::Module { name }
            | FieldDbgInfo::Record { name, .. }
            | FieldDbgInfo::RecordInline { name }
            | FieldDbgInfo::RecordExtension { name } => Expression::new(
                ExpressionDesc::StaticIndex(Box::new(target.clone()), name.clone(), None),
            ),
            FieldDbgInfo::Cons => Expression::new(ExpressionDesc::StaticIndex(
                Box::new(target.clone()),
                match idx {
                    0 => "hd".to_string(),
                    1 => "tl".to_string(),
                    _ => format!("_{}", idx),
                },
                None,
            )),
            FieldDbgInfo::VariantTag => Expression::new(ExpressionDesc::StaticIndex(
                Box::new(target.clone()),
                "TAG".to_string(),
                None,
            )),
            FieldDbgInfo::Variant => {
                // Variant fields are accessed as _0, _1, _2, ...
                Expression::new(ExpressionDesc::StaticIndex(
                    Box::new(target.clone()),
                    format!("_{}", idx),
                    None,
                ))
            }
            _ => Expression::new(ExpressionDesc::ArrayIndex(
                Box::new(target.clone()),
                Box::new(Expression::number(Number::int(idx))),
            )),
        }
    }

    fn compile_set_field(
        &self,
        _idx: i32,
        info: &crate::lambda::compat::SetFieldDbgInfo,
        target: &Expression,
        value: &Expression,
    ) -> Expression {
        let field = match info {
            crate::lambda::compat::SetFieldDbgInfo::RecordSet(name)
            | crate::lambda::compat::SetFieldDbgInfo::RecordInlineSet(name)
            | crate::lambda::compat::SetFieldDbgInfo::RecordExtensionSet(name) => Expression::new(
                ExpressionDesc::StaticIndex(Box::new(target.clone()), name.clone(), None),
            ),
        };
        Expression::bin(BinOp::Eq, field, value.clone())
    }

    fn compile_external_arg_const(&self, cst: &ExternalArgConst) -> Expression {
        match cst {
            ExternalArgConst::IntLit(i) => Expression::number(Number::Int {
                i: *i as i32,
                c: None,
            }),
            ExternalArgConst::StringLit(s, delim) => {
                let delim = match delim {
                    ExternalArgDelim::None => Delim::None,
                    ExternalArgDelim::StarJ => Delim::StarJ,
                    ExternalArgDelim::NoQuotes => Delim::NoQuotes,
                    ExternalArgDelim::BackQuotes => Delim::BackQuotes,
                };
                Expression::new(ExpressionDesc::Str {
                    delim,
                    txt: s.clone(),
                })
            }
        }
    }

    fn runtime_member_expr(&self, module_name: &str, member: &str) -> Expression {
        Expression::qualified(
            ModuleId {
                id: Ident::create_persistent(module_name),
                kind: Kind::Runtime,
                dynamic_import: false,
            },
            Some(member.to_string()),
        )
    }

    fn runtime_call_expr(
        &self,
        module_name: &str,
        member: &str,
        args: Vec<Expression>,
    ) -> Expression {
        Expression::call(
            self.runtime_member_expr(module_name, member),
            args,
            CallInfo::default(),
        )
    }

    fn external_module_id(
        &self,
        module_name: &ExternalModuleName,
        default: bool,
        dynamic_import: bool,
    ) -> ModuleId {
        ModuleId {
            id: Ident::create_persistent(external_module_ident_name(module_name)),
            kind: Kind::External {
                name: module_name.bundle.clone(),
                default,
                import_attributes: external_module_import_attributes(module_name),
            },
            dynamic_import,
        }
    }

    fn external_module_binding(
        &self,
        module_name: &ExternalModuleName,
        default: bool,
        dynamic_import: bool,
    ) -> Expression {
        Expression::qualified(
            self.external_module_id(module_name, default, dynamic_import),
            None,
        )
    }

    fn translate_scoped_module_value(
        &self,
        module_name: Option<&ExternalModuleName>,
        name: &str,
        scopes: &[String],
        dynamic_import: bool,
    ) -> Expression {
        match module_name {
            Some(module_name) => match scopes.split_first() {
                None => {
                    let default = name == "default";
                    let module = self.external_module_binding(module_name, default, dynamic_import);
                    if default {
                        module
                    } else {
                        self.static_index(module, name)
                    }
                }
                Some((first_scope, rest_scopes)) => {
                    let mut expr = self.external_module_binding(module_name, false, dynamic_import);
                    expr = self.static_index(expr, first_scope);
                    for scope in rest_scopes {
                        expr = self.static_index(expr, scope);
                    }
                    self.static_index(expr, name)
                }
            },
            None => self.translate_scoped_global_value(name, scopes),
        }
    }

    fn optional_block(&self, value: Expression, identity: bool) -> Expression {
        Expression::new(ExpressionDesc::OptionalBlock(Box::new(value), identity))
    }

    fn is_null_expr(&self, expr: Expression) -> Expression {
        Expression::bin(BinOp::EqEqEq, expr, Expression::null())
    }

    fn some_expr(&self, value: Expression) -> Expression {
        let identity = matches!(
            value.desc,
            ExpressionDesc::Null
                | ExpressionDesc::Object(_, _)
                | ExpressionDesc::Number(_)
                | ExpressionDesc::CamlBlock(_, _, _, _)
                | ExpressionDesc::Array(_, _)
                | ExpressionDesc::Str { .. }
        );
        self.optional_block(value, identity)
    }

    fn val_from_option_expr(&self, arg: Expression) -> Expression {
        match arg.desc {
            ExpressionDesc::OptionalBlock(inner, _) => *inner,
            _ => self.runtime_call_expr("Caml_option", "valFromOption", vec![arg]),
        }
    }

    fn is_not_none_expr(&self, arg: Expression) -> Expression {
        match arg.desc {
            ExpressionDesc::Undefined { .. } => Expression::bool(false),
            ExpressionDesc::OptionalBlock(_, _) => Expression::bool(true),
            _ => Expression::bin(BinOp::NotEqEq, arg, Expression::undefined(false)),
        }
    }

    fn lower_external_arg_value(
        &self,
        arg: Expression,
        arg_label: ExternalArgLabel,
        arg_type: &ExternalArgAttr,
    ) -> Option<Expression> {
        match arg_type {
            ExternalArgAttr::ArgCst(_) => None,
            ExternalArgAttr::ExternUnit => {
                if matches!(arg_label, ExternalArgLabel::Empty) {
                    None
                } else {
                    Some(Expression::undefined(true))
                }
            }
            ExternalArgAttr::Ignore => None,
            _ => Some(arg),
        }
    }

    fn assemble_external_args_no_splice(
        &self,
        arg_types: &[ExternalArgSpec],
        args: Vec<Expression>,
    ) -> Vec<Expression> {
        let mut runtime_args = args.into_iter();
        let mut assembled = Vec::new();

        for arg_spec in arg_types {
            match &arg_spec.arg_type {
                ExternalArgAttr::ArgCst(cst) => {
                    assembled.push(self.compile_external_arg_const(cst));
                }
                _ => {
                    let arg = runtime_args
                        .next()
                        .unwrap_or_else(|| Expression::undefined(false));
                    if let Some(expr) =
                        self.lower_external_arg_value(arg, arg_spec.arg_label, &arg_spec.arg_type)
                    {
                        assembled.push(expr);
                    }
                }
            }
        }

        debug_assert!(runtime_args.next().is_none());
        assembled
    }

    fn compile_js_object_create(
        &self,
        obj_params: &[ExternalObjSpec],
        args: Vec<Expression>,
        prelude: &mut Block,
    ) -> Expression {
        let mut runtime_args = args.into_iter();
        let mut props = Vec::new();
        let mut optional_assignments = Vec::new();

        for obj_param in obj_params {
            match &obj_param.obj_arg_label {
                ExternalObjLabel::Empty => {
                    if !matches!(obj_param.obj_arg_type, ExternalArgAttr::ArgCst(_)) {
                        let _ = runtime_args.next();
                    }
                }
                ExternalObjLabel::Label { name } => match &obj_param.obj_arg_type {
                    ExternalArgAttr::ArgCst(cst) => {
                        props.push((
                            PropertyName::lit(name.clone()),
                            self.compile_external_arg_const(cst),
                        ));
                    }
                    _ => {
                        let arg = runtime_args
                            .next()
                            .unwrap_or_else(|| Expression::undefined(false));
                        if let Some(value) = self.lower_external_arg_value(
                            arg,
                            ExternalArgLabel::Label,
                            &obj_param.obj_arg_type,
                        ) {
                            props.push((PropertyName::lit(name.clone()), value));
                        }
                    }
                },
                ExternalObjLabel::Optional { name, .. } => {
                    let arg = runtime_args
                        .next()
                        .unwrap_or_else(|| Expression::undefined(false));
                    if matches!(arg.desc, ExpressionDesc::Undefined { .. }) {
                        continue;
                    }

                    let prepared = if self.expr_is_simple(&arg) {
                        arg
                    } else {
                        let tmp = self.fresh_ident("obj");
                        prelude.push(Statement::variable(VariableDeclaration {
                            ident: tmp.clone(),
                            value: Some(arg),
                            property: LetKind::Variable,
                            ident_info: IdentInfo::default(),
                        }));
                        Expression::var(tmp)
                    };

                    if let Some(value) = self.lower_external_arg_value(
                        prepared.clone(),
                        ExternalArgLabel::Empty,
                        &obj_param.obj_arg_type,
                    ) {
                        optional_assignments.push((name.clone(), prepared, value));
                    }
                }
            }
        }

        debug_assert!(runtime_args.next().is_none());

        if optional_assignments.is_empty() {
            return Expression::new(ExpressionDesc::Object(None, props));
        }

        let obj = self.fresh_ident("obj");
        prelude.push(Statement::variable(VariableDeclaration {
            ident: obj.clone(),
            value: Some(Expression::new(ExpressionDesc::Object(None, props))),
            property: LetKind::Variable,
            ident_info: IdentInfo::default(),
        }));

        for (name, arg, value) in optional_assignments {
            let cond = Expression::bin(BinOp::NotEqEq, arg, Expression::undefined(false));
            let assign = Expression::bin(
                BinOp::Eq,
                self.static_index(Expression::var(obj.clone()), &name),
                value,
            );
            prelude.push(Statement::if_(cond, vec![Statement::exp(assign)], vec![]));
        }

        Expression::var(obj)
    }

    fn expr_is_simple(&self, expr: &Expression) -> bool {
        matches!(
            expr.desc,
            ExpressionDesc::Var(_)
                | ExpressionDesc::Undefined { .. }
                | ExpressionDesc::Null
                | ExpressionDesc::Bool(_)
                | ExpressionDesc::Number(_)
                | ExpressionDesc::Str { .. }
        )
    }

    fn compile_js_call(
        &self,
        prim_name: &str,
        arg_types: &[ExternalArgSpec],
        ffi: &crate::lambda::primitive::ExternalFfiSpec,
        dynamic_import: bool,
        args: Vec<Expression>,
        _prelude: &mut Block,
    ) -> Expression {
        match ffi.spec.as_ref() {
            Some(ExternalSpec::JsVar {
                name,
                external_module_name,
                scopes,
            }) => {
                let value = self.translate_scoped_module_value(
                    external_module_name.as_ref(),
                    name,
                    scopes,
                    dynamic_import,
                );
                let args = self.assemble_external_args_no_splice(arg_types, args);
                if args.is_empty() {
                    value
                } else {
                    Expression::call(value, args, CallInfo::default())
                }
            }
            Some(ExternalSpec::JsCall {
                name,
                external_module_name,
                scopes,
                tagged_template: false,
                ..
            }) => Expression::call(
                self.translate_scoped_module_value(
                    external_module_name.as_ref(),
                    name,
                    scopes,
                    dynamic_import,
                ),
                self.assemble_external_args_no_splice(arg_types, args),
                CallInfo::default(),
            ),
            Some(ExternalSpec::JsNew {
                name,
                external_module_name,
                scopes,
                ..
            }) => Expression::new(ExpressionDesc::New(
                Box::new(self.translate_scoped_module_value(
                    external_module_name.as_ref(),
                    name,
                    scopes,
                    dynamic_import,
                )),
                Some(self.assemble_external_args_no_splice(arg_types, args)),
            )),
            Some(ExternalSpec::JsSend {
                name,
                js_send_scopes,
                ..
            }) => match args.split_first() {
                Some((receiver, rest)) => {
                    let rest_args = self.assemble_external_args_no_splice(
                        arg_types.get(1..).unwrap_or(&[]),
                        rest.to_vec(),
                    );
                    Expression::call(
                        self.static_index(
                            self.apply_scoped_access(receiver.clone(), js_send_scopes),
                            name,
                        ),
                        rest_args,
                        CallInfo::default(),
                    )
                }
                None => self.compile_plain_js_call(prim_name, args),
            },
            Some(ExternalSpec::JsGet {
                js_get_name,
                js_get_scopes,
            }) => {
                let assembled = self.assemble_external_args_no_splice(arg_types, args);
                match assembled.as_slice() {
                    [receiver] => self.static_index(
                        self.apply_scoped_access(receiver.clone(), js_get_scopes),
                        js_get_name,
                    ),
                    _ => self.compile_plain_js_call(prim_name, assembled),
                }
            }
            Some(ExternalSpec::JsSet {
                js_set_name,
                js_set_scopes,
            }) => {
                let assembled = self.assemble_external_args_no_splice(arg_types, args);
                match assembled.as_slice() {
                    [receiver, value] => Expression::bin(
                        BinOp::Eq,
                        self.static_index(
                            self.apply_scoped_access(receiver.clone(), js_set_scopes),
                            js_set_name,
                        ),
                        value.clone(),
                    ),
                    _ => self.compile_plain_js_call(prim_name, assembled),
                }
            }
            Some(ExternalSpec::JsGetIndex {
                js_get_index_scopes,
            }) => {
                let assembled = self.assemble_external_args_no_splice(arg_types, args);
                match assembled.as_slice() {
                    [receiver, index] => Expression::new(ExpressionDesc::ArrayIndex(
                        Box::new(self.apply_scoped_access(receiver.clone(), js_get_index_scopes)),
                        Box::new(index.clone()),
                    )),
                    _ => self.compile_plain_js_call(prim_name, assembled),
                }
            }
            Some(ExternalSpec::JsSetIndex {
                js_set_index_scopes,
            }) => {
                let assembled = self.assemble_external_args_no_splice(arg_types, args);
                match assembled.as_slice() {
                    [receiver, index, value] => Expression::bin(
                        BinOp::Eq,
                        Expression::new(ExpressionDesc::ArrayIndex(
                            Box::new(
                                self.apply_scoped_access(receiver.clone(), js_set_index_scopes),
                            ),
                            Box::new(index.clone()),
                        )),
                        value.clone(),
                    ),
                    _ => self.compile_plain_js_call(prim_name, assembled),
                }
            }
            Some(ExternalSpec::JsModuleAsVar(module_name)) => {
                let value = self.external_module_binding(module_name, false, dynamic_import);
                let args = self.assemble_external_args_no_splice(arg_types, args);
                if args.is_empty() {
                    value
                } else {
                    Expression::call(value, args, CallInfo::default())
                }
            }
            Some(ExternalSpec::JsModuleAsFn {
                external_module_name,
                ..
            }) => Expression::call(
                self.external_module_binding(external_module_name, false, dynamic_import),
                self.assemble_external_args_no_splice(arg_types, args),
                CallInfo::default(),
            ),
            Some(ExternalSpec::JsModuleAsClass(module_name)) => {
                Expression::new(ExpressionDesc::New(
                    Box::new(self.external_module_binding(module_name, false, dynamic_import)),
                    Some(self.assemble_external_args_no_splice(arg_types, args)),
                ))
            }
            _ => self.compile_plain_js_call(prim_name, args),
        }
    }

    fn compile_plain_js_call(&self, prim_name: &str, args: Vec<Expression>) -> Expression {
        Expression::call(
            Expression::var(Ident::create_persistent(prim_name)),
            args,
            CallInfo::default(),
        )
    }

    fn compile_import(&self, args: Vec<Expression>) -> Expression {
        let arg = match args.as_slice() {
            [arg] => arg,
            [arg, Expression {
                desc: ExpressionDesc::Undefined { is_unit: true },
                ..
            }] => arg,
            _ => {
                return Expression::call(
                    Expression::var(Ident::create_persistent("import")),
                    args,
                    CallInfo::default(),
                );
            }
        };

        let Some((module, member)) = self.module_of_expression(arg) else {
            return Expression::call(
                Expression::var(Ident::create_persistent("import")),
                args,
                CallInfo::default(),
            );
        };

        let path = match &module.kind {
            Kind::External { name, .. } => Some(name.clone()),
            _ => self
                .module_path_resolver
                .as_ref()
                .and_then(|resolver| resolver.resolve_module_path(&module)),
        };

        let Some(path) = path else {
            return Expression::call(
                Expression::var(Ident::create_persistent("import")),
                args,
                CallInfo::default(),
            );
        };

        let import_expr = Expression::call(
            Expression::var(Ident::create_persistent("import")),
            vec![Expression::string(path)],
            CallInfo::default(),
        );

        let member = member.or_else(|| match &module.kind {
            Kind::External { default: true, .. } => Some("default".to_string()),
            _ => None,
        });

        match member {
            Some(member) => {
                let param = self.fresh_ident("m");
                let body = vec![Statement::return_(
                    self.static_index(Expression::var(param.clone()), &member),
                )];
                let callback = Expression::new(ExpressionDesc::Fun {
                    is_method: false,
                    params: vec![param],
                    body,
                    env: Default::default(),
                    return_unit: false,
                    async_: false,
                    directive: None,
                });
                Expression::call(
                    self.static_index(import_expr, "then"),
                    vec![callback],
                    CallInfo::default(),
                )
            }
            None => import_expr,
        }
    }

    fn module_of_expression(&self, expr: &Expression) -> Option<(ModuleId, Option<String>)> {
        match &expr.desc {
            ExpressionDesc::Var(crate::js_ir::VIdent::Qualified(module, member)) => {
                Some((module.clone(), member.clone()))
            }
            ExpressionDesc::StaticIndex(target, field, _) => match &target.desc {
                ExpressionDesc::Var(crate::js_ir::VIdent::Qualified(module, None)) => {
                    Some((module.clone(), Some(field.clone())))
                }
                _ => None,
            },
            ExpressionDesc::Call(func, _, _) => match &func.desc {
                ExpressionDesc::Var(crate::js_ir::VIdent::Qualified(module, member)) => {
                    Some((module.clone(), member.clone()))
                }
                _ => None,
            },
            _ => None,
        }
    }

    fn translate_scoped_global_value(&self, name: &str, scopes: &[String]) -> Expression {
        let mut expr = match scopes.split_first() {
            Some((head, rest)) => {
                let mut expr = Expression::var(Ident::create_persistent(head));
                for scope in rest {
                    expr = self.static_index(expr, scope);
                }
                expr
            }
            None => Expression::var(Ident::create_persistent(name)),
        };
        if !scopes.is_empty() {
            expr = self.static_index(expr, name);
        }
        expr
    }

    fn apply_scoped_access(&self, mut expr: Expression, scopes: &[String]) -> Expression {
        for scope in scopes {
            expr = self.static_index(expr, scope);
        }
        expr
    }

    fn static_index(&self, target: Expression, field: &str) -> Expression {
        Expression::new(ExpressionDesc::StaticIndex(
            Box::new(target),
            field.to_string(),
            None,
        ))
    }

    fn fresh_ident(&self, prefix: &str) -> Ident {
        self.id_gen.create(prefix)
    }

    fn collect_required_modules(&self, block: &Block) -> Vec<ModuleId> {
        let mut seen = std::collections::HashSet::new();
        collect_modules_from_block(block, &mut seen);
        let mut modules = seen.into_iter().collect::<Vec<_>>();
        modules.sort_by(|left, right| left.id.name().cmp(right.id.name()));
        modules
    }
}

fn module_side_effect_reason(lam: &Lambda) -> Option<String> {
    match lam {
        Lambda::Llet(kind, id, value, body) => {
            if matches!(kind, LetKind::Strict | LetKind::Variable)
                && !analysis::no_side_effects(value)
            {
                Some(id.name().to_string())
            } else {
                module_side_effect_reason(body)
            }
        }
        Lambda::Lletrec(bindings, body) => bindings
            .iter()
            .find_map(|(id, expr)| {
                (!analysis::no_side_effects(expr)).then(|| id.name().to_string())
            })
            .or_else(|| module_side_effect_reason(body)),
        Lambda::Lsequence(first, second) => {
            if analysis::no_side_effects(first) {
                module_side_effect_reason(second)
            } else {
                Some(String::new())
            }
        }
        _ if analysis::no_side_effects(lam) => None,
        _ => Some(String::new()),
    }
}

fn js_expr_no_side_effects(expr: &Expression) -> bool {
    match &expr.desc {
        ExpressionDesc::Undefined { .. }
        | ExpressionDesc::Null
        | ExpressionDesc::Bool(_)
        | ExpressionDesc::Var(_)
        | ExpressionDesc::Fun { .. }
        | ExpressionDesc::Number(_)
        | ExpressionDesc::Str { .. } => true,
        ExpressionDesc::StaticIndex(target, _, _) => js_expr_no_side_effects(target),
        ExpressionDesc::StringIndex(left, right)
        | ExpressionDesc::ArrayIndex(left, right)
        | ExpressionDesc::In(left, right)
        | ExpressionDesc::StringAppend(left, right)
        | ExpressionDesc::Seq(left, right) => {
            js_expr_no_side_effects(left) && js_expr_no_side_effects(right)
        }
        ExpressionDesc::IsNullOrUndefined(inner)
        | ExpressionDesc::Length(inner, _)
        | ExpressionDesc::Typeof(inner)
        | ExpressionDesc::JsNot(inner)
        | ExpressionDesc::JsBnot(inner)
        | ExpressionDesc::CamlBlockTag(inner, _)
        | ExpressionDesc::OptionalBlock(inner, _) => js_expr_no_side_effects(inner),
        ExpressionDesc::Array(items, _) => items.iter().all(js_expr_no_side_effects),
        ExpressionDesc::CamlBlock(items, _, _, _) => items.iter().all(js_expr_no_side_effects),
        ExpressionDesc::Object(dup, props) => {
            dup.as_deref().is_none_or(js_expr_no_side_effects)
                && props
                    .iter()
                    .all(|(_, value)| js_expr_no_side_effects(value))
        }
        ExpressionDesc::Cond(test, consequent, alternate) => {
            js_expr_no_side_effects(test)
                && js_expr_no_side_effects(consequent)
                && js_expr_no_side_effects(alternate)
        }
        ExpressionDesc::Bin(op, left, right) => {
            *op != BinOp::Eq && js_expr_no_side_effects(left) && js_expr_no_side_effects(right)
        }
        ExpressionDesc::TaggedTemplate(tag, strings, values) => {
            js_expr_no_side_effects(tag)
                && strings.iter().all(js_expr_no_side_effects)
                && values.iter().all(js_expr_no_side_effects)
        }
        ExpressionDesc::FlatCall(_, _)
        | ExpressionDesc::Call(_, _, _)
        | ExpressionDesc::New(_, _)
        | ExpressionDesc::RawJsCode(_)
        | ExpressionDesc::Await(_)
        | ExpressionDesc::Spread(_) => false,
    }
}

fn external_module_import_attributes(
    module_name: &ExternalModuleName,
) -> Option<JsImportAttributes> {
    module_name
        .import_attributes
        .as_ref()?
        .iter()
        .find_map(|(key, value)| {
            (key == "type").then(|| JsImportAttributes {
                type_: value.clone(),
            })
        })
}

fn external_module_ident_name(module_name: &ExternalModuleName) -> String {
    match &module_name.module_bind_name {
        ExternalModuleBindName::HintName(hint) => capitalize_ascii_first(hint),
        ExternalModuleBindName::Nothing => js_id_name_of_hint_name(&module_name.bundle),
    }
}

fn capitalize_ascii_first(s: &str) -> String {
    let mut chars = s.chars();
    match chars.next() {
        None => String::new(),
        Some(first) => {
            let mut out = String::new();
            out.push(first.to_ascii_uppercase());
            out.push_str(chars.as_str());
            out
        }
    }
}

fn good_hint_name(module_name: &str, offset: usize) -> bool {
    let bytes = module_name.as_bytes();
    offset < bytes.len()
        && bytes[offset].is_ascii_alphabetic()
        && bytes[offset + 1..]
            .iter()
            .all(|byte| byte.is_ascii_alphanumeric() || *byte == b'_')
}

fn collect_start(buf: &mut String, s: &[u8], mut offset: usize) {
    while offset < s.len() {
        match s[offset] {
            b'a'..=b'z' => {
                buf.push((s[offset] as char).to_ascii_uppercase());
                collect_next(buf, s, offset + 1);
                return;
            }
            b'A'..=b'Z' => {
                buf.push(s[offset] as char);
                collect_next(buf, s, offset + 1);
                return;
            }
            _ => offset += 1,
        }
    }
}

fn collect_next(buf: &mut String, s: &[u8], mut offset: usize) {
    while offset < s.len() {
        match s[offset] {
            b'a'..=b'z' | b'A'..=b'Z' | b'0'..=b'9' | b'_' => {
                buf.push(s[offset] as char);
                offset += 1;
            }
            b'.' | b'-' => {
                collect_start(buf, s, offset + 1);
                return;
            }
            _ => offset += 1,
        }
    }
}

fn js_id_name_of_hint_name(module_name: &str) -> String {
    let offset = module_name.rfind('/').map_or(0, |index| index + 1);
    if good_hint_name(module_name, offset) {
        capitalize_ascii_first(&module_name[offset..])
    } else {
        let bytes = module_name.as_bytes();
        let mut buf = String::new();
        collect_start(&mut buf, bytes, offset);
        if buf.is_empty() {
            if offset == 0 {
                module_name.to_string()
            } else {
                capitalize_ascii_first(module_name)
            }
        } else {
            buf
        }
    }
}

fn push_effect_expression(block: &mut Block, expr: Expression) {
    match expr.desc {
        ExpressionDesc::Seq(left, right) => {
            push_effect_expression(block, *left);
            push_effect_expression(block, *right);
        }
        _ if js_expr_no_side_effects(&expr) => {}
        _ => block.push(Statement::exp(expr)),
    }
}

fn comparison_to_binop(cmp: Comparison) -> BinOp {
    match cmp {
        Comparison::Eq => BinOp::EqEqEq,
        Comparison::Neq => BinOp::NotEqEq,
        Comparison::Lt => BinOp::Lt,
        Comparison::Le => BinOp::Le,
        Comparison::Gt => BinOp::Gt,
        Comparison::Ge => BinOp::Ge,
    }
}

fn int_expr(value: i32) -> Expression {
    Expression::number(Number::int(value))
}

fn int_literal(expr: &Expression) -> Option<i32> {
    match &expr.desc {
        ExpressionDesc::Number(Number::Int { i, .. }) => Some(*i),
        _ => None,
    }
}

fn is_zero_int(expr: &Expression) -> bool {
    int_literal(expr) == Some(0)
}

fn to_int32(expr: Expression) -> Expression {
    match &expr.desc {
        ExpressionDesc::Bin(BinOp::Bor, _, right) if is_zero_int(right) => expr,
        _ => Expression::bin(BinOp::Bor, expr, int_expr(0)),
    }
}

fn int32_add(left: Expression, right: Expression) -> Expression {
    match (int_literal(&left), int_literal(&right)) {
        (Some(lhs), Some(rhs)) => int_expr(lhs.wrapping_add(rhs)),
        _ => to_int32(Expression::bin(BinOp::Plus, left, right)),
    }
}

fn int32_minus(left: Expression, right: Expression) -> Expression {
    match (int_literal(&left), int_literal(&right)) {
        (Some(lhs), Some(rhs)) => int_expr(lhs.wrapping_sub(rhs)),
        _ => to_int32(Expression::bin(BinOp::Minus, left, right)),
    }
}

fn int32_mul(left: Expression, right: Expression) -> Expression {
    match (int_literal(&left), int_literal(&right)) {
        (Some(lhs), Some(rhs)) => int_expr(lhs.wrapping_mul(rhs)),
        _ => to_int32(Expression::bin(BinOp::Mul, left, right)),
    }
}

fn int32_div(left: Expression, right: Expression) -> Expression {
    to_int32(Expression::bin(BinOp::Div, left, right))
}

fn int32_mod(left: Expression, right: Expression) -> Expression {
    Expression::bin(BinOp::Mod, left, right)
}

fn int32_lsr(left: Expression, right: Expression) -> Expression {
    to_int32(Expression::bin(BinOp::Lsr, left, right))
}

fn int32_offset(expr: Expression, offset: i32) -> Expression {
    if offset == 0 {
        expr
    } else {
        int32_add(expr, int_expr(offset))
    }
}

fn int_bnot(expr: Expression) -> Expression {
    match int_literal(&expr) {
        Some(value) => int_expr(!value),
        None => Expression::new(ExpressionDesc::JsBnot(Box::new(expr))),
    }
}

fn apply_js_flatten_pass(mut deps: DepsProgram) -> DepsProgram {
    deps.program = flatten_program(deps.program);
    deps
}

fn flatten_program(mut program: Program) -> Program {
    program.block = flatten_block(program.block);
    program
}

fn flatten_block(block: Block) -> Block {
    let mut flattened = Vec::new();

    for stmt in block {
        match flatten_statement(stmt) {
            Statement {
                desc: StatementDesc::Block(inner),
                ..
            } => flattened.extend(inner),
            other => flattened.push(other),
        }
    }

    flattened
}

fn flatten_statement(stmt: Statement) -> Statement {
    let Statement { desc, comment } = stmt;

    match desc {
        StatementDesc::Exp(expr) => {
            let Expression {
                desc,
                comment: expr_comment,
            } = expr;

            match desc {
                ExpressionDesc::Seq(_, _) => {
                    let block = flatten_sequence_statements(Expression {
                        desc,
                        comment: expr_comment,
                    });
                    Statement::new(StatementDesc::Block(block))
                }
                ExpressionDesc::CamlBlock(args, _, _, _) => {
                    let block = args
                        .into_iter()
                        .map(|arg| flatten_statement(Statement::exp(arg)))
                        .collect();
                    Statement::new(StatementDesc::Block(block))
                }
                ExpressionDesc::Cond(test, consequent, alternate) => Statement {
                    desc: StatementDesc::If(
                        flatten_expression(*test),
                        vec![flatten_statement(Statement::exp(*consequent))],
                        vec![flatten_statement(Statement::exp(*alternate))],
                    ),
                    comment,
                },
                ExpressionDesc::Bin(BinOp::Eq, target, value) => {
                    if matches!(value.desc, ExpressionDesc::Seq(_, _)) {
                        let mut exprs = Vec::new();
                        flatten_sequence_expressions(*value, &mut exprs);
                        let last = exprs
                            .pop()
                            .expect("sequence flattening must produce at least one expression");
                        let mut block: Block = exprs
                            .into_iter()
                            .map(|expr| flatten_statement(Statement::exp(expr)))
                            .collect();
                        block.push(flatten_statement(Statement::exp(Expression::bin(
                            BinOp::Eq,
                            *target,
                            last,
                        ))));
                        Statement::new(StatementDesc::Block(block))
                    } else {
                        Statement {
                            desc: StatementDesc::Exp(flatten_expression(Expression {
                                desc: ExpressionDesc::Bin(BinOp::Eq, target, value),
                                comment: expr_comment,
                            })),
                            comment,
                        }
                    }
                }
                desc => Statement {
                    desc: StatementDesc::Exp(flatten_expression(Expression {
                        desc,
                        comment: expr_comment,
                    })),
                    comment,
                },
            }
        }
        StatementDesc::Return(expr) => {
            let Expression {
                desc,
                comment: expr_comment,
            } = expr;

            match desc {
                ExpressionDesc::Cond(test, consequent, alternate) => Statement {
                    desc: StatementDesc::If(
                        flatten_expression(*test),
                        vec![flatten_statement(Statement::return_(*consequent))],
                        vec![flatten_statement(Statement::return_(*alternate))],
                    ),
                    comment,
                },
                ExpressionDesc::Seq(_, _) => {
                    let mut exprs = Vec::new();
                    flatten_sequence_expressions(
                        Expression {
                            desc,
                            comment: expr_comment,
                        },
                        &mut exprs,
                    );
                    let last = exprs
                        .pop()
                        .expect("return sequence flattening must produce at least one expression");
                    let mut block: Block = exprs
                        .into_iter()
                        .map(|expr| flatten_statement(Statement::exp(expr)))
                        .collect();
                    block.push(flatten_statement(Statement::return_(last)));
                    Statement::new(StatementDesc::Block(block))
                }
                desc => Statement {
                    desc: StatementDesc::Return(flatten_expression(Expression {
                        desc,
                        comment: expr_comment,
                    })),
                    comment,
                },
            }
        }
        StatementDesc::Block(block) => {
            if block.len() == 1 {
                flatten_statement(block.into_iter().next().expect("single-item block"))
            } else {
                Statement {
                    desc: StatementDesc::Block(flatten_block(block)),
                    comment,
                }
            }
        }
        StatementDesc::Variable(decl) => Statement {
            desc: StatementDesc::Variable(VariableDeclaration {
                ident: decl.ident,
                value: decl.value.map(flatten_expression),
                property: decl.property,
                ident_info: decl.ident_info,
            }),
            comment,
        },
        StatementDesc::If(cond, then_block, else_block) => Statement {
            desc: StatementDesc::If(
                flatten_expression(cond),
                flatten_block(then_block),
                flatten_block(else_block),
            ),
            comment,
        },
        StatementDesc::While(cond, body) => Statement {
            desc: StatementDesc::While(flatten_expression(cond), flatten_block(body)),
            comment,
        },
        StatementDesc::ForRange(start, finish, ident, direction, body) => Statement {
            desc: StatementDesc::ForRange(
                start.map(flatten_expression),
                flatten_expression(finish),
                ident,
                direction,
                flatten_block(body),
            ),
            comment,
        },
        StatementDesc::IntSwitch(test, clauses, default) => Statement {
            desc: StatementDesc::IntSwitch(
                flatten_expression(test),
                clauses
                    .into_iter()
                    .map(|(tag, clause)| (tag, flatten_case_clause(clause)))
                    .collect(),
                default.map(flatten_block),
            ),
            comment,
        },
        StatementDesc::StringSwitch(test, clauses, default) => Statement {
            desc: StatementDesc::StringSwitch(
                flatten_expression(test),
                clauses
                    .into_iter()
                    .map(|clause| StringClause {
                        tag_type: clause.tag_type,
                        clause: flatten_case_clause(clause.clause),
                    })
                    .collect(),
                default.map(flatten_block),
            ),
            comment,
        },
        StatementDesc::Throw(expr) => Statement {
            desc: StatementDesc::Throw(flatten_expression(expr)),
            comment,
        },
        StatementDesc::Try(body, catch, finally) => Statement {
            desc: StatementDesc::Try(
                flatten_block(body),
                catch.map(|(id, block)| (id, flatten_block(block))),
                finally.map(flatten_block),
            ),
            comment,
        },
        StatementDesc::Debugger => Statement {
            desc: StatementDesc::Debugger,
            comment,
        },
        StatementDesc::Break => Statement {
            desc: StatementDesc::Break,
            comment,
        },
        StatementDesc::Continue => Statement {
            desc: StatementDesc::Continue,
            comment,
        },
    }
}

fn flatten_case_clause(clause: CaseClause) -> CaseClause {
    CaseClause {
        body: flatten_block(clause.body),
        should_break: clause.should_break,
        comment: clause.comment,
    }
}

fn flatten_expression(expr: Expression) -> Expression {
    let comment = expr.comment;
    let desc = match expr.desc {
        ExpressionDesc::Length(inner, object) => {
            ExpressionDesc::Length(Box::new(flatten_expression(*inner)), object)
        }
        ExpressionDesc::IsNullOrUndefined(inner) => {
            ExpressionDesc::IsNullOrUndefined(Box::new(flatten_expression(*inner)))
        }
        ExpressionDesc::StringAppend(left, right) => ExpressionDesc::StringAppend(
            Box::new(flatten_expression(*left)),
            Box::new(flatten_expression(*right)),
        ),
        ExpressionDesc::Bool(value) => ExpressionDesc::Bool(value),
        ExpressionDesc::Typeof(inner) => {
            ExpressionDesc::Typeof(Box::new(flatten_expression(*inner)))
        }
        ExpressionDesc::In(left, right) => ExpressionDesc::In(
            Box::new(flatten_expression(*left)),
            Box::new(flatten_expression(*right)),
        ),
        ExpressionDesc::JsNot(inner) => ExpressionDesc::JsNot(Box::new(flatten_expression(*inner))),
        ExpressionDesc::JsBnot(inner) => {
            ExpressionDesc::JsBnot(Box::new(flatten_expression(*inner)))
        }
        ExpressionDesc::Seq(left, right) => ExpressionDesc::Seq(
            Box::new(flatten_expression(*left)),
            Box::new(flatten_expression(*right)),
        ),
        ExpressionDesc::Cond(test, consequent, alternate) => ExpressionDesc::Cond(
            Box::new(flatten_expression(*test)),
            Box::new(flatten_expression(*consequent)),
            Box::new(flatten_expression(*alternate)),
        ),
        ExpressionDesc::Bin(op, left, right) => ExpressionDesc::Bin(
            op,
            Box::new(flatten_expression(*left)),
            Box::new(flatten_expression(*right)),
        ),
        ExpressionDesc::FlatCall(func, args) => ExpressionDesc::FlatCall(
            Box::new(flatten_expression(*func)),
            Box::new(flatten_expression(*args)),
        ),
        ExpressionDesc::Call(func, args, info) => ExpressionDesc::Call(
            Box::new(flatten_expression(*func)),
            args.into_iter().map(flatten_expression).collect(),
            info,
        ),
        ExpressionDesc::StringIndex(left, right) => ExpressionDesc::StringIndex(
            Box::new(flatten_expression(*left)),
            Box::new(flatten_expression(*right)),
        ),
        ExpressionDesc::ArrayIndex(left, right) => ExpressionDesc::ArrayIndex(
            Box::new(flatten_expression(*left)),
            Box::new(flatten_expression(*right)),
        ),
        ExpressionDesc::TaggedTemplate(tag, strings, values) => ExpressionDesc::TaggedTemplate(
            Box::new(flatten_expression(*tag)),
            strings.into_iter().map(flatten_expression).collect(),
            values.into_iter().map(flatten_expression).collect(),
        ),
        ExpressionDesc::StaticIndex(target, field, pos) => {
            ExpressionDesc::StaticIndex(Box::new(flatten_expression(*target)), field, pos)
        }
        ExpressionDesc::New(target, args) => ExpressionDesc::New(
            Box::new(flatten_expression(*target)),
            args.map(|args| args.into_iter().map(flatten_expression).collect()),
        ),
        ExpressionDesc::Var(var) => ExpressionDesc::Var(var),
        ExpressionDesc::Fun {
            is_method,
            params,
            body,
            env,
            return_unit,
            async_,
            directive,
        } => ExpressionDesc::Fun {
            is_method,
            params,
            body: flatten_block(body),
            env,
            return_unit,
            async_,
            directive,
        },
        ExpressionDesc::Str { delim, txt } => ExpressionDesc::Str { delim, txt },
        ExpressionDesc::RawJsCode(info) => ExpressionDesc::RawJsCode(info),
        ExpressionDesc::Array(items, mutable_flag) => ExpressionDesc::Array(
            items.into_iter().map(flatten_expression).collect(),
            mutable_flag,
        ),
        ExpressionDesc::OptionalBlock(inner, flag) => {
            ExpressionDesc::OptionalBlock(Box::new(flatten_expression(*inner)), flag)
        }
        ExpressionDesc::CamlBlock(items, mutable_flag, tag, tag_info) => ExpressionDesc::CamlBlock(
            items.into_iter().map(flatten_expression).collect(),
            mutable_flag,
            Box::new(flatten_expression(*tag)),
            tag_info,
        ),
        ExpressionDesc::CamlBlockTag(inner, tag) => {
            ExpressionDesc::CamlBlockTag(Box::new(flatten_expression(*inner)), tag)
        }
        ExpressionDesc::Number(number) => ExpressionDesc::Number(number),
        ExpressionDesc::Object(dup, props) => ExpressionDesc::Object(
            dup.map(|dup| Box::new(flatten_expression(*dup))),
            props
                .into_iter()
                .map(|(name, value)| (name, flatten_expression(value)))
                .collect(),
        ),
        ExpressionDesc::Undefined { is_unit } => ExpressionDesc::Undefined { is_unit },
        ExpressionDesc::Null => ExpressionDesc::Null,
        ExpressionDesc::Await(inner) => ExpressionDesc::Await(Box::new(flatten_expression(*inner))),
        ExpressionDesc::Spread(inner) => {
            ExpressionDesc::Spread(Box::new(flatten_expression(*inner)))
        }
    };

    Expression { desc, comment }
}

fn flatten_sequence_statements(expr: Expression) -> Block {
    let mut exprs = Vec::new();
    flatten_sequence_expressions(expr, &mut exprs);
    exprs
        .into_iter()
        .map(|expr| flatten_statement(Statement::exp(expr)))
        .collect()
}

fn flatten_sequence_expressions(expr: Expression, out: &mut Vec<Expression>) {
    match expr.desc {
        ExpressionDesc::Seq(left, right) => {
            flatten_sequence_expressions(*left, out);
            flatten_sequence_expressions(*right, out);
        }
        desc => out.push(Expression {
            desc,
            comment: expr.comment,
        }),
    }
}

fn apply_external_shadow_pass(mut deps: DepsProgram) -> DepsProgram {
    let shadowed_globals = deps
        .program
        .block
        .iter()
        .filter_map(|stmt| match &stmt.desc {
            StatementDesc::Variable(VariableDeclaration {
                ident, property, ..
            }) if is_lexical_binding_kind(*property) && should_rewrite_binding(ident) => {
                Some(ident.name().to_string())
            }
            _ => None,
        })
        .collect::<HashSet<_>>();

    if shadowed_globals.is_empty() {
        return deps;
    }

    deps.program.block = rewrite_block(&deps.program.block, &shadowed_globals);
    deps
}

fn is_lexical_binding_kind(property: LetKind) -> bool {
    matches!(
        property,
        LetKind::Strict | LetKind::StrictOpt | LetKind::Alias
    )
}

fn should_rewrite_binding(ident: &Ident) -> bool {
    !ident.is_global() && !is_js_keyword_or_global(ident.name())
}

fn rewrite_block(block: &Block, shadowed_globals: &HashSet<String>) -> Block {
    block
        .iter()
        .map(|stmt| rewrite_statement(stmt, shadowed_globals))
        .collect()
}

fn rewrite_statement(stmt: &Statement, shadowed_globals: &HashSet<String>) -> Statement {
    let desc = match &stmt.desc {
        StatementDesc::Block(block) => StatementDesc::Block(rewrite_block(block, shadowed_globals)),
        StatementDesc::Variable(decl) => {
            let value = decl.value.as_ref().map(|value| {
                let value = if is_lexical_binding_kind(decl.property)
                    && should_rewrite_binding(&decl.ident)
                {
                    rewrite_shadowed_global_in_expr(value, decl.ident.name())
                } else {
                    value.clone()
                };
                rewrite_global_static_index_expr(&value, shadowed_globals)
            });
            StatementDesc::Variable(VariableDeclaration {
                ident: decl.ident.clone(),
                value,
                property: decl.property,
                ident_info: decl.ident_info.clone(),
            })
        }
        StatementDesc::Exp(expr) => {
            StatementDesc::Exp(rewrite_global_static_index_expr(expr, shadowed_globals))
        }
        StatementDesc::If(cond, then_block, else_block) => StatementDesc::If(
            rewrite_global_static_index_expr(cond, shadowed_globals),
            rewrite_block(then_block, shadowed_globals),
            rewrite_block(else_block, shadowed_globals),
        ),
        StatementDesc::While(cond, body) => StatementDesc::While(
            rewrite_global_static_index_expr(cond, shadowed_globals),
            rewrite_block(body, shadowed_globals),
        ),
        StatementDesc::ForRange(init, end, id, direction, body) => StatementDesc::ForRange(
            init.as_ref()
                .map(|expr| rewrite_global_static_index_expr(expr, shadowed_globals)),
            rewrite_global_static_index_expr(end, shadowed_globals),
            id.clone(),
            *direction,
            rewrite_block(body, shadowed_globals),
        ),
        StatementDesc::Continue => StatementDesc::Continue,
        StatementDesc::Break => StatementDesc::Break,
        StatementDesc::Return(expr) => {
            StatementDesc::Return(rewrite_global_static_index_expr(expr, shadowed_globals))
        }
        StatementDesc::IntSwitch(expr, clauses, default) => StatementDesc::IntSwitch(
            rewrite_global_static_index_expr(expr, shadowed_globals),
            clauses
                .iter()
                .map(|(value, clause)| (*value, rewrite_case_clause(clause, shadowed_globals)))
                .collect(),
            default
                .as_ref()
                .map(|block| rewrite_block(block, shadowed_globals)),
        ),
        StatementDesc::StringSwitch(expr, clauses, default) => StatementDesc::StringSwitch(
            rewrite_global_static_index_expr(expr, shadowed_globals),
            clauses
                .iter()
                .map(|clause| crate::js_ir::StringClause {
                    tag_type: clause.tag_type.clone(),
                    clause: rewrite_case_clause(&clause.clause, shadowed_globals),
                })
                .collect(),
            default
                .as_ref()
                .map(|block| rewrite_block(block, shadowed_globals)),
        ),
        StatementDesc::Throw(expr) => {
            StatementDesc::Throw(rewrite_global_static_index_expr(expr, shadowed_globals))
        }
        StatementDesc::Try(body, catch, finally) => StatementDesc::Try(
            rewrite_block(body, shadowed_globals),
            catch
                .as_ref()
                .map(|(ident, block)| (ident.clone(), rewrite_block(block, shadowed_globals))),
            finally
                .as_ref()
                .map(|block| rewrite_block(block, shadowed_globals)),
        ),
        StatementDesc::Debugger => StatementDesc::Debugger,
    };

    Statement {
        desc,
        comment: stmt.comment.clone(),
    }
}

fn rewrite_case_clause(
    clause: &crate::js_ir::CaseClause,
    shadowed_globals: &HashSet<String>,
) -> crate::js_ir::CaseClause {
    crate::js_ir::CaseClause {
        body: rewrite_block(&clause.body, shadowed_globals),
        should_break: clause.should_break,
        comment: clause.comment.clone(),
    }
}

fn rewrite_shadowed_global_in_expr(expr: &Expression, name: &str) -> Expression {
    let expr = rewrite_expr_children(expr, &|child| rewrite_shadowed_global_in_expr(child, name));
    match &expr.desc {
        ExpressionDesc::Var(crate::js_ir::VIdent::Id(id))
            if id.is_global() && id.name() == name =>
        {
            global_this_field(name)
        }
        _ => expr,
    }
}

fn rewrite_global_static_index_expr(
    expr: &Expression,
    shadowed_globals: &HashSet<String>,
) -> Expression {
    let expr = rewrite_expr_children(expr, &|child| {
        rewrite_global_static_index_expr(child, shadowed_globals)
    });
    match &expr.desc {
        ExpressionDesc::StaticIndex(obj, field, pos) => match &obj.desc {
            ExpressionDesc::Var(crate::js_ir::VIdent::Id(id))
                if id.is_global() && shadowed_globals.contains(id.name()) =>
            {
                Expression::new(ExpressionDesc::StaticIndex(
                    Box::new(global_this_field(id.name())),
                    field.clone(),
                    *pos,
                ))
            }
            _ => expr,
        },
        _ => expr,
    }
}

fn rewrite_expr_children(
    expr: &Expression,
    rewrite: &impl Fn(&Expression) -> Expression,
) -> Expression {
    let desc = match &expr.desc {
        ExpressionDesc::Length(inner, kind) => {
            ExpressionDesc::Length(Box::new(rewrite(inner)), kind.clone())
        }
        ExpressionDesc::IsNullOrUndefined(inner) => {
            ExpressionDesc::IsNullOrUndefined(Box::new(rewrite(inner)))
        }
        ExpressionDesc::StringAppend(left, right) => {
            ExpressionDesc::StringAppend(Box::new(rewrite(left)), Box::new(rewrite(right)))
        }
        ExpressionDesc::Bool(value) => ExpressionDesc::Bool(*value),
        ExpressionDesc::Typeof(inner) => ExpressionDesc::Typeof(Box::new(rewrite(inner))),
        ExpressionDesc::In(left, right) => {
            ExpressionDesc::In(Box::new(rewrite(left)), Box::new(rewrite(right)))
        }
        ExpressionDesc::JsNot(inner) => ExpressionDesc::JsNot(Box::new(rewrite(inner))),
        ExpressionDesc::JsBnot(inner) => ExpressionDesc::JsBnot(Box::new(rewrite(inner))),
        ExpressionDesc::Seq(first, second) => {
            ExpressionDesc::Seq(Box::new(rewrite(first)), Box::new(rewrite(second)))
        }
        ExpressionDesc::Cond(cond, then_, else_) => ExpressionDesc::Cond(
            Box::new(rewrite(cond)),
            Box::new(rewrite(then_)),
            Box::new(rewrite(else_)),
        ),
        ExpressionDesc::Bin(op, left, right) => {
            ExpressionDesc::Bin(*op, Box::new(rewrite(left)), Box::new(rewrite(right)))
        }
        ExpressionDesc::FlatCall(func, args) => {
            ExpressionDesc::FlatCall(Box::new(rewrite(func)), Box::new(rewrite(args)))
        }
        ExpressionDesc::Call(func, args, info) => ExpressionDesc::Call(
            Box::new(rewrite(func)),
            args.iter().map(rewrite).collect(),
            info.clone(),
        ),
        ExpressionDesc::StringIndex(value, index) => {
            ExpressionDesc::StringIndex(Box::new(rewrite(value)), Box::new(rewrite(index)))
        }
        ExpressionDesc::ArrayIndex(value, index) => {
            ExpressionDesc::ArrayIndex(Box::new(rewrite(value)), Box::new(rewrite(index)))
        }
        ExpressionDesc::TaggedTemplate(func, strings, values) => ExpressionDesc::TaggedTemplate(
            Box::new(rewrite(func)),
            strings.iter().map(rewrite).collect(),
            values.iter().map(rewrite).collect(),
        ),
        ExpressionDesc::StaticIndex(obj, field, pos) => {
            ExpressionDesc::StaticIndex(Box::new(rewrite(obj)), field.clone(), *pos)
        }
        ExpressionDesc::New(ctor, args) => ExpressionDesc::New(
            Box::new(rewrite(ctor)),
            args.as_ref()
                .map(|items| items.iter().map(rewrite).collect()),
        ),
        ExpressionDesc::Var(vident) => ExpressionDesc::Var(vident.clone()),
        ExpressionDesc::Fun {
            is_method,
            params,
            body,
            env,
            return_unit,
            async_,
            directive,
        } => ExpressionDesc::Fun {
            is_method: *is_method,
            params: params.clone(),
            body: rewrite_block(body, &HashSet::new()),
            env: env.clone(),
            return_unit: *return_unit,
            async_: *async_,
            directive: directive.clone(),
        },
        ExpressionDesc::Str { delim, txt } => ExpressionDesc::Str {
            delim: *delim,
            txt: txt.clone(),
        },
        ExpressionDesc::RawJsCode(info) => ExpressionDesc::RawJsCode(info.clone()),
        ExpressionDesc::Array(items, mutable_flag) => {
            ExpressionDesc::Array(items.iter().map(rewrite).collect(), *mutable_flag)
        }
        ExpressionDesc::OptionalBlock(value, flag) => {
            ExpressionDesc::OptionalBlock(Box::new(rewrite(value)), *flag)
        }
        ExpressionDesc::CamlBlock(values, mutable_flag, tag, tag_info) => {
            ExpressionDesc::CamlBlock(
                values.iter().map(rewrite).collect(),
                *mutable_flag,
                Box::new(rewrite(tag)),
                tag_info.clone(),
            )
        }
        ExpressionDesc::CamlBlockTag(value, tag) => {
            ExpressionDesc::CamlBlockTag(Box::new(rewrite(value)), tag.clone())
        }
        ExpressionDesc::Number(number) => ExpressionDesc::Number(number.clone()),
        ExpressionDesc::Object(proto, props) => ExpressionDesc::Object(
            proto.as_ref().map(|expr| Box::new(rewrite(expr))),
            props
                .iter()
                .map(|(name, value)| (name.clone(), rewrite(value)))
                .collect(),
        ),
        ExpressionDesc::Undefined { is_unit } => ExpressionDesc::Undefined { is_unit: *is_unit },
        ExpressionDesc::Null => ExpressionDesc::Null,
        ExpressionDesc::Await(inner) => ExpressionDesc::Await(Box::new(rewrite(inner))),
        ExpressionDesc::Spread(inner) => ExpressionDesc::Spread(Box::new(rewrite(inner))),
    };

    Expression {
        desc,
        comment: expr.comment.clone(),
    }
}

fn global_this_field(name: &str) -> Expression {
    Expression::new(ExpressionDesc::StaticIndex(
        Box::new(Expression::var(Ident::create_persistent("globalThis"))),
        name.to_string(),
        None,
    ))
}

fn collect_modules_from_block(block: &Block, seen: &mut std::collections::HashSet<ModuleId>) {
    for stmt in block {
        collect_modules_from_statement(stmt, seen);
    }
}

fn collect_modules_from_statement(
    stmt: &Statement,
    seen: &mut std::collections::HashSet<ModuleId>,
) {
    match &stmt.desc {
        StatementDesc::Block(block) => collect_modules_from_block(block, seen),
        StatementDesc::Variable(decl) => {
            if let Some(value) = &decl.value {
                collect_modules_from_expression(value, seen);
            }
        }
        StatementDesc::Exp(expr) | StatementDesc::Throw(expr) | StatementDesc::Return(expr) => {
            collect_modules_from_expression(expr, seen)
        }
        StatementDesc::If(cond, then_block, else_block) => {
            collect_modules_from_expression(cond, seen);
            collect_modules_from_block(then_block, seen);
            collect_modules_from_block(else_block, seen);
        }
        StatementDesc::While(cond, body) => {
            collect_modules_from_expression(cond, seen);
            collect_modules_from_block(body, seen);
        }
        StatementDesc::ForRange(init, finish, _, _, body) => {
            if let Some(init) = init {
                collect_modules_from_expression(init, seen);
            }
            collect_modules_from_expression(finish, seen);
            collect_modules_from_block(body, seen);
        }
        StatementDesc::IntSwitch(expr, clauses, default) => {
            collect_modules_from_expression(expr, seen);
            for (_, clause) in clauses {
                collect_modules_from_block(&clause.body, seen);
            }
            if let Some(default) = default {
                collect_modules_from_block(default, seen);
            }
        }
        StatementDesc::StringSwitch(expr, clauses, default) => {
            collect_modules_from_expression(expr, seen);
            for clause in clauses {
                collect_modules_from_block(&clause.clause.body, seen);
            }
            if let Some(default) = default {
                collect_modules_from_block(default, seen);
            }
        }
        StatementDesc::Try(body, handler, finalizer) => {
            collect_modules_from_block(body, seen);
            if let Some((_, handler_block)) = handler {
                collect_modules_from_block(handler_block, seen);
            }
            if let Some(finalizer_block) = finalizer {
                collect_modules_from_block(finalizer_block, seen);
            }
        }
        StatementDesc::Debugger | StatementDesc::Break | StatementDesc::Continue => {}
    }
}

fn collect_modules_from_expression(
    expr: &Expression,
    seen: &mut std::collections::HashSet<ModuleId>,
) {
    match &expr.desc {
        ExpressionDesc::Var(crate::js_ir::VIdent::Qualified(module, _)) => {
            if !module.dynamic_import {
                seen.insert(module.clone());
            }
        }
        ExpressionDesc::Length(inner, _)
        | ExpressionDesc::IsNullOrUndefined(inner)
        | ExpressionDesc::Typeof(inner)
        | ExpressionDesc::JsNot(inner)
        | ExpressionDesc::JsBnot(inner)
        | ExpressionDesc::Await(inner)
        | ExpressionDesc::Spread(inner)
        | ExpressionDesc::CamlBlockTag(inner, _)
        | ExpressionDesc::OptionalBlock(inner, _) => collect_modules_from_expression(inner, seen),
        ExpressionDesc::StringAppend(left, right)
        | ExpressionDesc::Seq(left, right)
        | ExpressionDesc::Bin(_, left, right)
        | ExpressionDesc::StringIndex(left, right)
        | ExpressionDesc::ArrayIndex(left, right)
        | ExpressionDesc::In(left, right) => {
            collect_modules_from_expression(left, seen);
            collect_modules_from_expression(right, seen);
        }
        ExpressionDesc::Cond(test, consequent, alternate) => {
            collect_modules_from_expression(test, seen);
            collect_modules_from_expression(consequent, seen);
            collect_modules_from_expression(alternate, seen);
        }
        ExpressionDesc::FlatCall(func, args) => {
            collect_modules_from_expression(func, seen);
            collect_modules_from_expression(args, seen);
        }
        ExpressionDesc::Call(func, args, _) => {
            collect_modules_from_expression(func, seen);
            for arg in args {
                collect_modules_from_expression(arg, seen);
            }
        }
        ExpressionDesc::TaggedTemplate(tag, strings, values) => {
            collect_modules_from_expression(tag, seen);
            for string in strings {
                collect_modules_from_expression(string, seen);
            }
            for value in values {
                collect_modules_from_expression(value, seen);
            }
        }
        ExpressionDesc::StaticIndex(target, _, _) => collect_modules_from_expression(target, seen),
        ExpressionDesc::New(target, args) => {
            collect_modules_from_expression(target, seen);
            if let Some(args) = args {
                for arg in args {
                    collect_modules_from_expression(arg, seen);
                }
            }
        }
        ExpressionDesc::Fun { body, .. } => collect_modules_from_block(body, seen),
        ExpressionDesc::Array(items, _) => {
            for item in items {
                collect_modules_from_expression(item, seen);
            }
        }
        ExpressionDesc::CamlBlock(items, _, tag, _) => {
            for item in items {
                collect_modules_from_expression(item, seen);
            }
            collect_modules_from_expression(tag, seen);
        }
        ExpressionDesc::Object(dup, props) => {
            if let Some(dup) = dup {
                collect_modules_from_expression(dup, seen);
            }
            for (_, value) in props {
                collect_modules_from_expression(value, seen);
            }
        }
        ExpressionDesc::Bool(_)
        | ExpressionDesc::Var(crate::js_ir::VIdent::Id(_))
        | ExpressionDesc::Str { .. }
        | ExpressionDesc::RawJsCode(_)
        | ExpressionDesc::Number(_)
        | ExpressionDesc::Undefined { .. }
        | ExpressionDesc::Null => {}
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cmi::persistent_env::PersistentEnv;
    use crate::js_ir::{print_block, ModulePathResolver};
    use crate::lambda::constant::Constant;
    use crate::lambda::primitive::{
        ExternalArgAttr, ExternalArgConst, ExternalArgDelim, ExternalArgLabel, ExternalArgSpec,
        ExternalFfiKind, ExternalFfiSpec, ExternalModuleBindName, ExternalModuleName,
        ExternalObjLabel, ExternalObjSpec, ExternalReturnWrapper, ExternalSpec,
    };
    use crate::lambda::{ApInfo, Apply, ApplyStatus, InlineAttribute, Lambda};
    use crate::location::Location;
    use std::fs;
    use tempfile::tempdir;

    fn write_ast_source_stub(ast_path: &std::path::Path, source_path: &std::path::Path) {
        let mut bytes = Vec::new();
        bytes.extend_from_slice(&0u32.to_be_bytes());
        bytes.extend_from_slice(source_path.to_string_lossy().as_bytes());
        bytes.push(b'\n');
        fs::write(ast_path, bytes).expect("failed to write ast source stub");
    }

    fn external_module(bundle: &str) -> ExternalModuleName {
        ExternalModuleName {
            bundle: bundle.to_string(),
            module_bind_name: ExternalModuleBindName::Nothing,
            import_attributes: None,
        }
    }

    #[test]
    fn test_compile_constant_int() {
        let mut compiler = LambdaCompiler::new();
        let lam = Lambda::const_(Constant::int(7));
        let program = compiler.compile_program(&lam);
        assert!(!program.block.is_empty());
    }

    #[test]
    fn lowers_expression_sequences_to_js_comma_expressions() {
        let mut compiler = LambdaCompiler::new();
        let callback = Ident::create_local("callback");
        let sequence = Lambda::Lsequence(
            Box::new(Lambda::Lapply(Apply {
                ap_func: Box::new(Lambda::var(callback.clone())),
                ap_args: vec![],
                ap_info: ApInfo {
                    loc: Location::none(),
                    inlined: InlineAttribute::Default,
                    status: ApplyStatus::Na,
                },
                ap_transformed_jsx: false,
            })),
            Box::new(Lambda::const_(Constant::none())),
        );
        let program = compiler.compile_program(&Lambda::prim(
            Primitive::Pmakearray,
            vec![sequence],
            Location::none(),
        ));

        let [stmt] = program.block.as_slice() else {
            panic!("expected a single expression statement");
        };
        match &stmt.desc {
            StatementDesc::Exp(Expression {
                desc: ExpressionDesc::Array(items, _),
                ..
            }) => {
                let [item] = items.as_slice() else {
                    panic!("expected a single array element");
                };
                match &item.desc {
                    ExpressionDesc::Seq(first, second) => {
                        assert!(matches!(
                            first.as_ref(),
                            Expression {
                                desc: ExpressionDesc::Call(func, args, _),
                                ..
                            } if args.is_empty() && matches!(
                                func.as_ref(),
                                Expression {
                                    desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                                    ..
                                } if id.same(&callback)
                            )
                        ));
                        assert!(matches!(
                            second.as_ref(),
                            Expression {
                                desc: ExpressionDesc::Undefined { is_unit: false },
                                ..
                            }
                        ));
                    }
                    other => panic!("expected comma expression inside array, got {other:?}"),
                }
            }
            other => panic!("expected array literal output, got {other:?}"),
        }
    }

    #[test]
    fn drops_pure_sequence_prefixes_in_effect_contexts() {
        let mut compiler = LambdaCompiler::new();
        let value = Ident::create_local("value");
        let lam = Lambda::Lsequence(
            Box::new(Lambda::const_(Constant::int(1))),
            Box::new(Lambda::var(value.clone())),
        );
        let program = compiler.compile_program(&lam);

        let [stmt] = program.block.as_slice() else {
            panic!("expected a single expression statement");
        };
        match &stmt.desc {
            StatementDesc::Exp(Expression {
                desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                ..
            }) => assert!(id.same(&value)),
            other => panic!("expected pure sequence prefix to be removed, got {other:?}"),
        }
    }

    #[test]
    fn flattens_value_sequences_back_to_effect_statements_at_toplevel() {
        let mut compiler = LambdaCompiler::new();
        let callback = Ident::create_local("callback");
        let lam = Lambda::Lsequence(
            Box::new(Lambda::Lapply(Apply {
                ap_func: Box::new(Lambda::var(callback.clone())),
                ap_args: vec![],
                ap_info: ApInfo {
                    loc: Location::none(),
                    inlined: InlineAttribute::Default,
                    status: ApplyStatus::Na,
                },
                ap_transformed_jsx: false,
            })),
            Box::new(Lambda::const_(Constant::none())),
        );
        let program = compiler.compile_program(&lam);

        let [stmt] = program.block.as_slice() else {
            panic!("expected a single expression statement");
        };
        match &stmt.desc {
            StatementDesc::Exp(Expression {
                desc: ExpressionDesc::Call(func, args, _),
                ..
            }) => {
                assert!(args.is_empty());
                assert!(matches!(
                    func.as_ref(),
                    Expression {
                        desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                        ..
                    } if id.same(&callback)
                ));
            }
            other => {
                panic!("expected top-level sequence to flatten to a call statement, got {other:?}")
            }
        }
    }

    #[test]
    fn function_bodies_drop_pure_undefined_sequence_suffixes() {
        let mut compiler = LambdaCompiler::new();
        let callback = Ident::create_local("callback");
        let value = Ident::create_local("value");
        let call = || {
            Lambda::Lapply(Apply {
                ap_func: Box::new(Lambda::var(callback.clone())),
                ap_args: vec![],
                ap_info: ApInfo {
                    loc: Location::none(),
                    inlined: InlineAttribute::Default,
                    status: ApplyStatus::Na,
                },
                ap_transformed_jsx: false,
            })
        };
        let body = Lambda::Lsequence(
            Box::new(Lambda::Lsequence(
                Box::new(call()),
                Box::new(Lambda::const_(Constant::none())),
            )),
            Box::new(Lambda::Lsequence(
                Box::new(Lambda::Lsequence(
                    Box::new(call()),
                    Box::new(Lambda::const_(Constant::none())),
                )),
                Box::new(Lambda::var(value.clone())),
            )),
        );
        let compiled = compiler.compile_expr(&Lambda::Lfunction(crate::lambda::LFunction {
            arity: 1,
            params: vec![value.clone()],
            body: Box::new(body),
            attr: crate::lambda::FunctionAttribute::default(),
        }));

        let Expression {
            desc: ExpressionDesc::Fun { body, .. },
            ..
        } = compiled.expr
        else {
            panic!("expected a function expression");
        };

        let [first, second, third] = body.as_slice() else {
            panic!("expected two effect statements followed by a return");
        };

        for stmt in [first, second] {
            match &stmt.desc {
                StatementDesc::Exp(Expression {
                    desc: ExpressionDesc::Call(func, args, _),
                    ..
                }) => {
                    assert!(args.is_empty());
                    assert!(matches!(
                        func.as_ref(),
                        Expression {
                            desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                            ..
                        } if id.same(&callback)
                    ));
                }
                other => panic!("expected a callback call statement, got {other:?}"),
            }
        }

        match &third.desc {
            StatementDesc::Return(Expression {
                desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                ..
            }) => assert!(id.same(&value)),
            other => panic!("expected a return of the original value, got {other:?}"),
        }
    }

    #[test]
    fn js_flatten_pass_splits_function_return_sequences_into_statements() {
        let function_ident = Ident::create_local("run");
        let callback = Ident::create_local("callback");
        let deps = apply_js_flatten_pass(DepsProgram {
            program: Program::new(
                vec![Statement::variable(VariableDeclaration {
                    ident: function_ident,
                    value: Some(Expression::new(ExpressionDesc::Fun {
                        is_method: false,
                        params: vec![],
                        body: vec![Statement::return_(Expression::new(ExpressionDesc::Seq(
                            Box::new(Expression::call(
                                Expression::var(callback.clone()),
                                vec![],
                                CallInfo::default(),
                            )),
                            Box::new(Expression::undefined(false)),
                        )))],
                        env: Default::default(),
                        return_unit: false,
                        async_: false,
                        directive: None,
                    })),
                    property: LetKind::Strict,
                    ident_info: IdentInfo::default(),
                })],
                vec![],
            ),
            modules: vec![],
            side_effect: None,
        });

        let [stmt] = deps.program.block.as_slice() else {
            panic!("expected one top-level statement");
        };
        let StatementDesc::Variable(VariableDeclaration {
            value:
                Some(Expression {
                    desc: ExpressionDesc::Fun { body, .. },
                    ..
                }),
            ..
        }) = &stmt.desc
        else {
            panic!("expected a function-valued variable declaration");
        };

        let [first, second] = body.as_slice() else {
            panic!("expected flattened function body");
        };
        match &first.desc {
            StatementDesc::Exp(Expression {
                desc: ExpressionDesc::Call(func, args, _),
                ..
            }) => {
                assert!(args.is_empty());
                assert!(matches!(
                    func.as_ref(),
                    Expression {
                        desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                        ..
                    } if id.same(&callback)
                ));
            }
            other => panic!("expected callback expression statement, got {other:?}"),
        }
        match &second.desc {
            StatementDesc::Return(Expression {
                desc: ExpressionDesc::Undefined { is_unit: false },
                ..
            }) => {}
            other => panic!("expected return undefined after flattening, got {other:?}"),
        }
    }

    #[test]
    fn js_flatten_pass_turns_conditional_effects_into_if_statements() {
        let then_callback = Ident::create_local("thenCallback");
        let else_callback = Ident::create_local("elseCallback");
        let deps = apply_js_flatten_pass(DepsProgram {
            program: Program::new(
                vec![Statement::exp(Expression::cond(
                    Expression::bool(true),
                    Expression::call(
                        Expression::var(then_callback.clone()),
                        vec![],
                        CallInfo::default(),
                    ),
                    Expression::call(
                        Expression::var(else_callback.clone()),
                        vec![],
                        CallInfo::default(),
                    ),
                ))],
                vec![],
            ),
            modules: vec![],
            side_effect: None,
        });

        let [stmt] = deps.program.block.as_slice() else {
            panic!("expected one top-level statement");
        };
        let StatementDesc::If(test, then_block, else_block) = &stmt.desc else {
            panic!("expected conditional effect to lower to an if statement");
        };
        assert!(matches!(test.desc, ExpressionDesc::Bool(true)));

        let [then_stmt] = then_block.as_slice() else {
            panic!("expected one statement in then branch");
        };
        let [else_stmt] = else_block.as_slice() else {
            panic!("expected one statement in else branch");
        };

        match &then_stmt.desc {
            StatementDesc::Exp(Expression {
                desc: ExpressionDesc::Call(func, args, _),
                ..
            }) => {
                assert!(args.is_empty());
                assert!(matches!(
                    func.as_ref(),
                    Expression {
                        desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                        ..
                    } if id.same(&then_callback)
                ));
            }
            other => panic!("expected then branch effect call, got {other:?}"),
        }
        match &else_stmt.desc {
            StatementDesc::Exp(Expression {
                desc: ExpressionDesc::Call(func, args, _),
                ..
            }) => {
                assert!(args.is_empty());
                assert!(matches!(
                    func.as_ref(),
                    Expression {
                        desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                        ..
                    } if id.same(&else_callback)
                ));
            }
            other => panic!("expected else branch effect call, got {other:?}"),
        }
    }

    #[test]
    fn lowers_js_var_without_args_to_a_value() {
        let mut compiler = LambdaCompiler::new();
        let lam = Lambda::prim(
            Primitive::PjsCall {
                prim_name: "process".to_string(),
                arg_types: vec![],
                ffi: ExternalFfiSpec {
                    kind: ExternalFfiKind::Default,
                    spec: Some(ExternalSpec::JsVar {
                        name: "process".to_string(),
                        external_module_name: None,
                        scopes: vec![],
                    }),
                    obj_params: None,
                    return_wrapper: ExternalReturnWrapper::Identity,
                    inline_constant: None,
                },
                dynamic_import: false,
                transformed_jsx: false,
            },
            vec![],
            Location::none(),
        );

        let program = compiler.compile_program(&lam);
        let [stmt] = program.block.as_slice() else {
            panic!("expected a single expression statement");
        };
        match &stmt.desc {
            StatementDesc::Exp(Expression {
                desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                ..
            }) => assert_eq!(id.name(), "process"),
            other => panic!("expected a plain global value, got {other:?}"),
        }
    }

    #[test]
    fn lowers_module_external_calls_to_namespace_imports() {
        let mut compiler = LambdaCompiler::new();
        let lam = Lambda::prim(
            Primitive::PjsCall {
                prim_name: "describe".to_string(),
                arg_types: vec![],
                ffi: ExternalFfiSpec {
                    kind: ExternalFfiKind::Default,
                    spec: Some(ExternalSpec::JsCall {
                        name: "describe".to_string(),
                        external_module_name: Some(external_module("mocha")),
                        splice: false,
                        scopes: vec![],
                        tagged_template: false,
                    }),
                    obj_params: None,
                    return_wrapper: ExternalReturnWrapper::Identity,
                    inline_constant: None,
                },
                dynamic_import: false,
                transformed_jsx: false,
            },
            vec![],
            Location::none(),
        );

        let deps = compiler.compile_deps_program(&lam);
        assert!(matches!(
            deps.modules.as_slice(),
            [ModuleId {
                kind: Kind::External { name, default, .. },
                ..
            }] if name == "mocha" && !default
        ));

        let [stmt] = deps.program.block.as_slice() else {
            panic!("expected a single expression statement");
        };
        match &stmt.desc {
            StatementDesc::Exp(Expression {
                desc: ExpressionDesc::Call(func, args, _),
                ..
            }) => {
                assert!(args.is_empty());
                assert!(matches!(
                    func.as_ref(),
                    Expression {
                        desc: ExpressionDesc::StaticIndex(target, field, _),
                        ..
                    } if field == "describe"
                        && matches!(
                            target.as_ref(),
                            Expression {
                                desc: ExpressionDesc::Var(crate::js_ir::VIdent::Qualified(
                                    ModuleId {
                                        kind: Kind::External { name, default, .. },
                                        ..
                                    },
                                    None,
                                )),
                                ..
                            } if name == "mocha" && !default
                        )
                ));
            }
            other => panic!("expected external module call, got {other:?}"),
        }
    }

    #[test]
    fn lowers_default_module_values_in_dynamic_imports() {
        let mut compiler = LambdaCompiler::new();
        let external_value = Lambda::prim(
            Primitive::PjsCall {
                prim_name: "default".to_string(),
                arg_types: vec![],
                ffi: ExternalFfiSpec {
                    kind: ExternalFfiKind::Default,
                    spec: Some(ExternalSpec::JsVar {
                        name: "default".to_string(),
                        external_module_name: Some(external_module("a")),
                        scopes: vec![],
                    }),
                    obj_params: None,
                    return_wrapper: ExternalReturnWrapper::Identity,
                    inline_constant: None,
                },
                dynamic_import: false,
                transformed_jsx: false,
            },
            vec![],
            Location::none(),
        );
        let program = compiler.compile_program(&Lambda::prim(
            Primitive::Pimport,
            vec![external_value],
            Location::none(),
        ));
        let rendered = print_block(&program.block);
        assert_eq!(rendered, "import(\"a\").then(m => m.default);");
    }

    #[test]
    fn lowers_unit_returning_default_module_functions_in_dynamic_imports() {
        let mut compiler = LambdaCompiler::new();
        let param = Ident::create_local("prim");
        let eta_expanded_default = Lambda::Lfunction(crate::lambda::LFunction {
            arity: 1,
            params: vec![param.clone()],
            body: Box::new(Lambda::seq(
                Lambda::prim(
                    Primitive::PjsCall {
                        prim_name: "default".to_string(),
                        arg_types: vec![ExternalArgSpec::dummy()],
                        ffi: ExternalFfiSpec {
                            kind: ExternalFfiKind::Default,
                            spec: Some(ExternalSpec::JsVar {
                                name: "default".to_string(),
                                external_module_name: Some(external_module("b")),
                                scopes: vec![],
                            }),
                            obj_params: None,
                            return_wrapper: ExternalReturnWrapper::Identity,
                            inline_constant: None,
                        },
                        dynamic_import: false,
                        transformed_jsx: false,
                    },
                    vec![Lambda::var(param)],
                    Location::none(),
                ),
                Lambda::const_(Constant::JsUndefined { is_unit: true }),
            )),
            attr: crate::lambda::FunctionAttribute::default(),
        });
        let program = compiler.compile_program(&Lambda::prim(
            Primitive::Pimport,
            vec![eta_expanded_default],
            Location::none(),
        ));

        let rendered = print_block(&program.block);
        assert_eq!(rendered, "import(\"b\").then(m => m.default);");
    }

    #[test]
    fn lowers_js_new_to_new_expression() {
        let mut compiler = LambdaCompiler::new();
        let arg = Ident::create_local("prim");
        let lam = Lambda::prim(
            Primitive::PjsCall {
                prim_name: "URL".to_string(),
                arg_types: vec![],
                ffi: ExternalFfiSpec {
                    kind: ExternalFfiKind::Default,
                    spec: Some(ExternalSpec::JsNew {
                        name: "URL".to_string(),
                        external_module_name: None,
                        splice: false,
                        scopes: vec![],
                    }),
                    obj_params: None,
                    return_wrapper: ExternalReturnWrapper::Identity,
                    inline_constant: None,
                },
                dynamic_import: false,
                transformed_jsx: false,
            },
            vec![Lambda::var(arg.clone())],
            Location::none(),
        );

        let program = compiler.compile_program(&lam);
        let [stmt] = program.block.as_slice() else {
            panic!("expected a single expression statement");
        };
        match &stmt.desc {
            StatementDesc::Exp(Expression {
                desc: ExpressionDesc::New(ctor, Some(args)),
                ..
            }) => {
                assert!(matches!(
                    ctor.desc,
                    ExpressionDesc::Var(crate::js_ir::VIdent::Id(ref id)) if id.name() == "URL"
                ));
                assert!(matches!(
                    args.as_slice(),
                    [Expression {
                        desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                        ..
                    }] if id.same(&arg)
                ));
            }
            other => panic!("expected a new expression, got {other:?}"),
        }
    }

    #[test]
    fn lowers_marshaled_constant_args_in_js_call() {
        let mut compiler = LambdaCompiler::new();
        let lam = Lambda::prim(
            Primitive::PjsCall {
                prim_name: "somefn".to_string(),
                arg_types: vec![ExternalArgSpec {
                    arg_type: ExternalArgAttr::ArgCst(ExternalArgConst::StringLit(
                        "{foo:true}".to_string(),
                        ExternalArgDelim::NoQuotes,
                    )),
                    arg_label: ExternalArgLabel::Empty,
                }],
                ffi: ExternalFfiSpec {
                    kind: ExternalFfiKind::Default,
                    spec: Some(ExternalSpec::JsCall {
                        name: "somefn".to_string(),
                        external_module_name: None,
                        splice: false,
                        scopes: vec!["somescope".to_string()],
                        tagged_template: false,
                    }),
                    obj_params: None,
                    return_wrapper: ExternalReturnWrapper::Identity,
                    inline_constant: None,
                },
                dynamic_import: false,
                transformed_jsx: false,
            },
            vec![Lambda::const_(Constant::JsUndefined { is_unit: false })],
            Location::none(),
        );

        let program = compiler.compile_program(&lam);
        let [stmt] = program.block.as_slice() else {
            panic!("expected a single expression statement");
        };
        match &stmt.desc {
            StatementDesc::Exp(Expression {
                desc: ExpressionDesc::Call(func, args, _),
                ..
            }) => {
                assert!(matches!(
                    func.desc,
                    ExpressionDesc::StaticIndex(_, ref field, _)
                    if field == "somefn"
                ));
                assert!(matches!(
                    args.as_slice(),
                    [Expression {
                        desc: ExpressionDesc::Str {
                            delim: Delim::NoQuotes,
                            txt,
                        },
                        ..
                    }] if txt == "{foo:true}"
                ));
            }
            other => panic!("expected a JS call, got {other:?}"),
        }
    }

    #[test]
    fn lowers_js_object_create_with_marshaled_fields() {
        let mut compiler = LambdaCompiler::new();
        let name_ident = Ident::create_local("name");
        let lam = Lambda::prim(
            Primitive::PjsObjectCreate(vec![
                ExternalObjSpec {
                    obj_arg_type: ExternalArgAttr::ArgCst(ExternalArgConst::StringLit(
                        "false".to_string(),
                        ExternalArgDelim::NoQuotes,
                    )),
                    obj_arg_label: ExternalObjLabel::Label {
                        name: "objectMode".to_string(),
                    },
                },
                ExternalObjSpec {
                    obj_arg_type: ExternalArgAttr::Nothing,
                    obj_arg_label: ExternalObjLabel::Label {
                        name: "name".to_string(),
                    },
                },
                ExternalObjSpec {
                    obj_arg_type: ExternalArgAttr::ArgCst(ExternalArgConst::StringLit(
                        "true".to_string(),
                        ExternalArgDelim::NoQuotes,
                    )),
                    obj_arg_label: ExternalObjLabel::Label {
                        name: "someOther".to_string(),
                    },
                },
                ExternalObjSpec {
                    obj_arg_type: ExternalArgAttr::ExternUnit,
                    obj_arg_label: ExternalObjLabel::Empty,
                },
            ]),
            vec![
                Lambda::var(name_ident.clone()),
                Lambda::const_(Constant::JsUndefined { is_unit: true }),
            ],
            Location::none(),
        );

        let program = compiler.compile_program(&lam);
        let [stmt] = program.block.as_slice() else {
            panic!("expected a single expression statement");
        };
        match &stmt.desc {
            StatementDesc::Exp(Expression {
                desc: ExpressionDesc::Object(_, props),
                ..
            }) => {
                assert_eq!(props.len(), 3);
                assert!(matches!(
                    &props[0],
                    (
                        PropertyName::Lit(name),
                        Expression {
                            desc: ExpressionDesc::Str {
                                delim: Delim::NoQuotes,
                                txt,
                            },
                            ..
                        },
                    ) if name == "objectMode" && txt == "false"
                ));
                assert!(matches!(
                    &props[1],
                    (
                        PropertyName::Lit(name),
                        Expression {
                            desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                            ..
                        },
                    ) if name == "name" && id.same(&name_ident)
                ));
                assert!(matches!(
                    &props[2],
                    (
                        PropertyName::Lit(name),
                        Expression {
                            desc: ExpressionDesc::Str {
                                delim: Delim::NoQuotes,
                                txt,
                            },
                            ..
                        },
                    ) if name == "someOther" && txt == "true"
                ));
            }
            other => panic!("expected an object literal, got {other:?}"),
        }
    }

    #[test]
    fn collects_static_module_dependencies() {
        let mut compiler = LambdaCompiler::new();
        let deps = compiler.compile_deps_program(&Lambda::global_module(
            Ident::create_persistent("Belt_List"),
            false,
        ));

        assert_eq!(deps.modules.len(), 1);
        assert_eq!(deps.modules[0].id.name(), "Belt_List");
        assert!(!deps.modules[0].dynamic_import);
    }

    #[test]
    fn resolves_runtime_dynamic_import_to_string_path() {
        let runtime = tempdir().expect("failed to create runtime tempdir");
        let runtime_ocaml = runtime.path().join("lib").join("ocaml");
        fs::create_dir_all(&runtime_ocaml).expect("failed to create runtime ocaml dir");
        fs::write(runtime_ocaml.join("Belt_List.cmi"), []).expect("failed to stub runtime cmi");

        let project = tempdir().expect("failed to create project tempdir");
        let source = project.path().join("src").join("Import.res");
        let output = project.path().join("src").join("Import.mjs");

        let resolver = ModulePathResolver::from_compile_options(
            Some(source.to_str().expect("utf8 source path")),
            Some(output.as_path()),
            Some(runtime.path()),
            None,
        );
        let mut compiler = LambdaCompiler::with_module_path_resolver(Some(resolver));
        let program = compiler.compile_program(&Lambda::prim(
            Primitive::Pimport,
            vec![Lambda::global_module(
                Ident::create_persistent("Belt_List"),
                true,
            )],
            Location::none(),
        ));

        let [stmt] = program.block.as_slice() else {
            panic!("expected a single import expression statement");
        };
        match &stmt.desc {
            StatementDesc::Exp(Expression {
                desc: ExpressionDesc::Call(func, args, _),
                ..
            }) => {
                assert!(matches!(
                    func.desc,
                    ExpressionDesc::Var(crate::js_ir::VIdent::Id(ref id)) if id.name() == "import"
                ));
                assert!(matches!(
                    args.as_slice(),
                    [Expression {
                        desc: ExpressionDesc::Str { txt, .. },
                        ..
                    }] if txt == "@rescript/runtime/lib/es6/Belt_List.js"
                ));
            }
            other => panic!("expected import(\"...\") call, got {other:?}"),
        }
    }

    #[test]
    fn resolves_local_module_paths_from_ast_metadata() {
        let project = tempdir().expect("failed to create project tempdir");
        let source_dir = project.path().join("src");
        let build_dir = project.path().join("lib").join("bs").join("src");
        fs::create_dir_all(&source_dir).expect("failed to create source dir");
        fs::create_dir_all(&build_dir).expect("failed to create build dir");

        let current_source = source_dir.join("Current.res");
        let target_source = source_dir.join("ModuleWithAlias.res");
        fs::write(&current_source, "").expect("failed to stub current source");
        fs::write(&target_source, "").expect("failed to stub target source");
        write_ast_source_stub(&build_dir.join("ModuleWithAlias.ast"), &target_source);

        let mut pers = PersistentEnv::new();
        pers.set_load_path(vec![build_dir]);

        let resolver = ModulePathResolver::from_compile_options(
            Some(current_source.to_str().expect("utf8 current source path")),
            Some(source_dir.join("Current.mjs").as_path()),
            None,
            Some(pers),
        );
        let module = ModuleId {
            id: Ident::create_persistent("ModuleWithAlias"),
            kind: Kind::Ml,
            dynamic_import: true,
        };

        assert_eq!(
            resolver.resolve_module_path(&module).as_deref(),
            Some("./ModuleWithAlias.mjs")
        );
    }

    #[test]
    fn lowers_paddint_with_int32_coercion() {
        let mut compiler = LambdaCompiler::new();
        let lhs = Ident::create_local("lhs");
        let rhs = Ident::create_local("rhs");
        let program = compiler.compile_program(&Lambda::prim(
            Primitive::Paddint,
            vec![Lambda::var(lhs.clone()), Lambda::var(rhs.clone())],
            Location::none(),
        ));

        let [stmt] = program.block.as_slice() else {
            panic!("expected a single expression statement");
        };
        match &stmt.desc {
            StatementDesc::Exp(Expression {
                desc: ExpressionDesc::Bin(BinOp::Bor, left, right),
                ..
            }) => {
                assert!(matches!(
                    right.as_ref(),
                    Expression {
                        desc: ExpressionDesc::Number(Number::Int { i: 0, .. }),
                        ..
                    }
                ));
                assert!(matches!(
                    left.as_ref(),
                    Expression {
                        desc: ExpressionDesc::Bin(BinOp::Plus, lhs_expr, rhs_expr),
                        ..
                    }
                    if matches!(
                        lhs_expr.as_ref(),
                        Expression {
                            desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                            ..
                        } if id.same(&lhs)
                    ) && matches!(
                        rhs_expr.as_ref(),
                        Expression {
                            desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                            ..
                        } if id.same(&rhs)
                    )
                ));
            }
            other => panic!("expected `lhs + rhs | 0`, got {other:?}"),
        }
    }

    #[test]
    fn lowers_plsrint_with_int32_coercion() {
        let mut compiler = LambdaCompiler::new();
        let value = Ident::create_local("value");
        let shift = Ident::create_local("shift");
        let program = compiler.compile_program(&Lambda::prim(
            Primitive::Plsrint,
            vec![Lambda::var(value.clone()), Lambda::var(shift.clone())],
            Location::none(),
        ));

        let [stmt] = program.block.as_slice() else {
            panic!("expected a single expression statement");
        };
        match &stmt.desc {
            StatementDesc::Exp(Expression {
                desc: ExpressionDesc::Bin(BinOp::Bor, left, right),
                ..
            }) => {
                assert!(matches!(
                    right.as_ref(),
                    Expression {
                        desc: ExpressionDesc::Number(Number::Int { i: 0, .. }),
                        ..
                    }
                ));
                assert!(matches!(
                    left.as_ref(),
                    Expression {
                        desc: ExpressionDesc::Bin(BinOp::Lsr, value_expr, shift_expr),
                        ..
                    }
                    if matches!(
                        value_expr.as_ref(),
                        Expression {
                            desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                            ..
                        } if id.same(&value)
                    ) && matches!(
                        shift_expr.as_ref(),
                        Expression {
                            desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                            ..
                        } if id.same(&shift)
                    )
                ));
            }
            other => panic!("expected `value >>> shift | 0`, got {other:?}"),
        }
    }

    #[test]
    fn lowers_psome_not_nest_to_identity_optional_block() {
        let mut compiler = LambdaCompiler::new();
        let value = Ident::create_local("value");
        let program = compiler.compile_program(&Lambda::prim(
            Primitive::PsomeNotNest,
            vec![Lambda::var(value.clone())],
            Location::none(),
        ));

        let [stmt] = program.block.as_slice() else {
            panic!("expected a single expression statement");
        };
        match &stmt.desc {
            StatementDesc::Exp(Expression {
                desc: ExpressionDesc::OptionalBlock(inner, true),
                ..
            }) => {
                assert!(matches!(
                    inner.as_ref(),
                    Expression {
                        desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                        ..
                    } if id.same(&value)
                ));
            }
            other => panic!("expected identity optional block, got {other:?}"),
        }
    }

    #[test]
    fn lowers_pval_from_option_optional_block_to_inner_value() {
        let mut compiler = LambdaCompiler::new();
        let value = Ident::create_local("value");
        let program = compiler.compile_program(&Lambda::prim(
            Primitive::PvalFromOption,
            vec![Lambda::prim(
                Primitive::PsomeNotNest,
                vec![Lambda::var(value.clone())],
                Location::none(),
            )],
            Location::none(),
        ));

        let [stmt] = program.block.as_slice() else {
            panic!("expected a single expression statement");
        };
        match &stmt.desc {
            StatementDesc::Exp(Expression {
                desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                ..
            }) => assert!(id.same(&value)),
            other => panic!("expected optional unwrap to lower to the inner value, got {other:?}"),
        }
    }

    #[test]
    fn lowers_pfield_cons_to_hd_tl_properties() {
        let mut compiler = LambdaCompiler::new();
        let list = Ident::create_local("list");
        let head_program = compiler.compile_program(&Lambda::prim(
            Primitive::Pfield(0, FieldDbgInfo::Cons),
            vec![Lambda::var(list.clone())],
            Location::none(),
        ));
        let tail_program = compiler.compile_program(&Lambda::prim(
            Primitive::Pfield(1, FieldDbgInfo::Cons),
            vec![Lambda::var(list.clone())],
            Location::none(),
        ));

        let [head_stmt] = head_program.block.as_slice() else {
            panic!("expected a single expression statement for head");
        };
        let [tail_stmt] = tail_program.block.as_slice() else {
            panic!("expected a single expression statement for tail");
        };

        match &head_stmt.desc {
            StatementDesc::Exp(Expression {
                desc: ExpressionDesc::StaticIndex(target, field, _),
                ..
            }) => {
                assert_eq!(field, "hd");
                assert!(matches!(
                    target.as_ref(),
                    Expression {
                        desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                        ..
                    } if id.same(&list)
                ));
            }
            other => panic!("expected head access to lower to `.hd`, got {other:?}"),
        }

        match &tail_stmt.desc {
            StatementDesc::Exp(Expression {
                desc: ExpressionDesc::StaticIndex(target, field, _),
                ..
            }) => {
                assert_eq!(field, "tl");
                assert!(matches!(
                    target.as_ref(),
                    Expression {
                        desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                        ..
                    } if id.same(&list)
                ));
            }
            other => panic!("expected tail access to lower to `.tl`, got {other:?}"),
        }
    }

    #[test]
    fn external_shadow_pass_rewrites_only_shadowed_initializer_reads() {
        let process = Ident::create_local("process");
        let proc = Ident::create_local("proc");
        let global_process = Ident::create_persistent("process");
        let deps = DepsProgram {
            program: Program::new(
                vec![
                    Statement::variable(VariableDeclaration {
                        ident: process.clone(),
                        value: Some(Expression::var(global_process.clone())),
                        property: LetKind::Strict,
                        ident_info: IdentInfo::default(),
                    }),
                    Statement::variable(VariableDeclaration {
                        ident: proc,
                        value: Some(Expression::var(global_process.clone())),
                        property: LetKind::Strict,
                        ident_info: IdentInfo::default(),
                    }),
                ],
                vec![],
            ),
            modules: vec![],
            side_effect: None,
        };

        let rewritten = apply_external_shadow_pass(deps);
        let [first, second] = rewritten.program.block.as_slice() else {
            panic!("expected two variable declarations");
        };

        match &first.desc {
            StatementDesc::Variable(VariableDeclaration {
                value:
                    Some(Expression {
                        desc: ExpressionDesc::StaticIndex(target, field, _),
                        ..
                    }),
                ..
            }) => {
                assert_eq!(field, "process");
                assert!(matches!(
                    target.desc,
                    ExpressionDesc::Var(crate::js_ir::VIdent::Id(ref id)) if id.name() == "globalThis"
                ));
            }
            other => panic!("expected first initializer to read globalThis.process, got {other:?}"),
        }

        match &second.desc {
            StatementDesc::Variable(VariableDeclaration {
                value:
                    Some(Expression {
                        desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                        ..
                    }),
                ..
            }) => assert_eq!(id.name(), "process"),
            other => {
                panic!("expected second initializer to remain a plain process read, got {other:?}")
            }
        }
    }
}
