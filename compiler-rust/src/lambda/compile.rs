//! Lambda -> JS IR compilation.
//!
//! This module provides a straightforward lowering from Lambda IR into the
//! JavaScript IR used by the Rust compiler backend. The implementation favors
//! clarity over aggressive optimization; it is intended as a correct baseline
//! that can be extended with more advanced codegen passes.

use std::collections::{HashMap, HashSet};

use crate::context::IdGenerator;
use crate::ident::Ident;
use crate::js_ir::op::{
    IdentInfo, ImportAttributes as JsImportAttributes, Kind, LengthObject, MutableFlag, Number,
    PropertyName, UsedStats,
};
use crate::js_ir::printer::is_js_keyword_or_global;
use crate::js_ir::{
    BinOp, Block, CallInfo, CaseClause, Delim, DepsProgram, Expression, ExpressionDesc,
    ForDirection, ModuleId, ModulePathResolver, Program, Statement, StatementDesc, StringClause,
    VIdent, VariableDeclaration,
};
use crate::lambda::analysis;
use crate::lambda::compat::{Comparison, FieldDbgInfo, LetKind};
use crate::lambda::constant::{Constant, ConstructorRuntimeTag, PointerInfo, StringDelim};
use crate::lambda::primitive::{
    ExternalArgAttr, ExternalArgConst, ExternalArgDelim, ExternalArgLabel, ExternalArgSpec,
    ExternalModuleBindName, ExternalModuleName, ExternalObjLabel, ExternalObjSpec, ExternalSpec,
    Mutable, Primitive,
};
use crate::lambda::subst;
use crate::lambda::{Apply, Lambda, LambdaSwitch, TagInfo};

/// Compilation result for an expression: prelude statements plus a value expression.
#[derive(Debug, Clone)]
struct Compiled {
    prelude: Block,
    expr: Expression,
}

#[derive(Debug, Clone)]
struct StaticHandler {
    label: i32,
    bindings: Vec<Ident>,
    handler: Lambda,
}

/// Lambda compiler to JS IR.
pub struct LambdaCompiler {
    id_gen: IdGenerator,
    module_path_resolver: Option<ModulePathResolver>,
    static_handlers: Vec<StaticHandler>,
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
            static_handlers: Vec::new(),
        }
    }

    /// Create a compiler with module import resolution context.
    pub fn with_module_path_resolver(module_path_resolver: Option<ModulePathResolver>) -> Self {
        Self {
            id_gen: IdGenerator::new(),
            module_path_resolver,
            static_handlers: Vec::new(),
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
        let exports = resolve_export_aliases(&block, exports);
        let side_effect = module_side_effect_reason(&simplified);

        let mut deps = apply_js_shake_pass(apply_js_flatten_and_mark_dead_pass(
            apply_external_shadow_pass(apply_js_flatten_pass(DepsProgram {
                program: Program::new(block, exports),
                modules: vec![],
                side_effect,
            })),
        ));
        deps.modules = self.collect_required_modules(&deps.program.block);
        if deps.side_effect.is_none() {
            deps.side_effect = required_module_side_effect_reason(
                self.module_path_resolver.as_ref(),
                &deps.modules,
            );
        }
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
                let mut prelude = self.compile_let_binding(*kind, id, value);
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
            Lambda::LstaticRaise(id, args) => {
                if let Some(handler) = self.resolve_static_raise(*id, args) {
                    return self.compile_expr(&handler);
                }
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
            Lambda::LstaticCatch(body, (label, bindings), handler) => {
                self.with_static_handler(*label, bindings, handler, |this| this.compile_expr(body))
            }
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

    fn compile_let_binding(&mut self, kind: LetKind, id: &Ident, value: &Lambda) -> Block {
        match value {
            Lambda::Llet(inner_kind, inner_id, inner_value, body) => {
                let mut block = self.compile_let_binding(*inner_kind, inner_id, inner_value);
                block.extend(self.compile_let_binding(kind, id, body));
                block
            }
            Lambda::LstaticCatch(body, (label, bindings), handler) => {
                self.with_static_handler(*label, bindings, handler, |this| {
                    this.compile_let_binding(kind, id, body)
                })
            }
            Lambda::Lswitch(scrut, switch) => {
                let mut block = vec![Statement::variable(VariableDeclaration {
                    ident: id.clone(),
                    value: None,
                    property: kind,
                    ident_info: IdentInfo::default(),
                })];
                block.extend(self.compile_switch_assignment_block(id, scrut, switch));
                block
            }
            Lambda::LstringSwitch(scrut, cases, default) => {
                let mut block = vec![Statement::variable(VariableDeclaration {
                    ident: id.clone(),
                    value: None,
                    property: kind,
                    ident_info: IdentInfo::default(),
                })];
                block.extend(self.compile_string_switch_assignment_block(
                    id,
                    scrut,
                    cases,
                    default.as_deref(),
                ));
                block
            }
            _ => {
                let value_compiled = self.compile_expr(value);
                let mut block = value_compiled.prelude;
                block.push(Statement::variable(VariableDeclaration {
                    ident: id.clone(),
                    value: Some(value_compiled.expr),
                    property: kind,
                    ident_info: IdentInfo::default(),
                }));
                block
            }
        }
    }

    fn compile_effect_block(&mut self, lam: &Lambda) -> Block {
        match lam {
            Lambda::Llet(kind, id, value, body) => {
                let mut block = self.compile_let_binding(*kind, id, value);
                block.extend(self.compile_effect_block(body));
                block
            }
            Lambda::Lsequence(first, second) => {
                let mut block = self.compile_effect_block(first);
                block.extend(self.compile_effect_block(second));
                block
            }
            Lambda::LstaticCatch(body, (label, bindings), handler) => {
                self.with_static_handler(*label, bindings, handler, |this| {
                    this.compile_effect_block(body)
                })
            }
            Lambda::Lswitch(scrut, switch) => self.compile_switch_effect_block(scrut, switch),
            Lambda::LstringSwitch(scrut, cases, default) => {
                self.compile_string_switch_effect_block(scrut, cases, default.as_deref())
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
            Lambda::Llet(kind, id, value, body) => {
                let mut block = self.compile_let_binding(*kind, id, value);
                block.extend(self.compile_return_block(body));
                block
            }
            Lambda::Lsequence(first, second) => {
                let mut block = self.compile_effect_block(first);
                block.extend(self.compile_return_block(second));
                block
            }
            Lambda::LstaticCatch(body, (label, bindings), handler) => {
                self.with_static_handler(*label, bindings, handler, |this| {
                    this.compile_return_block(body)
                })
            }
            Lambda::Lswitch(scrut, switch) => self.compile_switch_return_block(scrut, switch),
            Lambda::LstringSwitch(scrut, cases, default) => {
                self.compile_string_switch_return_block(scrut, cases, default.as_deref())
            }
            _ => {
                let compiled = self.compile_expr(lam);
                let mut block = compiled.prelude;
                if !block_terminates(&block) {
                    block.push(Statement::return_(compiled.expr));
                }
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
            let body_block = self.compile_switch_value_block(&tmp, body);
            cases.push((
                *tag,
                crate::js_ir::CaseClause {
                    body: body_block,
                    should_break: false,
                    comment: None,
                },
            ));
        }

        let default_block = switch
            .sw_failaction
            .as_ref()
            .map(|fallback| self.compile_switch_value_block(&tmp, fallback));

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
            let body_block = self.compile_switch_value_block(&tmp, body);
            clauses.push(crate::js_ir::StringClause {
                tag_type: tag.clone(),
                clause: crate::js_ir::CaseClause {
                    body: body_block,
                    should_break: false,
                    comment: None,
                },
            });
        }

        let default_block = default.map(|fallback| self.compile_switch_value_block(&tmp, fallback));

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

    fn compile_switch_value_block(&mut self, result: &Ident, lam: &Lambda) -> Block {
        let mut block = self.compile_assign_to_target_block(result, lam);
        if !block_terminates(&block) {
            block.push(Statement::break_());
        }
        block
    }

    fn compile_assign_to_target_block(&mut self, result: &Ident, lam: &Lambda) -> Block {
        match lam {
            Lambda::LstaticCatch(body, (label, bindings), handler) => {
                self.with_static_handler(*label, bindings, handler, |this| {
                    this.compile_assign_to_target_block(result, body)
                })
            }
            Lambda::Lswitch(scrut, switch) => {
                self.compile_switch_assignment_block(result, scrut, switch)
            }
            Lambda::LstringSwitch(scrut, cases, default) => self
                .compile_string_switch_assignment_block(result, scrut, cases, default.as_deref()),
            _ => {
                let compiled = self.compile_expr(lam);
                let mut block = compiled.prelude;
                if !block_terminates(&block) {
                    block.push(Statement::exp(Expression::bin(
                        BinOp::Eq,
                        Expression::var(result.clone()),
                        compiled.expr,
                    )));
                }
                block
            }
        }
    }

    fn compile_switch_assignment_block(
        &mut self,
        result: &Ident,
        scrut: &Lambda,
        switch: &LambdaSwitch,
    ) -> Block {
        let scrut_compiled = self.compile_expr(scrut);
        let mut block = scrut_compiled.prelude;

        let mut cases = Vec::new();
        for (tag, body) in &switch.sw_consts {
            cases.push((
                *tag,
                crate::js_ir::CaseClause {
                    body: self.compile_switch_value_block(result, body),
                    should_break: false,
                    comment: None,
                },
            ));
        }

        let default_block = switch
            .sw_failaction
            .as_ref()
            .map(|fallback| self.compile_assign_to_target_block(result, fallback));

        block.push(Statement::new(StatementDesc::IntSwitch(
            scrut_compiled.expr,
            cases,
            default_block,
        )));
        block
    }

    fn compile_string_switch_assignment_block(
        &mut self,
        result: &Ident,
        scrut: &Lambda,
        cases: &[(String, Lambda)],
        default: Option<&Lambda>,
    ) -> Block {
        let scrut_compiled = self.compile_expr(scrut);
        let mut block = scrut_compiled.prelude;

        let mut clauses = Vec::new();
        for (tag, body) in cases {
            clauses.push(crate::js_ir::StringClause {
                tag_type: tag.clone(),
                clause: crate::js_ir::CaseClause {
                    body: self.compile_switch_value_block(result, body),
                    should_break: false,
                    comment: None,
                },
            });
        }

        let default_block =
            default.map(|fallback| self.compile_assign_to_target_block(result, fallback));

        block.push(Statement::new(StatementDesc::StringSwitch(
            scrut_compiled.expr,
            clauses,
            default_block,
        )));
        block
    }

    fn compile_switch_return_block(&mut self, scrut: &Lambda, switch: &LambdaSwitch) -> Block {
        let scrut_compiled = self.compile_expr(scrut);
        let mut block = scrut_compiled.prelude;

        let mut cases = Vec::new();
        for (tag, body) in &switch.sw_consts {
            cases.push((
                *tag,
                crate::js_ir::CaseClause {
                    body: self.compile_return_block(body),
                    should_break: false,
                    comment: None,
                },
            ));
        }

        let default_block = switch
            .sw_failaction
            .as_ref()
            .map(|fallback| self.compile_return_block(fallback));

        block.push(Statement::new(StatementDesc::IntSwitch(
            scrut_compiled.expr,
            cases,
            default_block,
        )));
        block
    }

    fn compile_string_switch_return_block(
        &mut self,
        scrut: &Lambda,
        cases: &[(String, Lambda)],
        default: Option<&Lambda>,
    ) -> Block {
        let scrut_compiled = self.compile_expr(scrut);
        let mut block = scrut_compiled.prelude;

        let mut clauses = Vec::new();
        for (tag, body) in cases {
            clauses.push(crate::js_ir::StringClause {
                tag_type: tag.clone(),
                clause: crate::js_ir::CaseClause {
                    body: self.compile_return_block(body),
                    should_break: false,
                    comment: None,
                },
            });
        }

        let default_block = default.map(|fallback| self.compile_return_block(fallback));

        block.push(Statement::new(StatementDesc::StringSwitch(
            scrut_compiled.expr,
            clauses,
            default_block,
        )));
        block
    }

    fn compile_switch_effect_block(&mut self, scrut: &Lambda, switch: &LambdaSwitch) -> Block {
        let scrut_compiled = self.compile_expr(scrut);
        let mut block = scrut_compiled.prelude;

        let mut cases = Vec::new();
        for (tag, body) in &switch.sw_consts {
            let body = self.compile_effect_block(body);
            cases.push((
                *tag,
                crate::js_ir::CaseClause {
                    should_break: !block_terminates(&body),
                    body,
                    comment: None,
                },
            ));
        }

        let default_block = switch
            .sw_failaction
            .as_ref()
            .map(|fallback| self.compile_effect_block(fallback));

        let has_effectful_case = cases.iter().any(|(_, clause)| !clause.body.is_empty())
            || default_block.as_ref().is_some_and(|body| !body.is_empty());
        if !has_effectful_case {
            push_effect_expression(&mut block, scrut_compiled.expr);
            return block;
        }

        block.push(Statement::new(StatementDesc::IntSwitch(
            scrut_compiled.expr,
            cases,
            default_block,
        )));
        block
    }

    fn compile_string_switch_effect_block(
        &mut self,
        scrut: &Lambda,
        cases: &[(String, Lambda)],
        default: Option<&Lambda>,
    ) -> Block {
        let scrut_compiled = self.compile_expr(scrut);
        let mut block = scrut_compiled.prelude;

        let mut clauses = Vec::new();
        for (tag, body) in cases {
            let body = self.compile_effect_block(body);
            clauses.push(crate::js_ir::StringClause {
                tag_type: tag.clone(),
                clause: crate::js_ir::CaseClause {
                    should_break: !block_terminates(&body),
                    body,
                    comment: None,
                },
            });
        }

        let default_block = default.map(|fallback| self.compile_effect_block(fallback));

        let has_effectful_case = clauses.iter().any(|clause| !clause.clause.body.is_empty())
            || default_block.as_ref().is_some_and(|body| !body.is_empty());
        if !has_effectful_case {
            push_effect_expression(&mut block, scrut_compiled.expr);
            return block;
        }

        block.push(Statement::new(StatementDesc::StringSwitch(
            scrut_compiled.expr,
            clauses,
            default_block,
        )));
        block
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
            Constant::Int {
                i,
                comment: Some(PointerInfo::Constructor(tag)),
            } => match &tag.runtime_tag {
                Some(ConstructorRuntimeTag::Int(value)) => Expression::number(Number::int(*value)),
                Some(ConstructorRuntimeTag::String(value)) => Expression::string(value.clone()),
                Some(ConstructorRuntimeTag::Float(value)) => {
                    Expression::number(Number::float(value.clone()))
                }
                Some(ConstructorRuntimeTag::BigInt(value)) => {
                    Expression::number(Number::bigint(true, value.clone()))
                }
                Some(ConstructorRuntimeTag::Bool(value)) => Expression::bool(*value),
                Some(ConstructorRuntimeTag::Null) => Expression::null(),
                Some(ConstructorRuntimeTag::Undefined) => Expression::undefined(false),
                None if tag.name != "[]" => Expression::string(tag.name.clone()),
                None => Expression::number(Number::int(*i)),
            },
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
            [
                arg,
                Expression {
                    desc: ExpressionDesc::Undefined { is_unit: true },
                    ..
                },
            ] => arg,
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

    fn with_static_handler<T>(
        &mut self,
        label: i32,
        bindings: &[Ident],
        handler: &Lambda,
        f: impl FnOnce(&mut Self) -> T,
    ) -> T {
        self.static_handlers.push(StaticHandler {
            label,
            bindings: bindings.to_vec(),
            handler: handler.clone(),
        });
        let result = f(self);
        self.static_handlers.pop();
        result
    }

    fn resolve_static_raise(&self, label: i32, args: &[Lambda]) -> Option<Lambda> {
        let handler = self
            .static_handlers
            .iter()
            .rev()
            .find(|handler| handler.label == label)?;
        if handler.bindings.len() != args.len() {
            return None;
        }
        if handler.bindings.is_empty() {
            return Some(handler.handler.clone());
        }

        let subst = subst::make_subst(&handler.bindings, args);
        Some(subst::subst(&subst, &handler.handler))
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

fn required_module_side_effect_reason(
    module_path_resolver: Option<&ModulePathResolver>,
    modules: &[ModuleId],
) -> Option<String> {
    modules.iter().find_map(|module| {
        if let Some(resolver) = module_path_resolver {
            resolver.module_side_effect_reason(module)
        } else {
            match &module.kind {
                Kind::Runtime => None,
                Kind::External { name, .. } => Some(name.clone()),
                Kind::Ml => Some(module.id.name().to_string()),
            }
        }
    })
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

fn resolve_export_aliases(block: &Block, exports: Vec<Ident>) -> Vec<Ident> {
    let mut declared = HashSet::new();
    collect_declared_idents(block, &mut declared);
    let mut aliases = HashMap::new();
    collect_export_aliases(block, &mut aliases);
    exports
        .into_iter()
        .map(|export| resolve_export_alias(&export, &aliases, &declared))
        .collect()
}

fn collect_declared_idents(block: &Block, declared: &mut HashSet<Ident>) {
    for stmt in block {
        match &stmt.desc {
            StatementDesc::Variable(VariableDeclaration { ident, .. }) => {
                declared.insert(ident.clone());
            }
            StatementDesc::Block(inner) => collect_declared_idents(inner, declared),
            StatementDesc::If(_, then_block, else_block) => {
                collect_declared_idents(then_block, declared);
                collect_declared_idents(else_block, declared);
            }
            _ => {}
        }
    }
}

fn collect_export_aliases(block: &Block, aliases: &mut HashMap<Ident, Ident>) {
    for stmt in block {
        match &stmt.desc {
            StatementDesc::Variable(VariableDeclaration {
                ident,
                value:
                    Some(Expression {
                        desc: ExpressionDesc::Var(VIdent::Id(target)),
                        ..
                    }),
                ..
            }) => {
                aliases.insert(ident.clone(), target.clone());
            }
            StatementDesc::Block(inner) => collect_export_aliases(inner, aliases),
            StatementDesc::If(_, then_block, else_block) => {
                collect_export_aliases(then_block, aliases);
                collect_export_aliases(else_block, aliases);
            }
            _ => {}
        }
    }
}

fn resolve_export_alias(
    export: &Ident,
    aliases: &HashMap<Ident, Ident>,
    declared: &HashSet<Ident>,
) -> Ident {
    let mut current = export.clone();
    let mut seen = HashSet::new();

    while let Some(target) = aliases.get(&current) {
        if target.name() != export.name()
            || !declared.contains(target)
            || !seen.insert(current.clone())
        {
            break;
        }
        current = target.clone();
    }

    current
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

fn block_terminates(block: &Block) -> bool {
    block.last().is_some_and(statement_terminates)
}

fn statement_terminates(stmt: &Statement) -> bool {
    match &stmt.desc {
        StatementDesc::Block(block) => block_terminates(block),
        StatementDesc::Return(_)
        | StatementDesc::Throw(_)
        | StatementDesc::Break
        | StatementDesc::Continue => true,
        StatementDesc::If(_, then_block, else_block) => {
            !then_block.is_empty()
                && !else_block.is_empty()
                && block_terminates(then_block)
                && block_terminates(else_block)
        }
        StatementDesc::IntSwitch(_, cases, default) => {
            default.as_ref().is_some_and(block_terminates)
                && !cases.is_empty()
                && cases
                    .iter()
                    .all(|(_, clause)| block_terminates(&clause.body))
        }
        StatementDesc::StringSwitch(_, cases, default) => {
            default.as_ref().is_some_and(block_terminates)
                && !cases.is_empty()
                && cases
                    .iter()
                    .all(|clause| block_terminates(&clause.clause.body))
        }
        _ => false,
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

fn apply_js_flatten_and_mark_dead_pass(mut deps: DepsProgram) -> DepsProgram {
    deps.program = flatten_and_mark_dead_program(deps.program);
    deps
}

fn flatten_and_mark_dead_program(mut program: Program) -> Program {
    let mut substitution = HashMap::new();
    program.block = flatten_and_mark_dead_block(program.block, &mut substitution);
    mark_dead_code(&mut program);
    program
}

fn flatten_and_mark_dead_block(
    block: Block,
    substitution: &mut HashMap<Ident, Expression>,
) -> Block {
    block
        .into_iter()
        .map(|stmt| flatten_and_mark_dead_statement(stmt, substitution))
        .collect()
}

fn flatten_and_mark_dead_statement(
    stmt: Statement,
    substitution: &mut HashMap<Ident, Expression>,
) -> Statement {
    let Statement { desc, comment } = stmt;
    match desc {
        StatementDesc::Variable(decl) => {
            if matches!(decl.ident_info.used_stats, UsedStats::DeadPure) {
                return Statement {
                    desc: StatementDesc::Block(vec![]),
                    comment,
                };
            }

            if matches!(decl.ident_info.used_stats, UsedStats::DeadNonPure) {
                return match decl.value {
                    None => Statement {
                        desc: StatementDesc::Block(vec![]),
                        comment,
                    },
                    Some(value) => Statement {
                        desc: StatementDesc::Exp(value),
                        comment,
                    },
                };
            }

            if matches!(
                decl.property,
                LetKind::Strict | LetKind::StrictOpt | LetKind::Alias
            ) {
                if let Some(Expression {
                    desc: ExpressionDesc::CamlBlock(items, MutableFlag::Immutable, tag, tag_info),
                    comment: value_comment,
                }) = decl.value
                {
                    if items.len() >= 2 {
                        let mut rewritten_items = Vec::with_capacity(items.len());
                        let mut bindings = Vec::new();

                        for (index, item) in items.into_iter().enumerate() {
                            if is_simple_block_binding_item(&item) {
                                rewritten_items.push(item);
                            } else {
                                let rewritten =
                                    flatten_and_mark_dead_expression(item, substitution);
                                let temp = Ident::create_local(block_substitution_name(
                                    &decl.ident,
                                    &tag_info,
                                    index,
                                ));
                                rewritten_items.push(Expression::var(temp.clone()));
                                bindings.push(Statement::variable(VariableDeclaration {
                                    ident: temp,
                                    value: Some(rewritten),
                                    property: LetKind::Strict,
                                    ident_info: IdentInfo::default(),
                                }));
                            }
                        }

                        let rewritten_value = Expression {
                            desc: ExpressionDesc::CamlBlock(
                                rewritten_items,
                                MutableFlag::Immutable,
                                tag,
                                tag_info,
                            ),
                            comment: value_comment,
                        };
                        substitution.insert(decl.ident.clone(), rewritten_value.clone());

                        let original = Statement {
                            desc: StatementDesc::Variable(VariableDeclaration {
                                ident: decl.ident,
                                value: Some(rewritten_value),
                                property: decl.property,
                                ident_info: decl.ident_info,
                            }),
                            comment,
                        };

                        if bindings.is_empty() {
                            return original;
                        }

                        bindings.push(original);
                        return Statement {
                            desc: StatementDesc::Block(bindings),
                            comment: None,
                        };
                    }

                    return Statement {
                        desc: StatementDesc::Variable(VariableDeclaration {
                            ident: decl.ident,
                            value: Some(Expression {
                                desc: ExpressionDesc::CamlBlock(
                                    items,
                                    MutableFlag::Immutable,
                                    tag,
                                    tag_info,
                                ),
                                comment: value_comment,
                            }),
                            property: decl.property,
                            ident_info: decl.ident_info,
                        }),
                        comment,
                    };
                }
            }

            Statement {
                desc: StatementDesc::Variable(VariableDeclaration {
                    ident: decl.ident,
                    value: decl
                        .value
                        .map(|value| flatten_and_mark_dead_expression(value, substitution)),
                    property: decl.property,
                    ident_info: decl.ident_info,
                }),
                comment,
            }
        }
        StatementDesc::Block(block) => Statement {
            desc: StatementDesc::Block(flatten_and_mark_dead_block(block, substitution)),
            comment,
        },
        StatementDesc::Exp(expr) => Statement {
            desc: StatementDesc::Exp(flatten_and_mark_dead_expression(expr, substitution)),
            comment,
        },
        StatementDesc::Return(expr) => Statement {
            desc: StatementDesc::Return(flatten_and_mark_dead_expression(expr, substitution)),
            comment,
        },
        StatementDesc::If(cond, then_block, else_block) => Statement {
            desc: StatementDesc::If(
                flatten_and_mark_dead_expression(cond, substitution),
                flatten_and_mark_dead_block(then_block, substitution),
                flatten_and_mark_dead_block(else_block, substitution),
            ),
            comment,
        },
        StatementDesc::While(cond, body) => Statement {
            desc: StatementDesc::While(
                flatten_and_mark_dead_expression(cond, substitution),
                flatten_and_mark_dead_block(body, substitution),
            ),
            comment,
        },
        StatementDesc::ForRange(start, finish, ident, direction, body) => Statement {
            desc: StatementDesc::ForRange(
                start.map(|expr| flatten_and_mark_dead_expression(expr, substitution)),
                flatten_and_mark_dead_expression(finish, substitution),
                ident,
                direction,
                flatten_and_mark_dead_block(body, substitution),
            ),
            comment,
        },
        StatementDesc::IntSwitch(test, clauses, default) => Statement {
            desc: StatementDesc::IntSwitch(
                flatten_and_mark_dead_expression(test, substitution),
                clauses
                    .into_iter()
                    .map(|(tag, clause)| {
                        (
                            tag,
                            CaseClause {
                                body: flatten_and_mark_dead_block(clause.body, substitution),
                                should_break: clause.should_break,
                                comment: clause.comment,
                            },
                        )
                    })
                    .collect(),
                default.map(|block| flatten_and_mark_dead_block(block, substitution)),
            ),
            comment,
        },
        StatementDesc::StringSwitch(test, clauses, default) => Statement {
            desc: StatementDesc::StringSwitch(
                flatten_and_mark_dead_expression(test, substitution),
                clauses
                    .into_iter()
                    .map(|clause| crate::js_ir::StringClause {
                        tag_type: clause.tag_type,
                        clause: CaseClause {
                            body: flatten_and_mark_dead_block(clause.clause.body, substitution),
                            should_break: clause.clause.should_break,
                            comment: clause.clause.comment,
                        },
                    })
                    .collect(),
                default.map(|block| flatten_and_mark_dead_block(block, substitution)),
            ),
            comment,
        },
        StatementDesc::Throw(expr) => Statement {
            desc: StatementDesc::Throw(flatten_and_mark_dead_expression(expr, substitution)),
            comment,
        },
        StatementDesc::Try(body, catch, finally) => Statement {
            desc: StatementDesc::Try(
                flatten_and_mark_dead_block(body, substitution),
                catch.map(|(ident, block)| {
                    (ident, flatten_and_mark_dead_block(block, substitution))
                }),
                finally.map(|block| flatten_and_mark_dead_block(block, substitution)),
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

fn flatten_and_mark_dead_expression(
    expr: Expression,
    substitution: &mut HashMap<Ident, Expression>,
) -> Expression {
    if let Some(rewritten) = try_substitute_caml_block_projection(&expr, substitution) {
        return rewritten;
    }

    let Expression { desc, comment } = expr;
    let desc = match desc {
        ExpressionDesc::Length(inner, object) => ExpressionDesc::Length(
            Box::new(flatten_and_mark_dead_expression(*inner, substitution)),
            object,
        ),
        ExpressionDesc::IsNullOrUndefined(inner) => ExpressionDesc::IsNullOrUndefined(Box::new(
            flatten_and_mark_dead_expression(*inner, substitution),
        )),
        ExpressionDesc::StringAppend(left, right) => ExpressionDesc::StringAppend(
            Box::new(flatten_and_mark_dead_expression(*left, substitution)),
            Box::new(flatten_and_mark_dead_expression(*right, substitution)),
        ),
        ExpressionDesc::Bool(value) => ExpressionDesc::Bool(value),
        ExpressionDesc::Typeof(inner) => ExpressionDesc::Typeof(Box::new(
            flatten_and_mark_dead_expression(*inner, substitution),
        )),
        ExpressionDesc::In(left, right) => ExpressionDesc::In(
            Box::new(flatten_and_mark_dead_expression(*left, substitution)),
            Box::new(flatten_and_mark_dead_expression(*right, substitution)),
        ),
        ExpressionDesc::JsNot(inner) => ExpressionDesc::JsNot(Box::new(
            flatten_and_mark_dead_expression(*inner, substitution),
        )),
        ExpressionDesc::JsBnot(inner) => ExpressionDesc::JsBnot(Box::new(
            flatten_and_mark_dead_expression(*inner, substitution),
        )),
        ExpressionDesc::Seq(left, right) => ExpressionDesc::Seq(
            Box::new(flatten_and_mark_dead_expression(*left, substitution)),
            Box::new(flatten_and_mark_dead_expression(*right, substitution)),
        ),
        ExpressionDesc::Cond(test, consequent, alternate) => ExpressionDesc::Cond(
            Box::new(flatten_and_mark_dead_expression(*test, substitution)),
            Box::new(flatten_and_mark_dead_expression(*consequent, substitution)),
            Box::new(flatten_and_mark_dead_expression(*alternate, substitution)),
        ),
        ExpressionDesc::Bin(op, left, right) => ExpressionDesc::Bin(
            op,
            Box::new(flatten_and_mark_dead_expression(*left, substitution)),
            Box::new(flatten_and_mark_dead_expression(*right, substitution)),
        ),
        ExpressionDesc::FlatCall(func, args) => ExpressionDesc::FlatCall(
            Box::new(flatten_and_mark_dead_expression(*func, substitution)),
            Box::new(flatten_and_mark_dead_expression(*args, substitution)),
        ),
        ExpressionDesc::Call(func, args, info) => ExpressionDesc::Call(
            Box::new(flatten_and_mark_dead_expression(*func, substitution)),
            args.into_iter()
                .map(|arg| flatten_and_mark_dead_expression(arg, substitution))
                .collect(),
            info,
        ),
        ExpressionDesc::StringIndex(left, right) => ExpressionDesc::StringIndex(
            Box::new(flatten_and_mark_dead_expression(*left, substitution)),
            Box::new(flatten_and_mark_dead_expression(*right, substitution)),
        ),
        ExpressionDesc::ArrayIndex(left, right) => ExpressionDesc::ArrayIndex(
            Box::new(flatten_and_mark_dead_expression(*left, substitution)),
            Box::new(flatten_and_mark_dead_expression(*right, substitution)),
        ),
        ExpressionDesc::TaggedTemplate(tag, strings, values) => ExpressionDesc::TaggedTemplate(
            Box::new(flatten_and_mark_dead_expression(*tag, substitution)),
            strings
                .into_iter()
                .map(|value| flatten_and_mark_dead_expression(value, substitution))
                .collect(),
            values
                .into_iter()
                .map(|value| flatten_and_mark_dead_expression(value, substitution))
                .collect(),
        ),
        ExpressionDesc::StaticIndex(target, field, pos) => ExpressionDesc::StaticIndex(
            Box::new(flatten_and_mark_dead_expression(*target, substitution)),
            field,
            pos,
        ),
        ExpressionDesc::New(target, args) => ExpressionDesc::New(
            Box::new(flatten_and_mark_dead_expression(*target, substitution)),
            args.map(|items| {
                items
                    .into_iter()
                    .map(|arg| flatten_and_mark_dead_expression(arg, substitution))
                    .collect()
            }),
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
            body: flatten_and_mark_dead_block(body, substitution),
            env,
            return_unit,
            async_,
            directive,
        },
        ExpressionDesc::Str { delim, txt } => ExpressionDesc::Str { delim, txt },
        ExpressionDesc::RawJsCode(info) => ExpressionDesc::RawJsCode(info),
        ExpressionDesc::Array(items, mutable_flag) => ExpressionDesc::Array(
            items
                .into_iter()
                .map(|item| flatten_and_mark_dead_expression(item, substitution))
                .collect(),
            mutable_flag,
        ),
        ExpressionDesc::OptionalBlock(inner, flag) => ExpressionDesc::OptionalBlock(
            Box::new(flatten_and_mark_dead_expression(*inner, substitution)),
            flag,
        ),
        ExpressionDesc::CamlBlock(items, mutable_flag, tag, tag_info) => ExpressionDesc::CamlBlock(
            items
                .into_iter()
                .map(|item| flatten_and_mark_dead_expression(item, substitution))
                .collect(),
            mutable_flag,
            Box::new(flatten_and_mark_dead_expression(*tag, substitution)),
            tag_info,
        ),
        ExpressionDesc::CamlBlockTag(inner, tag) => ExpressionDesc::CamlBlockTag(
            Box::new(flatten_and_mark_dead_expression(*inner, substitution)),
            tag,
        ),
        ExpressionDesc::Number(number) => ExpressionDesc::Number(number),
        ExpressionDesc::Object(dup, props) => ExpressionDesc::Object(
            dup.map(|expr| Box::new(flatten_and_mark_dead_expression(*expr, substitution))),
            props
                .into_iter()
                .map(|(name, value)| (name, flatten_and_mark_dead_expression(value, substitution)))
                .collect(),
        ),
        ExpressionDesc::Undefined { is_unit } => ExpressionDesc::Undefined { is_unit },
        ExpressionDesc::Null => ExpressionDesc::Null,
        ExpressionDesc::Await(inner) => ExpressionDesc::Await(Box::new(
            flatten_and_mark_dead_expression(*inner, substitution),
        )),
        ExpressionDesc::Spread(inner) => ExpressionDesc::Spread(Box::new(
            flatten_and_mark_dead_expression(*inner, substitution),
        )),
    };

    Expression { desc, comment }
}

fn try_substitute_caml_block_projection(
    expr: &Expression,
    substitution: &HashMap<Ident, Expression>,
) -> Option<Expression> {
    match &expr.desc {
        ExpressionDesc::ArrayIndex(left, right) => {
            let ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)) = &left.desc else {
                return None;
            };
            let ExpressionDesc::Number(Number::Int { i, .. }) = right.desc else {
                return None;
            };
            substituted_caml_block_item(substitution, id, i)
        }
        ExpressionDesc::StaticIndex(target, _, Some(index)) => {
            let ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)) = &target.desc else {
                return None;
            };
            substituted_caml_block_item(substitution, id, *index)
        }
        _ => None,
    }
}

fn substituted_caml_block_item(
    substitution: &HashMap<Ident, Expression>,
    id: &Ident,
    index: i32,
) -> Option<Expression> {
    let expression = substitution.get(id)?;
    let ExpressionDesc::CamlBlock(items, MutableFlag::Immutable, _, _) = &expression.desc else {
        return None;
    };
    let item = items.get(usize::try_from(index).ok()?)?;
    is_simple_substituted_index_value(item).then(|| item.clone())
}

fn is_simple_block_binding_item(expr: &Expression) -> bool {
    matches!(
        expr.desc,
        ExpressionDesc::Var(_)
            | ExpressionDesc::Number(_)
            | ExpressionDesc::Str { .. }
            | ExpressionDesc::Bool(_)
            | ExpressionDesc::Undefined { .. }
    )
}

fn is_simple_substituted_index_value(expr: &Expression) -> bool {
    matches!(
        expr.desc,
        ExpressionDesc::Var(_)
            | ExpressionDesc::Number(_)
            | ExpressionDesc::Str { .. }
            | ExpressionDesc::Undefined { .. }
    )
}

fn block_substitution_name(ident: &Ident, tag_info: &TagInfo, index: usize) -> String {
    let suffix = match tag_info {
        TagInfo::Module(fields) => fields
            .get(index)
            .cloned()
            .unwrap_or_else(|| index.to_string()),
        TagInfo::Record { fields, .. } => fields
            .get(index)
            .map(|(field, _)| field.clone())
            .unwrap_or_else(|| index.to_string()),
        _ => index.to_string(),
    };
    format!("{}_{}", ident.name(), suffix)
}

#[derive(Debug, Clone, Copy)]
enum MarkDeadInfo {
    Recursive,
    Info {
        pure: bool,
        used: bool,
        exported: bool,
    },
}

fn mark_dead_code(program: &mut Program) {
    let mut states = HashMap::new();
    collect_mark_dead_states_block(&program.block, &program.export_set, &mut states);
    apply_mark_dead_states_block(&mut program.block, &states);
}

fn collect_mark_dead_states_block(
    block: &Block,
    export_set: &HashSet<Ident>,
    states: &mut HashMap<Ident, MarkDeadInfo>,
) {
    for stmt in block {
        collect_mark_dead_states_statement(stmt, export_set, states);
    }
}

fn collect_mark_dead_states_statement(
    stmt: &Statement,
    export_set: &HashSet<Ident>,
    states: &mut HashMap<Ident, MarkDeadInfo>,
) {
    match &stmt.desc {
        StatementDesc::Block(block) => collect_mark_dead_states_block(block, export_set, states),
        StatementDesc::Variable(decl) => {
            collect_mark_dead_states_variable(decl, export_set, states)
        }
        StatementDesc::Exp(expr) | StatementDesc::Return(expr) | StatementDesc::Throw(expr) => {
            collect_mark_dead_states_expression(expr, states);
        }
        StatementDesc::If(cond, then_block, else_block) => {
            collect_mark_dead_states_expression(cond, states);
            collect_mark_dead_states_block(then_block, export_set, states);
            collect_mark_dead_states_block(else_block, export_set, states);
        }
        StatementDesc::While(cond, body) => {
            collect_mark_dead_states_expression(cond, states);
            collect_mark_dead_states_block(body, export_set, states);
        }
        StatementDesc::ForRange(start, finish, _, _, body) => {
            if let Some(start) = start {
                collect_mark_dead_states_expression(start, states);
            }
            collect_mark_dead_states_expression(finish, states);
            collect_mark_dead_states_block(body, export_set, states);
        }
        StatementDesc::IntSwitch(test, clauses, default) => {
            collect_mark_dead_states_expression(test, states);
            for (_, clause) in clauses {
                collect_mark_dead_states_block(&clause.body, export_set, states);
            }
            if let Some(default) = default {
                collect_mark_dead_states_block(default, export_set, states);
            }
        }
        StatementDesc::StringSwitch(test, clauses, default) => {
            collect_mark_dead_states_expression(test, states);
            for clause in clauses {
                collect_mark_dead_states_block(&clause.clause.body, export_set, states);
            }
            if let Some(default) = default {
                collect_mark_dead_states_block(default, export_set, states);
            }
        }
        StatementDesc::Try(body, catch, finally) => {
            collect_mark_dead_states_block(body, export_set, states);
            if let Some((_, block)) = catch {
                collect_mark_dead_states_block(block, export_set, states);
            }
            if let Some(block) = finally {
                collect_mark_dead_states_block(block, export_set, states);
            }
        }
        StatementDesc::Debugger | StatementDesc::Break | StatementDesc::Continue => {}
    }
}

fn collect_mark_dead_states_variable(
    decl: &VariableDeclaration,
    export_set: &HashSet<Ident>,
    states: &mut HashMap<Ident, MarkDeadInfo>,
) {
    match decl.ident_info.used_stats {
        UsedStats::DeadPure => return,
        UsedStats::DeadNonPure => {
            if let Some(value) = &decl.value {
                collect_mark_dead_states_expression(value, states);
            }
            return;
        }
        _ => {}
    }

    let pure = match &decl.value {
        None => true,
        Some(value) => {
            collect_mark_dead_states_expression(value, states);
            js_expr_no_side_effects(value)
        }
    };
    let exported = export_set.contains(&decl.ident);
    match states.get(&decl.ident).copied() {
        Some(MarkDeadInfo::Recursive) => {
            states.insert(
                decl.ident.clone(),
                MarkDeadInfo::Info {
                    pure,
                    used: true,
                    exported,
                },
            );
        }
        Some(MarkDeadInfo::Info { .. }) => {}
        None => {
            states.insert(
                decl.ident.clone(),
                MarkDeadInfo::Info {
                    pure,
                    used: false,
                    exported,
                },
            );
        }
    }
}

fn collect_mark_dead_states_expression(
    expr: &Expression,
    states: &mut HashMap<Ident, MarkDeadInfo>,
) {
    match &expr.desc {
        ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)) => mark_dead_ident_use(id, states),
        ExpressionDesc::Var(crate::js_ir::VIdent::Qualified(_, _))
        | ExpressionDesc::Undefined { .. }
        | ExpressionDesc::Null
        | ExpressionDesc::Bool(_)
        | ExpressionDesc::Str { .. }
        | ExpressionDesc::RawJsCode(_)
        | ExpressionDesc::Number(_) => {}
        ExpressionDesc::Length(inner, _)
        | ExpressionDesc::IsNullOrUndefined(inner)
        | ExpressionDesc::Typeof(inner)
        | ExpressionDesc::JsNot(inner)
        | ExpressionDesc::JsBnot(inner)
        | ExpressionDesc::CamlBlockTag(inner, _)
        | ExpressionDesc::OptionalBlock(inner, _)
        | ExpressionDesc::Await(inner)
        | ExpressionDesc::Spread(inner) => collect_mark_dead_states_expression(inner, states),
        ExpressionDesc::StringAppend(left, right)
        | ExpressionDesc::In(left, right)
        | ExpressionDesc::Seq(left, right)
        | ExpressionDesc::Bin(_, left, right)
        | ExpressionDesc::FlatCall(left, right)
        | ExpressionDesc::StringIndex(left, right)
        | ExpressionDesc::ArrayIndex(left, right) => {
            collect_mark_dead_states_expression(left, states);
            collect_mark_dead_states_expression(right, states);
        }
        ExpressionDesc::Cond(test, consequent, alternate) => {
            collect_mark_dead_states_expression(test, states);
            collect_mark_dead_states_expression(consequent, states);
            collect_mark_dead_states_expression(alternate, states);
        }
        ExpressionDesc::Call(func, args, _) => {
            collect_mark_dead_states_expression(func, states);
            for arg in args {
                collect_mark_dead_states_expression(arg, states);
            }
        }
        ExpressionDesc::TaggedTemplate(tag, strings, values) => {
            collect_mark_dead_states_expression(tag, states);
            for string in strings {
                collect_mark_dead_states_expression(string, states);
            }
            for value in values {
                collect_mark_dead_states_expression(value, states);
            }
        }
        ExpressionDesc::StaticIndex(target, _, _) => {
            collect_mark_dead_states_expression(target, states)
        }
        ExpressionDesc::New(target, args) => {
            collect_mark_dead_states_expression(target, states);
            if let Some(args) = args {
                for arg in args {
                    collect_mark_dead_states_expression(arg, states);
                }
            }
        }
        ExpressionDesc::Fun { body, .. } => {
            for stmt in body {
                collect_mark_dead_states_statement(stmt, &HashSet::new(), states);
            }
        }
        ExpressionDesc::Array(items, _) => {
            for item in items {
                collect_mark_dead_states_expression(item, states);
            }
        }
        ExpressionDesc::CamlBlock(items, _, tag, _) => {
            for item in items {
                collect_mark_dead_states_expression(item, states);
            }
            collect_mark_dead_states_expression(tag, states);
        }
        ExpressionDesc::Object(dup, props) => {
            if let Some(dup) = dup {
                collect_mark_dead_states_expression(dup, states);
            }
            for (_, value) in props {
                collect_mark_dead_states_expression(value, states);
            }
        }
    }
}

fn mark_dead_ident_use(id: &Ident, states: &mut HashMap<Ident, MarkDeadInfo>) {
    match states.get_mut(id) {
        None => {
            states.insert(id.clone(), MarkDeadInfo::Recursive);
        }
        Some(MarkDeadInfo::Recursive) => {}
        Some(MarkDeadInfo::Info { used, .. }) => {
            *used = true;
        }
    }
}

fn apply_mark_dead_states_block(block: &mut Block, states: &HashMap<Ident, MarkDeadInfo>) {
    for stmt in block {
        apply_mark_dead_states_statement(stmt, states);
    }
}

fn apply_mark_dead_states_statement(stmt: &mut Statement, states: &HashMap<Ident, MarkDeadInfo>) {
    match &mut stmt.desc {
        StatementDesc::Block(block) => apply_mark_dead_states_block(block, states),
        StatementDesc::Variable(decl) => {
            apply_mark_dead_states_variable(decl, states);
            if let Some(value) = &mut decl.value {
                apply_mark_dead_states_expression(value, states);
            }
        }
        StatementDesc::Exp(expr) | StatementDesc::Return(expr) | StatementDesc::Throw(expr) => {
            apply_mark_dead_states_expression(expr, states);
        }
        StatementDesc::If(_, then_block, else_block) => {
            apply_mark_dead_states_block(then_block, states);
            apply_mark_dead_states_block(else_block, states);
        }
        StatementDesc::While(_, body) => apply_mark_dead_states_block(body, states),
        StatementDesc::ForRange(_, _, _, _, body) => apply_mark_dead_states_block(body, states),
        StatementDesc::IntSwitch(_, clauses, default) => {
            for (_, clause) in clauses {
                apply_mark_dead_states_block(&mut clause.body, states);
            }
            if let Some(default) = default {
                apply_mark_dead_states_block(default, states);
            }
        }
        StatementDesc::StringSwitch(_, clauses, default) => {
            for clause in clauses {
                apply_mark_dead_states_block(&mut clause.clause.body, states);
            }
            if let Some(default) = default {
                apply_mark_dead_states_block(default, states);
            }
        }
        StatementDesc::Try(body, catch, finally) => {
            apply_mark_dead_states_block(body, states);
            if let Some((_, block)) = catch {
                apply_mark_dead_states_block(block, states);
            }
            if let Some(block) = finally {
                apply_mark_dead_states_block(block, states);
            }
        }
        StatementDesc::Debugger | StatementDesc::Break | StatementDesc::Continue => {}
    }
}

fn apply_mark_dead_states_variable(
    decl: &mut VariableDeclaration,
    states: &HashMap<Ident, MarkDeadInfo>,
) {
    let Some(MarkDeadInfo::Info {
        pure,
        used,
        exported,
    }) = states.get(&decl.ident).copied()
    else {
        return;
    };

    let status = if exported {
        UsedStats::Exported
    } else if used {
        UsedStats::Used
    } else if pure {
        UsedStats::DeadPure
    } else {
        UsedStats::DeadNonPure
    };
    update_used_stats(&mut decl.ident_info, status);
}

fn apply_mark_dead_states_expression(expr: &mut Expression, states: &HashMap<Ident, MarkDeadInfo>) {
    match &mut expr.desc {
        ExpressionDesc::Length(inner, _)
        | ExpressionDesc::IsNullOrUndefined(inner)
        | ExpressionDesc::Typeof(inner)
        | ExpressionDesc::JsNot(inner)
        | ExpressionDesc::JsBnot(inner)
        | ExpressionDesc::CamlBlockTag(inner, _)
        | ExpressionDesc::OptionalBlock(inner, _)
        | ExpressionDesc::Await(inner)
        | ExpressionDesc::Spread(inner) => apply_mark_dead_states_expression(inner, states),
        ExpressionDesc::StringAppend(left, right)
        | ExpressionDesc::In(left, right)
        | ExpressionDesc::Seq(left, right)
        | ExpressionDesc::Bin(_, left, right)
        | ExpressionDesc::FlatCall(left, right)
        | ExpressionDesc::StringIndex(left, right)
        | ExpressionDesc::ArrayIndex(left, right) => {
            apply_mark_dead_states_expression(left, states);
            apply_mark_dead_states_expression(right, states);
        }
        ExpressionDesc::Cond(test, consequent, alternate) => {
            apply_mark_dead_states_expression(test, states);
            apply_mark_dead_states_expression(consequent, states);
            apply_mark_dead_states_expression(alternate, states);
        }
        ExpressionDesc::Call(func, args, _) => {
            apply_mark_dead_states_expression(func, states);
            for arg in args {
                apply_mark_dead_states_expression(arg, states);
            }
        }
        ExpressionDesc::TaggedTemplate(tag, strings, values) => {
            apply_mark_dead_states_expression(tag, states);
            for string in strings {
                apply_mark_dead_states_expression(string, states);
            }
            for value in values {
                apply_mark_dead_states_expression(value, states);
            }
        }
        ExpressionDesc::StaticIndex(target, _, _) => {
            apply_mark_dead_states_expression(target, states)
        }
        ExpressionDesc::New(target, args) => {
            apply_mark_dead_states_expression(target, states);
            if let Some(args) = args {
                for arg in args {
                    apply_mark_dead_states_expression(arg, states);
                }
            }
        }
        ExpressionDesc::Fun { body, .. } => apply_mark_dead_states_block(body, states),
        ExpressionDesc::Array(items, _) => {
            for item in items {
                apply_mark_dead_states_expression(item, states);
            }
        }
        ExpressionDesc::CamlBlock(items, _, tag, _) => {
            for item in items {
                apply_mark_dead_states_expression(item, states);
            }
            apply_mark_dead_states_expression(tag, states);
        }
        ExpressionDesc::Object(dup, props) => {
            if let Some(dup) = dup {
                apply_mark_dead_states_expression(dup, states);
            }
            for (_, value) in props {
                apply_mark_dead_states_expression(value, states);
            }
        }
        ExpressionDesc::Var(_)
        | ExpressionDesc::Undefined { .. }
        | ExpressionDesc::Null
        | ExpressionDesc::Bool(_)
        | ExpressionDesc::Str { .. }
        | ExpressionDesc::RawJsCode(_)
        | ExpressionDesc::Number(_) => {}
    }
}

fn update_used_stats(info: &mut IdentInfo, status: UsedStats) {
    if matches!(
        info.used_stats,
        UsedStats::DeadPure | UsedStats::DeadNonPure | UsedStats::Exported
    ) {
        return;
    }
    info.used_stats = status;
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

fn apply_js_shake_pass(mut deps: DepsProgram) -> DepsProgram {
    deps.program = shake_program(deps.program);
    deps
}

fn shake_program(mut program: Program) -> Program {
    program.block = shake_block(&program.block, &program.export_set);
    program
}

fn shake_block(block: &Block, export_set: &HashSet<Ident>) -> Block {
    let block = flatten_toplevel_block(block);
    let required = fixed_point_required_idents(&block, export_set);

    block
        .into_iter()
        .filter(|stmt| match &stmt.desc {
            StatementDesc::Variable(VariableDeclaration { ident, value, .. }) => {
                if required.contains(ident) {
                    true
                } else {
                    value
                        .as_ref()
                        .is_some_and(|expr| !js_expr_no_side_effects(expr))
                }
            }
            _ => !js_statement_no_side_effects(stmt),
        })
        .collect()
}

fn flatten_toplevel_block(block: &Block) -> Block {
    let mut flattened = Vec::new();
    flatten_toplevel_block_into(block, &mut flattened);
    flattened
}

fn flatten_toplevel_block_into(block: &Block, flattened: &mut Block) {
    for stmt in block {
        match &stmt.desc {
            StatementDesc::Variable(VariableDeclaration {
                ident_info:
                    IdentInfo {
                        used_stats: UsedStats::DeadPure,
                    },
                ..
            })
            | StatementDesc::Variable(VariableDeclaration {
                ident_info:
                    IdentInfo {
                        used_stats: UsedStats::DeadNonPure,
                    },
                value: None,
                ..
            }) => {}
            StatementDesc::Block(inner) => flatten_toplevel_block_into(inner, flattened),
            _ => flattened.push(stmt.clone()),
        }
    }
}

fn fixed_point_required_idents(block: &Block, export_set: &HashSet<Ident>) -> HashSet<Ident> {
    let mut required = required_idents(block, export_set, true);
    loop {
        let next = required_idents(block, &required, false);
        if next.len() == required.len() && next.is_subset(&required) {
            return required;
        }
        required = next;
    }
}

fn required_idents(
    block: &Block,
    initial: &HashSet<Ident>,
    count_effect_statements: bool,
) -> HashSet<Ident> {
    let mut required = initial.clone();

    for stmt in block {
        match &stmt.desc {
            StatementDesc::Variable(VariableDeclaration { ident, value, .. }) => {
                if required.contains(ident) {
                    if let Some(value) = value {
                        required.extend(free_variables_of_expression(value));
                    }
                } else if let Some(value) = value {
                    if !js_expr_no_side_effects(value) {
                        required.insert(ident.clone());
                        required.extend(free_variables_of_expression(value));
                    }
                }
            }
            _ => {
                if count_effect_statements && !js_statement_no_side_effects(stmt) {
                    required.extend(free_variables_of_statement(stmt));
                }
            }
        }
    }

    required
}

#[derive(Default)]
struct JsIdentStats {
    used_idents: HashSet<Ident>,
    defined_idents: HashSet<Ident>,
}

impl JsIdentStats {
    fn with_defined<I>(idents: I) -> Self
    where
        I: IntoIterator<Item = Ident>,
    {
        Self {
            used_idents: HashSet::new(),
            defined_idents: idents.into_iter().collect(),
        }
    }

    fn add_used_ident(&mut self, ident: &Ident) {
        if !self.defined_idents.contains(ident) {
            self.used_idents.insert(ident.clone());
        }
    }

    fn add_defined_ident(&mut self, ident: &Ident) {
        self.defined_idents.insert(ident.clone());
    }

    fn extend_free_idents(&mut self, other: HashSet<Ident>) {
        self.used_idents.extend(other);
    }

    fn free_variables(mut self) -> HashSet<Ident> {
        self.used_idents
            .retain(|ident| !self.defined_idents.contains(ident));
        self.used_idents
    }
}

fn free_variables_of_statement(stmt: &Statement) -> HashSet<Ident> {
    let mut stats = JsIdentStats::default();
    collect_statement_idents(stmt, &mut stats);
    stats.free_variables()
}

fn free_variables_of_expression(expr: &Expression) -> HashSet<Ident> {
    let mut stats = JsIdentStats::default();
    collect_expression_idents(expr, &mut stats);
    stats.free_variables()
}

fn free_variables_of_block_with_defined(
    block: &Block,
    defined: impl IntoIterator<Item = Ident>,
) -> HashSet<Ident> {
    let mut stats = JsIdentStats::with_defined(defined);
    collect_block_idents(block, &mut stats);
    stats.free_variables()
}

fn collect_block_idents(block: &Block, stats: &mut JsIdentStats) {
    for stmt in block {
        collect_statement_idents(stmt, stats);
    }
}

fn collect_statement_idents(stmt: &Statement, stats: &mut JsIdentStats) {
    match &stmt.desc {
        StatementDesc::Block(block) => collect_block_idents(block, stats),
        StatementDesc::Variable(VariableDeclaration { ident, value, .. }) => {
            stats.add_defined_ident(ident);
            if let Some(value) = value {
                collect_expression_idents(value, stats);
            }
        }
        StatementDesc::Exp(expr) | StatementDesc::Return(expr) | StatementDesc::Throw(expr) => {
            collect_expression_idents(expr, stats);
        }
        StatementDesc::If(cond, then_block, else_block) => {
            collect_expression_idents(cond, stats);
            collect_block_idents(then_block, stats);
            collect_block_idents(else_block, stats);
        }
        StatementDesc::While(cond, body) => {
            collect_expression_idents(cond, stats);
            collect_block_idents(body, stats);
        }
        StatementDesc::ForRange(start, finish, loop_ident, _, body) => {
            if let Some(start) = start {
                collect_expression_idents(start, stats);
            }
            collect_expression_idents(finish, stats);
            stats.extend_free_idents(free_variables_of_block_with_defined(
                body,
                std::iter::once(loop_ident.clone()),
            ));
        }
        StatementDesc::IntSwitch(test, clauses, default) => {
            collect_expression_idents(test, stats);
            for (_, clause) in clauses {
                collect_block_idents(&clause.body, stats);
            }
            if let Some(default) = default {
                collect_block_idents(default, stats);
            }
        }
        StatementDesc::StringSwitch(test, clauses, default) => {
            collect_expression_idents(test, stats);
            for clause in clauses {
                collect_block_idents(&clause.clause.body, stats);
            }
            if let Some(default) = default {
                collect_block_idents(default, stats);
            }
        }
        StatementDesc::Try(body, catch, finally) => {
            collect_block_idents(body, stats);
            if let Some((catch_ident, catch_block)) = catch {
                stats.extend_free_idents(free_variables_of_block_with_defined(
                    catch_block,
                    std::iter::once(catch_ident.clone()),
                ));
            }
            if let Some(finally) = finally {
                collect_block_idents(finally, stats);
            }
        }
        StatementDesc::Debugger | StatementDesc::Break | StatementDesc::Continue => {}
    }
}

fn collect_expression_idents(expr: &Expression, stats: &mut JsIdentStats) {
    match &expr.desc {
        ExpressionDesc::Var(crate::js_ir::VIdent::Id(ident)) => stats.add_used_ident(ident),
        ExpressionDesc::Var(crate::js_ir::VIdent::Qualified(_, _))
        | ExpressionDesc::Undefined { .. }
        | ExpressionDesc::Null
        | ExpressionDesc::Bool(_)
        | ExpressionDesc::Str { .. }
        | ExpressionDesc::RawJsCode(_)
        | ExpressionDesc::Number(_) => {}
        ExpressionDesc::Length(inner, _)
        | ExpressionDesc::IsNullOrUndefined(inner)
        | ExpressionDesc::Typeof(inner)
        | ExpressionDesc::JsNot(inner)
        | ExpressionDesc::JsBnot(inner)
        | ExpressionDesc::CamlBlockTag(inner, _)
        | ExpressionDesc::OptionalBlock(inner, _)
        | ExpressionDesc::Await(inner)
        | ExpressionDesc::Spread(inner) => collect_expression_idents(inner, stats),
        ExpressionDesc::StringAppend(left, right)
        | ExpressionDesc::In(left, right)
        | ExpressionDesc::Seq(left, right)
        | ExpressionDesc::Bin(_, left, right)
        | ExpressionDesc::FlatCall(left, right)
        | ExpressionDesc::StringIndex(left, right)
        | ExpressionDesc::ArrayIndex(left, right) => {
            collect_expression_idents(left, stats);
            collect_expression_idents(right, stats);
        }
        ExpressionDesc::Cond(test, consequent, alternate) => {
            collect_expression_idents(test, stats);
            collect_expression_idents(consequent, stats);
            collect_expression_idents(alternate, stats);
        }
        ExpressionDesc::Call(func, args, _) => {
            collect_expression_idents(func, stats);
            for arg in args {
                collect_expression_idents(arg, stats);
            }
        }
        ExpressionDesc::TaggedTemplate(tag, strings, values) => {
            collect_expression_idents(tag, stats);
            for string in strings {
                collect_expression_idents(string, stats);
            }
            for value in values {
                collect_expression_idents(value, stats);
            }
        }
        ExpressionDesc::StaticIndex(target, _, _) => collect_expression_idents(target, stats),
        ExpressionDesc::New(target, args) => {
            collect_expression_idents(target, stats);
            if let Some(args) = args {
                for arg in args {
                    collect_expression_idents(arg, stats);
                }
            }
        }
        ExpressionDesc::Fun { params, body, .. } => {
            stats.extend_free_idents(free_variables_of_block_with_defined(
                body,
                params.iter().cloned(),
            ));
        }
        ExpressionDesc::Array(items, _) => {
            for item in items {
                collect_expression_idents(item, stats);
            }
        }
        ExpressionDesc::CamlBlock(items, _, tag, _) => {
            for item in items {
                collect_expression_idents(item, stats);
            }
            collect_expression_idents(tag, stats);
        }
        ExpressionDesc::Object(dup, props) => {
            if let Some(dup) = dup {
                collect_expression_idents(dup, stats);
            }
            for (_, value) in props {
                collect_expression_idents(value, stats);
            }
        }
    }
}

fn js_block_no_side_effects(block: &Block) -> bool {
    block.iter().all(js_statement_no_side_effects)
}

fn js_statement_no_side_effects(stmt: &Statement) -> bool {
    match &stmt.desc {
        StatementDesc::Throw(_)
        | StatementDesc::Debugger
        | StatementDesc::Break
        | StatementDesc::Variable(_)
        | StatementDesc::Continue => false,
        StatementDesc::Exp(expr) | StatementDesc::Return(expr) => js_expr_no_side_effects(expr),
        StatementDesc::Block(block) => js_block_no_side_effects(block),
        StatementDesc::If(cond, then_block, else_block) => {
            js_expr_no_side_effects(cond)
                && js_block_no_side_effects(then_block)
                && js_block_no_side_effects(else_block)
        }
        StatementDesc::While(cond, body) => {
            js_expr_no_side_effects(cond) && js_block_no_side_effects(body)
        }
        StatementDesc::ForRange(start, finish, _, _, body) => {
            start.as_ref().is_none_or(js_expr_no_side_effects)
                && js_expr_no_side_effects(finish)
                && js_block_no_side_effects(body)
        }
        StatementDesc::IntSwitch(test, clauses, default) => {
            js_expr_no_side_effects(test)
                && clauses
                    .iter()
                    .all(|(_, clause)| js_block_no_side_effects(&clause.body))
                && default.as_ref().is_none_or(js_block_no_side_effects)
        }
        StatementDesc::StringSwitch(test, clauses, default) => {
            js_expr_no_side_effects(test)
                && clauses
                    .iter()
                    .all(|clause| js_block_no_side_effects(&clause.clause.body))
                && default.as_ref().is_none_or(js_block_no_side_effects)
        }
        StatementDesc::Try(body, catch, finally) => {
            js_block_no_side_effects(body)
                && catch
                    .as_ref()
                    .is_none_or(|(_, block)| js_block_no_side_effects(block))
                && finally.as_ref().is_none_or(js_block_no_side_effects)
        }
    }
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
    use crate::js_ir::{ModulePathResolver, print_block};
    use crate::lambda::constant::{Constant, ConstructorRuntimeTag, ConstructorTag, PointerInfo};
    use crate::lambda::primitive::{
        ExternalArgAttr, ExternalArgConst, ExternalArgDelim, ExternalArgLabel, ExternalArgSpec,
        ExternalFfiKind, ExternalFfiSpec, ExternalModuleBindName, ExternalModuleName,
        ExternalObjLabel, ExternalObjSpec, ExternalReturnWrapper, ExternalSpec,
    };
    use crate::lambda::{ApInfo, Apply, ApplyStatus, InlineAttribute, Lambda};
    use crate::location::Location;
    use std::fs;
    use std::path::PathBuf;
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

    fn resolver_with_checked_in_cmj() -> ModulePathResolver {
        let mut persistent_env = PersistentEnv::new();
        persistent_env.add_load_path(
            PathBuf::from(env!("CARGO_MANIFEST_DIR"))
                .parent()
                .expect("repo root")
                .join("tests")
                .join("tests")
                .join("lib")
                .join("ocaml"),
        );
        ModulePathResolver::from_compile_options(
            None,
            Some(std::path::Path::new("/tmp/Effect.mjs")),
            None,
            Some(persistent_env),
        )
    }

    #[test]
    fn test_compile_constant_int() {
        let mut compiler = LambdaCompiler::new();
        let lam = Lambda::const_(Constant::int(7));
        let program = compiler.compile_program(&lam);
        assert!(!program.block.is_empty());
    }

    #[test]
    fn compile_constant_named_constructor_uses_string_runtime_name() {
        let compiled = LambdaCompiler::compile_constant(&Constant::Int {
            i: 0,
            comment: Some(PointerInfo::Constructor(ConstructorTag {
                name: "NoParam".to_string(),
                const_: 1,
                non_const: 2,
                runtime_tag: None,
            })),
        });

        assert!(matches!(
            compiled,
            Expression {
                desc: ExpressionDesc::Str { ref txt, .. },
                ..
            } if txt == "NoParam"
        ));
    }

    #[test]
    fn compile_constant_constructor_runtime_tag_uses_runtime_literal() {
        let compiled = LambdaCompiler::compile_constant(&Constant::Int {
            i: 0,
            comment: Some(PointerInfo::Constructor(ConstructorTag {
                name: "Three".to_string(),
                const_: 1,
                non_const: 0,
                runtime_tag: Some(ConstructorRuntimeTag::String("three".to_string())),
            })),
        });

        assert!(matches!(
            compiled,
            Expression {
                desc: ExpressionDesc::Str { ref txt, .. },
                ..
            } if txt == "three"
        ));
    }

    #[test]
    fn compile_constant_empty_list_keeps_numeric_zero() {
        let compiled = LambdaCompiler::compile_constant(&Constant::Int {
            i: 0,
            comment: Some(PointerInfo::Constructor(ConstructorTag {
                name: "[]".to_string(),
                const_: 1,
                non_const: 1,
                runtime_tag: None,
            })),
        });

        assert!(matches!(
            compiled,
            Expression {
                desc: ExpressionDesc::Number(Number::Int { i: 0, .. }),
                ..
            }
        ));
    }

    #[test]
    fn compile_deps_program_reuses_same_name_export_targets() {
        let mut compiler = LambdaCompiler::new();
        let source = Ident::create_local("value");
        let rebound_export = Ident::create_local("value");
        let param = Ident::create_local("arg");
        let lam = Lambda::let_(
            LetKind::Strict,
            source.clone(),
            Lambda::function_(
                1,
                vec![param.clone()],
                Lambda::var(param),
                crate::lambda::FunctionAttribute::default(),
            ),
            Lambda::let_(
                LetKind::Alias,
                rebound_export.clone(),
                Lambda::var(source.clone()),
                Lambda::prim(
                    Primitive::Pmakeblock(
                        0,
                        TagInfo::ModuleExport(vec![rebound_export]),
                        Mutable::Immutable,
                    ),
                    vec![Lambda::var(source.clone())],
                    Location::none(),
                ),
            ),
        );

        let deps = compiler.compile_deps_program(&lam);

        let [exported] = deps.program.exports.as_slice() else {
            panic!("expected a single export");
        };
        assert!(
            exported.same(&source),
            "expected export {:?}, got {:?}",
            source,
            exported
        );

        let [stmt] = deps.program.block.as_slice() else {
            panic!("expected the rebound export alias to be shaken away");
        };
        match &stmt.desc {
            StatementDesc::Variable(VariableDeclaration { ident, .. }) => {
                assert!(ident.same(&source))
            }
            other => panic!("expected only the original exported binding to remain, got {other:?}"),
        }
    }

    #[test]
    fn compile_deps_program_keeps_same_name_export_aliases_for_unbound_globals() {
        let mut compiler = LambdaCompiler::new();
        let global = Ident::create_persistent("parseInt");
        let rebound_export = Ident::create_local("parseInt");
        let lam = Lambda::let_(
            LetKind::Alias,
            rebound_export.clone(),
            Lambda::var(global.clone()),
            Lambda::prim(
                Primitive::Pmakeblock(
                    0,
                    TagInfo::ModuleExport(vec![rebound_export.clone()]),
                    Mutable::Immutable,
                ),
                vec![Lambda::var(rebound_export.clone())],
                Location::none(),
            ),
        );

        let deps = compiler.compile_deps_program(&lam);

        let [exported] = deps.program.exports.as_slice() else {
            panic!("expected a single export");
        };
        assert!(exported.same(&rebound_export));

        let [stmt] = deps.program.block.as_slice() else {
            panic!("expected the rebound alias to stay as a real binding");
        };
        match &stmt.desc {
            StatementDesc::Variable(VariableDeclaration { ident, .. }) => {
                assert!(ident.same(&rebound_export));
            }
            other => panic!("expected the rebound export binding to remain, got {other:?}"),
        }
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
    fn int_switch_expressions_assign_branch_values_into_the_result_temp() {
        let mut compiler = LambdaCompiler::new();
        let scrutinee = Ident::create_local("scrutinee");
        let compiled = compiler.compile_expr(&Lambda::Lswitch(
            Box::new(Lambda::var(scrutinee.clone())),
            LambdaSwitch {
                sw_consts_full: true,
                sw_consts: vec![
                    (0, Lambda::const_(Constant::int(1))),
                    (1, Lambda::const_(Constant::int(2))),
                ],
                sw_blocks_full: false,
                sw_blocks: vec![],
                sw_failaction: Some(Box::new(Lambda::const_(Constant::int(3)))),
                sw_names: None,
            },
        ));

        let [declare, switch_stmt] = compiled.prelude.as_slice() else {
            panic!("expected a declaration and switch statement");
        };
        let StatementDesc::Variable(VariableDeclaration { ident: result, .. }) = &declare.desc
        else {
            panic!("expected the switch temporary declaration");
        };
        let StatementDesc::IntSwitch(test, clauses, Some(default_block)) = &switch_stmt.desc else {
            panic!("expected an integer switch with a default block");
        };
        assert!(matches!(
            test,
            Expression {
                desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                ..
            } if id.same(&scrutinee)
        ));
        assert!(matches!(
            compiled.expr,
            Expression {
                desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                ..
            } if id.same(result)
        ));

        let expected_cases = [(0, 1_i32), (1, 2_i32)];
        for ((tag, clause), (expected_tag, expected_value)) in clauses.iter().zip(expected_cases) {
            assert_eq!(*tag, expected_tag);
            assert_switch_case_assigns_int_result(&clause.body, result, expected_value);
        }
        assert_switch_case_assigns_int_result(default_block, result, 3);
    }

    #[test]
    fn string_switch_expressions_assign_branch_values_into_the_result_temp() {
        let mut compiler = LambdaCompiler::new();
        let scrutinee = Ident::create_local("scrutinee");
        let compiled = compiler.compile_expr(&Lambda::LstringSwitch(
            Box::new(Lambda::var(scrutinee.clone())),
            vec![
                ("linux".to_string(), Lambda::const_(Constant::int(1))),
                ("darwin".to_string(), Lambda::const_(Constant::int(2))),
            ],
            Some(Box::new(Lambda::const_(Constant::int(3)))),
        ));

        let [declare, switch_stmt] = compiled.prelude.as_slice() else {
            panic!("expected a declaration and string switch statement");
        };
        let StatementDesc::Variable(VariableDeclaration { ident: result, .. }) = &declare.desc
        else {
            panic!("expected the string switch temporary declaration");
        };
        let StatementDesc::StringSwitch(test, clauses, Some(default_block)) = &switch_stmt.desc
        else {
            panic!("expected a string switch with a default block");
        };
        assert!(matches!(
            test,
            Expression {
                desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                ..
            } if id.same(&scrutinee)
        ));
        assert!(matches!(
            compiled.expr,
            Expression {
                desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                ..
            } if id.same(result)
        ));

        let expected_cases = [("linux", 1_i32), ("darwin", 2_i32)];
        for (clause, (expected_tag, expected_value)) in clauses.iter().zip(expected_cases) {
            assert_eq!(clause.tag_type, expected_tag);
            assert_switch_case_assigns_int_result(&clause.clause.body, result, expected_value);
        }
        assert_switch_case_assigns_int_result(default_block, result, 3);
    }

    #[test]
    fn let_bindings_lower_string_switches_directly_into_the_declared_binding() {
        let mut compiler = LambdaCompiler::new();
        let version = Ident::create_local("version");
        let scrutinee = Ident::create_local("platform");
        let program = compiler.compile_program(&Lambda::Llet(
            LetKind::Strict,
            version.clone(),
            Box::new(Lambda::LstringSwitch(
                Box::new(Lambda::var(scrutinee.clone())),
                vec![
                    ("linux".to_string(), Lambda::const_(Constant::int(1))),
                    ("darwin".to_string(), Lambda::const_(Constant::int(2))),
                ],
                Some(Box::new(Lambda::const_(Constant::int(3)))),
            )),
            Box::new(Lambda::var(version.clone())),
        ));

        let [declare, switch_stmt] = program.block.as_slice() else {
            panic!("expected a declaration followed by a string switch");
        };
        let StatementDesc::Variable(VariableDeclaration {
            ident, value: None, ..
        }) = &declare.desc
        else {
            panic!("expected an uninitialized binding declaration");
        };
        assert!(ident.same(&version));

        let StatementDesc::StringSwitch(test, clauses, Some(default_block)) = &switch_stmt.desc
        else {
            panic!("expected a direct string switch statement");
        };
        assert!(matches!(
            test,
            Expression {
                desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                ..
            } if id.same(&scrutinee)
        ));

        let expected_cases = [("linux", 1_i32), ("darwin", 2_i32)];
        for (clause, (expected_tag, expected_value)) in clauses.iter().zip(expected_cases) {
            assert_eq!(clause.tag_type, expected_tag);
            assert_switch_case_assigns_int_result(&clause.clause.body, &version, expected_value);
        }
        assert_switch_default_assigns_int_result(default_block, &version, 3);
    }

    #[test]
    fn staticcatch_wrapped_string_switches_use_the_handler_as_the_default_value() {
        let mut compiler = LambdaCompiler::new();
        let version = Ident::create_local("version");
        let scrutinee = Ident::create_local("platform");
        let program = compiler.compile_program(&Lambda::Llet(
            LetKind::Strict,
            version.clone(),
            Box::new(Lambda::LstaticCatch(
                Box::new(Lambda::LstringSwitch(
                    Box::new(Lambda::var(scrutinee.clone())),
                    vec![
                        ("linux".to_string(), Lambda::const_(Constant::int(1))),
                        ("darwin".to_string(), Lambda::const_(Constant::int(2))),
                    ],
                    Some(Box::new(Lambda::static_raise(1, Vec::new()))),
                )),
                (1, vec![]),
                Box::new(Lambda::const_(Constant::int(3))),
            )),
            Box::new(Lambda::var(version.clone())),
        ));

        let [declare, switch_stmt] = program.block.as_slice() else {
            panic!("expected a declaration followed by a string switch");
        };
        let StatementDesc::Variable(VariableDeclaration {
            ident, value: None, ..
        }) = &declare.desc
        else {
            panic!("expected an uninitialized binding declaration");
        };
        assert!(ident.same(&version));

        let StatementDesc::StringSwitch(_, clauses, Some(default_block)) = &switch_stmt.desc else {
            panic!("expected a direct string switch statement");
        };
        let expected_cases = [("linux", 1_i32), ("darwin", 2_i32)];
        for (clause, (expected_tag, expected_value)) in clauses.iter().zip(expected_cases) {
            assert_eq!(clause.tag_type, expected_tag);
            assert_switch_case_assigns_int_result(&clause.clause.body, &version, expected_value);
        }
        assert_switch_default_assigns_int_result(default_block, &version, 3);
    }

    #[test]
    fn nested_let_values_preserve_declaration_context_for_wrapped_string_switches() {
        let mut compiler = LambdaCompiler::new();
        let version = Ident::create_local("version");
        let match_id = Ident::create_local("match");
        let scrutinee = Ident::create_local("platform");
        let program = compiler.compile_program(&Lambda::Llet(
            LetKind::Strict,
            version.clone(),
            Box::new(Lambda::let_(
                LetKind::Strict,
                match_id.clone(),
                Lambda::var(scrutinee.clone()),
                Lambda::LstaticCatch(
                    Box::new(Lambda::LstringSwitch(
                        Box::new(Lambda::var(match_id.clone())),
                        vec![
                            ("linux".to_string(), Lambda::const_(Constant::int(1))),
                            ("darwin".to_string(), Lambda::const_(Constant::int(2))),
                        ],
                        Some(Box::new(Lambda::static_raise(1, Vec::new()))),
                    )),
                    (1, vec![]),
                    Box::new(Lambda::const_(Constant::int(3))),
                ),
            )),
            Box::new(Lambda::var(version.clone())),
        ));

        let [version_decl, switch_stmt] = program.block.as_slice() else {
            panic!(
                "expected simplification to inline the nested binding into a declaration and switch"
            );
        };

        let StatementDesc::Variable(VariableDeclaration {
            ident, value: None, ..
        }) = &version_decl.desc
        else {
            panic!("expected an uninitialized declaration for the outer binding");
        };
        assert!(ident.same(&version));

        let StatementDesc::StringSwitch(test, clauses, Some(default_block)) = &switch_stmt.desc
        else {
            panic!("expected the outer declaration context to reach the string switch");
        };
        assert!(matches!(
            test,
            Expression {
                desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                ..
            } if id.same(&scrutinee)
        ));

        let expected_cases = [("linux", 1_i32), ("darwin", 2_i32)];
        for (clause, (expected_tag, expected_value)) in clauses.iter().zip(expected_cases) {
            assert_eq!(clause.tag_type, expected_tag);
            assert_switch_case_assigns_int_result(&clause.clause.body, &version, expected_value);
        }
        assert_switch_default_assigns_int_result(default_block, &version, 3);
    }

    #[test]
    fn function_return_blocks_lower_switches_without_a_result_temp() {
        let mut compiler = LambdaCompiler::new();
        let scrutinee = Ident::create_local("scrutinee");
        let compiled = compiler.compile_expr(&Lambda::Lfunction(crate::lambda::LFunction {
            arity: 1,
            params: vec![scrutinee.clone()],
            body: Box::new(Lambda::Lswitch(
                Box::new(Lambda::var(scrutinee.clone())),
                LambdaSwitch {
                    sw_consts_full: true,
                    sw_consts: vec![
                        (0, Lambda::const_(Constant::int(1))),
                        (1, Lambda::const_(Constant::int(2))),
                    ],
                    sw_blocks_full: false,
                    sw_blocks: vec![],
                    sw_failaction: Some(Box::new(Lambda::const_(Constant::int(3)))),
                    sw_names: None,
                },
            )),
            attr: crate::lambda::FunctionAttribute::default(),
        }));

        let Expression {
            desc: ExpressionDesc::Fun { body, .. },
            ..
        } = compiled.expr
        else {
            panic!("expected a function expression");
        };

        let [switch_stmt] = body.as_slice() else {
            panic!("expected a single switch statement in the function body");
        };
        let StatementDesc::IntSwitch(test, clauses, Some(default_block)) = &switch_stmt.desc else {
            panic!("expected a direct integer switch in the function body");
        };
        assert!(matches!(
            test,
            Expression {
                desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                ..
            } if id.same(&scrutinee)
        ));

        let expected_cases = [(0, 1_i32), (1, 2_i32)];
        for ((tag, clause), (expected_tag, expected_value)) in clauses.iter().zip(expected_cases) {
            assert_eq!(*tag, expected_tag);
            assert_switch_case_returns_int_result(&clause.body, expected_value);
        }
        assert_switch_default_returns_int_result(default_block, 3);
    }

    fn assert_switch_case_assigns_int_result(block: &Block, result: &Ident, expected: i32) {
        let [assign, break_stmt] = block.as_slice() else {
            panic!("expected an assignment followed by break");
        };
        match &assign.desc {
            StatementDesc::Exp(Expression {
                desc: ExpressionDesc::Bin(BinOp::Eq, left, right),
                ..
            }) => {
                assert!(matches!(
                    left.as_ref(),
                    Expression {
                        desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                        ..
                    } if id.same(result)
                ));
                assert!(matches!(
                    right.as_ref(),
                    Expression {
                        desc: ExpressionDesc::Number(Number::Int { i, .. }),
                        ..
                    } if *i == expected
                ));
            }
            other => panic!("expected a result assignment, got {other:?}"),
        }
        assert!(matches!(break_stmt.desc, StatementDesc::Break));
    }

    fn assert_switch_default_assigns_int_result(block: &Block, result: &Ident, expected: i32) {
        let [assign] = block.as_slice() else {
            panic!("expected a single default assignment");
        };
        match &assign.desc {
            StatementDesc::Exp(Expression {
                desc: ExpressionDesc::Bin(BinOp::Eq, left, right),
                ..
            }) => {
                assert!(matches!(
                    left.as_ref(),
                    Expression {
                        desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                        ..
                    } if id.same(result)
                ));
                assert!(matches!(
                    right.as_ref(),
                    Expression {
                        desc: ExpressionDesc::Number(Number::Int { i, .. }),
                        ..
                    } if *i == expected
                ));
            }
            other => panic!("expected a default assignment, got {other:?}"),
        }
    }

    fn assert_switch_case_returns_int_result(block: &Block, expected: i32) {
        let [ret] = block.as_slice() else {
            panic!("expected a single return statement");
        };
        match &ret.desc {
            StatementDesc::Return(Expression {
                desc: ExpressionDesc::Number(Number::Int { i, .. }),
                ..
            }) if *i == expected => {}
            other => panic!("expected a return of {expected}, got {other:?}"),
        }
    }

    fn assert_switch_default_returns_int_result(block: &Block, expected: i32) {
        assert_switch_case_returns_int_result(block, expected);
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
    fn js_flatten_and_mark_dead_rewrites_pre_marked_dead_bindings() {
        let dead_pure = Ident::create_local("deadPure");
        let dead_non_pure = Ident::create_local("deadNonPure");
        let callback = Ident::create_local("callback");
        let deps = apply_js_flatten_and_mark_dead_pass(DepsProgram {
            program: Program::new(
                vec![
                    Statement::variable(VariableDeclaration {
                        ident: dead_pure,
                        value: Some(Expression::number(Number::int(1))),
                        property: LetKind::Strict,
                        ident_info: IdentInfo {
                            used_stats: UsedStats::DeadPure,
                        },
                    }),
                    Statement::variable(VariableDeclaration {
                        ident: dead_non_pure,
                        value: Some(Expression::call(
                            Expression::var(callback.clone()),
                            vec![],
                            CallInfo::default(),
                        )),
                        property: LetKind::Strict,
                        ident_info: IdentInfo {
                            used_stats: UsedStats::DeadNonPure,
                        },
                    }),
                ],
                vec![],
            ),
            modules: vec![],
            side_effect: None,
        });

        let [first, second] = deps.program.block.as_slice() else {
            panic!("expected two rewritten statements");
        };
        match &first.desc {
            StatementDesc::Block(block) => assert!(block.is_empty()),
            other => {
                panic!("expected the dead pure binding to become an empty block, got {other:?}")
            }
        }
        match &second.desc {
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
            other => panic!(
                "expected the dead impure binding to become an effect statement, got {other:?}"
            ),
        }
    }

    #[test]
    fn js_flatten_and_mark_dead_substitutes_immutable_caml_block_index_reads() {
        let tuple = Ident::create_local("tuple");
        let field = Ident::create_local("field");
        let callback = Ident::create_local("callback");
        let deps = apply_js_flatten_and_mark_dead_pass(DepsProgram {
            program: Program::new(
                vec![
                    Statement::variable(VariableDeclaration {
                        ident: tuple.clone(),
                        value: Some(Expression::new(ExpressionDesc::CamlBlock(
                            vec![
                                Expression::call(
                                    Expression::var(callback.clone()),
                                    vec![],
                                    CallInfo::default(),
                                ),
                                Expression::number(Number::int(2)),
                            ],
                            MutableFlag::Immutable,
                            Box::new(Expression::number(Number::int(0))),
                            TagInfo::tuple(),
                        ))),
                        property: LetKind::Strict,
                        ident_info: IdentInfo::default(),
                    }),
                    Statement::variable(VariableDeclaration {
                        ident: field,
                        value: Some(Expression::new(ExpressionDesc::ArrayIndex(
                            Box::new(Expression::var(tuple.clone())),
                            Box::new(Expression::number(Number::int(1))),
                        ))),
                        property: LetKind::Strict,
                        ident_info: IdentInfo::default(),
                    }),
                ],
                vec![],
            ),
            modules: vec![],
            side_effect: None,
        });

        let [tuple_stmt, field_stmt] = deps.program.block.as_slice() else {
            panic!("expected the tuple binding and the rewritten projection");
        };

        let StatementDesc::Block(bindings) = &tuple_stmt.desc else {
            panic!("expected the tuple binding to expand into helper bindings");
        };
        let [helper_stmt, original_stmt] = bindings.as_slice() else {
            panic!("expected one helper binding plus the original tuple binding");
        };

        match &helper_stmt.desc {
            StatementDesc::Variable(VariableDeclaration {
                value:
                    Some(Expression {
                        desc: ExpressionDesc::Call(func, args, _),
                        ..
                    }),
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
                panic!("expected the complex tuple field to become a helper binding, got {other:?}")
            }
        }
        match &original_stmt.desc {
            StatementDesc::Variable(VariableDeclaration {
                ident,
                value:
                    Some(Expression {
                        desc: ExpressionDesc::CamlBlock(items, MutableFlag::Immutable, _, _),
                        ..
                    }),
                ..
            }) => {
                assert!(ident.same(&tuple));
                assert!(matches!(
                    items.as_slice(),
                    [
                        Expression {
                            desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(_)),
                            ..
                        },
                        Expression {
                            desc: ExpressionDesc::Number(Number::Int { i: 2, .. }),
                            ..
                        }
                    ]
                ));
            }
            other => panic!(
                "expected the original tuple binding to remain as a rewritten Caml block, got {other:?}"
            ),
        }
        match &field_stmt.desc {
            StatementDesc::Variable(VariableDeclaration {
                value:
                    Some(Expression {
                        desc: ExpressionDesc::Number(Number::Int { i: 2, .. }),
                        ..
                    }),
                ..
            }) => {}
            other => panic!(
                "expected the tuple projection to inline to the selected field, got {other:?}"
            ),
        }
    }

    #[test]
    fn js_flatten_and_mark_dead_marks_unused_nested_pure_bindings() {
        let run = Ident::create_local("run");
        let unused = Ident::create_local("unused");
        let used = Ident::create_local("used");
        let deps = apply_js_flatten_and_mark_dead_pass(DepsProgram {
            program: Program::new(
                vec![Statement::variable(VariableDeclaration {
                    ident: run,
                    value: Some(Expression::new(ExpressionDesc::Fun {
                        is_method: false,
                        params: vec![],
                        body: vec![
                            Statement::variable(VariableDeclaration {
                                ident: unused.clone(),
                                value: Some(Expression::number(Number::int(1))),
                                property: LetKind::Strict,
                                ident_info: IdentInfo::default(),
                            }),
                            Statement::variable(VariableDeclaration {
                                ident: used.clone(),
                                value: Some(Expression::number(Number::int(2))),
                                property: LetKind::Strict,
                                ident_info: IdentInfo::default(),
                            }),
                            Statement::return_(Expression::var(used.clone())),
                        ],
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
            panic!("expected one top-level function binding");
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
            panic!("expected a function-valued binding");
        };
        let [unused_stmt, used_stmt, _] = body.as_slice() else {
            panic!("expected two nested bindings followed by a return");
        };
        match &unused_stmt.desc {
            StatementDesc::Variable(VariableDeclaration { ident_info, .. }) => {
                assert_eq!(ident_info.used_stats, UsedStats::DeadPure);
            }
            other => panic!(
                "expected the first nested binding to remain a variable declaration, got {other:?}"
            ),
        }
        match &used_stmt.desc {
            StatementDesc::Variable(VariableDeclaration { ident_info, .. }) => {
                assert_eq!(ident_info.used_stats, UsedStats::Used);
            }
            other => panic!(
                "expected the used nested binding to remain a variable declaration, got {other:?}"
            ),
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

        let compiled = compiler.compile_expr(&lam);
        assert!(compiled.prelude.is_empty());
        assert!(matches!(
            compiled.expr,
            Expression {
                desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(ref id)),
                ..
            } if id.name() == "process"
        ));
    }

    #[test]
    fn lowers_js_var_calls_with_runtime_args_even_without_external_arg_metadata() {
        let mut compiler = LambdaCompiler::new();
        let lam = Lambda::prim(
            Primitive::PjsCall {
                prim_name: "foo1".to_string(),
                arg_types: vec![],
                ffi: ExternalFfiSpec {
                    kind: ExternalFfiKind::Default,
                    spec: Some(ExternalSpec::JsVar {
                        name: "foo1".to_string(),
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
            vec![Lambda::Lconst(Constant::Int {
                i: 10,
                comment: None,
            })],
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
                assert_eq!(args.len(), 1);
                assert!(matches!(
                    func.as_ref(),
                    Expression {
                        desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                        ..
                    } if id.name() == "foo1"
                ));
                assert!(matches!(
                    args[0],
                    Expression {
                        desc: ExpressionDesc::Number(Number::Int { i: 10, .. }),
                        ..
                    }
                ));
            }
            other => panic!("expected a direct js-var call, got {other:?}"),
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
    fn required_module_effect_reason_uses_external_module_name() {
        let reason = required_module_side_effect_reason(
            None,
            &[ModuleId {
                id: Ident::create_persistent("GentTypeReTestGen"),
                kind: Kind::External {
                    name: "./gentTypeReTest.gen".to_string(),
                    default: false,
                    import_attributes: None,
                },
                dynamic_import: false,
            }],
        );

        assert_eq!(reason.as_deref(), Some("./gentTypeReTest.gen"));
    }

    #[test]
    fn pure_ml_dependencies_do_not_mark_module_impure() {
        let resolver = resolver_with_checked_in_cmj();
        let reason = required_module_side_effect_reason(
            Some(&resolver),
            &[ModuleId {
                id: Ident::create_persistent("Side_effect_free"),
                kind: Kind::Ml,
                dynamic_import: false,
            }],
        );

        assert_eq!(reason, None);
    }

    #[test]
    fn impure_ml_dependencies_use_module_name_as_effect_reason() {
        let resolver = resolver_with_checked_in_cmj();
        let reason = required_module_side_effect_reason(
            Some(&resolver),
            &[ModuleId {
                id: Ident::create_persistent("Test_utils"),
                kind: Kind::Ml,
                dynamic_import: false,
            }],
        );

        assert_eq!(reason.as_deref(), Some("Test_utils"));
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

    #[test]
    fn js_shake_pass_removes_unused_pure_toplevel_bindings_and_statements() {
        let exported = Ident::create_local("exported");
        let unused = Ident::create_local("unused");
        let deps = apply_js_shake_pass(DepsProgram {
            program: Program::new(
                vec![
                    Statement::exp(Expression::undefined(false)),
                    Statement::variable(VariableDeclaration {
                        ident: unused,
                        value: Some(Expression::number(Number::int(1))),
                        property: LetKind::Strict,
                        ident_info: IdentInfo::default(),
                    }),
                    Statement::variable(VariableDeclaration {
                        ident: exported.clone(),
                        value: Some(Expression::number(Number::int(2))),
                        property: LetKind::Strict,
                        ident_info: IdentInfo::default(),
                    }),
                ],
                vec![exported.clone()],
            ),
            modules: vec![],
            side_effect: None,
        });

        let [stmt] = deps.program.block.as_slice() else {
            panic!("expected only the exported binding to remain");
        };

        match &stmt.desc {
            StatementDesc::Variable(VariableDeclaration {
                ident,
                value:
                    Some(Expression {
                        desc: ExpressionDesc::Number(Number::Int { i: 2, .. }),
                        ..
                    }),
                ..
            }) => assert!(ident.same(&exported)),
            other => panic!("expected exported number binding, got {other:?}"),
        }
    }

    #[test]
    fn js_shake_pass_keeps_export_dependencies_and_impure_bindings() {
        let dep = Ident::create_local("dep");
        let exported = Ident::create_local("exported");
        let callback = Ident::create_local("callback");
        let side = Ident::create_local("side");
        let deps = apply_js_shake_pass(DepsProgram {
            program: Program::new(
                vec![
                    Statement::variable(VariableDeclaration {
                        ident: dep.clone(),
                        value: Some(Expression::number(Number::int(1))),
                        property: LetKind::Strict,
                        ident_info: IdentInfo::default(),
                    }),
                    Statement::variable(VariableDeclaration {
                        ident: exported.clone(),
                        value: Some(Expression::var(dep.clone())),
                        property: LetKind::Strict,
                        ident_info: IdentInfo::default(),
                    }),
                    Statement::variable(VariableDeclaration {
                        ident: side.clone(),
                        value: Some(Expression::call(
                            Expression::var(callback.clone()),
                            vec![],
                            CallInfo::default(),
                        )),
                        property: LetKind::Strict,
                        ident_info: IdentInfo::default(),
                    }),
                ],
                vec![exported.clone()],
            ),
            modules: vec![],
            side_effect: None,
        });

        let [dep_stmt, exported_stmt, side_stmt] = deps.program.block.as_slice() else {
            panic!("expected the dependency chain and impure binding to remain");
        };

        match &dep_stmt.desc {
            StatementDesc::Variable(VariableDeclaration { ident, .. }) => {
                assert!(ident.same(&dep));
            }
            other => panic!("expected the dependency binding to remain, got {other:?}"),
        }
        match &exported_stmt.desc {
            StatementDesc::Variable(VariableDeclaration { ident, .. }) => {
                assert!(ident.same(&exported));
            }
            other => panic!("expected the exported binding to remain, got {other:?}"),
        }
        match &side_stmt.desc {
            StatementDesc::Variable(VariableDeclaration {
                ident,
                value:
                    Some(Expression {
                        desc: ExpressionDesc::Call(func, args, _),
                        ..
                    }),
                ..
            }) => {
                assert!(ident.same(&side));
                assert!(args.is_empty());
                assert!(matches!(
                    func.as_ref(),
                    Expression {
                        desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                        ..
                    } if id.same(&callback)
                ));
            }
            other => panic!("expected the impure binding to remain, got {other:?}"),
        }
    }
}
