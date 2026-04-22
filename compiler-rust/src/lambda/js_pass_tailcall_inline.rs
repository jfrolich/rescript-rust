//! JS IR pass: tailcall inlining.
//!
//! Inlines single-use pure function bindings at their return-position call
//! sites, eliminating the intermediate function wrapper. Also tracks used/dead
//! status for variable declarations.

use std::collections::HashMap;

use crate::ident::Ident;
use crate::js_ir::op::{IdentInfo, UsedStats};
use crate::js_ir::{
    BinOp, Block, CaseClause, DepsProgram, Expression, ExpressionDesc, Program, Statement,
    StatementDesc, StringClause, VariableDeclaration,
};
use crate::lambda::compat::LetKind;
use crate::lambda::js_pass_external_shadow::is_lexical_binding_kind;

use super::compile::js_expr_no_side_effects;

pub(crate) fn apply_js_tailcall_inline_pass(mut deps: DepsProgram) -> DepsProgram {
    deps.program = tailcall_inline_program(deps.program);
    deps
}

fn tailcall_inline_program(program: Program) -> Program {
    let mut inliner = TailcallInlineState::new(&program);
    let mut program = Program {
        block: inliner.transform_block(program.block),
        exports: program.exports,
        export_set: program.export_set,
    };
    apply_tailcall_used_stats_block(&mut program.block, &inliner.statuses);
    program
}

#[derive(Debug, Clone)]
struct TailcallInlineState {
    decls: HashMap<Ident, VariableDeclaration>,
    statuses: HashMap<Ident, UsedStats>,
}

impl TailcallInlineState {
    fn new(program: &Program) -> Self {
        let mut decls = HashMap::new();
        let mut counts = HashMap::new();
        collect_tailcall_use_counts_block(&program.block, &mut decls, &mut counts);

        let mut statuses = HashMap::with_capacity(decls.len());
        for (ident, decl) in &decls {
            let count = counts.get(ident).copied().unwrap_or(0);
            let exported = program.export_set.contains(ident);
            let pure = decl.value.as_ref().is_some_and(js_expr_no_side_effects);
            let status = if exported {
                UsedStats::Exported
            } else if count == 0 {
                if pure {
                    UsedStats::DeadPure
                } else {
                    UsedStats::DeadNonPure
                }
            } else if count == 1 && pure {
                UsedStats::OncePure
            } else {
                UsedStats::Used
            };
            statuses.insert(ident.clone(), status);
        }

        Self { decls, statuses }
    }

    fn transform_block(&mut self, block: Block) -> Block {
        if block.len() == 1 {
            if let Some(inlined) = self.try_inline_single_return_block(&block[0]) {
                return inlined;
            }
        }

        let mut iter = block.into_iter();
        let Some(first) = iter.next() else {
            return Vec::new();
        };
        let rest: Block = iter.collect();

        let mut transformed = self.transform_statement(first);
        transformed.extend(self.transform_block(rest));
        transformed
    }

    fn transform_statement(&mut self, stmt: Statement) -> Vec<Statement> {
        let Statement { desc, comment } = stmt;
        match desc {
            StatementDesc::Block(block) => vec![Statement {
                desc: StatementDesc::Block(self.transform_block(block)),
                comment,
            }],
            StatementDesc::Variable(mut decl) => {
                if let Some(value) = decl.value.take() {
                    decl.value = Some(self.transform_expression(value));
                }

                let status = self
                    .statuses
                    .get(&decl.ident)
                    .copied()
                    .unwrap_or(UsedStats::Used);
                decl.ident_info.used_stats = status;
                self.decls.insert(decl.ident.clone(), decl.clone());

                match status {
                    UsedStats::DeadPure => vec![],
                    UsedStats::DeadNonPure => decl
                        .value
                        .map(|value| {
                            vec![Statement {
                                desc: StatementDesc::Exp(value),
                                comment,
                            }]
                        })
                        .unwrap_or_default(),
                    _ => vec![Statement {
                        desc: StatementDesc::Variable(decl),
                        comment,
                    }],
                }
            }
            StatementDesc::Exp(expr) => vec![Statement {
                desc: StatementDesc::Exp(self.transform_expression(expr)),
                comment,
            }],
            StatementDesc::If(cond, then_block, else_block) => vec![Statement {
                desc: StatementDesc::If(
                    self.transform_expression(cond),
                    self.transform_block(then_block),
                    self.transform_block(else_block),
                ),
                comment,
            }],
            StatementDesc::While(cond, body) => vec![Statement {
                desc: StatementDesc::While(
                    self.transform_expression(cond),
                    self.transform_block(body),
                ),
                comment,
            }],
            StatementDesc::ForRange(start, finish, ident, direction, body) => vec![Statement {
                desc: StatementDesc::ForRange(
                    start.map(|expr| self.transform_expression(expr)),
                    self.transform_expression(finish),
                    ident,
                    direction,
                    self.transform_block(body),
                ),
                comment,
            }],
            StatementDesc::Continue => vec![Statement {
                desc: StatementDesc::Continue,
                comment,
            }],
            StatementDesc::Break => vec![Statement {
                desc: StatementDesc::Break,
                comment,
            }],
            StatementDesc::Return(expr) => vec![Statement {
                desc: StatementDesc::Return(self.transform_expression(expr)),
                comment,
            }],
            StatementDesc::IntSwitch(test, clauses, default) => vec![Statement {
                desc: StatementDesc::IntSwitch(
                    self.transform_expression(test),
                    clauses
                        .into_iter()
                        .map(|(value, clause)| {
                            (
                                value,
                                CaseClause {
                                    body: self.transform_block(clause.body),
                                    should_break: clause.should_break,
                                    comment: clause.comment,
                                },
                            )
                        })
                        .collect(),
                    default.map(|block| self.transform_block(block)),
                ),
                comment,
            }],
            StatementDesc::StringSwitch(test, clauses, default) => vec![Statement {
                desc: StatementDesc::StringSwitch(
                    self.transform_expression(test),
                    clauses
                        .into_iter()
                        .map(|clause| StringClause {
                            tag_type: clause.tag_type,
                            clause: CaseClause {
                                body: self.transform_block(clause.clause.body),
                                should_break: clause.clause.should_break,
                                comment: clause.clause.comment,
                            },
                        })
                        .collect(),
                    default.map(|block| self.transform_block(block)),
                ),
                comment,
            }],
            StatementDesc::Throw(expr) => vec![Statement {
                desc: StatementDesc::Throw(self.transform_expression(expr)),
                comment,
            }],
            StatementDesc::Try(body, catch, finally) => vec![Statement {
                desc: StatementDesc::Try(
                    self.transform_block(body),
                    catch.map(|(ident, block)| (ident, self.transform_block(block))),
                    finally.map(|block| self.transform_block(block)),
                ),
                comment,
            }],
            StatementDesc::Debugger => vec![Statement {
                desc: StatementDesc::Debugger,
                comment,
            }],
        }
    }

    fn transform_expression(&mut self, expr: Expression) -> Expression {
        let Expression { desc, comment } = expr;
        let desc = match desc {
            ExpressionDesc::Length(inner, obj) => {
                ExpressionDesc::Length(Box::new(self.transform_expression(*inner)), obj)
            }
            ExpressionDesc::IsNullOrUndefined(inner) => {
                ExpressionDesc::IsNullOrUndefined(Box::new(self.transform_expression(*inner)))
            }
            ExpressionDesc::StringAppend(left, right) => ExpressionDesc::StringAppend(
                Box::new(self.transform_expression(*left)),
                Box::new(self.transform_expression(*right)),
            ),
            ExpressionDesc::Bool(value) => ExpressionDesc::Bool(value),
            ExpressionDesc::Typeof(inner) => {
                ExpressionDesc::Typeof(Box::new(self.transform_expression(*inner)))
            }
            ExpressionDesc::In(left, right) => ExpressionDesc::In(
                Box::new(self.transform_expression(*left)),
                Box::new(self.transform_expression(*right)),
            ),
            ExpressionDesc::JsNot(inner) => {
                ExpressionDesc::JsNot(Box::new(self.transform_expression(*inner)))
            }
            ExpressionDesc::JsBnot(inner) => {
                ExpressionDesc::JsBnot(Box::new(self.transform_expression(*inner)))
            }
            ExpressionDesc::Seq(left, right) => ExpressionDesc::Seq(
                Box::new(self.transform_expression(*left)),
                Box::new(self.transform_expression(*right)),
            ),
            ExpressionDesc::Cond(test, consequent, alternate) => ExpressionDesc::Cond(
                Box::new(self.transform_expression(*test)),
                Box::new(self.transform_expression(*consequent)),
                Box::new(self.transform_expression(*alternate)),
            ),
            ExpressionDesc::Bin(op, left, right) => ExpressionDesc::Bin(
                op,
                Box::new(self.transform_expression(*left)),
                Box::new(self.transform_expression(*right)),
            ),
            ExpressionDesc::FlatCall(func, args) => ExpressionDesc::FlatCall(
                Box::new(self.transform_expression(*func)),
                Box::new(self.transform_expression(*args)),
            ),
            ExpressionDesc::Call(func, args, info) => ExpressionDesc::Call(
                Box::new(self.transform_expression(*func)),
                args.into_iter()
                    .map(|arg| self.transform_expression(arg))
                    .collect(),
                info,
            ),
            ExpressionDesc::StringIndex(left, right) => ExpressionDesc::StringIndex(
                Box::new(self.transform_expression(*left)),
                Box::new(self.transform_expression(*right)),
            ),
            ExpressionDesc::ArrayIndex(left, right) => ExpressionDesc::ArrayIndex(
                Box::new(self.transform_expression(*left)),
                Box::new(self.transform_expression(*right)),
            ),
            ExpressionDesc::TaggedTemplate(tag, strings, values) => ExpressionDesc::TaggedTemplate(
                Box::new(self.transform_expression(*tag)),
                strings
                    .into_iter()
                    .map(|expr| self.transform_expression(expr))
                    .collect(),
                values
                    .into_iter()
                    .map(|expr| self.transform_expression(expr))
                    .collect(),
            ),
            ExpressionDesc::StaticIndex(target, field, position) => ExpressionDesc::StaticIndex(
                Box::new(self.transform_expression(*target)),
                field,
                position,
            ),
            ExpressionDesc::New(target, args) => ExpressionDesc::New(
                Box::new(self.transform_expression(*target)),
                args.map(|args| {
                    args.into_iter()
                        .map(|arg| self.transform_expression(arg))
                        .collect()
                }),
            ),
            ExpressionDesc::Var(ident) => ExpressionDesc::Var(ident),
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
                body: self.transform_block(body),
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
                    .map(|item| self.transform_expression(item))
                    .collect(),
                mutable_flag,
            ),
            ExpressionDesc::OptionalBlock(inner, flag) => {
                ExpressionDesc::OptionalBlock(Box::new(self.transform_expression(*inner)), flag)
            }
            ExpressionDesc::CamlBlock(items, mutable_flag, tag, info) => ExpressionDesc::CamlBlock(
                items
                    .into_iter()
                    .map(|item| self.transform_expression(item))
                    .collect(),
                mutable_flag,
                Box::new(self.transform_expression(*tag)),
                info,
            ),
            ExpressionDesc::CamlBlockTag(inner, field) => {
                ExpressionDesc::CamlBlockTag(Box::new(self.transform_expression(*inner)), field)
            }
            ExpressionDesc::Number(number) => ExpressionDesc::Number(number),
            ExpressionDesc::Object(dup, props) => ExpressionDesc::Object(
                dup.map(|expr| Box::new(self.transform_expression(*expr))),
                props
                    .into_iter()
                    .map(|(name, value)| (name, self.transform_expression(value)))
                    .collect(),
            ),
            ExpressionDesc::Undefined { is_unit } => ExpressionDesc::Undefined { is_unit },
            ExpressionDesc::Null => ExpressionDesc::Null,
            ExpressionDesc::Await(inner) => {
                ExpressionDesc::Await(Box::new(self.transform_expression(*inner)))
            }
            ExpressionDesc::Spread(inner) => {
                ExpressionDesc::Spread(Box::new(self.transform_expression(*inner)))
            }
        };

        Expression { desc, comment }
    }

    fn try_inline_single_return_block(&mut self, stmt: &Statement) -> Option<Block> {
        let StatementDesc::Return(expr) = &stmt.desc else {
            return None;
        };
        let ExpressionDesc::Call(func, args, _) = &expr.desc else {
            return None;
        };

        match &func.desc {
            ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)) => self.inline_named_call(id, args),
            ExpressionDesc::Fun {
                is_method: false,
                params,
                body,
                async_: false,
                directive: None,
                ..
            } if params.len() == args.len() => Some(self.inline_function_call(params, body, args)),
            _ => None,
        }
    }

    fn inline_named_call(&mut self, ident: &Ident, args: &[Expression]) -> Option<Block> {
        if self.statuses.get(ident).copied() != Some(UsedStats::OncePure) {
            return None;
        }

        let decl = self.decls.get(ident)?.clone();
        if !is_lexical_binding_kind(decl.property) {
            return None;
        }

        let Some(Expression {
            desc:
                ExpressionDesc::Fun {
                    is_method: false,
                    params,
                    body,
                    async_: false,
                    directive: None,
                    ..
                },
            ..
        }) = decl.value
        else {
            return None;
        };

        if params.len() != args.len() {
            return None;
        }

        self.statuses.insert(ident.clone(), UsedStats::DeadPure);
        Some(self.inline_function_call(&params, &body, args))
    }

    fn inline_function_call(
        &mut self,
        params: &[Ident],
        body: &Block,
        args: &[Expression],
    ) -> Block {
        let processed_body = self.transform_block(body.clone());
        let immutable_mask = immutable_param_mask(params, &processed_body);
        let args = args
            .iter()
            .cloned()
            .map(|arg| self.transform_expression(arg))
            .collect();
        inline_tailcall_call(&immutable_mask, params, args, processed_body)
    }
}

fn collect_tailcall_use_counts_block(
    block: &Block,
    decls: &mut HashMap<Ident, VariableDeclaration>,
    counts: &mut HashMap<Ident, usize>,
) {
    for stmt in block {
        collect_tailcall_use_counts_statement(stmt, decls, counts);
    }
}

fn collect_tailcall_use_counts_statement(
    stmt: &Statement,
    decls: &mut HashMap<Ident, VariableDeclaration>,
    counts: &mut HashMap<Ident, usize>,
) {
    match &stmt.desc {
        StatementDesc::Block(block) => collect_tailcall_use_counts_block(block, decls, counts),
        StatementDesc::Variable(decl) => {
            decls.insert(decl.ident.clone(), decl.clone());
            if let Some(value) = &decl.value {
                collect_tailcall_use_counts_expression(value, decls, counts);
            }
        }
        StatementDesc::Exp(expr) | StatementDesc::Return(expr) | StatementDesc::Throw(expr) => {
            collect_tailcall_use_counts_expression(expr, decls, counts);
        }
        StatementDesc::If(cond, then_block, else_block) => {
            collect_tailcall_use_counts_expression(cond, decls, counts);
            collect_tailcall_use_counts_block(then_block, decls, counts);
            collect_tailcall_use_counts_block(else_block, decls, counts);
        }
        StatementDesc::While(cond, body) => {
            collect_tailcall_use_counts_expression(cond, decls, counts);
            collect_tailcall_use_counts_block(body, decls, counts);
        }
        StatementDesc::ForRange(start, finish, _, _, body) => {
            if let Some(start) = start {
                collect_tailcall_use_counts_expression(start, decls, counts);
            }
            collect_tailcall_use_counts_expression(finish, decls, counts);
            collect_tailcall_use_counts_block(body, decls, counts);
        }
        StatementDesc::IntSwitch(test, clauses, default) => {
            collect_tailcall_use_counts_expression(test, decls, counts);
            for (_, clause) in clauses {
                collect_tailcall_use_counts_block(&clause.body, decls, counts);
            }
            if let Some(default) = default {
                collect_tailcall_use_counts_block(default, decls, counts);
            }
        }
        StatementDesc::StringSwitch(test, clauses, default) => {
            collect_tailcall_use_counts_expression(test, decls, counts);
            for clause in clauses {
                collect_tailcall_use_counts_block(&clause.clause.body, decls, counts);
            }
            if let Some(default) = default {
                collect_tailcall_use_counts_block(default, decls, counts);
            }
        }
        StatementDesc::Try(body, catch, finally) => {
            collect_tailcall_use_counts_block(body, decls, counts);
            if let Some((_, block)) = catch {
                collect_tailcall_use_counts_block(block, decls, counts);
            }
            if let Some(block) = finally {
                collect_tailcall_use_counts_block(block, decls, counts);
            }
        }
        StatementDesc::Debugger | StatementDesc::Break | StatementDesc::Continue => {}
    }
}

fn collect_tailcall_use_counts_expression(
    expr: &Expression,
    decls: &mut HashMap<Ident, VariableDeclaration>,
    counts: &mut HashMap<Ident, usize>,
) {
    match &expr.desc {
        ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)) => {
            *counts.entry(id.clone()).or_insert(0) += 1;
        }
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
        | ExpressionDesc::Spread(inner) => {
            collect_tailcall_use_counts_expression(inner, decls, counts)
        }
        ExpressionDesc::StringAppend(left, right)
        | ExpressionDesc::In(left, right)
        | ExpressionDesc::Seq(left, right)
        | ExpressionDesc::Bin(_, left, right)
        | ExpressionDesc::FlatCall(left, right)
        | ExpressionDesc::StringIndex(left, right)
        | ExpressionDesc::ArrayIndex(left, right) => {
            collect_tailcall_use_counts_expression(left, decls, counts);
            collect_tailcall_use_counts_expression(right, decls, counts);
        }
        ExpressionDesc::Cond(test, consequent, alternate) => {
            collect_tailcall_use_counts_expression(test, decls, counts);
            collect_tailcall_use_counts_expression(consequent, decls, counts);
            collect_tailcall_use_counts_expression(alternate, decls, counts);
        }
        ExpressionDesc::Call(func, args, _) => {
            collect_tailcall_use_counts_expression(func, decls, counts);
            for arg in args {
                collect_tailcall_use_counts_expression(arg, decls, counts);
            }
        }
        ExpressionDesc::TaggedTemplate(tag, strings, values) => {
            collect_tailcall_use_counts_expression(tag, decls, counts);
            for string in strings {
                collect_tailcall_use_counts_expression(string, decls, counts);
            }
            for value in values {
                collect_tailcall_use_counts_expression(value, decls, counts);
            }
        }
        ExpressionDesc::StaticIndex(target, _, _) => {
            collect_tailcall_use_counts_expression(target, decls, counts)
        }
        ExpressionDesc::New(target, args) => {
            collect_tailcall_use_counts_expression(target, decls, counts);
            if let Some(args) = args {
                for arg in args {
                    collect_tailcall_use_counts_expression(arg, decls, counts);
                }
            }
        }
        ExpressionDesc::Fun { body, .. } => collect_tailcall_use_counts_block(body, decls, counts),
        ExpressionDesc::Array(items, _) => {
            for item in items {
                collect_tailcall_use_counts_expression(item, decls, counts);
            }
        }
        ExpressionDesc::CamlBlock(items, _, tag, _) => {
            for item in items {
                collect_tailcall_use_counts_expression(item, decls, counts);
            }
            collect_tailcall_use_counts_expression(tag, decls, counts);
        }
        ExpressionDesc::Object(dup, props) => {
            if let Some(dup) = dup {
                collect_tailcall_use_counts_expression(dup, decls, counts);
            }
            for (_, value) in props {
                collect_tailcall_use_counts_expression(value, decls, counts);
            }
        }
    }
}

fn immutable_param_mask(params: &[Ident], body: &Block) -> Vec<bool> {
    params
        .iter()
        .map(|param| !block_assigns_ident(body, param))
        .collect()
}

fn block_assigns_ident(block: &Block, ident: &Ident) -> bool {
    block
        .iter()
        .any(|stmt| statement_assigns_ident(stmt, ident))
}

fn statement_assigns_ident(stmt: &Statement, ident: &Ident) -> bool {
    match &stmt.desc {
        StatementDesc::Block(block) => block_assigns_ident(block, ident),
        StatementDesc::Variable(decl) => decl
            .value
            .as_ref()
            .is_some_and(|value| expression_assigns_ident(value, ident)),
        StatementDesc::Exp(expr) | StatementDesc::Return(expr) | StatementDesc::Throw(expr) => {
            expression_assigns_ident(expr, ident)
        }
        StatementDesc::If(cond, then_block, else_block) => {
            expression_assigns_ident(cond, ident)
                || block_assigns_ident(then_block, ident)
                || block_assigns_ident(else_block, ident)
        }
        StatementDesc::While(cond, body) => {
            expression_assigns_ident(cond, ident) || block_assigns_ident(body, ident)
        }
        StatementDesc::ForRange(start, finish, _, _, body) => {
            start
                .as_ref()
                .is_some_and(|expr| expression_assigns_ident(expr, ident))
                || expression_assigns_ident(finish, ident)
                || block_assigns_ident(body, ident)
        }
        StatementDesc::IntSwitch(test, clauses, default) => {
            expression_assigns_ident(test, ident)
                || clauses
                    .iter()
                    .any(|(_, clause)| block_assigns_ident(&clause.body, ident))
                || default
                    .as_ref()
                    .is_some_and(|block| block_assigns_ident(block, ident))
        }
        StatementDesc::StringSwitch(test, clauses, default) => {
            expression_assigns_ident(test, ident)
                || clauses
                    .iter()
                    .any(|clause| block_assigns_ident(&clause.clause.body, ident))
                || default
                    .as_ref()
                    .is_some_and(|block| block_assigns_ident(block, ident))
        }
        StatementDesc::Try(body, catch, finally) => {
            block_assigns_ident(body, ident)
                || catch
                    .as_ref()
                    .is_some_and(|(_, block)| block_assigns_ident(block, ident))
                || finally
                    .as_ref()
                    .is_some_and(|block| block_assigns_ident(block, ident))
        }
        StatementDesc::Debugger | StatementDesc::Break | StatementDesc::Continue => false,
    }
}

fn expression_assigns_ident(expr: &Expression, ident: &Ident) -> bool {
    match &expr.desc {
        ExpressionDesc::Bin(BinOp::Eq, left, right) => {
            matches!(
                left.as_ref(),
                Expression {
                    desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(lhs)),
                    ..
                } if lhs.same(ident)
            ) || expression_assigns_ident(left, ident)
                || expression_assigns_ident(right, ident)
        }
        ExpressionDesc::Length(inner, _)
        | ExpressionDesc::IsNullOrUndefined(inner)
        | ExpressionDesc::Typeof(inner)
        | ExpressionDesc::JsNot(inner)
        | ExpressionDesc::JsBnot(inner)
        | ExpressionDesc::CamlBlockTag(inner, _)
        | ExpressionDesc::OptionalBlock(inner, _)
        | ExpressionDesc::Await(inner)
        | ExpressionDesc::Spread(inner) => expression_assigns_ident(inner, ident),
        ExpressionDesc::StringAppend(left, right)
        | ExpressionDesc::In(left, right)
        | ExpressionDesc::Seq(left, right)
        | ExpressionDesc::Bin(_, left, right)
        | ExpressionDesc::FlatCall(left, right)
        | ExpressionDesc::StringIndex(left, right)
        | ExpressionDesc::ArrayIndex(left, right) => {
            expression_assigns_ident(left, ident) || expression_assigns_ident(right, ident)
        }
        ExpressionDesc::Cond(test, consequent, alternate) => {
            expression_assigns_ident(test, ident)
                || expression_assigns_ident(consequent, ident)
                || expression_assigns_ident(alternate, ident)
        }
        ExpressionDesc::Call(func, args, _) => {
            expression_assigns_ident(func, ident)
                || args.iter().any(|arg| expression_assigns_ident(arg, ident))
        }
        ExpressionDesc::TaggedTemplate(tag, strings, values) => {
            expression_assigns_ident(tag, ident)
                || strings
                    .iter()
                    .any(|expr| expression_assigns_ident(expr, ident))
                || values
                    .iter()
                    .any(|expr| expression_assigns_ident(expr, ident))
        }
        ExpressionDesc::StaticIndex(target, _, _) => expression_assigns_ident(target, ident),
        ExpressionDesc::New(target, args) => {
            expression_assigns_ident(target, ident)
                || args
                    .as_ref()
                    .is_some_and(|args| args.iter().any(|arg| expression_assigns_ident(arg, ident)))
        }
        ExpressionDesc::Fun { body, .. } => block_assigns_ident(body, ident),
        ExpressionDesc::Array(items, _) => items
            .iter()
            .any(|item| expression_assigns_ident(item, ident)),
        ExpressionDesc::CamlBlock(items, _, tag, _) => {
            items
                .iter()
                .any(|item| expression_assigns_ident(item, ident))
                || expression_assigns_ident(tag, ident)
        }
        ExpressionDesc::Object(dup, props) => {
            dup.as_ref()
                .is_some_and(|expr| expression_assigns_ident(expr, ident))
                || props
                    .iter()
                    .any(|(_, value)| expression_assigns_ident(value, ident))
        }
        ExpressionDesc::Var(_)
        | ExpressionDesc::Undefined { .. }
        | ExpressionDesc::Null
        | ExpressionDesc::Bool(_)
        | ExpressionDesc::Str { .. }
        | ExpressionDesc::RawJsCode(_)
        | ExpressionDesc::Number(_) => false,
    }
}

fn inline_tailcall_call(
    immutable_mask: &[bool],
    params: &[Ident],
    args: Vec<Expression>,
    body: Block,
) -> Block {
    let mut bindings = Vec::new();
    let mut substitution = HashMap::new();

    for ((param, arg), immutable) in params
        .iter()
        .cloned()
        .zip(args.into_iter())
        .zip(immutable_mask.iter().copied())
    {
        if immutable {
            if let ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)) = &arg.desc {
                substitution.insert(param, id.clone());
                continue;
            }
        }

        bindings.push(Statement::variable(VariableDeclaration {
            ident: param,
            value: Some(arg),
            property: LetKind::Variable,
            ident_info: IdentInfo::default(),
        }));
    }

    let body = if substitution.is_empty() {
        body
    } else {
        substitute_inline_block(body, &substitution)
    };

    bindings.into_iter().chain(body).collect()
}

fn substitute_inline_block(block: Block, substitution: &HashMap<Ident, Ident>) -> Block {
    let mut current_substitution = substitution.clone();
    let mut rewritten = Vec::with_capacity(block.len());

    for stmt in block {
        let stmt = substitute_inline_statement(stmt, &current_substitution);
        shadow_inline_statement_bindings(&stmt, &mut current_substitution);
        rewritten.push(stmt);
    }

    rewritten
}

fn substitute_inline_statement(stmt: Statement, substitution: &HashMap<Ident, Ident>) -> Statement {
    let Statement { desc, comment } = stmt;
    let desc = match desc {
        StatementDesc::Block(block) => {
            StatementDesc::Block(substitute_inline_block(block, substitution))
        }
        StatementDesc::Variable(mut decl) => {
            decl.value = decl
                .value
                .map(|value| substitute_inline_expression(value, substitution));
            StatementDesc::Variable(decl)
        }
        StatementDesc::Exp(expr) => {
            StatementDesc::Exp(substitute_inline_expression(expr, substitution))
        }
        StatementDesc::If(cond, then_block, else_block) => StatementDesc::If(
            substitute_inline_expression(cond, substitution),
            substitute_inline_block(then_block, substitution),
            substitute_inline_block(else_block, substitution),
        ),
        StatementDesc::While(cond, body) => StatementDesc::While(
            substitute_inline_expression(cond, substitution),
            substitute_inline_block(body, substitution),
        ),
        StatementDesc::ForRange(start, finish, ident, direction, body) => {
            let body_substitution = prune_inline_substitution(substitution, [&ident]);
            StatementDesc::ForRange(
                start.map(|expr| substitute_inline_expression(expr, substitution)),
                substitute_inline_expression(finish, substitution),
                ident,
                direction,
                substitute_inline_block(body, &body_substitution),
            )
        }
        StatementDesc::Continue => StatementDesc::Continue,
        StatementDesc::Break => StatementDesc::Break,
        StatementDesc::Return(expr) => {
            StatementDesc::Return(substitute_inline_expression(expr, substitution))
        }
        StatementDesc::IntSwitch(test, clauses, default) => StatementDesc::IntSwitch(
            substitute_inline_expression(test, substitution),
            clauses
                .into_iter()
                .map(|(value, clause)| {
                    (
                        value,
                        CaseClause {
                            body: substitute_inline_block(clause.body, substitution),
                            should_break: clause.should_break,
                            comment: clause.comment,
                        },
                    )
                })
                .collect(),
            default.map(|block| substitute_inline_block(block, substitution)),
        ),
        StatementDesc::StringSwitch(test, clauses, default) => StatementDesc::StringSwitch(
            substitute_inline_expression(test, substitution),
            clauses
                .into_iter()
                .map(|clause| StringClause {
                    tag_type: clause.tag_type,
                    clause: CaseClause {
                        body: substitute_inline_block(clause.clause.body, substitution),
                        should_break: clause.clause.should_break,
                        comment: clause.clause.comment,
                    },
                })
                .collect(),
            default.map(|block| substitute_inline_block(block, substitution)),
        ),
        StatementDesc::Throw(expr) => {
            StatementDesc::Throw(substitute_inline_expression(expr, substitution))
        }
        StatementDesc::Try(body, catch, finally) => StatementDesc::Try(
            substitute_inline_block(body, substitution),
            catch.map(|(ident, block)| {
                let catch_substitution = prune_inline_substitution(substitution, [&ident]);
                (ident, substitute_inline_block(block, &catch_substitution))
            }),
            finally.map(|block| substitute_inline_block(block, substitution)),
        ),
        StatementDesc::Debugger => StatementDesc::Debugger,
    };

    Statement { desc, comment }
}

fn substitute_inline_expression(
    expr: Expression,
    substitution: &HashMap<Ident, Ident>,
) -> Expression {
    let Expression { desc, comment } = expr;
    let desc = match desc {
        ExpressionDesc::Length(inner, obj) => ExpressionDesc::Length(
            Box::new(substitute_inline_expression(*inner, substitution)),
            obj,
        ),
        ExpressionDesc::IsNullOrUndefined(inner) => ExpressionDesc::IsNullOrUndefined(Box::new(
            substitute_inline_expression(*inner, substitution),
        )),
        ExpressionDesc::StringAppend(left, right) => ExpressionDesc::StringAppend(
            Box::new(substitute_inline_expression(*left, substitution)),
            Box::new(substitute_inline_expression(*right, substitution)),
        ),
        ExpressionDesc::Bool(value) => ExpressionDesc::Bool(value),
        ExpressionDesc::Typeof(inner) => {
            ExpressionDesc::Typeof(Box::new(substitute_inline_expression(*inner, substitution)))
        }
        ExpressionDesc::In(left, right) => ExpressionDesc::In(
            Box::new(substitute_inline_expression(*left, substitution)),
            Box::new(substitute_inline_expression(*right, substitution)),
        ),
        ExpressionDesc::JsNot(inner) => {
            ExpressionDesc::JsNot(Box::new(substitute_inline_expression(*inner, substitution)))
        }
        ExpressionDesc::JsBnot(inner) => {
            ExpressionDesc::JsBnot(Box::new(substitute_inline_expression(*inner, substitution)))
        }
        ExpressionDesc::Seq(left, right) => ExpressionDesc::Seq(
            Box::new(substitute_inline_expression(*left, substitution)),
            Box::new(substitute_inline_expression(*right, substitution)),
        ),
        ExpressionDesc::Cond(test, consequent, alternate) => ExpressionDesc::Cond(
            Box::new(substitute_inline_expression(*test, substitution)),
            Box::new(substitute_inline_expression(*consequent, substitution)),
            Box::new(substitute_inline_expression(*alternate, substitution)),
        ),
        ExpressionDesc::Bin(op, left, right) => ExpressionDesc::Bin(
            op,
            Box::new(substitute_inline_expression(*left, substitution)),
            Box::new(substitute_inline_expression(*right, substitution)),
        ),
        ExpressionDesc::FlatCall(func, args) => ExpressionDesc::FlatCall(
            Box::new(substitute_inline_expression(*func, substitution)),
            Box::new(substitute_inline_expression(*args, substitution)),
        ),
        ExpressionDesc::Call(func, args, info) => ExpressionDesc::Call(
            Box::new(substitute_inline_expression(*func, substitution)),
            args.into_iter()
                .map(|arg| substitute_inline_expression(arg, substitution))
                .collect(),
            info,
        ),
        ExpressionDesc::StringIndex(left, right) => ExpressionDesc::StringIndex(
            Box::new(substitute_inline_expression(*left, substitution)),
            Box::new(substitute_inline_expression(*right, substitution)),
        ),
        ExpressionDesc::ArrayIndex(left, right) => ExpressionDesc::ArrayIndex(
            Box::new(substitute_inline_expression(*left, substitution)),
            Box::new(substitute_inline_expression(*right, substitution)),
        ),
        ExpressionDesc::TaggedTemplate(tag, strings, values) => ExpressionDesc::TaggedTemplate(
            Box::new(substitute_inline_expression(*tag, substitution)),
            strings
                .into_iter()
                .map(|expr| substitute_inline_expression(expr, substitution))
                .collect(),
            values
                .into_iter()
                .map(|expr| substitute_inline_expression(expr, substitution))
                .collect(),
        ),
        ExpressionDesc::StaticIndex(target, field, position) => ExpressionDesc::StaticIndex(
            Box::new(substitute_inline_expression(*target, substitution)),
            field,
            position,
        ),
        ExpressionDesc::New(target, args) => ExpressionDesc::New(
            Box::new(substitute_inline_expression(*target, substitution)),
            args.map(|args| {
                args.into_iter()
                    .map(|arg| substitute_inline_expression(arg, substitution))
                    .collect()
            }),
        ),
        ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)) => {
            let id = substitution.get(&id).cloned().unwrap_or(id);
            ExpressionDesc::Var(crate::js_ir::VIdent::Id(id))
        }
        ExpressionDesc::Var(crate::js_ir::VIdent::Qualified(module, member)) => {
            ExpressionDesc::Var(crate::js_ir::VIdent::Qualified(module, member))
        }
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
            body: {
                let body_substitution = prune_inline_substitution(substitution, params.iter());
                substitute_inline_block(body, &body_substitution)
            },
            params,
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
                .map(|item| substitute_inline_expression(item, substitution))
                .collect(),
            mutable_flag,
        ),
        ExpressionDesc::OptionalBlock(inner, flag) => ExpressionDesc::OptionalBlock(
            Box::new(substitute_inline_expression(*inner, substitution)),
            flag,
        ),
        ExpressionDesc::CamlBlock(items, mutable_flag, tag, info) => ExpressionDesc::CamlBlock(
            items
                .into_iter()
                .map(|item| substitute_inline_expression(item, substitution))
                .collect(),
            mutable_flag,
            Box::new(substitute_inline_expression(*tag, substitution)),
            info,
        ),
        ExpressionDesc::CamlBlockTag(inner, field) => ExpressionDesc::CamlBlockTag(
            Box::new(substitute_inline_expression(*inner, substitution)),
            field,
        ),
        ExpressionDesc::Number(number) => ExpressionDesc::Number(number),
        ExpressionDesc::Object(dup, props) => ExpressionDesc::Object(
            dup.map(|expr| Box::new(substitute_inline_expression(*expr, substitution))),
            props
                .into_iter()
                .map(|(name, value)| (name, substitute_inline_expression(value, substitution)))
                .collect(),
        ),
        ExpressionDesc::Undefined { is_unit } => ExpressionDesc::Undefined { is_unit },
        ExpressionDesc::Null => ExpressionDesc::Null,
        ExpressionDesc::Await(inner) => {
            ExpressionDesc::Await(Box::new(substitute_inline_expression(*inner, substitution)))
        }
        ExpressionDesc::Spread(inner) => {
            ExpressionDesc::Spread(Box::new(substitute_inline_expression(*inner, substitution)))
        }
    };

    Expression { desc, comment }
}

fn prune_inline_substitution<'a>(
    substitution: &HashMap<Ident, Ident>,
    shadowed: impl IntoIterator<Item = &'a Ident>,
) -> HashMap<Ident, Ident> {
    let mut pruned = substitution.clone();
    for ident in shadowed {
        pruned.remove(ident);
    }
    pruned
}

fn shadow_inline_statement_bindings(stmt: &Statement, substitution: &mut HashMap<Ident, Ident>) {
    if let StatementDesc::Variable(VariableDeclaration { ident, .. }) = &stmt.desc {
        substitution.remove(ident);
    }
}

fn apply_tailcall_used_stats_block(block: &mut Block, statuses: &HashMap<Ident, UsedStats>) {
    for stmt in block {
        apply_tailcall_used_stats_statement(stmt, statuses);
    }
}

fn apply_tailcall_used_stats_statement(stmt: &mut Statement, statuses: &HashMap<Ident, UsedStats>) {
    match &mut stmt.desc {
        StatementDesc::Block(block) => apply_tailcall_used_stats_block(block, statuses),
        StatementDesc::Variable(decl) => {
            if let Some(status) = statuses.get(&decl.ident).copied() {
                decl.ident_info.used_stats = status;
            }
            if let Some(value) = &mut decl.value {
                apply_tailcall_used_stats_expression(value, statuses);
            }
        }
        StatementDesc::Exp(expr) | StatementDesc::Return(expr) | StatementDesc::Throw(expr) => {
            apply_tailcall_used_stats_expression(expr, statuses);
        }
        StatementDesc::If(_, then_block, else_block) => {
            apply_tailcall_used_stats_block(then_block, statuses);
            apply_tailcall_used_stats_block(else_block, statuses);
        }
        StatementDesc::While(_, body) => apply_tailcall_used_stats_block(body, statuses),
        StatementDesc::ForRange(_, _, _, _, body) => {
            apply_tailcall_used_stats_block(body, statuses)
        }
        StatementDesc::IntSwitch(_, clauses, default) => {
            for (_, clause) in clauses {
                apply_tailcall_used_stats_block(&mut clause.body, statuses);
            }
            if let Some(default) = default {
                apply_tailcall_used_stats_block(default, statuses);
            }
        }
        StatementDesc::StringSwitch(_, clauses, default) => {
            for clause in clauses {
                apply_tailcall_used_stats_block(&mut clause.clause.body, statuses);
            }
            if let Some(default) = default {
                apply_tailcall_used_stats_block(default, statuses);
            }
        }
        StatementDesc::Try(body, catch, finally) => {
            apply_tailcall_used_stats_block(body, statuses);
            if let Some((_, block)) = catch {
                apply_tailcall_used_stats_block(block, statuses);
            }
            if let Some(block) = finally {
                apply_tailcall_used_stats_block(block, statuses);
            }
        }
        StatementDesc::Debugger | StatementDesc::Break | StatementDesc::Continue => {}
    }
}

fn apply_tailcall_used_stats_expression(
    expr: &mut Expression,
    statuses: &HashMap<Ident, UsedStats>,
) {
    match &mut expr.desc {
        ExpressionDesc::Length(inner, _)
        | ExpressionDesc::IsNullOrUndefined(inner)
        | ExpressionDesc::Typeof(inner)
        | ExpressionDesc::JsNot(inner)
        | ExpressionDesc::JsBnot(inner)
        | ExpressionDesc::CamlBlockTag(inner, _)
        | ExpressionDesc::OptionalBlock(inner, _)
        | ExpressionDesc::Await(inner)
        | ExpressionDesc::Spread(inner) => apply_tailcall_used_stats_expression(inner, statuses),
        ExpressionDesc::StringAppend(left, right)
        | ExpressionDesc::In(left, right)
        | ExpressionDesc::Seq(left, right)
        | ExpressionDesc::Bin(_, left, right)
        | ExpressionDesc::FlatCall(left, right)
        | ExpressionDesc::StringIndex(left, right)
        | ExpressionDesc::ArrayIndex(left, right) => {
            apply_tailcall_used_stats_expression(left, statuses);
            apply_tailcall_used_stats_expression(right, statuses);
        }
        ExpressionDesc::Cond(test, consequent, alternate) => {
            apply_tailcall_used_stats_expression(test, statuses);
            apply_tailcall_used_stats_expression(consequent, statuses);
            apply_tailcall_used_stats_expression(alternate, statuses);
        }
        ExpressionDesc::Call(func, args, _) => {
            apply_tailcall_used_stats_expression(func, statuses);
            for arg in args {
                apply_tailcall_used_stats_expression(arg, statuses);
            }
        }
        ExpressionDesc::TaggedTemplate(tag, strings, values) => {
            apply_tailcall_used_stats_expression(tag, statuses);
            for string in strings {
                apply_tailcall_used_stats_expression(string, statuses);
            }
            for value in values {
                apply_tailcall_used_stats_expression(value, statuses);
            }
        }
        ExpressionDesc::StaticIndex(target, _, _) => {
            apply_tailcall_used_stats_expression(target, statuses)
        }
        ExpressionDesc::New(target, args) => {
            apply_tailcall_used_stats_expression(target, statuses);
            if let Some(args) = args {
                for arg in args {
                    apply_tailcall_used_stats_expression(arg, statuses);
                }
            }
        }
        ExpressionDesc::Fun { body, .. } => apply_tailcall_used_stats_block(body, statuses),
        ExpressionDesc::Array(items, _) => {
            for item in items {
                apply_tailcall_used_stats_expression(item, statuses);
            }
        }
        ExpressionDesc::CamlBlock(items, _, tag, _) => {
            for item in items {
                apply_tailcall_used_stats_expression(item, statuses);
            }
            apply_tailcall_used_stats_expression(tag, statuses);
        }
        ExpressionDesc::Object(dup, props) => {
            if let Some(dup) = dup {
                apply_tailcall_used_stats_expression(dup, statuses);
            }
            for (_, value) in props {
                apply_tailcall_used_stats_expression(value, statuses);
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
