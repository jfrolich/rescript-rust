//! JS IR pass: tailcall inlining.
//!
//! Inlines single-use pure function bindings at their return-position call
//! sites, eliminating the intermediate function wrapper. Also tracks used/dead
//! status for variable declarations.

use ahash::AHashMap as HashMap;

use crate::ident::Ident;
use crate::js_ir::op::{IdentInfo, UsedStats};
use crate::js_ir::{
    BinOp, Block, CaseClause, DepsProgram, Expression, ExpressionDesc, Program, Statement,
    StatementDesc, StringClause, VariableDeclaration,
};
use crate::lambda::js_pass_external_shadow::is_lexical_binding_kind;
use crate::lambda::lam_compat::LetKind;

use super::js_exp_make::js_expr_no_side_effects;

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
        name_reservations: program.name_reservations,
    };
    apply_tailcall_used_stats_block(&mut program.block, &inliner.statuses);
    program
}

#[derive(Debug)]
struct TailcallInlineState {
    inline_decls: HashMap<Ident, InlineFunctionDecl>,
    statuses: HashMap<Ident, UsedStats>,
    active_decls: Vec<Ident>,
}

#[derive(Debug)]
struct DeclUsageInfo {
    pure: bool,
}

#[derive(Debug)]
struct InlineFunctionDecl {
    params: Vec<Ident>,
    body: Block,
}

impl TailcallInlineState {
    fn new(program: &Program) -> Self {
        let mut decls = HashMap::new();
        let mut counts = HashMap::new();
        collect_tailcall_use_counts_block(&program.block, &mut decls, &mut counts);

        let mut statuses = HashMap::with_capacity(decls.len());
        for (ident, info) in &decls {
            let count = counts.get(ident).copied().unwrap_or(0);
            let exported = program.export_set.contains(ident);
            let status = if exported {
                UsedStats::Exported
            } else if count == 0 {
                if info.pure {
                    UsedStats::DeadPure
                } else {
                    UsedStats::DeadNonPure
                }
            } else if count == 1 && info.pure {
                UsedStats::OncePure
            } else {
                UsedStats::Used
            };
            statuses.insert(ident.clone(), status);
        }

        // OCaml's stats table keeps the existing variable declarations by
        // pointer (`compiler/core/js_pass_get_used.ml:55-77`) and the tailcall
        // pass only needs function bodies for the Once_pure inline branch
        // (`compiler/core/js_pass_tailcall_inline.ml:160-192`). Keep Rust's
        // counted metadata lightweight, then clone only those inlineable
        // function bodies instead of cloning every JS declaration tree.
        let mut inline_decls = HashMap::new();
        collect_once_pure_inline_decls_block(&program.block, &statuses, &mut inline_decls);

        Self {
            inline_decls,
            statuses,
            active_decls: Vec::new(),
        }
    }

    fn transform_block(&mut self, block: Block) -> Block {
        let len = block.len();
        let mut transformed = Vec::with_capacity(len);
        for (index, stmt) in block.into_iter().enumerate() {
            // OCaml recurses as `x :: xs -> self.statement x :: self.block xs`
            // before matching the one-statement tail-call inline case
            // (`compiler/core/js_pass_tailcall_inline.ml:130-159,232`).
            // Check the final suffix after preceding declarations have updated
            // `inline_decls`, so `let aux; return aux(...)` can inline.
            if index + 1 == len {
                match self.try_inline_single_return_statement(stmt) {
                    Ok(inlined) => {
                        transformed.extend(inlined);
                    }
                    Err(stmt) => {
                        transformed.extend(self.transform_statement(stmt));
                    }
                }
            } else {
                transformed.extend(self.transform_statement(stmt));
            }
        }
        transformed
    }

    fn transform_statement(&mut self, stmt: Statement) -> Vec<Statement> {
        let Statement {
            source_loc,
            desc,
            comment,
        } = stmt;
        match desc {
            StatementDesc::Block(block) => vec![Statement {
                source_loc,
                desc: StatementDesc::Block(self.transform_block(block)),
                comment,
            }],
            StatementDesc::Variable(mut decl) => {
                if let Some(value) = decl.value.take() {
                    self.active_decls.push(decl.ident.clone());
                    decl.value = Some(self.transform_expression(value));
                    self.active_decls.pop();
                }

                let status = self
                    .statuses
                    .get(&decl.ident)
                    .copied()
                    .unwrap_or(UsedStats::Used);
                // OCaml rewrites a variable declaration first, then stores the
                // rewritten declaration back into the stats table
                // (`compiler/core/js_pass_tailcall_inline.ml:120-129`). Do the
                // same for inlineable function bodies without cloning unrelated
                // declarations.
                if status == UsedStats::OncePure
                    && let Some(inline_decl) = inline_function_decl_from_variable(&decl)
                {
                    self.inline_decls.insert(decl.ident.clone(), inline_decl);
                }
                decl.ident_info.used_stats = status;
                match status {
                    UsedStats::DeadPure => vec![],
                    UsedStats::DeadNonPure => decl
                        .value
                        .map(|value| {
                            vec![Statement {
                                source_loc,
                                desc: StatementDesc::Exp(value),
                                comment,
                            }]
                        })
                        .unwrap_or_default(),
                    _ => vec![Statement {
                        source_loc,
                        desc: StatementDesc::Variable(decl),
                        comment,
                    }],
                }
            }
            StatementDesc::Exp(expr) => vec![Statement {
                source_loc,
                desc: StatementDesc::Exp(self.transform_expression(expr)),
                comment,
            }],
            StatementDesc::If(cond, then_block, else_block) => vec![Statement {
                source_loc,
                desc: StatementDesc::If(
                    self.transform_expression(cond),
                    self.transform_block(then_block),
                    self.transform_block(else_block),
                ),
                comment,
            }],
            StatementDesc::While(label, cond, body) => vec![Statement {
                source_loc,
                desc: StatementDesc::While(
                    label,
                    self.transform_expression(cond),
                    self.transform_block(body),
                ),
                comment,
            }],
            StatementDesc::ForRange(label, start, finish, ident, direction, body) => {
                vec![Statement {
                    source_loc,
                    desc: StatementDesc::ForRange(
                        label,
                        start.map(|expr| self.transform_expression(expr)),
                        self.transform_expression(finish),
                        ident,
                        direction,
                        self.transform_block(body),
                    ),
                    comment,
                }]
            }
            StatementDesc::ForOf(label, ident, iterable, body) => vec![Statement {
                source_loc,
                desc: StatementDesc::ForOf(
                    label,
                    ident,
                    self.transform_expression(iterable),
                    self.transform_block(body),
                ),
                comment,
            }],
            StatementDesc::ForAwaitOf(label, ident, iterable, body) => vec![Statement {
                source_loc,
                desc: StatementDesc::ForAwaitOf(
                    label,
                    ident,
                    self.transform_expression(iterable),
                    self.transform_block(body),
                ),
                comment,
            }],
            StatementDesc::Continue(label) => vec![Statement {
                source_loc,
                desc: StatementDesc::Continue(label),
                comment,
            }],
            StatementDesc::Break(label) => vec![Statement {
                source_loc,
                desc: StatementDesc::Break(label),
                comment,
            }],
            StatementDesc::Return(expr) => vec![Statement {
                source_loc,
                desc: StatementDesc::Return(self.transform_expression(expr)),
                comment,
            }],
            StatementDesc::IntSwitch(test, clauses, default) => vec![Statement {
                source_loc,
                desc: StatementDesc::IntSwitch(
                    self.transform_expression(test),
                    clauses
                        .into_iter()
                        .map(|(value, clause)| {
                            (
                                value,
                                CaseClause {
                                    source_loc: None,
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
                source_loc,
                desc: StatementDesc::StringSwitch(
                    self.transform_expression(test),
                    clauses
                        .into_iter()
                        .map(|clause| StringClause {
                            tag_type: clause.tag_type,
                            clause: CaseClause {
                                source_loc: clause.clause.source_loc,
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
                source_loc,
                desc: StatementDesc::Throw(self.transform_expression(expr)),
                comment,
            }],
            StatementDesc::Try(body, catch, finally) => vec![Statement {
                source_loc,
                desc: StatementDesc::Try(
                    self.transform_block(body),
                    catch.map(|(ident, block)| (ident, self.transform_block(block))),
                    finally.map(|block| self.transform_block(block)),
                ),
                comment,
            }],
            StatementDesc::Debugger => vec![Statement {
                source_loc,
                desc: StatementDesc::Debugger,
                comment,
            }],
        }
    }

    fn transform_expression(&mut self, expr: Expression) -> Expression {
        let Expression {
            source_loc,
            desc,
            comment,
        } = expr;
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
            ExpressionDesc::CamlBlock(items, mutable_flag, info) => ExpressionDesc::CamlBlock(
                items
                    .into_iter()
                    .map(|item| self.transform_expression(item))
                    .collect(),
                mutable_flag,
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
            ExpressionDesc::RecordRest(fields, source) => {
                ExpressionDesc::RecordRest(fields, Box::new(self.transform_expression(*source)))
            }
        };

        Expression {
            source_loc,
            desc,
            comment,
        }
    }

    fn try_inline_single_return_statement(&mut self, stmt: Statement) -> Result<Block, Statement> {
        let Statement {
            source_loc: stmt_source_loc,
            desc,
            comment,
        } = stmt;
        let StatementDesc::Return(expr) = desc else {
            return Err(Statement {
                source_loc: stmt_source_loc,
                desc,
                comment,
            });
        };
        let Expression {
            source_loc: expr_source_loc,
            desc: expr_desc,
            comment: expr_comment,
        } = expr;
        let ExpressionDesc::Call(func, args, info) = expr_desc else {
            return Err(Statement {
                source_loc: stmt_source_loc,
                desc: StatementDesc::Return(Expression {
                    source_loc: expr_source_loc,
                    desc: expr_desc,
                    comment: expr_comment,
                }),
                comment,
            });
        };

        let Expression {
            source_loc: func_source_loc,
            desc: func_desc,
            comment: func_comment,
        } = *func;
        match func_desc {
            ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)) => {
                match self.inline_named_call_owned(&id, args) {
                    Ok(block) => Ok(block),
                    Err(args) => Err(Statement {
                        source_loc: stmt_source_loc,
                        desc: StatementDesc::Return(Expression {
                            source_loc: expr_source_loc,
                            desc: ExpressionDesc::Call(
                                Box::new(Expression {
                                    source_loc: func_source_loc,
                                    desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                                    comment: func_comment,
                                }),
                                args,
                                info,
                            ),
                            comment: expr_comment,
                        }),
                        comment,
                    }),
                }
            }
            ExpressionDesc::Fun {
                is_method: false,
                params,
                body,
                env: _,
                return_unit: _,
                async_: false,
                directive: None,
            } if params.len() == args.len() => {
                Ok(self.inline_function_call_owned(params, body, args))
            }
            func_desc => Err(Statement {
                source_loc: stmt_source_loc,
                desc: StatementDesc::Return(Expression {
                    source_loc: expr_source_loc,
                    desc: ExpressionDesc::Call(
                        Box::new(Expression {
                            source_loc: func_source_loc,
                            desc: func_desc,
                            comment: func_comment,
                        }),
                        args,
                        info,
                    ),
                    comment: expr_comment,
                }),
                comment,
            }),
        }
    }

    fn inline_named_call_owned(
        &mut self,
        ident: &Ident,
        args: Vec<Expression>,
    ) -> Result<Block, Vec<Expression>> {
        if self.statuses.get(ident).copied() != Some(UsedStats::OncePure) {
            return Err(args);
        }
        // OCaml keeps the transformed declaration in the stats table while
        // walking blocks, which avoids consuming a recursive function while
        // traversing its own body (`compiler/core/js_pass_tailcall_inline.ml:81-105`,
        // `compiler/core/js_pass_tailcall_inline.ml:120-129`). Only inline the
        // stored declaration at an outer tail-call site (`compiler/core/js_pass_tailcall_inline.ml:150-192`).
        if self.active_decls.iter().any(|active| active.same(ident)) {
            return Err(args);
        }

        let Some(decl) = self.inline_decls.remove(ident) else {
            return Err(args);
        };

        if decl.params.len() != args.len() {
            return Err(args);
        }

        self.statuses.insert(ident.clone(), UsedStats::DeadPure);
        Ok(self.inline_function_call_owned(decl.params, decl.body, args))
    }

    fn inline_function_call_owned(
        &mut self,
        params: Vec<Ident>,
        body: Block,
        args: Vec<Expression>,
    ) -> Block {
        let processed_body = self.transform_block(body);
        let immutable_mask = immutable_param_mask(&params, &processed_body);
        let args = args
            .into_iter()
            .map(|arg| self.transform_expression(arg))
            .collect();
        inline_tailcall_call(&immutable_mask, &params, args, processed_body)
    }
}

fn collect_tailcall_use_counts_block(
    block: &Block,
    decls: &mut HashMap<Ident, DeclUsageInfo>,
    counts: &mut HashMap<Ident, usize>,
) {
    for stmt in block {
        collect_tailcall_use_counts_statement(stmt, decls, counts);
    }
}

fn collect_tailcall_use_counts_statement(
    stmt: &Statement,
    decls: &mut HashMap<Ident, DeclUsageInfo>,
    counts: &mut HashMap<Ident, usize>,
) {
    match &stmt.desc {
        StatementDesc::Block(block) => collect_tailcall_use_counts_block(block, decls, counts),
        StatementDesc::Variable(decl) => {
            decls.insert(
                decl.ident.clone(),
                DeclUsageInfo {
                    pure: decl.value.as_ref().is_some_and(js_expr_no_side_effects),
                },
            );
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
        StatementDesc::While(_, cond, body) => {
            collect_tailcall_use_counts_expression(cond, decls, counts);
            collect_tailcall_use_counts_block(body, decls, counts);
        }
        StatementDesc::ForRange(_, start, finish, _, _, body) => {
            if let Some(start) = start {
                collect_tailcall_use_counts_expression(start, decls, counts);
            }
            collect_tailcall_use_counts_expression(finish, decls, counts);
            collect_tailcall_use_counts_block(body, decls, counts);
        }
        StatementDesc::ForOf(_, _, iterable, body)
        | StatementDesc::ForAwaitOf(_, _, iterable, body) => {
            collect_tailcall_use_counts_expression(iterable, decls, counts);
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
        StatementDesc::Debugger | StatementDesc::Break(_) | StatementDesc::Continue(_) => {}
    }
}

fn collect_tailcall_use_counts_expression(
    expr: &Expression,
    decls: &mut HashMap<Ident, DeclUsageInfo>,
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
        | ExpressionDesc::Spread(inner)
        | ExpressionDesc::RecordRest(_, inner) => {
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
        ExpressionDesc::CamlBlock(items, _, _) => {
            for item in items {
                collect_tailcall_use_counts_expression(item, decls, counts);
            }
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

fn inline_function_decl_from_variable(decl: &VariableDeclaration) -> Option<InlineFunctionDecl> {
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
    }) = &decl.value
    else {
        return None;
    };

    Some(InlineFunctionDecl {
        params: params.clone(),
        body: body.clone(),
    })
}

fn collect_once_pure_inline_decls_block(
    block: &Block,
    statuses: &HashMap<Ident, UsedStats>,
    inline_decls: &mut HashMap<Ident, InlineFunctionDecl>,
) {
    for stmt in block {
        collect_once_pure_inline_decls_statement(stmt, statuses, inline_decls);
    }
}

fn collect_once_pure_inline_decls_statement(
    stmt: &Statement,
    statuses: &HashMap<Ident, UsedStats>,
    inline_decls: &mut HashMap<Ident, InlineFunctionDecl>,
) {
    match &stmt.desc {
        StatementDesc::Block(block) => {
            collect_once_pure_inline_decls_block(block, statuses, inline_decls)
        }
        StatementDesc::Variable(decl) => {
            if statuses.get(&decl.ident).copied() == Some(UsedStats::OncePure)
                && let Some(inline_decl) = inline_function_decl_from_variable(decl)
            {
                inline_decls.insert(decl.ident.clone(), inline_decl);
            }
            if let Some(value) = &decl.value {
                collect_once_pure_inline_decls_expression(value, statuses, inline_decls);
            }
        }
        StatementDesc::Exp(expr) | StatementDesc::Return(expr) | StatementDesc::Throw(expr) => {
            collect_once_pure_inline_decls_expression(expr, statuses, inline_decls);
        }
        StatementDesc::If(cond, then_block, else_block) => {
            collect_once_pure_inline_decls_expression(cond, statuses, inline_decls);
            collect_once_pure_inline_decls_block(then_block, statuses, inline_decls);
            collect_once_pure_inline_decls_block(else_block, statuses, inline_decls);
        }
        StatementDesc::While(_, cond, body) => {
            collect_once_pure_inline_decls_expression(cond, statuses, inline_decls);
            collect_once_pure_inline_decls_block(body, statuses, inline_decls);
        }
        StatementDesc::ForRange(_, start, finish, _, _, body) => {
            if let Some(start) = start {
                collect_once_pure_inline_decls_expression(start, statuses, inline_decls);
            }
            collect_once_pure_inline_decls_expression(finish, statuses, inline_decls);
            collect_once_pure_inline_decls_block(body, statuses, inline_decls);
        }
        StatementDesc::ForOf(_, _, iterable, body)
        | StatementDesc::ForAwaitOf(_, _, iterable, body) => {
            collect_once_pure_inline_decls_expression(iterable, statuses, inline_decls);
            collect_once_pure_inline_decls_block(body, statuses, inline_decls);
        }
        StatementDesc::IntSwitch(test, clauses, default) => {
            collect_once_pure_inline_decls_expression(test, statuses, inline_decls);
            for (_, clause) in clauses {
                collect_once_pure_inline_decls_block(&clause.body, statuses, inline_decls);
            }
            if let Some(default) = default {
                collect_once_pure_inline_decls_block(default, statuses, inline_decls);
            }
        }
        StatementDesc::StringSwitch(test, clauses, default) => {
            collect_once_pure_inline_decls_expression(test, statuses, inline_decls);
            for clause in clauses {
                collect_once_pure_inline_decls_block(&clause.clause.body, statuses, inline_decls);
            }
            if let Some(default) = default {
                collect_once_pure_inline_decls_block(default, statuses, inline_decls);
            }
        }
        StatementDesc::Try(body, catch, finally) => {
            collect_once_pure_inline_decls_block(body, statuses, inline_decls);
            if let Some((_, block)) = catch {
                collect_once_pure_inline_decls_block(block, statuses, inline_decls);
            }
            if let Some(block) = finally {
                collect_once_pure_inline_decls_block(block, statuses, inline_decls);
            }
        }
        StatementDesc::Debugger | StatementDesc::Break(_) | StatementDesc::Continue(_) => {}
    }
}

fn collect_once_pure_inline_decls_expression(
    expr: &Expression,
    statuses: &HashMap<Ident, UsedStats>,
    inline_decls: &mut HashMap<Ident, InlineFunctionDecl>,
) {
    match &expr.desc {
        ExpressionDesc::Var(_)
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
        | ExpressionDesc::Spread(inner)
        | ExpressionDesc::StaticIndex(inner, _, _)
        | ExpressionDesc::New(inner, None) => {
            collect_once_pure_inline_decls_expression(inner, statuses, inline_decls)
        }
        ExpressionDesc::RecordRest(_, inner) => {
            collect_once_pure_inline_decls_expression(inner, statuses, inline_decls)
        }
        ExpressionDesc::StringAppend(left, right)
        | ExpressionDesc::In(left, right)
        | ExpressionDesc::Seq(left, right)
        | ExpressionDesc::Bin(_, left, right)
        | ExpressionDesc::FlatCall(left, right)
        | ExpressionDesc::StringIndex(left, right)
        | ExpressionDesc::ArrayIndex(left, right) => {
            collect_once_pure_inline_decls_expression(left, statuses, inline_decls);
            collect_once_pure_inline_decls_expression(right, statuses, inline_decls);
        }
        ExpressionDesc::Cond(test, consequent, alternate) => {
            collect_once_pure_inline_decls_expression(test, statuses, inline_decls);
            collect_once_pure_inline_decls_expression(consequent, statuses, inline_decls);
            collect_once_pure_inline_decls_expression(alternate, statuses, inline_decls);
        }
        ExpressionDesc::Call(func, args, _) => {
            collect_once_pure_inline_decls_expression(func, statuses, inline_decls);
            for arg in args {
                collect_once_pure_inline_decls_expression(arg, statuses, inline_decls);
            }
        }
        ExpressionDesc::TaggedTemplate(tag, strings, values) => {
            for string in strings {
                collect_once_pure_inline_decls_expression(string, statuses, inline_decls);
            }
            for value in values {
                collect_once_pure_inline_decls_expression(value, statuses, inline_decls);
            }
        }
        ExpressionDesc::New(target, Some(args)) => {
            collect_once_pure_inline_decls_expression(target, statuses, inline_decls);
            for arg in args {
                collect_once_pure_inline_decls_expression(arg, statuses, inline_decls);
            }
        }
        ExpressionDesc::Fun { body, .. } => {
            collect_once_pure_inline_decls_block(body, statuses, inline_decls)
        }
        ExpressionDesc::Array(items, _) => {
            for item in items {
                collect_once_pure_inline_decls_expression(item, statuses, inline_decls);
            }
        }
        ExpressionDesc::CamlBlock(items, _, _) => {
            for item in items {
                collect_once_pure_inline_decls_expression(item, statuses, inline_decls);
            }
        }
        ExpressionDesc::Object(dup, props) => {
            if let Some(dup) = dup {
                collect_once_pure_inline_decls_expression(dup, statuses, inline_decls);
            }
            for (_, value) in props {
                collect_once_pure_inline_decls_expression(value, statuses, inline_decls);
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
        StatementDesc::While(_, cond, body) => {
            expression_assigns_ident(cond, ident) || block_assigns_ident(body, ident)
        }
        StatementDesc::ForRange(_, start, finish, _, _, body) => {
            start
                .as_ref()
                .is_some_and(|expr| expression_assigns_ident(expr, ident))
                || expression_assigns_ident(finish, ident)
                || block_assigns_ident(body, ident)
        }
        StatementDesc::ForOf(_, _, iterable, body)
        | StatementDesc::ForAwaitOf(_, _, iterable, body) => {
            expression_assigns_ident(iterable, ident) || block_assigns_ident(body, ident)
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
        StatementDesc::Debugger | StatementDesc::Break(_) | StatementDesc::Continue(_) => false,
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
        | ExpressionDesc::Spread(inner)
        | ExpressionDesc::RecordRest(_, inner) => expression_assigns_ident(inner, ident),
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
        ExpressionDesc::CamlBlock(items, _, _) => items
            .iter()
            .any(|item| expression_assigns_ident(item, ident)),
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
    let Statement {
        source_loc,
        desc,
        comment,
    } = stmt;
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
        StatementDesc::While(label, cond, body) => StatementDesc::While(
            label,
            substitute_inline_expression(cond, substitution),
            substitute_inline_block(body, substitution),
        ),
        StatementDesc::ForRange(label, start, finish, ident, direction, body) => {
            let body_substitution = prune_inline_substitution(substitution, [&ident]);
            StatementDesc::ForRange(
                label,
                start.map(|expr| substitute_inline_expression(expr, substitution)),
                substitute_inline_expression(finish, substitution),
                ident,
                direction,
                substitute_inline_block(body, &body_substitution),
            )
        }
        StatementDesc::ForOf(label, ident, iterable, body) => {
            let body_substitution = prune_inline_substitution(substitution, [&ident]);
            StatementDesc::ForOf(
                label,
                ident,
                substitute_inline_expression(iterable, substitution),
                substitute_inline_block(body, &body_substitution),
            )
        }
        StatementDesc::ForAwaitOf(label, ident, iterable, body) => {
            let body_substitution = prune_inline_substitution(substitution, [&ident]);
            StatementDesc::ForAwaitOf(
                label,
                ident,
                substitute_inline_expression(iterable, substitution),
                substitute_inline_block(body, &body_substitution),
            )
        }
        StatementDesc::Continue(label) => StatementDesc::Continue(label),
        StatementDesc::Break(label) => StatementDesc::Break(label),
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
                            source_loc: clause.source_loc,
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
                        source_loc: None,
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

    Statement {
        source_loc,
        desc,
        comment,
    }
}

fn substitute_inline_expression(
    expr: Expression,
    substitution: &HashMap<Ident, Ident>,
) -> Expression {
    let Expression {
        source_loc,
        desc,
        comment,
    } = expr;
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
        ExpressionDesc::CamlBlock(items, mutable_flag, info) => ExpressionDesc::CamlBlock(
            items
                .into_iter()
                .map(|item| substitute_inline_expression(item, substitution))
                .collect(),
            mutable_flag,
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
        ExpressionDesc::RecordRest(fields, source) => ExpressionDesc::RecordRest(
            fields,
            Box::new(substitute_inline_expression(*source, substitution)),
        ),
    };

    Expression {
        source_loc,
        desc,
        comment,
    }
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
        StatementDesc::While(_, _, body) => apply_tailcall_used_stats_block(body, statuses),
        StatementDesc::ForRange(_, _, _, _, _, body) => {
            apply_tailcall_used_stats_block(body, statuses)
        }
        StatementDesc::ForOf(_, _, _, body) | StatementDesc::ForAwaitOf(_, _, _, body) => {
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
        StatementDesc::Debugger | StatementDesc::Break(_) | StatementDesc::Continue(_) => {}
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
        | ExpressionDesc::Spread(inner)
        | ExpressionDesc::RecordRest(_, inner) => {
            apply_tailcall_used_stats_expression(inner, statuses)
        }
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
        ExpressionDesc::CamlBlock(items, _, _) => {
            for item in items {
                apply_tailcall_used_stats_expression(item, statuses);
            }
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
