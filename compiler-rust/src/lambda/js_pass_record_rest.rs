//! Materialize `RecordRest` expressions as object destructuring declarations.
//! Port of `compiler/core/js_pass_record_rest.ml`.

use ahash::AHashMap as HashMap;

use crate::ident::Ident;
use crate::js_ir::op::IdentInfo;
use crate::js_ir::{
    Block, CaseClause, DepsProgram, Expression, ExpressionDesc, RecordRestField, Statement,
    StatementDesc, StringClause, VIdent, VariableDeclaration,
};
use crate::lambda::LetKind;

pub(crate) fn apply_js_record_rest_pass(mut deps: DepsProgram) -> DepsProgram {
    // Without a `RecordRest` expression the rewrite rebuilds the program
    // unchanged and creates no identifiers. The flatten-and-mark-dead pass
    // that runs next raises the identifier counter past the same program, so
    // the counter only needs raising here before a rewrite.
    let mut finder = RecordRestFinder::default();
    crate::js_ir::walk::walk_block(&mut finder, &deps.program.block);
    if !finder.found {
        return deps;
    }
    let start_stamp =
        crate::lambda::js_pass_flatten_and_mark_dead::max_ident_stamp_in_program(&deps.program)
            .max(Ident::current_local_stamp());
    Ident::set_current_time(start_stamp);
    deps.program.block = rewrite_block(std::mem::take(&mut deps.program.block));
    deps
}

#[derive(Default)]
struct RecordRestFinder {
    found: bool,
}

impl<'a> crate::js_ir::walk::Visitor<'a> for RecordRestFinder {
    fn visit_expression(&mut self, expression: &'a Expression) {
        if matches!(expression.desc, ExpressionDesc::RecordRest(_, _)) {
            self.found = true;
        }
    }

    fn done(&self) -> bool {
        self.found
    }
}

fn field_ident_name(index: usize, label: &str) -> String {
    if crate::js_ir::printer::is_valid_js_ident(label) {
        label.to_string()
    } else {
        format!("__rest_field{index}")
    }
}

fn materialize_fields(
    source: &Expression,
    mut fields: Vec<RecordRestField>,
    tail: Block,
) -> (Vec<RecordRestField>, Block) {
    let ExpressionDesc::Var(VIdent::Id(source_ident)) = &source.desc else {
        for (index, field) in fields.iter_mut().enumerate() {
            if field.ident.is_none() {
                field.ident = Some(Ident::create_local(format!("__unused{index}")));
            }
        }
        return (fields, tail);
    };

    let field_indices = fields
        .iter()
        .enumerate()
        .map(|(index, field)| (field.label.clone(), index))
        .collect::<HashMap<_, _>>();
    let mut used_fields = HashMap::<String, Ident>::new();
    let tail = replace_source_fields(tail, source_ident, &field_indices, &mut used_fields);
    for (index, field) in fields.iter_mut().enumerate() {
        if field.ident.is_none() {
            field.ident = Some(
                used_fields
                    .get(&field.label)
                    .cloned()
                    .unwrap_or_else(|| Ident::create_local(format!("__unused{index}"))),
            );
        }
    }
    (fields, tail)
}

fn replace_source_fields(
    block: Block,
    source: &Ident,
    field_indices: &HashMap<String, usize>,
    used: &mut HashMap<String, Ident>,
) -> Block {
    let mut result = Vec::with_capacity(block.len());
    for statement in block {
        if let StatementDesc::Variable(declaration) = &statement.desc {
            if let Some(Expression {
                desc: ExpressionDesc::StaticIndex(target, label, _),
                ..
            }) = &declaration.value
            {
                if matches!(&target.desc, ExpressionDesc::Var(VIdent::Id(id)) if id.same(source))
                    && field_indices.contains_key(label)
                {
                    used.insert(label.clone(), declaration.ident.clone());
                    continue;
                }
            }
        }
        result.push(map_statement(statement, &mut |expr| {
            if let ExpressionDesc::StaticIndex(target, label, _) = &expr.desc {
                if matches!(&target.desc, ExpressionDesc::Var(VIdent::Id(id)) if id.same(source)) {
                    if let Some(index) = field_indices.get(label) {
                        let ident = used
                            .entry(label.clone())
                            .or_insert_with(|| Ident::create_local(field_ident_name(*index, label)))
                            .clone();
                        return Expression::var(ident);
                    }
                }
            }
            expr
        }));
    }
    result
}

fn rewrite_block(block: Block) -> Block {
    let mut reversed = Vec::with_capacity(block.len());
    for statement in block.into_iter().rev() {
        let statement = rewrite_statement(statement);
        match statement.desc {
            StatementDesc::Variable(mut declaration) => {
                if matches!(
                    declaration.value.as_ref().map(|value| &value.desc),
                    Some(ExpressionDesc::RecordRest(_, _))
                ) {
                    let Expression {
                        desc: ExpressionDesc::RecordRest(fields, source),
                        comment,
                        source_loc,
                    } = declaration.value.take().expect("record-rest value")
                    else {
                        unreachable!()
                    };
                    let tail = reversed.into_iter().rev().collect();
                    let source = rewrite_expression(*source);
                    let (fields, tail) = materialize_fields(&source, fields, tail);
                    reversed = tail.into_iter().rev().collect();
                    declaration.value = Some(Expression {
                        desc: ExpressionDesc::RecordRest(fields, Box::new(source)),
                        comment,
                        source_loc,
                    });
                }
                reversed.push(Statement {
                    desc: StatementDesc::Variable(declaration),
                    ..statement
                });
            }
            StatementDesc::Return(Expression {
                desc: ExpressionDesc::RecordRest(fields, source),
                comment,
                source_loc,
            }) => {
                let rest = Ident::create_local("rest");
                let source = rewrite_expression(*source);
                let return_statement = Statement {
                    desc: StatementDesc::Return(Expression::var(rest.clone())),
                    comment: statement.comment.clone(),
                    source_loc: statement.source_loc.clone(),
                };
                let (fields, mut return_block) =
                    materialize_fields(&source, fields, vec![return_statement]);
                let declaration = Statement::variable(VariableDeclaration {
                    ident: rest,
                    value: Some(Expression {
                        desc: ExpressionDesc::RecordRest(fields, Box::new(source)),
                        comment,
                        source_loc,
                    }),
                    property: LetKind::Strict,
                    ident_info: IdentInfo::default(),
                });
                let tail = reversed.into_iter().rev().collect::<Vec<_>>();
                return_block.extend(tail);
                reversed = return_block.into_iter().rev().collect();
                reversed.push(declaration);
            }
            desc => reversed.push(Statement { desc, ..statement }),
        }
    }
    reversed.into_iter().rev().collect()
}

fn rewrite_statement(mut statement: Statement) -> Statement {
    statement.desc = match statement.desc {
        StatementDesc::Block(block) => StatementDesc::Block(rewrite_block(block)),
        StatementDesc::Variable(mut declaration) => {
            declaration.value = declaration.value.map(rewrite_expression);
            StatementDesc::Variable(declaration)
        }
        StatementDesc::Exp(expr) => StatementDesc::Exp(rewrite_expression(expr)),
        StatementDesc::Return(expr) => StatementDesc::Return(rewrite_expression(expr)),
        StatementDesc::Throw(expr) => StatementDesc::Throw(rewrite_expression(expr)),
        StatementDesc::If(cond, yes, no) => StatementDesc::If(
            rewrite_expression(cond),
            rewrite_block(yes),
            rewrite_block(no),
        ),
        StatementDesc::While(label, cond, body) => {
            StatementDesc::While(label, rewrite_expression(cond), rewrite_block(body))
        }
        StatementDesc::ForRange(label, init, end, ident, dir, body) => StatementDesc::ForRange(
            label,
            init.map(|expr| Box::new(rewrite_expression(*expr))),
            Box::new(rewrite_expression(*end)),
            ident,
            dir,
            rewrite_block(body),
        ),
        StatementDesc::ForOf(label, ident, expr, body) => {
            StatementDesc::ForOf(label, ident, Box::new(rewrite_expression(*expr)), rewrite_block(body))
        }
        StatementDesc::ForAwaitOf(label, ident, expr, body) => {
            StatementDesc::ForAwaitOf(label, ident, Box::new(rewrite_expression(*expr)), rewrite_block(body))
        }
        StatementDesc::IntSwitch(expr, clauses, default) => StatementDesc::IntSwitch(
            rewrite_expression(expr),
            clauses
                .into_iter()
                .map(|(tag, clause)| (tag, rewrite_clause(clause)))
                .collect(),
            default.map(rewrite_block),
        ),
        StatementDesc::StringSwitch(expr, clauses, default) => StatementDesc::StringSwitch(
            rewrite_expression(expr),
            clauses
                .into_iter()
                .map(|clause| StringClause {
                    clause: rewrite_clause(clause.clause),
                    ..clause
                })
                .collect(),
            default.map(rewrite_block),
        ),
        StatementDesc::Try(body, catch, finally) => StatementDesc::Try(
            rewrite_block(body),
            catch.map(|(id, body)| (id, rewrite_block(body))),
            finally.map(rewrite_block),
        ),
        other => other,
    };
    statement
}

fn rewrite_clause(mut clause: CaseClause) -> CaseClause {
    clause.body = rewrite_block(clause.body);
    clause
}

fn rewrite_expression(mut expression: Expression) -> Expression {
    expression.desc = match expression.desc {
        ExpressionDesc::Length(inner, kind) => {
            ExpressionDesc::Length(Box::new(rewrite_expression(*inner)), kind)
        }
        ExpressionDesc::IsNullOrUndefined(inner) => {
            ExpressionDesc::IsNullOrUndefined(Box::new(rewrite_expression(*inner)))
        }
        ExpressionDesc::Typeof(inner) => {
            ExpressionDesc::Typeof(Box::new(rewrite_expression(*inner)))
        }
        ExpressionDesc::JsNot(inner) => ExpressionDesc::JsNot(Box::new(rewrite_expression(*inner))),
        ExpressionDesc::JsBnot(inner) => {
            ExpressionDesc::JsBnot(Box::new(rewrite_expression(*inner)))
        }
        ExpressionDesc::CamlBlockTag(inner, tag) => {
            ExpressionDesc::CamlBlockTag(Box::new(rewrite_expression(*inner)), tag)
        }
        ExpressionDesc::OptionalBlock(inner, flag) => {
            ExpressionDesc::OptionalBlock(Box::new(rewrite_expression(*inner)), flag)
        }
        ExpressionDesc::Await(inner) => ExpressionDesc::Await(Box::new(rewrite_expression(*inner))),
        ExpressionDesc::Spread(inner) => {
            ExpressionDesc::Spread(Box::new(rewrite_expression(*inner)))
        }
        ExpressionDesc::RecordRest(fields, source) => {
            ExpressionDesc::RecordRest(fields, Box::new(rewrite_expression(*source)))
        }
        ExpressionDesc::StaticIndex(inner, name, pos) => {
            ExpressionDesc::StaticIndex(Box::new(rewrite_expression(*inner)), name, pos)
        }
        ExpressionDesc::New(inner, args) => ExpressionDesc::New(
            Box::new(rewrite_expression(*inner)),
            args.map(|args| args.into_iter().map(rewrite_expression).collect()),
        ),
        ExpressionDesc::StringAppend(left, right) => ExpressionDesc::StringAppend(
            Box::new(rewrite_expression(*left)),
            Box::new(rewrite_expression(*right)),
        ),
        ExpressionDesc::In(left, right) => ExpressionDesc::In(
            Box::new(rewrite_expression(*left)),
            Box::new(rewrite_expression(*right)),
        ),
        ExpressionDesc::Seq(left, right) => ExpressionDesc::Seq(
            Box::new(rewrite_expression(*left)),
            Box::new(rewrite_expression(*right)),
        ),
        ExpressionDesc::Bin(op, left, right) => ExpressionDesc::Bin(
            op,
            Box::new(rewrite_expression(*left)),
            Box::new(rewrite_expression(*right)),
        ),
        ExpressionDesc::FlatCall(left, right) => ExpressionDesc::FlatCall(
            Box::new(rewrite_expression(*left)),
            Box::new(rewrite_expression(*right)),
        ),
        ExpressionDesc::StringIndex(left, right) => ExpressionDesc::StringIndex(
            Box::new(rewrite_expression(*left)),
            Box::new(rewrite_expression(*right)),
        ),
        ExpressionDesc::ArrayIndex(left, right) => ExpressionDesc::ArrayIndex(
            Box::new(rewrite_expression(*left)),
            Box::new(rewrite_expression(*right)),
        ),
        ExpressionDesc::Cond(a, b, c) => ExpressionDesc::Cond(
            Box::new(rewrite_expression(*a)),
            Box::new(rewrite_expression(*b)),
            Box::new(rewrite_expression(*c)),
        ),
        ExpressionDesc::Call(func, args, info) => ExpressionDesc::Call(
            Box::new(rewrite_expression(*func)),
            args.into_iter().map(rewrite_expression).collect(),
            info,
        ),
        ExpressionDesc::TaggedTemplate(tag, strings, values) => ExpressionDesc::TaggedTemplate(
            Box::new(rewrite_expression(*tag)),
            strings.into_iter().map(rewrite_expression).collect(),
            values.into_iter().map(rewrite_expression).collect(),
        ),
        ExpressionDesc::Array(items, mutable) => {
            ExpressionDesc::Array(items.into_iter().map(rewrite_expression).collect(), mutable)
        }
        ExpressionDesc::Object(proto, fields) => ExpressionDesc::Object(
            proto.map(|expr| Box::new(rewrite_expression(*expr))),
            fields
                .into_iter()
                .map(|(name, value)| (name, rewrite_expression(value)))
                .collect(),
        ),
        ExpressionDesc::CamlBlock(items, mutable, info) => ExpressionDesc::CamlBlock(
            items.into_iter().map(rewrite_expression).collect(),
            mutable,
            info,
        ),
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
            body: rewrite_block(body),
            env,
            return_unit,
            async_,
            directive,
        },
        other => other,
    };
    expression
}

fn map_statement(statement: Statement, f: &mut impl FnMut(Expression) -> Expression) -> Statement {
    fn map_expr(expr: Expression, f: &mut impl FnMut(Expression) -> Expression) -> Expression {
        let mut expr = f(expr);
        expr.desc = match expr.desc {
            ExpressionDesc::StaticIndex(inner, name, pos) => {
                ExpressionDesc::StaticIndex(Box::new(map_expr(*inner, f)), name, pos)
            }
            ExpressionDesc::Array(items, mutable) => ExpressionDesc::Array(
                items.into_iter().map(|item| map_expr(item, f)).collect(),
                mutable,
            ),
            ExpressionDesc::Object(proto, fields) => ExpressionDesc::Object(
                proto.map(|inner| Box::new(map_expr(*inner, f))),
                fields
                    .into_iter()
                    .map(|(name, value)| (name, map_expr(value, f)))
                    .collect(),
            ),
            ExpressionDesc::Call(func, args, info) => ExpressionDesc::Call(
                Box::new(map_expr(*func, f)),
                args.into_iter().map(|arg| map_expr(arg, f)).collect(),
                info,
            ),
            ExpressionDesc::StringAppend(left, right) => ExpressionDesc::StringAppend(
                Box::new(map_expr(*left, f)),
                Box::new(map_expr(*right, f)),
            ),
            ExpressionDesc::Bin(op, left, right) => ExpressionDesc::Bin(
                op,
                Box::new(map_expr(*left, f)),
                Box::new(map_expr(*right, f)),
            ),
            ExpressionDesc::Seq(left, right) => {
                ExpressionDesc::Seq(Box::new(map_expr(*left, f)), Box::new(map_expr(*right, f)))
            }
            ExpressionDesc::Cond(test, yes, no) => ExpressionDesc::Cond(
                Box::new(map_expr(*test, f)),
                Box::new(map_expr(*yes, f)),
                Box::new(map_expr(*no, f)),
            ),
            ExpressionDesc::OptionalBlock(inner, flag) => {
                ExpressionDesc::OptionalBlock(Box::new(map_expr(*inner, f)), flag)
            }
            ExpressionDesc::CamlBlock(items, mutable, info) => ExpressionDesc::CamlBlock(
                items.into_iter().map(|item| map_expr(item, f)).collect(),
                mutable,
                info,
            ),
            desc => desc,
        };
        expr
    }
    let mut statement = statement;
    statement.desc = match statement.desc {
        StatementDesc::Block(block) => StatementDesc::Block(
            block
                .into_iter()
                .map(|stmt| map_statement(stmt, f))
                .collect(),
        ),
        StatementDesc::Variable(mut decl) => {
            decl.value = decl.value.map(|expr| map_expr(expr, f));
            StatementDesc::Variable(decl)
        }
        StatementDesc::Exp(expr) => StatementDesc::Exp(map_expr(expr, f)),
        StatementDesc::Return(expr) => StatementDesc::Return(map_expr(expr, f)),
        other => other,
    };
    statement
}
