//! Materialize `RecordRest` expressions as object destructuring declarations.
//! Port of `compiler/core/js_pass_record_rest.ml`.

use ahash::AHashMap as HashMap;

use crate::ident::Ident;
use crate::js_ir::RecordRestField;
use crate::js_ir::arena::{
    Block, Expr, ExprKind, JsArena, JsDepsProgram as DepsProgram, Stmt, StmtKind, VarDecl,
};
use crate::js_ir::build::{exp as E, stmt as S};
use crate::js_ir::walk::Mapper;
use crate::lambda::LetKind;

pub(crate) fn apply_js_record_rest_pass(mut deps: DepsProgram) -> DepsProgram {
    // Without a `RecordRest` expression the rewrite rebuilds the program
    // unchanged and creates no identifiers. The flatten-and-mark-dead pass
    // that runs next raises the identifier counter past the same program, so
    // the counter only needs raising here before a rewrite.
    let mut finder = RecordRestFinder::default();
    crate::js_ir::walk::walk_block(&mut finder, &deps.program.arena, &deps.program.block);
    if !finder.found {
        return deps;
    }
    let start_stamp =
        crate::lambda::js_pass_flatten_and_mark_dead::max_ident_stamp_in_program(&deps.program)
            .max(Ident::current_local_stamp());
    Ident::set_current_time(start_stamp);
    let program = &mut deps.program;
    let block = std::mem::take(&mut program.block);
    program.block = RecordRest.block_items(&mut program.arena, &block);
    deps
}

#[derive(Default)]
struct RecordRestFinder {
    found: bool,
}

impl crate::js_ir::walk::Visitor for RecordRestFinder {
    fn visit_expression(&mut self, a: &JsArena, expression: Expr) {
        if matches!(a.ek(expression), ExprKind::RecordRest(_, _)) {
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
    j: &mut JsArena,
    source: Expr,
    mut fields: Vec<RecordRestField>,
    tail: Block,
) -> (Vec<RecordRestField>, Block) {
    let ExprKind::Var(source_ident) = j.ek(source) else {
        for (index, field) in fields.iter_mut().enumerate() {
            if field.ident.is_none() {
                field.ident = Some(Ident::create_local(format!("__unused{index}")));
            }
        }
        return (fields, tail);
    };
    let source_ident = j.ident(source_ident);

    let field_indices = fields
        .iter()
        .enumerate()
        .map(|(index, field)| (field.label.clone(), index))
        .collect::<HashMap<_, _>>();
    let mut used_fields = HashMap::<String, Ident>::new();
    let tail = replace_source_fields(j, tail, &source_ident, &field_indices, &mut used_fields);
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

/// `s.label` for the source variable `source`.
fn source_field<'a>(j: &'a JsArena, expr: Expr, source: &Ident) -> Option<&'a str> {
    let ExprKind::StaticIndex(target, label, _) = j.ek(expr) else {
        return None;
    };
    matches!(j.ek(target), ExprKind::Var(id) if j.ident(id).same(source)).then(|| j.text(label))
}

fn replace_source_fields(
    j: &mut JsArena,
    block: Block,
    source: &Ident,
    field_indices: &HashMap<String, usize>,
    used: &mut HashMap<String, Ident>,
) -> Block {
    let mut result = Vec::with_capacity(block.len());
    for statement in block {
        if let StmtKind::Variable(declaration) = j.sk(statement) {
            let declaration = j.var(declaration);
            if let Some(value) = declaration.value
                && let Some(label) = source_field(j, value, source)
                && field_indices.contains_key(label)
            {
                used.insert(label.to_string(), declaration.ident);
                continue;
            }
        }
        let mut f = |j: &mut JsArena, expr: Expr| {
            if let Some(label) = source_field(j, expr, source)
                && let Some(index) = field_indices.get(label)
            {
                let label = label.to_string();
                let ident = *used
                    .entry(label.clone())
                    .or_insert_with(|| Ident::create_local(field_ident_name(*index, &label)));
                return E::var(ident, j);
            }
            expr
        };
        result.push(map_statement(j, statement, &mut f));
    }
    result
}

/// `js_pass_record_rest.ml` `rewrite_block`: statements are rewritten from
/// last to first, so each `RecordRest` sees its already rewritten tail.
struct RecordRest;

impl Mapper for RecordRest {
    fn block(
        &mut self,
        j: &mut JsArena,
        block: crate::js_ir::arena::StmtList,
    ) -> crate::js_ir::arena::StmtList {
        crate::js_ir::walk::map_block_with_items(self, j, block)
    }

    fn block_items(&mut self, j: &mut JsArena, block: &[Stmt]) -> Vec<Stmt> {
        let mut reversed: Vec<Stmt> = Vec::with_capacity(block.len());
        for statement in block.iter().rev() {
            let statement = self.statement(j, *statement);
            match j.sk(statement) {
                StmtKind::Variable(v) => {
                    let decl = j.var(v).clone();
                    if let Some(value) = decl.value
                        && let ExprKind::RecordRest(fields, source) = j.ek(value)
                    {
                        let fields = j.rest(fields).to_vec();
                        let tail = reversed.into_iter().rev().collect();
                        let source = self.expression(j, source);
                        let (fields, tail) = materialize_fields(j, source, fields, tail);
                        reversed = tail.into_iter().rev().collect();
                        let fields = j.rest_id(fields);
                        let value = j.rekind_expr(value, ExprKind::RecordRest(fields, source));
                        let v = j.var_id(VarDecl {
                            value: Some(value),
                            ..decl
                        });
                        reversed.push(j.rekind_stmt(statement, StmtKind::Variable(v)));
                    } else {
                        reversed.push(statement);
                    }
                }
                StmtKind::Return(value) if matches!(j.ek(value), ExprKind::RecordRest(_, _)) => {
                    let ExprKind::RecordRest(fields, source) = j.ek(value) else {
                        unreachable!()
                    };
                    let fields = j.rest(fields).to_vec();
                    let rest = Ident::create_local("rest");
                    let source = self.expression(j, source);
                    let rest_var = E::var(rest, j);
                    let return_statement = j.rekind_stmt(statement, StmtKind::Return(rest_var));
                    let (fields, mut return_block) =
                        materialize_fields(j, source, fields, vec![return_statement]);
                    let fields = j.rest_id(fields);
                    let rest_value = j.rekind_expr(value, ExprKind::RecordRest(fields, source));
                    let declaration = S::define(rest, Some(rest_value), LetKind::Strict, j);
                    let tail = reversed.into_iter().rev().collect::<Vec<_>>();
                    return_block.extend(tail);
                    reversed = return_block.into_iter().rev().collect();
                    reversed.push(declaration);
                }
                _ => reversed.push(statement),
            }
        }
        reversed.into_iter().rev().collect()
    }
}

/// Pre-order rewrite of the expressions of a statement through `f`,
/// descending only through the statement and expression kinds the OCaml
/// pass rewrites.
fn map_statement(
    j: &mut JsArena,
    statement: Stmt,
    f: &mut impl FnMut(&mut JsArena, Expr) -> Expr,
) -> Stmt {
    fn map_expr(
        j: &mut JsArena,
        expr: Expr,
        f: &mut impl FnMut(&mut JsArena, Expr) -> Expr,
    ) -> Expr {
        let expr = f(j, expr);
        let list = |j: &mut JsArena, l, f: &mut _| {
            let items = j.expr_vec(l);
            let items: Vec<Expr> = items.into_iter().map(|item| map_expr(j, item, f)).collect();
            j.expr_list(&items)
        };
        let kind = match j.ek(expr) {
            ExprKind::StaticIndex(inner, name, pos) => {
                ExprKind::StaticIndex(map_expr(j, inner, f), name, pos)
            }
            ExprKind::Array(items, mutable) => ExprKind::Array(list(j, items, f), mutable),
            ExprKind::Object(proto, fields) => {
                let proto = proto.map(|inner| map_expr(j, inner, f));
                let items = j.props(fields).to_vec();
                let items: Vec<_> = items
                    .into_iter()
                    .map(|(name, value)| (name, map_expr(j, value, f)))
                    .collect();
                ExprKind::Object(proto, j.prop_list(&items))
            }
            ExprKind::Call(func, args, info) => {
                let func = map_expr(j, func, f);
                ExprKind::Call(func, list(j, args, f), info)
            }
            ExprKind::StringAppend(left, right) => {
                let left = map_expr(j, left, f);
                ExprKind::StringAppend(left, map_expr(j, right, f))
            }
            ExprKind::Bin(op, left, right) => {
                let left = map_expr(j, left, f);
                ExprKind::Bin(op, left, map_expr(j, right, f))
            }
            ExprKind::Seq(left, right) => {
                let left = map_expr(j, left, f);
                ExprKind::Seq(left, map_expr(j, right, f))
            }
            ExprKind::Cond(test, yes, no) => {
                let test = map_expr(j, test, f);
                let yes = map_expr(j, yes, f);
                ExprKind::Cond(test, yes, map_expr(j, no, f))
            }
            ExprKind::OptionalBlock(inner, flag) => {
                ExprKind::OptionalBlock(map_expr(j, inner, f), flag)
            }
            ExprKind::CamlBlock(items, mutable, info) => {
                ExprKind::CamlBlock(list(j, items, f), mutable, info)
            }
            _ => return expr,
        };
        j.rekind_expr(expr, kind)
    }
    let kind = match j.sk(statement) {
        StmtKind::Block(block) => {
            let items = j.block_vec(block);
            let items: Vec<Stmt> = items.into_iter().map(|s| map_statement(j, s, f)).collect();
            StmtKind::Block(j.stmt_list(&items))
        }
        StmtKind::Variable(v) => {
            let decl = j.var(v).clone();
            let Some(value) = decl.value else {
                return statement;
            };
            let value = map_expr(j, value, f);
            StmtKind::Variable(j.var_id(VarDecl {
                value: Some(value),
                ..decl
            }))
        }
        StmtKind::Exp(expr) => StmtKind::Exp(map_expr(j, expr, f)),
        StmtKind::Return(expr) => StmtKind::Return(map_expr(j, expr, f)),
        _ => return statement,
    };
    j.rekind_stmt(statement, kind)
}
