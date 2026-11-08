//! JS IR pass: flatten and mark dead.
//!
//! This pass flattens nested block structures, substitutes caml block
//! projections, and marks dead code for elimination.

use ahash::AHashMap as HashMap;
use ahash::AHashSet as HashSet;

use crate::context::IdGenerator;
use crate::ident::Ident;
use crate::js_ir::BinOp;
use crate::js_ir::arena::{
    Block, Expr, ExprKind, JsArena, JsDepsProgram as DepsProgram, JsProgram as Program, Stmt,
    StmtKind, StmtList, VarDecl,
};
use crate::js_ir::build::{exp as E, stmt as S};
use crate::js_ir::op::{IdentInfo, MutableFlag, UsedStats};
use crate::js_ir::walk::{Mapper, map_expression_children, map_statement_children};
use crate::lambda::TagInfo;
use crate::lambda::lam_compat::LetKind;

use super::js_exp_make::{
    direct_projection_from_pure_literal, int_literal, js_expr_no_side_effects,
};
use super::lam_coercion::max_ident_stamp_in_block;

pub(crate) fn apply_js_flatten_pass(mut deps: DepsProgram) -> DepsProgram {
    let program = &mut deps.program;
    let block = std::mem::take(&mut program.block);
    program.block = flatten_block(&mut program.arena, &block);
    deps
}

pub(crate) fn apply_js_flatten_and_mark_dead_pass(
    mut deps: DepsProgram,
    jsx_preserve: bool,
) -> DepsProgram {
    // OCaml's substitution pass allocates materialized block fields with
    // `Ext_ident.create` from the process-wide Ident counter
    // (compiler/core/js_pass_flatten_and_mark_dead.ml:188-204). Keep Rust's
    // pass generator past both the JS program and the legacy local counter so
    // newly materialized fields cannot share stamps with existing locals.
    let start_stamp = max_ident_stamp_in_program(&deps.program).max(Ident::current_local_stamp());
    let id_gen = IdGenerator::with_start_stamp(start_stamp);
    Ident::set_current_time(start_stamp);
    flatten_and_mark_dead_program(&mut deps.program, &id_gen, jsx_preserve);
    deps
}

fn flatten_and_mark_dead_program(program: &mut Program, id_gen: &IdGenerator, jsx_preserve: bool) {
    let mut subst = Substitute {
        id_gen,
        substitution: HashMap::new(),
        jsx_preserve,
    };
    let block = std::mem::take(&mut program.block);
    program.block = subst.block_items(&mut program.arena, &block);
    mark_dead_code(program);
}

/// `js_pass_flatten_and_mark_dead.ml` `subst_map`.
struct Substitute<'g> {
    id_gen: &'g IdGenerator,
    substitution: HashMap<Ident, Expr>,
    jsx_preserve: bool,
}

impl Mapper for Substitute<'_> {
    fn statement(&mut self, j: &mut JsArena, stmt: Stmt) -> Stmt {
        let StmtKind::Variable(v) = j.sk(stmt) else {
            return map_statement_children(self, j, stmt);
        };
        let decl = j.var(v).clone();
        let cold = j.stmt_cold(stmt);
        if matches!(decl.ident_info.used_stats, UsedStats::DeadPure) {
            let empty = j.empty_block();
            return j.stmt_with(StmtKind::Block(empty), cold);
        }

        if matches!(decl.ident_info.used_stats, UsedStats::DeadNonPure) {
            return match decl.value {
                None => {
                    let empty = j.empty_block();
                    j.stmt_with(StmtKind::Block(empty), cold)
                }
                Some(value) => j.stmt_with(StmtKind::Exp(value), cold),
            };
        }

        if matches!(
            decl.property,
            LetKind::Strict | LetKind::StrictOpt | LetKind::Alias
        ) && let Some(value) = decl.value
            && let ExprKind::CamlBlock(items, MutableFlag::Immutable, tag) = j.ek(value)
        {
            let items = j.expr_vec(items);
            if should_materialize_block_binding_items(j, decl.property, &items, j.tag(tag)) {
                let mut rewritten_items = Vec::with_capacity(items.len());
                let mut bindings = Vec::new();

                for (index, item) in items.into_iter().enumerate() {
                    if is_simple_block_binding_item(j, item) {
                        rewritten_items.push(item);
                    } else {
                        let rewritten = self.expression(j, item);
                        let temp = self.id_gen.create(&block_substitution_name(
                            &decl.ident,
                            j.tag(tag),
                            index,
                        ));
                        rewritten_items.push(E::var(temp, j));
                        bindings.push(S::define(temp, Some(rewritten), LetKind::Strict, j));
                    }
                }

                let rewritten_items = j.expr_list(&rewritten_items);
                let rewritten_value = j.rekind_expr(
                    value,
                    ExprKind::CamlBlock(rewritten_items, MutableFlag::Immutable, tag),
                );
                self.substitution.insert(decl.ident, rewritten_value);

                let new_var = j.var_id(VarDecl {
                    value: Some(rewritten_value),
                    ..decl
                });
                let original = j.stmt_with(StmtKind::Variable(new_var), cold);

                if bindings.is_empty() {
                    return original;
                }

                bindings.push(original);
                let bindings = j.stmt_list(&bindings);
                return j.stmt_with(
                    StmtKind::Block(bindings),
                    crate::js_ir::arena::Cold {
                        comment: None,
                        source_loc: cold.source_loc,
                    },
                );
            }

            // OCaml's js_pass_flatten_and_mark_dead matches
            // `_ :: _ :: _ as ls`, which means immutable Caml blocks
            // with at least two payload elements. Polyvar wrappers stay
            // out of this path because their exported `NAME`/`VAL`
            // object shape is already materialized before this pass in
            // the OCaml backend.
            let mapped: Vec<Expr> = items.iter().map(|item| self.expression(j, *item)).collect();
            let mapped = j.expr_list(&mapped);
            let rewritten_value = j.rekind_expr(
                value,
                ExprKind::CamlBlock(mapped, MutableFlag::Immutable, tag),
            );
            let new_var = j.var_id(VarDecl {
                value: Some(rewritten_value),
                ..decl
            });
            return j.stmt_with(StmtKind::Variable(new_var), cold);
        }

        map_statement_children(self, j, stmt)
    }

    fn expression(&mut self, j: &mut JsArena, expr: Expr) -> Expr {
        if let Some(rewritten) = self.try_substitute_caml_block_projection(j, expr) {
            return rewritten;
        }

        match j.ek(expr) {
            ExprKind::ArrayIndex(left, right) => {
                let left = self.expression(j, left);
                let right = self.expression(j, right);
                if let Some(rewritten) =
                    direct_projection_from_pure_literal(j, left, None, int_literal(j, right))
                {
                    return rewritten;
                }
                j.rekind_expr(expr, ExprKind::ArrayIndex(left, right))
            }
            ExprKind::StaticIndex(target, field, pos) => {
                let target = self.expression(j, target);
                let name = j.text(field).to_string();
                if let Some(rewritten) =
                    direct_projection_from_pure_literal(j, target, Some(&name), pos.get())
                {
                    return rewritten;
                }
                j.rekind_expr(expr, ExprKind::StaticIndex(target, field, pos))
            }
            _ => map_expression_children(self, j, expr),
        }
    }
}

impl Substitute<'_> {
    fn try_substitute_caml_block_projection(&self, j: &JsArena, expr: Expr) -> Option<Expr> {
        match j.ek(expr) {
            ExprKind::ArrayIndex(left, right) => {
                let ExprKind::Var(id) = j.ek(left) else {
                    return None;
                };
                let i = int_literal(j, right)?;
                self.substituted_caml_block_item(j, &j.ident(id), None, i)
            }
            ExprKind::StaticIndex(target, field, pos) => {
                let index = pos.get()?;
                let ExprKind::Var(id) = j.ek(target) else {
                    return None;
                };
                self.substituted_caml_block_item(j, &j.ident(id), Some(j.text(field)), index)
            }
            _ => None,
        }
    }

    fn substituted_caml_block_item(
        &self,
        j: &JsArena,
        id: &Ident,
        field: Option<&str>,
        index: i32,
    ) -> Option<Expr> {
        let expression = *self.substitution.get(id)?;
        // js_pass_flatten_and_mark_dead.ml:266-270 (7432): in JSX preserve mode a
        // block item that is the variable `make` stays a projection, so the
        // dumper prints `<Foo.make />`.
        let substitutable = |item: Expr| {
            is_simple_substituted_index_value(j, item)
                && !(self.jsx_preserve
                    && matches!(j.ek(item), ExprKind::Var(id) if j.ident(id).name() == "make"))
        };
        let ExprKind::CamlBlock(items, MutableFlag::Immutable, tag_info) = j.ek(expression) else {
            return None;
        };
        let items = j.exprs(items);
        let tag_info = j.tag(tag_info);
        if let Some(field) = field {
            match tag_info {
                TagInfo::Record(_) | TagInfo::RecordInlined(_) => {
                    let fields = tag_info.record_fields().expect("record block");
                    let item =
                        items
                            .iter()
                            .zip(fields.iter())
                            .find_map(|(item, (field_name, _))| {
                                (field_name == field).then_some(*item)
                            })?;
                    return substitutable(item).then_some(item);
                }
                _ => {}
            }
        }
        let item = *items.get(usize::try_from(index).ok()?)?;
        substitutable(item).then_some(item)
    }
}

fn should_materialize_block_binding_items(
    j: &JsArena,
    property: LetKind,
    items: &[Expr],
    tag_info: &TagInfo,
) -> bool {
    // OCaml's substitution pass matches every immutable `Caml_block`
    // with at least two elements, including `Blk_poly_var`, before
    // splitting complex payload fields
    // (`compiler/core/js_pass_flatten_and_mark_dead.ml:174-221`).
    let item_count = match tag_info {
        TagInfo::Record(_) | TagInfo::RecordInlined(_) => tag_info.logical_field_count(),
        _ => items.len(),
    };
    if item_count < 2 {
        return false;
    }

    // Checked-in OCaml snapshots keep alias-bound deep constants inline, while
    // still materializing Strict/StrictOpt bindings and alias blocks with
    // computed payloads.
    !(property == LetKind::Alias
        && items
            .iter()
            .all(|item| is_deep_constant_block_binding_item(j, *item)))
}

fn is_deep_constant_block_binding_item(j: &JsArena, expr: Expr) -> bool {
    match j.ek(expr) {
        ExprKind::Number(_)
        | ExprKind::Str(_)
        | ExprKind::TemplateLiteral(_)
        | ExprKind::Bool(_)
        | ExprKind::Undefined { .. } => true,
        ExprKind::OptionalBlock(inner, _) => is_deep_constant_block_binding_item(j, inner),
        ExprKind::CamlBlock(items, MutableFlag::Immutable, _) => j
            .exprs(items)
            .iter()
            .all(|item| is_deep_constant_block_binding_item(j, *item)),
        _ => false,
    }
}

fn is_simple_block_binding_item(j: &JsArena, expr: Expr) -> bool {
    // Mirror OCaml's `js_pass_flatten_and_mark_dead.ml:188-193` "simple"
    // case: only `Var`, `Number`, `Str`, `Bool`, `Undefined` items stay
    // inline; everything else, including `Optional_block` and any
    // `Caml_block`, is hoisted into a fresh local binding.
    matches!(
        j.ek(expr),
        ExprKind::Var(_)
            | ExprKind::Qualified(_)
            | ExprKind::Number(_)
            | ExprKind::Str(_)
            | ExprKind::TemplateLiteral(_)
            | ExprKind::Bool(_)
            | ExprKind::Undefined { .. }
    )
}

fn is_simple_substituted_index_value(j: &JsArena, expr: Expr) -> bool {
    match j.ek(expr) {
        ExprKind::Var(_)
        | ExprKind::Qualified(_)
        | ExprKind::Number(_)
        | ExprKind::Str(_)
        | ExprKind::TemplateLiteral(_)
        | ExprKind::Undefined { .. } => true,
        ExprKind::CamlBlock(items, MutableFlag::Immutable, tag)
            if matches!(j.tag(tag), TagInfo::Constructor(_)) =>
        {
            j.exprs(items)
                .iter()
                .all(|item| is_simple_substituted_index_value(j, *item))
        }
        _ => false,
    }
}

fn block_substitution_name(ident: &Ident, tag_info: &TagInfo, index: usize) -> String {
    let suffix = match tag_info {
        TagInfo::Module(fields) => fields
            .get(index)
            .cloned()
            .unwrap_or_else(|| index.to_string()),
        TagInfo::Record(record) => record
            .fields
            .get(index)
            .map(|(field, _)| field.clone())
            .unwrap_or_else(|| index.to_string()),
        _ => index.to_string(),
    };
    format!("{}_{}", ident.name(), suffix)
}

pub(crate) fn max_ident_stamp_in_program(program: &Program) -> i32 {
    program.exports.iter().fold(
        max_ident_stamp_in_block(&program.arena, &program.block),
        |max_stamp, export| max_stamp.max(export.stamp()),
    )
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
    collect_mark_dead_states_block(
        &program.arena,
        &program.block,
        &program.export_set,
        &mut states,
    );
    let block = program.block.clone();
    apply_mark_dead_states_block(&mut program.arena, &block, &states);
}

fn collect_mark_dead_states_block(
    a: &JsArena,
    block: &[Stmt],
    export_set: &HashSet<Ident>,
    states: &mut HashMap<Ident, MarkDeadInfo>,
) {
    for stmt in block {
        collect_mark_dead_states_statement(a, *stmt, export_set, states);
    }
}

fn collect_mark_dead_states_list(
    a: &JsArena,
    block: StmtList,
    export_set: &HashSet<Ident>,
    states: &mut HashMap<Ident, MarkDeadInfo>,
) {
    collect_mark_dead_states_block(a, a.stmts(block), export_set, states);
}

fn collect_mark_dead_states_statement(
    a: &JsArena,
    stmt: Stmt,
    export_set: &HashSet<Ident>,
    states: &mut HashMap<Ident, MarkDeadInfo>,
) {
    match a.sk(stmt) {
        StmtKind::Block(block) => collect_mark_dead_states_list(a, block, export_set, states),
        StmtKind::Variable(decl) => {
            collect_mark_dead_states_variable(a, a.var(decl), export_set, states)
        }
        StmtKind::Exp(expr) | StmtKind::Return(expr) | StmtKind::Throw(expr) => {
            collect_mark_dead_states_expression(a, expr, states);
        }
        StmtKind::If(cond, then_block, else_block) => {
            collect_mark_dead_states_expression(a, cond, states);
            collect_mark_dead_states_list(a, then_block, export_set, states);
            collect_mark_dead_states_list(a, else_block, export_set, states);
        }
        StmtKind::While(_, cond, body) => {
            collect_mark_dead_states_expression(a, cond, states);
            collect_mark_dead_states_list(a, body, export_set, states);
        }
        StmtKind::ForRange(info) => {
            let info = a.for_range(info);
            if let Some(start) = info.init {
                collect_mark_dead_states_expression(a, start, states);
            }
            collect_mark_dead_states_expression(a, info.end, states);
            collect_mark_dead_states_list(a, info.body, export_set, states);
        }
        StmtKind::ForOf(info) | StmtKind::ForAwaitOf(info) => {
            let info = a.for_of(info);
            collect_mark_dead_states_expression(a, info.iterable, states);
            collect_mark_dead_states_list(a, info.body, export_set, states);
        }
        StmtKind::IntSwitch(test, info) => {
            collect_mark_dead_states_expression(a, test, states);
            let info = a.int_switch(info);
            for (_, clause) in &info.clauses {
                collect_mark_dead_states_list(a, clause.body, export_set, states);
            }
            if let Some(default) = info.default {
                collect_mark_dead_states_list(a, default, export_set, states);
            }
        }
        StmtKind::StringSwitch(test, info) => {
            collect_mark_dead_states_expression(a, test, states);
            let info = a.string_switch(info);
            for clause in &info.clauses {
                collect_mark_dead_states_list(a, clause.clause.body, export_set, states);
            }
            if let Some(default) = info.default {
                collect_mark_dead_states_list(a, default, export_set, states);
            }
        }
        StmtKind::Try(info) => {
            let info = a.try_info(info);
            collect_mark_dead_states_list(a, info.body, export_set, states);
            if let Some((_, block)) = info.catch {
                collect_mark_dead_states_list(a, block, export_set, states);
            }
            if let Some(block) = info.finally {
                collect_mark_dead_states_list(a, block, export_set, states);
            }
        }
        StmtKind::Debugger | StmtKind::Break(_) | StmtKind::Continue(_) => {}
    }
}

fn collect_mark_dead_states_variable(
    a: &JsArena,
    decl: &VarDecl,
    export_set: &HashSet<Ident>,
    states: &mut HashMap<Ident, MarkDeadInfo>,
) {
    match decl.ident_info.used_stats {
        UsedStats::DeadPure => return,
        UsedStats::DeadNonPure => {
            if let Some(value) = decl.value {
                collect_mark_dead_states_expression(a, value, states);
            }
            return;
        }
        _ => {}
    }

    let pure = match decl.value {
        None => true,
        Some(value) => {
            collect_mark_dead_states_expression(a, value, states);
            js_expr_no_side_effects(a, value)
        }
    };
    let exported = export_set.contains(&decl.ident);
    match states.get(&decl.ident).copied() {
        Some(MarkDeadInfo::Recursive) => {
            states.insert(
                decl.ident,
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
                decl.ident,
                MarkDeadInfo::Info {
                    pure,
                    used: false,
                    exported,
                },
            );
        }
    }
}

/// Every direct sub-expression of `expr`, in field order; function bodies
/// are returned separately.
fn expression_children(a: &JsArena, expr: Expr, out: &mut Vec<Expr>) -> Option<StmtList> {
    match a.ek(expr) {
        ExprKind::Var(_)
        | ExprKind::Qualified(_)
        | ExprKind::Undefined { .. }
        | ExprKind::Null
        | ExprKind::Bool(_)
        | ExprKind::Str(_)
        | ExprKind::TemplateLiteral(_)
        | ExprKind::JsonLiteral(_)
        | ExprKind::RawJsCode(_)
        | ExprKind::Number(_) => {}
        ExprKind::Length(inner, _)
        | ExprKind::IsNullOrUndefined(inner)
        | ExprKind::Typeof(inner)
        | ExprKind::JsNot(inner)
        | ExprKind::JsBnot(inner)
        | ExprKind::CamlBlockTag(inner, _)
        | ExprKind::OptionalBlock(inner, _)
        | ExprKind::Await(inner)
        | ExprKind::Spread(inner)
        | ExprKind::RecordRest(_, inner)
        | ExprKind::StaticIndex(inner, _, _) => out.push(inner),
        ExprKind::StringAppend(left, right)
        | ExprKind::In(left, right)
        | ExprKind::Seq(left, right)
        | ExprKind::Bin(_, left, right)
        | ExprKind::FlatCall(left, right)
        | ExprKind::StringIndex(left, right)
        | ExprKind::ArrayIndex(left, right) => {
            out.push(left);
            out.push(right);
        }
        ExprKind::Cond(test, consequent, alternate) => {
            out.extend([test, consequent, alternate]);
        }
        ExprKind::Call(func, args, _) | ExprKind::TaggedTemplate(func, _, args) => {
            out.push(func);
            out.extend_from_slice(a.exprs(args));
        }
        ExprKind::InterpolatedTemplate(_, values) => out.extend_from_slice(a.exprs(values)),
        ExprKind::New(target, args) => {
            out.push(target);
            if let Some(args) = args {
                out.extend_from_slice(a.exprs(args));
            }
        }
        ExprKind::Fun(f) => return Some(a.fun(f).body),
        ExprKind::Array(items, _) | ExprKind::CamlBlock(items, _, _) => {
            out.extend_from_slice(a.exprs(items))
        }
        ExprKind::Object(dup, props) => {
            out.extend(dup);
            out.extend(a.props(props).iter().map(|(_, value)| *value));
        }
    }
    None
}

fn collect_mark_dead_states_expression(
    a: &JsArena,
    expr: Expr,
    states: &mut HashMap<Ident, MarkDeadInfo>,
) {
    if let ExprKind::Var(id) = a.ek(expr) {
        mark_dead_ident_use(&a.ident(id), states);
        return;
    }
    let mut children = Vec::new();
    if let Some(body) = expression_children(a, expr, &mut children) {
        for stmt in a.stmts(body) {
            collect_mark_dead_states_statement(a, *stmt, &HashSet::new(), states);
        }
        return;
    }
    for child in children {
        collect_mark_dead_states_expression(a, child, states);
    }
}

fn mark_dead_ident_use(id: &Ident, states: &mut HashMap<Ident, MarkDeadInfo>) {
    match states.get_mut(id) {
        None => {
            states.insert(*id, MarkDeadInfo::Recursive);
        }
        Some(MarkDeadInfo::Recursive) => {}
        Some(MarkDeadInfo::Info { used, .. }) => {
            *used = true;
        }
    }
}

fn apply_mark_dead_states_block(
    j: &mut JsArena,
    block: &[Stmt],
    states: &HashMap<Ident, MarkDeadInfo>,
) {
    for stmt in block {
        apply_mark_dead_states_statement(j, *stmt, states);
    }
}

fn apply_mark_dead_states_list(
    j: &mut JsArena,
    block: StmtList,
    states: &HashMap<Ident, MarkDeadInfo>,
) {
    let block = j.block_vec(block);
    apply_mark_dead_states_block(j, &block, states);
}

fn apply_mark_dead_states_statement(
    j: &mut JsArena,
    stmt: Stmt,
    states: &HashMap<Ident, MarkDeadInfo>,
) {
    match j.sk(stmt) {
        StmtKind::Block(block) => apply_mark_dead_states_list(j, block, states),
        StmtKind::Variable(decl) => {
            apply_mark_dead_states_variable(j, decl, states);
            if let Some(value) = j.var(decl).value {
                apply_mark_dead_states_expression(j, value, states);
            }
        }
        StmtKind::Exp(expr) | StmtKind::Return(expr) | StmtKind::Throw(expr) => {
            apply_mark_dead_states_expression(j, expr, states);
        }
        StmtKind::If(_, then_block, else_block) => {
            apply_mark_dead_states_list(j, then_block, states);
            apply_mark_dead_states_list(j, else_block, states);
        }
        StmtKind::While(_, _, body) => apply_mark_dead_states_list(j, body, states),
        StmtKind::ForRange(info) => {
            let body = j.for_range(info).body;
            apply_mark_dead_states_list(j, body, states)
        }
        StmtKind::ForOf(info) | StmtKind::ForAwaitOf(info) => {
            let body = j.for_of(info).body;
            apply_mark_dead_states_list(j, body, states)
        }
        StmtKind::IntSwitch(_, info) => {
            let info = j.int_switch(info).clone();
            for (_, clause) in &info.clauses {
                apply_mark_dead_states_list(j, clause.body, states);
            }
            if let Some(default) = info.default {
                apply_mark_dead_states_list(j, default, states);
            }
        }
        StmtKind::StringSwitch(_, info) => {
            let bodies: Vec<StmtList> = j
                .string_switch(info)
                .clauses
                .iter()
                .map(|clause| clause.clause.body)
                .collect();
            let default = j.string_switch(info).default;
            for body in bodies {
                apply_mark_dead_states_list(j, body, states);
            }
            if let Some(default) = default {
                apply_mark_dead_states_list(j, default, states);
            }
        }
        StmtKind::Try(info) => {
            let info = j.try_info(info);
            apply_mark_dead_states_list(j, info.body, states);
            if let Some((_, block)) = info.catch {
                apply_mark_dead_states_list(j, block, states);
            }
            if let Some(block) = info.finally {
                apply_mark_dead_states_list(j, block, states);
            }
        }
        StmtKind::Debugger | StmtKind::Break(_) | StmtKind::Continue(_) => {}
    }
}

fn apply_mark_dead_states_variable(
    j: &mut JsArena,
    decl: crate::js_ir::arena::VarId,
    states: &HashMap<Ident, MarkDeadInfo>,
) {
    let Some(MarkDeadInfo::Info {
        pure,
        used,
        exported,
    }) = states.get(&j.var(decl).ident).copied()
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
    update_used_stats(j.var_ident_info_mut(decl), status);
}

fn apply_mark_dead_states_expression(
    j: &mut JsArena,
    expr: Expr,
    states: &HashMap<Ident, MarkDeadInfo>,
) {
    let mut children = Vec::new();
    if let Some(body) = expression_children(j, expr, &mut children) {
        apply_mark_dead_states_list(j, body, states);
        return;
    }
    for child in children {
        apply_mark_dead_states_expression(j, child, states);
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

// ---- js_pass_flatten ------------------------------------------------------

/// `js_pass_flatten.ml`.
struct Flatten;

fn flatten_block(j: &mut JsArena, block: &[Stmt]) -> Block {
    Flatten.block_items(j, block)
}

impl Mapper for Flatten {
    fn block_items(&mut self, j: &mut JsArena, block: &[Stmt]) -> Vec<Stmt> {
        let mut flattened = Vec::new();
        for stmt in block {
            let stmt = self.statement(j, *stmt);
            match j.sk(stmt) {
                StmtKind::Block(inner) => flattened.extend_from_slice(j.stmts(inner)),
                _ => flattened.push(stmt),
            }
        }
        flattened
    }

    fn statement(&mut self, j: &mut JsArena, stmt: Stmt) -> Stmt {
        let cold = j.stmt_cold(stmt);
        match j.sk(stmt) {
            StmtKind::Exp(expr) => match j.ek(expr) {
                ExprKind::Seq(_, _) => {
                    let block = flatten_sequence_statements(self, j, expr);
                    // OCaml uses `S.block` here, not a raw `Block`
                    // (compiler/core/js_pass_flatten.ml:43-47), so a single
                    // empty flattened effect is normalized before printing.
                    S::block(&block, j)
                }
                ExprKind::CamlBlock(args, _, _) => {
                    let args = j.expr_vec(args);
                    let block: Vec<Stmt> = args
                        .into_iter()
                        .map(|arg| {
                            let s = S::exp(arg, j);
                            self.statement(j, s)
                        })
                        .collect();
                    // OCaml's Caml_block flattening also goes through
                    // `S.block` (compiler/core/js_pass_flatten.ml:48-53).
                    S::block(&block, j)
                }
                ExprKind::Cond(test, consequent, alternate) => {
                    // js_pass_flatten.ml:54-61 / 79-86 take the condition
                    // expression's `source_loc`. OCaml keeps the conditional
                    // predicate untouched here; only the consequent/alternate
                    // are re-entered as statements.
                    let c = S::exp(consequent, j);
                    let c = self.statement(j, c);
                    let a = S::exp(alternate, j);
                    let a = self.statement(j, a);
                    let (c, a) = (j.stmt_list(&[c]), j.stmt_list(&[a]));
                    let loc = j.expr_loc(expr);
                    j.stmt_with(
                        StmtKind::If(test, c, a),
                        crate::js_ir::arena::Cold {
                            comment: cold.comment,
                            source_loc: loc,
                        },
                    )
                }
                ExprKind::Bin(BinOp::Eq, target, value)
                    if matches!(j.ek(value), ExprKind::Seq(_, _)) =>
                {
                    let mut exprs = Vec::new();
                    flatten_sequence_expressions(j, value, &mut exprs);
                    let last = exprs
                        .pop()
                        .expect("sequence flattening must produce at least one expression");
                    let mut block: Block = exprs
                        .into_iter()
                        .map(|expr| {
                            let s = S::exp(expr, j);
                            self.statement(j, s)
                        })
                        .collect();
                    let assign = E::bin(BinOp::Eq, target, last, j);
                    let assign = S::exp(assign, j);
                    block.push(self.statement(j, assign));
                    // Match OCaml's `S.block` in
                    // compiler/core/js_pass_flatten.ml:63-77.
                    S::block(&block, j)
                }
                _ => {
                    let e = self.expression(j, expr);
                    j.rekind_stmt(stmt, StmtKind::Exp(e))
                }
            },
            StmtKind::Return(expr) => match j.ek(expr) {
                ExprKind::Cond(test, consequent, alternate) => {
                    // Same predicate preservation as OCaml's Return(Cond)
                    // flatten arm (compiler/core/js_pass_flatten.ml:79-86).
                    let c = S::return_(consequent, j);
                    let c = self.statement(j, c);
                    let a = S::return_(alternate, j);
                    let a = self.statement(j, a);
                    let (c, a) = (j.stmt_list(&[c]), j.stmt_list(&[a]));
                    let loc = j.expr_loc(expr);
                    j.stmt_with(
                        StmtKind::If(test, c, a),
                        crate::js_ir::arena::Cold {
                            comment: cold.comment,
                            source_loc: loc,
                        },
                    )
                }
                ExprKind::Seq(_, _) => {
                    let mut exprs = Vec::new();
                    flatten_sequence_expressions(j, expr, &mut exprs);
                    let last = exprs
                        .pop()
                        .expect("return sequence flattening must produce at least one expression");
                    let mut block: Block = exprs
                        .into_iter()
                        .map(|expr| {
                            let s = S::exp(expr, j);
                            self.statement(j, s)
                        })
                        .collect();
                    let ret = S::return_(last, j);
                    block.push(self.statement(j, ret));
                    // OCaml wraps the flattened return sequence with
                    // `S.block` before applying `super.statement`
                    // (compiler/core/js_pass_flatten.ml:88-96).
                    S::block(&block, j)
                }
                _ => {
                    let e = self.expression(j, expr);
                    j.rekind_stmt(stmt, StmtKind::Return(e))
                }
            },
            StmtKind::Block(block) if j.stmts(block).len() == 1 => {
                let inner = j.stmts(block)[0];
                self.statement(j, inner)
            }
            _ => map_statement_children(self, j, stmt),
        }
    }
}

fn flatten_sequence_statements(f: &mut Flatten, j: &mut JsArena, expr: Expr) -> Block {
    let mut exprs = Vec::new();
    flatten_sequence_expressions(j, expr, &mut exprs);
    exprs
        .into_iter()
        .map(|expr| {
            let s = S::exp(expr, j);
            f.statement(j, s)
        })
        .collect()
}

fn flatten_sequence_expressions(j: &mut JsArena, expr: Expr, out: &mut Vec<Expr>) {
    match j.ek(expr) {
        ExprKind::Seq(left, right) => {
            flatten_sequence_expressions(j, left, out);
            flatten_sequence_expressions(j, right, out);
        }
        _ => out.push(expr),
    }
}
