//! JS IR pass: tailcall inlining.
//!
//! Inlines single-use pure function bindings at their return-position call
//! sites, eliminating the intermediate function wrapper. Also tracks used/dead
//! status for variable declarations.

use ahash::{AHashMap as HashMap, AHashSet as HashSet};

use crate::ident::Ident;
use crate::js_ir::BinOp;
use crate::js_ir::arena::{
    Block, Expr, ExprKind, FunInfo, IdentList, JsArena, JsDepsProgram as DepsProgram,
    JsProgram as Program, Stmt, StmtKind, StmtList, StringClauseInfo, VarDecl,
};
use crate::js_ir::build::stmt as S;
use crate::js_ir::op::UsedStats;
use crate::js_ir::walk::{
    Mapper, Visitor, each_child, map_expression_children, map_statement_children, walk_block,
};
use crate::lambda::js_pass_external_shadow::is_lexical_binding_kind;
use crate::lambda::lam_compat::LetKind;

use super::js_exp_make::js_expr_no_side_effects;

pub(crate) fn apply_js_tailcall_inline_pass(mut deps: DepsProgram) -> DepsProgram {
    tailcall_inline_program(&mut deps.program);
    deps
}

fn tailcall_inline_program(program: &mut Program) {
    let mut inliner = TailcallInlineState::new(program);
    let block = std::mem::take(&mut program.block);
    program.block = inliner.block_items(&mut program.arena, &block);
    let block = program.block.clone();
    update_declaration_infos(&mut program.arena, &block, &mut |ident, info| {
        if let Some(status) = inliner.statuses.get(&ident).copied() {
            info.used_stats = status;
        }
    });
}

/// Updates the `ident_info` of every declaration reachable through the
/// statement positions the OCaml stats passes visit (blocks, initializers and
/// function bodies; not loop or branch conditions).
pub(crate) fn update_declaration_infos(
    j: &mut JsArena,
    block: &[Stmt],
    f: &mut impl FnMut(Ident, &mut crate::js_ir::op::IdentInfo),
) {
    fn list(
        j: &mut JsArena,
        l: StmtList,
        f: &mut impl FnMut(Ident, &mut crate::js_ir::op::IdentInfo),
    ) {
        // Index the arena list instead of copying it: `f` only touches
        // declaration infos, never the list pools.
        for i in 0..j.stmts(l).len() {
            let stmt = j.stmts(l)[i];
            update_declaration_infos(j, std::slice::from_ref(&stmt), f);
        }
    }
    fn expr(j: &mut JsArena, e: Expr, f: &mut impl FnMut(Ident, &mut crate::js_ir::op::IdentInfo)) {
        // Collect the outermost function bodies of `e`; their statements are
        // visited (with their own nested functions) below.
        let mut bodies = Vec::new();
        collect_outer_fun_bodies(j, e, &mut bodies);
        for body in bodies {
            list(j, body, f);
        }
    }
    for stmt in block {
        match j.sk(*stmt) {
            StmtKind::Block(b) => list(j, b, f),
            StmtKind::Variable(v) => {
                let ident = j.var(v).ident;
                f(ident, j.var_ident_info_mut(v));
                if let Some(value) = j.var(v).value {
                    expr(j, value, f);
                }
            }
            StmtKind::Exp(e) | StmtKind::Return(e) | StmtKind::Throw(e) => expr(j, e, f),
            StmtKind::If(_, t, e) => {
                list(j, t, f);
                list(j, e, f);
            }
            StmtKind::While(_, _, body) => list(j, body, f),
            StmtKind::ForRange(info) => {
                let body = j.for_range(info).body;
                list(j, body, f)
            }
            StmtKind::ForOf(info) | StmtKind::ForAwaitOf(info) => {
                let body = j.for_of(info).body;
                list(j, body, f)
            }
            StmtKind::IntSwitch(_, info) => {
                let info = j.int_switch(info).clone();
                for (_, clause) in &info.clauses {
                    list(j, clause.body, f);
                }
                if let Some(d) = info.default {
                    list(j, d, f);
                }
            }
            StmtKind::StringSwitch(_, info) => {
                let bodies: Vec<StmtList> = j
                    .string_switch(info)
                    .clauses
                    .iter()
                    .map(|c| c.clause.body)
                    .collect();
                let default = j.string_switch(info).default;
                for b in bodies {
                    list(j, b, f);
                }
                if let Some(d) = default {
                    list(j, d, f);
                }
            }
            StmtKind::Try(info) => {
                let info = j.try_info(info);
                list(j, info.body, f);
                if let Some((_, b)) = info.catch {
                    list(j, b, f);
                }
                if let Some(b) = info.finally {
                    list(j, b, f);
                }
            }
            StmtKind::Debugger | StmtKind::Break(_) | StmtKind::Continue(_) => {}
        }
    }
}

/// The bodies of the functions in `e` that are not nested in another
/// function of `e`, in traversal order.
fn collect_outer_fun_bodies(a: &JsArena, e: Expr, out: &mut Vec<StmtList>) {
    if let ExprKind::Fun(f) = a.ek(e) {
        out.push(a.fun(f).body);
        return;
    }
    each_child(a, e, |child| collect_outer_fun_bodies(a, child, out));
}

#[derive(Debug)]
struct TailcallInlineState {
    inline_decls: HashMap<Ident, InlineFunctionDecl>,
    /// Functions called by the final `return f(...)` of some block: the only
    /// calls `try_inline_single_return_statement` can inline, so the only
    /// declarations whose bodies are worth keeping in `inline_decls`.
    tail_callees: HashSet<Ident>,
    statuses: HashMap<Ident, UsedStats>,
    active_decls: Vec<Ident>,
}

/// An inlineable function declaration: handles to its parameters and body,
/// shared with the declaration itself.
#[derive(Debug, Clone, Copy)]
struct InlineFunctionDecl {
    params: IdentList,
    body: StmtList,
}

impl TailcallInlineState {
    fn new(program: &Program) -> Self {
        let a = &program.arena;
        let mut counter = UseCounts::default();
        walk_block(&mut counter, a, &program.block);
        let UseCounts { decls, counts } = counter;

        let mut statuses = HashMap::with_capacity(decls.len());
        for (ident, pure) in &decls {
            let count = counts.get(ident).copied().unwrap_or(0);
            let exported = program.export_set.contains(ident);
            let status = if exported {
                UsedStats::Exported
            } else if count == 0 {
                if *pure {
                    UsedStats::DeadPure
                } else {
                    UsedStats::DeadNonPure
                }
            } else if count == 1 && *pure {
                UsedStats::OncePure
            } else {
                UsedStats::Used
            };
            statuses.insert(*ident, status);
        }

        // OCaml's stats table keeps the existing variable declarations by
        // pointer (`compiler/core/js_pass_get_used.ml:55-77`) and the tailcall
        // pass only needs function bodies for the Once_pure inline branch
        // (`compiler/core/js_pass_tailcall_inline.ml:160-192`).
        let tail_callees = collect_tail_callees(a, &program.block);
        let mut collector = OncePureDecls {
            statuses: &statuses,
            tail_callees: &tail_callees,
            inline_decls: HashMap::new(),
        };
        walk_block(&mut collector, a, &program.block);
        let inline_decls = collector.inline_decls;

        Self {
            inline_decls,
            tail_callees,
            statuses,
            active_decls: Vec::new(),
        }
    }

    fn transform_statement(&mut self, j: &mut JsArena, stmt: Stmt) -> Option<Stmt> {
        let StmtKind::Variable(v) = j.sk(stmt) else {
            return Some(map_statement_children(self, j, stmt));
        };
        let mut decl = j.var(v).clone();
        if let Some(value) = decl.value {
            self.active_decls.push(decl.ident);
            decl.value = Some(self.expression(j, value));
            self.active_decls.pop();
        }

        let status = self
            .statuses
            .get(&decl.ident)
            .copied()
            .unwrap_or(UsedStats::Used);
        // OCaml rewrites a variable declaration first, then stores the
        // rewritten declaration back into the stats table
        // (`compiler/core/js_pass_tailcall_inline.ml:120-129`).
        if status == UsedStats::OncePure
            && self.tail_callees.contains(&decl.ident)
            && let Some(inline_decl) = inline_function_decl_from_variable(j, &decl)
        {
            self.inline_decls.insert(decl.ident, inline_decl);
        }
        decl.ident_info.used_stats = status;
        match status {
            UsedStats::DeadPure => None,
            UsedStats::DeadNonPure => decl
                .value
                .map(|value| j.rekind_stmt(stmt, StmtKind::Exp(value))),
            _ => {
                let v = j.var_id(decl);
                Some(j.rekind_stmt(stmt, StmtKind::Variable(v)))
            }
        }
    }

    fn try_inline_single_return_statement(&mut self, j: &mut JsArena, stmt: Stmt) -> Option<Block> {
        let StmtKind::Return(expr) = j.sk(stmt) else {
            return None;
        };
        let ExprKind::Call(func, args, _) = j.ek(expr) else {
            return None;
        };
        match j.ek(func) {
            ExprKind::Var(id) => self.inline_named_call(j, &j.ident(id), args),
            ExprKind::Fun(f) => {
                let info = j.fun(f);
                if !info.is_method
                    && !info.async_
                    && info.directive.is_none()
                    && j.ident_slice(info.params).len() == j.exprs(args).len()
                {
                    Some(self.inline_function_call(j, info.params, info.body, args))
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    fn inline_named_call(
        &mut self,
        j: &mut JsArena,
        ident: &Ident,
        args: crate::js_ir::arena::ExprList,
    ) -> Option<Block> {
        if self.statuses.get(ident).copied() != Some(UsedStats::OncePure) {
            return None;
        }
        // OCaml keeps the transformed declaration in the stats table while
        // walking blocks, which avoids consuming a recursive function while
        // traversing its own body (`compiler/core/js_pass_tailcall_inline.ml:81-105`,
        // `compiler/core/js_pass_tailcall_inline.ml:120-129`). Only inline the
        // stored declaration at an outer tail-call site (`compiler/core/js_pass_tailcall_inline.ml:150-192`).
        if self.active_decls.iter().any(|active| active.same(ident)) {
            return None;
        }

        // `when Ext_list.same_length params args` (js_pass_tailcall_inline.ml:185)
        // is checked against the stored declaration without consuming it.
        let decl = *self.inline_decls.get(ident)?;
        if j.ident_slice(decl.params).len() != j.exprs(args).len() {
            return None;
        }
        self.inline_decls.remove(ident);

        self.statuses.insert(*ident, UsedStats::DeadPure);
        Some(self.inline_function_call(j, decl.params, decl.body, args))
    }

    fn inline_function_call(
        &mut self,
        j: &mut JsArena,
        params: IdentList,
        body: StmtList,
        args: crate::js_ir::arena::ExprList,
    ) -> Block {
        // OCaml re-transforms the stored, already transformed body at the
        // call site (`compiler/core/js_pass_tailcall_inline.ml:186-192`).
        let body = j.block_vec(body);
        let processed_body = self.block_items(j, &body);
        let params = j.ident_slice(params).to_vec();
        let immutable_mask = immutable_param_mask(j, &params, &processed_body);
        let args = j.expr_vec(args);
        let args: Vec<Expr> = args
            .into_iter()
            .map(|arg| self.expression(j, arg))
            .collect();
        inline_tailcall_call(j, &immutable_mask, &params, args, processed_body)
    }
}

impl Mapper for TailcallInlineState {
    fn block(&mut self, j: &mut JsArena, block: StmtList) -> StmtList {
        crate::js_ir::walk::map_block_with_items(self, j, block)
    }

    fn block_items(&mut self, j: &mut JsArena, block: &[Stmt]) -> Vec<Stmt> {
        let len = block.len();
        let mut transformed = Vec::with_capacity(len);
        for (index, stmt) in block.iter().enumerate() {
            // OCaml recurses as `x :: xs -> self.statement x :: self.block xs`
            // before matching the one-statement tail-call inline case
            // (`compiler/core/js_pass_tailcall_inline.ml:130-159,232`).
            // Check the final suffix after preceding declarations have updated
            // `inline_decls`, so `let aux; return aux(...)` can inline.
            if index + 1 == len
                && let Some(inlined) = self.try_inline_single_return_statement(j, *stmt)
            {
                transformed.extend(inlined);
                continue;
            }
            transformed.extend(self.transform_statement(j, *stmt));
        }
        transformed
    }
}

/// Counts the uses of each local and records each declaration's purity.
#[derive(Default)]
struct UseCounts {
    decls: HashMap<Ident, bool>,
    counts: HashMap<Ident, usize>,
}

impl Visitor for UseCounts {
    fn visit_expression(&mut self, a: &JsArena, e: Expr) {
        if let ExprKind::Var(id) = a.ek(e) {
            *self.counts.entry(a.ident(id)).or_insert(0) += 1;
        }
    }

    fn visit_declaration(&mut self, a: &JsArena, decl: &VarDecl) {
        self.decls.insert(
            decl.ident,
            decl.value.is_some_and(|v| js_expr_no_side_effects(a, v)),
        );
    }
}

fn inline_function_decl_from_variable(a: &JsArena, decl: &VarDecl) -> Option<InlineFunctionDecl> {
    if !is_lexical_binding_kind(decl.property) {
        return None;
    }
    let ExprKind::Fun(f) = a.ek(decl.value?) else {
        return None;
    };
    let FunInfo {
        is_method,
        params,
        body,
        async_,
        directive,
        ..
    } = a.fun(f);
    (!is_method && !async_ && directive.is_none()).then_some(InlineFunctionDecl { params, body })
}

struct OncePureDecls<'s> {
    statuses: &'s HashMap<Ident, UsedStats>,
    tail_callees: &'s HashSet<Ident>,
    inline_decls: HashMap<Ident, InlineFunctionDecl>,
}

impl Visitor for OncePureDecls<'_> {
    fn visit_declaration(&mut self, a: &JsArena, decl: &VarDecl) {
        if self.statuses.get(&decl.ident).copied() == Some(UsedStats::OncePure)
            && self.tail_callees.contains(&decl.ident)
            && let Some(inline_decl) = inline_function_decl_from_variable(a, decl)
        {
            self.inline_decls.insert(decl.ident, inline_decl);
        }
    }
}

fn immutable_param_mask(a: &JsArena, params: &[Ident], body: &[Stmt]) -> Vec<bool> {
    params
        .iter()
        .map(|param| !block_assigns_ident(a, body, param))
        .collect()
}

fn block_assigns_ident(a: &JsArena, block: &[Stmt], ident: &Ident) -> bool {
    struct Assigns<'i> {
        ident: &'i Ident,
        found: bool,
    }
    impl Visitor for Assigns<'_> {
        fn visit_expression(&mut self, a: &JsArena, e: Expr) {
            if let ExprKind::Bin(BinOp::Eq, left, _) = a.ek(e)
                && let ExprKind::Var(lhs) = a.ek(left)
                && a.ident(lhs).same(self.ident)
            {
                self.found = true;
            }
        }
        fn done(&self) -> bool {
            self.found
        }
    }
    let mut assigns = Assigns {
        ident,
        found: false,
    };
    walk_block(&mut assigns, a, block);
    assigns.found
}

fn inline_tailcall_call(
    j: &mut JsArena,
    immutable_mask: &[bool],
    params: &[Ident],
    args: Vec<Expr>,
    body: Block,
) -> Block {
    let mut bindings = Vec::new();
    let mut substitution = HashMap::new();

    for ((param, arg), immutable) in params
        .iter()
        .copied()
        .zip(args)
        .zip(immutable_mask.iter().copied())
    {
        if immutable && let ExprKind::Var(id) = j.ek(arg) {
            substitution.insert(param, j.ident(id));
            continue;
        }

        bindings.push(S::define(param, Some(arg), LetKind::Variable, j));
    }

    let body = if substitution.is_empty() {
        body
    } else {
        SubstituteInline { substitution }.block_items(j, &body)
    };

    bindings.into_iter().chain(body).collect()
}

/// Renames inlined parameters, respecting shadowing by inner bindings.
struct SubstituteInline {
    substitution: HashMap<Ident, Ident>,
}

impl SubstituteInline {
    /// Maps `block` with `shadowed` removed from the substitution.
    fn pruned_block(&mut self, j: &mut JsArena, block: StmtList, shadowed: &[Ident]) -> StmtList {
        let saved = self.substitution.clone();
        for ident in shadowed {
            self.substitution.remove(ident);
        }
        let block = self.block(j, block);
        self.substitution = saved;
        block
    }
}

impl Mapper for SubstituteInline {
    fn block(&mut self, j: &mut JsArena, block: StmtList) -> StmtList {
        crate::js_ir::walk::map_block_with_items(self, j, block)
    }

    fn block_items(&mut self, j: &mut JsArena, block: &[Stmt]) -> Vec<Stmt> {
        let saved = self.substitution.clone();
        let mut rewritten = Vec::with_capacity(block.len());
        for stmt in block {
            let stmt = self.statement(j, *stmt);
            if let StmtKind::Variable(v) = j.sk(stmt) {
                let ident = j.var(v).ident;
                self.substitution.remove(&ident);
            }
            rewritten.push(stmt);
        }
        self.substitution = saved;
        rewritten
    }

    fn statement(&mut self, j: &mut JsArena, stmt: Stmt) -> Stmt {
        match j.sk(stmt) {
            StmtKind::ForRange(id) => {
                let info = j.for_range(id);
                let init = info.init.map(|e| self.expression(j, e));
                let end = self.expression(j, info.end);
                let ident = j.ident(info.ident);
                let body = self.pruned_block(j, info.body, &[ident]);
                let id = j.for_range_id(crate::js_ir::arena::ForRangeInfo {
                    init,
                    end,
                    body,
                    ..info
                });
                j.rekind_stmt(stmt, StmtKind::ForRange(id))
            }
            StmtKind::ForOf(id) | StmtKind::ForAwaitOf(id) => {
                let info = j.for_of(id);
                let iterable = self.expression(j, info.iterable);
                let ident = j.ident(info.ident);
                let body = self.pruned_block(j, info.body, &[ident]);
                let new = j.for_of_id(crate::js_ir::arena::ForOfInfo {
                    iterable,
                    body,
                    ..info
                });
                let kind = if matches!(j.sk(stmt), StmtKind::ForOf(_)) {
                    StmtKind::ForOf(new)
                } else {
                    StmtKind::ForAwaitOf(new)
                };
                j.rekind_stmt(stmt, kind)
            }
            StmtKind::StringSwitch(test, id) => {
                let test = self.expression(j, test);
                let info = j.string_switch(id).clone();
                let clauses = info
                    .clauses
                    .iter()
                    .map(|c| {
                        let body = self.block(j, c.clause.body);
                        StringClauseInfo {
                            tag_type: c.tag_type.clone(),
                            clause: crate::js_ir::arena::Clause {
                                body,
                                source_loc: None,
                                ..c.clause
                            },
                        }
                    })
                    .collect();
                let default = info.default.map(|d| self.block(j, d));
                let id =
                    j.string_switch_id(crate::js_ir::arena::StringSwitchInfo { clauses, default });
                j.rekind_stmt(stmt, StmtKind::StringSwitch(test, id))
            }
            StmtKind::Try(id) => {
                let info = j.try_info(id);
                let body = self.block(j, info.body);
                let catch = info.catch.map(|(ident, b)| {
                    let shadow = j.ident(ident);
                    (ident, self.pruned_block(j, b, &[shadow]))
                });
                let finally = info.finally.map(|b| self.block(j, b));
                let id = j.try_id(crate::js_ir::arena::TryInfo {
                    body,
                    catch,
                    finally,
                });
                j.rekind_stmt(stmt, StmtKind::Try(id))
            }
            _ => map_statement_children(self, j, stmt),
        }
    }

    fn expression(&mut self, j: &mut JsArena, expr: Expr) -> Expr {
        match j.ek(expr) {
            ExprKind::Var(id) => match self.substitution.get(&j.ident(id)).copied() {
                Some(target) => {
                    let target = j.ident_id(target);
                    j.rekind_expr(expr, ExprKind::Var(target))
                }
                None => expr,
            },
            ExprKind::Fun(f) => {
                let info = j.fun(f);
                let params = j.ident_slice(info.params).to_vec();
                let body = self.pruned_block(j, info.body, &params);
                if body == info.body {
                    return expr;
                }
                let f = j.fun_id(FunInfo { body, ..info });
                j.rekind_expr(expr, ExprKind::Fun(f))
            }
            _ => map_expression_children(self, j, expr),
        }
    }
}

/// Callees of the final `return f(...)` statement of every block.
fn collect_tail_callees(a: &JsArena, block: &[Stmt]) -> HashSet<Ident> {
    struct TailCallees(HashSet<Ident>);
    impl Visitor for TailCallees {
        fn visit_block(&mut self, a: &JsArena, block: &[Stmt]) {
            if let Some(last) = block.last()
                && let StmtKind::Return(e) = a.sk(*last)
                && let ExprKind::Call(func, _, _) = a.ek(e)
                && let ExprKind::Var(id) = a.ek(func)
            {
                self.0.insert(a.ident(id));
            }
        }
    }
    let mut callees = TailCallees(HashSet::new());
    walk_block(&mut callees, a, block);
    callees.0
}

#[cfg(test)]
mod source_loc_tests {
    use super::*;
    use crate::js_ir::build::exp as E;

    #[test]
    fn int_switch_clause_keeps_source_loc() {
        // Js_record_map (js_record_map.ml:200-202) rebuilds case clauses with
        // their original `source_loc`.
        let mut j = JsArena::new();
        let mut clause = S::clause(&[], true, &mut j);
        clause.source_loc = Some(crate::lambda::LamLoc::NONE);
        let zero = E::int(0, &mut j);
        // Built raw: `S::int_switch` would fold the literal scrutinee.
        let info = j.int_switch_id(crate::js_ir::arena::IntSwitchInfo {
            clauses: vec![(0, clause)],
            default: None,
        });
        let switch = j.stmt(StmtKind::IntSwitch(zero, info));
        let mut program = Program {
            arena: j,
            block: vec![switch],
            exports: vec![],
            export_set: Default::default(),
            name_reservations: vec![],
        };

        tailcall_inline_program(&mut program);

        let a = &program.arena;
        let StmtKind::IntSwitch(_, info) = a.sk(program.block[0]) else {
            panic!("expected an int switch");
        };
        assert!(a.int_switch(info).clauses[0].1.source_loc.is_some());
    }
}
