//! Rewrite JS globals shadowed by bindings in their actual lexical scope.
use crate::ident::Ident;
use crate::js_ir::arena::*;
use crate::js_ir::build::exp as E;
use crate::js_ir::printer::convert_ident_name;
use crate::js_ir::walk::{Mapper, Visitor, map_expression_children, map_statement_children};
use ahash::{AHashMap as HashMap, AHashSet as HashSet};

pub(crate) fn apply_external_shadow_pass(mut deps: JsDepsProgram) -> JsDepsProgram {
    let mut names = ReferencedNames::default();
    crate::js_ir::walk::walk_block(&mut names, &deps.program.arena, &deps.program.block);
    if names.globals.is_empty() {
        return deps;
    }
    let mut scope = Scope {
        globals: names.globals,
        counts: HashMap::default(),
        log: Vec::new(),
    };
    for module in &names.imported_modules {
        scope.add_binding(module);
    }
    if scope.log.is_empty()
        && !names
            .bindings
            .iter()
            .any(|name| scope.globals.contains(name))
    {
        return deps;
    }
    let block = std::mem::take(&mut deps.program.block);
    deps.program.block = scope.block_items(&mut deps.program.arena, &block);
    deps
}

struct Scope {
    globals: HashSet<String>,
    counts: HashMap<String, u32>,
    log: Vec<String>,
}

pub(crate) fn is_js_global(id: &Ident) -> bool {
    id.is_js() || (id.is_global() && id.stamp() == 0)
}

fn printed_binding_name(ident: &Ident) -> Option<String> {
    (!ident.is_js()).then(|| convert_ident_name(ident.name()))
}

impl Scope {
    fn add_binding(&mut self, ident: &Ident) {
        if let Some(name) = printed_binding_name(ident)
            && self.globals.contains(&name)
        {
            *self.counts.entry(name.clone()).or_default() += 1;
            self.log.push(name);
        }
    }
    fn in_scope(&self, name: &str) -> bool {
        self.counts.get(name).is_some_and(|count| *count > 0)
    }
    fn enter(&self) -> usize {
        self.log.len()
    }
    fn leave(&mut self, mark: usize) {
        while self.log.len() > mark {
            let name = self.log.pop().expect("scope entry");
            *self.counts.get_mut(&name).expect("scope count") -= 1;
        }
    }
    fn add_declarations(&mut self, j: &JsArena, block: &[Stmt]) {
        for stmt in block {
            if let StmtKind::Variable(decl) = j.sk(*stmt) {
                self.add_binding(&j.var(decl).ident);
            }
        }
    }
    fn add_switch_declarations(
        &mut self,
        j: &JsArena,
        bodies: impl Iterator<Item = StmtList>,
        default: Option<StmtList>,
    ) {
        for body in bodies.chain(default) {
            self.add_declarations(j, j.stmts(body));
        }
    }
}

impl Mapper for Scope {
    fn block(&mut self, j: &mut JsArena, block: StmtList) -> StmtList {
        crate::js_ir::walk::map_block_with_items(self, j, block)
    }

    fn block_items(&mut self, j: &mut JsArena, block: &[Stmt]) -> Block {
        let mark = self.enter();
        self.add_declarations(j, block);
        let result = block.iter().map(|stmt| self.statement(j, *stmt)).collect();
        self.leave(mark);
        result
    }
    fn statement(&mut self, j: &mut JsArena, stmt: Stmt) -> Stmt {
        let kind = match j.sk(stmt) {
            StmtKind::ForRange(id) => {
                let mark = self.enter();
                self.add_binding(&j.ident(j.for_range(id).ident));
                let result = map_statement_children(self, j, stmt);
                self.leave(mark);
                return result;
            }
            StmtKind::ForOf(id) | StmtKind::ForAwaitOf(id) => {
                let mark = self.enter();
                self.add_binding(&j.ident(j.for_of(id).ident));
                let result = map_statement_children(self, j, stmt);
                self.leave(mark);
                return result;
            }
            StmtKind::IntSwitch(test, id) => {
                // The discriminant is outside the shared case scope.
                let test = self.expression(j, test);
                let info = j.int_switch(id).clone();
                let mark = self.enter();
                self.add_switch_declarations(
                    j,
                    info.clauses.iter().map(|(_, c)| c.body),
                    info.default,
                );
                let clauses = info
                    .clauses
                    .iter()
                    .map(|(tag, clause)| {
                        (
                            *tag,
                            Clause {
                                body: self.block(j, clause.body),
                                ..*clause
                            },
                        )
                    })
                    .collect();
                let default = info.default.map(|b| self.block(j, b));
                self.leave(mark);
                StmtKind::IntSwitch(test, j.int_switch_id(IntSwitchInfo { clauses, default }))
            }
            StmtKind::StringSwitch(test, id) => {
                let test = self.expression(j, test);
                let info = j.string_switch(id).clone();
                let mark = self.enter();
                self.add_switch_declarations(
                    j,
                    info.clauses.iter().map(|c| c.clause.body),
                    info.default,
                );
                let clauses = info
                    .clauses
                    .into_iter()
                    .map(|c| StringClauseInfo {
                        tag_type: c.tag_type,
                        clause: Clause {
                            body: self.block(j, c.clause.body),
                            ..c.clause
                        },
                    })
                    .collect();
                let default = info.default.map(|b| self.block(j, b));
                self.leave(mark);
                StmtKind::StringSwitch(
                    test,
                    j.string_switch_id(StringSwitchInfo { clauses, default }),
                )
            }
            StmtKind::Try(id) => {
                let info = j.try_info(id);
                let body = self.block(j, info.body);
                let catch = info.catch.map(|(ident, handler)| {
                    let mark = self.enter();
                    self.add_binding(&j.ident(ident));
                    let handler = self.block(j, handler);
                    self.leave(mark);
                    (ident, handler)
                });
                let finally = info.finally.map(|b| self.block(j, b));
                StmtKind::Try(j.try_id(TryInfo {
                    body,
                    catch,
                    finally,
                }))
            }
            _ => return map_statement_children(self, j, stmt),
        };
        j.rekind_stmt(stmt, kind)
    }
    fn expression(&mut self, j: &mut JsArena, expr: Expr) -> Expr {
        match j.ek(expr) {
            ExprKind::Var(id)
                if is_js_global(&j.ident(id)) && self.in_scope(j.ident(id).name()) =>
            {
                let name = j.ident(id).name();
                let global = E::var(Ident::create_persistent("globalThis"), j);
                E::static_index(global, name, None, j)
            }
            ExprKind::Fun(id) => {
                let mark = self.enter();
                for param in j.ident_slice(j.fun(id).params) {
                    self.add_binding(param);
                }
                let result = map_expression_children(self, j, expr);
                self.leave(mark);
                result
            }
            _ => map_expression_children(self, j, expr),
        }
    }
}

#[derive(Default)]
struct ReferencedNames {
    globals: HashSet<String>,
    bindings: HashSet<String>,
    imported_modules: Vec<Ident>,
}

impl Visitor for ReferencedNames {
    fn visit_expression(&mut self, j: &JsArena, expression: Expr) {
        match j.ek(expression) {
            ExprKind::Var(id) if is_js_global(&j.ident(id)) => {
                self.globals.insert(j.ident(id).name().to_string());
            }
            ExprKind::Qualified(q) if !j.qual(q).0.dynamic_import => {
                self.imported_modules.push(j.qual(q).0.id)
            }
            ExprKind::Fun(id) => self.bindings.extend(
                j.ident_slice(j.fun(id).params)
                    .iter()
                    .filter_map(printed_binding_name),
            ),
            _ => {}
        }
    }
    fn visit_declaration(&mut self, _j: &JsArena, declaration: &VarDecl) {
        self.bindings
            .extend(printed_binding_name(&declaration.ident));
    }
    fn visit_block(&mut self, j: &JsArena, block: &[Stmt]) {
        for stmt in block {
            let ident = match j.sk(*stmt) {
                StmtKind::ForRange(id) => Some(j.for_range(id).ident),
                StmtKind::ForOf(id) | StmtKind::ForAwaitOf(id) => Some(j.for_of(id).ident),
                StmtKind::Try(id) => j.try_info(id).catch.map(|(id, _)| id),
                _ => None,
            };
            if let Some(id) = ident {
                self.bindings.extend(printed_binding_name(&j.ident(id)));
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ident::IdentFlags;

    #[test]
    fn shadowed_static_index_keeps_comment() {
        let mut j = JsArena::new();
        let global = Ident::new("Map", 0, IdentFlags::GLOBAL);
        let target = E::var(global, &mut j);
        let expr = E::static_index(target, "size", None, &mut j);
        let expr = E::comment(expr, "note", &mut j);
        let shadowed: HashSet<String> = ["Map".to_string()].into_iter().collect();

        let mut scope = Scope {
            globals: shadowed,
            counts: HashMap::default(),
            log: Vec::new(),
        };
        scope.counts.insert("Map".to_string(), 1);
        let rewritten = scope.expression(&mut j, expr);

        assert_eq!(j.expr_comment(rewritten), Some("note"));
        let ExprKind::StaticIndex(obj, field, _) = j.ek(rewritten) else {
            panic!("expected a static index");
        };
        assert_eq!(j.text(field), "size");
        assert!(!matches!(j.ek(obj), ExprKind::Var(_)));
    }

    fn run(j: JsArena, block: Block) -> JsProgram {
        apply_external_shadow_pass(JsDepsProgram {
            program: JsProgram::new_in(block, vec![], j),
            modules: Default::default(),
            side_effect: None,
        })
        .program
    }
    fn call_f(j: &mut JsArena, args: &[Expr]) -> Stmt {
        let f = E::var(Ident::create_persistent("f"), j);
        let call = E::call(f, args, crate::js_ir::CallInfo::default(), j);
        j.stmt(StmtKind::Exp(call))
    }
    fn call_arg(j: &JsArena, stmt: Stmt, index: usize) -> Expr {
        let StmtKind::Exp(call) = j.sk(stmt) else {
            panic!("expected expression statement")
        };
        let ExprKind::Call(_, args, _) = j.ek(call) else {
            panic!("expected call")
        };
        j.exprs(args)[index]
    }
    fn global_this_read(j: &JsArena, expr: Expr) -> bool {
        matches!(j.ek(expr), ExprKind::StaticIndex(obj, _, _) if matches!(j.ek(obj), ExprKind::Var(id) if j.ident(id).name() == "globalThis"))
    }
    #[test]
    fn switch_discriminant_is_read_outside_the_scope_of_the_cases() {
        let mut j = JsArena::new();
        let local = Ident::create_local("g");
        let global = E::var(Ident::create_persistent("g"), &mut j);
        let one = E::int(1, &mut j);
        let decl = crate::js_ir::build::stmt::define(
            local,
            Some(one),
            crate::lambda::lam_compat::LetKind::Strict,
            &mut j,
        );
        let local_read = E::var(local, &mut j);
        let call = call_f(&mut j, &[local_read, global]);
        let body = j.stmt_list(&[decl, call]);
        let switch = crate::js_ir::build::stmt::int_switch(
            global,
            vec![(
                1,
                Clause {
                    body,
                    should_break: true,
                    comment: None,
                    source_loc: None,
                },
            )],
            None,
            &mut j,
        );
        let program = run(j, vec![switch]);
        let j = &program.arena;
        let StmtKind::IntSwitch(discriminant, info) = j.sk(program.block[0]) else {
            panic!("expected switch")
        };
        assert!(matches!(j.ek(discriminant), ExprKind::Var(id) if is_js_global(&j.ident(id))));
        let body = j.stmts(j.int_switch(info).clauses[0].1.body);
        assert!(global_this_read(j, call_arg(j, body[1], 1)));
        assert!(matches!(j.ek(call_arg(j, body[1], 0)), ExprKind::Var(id) if j.ident(id) == local));
    }
    #[test]
    fn bindings_follow_js_scoping() {
        let mut j = JsArena::new();
        let global = E::var(Ident::create_persistent("g"), &mut j);
        let call = call_f(&mut j, &[global]);
        let local = Ident::create_local("g");
        let one = E::int(1, &mut j);
        let decl = crate::js_ir::build::stmt::define(
            local,
            Some(one),
            crate::lambda::lam_compat::LetKind::Strict,
            &mut j,
        );
        let program = run(j, vec![call, decl]);
        assert!(global_this_read(
            &program.arena,
            call_arg(&program.arena, program.block[0], 0)
        ));

        let mut j = JsArena::new();
        let global = E::var(Ident::create_persistent("g"), &mut j);
        let call = call_f(&mut j, &[global]);
        let params = j.ident_list(&[Ident::create_local("g")]);
        let body = j.stmt_list(&[call]);
        let info = j.fun_id(FunInfo {
            params,
            body,
            is_method: false,
            return_unit: false,
            async_: false,
            directive: None,
        });
        let fun = j.expr(ExprKind::Fun(info));
        let fun_stmt = j.stmt(StmtKind::Exp(fun));
        let program = run(j, vec![call, fun_stmt]);
        let j = &program.arena;
        assert!(
            matches!(j.ek(call_arg(j, program.block[0], 0)), ExprKind::Var(id) if is_js_global(&j.ident(id)))
        );
        let StmtKind::Exp(fun) = j.sk(program.block[1]) else {
            panic!("expected expression")
        };
        let ExprKind::Fun(info) = j.ek(fun) else {
            panic!("expected function")
        };
        assert!(global_this_read(
            j,
            call_arg(j, j.stmts(j.fun(info).body)[0], 0)
        ));
    }
}
