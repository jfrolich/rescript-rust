//! JS IR pass (`Js_pass_external_shadow`): a reference to a JS global `x` is
//! printed as `x`. If a binding printed as `x` is in scope there, that name
//! refers to the binding instead, so the reference has to go through
//! `globalThis.x`.

use crate::ident::Ident;
use crate::js_ir::printer::convert_ident_name;
use crate::js_ir::{
    Block, CaseClause, DepsProgram, Expression, ExpressionDesc, Statement, StatementDesc,
    StringClause, VIdent, VariableDeclaration,
};
use ahash::{AHashMap as HashMap, AHashSet as HashSet};

pub(crate) fn apply_external_shadow_pass(mut deps: DepsProgram) -> DepsProgram {
    // Only bindings named like a referenced JS global matter; without such
    // references the pass would rebuild the program unchanged.
    let mut names = ReferencedNames::default();
    crate::js_ir::walk::walk_block(&mut names, &deps.program.block);
    if names.globals.is_empty() {
        return deps;
    }
    let mut scope = Scope {
        globals: names.globals.iter().map(|name| name.to_string()).collect(),
        counts: HashMap::default(),
        log: Vec::new(),
    };
    // Statically imported modules are toplevel bindings of the generated
    // module (`import * as M from ...` or `let M = require(...)`).
    for module in &names.imported_modules {
        scope.add_binding(module);
    }
    if scope.log.is_empty()
        && !names
            .bindings
            .iter()
            .any(|name| scope.globals.contains(name.as_str()))
    {
        return deps;
    }
    deps.program.block = scope.block(std::mem::take(&mut deps.program.block));
    deps
}

/// `in_scope`: the printed names of the bindings in scope at the current
/// point, restricted to the names of referenced JS globals.
struct Scope {
    globals: HashSet<String>,
    counts: HashMap<String, u32>,
    /// The names added, in order, so that leaving a scope can remove them.
    log: Vec<String>,
}

/// A reference to a JS global (`Ext_ident.is_js`): Rust creates JS globals
/// as persistent idents.
fn is_js_global(id: &Ident) -> bool {
    id.is_js() || (id.is_global() && id.stamp() == 0)
}

/// The name a binding is printed with. Bindings named like JS keywords or
/// reserved globals are printed with a `$$` prefix, so they shadow nothing.
fn printed_binding_name(ident: &Ident) -> Option<String> {
    (!ident.is_js()).then(|| convert_ident_name(ident.name()))
}

impl Scope {
    fn add_binding(&mut self, ident: &Ident) {
        if let Some(name) = printed_binding_name(ident)
            && self.globals.contains(&name)
        {
            *self.counts.entry(name.clone()).or_insert(0) += 1;
            self.log.push(name);
        }
    }

    fn in_scope(&self, name: &str) -> bool {
        self.counts.get(name).is_some_and(|count| *count > 0)
    }

    /// `with_bindings`: the bindings added after `enter` stay in scope
    /// until `leave`.
    fn enter(&self) -> usize {
        self.log.len()
    }

    fn leave(&mut self, mark: usize) {
        while self.log.len() > mark {
            let name = self.log.pop().expect("scope log entry");
            if let Some(count) = self.counts.get_mut(&name) {
                *count -= 1;
            }
        }
    }

    /// A JS `let`, `const` or function declaration is in scope in its whole
    /// block, including before the declaration.
    fn add_declarations(&mut self, block: &Block) {
        for stmt in block {
            if let StatementDesc::Variable(VariableDeclaration { ident, .. }) = &stmt.desc {
                self.add_binding(ident);
            }
        }
    }

    fn block(&mut self, block: Block) -> Block {
        let mark = self.enter();
        self.add_declarations(&block);
        let block = block.into_iter().map(|stmt| self.statement(stmt)).collect();
        self.leave(mark);
        block
    }

    fn with_binding<T>(&mut self, ident: &Ident, f: impl FnOnce(&mut Self) -> T) -> T {
        let mark = self.enter();
        self.add_binding(ident);
        let result = f(self);
        self.leave(mark);
        result
    }

    fn case_clause(&mut self, clause: CaseClause) -> CaseClause {
        CaseClause {
            body: self.block(clause.body),
            ..clause
        }
    }

    /// The cases of a switch are printed without braces, so they share one
    /// scope.
    fn add_switch_declarations<'c>(
        &mut self,
        bodies: impl Iterator<Item = &'c Block>,
        default: Option<&Block>,
    ) {
        for body in bodies {
            self.add_declarations(body);
        }
        if let Some(block) = default {
            self.add_declarations(block);
        }
    }

    fn statement(&mut self, stmt: Statement) -> Statement {
        let Statement {
            source_loc,
            desc,
            comment,
        } = stmt;
        let desc = match desc {
            StatementDesc::Block(block) => StatementDesc::Block(self.block(block)),
            StatementDesc::Variable(decl) => StatementDesc::Variable(VariableDeclaration {
                value: decl.value.map(|value| self.expression(value)),
                ..decl
            }),
            StatementDesc::Exp(expr) => StatementDesc::Exp(self.expression(expr)),
            StatementDesc::If(cond, then_block, else_block) => StatementDesc::If(
                self.expression(cond),
                self.block(then_block),
                self.block(else_block),
            ),
            StatementDesc::While(label, cond, body) => {
                StatementDesc::While(label, self.expression(cond), self.block(body))
            }
            StatementDesc::ForRange(label, init, end, id, direction, body) => {
                self.with_binding(&id, |this| {
                    StatementDesc::ForRange(
                        label,
                        init.map(|expr| Box::new(this.expression(*expr))),
                        Box::new(this.expression(*end)),
                        id,
                        direction,
                        this.block(body),
                    )
                })
            }
            StatementDesc::ForOf(label, id, iterable, body) => self.with_binding(&id, |this| {
                StatementDesc::ForOf(
                    label,
                    id,
                    Box::new(this.expression(*iterable)),
                    this.block(body),
                )
            }),
            StatementDesc::ForAwaitOf(label, id, iterable, body) => {
                self.with_binding(&id, |this| {
                    StatementDesc::ForAwaitOf(
                        label,
                        id,
                        Box::new(this.expression(*iterable)),
                        this.block(body),
                    )
                })
            }
            StatementDesc::Continue(label) => StatementDesc::Continue(label),
            StatementDesc::Break(label) => StatementDesc::Break(label),
            StatementDesc::Return(expr) => StatementDesc::Return(self.expression(expr)),
            // The discriminant is evaluated before the scope shared by the
            // cases is entered.
            StatementDesc::IntSwitch(expr, clauses, default) => {
                let expr = self.expression(expr);
                let mark = self.enter();
                self.add_switch_declarations(
                    clauses.iter().map(|(_, clause)| &clause.body),
                    default.as_ref(),
                );
                let clauses = clauses
                    .into_iter()
                    .map(|(value, clause)| (value, self.case_clause(clause)))
                    .collect();
                let default = default.map(|block| self.block(block));
                self.leave(mark);
                StatementDesc::IntSwitch(expr, clauses, default)
            }
            StatementDesc::StringSwitch(expr, clauses, default) => {
                let expr = self.expression(expr);
                let mark = self.enter();
                self.add_switch_declarations(
                    clauses.iter().map(|clause| &clause.clause.body),
                    default.as_ref(),
                );
                let clauses = clauses
                    .into_iter()
                    .map(|clause| StringClause {
                        tag_type: clause.tag_type,
                        clause: self.case_clause(clause.clause),
                    })
                    .collect();
                let default = default.map(|block| self.block(block));
                self.leave(mark);
                StatementDesc::StringSwitch(expr, clauses, default)
            }
            StatementDesc::Throw(expr) => StatementDesc::Throw(self.expression(expr)),
            // The catch parameter is only in scope in the handler.
            StatementDesc::Try(body, catch, finally) => {
                let body = self.block(body);
                let catch = catch.map(|(ident, handler)| {
                    let handler = self.with_binding(&ident, |this| this.block(handler));
                    (ident, handler)
                });
                let finally = finally.map(|block| self.block(block));
                StatementDesc::Try(body, catch, finally)
            }
            StatementDesc::Debugger => StatementDesc::Debugger,
        };
        Statement {
            source_loc,
            desc,
            comment,
        }
    }

    fn expression(&mut self, expr: Expression) -> Expression {
        match &expr.desc {
            ExpressionDesc::Var(VIdent::Id(id)) if is_js_global(id) && self.in_scope(id.name()) => {
                global_this_field(id.name())
            }
            ExpressionDesc::Fun { params, .. } => {
                let mark = self.enter();
                for param in params {
                    self.add_binding(param);
                }
                let expr = self.expression_children(expr);
                self.leave(mark);
                expr
            }
            _ => self.expression_children(expr),
        }
    }

    fn expression_children(&mut self, expr: Expression) -> Expression {
        let this = std::cell::RefCell::new(self);
        rewrite_expr_children(
            expr,
            &mut |child| this.borrow_mut().expression(child),
            &mut |body| this.borrow_mut().block(body),
        )
    }
}

fn rewrite_expr_children(
    expr: Expression,
    rewrite: &mut impl FnMut(Expression) -> Expression,
    rewrite_function_body: &mut impl FnMut(Block) -> Block,
) -> Expression {
    let Expression {
        source_loc,
        desc,
        comment,
    } = expr;
    let desc = match desc {
        ExpressionDesc::Length(inner, kind) => {
            ExpressionDesc::Length(Box::new(rewrite(*inner)), kind)
        }
        ExpressionDesc::IsNullOrUndefined(inner) => {
            ExpressionDesc::IsNullOrUndefined(Box::new(rewrite(*inner)))
        }
        ExpressionDesc::StringAppend(left, right) => {
            ExpressionDesc::StringAppend(Box::new(rewrite(*left)), Box::new(rewrite(*right)))
        }
        ExpressionDesc::Bool(value) => ExpressionDesc::Bool(value),
        ExpressionDesc::Typeof(inner) => ExpressionDesc::Typeof(Box::new(rewrite(*inner))),
        ExpressionDesc::In(left, right) => {
            ExpressionDesc::In(Box::new(rewrite(*left)), Box::new(rewrite(*right)))
        }
        ExpressionDesc::JsNot(inner) => ExpressionDesc::JsNot(Box::new(rewrite(*inner))),
        ExpressionDesc::JsBnot(inner) => ExpressionDesc::JsBnot(Box::new(rewrite(*inner))),
        ExpressionDesc::Seq(first, second) => {
            ExpressionDesc::Seq(Box::new(rewrite(*first)), Box::new(rewrite(*second)))
        }
        ExpressionDesc::Cond(cond, then_, else_) => ExpressionDesc::Cond(
            Box::new(rewrite(*cond)),
            Box::new(rewrite(*then_)),
            Box::new(rewrite(*else_)),
        ),
        ExpressionDesc::Bin(op, left, right) => {
            ExpressionDesc::Bin(op, Box::new(rewrite(*left)), Box::new(rewrite(*right)))
        }
        ExpressionDesc::FlatCall(func, args) => {
            ExpressionDesc::FlatCall(Box::new(rewrite(*func)), Box::new(rewrite(*args)))
        }
        ExpressionDesc::Call(func, args, info) => ExpressionDesc::Call(
            Box::new(rewrite(*func)),
            args.into_iter().map(rewrite).collect(),
            info,
        ),
        ExpressionDesc::ArrayIndex(value, index) => {
            ExpressionDesc::ArrayIndex(Box::new(rewrite(*value)), Box::new(rewrite(*index)))
        }
        ExpressionDesc::TaggedTemplate(func, strings, values) => ExpressionDesc::TaggedTemplate(
            Box::new(rewrite(*func)),
            strings,
            values.into_iter().map(&mut *rewrite).collect(),
        ),
        ExpressionDesc::InterpolatedTemplate { segments, values } => {
            ExpressionDesc::InterpolatedTemplate {
                segments,
                values: values.into_iter().map(&mut *rewrite).collect(),
            }
        }
        ExpressionDesc::StaticIndex(obj, field, pos) => {
            ExpressionDesc::StaticIndex(Box::new(rewrite(*obj)), field, pos)
        }
        ExpressionDesc::New(ctor, args) => ExpressionDesc::New(
            Box::new(rewrite(*ctor)),
            args.map(|items| items.into_iter().map(rewrite).collect()),
        ),
        ExpressionDesc::Var(vident) => ExpressionDesc::Var(vident),
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
            // Match `Js_record_map.super` as used by
            // `compiler/core/js_pass_external_shadow.ml:43-57` and 76-101:
            // function expressions recurse into their body through
            // `compiler/core/js_record_map.ml:165-168`, so global-shadow
            // rewrites remain visible inside nested functions.
            body: rewrite_function_body(body),
            env,
            return_unit,
            async_,
            directive,
        },
        ExpressionDesc::Str(txt) => ExpressionDesc::Str(txt),
        ExpressionDesc::TemplateLiteral(segment) => ExpressionDesc::TemplateLiteral(segment),
        ExpressionDesc::JsonLiteral(source) => ExpressionDesc::JsonLiteral(source),
        ExpressionDesc::RawJsCode(info) => ExpressionDesc::RawJsCode(info),
        ExpressionDesc::Array(items, mutable_flag) => {
            ExpressionDesc::Array(items.into_iter().map(rewrite).collect(), mutable_flag)
        }
        ExpressionDesc::OptionalBlock(value, flag) => {
            ExpressionDesc::OptionalBlock(Box::new(rewrite(*value)), flag)
        }
        ExpressionDesc::CamlBlock(values, mutable_flag, tag_info) => ExpressionDesc::CamlBlock(
            values.into_iter().map(&mut *rewrite).collect(),
            mutable_flag,
            tag_info,
        ),
        ExpressionDesc::CamlBlockTag(value, tag) => {
            ExpressionDesc::CamlBlockTag(Box::new(rewrite(*value)), tag)
        }
        ExpressionDesc::Number(number) => ExpressionDesc::Number(number),
        ExpressionDesc::Jsx(jsx) => ExpressionDesc::Jsx(Box::new(jsx.map(&mut *rewrite))),
        ExpressionDesc::Object(entries) => ExpressionDesc::Object(
            entries
                .into_iter()
                .map(|entry| entry.map(&mut *rewrite))
                .collect(),
        ),
        ExpressionDesc::Undefined { is_unit } => ExpressionDesc::Undefined { is_unit },
        ExpressionDesc::Null => ExpressionDesc::Null,
        ExpressionDesc::Await(inner) => ExpressionDesc::Await(Box::new(rewrite(*inner))),
        ExpressionDesc::Spread(inner) => ExpressionDesc::Spread(Box::new(rewrite(*inner))),
        ExpressionDesc::RecordRest(fields, source) => {
            ExpressionDesc::RecordRest(fields, Box::new(rewrite(*source)))
        }
    };

    Expression {
        source_loc,
        desc,
        comment,
    }
}

fn global_this_field(name: &str) -> Expression {
    Expression::new(ExpressionDesc::StaticIndex(
        Box::new(Expression::var(Ident::create_persistent("globalThis"))),
        name.to_string(),
        None,
    ))
}

/// Names of the JS globals a program references, of the bindings it
/// declares and the statically imported modules.
#[derive(Default)]
struct ReferencedNames<'a> {
    globals: HashSet<&'a str>,
    bindings: HashSet<String>,
    imported_modules: Vec<&'a Ident>,
}

impl<'a> crate::js_ir::walk::Visitor<'a> for ReferencedNames<'a> {
    fn visit_expression(&mut self, expression: &'a Expression) {
        match &expression.desc {
            ExpressionDesc::Var(VIdent::Id(id)) if is_js_global(id) => {
                self.globals.insert(id.name());
            }
            ExpressionDesc::Var(VIdent::Qualified(module, _)) if !module.dynamic_import => {
                self.imported_modules.push(&module.id);
            }
            ExpressionDesc::Fun { params, .. } => {
                self.bindings
                    .extend(params.iter().filter_map(printed_binding_name));
            }
            _ => {}
        }
    }

    fn visit_declaration(&mut self, declaration: &'a VariableDeclaration) {
        self.bindings
            .extend(printed_binding_name(&declaration.ident));
    }

    fn visit_block(&mut self, block: &'a Block) {
        for stmt in block {
            match &stmt.desc {
                StatementDesc::ForRange(_, _, _, id, _, _)
                | StatementDesc::ForOf(_, id, _, _)
                | StatementDesc::ForAwaitOf(_, id, _, _)
                | StatementDesc::Try(_, Some((id, _)), _) => {
                    self.bindings.extend(printed_binding_name(id));
                }
                _ => {}
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::js_ir::op::IdentInfo;
    use crate::js_ir::{CallInfo, Program};
    use crate::lambda::lam_compat::LetKind;

    fn js_global(name: &str) -> Expression {
        Expression::var(Ident::create_persistent(name))
    }

    fn is_global_read(e: &Expression) -> bool {
        matches!(&e.desc, ExpressionDesc::Var(VIdent::Id(id)) if is_js_global(id) && id.name() == "g")
    }

    fn is_global_this_read(e: &Expression) -> bool {
        matches!(
            &e.desc,
            ExpressionDesc::StaticIndex(obj, field, _)
                if field == "g"
                    && matches!(&obj.desc, ExpressionDesc::Var(VIdent::Id(gt)) if gt.name() == "globalThis")
        )
    }

    fn run(block: Block) -> Block {
        apply_external_shadow_pass(DepsProgram {
            program: Program::new(block, vec![]),
            modules: Default::default(),
            side_effect: None,
        })
        .program
        .block
    }

    fn define(ident: Ident, value: Expression) -> Statement {
        Statement::variable(VariableDeclaration {
            ident,
            value: Some(value),
            property: LetKind::Strict,
            ident_info: IdentInfo::default(),
        })
    }

    fn call_f(args: Vec<Expression>) -> Statement {
        Statement::exp(Expression::call(js_global("f"), args, CallInfo::default()))
    }

    /// `switch (g) { case 1: let g = 1; f(g, <global g>) }`: the
    /// discriminant is read outside the scope of the cases
    /// (ounit_external_shadow_tests.ml).
    #[test]
    fn switch_discriminant_is_read_outside_the_scope_of_the_cases() {
        let local = Ident::create_local("g");
        let body = vec![
            define(local, Expression::number(crate::js_ir::Number::int(1))),
            call_f(vec![Expression::var(local), js_global("g")]),
        ];
        let block = run(vec![Statement::new(StatementDesc::IntSwitch(
            js_global("g"),
            vec![(
                1,
                CaseClause {
                    body,
                    should_break: true,
                    comment: None,
                    source_loc: None,
                },
            )],
            None,
        ))]);
        let [
            Statement {
                desc: StatementDesc::IntSwitch(discr, clauses, None),
                ..
            },
        ] = block.as_slice()
        else {
            panic!("unexpected program shape")
        };
        assert!(
            is_global_read(discr),
            "discriminant reads the global directly"
        );
        let [
            _,
            Statement {
                desc: StatementDesc::Exp(call),
                ..
            },
        ] = clauses[0].1.body.as_slice()
        else {
            panic!("unexpected case body")
        };
        let ExpressionDesc::Call(_, args, _) = &call.desc else {
            panic!("expected a call")
        };
        assert!(
            args.iter().any(is_global_this_read),
            "read in the case goes through globalThis"
        );
    }

    /// A toplevel binding is in scope before its declaration, and a
    /// parameter only inside its function.
    #[test]
    fn bindings_follow_js_scoping() {
        let local = Ident::create_local("g");
        let param = Ident::create_local("g");
        let fun = Expression::new(ExpressionDesc::Fun {
            is_method: false,
            params: vec![param],
            body: vec![call_f(vec![js_global("g")])],
            env: Default::default(),
            return_unit: false,
            async_: false,
            directive: None,
        });
        let block = run(vec![
            call_f(vec![js_global("g")]),
            define(local, Expression::number(crate::js_ir::Number::int(1))),
        ]);
        let Statement {
            desc: StatementDesc::Exp(call),
            ..
        } = &block[0]
        else {
            panic!("expected a call")
        };
        let ExpressionDesc::Call(_, args, _) = &call.desc else {
            panic!("expected a call")
        };
        assert!(is_global_this_read(&args[0]));

        let block = run(vec![call_f(vec![js_global("g")]), Statement::exp(fun)]);
        let Statement {
            desc: StatementDesc::Exp(call),
            ..
        } = &block[0]
        else {
            panic!("expected a call")
        };
        let ExpressionDesc::Call(_, args, _) = &call.desc else {
            panic!("expected a call")
        };
        assert!(
            is_global_read(&args[0]),
            "the parameter is out of scope here"
        );
        let Statement {
            desc: StatementDesc::Exp(fun),
            ..
        } = &block[1]
        else {
            panic!("expected the function")
        };
        let ExpressionDesc::Fun { body, .. } = &fun.desc else {
            panic!("expected the function")
        };
        let StatementDesc::Exp(call) = &body[0].desc else {
            panic!("expected a call")
        };
        let ExpressionDesc::Call(_, args, _) = &call.desc else {
            panic!("expected a call")
        };
        assert!(
            is_global_this_read(&args[0]),
            "the parameter shadows the global"
        );
    }
}
