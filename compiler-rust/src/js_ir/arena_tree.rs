//! Conversion between the boxed JS IR tree and [`JsArena`] handles.
//!
//! Both directions are exact copies: no folding or normalization.

use super::arena::*;
use super::{
    Block, CaseClause, Expression, ExpressionDesc, PropertyName, Statement, StatementDesc,
    StringClause, VIdent, VariableDeclaration,
};

fn cold(a: &mut JsArena, comment: Option<&str>, source_loc: Option<crate::lambda::LamLoc>) -> Cold {
    Cold {
        comment: comment.map(|c| a.str(c)),
        source_loc,
    }
}

pub fn import_block(a: &mut JsArena, block: &[Statement]) -> StmtList {
    let items: Vec<Stmt> = block.iter().map(|s| import_stmt(a, s)).collect();
    a.stmt_list(&items)
}

pub fn import_block_vec(a: &mut JsArena, block: &[Statement]) -> Vec<Stmt> {
    block.iter().map(|s| import_stmt(a, s)).collect()
}

fn import_exprs(a: &mut JsArena, items: &[Expression]) -> ExprList {
    let items: Vec<Expr> = items.iter().map(|e| import_expr(a, e)).collect();
    a.expr_list(&items)
}

fn import_clause(a: &mut JsArena, clause: &CaseClause) -> Clause {
    let body = import_block(a, &clause.body);
    let comment = clause.comment.as_deref().map(|c| a.str(c));
    Clause {
        body,
        should_break: clause.should_break,
        comment,
        source_loc: clause.source_loc,
    }
}

pub fn import_stmt(a: &mut JsArena, stmt: &Statement) -> Stmt {
    let kind = match &stmt.desc {
        StatementDesc::Block(block) => StmtKind::Block(import_block(a, block)),
        StatementDesc::Variable(decl) => {
            let value = decl.value.as_ref().map(|v| import_expr(a, v));
            StmtKind::Variable(a.var_id(VarDecl {
                ident: decl.ident,
                value,
                property: decl.property,
                ident_info: decl.ident_info.clone(),
            }))
        }
        StatementDesc::Exp(e) => StmtKind::Exp(import_expr(a, e)),
        StatementDesc::If(c, t, e) => {
            let c = import_expr(a, c);
            let t = import_block(a, t);
            let e = import_block(a, e);
            StmtKind::If(c, t, e)
        }
        StatementDesc::While(label, c, body) => {
            let label = label.as_deref().map(|l| a.str(l));
            let c = import_expr(a, c);
            let body = import_block(a, body);
            StmtKind::While(label, c, body)
        }
        StatementDesc::ForRange(label, init, end, ident, direction, body) => {
            let label = label.as_deref().map(|l| a.str(l));
            let init = init.as_deref().map(|e| import_expr(a, e));
            let end = import_expr(a, end);
            let ident = a.ident_id(*ident);
            let body = import_block(a, body);
            StmtKind::ForRange(a.for_range_id(ForRangeInfo {
                label,
                init,
                end,
                ident,
                direction: *direction,
                body,
            }))
        }
        StatementDesc::ForOf(label, ident, iterable, body)
        | StatementDesc::ForAwaitOf(label, ident, iterable, body) => {
            let label = label.as_deref().map(|l| a.str(l));
            let ident = a.ident_id(*ident);
            let iterable = import_expr(a, iterable);
            let body = import_block(a, body);
            let id = a.for_of_id(ForOfInfo {
                label,
                ident,
                iterable,
                body,
            });
            if matches!(stmt.desc, StatementDesc::ForOf(..)) {
                StmtKind::ForOf(id)
            } else {
                StmtKind::ForAwaitOf(id)
            }
        }
        StatementDesc::Continue(label) => StmtKind::Continue(label.as_deref().map(|l| a.str(l))),
        StatementDesc::Break(label) => StmtKind::Break(label.as_deref().map(|l| a.str(l))),
        StatementDesc::Return(e) => StmtKind::Return(import_expr(a, e)),
        StatementDesc::IntSwitch(e, clauses, default) => {
            let e = import_expr(a, e);
            let clauses = clauses
                .iter()
                .map(|(i, c)| (*i, import_clause(a, c)))
                .collect();
            let default = default.as_ref().map(|d| import_block(a, d));
            StmtKind::IntSwitch(e, a.int_switch_id(IntSwitchInfo { clauses, default }))
        }
        StatementDesc::StringSwitch(e, clauses, default) => {
            let e = import_expr(a, e);
            let clauses = clauses
                .iter()
                .map(|c| StringClauseInfo {
                    tag_type: c.tag_type.clone(),
                    clause: import_clause(a, &c.clause),
                })
                .collect();
            let default = default.as_ref().map(|d| import_block(a, d));
            StmtKind::StringSwitch(e, a.string_switch_id(StringSwitchInfo { clauses, default }))
        }
        StatementDesc::Throw(e) => StmtKind::Throw(import_expr(a, e)),
        StatementDesc::Try(body, catch, finally) => {
            let body = import_block(a, body);
            let catch = catch.as_ref().map(|(id, b)| {
                let id = a.ident_id(*id);
                (id, import_block(a, b))
            });
            let finally = finally.as_ref().map(|b| import_block(a, b));
            StmtKind::Try(a.try_id(TryInfo {
                body,
                catch,
                finally,
            }))
        }
        StatementDesc::Debugger => StmtKind::Debugger,
    };
    let cold = cold(
        a,
        stmt.comment.as_deref().map(|c| c.as_str()),
        stmt.source_loc,
    );
    a.stmt_with(kind, cold)
}

pub fn import_expr(a: &mut JsArena, expr: &Expression) -> Expr {
    use ExpressionDesc as D;
    let kind = match &expr.desc {
        D::Length(e, o) => ExprKind::Length(import_expr(a, e), *o),
        D::IsNullOrUndefined(e) => ExprKind::IsNullOrUndefined(import_expr(a, e)),
        D::StringAppend(l, r) => {
            let l = import_expr(a, l);
            ExprKind::StringAppend(l, import_expr(a, r))
        }
        D::Bool(b) => ExprKind::Bool(*b),
        D::Typeof(e) => ExprKind::Typeof(import_expr(a, e)),
        D::In(l, r) => {
            let l = import_expr(a, l);
            ExprKind::In(l, import_expr(a, r))
        }
        D::JsNot(e) => ExprKind::JsNot(import_expr(a, e)),
        D::JsBnot(e) => ExprKind::JsBnot(import_expr(a, e)),
        D::Seq(l, r) => {
            let l = import_expr(a, l);
            ExprKind::Seq(l, import_expr(a, r))
        }
        D::Cond(c, t, e) => {
            let c = import_expr(a, c);
            let t = import_expr(a, t);
            ExprKind::Cond(c, t, import_expr(a, e))
        }
        D::Bin(op, l, r) => {
            let l = import_expr(a, l);
            ExprKind::Bin(*op, l, import_expr(a, r))
        }
        D::FlatCall(l, r) => {
            let l = import_expr(a, l);
            ExprKind::FlatCall(l, import_expr(a, r))
        }
        D::Call(f, args, info) => {
            let f = import_expr(a, f);
            let args = import_exprs(a, args);
            ExprKind::Call(f, args, a.call_id(info.clone()))
        }
        D::StringIndex(l, r) => {
            let l = import_expr(a, l);
            ExprKind::StringIndex(l, import_expr(a, r))
        }
        D::ArrayIndex(l, r) => {
            let l = import_expr(a, l);
            ExprKind::ArrayIndex(l, import_expr(a, r))
        }
        D::TaggedTemplate(tag, strings, values) => {
            let tag = import_expr(a, tag);
            let strings = a.tagged_id(strings.clone());
            ExprKind::TaggedTemplate(tag, strings, import_exprs(a, values))
        }
        D::InterpolatedTemplate { segments, values } => {
            let segments = a.segments_id(segments.clone());
            ExprKind::InterpolatedTemplate(segments, import_exprs(a, values))
        }
        D::StaticIndex(e, field, pos) => {
            let e = import_expr(a, e);
            ExprKind::StaticIndex(e, a.str(field), FieldPos::new(*pos))
        }
        D::New(e, args) => {
            let e = import_expr(a, e);
            ExprKind::New(e, args.as_ref().map(|args| import_exprs(a, args)))
        }
        D::Var(VIdent::Id(id)) => ExprKind::Var(a.ident_id(*id)),
        D::Var(VIdent::Qualified(module, member)) => {
            ExprKind::Qualified(a.qual_id((**module).clone(), member.clone()))
        }
        D::Fun {
            is_method,
            params,
            body,
            env: _,
            return_unit,
            async_,
            directive,
        } => {
            let params = a.ident_list(params);
            let body = import_block(a, body);
            let directive = directive.as_deref().map(|d| a.str(d));
            ExprKind::Fun(a.fun_id(FunInfo {
                is_method: *is_method,
                params,
                body,
                return_unit: *return_unit,
                async_: *async_,
                directive,
            }))
        }
        D::Str(s) => ExprKind::Str(a.str(s)),
        D::TemplateLiteral(seg) => ExprKind::TemplateLiteral(a.template_id(seg.clone())),
        D::JsonLiteral(s) => ExprKind::JsonLiteral(a.str(s)),
        D::RawJsCode(info) => ExprKind::RawJsCode(a.raw_id(info.clone())),
        D::Array(items, flag) => ExprKind::Array(import_exprs(a, items), *flag),
        D::OptionalBlock(e, b) => ExprKind::OptionalBlock(import_expr(a, e), *b),
        D::CamlBlock(items, flag, tag) => {
            let items = import_exprs(a, items);
            ExprKind::CamlBlock(items, *flag, a.tag_id((**tag).clone()))
        }
        D::CamlBlockTag(e, s) => {
            let e = import_expr(a, e);
            ExprKind::CamlBlockTag(e, a.str(s))
        }
        D::Number(n) => ExprKind::Number(a.number_id(n.clone())),
        D::Object(dup, props) => {
            let dup = dup.as_deref().map(|d| import_expr(a, d));
            let props: Vec<(PropName, Expr)> = props
                .iter()
                .map(|(name, value)| {
                    let name = match name {
                        PropertyName::Lit(s) => PropName::Lit(a.str(s)),
                        PropertyName::Symbol => PropName::Symbol,
                    };
                    (name, import_expr(a, value))
                })
                .collect();
            ExprKind::Object(dup, a.prop_list(&props))
        }
        D::Undefined { is_unit } => ExprKind::Undefined { is_unit: *is_unit },
        D::Null => ExprKind::Null,
        D::Await(e) => ExprKind::Await(import_expr(a, e)),
        D::Spread(e) => ExprKind::Spread(import_expr(a, e)),
        D::RecordRest(fields, e) => {
            let fields = a.rest_id(fields.clone());
            ExprKind::RecordRest(fields, import_expr(a, e))
        }
    };
    let cold = cold(
        a,
        expr.comment.as_deref().map(|c| c.as_str()),
        expr.source_loc,
    );
    a.expr_with(kind, cold)
}

// ---- export --------------------------------------------------------------

pub fn export_block(a: &JsArena, block: StmtList) -> Block {
    a.stmts(block).iter().map(|s| export_stmt(a, *s)).collect()
}

fn export_exprs(a: &JsArena, list: ExprList) -> Vec<Expression> {
    a.exprs(list).iter().map(|e| export_expr(a, *e)).collect()
}

fn opt_string(a: &JsArena, s: Option<StrId>) -> Option<String> {
    s.map(|s| a.text(s).to_string())
}

fn export_clause(a: &JsArena, clause: Clause) -> CaseClause {
    CaseClause {
        body: export_block(a, clause.body),
        should_break: clause.should_break,
        comment: opt_string(a, clause.comment),
        source_loc: clause.source_loc,
    }
}

pub fn export_stmt(a: &JsArena, s: Stmt) -> Statement {
    let desc = match a.sk(s) {
        StmtKind::Block(b) => StatementDesc::Block(export_block(a, b)),
        StmtKind::Variable(v) => {
            let decl = a.var(v);
            StatementDesc::Variable(VariableDeclaration {
                ident: decl.ident,
                value: decl.value.map(|e| export_expr(a, e)),
                property: decl.property,
                ident_info: decl.ident_info.clone(),
            })
        }
        StmtKind::Exp(e) => StatementDesc::Exp(export_expr(a, e)),
        StmtKind::If(c, t, e) => {
            StatementDesc::If(export_expr(a, c), export_block(a, t), export_block(a, e))
        }
        StmtKind::While(label, c, body) => StatementDesc::While(
            opt_string(a, label),
            export_expr(a, c),
            export_block(a, body),
        ),
        StmtKind::ForRange(id) => {
            let info = a.for_range(id);
            StatementDesc::ForRange(
                opt_string(a, info.label),
                info.init.map(|e| Box::new(export_expr(a, e))),
                Box::new(export_expr(a, info.end)),
                a.ident(info.ident),
                info.direction,
                export_block(a, info.body),
            )
        }
        StmtKind::ForOf(id) | StmtKind::ForAwaitOf(id) => {
            let info = a.for_of(id);
            let label = opt_string(a, info.label);
            let ident = a.ident(info.ident);
            let iterable = Box::new(export_expr(a, info.iterable));
            let body = export_block(a, info.body);
            if matches!(a.sk(s), StmtKind::ForOf(_)) {
                StatementDesc::ForOf(label, ident, iterable, body)
            } else {
                StatementDesc::ForAwaitOf(label, ident, iterable, body)
            }
        }
        StmtKind::Continue(label) => StatementDesc::Continue(opt_string(a, label)),
        StmtKind::Break(label) => StatementDesc::Break(opt_string(a, label)),
        StmtKind::Return(e) => StatementDesc::Return(export_expr(a, e)),
        StmtKind::IntSwitch(e, id) => {
            let info = a.int_switch(id);
            StatementDesc::IntSwitch(
                export_expr(a, e),
                info.clauses
                    .iter()
                    .map(|(i, c)| (*i, export_clause(a, *c)))
                    .collect(),
                info.default.map(|d| export_block(a, d)),
            )
        }
        StmtKind::StringSwitch(e, id) => {
            let info = a.string_switch(id);
            StatementDesc::StringSwitch(
                export_expr(a, e),
                info.clauses
                    .iter()
                    .map(|c| StringClause {
                        tag_type: c.tag_type.clone(),
                        clause: export_clause(a, c.clause),
                    })
                    .collect(),
                info.default.map(|d| export_block(a, d)),
            )
        }
        StmtKind::Throw(e) => StatementDesc::Throw(export_expr(a, e)),
        StmtKind::Try(id) => {
            let info = a.try_info(id);
            StatementDesc::Try(
                export_block(a, info.body),
                info.catch.map(|(id, b)| (a.ident(id), export_block(a, b))),
                info.finally.map(|b| export_block(a, b)),
            )
        }
        StmtKind::Debugger => StatementDesc::Debugger,
    };
    let cold = a.stmt_cold(s);
    Statement {
        desc,
        comment: opt_string(a, cold.comment).map(Box::new),
        source_loc: cold.source_loc,
    }
}

pub fn export_expr(a: &JsArena, e: Expr) -> Expression {
    use ExpressionDesc as D;
    let bx = |e: Expr| Box::new(export_expr(a, e));
    let desc = match a.ek(e) {
        ExprKind::Length(e, o) => D::Length(bx(e), o),
        ExprKind::IsNullOrUndefined(e) => D::IsNullOrUndefined(bx(e)),
        ExprKind::StringAppend(l, r) => D::StringAppend(bx(l), bx(r)),
        ExprKind::Bool(b) => D::Bool(b),
        ExprKind::Typeof(e) => D::Typeof(bx(e)),
        ExprKind::In(l, r) => D::In(bx(l), bx(r)),
        ExprKind::JsNot(e) => D::JsNot(bx(e)),
        ExprKind::JsBnot(e) => D::JsBnot(bx(e)),
        ExprKind::Seq(l, r) => D::Seq(bx(l), bx(r)),
        ExprKind::Cond(c, t, f) => D::Cond(bx(c), bx(t), bx(f)),
        ExprKind::Bin(op, l, r) => D::Bin(op, bx(l), bx(r)),
        ExprKind::FlatCall(l, r) => D::FlatCall(bx(l), bx(r)),
        ExprKind::Call(f, args, info) => {
            D::Call(bx(f), export_exprs(a, args), a.call_info(info).clone())
        }
        ExprKind::StringIndex(l, r) => D::StringIndex(bx(l), bx(r)),
        ExprKind::ArrayIndex(l, r) => D::ArrayIndex(bx(l), bx(r)),
        ExprKind::TaggedTemplate(tag, strings, values) => {
            D::TaggedTemplate(bx(tag), a.tagged(strings).to_vec(), export_exprs(a, values))
        }
        ExprKind::InterpolatedTemplate(segments, values) => D::InterpolatedTemplate {
            segments: a.segments(segments).to_vec(),
            values: export_exprs(a, values),
        },
        ExprKind::StaticIndex(e, field, pos) => {
            D::StaticIndex(bx(e), a.text(field).to_string(), pos.get())
        }
        ExprKind::New(e, args) => D::New(bx(e), args.map(|args| export_exprs(a, args))),
        ExprKind::Var(id) => D::Var(VIdent::Id(a.ident(id))),
        ExprKind::Qualified(q) => {
            let (module, member) = a.qual(q);
            D::Var(VIdent::Qualified(
                Box::new(module.clone()),
                member.map(str::to_string),
            ))
        }
        ExprKind::Fun(f) => {
            let info = a.fun(f);
            D::Fun {
                is_method: info.is_method,
                params: a.ident_slice(info.params).to_vec(),
                body: export_block(a, info.body),
                env: super::FunEnv,
                return_unit: info.return_unit,
                async_: info.async_,
                directive: opt_string(a, info.directive).map(Box::new),
            }
        }
        ExprKind::Str(s) => D::Str(a.text(s).to_string()),
        ExprKind::TemplateLiteral(t) => D::TemplateLiteral(a.template(t).clone()),
        ExprKind::JsonLiteral(s) => D::JsonLiteral(a.text(s).to_string()),
        ExprKind::RawJsCode(r) => D::RawJsCode(a.raw(r).clone()),
        ExprKind::Array(items, flag) => D::Array(export_exprs(a, items), flag),
        ExprKind::OptionalBlock(e, b) => D::OptionalBlock(bx(e), b),
        ExprKind::CamlBlock(items, flag, tag) => {
            D::CamlBlock(export_exprs(a, items), flag, Box::new(a.tag(tag).clone()))
        }
        ExprKind::CamlBlockTag(e, s) => D::CamlBlockTag(bx(e), a.text(s).to_string()),
        ExprKind::Number(n) => D::Number(a.number(n).clone()),
        ExprKind::Object(dup, props) => D::Object(
            dup.map(bx),
            a.props(props)
                .iter()
                .map(|(name, value)| {
                    let name = match name {
                        PropName::Lit(s) => PropertyName::Lit(a.text(*s).to_string()),
                        PropName::Symbol => PropertyName::Symbol,
                    };
                    (name, export_expr(a, *value))
                })
                .collect(),
        ),
        ExprKind::Undefined { is_unit } => D::Undefined { is_unit },
        ExprKind::Null => D::Null,
        ExprKind::Await(e) => D::Await(bx(e)),
        ExprKind::Spread(e) => D::Spread(bx(e)),
        ExprKind::RecordRest(fields, e) => D::RecordRest(a.rest(fields).to_vec(), bx(e)),
    };
    let cold = a.expr_cold(e);
    Expression {
        desc,
        comment: opt_string(a, cold.comment).map(Box::new),
        source_loc: cold.source_loc,
    }
}

impl JsProgram {
    /// Copy a tree program into a fresh arena.
    pub fn from_tree(program: &super::Program) -> Self {
        let mut arena = JsArena::new();
        let block = import_block_vec(&mut arena, &program.block);
        JsProgram {
            arena,
            block,
            exports: program.exports.clone(),
            export_set: program.export_set.clone(),
            name_reservations: program.name_reservations.clone(),
        }
    }

    /// Copy back into a tree program.
    pub fn to_tree(&self) -> super::Program {
        super::Program {
            block: self
                .block
                .iter()
                .map(|s| export_stmt(&self.arena, *s))
                .collect(),
            exports: self.exports.clone(),
            export_set: self.export_set.clone(),
            name_reservations: self.name_reservations.clone(),
        }
    }
}

impl JsDepsProgram {
    /// Copy a tree program into a fresh arena.
    pub fn from_tree(program: &super::DepsProgram) -> Self {
        JsDepsProgram {
            program: JsProgram::from_tree(&program.program),
            modules: program.modules.clone(),
            side_effect: program.side_effect.clone(),
        }
    }

    /// Copy back into a tree program.
    pub fn to_tree(&self) -> super::DepsProgram {
        super::DepsProgram {
            program: self.program.to_tree(),
            modules: self.modules.clone(),
            side_effect: self.side_effect.clone(),
        }
    }
}
