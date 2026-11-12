//! The only expression/statement layer that knows oxc AST types.
use super::{Unsupported, literal, naming::Names, walk};
use crate::js_ir::arena::{Expr, ExprKind, FunId, JsArena, PropName, Stmt, StmtKind};
use crate::js_ir::op::{BinOp, Kind, Number};
use crate::js_ir::printer::{js_export_name, normalize_float_literal_for_js};
use oxc_allocator::{Allocator, GetAllocator, Vec as ArenaVec};
use oxc_ast::{ast::*, builder::AstBuilder};
use oxc_span::SPAN;
use oxc_syntax::{
    number::{BigintBase, NumberBase},
    operator::{BinaryOperator as B, LogicalOperator as L, UnaryOperator as U},
};

pub(super) struct Build<'a, 'r> {
    pub b: AstBuilder<'a>,
    pub arena: &'r JsArena,
    pub names: &'r Names,
}
impl<'a, 'r> Build<'a, 'r> {
    pub fn new(alloc: &'a Allocator, arena: &'r JsArena, names: &'r Names) -> Self {
        Self {
            b: AstBuilder::new(alloc),
            arena,
            names,
        }
    }
    pub fn text(&self, s: &str) -> &'a str {
        self.b.allocator().alloc_str(s)
    }
    pub fn id(&self, name: &str) -> Expression<'a> {
        Expression::new_identifier(SPAN, self.text(name), &self.b)
    }
    pub fn string(&self, value: &str) -> StringLiteral<'a> {
        StringLiteral::new(
            SPAN,
            self.text(&literal::string_value(value)),
            None,
            &self.b,
        )
    }
    pub fn string_expr(&self, value: &str) -> Expression<'a> {
        Expression::StringLiteral(self.b.alloc(self.string(value)))
    }
    pub fn binding(&self, name: &str) -> BindingIdentifier<'a> {
        BindingIdentifier::new(SPAN, self.text(name), &self.b)
    }
    pub fn variable(&self, name: &str, init: Option<Expression<'a>>) -> Statement<'a> {
        let pattern = BindingPattern::BindingIdentifier(self.b.alloc(self.binding(name)));
        let decl = VariableDeclarator::new(SPAN, pattern, None, init, false, &self.b);
        Statement::new_variable_declaration(
            SPAN,
            VariableDeclarationKind::Let,
            self.b.vec1(decl),
            false,
            &self.b,
        )
    }
    pub fn member(&self, target: Expression<'a>, name: &str) -> Expression<'a> {
        let (name, dot) = walk::member_form(name);
        if dot {
            Expression::new_static_member_expression(
                SPAN,
                target,
                IdentifierName::new(SPAN, self.text(name), &self.b),
                false,
                &self.b,
            )
        } else {
            Expression::new_computed_member_expression(
                SPAN,
                target,
                self.string_expr(name),
                false,
                &self.b,
            )
        }
    }
    pub fn target(&self, e: Expression<'a>) -> Result<AssignmentTarget<'a>, Unsupported> {
        Ok(match e {
            Expression::StaticMemberExpression(m) => AssignmentTarget::StaticMemberExpression(m),
            Expression::ComputedMemberExpression(m) => {
                AssignmentTarget::ComputedMemberExpression(m)
            }
            Expression::Identifier(id) => AssignmentTarget::AssignmentTargetIdentifier(id),
            _ => return Err(Unsupported("assignment target")),
        })
    }
    pub fn expression_statement(&self, expression: Expression<'a>) -> Statement<'a> {
        Statement::new_expression_statement(SPAN, expression, &self.b)
    }
    fn unary(&self, operator: U, argument: Expression<'a>) -> Expression<'a> {
        Expression::new_unary_expression(SPAN, operator, argument, &self.b)
    }
    fn binary(&self, operator: B, left: Expression<'a>, right: Expression<'a>) -> Expression<'a> {
        Expression::new_binary_expression(SPAN, left, operator, right, &self.b)
    }
    fn number(&self, n: &Number) -> Result<Expression<'a>, Unsupported> {
        if let Number::BigInt(n) = n {
            // Keep lexical radix normalization explicit rather than guessing from digits.
            if !n.value.chars().all(|c| c.is_ascii_digit()) {
                return Err(Unsupported("non-decimal bigint"));
            }
            let e = Expression::new_big_int_literal(
                SPAN,
                self.text(&n.value),
                None,
                BigintBase::Decimal,
                &self.b,
            );
            return Ok(if n.positive {
                e
            } else {
                self.unary(U::UnaryNegation, e)
            });
        }
        let value = match n {
            Number::Int { i, .. } => *i as f64,
            Number::Float(f) => normalize_float_literal_for_js(&f.f)
                .parse::<f64>()
                .map_err(|_| Unsupported("float literal"))?,
            Number::BigInt(_) => unreachable!(),
        };
        let e = if value.is_nan() {
            self.id("NaN")
        } else if value.is_infinite() {
            self.id("Infinity")
        } else {
            Expression::new_numeric_literal(SPAN, value.abs(), None, NumberBase::Decimal, &self.b)
        };
        Ok(if value.is_sign_negative() {
            self.unary(U::UnaryNegation, e)
        } else {
            e
        })
    }
    fn args(&self, args: &[Expr]) -> Result<ArenaVec<'a, Argument<'a>>, Unsupported> {
        let mut result = self.b.vec();
        for e in args {
            result.push(if let ExprKind::Spread(inner) = self.arena.ek(*e) {
                Argument::SpreadElement(self.b.alloc(SpreadElement::new(
                    SPAN,
                    self.expr(inner)?,
                    &self.b,
                )))
            } else {
                Argument::from(self.expr(*e)?)
            });
        }
        Ok(result)
    }
    fn sequence(&self, e: Expr, out: &mut ArenaVec<'a, Expression<'a>>) -> Result<(), Unsupported> {
        if let ExprKind::Seq(l, r) = self.arena.ek(e) {
            self.sequence(l, out)?;
            self.sequence(r, out)?;
        } else {
            out.push(self.expr(e)?);
        }
        Ok(())
    }
    // The legacy printer omits parentheses on either side of these chains.
    fn chain(&self, op: BinOp, e: Expr, out: &mut Vec<Expr>) {
        if let ExprKind::Bin(child, l, r) = self.arena.ek(e)
            && child == op
        {
            self.chain(op, l, out);
            self.chain(op, r, out);
        } else {
            out.push(e);
        }
    }
    fn bin(&self, op: BinOp, l: Expr, r: Expr) -> Result<Expression<'a>, Unsupported> {
        if walk::negation_form(self.arena, op, l) {
            return Ok(self.unary(U::UnaryNegation, self.expr(r)?));
        }
        if walk::possible_nullish(self.arena, op, l, r) {
            return Err(Unsupported("nullish comparison rewrite"));
        }
        if matches!(op, BinOp::And | BinOp::Or | BinOp::Bor) {
            let mut operands = Vec::new();
            self.chain(op, l, &mut operands);
            self.chain(op, r, &mut operands);
            let mut iter = operands.into_iter();
            let mut expr = self.expr(iter.next().expect("two operands"))?;
            for e in iter {
                let right = self.expr(e)?;
                expr = if op == BinOp::Bor {
                    self.binary(B::BitwiseOR, expr, right)
                } else {
                    Expression::new_logical_expression(
                        SPAN,
                        expr,
                        if op == BinOp::And { L::And } else { L::Or },
                        right,
                        &self.b,
                    )
                };
            }
            return Ok(expr);
        }
        let operator = match op {
            BinOp::Eq => return Err(Unsupported("assignment")),
            BinOp::Bnot => return Err(Unsupported("binary bitwise-not")),
            BinOp::EqEqEq => B::StrictEquality,
            BinOp::NotEqEq => B::StrictInequality,
            BinOp::Lt | BinOp::FloatLt => B::LessThan,
            BinOp::Le | BinOp::FloatLe => B::LessEqualThan,
            BinOp::Gt | BinOp::FloatGt => B::GreaterThan,
            BinOp::Ge | BinOp::FloatGe => B::GreaterEqualThan,
            BinOp::Bxor => B::BitwiseXOR,
            BinOp::Band => B::BitwiseAnd,
            BinOp::Lsl => B::ShiftLeft,
            BinOp::Lsr => B::ShiftRightZeroFill,
            BinOp::Asr => B::ShiftRight,
            BinOp::Plus => B::Addition,
            BinOp::Minus => B::Subtraction,
            BinOp::Mul => B::Multiplication,
            BinOp::Div => B::Division,
            BinOp::Mod => B::Remainder,
            BinOp::Pow => B::Exponential,
            BinOp::InstanceOf => B::Instanceof,
            BinOp::In => B::In,
            BinOp::And | BinOp::Or | BinOp::Bor => unreachable!(),
        };
        Ok(self.binary(operator, self.expr(l)?, self.expr(r)?))
    }
    pub fn expr(&self, e: Expr) -> Result<Expression<'a>, Unsupported> {
        let a = self.arena;
        if a.expr_comment(e).is_some() {
            return Err(Unsupported("expression comment"));
        }
        Ok(match a.ek(e) {
            ExprKind::Var(id) => self.id(self.names.get(&a.ident(id))),
            ExprKind::Qualified(q) => {
                let (m, field) = a.qual(q);
                let base = self.id(self.names.get(&m.id));
                match field {
                    None => base,
                    Some(_) if matches!(m.kind, Kind::External { default: true, .. }) => base,
                    Some(s) => self.member(
                        base,
                        &if matches!(m.kind, Kind::Ml | Kind::Runtime) {
                            js_export_name(s)
                        } else {
                            s.into()
                        },
                    ),
                }
            }
            ExprKind::Number(n) => self.number(a.number(n))?,
            ExprKind::Str(s) => self.string_expr(a.text(s)),
            ExprKind::Bool(b) => Expression::new_boolean_literal(SPAN, b, &self.b),
            ExprKind::Null => Expression::new_null_literal(SPAN, &self.b),
            ExprKind::Undefined { .. } => self.id("undefined"),
            ExprKind::Bin(op, l, r) => self.bin(op, l, r)?,
            ExprKind::StringAppend(_, _) => {
                return Err(Unsupported("string concatenation association"));
            }
            ExprKind::In(l, r) => self.binary(B::In, self.expr(l)?, self.expr(r)?),
            ExprKind::IsNullOrUndefined(e) => self.binary(
                B::Equality,
                self.expr(e)?,
                Expression::new_null_literal(SPAN, &self.b),
            ),
            ExprKind::JsNot(e) => self.unary(U::LogicalNot, self.expr(e)?),
            ExprKind::JsBnot(e) => self.unary(U::BitwiseNot, self.expr(e)?),
            ExprKind::Typeof(e) => self.unary(U::Typeof, self.expr(e)?),
            ExprKind::Cond(c, t, f) => Expression::new_conditional_expression(
                SPAN,
                self.expr(c)?,
                self.expr(t)?,
                self.expr(f)?,
                &self.b,
            ),
            ExprKind::Seq(..) => {
                let mut expressions = self.b.vec();
                self.sequence(e, &mut expressions)?;
                Expression::new_sequence_expression(SPAN, expressions, &self.b)
            }
            ExprKind::Call(f, args, _) => Expression::new_call_expression(
                SPAN,
                self.expr(f)?,
                None,
                self.args(walk::arguments(a, a.exprs(args)))?,
                false,
                &self.b,
            ),
            ExprKind::New(f, args) => Expression::new_new_expression(
                SPAN,
                self.expr(f)?,
                None,
                self.args(args.map_or(&[], |args| a.exprs(args)))?,
                &self.b,
            ),
            ExprKind::StaticIndex(e, s, _) | ExprKind::CamlBlockTag(e, s) => {
                self.member(self.expr(e)?, a.text(s))
            }
            ExprKind::Length(e, _) => self.member(self.expr(e)?, "length"),
            ExprKind::ArrayIndex(e, i) => Expression::new_computed_member_expression(
                SPAN,
                self.expr(e)?,
                self.expr(i)?,
                false,
                &self.b,
            ),
            ExprKind::Array(items, _) => {
                let mut elements = self.b.vec();
                for e in a.exprs(items) {
                    elements.push(if let ExprKind::Spread(e) = a.ek(*e) {
                        ArrayExpressionElement::SpreadElement(self.b.alloc(SpreadElement::new(
                            SPAN,
                            self.expr(e)?,
                            &self.b,
                        )))
                    } else {
                        ArrayExpressionElement::from(self.expr(*e)?)
                    });
                }
                Expression::new_array_expression(SPAN, elements, &self.b)
            }
            ExprKind::Object(props) => {
                let mut properties = self.b.vec();
                for (key, value) in a.props(props) {
                    if key.is_spread() {
                        properties.push(ObjectPropertyKind::SpreadProperty(
                            self.b
                                .alloc(SpreadElement::new(SPAN, self.expr(*value)?, &self.b)),
                        ));
                        continue;
                    }
                    let PropName::Lit(s) = key else {
                        return Err(Unsupported("symbol object key"));
                    };
                    let (name, dot) = walk::member_form(a.text(*s));
                    let computed = name == "__proto__";
                    let key = if dot && !computed {
                        PropertyKey::StaticIdentifier(self.b.alloc(IdentifierName::new(
                            SPAN,
                            self.text(name),
                            &self.b,
                        )))
                    } else {
                        PropertyKey::from(self.string_expr(name))
                    };
                    properties.push(ObjectPropertyKind::ObjectProperty(self.b.alloc(
                        ObjectProperty::new(
                            SPAN,
                            PropertyKind::Init,
                            key,
                            self.expr(*value)?,
                            false,
                            false,
                            computed,
                            &self.b,
                        ),
                    )));
                }
                Expression::new_object_expression(SPAN, properties, &self.b)
            }
            ExprKind::Fun(f) => self.function_expr(f)?,
            ExprKind::Await(e) => Expression::new_await_expression(SPAN, self.expr(e)?, &self.b),
            ExprKind::OptionalBlock(e, true) => self.expr(e)?,
            ExprKind::OptionalBlock(_, false) => return Err(Unsupported("optional block helper")),
            ExprKind::CamlBlock(..) => return Err(Unsupported("block literal shape")),
            ExprKind::RawJsCode(_) => return Err(Unsupported("raw JavaScript")),
            ExprKind::Jsx(_) => return Err(Unsupported("JSX")),
            ExprKind::TemplateLiteral(_)
            | ExprKind::InterpolatedTemplate(..)
            | ExprKind::TaggedTemplate(..) => return Err(Unsupported("template literal")),
            ExprKind::JsonLiteral(_) => return Err(Unsupported("JSON literal")),
            ExprKind::FlatCall(..) => return Err(Unsupported("flat call")),
            ExprKind::Spread(_) => return Err(Unsupported("standalone spread")),
            ExprKind::RecordRest(..) => return Err(Unsupported("record rest")),
        })
    }
    fn params(&self, f: FunId) -> oxc_allocator::Box<'a, FormalParameters<'a>> {
        let mut items = self.b.vec();
        for id in self.arena.ident_slice(self.arena.fun(f).params) {
            let pattern =
                BindingPattern::BindingIdentifier(self.b.alloc(self.binding(self.names.get(id))));
            items.push(FormalParameter::new(
                SPAN,
                self.b.vec(),
                pattern,
                None,
                None,
                false,
                None,
                false,
                false,
                &self.b,
            ));
        }
        self.b.alloc(FormalParameters::new(
            SPAN,
            FormalParameterKind::FormalParameter,
            items,
            None,
            &self.b,
        ))
    }
    fn function_body(
        &self,
        f: FunId,
    ) -> Result<oxc_allocator::Box<'a, FunctionBody<'a>>, Unsupported> {
        let info = self.arena.fun(f);
        let body = walk::function_body(self.arena, self.arena.stmts(info.body));
        let mut statements = self.b.vec();
        for (index, s) in body.iter().enumerate() {
            self.stmt(
                *s,
                false,
                (index + 1 == body.len()).then_some(info.return_unit),
                &mut statements,
            )?;
        }
        Ok(self
            .b
            .alloc(FunctionBody::new(SPAN, self.b.vec(), statements, &self.b)))
    }
    fn function_expr(&self, f: FunId) -> Result<Expression<'a>, Unsupported> {
        let body = match walk::function_form(self.arena, f, false)? {
            walk::FunctionForm::Eta(e) => return self.expr(e),
            walk::FunctionForm::ArrowExpression(e) => ArrowFunctionBody::from(self.expr(e)?),
            walk::FunctionForm::ArrowEmpty => ArrowFunctionBody::FunctionBody(
                self.b
                    .alloc(FunctionBody::new(SPAN, self.b.vec(), self.b.vec(), &self.b)),
            ),
            walk::FunctionForm::ArrowBlock => {
                ArrowFunctionBody::FunctionBody(self.function_body(f)?)
            }
            walk::FunctionForm::Declaration => unreachable!(),
        };
        Ok(Expression::new_arrow_function_expression(
            SPAN,
            self.arena.fun(f).async_,
            None,
            self.params(f),
            None,
            body,
            &self.b,
        ))
    }
    pub fn block(
        &self,
        block: &[Stmt],
        top: bool,
    ) -> Result<ArenaVec<'a, Statement<'a>>, Unsupported> {
        let mut result = self.b.vec();
        for s in block {
            self.stmt(*s, top, None, &mut result)?;
        }
        Ok(result)
    }
    fn effect(&self, e: Expr, out: &mut ArenaVec<'a, Statement<'a>>) -> Result<(), Unsupported> {
        if !walk::omitted_expression(self.arena, e) {
            out.push(self.expression_statement(self.expr(e)?));
        }
        Ok(())
    }
    fn stmt(
        &self,
        s: Stmt,
        top: bool,
        tail: Option<bool>,
        out: &mut ArenaVec<'a, Statement<'a>>,
    ) -> Result<(), Unsupported> {
        let a = self.arena;
        if a.stmt_comment(s).is_some() {
            return Err(Unsupported("statement comment"));
        }
        match a.sk(s) {
            StmtKind::Block(b) => out.extend(self.block(a.stmts(b), false)?),
            StmtKind::Variable(v) => {
                let decl = a.var(v);
                match walk::prints_declaration(decl) {
                    walk::Declaration::Omit => return Ok(()),
                    walk::Declaration::Effect(e) => return self.effect(e, out),
                    walk::Declaration::Binding => {}
                }
                let name = self.names.get(&decl.ident);
                if let Some(e) = decl.value
                    && let ExprKind::Fun(f) = a.ek(e)
                {
                    match walk::function_form(a, f, top)? {
                        walk::FunctionForm::Declaration => {
                            out.push(Statement::new_function_declaration(
                                SPAN,
                                FunctionType::FunctionDeclaration,
                                Some(self.binding(name)),
                                false,
                                a.fun(f).async_,
                                false,
                                None,
                                None,
                                self.params(f),
                                None,
                                Some(self.function_body(f)?),
                                &self.b,
                            ));
                            return Ok(());
                        }
                        walk::FunctionForm::Eta(e) => {
                            out.push(self.variable(name, Some(self.expr(e)?)));
                            return Ok(());
                        }
                        _ => {}
                    }
                }
                let init = decl
                    .value
                    .filter(|e| !walk::undefined(a, *e))
                    .map(|e| self.expr(e))
                    .transpose()?;
                out.push(self.variable(name, init));
            }
            StmtKind::Exp(e) => self.effect(e, out)?,
            StmtKind::Return(e) if tail.is_some() && walk::undefined(a, e) => {}
            StmtKind::Return(_) if tail == Some(true) => {
                return Err(Unsupported("unit function tail effect"));
            }
            StmtKind::Return(e) => out.push(Statement::new_return_statement(
                SPAN,
                if walk::undefined(a, e) {
                    None
                } else {
                    Some(self.expr(e)?)
                },
                &self.b,
            )),
            StmtKind::If(c, t, f) => {
                let f = a.stmts(f);
                let omit = walk::else_omitted(a, f)
                    || (tail.is_some() && matches!(f, [s] if walk::return_undefined(a, *s)));
                let alternate = if omit {
                    None
                } else if let Some(s) = walk::else_if(a, f) {
                    let mut nested = self.b.vec();
                    self.stmt(s, false, None, &mut nested)?;
                    Some(nested.pop().expect("if emits a statement"))
                } else {
                    Some(Statement::new_block_statement(
                        SPAN,
                        self.block(f, false)?,
                        &self.b,
                    ))
                };
                out.push(Statement::new_if_statement(
                    SPAN,
                    self.expr(c)?,
                    Statement::new_block_statement(SPAN, self.block(a.stmts(t), false)?, &self.b),
                    alternate,
                    &self.b,
                ));
            }
            StmtKind::Debugger => out.push(Statement::new_debugger_statement(SPAN, &self.b)),
            StmtKind::While(..)
            | StmtKind::ForRange(_)
            | StmtKind::ForOf(_)
            | StmtKind::ForAwaitOf(_) => return Err(Unsupported("loop")),
            StmtKind::IntSwitch(..) | StmtKind::StringSwitch(..) => {
                return Err(Unsupported("switch"));
            }
            StmtKind::Try(_) => return Err(Unsupported("try")),
            StmtKind::Throw(_) => return Err(Unsupported("throw")),
            StmtKind::Break(_) | StmtKind::Continue(_) => {
                return Err(Unsupported("break/continue"));
            }
        }
        Ok(())
    }
}

/// Small allocation helpers shared with program assembly.
pub(super) trait Allocate<'a>: GetAllocator<'a> {
    fn alloc<T>(&self, value: T) -> oxc_allocator::Box<'a, T> {
        oxc_allocator::Box::new_in(value, &self.allocator())
    }
    fn vec<T>(&self) -> ArenaVec<'a, T> {
        ArenaVec::new_in(&self.allocator())
    }
    fn vec1<T>(&self, value: T) -> ArenaVec<'a, T> {
        let mut v = self.vec();
        v.push(value);
        v
    }
}
impl<'a> Allocate<'a> for AstBuilder<'a> {}
