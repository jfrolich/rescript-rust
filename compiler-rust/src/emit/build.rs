//! The only expression/statement layer that knows oxc AST types.
use super::{Unsupported, literal, naming::Names, walk};
use crate::js_ir::arena::{Expr, ExprKind, FunId, JsArena, PropName, Stmt, StmtKind};
use crate::js_ir::op::{BinOp, Kind, Number};
use crate::js_ir::printer::{js_export_name, normalize_float_literal_for_js};
use oxc_allocator::{Allocator, GetAllocator, Vec as ArenaVec};
use oxc_ast::{ast::*, builder::AstBuilder};
use oxc_span::{SPAN, GetSpanMut};
use oxc_syntax::{
    number::{BigintBase, NumberBase},
    operator::{BinaryOperator as B, LogicalOperator as L, UnaryOperator as U},
};

pub(super) struct Build<'a, 'r> {
    pub b: AstBuilder<'a>,
    pub arena: &'r JsArena,
    pub names: &'r Names,
    pub debug: bool,
    pub jsx_preserve: bool,
    rest_name: std::cell::RefCell<String>,
    chain_tasks: std::cell::RefCell<Vec<Expr>>,
    jsx_indent: std::cell::Cell<usize>,
    suppress_call_indent: std::cell::Cell<bool>,
    string_tasks: std::cell::RefCell<Vec<(Expr, bool)>>,
    string_values: std::cell::RefCell<Vec<Expression<'a>>>,
    pub raw_prefix: &'a str,
    pub raw_pieces: std::cell::RefCell<ArenaVec<'a, super::raw::Piece<'a>>>,
    // S1.2: absent on the default, location-free path.
    pub source_map: Option<&'r super::sourcemap::Spans>,
}
impl<'a, 'r> Build<'a, 'r> {
    pub fn new(alloc: &'a Allocator, arena: &'r JsArena, names: &'r Names) -> Self {
        let mut prefix = oxc_allocator::StringBuilder::from_str_in(super::raw::PREFIX, alloc);
        let prefix_len = names.raw_prefix_len();
        while prefix.len() < prefix_len {
            prefix.push('_');
        }
        Self {
            b: AstBuilder::new(alloc),
            raw_prefix: prefix.into_str(),
            raw_pieces: std::cell::RefCell::new(ArenaVec::new_in(&alloc)),
            arena,
            names,
            debug: false,
            jsx_preserve: false,
            rest_name: Default::default(),
            chain_tasks: Default::default(),
            jsx_indent: Default::default(),
            suppress_call_indent: Default::default(),
            string_tasks: Default::default(),
            string_values: Default::default(),
            source_map: None,
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
            literal::arena_string(value, self.b.allocator()),
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
                if let Some(index) = walk::numeric_member(name) {
                    let value = Expression::new_numeric_literal(
                        SPAN,
                        index.unsigned_abs() as f64,
                        None,
                        NumberBase::Decimal,
                        &self.b,
                    );
                    if index < 0 {
                        self.unary(U::UnaryNegation, value)
                    } else {
                        value
                    }
                } else {
                    self.string_expr(name)
                },
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
    fn argument(&self, e: Expr, level: u8) -> Result<Expression<'a>, Unsupported> {
        let extra = !self.suppress_call_indent.get()
            && crate::js_ir::printer::call_argument_needs_extra_group_indent(
                self.arena,
                e,
                level,
                self.jsx_indent.get(),
            );
        self.indented_expr(e, usize::from(extra))
    }
    fn args(&self, args: &[Expr], level: u8) -> Result<ArenaVec<'a, Argument<'a>>, Unsupported> {
        let mut result = self.b.vec();
        for e in args {
            result.push(if let ExprKind::Spread(inner) = self.arena.ek(*e) {
                Argument::SpreadElement(self.b.alloc(SpreadElement::new(
                    SPAN,
                    self.expr(inner)?,
                    &self.b,
                )))
            } else {
                Argument::from(self.argument(*e, level)?)
            });
        }
        Ok(result)
    }
    /// Record-rest expressions are an immediately called destructuring arrow;
    /// declarations instead bind the real fields and rest name. Synthetic names
    /// __unusedN and __rest never enter naming. Only source is an expression.
    fn rest_pattern(
        &self,
        fields: crate::js_ir::arena::RestId,
        rest: &str,
        declaration: bool,
    ) -> BindingPattern<'a> {
        use std::fmt::Write;
        let mut props = self.b.vec();
        let mut synthetic = self.rest_name.borrow_mut();
        for (i, field) in self.arena.rest(fields).iter().enumerate() {
            let name = if declaration {
                field
                    .ident
                    .as_ref()
                    .map(|id| self.names.get(id))
                    .unwrap_or(&field.label)
            } else {
                synthetic.clear();
                write!(synthetic, "__unused{i}").expect("writing a String cannot fail");
                &synthetic
            };
            let computed = field.label == "__proto__";
            let (label, bare) = walk::member_form(&field.label);
            let key = if bare && !computed {
                PropertyKey::StaticIdentifier(self.b.alloc(IdentifierName::new(
                    SPAN,
                    self.text(label),
                    &self.b,
                )))
            } else {
                PropertyKey::from(self.string_expr(label))
            };
            props.push(BindingProperty::new(
                SPAN,
                key,
                BindingPattern::BindingIdentifier(self.b.alloc(self.binding(name))),
                declaration && name == field.label,
                computed,
                &self.b,
            ));
        }
        BindingPattern::ObjectPattern(self.b.alloc(ObjectPattern::new(
            SPAN,
            props,
            Some(self.b.alloc(BindingRestElement::new(
                SPAN,
                BindingPattern::BindingIdentifier(self.b.alloc(self.binding(rest))),
                &self.b,
            ))),
            &self.b,
        )))
    }

    fn record_rest(
        &self,
        fields: crate::js_ir::arena::RestId,
        source: Expr,
    ) -> Result<Expression<'a>, Unsupported> {
        let param = FormalParameter::new(
            SPAN,
            self.b.vec(),
            self.rest_pattern(fields, "__rest", false),
            None,
            None,
            false,
            None,
            false,
            false,
            &self.b,
        );
        let params = self.b.alloc(FormalParameters::new(
            SPAN,
            FormalParameterKind::FormalParameter,
            self.b.vec1(param),
            None,
            &self.b,
        ));
        let callee = Expression::new_arrow_function_expression(
            SPAN,
            false,
            None,
            params,
            None,
            ArrowFunctionBody::from(self.id("__rest")),
            &self.b,
        );
        Ok(self.call(callee, self.b.vec1(Argument::from(self.expr(source)?))))
    }

    /// Runtime JSX prints callee(tag, props[, key]). Names are encountered in
    /// that order, with spread before properties and children. oxc supplies
    /// call/object/array parentheses, matching printer::print_jsx_call.
    fn jsx_call(
        &self,
        id: crate::js_ir::arena::JsxId,
        level: u8,
    ) -> Result<Expression<'a>, Unsupported> {
        let (jsx, form) = walk::jsx_form(self.arena, id, self.jsx_preserve)?;
        match form {
            walk::JsxForm::Fragment => {
                return Ok(Expression::new_jsx_fragment(
                    SPAN,
                    JSXOpeningFragment::new(SPAN, &self.b),
                    self.jsx_children(&jsx, false)?,
                    JSXClosingFragment::new(SPAN, &self.b),
                    &self.b,
                ));
            }
            walk::JsxForm::Element => return self.jsx_element(&jsx),
            walk::JsxForm::Runtime => {}
        }
        let callee = self.expr_at(jsx.callee, 15)?;
        let mut args = self.b.vec1(Argument::from(self.argument(jsx.tag, level)?));
        let props = self.arena.props(jsx.props);
        let extra = usize::from(
            level == 15 && self.jsx_indent.get() == 0 && !self.suppress_call_indent.get(),
        );
        let value = if let Some(spread) = jsx
            .spread
            .filter(|_| props.is_empty() && jsx.children.is_none())
        {
            self.argument(spread, level)?
        } else {
            let mut properties = self.b.vec();
            if let Some(spread) = jsx.spread {
                properties.push(ObjectPropertyKind::SpreadProperty(self.b.alloc(
                    SpreadElement::new(
                        SPAN,
                        self.with_indent(1 + extra, || self.high_expr(spread))?,
                        &self.b,
                    ),
                )));
            }
            for (key, value) in props {
                let PropName::Lit(name) = key else {
                    return Err(Unsupported("symbol JSX key"));
                };
                properties.push(self.block_property(
                    self.arena.text(*name),
                    self.indented_expr(*value, 1 + extra)?,
                ));
            }
            if let Some(children) = jsx.children {
                let children = self.arena.exprs(children);
                let value = if let [child] = children
                    && !jsx.multi
                {
                    self.indented_expr(*child, 1 + extra)?
                } else {
                    let mut elements = self.b.vec();
                    for child in children {
                        elements.push(ArrayExpressionElement::from(
                            self.indented_expr(*child, 2 + extra)?,
                        ));
                    }
                    Expression::new_array_expression(SPAN, elements, &self.b)
                };
                properties.push(self.block_property("children", value));
            }
            Expression::new_object_expression(SPAN, properties, &self.b)
        };
        args.push(Argument::from(value));
        if let Some(key) = jsx.key {
            args.push(Argument::from(self.argument(key, level)?));
        }
        Ok(self.call(callee, args))
    }

    fn jsx_tag(&self, tag: Expr) -> Result<JSXElementName<'a>, Unsupported> {
        if let ExprKind::Str(name) = self.arena.ek(tag) {
            return Ok(JSXElementName::Identifier(self.b.alloc(
                JSXIdentifier::new(SPAN, self.text(self.arena.text(name)), &self.b),
            )));
        }
        let mut value = self.expr(tag)?;
        let mut properties = self.b.vec();
        while let Expression::StaticMemberExpression(member) = value {
            let member = member.unbox();
            properties.push(member.property.name);
            value = member.object;
        }
        let Expression::Identifier(id) = value else {
            return Err(Unsupported("JSX computed tag"));
        };
        if properties.is_empty() {
            return Ok(JSXElementName::IdentifierReference(id));
        }
        let mut object = JSXMemberExpressionObject::IdentifierReference(id);
        while let Some(name) = properties.pop() {
            object = JSXMemberExpressionObject::new_member_expression(
                SPAN,
                object,
                JSXIdentifier::new(SPAN, name, &self.b),
                &self.b,
            );
        }
        let JSXMemberExpressionObject::MemberExpression(member) = object else {
            unreachable!()
        };
        Ok(JSXElementName::MemberExpression(member))
    }

    /// Every legacy JSX attribute is an expression container, even strings.
    /// Preserve key-before-spread ordering; tag and attribute spelling are
    /// checked by the same jsx_form decision used in naming.
    fn jsx_element(
        &self,
        jsx: &crate::js_ir::arena::JsxInfo,
    ) -> Result<Expression<'a>, Unsupported> {
        let mut attributes = self.b.vec();
        let attribute = |name: &str, value: Expr| -> Result<JSXAttributeItem<'a>, Unsupported> {
            Ok(JSXAttributeItem::Attribute(self.b.alloc(
                JSXAttribute::new(
                    SPAN,
                    JSXAttributeName::Identifier(self.b.alloc(JSXIdentifier::new(
                        SPAN,
                        self.text(name),
                        &self.b,
                    ))),
                    Some(JSXAttributeValue::ExpressionContainer(self.b.alloc(
                        JSXExpressionContainer::new(
                            SPAN,
                            JSXExpression::from(self.indented_expr(value, 1)?),
                            &self.b,
                        ),
                    ))),
                    &self.b,
                ),
            )))
        };
        let name = self.jsx_tag(jsx.tag)?;
        if let Some(key) = jsx.key {
            attributes.push(attribute("key", key)?);
        }
        if let Some(spread) = jsx.spread {
            attributes.push(JSXAttributeItem::SpreadAttribute(self.b.alloc(
                JSXSpreadAttribute::new(
                    SPAN,
                    self.with_indent(1, || self.high_expr(spread))?,
                    &self.b,
                ),
            )));
        }
        for (key, value) in self.arena.props(jsx.props) {
            let PropName::Lit(key) = key else {
                unreachable!("validated JSX property")
            };
            attributes.push(attribute(
                walk::member_form(self.arena.text(*key)).0,
                *value,
            )?);
        }
        let children = self.jsx_children(jsx, !attributes.is_empty())?;
        let closing = if jsx.children.is_some() {
            Some(self.b.alloc(JSXClosingElement::new(
                SPAN,
                self.jsx_tag(jsx.tag)?,
                &self.b,
            )))
        } else {
            None
        };
        Ok(Expression::new_jsx_element(
            SPAN,
            self.b.alloc(JSXOpeningElement::new(
                SPAN, name, None, attributes, &self.b,
            )),
            children,
            closing,
            &self.b,
        ))
    }

    fn jsx_children(
        &self,
        jsx: &crate::js_ir::arena::JsxInfo,
        has_attrs: bool,
    ) -> Result<ArenaVec<'a, JSXChild<'a>>, Unsupported> {
        let mut children = self.b.vec();
        let Some(list) = jsx.children else {
            return Ok(children);
        };
        let expressions = self.arena.exprs(list);
        let whitespace = |indent: usize| {
            let text = self.text(&format!("\n{}", "  ".repeat(indent)));
            JSXChild::Text(
                self.b
                    .alloc(JSXText::new(SPAN, text, Some(text.into()), &self.b)),
            )
        };
        for e in expressions {
            children.push(whitespace(self.jsx_indent.get() + 1));
            let expression = self.indented_expr(*e, 1)?;
            children.push(match expression {
                Expression::JSXElement(element) => JSXChild::Element(element),
                Expression::JSXFragment(fragment) => JSXChild::Fragment(fragment),
                value => JSXChild::ExpressionContainer(self.b.alloc(JSXExpressionContainer::new(
                    SPAN,
                    JSXExpression::from(value),
                    &self.b,
                ))),
            });
        }
        if has_attrs || !expressions.is_empty() {
            children.push(whitespace(self.jsx_indent.get()));
        }
        Ok(children)
    }

    fn call(&self, callee: Expression<'a>, args: ArenaVec<'a, Argument<'a>>) -> Expression<'a> {
        Expression::new_call_expression(SPAN, callee, None, args, false, &self.b)
    }

    /// StringAppend uses Plus's (11, 11, 12) precedence in the legacy printer:
    /// the right child remains grouped, unlike logical chains. Visit leaves
    /// left to right and build postorder without recursing through the chain.
    fn string_append(&self, root: Expr) -> Result<Expression<'a>, Unsupported> {
        if self.source_map.is_some() {
            return Err(Unsupported("source map: string concatenation"));
        }
        let mut tasks = self.string_tasks.take();
        let mut values = self.string_values.take();
        tasks.push((root, false));
        let result = (|| {
            while let Some((expr, finish)) = tasks.pop() {
                walk::expression_comment(self.arena, expr)?;
                if let Some((left, right)) = walk::string_children(self.arena, expr) {
                    if finish {
                        let right = values.pop().unwrap();
                        let left = values.pop().unwrap();
                        values.push(self.binary(B::Addition, left, right));
                    } else {
                        tasks.push((expr, true));
                        tasks.push((right, false));
                        tasks.push((left, false));
                    }
                } else {
                    values.push(self.high_expr(expr)?);
                }
            }
            Ok(values.pop().unwrap())
        })();
        tasks.clear();
        values.clear();
        self.string_tasks.replace(tasks);
        self.string_values.replace(values);
        result
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
    fn bin(&self, op: BinOp, l: Expr, r: Expr) -> Result<Expression<'a>, Unsupported> {
        if walk::negation_form(self.arena, op, l) {
            return Ok(self.unary(U::UnaryNegation, self.high_expr(r)?));
        }
        if let Some(target) = walk::nullish_target(self.arena, op, l, r)? {
            return Ok(self.binary(
                B::Equality,
                self.high_expr(target)?,
                Expression::new_null_literal(SPAN, &self.b),
            ));
        }
        if matches!(op, BinOp::And | BinOp::Or | BinOp::Bor) {
            let mut pending = self.chain_tasks.take();
            pending.extend([r, l]);
            let result = (|| {
                let mut value = None;
                while let Some(e) = pending.pop() {
                    if let Some((l, r)) = walk::chain_children(self.arena, op, e)? {
                        pending.extend([r, l]);
                        continue;
                    }
                    let right = self.high_expr(e)?;
                    value = Some(match value {
                        None => right,
                        Some(left) if op == BinOp::Bor => self.binary(B::BitwiseOR, left, right),
                        Some(left) => Expression::new_logical_expression(
                            SPAN, left, if op == BinOp::And { L::And } else { L::Or }, right, &self.b),
                    });
                }
                Ok(value.expect("binary chain has operands"))
            })();
            pending.clear();
            self.chain_tasks.replace(pending);
            return result;
        }

        let operator = match op {
            BinOp::Eq => {
                walk::assignment_target(self.arena, l)?;
                return Ok(Expression::new_assignment_expression(
                    SPAN,
                    oxc_syntax::operator::AssignmentOperator::Assign,
                    self.target(self.expr(l)?)?,
                    self.expr(r)?,
                    &self.b,
                ));
            }
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
            BinOp::And | BinOp::Or | BinOp::Bor => unreachable!(),
        };
        Ok(self.binary(operator, self.high_expr(l)?, self.high_expr(r)?))
    }
    /// Shapes from `js_ir::printer::print_caml_block` (OCaml js_dump.ml:859-947).
    ///
    /// | Tag info | JavaScript shape |
    /// | --- | --- |
    /// | Record, array=true | array, including undefined elements |
    /// | Record, matching field count | named object |
    /// | RecordInlined, matching count | named object; tagged runtime prepends tag |
    /// | Module, matching count | object with identifier-mangled field names |
    /// | Constructor `::` | hd, tl, then _2, _3, ...; no tag |
    /// | Other Constructor | tag (custom name or TAG), _0, _1, ...; debug symbol last |
    /// | PolyVar | NAME from first element, VAL from second if present |
    /// | Extension | RE_EXN_ID, _1, _2, ... |
    /// | RecordExt | RE_EXN_ID, named fields, positional fallback for missing names |
    /// | Tuple, Some, SomeNotNested, ModuleExport, mismatched record/module | array |
    ///
    /// Mutable flags never affect printing. Only optional record/inlined-record
    /// fields whose expression is literally Undefined are omitted; required and
    /// extension fields retain undefined. Untagged inline records omit the tag;
    /// scalar unboxed and lazy forms are already lowered before this IR. Exception
    /// literals here have no Error stack field (that belongs to throw printing).
    /// Keys follow literal-property spelling, not member-access spelling: numeric
    /// names remain strings and __proto__ is computed. No property is shorthand.
    fn caml_block(
        &self,
        elements: &[Expr],
        tag: &crate::lambda::TagInfo,
    ) -> Result<Expression<'a>, Unsupported> {
        use crate::lambda::TagInfo;
        walk::block_supported(elements, tag)?;
        let children = || walk::block_elements(self.arena, elements, tag);
        let mut properties = self.b.vec();
        let mut indexed = String::with_capacity(21); // One scratch buffer per block, not per field.
        let mut field = |name: &str, value: Expr| -> Result<(), Unsupported> {
            properties.push(self.block_property(name, self.expr(value)?));
            Ok(())
        };
        match tag {
            TagInfo::Record(r) if !r.array && r.fields.len() == elements.len() => {
                for (i, value) in children() {
                    field(&r.fields[i].0, value)?;
                }
            }
            TagInfo::RecordInlined(r) if r.fields.len() == elements.len() => {
                if let crate::types::VariantBlock::Tagged(t) = &*r.runtime {
                    properties.push(self.block_property(
                        t.tag_name.as_deref().unwrap_or("TAG"),
                        self.block_tag(&t.tag.literal)?,
                    ));
                }
                for (i, value) in children() {
                    properties.push(self.block_property(&r.fields[i].0, self.expr(value)?));
                }
            }
            TagInfo::Module(names) if names.len() == elements.len() => {
                // Longest replacement is $question (9 bytes); reserve once.
                let mut scratch = String::with_capacity(
                    2 + names.iter().map(|s| s.len()).max().unwrap_or(0) * 9,
                );
                for (i, value) in children() {
                    field(literal::module_field(&names[i], &mut scratch), value)?;
                }
            }
            TagInfo::Constructor(c) => {
                if c.name != "::" {
                    properties.push(self.block_property(
                        c.runtime.tag_name.as_deref().unwrap_or("TAG"),
                        self.block_tag(&c.runtime.tag.literal)?,
                    ));
                }
                for (i, value) in children() {
                    let name = if c.name == "::" && i < 2 {
                        if i == 0 { "hd" } else { "tl" }
                    } else {
                        use std::fmt::Write;
                        indexed.clear();
                        write!(indexed, "_{i}").expect("write to String");
                        &indexed
                    };
                    properties.push(self.block_property(name, self.expr(value)?));
                }
                if self.debug && c.name != "::" {
                    let key = Expression::new_call_expression(
                        SPAN,
                        self.member(self.id("Symbol"), "for"),
                        None,
                        self.b.vec1(Argument::from(self.string_expr("name"))),
                        false,
                        &self.b,
                    );
                    properties.push(ObjectPropertyKind::ObjectProperty(self.b.alloc(
                        ObjectProperty::new(
                            SPAN,
                            PropertyKind::Init,
                            PropertyKey::from(key),
                            self.string_expr(&c.name),
                            false,
                            false,
                            true,
                            &self.b,
                        ),
                    )));
                }
            }
            TagInfo::PolyVar(_) => {
                for (i, value) in children() {
                    field(if i == 0 { "NAME" } else { "VAL" }, value)?;
                }
            }
            TagInfo::Extension | TagInfo::RecordExt { .. } => {
                for (i, value) in children() {
                    let name = if i == 0 {
                        "RE_EXN_ID"
                    } else if let TagInfo::RecordExt { fields, .. } = tag
                        && let Some(name) = fields.get(i - 1)
                    {
                        name
                    } else {
                        use std::fmt::Write;
                        indexed.clear();
                        write!(indexed, "_{i}").expect("write to String");
                        &indexed
                    };
                    field(name, value)?;
                }
            }
            TagInfo::Record(_)
            | TagInfo::RecordInlined(_)
            | TagInfo::Module(_)
            | TagInfo::Tuple
            | TagInfo::Some
            | TagInfo::SomeNotNested
            | TagInfo::ModuleExport(_) => {
                let mut values = self.b.vec();
                for (_, value) in children() {
                    values.push(if let ExprKind::Spread(inner) = self.arena.ek(value) {
                        ArrayExpressionElement::SpreadElement(self.b.alloc(SpreadElement::new(
                            SPAN,
                            self.expr(inner)?,
                            &self.b,
                        )))
                    } else {
                        ArrayExpressionElement::from(self.expr(value)?)
                    });
                }
                return Ok(Expression::new_array_expression(SPAN, values, &self.b));
            }
        }
        Ok(Expression::new_object_expression(SPAN, properties, &self.b))
    }

    fn block_property(&self, name: &str, value: Expression<'a>) -> ObjectPropertyKind<'a> {
        let computed = name == "__proto__";
        let (name, bare) = walk::member_form(name);
        let key = if bare && !computed {
            PropertyKey::StaticIdentifier(self.b.alloc(IdentifierName::new(
                SPAN,
                self.text(name),
                &self.b,
            )))
        } else {
            PropertyKey::from(self.string_expr(name))
        };
        ObjectPropertyKind::ObjectProperty(self.b.alloc(ObjectProperty::new(
            SPAN,
            PropertyKind::Init,
            key,
            value,
            false,
            false,
            computed,
            &self.b,
        )))
    }

    fn block_tag(
        &self,
        tag: &crate::types::VariantLiteralTag,
    ) -> Result<Expression<'a>, Unsupported> {
        use crate::types::VariantLiteralTag as T;
        Ok(match tag {
            T::String(s) => self.string_expr(s),
            T::Int(i) => self.number(&Number::int(*i as i32))?,
            T::Float(s) => {
                let value = walk::block_float_tag(s)?;
                let literal = Expression::new_numeric_literal(
                    SPAN,
                    value.abs(),
                    None,
                    NumberBase::Decimal,
                    &self.b,
                );
                if value.is_sign_negative() {
                    self.unary(U::UnaryNegation, literal)
                } else {
                    literal
                }
            }
            T::BigInt(s) => {
                let (positive, digits) = crate::types::typecore::parse_bigint_literal(s);
                let literal = Expression::new_big_int_literal(
                    SPAN,
                    self.text(&digits),
                    None,
                    BigintBase::Decimal,
                    &self.b,
                );
                if positive {
                    literal
                } else {
                    self.unary(U::UnaryNegation, literal)
                }
            }
            T::Bool(b) => Expression::new_boolean_literal(SPAN, *b, &self.b),
            T::Null => Expression::new_null_literal(SPAN, &self.b),
            T::Undefined => self.id("undefined"),
        })
    }
    /// Layout matters only to preserved JSXText. Mirror legacy grouping at
    /// construction edges, not codegen formatting (which has different layout).
    fn with_indent<T>(&self, extra: usize, f: impl FnOnce() -> T) -> T {
        let previous = self.jsx_indent.get();
        self.jsx_indent.set(previous + extra);
        let result = f();
        self.jsx_indent.set(previous);
        result
    }
    fn high_expr(&self, e: Expr) -> Result<Expression<'a>, Unsupported> {
        self.expr_at(e, 3)
    }
    fn dot_target(&self, e: Expr) -> Result<Expression<'a>, Unsupported> {
        let previous = self.suppress_call_indent.replace(true);
        let result = self.expr_at(e, 15);
        self.suppress_call_indent.set(previous);
        result
    }
    fn indented_expr(&self, e: Expr, extra: usize) -> Result<Expression<'a>, Unsupported> {
        self.with_indent(extra, || self.expr(e))
    }
    pub fn expr(&self, e: Expr) -> Result<Expression<'a>, Unsupported> {
        self.expr_at(e, 0)
    }
    fn expr_at(&self, e: Expr, level: u8) -> Result<Expression<'a>, Unsupported> {
        let extra = match self.arena.ek(e) {
            ExprKind::Cond(..) => usize::from(level > 2),
            ExprKind::CamlBlock(items, _, tag)
                if self.arena.exprs(items).len() == 2
                    && matches!(self.arena.tag(tag), crate::lambda::TagInfo::Constructor(c) if c.name == "::") =>
            {
                0
            }
            ExprKind::Array(..) | ExprKind::CamlBlock(..) => 1,
            ExprKind::Object(props) => usize::from(
                !self
                    .arena
                    .props(props)
                    .iter()
                    .all(|(key, _)| matches!(key, PropName::Spread | PropName::RecordSpread)),
            ),
            _ => 0,
        };
        let mut expression = self.with_indent(extra, || self.expr_unmapped(e, level))?;
        // S1.2: only kinds with a codegen start-token mapping are supported.
        if let Some(maps) = self.source_map {
            if maps.is_located(self.arena.expr_loc(e)) {
                match &expression {
                    Expression::Identifier(_) | Expression::NumericLiteral(_)
                    | Expression::StringLiteral(_) | Expression::BooleanLiteral(_)
                    | Expression::NullLiteral(_) | Expression::BigIntLiteral(_) => {}
                    _ => return Err(Unsupported("source map: located compound expression")),
                }
                *expression.span_mut() = maps.span(self.arena.expr_loc(e))?;
            }
        }
        Ok(expression)
    }
    fn expr_unmapped(&self, e: Expr, level: u8) -> Result<Expression<'a>, Unsupported> {
        let a = self.arena;
        walk::expression_comment(a, e)?;
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
            ExprKind::StringAppend(_, _) => self.string_append(e)?,
            ExprKind::In(l, r) => self.binary(B::In, self.expr(l)?, self.expr(r)?),
            ExprKind::IsNullOrUndefined(e) => self.binary(
                B::Equality,
                self.expr(e)?,
                Expression::new_null_literal(SPAN, &self.b),
            ),
            ExprKind::JsNot(e) => self.unary(U::LogicalNot, self.high_expr(e)?),
            ExprKind::JsBnot(e) => self.unary(U::BitwiseNot, self.high_expr(e)?),
            ExprKind::Typeof(e) => self.unary(U::Typeof, self.high_expr(e)?),
            ExprKind::Cond(c, t, f) => Expression::new_conditional_expression(
                SPAN,
                self.high_expr(c)?,
                self.with_indent(1, || self.high_expr(t))?,
                self.with_indent(1, || self.high_expr(f))?,
                &self.b,
            ),
            ExprKind::Seq(..) => {
                let mut expressions = self.b.vec();
                self.sequence(e, &mut expressions)?;
                Expression::new_sequence_expression(SPAN, expressions, &self.b)
            }
            ExprKind::Call(f, args, _) => {
                walk::call_supported(a, f)?;
                let mut call = CallExpression::new(
                    SPAN,
                    self.expr(f)?,
                    None,
                    self.args(walk::arguments(a, a.exprs(args)), level)?,
                    false,
                    &self.b,
                );
                call.pure = walk::pure_call(a, e);
                Expression::CallExpression(self.b.alloc(call))
            }
            ExprKind::New(f, args) => Expression::new_new_expression(
                SPAN,
                self.expr_at(f, 16)?,
                None,
                self.args(args.map_or(&[], |args| a.exprs(args)), level)?,
                &self.b,
            ),
            ExprKind::StaticIndex(e, s, _) => {
                self.member(self.dot_target(e)?, a.text(s))
            }
            ExprKind::CamlBlockTag(e, s) => {
                self.member(self.with_indent(1, || self.expr_at(e, 15))?, a.text(s))
            }
            ExprKind::Length(e, _) => self.member(self.dot_target(e)?, "length"),
            ExprKind::ArrayIndex(e, i) => Expression::new_computed_member_expression(
                SPAN,
                self.with_indent(1, || self.expr_at(e, 15))?,
                self.indented_expr(i, 2)?,
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
            ExprKind::Await(e) => {
                Expression::new_await_expression(SPAN, self.high_expr(e)?, &self.b)
            }
            ExprKind::OptionalBlock(e, true) => self.expr_at(e, level)?,
            ExprKind::OptionalBlock(inner, false) => {
                let mut args = self.b.vec();
                if let Some(inner) = walk::optional_argument(a, inner) {
                    args.push(Argument::from(self.expr(inner)?));
                }
                self.call(self.member(self.id("Primitive_option"), "some"), args)
            }
            ExprKind::CamlBlock(items, _, tag) => self.caml_block(a.exprs(items), a.tag(tag))?,
            ExprKind::RawJsCode(id) => self.raw(id, walk::RawContext::Expression)?,
            ExprKind::Jsx(id) => self.jsx_call(id, level)?,
            ExprKind::TemplateLiteral(segment) => Expression::TemplateLiteral(
                self.b
                    .alloc(self.template(std::iter::once(a.template(segment).source()), &[])?),
            ),
            ExprKind::InterpolatedTemplate(segments, values) => {
                Expression::TemplateLiteral(self.b.alloc(self.template(
                    a.segments(segments).iter().map(|s| s.source()),
                    a.exprs(values),
                )?))
            }
            ExprKind::TaggedTemplate(tag, strings, values) => {
                let tag = self.expr(tag)?;
                let quasi = self.template(
                    a.tagged(strings).iter().map(|s| s.as_str()),
                    a.exprs(values),
                )?;
                Expression::new_tagged_template_expression(SPAN, tag, None, quasi, &self.b)
            }
            ExprKind::JsonLiteral(source) => self.json(a.text(source))?,
            ExprKind::FlatCall(func, args) => self.call(self.member(self.expr(func)?, "apply"), {
                let mut values = self.b.vec();
                values.push(Argument::from(Expression::new_null_literal(SPAN, &self.b)));
                values.push(Argument::from(self.expr(args)?));
                values
            }),
            ExprKind::Spread(_) => return Err(Unsupported("standalone spread")),
            ExprKind::RecordRest(fields, source) => self.record_rest(fields, source)?,
        })
    }
    /// The first line receives oxc's surrounding indentation; continuation
    /// lines are copied byte-for-byte, including their original indentation.
    /// Adding indentation to them would mutate the programmer's raw payload.
    fn raw(
        &self,
        id: crate::js_ir::arena::RawId,
        context: walk::RawContext,
    ) -> Result<Expression<'a>, Unsupported> {
        use std::fmt::Write;
        if self.source_map.is_some() {
            return Err(Unsupported("source map: verbatim raw JavaScript"));
        }
        let info = self.arena.raw(id);
        let (before, after, remove_semicolon) = walk::raw_wrapping(info, context)?;
        let mut pieces = self.raw_pieces.borrow_mut();
        let mut token =
            oxc_allocator::StringBuilder::from_str_in(self.raw_prefix, self.b.allocator());
        write!(&mut token, "{}$", pieces.len()).expect("arena string write");
        let token = token.into_str();
        pieces.push(super::raw::Piece {
            token,
            text: literal::arena_raw(&info.code, self.b.allocator()),
            before,
            after,
            remove_semicolon,
        });
        Ok(Expression::new_identifier(SPAN, token, &self.b))
    }

    /// JSON is already validated source, not a string value. It meets no
    /// identifiers; parsing reproduces property-key forms and precedence, while
    /// the surrounding oxc node supplies parentheses and statement semicolons.
    fn json(&self, source: &str) -> Result<Expression<'a>, Unsupported> {
        let source = literal::arena_string(source, self.b.allocator());
        oxc_parser::Parser::new(self.b.allocator(), source, oxc_span::SourceType::mjs())
            .parse_expression()
            .map_err(|_| Unsupported("invalid JSON or directive"))
    }

    /// See `walk::template_supported`: source spelling, not the cooked value,
    /// determines printed quasis. Codegen never reads cooked values here; tagged
    /// templates may have invalid escapes and therefore no cooked value at all.
    fn template(
        &self,
        segments: impl ExactSizeIterator<Item = &'r str>,
        values: &[Expr],
    ) -> Result<TemplateLiteral<'a>, Unsupported> {
        walk::template_supported(segments.len(), values.len())?;
        let mut quasis = self.b.vec();
        for (i, source) in segments.enumerate() {
            quasis.push(TemplateElement::new(
                SPAN,
                TemplateElementValue {
                    raw: literal::arena_string(source, self.b.allocator()).into(),
                    cooked: None,
                },
                i == values.len(),
                &self.b,
            ));
        }
        let mut expressions = self.b.vec();
        for e in values {
            expressions.push(self.expr(*e)?);
        }
        Ok(TemplateLiteral::new(SPAN, quasis, expressions, &self.b))
    }

    fn params(&self, f: FunId) -> oxc_allocator::Box<'a, FormalParameters<'a>> {
        let mut items = self.b.vec();
        let info = self.arena.fun(f);
        for id in self
            .arena
            .ident_slice(info.params)
            .iter()
            .skip(usize::from(info.is_method))
        {
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
        self.with_indent(1, || self.function_body_inner(f))
    }
    fn function_body_inner(
        &self,
        f: FunId,
    ) -> Result<oxc_allocator::Box<'a, FunctionBody<'a>>, Unsupported> {
        let info = self.arena.fun(f);
        let body = walk::function_body(self.arena, self.arena.stmts(info.body));
        let mut statements = self.b.vec();
        // Methods omit their first IR parameter and materialize it as `this`
        // only when used. Naming meets that binding before the real parameters.
        if info.is_method && self.names.method_this_used(f) {
            let this = &self.arena.ident_slice(info.params)[0];
            statements.push(self.variable(
                self.names.get(this),
                Some(Expression::new_this_expression(SPAN, &self.b)),
            ));
        }
        for (index, s) in body.iter().enumerate() {
            self.stmt(
                *s,
                false,
                (index + 1 == body.len()).then_some(info.return_unit),
                &mut statements,
            )?;
        }
        let mut directives = self.b.vec();
        if let Some(directive) = info.directive {
            // The legacy directive includes its quotes. It precedes every body
            // statement and meets no identifiers; codegen supplies the semicolon.
            let Expression::StringLiteral(value) = self.json(self.arena.text(directive))? else {
                return Err(Unsupported("non-string function directive"));
            };
            directives.push(Directive::new(
                SPAN,
                value.unbox(),
                self.text(self.arena.text(directive).trim_matches(['\'', '"'])),
                &self.b,
            ));
        }
        Ok(self
            .b
            .alloc(FunctionBody::new(SPAN, directives, statements, &self.b)))
    }
    fn function_expr(&self, f: FunId) -> Result<Expression<'a>, Unsupported> {
        if self.source_map.is_some() {
            return Err(Unsupported("source map: transformed function body"));
        }
        let body = match walk::function_form(self.arena, f, false)? {
            walk::FunctionForm::Eta(e) => return self.expr(e),
            walk::FunctionForm::ArrowExpression(e) => {
                let mut value = if let ExprKind::RawJsCode(id) = self.arena.ek(e) {
                    walk::expression_comment(self.arena, e)?;
                    self.raw(id, walk::RawContext::Arrow)?
                } else {
                    self.expr(e)?
                };
                // Legacy groups Fun bodies. oxc records parenthesized functions
                // as PIFEs even with preserve_parens=false; a ParenthesizedExpression
                // alone is ignored by codegen and does not reproduce these tokens.
                if walk::arrow_function_body(self.arena, e) {
                    match &mut value {
                        Expression::ArrowFunctionExpression(f) => f.pife = true,
                        Expression::FunctionExpression(f) => f.pife = true,
                        _ => {} // Eta reduction prints an identifier, not a function.
                    }
                }
                ArrowFunctionBody::from(value)
            }
            walk::FunctionForm::ArrowEmpty => ArrowFunctionBody::FunctionBody(
                self.b
                    .alloc(FunctionBody::new(SPAN, self.b.vec(), self.b.vec(), &self.b)),
            ),
            walk::FunctionForm::ArrowBlock => {
                ArrowFunctionBody::FunctionBody(self.function_body(f)?)
            }
            walk::FunctionForm::Method => {
                return Ok(Expression::new_function_expression(
                    SPAN,
                    FunctionType::FunctionExpression,
                    None,
                    false,
                    self.arena.fun(f).async_,
                    false,
                    None,
                    None,
                    self.params(f),
                    None,
                    Some(self.function_body(f)?),
                    &self.b,
                ));
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
            let expression = if let ExprKind::RawJsCode(id) = self.arena.ek(e) {
                walk::expression_comment(self.arena, e)?;
                self.raw(id, walk::RawContext::Statement)?
            } else {
                self.expr(e)?
            };
            out.push(self.expression_statement(expression));
        }
        Ok(())
    }
    fn brace(
        &self,
        b: crate::js_ir::arena::StmtList,
    ) -> Result<oxc_allocator::Box<'a, BlockStatement<'a>>, Unsupported> {
        Ok(self.b.alloc(BlockStatement::new(
            SPAN,
            self.with_indent(1, || self.block(self.arena.stmts(b), false))?,
            &self.b,
        )))
    }
    fn label(
        &self,
        label: Option<crate::js_ir::arena::StrId>,
        body: Statement<'a>,
    ) -> Statement<'a> {
        match label {
            Some(l) => Statement::new_labeled_statement(
                SPAN,
                LabelIdentifier::new(SPAN, self.text(self.arena.text(l)), &self.b),
                body,
                &self.b,
            ),
            None => body,
        }
    }
    fn declarator(&self, name: &str, init: Option<Expression<'a>>) -> VariableDeclarator<'a> {
        VariableDeclarator::new(
            SPAN,
            BindingPattern::BindingIdentifier(self.b.alloc(self.binding(name))),
            None,
            init,
            false,
            &self.b,
        )
    }
    /// Legacy range header: cache a non-simple end once, before the test; use
    /// prefix ++/-- and <=/>=/ < according to direction. See walk::finish_binding.
    fn range(
        &self,
        s: Stmt,
        id: crate::js_ir::arena::ForRangeId,
    ) -> Result<Statement<'a>, Unsupported> {
        use crate::js_ir::ForDirection;
        let a = self.arena;
        let f = a.for_range(id);
        walk::range_supported(a, f)?;
        let name = self.names.get(&a.ident(f.ident));
        let finish = walk::finish_binding(a, f.end).then(|| self.names.finish(s));
        let mut declarations = self.b.vec();
        if let Some(e) = f.init {
            declarations.push(self.declarator(name, Some(self.expr(e)?)));
        }
        if let Some(name) = finish {
            declarations.push(self.declarator(name, Some(self.expr(f.end)?)));
        }
        let init = if declarations.is_empty() {
            None
        } else {
            Some(ForStatementInit::VariableDeclaration(self.b.alloc(
                VariableDeclaration::new(
                    SPAN,
                    VariableDeclarationKind::Let,
                    declarations,
                    false,
                    &self.b,
                ),
            )))
        };
        let test = self.binary(
            match f.direction {
                ForDirection::Upto => B::LessEqualThan,
                ForDirection::Downto => B::GreaterEqualThan,
                ForDirection::Up => B::LessThan,
            },
            self.id(name),
            match finish {
                Some(n) => self.id(n),
                None => self.expr(f.end)?,
            },
        );
        let update = Expression::new_update_expression(
            SPAN,
            if f.direction == ForDirection::Downto {
                oxc_syntax::operator::UpdateOperator::Decrement
            } else {
                oxc_syntax::operator::UpdateOperator::Increment
            },
            true,
            SimpleAssignmentTarget::AssignmentTargetIdentifier(
                self.b
                    .alloc(IdentifierReference::new(SPAN, self.text(name), &self.b)),
            ),
            &self.b,
        );
        Ok(self.label(
            f.label,
            Statement::new_for_statement(
                SPAN,
                init,
                Some(test),
                Some(update),
                Statement::BlockStatement(self.brace(f.body)?),
                &self.b,
            ),
        ))
    }
    /// `print_case_body` appends break exactly when should_break is set, even
    /// after an abrupt body; empty fallthrough cases remain empty, default last.
    fn case(
        &self,
        test: Expression<'a>,
        c: &crate::js_ir::arena::Clause,
    ) -> Result<SwitchCase<'a>, Unsupported> {
        let mut body = self.with_indent(2, || self.block(self.arena.stmts(c.body), false))?;
        if c.should_break {
            body.push(Statement::new_break_statement(SPAN, None, &self.b));
        }
        Ok(SwitchCase::new(SPAN, Some(test), body, &self.b))
    }
    fn switch_tag(
        &self,
        tag: &crate::lambda::SwitchCaseTag,
    ) -> Result<Expression<'a>, Unsupported> {
        use crate::lambda::SwitchCaseTag as T;
        Ok(match tag {
            T::String(s) => self.string_expr(s),
            T::Int(i) => {
                let e = Expression::new_numeric_literal(
                    SPAN,
                    (*i as f64).abs(),
                    None,
                    NumberBase::Decimal,
                    &self.b,
                );
                if *i < 0 {
                    self.unary(U::UnaryNegation, e)
                } else {
                    e
                }
            }
            T::Bool(b) => Expression::new_boolean_literal(SPAN, *b, &self.b),
            T::Null => Expression::new_null_literal(SPAN, &self.b),
            T::Undefined => self.id("undefined"),
            T::Float(s) => {
                let value = walk::block_float_tag(s)?;
                let e = Expression::new_numeric_literal(
                    SPAN,
                    value.abs(),
                    None,
                    NumberBase::Decimal,
                    &self.b,
                );
                if value.is_sign_negative() {
                    self.unary(U::UnaryNegation, e)
                } else {
                    e
                }
            }
            T::BigInt(s) => {
                walk::switch_tag_supported(tag)?;
                let digits = s.trim_start_matches(['-', '+']).trim_start_matches('0');
                let digits = if digits.is_empty() { "0" } else { digits };
                let e = Expression::new_big_int_literal(
                    SPAN,
                    self.text(digits),
                    None,
                    BigintBase::Decimal,
                    &self.b,
                );
                if s.starts_with('-') {
                    self.unary(U::UnaryNegation, e)
                } else {
                    e
                }
            }
        })
    }
    /// Throwing a literal Extension/RecordExt appends an Error field, not an
    /// Error wrapper call. Ordinary throws retain their expression unchanged.
    fn throw_value(&self, e: Expr) -> Result<Expression<'a>, Unsupported> {
        let mut value = self.expr(e)?;
        if let ExprKind::CamlBlock(_, _, tag) = self.arena.ek(e)
            && matches!(
                self.arena.tag(tag),
                crate::lambda::TagInfo::Extension | crate::lambda::TagInfo::RecordExt { .. }
            )
        {
            let Expression::ObjectExpression(ref mut object) = value else {
                unreachable!()
            };
            let error = Expression::new_new_expression(
                SPAN,
                self.id("Error"),
                None,
                self.b.vec::<Argument<'a>>(),
                &self.b,
            );
            object.properties.push(self.block_property("Error", error));
        }
        Ok(value)
    }
    fn stmt(
        &self,
        s: Stmt,
        top: bool,
        tail: Option<bool>,
        out: &mut ArenaVec<'a, Statement<'a>>,
    ) -> Result<(), Unsupported> {
        // S1.2: switch clauses have independent mapping points, not just the
        // statement/expression locations covered by the hooks below.
        if self.source_map.is_some()
            && matches!(self.arena.sk(s), StmtKind::IntSwitch(..) | StmtKind::StringSwitch(..))
        {
            return Err(Unsupported("source map: switch clause markers"));
        }
        let start = out.len();
        self.stmt_unmapped(s, top, tail, out)?;
        // S1.2: block/expression wrappers do not reliably emit a start token.
        if let Some(maps) = self.source_map {
            let loc = self.arena.stmt_loc(s);
            if maps.is_located(loc) {
                if out.len() != start + 1 {
                    return Err(Unsupported("source map: expanded or omitted statement"));
                }
                match &mut out[start] {
                    Statement::VariableDeclaration(_) | Statement::ReturnStatement(_)
                    | Statement::IfStatement(_) | Statement::DebuggerStatement(_) => {
                        *out[start].span_mut() = maps.span(loc)?;
                    }
                    Statement::FunctionDeclaration(f) => {
                        // The statement's mark precedes the function expression's
                        // mark at the same token; the legacy builder keeps the first.
                        f.span = maps.span(loc)?;
                    }
                    _ => return Err(Unsupported("source map: statement without start token")),
                }
            }
        }
        Ok(())
    }
    fn stmt_unmapped(
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
                if let Some((fields, source)) = walk::rest_declaration(a, decl) {
                    let item = VariableDeclarator::new(
                        SPAN,
                        self.rest_pattern(fields, name, true),
                        None,
                        Some(self.expr(source)?),
                        false,
                        &self.b,
                    );
                    out.push(Statement::new_variable_declaration(
                        SPAN,
                        VariableDeclarationKind::Let,
                        self.b.vec1(item),
                        false,
                        &self.b,
                    ));
                    return Ok(());
                }

                if let Some(e) = decl.value
                    && let ExprKind::Fun(f) = a.ek(e)
                {
                    match walk::function_form(a, f, top)? {
                        walk::FunctionForm::Declaration => {
                            out.push(Statement::new_function_declaration(
                                // S1.2: initializer maps to the `function` token.
                                self.source_map.map_or(Ok(SPAN), |m| m.span(a.expr_loc(e)))?,
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
                            if self.source_map.is_some() {
                                return Err(Unsupported("source map: eta-reduced declaration"));
                            }
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
            StmtKind::Return(e) if tail == Some(true) => {
                if let Some(e) = walk::tail_effect(a, e) {
                    self.effect(e, out)?;
                }
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
                        self.with_indent(1, || self.block(f, false))?,
                        &self.b,
                    ))
                };
                out.push(Statement::new_if_statement(
                    SPAN,
                    self.indented_expr(c, 1)?,
                    Statement::new_block_statement(
                        SPAN,
                        self.with_indent(1, || self.block(a.stmts(t), false))?,
                        &self.b,
                    ),
                    alternate,
                    &self.b,
                ));
            }
            StmtKind::Debugger => out.push(Statement::new_debugger_statement(SPAN, &self.b)),
            StmtKind::While(label, cond, body) => {
                out.push(self.label(
                    label,
                    Statement::new_while_statement(
                        SPAN,
                        self.indented_expr(cond, 1)?,
                        Statement::BlockStatement(self.brace(body)?),
                        &self.b,
                    ),
                ));
                out.push(Statement::new_empty_statement(SPAN, &self.b));
            }
            StmtKind::ForRange(id) => out.push(self.range(s, id)?),
            StmtKind::ForOf(id) | StmtKind::ForAwaitOf(id) => {
                let f = a.for_of(id);
                let decl = VariableDeclaration::new(
                    SPAN,
                    VariableDeclarationKind::Let,
                    self.b
                        .vec1(self.declarator(self.names.get(&a.ident(f.ident)), None)),
                    false,
                    &self.b,
                );
                out.push(self.label(
                    f.label,
                    Statement::new_for_of_statement(
                        SPAN,
                        matches!(a.sk(s), StmtKind::ForAwaitOf(_)),
                        ForStatementLeft::VariableDeclaration(self.b.alloc(decl)),
                        self.indented_expr(f.iterable, 1)?,
                        Statement::BlockStatement(self.brace(f.body)?),
                        &self.b,
                    ),
                ));
            }
            StmtKind::IntSwitch(e, id) => {
                let info = a.int_switch(id);
                let mut cases = self.b.vec();
                for (value, c) in &info.clauses {
                    cases.push(self.case(self.number(&Number::int(*value))?, c)?);
                }
                if let Some(b) = info.default {
                    cases.push(SwitchCase::new(
                        SPAN,
                        None,
                        self.with_indent(2, || self.block(a.stmts(b), false))?,
                        &self.b,
                    ));
                }
                out.push(Statement::new_switch_statement(
                    SPAN,
                    self.expr(e)?,
                    cases,
                    &self.b,
                ));
            }
            StmtKind::StringSwitch(e, id) => {
                let info = a.string_switch(id);
                let mut cases = self.b.vec();
                for c in &info.clauses {
                    cases.push(self.case(self.switch_tag(&c.tag_type)?, &c.clause)?);
                }
                if let Some(b) = info.default {
                    cases.push(SwitchCase::new(
                        SPAN,
                        None,
                        self.with_indent(2, || self.block(a.stmts(b), false))?,
                        &self.b,
                    ));
                }
                out.push(Statement::new_switch_statement(
                    SPAN,
                    self.expr(e)?,
                    cases,
                    &self.b,
                ));
            }
            StmtKind::Try(id) => {
                let t = a.try_info(id);
                let handler = if let Some((id, body)) = t.catch {
                    let pattern = BindingPattern::BindingIdentifier(
                        self.b.alloc(self.binding(self.names.get(&a.ident(id)))),
                    );
                    Some(self.b.alloc(CatchClause::new(
                        SPAN,
                        Some(CatchParameter::new(SPAN, pattern, None, &self.b)),
                        self.brace(body)?,
                        &self.b,
                    )))
                } else {
                    None
                };
                out.push(Statement::new_try_statement(
                    SPAN,
                    self.brace(t.body)?,
                    handler,
                    t.finally.map(|b| self.brace(b)).transpose()?,
                    &self.b,
                ));
            }
            StmtKind::Throw(e) => out.push(Statement::new_throw_statement(
                SPAN,
                self.throw_value(e)?,
                &self.b,
            )),
            StmtKind::Break(l) | StmtKind::Continue(l) => {
                let label = l.map(|l| LabelIdentifier::new(SPAN, self.text(a.text(l)), &self.b));
                out.push(if matches!(a.sk(s), StmtKind::Break(_)) {
                    Statement::new_break_statement(SPAN, label, &self.b)
                } else {
                    Statement::new_continue_statement(SPAN, label, &self.b)
                });
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

#[cfg(test)]
mod block_tests {
    use super::*;
    use crate::js_ir::build::exp as E;
    use crate::js_ir::op::MutableFlag;
    use crate::lambda::{TagInfo, lam_tag_info::RecordInlinedTag};
    use crate::types::{VariantBlock, VariantLiteralTag as T};
    use js_reformat::{ReformatOptions, reformat};

    fn oracle(tag: TagInfo, undefined: &[bool]) {
        for mutable in [MutableFlag::Immutable, MutableFlag::Mutable] {
            for debug in [false, true] {
                let mut arena = JsArena::new();
                let values: Vec<_> = undefined
                    .iter()
                    .enumerate()
                    .map(|(i, &u)| {
                        if u {
                            E::new(ExprKind::Undefined { is_unit: false }, &mut arena)
                        } else {
                            E::number(Number::int(i as i32), &mut arena)
                        }
                    })
                    .collect();
                let items = E::list(&values, &mut arena);
                let info = arena.tag_id(tag.clone());
                let expr = E::new(ExprKind::CamlBlock(items, mutable, info), &mut arena);
                let legacy =
                    crate::js_ir::printer::print_expr_with_options(&arena, expr, 1, debug, false);
                let alloc = Allocator::default();
                let names = Names::default();
                let mut build = Build::new(&alloc, &arena, &names);
                build.debug = debug;
                let stmt = build.variable("value", Some(build.expr(expr).unwrap()));
                let program = Program::new(
                    SPAN,
                    oxc_span::SourceType::mjs(),
                    "",
                    build.b.vec(),
                    None,
                    build.b.vec(),
                    build.b.vec1(stmt),
                    &build.b,
                );
                let actual = oxc_codegen::Codegen::new().build(&program).code;
                let mode = ReformatOptions {
                    drop_decoration_comments: true,
                    ..Default::default()
                };
                assert_eq!(
                    reformat(&format!("let value = {legacy};"), mode).unwrap(),
                    actual,
                    "{tag:?}"
                );
                assert_eq!(reformat(&actual, mode).unwrap(), actual);
            }
        }
    }

    #[test]
    fn tuple_and_lowered_option_arrays() {
        for tag in [
            TagInfo::Tuple,
            TagInfo::Some,
            TagInfo::SomeNotNested,
            TagInfo::ModuleExport(vec![]),
        ] {
            oracle(tag, &[false, true]);
        }
    }
    #[test]
    fn record_array() {
        let TagInfo::Record(mut r) = TagInfo::ref_tag() else {
            unreachable!()
        };
        r.array = true;
        oracle(TagInfo::Record(r), &[false, true]);
    }
    #[test]
    fn record_keys_and_optional_fields() {
        oracle(
            TagInfo::record(
                vec![
                    ("optional".into(), true),
                    ("required".into(), false),
                    ("__proto__".into(), false),
                    ("123".into(), false),
                    ("a-b".into(), false),
                    ("default".into(), false),
                    ("present".into(), true),
                ],
                crate::parser::ast::MutableFlag::Immutable,
            ),
            &[true, true, false, false, false, false, false],
        );
        oracle(
            TagInfo::record(vec![], crate::parser::ast::MutableFlag::Immutable),
            &[],
        );
    }
    fn inline(tagged: bool) -> TagInfo {
        let TagInfo::Constructor(c) = TagInfo::constructor("Inline", 1) else {
            unreachable!()
        };
        let runtime = if tagged {
            VariantBlock::Tagged(*c.runtime)
        } else {
            VariantBlock::Untagged {
                tag: c.runtime.tag,
                block_type: crate::types::VariantBlockType::Object,
            }
        };
        TagInfo::RecordInlined(Box::new(RecordInlinedTag {
            name: "Inline".into(),
            num_nonconst: 1,
            fields: vec![("gone".into(), true), ("kept".into(), false)],
            logical_field_count: None,
            mutable_flag: crate::parser::ast::MutableFlag::Immutable,
            runtime: Box::new(runtime),
        }))
    }
    #[test]
    fn tagged_inline_record() {
        oracle(inline(true), &[true, true]);
    }
    #[test]
    fn untagged_inline_record() {
        oracle(inline(false), &[true, true]);
    }
    #[test]
    fn module_fields() {
        oracle(
            TagInfo::Module(vec!["default".into(), "a-b".into(), "value".into()]),
            &[false, false, true],
        );
    }
    #[test]
    fn constructor_and_tag_literals() {
        for literal in [
            T::String("A".into()),
            T::Int(-42),
            T::Float("-1.5".into()),
            T::BigInt("-12345678901234567890".into()),
            T::Bool(true),
            T::Null,
            T::Undefined,
        ] {
            let TagInfo::Constructor(mut c) = TagInfo::constructor("A", 1) else {
                unreachable!()
            };
            c.runtime.tag.literal = literal;
            c.runtime.tag_name = Some("custom-tag".into());
            oracle(TagInfo::Constructor(c), &[false, true]);
        }
    }
    #[test]
    fn list_cells() {
        for values in [&[][..], &[false, false][..], &[false, true, false][..]] {
            oracle(TagInfo::constructor("::", 1), values);
        }
    }
    #[test]
    fn polymorphic_variant() {
        oracle(TagInfo::poly_var("ignored"), &[false, true]);
        oracle(TagInfo::poly_var("ignored"), &[false]);
    }
    #[test]
    fn extension() {
        oracle(TagInfo::Extension, &[false, true, false]);
    }
    #[test]
    fn record_extension() {
        oracle(
            TagInfo::RecordExt {
                fields: vec!["__proto__".into(), "123".into()],
                mutable_flag: crate::parser::ast::MutableFlag::Mutable,
            },
            &[false, true, false, true],
        );
    }
    #[test]
    fn mismatched_metadata_uses_array() {
        for tag in [TagInfo::ref_tag(), inline(true), TagInfo::Module(vec![])] {
            oracle(tag, &[false, true, false]);
        }
    }
}

#[cfg(test)]
mod statement_tests {
    use super::*;
    use crate::ident::{Ident, IdentFlags};
    use crate::js_ir::arena::*;
    use crate::js_ir::op::MutableFlag;
    use crate::js_ir::{ForDirection, ModulePathResolver};
    use crate::lambda::{SwitchCaseTag, TagInfo};
    use js_reformat::{ReformatOptions, reformat};

    fn id(a: &mut JsArena, name: &str, stamp: i32) -> IdentId {
        a.ident_id(Ident::new(name, stamp, IdentFlags::NONE))
    }
    fn number(a: &mut JsArena, n: i32) -> Expr {
        let n = a.number_id(Number::int(n));
        a.expr(ExprKind::Number(n))
    }
    fn oracle(a: JsArena, block: Vec<Stmt>) {
        let p = JsDepsProgram {
            program: JsProgram::new_in(block, vec![], a),
            modules: vec![],
            side_effect: None,
        };
        let resolver =
            ModulePathResolver::from_compile_options(None, None, None, None, None, None, false);
        let legacy = crate::js_ir::program_printer::print_deps_program_with_directives_and_options(
            &p,
            Some(&resolver),
            &[],
            false,
            false,
            true,
        );
        let actual = crate::emit::emit(&p, &resolver, &[], false, false, true)
            .unwrap()
            .0;
        let mode = ReformatOptions {
            split_file: true,
            drop_decoration_comments: true,
            ..Default::default()
        };
        assert_eq!(reformat(&legacy, mode).unwrap(), actual, "{legacy}");
        assert_eq!(reformat(&actual, mode).unwrap(), actual);
    }

    #[test]
    fn ranges_labels_and_finish_collisions() {
        for direction in [ForDirection::Upto, ForDirection::Downto, ForDirection::Up] {
            for cached in [false, true] {
                for initialized in [false, true] {
                    let mut a = JsArena::new();
                    let i = id(&mut a, "i", 1);
                    let reserved = id(&mut a, "i_finish", 2);
                    let reserved = a.expr(ExprKind::Var(reserved));
                    let start = number(&mut a, 0);
                    let one = number(&mut a, 1);
                    let end = if cached {
                        a.expr(ExprKind::Bin(BinOp::Plus, reserved, one))
                    } else {
                        one
                    };
                    let label = a.str("outer");
                    let cont = a.stmt(StmtKind::Continue(Some(label)));
                    let body = a.stmt_list(&[cont]);
                    let f = a.for_range_id(ForRangeInfo {
                        label: Some(label),
                        init: initialized.then_some(start),
                        end,
                        ident: i,
                        direction,
                        body,
                    });
                    let first = a.stmt(StmtKind::ForRange(f));
                    let second = a.stmt(StmtKind::ForRange(f));
                    oracle(a, vec![first, second]);
                }
            }
        }
    }
    #[test]
    fn while_and_iteration() {
        for await_ in [false, true] {
            let mut a = JsArena::new();
            let i = id(&mut a, "item", 1);
            let iterable = a.expr(ExprKind::Array(ExprList::EMPTY, MutableFlag::Immutable));
            let label = a.str("outer");
            let br = a.stmt(StmtKind::Break(Some(label)));
            let body = a.stmt_list(&[br]);
            let yes = a.expr(ExprKind::Bool(true));
            let w = a.stmt(StmtKind::While(None, yes, body));
            let body = a.stmt_list(&[w]);
            let f = a.for_of_id(ForOfInfo {
                label: Some(label),
                ident: i,
                iterable,
                body,
            });
            let s = a.stmt(if await_ {
                StmtKind::ForAwaitOf(f)
            } else {
                StmtKind::ForOf(f)
            });
            oracle(a, vec![s]);
        }
    }
    #[test]
    fn switch_fallthrough_and_breaks() {
        let mut a = JsArena::new();
        let value = number(&mut a, 3);
        let throw = a.stmt(StmtKind::Throw(value));
        let body = a.stmt_list(&[throw]);
        let empty = Clause {
            body: StmtList::EMPTY,
            should_break: false,
            comment: None,
            source_loc: None,
        };
        let break_ = Clause {
            should_break: true,
            ..empty
        };
        let full = Clause { body, ..break_ };
        let info = a.int_switch_id(IntSwitchInfo {
            clauses: vec![(-1, empty), (0, break_), (1, full)],
            default: Some(body),
        });
        let ints = a.stmt(StmtKind::IntSwitch(value, info));
        let clauses = [
            SwitchCaseTag::String("key".into()),
            SwitchCaseTag::Int(4_294_967_296),
            SwitchCaseTag::Float("-2.5".into()),
            SwitchCaseTag::BigInt("123".into()),
            SwitchCaseTag::BigInt("-000123".into()),
            SwitchCaseTag::BigInt("+000".into()),
            SwitchCaseTag::Bool(false),
            SwitchCaseTag::Null,
            SwitchCaseTag::Undefined,
        ]
        .into_iter()
        .map(|tag_type| StringClauseInfo {
            tag_type,
            clause: full,
        })
        .collect();
        let info = a.string_switch_id(StringSwitchInfo {
            clauses,
            default: Some(StmtList::EMPTY),
        });
        let strings = a.stmt(StmtKind::StringSwitch(value, info));
        oracle(a, vec![ints, strings]);
    }
    #[test]
    fn throw_exception_fields_and_try() {
        for record in [false, true] {
            let mut a = JsArena::new();
            let exn = id(&mut a, "exn", 1);
            let payload = id(&mut a, "exn", 2);
            let value = a.expr(ExprKind::Var(payload));
            let items = a.expr_list(&[value, value]);
            let tag = a.tag_id(if record {
                TagInfo::RecordExt {
                    fields: vec!["message".into()],
                    mutable_flag: crate::parser::ast::MutableFlag::Immutable,
                }
            } else {
                TagInfo::Extension
            });
            let value = a.expr(ExprKind::CamlBlock(items, MutableFlag::Immutable, tag));
            let throw = a.stmt(StmtKind::Throw(value));
            let body = a.stmt_list(&[throw]);
            let value = a.expr(ExprKind::Var(exn));
            let throw = a.stmt(StmtKind::Throw(value));
            let catch = a.stmt_list(&[throw]);
            let info = a.try_id(TryInfo {
                body,
                catch: Some((exn, catch)),
                finally: Some(StmtList::EMPTY),
            });
            let s = a.stmt(StmtKind::Try(info));
            oracle(a, vec![s]);
        }
    }
    #[test]
    fn assignment_and_unit_tail() {
        for trivial in [false, true] {
            let mut a = JsArena::new();
            let x = id(&mut a, "x", 1);
            let x = a.expr(ExprKind::Var(x));
            let one = number(&mut a, 1);
            let assign = a.expr(ExprKind::Bin(BinOp::Eq, x, one));
            let seq = a.expr(ExprKind::Seq(one, assign));
            let ret = a.stmt(StmtKind::Return(if trivial { one } else { seq }));
            let debug = a.stmt(StmtKind::Debugger);
            let body = a.stmt_list(&[debug, ret]);
            let params = a.ident_list(&[]);
            let f = a.fun_id(FunInfo {
                is_method: false,
                params,
                body,
                return_unit: true,
                async_: false,
                directive: None,
            });
            let f = a.expr(ExprKind::Fun(f));
            let v = a.var_id(VarDecl {
                ident: Ident::new("effect", 3, IdentFlags::NONE),
                value: Some(f),
                property: crate::js_ir::op::Property::Strict,
                ident_info: Default::default(),
            });
            let s = a.stmt(StmtKind::Variable(v));
            oracle(a, vec![s]);
        }
    }
}

#[cfg(test)]
mod remaining_expression_tests {
    use super::*;
    use crate::js_ir::build::exp as E;
    use js_reformat::{ReformatOptions, reformat};

    fn oracle(arena: &JsArena, expr: Expr) {
        let legacy = crate::js_ir::printer::print_expr_with_options(arena, expr, 1, false, false);
        let alloc = Allocator::default();
        let names = Names::default();
        let build = Build::new(&alloc, arena, &names);
        let stmt = build.variable("value", Some(build.expr(expr).unwrap()));
        let program = Program::new(
            SPAN,
            oxc_span::SourceType::mjs(),
            "",
            build.b.vec(),
            None,
            build.b.vec(),
            build.b.vec1(stmt),
            &build.b,
        );
        let actual = oxc_codegen::Codegen::new().build(&program).code;
        let mode = ReformatOptions {
            drop_decoration_comments: true,
            ..Default::default()
        };
        assert_eq!(
            reformat(&format!("let value = {legacy};"), mode).unwrap(),
            actual
        );
        assert_eq!(reformat(&actual, mode).unwrap(), actual);
    }

    #[test]
    fn canonical_numeric_members_match_legacy() {
        use crate::js_ir::arena::FieldPos;
        for key in [
            "0",
            "1",
            "-1",
            "-0",
            "00",
            "01",
            "+1",
            "9007199254740993",
            "9223372036854775807",
            "-9223372036854775808",
            "9223372036854775808",
        ] {
            let mut a = JsArena::new();
            let value = E::new(ExprKind::Undefined { is_unit: false }, &mut a);
            let key = a.str(key);
            let expr = E::new(
                ExprKind::StaticIndex(value, key, FieldPos::new(None)),
                &mut a,
            );
            oracle(&a, expr);
        }
    }

    #[test]
    fn runtime_jsx_and_rest_expression_oracle() {
        let mut a = JsArena::new();
        let value = E::new(ExprKind::Undefined { is_unit: false }, &mut a);
        for multi in [false, true] {
            for spread in [None, Some(value)] {
                for has_children in [false, true] {
                    let props = a.prop_list(&[]);
                    let children = has_children.then(|| a.expr_list(&[value]));
                    let jsx = a.jsx_id(crate::js_ir::arena::JsxInfo {
                        callee: value,
                        tag: value,
                        spread,
                        props,
                        children,
                        key: Some(value),
                        multi,
                        fragment: false,
                    });
                    let expr = a.expr(ExprKind::Jsx(jsx));
                    oracle(&a, expr);
                }
            }
        }
        for labels in [vec![], vec!["a", "with-dash", "__proto__"]] {
            let fields = a.rest_id(
                labels
                    .into_iter()
                    .map(|label| crate::js_ir::RecordRestField {
                        label: label.into(),
                        ident: None,
                    })
                    .collect(),
            );
            let expr = a.expr(ExprKind::RecordRest(fields, value));
            oracle(&a, expr);
        }
    }

    #[test]
    fn string_spine_does_not_bypass_comment_rejection() {
        let mut a = JsArena::new();
        let value = a.expr(ExprKind::Null);
        let inner = a.expr_commented(ExprKind::StringAppend(value, value), "keep me");
        let root = a.expr(ExprKind::StringAppend(value, inner));
        let alloc = Allocator::default();
        let names = Names::default();
        let error = Build::new(&alloc, &a, &names).expr(root).unwrap_err();
        assert_eq!(error, Unsupported("non-decoration expression comment"));
        assert_eq!(walk::string_leaves(&a, root, &mut Vec::new(), |_| Ok(())), Err(error));
    }

    #[test]
    fn nullish_comparison_oracle() {
        let mut a = JsArena::new();
        let value = a.expr(ExprKind::Bool(true));
        let null = a.expr(ExprKind::Null);
        let undefined = a.expr(ExprKind::Undefined { is_unit: false });
        for (left, right) in [(null, undefined), (undefined, null), (null, null)] {
            let left = a.expr(ExprKind::Bin(BinOp::EqEqEq, value, left));
            let right = a.expr(ExprKind::Bin(BinOp::EqEqEq, value, right));
            let expr = a.expr(ExprKind::Bin(BinOp::Or, left, right));
            oracle(&a, expr);
        }
    }

    #[test]
    fn string_append_preserves_both_associations() {
        let mut a = JsArena::new();
        let one = E::number(Number::int(1), &mut a);
        let two = E::number(Number::int(2), &mut a);
        let three = E::number(Number::int(3), &mut a);
        let pair = E::new(ExprKind::StringAppend(one, two), &mut a);
        let left = E::new(ExprKind::StringAppend(pair, three), &mut a);
        let right = E::new(ExprKind::StringAppend(three, pair), &mut a);
        oracle(&a, left);
        oracle(&a, right);
    }

    #[test]
    fn optional_helper_omits_only_synthetic_unit() {
        let mut a = JsArena::new();
        for unit in [true, false] {
            let value = E::new(ExprKind::Undefined { is_unit: unit }, &mut a);
            let expr = E::new(ExprKind::OptionalBlock(value, false), &mut a);
            oracle(&a, expr);
        }
        let number = E::number(Number::int(1), &mut a);
        let expr = E::new(ExprKind::OptionalBlock(number, false), &mut a);
        oracle(&a, expr);
    }

    #[test]
    fn flat_call_uses_apply_null_array() {
        let mut a = JsArena::new();
        let value = E::new(ExprKind::Undefined { is_unit: false }, &mut a);
        let expr = E::new(ExprKind::FlatCall(value, value), &mut a);
        oracle(&a, expr);
    }

    #[test]
    fn ten_thousand_term_string_chain_builds_and_names_iteratively() {
        let mut a = JsArena::new();
        let value = E::number(Number::int(1), &mut a);
        let mut expr = value;
        for _ in 1..10_000 {
            expr = E::new(ExprKind::StringAppend(value, expr), &mut a);
        }
        let mut count = 0;
        walk::string_leaves(&a, expr, &mut Vec::new(), |_| {
            count += 1;
            Ok(())
        })
        .unwrap();
        assert_eq!(count, 10_000);
        let alloc = Allocator::default();
        let names = Names::default();
        Build::new(&alloc, &a, &names).expr(expr).unwrap();
        let stmt = a.stmt(StmtKind::Exp(expr));
        let program = crate::js_ir::arena::JsDepsProgram {
            program: crate::js_ir::arena::JsProgram::new_in(vec![stmt], vec![], a),
            modules: vec![],
            side_effect: None,
        };
        let resolver = crate::js_ir::ModulePathResolver::from_compile_options(
            None, None, None, None, None, None, false,
        );
        Names::collect(&program, &resolver, false).unwrap();
    }
}
