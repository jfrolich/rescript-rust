//! The builder over oxc nodes (THREE_TREES 11.4, "T6 design").
//!
//! A JavaScript expression in flight is a [`J`]: the oxc `Expression` by
//! value and the [`Row`] of facts the normalising rules read. The row of a
//! node that is already inside a parent is in [`Builder::rows`], dense by the
//! node's `node_id`. Nothing here walks an expression: a constructor reads
//! the rows of its operands (in the handles) and writes one node and one row.
//! A constructor builds the node it is asked for: the rules of
//! BACKEND_LOWERING 6 are not its work.
//!
//! Slices: T6a is the handle, the table, the leaves and the operators, calls
//! and members; T6b is statements and statement lists. Until a slice is
//! built its bodies are `todo!` and its tests are ignored by its name.
//!
//! # The flags of a node
//!
//! Those `bir/j/facts.rs` computes for the same J node (`purity`,
//! `delay_safe`, `subexpression`, `external_duplicable`), from the rows of
//! the operands, in O(arity). "Operand", "both", "all": the flag holds for
//! the node when it holds for those operands.
//!
//! | Kind | `PURE` and `STRICT` | `DELAY_SAFE` | `SUBEXPR` | `DUPLICABLE` |
//! | --- | --- | --- | --- | --- |
//! | `Var` | yes | not assigned and not a global | yes | not a global |
//! | `Named` | yes | no | yes | no |
//! | `Number`, `Str` | yes | yes | yes | yes |
//! | `Bool`, `Undefined` | yes | yes | no | yes |
//! | `Null` | yes | yes | no | no |
//! | `Bin` | not `=`, and both. `STRICT` reads the right operand of `**`, `/` and `%` as a literal instead (E:15): an integer that is not zero (any integer for `**`); any float; a bigint whose digits are not `0` (for `**`: with the positive sign); nothing else | not `=`, the node is `PURE`, and both | no | no |
//! | `Not`, `Bnot`, `Typeof`, `IsNullish` | operand | operand | no | no |
//! | `In` | both | no | no | no |
//! | `StrAppend` | both | both | no | no |
//! | `Cond` | all | all | no | all |
//! | `Seq` | both | no | both | no |
//! | `Dot` | operand | no | no | a position is given, and the operand |
//! | `Length` | operand | no | no | no |
//! | `Index` | both | no | both | both |
//! | `Call` | exactly one argument, and it; the callee is `Array.isArray`: a `Dot` named `isArray`, without position, not a tag, on a `Named` JavaScript identifier `Array` (B:164) | no | no | no |
//! | `New` | no | no | no | no |
//!
//! `HAS_FUN`, `SEAL` and `HAS_GLOBAL` hold for a node, and for a statement,
//! when they hold for anything it is built from. `SEAL` is set where it
//! starts: by [`Builder::bin`] for `&&`, `||` and `|` whose right operand is
//! a `Bin` of the same operator, and by [`Builder::seq`] when an operand is
//! a `Seq`. `HAS_GLOBAL` starts at [`Builder::reference`] of a variable the
//! caller knows as a JavaScript global (`var::GLOBAL`). A statement's row
//! has no other flag.
pub(crate) use super::row::{Kind, Row, flag, num, var};
use super::{Unsupported, literal, walk};
use crate::js_ir::op::{BinOp, Number};
use crate::js_ir::printer::normalize_float_literal_for_js_into;
use oxc_allocator::{Allocator, CloneIn, GetAllocator, Vec as ArenaVec};
use oxc_ast::{ast::*, builder::AstBuilder};
use oxc_span::SPAN;
use oxc_syntax::{
    node::NodeId,
    number::{BigintBase, NumberBase},
    operator::{AssignmentOperator, BinaryOperator, LogicalOperator, UnaryOperator},
    reference::ReferenceId,
    symbol::SymbolId,
};

/// The five facts a literal has (`Number`, `Str`).
const LITERAL: u16 =
    flag::PURE | flag::STRICT | flag::DELAY_SAFE | flag::SUBEXPR | flag::DUPLICABLE;

/// [`Row::payload`] of a float literal whose text is `0.`: the one float
/// `0 - x` prints as `-x` for (`walk::negation_form`, OCaml
/// `compiler/core/js_dump.ml`, `Bin (Minus, Number (Float {f = "0."}), e)`).
/// The text is not in the row otherwise; every other float has payload 0.
const FLOAT_ZERO_TEXT: u32 = 1;

/// `PURE` and `STRICT`, which a node of the table takes from its operands
/// alike (except `Bin`'s `STRICT`).
const PURITY: u16 = flag::PURE | flag::STRICT;

/// `HAS_FUN`, `SEAL` and `HAS_GLOBAL`: what a node holds when an operand
/// holds it.
const INHERITED: u16 = flag::HAS_FUN | flag::SEAL | flag::HAS_GLOBAL;

/// The flags of a node with one operand whose `kept` flags hold when they
/// hold for the operand. O(1).
fn of_operand(operand: Row, kept: u16) -> u16 {
    operand.flags & (kept | INHERITED)
}

/// The flags of a node with two operands whose `kept` flags hold when they
/// hold for both. O(1).
fn of_both(left: Row, right: Row, kept: u16) -> u16 {
    (left.flags & right.flags & kept) | ((left.flags | right.flags) & INHERITED)
}

/// E:15 `js_expr_no_side_effects` of `**`, `/` and `%`: the right operand
/// read as a literal (the table in the header). O(1).
fn strict_divisor(op: BinOp, right: Row) -> bool {
    if right.kind != Kind::Number {
        return false;
    }
    let power = op == BinOp::Pow;
    match right.aux & num::CLASS {
        num::INT => power || right.aux & num::NONZERO != 0,
        num::FLOAT => true,
        num::BIGINT => right.aux & if power { num::POSITIVE } else { num::NONZERO } != 0,
        _ => false,
    }
}

/// The flags of `left op right` (the `Bin` row of the table). O(1).
fn bin_flags(op: BinOp, left: Row, right: Row) -> u16 {
    let mut flags = (left.flags | right.flags) & INHERITED;
    if op == BinOp::Eq {
        return flags;
    }
    let pure = left.has(flag::PURE) && right.has(flag::PURE);
    if pure {
        flags |= flag::PURE;
        if left.has(flag::DELAY_SAFE) && right.has(flag::DELAY_SAFE) {
            flags |= flag::DELAY_SAFE;
        }
    }
    let strict_right = if matches!(op, BinOp::Pow | BinOp::Div | BinOp::Mod) {
        strict_divisor(op, right)
    } else {
        right.has(flag::STRICT)
    };
    if left.has(flag::STRICT) && strict_right {
        flags |= flag::STRICT;
    }
    flags
}

/// The oxc operator of a `BinOp` printed as a binary expression; `None`
/// for those that are not (`=`, `&&`, `||`, the binary bitwise-not). O(1).
fn binary_operator(op: BinOp) -> Option<BinaryOperator> {
    use BinaryOperator as B;
    Some(match op {
        BinOp::EqEqEq => B::StrictEquality,
        BinOp::NotEqEq => B::StrictInequality,
        BinOp::Lt | BinOp::FloatLt => B::LessThan,
        BinOp::Le | BinOp::FloatLe => B::LessEqualThan,
        BinOp::Gt | BinOp::FloatGt => B::GreaterThan,
        BinOp::Ge | BinOp::FloatGe => B::GreaterEqualThan,
        BinOp::Bor => B::BitwiseOR,
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
        BinOp::Eq | BinOp::Or | BinOp::And | BinOp::Bnot => return None,
    })
}

/// An expression in flight: the oxc node and its facts. 24 bytes. The node
/// is 16 (a tag and an arena box); the row beside it saves the load of the
/// node's `node_id` and of its table row for every operand a rule reads.
/// Not `Copy`: an operand is consumed by the constructor that attaches it.
pub(crate) struct J<'a> {
    pub expr: Expression<'a>,
    pub row: Row,
}

/// The first operand of a list a constructor consumes ([`Builder::mark`]).
#[derive(Clone, Copy)]
pub(crate) struct Mark(u32);

/// A statement in flight, in the form the lowering's rules read (a `return`
/// always has its value, an `if` always has both blocks): the print form is
/// the seal's. 24 bytes, as [`J`]. Not `Copy`.
pub(crate) struct S<'a> {
    pub stmt: Statement<'a>,
    pub row: Row,
}

impl<'a> S<'a> {
    /// The expression the statement evaluates first, read in place: the
    /// value of an expression statement, of a `return`, of a `throw` and of
    /// a declaration that has one; the test of an `if` and of a `while`.
    /// `None` for every other statement. (The lowering's `JsStmt::value_of`
    /// also gives the scrutinee of a `switch`: the builder makes no
    /// `switch` yet, and the slice that adds one adds its scrutinee here.)
    /// Its row is [`Builder::row`] of it.
    /// O(1): the statement's node and one field of it.
    pub fn value(&self) -> Option<&Expression<'a>> {
        match &self.stmt {
            Statement::ExpressionStatement(statement) => Some(&statement.expression),
            Statement::ReturnStatement(statement) => statement.argument.as_ref(),
            Statement::ThrowStatement(statement) => Some(&statement.argument),
            Statement::VariableDeclaration(declaration) => declaration.declarations.first()?.init.as_ref(),
            Statement::IfStatement(statement) => Some(&statement.test),
            Statement::WhileStatement(statement) => Some(&statement.test),
            _ => None,
        }
    }
}

/// A statement list in flight: a run of [`Builder::pool`]. 8 bytes, `Copy`;
/// a statement is taken out of it at most once.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct List {
    start: u32,
    len: u32,
}

impl List {
    /// The list without statements. O(1).
    pub const EMPTY: List = List { start: 0, len: 0 };
    /// O(1).
    pub fn len(self) -> usize {
        self.len as usize
    }
    /// O(1).
    pub fn is_empty(self) -> bool {
        self.len == 0
    }
}

/// The builder of one compilation unit.
pub(crate) struct Builder<'a> {
    pub ast: AstBuilder<'a>,
    /// The row of every node built, dense by `node_id`; entry 0 is unused
    /// (`NodeId::DUMMY`).
    rows: Vec<Row>,
    /// Operands of the list constructors, pushed by the caller.
    operands: Vec<J<'a>>,
    /// Statements staged for the next [`Builder::list`].
    staged: Vec<S<'a>>,
    /// The statements of the lists in flight; `None` once taken.
    pool: Vec<Option<S<'a>>>,
    /// Unit operations: one per node built and one per operand of a list.
    pub steps: u64,
    /// The normalized text of the float literal [`Builder::number`] reads,
    /// cleared and reused: it grows to the longest literal of the builder's
    /// life and allocates nothing after that.
    float_text: String,
    /// The member reads [`Builder::copy_members`] has still to write, the
    /// innermost last: the copied property of each with the `aux` and the
    /// payload of its row. Empty between calls and kept, so that a copy
    /// allocates only when a chain is deeper than any before it.
    members: Vec<(Property<'a>, u8, u32)>,
    /// The declarations whose initialiser is a reference, as (`node_id` of
    /// the statement, variable of the reference), in the order they were
    /// made: sorted by id, since ids ascend. What [`Builder::alias_at`]
    /// reads.
    aliases: Vec<(u32, u32)>,
    /// The allocation of the work stack of [`Builder::references`] and
    /// [`Builder::return_calls`], kept between walks. Such a stack holds
    /// references into the tree, which borrow it for one walk, so the
    /// builder keeps the storage as words and each walk takes it as an
    /// empty vector of references ([`recycle`]). Always empty.
    spare: Vec<usize>,
}

/// An empty vector of `U` over the allocation of `from`, which is cleared:
/// how a walk keeps the storage of a stack of references whose lifetime
/// ends with it. No allocation when `T` and `U` have one size and one
/// alignment (the standard library collects a mapped `Vec` iterator into
/// the vector it came from); with other types the result is a new, empty
/// vector. O(1).
fn recycle<T, U>(mut from: Vec<T>) -> Vec<U> {
    from.clear();
    from.into_iter().map(|_| unreachable!("the vector is empty")).collect()
}

/// What [`Builder::references`] finds: a reference to a variable or a name
/// the unit does not bind, with the `node_id` of the reference, or a
/// function literal by the header its row holds. 12 bytes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Reference {
    Var { variable: u32, id: u32 },
    Named { id: u32 },
    Function(u32),
}

/// The property of a member read, taken from the read it is copied from.
enum Property<'a> {
    /// `object.name`.
    Static(IdentifierName<'a>),
    /// `object[key]`.
    Computed(Expression<'a>),
}

/// What a walk of [`Builder::substitute`] has still to read.
enum Pending<'s, 'a> {
    Statement(&'s mut Statement<'a>),
    Expression(&'s mut Expression<'a>),
}

impl<'a> Builder<'a> {
    /// One allocation for the table and one for the operand stack, both
    /// empty until [`Builder::reserve`].
    pub fn new(allocator: &'a Allocator) -> Self {
        Self {
            ast: AstBuilder::new(allocator),
            rows: vec![Row { flags: 0, kind: Kind::Null, aux: 0, payload: 0 }],
            operands: Vec::new(),
            staged: Vec::new(),
            pool: Vec::new(),
            steps: 0,
            float_text: String::new(),
            members: Vec::new(),
            aliases: Vec::new(),
            spare: Vec::new(),
        }
    }

    /// Room for `nodes` nodes and `operands` pending operands: at most two
    /// allocations, none when the capacity is there.
    pub fn reserve(&mut self, nodes: usize, operands: usize) {
        self.rows.reserve(nodes);
        self.operands.reserve(operands);
    }

    /// Start a unit with the capacity of the last one. O(1); no allocation.
    pub fn clear(&mut self) {
        self.rows.truncate(1);
        self.operands.clear();
        self.staged.clear();
        self.pool.clear();
        self.aliases.clear();
        self.steps = 0;
    }

    /// Nodes built in this unit. O(1).
    pub fn nodes(&self) -> usize {
        self.rows.len() - 1
    }

    /// The row of a node that is inside a parent. O(1): the node's
    /// `node_id` and one indexed read.
    pub fn row(&self, expr: &Expression<'a>) -> Row {
        self.rows[expr.node_id().index()]
    }

    /// Give `expr` the next `node_id`, push its row and count the step.
    /// O(1): one store into the node and one push onto the table.
    fn attach(&mut self, expr: Expression<'a>, row: Row) -> J<'a> {
        expr.set_node_id(NodeId::from_usize(self.rows.len()));
        self.rows.push(row);
        self.steps += 1;
        J { expr, row }
    }

    /// `-value`, a node of the printed form without a row of its own (the
    /// row is that of the constructor that writes it). O(1).
    fn negation(&self, value: Expression<'a>) -> Expression<'a> {
        Expression::new_unary_expression(SPAN, UnaryOperator::UnaryNegation, value, &self.ast)
    }

    /// The numeric literal `value` (not negative). O(1).
    fn numeric(&self, value: f64) -> Expression<'a> {
        Expression::new_numeric_literal(SPAN, value, None, NumberBase::Decimal, &self.ast)
    }

    /// `target.name`, or `target[name]` with a numeric or string key when
    /// the name is no identifier (`Build::member`). O(length of the name):
    /// the name is copied into the arena.
    fn member(&self, target: Expression<'a>, name: &str) -> Expression<'a> {
        let (name, dot) = walk::member_form(name);
        if dot {
            let property =
                IdentifierName::new(SPAN, self.ast.allocator().alloc_str(name), &self.ast);
            return Expression::new_static_member_expression(
                SPAN, target, property, false, &self.ast,
            );
        }
        let key = match walk::numeric_member(name) {
            Some(index) => {
                let value = self.numeric(index.unsigned_abs() as f64);
                if index < 0 { self.negation(value) } else { value }
            }
            None => {
                let text = literal::arena_string(name, self.ast.allocator());
                Expression::new_string_literal(SPAN, text, None, &self.ast)
            }
        };
        Expression::new_computed_member_expression(SPAN, target, key, false, &self.ast)
    }

    /// B:164 `is_array_is_array_callee`: `callee` is a `Dot` named
    /// `isArray`, without position, not a tag, on a `Named` JavaScript
    /// identifier `Array`. O(1): the callee's row, its node and the table
    /// row of its object.
    fn is_array_is_array(&self, callee: &J<'a>) -> bool {
        if callee.row.kind != Kind::Dot || callee.row.payload != 0 || callee.row.aux != 0 {
            return false;
        }
        let Expression::StaticMemberExpression(member) = &callee.expr else {
            return false;
        };
        if member.property.name != "isArray" {
            return false;
        }
        let object = self.row(&member.object);
        object.kind == Kind::Named
            && object.aux == 1
            && matches!(&member.object, Expression::Identifier(id) if id.name == "Array")
    }

    /// A reference to variable `var`, printed through the name table (the
    /// reference id is the variable's index). `known` is of [`var`]; a
    /// reference to a JavaScript global (`var::GLOBAL`) has `HAS_GLOBAL`,
    /// which every node and statement built over it inherits: it is what
    /// the replay's descent is pruned by ([`Builder::below`]). O(1).
    pub fn reference(&mut self, variable: u32, known: u8) -> J<'a> {
        let expr = Expression::new_identifier_with_reference_id(
            SPAN,
            "",
            ReferenceId::from_usize(variable as usize),
            &self.ast,
        );
        let mut flags = flag::PURE | flag::STRICT | flag::SUBEXPR;
        if known & (var::ASSIGNED | var::GLOBAL) == 0 {
            flags |= flag::DELAY_SAFE;
        }
        if known & var::GLOBAL == 0 {
            flags |= flag::DUPLICABLE;
        } else {
            flags |= flag::HAS_GLOBAL;
        }
        self.attach(expr, Row { flags, kind: Kind::Var, aux: known, payload: variable })
    }

    /// An identifier printed as `name`: a name the unit does not bind. `js`
    /// says it is a JavaScript identifier (the `JS` flag, or a global of
    /// stamp zero): B:164 reads it. O(length of the name): the name is
    /// copied into the arena.
    pub fn named(&mut self, name: &str, js: bool) -> J<'a> {
        let name = self.ast.allocator().alloc_str(name);
        let expr = Expression::new_identifier(SPAN, name, &self.ast);
        let flags = flag::PURE | flag::STRICT | flag::SUBEXPR;
        self.attach(expr, Row { flags, kind: Kind::Named, aux: u8::from(js), payload: 0 })
    }

    /// `undefined`; `unit` marks the unit value. O(1).
    pub fn undefined(&mut self, unit: bool) -> J<'a> {
        let expr = Expression::new_identifier(SPAN, "undefined", &self.ast);
        let flags = flag::PURE | flag::STRICT | flag::DELAY_SAFE | flag::DUPLICABLE;
        self.attach(expr, Row { flags, kind: Kind::Undefined, aux: u8::from(unit), payload: 0 })
    }

    /// `null`. O(1).
    pub fn null(&mut self) -> J<'a> {
        let expr = Expression::new_null_literal(SPAN, &self.ast);
        let flags = flag::PURE | flag::STRICT | flag::DELAY_SAFE;
        self.attach(expr, Row { flags, kind: Kind::Null, aux: 0, payload: 0 })
    }

    /// A boolean literal. O(1).
    pub fn boolean(&mut self, value: bool) -> J<'a> {
        let expr = Expression::new_boolean_literal(SPAN, value, &self.ast);
        let flags = flag::PURE | flag::STRICT | flag::DELAY_SAFE | flag::DUPLICABLE;
        self.attach(expr, Row { flags, kind: Kind::Bool, aux: u8::from(value), payload: 0 })
    }

    /// A string literal. O(length): the text is copied into the arena.
    pub fn string(&mut self, value: &str) -> J<'a> {
        let text = literal::arena_string(value, self.ast.allocator());
        let expr = Expression::new_string_literal(SPAN, text, None, &self.ast);
        self.attach(expr, Row { flags: LITERAL, kind: Kind::Str, aux: 0, payload: 0 })
    }

    /// An integer literal; a negative one is `-n`. O(1).
    pub fn int(&mut self, value: i32) -> J<'a> {
        let literal = self.numeric(f64::from(value.unsigned_abs()));
        let expr = if value < 0 { self.negation(literal) } else { literal };
        let aux = num::INT | if value != 0 { num::NONZERO } else { 0 };
        self.attach(expr, Row { flags: LITERAL, kind: Kind::Number, aux, payload: value as u32 })
    }

    /// A number literal as the printer spells it (A.7, number spelling):
    /// `NaN`, `Infinity`, a leading `-` as a negation. O(length of the
    /// literal's text).
    pub fn number(&mut self, n: &Number) -> Result<J<'a>, Unsupported> {
        let row = |aux, payload| Row { flags: LITERAL, kind: Kind::Number, aux, payload };
        match n {
            Number::Int { i, .. } => Ok(self.int(*i)),
            Number::BigInt(n) => {
                // Keep lexical radix normalization explicit rather than
                // guessing from digits (`Build::number`).
                if !n.value.chars().all(|c| c.is_ascii_digit()) {
                    return Err(Unsupported("non-decimal bigint"));
                }
                let digits = self.ast.allocator().alloc_str(&n.value);
                let literal = Expression::new_big_int_literal(
                    SPAN,
                    digits,
                    None,
                    BigintBase::Decimal,
                    &self.ast,
                );
                let mut aux = num::BIGINT;
                if n.value != "0" {
                    aux |= num::NONZERO;
                }
                let expr = if n.positive {
                    aux |= num::POSITIVE;
                    literal
                } else {
                    self.negation(literal)
                };
                Ok(self.attach(expr, row(aux, 0)))
            }
            Number::Float(f) => {
                self.float_text.clear();
                normalize_float_literal_for_js_into(&f.f, &mut self.float_text);
                let value =
                    self.float_text.parse::<f64>().map_err(|_| Unsupported("float literal"))?;
                let literal = if value.is_nan() {
                    Expression::new_identifier(SPAN, "NaN", &self.ast)
                } else if value.is_infinite() {
                    Expression::new_identifier(SPAN, "Infinity", &self.ast)
                } else {
                    self.numeric(value.abs())
                };
                let expr = if value.is_sign_negative() { self.negation(literal) } else { literal };
                let payload = if f.f == "0." { FLOAT_ZERO_TEXT } else { 0 };
                Ok(self.attach(expr, row(num::FLOAT, payload)))
            }
        }
    }

    /// `!value`, as given (J-E8 is a rule, not this constructor). O(1).
    pub fn not(&mut self, value: J<'a>) -> J<'a> {
        let row = Row {
            flags: of_operand(value.row, PURITY | flag::DELAY_SAFE),
            kind: Kind::Not,
            aux: 0,
            payload: 0,
        };
        let expr = Expression::new_unary_expression(
            SPAN,
            UnaryOperator::LogicalNot,
            value.expr,
            &self.ast,
        );
        self.attach(expr, row)
    }

    /// `~value`. O(1).
    pub fn bnot(&mut self, value: J<'a>) -> J<'a> {
        let row = Row {
            flags: of_operand(value.row, PURITY | flag::DELAY_SAFE),
            kind: Kind::Bnot,
            aux: 0,
            payload: 0,
        };
        let expr = Expression::new_unary_expression(
            SPAN,
            UnaryOperator::BitwiseNot,
            value.expr,
            &self.ast,
        );
        self.attach(expr, row)
    }

    /// `typeof value`. O(1).
    pub fn typeof_(&mut self, value: J<'a>) -> J<'a> {
        let row = Row {
            flags: of_operand(value.row, PURITY | flag::DELAY_SAFE),
            kind: Kind::Typeof,
            aux: 0,
            payload: 0,
        };
        let expr =
            Expression::new_unary_expression(SPAN, UnaryOperator::Typeof, value.expr, &self.ast);
        self.attach(expr, row)
    }

    /// The nullish test, printed `value == null` (A.7). O(1).
    pub fn is_nullish(&mut self, value: J<'a>) -> J<'a> {
        let row = Row {
            flags: of_operand(value.row, PURITY | flag::DELAY_SAFE),
            kind: Kind::IsNullish,
            aux: 0,
            payload: 0,
        };
        let null = Expression::new_null_literal(SPAN, &self.ast);
        let expr = Expression::new_binary_expression(
            SPAN,
            value.expr,
            BinaryOperator::Equality,
            null,
            &self.ast,
        );
        self.attach(expr, row)
    }

    /// `left in right`. O(1).
    pub fn in_(&mut self, left: J<'a>, right: J<'a>) -> J<'a> {
        let row =
            Row { flags: of_both(left.row, right.row, PURITY), kind: Kind::In, aux: 0, payload: 0 };
        let expr = Expression::new_binary_expression(
            SPAN,
            left.expr,
            BinaryOperator::In,
            right.expr,
            &self.ast,
        );
        self.attach(expr, row)
    }

    /// The string concatenation `left + right`, as given (J-E1 is a rule).
    /// O(1).
    pub fn str_append(&mut self, left: J<'a>, right: J<'a>) -> J<'a> {
        let flags = of_both(left.row, right.row, PURITY | flag::DELAY_SAFE);
        let row = Row { flags, kind: Kind::StrAppend, aux: 0, payload: 0 };
        let expr = Expression::new_binary_expression(
            SPAN,
            left.expr,
            BinaryOperator::Addition,
            right.expr,
            &self.ast,
        );
        self.attach(expr, row)
    }

    /// The binary operation as given (J-E4 is a rule, not this constructor),
    /// with the printer's decisions of A.7 that depend on the node alone:
    /// `0 - x` is `-x`; `x === null || x === undefined` on one variable is
    /// `x == null`; `=` is an assignment. A logical or `|` chain whose right
    /// operand is a chain of the same operator is marked for the seal, which
    /// writes it in print form. O(1).
    pub fn bin(&mut self, op: BinOp, left: J<'a>, right: J<'a>) -> Result<J<'a>, Unsupported> {
        let mut flags = bin_flags(op, left.row, right.row);
        // A chain the lowering built right-nested is not in print form.
        if matches!(op, BinOp::And | BinOp::Or | BinOp::Bor)
            && right.row.kind == Kind::Bin
            && right.row.aux == op as u8
        {
            flags |= flag::SEAL;
        }
        let row = |flags| Row { flags, kind: Kind::Bin, aux: op as u8, payload: 0 };
        // `0 - x` prints `-x` (`walk::negation_form`).
        if op == BinOp::Minus
            && left.row.kind == Kind::Number
            && match left.row.aux & num::CLASS {
                num::INT => left.row.payload == 0,
                num::FLOAT => left.row.payload == FLOAT_ZERO_TEXT,
                _ => false,
            }
        {
            let expr = self.negation(right.expr);
            return Ok(self.attach(expr, row(flags)));
        }
        // `x === null || x === undefined` prints `x == null`
        // (`walk::nullish_target`).
        let strict_equality = |row: Row| row.kind == Kind::Bin && row.aux == BinOp::EqEqEq as u8;
        if op == BinOp::Or && strict_equality(left.row) && strict_equality(right.row) {
            let (Expression::BinaryExpression(l), Expression::BinaryExpression(r)) =
                (&left.expr, &right.expr)
            else {
                unreachable!("a `===` is built as a binary expression")
            };
            let pair = (self.row(&l.right).kind, self.row(&r.right).kind);
            if matches!(pair, (Kind::Null, Kind::Undefined) | (Kind::Undefined, Kind::Null)) {
                let (x, y) = (self.row(&l.left), self.row(&r.left));
                let same = match (x.kind, y.kind) {
                    (Kind::Var, Kind::Var) => x.payload == y.payload,
                    (Kind::Named, Kind::Named) => matches!(
                        (&l.left, &r.left),
                        (Expression::Identifier(x), Expression::Identifier(y)) if x.name == y.name
                    ),
                    _ => false,
                };
                if !same {
                    return Err(Unsupported("nullish comparison target equality"));
                }
                let Expression::BinaryExpression(l) = left.expr else { unreachable!() };
                let target = l.unbox().left;
                let null = Expression::new_null_literal(SPAN, &self.ast);
                let expr = Expression::new_binary_expression(
                    SPAN,
                    target,
                    BinaryOperator::Equality,
                    null,
                    &self.ast,
                );
                return Ok(self.attach(expr, row(flags)));
            }
        }
        let expr = match op {
            BinOp::And | BinOp::Or => {
                let operator =
                    if op == BinOp::And { LogicalOperator::And } else { LogicalOperator::Or };
                Expression::new_logical_expression(SPAN, left.expr, operator, right.expr, &self.ast)
            }
            BinOp::Eq => {
                let target = match left.expr {
                    Expression::StaticMemberExpression(m) => {
                        AssignmentTarget::StaticMemberExpression(m)
                    }
                    Expression::ComputedMemberExpression(m) => {
                        AssignmentTarget::ComputedMemberExpression(m)
                    }
                    Expression::Identifier(id) => AssignmentTarget::AssignmentTargetIdentifier(id),
                    _ => return Err(Unsupported("assignment target")),
                };
                Expression::new_assignment_expression(
                    SPAN,
                    AssignmentOperator::Assign,
                    target,
                    right.expr,
                    &self.ast,
                )
            }
            BinOp::Bnot => return Err(Unsupported("binary bitwise-not")),
            _ => {
                let operator = binary_operator(op).expect("a binary operator");
                Expression::new_binary_expression(SPAN, left.expr, operator, right.expr, &self.ast)
            }
        };
        Ok(self.attach(expr, row(flags)))
    }

    /// `test ? then : otherwise`, as given (J-E7 is a rule). O(1).
    pub fn cond(&mut self, test: J<'a>, then: J<'a>, otherwise: J<'a>) -> J<'a> {
        let all = test.row.flags & then.row.flags & otherwise.row.flags;
        let any = test.row.flags | then.row.flags | otherwise.row.flags;
        let flags = (all & (PURITY | flag::DELAY_SAFE | flag::DUPLICABLE)) | (any & INHERITED);
        let row = Row { flags, kind: Kind::Cond, aux: 0, payload: 0 };
        let expr = Expression::new_conditional_expression(
            SPAN,
            test.expr,
            then.expr,
            otherwise.expr,
            &self.ast,
        );
        self.attach(expr, row)
    }

    /// `first, second`, as given (J-M1 is a rule): a sequence of two. A
    /// sequence with a sequence as operand is marked for the seal, which
    /// writes one flat list. O(1).
    pub fn seq(&mut self, first: J<'a>, second: J<'a>) -> J<'a> {
        let mut flags = of_both(first.row, second.row, PURITY | flag::SUBEXPR);
        if first.row.kind == Kind::Seq || second.row.kind == Kind::Seq {
            flags |= flag::SEAL;
        }
        let mut expressions = ArenaVec::with_capacity_in(2, &self.ast);
        expressions.push(first.expr);
        expressions.push(second.expr);
        let expr = Expression::new_sequence_expression(SPAN, expressions, &self.ast);
        self.attach(expr, Row { flags, kind: Kind::Seq, aux: 0, payload: 0 })
    }

    /// `object.name`, or `object["name"]` when the name is no identifier
    /// (A.7, property access). `position` is the field's position in its
    /// block; `tag` says the read is of a block's tag. O(length of the
    /// name).
    pub fn dot(&mut self, object: J<'a>, name: &str, position: Option<u32>, tag: bool) -> J<'a> {
        let row = Self::dot_row(object.row, position.map_or(0, |p| p + 1), u8::from(tag));
        let expr = self.member(object.expr, name);
        self.attach(expr, row)
    }

    /// The row of a member read of `object` (the `Dot` row of the table):
    /// `payload` is the position plus one, zero for none; `aux` the tag
    /// bit. O(1).
    fn dot_row(object: Row, payload: u32, aux: u8) -> Row {
        let mut flags = of_operand(object, PURITY);
        if payload != 0 && object.has(flag::DUPLICABLE) {
            flags |= flag::DUPLICABLE;
        }
        Row { flags, kind: Kind::Dot, aux, payload }
    }

    /// The id of the node built last: a key (the lowering's `Js::id`).
    /// O(1).
    fn last_id(&self) -> u32 {
        self.rows.len() as u32 - 1
    }

    /// A new leaf with the node and the row of the leaf `leaf`, which
    /// stays where it is (the lowering's `Js::copy_leaf`). The row is the
    /// original's: a leaf has every flag from its constructor, and no
    /// function of the builder changes a row afterwards. O(1) but for a
    /// string, a bigint and a name, whose text is copied into the arena:
    /// O(length). Panics when `leaf` is not a `Var`, `Named`, `Number`,
    /// `Str`, `Bool`, `Null` or `Undefined`.
    pub fn copy_leaf(&mut self, leaf: &Expression<'a>) -> J<'a> {
        let row = self.row(leaf);
        assert!(
            matches!(
                row.kind,
                Kind::Var | Kind::Named | Kind::Number | Kind::Str | Kind::Bool | Kind::Null | Kind::Undefined
            ),
            "a copy of a leaf that is a {:?}",
            row.kind
        );
        // With its semantic ids: a reference is printed through its
        // reference id, which a plain clone leaves out.
        let expr = leaf.clone_in_with_semantic_ids(self.ast.allocator());
        self.attach(expr, row)
    }

    /// A copy of a chain of member reads (the lowering's
    /// `Js::copy_members`): of the reads from `chain` down to the first
    /// node that is not a `Dot`, and of that node, a leaf
    /// ([`Builder::copy_leaf`]). Each read is written again from the
    /// innermost out with the property, the position and the tag bit of
    /// its original, and its row is computed from the row of the copy
    /// below it, as [`Builder::dot`] computes it. `made` is given the id
    /// of each node made, in that order. `chain` is the caller's node (a
    /// handle's, or one inside a statement it holds) and stays whole.
    ///
    /// One step per node made; the chain is read once more on the way
    /// down, which counts nothing. A property is copied into the arena
    /// (O(length of its name)). Allocates outside the arena only when the
    /// chain is deeper than any copied before (`Builder::members`).
    pub fn copy_members(&mut self, chain: &Expression<'a>, mut made: impl FnMut(u32)) -> J<'a> {
        let base = self.members.len();
        let mut at = chain;
        loop {
            let row = self.row(at);
            if row.kind != Kind::Dot {
                break;
            }
            let (property, object) = match at {
                Expression::StaticMemberExpression(member) => (
                    Property::Static(member.property.clone_in(self.ast.allocator())),
                    &member.object,
                ),
                Expression::ComputedMemberExpression(member) => (
                    Property::Computed(member.expression.clone_in(self.ast.allocator())),
                    &member.object,
                ),
                _ => unreachable!("a `Dot` is built as a member expression"),
            };
            self.members.push((property, row.aux, row.payload));
            at = object;
        }
        let mut copy = self.copy_leaf(at);
        made(self.last_id());
        while self.members.len() > base {
            let (property, aux, payload) = self.members.pop().expect("a member read");
            let row = Self::dot_row(copy.row, payload, aux);
            let expr = match property {
                Property::Static(property) => {
                    Expression::new_static_member_expression(SPAN, copy.expr, property, false, &self.ast)
                }
                Property::Computed(key) => {
                    Expression::new_computed_member_expression(SPAN, copy.expr, key, false, &self.ast)
                }
            };
            copy = self.attach(expr, row);
            made(self.last_id());
        }
        copy
    }

    /// `value.length`. O(1).
    pub fn length(&mut self, value: J<'a>) -> J<'a> {
        let row =
            Row { flags: of_operand(value.row, PURITY), kind: Kind::Length, aux: 0, payload: 0 };
        let property = IdentifierName::new(SPAN, "length", &self.ast);
        let expr =
            Expression::new_static_member_expression(SPAN, value.expr, property, false, &self.ast);
        self.attach(expr, row)
    }

    /// `object[index]`. O(1).
    pub fn index(&mut self, object: J<'a>, index: J<'a>) -> J<'a> {
        let flags = of_both(object.row, index.row, PURITY | flag::SUBEXPR | flag::DUPLICABLE);
        let row = Row { flags, kind: Kind::Index, aux: 0, payload: 0 };
        let expr = Expression::new_computed_member_expression(
            SPAN,
            object.expr,
            index.expr,
            false,
            &self.ast,
        );
        self.attach(expr, row)
    }

    /// The operands pushed from here on belong to the next list
    /// constructor. O(1).
    pub fn mark(&self) -> Mark {
        Mark(self.operands.len() as u32)
    }

    /// One operand of the list being collected. O(1): a move of 24 bytes
    /// onto the builder's stack.
    pub fn push(&mut self, operand: J<'a>) {
        self.operands.push(operand);
    }

    /// `callee(arguments since mark)`. `info` is the lowering's call
    /// information; `pure` writes the pure annotation. A call is pure only
    /// as `Array.isArray(x)` over a pure `x` (B:164). One step per
    /// argument.
    pub fn call(&mut self, callee: J<'a>, mark: Mark, info: u32, pure: bool) -> J<'a> {
        let start = mark.0 as usize;
        let count = self.operands.len() - start;
        let is_array = self.is_array_is_array(&callee);
        // A call whose only argument is the unit value prints `f()`
        // (`walk::arguments`).
        let unit = count == 1 && {
            let row = self.operands[start].row;
            row.kind == Kind::Undefined && row.aux == 1
        };
        let mut arguments = ArenaVec::with_capacity_in(if unit { 0 } else { count }, &self.ast);
        let mut flags = callee.row.flags & INHERITED;
        let mut argument_purity = PURITY;
        for operand in self.operands.drain(start..) {
            flags |= operand.row.flags & INHERITED;
            argument_purity &= operand.row.flags;
            if !unit {
                arguments.push(Argument::from(operand.expr));
            }
        }
        self.steps += count as u64;
        if count == 1 && is_array {
            flags |= argument_purity;
        }
        let mut node = CallExpression::new(SPAN, callee.expr, None, arguments, false, &self.ast);
        node.pure = pure;
        let expr = Expression::CallExpression(oxc_allocator::Box::new_in(node, &self.ast));
        self.attach(expr, Row { flags, kind: Kind::Call, aux: 0, payload: info })
    }

    /// `new callee(arguments since mark)`. One step per argument.
    pub fn new_(&mut self, callee: J<'a>, mark: Mark) -> J<'a> {
        let start = mark.0 as usize;
        let count = self.operands.len() - start;
        let mut arguments = ArenaVec::with_capacity_in(count, &self.ast);
        let mut flags = callee.row.flags & INHERITED;
        for operand in self.operands.drain(start..) {
            flags |= operand.row.flags & INHERITED;
            arguments.push(Argument::from(operand.expr));
        }
        self.steps += count as u64;
        let expr = Expression::new_new_expression(SPAN, callee.expr, None, arguments, &self.ast);
        self.attach(expr, Row { flags, kind: Kind::New, aux: 0, payload: 0 })
    }
}

/// T6b: statements and statement lists.
impl<'a> Builder<'a> {
    /// Room for `statements` statements in lists in flight and `staged`
    /// staged ones: at most two allocations, none when the capacity is
    /// there.
    pub fn reserve_statements(&mut self, statements: usize, staged: usize) {
        self.pool.reserve(statements);
        self.staged.reserve(staged);
    }

    /// The row of a statement that is inside a list of the tree. O(1).
    pub fn statement_row(&self, stmt: &Statement<'a>) -> Row {
        self.rows[stmt.node_id().index()]
    }

    /// Give `stmt` the next `node_id`, push its row and count the step: the
    /// statement twin of [`Builder::attach`]. O(1).
    fn attach_statement(&mut self, stmt: Statement<'a>, row: Row) -> S<'a> {
        stmt.set_node_id(NodeId::from_usize(self.rows.len()));
        self.rows.push(row);
        self.steps += 1;
        S { stmt, row }
    }

    /// The statements of `list` moved out of the pool into an arena vector
    /// of exactly that length, and the union of their rows' flags (read in
    /// the pool, not the table). One step and one move of 24 bytes per
    /// statement; panics on a statement taken before.
    fn drain(&mut self, list: List) -> (ArenaVec<'a, Statement<'a>>, u16) {
        let mut body = ArenaVec::with_capacity_in(list.len(), &self.ast);
        let mut flags = 0;
        let start = list.start as usize;
        for slot in &mut self.pool[start..start + list.len()] {
            let statement = slot.take().expect("a statement taken twice");
            flags |= statement.row.flags;
            body.push(statement.stmt);
        }
        self.steps += list.len() as u64;
        (body, flags)
    }

    /// `{ list }` as a block statement of the print form, without a row of
    /// its own (the row is that of the constructor that writes it), and the
    /// union of its statements' flags. As [`Builder::drain`].
    fn block_of(&mut self, list: List) -> (Statement<'a>, u16) {
        let (body, flags) = self.drain(list);
        (Statement::new_block_statement(SPAN, body, &self.ast), flags)
    }

    /// The label `name`. O(length of the name): copied into the arena.
    fn label(&self, name: &str) -> LabelIdentifier<'a> {
        LabelIdentifier::new(SPAN, self.ast.allocator().alloc_str(name), &self.ast)
    }

    /// The row of a statement of `kind` that holds what has `flags`: their
    /// `HAS_FUN`, `SEAL` and `HAS_GLOBAL`, and no other flag. O(1).
    fn statement(kind: Kind, flags: u16) -> Row {
        Row { flags: flags & INHERITED, kind, aux: 0, payload: 0 }
    }

    /// The slot of statement `index` of `list` in the pool. O(1). Panics
    /// when the index is outside the list.
    fn slot(&self, list: List, index: usize) -> &Option<S<'a>> {
        assert!(index < list.len(), "statement {index} of a list of {}", list.len());
        &self.pool[list.start as usize + index]
    }

    /// The statements staged from here on belong to the next
    /// [`Builder::list`]. O(1).
    pub fn stage_mark(&self) -> Mark {
        Mark(self.staged.len() as u32)
    }

    /// One statement of the list being collected. O(1): a move of 24 bytes.
    pub fn stage(&mut self, statement: S<'a>) {
        self.staged.push(statement);
    }

    /// The statements staged since `mark`, as a list in flight. One step
    /// and one move of 24 bytes per statement.
    pub fn list(&mut self, mark: Mark) -> List {
        let start = self.pool.len() as u32;
        let len = (self.staged.len() - mark.0 as usize) as u32;
        self.pool.extend(self.staged.drain(mark.0 as usize..).map(Some));
        self.steps += u64::from(len);
        List { start, len }
    }

    /// The row of statement `index` of `list`. O(1). Panics when the
    /// statement was taken.
    pub fn row_at(&self, list: List, index: usize) -> Row {
        self.statement_at(list, index).row
    }

    /// The row of the last statement of `list`: what "ends in `return`"
    /// reads (J-S3, rule 6). O(1).
    pub fn last_row(&self, list: List) -> Option<Row> {
        (!list.is_empty()).then(|| self.row_at(list, list.len() - 1))
    }

    /// Statement `index` of `list`, by reference: the statement stays in
    /// the list, and no other statement of it is read. It is what the
    /// lowering's `JsStmt::with_stmt_at` gives its reader on the builder.
    /// O(1): one indexed read of the pool; counts no step. Panics when the
    /// statement was taken.
    pub fn statement_at(&self, list: List, index: usize) -> &S<'a> {
        self.slot(list, index).as_ref().expect("a statement taken twice")
    }

    /// Take statement `index` out of `list`. O(1): a move of 24 bytes.
    /// Panics when it was taken before.
    pub fn take(&mut self, list: List, index: usize) -> S<'a> {
        assert!(index < list.len(), "statement {index} of a list of {}", list.len());
        self.pool[list.start as usize + index].take().expect("a statement taken twice")
    }

    /// The statements of `list` as the body of a program or a function,
    /// consuming the list. One step per statement.
    pub fn statements_of(&mut self, list: List) -> ArenaVec<'a, Statement<'a>> {
        self.drain(list).0
    }

    /// The expression statement `value;`, as given (J-S1 is a rule). O(1).
    pub fn exp(&mut self, value: J<'a>) -> S<'a> {
        let row = Self::statement(Kind::Exp, value.row.flags);
        let stmt = Statement::new_expression_statement(SPAN, value.expr, &self.ast);
        self.attach_statement(stmt, row)
    }

    /// `return value;`. The value is always written: a unit function's
    /// final `return` is dropped by the seal. O(1).
    pub fn return_(&mut self, value: J<'a>) -> S<'a> {
        let row = Self::statement(Kind::Return, value.row.flags);
        let stmt = Statement::new_return_statement(SPAN, Some(value.expr), &self.ast);
        self.attach_statement(stmt, row)
    }

    /// `throw value;`. O(1).
    pub fn throw(&mut self, value: J<'a>) -> S<'a> {
        let row = Self::statement(Kind::Throw, value.row.flags);
        let stmt = Statement::new_throw_statement(SPAN, value.expr, &self.ast);
        self.attach_statement(stmt, row)
    }

    /// `let variable = value;`, the binder printed through the name table
    /// (the symbol id is the variable's index). `kind` is the `aux` of a
    /// `Declare`: the `LetKind` in its low two bits and the `UsedStats`
    /// above them ([`Builder::status`]). Whether the declaration prints,
    /// and as what, is the seal's. O(1).
    pub fn declare(&mut self, variable: u32, kind: u8, value: Option<J<'a>>) -> S<'a> {
        let flags = value.as_ref().map_or(0, |value| value.row.flags);
        if let Some(value) = &value {
            if value.row.kind == Kind::Var {
                // The id `attach_statement` gives this declaration.
                self.aliases.push((self.rows.len() as u32, value.row.payload));
            }
        }
        let row = Row { aux: kind, payload: variable, ..Self::statement(Kind::Declare, flags) };
        let binder = BindingIdentifier::new_with_symbol_id(
            SPAN,
            "",
            SymbolId::from_usize(variable as usize),
            &self.ast,
        );
        let declarator = VariableDeclarator::new(
            SPAN,
            BindingPattern::BindingIdentifier(oxc_allocator::Box::new_in(binder, &self.ast)),
            None,
            value.map(|value| value.expr),
            false,
            &self.ast,
        );
        let mut declarations = ArenaVec::with_capacity_in(1, &self.ast);
        declarations.push(declarator);
        let stmt = Statement::new_variable_declaration(
            SPAN,
            VariableDeclarationKind::Let,
            declarations,
            false,
            &self.ast,
        );
        self.attach_statement(stmt, row)
    }

    /// `if (test) { then } else { otherwise }`, as given (J-S3 is a rule):
    /// both blocks are written, an empty one too. One step per statement
    /// of the two lists.
    pub fn if_(&mut self, test: J<'a>, then: List, otherwise: List) -> S<'a> {
        let (consequent, then_flags) = self.block_of(then);
        let (alternate, otherwise_flags) = self.block_of(otherwise);
        let row = Self::statement(Kind::If, test.row.flags | then_flags | otherwise_flags);
        let stmt =
            Statement::new_if_statement(SPAN, test.expr, consequent, Some(alternate), &self.ast);
        self.attach_statement(stmt, row)
    }

    /// The block statement `{ list }`. One step per statement.
    pub fn block(&mut self, list: List) -> S<'a> {
        let (stmt, flags) = self.block_of(list);
        self.attach_statement(stmt, Self::statement(Kind::Block, flags))
    }

    /// `while (test) { body }`, under `label` when given. One step per
    /// statement of the body.
    pub fn while_(&mut self, label: Option<&str>, test: J<'a>, body: List) -> S<'a> {
        let (body, body_flags) = self.block_of(body);
        let row = Self::statement(Kind::While, test.row.flags | body_flags);
        let mut stmt = Statement::new_while_statement(SPAN, test.expr, body, &self.ast);
        if let Some(label) = label {
            stmt = Statement::new_labeled_statement(SPAN, self.label(label), stmt, &self.ast);
        }
        self.attach_statement(stmt, row)
    }

    /// `break;` or `break label;`. O(length of the label).
    pub fn break_(&mut self, label: Option<&str>) -> S<'a> {
        let label = label.map(|label| self.label(label));
        let stmt = Statement::new_break_statement(SPAN, label, &self.ast);
        self.attach_statement(stmt, Self::statement(Kind::Break, 0))
    }

    /// `continue;` or `continue label;`. O(length of the label).
    pub fn continue_(&mut self, label: Option<&str>) -> S<'a> {
        let label = label.map(|label| self.label(label));
        let stmt = Statement::new_continue_statement(SPAN, label, &self.ast);
        self.attach_statement(stmt, Self::statement(Kind::Continue, 0))
    }

    /// `debugger;`. O(1).
    pub fn debugger(&mut self) -> S<'a> {
        let stmt = Statement::new_debugger_statement(SPAN, &self.ast);
        self.attach_statement(stmt, Self::statement(Kind::Debugger, 0))
    }
}

/// What the lowering's export fold reads and edits where its rows are
/// (THREE_TREES 11.4, "T6x-e and T6x-f: the fold reads where its rows
/// are"): the statements of a block the caller holds, the references to a
/// variable in a statement, and the alias of a declaration.
///
/// A statement inside a block is the node alone: its row is in the table
/// ([`Builder::statement_row`]). So the read by reference gives the node,
/// and the lowering's `JsStmt::with_block_stmt`, which lends a statement
/// handle, needs a handle that is the node (T6v, decision 3 there).
impl<'a> Builder<'a> {
    /// The statements of the block statement `block`. O(1). Panics on a
    /// statement that is not a block.
    fn body<'s>(block: &'s S<'a>) -> &'s ArenaVec<'a, Statement<'a>> {
        let Statement::BlockStatement(node) = &block.stmt else { panic!("not a block statement") };
        &node.body
    }

    /// [`Builder::body`], to be changed. O(1).
    fn body_mut<'s>(block: &'s mut S<'a>) -> &'s mut ArenaVec<'a, Statement<'a>> {
        let Statement::BlockStatement(node) = &mut block.stmt else { panic!("not a block statement") };
        &mut node.body
    }

    /// The number of statements of the block statement `block`, a hole
    /// counted (the lowering's `JsStmt::block_len`). O(1); counts no step.
    pub fn block_len(&self, block: &S<'a>) -> usize {
        Self::body(block).len()
    }

    /// Statement `index` of the block statement `block`, read where it is
    /// (the lowering's `JsStmt::with_block_stmt`): the node by reference;
    /// its row is [`Builder::statement_row`] of it. O(1): one indexed
    /// read; counts no step. Panics on an index outside the block and on a
    /// hole.
    pub fn block_statement<'s>(&self, block: &'s S<'a>, index: usize) -> &'s Statement<'a> {
        let statement = &Self::body(block)[index];
        assert!(!matches!(statement, Statement::EmptyStatement(_)), "a statement taken out of its block");
        statement
    }

    /// Statement `index` of the block statement `block`, lent to be
    /// changed where it is (the lowering's `JsStmt::lend_block_stmt`).
    /// O(1); counts no step. Panics as [`Builder::block_statement`] does.
    pub fn block_statement_mut<'s>(&mut self, block: &'s mut S<'a>, index: usize) -> &'s mut Statement<'a> {
        let statement = &mut Self::body_mut(block)[index];
        assert!(!matches!(statement, Statement::EmptyStatement(_)), "a statement taken out of its block");
        statement
    }

    /// Statement `index` of the block statement `block` moved out (the
    /// lowering's `JsStmt::take_block_stmt`). The slot keeps a hole: an
    /// empty statement, which no constructor of the builder makes, so the
    /// statements after it keep their indexes and a hole is told from a
    /// statement. A block with a hole is read by the functions of this
    /// block and released; it is not given to a list, so the hole is never
    /// printed. One step; O(1): a move of 16 bytes and one node of the
    /// arena for the hole. Panics on an index outside the block and on a
    /// hole.
    pub fn take_from_block(&mut self, block: &mut S<'a>, index: usize) -> S<'a> {
        let hole = Statement::new_empty_statement(SPAN, &self.ast);
        let slot = &mut Self::body_mut(block)[index];
        assert!(!matches!(slot, Statement::EmptyStatement(_)), "a statement taken out of its block");
        let stmt = std::mem::replace(slot, hole);
        self.steps += 1;
        let row = self.statement_row(&stmt);
        S { stmt, row }
    }

    /// The variable the declaration with the id `id` binds its own to,
    /// when its initialiser is a reference (the lowering's
    /// `JsStmt::alias_at`). The id is a key: the node is not found. A
    /// binary search among the declarations whose initialiser is a
    /// reference: O(log of their number); counts no step.
    pub fn alias_at(&self, id: u32) -> Option<u32> {
        let at = self.aliases.binary_search_by_key(&id, |&(declaration, _)| declaration).ok()?;
        Some(self.aliases[at].1)
    }

    /// Record that the initialiser of the declaration `id` is now `value`:
    /// what [`Builder::substitute`] does when it replaces one. O(log of
    /// the alias declarations), and the entries after it moved when the
    /// declaration stops being an alias.
    fn realias(&mut self, id: u32, value: Row) {
        let Ok(at) = self.aliases.binary_search_by_key(&id, |&(declaration, _)| declaration) else {
            return;
        };
        if value.kind == Kind::Var {
            self.aliases[at].1 = value.payload;
        } else {
            self.aliases.remove(at);
        }
    }

    /// Replace references to `variable` inside the statement `statement`,
    /// which the caller holds, each by what `make` gives: at most `uses`,
    /// and the walk stops at the last (the lowering's
    /// `JsStmt::substitute`). Returns the number replaced. A reference is
    /// a `Var` node of exactly that variable; what replaces it is not
    /// entered. The statement stays where it is and keeps its id. The rows
    /// of the nodes above a replaced reference are not written again: the
    /// lowering replaces a strictly pure reference by a strictly pure
    /// expression after the last rule that reads them ran, and neither
    /// has `HAS_FUN` or `SEAL`.
    ///
    /// One step per node the walk reads, until the last reference
    /// replaced: O(nodes of the statement). The work stack is one vector
    /// of the call (its references borrow the statement, so the builder
    /// cannot keep it): one allocation a call that has a use to replace,
    /// none per node. Panics on a node no constructor of the builder
    /// makes: the slice that adds a constructor adds its arm.
    pub fn substitute(
        &mut self,
        statement: &mut S<'a>,
        variable: u32,
        uses: u32,
        mut make: impl FnMut(&mut Self) -> J<'a>,
    ) -> u32 {
        let mut replaced = 0;
        if uses == 0 {
            return replaced;
        }
        let mut work = vec![Pending::Statement(&mut statement.stmt)];
        while let Some(pending) = work.pop() {
            self.steps += 1;
            let expr = match pending {
                Pending::Statement(statement) => {
                    let id = statement.node_id().index() as u32;
                    match statement {
                        Statement::ExpressionStatement(node) => work.push(Pending::Expression(&mut node.expression)),
                        Statement::ReturnStatement(node) => {
                            work.extend(node.argument.as_mut().map(Pending::Expression))
                        }
                        Statement::ThrowStatement(node) => work.push(Pending::Expression(&mut node.argument)),
                        Statement::VariableDeclaration(node) => {
                            for declarator in node.declarations.iter_mut() {
                                let Some(init) = &mut declarator.init else { continue };
                                // The initialiser itself: the alias table
                                // names this declaration.
                                if self.is_reference(init, variable) {
                                    let copy = make(self);
                                    self.realias(id, copy.row);
                                    *init = copy.expr;
                                    replaced += 1;
                                } else {
                                    work.push(Pending::Expression(init));
                                }
                            }
                        }
                        Statement::IfStatement(node) => {
                            let node = &mut **node;
                            work.push(Pending::Expression(&mut node.test));
                            work.push(Pending::Statement(&mut node.consequent));
                            work.extend(node.alternate.as_mut().map(Pending::Statement));
                        }
                        Statement::BlockStatement(node) => work.extend(node.body.iter_mut().map(Pending::Statement)),
                        Statement::WhileStatement(node) => {
                            let node = &mut **node;
                            work.push(Pending::Expression(&mut node.test));
                            work.push(Pending::Statement(&mut node.body));
                        }
                        Statement::LabeledStatement(node) => work.push(Pending::Statement(&mut node.body)),
                        Statement::BreakStatement(_)
                        | Statement::ContinueStatement(_)
                        | Statement::DebuggerStatement(_)
                        | Statement::EmptyStatement(_) => {}
                        _ => unreachable!("a statement no constructor of the builder makes"),
                    }
                    if replaced == uses {
                        break;
                    }
                    continue;
                }
                Pending::Expression(expr) => expr,
            };
            if self.is_reference(expr, variable) {
                *expr = make(self).expr;
                replaced += 1;
                if replaced == uses {
                    break;
                }
                continue;
            }
            match expr {
                Expression::UnaryExpression(node) => work.push(Pending::Expression(&mut node.argument)),
                Expression::BinaryExpression(node) => {
                    let node = &mut **node;
                    work.push(Pending::Expression(&mut node.left));
                    work.push(Pending::Expression(&mut node.right));
                }
                Expression::LogicalExpression(node) => {
                    let node = &mut **node;
                    work.push(Pending::Expression(&mut node.left));
                    work.push(Pending::Expression(&mut node.right));
                }
                Expression::ConditionalExpression(node) => {
                    let node = &mut **node;
                    work.push(Pending::Expression(&mut node.test));
                    work.push(Pending::Expression(&mut node.consequent));
                    work.push(Pending::Expression(&mut node.alternate));
                }
                Expression::SequenceExpression(node) => {
                    work.extend(node.expressions.iter_mut().map(Pending::Expression))
                }
                Expression::StaticMemberExpression(node) => work.push(Pending::Expression(&mut node.object)),
                Expression::ComputedMemberExpression(node) => {
                    let node = &mut **node;
                    work.push(Pending::Expression(&mut node.object));
                    work.push(Pending::Expression(&mut node.expression));
                }
                Expression::AssignmentExpression(node) => {
                    let node = &mut **node;
                    match &mut node.left {
                        AssignmentTarget::StaticMemberExpression(target) => {
                            work.push(Pending::Expression(&mut target.object))
                        }
                        AssignmentTarget::ComputedMemberExpression(target) => {
                            let target = &mut **target;
                            work.push(Pending::Expression(&mut target.object));
                            work.push(Pending::Expression(&mut target.expression));
                        }
                        // The target of an assignment is not a reference
                        // the lowering replaces: a moved variable is never
                        // assigned.
                        AssignmentTarget::AssignmentTargetIdentifier(_) => {}
                        _ => unreachable!("an assignment target no constructor of the builder makes"),
                    }
                    work.push(Pending::Expression(&mut node.right));
                }
                Expression::CallExpression(node) => {
                    let node = &mut **node;
                    work.push(Pending::Expression(&mut node.callee));
                    work.extend(node.arguments.iter_mut().map(|argument| {
                        Pending::Expression(argument.as_expression_mut().expect("an argument that is an expression"))
                    }));
                }
                Expression::NewExpression(node) => {
                    let node = &mut **node;
                    work.push(Pending::Expression(&mut node.callee));
                    work.extend(node.arguments.iter_mut().map(|argument| {
                        Pending::Expression(argument.as_expression_mut().expect("an argument that is an expression"))
                    }));
                }
                Expression::Identifier(_)
                | Expression::NullLiteral(_)
                | Expression::BooleanLiteral(_)
                | Expression::StringLiteral(_)
                | Expression::NumericLiteral(_)
                | Expression::BigIntLiteral(_) => {}
                _ => unreachable!("an expression no constructor of the builder makes"),
            }
        }
        replaced
    }

    /// The operands of `expr`, pushed on `out` in order: what a walk that
    /// reads an expression enters. Nothing for a leaf. O(arity). Panics on
    /// a node no constructor of the builder makes: the slice that adds a
    /// constructor adds its arm.
    fn operands_into<'s>(expr: &'s Expression<'a>, out: &mut Vec<&'s Expression<'a>>) {
        match expr {
            Expression::UnaryExpression(node) => out.push(&node.argument),
            Expression::BinaryExpression(node) => out.extend([&node.left, &node.right]),
            Expression::LogicalExpression(node) => out.extend([&node.left, &node.right]),
            Expression::ConditionalExpression(node) => {
                out.extend([&node.test, &node.consequent, &node.alternate])
            }
            Expression::SequenceExpression(node) => out.extend(node.expressions.iter()),
            Expression::StaticMemberExpression(node) => out.push(&node.object),
            Expression::ComputedMemberExpression(node) => out.extend([&node.object, &node.expression]),
            Expression::AssignmentExpression(node) => {
                match &node.left {
                    AssignmentTarget::StaticMemberExpression(target) => out.push(&target.object),
                    AssignmentTarget::ComputedMemberExpression(target) => {
                        out.extend([&target.object, &target.expression])
                    }
                    AssignmentTarget::AssignmentTargetIdentifier(_) => {}
                    _ => unreachable!("an assignment target no constructor of the builder makes"),
                }
                out.push(&node.right);
            }
            Expression::CallExpression(node) => {
                out.push(&node.callee);
                out.extend(node.arguments.iter().map(|argument| {
                    argument.as_expression().expect("an argument that is an expression")
                }));
            }
            Expression::NewExpression(node) => {
                out.push(&node.callee);
                out.extend(node.arguments.iter().map(|argument| {
                    argument.as_expression().expect("an argument that is an expression")
                }));
            }
            Expression::Identifier(_)
            | Expression::NullLiteral(_)
            | Expression::BooleanLiteral(_)
            | Expression::StringLiteral(_)
            | Expression::NumericLiteral(_)
            | Expression::BigIntLiteral(_) => {}
            _ => unreachable!("an expression no constructor of the builder makes"),
        }
    }

    /// Every reference and every function literal at or below `e`, each
    /// given to `visit` once with the builder, to read a row by id (the
    /// lowering's `Js::references`); a function literal is not entered. `e` is the caller's and is not changed.
    /// Returns the number of nodes read. One read per node at or below `e`
    /// outside function literals, a node of a printed form without a row
    /// of its own (the operand of a negative literal) counted: O(nodes);
    /// counts no step. The work stack is the builder's kept storage
    /// ([`recycle`]): nothing is allocated once it has held an expression
    /// as wide and as deep.
    pub fn references(&mut self, e: &J<'a>, mut visit: impl FnMut(&Self, Reference)) -> u32 {
        let mut work: Vec<&Expression<'a>> = recycle(std::mem::take(&mut self.spare));
        let mut read = 0;
        work.push(&e.expr);
        while let Some(expr) = work.pop() {
            read += 1;
            let id = expr.node_id().index() as u32;
            let row = self.rows[id as usize];
            match row.kind {
                Kind::Var => visit(self, Reference::Var { variable: row.payload, id }),
                Kind::Named => visit(self, Reference::Named { id }),
                Kind::Fun => visit(self, Reference::Function(row.payload)),
                _ => Self::operands_into(expr, &mut work),
            }
        }
        self.spare = recycle(work);
        read
    }

    /// The calls the `return` that is statement `index` of `list` ends in
    /// once the flatten pass has split its value (the lowering's
    /// `JsStmt::return_calls`): both branches of a conditional, the last
    /// operand of a sequence, a call whose callee is a reference to a
    /// variable. `visit` is given the variable and the `node_id` of the
    /// call, a then-branch before its else-branch; `last` says the
    /// `return` ends its list, and a call that is the whole value or the
    /// end of a sequence that is, is given only then. Returns the number
    /// of nodes read: one per conditional and sequence between the value
    /// and its calls and one per node they end in; a test, the head of a
    /// sequence and the arguments of a call are not read. Counts no step.
    /// The work stack is the builder's kept storage ([`recycle`]): nothing
    /// is allocated once it has held a value whose conditionals nest as
    /// deep. Panics on a statement that is not a `return`, and on one
    /// taken out of the list.
    pub fn return_calls(&mut self, list: List, index: usize, last: bool, mut visit: impl FnMut(u32, u32)) -> u32 {
        let mut work: Vec<&Expression<'a>> = recycle(std::mem::take(&mut self.spare));
        let Statement::ReturnStatement(statement) = &self.statement_at(list, index).stmt else {
            panic!("not a return statement")
        };
        let mut read = 0;
        let mut expr = statement.argument.as_ref().expect("a return with its value");
        let mut site = last;
        loop {
            read += 1;
            match (self.row(expr).kind, expr) {
                (Kind::Cond, Expression::ConditionalExpression(node)) => {
                    work.push(&node.alternate);
                    work.push(&node.consequent);
                }
                (Kind::Seq, Expression::SequenceExpression(node)) => {
                    expr = node.expressions.last().expect("a sequence of two");
                    continue;
                }
                (Kind::Call, Expression::CallExpression(node)) if site => {
                    let callee = self.row(&node.callee);
                    if callee.kind == Kind::Var {
                        visit(callee.payload, expr.node_id().index() as u32);
                    }
                }
                _ => {}
            }
            let Some(next) = work.pop() else { break };
            expr = next;
            site = true;
        }
        self.spare = recycle(work);
        read
    }

    /// Whether `expr` is a reference to `variable`: a `Var` row of that
    /// variable. O(1): the node's `node_id` and its row.
    fn is_reference(&self, expr: &Expression<'a>, variable: u32) -> bool {
        let row = self.row(expr);
        row.kind == Kind::Var && row.payload == variable
    }
}

/// What the lowering's naming replay reads of a statement and takes out
/// of it (THREE_TREES 11.4, "T6r: the naming replay behind the
/// interface", decisions 1, 2, 7 and 12 to 16; slice T6r-c).
///
/// The readers of a statement in hand answer from its row alone
/// ([`S::row`]): a constructor writes the row as [`Kind`] says for its
/// kind, and the builder has no constructor yet for a loop over a range or
/// an iterable, a `try`, a `switch` and a rest declaration (T6d adds
/// them, each with the row these readers read).
impl<'a> Builder<'a> {
    /// The variable the statement binds (the lowering's `JsStmt::binder`):
    /// the payload of a `Declare`, a `Rest`, a `ForRange`, a `ForOf` and a
    /// `ForAwaitOf`; the exception variable of a `Try` that has a handler
    /// (its payload less one). `None` for every other statement. O(1): the
    /// row in the handle, no node; counts no step.
    pub fn binder(&self, statement: &S<'a>) -> Option<u32> {
        let row = statement.row;
        match row.kind {
            Kind::Declare | Kind::Rest | Kind::ForRange | Kind::ForOf | Kind::ForAwaitOf => Some(row.payload),
            Kind::Try => row.payload.checked_sub(1),
            _ => None,
        }
    }

    /// The status of a `Declare` or a `Rest` (the lowering's
    /// `JsStmt::status`): the bits of the row's `aux` above the two of the
    /// `LetKind`. O(1): the row in the handle; counts no step. Panics on a
    /// statement that is neither.
    pub fn status(&self, statement: &S<'a>) -> u8 {
        let row = statement.row;
        assert!(matches!(row.kind, Kind::Declare | Kind::Rest), "not a declaration");
        row.aux >> 2
    }

    /// Of a range loop, the variable it runs over and the kind of its
    /// bound (the lowering's `JsStmt::range_of`): of a `ForRange` the
    /// payload, of a `ForRangeExisting` the payload less one (`None` when
    /// its target is no reference), with the kind whose number the row's
    /// `aux` holds. `None` for every other statement. O(1): the row in the
    /// handle; counts no step.
    pub fn range_of(&self, statement: &S<'a>) -> Option<(Option<u32>, Kind)> {
        let row = statement.row;
        let variable = match row.kind {
            Kind::ForRange => Some(row.payload),
            Kind::ForRangeExisting => row.payload.checked_sub(1),
            _ => return None,
        };
        Some((variable, Kind::ALL[row.aux as usize]))
    }

    /// The number of statement lists the statement holds (the lowering's
    /// `JsStmt::bodies`): one for a block and a `while`, labelled or not;
    /// one or two for an `if` (the builder writes both blocks, so two);
    /// none for a statement without a list. O(1): the node and, for a
    /// labelled statement, the node below the label; counts no step.
    /// Panics on a statement no constructor of the builder makes: the
    /// slice that adds a constructor adds its arm.
    pub fn bodies(&self, statement: &S<'a>) -> u32 {
        let mut stmt = &statement.stmt;
        if let Statement::LabeledStatement(node) = stmt {
            stmt = &node.body;
        }
        match stmt {
            Statement::BlockStatement(_) | Statement::WhileStatement(_) => 1,
            Statement::IfStatement(node) => 1 + u32::from(node.alternate.is_some()),
            Statement::ExpressionStatement(_)
            | Statement::ReturnStatement(_)
            | Statement::ThrowStatement(_)
            | Statement::VariableDeclaration(_)
            | Statement::BreakStatement(_)
            | Statement::ContinueStatement(_)
            | Statement::DebuggerStatement(_) => 0,
            _ => unreachable!("a statement no constructor of the builder makes"),
        }
    }

    /// The statements of list `index` of the statement `stmt`
    /// ([`Builder::bodies`]), in the node that holds them. O(1). Panics
    /// when the statement has no such list.
    fn list_of<'s>(stmt: &'s mut Statement<'a>, index: usize) -> &'s mut ArenaVec<'a, Statement<'a>> {
        let mut stmt = stmt;
        if let Statement::LabeledStatement(node) = stmt {
            stmt = &mut node.body;
        }
        let block = match (stmt, index) {
            (block @ Statement::BlockStatement(_), 0) => Some(block),
            (Statement::IfStatement(node), 0) => Some(&mut node.consequent),
            (Statement::IfStatement(node), 1) => node.alternate.as_mut(),
            (Statement::WhileStatement(node), 0) => Some(&mut node.body),
            _ => None,
        };
        match block {
            Some(Statement::BlockStatement(node)) => &mut node.body,
            _ => panic!("statement list {index} of a statement that has no such list"),
        }
    }

    /// List `index` of the statement `statement` taken out of it as a
    /// list in flight (the lowering's `JsStmt::body`): its statements are
    /// moved from the node into the pool, each with its row from the
    /// table, and the node keeps an empty vector with its capacity, which
    /// [`Builder::set_body`] fills again. One step, and one step and one
    /// move of 16 bytes per statement: the builder keeps a compound
    /// statement as a node (T6b). The statements are appended to the pool
    /// of lists in flight, which is cleared a unit and not before: a list
    /// taken k times in a unit leaves k times its length there, and the
    /// pool allocates when it grows. Panics when the statement has no
    /// such list. (Named
    /// `take_body`: `Builder::body` is the reader of a block's statements.)
    pub fn take_body(&mut self, statement: &mut S<'a>, index: usize) -> List {
        let Self { rows, pool, .. } = self;
        let body = Self::list_of(&mut statement.stmt, index);
        let (start, len) = (pool.len() as u32, body.len() as u32);
        pool.extend(body.drain(..).map(|stmt| {
            let row = rows[stmt.node_id().index()];
            Some(S { stmt, row })
        }));
        self.steps += 1 + u64::from(len);
        List { start, len }
    }

    /// `list` becomes list `index` of the statement `statement`, in place
    /// of the one [`Builder::take_body`] took (the lowering's
    /// `JsStmt::set_body`); the list is consumed. The statements are moved
    /// into the vector the taken ones came from: nothing is allocated in
    /// the arena when the list is no longer than that one. The row of
    /// `statement` is not written again. One step, and one step and one
    /// move of 24 bytes per statement. Panics when the statement has no
    /// such list, when that list was not taken, and on a statement of
    /// `list` taken before.
    pub fn set_body(&mut self, statement: &mut S<'a>, index: usize, list: List) {
        let body = Self::list_of(&mut statement.stmt, index);
        assert!(body.is_empty(), "a statement list put back that was not taken");
        let start = list.start as usize;
        body.extend(self.pool[start..start + list.len()].iter_mut().map(|slot| slot.take().expect("a statement taken twice").stmt));
        self.steps += 1 + list.len() as u64;
    }
}

#[cfg(test)]
#[path = "builder_tests.rs"]
mod tests;
