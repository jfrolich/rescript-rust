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
//! `HAS_FUN` and `SEAL` hold for a node, and for a statement, when they hold
//! for anything it is built from. `SEAL` is set where it starts: by
//! [`Builder::bin`] for `&&`, `||` and `|` whose right operand is a `Bin` of
//! the same operator, and by [`Builder::seq`] when an operand is a `Seq`.
//! A statement's row has no other flag.
use super::{Unsupported, literal};
use crate::js_ir::op::{BinOp, Number};
use crate::js_ir::printer::normalize_float_literal_for_js;
use oxc_allocator::{Allocator, GetAllocator, Vec as ArenaVec};
use oxc_ast::{ast::*, builder::AstBuilder};
use oxc_span::SPAN;
use oxc_syntax::{
    node::NodeId,
    number::{BigintBase, NumberBase},
    operator::UnaryOperator,
    reference::ReferenceId,
};

/// The five facts a literal has (`Number`, `Str`).
const LITERAL: u16 = flag::PURE | flag::STRICT | flag::DELAY_SAFE | flag::SUBEXPR | flag::DUPLICABLE;

/// [`Row::payload`] of a float literal whose text is `0.`: the one float
/// `0 - x` prints as `-x` for (`walk::negation_form`, OCaml
/// `compiler/core/js_dump.ml`, `Bin (Minus, Number (Float {f = "0."}), e)`).
/// The text is not in the row otherwise; every other float has payload 0.
const FLOAT_ZERO_TEXT: u32 = 1;

/// The facts of one node, as bits of [`Row::flags`].
pub(crate) mod flag {
    /// B:102 `expression_has_no_side_effects`.
    pub const PURE: u16 = 1 << 0;
    /// E:15 `js_expr_no_side_effects`.
    pub const STRICT: u16 = 1 << 1;
    /// A:28 `delay_safe`.
    pub const DELAY_SAFE: u16 = 1 << 2;
    /// E:146 `is_pure_subexpression`.
    pub const SUBEXPR: u16 = 1 << 3;
    /// X:60 `duplicable`.
    pub const DUPLICABLE: u16 = 1 << 4;
    /// A function literal is at or below this node.
    pub const HAS_FUN: u16 = 1 << 5;
    /// The seal has work at or below this node: a logical or `|` chain or a
    /// sequence that is not in print form, or a function literal whose body
    /// the flatten rules change.
    pub const SEAL: u16 = 1 << 6;
}

/// What the caller knows of a variable when it builds a reference to it.
pub(crate) mod var {
    /// The variable is assigned after its declaration.
    pub const ASSIGNED: u8 = 1 << 0;
    /// A JavaScript global.
    pub const GLOBAL: u8 = 1 << 1;
}

/// [`Row::aux`] of a [`Kind::Number`].
pub(crate) mod num {
    /// Class, in the low two bits.
    pub const INT: u8 = 0;
    pub const FLOAT: u8 = 1;
    pub const BIGINT: u8 = 2;
    pub const CLASS: u8 = 3;
    /// An integer that is not zero; a bigint whose digits are not `0`.
    pub const NONZERO: u8 = 1 << 2;
    /// A bigint with the positive sign.
    pub const POSITIVE: u8 = 1 << 3;
}

/// The J-level kind of a node: what the lowering built, which the oxc node
/// alone does not say (a length is a member, a string append is a `+`).
#[repr(u8)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Kind {
    /// A reference to a variable; `payload` is the variable's index, `aux`
    /// what the caller knew of it ([`var`]).
    Var,
    /// An identifier printed as written; `aux` is 1 for a JavaScript
    /// identifier.
    Named,
    /// `aux` is of [`num`]; `payload` is an integer's value.
    Number,
    Str,
    /// `aux` is the value.
    Bool,
    Null,
    /// `aux` is 1 for the unit value.
    Undefined,
    /// `aux` is the `BinOp`.
    Bin,
    Not,
    Bnot,
    Typeof,
    In,
    Cond,
    Seq,
    /// `payload` is the call information of the lowering.
    Call,
    New,
    Index,
    /// `payload` is the field position plus one, 0 for none; `aux` is 1 for
    /// the tag of a block.
    Dot,
    Length,
    IsNullish,
    StrAppend,
    /// Statements (T6b). An expression statement.
    Exp,
    Return,
    Throw,
    /// `payload` is the variable's index; `aux` is the `LetKind`.
    Declare,
    If,
    Block,
    While,
    Break,
    Continue,
    Debugger,
}

impl Kind {
    /// Every kind, in the order of its number.
    pub const ALL: [Kind; 31] = [
        Kind::Var,
        Kind::Named,
        Kind::Number,
        Kind::Str,
        Kind::Bool,
        Kind::Null,
        Kind::Undefined,
        Kind::Bin,
        Kind::Not,
        Kind::Bnot,
        Kind::Typeof,
        Kind::In,
        Kind::Cond,
        Kind::Seq,
        Kind::Call,
        Kind::New,
        Kind::Index,
        Kind::Dot,
        Kind::Length,
        Kind::IsNullish,
        Kind::StrAppend,
        Kind::Exp,
        Kind::Return,
        Kind::Throw,
        Kind::Declare,
        Kind::If,
        Kind::Block,
        Kind::While,
        Kind::Break,
        Kind::Continue,
        Kind::Debugger,
    ];
}

/// The facts of one node. 8 bytes: one per node in [`Builder::rows`], and
/// the same value travels in the handle.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Row {
    pub flags: u16,
    pub kind: Kind,
    pub aux: u8,
    pub payload: u32,
}

impl Row {
    /// O(1).
    pub fn has(self, flags: u16) -> bool {
        self.flags & flags == flags
    }
    /// O(1): the value of an integer literal.
    pub fn int(self) -> Option<i32> {
        (self.kind == Kind::Number && self.aux & num::CLASS == num::INT)
            .then_some(self.payload as i32)
    }
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

    /// A reference to variable `var`, printed through the name table (the
    /// reference id is the variable's index). `known` is of [`var`]. O(1).
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
                let literal =
                    Expression::new_big_int_literal(SPAN, digits, None, BigintBase::Decimal, &self.ast);
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
                let value = normalize_float_literal_for_js(&f.f)
                    .parse::<f64>()
                    .map_err(|_| Unsupported("float literal"))?;
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
        let _inputs = value;
        todo!("T6a")
    }

    /// `~value`. O(1).
    pub fn bnot(&mut self, value: J<'a>) -> J<'a> {
        let _inputs = value;
        todo!("T6a")
    }

    /// `typeof value`. O(1).
    pub fn typeof_(&mut self, value: J<'a>) -> J<'a> {
        let _inputs = value;
        todo!("T6a")
    }

    /// The nullish test, printed `value == null` (A.7). O(1).
    pub fn is_nullish(&mut self, value: J<'a>) -> J<'a> {
        let _inputs = value;
        todo!("T6a")
    }

    /// `left in right`. O(1).
    pub fn in_(&mut self, left: J<'a>, right: J<'a>) -> J<'a> {
        let _inputs = (left, right);
        todo!("T6a")
    }

    /// The string concatenation `left + right`, as given (J-E1 is a rule).
    /// O(1).
    pub fn str_append(&mut self, left: J<'a>, right: J<'a>) -> J<'a> {
        let _inputs = (left, right);
        todo!("T6a")
    }

    /// The binary operation as given (J-E4 is a rule, not this constructor),
    /// with the printer's decisions of A.7 that depend on the node alone:
    /// `0 - x` is `-x`; `x === null || x === undefined` on one variable is
    /// `x == null`; `=` is an assignment. A logical or `|` chain whose right
    /// operand is a chain of the same operator is marked for the seal, which
    /// writes it in print form. O(1).
    pub fn bin(&mut self, op: BinOp, left: J<'a>, right: J<'a>) -> Result<J<'a>, Unsupported> {
        let _inputs = (op, left, right);
        todo!("T6a")
    }

    /// `test ? then : otherwise`, as given (J-E7 is a rule). O(1).
    pub fn cond(&mut self, test: J<'a>, then: J<'a>, otherwise: J<'a>) -> J<'a> {
        let _inputs = (test, then, otherwise);
        todo!("T6a")
    }

    /// `first, second`, as given (J-M1 is a rule): a sequence of two. A
    /// sequence with a sequence as operand is marked for the seal, which
    /// writes one flat list. O(1).
    pub fn seq(&mut self, first: J<'a>, second: J<'a>) -> J<'a> {
        let _inputs = (first, second);
        todo!("T6a")
    }

    /// `object.name`, or `object["name"]` when the name is no identifier
    /// (A.7, property access). `position` is the field's position in its
    /// block; `tag` says the read is of a block's tag. O(length of the
    /// name).
    pub fn dot(&mut self, object: J<'a>, name: &str, position: Option<u32>, tag: bool) -> J<'a> {
        let _inputs = (object, name, position, tag);
        todo!("T6a")
    }

    /// `value.length`. O(1).
    pub fn length(&mut self, value: J<'a>) -> J<'a> {
        let _inputs = value;
        todo!("T6a")
    }

    /// `object[index]`. O(1).
    pub fn index(&mut self, object: J<'a>, index: J<'a>) -> J<'a> {
        let _inputs = (object, index);
        todo!("T6a")
    }

    /// The operands pushed from here on belong to the next list
    /// constructor. O(1).
    pub fn mark(&self) -> Mark {
        Mark(self.operands.len() as u32)
    }

    /// One operand of the list being collected. O(1): a move of 24 bytes
    /// onto the builder's stack.
    pub fn push(&mut self, operand: J<'a>) {
        let _inputs = operand;
        todo!("T6a")
    }

    /// `callee(arguments since mark)`. `info` is the lowering's call
    /// information; `pure` writes the pure annotation. A call is pure only
    /// as `Array.isArray(x)` over a pure `x` (B:164). One step per
    /// argument.
    pub fn call(&mut self, callee: J<'a>, mark: Mark, info: u32, pure: bool) -> J<'a> {
        let _inputs = (callee, mark, info, pure);
        todo!("T6a")
    }

    /// `new callee(arguments since mark)`. One step per argument.
    pub fn new_(&mut self, callee: J<'a>, mark: Mark) -> J<'a> {
        let _inputs = (callee, mark);
        todo!("T6a")
    }
}

/// T6b: statements and statement lists.
impl<'a> Builder<'a> {
    /// Room for `statements` statements in lists in flight and `staged`
    /// staged ones: at most two allocations, none when the capacity is
    /// there.
    pub fn reserve_statements(&mut self, statements: usize, staged: usize) {
        let _inputs = (statements, staged);
        todo!("T6b")
    }

    /// The row of a statement that is inside a list of the tree. O(1).
    pub fn statement_row(&self, stmt: &Statement<'a>) -> Row {
        let _inputs = stmt;
        todo!("T6b")
    }

    /// The statements staged from here on belong to the next
    /// [`Builder::list`]. O(1).
    pub fn stage_mark(&self) -> Mark {
        Mark(self.staged.len() as u32)
    }

    /// One statement of the list being collected. O(1): a move of 24 bytes.
    pub fn stage(&mut self, statement: S<'a>) {
        let _inputs = statement;
        todo!("T6b")
    }

    /// The statements staged since `mark`, as a list in flight. One step
    /// and one move of 24 bytes per statement.
    pub fn list(&mut self, mark: Mark) -> List {
        let _inputs = mark;
        todo!("T6b")
    }

    /// The row of statement `index` of `list`. O(1). Panics when the
    /// statement was taken.
    pub fn row_at(&self, list: List, index: usize) -> Row {
        let _inputs = (list, index);
        todo!("T6b")
    }

    /// The row of the last statement of `list`: what "ends in `return`"
    /// reads (J-S3, rule 6). O(1).
    pub fn last_row(&self, list: List) -> Option<Row> {
        let _inputs = list;
        todo!("T6b")
    }

    /// Statement `index` of `list`, by reference. O(1).
    pub fn statement_at(&self, list: List, index: usize) -> &S<'a> {
        let _inputs = (list, index);
        todo!("T6b")
    }

    /// Take statement `index` out of `list`. O(1): a move of 24 bytes.
    /// Panics when it was taken before.
    pub fn take(&mut self, list: List, index: usize) -> S<'a> {
        let _inputs = (list, index);
        todo!("T6b")
    }

    /// The statements of `list` as the body of a program or a function,
    /// consuming the list. One step per statement.
    pub fn statements_of(&mut self, list: List) -> ArenaVec<'a, Statement<'a>> {
        let _inputs = list;
        todo!("T6b")
    }

    /// The expression statement `value;`, as given (J-S1 is a rule). O(1).
    pub fn exp(&mut self, value: J<'a>) -> S<'a> {
        let _inputs = value;
        todo!("T6b")
    }

    /// `return value;`. The value is always written: a unit function's
    /// final `return` is dropped by the seal. O(1).
    pub fn return_(&mut self, value: J<'a>) -> S<'a> {
        let _inputs = value;
        todo!("T6b")
    }

    /// `throw value;`. O(1).
    pub fn throw(&mut self, value: J<'a>) -> S<'a> {
        let _inputs = value;
        todo!("T6b")
    }

    /// `let variable = value;`, the binder printed through the name table
    /// (the symbol id is the variable's index). `kind` is the `LetKind`.
    /// Whether the declaration prints, and as what, is the seal's. O(1).
    pub fn declare(&mut self, variable: u32, kind: u8, value: Option<J<'a>>) -> S<'a> {
        let _inputs = (variable, kind, value);
        todo!("T6b")
    }

    /// `if (test) { then } else { otherwise }`, as given (J-S3 is a rule):
    /// both blocks are written, an empty one too. One step per statement
    /// of the two lists.
    pub fn if_(&mut self, test: J<'a>, then: List, otherwise: List) -> S<'a> {
        let _inputs = (test, then, otherwise);
        todo!("T6b")
    }

    /// The block statement `{ list }`. One step per statement.
    pub fn block(&mut self, list: List) -> S<'a> {
        let _inputs = list;
        todo!("T6b")
    }

    /// `while (test) { body }`, under `label` when given. One step per
    /// statement of the body.
    pub fn while_(&mut self, label: Option<&str>, test: J<'a>, body: List) -> S<'a> {
        let _inputs = (label, test, body);
        todo!("T6b")
    }

    /// `break;` or `break label;`. O(length of the label).
    pub fn break_(&mut self, label: Option<&str>) -> S<'a> {
        let _inputs = label;
        todo!("T6b")
    }

    /// `continue;` or `continue label;`. O(length of the label).
    pub fn continue_(&mut self, label: Option<&str>) -> S<'a> {
        let _inputs = label;
        todo!("T6b")
    }

    /// `debugger;`. O(1).
    pub fn debugger(&mut self) -> S<'a> {
        todo!("T6b")
    }
}

#[cfg(test)]
#[path = "builder_tests.rs"]
mod tests;
