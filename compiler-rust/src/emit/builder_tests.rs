//! Acceptance tests of the builder (THREE_TREES 11.4, "T6 design").
//!
//! The oracle form: one description of an expression ([`T`]) is built twice,
//! as legacy JS IR with the plain arena constructors (no rule runs) and
//! through the builder. The legacy printer's text, reformatted once, must be
//! the text `oxc_codegen` prints for the builder's node, and the builder's
//! facts must be what the legacy predicates compute on the legacy node. No
//! expected text is written down.
use super::*;
use crate::ident::{Ident, IdentFlags};
use crate::js_ir::arena::{Expr, ExprKind, FieldPos, JsArena};
use crate::js_ir::op::{FloatLit, LengthObject};
use crate::js_ir::CallInfo;
use js_reformat::{ReformatOptions, reformat};

/// An expression, described once.
#[derive(Clone)]
enum T {
    Named(&'static str),
    /// A JavaScript identifier (`IdentFlags::JS`).
    Js(&'static str),
    Int(i32),
    Float(&'static str),
    Str(&'static str),
    Bool(bool),
    Null,
    Undefined(bool),
    Bin(BinOp, Box<T>, Box<T>),
    Not(Box<T>),
    Bnot(Box<T>),
    Typeof(Box<T>),
    IsNullish(Box<T>),
    In(Box<T>, Box<T>),
    StrAppend(Box<T>, Box<T>),
    Cond(Box<T>, Box<T>, Box<T>),
    Seq(Box<T>, Box<T>),
    Dot(Box<T>, &'static str, Option<u32>),
    Length(Box<T>),
    Index(Box<T>, Box<T>),
    Call(Box<T>, Vec<T>),
    New(Box<T>, Vec<T>),
}

fn n(name: &'static str) -> T {
    T::Named(name)
}
fn bin(op: BinOp, l: T, r: T) -> T {
    T::Bin(op, Box::new(l), Box::new(r))
}
fn call(f: T, args: Vec<T>) -> T {
    T::Call(Box::new(f), args)
}
fn dot(o: T, name: &'static str) -> T {
    T::Dot(Box::new(o), name, None)
}

fn legacy(t: &T, a: &mut JsArena) -> Expr {
    let kind = match t {
        T::Named(name) => ExprKind::Var(a.ident_id(Ident::new(*name, 0, IdentFlags::NONE))),
        T::Js(name) => ExprKind::Var(a.ident_id(Ident::new(*name, 0, IdentFlags::JS))),
        T::Int(i) => ExprKind::Number(a.number_id(Number::int(*i))),
        T::Float(f) => ExprKind::Number(a.number_id(Number::Float(FloatLit { f: (*f).into() }))),
        T::Str(s) => ExprKind::Str(a.str(s)),
        T::Bool(b) => ExprKind::Bool(*b),
        T::Null => ExprKind::Null,
        T::Undefined(unit) => ExprKind::Undefined { is_unit: *unit },
        T::Bin(op, l, r) => ExprKind::Bin(*op, legacy(l, a), legacy(r, a)),
        T::Not(e) => ExprKind::JsNot(legacy(e, a)),
        T::Bnot(e) => ExprKind::JsBnot(legacy(e, a)),
        T::Typeof(e) => ExprKind::Typeof(legacy(e, a)),
        T::IsNullish(e) => ExprKind::IsNullOrUndefined(legacy(e, a)),
        T::In(l, r) => ExprKind::In(legacy(l, a), legacy(r, a)),
        T::StrAppend(l, r) => ExprKind::StringAppend(legacy(l, a), legacy(r, a)),
        T::Cond(c, x, y) => ExprKind::Cond(legacy(c, a), legacy(x, a), legacy(y, a)),
        T::Seq(l, r) => ExprKind::Seq(legacy(l, a), legacy(r, a)),
        T::Dot(o, name, position) => {
            let o = legacy(o, a);
            ExprKind::StaticIndex(o, a.str(name), FieldPos::new(position.map(|p| p as i32)))
        }
        T::Length(e) => ExprKind::Length(legacy(e, a), LengthObject::Array),
        T::Index(o, i) => ExprKind::ArrayIndex(legacy(o, a), legacy(i, a)),
        T::Call(f, args) => {
            let f = legacy(f, a);
            let args: Vec<Expr> = args.iter().map(|x| legacy(x, a)).collect();
            let args = a.expr_list(&args);
            ExprKind::Call(f, args, a.call_id(CallInfo::default()))
        }
        T::New(f, args) => {
            let f = legacy(f, a);
            let args: Vec<Expr> = args.iter().map(|x| legacy(x, a)).collect();
            ExprKind::New(f, Some(a.expr_list(&args)))
        }
    };
    a.expr(kind)
}

fn built<'a>(t: &T, b: &mut Builder<'a>) -> J<'a> {
    match t {
        T::Named(name) => b.named(name, false),
        T::Js(name) => b.named(name, true),
        T::Int(i) => b.int(*i),
        T::Float(f) => b.number(&Number::Float(FloatLit { f: (*f).into() })).unwrap(),
        T::Str(s) => b.string(s),
        T::Bool(v) => b.boolean(*v),
        T::Null => b.null(),
        T::Undefined(unit) => b.undefined(*unit),
        T::Bin(op, l, r) => {
            let (l, r) = (built(l, b), built(r, b));
            b.bin(*op, l, r).unwrap()
        }
        T::Not(e) => {
            let e = built(e, b);
            b.not(e)
        }
        T::Bnot(e) => {
            let e = built(e, b);
            b.bnot(e)
        }
        T::Typeof(e) => {
            let e = built(e, b);
            b.typeof_(e)
        }
        T::IsNullish(e) => {
            let e = built(e, b);
            b.is_nullish(e)
        }
        T::In(l, r) => {
            let (l, r) = (built(l, b), built(r, b));
            b.in_(l, r)
        }
        T::StrAppend(l, r) => {
            let (l, r) = (built(l, b), built(r, b));
            b.str_append(l, r)
        }
        T::Cond(c, x, y) => {
            let (c, x, y) = (built(c, b), built(x, b), built(y, b));
            b.cond(c, x, y)
        }
        T::Seq(l, r) => {
            let (l, r) = (built(l, b), built(r, b));
            b.seq(l, r)
        }
        T::Dot(o, name, position) => {
            let o = built(o, b);
            b.dot(o, name, *position, false)
        }
        T::Length(e) => {
            let e = built(e, b);
            b.length(e)
        }
        T::Index(o, i) => {
            let (o, i) = (built(o, b), built(i, b));
            b.index(o, i)
        }
        T::Call(f, args) => {
            let f = built(f, b);
            let mark = b.mark();
            for x in args {
                let x = built(x, b);
                b.push(x);
            }
            b.call(f, mark, 0, false)
        }
        T::New(f, args) => {
            let f = built(f, b);
            let mark = b.mark();
            for x in args {
                let x = built(x, b);
                b.push(x);
            }
            b.new_(f, mark)
        }
    }
}

/// `let value = <expr>;` printed by `oxc_codegen` with the emitter's options.
fn printed<'a>(b: &Builder<'a>, value: Expression<'a>) -> String {
    use super::super::build::Allocate;
    let ast = &b.ast;
    let binding = BindingIdentifier::new(SPAN, "value", ast);
    let declarator = VariableDeclarator::new(
        SPAN,
        BindingPattern::BindingIdentifier(ast.alloc(binding)),
        None,
        Some(value),
        false,
        ast,
    );
    let statement = Statement::new_variable_declaration(
        SPAN,
        VariableDeclarationKind::Let,
        ast.vec1(declarator),
        false,
        ast,
    );
    let program = Program::new(
        SPAN,
        oxc_span::SourceType::mjs(),
        "",
        ast.vec(),
        None,
        ast.vec(),
        ast.vec1(statement),
        ast,
    );
    oxc_codegen::Codegen::new()
        .with_options(super::super::program::codegen_options())
        .build(&program)
        .code
}

fn mode() -> ReformatOptions {
    ReformatOptions { drop_decoration_comments: true, ..Default::default() }
}

/// The oracle: same text as the legacy printer, same purity as the legacy
/// predicates, and a row in the table equal to the handle's.
fn oracle(t: &T) {
    let mut a = JsArena::default();
    let e = legacy(t, &mut a);
    let text = crate::js_ir::printer::print_expr_with_options(&a, e, 1, false, false);
    let expected = reformat(&format!("let value = {text};"), mode()).unwrap();
    let allocator = Allocator::default();
    let mut b = Builder::new(&allocator);
    let j = built(t, &mut b);
    assert_eq!(b.row(&j.expr), j.row, "{text}: the table row is the handle's");
    assert_eq!(
        j.row.has(flag::PURE),
        crate::js_ir::build::expression_has_no_side_effects(&a, e),
        "{text}: PURE"
    );
    assert_eq!(
        j.row.has(flag::STRICT),
        crate::lambda::js_exp_make::js_expr_no_side_effects(&a, e),
        "{text}: STRICT"
    );
    let actual = printed(&b, j.expr);
    assert_eq!(expected, actual, "{text}");
    assert_eq!(reformat(&actual, mode()).unwrap(), actual, "{text}: a fixed point");
}

#[test]
fn kinds_and_flags_are_dense_and_distinct() {
    // A kind is its position: a row's kind indexes a table without a map.
    for (index, kind) in Kind::ALL.iter().enumerate() {
        assert_eq!(*kind as usize, index);
    }
    let flags = [
        flag::PURE,
        flag::STRICT,
        flag::DELAY_SAFE,
        flag::SUBEXPR,
        flag::DUPLICABLE,
        flag::HAS_FUN,
        flag::SEAL,
    ];
    assert_eq!(flags.iter().fold(0, |all, f| all | f).count_ones() as usize, flags.len());
    assert_eq!([num::INT, num::FLOAT, num::BIGINT].map(|class| class & num::CLASS), [0, 1, 2]);
    assert_eq!((num::CLASS | num::NONZERO | num::POSITIVE).count_ones(), 4);
    assert_eq!((var::ASSIGNED | var::GLOBAL).count_ones(), 2);
    let row = Row { flags: flag::PURE | flag::STRICT, kind: Kind::Number, aux: num::INT, payload: 7 };
    assert!(row.has(flag::PURE) && row.has(flag::PURE | flag::STRICT) && !row.has(flag::PURE | flag::SEAL));
    assert_eq!(row.int(), Some(7));
    assert_eq!(Row { aux: num::FLOAT, ..row }.int(), None);
    assert_eq!(Row { kind: Kind::Str, ..row }.int(), None);
}

#[test]
fn a_new_builder_is_empty() {
    let allocator = Allocator::default();
    let mut b = Builder::new(&allocator);
    assert_eq!((b.nodes(), b.steps, b.mark().0, b.stage_mark().0), (0, 0, 0, 0));
    b.clear();
    assert_eq!((b.nodes(), b.steps), (0, 0));
    assert!(List::EMPTY.is_empty());
    assert_eq!(List::EMPTY.len(), 0);
}

#[test]
fn sizes() {
    assert_eq!(std::mem::size_of::<Row>(), 8);
    assert_eq!(std::mem::size_of::<J<'_>>(), 24);
    assert_eq!(std::mem::size_of::<Kind>(), 1);
    assert_eq!(std::mem::size_of::<Mark>(), 4);
    assert_eq!(std::mem::size_of::<Expression<'_>>(), 16);
}

#[test]
#[ignore = "T6a build"]
fn leaves_print_as_the_legacy_printer_prints_them() {
    for t in [
        n("x"),
        T::Int(0),
        T::Int(42),
        T::Int(-7),
        T::Int(i32::MIN),
        T::Float("1.5"),
        T::Float("-0.5"),
        T::Float("1."),
        T::Float("1e21"),
        T::Str("plain"),
        T::Str("a \"quoted\" \\ string\n"),
        T::Str("Ã©"),
        T::Bool(true),
        T::Bool(false),
        T::Null,
        T::Undefined(false),
        T::Undefined(true),
    ] {
        oracle(&t);
    }
}

#[test]
#[ignore = "T6a build"]
fn every_binary_operator_prints_as_the_legacy_printer_prints_it() {
    use BinOp::*;
    for op in [
        Or, And, EqEqEq, NotEqEq, Lt, Le, Gt, Ge, FloatLt, FloatLe, FloatGt, FloatGe, Bor, Bxor,
        Band, Lsl, Lsr, Asr, Plus, Minus, Mul, Div, Mod, Pow, InstanceOf,
    ] {
        oracle(&bin(op, n("a"), n("b")));
        // Precedence on both sides is oxc's; the legacy text must agree.
        oracle(&bin(op, bin(Plus, n("a"), n("b")), bin(Mul, n("c"), n("d"))));
        oracle(&bin(Mul, bin(op, n("a"), n("b")), n("c")));
    }
    oracle(&bin(Eq, n("a"), n("b")));
    oracle(&bin(Eq, dot(n("a"), "f"), T::Int(1)));
    oracle(&bin(Eq, T::Index(Box::new(n("a")), Box::new(T::Int(0))), n("b")));
}

#[test]
#[ignore = "T6a build"]
fn the_strict_flag_of_a_division_follows_its_right_operand() {
    use BinOp::*;
    for op in [Div, Mod, Pow] {
        for right in [T::Int(0), T::Int(2), T::Float("0."), T::Float("2.5"), n("y")] {
            oracle(&bin(op, n("x"), right));
        }
    }
}

#[test]
#[ignore = "T6a build"]
fn zero_minus_a_value_prints_as_a_negation() {
    oracle(&bin(BinOp::Minus, T::Int(0), n("x")));
    oracle(&bin(BinOp::Minus, T::Float("0."), n("x")));
    oracle(&bin(BinOp::Minus, T::Int(0), bin(BinOp::Plus, n("x"), n("y"))));
    oracle(&bin(BinOp::Minus, T::Int(1), n("x")));
    oracle(&bin(BinOp::Minus, n("x"), T::Int(0)));
}

#[test]
#[ignore = "T6a build"]
fn the_two_strict_nullish_tests_of_one_name_print_as_one_loose_test() {
    let test = |name, null_first: bool| {
        let (a, b) = if null_first { (T::Null, T::Undefined(false)) } else { (T::Undefined(false), T::Null) };
        bin(BinOp::Or, bin(BinOp::EqEqEq, n(name), a), bin(BinOp::EqEqEq, n(name), b))
    };
    oracle(&test("x", true));
    oracle(&test("x", false));
    // Not the shape: an `&&`, a `!==`, a test against a number.
    oracle(&bin(
        BinOp::And,
        bin(BinOp::EqEqEq, n("x"), T::Null),
        bin(BinOp::EqEqEq, n("x"), T::Undefined(false)),
    ));
    oracle(&bin(
        BinOp::Or,
        bin(BinOp::NotEqEq, n("x"), T::Null),
        bin(BinOp::EqEqEq, n("x"), T::Undefined(false)),
    ));
    oracle(&bin(
        BinOp::Or,
        bin(BinOp::EqEqEq, n("x"), T::Null),
        bin(BinOp::EqEqEq, n("x"), T::Int(0)),
    ));
}

#[test]
#[ignore = "T6a build"]
fn two_nullish_tests_of_different_targets_have_no_rule() {
    let allocator = Allocator::default();
    let mut b = Builder::new(&allocator);
    let t = bin(
        BinOp::Or,
        bin(BinOp::EqEqEq, n("x"), T::Null),
        bin(BinOp::EqEqEq, n("y"), T::Undefined(false)),
    );
    let T::Bin(op, l, r) = &t else { unreachable!() };
    let (l, r) = (built(l, &mut b), built(r, &mut b));
    // The emitter's rule today (`walk::nullish_target`): the whole unit falls
    // back. The reason must stay the same string.
    assert_eq!(b.bin(*op, l, r).err(), Some(Unsupported("nullish comparison target equality")));
}

#[test]
#[ignore = "T6a build"]
fn unary_and_conditional_forms_print_as_the_legacy_printer_prints_them() {
    let x = || Box::new(n("x"));
    for t in [
        T::Not(x()),
        T::Not(Box::new(T::Not(x()))),
        T::Not(Box::new(bin(BinOp::And, n("a"), n("b")))),
        T::Bnot(x()),
        T::Typeof(x()),
        T::Typeof(Box::new(call(n("f"), vec![]))),
        T::IsNullish(x()),
        T::IsNullish(Box::new(bin(BinOp::Plus, n("a"), n("b")))),
        T::In(Box::new(T::Str("k")), x()),
        T::StrAppend(Box::new(T::Str("a")), x()),
        T::StrAppend(Box::new(T::StrAppend(x(), Box::new(T::Str("b")))), Box::new(T::Str("c"))),
        T::StrAppend(x(), Box::new(T::StrAppend(Box::new(T::Str("b")), Box::new(T::Str("c"))))),
        T::Cond(x(), Box::new(T::Int(1)), Box::new(T::Int(2))),
        T::Cond(
            Box::new(T::Cond(x(), Box::new(n("a")), Box::new(n("b")))),
            Box::new(T::Cond(x(), Box::new(n("c")), Box::new(n("d")))),
            Box::new(T::Cond(x(), Box::new(n("e")), Box::new(n("f")))),
        ),
        T::Cond(Box::new(bin(BinOp::Eq, n("a"), n("b"))), Box::new(T::Int(1)), Box::new(T::Int(2))),
        T::Seq(Box::new(call(n("f"), vec![])), x()),
        call(n("f"), vec![T::Seq(Box::new(n("a")), Box::new(n("b")))]),
    ] {
        oracle(&t);
    }
}

#[test]
#[ignore = "T6a build"]
fn members_calls_and_constructions_print_as_the_legacy_printer_prints_them() {
    let x = || Box::new(n("x"));
    for t in [
        dot(n("x"), "field"),
        dot(n("x"), "not-an-identifier"),
        dot(n("x"), "0"),
        dot(n("x"), "\\\"exotic\""),
        dot(n("x"), "$ok_1"),
        dot(dot(n("x"), "a"), "b"),
        dot(call(n("f"), vec![]), "a"),
        dot(T::Int(1), "a"),
        T::Dot(x(), "f", Some(0)),
        T::Length(x()),
        T::Length(Box::new(T::Str("abc"))),
        T::Index(x(), Box::new(T::Int(0))),
        T::Index(x(), Box::new(bin(BinOp::Plus, n("i"), T::Int(1)))),
        call(n("f"), vec![]),
        call(n("f"), vec![T::Undefined(true)]),
        call(n("f"), vec![T::Undefined(false)]),
        call(n("f"), vec![T::Undefined(true), T::Undefined(true)]),
        call(n("f"), vec![n("a"), T::Int(1), T::Str("s")]),
        call(dot(n("o"), "m"), vec![n("a")]),
        call(call(n("f"), vec![n("a")]), vec![n("b")]),
        // B:164: pure only as `Array.isArray(x)` on the JavaScript identifier.
        call(dot(T::Js("Array"), "isArray"), vec![n("a")]),
        call(dot(T::Js("Array"), "isArray"), vec![call(n("f"), vec![])]),
        call(dot(T::Js("Array"), "isArray"), vec![n("a"), n("b")]),
        call(T::Dot(Box::new(T::Js("Array")), "isArray", Some(0)), vec![n("a")]),
        call(dot(n("Array"), "isArray"), vec![n("a")]),
        call(dot(T::Js("Other"), "isArray"), vec![n("a")]),
        T::New(Box::new(n("C")), vec![]),
        T::New(Box::new(n("C")), vec![n("a"), n("b")]),
        T::New(Box::new(dot(n("M"), "C")), vec![n("a")]),
    ] {
        oracle(&t);
    }
}

#[test]
#[ignore = "T6a build"]
fn a_reference_carries_the_index_of_its_variable() {
    let allocator = Allocator::default();
    let mut b = Builder::new(&allocator);
    let plain = b.reference(7, 0);
    let assigned = b.reference(8, var::ASSIGNED);
    let global = b.reference(9, var::GLOBAL);
    let Expression::Identifier(node) = &plain.expr else { panic!("an identifier") };
    assert_eq!(node.reference_id.get().map(|id| id.index()), Some(7));
    assert_eq!((plain.row.kind, plain.row.payload), (Kind::Var, 7));
    // A:28 and X:60 on a variable (`bir::j::facts::{delay_safe, external_duplicable}`).
    let facts = |j: &J<'_>| (j.row.has(flag::DELAY_SAFE), j.row.has(flag::DUPLICABLE));
    assert_eq!(facts(&plain), (true, true));
    assert_eq!(facts(&assigned), (false, true));
    assert_eq!(facts(&global), (false, false));
    for j in [&plain, &assigned, &global] {
        assert!(j.row.has(flag::PURE | flag::STRICT | flag::SUBEXPR));
        assert_eq!(b.row(&j.expr), j.row);
    }
    // The nullish form compares variables by index.
    fn test<'a>(b: &mut Builder<'a>, v: u32, null: bool) -> J<'a> {
        let (x, y) = (b.reference(v, 0), if null { b.null() } else { b.undefined(false) });
        b.bin(BinOp::EqEqEq, x, y).unwrap()
    }
    let (l, r) = (test(&mut b, 3, true), test(&mut b, 3, false));
    let same = b.bin(BinOp::Or, l, r).unwrap();
    assert!(matches!(&same.expr, Expression::BinaryExpression(e) if e.operator == BinaryOperator::Equality));
    let (l, r) = (test(&mut b, 3, true), test(&mut b, 4, false));
    assert!(b.bin(BinOp::Or, l, r).is_err());
}

#[test]
#[ignore = "T6a build"]
fn the_facts_of_a_node_are_computed_from_the_rows_of_its_operands() {
    let allocator = Allocator::default();
    let mut b = Builder::new(&allocator);
    let has = |b: &mut Builder<'_>, t: &T, f: u16| built(t, b).row.has(f);
    // A:28 delay_safe: no property read, no call, no assignment.
    assert!(has(&mut b, &bin(BinOp::Plus, T::Int(1), T::Int(2)), flag::DELAY_SAFE));
    assert!(has(&mut b, &T::Not(Box::new(T::Bool(true))), flag::DELAY_SAFE));
    assert!(!has(&mut b, &dot(n("x"), "f"), flag::DELAY_SAFE));
    assert!(!has(&mut b, &bin(BinOp::Plus, call(n("f"), vec![]), T::Int(2)), flag::DELAY_SAFE));
    // E:146 is_pure_subexpression: an index of two, a sequence of two.
    assert!(has(&mut b, &T::Index(Box::new(n("a")), Box::new(T::Int(0))), flag::SUBEXPR));
    assert!(!has(&mut b, &T::Index(Box::new(n("a")), Box::new(call(n("f"), vec![]))), flag::SUBEXPR));
    assert!(!has(&mut b, &bin(BinOp::Plus, T::Int(1), T::Int(2)), flag::SUBEXPR));
    // X:60 duplicable: a field with a known position of a duplicable object.
    assert!(!has(&mut b, &dot(T::Bool(true), "f"), flag::DUPLICABLE));
    assert!(has(&mut b, &T::Dot(Box::new(T::Bool(true)), "f", Some(0)), flag::DUPLICABLE));
    assert!(has(
        &mut b,
        &T::Cond(Box::new(T::Bool(true)), Box::new(T::Int(1)), Box::new(T::Str("s"))),
        flag::DUPLICABLE
    ));
    // The kinds and what they carry.
    let j = built(&T::Dot(Box::new(n("x")), "f", Some(3)), &mut b);
    assert_eq!((j.row.kind, j.row.payload, j.row.aux), (Kind::Dot, 4, 0));
    let j = built(&bin(BinOp::Lsr, n("x"), T::Int(0)), &mut b);
    assert_eq!((j.row.kind, j.row.aux), (Kind::Bin, BinOp::Lsr as u8));
    assert_eq!(built(&T::Int(-5), &mut b).row.int(), Some(-5));
    assert_eq!(built(&T::Float("5."), &mut b).row.int(), None);
    assert_eq!(built(&T::Undefined(true), &mut b).row.aux, 1);
    assert_eq!(built(&T::Length(Box::new(n("x"))), &mut b).row.kind, Kind::Length);
    assert_eq!(built(&T::IsNullish(Box::new(n("x"))), &mut b).row.kind, Kind::IsNullish);
    assert_eq!(built(&T::StrAppend(Box::new(n("x")), Box::new(n("y"))), &mut b).row.kind, Kind::StrAppend);
}

#[test]
#[ignore = "T6a build"]
fn a_chain_or_a_sequence_that_is_not_in_print_form_is_marked_for_the_seal() {
    let allocator = Allocator::default();
    let mut b = Builder::new(&allocator);
    let seal = |b: &mut Builder<'_>, t: &T| built(t, b).row.has(flag::SEAL);
    for op in [BinOp::And, BinOp::Or, BinOp::Bor] {
        // Left-nested is the print form; right-nested is what the rules build.
        assert!(!seal(&mut b, &bin(op, bin(op, n("a"), n("b")), n("c"))), "{op:?}");
        assert!(seal(&mut b, &bin(op, n("a"), bin(op, n("b"), n("c")))), "{op:?}");
        // The mark is of the subtree: a parent of another kind keeps it.
        assert!(seal(&mut b, &T::Not(Box::new(bin(op, n("a"), bin(op, n("b"), n("c")))))), "{op:?}");
        assert!(seal(&mut b, &call(n("f"), vec![bin(op, n("a"), bin(op, n("b"), n("c")))])), "{op:?}");
    }
    assert!(!seal(&mut b, &bin(BinOp::And, n("a"), bin(BinOp::Or, n("b"), n("c")))));
    assert!(!seal(&mut b, &bin(BinOp::Plus, n("a"), bin(BinOp::Plus, n("b"), n("c")))));
    assert!(!seal(&mut b, &T::Seq(Box::new(n("a")), Box::new(n("b")))));
    assert!(seal(&mut b, &T::Seq(Box::new(n("a")), Box::new(T::Seq(Box::new(n("b")), Box::new(n("c")))))));
    assert!(seal(&mut b, &T::Seq(Box::new(T::Seq(Box::new(n("a")), Box::new(n("b")))), Box::new(n("c")))));
}

/// Builds `width` calls `f(a.b, 1, "s")` and one call of all of them, and
/// returns the steps and the nodes.
fn wide<'a>(b: &mut Builder<'a>, width: usize) -> (u64, usize) {
    let (steps, nodes) = (b.steps, b.nodes());
    let outer = b.named("g", false);
    let all = b.mark();
    for _ in 0..width {
        let f = b.named("f", false);
        let mark = b.mark();
        let a = b.named("a", false);
        let member = b.dot(a, "b", None, false);
        b.push(member);
        let one = b.int(1);
        b.push(one);
        let s = b.string("s");
        b.push(s);
        let call = b.call(f, mark, 0, false);
        b.push(call);
    }
    b.call(outer, all, 0, false);
    (b.steps - steps, b.nodes() - nodes)
}

/// A member chain `x.f.f...` of `depth` reads under `depth` negations.
fn deep<'a>(b: &mut Builder<'a>, depth: usize) -> (u64, usize) {
    let (steps, nodes) = (b.steps, b.nodes());
    let mut value = b.named("x", false);
    for _ in 0..depth {
        value = b.dot(value, "f", None, false);
    }
    for _ in 0..depth {
        value = b.not(value);
    }
    assert!(value.row.has(flag::PURE));
    (b.steps - steps, b.nodes() - nodes)
}

/// A string concatenation of `terms` terms, left-nested.
fn concatenation<'a>(b: &mut Builder<'a>, terms: usize) -> (u64, usize) {
    let (steps, nodes) = (b.steps, b.nodes());
    let mut value = b.string("s");
    for _ in 1..terms {
        let next = b.named("x", false);
        value = b.str_append(value, next);
    }
    (b.steps - steps, b.nodes() - nodes)
}

#[test]
#[ignore = "T6a build"]
fn ten_thousand_nodes_cost_ten_times_a_thousand() {
    // Relations between two sizes, not constants: the builder states one
    // step per node and one per operand of a list.
    type Shape = for<'a> fn(&mut Builder<'a>, usize) -> (u64, usize);
    for (name, shape) in [
        ("wide", wide as Shape),
        ("deep", deep as Shape),
        ("concatenation", concatenation as Shape),
    ] {
        let allocator = Allocator::default();
        let mut b = Builder::new(&allocator);
        let (small_steps, small_nodes) = shape(&mut b, 1_000);
        let (large_steps, large_nodes) = shape(&mut b, 10_000);
        // Exactly linear: the part that does not depend on the size is the
        // same in both.
        let per_unit = (large_steps - small_steps) / 9_000;
        assert_eq!(large_steps - small_steps, per_unit * 9_000, "{name}: steps");
        assert_eq!((large_nodes - small_nodes) % 9_000, 0, "{name}: nodes");
        // A step is a node or an operand of a list: never more than two
        // steps a node.
        assert!(large_steps <= 2 * large_nodes as u64, "{name}: {large_steps} steps, {large_nodes} nodes");
        assert!(large_steps >= large_nodes as u64, "{name}");
    }
}

#[test]
#[ignore = "T6a build"]
fn a_warm_builder_allocates_nothing_outside_the_arena() {
    // Warm: one arena chunk that holds the unit (a reset arena keeps its
    // largest chunk), and the table and the operand stack at the capacity a
    // first unit of the same shape needed.
    let allocator = Allocator::with_capacity(64 << 20);
    let capacity = {
        let first = Allocator::default();
        let mut b = Builder::new(&first);
        wide(&mut b, 10_000);
        deep(&mut b, 10_000);
        (b.nodes(), 10_004)
    };
    let mut b = Builder::new(&allocator);
    b.reserve(capacity.0, capacity.1);
    let allocations = allocation_counter::measure(|| {
        wide(&mut b, 10_000);
        deep(&mut b, 10_000);
    });
    assert_eq!(allocations.count_total, 0, "{allocations:?}");
    assert_eq!(b.nodes(), capacity.0);
}

#[test]
#[ignore = "T6a build"]
fn clearing_the_builder_keeps_its_capacity() {
    let allocator = Allocator::default();
    let mut b = Builder::new(&allocator);
    wide(&mut b, 1_000);
    let nodes = b.nodes();
    b.clear();
    assert_eq!((b.nodes(), b.steps), (0, 0));
    let allocations = allocation_counter::measure(|| b.reserve(nodes, 1_000));
    assert_eq!(allocations.count_total, 0);
}

/// T6b: statements and statement lists.
mod statements {
    use super::*;
    use crate::js_ir::arena::{JsDepsProgram, JsProgram, Stmt, StmtKind, VarDecl};
    use crate::js_ir::op::IdentInfo;
    use crate::js_ir::ModulePathResolver;
    use crate::lambda::lam_compat::LetKind;

    /// A statement, described once. Only shapes the printer writes as the
    /// lowering builds them: the forms that the seal decides (a block's
    /// braces, a dropped `else`, an omitted declaration) are not T6b's.
    #[derive(Clone)]
    enum St {
        Exp(T),
        Return(T),
        Throw(T),
        /// A variable by index; its name is `v<index>`.
        Declare(u32, Option<T>),
        If(T, Vec<St>, Vec<St>),
        While(T, Vec<St>),
        Break,
        Continue,
        Debugger,
    }

    fn variable(index: u32) -> Ident {
        Ident::new(format!("v{index}").as_str(), 0, IdentFlags::NONE)
    }

    fn legacy_statement(s: &St, a: &mut JsArena) -> Stmt {
        let kind = match s {
            St::Exp(e) => StmtKind::Exp(legacy(e, a)),
            St::Return(e) => StmtKind::Return(legacy(e, a)),
            St::Throw(e) => StmtKind::Throw(legacy(e, a)),
            St::Declare(index, value) => {
                let value = value.as_ref().map(|value| legacy(value, a));
                StmtKind::Variable(a.var_id(VarDecl {
                    ident: variable(*index),
                    value,
                    property: LetKind::Strict,
                    ident_info: IdentInfo::default(),
                }))
            }
            St::If(c, t, e) => {
                let c = legacy(c, a);
                let (t, e) = (legacy_list(t, a), legacy_list(e, a));
                StmtKind::If(c, a.stmt_list(&t), a.stmt_list(&e))
            }
            St::While(c, body) => {
                let c = legacy(c, a);
                let body = legacy_list(body, a);
                StmtKind::While(None, c, a.stmt_list(&body))
            }
            St::Break => StmtKind::Break(None),
            St::Continue => StmtKind::Continue(None),
            St::Debugger => StmtKind::Debugger,
        };
        a.stmt(kind)
    }

    fn legacy_list(list: &[St], a: &mut JsArena) -> Vec<Stmt> {
        list.iter().map(|s| legacy_statement(s, a)).collect()
    }

    fn built_statement<'a>(s: &St, b: &mut Builder<'a>) -> S<'a> {
        match s {
            St::Exp(e) => {
                let e = built(e, b);
                b.exp(e)
            }
            St::Return(e) => {
                let e = built(e, b);
                b.return_(e)
            }
            St::Throw(e) => {
                let e = built(e, b);
                b.throw(e)
            }
            St::Declare(index, value) => {
                let value = value.as_ref().map(|value| built(value, b));
                b.declare(*index, LetKind::Strict as u8, value)
            }
            St::If(c, t, e) => {
                let c = built(c, b);
                let (t, e) = (built_list(t, b), built_list(e, b));
                b.if_(c, t, e)
            }
            St::While(c, body) => {
                let c = built(c, b);
                let body = built_list(body, b);
                b.while_(None, c, body)
            }
            St::Break => b.break_(None),
            St::Continue => b.continue_(None),
            St::Debugger => b.debugger(),
        }
    }

    fn built_list<'a>(list: &[St], b: &mut Builder<'a>) -> List {
        let mark = b.stage_mark();
        for s in list {
            let s = built_statement(s, b);
            b.stage(s);
        }
        b.list(mark)
    }

    /// The name table `oxc_codegen` reads: symbol `i` is named `v<i>`, and
    /// reference `i` resolves to symbol `i`. This is the mechanism of
    /// "T6 design" (d), built by hand here; the program slice builds it
    /// from the replay's names.
    fn names(variables: u32) -> oxc_semantic::Scoping {
        use oxc_syntax::{node::NodeId, reference::{Reference, ReferenceFlags}, scope::ScopeFlags, symbol::SymbolFlags};
        let mut scoping = oxc_semantic::Scoping::default();
        let scope = scoping.add_scope(None, NodeId::DUMMY, ScopeFlags::Top);
        for index in 0..variables {
            let name = format!("v{index}");
            let symbol = scoping.create_symbol(
                SPAN,
                oxc_ast::ast::Ident::from(name.as_str()),
                SymbolFlags::empty(),
                scope,
                NodeId::DUMMY,
            );
            let reference = scoping.create_reference(Reference::new_with_symbol_id(
                NodeId::DUMMY,
                symbol,
                scope,
                ReferenceFlags::Read,
            ));
            assert_eq!((symbol.index(), reference.index()), (index as usize, index as usize));
        }
        scoping
    }

    fn print_program<'a>(b: &Builder<'a>, body: ArenaVec<'a, Statement<'a>>, variables: u32) -> String {
        use super::super::super::build::Allocate;
        let ast = &b.ast;
        let program =
            Program::new(SPAN, oxc_span::SourceType::mjs(), "", ast.vec(), None, ast.vec(), body, ast);
        oxc_codegen::Codegen::new()
            .with_options(super::super::super::program::codegen_options())
            .with_scoping(Some(names(variables)))
            .build(&program)
            .code
    }

    /// The legacy program's statements (without the directive and the
    /// trailer comment of the file), reformatted once.
    fn legacy_text(list: &[St]) -> String {
        let mut a = JsArena::default();
        let block = legacy_list(list, &mut a);
        let p = JsDepsProgram {
            program: JsProgram::new_in(block, vec![], a),
            modules: vec![],
            side_effect: None,
        };
        let resolver = ModulePathResolver::from_compile_options(None, None, None, None, None, None, false);
        let text = crate::js_ir::program_printer::print_deps_program_with_directives_and_options(
            &p,
            Some(&resolver),
            &[],
            false,
            false,
            false,
        );
        // The file's frame is the program slice's: compare the statements.
        let body = text.strip_suffix("/* No side effect */\n").expect("the trailer");
        let body = body.strip_prefix("'use strict';\n").expect("the CommonJS directive");
        reformat(body, mode()).unwrap()
    }

    fn oracle(list: &[St], variables: u32) {
        let expected = legacy_text(list);
        let allocator = Allocator::default();
        let mut b = Builder::new(&allocator);
        let built = built_list(list, &mut b);
        let body = b.statements_of(built);
        let actual = print_program(&b, body, variables);
        assert_eq!(expected, actual);
        assert_eq!(reformat(&actual, mode()).unwrap(), actual, "a fixed point");
    }

    fn f(name: &'static str) -> St {
        St::Exp(call(n(name), vec![]))
    }

    #[test]
    fn sizes() {
        assert_eq!(std::mem::size_of::<S<'_>>(), 24);
        assert_eq!(std::mem::size_of::<Option<S<'_>>>(), 24);
        assert_eq!(std::mem::size_of::<List>(), 8);
        assert_eq!(std::mem::size_of::<Statement<'_>>(), 16);
    }

    #[test]
    #[ignore = "T6b build"]
    fn plain_statements_print_as_the_legacy_printer_prints_them() {
        oracle(&[f("a"), f("b")], 0);
        oracle(&[St::Exp(bin(BinOp::Eq, dot(n("o"), "f"), T::Int(1)))], 0);
        oracle(&[St::Throw(n("e"))], 0);
        oracle(&[St::Debugger], 0);
        oracle(&[St::Declare(0, Some(T::Int(1))), St::Declare(1, Some(call(n("f"), vec![])))], 2);
        oracle(&[St::If(n("c"), vec![f("a")], vec![f("b")])], 0);
        oracle(&[St::If(n("c"), vec![f("a"), f("b")], vec![St::Throw(n("e"))])], 0);
        oracle(&[St::If(n("c"), vec![St::If(n("d"), vec![f("a")], vec![f("b")])], vec![f("e")])], 0);
    }

    #[test]
    #[ignore = "T6b build"]
    fn a_reference_and_a_binder_print_the_name_of_their_variable() {
        // The declaration's binder carries the symbol and a use carries the
        // reference of the same index: both print the table's name.
        let allocator = Allocator::default();
        let mut b = Builder::new(&allocator);
        let mark = b.stage_mark();
        let one = b.int(1);
        let declaration = b.declare(1, LetKind::Strict as u8, Some(one));
        assert_eq!((declaration.row.kind, declaration.row.payload), (Kind::Declare, 1));
        assert_eq!(declaration.row.aux, LetKind::Strict as u8);
        b.stage(declaration);
        let callee = b.named("f", false);
        let arguments = b.mark();
        let use_ = b.reference(1, 0);
        b.push(use_);
        let call = b.call(callee, arguments, 0, false);
        let statement = b.exp(call);
        b.stage(statement);
        let list = b.list(mark);
        let body = b.statements_of(list);
        assert_eq!(print_program(&b, body, 2), "let v1 = 1;\nf(v1);\n");
    }

    #[test]
    #[ignore = "T6b build"]
    fn a_statement_is_written_in_the_form_the_rules_read() {
        let allocator = Allocator::default();
        let mut b = Builder::new(&allocator);
        // A `return` keeps its value, `undefined` too.
        let unit = b.undefined(true);
        let statement = b.return_(unit);
        assert!(matches!(&statement.stmt, Statement::ReturnStatement(r) if r.argument.is_some()));
        // An `if` keeps both blocks, the empty one too.
        let test = b.named("c", false);
        let then = built_list(&[f("a")], &mut b);
        let statement = b.if_(test, then, List::EMPTY);
        let Statement::IfStatement(node) = &statement.stmt else { panic!("an if") };
        assert!(matches!(&node.alternate, Some(Statement::BlockStatement(block)) if block.body.is_empty()));
        assert!(matches!(&node.consequent, Statement::BlockStatement(block) if block.body.len() == 1));
        // A declaration keeps its value, `undefined` too.
        let unit = b.undefined(false);
        let statement = b.declare(0, LetKind::Variable as u8, Some(unit));
        let Statement::VariableDeclaration(node) = &statement.stmt else { panic!("a declaration") };
        assert!(node.declarations[0].init.is_some());
        assert_eq!(statement.row.aux, LetKind::Variable as u8);
        // The row of a statement is in the table.
        assert_eq!(b.statement_row(&statement.stmt), statement.row);
        // A block statement keeps its braces and its statements.
        let list = built_list(&[f("a"), f("b")], &mut b);
        let statement = b.block(list);
        assert_eq!(statement.row.kind, Kind::Block);
        assert!(matches!(&statement.stmt, Statement::BlockStatement(block) if block.body.len() == 2));
        // A loop is one statement: the `;` the legacy printer writes after
        // a `while` is the seal's (observed: `while (c) {...}\n;`).
        let test = b.named("c", false);
        let body = built_list(&[f("a"), St::Break, St::Continue], &mut b);
        let statement = b.while_(None, test, body);
        let Statement::WhileStatement(node) = &statement.stmt else { panic!("a while") };
        let Statement::BlockStatement(block) = &node.body else { panic!("a block") };
        assert_eq!(block.body.len(), 3);
        assert_eq!(b.statement_row(&block.body[1]).kind, Kind::Break);
        assert_eq!(b.statement_row(&block.body[2]).kind, Kind::Continue);
        let test = b.named("c", false);
        let statement = b.while_(Some("loop"), test, List::EMPTY);
        assert_eq!(statement.row.kind, Kind::While);
        let Statement::LabeledStatement(node) = &statement.stmt else { panic!("a label") };
        assert_eq!(node.label.name, "loop");
        let exit = b.break_(Some("loop"));
        assert!(matches!(&exit.stmt, Statement::BreakStatement(node) if node.label.as_ref().is_some_and(|l| l.name == "loop")));
        let next = b.continue_(Some("loop"));
        assert!(matches!(&next.stmt, Statement::ContinueStatement(node) if node.label.as_ref().is_some_and(|l| l.name == "loop")));
        assert_eq!(b.debugger().row.kind, Kind::Debugger);
    }

    #[test]
    #[ignore = "T6b build"]
    fn a_list_in_flight_is_read_and_taken_by_position() {
        let allocator = Allocator::default();
        let mut b = Builder::new(&allocator);
        let list = built_list(&[f("a"), St::Declare(3, None), St::Return(n("x"))], &mut b);
        assert_eq!(list.len(), 3);
        assert!(!list.is_empty() && List::EMPTY.is_empty());
        assert_eq!(b.last_row(list).map(|row| row.kind), Some(Kind::Return));
        assert_eq!(b.last_row(List::EMPTY), None);
        assert_eq!(b.row_at(list, 1).kind, Kind::Declare);
        assert_eq!(b.row_at(list, 1).payload, 3);
        assert_eq!(b.statement_at(list, 0).row.kind, Kind::Exp);
        // Lists nest: a list built while another is being staged is its own run.
        let mark = b.stage_mark();
        let first = built_statement(&f("p"), &mut b);
        b.stage(first);
        let inner = built_list(&[f("q"), f("r")], &mut b);
        let test = b.named("c", false);
        let nested = b.if_(test, inner, List::EMPTY);
        b.stage(nested);
        let outer = b.list(mark);
        assert_eq!(outer.len(), 2);
        assert_eq!(b.row_at(outer, 1).kind, Kind::If);
        // A statement is taken once; the others stay.
        let taken = b.take(list, 2);
        assert_eq!(taken.row.kind, Kind::Return);
        assert_eq!(b.row_at(list, 0).kind, Kind::Exp);
        let again = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| b.row_at(list, 2)));
        assert!(again.is_err(), "a taken statement is not read again");
    }

    #[test]
    #[ignore = "T6b build"]
    fn the_marks_of_a_statement_are_those_of_what_it_holds() {
        let allocator = Allocator::default();
        let mut b = Builder::new(&allocator);
        let chain = || bin(BinOp::And, n("a"), bin(BinOp::And, n("b"), n("c")));
        let marked = |b: &mut Builder<'_>, s: &St| built_statement(s, b).row.has(flag::SEAL);
        assert!(marked(&mut b, &St::Exp(chain())));
        assert!(marked(&mut b, &St::Return(chain())));
        assert!(marked(&mut b, &St::Throw(chain())));
        assert!(marked(&mut b, &St::Declare(0, Some(chain()))));
        assert!(marked(&mut b, &St::If(chain(), vec![], vec![])));
        assert!(marked(&mut b, &St::If(n("c"), vec![St::Exp(chain())], vec![])));
        assert!(marked(&mut b, &St::If(n("c"), vec![], vec![St::Exp(chain())])));
        assert!(marked(&mut b, &St::While(n("c"), vec![St::Exp(chain())])));
        assert!(marked(&mut b, &St::While(chain(), vec![])));
        assert!(!marked(&mut b, &St::If(n("c"), vec![f("a")], vec![f("b")])));
        assert!(!marked(&mut b, &St::Declare(0, None)));
        assert!(!marked(&mut b, &St::Break));
    }

    /// A list of `length` statements `f(v0);` under `depth` nested `if`s.
    fn tower<'a>(b: &mut Builder<'a>, length: usize, depth: usize) -> (u64, usize) {
        let (steps, nodes) = (b.steps, b.nodes());
        let mark = b.stage_mark();
        for _ in 0..length {
            let callee = b.named("f", false);
            let arguments = b.mark();
            let argument = b.reference(0, 0);
            b.push(argument);
            let call = b.call(callee, arguments, 0, false);
            let statement = b.exp(call);
            b.stage(statement);
        }
        let mut list = b.list(mark);
        for _ in 0..depth {
            let test = b.named("c", false);
            let statement = b.if_(test, list, List::EMPTY);
            let mark = b.stage_mark();
            b.stage(statement);
            list = b.list(mark);
        }
        let body = b.statements_of(list);
        assert_eq!(body.len(), if depth == 0 { length } else { 1 });
        (b.steps - steps, b.nodes() - nodes)
    }

    #[test]
    #[ignore = "T6b build"]
    fn ten_thousand_statements_cost_ten_times_a_thousand() {
        // Relations between two sizes: a statement is staged once, moved
        // into its list once and into its parent once, however long the
        // list and however deep the nesting.
        for (name, long, deep) in [("a long list", true, false), ("a deep nest", false, true), ("both", true, true)] {
            let size = |n: usize| (if long { n } else { 1 }, if deep { n } else { 0 });
            let allocator = Allocator::default();
            let mut b = Builder::new(&allocator);
            let (small_length, small_depth) = size(1_000);
            let (large_length, large_depth) = size(10_000);
            let (small_steps, small_nodes) = tower(&mut b, small_length, small_depth);
            let (large_steps, large_nodes) = tower(&mut b, large_length, large_depth);
            let per_unit = (large_steps - small_steps) / 9_000;
            assert_eq!(large_steps - small_steps, per_unit * 9_000, "{name}: steps");
            assert_eq!((large_nodes - small_nodes) % 9_000, 0, "{name}: nodes");
            // A statement costs its node and at most three moves (staged,
            // into its list, into its parent); an expression node at most
            // two steps (T6a).
            assert!(large_steps <= 4 * large_nodes as u64, "{name}: {large_steps} steps, {large_nodes} nodes");
        }
    }

    #[test]
    #[ignore = "T6b build"]
    fn a_warm_builder_builds_statements_without_allocating() {
        let allocator = Allocator::with_capacity(64 << 20);
        let (nodes, statements) = {
            let first = Allocator::default();
            let mut b = Builder::new(&first);
            tower(&mut b, 10_000, 0);
            tower(&mut b, 1, 10_000);
            (b.nodes(), 20_002)
        };
        let mut b = Builder::new(&allocator);
        b.reserve(nodes, 4);
        b.reserve_statements(statements, 10_000);
        let allocations = allocation_counter::measure(|| {
            tower(&mut b, 10_000, 0);
            tower(&mut b, 1, 10_000);
        });
        assert_eq!(allocations.count_total, 0, "{allocations:?}");
        // Clearing keeps the capacity.
        b.clear();
        let allocations = allocation_counter::measure(|| b.reserve_statements(statements, 10_000));
        assert_eq!(allocations.count_total, 0);
    }
}
