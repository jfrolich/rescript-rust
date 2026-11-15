//! Acceptance tests of the statement half of the lowering's interface on J
//! rows (THREE_TREES 11.4, "T6: the interface"; slice T6l).
//!
//! The oracle form of `js_tests.rs`: the same statements are built twice in
//! two arenas that start equal, once through [`JsStmt`] on [`Rows`] and
//! once with the calls the lowering makes today, and `Bir::dump` of the two
//! must be equal. No expected row is written down.
use super::{JsStmt, Range};
use crate::bir::j::rows::{E, Rows};
use crate::bir::j::rows_stmt::S;
use crate::bir::j::{norm, plain};
use crate::bir::lower::js::Js;
use crate::bir::lower::scope::Scope;
use crate::bir::{Bir, FuncId, JsId, JsPayload, ListId, NodeId, StrId, SwitchId, VarId, VarSpan, View};
use crate::emit::row::Kind;
use crate::js_ir::{BinOp, ForDirection};
use crate::lambda::lam_compat::LetKind;
use crate::name::Name;

/// What both sides of a comparison start from: an arena that counts
/// JavaScript occurrences, four variables, a label, and the descriptors of
/// a call, of a function and of a switch with one key and a default.
struct Unit {
    b: Bir,
    x: VarId,
    y: VarId,
    f: VarId,
    /// Bound by the one declaration or loop a test builds.
    t: VarId,
    label: StrId,
    call: JsId,
    header: FuncId,
    switch: SwitchId,
}

fn unit() -> Unit {
    let mut b = Bir::default();
    b.begin_bulk();
    b.js_scope = Some(Scope::new(0));
    let x = b.new_var_id(Name::new("x"), 1);
    let y = b.new_var_id(Name::new("y"), 2);
    let f = b.new_var_id(Name::new("f"), 3);
    let t = b.new_var_id(Name::new("t"), 4);
    let label = b.intern_text("loop");
    let call = b.js_info(JsPayload::Call(Default::default()));
    let header = b.function_header(VarSpan { start: 0, len: 0 }, Default::default(), crate::lambda::LamLoc::NONE);
    let switch = b.switch_header(crate::bir::SwitchInput {
        keys: vec![crate::bir::CaseKey::String(label)],
        clauses: vec![],
        constants: 1,
        consts_full: false,
        blocks_full: false,
        has_default: true,
        dispatch: crate::lambda::SwitchDispatch::Direct,
    });
    Unit { b, x, y, f, t, label, call, header, switch }
}

/// Build with the interface in one unit and with today's calls in another,
/// and require equal arenas.
fn same(interface: impl FnOnce(&mut Rows, &mut Unit), today: impl FnOnce(&mut Unit)) {
    let (mut left, mut right) = (unit(), unit());
    let mut rows = Rows::default();
    interface(&mut rows, &mut left);
    today(&mut right);
    assert_eq!(left.b.dump(), right.b.dump());
}

/// A statement of today's side that the comparison reads in the dump.
fn built(_: NodeId) {}
/// A statement that is not attached: the comparison reads it in the dump.
fn done(_: S) {}

fn var(b: &mut Bir, var: VarId) -> NodeId {
    plain::node(b, View::Var { var }, 0)
}

/// The statements the lists of these tests are made of.
#[derive(Clone, Copy, Debug)]
enum St {
    /// `f();`
    Call,
    /// `return y;`
    Return,
    /// `break;`
    Break,
    /// `throw x;`
    Throw,
}

fn statement(r: &mut Rows, u: &mut Unit, st: St) -> S {
    let a = &mut u.b;
    match st {
        St::Call => {
            let f = r.var(a, u.f);
            let mark = r.mark();
            let call = r.call(a, f, mark, u.call);
            r.exp(a, call)
        }
        St::Return => {
            let y = r.var(a, u.y);
            r.return_(a, y)
        }
        St::Break => r.break_(a, None),
        St::Throw => {
            let x = r.var(a, u.x);
            r.throw(a, x)
        }
    }
}

fn statement_today(u: &mut Unit, st: St) -> NodeId {
    let b = &mut u.b;
    match st {
        St::Call => {
            let callee = var(b, u.f);
            let value = plain::node(b, View::JCall { callee, args: &[], info: u.call }, 0);
            b.new_node(View::SExp { value }, 0)
        }
        St::Return => {
            let value = var(b, u.y);
            crate::bir::j::return_value(b, value)
        }
        St::Break => b.new_node(View::SBreak { label: None }, 0),
        St::Throw => {
            let value = var(b, u.x);
            plain::node(b, View::SThrow { value }, 0)
        }
    }
}

/// A list in flight of the statements of `shape`.
fn run(r: &mut Rows, u: &mut Unit, shape: &[St]) -> ListId {
    let statements: Vec<S> = shape.iter().map(|&st| statement(r, u, st)).collect();
    r.list(&mut u.b, shape.len() as u32, statements.into_iter())
}

fn run_today(u: &mut Unit, shape: &[St]) -> ListId {
    let statements: Vec<NodeId> = shape.iter().map(|&st| statement_today(u, st)).collect();
    u.b.lists.push_iter(statements.len(), statements.into_iter())
}

const SHAPES: [&[St]; 6] =
    [&[], &[St::Call], &[St::Return], &[St::Break], &[St::Call, St::Return], &[St::Call, St::Call, St::Throw]];

#[test]
fn sizes() {
    assert_eq!(std::mem::size_of::<S>(), 4);
    assert_eq!(std::mem::size_of::<Option<S>>(), 8);
    assert_eq!(std::mem::size_of::<<Rows as JsStmt>::L>(), 4);
    assert_eq!(std::mem::size_of::<Range<E>>(), 16);
}

/// A statement is consumed by what it is given to; a list is an index.
/// Compiles only while `S` is not `Copy` and `L` is.
#[test]
fn a_statement_is_not_copy_and_a_list_is() {
    trait NotCopy<A> {
        fn check() {}
    }
    impl<T> NotCopy<()> for T {}
    impl<T: Copy> NotCopy<u8> for T {}
    <S as NotCopy<_>>::check();
    fn copy<T: Copy>() {}
    copy::<<Rows as JsStmt>::L>();
}

#[test]
fn the_transition_is_the_identity() {
    let mut u = unit();
    let node = u.b.new_node(View::SBreak { label: None }, 0);
    assert_eq!(Rows::stmt_node(Rows::stmt_from_node(node)), node);
    let list = u.b.lists.push_iter(1, std::iter::once(node));
    assert_eq!(Rows::list_id(Rows::list_from(list)), list);
}

#[test]
fn a_statement_is_the_row_the_lowering_writes_today() {
    for st in [St::Call, St::Return, St::Break, St::Throw] {
        same(|r, u| done(statement(r, u, st)), |u| built(statement_today(u, st)));
    }
    // A `return` is built in two ways today (`bir::j::return_value` and
    // `plain::node`): they write the same row, so one function serves.
    same(
        |r, u| done(statement(r, u, St::Return)),
        |u| {
            let value = var(&mut u.b, u.y);
            built(plain::node(&mut u.b, View::SReturn { value }, 0));
        },
    );
    same(
        |r, u| {
            let value = r.int_literal(&mut u.b, 3);
            done(r.assign(&mut u.b, u.x, value));
        },
        |u| {
            let value = plain::int(&mut u.b, 3);
            built(crate::bir::j::assign(&mut u.b, u.x, value));
        },
    );
    for kind in [LetKind::Strict, LetKind::Alias, LetKind::StrictOpt, LetKind::Variable] {
        same(
            |r, u| {
                let value = r.var(&mut u.b, u.x);
                done(r.declare(&mut u.b, kind, u.t, Some(value)));
            },
            |u| {
                let value = var(&mut u.b, u.x);
                built(crate::bir::j::declare(&mut u.b, kind, u.t, value));
            },
        );
        same(
            |r, u| done(r.declare(&mut u.b, kind, u.t, None)),
            |u| {
                let aux = kind as u16 | ((crate::js_ir::op::UsedStats::Used as u16) << 2);
                built(plain::node(&mut u.b, View::SDecl { var: u.t, value: None }, aux));
            },
        );
    }
    same(|r, u| done(r.debugger(&mut u.b)), |u| built(plain::node(&mut u.b, View::SDebugger, 0)));
    for labelled in [false, true] {
        same(
            |r, u| {
                let label = labelled.then_some(u.label);
                done(r.break_(&mut u.b, label));
                done(r.continue_(&mut u.b, label));
            },
            |u| {
                let label = labelled.then_some(u.label);
                built(u.b.new_node(View::SBreak { label }, 0));
                built(u.b.new_node(View::SContinue { label }, 0));
            },
        );
    }
}

#[test]
fn a_list_is_the_pool_list_of_its_statements() {
    for shape in SHAPES {
        same(
            |r, u| {
                let list = run(r, u, shape);
                assert_eq!(r.len(&u.b, list) as usize, shape.len());
                for (index, st) in shape.iter().enumerate() {
                    let kind = match st {
                        St::Call => Kind::Exp,
                        St::Return => Kind::Return,
                        St::Break => Kind::Break,
                        St::Throw => Kind::Throw,
                    };
                    assert_eq!(r.kind_at(&u.b, list, index as u32), kind);
                }
                // Taken out one by one, the statements are those given, in
                // order, and they make an equal list again.
                let again: Vec<S> = (0..shape.len()).map(|index| r.take_at(&mut u.b, list, index as u32)).collect();
                for (index, statement) in again.iter().enumerate() {
                    assert_eq!(r.stmt_kind(&u.b, statement), r.kind_at(&u.b, list, index as u32));
                }
                let second = r.list(&mut u.b, shape.len() as u32, again.into_iter());
                assert_eq!(u.b.lists.get(second), u.b.lists.get(list));
                done(r.block_of(&mut u.b, second));
            },
            |u| {
                let list = run_today(u, shape);
                let nodes = u.b.lists.get(list).to_vec();
                let second = u.b.lists.push_iter(nodes.len(), nodes.into_iter());
                built(u.b.block_from_list(second));
            },
        );
    }
}

#[test]
fn a_body_is_adopted_by_its_statement() {
    for shape in SHAPES {
        same(
            |r, u| {
                let list = run(r, u, shape);
                done(r.block_of(&mut u.b, list));
                let list = run(r, u, shape);
                done(r.explicit_block(&mut u.b, list));
            },
            |u| {
                let list = run_today(u, shape);
                built(u.b.block_from_list(list));
                let list = run_today(u, shape);
                built(u.b.explicit_block_from_list(list));
            },
        );
        for other in SHAPES {
            same(
                |r, u| {
                    let (yes, no) = (run(r, u, shape), run(r, u, other));
                    let test = r.var(&mut u.b, u.x);
                    done(r.if_plain(&mut u.b, test, yes, no));
                },
                |u| {
                    let (yes, no) = (run_today(u, shape), run_today(u, other));
                    let condition = var(&mut u.b, u.x);
                    let then_ = u.b.block_from_list(yes);
                    let else_ = u.b.block_from_list(no);
                    built(u.b.new_node(View::SIf { condition, then_, else_: Some(else_) }, 0));
                },
            );
        }
        for labelled in [false, true] {
            same(
                |r, u| {
                    let label = labelled.then_some(u.label);
                    let body = run(r, u, shape);
                    let condition = r.boolean(&mut u.b, true);
                    done(r.while_(&mut u.b, condition, body, label));
                },
                |u| {
                    let label = labelled.then_some(u.label);
                    let body = run_today(u, shape);
                    let condition = plain::boolean(&mut u.b, true);
                    let body = u.b.block_from_list(body);
                    built(u.b.new_node(View::SWhile { condition, body, label }, 0));
                },
            );
            for awaited in [false, true] {
                same(
                    |r, u| {
                        let label = labelled.then_some(u.label);
                        let body = run(r, u, shape);
                        let iterable = r.var(&mut u.b, u.x);
                        done(r.for_of(&mut u.b, u.t, iterable, body, label, awaited));
                    },
                    |u| {
                        let label = labelled.then_some(u.label);
                        let body = run_today(u, shape);
                        let iterable = var(&mut u.b, u.x);
                        let body = u.b.block_from_list(body);
                        let parts = [iterable, body];
                        built(u.b.new_node(
                            if awaited {
                                View::SForAwaitOf { var: u.t, parts: &parts, label }
                            } else {
                                View::SForOf { var: u.t, parts: &parts, label }
                            },
                            0,
                        ));
                    },
                );
            }
            for direction in [ForDirection::Upto, ForDirection::Downto, ForDirection::Up] {
                for with_init in [false, true] {
                    same(
                        |r, u| {
                            let label = labelled.then_some(u.label);
                            let body = run(r, u, shape);
                            let init = with_init.then(|| r.int_literal(&mut u.b, 0));
                            let end = r.var(&mut u.b, u.x);
                            let range = Range { init, end, direction: direction as u16 };
                            done(r.for_range(&mut u.b, u.t, range, body, label));
                        },
                        |u| {
                            let label = labelled.then_some(u.label);
                            let body = run_today(u, shape);
                            let init = with_init.then(|| plain::int(&mut u.b, 0));
                            let end = var(&mut u.b, u.x);
                            let body = u.b.block_from_list(body);
                            let parts = [init.unwrap_or(end), end, body];
                            let parts = if with_init { &parts[..] } else { &parts[1..] };
                            built(u.b.new_node(View::SForRange { var: u.t, parts, label }, direction as u16));
                        },
                    );
                }
            }
        }
        for (caught, with_finaliser) in [(true, false), (true, true), (false, true)] {
            same(
                |r, u| {
                    let body = run(r, u, shape);
                    let handler = caught.then(|| (u.t, run(r, u, &[St::Call])));
                    let finaliser = with_finaliser.then(|| run(r, u, shape));
                    done(r.try_(&mut u.b, body, handler, finaliser));
                },
                |u| {
                    let body = run_today(u, shape);
                    let handler = caught.then(|| run_today(u, &[St::Call]));
                    let finaliser = with_finaliser.then(|| run_today(u, shape));
                    let mut parts = vec![u.b.block_from_list(body)];
                    for list in [handler, finaliser].into_iter().flatten() {
                        parts.push(u.b.block_from_list(list));
                    }
                    built(u.b.new_node(View::STry { parts: &parts, exception: caught.then_some(u.t) }, 0));
                },
            );
        }
        same(
            |r, u| {
                let body = run(r, u, shape);
                let function = r.function(&mut u.b, u.header, body);
                assert_eq!(r.function_of(&u.b, Rows::of(&function)), Some(u.header));
                assert!(r.has(&u.b, Rows::of(&function), crate::emit::row::flag::STRICT));
            },
            |u| {
                let body = run_today(u, shape);
                let body = u.b.block_from_list(body);
                built(crate::bir::j::pure_expression(&mut u.b, View::JFun { body, header: u.header }, 0));
            },
        );
    }
    // A switch of two actions (the key and the default), each a block.
    for string in [false, true] {
        same(
            |r, u| {
                let first = run(r, u, &[St::Call, St::Break]);
                let first = r.block_of(&mut u.b, first);
                let second = run(r, u, &[St::Return]);
                let second = r.block_of(&mut u.b, second);
                let actions = r.list(&mut u.b, 2, [first, second].into_iter());
                let scrutinee = r.var(&mut u.b, u.x);
                done(r.switch(&mut u.b, scrutinee, actions, u.switch, string));
            },
            |u| {
                let first = run_today(u, &[St::Call, St::Break]);
                let first = u.b.block_from_list(first);
                let second = run_today(u, &[St::Return]);
                let second = u.b.block_from_list(second);
                let actions = u.b.lists.push_iter(2, [first, second].into_iter());
                let scrutinee = var(&mut u.b, u.x);
                built(u.b.switch_from_list(scrutinee, actions, u.switch, u16::from(string)));
            },
        );
    }
}

/// The lowering builds some blocks from a slice of statements and not
/// from a pool list (`Bir::new_node`, `plain::node` or `plain::list` with
/// `View::SBlock { statements }`). They are the rows `block_of`,
/// `explicit_block` and `function` write for the list of the same
/// statements, so the interface needs no constructor that takes a slice.
#[test]
fn a_block_of_a_slice_is_the_block_of_its_list() {
    for shape in SHAPES {
        type Slice = fn(&mut Bir, &[NodeId]) -> NodeId;
        let slices: [Slice; 3] = [
            |b, statements| b.new_node(View::SBlock { statements }, 0),
            |b, statements| plain::node(b, View::SBlock { statements }, 0),
            plain::list,
        ];
        for slice in slices {
            same(
                |r, u| {
                    let list = run(r, u, shape);
                    done(r.block_of(&mut u.b, list));
                },
                |u| {
                    let statements: Vec<NodeId> = shape.iter().map(|&st| statement_today(u, st)).collect();
                    built(slice(&mut u.b, &statements));
                },
            );
        }
        same(
            |r, u| {
                let list = run(r, u, shape);
                done(r.explicit_block(&mut u.b, list));
            },
            |u| {
                let statements: Vec<NodeId> = shape.iter().map(|&st| statement_today(u, st)).collect();
                built(u.b.new_node(View::SBlock { statements: &statements }, 1));
            },
        );
        same(
            |r, u| {
                let list = run(r, u, shape);
                let function = r.function(&mut u.b, u.header, list);
                r.release(&mut u.b, function);
            },
            |u| {
                let statements: Vec<NodeId> = shape.iter().map(|&st| statement_today(u, st)).collect();
                let body = plain::node(&mut u.b, View::SBlock { statements: &statements }, 0);
                let function = crate::bir::j::pure_expression(&mut u.b, View::JFun { body, header: u.header }, 0);
                u.b.release(function);
            },
        );
    }
}

/// The values the statement rules treat differently: a variable, a
/// literal, a call, a negation, and commas of them.
#[derive(Clone, Copy, Debug)]
enum Value {
    X,
    Int,
    True,
    False,
    Undefined,
    Call,
    NotX,
    /// `(f(), x)`
    CallThenX,
    /// `(f(), f())`
    CallThenCall,
    /// `(1, f())`
    IntThenCall,
    /// `x.loop = 3`, then `undefined`: an assignment used for its effect.
    AssignThenUnit,
}

const VALUES: [Value; 11] = [
    Value::X,
    Value::Int,
    Value::True,
    Value::False,
    Value::Undefined,
    Value::Call,
    Value::NotX,
    Value::CallThenX,
    Value::CallThenCall,
    Value::IntThenCall,
    Value::AssignThenUnit,
];

fn value(r: &mut Rows, u: &mut Unit, value: Value) -> E {
    let a = &mut u.b;
    let call = |r: &mut Rows, a: &mut Bir| {
        let f = r.var(a, u.f);
        let mark = r.mark();
        r.call(a, f, mark, u.call)
    };
    match value {
        Value::X => r.var(a, u.x),
        Value::Int => r.int_literal(a, 1),
        Value::True => r.boolean(a, true),
        Value::False => r.boolean(a, false),
        Value::Undefined => r.undefined(a, false),
        Value::Call => call(r, a),
        Value::NotX => {
            let x = r.var(a, u.x);
            r.not(a, x)
        }
        Value::CallThenX => {
            let (first, second) = (call(r, a), r.var(a, u.x));
            r.seq(a, first, second)
        }
        Value::CallThenCall => {
            let (first, second) = (call(r, a), call(r, a));
            r.seq(a, first, second)
        }
        Value::IntThenCall => {
            let (first, second) = (r.int_literal(a, 1), call(r, a));
            r.seq(a, first, second)
        }
        Value::AssignThenUnit => {
            let x = r.var(a, u.x);
            let target = r.dot(a, x, u.label, crate::js_ir::arena::FieldPos::NONE, false);
            let three = r.int_literal(a, 3);
            let assignment = r.bin_plain(a, BinOp::Eq, target, three);
            let unit = r.undefined(a, false);
            r.seq(a, assignment, unit)
        }
    }
}

fn value_today(u: &mut Unit, value: Value) -> NodeId {
    let b = &mut u.b;
    let call = |b: &mut Bir| {
        let callee = var(b, u.f);
        plain::node(b, View::JCall { callee, args: &[], info: u.call }, 0)
    };
    match value {
        Value::X => var(b, u.x),
        Value::Int => plain::int(b, 1),
        Value::True => plain::boolean(b, true),
        Value::False => plain::boolean(b, false),
        Value::Undefined => plain::node(b, View::JUndefined, 0),
        Value::Call => call(b),
        Value::NotX => {
            let x = var(b, u.x);
            norm::je8_not(b, x)
        }
        Value::CallThenX => {
            let (first, second) = (call(b), var(b, u.x));
            plain::seq(b, first, second)
        }
        Value::CallThenCall => {
            let (first, second) = (call(b), call(b));
            plain::seq(b, first, second)
        }
        Value::IntThenCall => {
            let (first, second) = (plain::int(b, 1), call(b));
            plain::seq(b, first, second)
        }
        Value::AssignThenUnit => {
            let object = var(b, u.x);
            let position = crate::js_ir::arena::FieldPos::NONE;
            let target = plain::node(b, View::JDot { object, property: u.label, position }, 0);
            let three = plain::int(b, 3);
            let assignment = plain::bin(b, BinOp::Eq, target, three);
            let unit = plain::node(b, View::JUndefined, 0);
            plain::seq(b, assignment, unit)
        }
    }
}

#[test]
fn the_statement_rules_are_their_rows_of_section_6() {
    for operand in VALUES {
        // J-S1.
        same(
            |r, u| {
                let value = value(r, u, operand);
                done(r.exp_rule(&mut u.b, value));
            },
            |u| {
                let value = value_today(u, operand);
                built(norm::js1_exp(&mut u.b, value));
            },
        );
        // J-M14: the statements come in the rule's order, and as many.
        for if_impure in [false, true] {
            let (mut left, mut right) = (unit(), unit());
            let mut rows = Rows::default();
            let mut given = Vec::new();
            let e = value(&mut rows, &mut left, operand);
            if if_impure {
                rows.effect_if_impure(&mut left.b, e, |s| given.push(Rows::stmt_node(s)));
            } else {
                rows.effect(&mut left.b, e, |s| given.push(Rows::stmt_node(s)));
            }
            let mut today = Vec::new();
            let node = value_today(&mut right, operand);
            if if_impure {
                norm::jm14_push_s_if_empty(&mut right.b, node, &mut today);
            } else {
                norm::jm14_push_effect_expression(&mut right.b, node, &mut today);
            }
            assert_eq!(given, today, "{operand:?}, if_impure {if_impure}");
            assert_eq!(left.b.dump(), right.b.dump(), "{operand:?}, if_impure {if_impure}");
            // The rule gives its statements on as it makes them: the
            // operand stack is not used.
            assert_eq!((rows.mark().0, rows.operand_capacity()), (0, 0));
        }
        // J-S3, on every pair of branches.
        for yes in SHAPES {
            for no in SHAPES {
                let (mut left, mut right) = (unit(), unit());
                let mut rows = Rows::default();
                let (then_, else_) = (run(&mut rows, &mut left, yes), run(&mut rows, &mut left, no));
                let test = value(&mut rows, &mut left, operand);
                done(rows.if_(&mut left.b, test, then_, else_));
                let (then_, else_) = (run_today(&mut right, yes), run_today(&mut right, no));
                let test = value_today(&mut right, operand);
                built(norm::js3_simplify_if(&mut right.b, test, then_, else_));
                assert_eq!(left.b.dump(), right.b.dump(), "if ({operand:?}) {yes:?} else {no:?}");
            }
        }
    }
}

#[test]
fn a_reader_reads_the_statement_in_hand() {
    let mut u = unit();
    let mut r = Rows::default();
    // The value of a statement that has one is the expression given.
    let call = statement(&mut r, &mut u, St::Call);
    assert_eq!(r.stmt_kind(&u.b, &call), Kind::Exp);
    assert_eq!(r.value_of(&u.b, &call).map(|value| r.kind(&u.b, value)), Some(Kind::Call));
    let ret = statement(&mut r, &mut u, St::Return);
    assert_eq!(r.stmt_kind(&u.b, &ret), Kind::Return);
    assert_eq!(r.value_of(&u.b, &ret).and_then(|value| r.var_of(&u.b, value)), Some(u.y));
    let throw = statement(&mut r, &mut u, St::Throw);
    assert_eq!(r.stmt_kind(&u.b, &throw), Kind::Throw);
    assert_eq!(r.value_of(&u.b, &throw).and_then(|value| r.var_of(&u.b, value)), Some(u.x));
    let a = &mut u.b;
    let brk = r.break_(a, None);
    assert_eq!((r.stmt_kind(a, &brk), r.value_of(a, &brk).is_none()), (Kind::Break, true));
    let cont = r.continue_(a, Some(u.label));
    assert_eq!(r.stmt_kind(a, &cont), Kind::Continue);
    let debugger = r.debugger(a);
    assert_eq!(r.stmt_kind(a, &debugger), Kind::Debugger);
    // A declaration: its kind is its `aux`, its value is read when it has
    // one.
    let value = r.int_literal(a, 2);
    let declaration = r.declare(a, LetKind::Variable, u.t, Some(value));
    assert_eq!(r.stmt_kind(a, &declaration), Kind::Declare);
    assert_eq!(r.stmt_aux(a, &declaration), LetKind::Variable as u8);
    assert_eq!(r.value_of(a, &declaration).and_then(|value| r.int(a, value)), Some(2));
    let mut u = unit();
    let a = &mut u.b;
    let empty = r.declare(a, LetKind::Strict, u.t, None);
    assert_eq!((r.stmt_aux(a, &empty), r.value_of(a, &empty).is_none()), (LetKind::Strict as u8, true));
    // Compound statements: the kind, and the expression evaluated first.
    let none = r.list(a, 0, std::iter::empty());
    let block = r.block_of(a, none);
    assert_eq!((r.stmt_kind(a, &block), r.stmt_aux(a, &block)), (Kind::Block, 0));
    let none = r.list(a, 0, std::iter::empty());
    let explicit = r.explicit_block(a, none);
    assert_eq!((r.stmt_kind(a, &explicit), r.stmt_aux(a, &explicit)), (Kind::Block, 1));
    let (yes, no) = (r.list(a, 0, std::iter::empty()), r.list(a, 0, std::iter::empty()));
    let test = r.var(a, u.x);
    let branch = r.if_plain(a, test, yes, no);
    assert_eq!(r.stmt_kind(a, &branch), Kind::If);
    assert_eq!(r.value_of(a, &branch).and_then(|value| r.var_of(a, value)), Some(u.x));
    let body = r.list(a, 0, std::iter::empty());
    let condition = r.var(a, u.y);
    let looped = r.while_(a, condition, body, None);
    assert_eq!(r.stmt_kind(a, &looped), Kind::While);
    assert_eq!(r.value_of(a, &looped).and_then(|value| r.var_of(a, value)), Some(u.y));
    let body = r.list(a, 0, std::iter::empty());
    let iterable = r.var(a, u.x);
    let item = a.new_var_id(Name::new("item"), 5);
    let each = r.for_of(a, item, iterable, body, None, false);
    assert_eq!((r.stmt_kind(a, &each), r.value_of(a, &each).is_none()), (Kind::ForOf, true));
    let (body, finaliser) = (r.list(a, 0, std::iter::empty()), r.list(a, 0, std::iter::empty()));
    let guarded = r.try_(a, body, None, Some(finaliser));
    assert_eq!((r.stmt_kind(a, &guarded), r.value_of(a, &guarded).is_none()), (Kind::Try, true));
    for string in [false, true] {
        let actions = r.list(a, 0, std::iter::empty());
        let scrutinee = r.var(a, u.f);
        let switch = r.switch(a, scrutinee, actions, u.switch, string);
        assert_eq!((r.stmt_kind(a, &switch), r.stmt_aux(a, &switch)), (Kind::Switch, u8::from(string)));
        assert_eq!(r.value_of(a, &switch).and_then(|value| r.var_of(a, value)), Some(u.f));
    }
}

// ---- Functions the conversion slices T6m to T6q call ----

fn located_today(b: &mut Bir, statement: NodeId) {
    let comment = b.cold(statement).and_then(|cold| cold.comment);
    b.set_cold(statement, crate::bir::Cold { loc: crate::lambda::LamLoc::NONE, comment });
    let mut flags = b.node(statement).flags();
    flags.0 |= crate::bir::NodeFlags::JS_LOC_PRESENT;
    b.nodes[statement.index()].set_flags(flags);
}

#[test]
fn a_located_statement_is_the_row_the_lowering_writes_today() {
    for st in [St::Call, St::Throw] {
        same(
            |r, u| {
                let mut statement = statement(r, u, st);
                r.locate_stmt(&mut u.b, &mut statement, crate::lambda::LamLoc::NONE);
            },
            |u| {
                let statement = statement_today(u, st);
                located_today(&mut u.b, statement);
            },
        );
    }
}

#[test]
fn a_statement_says_whether_it_is_located() {
    let mut u = unit();
    let r = Rows::default();
    let node = statement_today(&mut u, St::Call);
    let statement = Rows::stmt_from_node(node);
    assert!(!r.stmt_located(&u.b, &statement));
    located_today(&mut u.b, node);
    assert!(r.stmt_located(&u.b, &statement));
}

#[test]
fn a_statement_gives_its_value_and_a_block_its_statements() {
    // `f();`, `return y;` and `throw x;` give their value and are released.
    for st in [St::Call, St::Return, St::Throw] {
        same(
            |r, u| {
                let statement = statement(r, u, st);
                let value = r.take_value(&mut u.b, statement);
                let kind = if matches!(st, St::Call) { Kind::Call } else { Kind::Var };
                assert_eq!(r.kind(&u.b, Rows::of(&value)), kind);
            },
            |u| {
                let statement = statement_today(u, st);
                let (View::SExp { value } | View::SReturn { value } | View::SThrow { value }) = u.b.view(statement)
                else {
                    unreachable!()
                };
                u.b.detach(value);
                u.b.release(statement);
            },
        );
    }
    // A block gives its statements in order, and they make an equal list.
    for shape in SHAPES {
        same(
            |r, u| {
                let list = run(r, u, shape);
                let block = r.block_of(&mut u.b, list);
                let steps = r.steps();
                let mut statements = Vec::new();
                r.unblock(&mut u.b, block, |s| statements.push(s));
                assert_eq!(statements.len(), shape.len());
                assert_eq!(r.steps() - steps, 1 + shape.len() as u64);
                assert_eq!(r.mark().0, 0);
                let again = r.list(&mut u.b, shape.len() as u32, statements.into_iter());
                done(r.explicit_block(&mut u.b, again));
            },
            |u| {
                let list = run_today(u, shape);
                let block = u.b.block_from_list(list);
                let View::SBlock { statements } = u.b.view(block) else { unreachable!() };
                let statements = statements.to_vec();
                for &statement in &statements {
                    u.b.detach(statement);
                }
                u.b.release(block);
                let again = u.b.lists.push_iter(statements.len(), statements.into_iter());
                built(u.b.explicit_block_from_list(again));
            },
        );
    }
}

/// A block of `width` statements `f();`.
fn wide(r: &mut Rows, u: &mut Unit, width: usize) -> S {
    let statements: Vec<S> = (0..width).map(|_| statement(r, u, St::Call)).collect();
    let list = r.list(&mut u.b, width as u32, statements.into_iter());
    r.block_of(&mut u.b, list)
}

/// `while (true) { f(); while (true) { ... } }`, `depth` loops deep.
fn nest(r: &mut Rows, u: &mut Unit, depth: usize) -> S {
    let mut inner = statement(r, u, St::Break);
    for _ in 0..depth {
        let call = statement(r, u, St::Call);
        let body = r.list(&mut u.b, 2, [call, inner].into_iter());
        let condition = r.boolean(&mut u.b, true);
        inner = r.while_(&mut u.b, condition, body, None);
    }
    inner
}

/// A list of `width` statements made, taken apart and made again.
fn remade(r: &mut Rows, u: &mut Unit, width: usize) -> S {
    let statements: Vec<S> = (0..width).map(|_| statement(r, u, St::Call)).collect();
    let list = r.list(&mut u.b, width as u32, statements.into_iter());
    let again: Vec<S> = (0..width).map(|index| r.take_at(&mut u.b, list, index as u32)).collect();
    let list = r.list(&mut u.b, width as u32, again.into_iter());
    r.block_of(&mut u.b, list)
}

/// The effect statements of a comma of `length` calls.
fn effects(r: &mut Rows, u: &mut Unit, length: usize) -> S {
    let mut chain = value(r, u, Value::Call);
    for _ in 1..length {
        let call = value(r, u, Value::Call);
        chain = r.seq(&mut u.b, call, chain);
    }
    let mut statements = Vec::with_capacity(length);
    r.effect(&mut u.b, chain, |s| statements.push(s));
    assert_eq!(statements.len(), length);
    let list = r.list(&mut u.b, length as u32, statements.into_iter());
    r.block_of(&mut u.b, list)
}

#[test]
fn ten_thousand_statements_cost_ten_times_a_thousand() {
    for build in [wide, nest, remade, effects] {
        let steps = |size: usize| {
            let mut u = unit();
            let mut r = Rows::default();
            done(build(&mut r, &mut u, size));
            r.steps()
        };
        let (one, two, ten) = (steps(1_000), steps(2_000), steps(10_000));
        // Exactly linear: the step from 1,000 to 2,000, nine times.
        assert_eq!(ten - one, 9 * (two - one), "{one} {two} {ten}");
        assert!(two > one);
    }
}

#[test]
fn rows_allocates_what_the_calls_of_today_allocate() {
    // A list and its block: the interface is the same two calls, so the
    // two sides allocate alike (the arena's vectors grow on both).
    for width in [1_000usize, 10_000] {
        let (mut left, mut right) = (unit(), unit());
        let mut rows = Rows::default();
        let statements: Vec<S> = (0..width).map(|_| statement(&mut rows, &mut left, St::Call)).collect();
        let nodes: Vec<NodeId> = (0..width).map(|_| statement_today(&mut right, St::Call)).collect();
        let through = allocation_counter::measure(|| {
            let list = rows.list(&mut left.b, width as u32, statements.into_iter());
            done(rows.block_of(&mut left.b, list));
        })
        .count_total;
        let direct = allocation_counter::measure(|| {
            let list = right.b.lists.push_iter(width, nodes.into_iter());
            built(right.b.block_from_list(list));
        })
        .count_total;
        assert_eq!(through, direct, "width {width}");
    }
    // J-M14 through the interface collects nothing: it allocates less than
    // with the vector the rule is lent elsewhere, taken empty, and the
    // operand stack of a `Rows` that reserved nothing stays empty.
    for length in [1_000usize, 10_000] {
        let (mut left, mut right) = (unit(), unit());
        let mut rows = Rows::default();
        let mut chain = value(&mut rows, &mut left, Value::Call);
        let mut chain_today = value_today(&mut right, Value::Call);
        for _ in 1..length {
            let call = value(&mut rows, &mut left, Value::Call);
            chain = rows.seq(&mut left.b, call, chain);
            let call = value_today(&mut right, Value::Call);
            chain_today = plain::seq(&mut right.b, call, chain_today);
        }
        let mut count = 0;
        let through = allocation_counter::measure(|| rows.effect(&mut left.b, chain, |_| count += 1)).count_total;
        let direct = allocation_counter::measure(|| {
            let mut statements = Vec::new();
            norm::jm14_push_effect_expression(&mut right.b, chain_today, &mut statements);
            assert_eq!(statements.len(), length);
        })
        .count_total;
        assert_eq!(count, length);
        assert!(through < direct, "length {length}: {through} through the interface, {direct} direct");
        assert_eq!(rows.operand_capacity(), 0);
    }
    // A block of any width gives its statements back without storage.
    for width in [1_000usize, 10_000] {
        let mut u = unit();
        let mut rows = Rows::default();
        let statements: Vec<S> = (0..width).map(|_| statement(&mut rows, &mut u, St::Call)).collect();
        let list = rows.list(&mut u.b, width as u32, statements.into_iter());
        let block = rows.block_of(&mut u.b, list);
        let mut count = 0;
        let before = rows.steps();
        rows.unblock(&mut u.b, block, |_| count += 1);
        assert_eq!((count, rows.operand_capacity()), (width, 0), "width {width}");
        assert_eq!(rows.steps() - before, 1 + width as u64);
    }
}

#[test]
fn a_guard_is_taken_apart_and_rebuilt_over_its_blocks() {
    // `if (x) { ...; jump }` followed by other statements becomes
    // `{ if (x) { ...; jump } else { the others } }`, as
    // `cond.rs::merge_tail_guard` writes it today.
    for guard in [&[St::Return][..], &[St::Call, St::Throw], &[St::Break]] {
        for rest in SHAPES {
            same(
                |r, u| {
                    let (yes, no) = (run(r, u, guard), run(r, u, &[]));
                    let test = r.var(&mut u.b, u.x);
                    let statement = r.if_plain(&mut u.b, test, yes, no);
                    assert_eq!(r.stmt_kind(&u.b, &statement), Kind::If);
                    assert!(!r.is_empty_block(&u.b, &statement));
                    let last = match guard[guard.len() - 1] {
                        St::Return => Kind::Return,
                        St::Throw => Kind::Throw,
                        St::Break => Kind::Break,
                        St::Call => Kind::Exp,
                    };
                    assert_eq!(r.branch_last_kind(&u.b, &statement, false), Some(last));
                    assert_eq!(r.branch_last_kind(&u.b, &statement, true), None);
                    let before = r.steps();
                    let (test, then_, else_) = r.take_if(&mut u.b, statement);
                    assert_eq!(r.steps() - before, 1);
                    let empty = else_.expect("built with an else");
                    assert!(r.is_empty_block(&u.b, &empty));
                    r.release_stmt(&mut u.b, empty);
                    let rest = run(r, u, rest);
                    let else_ = r.block_of(&mut u.b, rest);
                    let statement = r.if_blocks(&mut u.b, test, then_, else_);
                    let one = r.list(&mut u.b, 1, std::iter::once(statement));
                    done(r.block_of(&mut u.b, one));
                },
                |u| {
                    let (yes, no) = (run_today(u, guard), run_today(u, &[]));
                    let condition = var(&mut u.b, u.x);
                    let then_ = u.b.block_from_list(yes);
                    let else_ = u.b.block_from_list(no);
                    let statement = u.b.new_node(View::SIf { condition, then_, else_: Some(else_) }, 0);
                    u.b.detach(condition);
                    u.b.detach(then_);
                    u.b.release(statement);
                    let rest = run_today(u, rest);
                    let else_ = u.b.block_from_list(rest);
                    let statement = u.b.new_node(View::SIf { condition, then_, else_: Some(else_) }, 0);
                    built(u.b.new_node(View::SBlock { statements: &[statement] }, 0));
                },
            );
        }
    }
}

#[test]
fn an_if_without_an_else_has_no_last_statement_there() {
    let mut u = unit();
    let r = Rows::default();
    let condition = var(&mut u.b, u.x);
    let body = run_today(&mut u, &[St::Call, St::Return]);
    let then_ = u.b.block_from_list(body);
    let statement = Rows::stmt_from_node(u.b.new_node(View::SIf { condition, then_, else_: None }, 0));
    assert_eq!(r.branch_last_kind(&u.b, &statement, true), None);
    assert_eq!(r.branch_last_kind(&u.b, &statement, false), Some(Kind::Return));
}

#[test]
fn a_function_over_a_block_is_the_function_over_its_list() {
    for shape in SHAPES {
        same(
            |r, u| {
                let body = run(r, u, shape);
                let body = r.block_of(&mut u.b, body);
                let function = r.function_of_block(&mut u.b, u.header, body);
                assert!(r.has(&u.b, Rows::of(&function), crate::emit::row::flag::STRICT));
            },
            |u| {
                let body = run_today(u, shape);
                let body = u.b.block_from_list(body);
                built(crate::bir::j::pure_expression(&mut u.b, View::JFun { body, header: u.header }, 0));
            },
        );
    }
}

#[test]
fn releasing_a_statement_costs_one_step_per_node() {
    let steps = |size: usize| {
        let mut u = unit();
        let mut r = Rows::default();
        let statement = nest(&mut r, &mut u, size);
        let live = u.b.nodes.len();
        let before = r.steps();
        r.release_stmt(&mut u.b, statement);
        let steps = r.steps() - before;
        assert!(steps as usize >= size && steps as usize <= live);
        steps
    };
    let (one, two, ten) = (steps(1_000), steps(2_000), steps(10_000));
    assert_eq!(ten - one, 9 * (two - one), "{one} {two} {ten}");
}

#[test]
fn a_copy_is_the_copy_the_lowering_makes_today_and_reports_its_binders() {
    // A block of `let t = x;` and a run: the binder is fresh in the copy.
    for shape in SHAPES {
        let (mut left, mut right) = (unit(), unit());
        let mut r = Rows::default();
        let x = r.var(&mut left.b, left.x);
        let declaration = r.declare(&mut left.b, LetKind::Strict, left.t, Some(x));
        let rest: Vec<S> = shape.iter().map(|&st| statement(&mut r, &mut left, st)).collect();
        let list = r.list(&mut left.b, 1 + shape.len() as u32, std::iter::once(declaration).chain(rest));
        let block = r.block_of(&mut left.b, list);
        let mut fresh = Vec::new();
        done(r.copy_stmt(&mut left.b, &block, &mut fresh));
        assert_eq!(fresh.len(), 1);
        assert_eq!(fresh[0].1, left.t);

        let b = &mut right.b;
        let value = var(b, right.x);
        let declaration = crate::bir::j::declare(b, LetKind::Strict, right.t, value);
        let mut statements = vec![declaration];
        statements.extend(shape.iter().map(|&st| statement_today(&mut right, st)));
        let b = &mut right.b;
        let list = b.lists.push_iter(statements.len(), statements.into_iter());
        let block = b.block_from_list(list);
        let (mut vars, mut labels) = (Vec::new(), Vec::new());
        built(b.copy_subtree_recording(block, &[], &mut vars, &mut labels));
        assert_eq!(vars, fresh);
        assert_eq!(left.b.dump(), right.b.dump());
    }
    // The copy of an expression reports alike.
    let mut u = unit();
    let mut r = Rows::default();
    let body = run(&mut r, &mut u, &[St::Return]);
    let function = r.function(&mut u.b, u.header, body);
    let mut fresh = Vec::new();
    let copy = r.copy_fresh(&mut u.b, Rows::of(&function), &mut fresh);
    assert_eq!(r.kind(&u.b, Rows::of(&copy)), Kind::Fun);
    assert!(fresh.is_empty());
}

#[test]
fn a_copy_costs_one_step_per_node_and_allocates_nothing_in_a_warm_unit() {
    let measure = |size: usize| {
        let mut u = unit();
        let mut r = Rows::default();
        let statement = nest(&mut r, &mut u, size);
        let mut fresh = Vec::new();
        // The first copy sizes the arena and the copy storage.
        let lists_before = u.b.lists.storage_shape().0;
        let warm = r.copy_stmt(&mut u.b, &statement, &mut fresh);
        let growth = u.b.lists.storage_shape().0 - lists_before;
        r.release_stmt(&mut u.b, warm);
        u.b.lists.reserve_test_growth(growth);
        r.reserve_copy(&u.b);
        u.b.js_scope.as_mut().expect("the unit counts occurrences").reserve_repeat();
        let capacities = r.copy_capacities();
        let caps = |b: &Bir| [b.nodes.capacity(), b.lists.storage_shape().1, b.pools.js.capacity(), b.release_stack.capacity(), b.free_nodes.capacity(), b.parents.capacity(), b.vars.name.capacity()];
        let caps_before = caps(&u.b);
        let before = r.steps();
        let mut copy = None;
        let allocations = allocation_counter::measure(|| copy = Some(r.copy_stmt(&mut u.b, &statement, &mut fresh)));
        let steps = r.steps() - before;
        assert_eq!(caps(&u.b), caps_before);
        assert_eq!(allocations.count_total, 0, "size {size}");
        assert_eq!(r.copy_capacities(), capacities);
        assert!(fresh.is_empty());
        // One step per node: releasing the copy counts the same nodes.
        let before = r.steps();
        r.release_stmt(&mut u.b, copy.expect("the copy"));
        assert_eq!(r.steps() - before, steps);
        assert!(steps as usize >= size);
        steps
    };
    let (one, two, ten) = (measure(1_000), measure(2_000), measure(10_000));
    assert_eq!(ten - one, 9 * (two - one), "{one} {two} {ten}");
}
