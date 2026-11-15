//! Acceptance tests of the lowering's interface on J rows (THREE_TREES
//! 11.4, "T6: the interface"; slice T6k).
//!
//! The oracle form: the same nodes are built twice in two arenas that start
//! equal, once through [`Js`] on [`Rows`] and once with the calls of
//! `bir/j/plain.rs` and `bir/j/norm.rs` the lowering makes today. The two
//! arenas must then dump alike (`Bir::dump`: every node with its operation,
//! `aux`, flags and operands, every variable with its uses). No expected
//! row is written down.
use super::{Js, Mark};
use crate::bir::j::rows::{E, Rows};
use crate::bir::j::{norm, plain};
use crate::bir::lower::scope::Scope;
use crate::bir::{Bir, Constant, JsId, JsPayload, NodeFlags, NodeId, PropertyKey, StrId, VarId, View};
use crate::emit::row::{Kind, flag};
use crate::js_ir::BinOp;
use crate::js_ir::arena::FieldPos;
use crate::js_ir::op::LengthObject;
use crate::name::Name;

/// What both sides of a comparison start from: an arena that counts
/// JavaScript occurrences, three variables, two interned names, a constant
/// of each number class and the `JsId` of a call, of an object with two
/// keys and of a block.
struct Unit {
    b: Bir,
    x: VarId,
    y: VarId,
    f: VarId,
    name: StrId,
    other: StrId,
    float: crate::bir::ConstId,
    bigint: crate::bir::ConstId,
    call: JsId,
    keys: JsId,
    tuple: JsId,
}

fn unit() -> Unit {
    let mut b = Bir::default();
    b.begin_bulk();
    b.js_scope = Some(Scope::new(0));
    let x = b.new_var_id(Name::new("x"), 1);
    let y = b.new_var_id(Name::new("y"), 2);
    let f = b.new_var_id(Name::new("f"), 3);
    let name = b.intern_text("name");
    let other = b.intern_text("other");
    let float = b.intern_float("1.5").unwrap();
    let digits = b.intern_text("+12");
    let bigint = b.intern_const(Constant::BigInt(digits));
    let call = b.js_info(JsPayload::Call(Default::default()));
    let keys = b.object_info(&[PropertyKey::Literal(name), PropertyKey::Literal(other)]);
    let tuple = b.block_info(&crate::lambda::TagInfo::Tuple);
    Unit { b, x, y, f, name, other, float, bigint, call, keys, tuple }
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

/// A node of today's side that the comparison reads in the arena's dump.
fn built(_: NodeId) {}

/// A handle that is not attached: the comparison reads its node in the
/// arena's dump.
fn done(_: E) {}

fn var(b: &mut Bir, var: VarId) -> NodeId {
    plain::node(b, View::Var { var }, 0)
}

#[test]
fn sizes() {
    assert_eq!(std::mem::size_of::<E>(), 4);
    assert_eq!(std::mem::size_of::<Option<E>>(), 8);
    assert_eq!(std::mem::size_of::<Mark>(), 4);
    // The operand stack (24), the step count (8), the copy storage (336)
    // and the label vector (24): one per unit, never passed down a walk.
    assert_eq!(std::mem::size_of::<Rows>(), 392);
    assert_eq!(std::mem::size_of::<<Rows as Js>::Ref<'_>>(), 4);
}

/// A handle is consumed by the function it is given to: nothing can copy
/// it. Compiles only while `E` is not `Copy` (two candidate impls would
/// make the call ambiguous).
#[test]
fn a_handle_is_not_copy() {
    trait NotCopy<A> {
        fn check() {}
    }
    impl<T> NotCopy<()> for T {}
    impl<T: Copy> NotCopy<u8> for T {}
    <E as NotCopy<_>>::check();
}

#[test]
fn the_flags_the_interface_reads_are_distinct_bits() {
    let flags = [
        flag::PURE,
        flag::STRICT,
        flag::DELAY_SAFE,
        flag::SUBEXPR,
        flag::DUPLICABLE,
        flag::HAS_FUN,
        flag::SEAL,
        flag::JSX,
        flag::HAS_GLOBAL,
    ];
    assert_eq!(flags.iter().fold(0, |all, f| all | f).count_ones() as usize, flags.len());
    assert_eq!(Kind::ALL.len(), 53);
}

#[test]
fn every_j_operation_has_a_kind_of_its_own() {
    use crate::bir::Op;
    let operations = [
        Op::Var, Op::JBin, Op::JNot, Op::JBnot, Op::JTypeof, Op::JIn, Op::JCond, Op::JSeq, Op::JCall,
        Op::JFlatCall, Op::JNew, Op::JIndex, Op::JDot, Op::JLength, Op::JIsNullish, Op::JStrAppend,
        Op::JFun, Op::JObject, Op::JArray, Op::JBlockLit, Op::JOptional, Op::JJsx, Op::JTemplate,
        Op::JTagged, Op::JRaw, Op::JAwait, Op::JSpread, Op::JQualified, Op::JNumber, Op::JStr,
        Op::JBool, Op::JNull, Op::JUndefined, Op::JJson, Op::JRecordRest, Op::SBlock, Op::SDecl,
        Op::SExp, Op::SIf, Op::SWhile, Op::SForRangeExisting, Op::SForRange, Op::SForOf,
        Op::SForAwaitOf, Op::SSwitch, Op::SReturn, Op::SThrow, Op::STry, Op::SBreak, Op::SContinue,
        Op::SDebugger, Op::SRest,
    ];
    let mut seen = 0u64;
    for operation in operations {
        let kind = crate::bir::j::rows::kind_of(operation);
        // `Named` is the builder's: no J operation is one.
        assert_ne!(kind, Kind::Named);
        assert_eq!(seen & (1 << kind as u64), 0, "{operation:?} shares {kind:?}");
        seen |= 1 << kind as u64;
    }
    assert_eq!(seen.count_ones() as usize, Kind::ALL.len() - 1);
}

#[test]
fn a_leaf_is_the_row_the_lowering_writes_today() {
    same(|r, u| done(r.var(&mut u.b, u.x)), |u| built(var(&mut u.b, u.x)));
    same(|r, u| done(r.int_literal(&mut u.b, -7)), |u| built(plain::int(&mut u.b, -7)));
    same(
        |r, u| done(r.number(&mut u.b, u.float)),
        |u| built(plain::node(&mut u.b, View::JNumber { value: u.float }, 0)),
    );
    same(|r, u| done(r.string(&mut u.b, "text")), |u| built(plain::string(&mut u.b, "text")));
    same(
        |r, u| done(r.str(&mut u.b, u.name)),
        |u| built(plain::node(&mut u.b, View::JStr { text: u.name }, 0)),
    );
    for value in [false, true] {
        same(|r, u| done(r.boolean(&mut u.b, value)), |u| built(plain::boolean(&mut u.b, value)));
        same(
            |r, u| done(r.undefined(&mut u.b, value)),
            |u| built(plain::node(&mut u.b, View::JUndefined, u16::from(value))),
        );
        same(
            |r, u| done(r.raw(&mut u.b, u.name, value)),
            |u| built(plain::node(&mut u.b, View::JRaw { text: u.name }, u16::from(value))),
        );
    }
    same(|r, u| done(r.null(&mut u.b)), |u| built(plain::node(&mut u.b, View::JNull, 0)));
    // The lowering makes most leaves with `bir::j::pure_expression`, which
    // sets `STRICT` after the node is built: a leaf has it already, so the
    // interface needs one function per leaf and no second family.
    let strict = crate::bir::j::pure_expression;
    same(|r, u| done(r.var(&mut u.b, u.x)), |u| built(strict(&mut u.b, View::Var { var: u.x }, 0)));
    same(|r, u| done(r.null(&mut u.b)), |u| built(strict(&mut u.b, View::JNull, 0)));
    same(|r, u| done(r.undefined(&mut u.b, true)), |u| built(strict(&mut u.b, View::JUndefined, 1)));
    same(|r, u| done(r.boolean(&mut u.b, true)), |u| built(strict(&mut u.b, View::JBool, 1)));
    same(|r, u| done(r.str(&mut u.b, u.name)), |u| built(strict(&mut u.b, View::JStr { text: u.name }, 0)));
    same(
        |r, u| done(r.number(&mut u.b, u.float)),
        |u| built(strict(&mut u.b, View::JNumber { value: u.float }, 0)),
    );
    same(
        |r, u| done(r.json(&mut u.b, u.name)),
        |u| built(plain::node(&mut u.b, View::JJson { text: u.name }, 0)),
    );
}

#[test]
fn a_plain_function_builds_the_node_it_is_asked_for() {
    same(
        |r, u| {
            // `1 + 2` stays a sum: no rule runs.
            let (l, right) = (r.int_literal(&mut u.b, 1), r.int_literal(&mut u.b, 2));
            done(r.bin_plain(&mut u.b, BinOp::Plus, l, right));
        },
        |u| {
            let (l, r) = (plain::int(&mut u.b, 1), plain::int(&mut u.b, 2));
            built(plain::bin(&mut u.b, BinOp::Plus, l, r));
        },
    );
    same(
        |r, u| {
            let (x, y) = (r.var(&mut u.b, u.x), r.undefined(&mut u.b, true));
            done(r.seq(&mut u.b, x, y));
        },
        |u| {
            let x = var(&mut u.b, u.x);
            let y = plain::node(&mut u.b, View::JUndefined, 1);
            built(plain::seq(&mut u.b, x, y));
        },
    );
    same(
        |r, u| {
            let x = r.string(&mut u.b, "s");
            done(r.typeof_plain(&mut u.b, x));
        },
        |u| {
            let value = plain::string(&mut u.b, "s");
            built(plain::node(&mut u.b, View::JTypeof { value }, 0));
        },
    );
    same(
        |r, u| {
            let (x, y) = (r.var(&mut u.b, u.x), r.var(&mut u.b, u.y));
            let i = r.index(&mut u.b, x, y);
            let z = r.var(&mut u.b, u.f);
            done(r.in_(&mut u.b, i, z));
        },
        |u| {
            let (object, index) = (var(&mut u.b, u.x), var(&mut u.b, u.y));
            let left = plain::node(&mut u.b, View::JIndex { object, index }, 0);
            let right = var(&mut u.b, u.f);
            built(plain::node(&mut u.b, View::JIn { left, right }, 0));
        },
    );
    for (position, tag) in [(FieldPos::NONE, false), (FieldPos::new(Some(1)), false), (FieldPos::NONE, true)] {
        same(
            |r, u| {
                let x = r.var(&mut u.b, u.x);
                done(r.dot(&mut u.b, x, u.name, position, tag));
            },
            |u| {
                let object = var(&mut u.b, u.x);
                built(plain::node(&mut u.b, View::JDot { object, property: u.name, position }, u16::from(tag)));
            },
        );
    }
    for identity in [false, true] {
        same(
            |r, u| {
                let x = r.var(&mut u.b, u.x);
                let awaited = r.await_(&mut u.b, x);
                let spread = r.spread(&mut u.b, awaited);
                done(r.optional(&mut u.b, spread, identity));
            },
            |u| {
                let value = var(&mut u.b, u.x);
                let value = plain::node(&mut u.b, View::JAwait { value }, 0);
                let value = plain::node(&mut u.b, View::JSpread { value }, 0);
                built(plain::node(&mut u.b, View::JOptional { value }, u16::from(identity)));
            },
        );
    }
    same(
        |r, u| {
            let (f, x) = (r.var(&mut u.b, u.f), r.var(&mut u.b, u.x));
            done(r.flat_call(&mut u.b, f, x));
        },
        |u| {
            let (callee, args) = (var(&mut u.b, u.f), var(&mut u.b, u.x));
            built(plain::node(&mut u.b, View::JFlatCall { callee, args }, 0));
        },
    );
}

#[test]
fn a_list_constructor_takes_the_operands_since_its_mark() {
    // An outer list is being collected while an inner one is built: the
    // inner constructor takes only its own operands.
    same(
        |r, u| {
            let f = r.var(&mut u.b, u.f);
            let outer = r.mark();
            let x = r.var(&mut u.b, u.x);
            r.push(x);
            let inner = r.mark();
            for value in [1, 2] {
                let item = r.int_literal(&mut u.b, value);
                r.push(item);
            }
            let array = r.array(&mut u.b, inner, 1);
            r.push(array);
            assert_eq!(r.mark(), Mark(outer.0 + 2));
            done(r.call(&mut u.b, f, outer, u.call));
            assert_eq!(r.mark(), outer);
        },
        |u| {
            let callee = var(&mut u.b, u.f);
            let x = var(&mut u.b, u.x);
            let items = [plain::int(&mut u.b, 1), plain::int(&mut u.b, 2)];
            let array = plain::node(&mut u.b, View::JArray { values: &items }, 1);
            built(plain::node(&mut u.b, View::JCall { callee, args: &[x, array], info: u.call }, 0));
        },
    );
    same(
        |r, u| {
            let f = r.var(&mut u.b, u.f);
            let mark = r.mark();
            let x = r.var(&mut u.b, u.x);
            r.push(x);
            done(r.new_(&mut u.b, f, mark));
        },
        |u| {
            let callee = var(&mut u.b, u.f);
            let x = var(&mut u.b, u.x);
            // As `external.rs` builds it today: `aux` 1, the argument
            // list is present (`new F()`, not `new F`).
            let args = u.b.lists.push(&[x]);
            built(u.b.call_from_list(callee, args, None));
        },
    );
    for mutability in [0, 1] {
        same(
            |r, u| {
                let mark = r.mark();
                for variable in [u.x, u.y] {
                    let value = r.var(&mut u.b, variable);
                    r.push(value);
                }
                let block = r.block(&mut u.b, mark, u.tuple, mutability);
                let mark = r.mark();
                r.push(block);
                let one = r.int_literal(&mut u.b, 1);
                r.push(one);
                done(r.object(&mut u.b, mark, u.keys));
            },
            |u| {
                let values = [var(&mut u.b, u.x), var(&mut u.b, u.y)];
                let block = plain::node(&mut u.b, View::JBlockLit { values: &values, info: u.tuple }, mutability.into());
                let one = plain::int(&mut u.b, 1);
                built(plain::node(&mut u.b, View::JObject { values: &[block, one], info: u.keys }, 0));
            },
        );
    }
}

/// The descriptors of a tagged template with one value and of a record
/// rest without fields.
fn descriptors(u: &mut Unit) -> (JsId, JsId) {
    let start = u.b.pools.template_parts.len() as u32;
    for raw in [u.name, u.other] {
        u.b.pools.template_parts.push(crate::bir::TemplatePart { raw, cooked: None });
    }
    let tagged = u.b.js_info(JsPayload::Tagged(crate::bir::TemplateSpan { start, len: 2 }));
    (tagged, u.b.rest_info(std::iter::empty()))
}

#[test]
fn the_constructors_with_a_descriptor_keep_it() {
    // A tagged template and a record rest.
    same(
        |r, u| {
            let (template, fields) = descriptors(u);
            let f = r.var(&mut u.b, u.f);
            let mark = r.mark();
            let x = r.var(&mut u.b, u.x);
            r.push(x);
            let tagged = r.tagged(&mut u.b, f, mark, template);
            assert_eq!((r.kind(&u.b, Rows::of(&tagged)), r.info_of(&u.b, Rows::of(&tagged))), (Kind::Tagged, Some(template)));
            let y = r.var(&mut u.b, u.y);
            let rest = r.record_rest(&mut u.b, y, fields);
            assert_eq!((r.kind(&u.b, Rows::of(&rest)), r.info_of(&u.b, Rows::of(&rest))), (Kind::RecordRest, Some(fields)));
        },
        |u| {
            let (template, fields) = descriptors(u);
            let tag = var(&mut u.b, u.f);
            let x = var(&mut u.b, u.x);
            built(plain::node(&mut u.b, View::JTagged { tag, values: &[x], info: template }, 0));
            let value = var(&mut u.b, u.y);
            built(plain::node(&mut u.b, View::JRecordRest { value, info: fields }, 0));
        },
    );
    // A JSX element: the descriptor and the children bit.
    for has_children in [false, true] {
        same(
            |r, u| {
                let info = u.b.js_info(JsPayload::Jsx(Default::default()));
                let mark = r.mark();
                for variable in [u.f, u.x] {
                    let value = r.var(&mut u.b, variable);
                    r.push(value);
                }
                let jsx = r.jsx(&mut u.b, mark, info, has_children);
                assert_eq!((r.kind(&u.b, Rows::of(&jsx)), r.aux(&u.b, Rows::of(&jsx))), (Kind::Jsx, u8::from(has_children)));
            },
            |u| {
                let info = u.b.js_info(JsPayload::Jsx(Default::default()));
                let values = [var(&mut u.b, u.f), var(&mut u.b, u.x)];
                built(plain::node(&mut u.b, View::JJsx { values: &values, info }, u16::from(has_children)));
            },
        );
    }
    // J-M12: a literal value is merged into its neighbours, a variable is
    // kept.
    let segments = || {
        [
            crate::string_literal::template_from_semantic("a"),
            crate::string_literal::template_from_semantic("b"),
            crate::string_literal::template_from_semantic("c"),
        ]
    };
    same(
        |r, u| {
            let mark = r.mark();
            let text = r.string(&mut u.b, "s");
            r.push(text);
            let x = r.var(&mut u.b, u.x);
            r.push(x);
            let template = r.template(&mut u.b, &segments(), mark);
            assert_eq!(r.kind(&u.b, Rows::of(&template)), Kind::Template);
            assert_eq!(r.mark(), mark);
        },
        |u| {
            let values = vec![plain::string(&mut u.b, "s"), var(&mut u.b, u.x)];
            built(norm::jm12_interpolated_template(&mut u.b, segments(), values));
        },
    );
}

/// One rule function and the function of `norm.rs` it stands for, on two
/// operands.
type Binary = (fn(&mut Rows, &mut Bir, E, E) -> E, fn(&mut Bir, NodeId, NodeId) -> NodeId);
/// The same for one operand.
type Unary = (fn(&mut Rows, &mut Bir, E) -> E, fn(&mut Bir, NodeId) -> NodeId);

/// Operands the rules of section 6 treat differently: literals that fold,
/// a variable, a variable twice, a sum.
#[derive(Clone, Copy, Debug)]
enum Operand {
    Int(i32),
    Str(&'static str),
    Bool(bool),
    Null,
    Undefined,
    X,
    Y,
    Sum,
}

const OPERANDS: [Operand; 11] = [
    Operand::Int(0),
    Operand::Int(1),
    Operand::Int(-8),
    Operand::Str(""),
    Operand::Str("s"),
    Operand::Bool(true),
    Operand::Null,
    Operand::Undefined,
    Operand::X,
    Operand::Y,
    Operand::Sum,
];

fn operand_today(u: &mut Unit, operand: Operand) -> NodeId {
    match operand {
        Operand::Int(value) => plain::int(&mut u.b, value),
        Operand::Str(text) => plain::string(&mut u.b, text),
        Operand::Bool(value) => plain::boolean(&mut u.b, value),
        Operand::Null => plain::node(&mut u.b, View::JNull, 0),
        Operand::Undefined => plain::node(&mut u.b, View::JUndefined, 0),
        Operand::X => var(&mut u.b, u.x),
        Operand::Y => var(&mut u.b, u.y),
        Operand::Sum => {
            let (l, r) = (var(&mut u.b, u.x), plain::int(&mut u.b, 1));
            plain::bin(&mut u.b, BinOp::Plus, l, r)
        }
    }
}

fn operand(r: &mut Rows, u: &mut Unit, operand: Operand) -> E {
    match operand {
        Operand::Int(value) => r.int_literal(&mut u.b, value),
        Operand::Str(text) => r.string(&mut u.b, text),
        Operand::Bool(value) => r.boolean(&mut u.b, value),
        Operand::Null => r.null(&mut u.b),
        Operand::Undefined => r.undefined(&mut u.b, false),
        Operand::X => r.var(&mut u.b, u.x),
        Operand::Y => r.var(&mut u.b, u.y),
        Operand::Sum => {
            let (l, right) = (r.var(&mut u.b, u.x), r.int_literal(&mut u.b, 1));
            r.bin_plain(&mut u.b, BinOp::Plus, l, right)
        }
    }
}

#[test]
fn a_rule_function_is_its_row_of_section_6() {
    let binary: [Binary; 22] = [
        (|r, a, x, y| r.append(a, x, y), norm::je1_string_append),
        (|r, a, x, y| r.and(a, x, y), norm::je5_js_and),
        (|r, a, x, y| r.or(a, x, y), norm::je6_js_or),
        (|r, a, x, y| r.seq_rule(a, x, y), norm::jm1_js_seq),
        (|r, a, x, y| r.nullish_eq(a, false, x, y), |a, x, y| norm::jm2_nullish_strict_comparison(a, false, x, y)),
        (|r, a, x, y| r.nullish_eq(a, true, x, y), |a, x, y| norm::jm2_nullish_strict_comparison(a, true, x, y)),
        (|r, a, x, y| r.int_eq(a, x, y), norm::jm2_int_equality),
        (|r, a, x, y| r.int_or(a, x, y), norm::jm3_int32_bor),
        (|r, a, x, y| r.int_add(a, false, x, y), |a, x, y| norm::jm4_int32_add_sub(a, false, x, y)),
        (|r, a, x, y| r.int_add(a, true, x, y), |a, x, y| norm::jm4_int32_add_sub(a, true, x, y)),
        (|r, a, x, y| r.int_mul(a, x, y), norm::jm5_int32_mul),
        (|r, a, x, y| r.int_pow(a, x, y), norm::jm6_int32_pow),
        (|r, a, x, y| r.int_lsl(a, x, y), norm::jm7_int32_lsl),
        (|r, a, x, y| r.int_lsr(a, x, y), norm::jm8_int32_lsr),
        (|r, a, x, y| r.int_xor(a, x, y), norm::jm8_int32_bxor),
        (|r, a, x, y| r.int_and(a, x, y), norm::jm8_int32_band),
        (|r, a, x, y| r.int_div(a, true, x, y), |a, x, y| norm::jm13_int32_div(a, true, x, y)),
        (|r, a, x, y| r.int_div(a, false, x, y), |a, x, y| norm::jm13_int32_div(a, false, x, y)),
        (|r, a, x, y| r.int_mod(a, true, x, y), |a, x, y| norm::jm13_int32_mod(a, true, x, y)),
        (|r, a, x, y| r.bin(a, BinOp::EqEqEq, x, y), |a, x, y| norm::je4_bin(a, BinOp::EqEqEq, x, y)),
        (|r, a, x, y| r.bin(a, BinOp::Plus, x, y), |a, x, y| norm::je4_bin(a, BinOp::Plus, x, y)),
        (|r, a, x, y| r.bin(a, BinOp::Lt, x, y), |a, x, y| norm::je4_bin(a, BinOp::Lt, x, y)),
    ];
    for (index, (interface, today)) in binary.iter().enumerate() {
        for left in OPERANDS {
            for right in OPERANDS {
                // A shift by a negative literal count is no input of the
                // rules (`jm8_int32_lsr` folds with `>>`, which overflows
                // in a debug build).
                if matches!(index, 12 | 13) && matches!(right, Operand::Int(count) if count < 0) {
                    continue;
                }
                let (mut l, mut t) = (unit(), unit());
                let mut rows = Rows::default();
                let (x, y) = (operand(&mut rows, &mut l, left), operand(&mut rows, &mut l, right));
                done(interface(&mut rows, &mut l.b, x, y));
                let (x, y) = (operand_today(&mut t, left), operand_today(&mut t, right));
                today(&mut t.b, x, y);
                assert_eq!(l.b.dump(), t.b.dump(), "rule {index} on {left:?} and {right:?}");
            }
        }
    }
    let unary: [Unary; 10] = [
        (|r, a, x| r.not(a, x), norm::je8_not),
        (|r, a, x| r.is_nullish(a, x), norm::je3_is_null_or_undefined),
        (|r, a, x| r.typeof_(a, x), norm::jm9_typeof),
        (|r, a, x| r.bnot(a, x), norm::jm10_int_bnot),
        (|r, a, x| r.to_int32(a, x), norm::jm3_to_int32),
        (|r, a, x| r.length(a, x, LengthObject::String), |a, x| norm::je2_length(a, x, LengthObject::String)),
        (|r, a, x| r.length(a, x, LengthObject::Array), |a, x| norm::je2_length(a, x, LengthObject::Array)),
        (|r, a, x| r.poly_var(a, x, false), |a, x| norm::jm11_poly_var_access(a, x, false)),
        (|r, a, x| r.poly_var(a, x, true), |a, x| norm::jm11_poly_var_access(a, x, true)),
        (
            |r, a, x| {
                let (y, z) = (r.int_literal(a, 1), r.int_literal(a, 2));
                r.cond(a, x, y, z)
            },
            |a, x| {
                let (y, z) = (plain::int(a, 1), plain::int(a, 2));
                norm::je7_cond(a, x, y, z)
            },
        ),
    ];
    for (index, (interface, today)) in unary.iter().enumerate() {
        for value in OPERANDS {
            let (mut l, mut t) = (unit(), unit());
            let mut rows = Rows::default();
            let x = operand(&mut rows, &mut l, value);
            done(interface(&mut rows, &mut l.b, x));
            let x = operand_today(&mut t, value);
            today(&mut t.b, x);
            assert_eq!(l.b.dump(), t.b.dump(), "rule {index} on {value:?}");
        }
    }
}

#[test]
fn the_rules_that_may_decline_give_the_value_back() {
    // J-M11 on a strictly pure literal gives the field and releases the
    // rest; on a variable it gives the variable back.
    same(
        |r, u| {
            let mark = r.mark();
            for value in [1, 2] {
                let item = r.int_literal(&mut u.b, value);
                r.push(item);
            }
            let array = r.array(&mut u.b, mark, 0);
            let field = r.project(&mut u.b, array, None, Some(1)).expect("a pure literal");
            assert_eq!(r.int(&u.b, Rows::of(&field)), Some(2));
            let x = r.var(&mut u.b, u.x);
            let x = r.project(&mut u.b, x, None, Some(0)).expect_err("a variable has no field");
            assert_eq!(r.var_of(&u.b, Rows::of(&x)), Some(u.x));
        },
        |u| {
            let items = [plain::int(&mut u.b, 1), plain::int(&mut u.b, 2)];
            let array = plain::node(&mut u.b, View::JArray { values: &items }, 0);
            assert!(norm::jm11_projection(&mut u.b, array, None, Some(1)).is_some());
            let x = var(&mut u.b, u.x);
            assert!(norm::jm11_projection(&mut u.b, x, None, Some(0)).is_none());
        },
    );
    // J-M0: a variable is dropped whole; a call is kept.
    same(
        |r, u| {
            let x = r.var(&mut u.b, u.x);
            assert!(r.without_pure(&mut u.b, x).is_none());
            let f = r.var(&mut u.b, u.f);
            let mark = r.mark();
            let call = r.call(&mut u.b, f, mark, u.call);
            assert!(r.without_pure(&mut u.b, call).is_some());
        },
        |u| {
            let x = var(&mut u.b, u.x);
            assert!(norm::jm0_remove_pure_subexpression(&mut u.b, x).is_none());
            let callee = var(&mut u.b, u.f);
            let call = plain::node(&mut u.b, View::JCall { callee, args: &[], info: u.call }, 0);
            assert!(norm::jm0_remove_pure_subexpression(&mut u.b, call).is_some());
        },
    );
}

#[test]
fn a_reader_reads_what_the_lowering_reads_today() {
    let mut u = unit();
    let mut r = Rows::default();
    let a = &mut u.b;
    // `f(x.name, 1.5, "s")`, the call located.
    let f = r.var(a, u.f);
    let mark = r.mark();
    let x = r.var(a, u.x);
    let dot = r.dot(a, x, u.name, FieldPos::new(Some(2)), false);
    r.push(dot);
    let float = r.number(a, u.float);
    r.push(float);
    let text = r.string(a, "s");
    r.push(text);
    let mut call = r.call(a, f, mark, u.call);
    assert!(!r.located(a, Rows::of(&call)));
    r.locate(a, &mut call, crate::lambda::LamLoc::NONE);
    assert!(r.located(a, Rows::of(&call)));
    let root = Rows::of(&call);
    assert_eq!(r.id(a, root), Rows::node(Rows::from_node(root)).0);
    assert_eq!(r.kind(a, root), Kind::Call);
    assert_eq!(r.info_of(a, root), Some(u.call));
    assert_eq!(r.arity(a, root), 4);
    assert!(!r.has(a, root, flag::PURE));
    let callee = r.operand(a, root, 0);
    assert_eq!((r.kind(a, callee), r.var_of(a, callee)), (Kind::Var, Some(u.f)));
    assert!(r.has(a, callee, flag::PURE | flag::STRICT | flag::DELAY_SAFE | flag::SUBEXPR | flag::DUPLICABLE));
    let member = r.operand(a, root, 1);
    assert_eq!(r.kind(a, member), Kind::Dot);
    assert_eq!(r.member_of(a, member), Some((u.name, FieldPos::new(Some(2)))));
    assert_eq!(r.aux(a, member), 0);
    assert!(r.has(a, member, flag::PURE | flag::STRICT | flag::DUPLICABLE));
    assert!(!r.has(a, member, flag::DELAY_SAFE) && !r.has(a, member, flag::SUBEXPR));
    assert!(r.runs_no_code(a, member));
    assert_eq!(r.var_of(a, r.operand(a, member, 0)), Some(u.x));
    let number = r.operand(a, root, 2);
    assert!(r.is_float(a, number));
    assert_eq!((r.int(a, number), r.bigint(a, number), r.text(a, number)), (None, None, None));
    assert_eq!(r.text(a, r.operand(a, root, 3)), Some("s"));
    // A template without values reads as its text, as a string does.
    let mark = r.mark();
    let template = r.template(a, &[crate::string_literal::template_from_semantic("ab")], mark);
    assert_eq!((r.kind(a, Rows::of(&template)), r.text(a, Rows::of(&template))), (Kind::Template, Some("ab")));
    assert_eq!(r.arity(a, Rows::of(&template)), 0);
    // The flags are the node's, bit for bit, for every node built above.
    for index in 0..a.nodes.len() {
        let node = NodeId(index as u32);
        let today = a.node(node).flags();
        for (ours, theirs) in [
            (flag::PURE, NodeFlags::PURE),
            (flag::STRICT, NodeFlags::STRICT),
            (flag::DELAY_SAFE, NodeFlags::DELAY_SAFE),
            (flag::SUBEXPR, NodeFlags::J_SUBEXPR),
        ] {
            assert_eq!(r.has(a, Rows::at(node), ours), today.contains(theirs), "node {index}, flag {ours}");
        }
    }
    // Literals.
    let int = r.int_literal(a, -3);
    assert_eq!((r.kind(a, Rows::of(&int)), r.int(a, Rows::of(&int))), (Kind::Number, Some(-3)));
    assert!(!r.is_float(a, Rows::of(&int)));
    let big = r.number(a, u.bigint);
    assert_eq!(r.bigint(a, Rows::of(&big)), Some("+12"));
    let truth = r.boolean(a, true);
    assert_eq!((r.kind(a, Rows::of(&truth)), r.aux(a, Rows::of(&truth))), (Kind::Bool, 1));
    let unit_value = r.undefined(a, true);
    assert_eq!((r.kind(a, Rows::of(&unit_value)), r.aux(a, Rows::of(&unit_value))), (Kind::Undefined, 1));
    let (l, right) = (r.var(a, u.x), r.var(a, u.y));
    let sum = r.bin_plain(a, BinOp::Minus, l, right);
    assert_eq!((r.kind(a, Rows::of(&sum)), r.aux(a, Rows::of(&sum))), (Kind::Bin, BinOp::Minus as u8));
    let module = crate::bir::ImportId(0);
    a.pools.j_modules.push(crate::js_ir::ModuleId {
        id: crate::ident::Ident::create_persistent("M"),
        kind: crate::js_ir::Kind::Ml,
        dynamic_import: false,
    });
    let qualified = r.qualified(a, module, Some(u.other));
    assert_eq!(r.kind(a, Rows::of(&qualified)), Kind::Qualified);
    assert_eq!(r.qualified_of(a, Rows::of(&qualified)), Some((module, Some(u.other))));
    assert_eq!(r.function_of(a, Rows::of(&qualified)), None);
}

#[test]
fn taking_a_node_apart_releases_what_is_not_kept() {
    let uses = |b: &Bir, v: VarId| b.js_scope.as_ref().unwrap().uses[v.index()].remaining;
    let mut u = unit();
    let mut r = Rows::default();
    let a = &mut u.b;
    // `(x, y)`: keeping the second operand releases the reference to x.
    let (x, y) = (r.var(a, u.x), r.var(a, u.y));
    let seq = r.seq(a, x, y);
    assert_eq!((uses(a, u.x), uses(a, u.y)), (1, 1));
    let kept = r.keep_operand(a, seq, 1);
    assert_eq!(r.var_of(a, Rows::of(&kept)), Some(u.y));
    assert_eq!((uses(a, u.x), uses(a, u.y)), (0, 1));
    // `f(x, kept)`: the operands come back in order, the callee first.
    let f = r.var(a, u.f);
    let mark = r.mark();
    let x = r.var(a, u.x);
    r.push(x);
    r.push(kept);
    let call = r.call(a, f, mark, u.call);
    let before = r.mark();
    assert_eq!(r.unpack_rev(a, call), 3);
    assert_eq!(r.mark(), Mark(before.0 + 3));
    let order = [u.f, u.x, u.y];
    for expected in order {
        let operand = r.pop();
        assert_eq!(r.var_of(a, Rows::of(&operand)), Some(expected));
        r.push(operand);
        let top = Mark(r.mark().0 - 1);
        r.drop_operands(a, top);
    }
    assert_eq!(r.mark(), before);
    assert_eq!([uses(a, u.f), uses(a, u.x), uses(a, u.y)], [0, 0, 0]);
    // A released handle gives its reference back.
    let x = r.var(a, u.x);
    r.release(a, x);
    assert_eq!(uses(a, u.x), 0);
}

#[test]
fn a_copy_is_a_second_node_and_cold_data_is_given_separately() {
    let mut u = unit();
    let mut r = Rows::default();
    let a = &mut u.b;
    let mut original = r.string(a, "s");
    r.comment(a, &mut original, u.name);
    r.locate(a, &mut original, crate::lambda::LamLoc::NONE);
    let mut leaf = r.copy_leaf(a, Rows::of(&original));
    assert_ne!(r.id(a, Rows::of(&leaf)), r.id(a, Rows::of(&original)));
    assert_eq!(r.text(a, Rows::of(&leaf)), Some("s"));
    assert!(!r.located(a, Rows::of(&leaf)));
    assert!(a.cold(Rows::of(&leaf)).is_none());
    r.copy_cold(a, Rows::of(&original), &mut leaf);
    assert!(r.located(a, Rows::of(&leaf)));
    assert_eq!(a.cold(Rows::of(&leaf)).unwrap().comment, Some(u.name));
    // A copy of `x.name` holds a second reference to x.
    let x = r.var(a, u.x);
    let dot = r.dot(a, x, u.name, FieldPos::NONE, false);
    let copy = r.copy(a, Rows::of(&dot));
    assert_eq!(r.kind(a, Rows::of(&copy)), Kind::Dot);
    assert_eq!(a.js_scope.as_ref().unwrap().uses[u.x.index()].remaining, 2);
    // What the caller knows.
    let mark = r.mark();
    let mut array = r.array(a, mark, 1);
    let strict = r.has(a, Rows::of(&array), flag::STRICT);
    r.assume_strict(a, &mut array);
    assert!(r.has(a, Rows::of(&array), flag::STRICT), "was {strict}");
}

/// `f(x.name, 1)` built `calls` times, each the argument of the next.
fn nest(r: &mut Rows, u: &mut Unit, calls: usize) -> E {
    let a = &mut u.b;
    let mut value = r.var(a, u.x);
    for _ in 0..calls {
        let f = r.var(a, u.f);
        let mark = r.mark();
        let member = r.dot(a, value, u.name, FieldPos::NONE, false);
        r.push(member);
        let one = r.int_literal(a, 1);
        r.push(one);
        value = r.call(a, f, mark, u.call);
    }
    value
}

/// One call of `width` integer arguments.
fn wide(r: &mut Rows, u: &mut Unit, width: usize) -> E {
    let a = &mut u.b;
    let f = r.var(a, u.f);
    let mark = r.mark();
    for value in 0..width {
        let argument = r.int_literal(a, value as i32);
        r.push(argument);
    }
    r.call(a, f, mark, u.call)
}

fn steps(build: fn(&mut Rows, &mut Unit, usize) -> E, size: usize) -> u64 {
    let mut u = unit();
    let mut r = Rows::default();
    done(build(&mut r, &mut u, size));
    r.steps()
}

#[test]
fn a_node_is_read_by_its_id() {
    let mut u = unit();
    let mut r = Rows::default();
    let a = &mut u.b;
    // `f(x, "s")`, `new f(y)` and a flat call: the callee is what its owner
    // calls, an argument is not.
    let f = r.var(a, u.f);
    let callee = r.id(a, Rows::of(&f));
    let mark = r.mark();
    let x = r.var(a, u.x);
    let argument = r.id(a, Rows::of(&x));
    r.push(x);
    let text = r.str(a, u.name);
    assert_eq!(r.str_of(a, Rows::of(&text)), Some(u.name));
    r.push(text);
    assert_eq!((r.owner(a, callee), r.is_callee(a, callee)), (None, false));
    let call = r.call(a, f, mark, u.call);
    let id = r.id(a, Rows::of(&call));
    assert_eq!((r.owner(a, callee), r.owner(a, argument), r.owner(a, id)), (Some(id), Some(id), None));
    assert!(r.is_callee(a, callee) && !r.is_callee(a, argument));
    assert_eq!((r.kind_of(a, id), r.kind_of(a, callee)), (Kind::Call, Kind::Var));
    for flat in [false, true] {
        let f = r.var(a, u.f);
        let callee = r.id(a, Rows::of(&f));
        let y = r.var(a, u.y);
        let argument = r.id(a, Rows::of(&y));
        let built = if flat {
            r.flat_call(a, f, y)
        } else {
            let mark = r.mark();
            r.push(y);
            r.new_(a, f, mark)
        };
        assert!(r.is_callee(a, callee) && !r.is_callee(a, argument));
        assert_eq!(r.owner(a, argument), Some(r.id(a, Rows::of(&built))));
    }
    // An operand of anything else is not a callee, the first one neither.
    let (l, right) = (r.var(a, u.x), r.var(a, u.y));
    let first = r.id(a, Rows::of(&l));
    let sum = r.bin_plain(a, BinOp::Plus, l, right);
    assert!(!r.is_callee(a, first));
    assert_eq!(r.owner(a, first), Some(r.id(a, Rows::of(&sum))));
    // Only a string literal has an interned text to give.
    let template = r.mark();
    let template = r.template(a, &[crate::string_literal::template_from_semantic("ab")], template);
    let number = r.int_literal(a, 1);
    for other in [&template, &number, &sum] {
        assert_eq!(r.str_of(a, Rows::of(other)), None);
    }
    // The owner of a statement's value is the statement, and the id of a
    // statement has a kind.
    let value = a.new_node(View::SExp { value: Rows::node(sum) }, 0);
    assert_eq!(r.kind_of(a, value.0), Kind::Exp);
}

#[test]
fn a_pool_list_of_operands_is_pushed_in_order() {
    same(
        |r, u| {
            let f = r.var(&mut u.b, u.f);
            let nodes = [var(&mut u.b, u.x), plain::int(&mut u.b, 1), var(&mut u.b, u.y)];
            let list = u.b.lists.push(&nodes);
            let steps = r.steps();
            let mark = r.mark();
            r.push_list(&u.b, list);
            assert_eq!((r.mark(), r.steps()), (Mark(mark.0 + 3), steps));
            done(r.call(&mut u.b, f, mark, u.call));
        },
        |u| {
            let callee = var(&mut u.b, u.f);
            let args = [var(&mut u.b, u.x), plain::int(&mut u.b, 1), var(&mut u.b, u.y)];
            let _list = u.b.lists.push(&args);
            built(plain::node(&mut u.b, View::JCall { callee, args: &args, info: u.call }, 0));
        },
    );
}

/// Releasing costs one step per node released, whichever function
/// releases: `release` of a nest, `keep_operand` on a comma of the nest
/// and a variable (the nest is the operand not kept), and `drop_operands`
/// with the nest on the operand stack.
#[test]
fn releasing_ten_thousand_nodes_costs_ten_times_a_thousand() {
    type Release = fn(&mut Rows, &mut Unit, E);
    let ways: [Release; 3] = [
        |r, u, nest| r.release(&mut u.b, nest),
        |r, u, nest| {
            let x = r.var(&mut u.b, u.x);
            let comma = r.seq(&mut u.b, nest, x);
            let before = r.steps();
            let kept = r.keep_operand(&mut u.b, comma, 1);
            // The comma, and every node of the nest.
            assert!(r.steps() - before > 1);
            r.release(&mut u.b, kept);
        },
        |r, u, nest| {
            let mark = r.mark();
            r.push(nest);
            r.drop_operands(&mut u.b, mark);
        },
    ];
    for (way, release) in ways.iter().enumerate() {
        let released = |calls: usize| {
            let mut u = unit();
            let mut r = Rows::default();
            let nest = nest(&mut r, &mut u, calls);
            let nodes = u.b.nodes.len() as u64;
            let before = r.steps();
            release(&mut r, &mut u, nest);
            // At least one step per node of the nest.
            assert!(r.steps() - before >= nodes, "way {way}: {} steps, {nodes} nodes", r.steps() - before);
            r.steps() - before
        };
        let (one, two, ten) = (released(1_000), released(2_000), released(10_000));
        assert_eq!(ten - one, 9 * (two - one), "way {way}: {one} {two} {ten}");
        assert!(two > one);
    }
}

#[test]
fn ten_thousand_nodes_cost_ten_times_a_thousand() {
    for build in [nest, wide] {
        let (one, two, ten) = (steps(build, 1_000), steps(build, 2_000), steps(build, 10_000));
        // Exactly linear: the step from 1,000 to 2,000, nine times.
        assert_eq!(ten - one, 9 * (two - one), "{one} {two} {ten}");
        assert!(two > one);
    }
    // Taking a wide call apart and dropping its operands is linear too.
    let apart = |width: usize| {
        let mut u = unit();
        let mut r = Rows::default();
        let call = wide(&mut r, &mut u, width);
        let before = r.steps();
        let mark = r.mark();
        assert_eq!(r.unpack_rev(&mut u.b, call) as usize, width + 1);
        r.drop_operands(&mut u.b, mark);
        r.steps() - before
    };
    let (one, two, ten) = (apart(1_000), apart(2_000), apart(10_000));
    assert_eq!(ten - one, 9 * (two - one), "{one} {two} {ten}");
}

#[test]
fn the_operand_stack_is_the_one_allocation_of_rows() {
    // Warm: the stack has its capacity. The arena's own vectors grow, so
    // the count is taken as a difference between two widths: a wider call
    // may not cost one allocation more in `Rows`.
    let allocations = |width: usize| {
        let mut u = unit();
        let mut r = Rows::default();
        r.reserve(width);
        let direct = {
            let mut t = unit();
            allocation_counter::measure(|| {
                let callee = var(&mut t.b, t.f);
                let args: Vec<NodeId> = (0..width).map(|value| plain::int(&mut t.b, value as i32)).collect();
                built(plain::node(&mut t.b, View::JCall { callee, args: &args, info: t.call }, 0));
            })
            .count_total
        };
        let through = allocation_counter::measure(|| done(wide(&mut r, &mut u, width))).count_total;
        (through, direct)
    };
    // The direct form allocates its argument vector; the interface does not
    // allocate at all beyond what the arena does for the same nodes.
    for width in [1_000, 10_000] {
        let (through, direct) = allocations(width);
        assert!(through < direct, "width {width}: {through} through the interface, {direct} direct");
    }
}

#[test]
fn a_node_keeps_its_row_over_other_operands() {
    // `args.rs` holds the operands of a literal or of a member callee in
    // variables and builds the node again over the variables: the same
    // kind, `aux`, information and location, a new row.
    for shape in 0..5u8 {
        let arity = if matches!(shape, 0 | 4) { 1 } else { 2 };
        same(
            |r, u| {
                let a = &mut u.b;
                let (x, y) = (r.var(a, u.x), r.var(a, u.y));
                let mark = r.mark();
                let mut old = match shape {
                    0 => {
                        r.release(a, y);
                        r.optional(a, x, true)
                    }
                    4 => {
                        r.release(a, y);
                        r.dot(a, x, u.name, FieldPos::new(Some(1)), false)
                    }
                    _ => {
                        r.push(x);
                        r.push(y);
                        match shape {
                            1 => r.array(a, mark, 1),
                            2 => r.block(a, mark, u.tuple, 1),
                            _ => r.object(a, mark, u.keys),
                        }
                    }
                };
                r.locate(a, &mut old, crate::lambda::LamLoc::NONE);
                let before = r.steps();
                assert_eq!(r.take_operands(a, &mut old), arity);
                assert_eq!(r.steps() - before, 1 + u64::from(arity));
                for _ in 0..arity {
                    let operand = r.pop();
                    r.release(a, operand);
                }
                let mark = r.mark();
                for _ in 0..arity {
                    let f = r.var(a, u.f);
                    r.push(f);
                }
                let kind = r.kind(a, Rows::of(&old));
                let new = r.refill(a, old, mark);
                assert_eq!(r.kind(a, Rows::of(&new)), kind);
                assert!(r.located(a, Rows::of(&new)));
                assert_eq!(r.arity(a, Rows::of(&new)), arity);
                done(new);
            },
            |u| {
                let (tuple, keys, name) = (u.tuple, u.keys, u.name);
                let b = &mut u.b;
                let (x, y) = (var(b, u.x), var(b, u.y));
                fn view(shape: u8, values: &[NodeId], tuple: JsId, keys: JsId, property: StrId) -> (u16, View<'_>) {
                    match shape {
                        0 => (1, View::JOptional { value: values[0] }),
                        1 => (1, View::JArray { values }),
                        2 => (1, View::JBlockLit { values, info: tuple }),
                        3 => (0, View::JObject { values, info: keys }),
                        _ => (0, View::JDot { object: values[0], property, position: FieldPos::new(Some(1)) }),
                    }
                }
                let view = |values| view(shape, values, tuple, keys, name);
                let operands = [x, y];
                if arity == 1 {
                    b.release(y);
                }
                let (aux, old_view) = view(&operands[..arity as usize]);
                let old = plain::node(b, old_view, aux);
                b.set_cold(old, crate::bir::Cold { loc: crate::lambda::LamLoc::NONE, comment: None });
                let mut flags = b.node(old).flags();
                flags.0 |= crate::bir::NodeFlags::JS_LOC_PRESENT;
                b.nodes[old.index()].set_flags(flags);
                for &operand in &operands[..arity as usize] {
                    b.detach(operand);
                }
                for &operand in &operands[..arity as usize] {
                    b.release(operand);
                }
                let first = var(b, u.f);
                let fresh = [first, if arity == 2 { var(b, u.f) } else { first }];
                let (aux, new_view) = view(&fresh[..arity as usize]);
                let new = plain::node(b, new_view, aux);
                b.set_cold(new, crate::bir::Cold { loc: crate::lambda::LamLoc::NONE, comment: None });
                let mut flags = b.node(new).flags();
                flags.0 |= crate::bir::NodeFlags::JS_LOC_PRESENT;
                b.nodes[new.index()].set_flags(flags);
                b.release(old);
                built(new);
            },
        );
    }
}

/// `copy` costs one step per node copied also when the copy takes slots
/// that a release freed (the node vector does not grow then), and in a
/// warm unit it allocates nothing.
#[test]
fn a_copy_into_freed_slots_costs_one_step_per_node() {
    let copied = |calls: usize| {
        let mut u = unit();
        let mut r = Rows::default();
        let tree = nest(&mut r, &mut u, calls);
        // As many nodes again, released: the copy below reuses them.
        let other = nest(&mut r, &mut u, calls);
        let before = r.steps();
        r.release(&mut u.b, other);
        let nodes = r.steps() - before;
        // A first copy sizes the pools and the copy storage.
        let lists_before = u.b.lists.storage_shape().0;
        let warm = r.copy(&mut u.b, Rows::of(&tree));
        let growth = u.b.lists.storage_shape().0 - lists_before;
        r.release(&mut u.b, warm);
        u.b.lists.reserve_test_growth(growth);
        r.reserve_copy(&u.b);
        u.b.js_scope.as_mut().expect("the unit counts occurrences").reserve_repeat();
        let (len, before) = (u.b.nodes.len(), r.steps());
        let mut copy = None;
        let allocations = allocation_counter::measure(|| copy = Some(r.copy(&mut u.b, Rows::of(&tree))));
        let steps = r.steps() - before;
        assert_eq!(u.b.nodes.len(), len, "the copy took freed slots");
        assert_eq!(steps, nodes, "one step per node copied");
        assert_eq!(allocations.count_total, 0, "{calls} calls");
        done(copy.expect("the copy"));
        steps
    };
    let (one, two, ten) = (copied(1_000), copied(2_000), copied(10_000));
    assert_eq!(ten - one, 9 * (two - one), "{one} {two} {ten}");
    assert!(one as usize >= 1_000);
}

#[test]
#[should_panic(expected = "one operand per key of the object")]
fn an_object_with_fewer_operands_than_keys_is_refused() {
    let mut u = unit();
    let mut r = Rows::default();
    let mark = r.mark();
    let x = r.var(&mut u.b, u.x);
    r.push(x);
    // `u.keys` has two keys.
    done(r.object(&mut u.b, mark, u.keys));
}

#[test]
#[should_panic(expected = "the operands the JSX header counts")]
fn a_jsx_element_without_the_operands_of_its_header_is_refused() {
    let mut u = unit();
    let mut r = Rows::default();
    let info = u.b.js_info(JsPayload::Jsx(crate::bir::JsxHeader {
        spread: false,
        props: crate::bir::PropertySpan { start: 0, len: 2 },
        children: 0,
        key: false,
        multi: false,
        fragment: false,
    }));
    let mark = r.mark();
    // The callee and the tag, and no value for the two properties.
    for var in [u.f, u.x] {
        let operand = r.var(&mut u.b, var);
        r.push(operand);
    }
    done(r.jsx(&mut u.b, mark, info, false));
}
