//! Level L normalising rules: what `LamArena`'s smart constructors do when a
//! node is built (`compiler-rust/src/lambda/arena.rs`). The table in
//! BACKEND_REDESIGN.md C.5 is the specification; every rule cites its row.
//!
//! | Row | Constructor (`LamArena`) | Trigger | Result | Pattern depth |
//! | --- | --- | --- | --- | --- |
//! | N1 | `prim`, `fold_prim` | unary primitive on a constant | constant | 1 |
//! | N2 | `prim`, `fold_prim` | binary primitive on two constants | constant | 1 |
//! | N3 | `prim`, `fold_makeblock_module_alias` | module block of all fields of one module, in order | that module | 2, all arguments |
//! | N4 | `if_` | constant condition | the branch taken | 1 |
//! | N5 | `if_` | a branch is `assert false` | `seq(condition, other branch)` | 1 |
//! | N6 | `if_` | `if c then true else false`, `c` a boolean primitive | `c` | 1 |
//! | N7 | `if_`, `lambda_not` | `if c then false else true`, `c` a boolean primitive | `not c`; `a != b` becomes `a == b` | 1 |
//! | N8 | `seq` | first is a non-empty `Pmakeblock` | its arguments in sequence, then second | 1, all arguments |
//! | N9 | `seq` | first is a one-argument null-to-option conversion | `seq(argument, second)` | 1 |
//! | N10 | `switch_with`, `decide_switch` | constant scrutinee | the action of its case, or the default | 1, the keys |
//! | N11 | `switch_with`, `decide_switch` | constant scrutinee, untagged variant | the action the generated dispatch reaches | 1, the keys, and `eq_approx` of actions |
//! | N12 | `string_switch_with` | constant string scrutinee | the action of its case, or the default | 1, the keys |
//! | N13 | `apply`, `eta_reduce_function_apply` | callee is a function that only forwards its parameters to a primitive | the primitive on the arguments | 4 |
//! | N14 | `apply` | callee is `let x = v in fun` | `let x = v in apply(fun, args)` | 2 |
//!
//! `let_`, `letrec`, `function_`, `static_catch`, `try_`, loops and
//! assignments build their node as given: there is no rule for them.
//!
//! Each rule edits the node in place and pushes what the constructor would
//! have passed to another constructor; it never calls another rule.
use crate::bir::engine::{Changed, Engine};
use crate::bir::*;
use crate::lambda::lam_compat::{Comparison, FieldDbgInfo};
use crate::lambda::lam_constant::{Constant as C, PointerInfo};
use crate::lambda::lam_primitive::Primitive;
use crate::lambda::lam_tag_info::TagInfo;
use crate::lambda::{SwitchDispatch, SwitchKey};
use smallvec::SmallVec;

/// Number of rows in the table.
pub const ROWS: usize = 14;
/// Row names, for reports.
pub const ROW_NAMES: [&str; ROWS] = [
    "N1", "N2", "N3", "N4", "N5", "N6", "N7", "N8", "N9", "N10", "N11", "N12", "N13", "N14",
];
const N1: usize = 0;
const N2: usize = 1;
const N3: usize = 2;
const N4: usize = 3;
const N5: usize = 4;
const N6: usize = 5;
const N7: usize = 6;
const N8: usize = 7;
const N9: usize = 8;
const N10: usize = 9;
const N11: usize = 10;
const N12: usize = 11;
const N13: usize = 12;
const N14: usize = 13;

fn fired(e: &mut Engine<'_>, row: usize) -> Changed {
    e.stats.fired[row] += 1;
    Changed::Yes
}

/// Offer one node to the rule of its opcode.
pub(crate) fn step(e: &mut Engine<'_>, node: NodeId) -> Changed {
    match e.bir().node(node).op() {
        Op::Prim => prim(e, node),
        Op::If => if_(e, node),
        Op::Seq => seq(e, node),
        Op::Switch => switch(e, node),
        Op::StrSwitch => str_switch(e, node),
        Op::Apply => apply(e, node),
        _ => Changed::No,
    }
}

pub(crate) fn const_of(b: &Bir, node: NodeId) -> Option<&Constant> {
    match b.view(node) {
        View::Const { value } => Some(b.constant(value)),
        _ => None,
    }
}

/// `Constant::Int { i, .. }` of the legacy arena, with or without a comment.
fn int_of(c: &Constant) -> Option<i32> {
    match c {
        Constant::Int(i)
        | Constant::DecoratedInt {
            value: i,
            native: false,
            ..
        } => i32::try_from(*i).ok(),
        _ => None,
    }
}

enum Folded {
    Int(i32),
    Bool(bool),
    Str(String),
    Char(i32),
}

/// Rows N1 and N2: `LamArena::fold_prim`, same tests in the same order.
fn fold(b: &Bir, p: &Primitive, args: &[&Constant]) -> Option<Folded> {
    // The legacy fold parses the spelling with Rust's parser, not OCaml's.
    let float = |c: &Constant| match c {
        Constant::Float(f) => b.text(f.spelling()).parse::<f64>().ok(),
        _ => None,
    };
    match *args {
        [a] => match (p, a) {
            (Primitive::Pnegint, a) => Some(Folded::Int(int_of(a)?.wrapping_neg())),
            (Primitive::Pintoffloat, Constant::Float(_)) => Some(Folded::Int(float(a)? as i32)),
            (Primitive::Pstringlength, Constant::String(s)) => Some(Folded::Int(
                crate::string_literal::utf16_length(b.text(*s))
                    .expect("String_literal.utf16_length: Invalid_utf8") as i32,
            )),
            (Primitive::Pnot, Constant::Bool(v)) => Some(Folded::Bool(!v)),
            _ => None,
        },
        [a, c] => match (p, a, c) {
            (Primitive::Pintcomp(cmp), _, _) if int_of(a).is_some() && int_of(c).is_some() => {
                Some(Folded::Bool(cmp.cmp_int32(int_of(a)?, int_of(c)?)))
            }
            (Primitive::Pfloatcomp(cmp), Constant::Float(_), Constant::Float(_)) => {
                Some(Folded::Bool(cmp.cmp_float(float(a)?, float(c)?)))
            }
            (
                Primitive::Pintcomp(op @ (Comparison::Eq | Comparison::Neq)),
                Constant::Pointer(x),
                Constant::Pointer(y),
            ) => {
                let eq = b.text(*x) == b.text(*y);
                Some(Folded::Bool(if matches!(op, Comparison::Eq) {
                    eq
                } else {
                    !eq
                }))
            }
            (
                Primitive::Paddint
                | Primitive::Psubint
                | Primitive::Pmulint
                | Primitive::Pdivint
                | Primitive::Pmodint
                | Primitive::Pandint
                | Primitive::Porint
                | Primitive::Pxorint
                | Primitive::Plslint
                | Primitive::Plsrint
                | Primitive::Pasrint,
                _,
                _,
            ) => {
                let (x, y) = (int_of(a)?, int_of(c)?);
                Some(Folded::Int(match p {
                    Primitive::Paddint => x.wrapping_add(y),
                    Primitive::Psubint => x.wrapping_sub(y),
                    Primitive::Pmulint => x.wrapping_mul(y),
                    Primitive::Pdivint if y != 0 => x.wrapping_div(y),
                    Primitive::Pmodint if y != 0 => x.wrapping_rem(y),
                    Primitive::Pdivint | Primitive::Pmodint => return None,
                    Primitive::Pandint => x & y,
                    Primitive::Porint => x | y,
                    Primitive::Pxorint => x ^ y,
                    Primitive::Plslint => x.wrapping_shl(y as u32),
                    Primitive::Plsrint => (x as u32).wrapping_shr(y as u32) as i32,
                    Primitive::Pasrint => x.wrapping_shr(y as u32),
                    _ => unreachable!(),
                }))
            }
            (Primitive::Psequand, Constant::Bool(x), Constant::Bool(y)) => {
                Some(Folded::Bool(*x && *y))
            }
            (Primitive::Psequor, Constant::Bool(x), Constant::Bool(y)) => {
                Some(Folded::Bool(*x || *y))
            }
            (Primitive::Pstringadd, Constant::String(x), Constant::String(y)) => {
                Some(Folded::Str(format!("{}{}", b.text(*x), b.text(*y))))
            }
            (Primitive::Pstringrefs | Primitive::Pstringrefu, Constant::String(s), _) => {
                let index = int_of(c)?;
                match crate::string_literal::code_point_at_utf16_index(b.text(*s), index as i64) {
                    Ok(Some(codepoint)) => Some(Folded::Char(codepoint as i32)),
                    _ => None,
                }
            }
            _ => None,
        },
        _ => None,
    }
}

/// Row N3: `LamArena::fold_makeblock_module_alias`. The source of every
/// field must be the same variable or the same module; lowered Lambda never
/// has a variable and a module reference of one identity.
fn module_alias(b: &Bir, p: &Primitive, args: &[NodeId]) -> Option<NodeId> {
    let Primitive::Pmakeblock(TagInfo::Module(fields), _) = p else {
        return None;
    };
    if fields.len() != args.len() || fields.is_empty() {
        return None;
    }
    let field = |arg: NodeId| -> Option<(i32, &str, NodeId)> {
        let View::Prim { args, primitive } = b.view(arg) else {
            return None;
        };
        let Primitive::Pfield(pos, FieldDbgInfo::Module { name }) =
            &b.primitive(primitive).primitive
        else {
            return None;
        };
        let [source] = args else { return None };
        Some((*pos, name.as_str(), *source))
    };
    let (pos, name, source) = field(args[0])?;
    if pos != 0 || name != fields[0] {
        return None;
    }
    let identity = |node: NodeId| match b.view(node) {
        View::Var { var } => Some((0, var.index())),
        View::Global { module } => Some((1, module.index())),
        _ => None,
    };
    let wanted = identity(source)?;
    for (i, (arg, expected)) in args.iter().zip(fields.iter()).enumerate().skip(1) {
        let (pos, name, src) = field(*arg)?;
        if pos as usize != i || name != expected || identity(src) != Some(wanted) {
            return None;
        }
    }
    Some(source)
}

fn prim(e: &mut Engine<'_>, node: NodeId) -> Changed {
    let b = e.bir();
    let View::Prim { args, primitive } = b.view(node) else {
        unreachable!()
    };
    let p = &b.primitive(primitive).primitive;
    // `[a] if is_const(a)` and `[a, b] if both are constants`: fold or leave.
    let folded = match *args {
        [a] => const_of(b, a).map(|a| fold(b, p, &[a])),
        [a, c] => match (const_of(b, a), const_of(b, c)) {
            (Some(a), Some(c)) => Some(fold(b, p, &[a, c])),
            _ => None,
        },
        _ => None,
    };
    if let Some(folded) = folded {
        let Some(folded) = folded else {
            return Changed::No;
        };
        let row = if args.len() == 1 { N1 } else { N2 };
        let value = match folded {
            Folded::Int(i) => Constant::Int(i64::from(i)),
            Folded::Bool(v) => Constant::Bool(v),
            Folded::Char(c) => Constant::Char(c as u32),
            Folded::Str(s) => {
                let text = e.intern_text(&s);
                Constant::String(text)
            }
        };
        let value = e.intern_const(value);
        e.put(node, View::Const { value }, 0);
        return fired(e, row);
    }
    match module_alias(b, p, args) {
        Some(source) => {
            e.promote(node, source);
            fired(e, N3)
        }
        None => Changed::No,
    }
}

/// `Constant::eval_as_bool` of the legacy arena.
pub(crate) fn eval_as_bool<'a>(b: &'a Bir, mut c: &'a Constant) -> bool {
    use crate::types::VariantLiteralTag as L;
    loop {
        return match c {
            Constant::Int(i) | Constant::NativeInt(i) | Constant::DecoratedInt { value: i, .. } => {
                *i != 0
            }
            Constant::Constructor(tag) => match &tag.literal {
                L::String(value) => !value.is_empty(),
                L::Int(value) => *value != 0,
                L::Bool(value) => *value,
                L::Null | L::Undefined => false,
                L::Float(_) | L::BigInt(_) => true,
            },
            Constant::Char(c) => *c != 0,
            Constant::Bool(v) => *v,
            Constant::Null | Constant::ModuleAlias | Constant::Undefined(_) => false,
            Constant::String(_)
            | Constant::ImmString(_)
            | Constant::Pointer(_)
            | Constant::Float(_)
            | Constant::BigInt(_)
            | Constant::Block { .. } => true,
            Constant::Some(inner) => {
                c = b.constant(*inner);
                continue;
            }
        };
    }
}

fn is_assert_false(b: &Bir, node: NodeId) -> bool {
    matches!(
        const_of(b, node),
        Some(Constant::DecoratedInt {
            native: false,
            comment: PointerInfo::AssertFalse,
            ..
        })
    )
}

fn bool_const(b: &Bir, node: NodeId) -> Option<bool> {
    match const_of(b, node) {
        Some(Constant::Bool(v)) => Some(*v),
        _ => None,
    }
}

/// `LamArena::has_boolean_type`: the primitive of a boolean-valued node.
fn boolean_prim(b: &Bir, node: NodeId) -> Option<PrimId> {
    let View::Prim { primitive, .. } = b.view(node) else {
        return None;
    };
    matches!(
        b.primitive(primitive).primitive,
        Primitive::Pnot
            | Primitive::Psequand
            | Primitive::Psequor
            | Primitive::PisNotNone
            | Primitive::Pobjcomp(_)
            | Primitive::Pboolcomp(_)
            | Primitive::Pintcomp(_)
            | Primitive::Pfloatcomp(_)
            | Primitive::Pbigintcomp(_)
            | Primitive::Pstringcomp(_)
    )
    .then_some(primitive)
}

/// Rows N4 to N7: `LamArena::if_`.
fn if_(e: &mut Engine<'_>, node: NodeId) -> Changed {
    let b = e.bir();
    let View::If {
        condition,
        then_,
        else_,
    } = b.view(node)
    else {
        unreachable!()
    };
    if let Some(c) = const_of(b, condition) {
        let kept = if eval_as_bool(b, c) { then_ } else { else_ };
        e.promote(node, kept);
        return fired(e, N4);
    }
    let other = if is_assert_false(b, else_) {
        Some(then_)
    } else if is_assert_false(b, then_) {
        Some(else_)
    } else {
        None
    };
    if let Some(other) = other {
        e.detach(condition);
        e.detach(other);
        e.put(
            node,
            View::Seq {
                first: condition,
                second: other,
            },
            0,
        );
        // `self.seq(cond, branch)`.
        e.push(node);
        return fired(e, N5);
    }
    match (bool_const(b, then_), bool_const(b, else_)) {
        (Some(true), Some(false)) if boolean_prim(b, condition).is_some() => {
            e.promote(node, condition);
            fired(e, N6)
        }
        (Some(false), Some(true)) => {
            let Some(primitive) = boolean_prim(b, condition) else {
                return Changed::No;
            };
            let payload = b.primitive(primitive);
            let loc = payload.loc;
            // `lambda_not`: `a != b` becomes `a == b` without folding;
            // anything else goes under `Pnot`, which cannot fold a primitive.
            if matches!(payload.primitive, Primitive::Pintcomp(Comparison::Neq)) {
                let View::Prim { args, .. } = b.view(condition) else {
                    unreachable!()
                };
                let args: SmallVec<[NodeId; 4]> = SmallVec::from_slice(args);
                for &arg in &args {
                    e.detach(arg);
                }
                let primitive = e.intern_prim(Primitive::Pintcomp(Comparison::Eq), loc);
                e.put(
                    node,
                    View::Prim {
                        args: &args,
                        primitive,
                    },
                    0,
                );
            } else {
                e.detach(condition);
                let primitive = e.intern_prim(Primitive::Pnot, loc);
                e.put(
                    node,
                    View::Prim {
                        args: &[condition],
                        primitive,
                    },
                    0,
                );
            }
            fired(e, N7)
        }
        _ => Changed::No,
    }
}

/// Rows N8 and N9: `LamArena::seq`. A sequence built by `seq` is always a
/// `Seq` node, so of the sequences N8 builds only the innermost, whose first
/// is the block's first argument, can match again.
fn seq(e: &mut Engine<'_>, node: NodeId) -> Changed {
    let b = e.bir();
    let View::Seq { first, .. } = b.view(node) else {
        unreachable!()
    };
    let View::Prim { args, primitive } = b.view(first) else {
        return Changed::No;
    };
    match &b.primitive(primitive).primitive {
        Primitive::Pmakeblock(_, _) if !args.is_empty() => {
            if let [only] = *args {
                e.promote(first, only);
                e.push(node);
                return fired(e, N8);
            }
            let args: SmallVec<[NodeId; 8]> = SmallVec::from_slice(args);
            let weight = e.weight(first);
            for &arg in &args {
                e.detach(arg);
            }
            let inner = e.node(
                View::Seq {
                    first: args[0],
                    second: args[1],
                },
                0,
                weight,
            );
            let mut acc = inner;
            for &arg in &args[2..] {
                acc = e.node(
                    View::Seq {
                        first: acc,
                        second: arg,
                    },
                    0,
                    weight,
                );
            }
            // The chain's top moves into `first`'s slot.
            e.fill(first, acc);
            e.push(if acc == inner { first } else { inner });
            fired(e, N8)
        }
        Primitive::PnullToOpt | Primitive::PnullUndefinedToOpt if args.len() == 1 => {
            let arg = args[0];
            e.promote(first, arg);
            e.push(node);
            fired(e, N9)
        }
        _ => Changed::No,
    }
}

/// The legacy form of a constant, without the elements of a block: what
/// `untagged_value` reads.
fn shallow_legacy_const(b: &Bir, c: &Constant) -> Option<C> {
    Some(match c {
        Constant::Null => C::JsNull,
        Constant::Undefined(is_unit) => C::JsUndefined { is_unit: *is_unit },
        Constant::Bool(true) => C::JsTrue,
        Constant::Bool(false) => C::JsFalse,
        Constant::Int(i) => C::Int {
            i: i32::try_from(*i).ok()?,
            comment: None,
        },
        Constant::NativeInt(i) => C::NativeInt {
            i: *i,
            comment: None,
        },
        Constant::DecoratedInt { value, native, .. } => {
            if *native {
                C::NativeInt {
                    i: *value,
                    comment: None,
                }
            } else {
                C::Int {
                    i: i32::try_from(*value).ok()?,
                    comment: None,
                }
            }
        }
        Constant::Constructor(tag) => C::Constructor(tag.clone()),
        Constant::String(s) => C::String(b.text(*s).to_owned()),
        Constant::ImmString(s) => C::ImmString(b.text(*s).to_owned()),
        Constant::Pointer(s) => C::Pointer(b.text(*s).to_owned()),
        Constant::Float(f) => C::Float(b.text(f.spelling()).to_owned()),
        Constant::BigInt(s) => {
            let (sign, value) = b.text(*s).split_at_checked(1)?;
            C::BigInt {
                negative: sign == "-",
                value: value.to_owned(),
            }
        }
        Constant::Block { tag, .. } => C::Block {
            tag_info: Box::new(tag.clone()),
            elements: Vec::new(),
        },
        Constant::Char(_) | Constant::Some(_) | Constant::ModuleAlias => return None,
    })
}

/// `LamArena::eq_approx` on two subtrees. Counts the node pairs it compares.
fn eq_approx(b: &Bir, x: NodeId, y: NodeId, compared: &std::cell::Cell<u64>) -> bool {
    let mut stack: SmallVec<[(NodeId, NodeId); 8]> = SmallVec::new();
    stack.push((x, y));
    while let Some((x, y)) = stack.pop() {
        compared.set(compared.get() + 1);
        let same = match (b.view(x), b.view(y)) {
            (View::Var { var: v1 }, View::Var { var: v2 }) => v1 == v2,
            (View::Global { module: m1 }, View::Global { module: m2 }) => m1 == m2,
            (View::Const { value: c1 }, View::Const { value: c2 }) => {
                c1 == c2
                    || match (
                        crate::bir::bridge::export_constant(b, c1),
                        crate::bir::bridge::export_constant(b, c2),
                    ) {
                        (Ok(c1), Ok(c2)) => c1.eq_approx(&c2),
                        _ => false,
                    }
            }
            (
                View::Apply {
                    callee: f1,
                    args: a1,
                    ..
                },
                View::Apply {
                    callee: f2,
                    args: a2,
                    ..
                },
            ) => {
                stack.push((f1, f2));
                a1.len() == a2.len() && {
                    stack.extend(a1.iter().copied().zip(a2.iter().copied()));
                    true
                }
            }
            (
                View::If {
                    condition: a1,
                    then_: b1,
                    else_: c1,
                },
                View::If {
                    condition: a2,
                    then_: b2,
                    else_: c2,
                },
            ) => {
                stack.extend([(a1, a2), (b1, b2), (c1, c2)]);
                true
            }
            (
                View::Seq {
                    first: a1,
                    second: b1,
                },
                View::Seq {
                    first: a2,
                    second: b2,
                },
            )
            | (
                View::While {
                    condition: a1,
                    body: b1,
                },
                View::While {
                    condition: a2,
                    body: b2,
                },
            ) => {
                stack.extend([(a1, a2), (b1, b2)]);
                true
            }
            (View::Break, View::Break) | (View::Continue, View::Continue) => true,
            (View::Assign { var: v1, value: l1 }, View::Assign { var: v2, value: l2 }) => {
                stack.push((l1, l2));
                v1 == v2
            }
            (
                View::Exit {
                    label: l1,
                    args: a1,
                },
                View::Exit {
                    label: l2,
                    args: a2,
                },
            ) => {
                l1 == l2 && a1.len() == a2.len() && {
                    stack.extend(a1.iter().copied().zip(a2.iter().copied()));
                    true
                }
            }
            (
                View::Prim {
                    args: a1,
                    primitive: p1,
                },
                View::Prim {
                    args: a2,
                    primitive: p2,
                },
            ) => {
                b.primitive(p1)
                    .primitive
                    .eq_approx(&b.primitive(p2).primitive)
                    && a1.len() == a2.len()
                    && {
                        stack.extend(a1.iter().copied().zip(a2.iter().copied()));
                        true
                    }
            }
            (
                View::StrSwitch {
                    scrutinee: s1,
                    actions: a1,
                    header: h1,
                },
                View::StrSwitch {
                    scrutinee: s2,
                    actions: a2,
                    header: h2,
                },
            ) => {
                let (h1, h2) = (b.switch(h1), b.switch(h2));
                let key = |k: &CaseKey| match k {
                    CaseKey::String(s) => Some(*s),
                    _ => None,
                };
                stack.push((s1, s2));
                h1.has_default == h2.has_default
                    && h1.keys.len() == h2.keys.len()
                    && h1
                        .keys
                        .iter()
                        .zip(h2.keys)
                        .all(|(k1, k2)| key(k1) == key(k2))
                    && {
                        stack.extend(a1.iter().copied().zip(a2.iter().copied()));
                        true
                    }
            }
            _ => false,
        };
        if !same {
            return false;
        }
    }
    true
}

/// Rows N10 and N11: `LamArena::decide_switch`.
fn decide_switch(
    e: &Engine<'_>,
    node: NodeId,
    compared: &std::cell::Cell<u64>,
) -> Option<(NodeId, usize)> {
    let b = e.bir();
    let View::Switch {
        scrutinee,
        actions,
        header,
    } = b.view(node)
    else {
        unreachable!()
    };
    let cst = const_of(b, scrutinee)?;
    decide_switch_on(b, cst, actions, header, compared)
}

/// [`decide_switch`] for a scrutinee constant that is not in the tree
/// (`Lam_analysis.destruct_pattern` asks for a parameter's argument).
pub(crate) fn decide_switch_on(
    b: &Bir,
    cst: &Constant,
    actions: &[NodeId],
    header: SwitchId,
    compared: &std::cell::Cell<u64>,
) -> Option<(NodeId, usize)> {
    use crate::types::{VariantBlock, VariantConstructorCase as Case, VariantLiteralTag};
    let h = b.switch(header);
    let n_consts = h.constants as usize;
    let keys: SmallVec<[&SwitchKey; 8]> = h
        .keys
        .iter()
        .map(|key| match key {
            CaseKey::Lambda(key) => Some(key),
            _ => None,
        })
        .collect::<Option<_>>()?;
    let (const_keys, block_keys) = keys.split_at(n_consts);
    let consts = &actions[..n_consts];
    let blocks = &actions[n_consts..keys.len()];
    let fail = h.has_default.then(|| actions[keys.len()]);
    if let SwitchDispatch::Variant(facts) = &h.dispatch
        && !facts.block_types.is_empty()
    {
        let pair = |keys: &[&SwitchKey], actions: &[NodeId]| -> Vec<(SwitchKey, NodeId)> {
            keys.iter()
                .map(|k| (*k).clone())
                .zip(actions.iter().copied())
                .collect()
        };
        let (consts, blocks) = (pair(const_keys, consts), pair(block_keys, blocks));
        let plan = crate::lambda::untagged_plan_with(
            h.consts_full,
            &consts,
            h.blocks_full,
            &blocks,
            fail,
            h.dispatch,
            |x: &NodeId, y: &NodeId| eq_approx(b, *x, *y, compared),
        );
        let value = shallow_legacy_const(b, cst).and_then(|c| crate::lambda::untagged_value(&c));
        return match (plan, value) {
            (Some(mut plan), Some(value)) => {
                match crate::lambda::untagged_dispatch::select(&mut plan, &value, &mut |_| ()) {
                    crate::lambda::untagged_dispatch::Outcome::Arm(action) => Some(action),
                    crate::lambda::untagged_dispatch::Outcome::Default => fail,
                    crate::lambda::untagged_dispatch::Outcome::Nothing => None,
                }
            }
            _ => None,
        }
        .map(|action| (action, N11));
    }
    let same = crate::lambda::literal_denotes_same;
    let found = match cst {
        Constant::Constructor(tag) => const_keys
            .iter()
            .position(|key| {
                matches!(key, SwitchKey::Constructor(Case::Constant(candidate))
                    if same(&tag.literal, &candidate.literal))
            })
            .map(|i| consts[i])
            .or(fail),
        Constant::Int(_) | Constant::DecoratedInt { native: false, .. } => {
            let i = int_of(cst)?;
            let literal = VariantLiteralTag::Int(i64::from(i));
            const_keys
                .iter()
                .position(|key| match key {
                    SwitchKey::Int(value) => *value == i,
                    SwitchKey::Constructor(Case::Constant(tag)) => same(&literal, &tag.literal),
                    SwitchKey::Constructor(_) => false,
                })
                .map(|i| consts[i])
                .or(fail)
        }
        Constant::Block { tag, .. } => {
            let runtime = match tag {
                TagInfo::Constructor(c) => Some(VariantBlock::Tagged((*c.runtime).clone())),
                TagInfo::RecordInlined(r) => Some((*r.runtime).clone()),
                _ => None,
            };
            block_keys
                .iter()
                .position(|key| {
                    matches!((key, runtime.as_ref()),
                        (SwitchKey::Constructor(Case::Block(candidate)), Some(runtime))
                            if crate::lambda::same_block_runtime(runtime, candidate))
                })
                .map(|i| blocks[i])
                .or(fail)
        }
        _ => None,
    };
    found.map(|action| (action, N10))
}

fn switch(e: &mut Engine<'_>, node: NodeId) -> Changed {
    let compared = std::cell::Cell::new(0);
    let decided = decide_switch(e, node, &compared);
    e.stats.compared += compared.get();
    match decided {
        Some((action, row)) => {
            e.promote(node, action);
            fired(e, row)
        }
        None => Changed::No,
    }
}

/// Row N12: `LamArena::string_switch_with`.
fn str_switch(e: &mut Engine<'_>, node: NodeId) -> Changed {
    let b = e.bir();
    let View::StrSwitch {
        scrutinee,
        actions,
        header,
    } = b.view(node)
    else {
        unreachable!()
    };
    let Some(Constant::String(s) | Constant::ImmString(s)) = const_of(b, scrutinee) else {
        return Changed::No;
    };
    let h = b.switch(header);
    let text = b.text(*s);
    let action = h
        .keys
        .iter()
        .position(|key| matches!(key, CaseKey::String(k) if b.text(*k) == text))
        .map(|i| actions[i])
        .or_else(|| h.has_default.then(|| actions[h.keys.len()]));
    match action {
        Some(action) => {
            e.promote(node, action);
            fired(e, N12)
        }
        None => Changed::No,
    }
}

/// `LamArena::eta_conversion_args`: the function's parameters, in order, are
/// exactly the primitive's arguments, and the primitive evaluates the call's
/// arguments as the call does (`evaluates_args_as_call`).
fn forwards_params(
    b: &Bir,
    primitive: &Primitive,
    params: VarSpan,
    inner_args: &[NodeId],
    outer_args: &[NodeId],
) -> bool {
    let as_call = !primitive.may_skip_operands()
        || outer_args
            .iter()
            .skip(1)
            .all(|arg| matches!(b.node(*arg).op(), Op::Const | Op::Var));
    as_call
        && params.len() == inner_args.len()
        && params.len() == outer_args.len()
        && params
            .iter()
            .zip(inner_args)
            .all(|(param, arg)| matches!(b.view(*arg), View::Var { var } if var == param))
}

/// Rows N13 and N14: `LamArena::apply`.
fn apply(e: &mut Engine<'_>, node: NodeId) -> Changed {
    let b = e.bir();
    let View::Apply { callee, args, info } = b.view(node) else {
        unreachable!()
    };
    let outer: SmallVec<[NodeId; 8]> = SmallVec::from_slice(args);
    match b.view(callee) {
        View::Fun { body, header } => {
            // `lfunction_can_be_inlined`: an async function or one with a
            // directive stays a function.
            if !crate::lambda::lam_analysis::attr_can_be_inlined(b.function_attributes(header)) {
                return Changed::No;
            }
            let params = b.function(header).params;
            let loc = b.application(info).loc;
            let prim_of = |n: NodeId| match b.view(n) {
                View::Prim { args, primitive } => Some((&b.primitive(primitive).primitive, args)),
                _ => None,
            };
            match b.view(body) {
                View::Prim {
                    args: wrap_args,
                    primitive: wrap,
                } if matches!(
                    b.primitive(wrap).primitive,
                    Primitive::PnullToOpt
                        | Primitive::PnullUndefinedToOpt
                        | Primitive::PisNull
                        | Primitive::PisNullUndefined
                        | Primitive::Ptypeof
                ) =>
                {
                    let [inner_call] = wrap_args else {
                        return Changed::No;
                    };
                    let Some((inner, inner_args)) = prim_of(*inner_call) else {
                        return Changed::No;
                    };
                    if !forwards_params(b, inner, params, inner_args, &outer) {
                        return Changed::No;
                    }
                    let (inner, wrap) = (inner.clone(), b.primitive(wrap).primitive.clone());
                    let weight = e.weight(node);
                    for &arg in &outer {
                        e.detach(arg);
                    }
                    let primitive = e.intern_prim(inner, loc);
                    let inner = e.node(
                        View::Prim {
                            args: &outer,
                            primitive,
                        },
                        0,
                        weight,
                    );
                    let primitive = e.intern_prim(wrap, loc);
                    e.put(
                        node,
                        View::Prim {
                            args: &[inner],
                            primitive,
                        },
                        0,
                    );
                    // `prim(inner)` first, then `prim(wrap, [inner])`.
                    e.push(node);
                    e.push(inner);
                }
                View::Prim {
                    args: inner_args,
                    primitive,
                } => {
                    let inner = &b.primitive(primitive).primitive;
                    if !forwards_params(b, inner, params, inner_args, &outer) {
                        return Changed::No;
                    }
                    let inner = inner.clone();
                    for &arg in &outer {
                        e.detach(arg);
                    }
                    let primitive = e.intern_prim(inner, loc);
                    e.put(
                        node,
                        View::Prim {
                            args: &outer,
                            primitive,
                        },
                        0,
                    );
                    e.push(node);
                }
                View::Seq { first, second } => {
                    let Some((inner, inner_args)) = prim_of(first) else {
                        return Changed::No;
                    };
                    if b.node(second).op() != Op::Const
                        || !forwards_params(b, inner, params, inner_args, &outer)
                    {
                        return Changed::No;
                    }
                    let inner = inner.clone();
                    let weight = e.weight(node);
                    for &arg in &outer {
                        e.detach(arg);
                    }
                    e.detach(second);
                    let primitive = e.intern_prim(inner, loc);
                    let inner = e.node(
                        View::Prim {
                            args: &outer,
                            primitive,
                        },
                        0,
                        weight,
                    );
                    e.put(
                        node,
                        View::Seq {
                            first: inner,
                            second,
                        },
                        0,
                    );
                    // `prim(inner)` first, then `seq(inner, second)`.
                    e.push(node);
                    e.push(inner);
                }
                _ => return Changed::No,
            }
            fired(e, N13)
        }
        View::Let {
            var,
            value: Some(value),
            body,
        } if b.node(body).op() == Op::Fun => {
            let kind = b.node(callee).aux();
            let aux = b.node(node).aux();
            let weight = e.weight(node);
            e.detach(value);
            e.detach(body);
            for &arg in &outer {
                e.detach(arg);
            }
            // The binding moves: free the old `let` before the new one binds.
            e.detach(callee);
            e.release(callee);
            let inner = e.node(
                View::Apply {
                    callee: body,
                    args: &outer,
                    info,
                },
                aux,
                weight,
            );
            e.put(
                node,
                View::Let {
                    var,
                    value: Some(value),
                    body: inner,
                },
                kind,
            );
            // `self.apply(body, args, info)`.
            e.push(inner);
            fired(e, N14)
        }
        _ => Changed::No,
    }
}

#[cfg(test)]
mod tests {
    //! Every row against its oracle: the same children given to the legacy
    //! smart constructor and, built plainly and imported, to the rule.
    use super::*;
    use crate::bir::bridge::{export_lambda, import_lambda};
    use crate::ident::{Ident, IdentFlags};
    use crate::lambda::arena::{Lam, LamArena, SwitchSpec};
    use crate::lambda::lam_compat::LetKind;
    use crate::lambda::lam_primitive::Mutable;
    use crate::lambda::{ApInfo, ApplyStatus, FunctionAttribute, LamLoc};

    fn id(name: &str, stamp: i32) -> Ident {
        Ident::new(name, stamp, IdentFlags::NONE)
    }
    fn dump(a: &LamArena, root: Lam) -> String {
        let mut out = Vec::new();
        crate::lambda::sexp_lambda::print_lambda(&a.export(root), &mut out).unwrap();
        String::from_utf8(out).unwrap()
    }
    /// `build(arena, smart)` builds the same node with the smart constructor
    /// or its plain counterpart. Returns the row counters of the rules.
    fn agrees(build: impl Fn(&mut LamArena, bool) -> Lam) -> [u32; ROWS] {
        let mut legacy = LamArena::new();
        let expected = build(&mut legacy, true);
        let expected = dump(&legacy, expected);
        let mut raw = LamArena::new();
        let root = build(&mut raw, false);
        let mut imported = import_lambda(&raw, root).unwrap();
        let fired = {
            let mut engine = Engine::new(&mut imported.arena);
            engine.normalise(imported.root);
            engine.stats.fired
        };
        imported.arena.validate(Some(imported.root)).unwrap();
        let exported = export_lambda(&imported).unwrap();
        assert_eq!(dump(&exported.arena, exported.root), expected);
        fired
    }
    fn int(a: &mut LamArena, i: i32) -> Lam {
        a.const_(C::int(i))
    }
    fn string(a: &mut LamArena, s: &str) -> Lam {
        a.const_(C::String(s.to_owned()))
    }
    fn prim(a: &mut LamArena, smart: bool, p: Primitive, args: &[Lam]) -> Lam {
        if smart {
            a.prim(p, args, LamLoc::NONE)
        } else {
            a.prim_raw(p, args, LamLoc::NONE)
        }
    }
    fn call(a: &mut LamArena, name: &str, stamp: i32) -> Lam {
        let f = a.var(id(name, stamp));
        let unit = a.unit();
        a.apply_raw(
            f,
            &[unit],
            ApInfo {
                loc: LamLoc::NONE,
                status: ApplyStatus::Uncurry,
            },
        )
    }
    fn only(fired: [u32; ROWS], rows: &[(usize, u32)]) {
        let mut expected = [0; ROWS];
        for &(row, count) in rows {
            expected[row] = count;
        }
        assert_eq!(fired, expected);
    }

    #[test]
    fn n1_unary_folds() {
        only(
            agrees(|a, smart| {
                let one = int(a, 1);
                prim(a, smart, Primitive::Pnegint, &[one])
            }),
            &[(N1, 1)],
        );
        // `String.length("héllo")` counts UTF-16 units.
        only(
            agrees(|a, smart| {
                let s = string(a, "h\u{e9}llo \u{1f600}");
                prim(a, smart, Primitive::Pstringlength, &[s])
            }),
            &[(N1, 1)],
        );
        only(
            agrees(|a, smart| {
                let t = a.true_();
                prim(a, smart, Primitive::Pnot, &[t])
            }),
            &[(N1, 1)],
        );
        for spelling in ["3.7", "-0.5", "1e40", "nan", "0x1p3", "1_0.0"] {
            agrees(|a, smart| {
                let f = a.const_(C::Float(spelling.to_owned()));
                prim(a, smart, Primitive::Pintoffloat, &[f])
            });
        }
        // Not a fold: negating a variable.
        only(
            agrees(|a, smart| {
                let x = a.var(id("x", 1));
                prim(a, smart, Primitive::Pnegint, &[x])
            }),
            &[],
        );
    }

    #[test]
    fn n2_binary_folds() {
        let ints = [
            Primitive::Paddint,
            Primitive::Psubint,
            Primitive::Pmulint,
            Primitive::Pdivint,
            Primitive::Pmodint,
            Primitive::Pandint,
            Primitive::Porint,
            Primitive::Pxorint,
            Primitive::Plslint,
            Primitive::Plsrint,
            Primitive::Pasrint,
            Primitive::Pintcomp(Comparison::Lt),
            Primitive::Pintcomp(Comparison::Eq),
        ];
        for p in ints {
            for (x, y) in [
                (7, 2),
                (-7, 2),
                (i32::MAX, 1),
                (i32::MIN, -1),
                (5, 0),
                (1, 33),
            ] {
                agrees(|a, smart| {
                    let (x, y) = (int(a, x), int(a, y));
                    prim(a, smart, p.clone(), &[x, y])
                });
            }
        }
        only(
            agrees(|a, smart| {
                let (x, y) = (string(a, "a"), string(a, "b"));
                prim(a, smart, Primitive::Pstringadd, &[x, y])
            }),
            &[(N2, 1)],
        );
        agrees(|a, smart| {
            let (s, i) = (string(a, "h\u{e9}llo"), int(a, 1));
            prim(a, smart, Primitive::Pstringrefu, &[s, i])
        });
        agrees(|a, smart| {
            let (s, i) = (string(a, "abc"), int(a, 9));
            prim(a, smart, Primitive::Pstringrefs, &[s, i])
        });
        for (x, y) in [("1.5", "2.5"), ("nan", "nan"), ("0x1p0", "1.0")] {
            agrees(|a, smart| {
                let x = a.const_(C::Float(x.to_owned()));
                let y = a.const_(C::Float(y.to_owned()));
                prim(a, smart, Primitive::Pfloatcomp(Comparison::Lt), &[x, y])
            });
        }
        for op in [Comparison::Eq, Comparison::Neq] {
            agrees(|a, smart| {
                let x = a.const_(C::Pointer("a".to_owned()));
                let y = a.const_(C::Pointer("b".to_owned()));
                prim(a, smart, Primitive::Pintcomp(op), &[x, y])
            });
        }
        for p in [Primitive::Psequand, Primitive::Psequor] {
            for (x, y) in [(true, true), (true, false), (false, true), (false, false)] {
                agrees(|a, smart| {
                    let x = a.const_(if x { C::JsTrue } else { C::JsFalse });
                    let y = a.const_(if y { C::JsTrue } else { C::JsFalse });
                    prim(a, smart, p.clone(), &[x, y])
                });
            }
        }
    }

    fn module_block(a: &mut LamArena, smart: bool, sources: [&str; 2], names: [&str; 2]) -> Lam {
        let fields: Vec<Lam> = (0..2)
            .map(|i| {
                let m = a.global_module(Ident::create_persistent(sources[i]));
                a.prim_raw(
                    Primitive::Pfield(
                        i as i32,
                        FieldDbgInfo::Module {
                            name: crate::name::Name::new(names[i]),
                        },
                    ),
                    &[m],
                    LamLoc::NONE,
                )
            })
            .collect();
        prim(
            a,
            smart,
            Primitive::Pmakeblock(
                TagInfo::Module(vec!["make".to_owned(), "get".to_owned()]),
                Mutable::Immutable,
            ),
            &fields,
        )
    }

    #[test]
    fn n3_module_alias() {
        // `module M = Belt_Map` after inclusion: every field of one module.
        only(
            agrees(|a, smart| module_block(a, smart, ["Belt_Map", "Belt_Map"], ["make", "get"])),
            &[(N3, 1)],
        );
        only(
            agrees(|a, smart| module_block(a, smart, ["Belt_Map", "Belt_Set"], ["make", "get"])),
            &[],
        );
        only(
            agrees(|a, smart| module_block(a, smart, ["Belt_Map", "Belt_Map"], ["get", "make"])),
            &[],
        );
    }

    fn if_node(a: &mut LamArena, smart: bool, c: Lam, t: Lam, e: Lam) -> Lam {
        if smart {
            a.if_(c, t, e)
        } else {
            a.if_raw(c, t, e)
        }
    }
    fn compare(a: &mut LamArena, cmp: Comparison) -> Lam {
        let x = a.var(id("x", 1));
        let y = a.var(id("y", 2));
        a.prim_raw(Primitive::Pintcomp(cmp), &[x, y], LamLoc::NONE)
    }

    #[test]
    fn n4_constant_condition() {
        for c in [
            C::JsTrue,
            C::JsFalse,
            C::int(0),
            C::String(String::new()),
            C::JsNull,
        ] {
            only(
                agrees(|a, smart| {
                    let c = a.const_(c.clone());
                    let t = call(a, "f", 1);
                    let e = call(a, "g", 2);
                    if_node(a, smart, c, t, e)
                }),
                &[(N4, 1)],
            );
        }
    }

    #[test]
    fn n5_assert_false_branch() {
        let assert_false = |a: &mut LamArena| {
            a.const_(C::Int {
                i: 0,
                comment: Some(Box::new(PointerInfo::AssertFalse)),
            })
        };
        // A match with an unreachable arm: `if c then x else assert false`.
        only(
            agrees(|a, smart| {
                let c = compare(a, Comparison::Lt);
                let t = call(a, "f", 3);
                let e = assert_false(a);
                if_node(a, smart, c, t, e)
            }),
            &[(N5, 1)],
        );
        only(
            agrees(|a, smart| {
                let c = compare(a, Comparison::Lt);
                let t = assert_false(a);
                let e = call(a, "f", 3);
                if_node(a, smart, c, t, e)
            }),
            &[(N5, 1)],
        );
        // The sequence it builds is normalised: a null check on a call.
        only(
            agrees(|a, smart| {
                let inner = call(a, "f", 3);
                let c = a.prim_raw(Primitive::PnullToOpt, &[inner], LamLoc::NONE);
                let t = call(a, "g", 4);
                let e = assert_false(a);
                if_node(a, smart, c, t, e)
            }),
            &[(N5, 1), (N9, 1)],
        );
    }

    #[test]
    fn n6_n7_boolean_branches() {
        only(
            agrees(|a, smart| {
                let c = compare(a, Comparison::Eq);
                let (t, e) = (a.true_(), a.false_());
                if_node(a, smart, c, t, e)
            }),
            &[(N6, 1)],
        );
        // `x != y` negated is `x == y`.
        only(
            agrees(|a, smart| {
                let c = compare(a, Comparison::Neq);
                let (t, e) = (a.false_(), a.true_());
                if_node(a, smart, c, t, e)
            }),
            &[(N7, 1)],
        );
        only(
            agrees(|a, smart| {
                let c = compare(a, Comparison::Lt);
                let (t, e) = (a.false_(), a.true_());
                if_node(a, smart, c, t, e)
            }),
            &[(N7, 1)],
        );
        // A call is not known to be boolean.
        for swap in [false, true] {
            only(
                agrees(|a, smart| {
                    let c = call(a, "f", 1);
                    let (t, e) = if swap {
                        (a.false_(), a.true_())
                    } else {
                        (a.true_(), a.false_())
                    };
                    if_node(a, smart, c, t, e)
                }),
                &[],
            );
        }
    }

    fn seq_node(a: &mut LamArena, smart: bool, first: Lam, second: Lam) -> Lam {
        if smart {
            a.seq(first, second)
        } else {
            a.seq_raw(first, second)
        }
    }
    fn tuple(a: &mut LamArena, args: &[Lam]) -> Lam {
        a.prim_raw(
            Primitive::Pmakeblock(TagInfo::Tuple, Mutable::Immutable),
            args,
            LamLoc::NONE,
        )
    }

    #[test]
    fn n8_block_in_statement_position() {
        // `(f(), g(), h())->ignore`.
        for n in 0..5 {
            agrees(|a, smart| {
                let args: Vec<Lam> = (0..n).map(|i| call(a, "f", i + 1)).collect();
                let first = tuple(a, &args);
                let second = a.unit();
                seq_node(a, smart, first, second)
            });
        }
        // Nested in first position, and a conversion as first argument.
        only(
            agrees(|a, smart| {
                let (f, g, h) = (call(a, "f", 1), call(a, "g", 2), call(a, "h", 3));
                let inner = tuple(a, &[f, g]);
                let first = tuple(a, &[inner, h]);
                let second = a.unit();
                seq_node(a, smart, first, second)
            }),
            &[(N8, 2)],
        );
        only(
            agrees(|a, smart| {
                let (f, g) = (call(a, "f", 1), call(a, "g", 2));
                let conv = a.prim_raw(Primitive::PnullUndefinedToOpt, &[f], LamLoc::NONE);
                let first = tuple(a, &[conv, g]);
                let second = a.unit();
                seq_node(a, smart, first, second)
            }),
            &[(N8, 1), (N9, 1)],
        );
    }

    #[test]
    fn n9_conversion_in_statement_position() {
        only(
            agrees(|a, smart| {
                let f = call(a, "f", 1);
                let first = a.prim_raw(Primitive::PnullToOpt, &[f], LamLoc::NONE);
                let second = a.unit();
                seq_node(a, smart, first, second)
            }),
            &[(N9, 1)],
        );
    }

    fn int_switch(a: &mut LamArena, smart: bool, scrut: Lam, default: bool) -> Lam {
        let spec = SwitchSpec {
            consts_full: !default,
            consts: vec![
                (SwitchKey::Int(0), call(a, "f", 1)),
                (SwitchKey::Int(1), call(a, "g", 2)),
            ],
            blocks_full: true,
            blocks: vec![],
            fail: default.then(|| call(a, "h", 3)),
            dispatch: SwitchDispatch::Direct,
        };
        if smart {
            a.switch(scrut, spec)
        } else {
            let actions: Vec<Lam> = spec
                .consts
                .iter()
                .map(|(_, l)| *l)
                .chain(spec.fail)
                .collect();
            let actions = a.add_list(&actions);
            let info = a.add_switch(
                spec.consts_full,
                spec.consts.into_iter().map(|(k, _)| k),
                true,
                std::iter::empty(),
                default,
                SwitchDispatch::Direct,
            );
            a.switch_raw(scrut, actions, info)
        }
    }

    #[test]
    fn n10_switch_on_constant() {
        for (value, default) in [(0, false), (1, true), (7, true), (7, false)] {
            let fired = agrees(|a, smart| {
                let scrut = int(a, value);
                int_switch(a, smart, scrut, default)
            });
            only(
                fired,
                if value < 2 || default {
                    &[(N10, 1)]
                } else {
                    &[]
                },
            );
        }
        only(
            agrees(|a, smart| {
                let scrut = a.var(id("x", 9));
                int_switch(a, smart, scrut, true)
            }),
            &[],
        );
    }

    /// `@unboxed type t = Empty | S(string) | N(float)`.
    fn untagged_switch(a: &mut LamArena, smart: bool, scrut: Lam, same_bodies: bool) -> Lam {
        use crate::types::*;
        let block = |name: &str, block_type: VariantBlockType| {
            SwitchKey::Constructor(VariantConstructorCase::Block(VariantBlock::Untagged {
                tag: VariantTag {
                    name: crate::name::Name::new(name),
                    literal: VariantLiteralTag::String(name.to_owned()),
                },
                block_type,
            }))
        };
        let empty = SwitchKey::Constructor(VariantConstructorCase::Constant(VariantTag {
            name: crate::name::Name::new("Empty"),
            literal: VariantLiteralTag::Undefined,
        }));
        let dispatch = SwitchDispatch::Variant(VariantMatchingFacts {
            tag_name: None,
            block_types: vec![VariantBlockType::String, VariantBlockType::Number],
            literal_tags: vec![VariantLiteralTag::Undefined],
        });
        let g = if same_bodies { "f" } else { "g" };
        let actions = [
            call(a, "f", 1),
            call(a, g, if same_bodies { 1 } else { 2 }),
            call(a, "h", 3),
        ];
        if smart {
            a.switch(
                scrut,
                SwitchSpec {
                    consts_full: true,
                    consts: vec![(empty, actions[0])],
                    blocks_full: true,
                    blocks: vec![
                        (block("S", VariantBlockType::String), actions[1]),
                        (block("N", VariantBlockType::Number), actions[2]),
                    ],
                    fail: None,
                    dispatch,
                },
            )
        } else {
            let list = a.add_list(&actions);
            let info = a.add_switch(
                true,
                [empty],
                true,
                [
                    block("S", VariantBlockType::String),
                    block("N", VariantBlockType::Number),
                ],
                false,
                dispatch,
            );
            a.switch_raw(scrut, list, info)
        }
    }

    #[test]
    fn n11_untagged_switch_on_constant() {
        let scrutinees = [
            C::String("x".to_owned()),
            C::int(3),
            C::Float("1.5".to_owned()),
            C::JsUndefined { is_unit: false },
            C::JsTrue,
            C::JsNull,
        ];
        for same_bodies in [false, true] {
            let mut decided = 0;
            for c in &scrutinees {
                let fired = agrees(|a, smart| {
                    let scrut = a.const_(c.clone());
                    untagged_switch(a, smart, scrut, same_bodies)
                });
                assert_eq!(fired[N10], 0);
                decided += fired[N11];
            }
            assert!(decided >= 4, "{decided}");
        }
    }

    fn str_switch_node(a: &mut LamArena, smart: bool, scrut: Lam, default: bool) -> Lam {
        let cases = [("a", call(a, "f", 1)), ("b", call(a, "g", 2))];
        let default = default.then(|| call(a, "h", 3));
        if smart {
            a.string_switch(scrut, &cases, default)
        } else {
            let actions: Vec<Lam> = cases.iter().map(|(_, l)| *l).chain(default).collect();
            let actions = a.add_list(&actions);
            let info = a.add_str_switch(cases.iter().map(|(k, _)| *k), default.is_some());
            a.string_switch_raw(scrut, actions, info)
        }
    }

    #[test]
    fn n12_string_switch_on_constant() {
        for (value, default) in [("a", false), ("b", true), ("z", true), ("z", false)] {
            let fired = agrees(|a, smart| {
                let scrut = string(a, value);
                str_switch_node(a, smart, scrut, default)
            });
            only(
                fired,
                if value != "z" || default {
                    &[(N12, 1)]
                } else {
                    &[]
                },
            );
        }
    }

    fn apply_node(a: &mut LamArena, smart: bool, func: Lam, args: &[Lam]) -> Lam {
        let info = ApInfo {
            loc: LamLoc::NONE,
            status: ApplyStatus::Uncurry,
        };
        if smart {
            a.apply(func, args, info)
        } else {
            a.apply_raw(func, args, info)
        }
    }
    fn forwarder(a: &mut LamArena, p: Primitive, attr: FunctionAttribute) -> Lam {
        let (x, y) = (id("x", 11), id("y", 12));
        let (vx, vy) = (a.var(x), a.var(y));
        let body = a.prim_raw(p, &[vx, vy], LamLoc::NONE);
        a.function_(2, &[x, y], body, attr, LamLoc::NONE)
    }

    #[test]
    fn n13_eta_reduction() {
        // `((x, y) => x + y)(1, 2)`: the external's wrapper applied, then folded.
        only(
            agrees(|a, smart| {
                let f = forwarder(a, Primitive::Paddint, FunctionAttribute::default());
                let args = [int(a, 1), int(a, 2)];
                apply_node(a, smart, f, &args)
            }),
            &[(N13, 1), (N2, 1)],
        );
        // `&&` may skip its right operand: only for an argument that does nothing.
        only(
            agrees(|a, smart| {
                let f = forwarder(a, Primitive::Psequand, FunctionAttribute::default());
                let args = [call(a, "f", 1), call(a, "g", 2)];
                apply_node(a, smart, f, &args)
            }),
            &[],
        );
        only(
            agrees(|a, smart| {
                let f = forwarder(a, Primitive::Psequand, FunctionAttribute::default());
                let args = [call(a, "f", 1), a.var(id("b", 2))];
                apply_node(a, smart, f, &args)
            }),
            &[(N13, 1)],
        );
        // An async function stays a function.
        only(
            agrees(|a, smart| {
                let attr = FunctionAttribute {
                    async_: true,
                    ..FunctionAttribute::default()
                };
                let f = forwarder(a, Primitive::Paddint, attr);
                let args = [int(a, 1), int(a, 2)];
                apply_node(a, smart, f, &args)
            }),
            &[],
        );
        // `x => Nullable.toOption(get(x))` and `x => (set(x); ())`.
        only(
            agrees(|a, smart| {
                let x = id("x", 11);
                let vx = a.var(x);
                let inner = a.prim_raw(Primitive::Pnegint, &[vx], LamLoc::NONE);
                let body = a.prim_raw(Primitive::PnullToOpt, &[inner], LamLoc::NONE);
                let f = a.function_(1, &[x], body, FunctionAttribute::default(), LamLoc::NONE);
                let args = [call(a, "f", 1)];
                apply_node(a, smart, f, &args)
            }),
            &[(N13, 1)],
        );
        only(
            agrees(|a, smart| {
                let x = id("x", 11);
                let vx = a.var(x);
                let inner = a.prim_raw(Primitive::PnullToOpt, &[vx], LamLoc::NONE);
                let unit = a.unit();
                let body = a.seq_raw(inner, unit);
                let f = a.function_(1, &[x], body, FunctionAttribute::default(), LamLoc::NONE);
                let args = [call(a, "f", 1)];
                apply_node(a, smart, f, &args)
            }),
            &[(N13, 1), (N9, 1)],
        );
        // Parameters out of order, or too few arguments: no reduction.
        only(
            agrees(|a, smart| {
                let (x, y) = (id("x", 11), id("y", 12));
                let (vx, vy) = (a.var(x), a.var(y));
                let body = a.prim_raw(Primitive::Psubint, &[vy, vx], LamLoc::NONE);
                let f = a.function_(2, &[x, y], body, FunctionAttribute::default(), LamLoc::NONE);
                let args = [int(a, 1), int(a, 2)];
                apply_node(a, smart, f, &args)
            }),
            &[],
        );
        only(
            agrees(|a, smart| {
                let f = forwarder(a, Primitive::Paddint, FunctionAttribute::default());
                let args = [int(a, 1)];
                apply_node(a, smart, f, &args)
            }),
            &[],
        );
    }

    #[test]
    fn n14_application_under_let() {
        // A curried external applied in one go: `(let t = f() in (x, y) => x + y)(1, 2)`.
        only(
            agrees(|a, smart| {
                let value = call(a, "f", 1);
                let f = forwarder(a, Primitive::Paddint, FunctionAttribute::default());
                let func = a.let_(LetKind::Strict, id("t", 20), value, f);
                let args = [int(a, 1), int(a, 2)];
                apply_node(a, smart, func, &args)
            }),
            &[(N14, 1), (N13, 1), (N2, 1)],
        );
        // A `let` whose body is not a function is left.
        only(
            agrees(|a, smart| {
                let value = call(a, "f", 1);
                let body = a.var(id("g", 2));
                let func = a.let_(LetKind::Strict, id("t", 20), value, body);
                let args = [int(a, 1)];
                apply_node(a, smart, func, &args)
            }),
            &[],
        );
    }
}

#[cfg(test)]
mod cost_tests {
    //! The costs the engine states, pinned as step counts. A step is one
    //! node read, one node allocation or one worklist push.
    use super::*;
    use crate::bir::engine::testing::{call, id, import, prim};
    use crate::bir::engine::{Facts, OpMask, Order, Round};
    use crate::lambda::arena::{Lam, LamArena};
    use crate::lambda::lam_compat::LetKind;
    use crate::lambda::lam_primitive::Mutable;
    use crate::lambda::{ApInfo, ApplyStatus, FunctionAttribute, LamLoc, SwitchDispatch};

    const N: u64 = 10_000;

    fn big(a: &mut LamArena) -> Lam {
        let mut root = a.unit();
        for _ in 0..N {
            let statement = call(a, "f", 1);
            root = a.seq_raw(statement, root);
        }
        root
    }

    #[test]
    fn an_attempt_reads_the_pattern_not_the_subtrees() {
        let mut a = LamArena::new();
        let cond = call(&mut a, "c", 2);
        let (then_, else_) = (big(&mut a), big(&mut a));
        let root = a.if_raw(cond, then_, else_);
        let mut unit = import(&a, root);
        let mut e = Engine::new(&mut unit.arena);
        assert_eq!(e.normalise(unit.root), Changed::No);
        println!(
            "COST attempt on an if over two 40,000-node branches: {} steps",
            e.steps()
        );
        assert!(e.steps() <= 12, "{}", e.steps());
    }

    #[test]
    fn replacing_a_node_by_its_child_costs_the_removed_nodes() {
        let mut a = LamArena::new();
        let cond = a.true_();
        let (then_, else_) = (big(&mut a), a.unit());
        let root = a.if_raw(cond, then_, else_);
        let mut unit = import(&a, root);
        let mut e = Engine::new(&mut unit.arena);
        assert_eq!(e.normalise(unit.root), Changed::Yes);
        println!(
            "COST if true over a 40,000-node branch: {} steps",
            e.steps()
        );
        assert!(e.steps() <= 64, "{}", e.steps());
        unit.arena.validate(Some(unit.root)).unwrap();
    }

    fn pass(name: &str, a: &LamArena, root: Lam, nodes: u64, row: usize, rewrites: u32) {
        let mut unit = import(a, root);
        let mut e = Engine::new(&mut unit.arena);
        assert_eq!(e.normalise_tree(unit.root), Changed::Yes);
        println!(
            "COST normalising pass, {name}: {nodes} nodes, {rewrites} rewrites, {} steps",
            e.steps()
        );
        assert_eq!(e.stats.fired[row], rewrites);
        assert!(e.steps() <= 32 * nodes, "{}", e.steps());
        unit.arena.validate(Some(unit.root)).unwrap();
    }

    #[test]
    fn a_normalising_pass_is_linear_in_a_deep_chain() {
        // 10,000 nested sequences, each headed by a conversion (N9).
        let mut a = LamArena::new();
        let mut root = a.unit();
        for _ in 0..N {
            let inner = call(&mut a, "f", 1);
            let first = prim(&mut a, Primitive::PnullToOpt, &[inner]);
            root = a.seq_raw(first, root);
        }
        pass("10,000 nested sequences", &a, root, 5 * N + 1, N9, N as u32);
        // 10,000 nested conditionals on `true`: each collapses into the next.
        let mut a = LamArena::new();
        let mut root = call(&mut a, "f", 1);
        for _ in 0..N {
            let (cond, else_) = (a.true_(), a.unit());
            root = a.if_raw(cond, root, else_);
        }
        pass(
            "10,000 nested conditionals",
            &a,
            root,
            3 * N + 3,
            N4,
            N as u32,
        );
        // 10,000 nested lets, each binding `1 + 2`.
        let mut a = LamArena::new();
        let mut root = a.unit();
        for i in 0..N {
            let (x, y) = (a.const_(C::int(1)), a.const_(C::int(2)));
            let value = prim(&mut a, Primitive::Paddint, &[x, y]);
            root = a.let_(LetKind::Strict, id("x", i as i32 + 1), value, root);
        }
        pass("10,000 nested lets", &a, root, 4 * N + 1, N2, N as u32);
    }

    #[test]
    fn a_normalising_pass_is_linear_in_a_wide_node() {
        // A 10,000-element tuple in statement position (N8).
        let mut a = LamArena::new();
        let elements: Vec<Lam> = (0..N).map(|_| call(&mut a, "f", 1)).collect();
        let first = prim(
            &mut a,
            Primitive::Pmakeblock(TagInfo::Tuple, Mutable::Immutable),
            &elements,
        );
        let second = a.unit();
        let root = a.seq_raw(first, second);
        pass(
            "10,000-wide block in a sequence",
            &a,
            root,
            3 * N + 3,
            N8,
            1,
        );
        // A module block of 10,000 fields of one module (N3), and 10,000
        // foldable children of one block (N2 below a wide parent).
        let mut a = LamArena::new();
        let names: Vec<String> = (0..N).map(|i| format!("f{i}")).collect();
        let fields: Vec<Lam> = names
            .iter()
            .enumerate()
            .map(|(i, name)| {
                let m = a.global_module(crate::ident::Ident::create_persistent("M"));
                prim(
                    &mut a,
                    Primitive::Pfield(
                        i as i32,
                        FieldDbgInfo::Module {
                            name: crate::name::Name::new(name),
                        },
                    ),
                    &[m],
                )
            })
            .collect();
        let root = prim(
            &mut a,
            Primitive::Pmakeblock(TagInfo::Module(names), Mutable::Immutable),
            &fields,
        );
        pass("10,000-field module alias", &a, root, 2 * N + 1, N3, 1);
        let mut a = LamArena::new();
        let elements: Vec<Lam> = (0..N)
            .map(|_| {
                let (x, y) = (a.const_(C::int(1)), a.const_(C::int(2)));
                prim(&mut a, Primitive::Paddint, &[x, y])
            })
            .collect();
        let root = prim(
            &mut a,
            Primitive::Pmakeblock(TagInfo::Tuple, Mutable::Immutable),
            &elements,
        );
        pass(
            "10,000 folds below one block",
            &a,
            root,
            3 * N + 1,
            N2,
            N as u32,
        );
    }

    #[test]
    fn a_normalising_pass_is_linear_inside_a_doubled_switch_default() {
        let mut a = LamArena::new();
        let x = id("x", 1);
        let mut chain = a.var(x);
        for _ in 0..N {
            let inner = a.var(x);
            let first = prim(
                &mut a,
                Primitive::Pmakeblock(TagInfo::Tuple, Mutable::Immutable),
                &[inner],
            );
            chain = a.seq_raw(first, chain);
        }
        let case = a.unit();
        let actions = a.add_list(&[case, chain]);
        let info = a.add_switch(
            false,
            [SwitchKey::Int(0)],
            false,
            std::iter::empty(),
            true,
            SwitchDispatch::Direct,
        );
        let scrut = a.var(id("c", 2));
        let switch = a.switch_raw(scrut, actions, info);
        let value = a.unit();
        let root = a.let_(LetKind::Strict, x, value, switch);
        pass(
            "10,000 rewrites in a doubled default",
            &a,
            root,
            3 * N + 5,
            N8,
            N as u32,
        );
    }

    fn drop_identity(e: &mut Engine<'_>, node: NodeId) -> Changed {
        let arg = match e.bir().view(node) {
            View::Prim {
                args: [arg],
                primitive,
            } if matches!(e.bir().primitive(primitive).primitive, Primitive::Pidentity) => *arg,
            _ => return Changed::No,
        };
        e.promote(node, arg);
        Changed::Yes
    }

    #[test]
    fn the_way_back_up_a_sweep_renormalises_what_shallow_map_rebuilds() {
        // let r = ((x, y) => identity(x + y))(1, 2) in r: once a pass rule
        // removes `identity`, the application above it is an eta redex.
        let build = |a: &mut LamArena| {
            let (x, y) = (id("x", 1), id("y", 2));
            let (vx, vy) = (a.var(x), a.var(y));
            let sum = prim(a, Primitive::Paddint, &[vx, vy]);
            let body = prim(a, Primitive::Pidentity, &[sum]);
            let f = a.function_(2, &[x, y], body, FunctionAttribute::default(), LamLoc::NONE);
            let args = [a.const_(C::int(1)), a.const_(C::int(2))];
            let info = ApInfo {
                loc: LamLoc::NONE,
                status: ApplyStatus::Uncurry,
            };
            let value = a.apply_raw(f, &args, info);
            let r = id("r", 3);
            let body = a.var(r);
            a.let_(LetKind::Strict, r, value, body)
        };
        for (renorm, expected) in [(OpMask::SHALLOW_MAP, Op::Const), (OpMask::NONE, Op::Apply)] {
            let mut a = LamArena::new();
            let root = build(&mut a);
            let mut unit = import(&a, root);
            let mut e = Engine::new(&mut unit.arena);
            let round = Round {
                name: "test",
                mask: OpMask::PRIM,
                order: Order::Post,
                renorm,
                facts: Facts::Current,
                guard: None,
                rule: drop_identity,
            };
            assert_eq!(e.run(&round, unit.root), Changed::Yes);
            let View::Let {
                value: Some(value), ..
            } = e.bir().view(unit.root)
            else {
                panic!()
            };
            assert_eq!(e.bir().node(value).op(), expected);
            let cascaded = u32::from(expected == Op::Const);
            assert_eq!(
                (e.stats.fired[N13], e.stats.fired[N2]),
                (cascaded, cascaded)
            );
            unit.arena.validate(Some(unit.root)).unwrap();
        }
    }
}
