//! J normalising constructors, indexed by BACKEND_LOWERING section 6.
use crate::bir::{Bir, NodeFlags, NodeId};

/// J-M14, O:339 push_effect_expression: discard a strictly pure effect value.
/// All expression producers supported by S3.3a are strictly pure. Their
/// structural preludes remain on the statement stack; only the value is dropped.
/// Later slices add comma splitting and effectful values when they can occur.
pub(crate) fn discard_pure_effect(bir: &mut Bir, value: NodeId) {
    assert!(bir.node(value).flags().contains(NodeFlags::STRICT));
    bir.release(value);
}

use super::plain as p;
use crate::bir::View;
use crate::js_ir::{BinOp, LengthObject};

/// J-E1, B:398 string_append. The work stack replaces both recursive calls;
/// every successful reassociation removes at least one input append node.
pub fn je1_string_append(b: &mut Bir, mut left: NodeId, mut right: NodeId) -> NodeId {
    let mut suffix = Vec::new();
    loop {
        let ls = p::string_of(b, left).map(str::to_owned);
        let rs = p::string_of(b, right).map(str::to_owned);
        let value = match (ls.as_deref(), rs.as_deref()) {
            (Some(""), _) => {
                b.release(left);
                Some(right)
            }
            (_, Some("")) => {
                b.release(right);
                Some(left)
            }
            (Some(l), Some(r)) => {
                let value = p::string(b, &format!("{l}{r}"));
                p::retain(b, &[left, right], &[]);
                Some(value)
            }
            _ => None,
        };
        if let Some(value) = value {
            if let Some(next) = suffix.pop() {
                left = value;
                right = next;
                continue;
            }
            return value;
        }
        if let (View::JStrAppend { left: a, right: be }, View::JStrAppend { left: ce, right: d }) =
            (b.view(left), b.view(right))
        {
            if let (Some(bs), Some(cs)) = (p::string_of(b, be), p::string_of(b, ce)) {
                let text = format!("{bs}{cs}");
                let merged = p::string(b, &text);
                p::copy_cold(b, be, merged);
                p::retain(b, &[left, right], &[a, d]);
                suffix.push(d);
                left = a;
                right = merged;
                continue;
            }
        }
        if let View::JStrAppend { left: be, right: c } = b.view(right) {
            if let (Some(ls), Some(bs)) = (ls.as_deref(), p::string_of(b, be)) {
                let text = format!("{ls}{bs}");
                let merged = p::string(b, &text);
                p::copy_cold(b, left, merged);
                p::retain(b, &[left, right], &[c]);
                left = merged;
                right = c;
                continue;
            }
        }
        if let View::JStrAppend { left: c, right: be } = b.view(left) {
            if let (Some(bs), Some(rs)) = (p::string_of(b, be), rs.as_deref()) {
                let text = format!("{bs}{rs}");
                let merged = p::string(b, &text);
                p::copy_cold(b, be, merged);
                p::retain(b, &[left, right], &[c]);
                left = c;
                right = merged;
                continue;
            }
        }
        let value = p::node(b, View::JStrAppend { left, right }, 0);
        if let Some(next) = suffix.pop() {
            left = value;
            right = next;
        } else {
            return value;
        }
    }
}

/// J-E2, B:453 length. Literal strings use their semantic UTF-16 length.
pub fn je2_length(b: &mut Bir, target: NodeId, kind: LengthObject) -> NodeId {
    let len = match (b.view(target), kind) {
        (View::JArray { values } | View::JBlockLit { values, .. }, LengthObject::Array)
            if p::pure(b, target) =>
        {
            Some(values.len() as i32)
        }
        (_, LengthObject::String) => p::string_of(b, target)
            .map(|s| crate::string_literal::utf16_length(s).expect("valid string literal") as i32),
        (View::JFun { header, .. }, LengthObject::Function) => {
            let h = b.function(header);
            Some(h.params.len() as i32 - i32::from(h.flags & crate::bir::FuncHeader::METHOD != 0))
        }
        _ => None,
    };
    if let Some(len) = len {
        b.release(target);
        p::int(b, len)
    } else {
        p::node(b, View::JLength { value: target }, kind as u16)
    }
}

/// J-E3, B:480 is_null_or_undefined. This row intentionally has no purity guard.
pub fn je3_is_null_or_undefined(b: &mut Bir, target: NodeId) -> NodeId {
    let value = match b.view(target) {
        View::JNull | View::JUndefined => Some(true),
        View::JNumber { .. } | View::JArray { .. } | View::JBlockLit { .. } => Some(false),
        _ => None,
    };
    if let Some(value) = value {
        b.release(target);
        p::boolean(b, value)
    } else {
        p::node(b, View::JIsNullish { value: target }, 0)
    }
}

fn strict_equality(b: &Bir, mut l: NodeId, mut r: NodeId) -> Option<bool> {
    while let (View::JOptional { value: x }, View::JOptional { value: y }) = (b.view(l), b.view(r))
    {
        l = x;
        r = y;
    }
    if let (Some(x), Some(y)) = (p::int_of(b, l), p::int_of(b, r)) {
        return Some(x == y);
    }
    if let (Some(x), Some(y)) = (p::string_of(b, l), p::string_of(b, r)) {
        return Some(x == y);
    }
    let nullish = |n| matches!(b.view(n), View::JNull | View::JUndefined);
    if nullish(l) && nullish(r) {
        return Some(matches!(b.view(l), View::JNull) == matches!(b.view(r), View::JNull));
    }
    for (x, y) in [(l, r), (r, l)] {
        if p::undefined(b, x) && matches!(b.view(y), View::JOptional { .. }) && p::pure(b, y) {
            return Some(false);
        }
        if nullish(x)
            && p::pure(b, y)
            && matches!(
                b.view(y),
                View::JBool
                    | View::JNumber { .. }
                    | View::JTypeof { .. }
                    | View::JFun { .. }
                    | View::JArray { .. }
                    | View::JBlockLit { .. }
            )
        {
            return Some(false);
        }
    }
    None
}

/// J-E4, B:491 bin; helpers B:765, B:685, B:659, B:704, in that order.
pub fn je4_bin(b: &mut Bir, op: BinOp, left: NodeId, right: NodeId) -> NodeId {
    if op == BinOp::Plus {
        if let Some(n) = p::int_of(b, right).filter(|n| *n < 0) {
            let positive = p::int(b, n.wrapping_neg());
            p::copy_cold(b, right, positive);
            if let Some(c) = b.node(right).js_char() {
                b.nodes[positive.index()].set_js_char(c);
            }
            b.release(right);
            return p::bin(b, BinOp::Minus, left, positive);
        }
    }
    if let View::JLength { value } = b.view(left) {
        if p::int_of(b, right) == Some(0) {
            if op == BinOp::Ge && p::pure(b, value) {
                p::retain(b, &[left, right], &[]);
                return p::boolean(b, true);
            }
            if op == BinOp::Gt {
                return p::bin(b, BinOp::NotEqEq, left, right);
            }
        }
    }
    if let (Some(l), Some(r)) = (p::int_of(b, left), p::int_of(b, right)) {
        let (l, r) = (i64::from(l as u32), i64::from(r));
        let folded = match op {
            BinOp::Lt => Some(l < r),
            BinOp::Le => Some(l <= r),
            BinOp::Gt => Some(l > r),
            BinOp::Ge => Some(l >= r),
            _ => None,
        };
        if let Some(value) = folded {
            p::retain(b, &[left, right], &[]);
            return p::boolean(b, value);
        }
    }
    if op == BinOp::EqEqEq {
        if let Some(value) = strict_equality(b, left, right) {
            p::retain(b, &[left, right], &[]);
            return p::boolean(b, value);
        }
    }
    match op {
        BinOp::And => je5_js_and(b, left, right),
        BinOp::Or => je6_js_or(b, left, right),
        _ => p::bin(b, op, left, right),
    }
}

fn repeated_variable(b: &mut Bir, op: BinOp, left: NodeId, right: NodeId) -> Option<NodeId> {
    if p::same_var(b, left, right) {
        b.release(right);
        return Some(left);
    }
    if let Some((rl, rr)) = p::binary(b, right, op) {
        if p::same_var(b, left, rl) {
            b.release(left);
            return Some(right);
        }
        if p::same_var(b, left, rr) {
            p::retain(b, &[left, right], &[rr, rl]);
            return Some(p::bin(b, op, rr, rl));
        }
    }
    None
}

/// J-E5, B:797 js_and. Variable rules precede bounded pure simplification.
pub fn je5_js_and(b: &mut Bir, left: NodeId, right: NodeId) -> NodeId {
    if let Some(value) = repeated_variable(b, BinOp::And, left, right) {
        return value;
    }
    if let (Some((ll, lr)), Some((rl, rr))) = (
        p::binary(b, left, BinOp::NotEqEq),
        p::binary(b, right, BinOp::EqEqEq),
    ) {
        if p::undefined(b, lr)
            && matches!(b.view(rr), View::JStr { .. } | View::JNumber { .. })
            && p::same_var(b, ll, rl)
        {
            b.release(left);
            return right;
        }
    }
    if p::pure(b, left) && p::pure(b, right) {
        if let Some(value) = je9_simplify_and(b, left, right, &mut 0) {
            return value;
        }
    }
    p::bin(b, BinOp::And, left, right)
}

/// J-E6, B:836 js_or. Variable rules precede bounded pure simplification.
pub fn je6_js_or(b: &mut Bir, left: NodeId, right: NodeId) -> NodeId {
    if let Some(value) = repeated_variable(b, BinOp::Or, left, right) {
        return value;
    }
    if p::pure(b, left) && p::pure(b, right) {
        if let Some(value) = je10_simplify_or(b, left, right, &mut 0) {
            return value;
        }
    }
    p::bin(b, BinOp::Or, left, right)
}

/// J-E7, B:512 cond. A loop removes one nested conditional, leading negation,
/// or comma suffix per successful iteration; suffix reconstruction is iterative.
pub fn je7_cond(b: &mut Bir, mut test: NodeId, mut yes: NodeId, mut no: NodeId) -> NodeId {
    let mut suffixes = 0;
    let value = loop {
        if let (
            View::JSeq {
                first: y,
                second: yu,
            },
            View::JSeq {
                first: n,
                second: nu,
            },
        ) = (b.view(yes), b.view(no))
        {
            if p::undefined(b, yu) && p::undefined(b, nu) {
                p::retain(b, &[yes, no], &[y, n]);
                yes = y;
                no = n;
                suffixes += 1;
                continue;
            }
        }
        let selected = match b.view(test) {
            View::JBool => Some(if p::bool_of(b, test) == Some(true) {
                yes
            } else {
                no
            }),
            View::JNumber { .. } if p::int_of(b, test) == Some(0) => Some(no),
            View::JNumber { .. } | View::JArray { .. } | View::JBlockLit { .. }
                if p::pure(b, test) =>
            {
                Some(yes)
            }
            _ => None,
        };
        if let Some(selected) = selected {
            p::retain(b, &[test, yes, no], &[selected]);
            break selected;
        }
        if p::bool_of(b, yes) == Some(true) && p::bool_of(b, no) == Some(false) {
            p::retain(b, &[test, yes, no], &[test]);
            break test;
        }
        if p::equal(b, yes, no) {
            b.release(no);
            if p::pure(b, test) {
                b.release(test);
                break yes;
            }
            break p::seq(b, test, yes);
        }
        if let View::JCond {
            condition: c,
            then_: y,
            else_: n,
        } = b.view(yes)
        {
            if p::equal(b, n, no) {
                p::retain(b, &[yes], &[c, y]);
                test = je5_js_and(b, test, c);
                yes = y;
                continue;
            }
            if p::equal(b, y, no) {
                p::retain(b, &[yes], &[c, n]);
                let c = je8_not(b, c);
                test = je5_js_and(b, test, c);
                yes = n;
                continue;
            }
        }
        if let View::JCond {
            condition: c,
            then_: y,
            else_: n,
        } = b.view(no)
        {
            if p::equal(b, yes, y) {
                p::retain(b, &[no], &[c, n]);
                test = je6_js_or(b, test, c);
                no = n;
                continue;
            }
            if p::equal(b, yes, n) {
                p::retain(b, &[no], &[c, y]);
                let c = je8_not(b, c);
                test = je6_js_or(b, test, c);
                no = y;
                continue;
            }
        }
        if let View::JNot { value: inner } = b.view(test) {
            p::retain(b, &[test], &[inner]);
            if p::int_of(b, no) != Some(0) && !p::undefined(b, no) {
                test = inner;
                std::mem::swap(&mut yes, &mut no);
                continue;
            }
            test = p::node(b, View::JNot { value: inner }, 0);
            break p::node(
                b,
                View::JCond {
                    condition: test,
                    then_: yes,
                    else_: no,
                },
                0,
            );
        }
        if p::bool_of(b, no) == Some(false) && p::pure(b, test) && p::pure(b, yes) {
            if let Some(value) = je9_simplify_and(b, test, yes, &mut 0) {
                b.release(no);
                break value;
            }
        }
        if p::bool_of(b, yes) == Some(false) {
            // A failed speculative simplification must preserve the original test.
            if let Some(value) = super::logic::negated_and(b, test, no, &mut 0) {
                b.release(yes);
                break value;
            }
        }
        break p::node(
            b,
            View::JCond {
                condition: test,
                then_: yes,
                else_: no,
            },
            0,
        );
    };
    let mut value = value;
    for _ in 0..suffixes {
        let u = p::node(b, View::JUndefined, 0);
        value = p::seq(b, value, u);
    }
    value
}

/// J-E8, B:599 not and B:633 push_negation. Negation uses an explicit stack.
pub fn je8_not(b: &mut Bir, value: NodeId) -> NodeId {
    if let Some(result) = p::int_of(b, value)
        .map(|n| n == 0)
        .or_else(|| p::bool_of(b, value).map(|v| !v))
    {
        let result = p::boolean(b, result);
        if let Some(comment) = b.cold(value).and_then(|c| c.comment) {
            b.set_cold(
                result,
                crate::bir::Cold {
                    comment: Some(comment),
                    loc: crate::lambda::LamLoc::NONE,
                },
            );
        }
        b.release(value);
        return result;
    }
    if let View::JNot { value: inner } = b.view(value) {
        p::retain(b, &[value], &[inner]);
        return inner;
    }
    if let View::JBin { left, right } = b.view(value) {
        let op = b.node(value).aux();
        for (a, z) in [
            (BinOp::EqEqEq, BinOp::NotEqEq),
            (BinOp::NotEqEq, BinOp::EqEqEq),
            (BinOp::Lt, BinOp::Ge),
            (BinOp::Ge, BinOp::Lt),
            (BinOp::Le, BinOp::Gt),
            (BinOp::Gt, BinOp::Le),
        ] {
            if op == a as u16 {
                b.detach(left);
                b.detach(right);
                let result = p::bin(b, z, left, right);
                p::copy_cold(b, value, result);
                b.release(value);
                return result;
            }
        }
    }
    if let Some(result) = super::logic::negate(b, value, &mut 0) {
        result
    } else {
        p::node(b, View::JNot { value }, 0)
    }
}

/// J-E9, B:956 simplify_and_. Pure operands only. Returns None without consuming
/// either input. Recursion is bounded by the legacy depth budget (n > 10).
pub fn je9_simplify_and(
    b: &mut Bir,
    left: NodeId,
    right: NodeId,
    steps: &mut usize,
) -> Option<NodeId> {
    assert!(p::pure(b, left) && p::pure(b, right));
    super::logic::simplify(b, left, right, false, steps)
}

/// J-E10, B:1148 simplify_or_. De Morgan uses the same bounded J-E9 attempt.
pub fn je10_simplify_or(
    b: &mut Bir,
    left: NodeId,
    right: NodeId,
    steps: &mut usize,
) -> Option<NodeId> {
    assert!(p::pure(b, left) && p::pure(b, right));
    super::logic::simplify(b, left, right, true, steps)
}

/// J-S1, B:1207 exp. Trivial comma arms are stripped iteratively; a surviving
/// comma loses its location but keeps its comment, exactly like the legacy row.
pub fn js1_exp(b: &mut Bir, mut value: NodeId) -> NodeId {
    loop {
        if let View::JSeq { first, second } = b.view(value) {
            let trivial = |id| matches!(b.view(id), View::JNumber { .. } | View::JUndefined);
            let selected = if trivial(first) {
                Some(second)
            } else if trivial(second) {
                Some(first)
            } else {
                None
            };
            if let Some(selected) = selected {
                p::retain(b, &[value], &[selected]);
                value = selected;
                continue;
            }
            let mut flags = b.node(value).flags();
            flags.0 &= !NodeFlags::JS_LOC_PRESENT;
            b.nodes[value.index()].set_flags(flags);
        }
        if matches!(b.view(value), View::JNumber { .. } | View::JUndefined) {
            b.release(value);
            return js2_block(b, vec![]);
        }
        return p::node(b, View::SExp { value }, 0);
    }
}

/// J-S2, B:1225 block. Singleton block shells are consumed, never recursively
/// revisited. Empty/multiple statements produce an explicit block (aux=1).
pub fn js2_block(b: &mut Bir, statements: Vec<NodeId>) -> NodeId {
    let statements = js5_unnest_block(b, statements);
    if let [statement] = statements.as_slice() {
        *statement
    } else {
        p::node(
            b,
            View::SBlock {
                statements: &statements,
            },
            1,
        )
    }
}

/// J-S5, B:1565 unnest_block. Only a single explicit block is flattened.
pub fn js5_unnest_block(b: &mut Bir, mut statements: Vec<NodeId>) -> Vec<NodeId> {
    loop {
        let [statement] = statements.as_slice() else {
            return statements;
        };
        let statement = *statement;
        let View::SBlock { statements: inner } = b.view(statement) else {
            return statements;
        };
        let inner = inner.to_vec();
        p::retain(b, &[statement], &inner);
        statements = inner;
    }
}

/// J-S4, B:1268 normalize. A nonmatching literal switch without a default is
/// invalid in the legacy API too. All nonliteral statements are returned as-is.
pub fn js4_normalize(b: &mut Bir, statement: NodeId) -> NodeId {
    let View::SSwitch {
        scrutinee,
        actions,
        header,
    } = b.view(statement)
    else {
        return statement;
    };
    let h = b.switch(header);
    let selected = if b.node(statement).aux() == 0 {
        let Some(value) = p::int_of(b, scrutinee) else { return statement; };
        h.keys.iter().position(|key| matches!(key, crate::bir::CaseKey::Lambda(crate::lambda::SwitchKey::Int(n)) if *n == value))
    } else {
        let View::JStr { text } = b.view(scrutinee) else { return statement; };
        h.keys.iter().position(|key| matches!(key, crate::bir::CaseKey::JavaScript(crate::lambda::SwitchCaseTag::String(s)) if s == b.text(text)))
    }.or_else(|| h.has_default.then_some(h.keys.len())).expect("literal switch must match a clause or default");
    let action = actions[selected];
    let View::SBlock { statements } = b.view(action) else {
        panic!("switch body must be a statement list");
    };
    let statements = statements.to_vec();
    let comment = b.cold(statement).and_then(|c| c.comment);
    p::retain(b, &[statement], &statements);
    let statements = js5_unnest_block(b, statements);
    if let [statement] = statements.as_slice() {
        return *statement;
    }
    let result = p::node(
        b,
        View::SBlock {
            statements: &statements,
        },
        1,
    );
    if let Some(comment) = comment {
        b.set_cold(
            result,
            crate::bir::Cold {
                comment: Some(comment),
                loc: crate::lambda::LamLoc::NONE,
            },
        );
    }
    result
}

fn single_value(b: &Bir, statements: &[NodeId], return_: bool) -> Option<NodeId> {
    let [statement] = statements else {
        return None;
    };
    match b.view(*statement) {
        View::SReturn { value } if return_ => Some(value),
        View::SExp { value } if !return_ => Some(value),
        _ => None,
    }
}
fn same_assignment_target(b: &Bir, left: NodeId, right: NodeId) -> bool {
    let mut work = vec![(left, right)];
    while let Some((l, r)) = work.pop() {
        match (b.view(l), b.view(r)) {
            (View::Var { .. }, View::Var { .. }) if p::same_var(b, l, r) => {}
            (
                View::JQualified {
                    module: l,
                    member: lm,
                },
                View::JQualified {
                    module: r,
                    member: rm,
                },
            ) if b.pools.j_modules[l.index()] == b.pools.j_modules[r.index()] && lm == rm => {}
            (
                View::JDot {
                    object: l1,
                    property: lp,
                    position: li,
                },
                View::JDot {
                    object: r1,
                    property: rp,
                    position: ri,
                },
            ) if b.node(l).aux() == 0 && b.node(r).aux() == 0 && lp == rp && li == ri => {
                work.push((l1, r1))
            }
            (
                View::JIndex {
                    object: l,
                    index: li,
                },
                View::JIndex {
                    object: r,
                    index: ri,
                },
            ) => {
                work.push((li, ri));
                work.push((l, r));
            }
            _ => return false,
        }
    }
    true
}
fn equal_statements(b: &Bir, left: &[NodeId], right: &[NodeId]) -> bool {
    left.len() == right.len() && left.iter().zip(right).all(|(&l, &r)| p::equal(b, l, r))
}
fn nested_if(b: &Bir, statements: &[NodeId]) -> Option<(NodeId, Vec<NodeId>, Vec<NodeId>)> {
    let [statement] = statements else {
        return None;
    };
    let View::SIf {
        condition,
        then_,
        else_,
    } = b.view(*statement)
    else {
        return None;
    };
    let View::SBlock { statements: yes } = b.view(then_) else {
        panic!("if body list");
    };
    let no = else_.map_or(&[][..], |no| match b.view(no) {
        View::SBlock { statements } => statements,
        _ => panic!("if body list"),
    });
    Some((condition, yes.to_vec(), no.to_vec()))
}
fn raw_if(b: &mut Bir, condition: NodeId, yes: Vec<NodeId>, no: Vec<NodeId>) -> NodeId {
    let then_ = p::list(b, &yes);
    let else_ = p::list(b, &no);
    p::node(
        b,
        View::SIf {
            condition,
            then_,
            else_: Some(else_),
        },
        0,
    )
}
fn release_list(b: &mut Bir, statements: &[NodeId]) {
    for &s in statements {
        b.release(s);
    }
}
fn remove_empty(b: &mut Bir, statements: &mut Vec<NodeId>) {
    statements.retain(|&s| {
        if matches!(b.view(s), View::SBlock { statements } if statements.is_empty()) {
            b.release(s);
            false
        } else {
            true
        }
    });
}

/// J-S3, B:1575 simplify_if, rules 0..10 in order. Each loop removes a test
/// negation, swaps an empty then branch once, or removes a nested if. The other
/// rules return immediately. Statement lists are moved, not re-lowered.
pub fn js3_simplify_if(
    b: &mut Bir,
    mut test: NodeId,
    mut yes: Vec<NodeId>,
    mut no: Vec<NodeId>,
) -> NodeId {
    loop {
        remove_empty(b, &mut yes);
        remove_empty(b, &mut no);
        if let Some(value) = p::bool_of(b, test) {
            b.release(test);
            if value {
                release_list(b, &no);
                return js2_block(b, yes);
            }
            release_list(b, &yes);
            return js2_block(b, no);
        }
        if let View::JNot { value } = b.view(test) {
            if !no.is_empty() {
                p::retain(b, &[test], &[value]);
                test = value;
                std::mem::swap(&mut yes, &mut no);
                continue;
            }
        }
        if yes.is_empty() {
            if no.is_empty() {
                return if p::pure(b, test) {
                    b.release(test);
                    js2_block(b, vec![])
                } else {
                    js1_exp(b, test)
                };
            }
            test = je8_not(b, test);
            std::mem::swap(&mut yes, &mut no);
            continue;
        }
        let (yr, nr) = (single_value(b, &yes, true), single_value(b, &no, true));
        if let (Some(y), Some(n)) = (yr, nr) {
            p::retain(b, &yes, &[y]);
            p::retain(b, &no, &[n]);
            let value = je7_cond(b, test, y, n);
            return p::node(b, View::SReturn { value }, 0);
        }
        if let Some(n) = nr {
            p::retain(b, &no, &[n]);
            let test = je8_not(b, test);
            let ret = p::node(b, View::SReturn { value: n }, 0);
            let guard = raw_if(b, test, vec![ret], vec![]);
            yes.insert(0, guard);
            return js2_block(b, yes);
        }
        if yes.last().is_some_and(|&s| {
            matches!(
                b.view(s),
                View::SReturn { .. }
                    | View::SThrow { .. }
                    | View::SContinue { .. }
                    | View::SBreak { .. }
            )
        }) {
            let guard = raw_if(b, test, yes, vec![]);
            no.insert(0, guard);
            return js2_block(b, no);
        }
        if let (Some(y), Some(n)) = (single_value(b, &yes, false), single_value(b, &no, false)) {
            if let (Some((yl, yr)), Some((nl, nr))) =
                (p::binary(b, y, BinOp::Eq), p::binary(b, n, BinOp::Eq))
            {
                if same_assignment_target(b, yl, nl) {
                    p::retain(b, &yes, &[yl, yr]);
                    p::retain(b, &no, &[nr]);
                    let value = je7_cond(b, test, yr, nr);
                    let value = je4_bin(b, BinOp::Eq, yl, value);
                    return js1_exp(b, value);
                }
            }
            p::retain(b, &yes, &[y]);
            p::retain(b, &no, &[n]);
            let value = je7_cond(b, test, y, n);
            return js1_exp(b, value);
        }
        if let Some((c, y, n)) = nested_if(b, &yes) {
            let merge = if equal_statements(b, &n, &no) {
                Some(false)
            } else if !y.is_empty() && equal_statements(b, &y, &no) {
                Some(true)
            } else {
                None
            };
            if let Some(negate) = merge {
                let mut kept = vec![c];
                kept.extend_from_slice(&y);
                kept.extend_from_slice(&n);
                p::retain(b, &yes, &kept);
                release_list(b, &no);
                let c = if negate { je8_not(b, c) } else { c };
                test = je5_js_and(b, test, c);
                if negate {
                    yes = n;
                    no = y;
                } else {
                    yes = y;
                    no = n;
                }
                continue;
            }
        }
        if let Some((c, y, n)) = nested_if(b, &no) {
            let merge = if !yes.is_empty() && !y.is_empty() && equal_statements(b, &yes, &y) {
                Some(false)
            } else if !yes.is_empty() && !n.is_empty() && equal_statements(b, &yes, &n) {
                Some(true)
            } else {
                None
            };
            if let Some(negate) = merge {
                let other = if negate { y } else { n };
                let mut kept = vec![c];
                kept.extend_from_slice(&other);
                p::retain(b, &no, &kept);
                let c = if negate { je8_not(b, c) } else { c };
                test = je6_js_or(b, test, c);
                no = other;
                continue;
            }
        }
        return raw_if(b, test, yes, no);
    }
}

fn trivial(b: &Bir, id: NodeId) -> bool {
    matches!(b.view(id), View::JNumber { .. } | View::JUndefined)
}
fn clear_location(b: &mut Bir, id: NodeId) {
    let mut flags = b.node(id).flags();
    flags.0 &= !NodeFlags::JS_LOC_PRESENT;
    b.nodes[id.index()].set_flags(flags);
}

/// J-M0, E:96 remove_pure_subexpression. The narrower cached J_SUBEXPR fact
/// answers the array/index tests; only sequence spines need traversal.
pub fn jm0_remove_pure_subexpression(b: &mut Bir, root: NodeId) -> Option<NodeId> {
    enum Work {
        Enter(NodeId),
        Seq(NodeId),
    }
    let mut work = vec![Work::Enter(root)];
    let mut results = vec![];
    while let Some(w) = work.pop() {
        match w {
            Work::Enter(id) => {
                if b.node(id).flags().contains(NodeFlags::J_SUBEXPR) {
                    b.release(id);
                    results.push(None);
                    continue;
                }
                if let View::JSeq { first, second } = b.view(id) {
                    b.detach(first);
                    b.detach(second);
                    work.push(Work::Seq(id));
                    work.push(Work::Enter(second));
                    work.push(Work::Enter(first));
                } else {
                    results.push(Some(id));
                }
            }
            Work::Seq(id) => {
                let right = results.pop().unwrap();
                let left = results.pop().unwrap();
                let result = match (left, right) {
                    (Some(l), Some(r)) => {
                        let value = jm1_js_seq(b, l, r);
                        let outer = b.cold(id);
                        let own = b.cold(value);
                        let own_loc = b.node(value).flags().contains(NodeFlags::JS_LOC_PRESENT);
                        let outer_loc = b.node(id).flags().contains(NodeFlags::JS_LOC_PRESENT);
                        if let Some(outer) = outer {
                            let cold = crate::bir::Cold {
                                comment: own.and_then(|c| c.comment).or(outer.comment),
                                loc: if own_loc { own.unwrap().loc } else { outer.loc },
                            };
                            b.set_cold(value, cold);
                            if own_loc || outer_loc {
                                let mut flags = b.node(value).flags();
                                flags.0 |= NodeFlags::JS_LOC_PRESENT;
                                b.nodes[value.index()].set_flags(flags);
                            }
                        }
                        Some(value)
                    }
                    (Some(v), None) | (None, Some(v)) => Some(v),
                    (None, None) => None,
                };
                b.release(id);
                results.push(result);
            }
        }
    }
    results.pop().unwrap()
}

/// J-M1, E:399 js_seq. Each loop consumes a comma shell; pending final trivial
/// operands use a suffix stack, preserving the final expression's value.
pub fn jm1_js_seq(b: &mut Bir, mut left: NodeId, mut right: NodeId) -> NodeId {
    let mut suffix = vec![];
    loop {
        if let View::JSeq { first, second } = b.view(left) {
            let keep = if trivial(b, second) {
                Some(first)
            } else if trivial(b, first) {
                Some(second)
            } else {
                None
            };
            if let Some(keep) = keep {
                p::retain(b, &[left], &[keep]);
                left = keep;
                continue;
            }
        }
        if let View::JSeq { first, second } = b.view(right) {
            if trivial(b, first) {
                p::retain(b, &[right], &[second]);
                right = second;
                continue;
            }
            if trivial(b, second) {
                p::retain(b, &[right], &[first, second]);
                suffix.push(second);
                right = first;
                continue;
            }
        }
        let value = if trivial(b, left)
            || matches!(b.view(left), View::Var { .. } | View::JQualified { .. })
        {
            b.release(left);
            right
        } else {
            p::seq(b, left, right)
        };
        if let Some(next) = suffix.pop() {
            left = value;
            right = next;
        } else {
            return value;
        }
    }
}

/// J-M2, E:253 compile_nullish_strict_comparison. The final comparison is raw:
/// in particular it must not fold Optional_block === Undefined through J-E4.
pub fn jm2_nullish_strict_comparison(
    b: &mut Bir,
    neq: bool,
    left: NodeId,
    right: NodeId,
) -> NodeId {
    let nullish = |id| matches!(b.view(id), View::JNull | View::JUndefined);
    let impossible = |id| {
        super::facts::strictly_pure(b, id)
            && matches!(
                b.view(id),
                View::JBool
                    | View::JNumber { .. }
                    | View::JTypeof { .. }
                    | View::JFun { .. }
                    | View::JArray { .. }
                    | View::JBlockLit { .. }
            )
    };
    let value = if nullish(left) && nullish(right) {
        Some((matches!(b.view(left), View::JNull) == matches!(b.view(right), View::JNull)) != neq)
    } else if (nullish(left) && impossible(right)) || (nullish(right) && impossible(left)) {
        Some(neq)
    } else {
        None
    };
    if let Some(value) = value {
        p::retain(b, &[left, right], &[]);
        p::boolean(b, value)
    } else {
        p::bin(
            b,
            if neq { BinOp::NotEqEq } else { BinOp::EqEqEq },
            left,
            right,
        )
    }
}
/// J-M2, E:327 compile_int_equality. Float spellings, not float values, compare.
pub fn jm2_int_equality(b: &mut Bir, left: NodeId, right: NodeId) -> NodeId {
    let floats = match (b.view(left), b.view(right)) {
        (View::JNumber { value: l }, View::JNumber { value: r }) => {
            match (b.constant(l), b.constant(r)) {
                (crate::bir::Constant::Float(l), crate::bir::Constant::Float(r)) => {
                    l.spelling() == r.spelling()
                }
                _ => false,
            }
        }
        _ => false,
    };
    let value = if floats {
        Some(true)
    } else {
        p::int_of(b, left)
            .zip(p::int_of(b, right))
            .map(|(l, r)| l == r)
    };
    if let Some(value) = value {
        p::retain(b, &[left, right], &[]);
        p::boolean(b, value)
    } else {
        p::bin(b, BinOp::EqEqEq, left, right)
    }
}

/// J-M3, E:483 to_int32.
pub fn jm3_to_int32(b: &mut Bir, value: NodeId) -> NodeId {
    let zero = p::int(b, 0);
    jm3_int32_bor(b, value, zero)
}
/// J-M3, E:570 int32_bor. Redundant shifts/truncations are stripped in a loop.
pub fn jm3_int32_bor(b: &mut Bir, mut left: NodeId, mut right: NodeId) -> NodeId {
    loop {
        if let (Some(l), Some(r)) = (p::int_of(b, left), p::int_of(b, right)) {
            p::retain(b, &[left, right], &[]);
            return p::int(b, l | r);
        }
        if let Some((inner, shift)) = p::binary(b, right, BinOp::Lsr) {
            if p::int_of(b, shift) == Some(0) {
                p::retain(b, &[right], &[inner]);
                right = inner;
                continue;
            }
        }
        if let Some((inner, shift)) = p::binary(b, left, BinOp::Lsr) {
            if p::int_of(b, shift) == Some(0) {
                p::retain(b, &[left], &[inner]);
                left = inner;
                continue;
            }
            if p::int_of(b, right) == Some(0) && p::int_of(b, shift).is_some_and(|v| v > 0) {
                b.release(right);
                return left;
            }
        }
        if let Some((inner, zero)) = p::binary(b, left, BinOp::Bor) {
            if p::int_of(b, right) == Some(0) && p::int_of(b, zero) == Some(0) {
                p::retain(b, &[left], &[inner]);
                left = inner;
                continue;
            }
        }
        return je4_bin(b, BinOp::Bor, left, right);
    }
}
/// J-M4, E:488 int32_add / E:498 int32_minus.
pub fn jm4_int32_add_sub(b: &mut Bir, subtract: bool, left: NodeId, right: NodeId) -> NodeId {
    if let (Some(l), Some(r)) = (p::int_of(b, left), p::int_of(b, right)) {
        p::retain(b, &[left, right], &[]);
        return p::int(
            b,
            if subtract {
                l.wrapping_sub(r)
            } else {
                l.wrapping_add(r)
            },
        );
    }
    let value = je4_bin(
        b,
        if subtract { BinOp::Minus } else { BinOp::Plus },
        left,
        right,
    );
    jm3_to_int32(b, value)
}
/// J-M5, E:508 int32_mul. Zero uses permissive PURE, not STRICT.
pub fn jm5_int32_mul(b: &mut Bir, left: NodeId, right: NodeId) -> NodeId {
    let (l, r) = (p::int_of(b, left), p::int_of(b, right));
    if (r == Some(0) && p::pure(b, left)) || (l == Some(0) && p::pure(b, right)) {
        p::retain(b, &[left, right], &[]);
        return p::int(b, 0);
    }
    if let (Some(l), Some(r)) = (l, r) {
        p::retain(b, &[left, right], &[]);
        return p::int(b, l.wrapping_mul(r));
    }
    let power = |v: i32| {
        (v > 0 && (v as u32).is_power_of_two()).then(|| (v as u32).trailing_zeros() as i32)
    };
    let selected = if let Some(r) = r {
        power(r).map(|n| (left, right, n))
    } else if let Some(l) = l {
        power(l).map(|n| (right, left, n))
    } else {
        None
    };
    if let Some((value, literal, shift)) = selected {
        b.release(literal);
        let shift = p::int(b, shift);
        return jm7_int32_lsl(b, value, shift);
    }
    let value = je4_bin(b, BinOp::Mul, left, right);
    jm3_to_int32(b, value)
}
/// J-M6, E:545 int32_pow / E:535 ocaml_int32_pow, including float-to-int wrap.
pub fn jm6_int32_pow(b: &mut Bir, left: NodeId, right: NodeId) -> NodeId {
    if let (Some(l), Some(r)) = (p::int_of(b, left), p::int_of(b, right)) {
        let value = (l as f64).powf(r as f64);
        let value = if value > i32::MAX as f64 || value < i32::MIN as f64 {
            ((value.trunc() as i64 & 0xFFFF_FFFF) as u32) as i32
        } else {
            value.trunc() as i32
        };
        p::retain(b, &[left, right], &[]);
        return p::int(b, value);
    }
    let value = je4_bin(b, BinOp::Pow, left, right);
    jm3_to_int32(b, value)
}
/// J-M7, E:555 int32_lsl.
pub fn jm7_int32_lsl(b: &mut Bir, left: NodeId, right: NodeId) -> NodeId {
    if let (Some(l), Some(r)) = (p::int_of(b, left), p::int_of(b, right)) {
        p::retain(b, &[left, right], &[]);
        p::int(b, l.wrapping_shl(r as u32))
    } else {
        je4_bin(b, BinOp::Lsl, left, right)
    }
}
/// J-M8, E:596 int32_lsr. Literal shifts have the legacy valid-count domain.
pub fn jm8_int32_lsr(b: &mut Bir, mut left: NodeId, right: NodeId) -> NodeId {
    loop {
        if let (Some(l), Some(r)) = (p::int_of(b, left), p::int_of(b, right)) {
            let value = ((l as u32) >> (r as u32)) as i32;
            p::retain(b, &[left, right], &[]);
            return p::int(b, value);
        }
        if p::binary(b, left, BinOp::Lsr).is_some() && p::int_of(b, right) == Some(0) {
            b.release(right);
            return left;
        }
        if let Some((inner, zero)) = p::binary(b, left, BinOp::Bor) {
            if p::int_of(b, right) == Some(0) && p::int_of(b, zero) == Some(0) {
                p::retain(b, &[left], &[inner]);
                left = inner;
                continue;
            }
        }
        return je4_bin(b, BinOp::Lsr, left, right);
    }
}
/// J-M8, E:614 int32_bxor.
pub fn jm8_int32_bxor(b: &mut Bir, mut left: NodeId, mut right: NodeId) -> NodeId {
    loop {
        if let (Some(l), Some(r)) = (p::int_of(b, left), p::int_of(b, right)) {
            p::retain(b, &[left, right], &[]);
            return p::int(b, l ^ r);
        }
        if let Some((inner, zero)) = p::binary(b, right, BinOp::Lsr) {
            if p::int_of(b, zero) == Some(0) {
                p::retain(b, &[right], &[inner]);
                right = inner;
                continue;
            }
        }
        if let Some((inner, zero)) = p::binary(b, left, BinOp::Lsr) {
            if p::int_of(b, zero) == Some(0) {
                p::retain(b, &[left], &[inner]);
                left = inner;
                continue;
            }
        }
        return je4_bin(b, BinOp::Bxor, left, right);
    }
}
/// J-M8, E:631 int32_band. Unlike xor/shift, literal operands are NOT folded.
pub fn jm8_int32_band(b: &mut Bir, mut left: NodeId, right: NodeId) -> NodeId {
    loop {
        if let Some((inner, zero)) = p::binary(b, left, BinOp::Bor) {
            if p::int_of(b, zero) == Some(0) {
                p::retain(b, &[left], &[inner]);
                left = inner;
                continue;
            }
        }
        return je4_bin(b, BinOp::Band, left, right);
    }
}
/// J-M9, E:640 ocaml_typeof_expr. Folding is syntactic, with no purity guard.
pub fn jm9_typeof(b: &mut Bir, value: NodeId) -> NodeId {
    let ty = match b.view(value) {
        View::JNumber { .. } | View::JLength { .. } => Some("number"),
        View::JStr { .. } => Some("string"),
        View::JTemplate { .. } if b.node(value).aux() == 1 => Some("string"),
        View::JArray { .. } => Some("object"),
        View::JBool => Some("boolean"),
        _ => None,
    };
    if let Some(ty) = ty {
        b.release(value);
        p::string(b, ty)
    } else {
        clear_location(b, value);
        p::node(b, View::JTypeof { value }, 0)
    }
}
/// J-M10, E:835 int_bnot.
pub fn jm10_int_bnot(b: &mut Bir, value: NodeId) -> NodeId {
    if let Some(n) = p::int_of(b, value) {
        b.release(value);
        p::int(b, !n)
    } else {
        p::node(b, View::JBnot { value }, 0)
    }
}

/// J-M11, E:664/E:695/E:711 pure literal projections. `field` is authoritative
/// on records; a missing named record field never falls back to the index.
/// On success consumes the target and returns its retained element; on failure
/// leaves the target unchanged for the caller's plain field-access constructor.
pub fn jm11_projection(
    b: &mut Bir,
    target: NodeId,
    field: Option<&str>,
    index: Option<i32>,
) -> Option<NodeId> {
    if !super::facts::strictly_pure(b, target) {
        return None;
    }
    let value = match b.view(target) {
        View::JBlockLit { values, info } => {
            let crate::bir::JsPayload::Block(tag) = b.javascript(info) else {
                unreachable!()
            };
            if let (Some(field), Some(fields)) = (field, tag.record_fields()) {
                values
                    .iter()
                    .zip(fields)
                    .find_map(|(&v, (name, _))| (name == field).then_some(v))
            } else {
                values.get(usize::try_from(index?).ok()?).copied()
            }
        }
        View::JArray { values } => values.get(usize::try_from(index?).ok()?).copied(),
        _ => None,
    }?;
    p::retain(b, &[target], &[value]);
    Some(value)
}
/// J-M11, E:740/E:750 poly_var_tag_access / poly_var_value_access.
pub fn jm11_poly_var_access(b: &mut Bir, target: NodeId, payload: bool) -> NodeId {
    let idx = usize::from(payload);
    if let View::JBlockLit { values, .. } = b.view(target) {
        if super::facts::strictly_pure(b, target) {
            let value = values.get(idx).copied().expect("polyvariant field exists");
            p::retain(b, &[target], &[value]);
            return value;
        }
    }
    let property = b.intern_text(if payload { "VAL" } else { "NAME" });
    p::node(
        b,
        View::JDot {
            object: target,
            property,
            position: crate::js_ir::arena::FieldPos::new(Some(idx as i32)),
        },
        0,
    )
}

/// J-M12, E:844 interpolated_template. Segment utilities operate on literal
/// text only; no legacy expression builder is called. Comments inhibit merging.
pub fn jm12_interpolated_template(
    b: &mut Bir,
    segments: Vec<crate::string_literal::TemplateSegment>,
    values: Vec<NodeId>,
) -> NodeId {
    use crate::string_literal::{StringLiteral, concat_template, template_from_semantic};
    assert_eq!(segments.len(), values.len() + 1);
    let mut segments = segments.into_iter();
    let mut parts = vec![segments.next().unwrap()];
    let mut merged = vec![];
    let mut kept = vec![];
    for (next, value) in segments.zip(values) {
        let literal = if b.cold(value).and_then(|c| c.comment).is_some() {
            None
        } else {
            match b.view(value) {
                View::JStr { text } => Some(template_from_semantic(b.text(text))),
                View::JTemplate { info, .. } if b.node(value).aux() == 1 => {
                    let crate::bir::JsPayload::Template(p) = b.javascript(info) else {
                        unreachable!()
                    };
                    Some(match p[0].cooked {
                        Some(s) => StringLiteral::Valid {
                            source: b.text(p[0].raw).to_owned().into(),
                            semantic: b.text(s).to_owned().into(),
                        },
                        None => StringLiteral::InvalidSource(b.text(p[0].raw).to_owned().into()),
                    })
                }
                _ => None,
            }
        };
        if let Some(literal) = literal {
            parts.push(literal);
            parts.push(next);
            b.release(value);
        } else {
            merged.push(concat_template(&parts));
            kept.push(value);
            parts = vec![next];
        }
    }
    merged.push(concat_template(&parts));
    let parts = merged
        .into_iter()
        .map(|part| match part {
            StringLiteral::Valid { source, semantic } => crate::bir::TemplatePart {
                raw: b.intern_text(&source),
                cooked: Some(b.intern_text(&semantic)),
            },
            StringLiteral::InvalidSource(source) => crate::bir::TemplatePart {
                raw: b.intern_text(&source),
                cooked: None,
            },
        })
        .collect();
    let info = b.js_info(crate::bir::JsPayload::Template(parts));
    p::node(
        b,
        View::JTemplate {
            values: &kept,
            info,
        },
        u16::from(kept.is_empty()),
    )
}

fn integer_runtime_call(b: &mut Bir, modulo: bool, left: NodeId, right: NodeId) -> NodeId {
    let name = "Primitive_int";
    let module = if let Some(i) = b
        .pools
        .j_modules
        .iter()
        .position(|m| m.id.name() == name && matches!(m.kind, crate::js_ir::Kind::Runtime))
    {
        crate::bir::ImportId(i as u32)
    } else {
        let id = crate::bir::ImportId(b.pools.imports.len() as u32);
        let path = b.intern_text(name);
        b.pools.imports.push(crate::bir::Import {
            name: crate::name::Name::new(name),
            path,
        });
        b.pools.j_modules.push(crate::js_ir::ModuleId {
            id: crate::ident::Ident::create_persistent(name),
            kind: crate::js_ir::Kind::Runtime,
            dynamic_import: false,
        });
        id
    };
    let member = Some(b.intern_text(if modulo { "mod_" } else { "div" }));
    let callee = p::node(b, View::JQualified { module, member }, 0);
    let info = b.js_info(crate::bir::JsPayload::Call(crate::js_ir::CallInfo {
        kind: crate::js_ir::CallKind::BuiltinRuntime,
        arity: crate::js_ir::CallArity::Full,
        ..Default::default()
    }));
    p::node(
        b,
        View::JCall {
            callee,
            args: &[left, right],
            info,
        },
        0,
    )
}
/// J-M13, C:6174 int32_div_expr (formerly C:6033). The checked runtime call
/// is selected only when the divisor is not a known nonzero integer literal.
pub fn jm13_int32_div(b: &mut Bir, check_zero: bool, left: NodeId, right: NodeId) -> NodeId {
    if matches!(b.view(left), View::JLength { .. }) && p::int_of(b, right) == Some(2) {
        b.release(right);
        let one = p::int(b, 1);
        return je4_bin(b, BinOp::Asr, left, one);
    }
    if let Some(r) = p::int_of(b, right).filter(|r| *r != 0) {
        if let Some(l) = p::int_of(b, left) {
            p::retain(b, &[left, right], &[]);
            return p::int(b, l.wrapping_div(r));
        }
    } else if check_zero {
        return integer_runtime_call(b, false, left, right);
    }
    let value = je4_bin(b, BinOp::Div, left, right);
    jm3_to_int32(b, value)
}
/// J-M13, C:6190 int32_mod_expr (formerly C:6049). Legacy modulo has neither
/// a two-literal fold nor int32 coercion; its unchecked result stays raw `%`.
pub fn jm13_int32_mod(b: &mut Bir, check_zero: bool, left: NodeId, right: NodeId) -> NodeId {
    if !p::int_of(b, right).is_some_and(|r| r != 0) && check_zero {
        return integer_runtime_call(b, true, left, right);
    }
    je4_bin(b, BinOp::Mod, left, right)
}

/// J-M14, O:339 push_effect_expression. Split sequences left-to-right, drop
/// strictly pure values, and preserve assignment locations carried by unit pairs.
pub fn jm14_push_effect_expression(b: &mut Bir, value: NodeId, statements: &mut Vec<NodeId>) {
    let mut work = vec![value];
    while let Some(value) = work.pop() {
        if let View::JSeq { first, second } = b.view(value) {
            if p::undefined(b, second)
                && b.node(second).aux() == 0
                && p::binary(b, first, BinOp::Eq).is_some()
                && b.node(value).flags().contains(NodeFlags::JS_LOC_PRESENT)
                && !b.node(first).flags().contains(NodeFlags::JS_LOC_PRESENT)
            {
                let outer = b.cold(value).unwrap();
                let comment = b.cold(first).and_then(|c| c.comment).or(outer.comment);
                b.set_cold(
                    first,
                    crate::bir::Cold {
                        loc: outer.loc,
                        comment,
                    },
                );
                let mut flags = b.node(first).flags();
                flags.0 |= NodeFlags::JS_LOC_PRESENT;
                b.nodes[first.index()].set_flags(flags);
            }
            p::retain(b, &[value], &[first, second]);
            work.push(second);
            work.push(first);
        } else if super::facts::strictly_pure(b, value) {
            discard_pure_effect(b, value);
        } else {
            statements.push(js1_exp(b, value));
        }
    }
}
/// J-M14, O:368 push_s_exp: only numbers/undefined and trivial comma arms drop.
pub fn jm14_push_s_exp(b: &mut Bir, mut value: NodeId, statements: &mut Vec<NodeId>) {
    loop {
        if trivial(b, value) {
            b.release(value);
            return;
        }
        if let View::JSeq { first, second } = b.view(value) {
            let keep = if trivial(b, first) {
                Some(second)
            } else if trivial(b, second) {
                Some(first)
            } else {
                None
            };
            if let Some(keep) = keep {
                p::retain(b, &[value], &[keep]);
                value = keep;
                continue;
            }
        }
        statements.push(js1_exp(b, value));
        return;
    }
}
/// J-M14, O:359 push_s_if_empty uses permissive PURE, not STRICT.
pub fn jm14_push_s_if_empty(b: &mut Bir, value: NodeId, statements: &mut Vec<NodeId>) {
    if p::pure(b, value) {
        b.release(value);
    } else {
        jm14_push_s_exp(b, value, statements);
    }
}
#[cfg(test)]
mod tests {
    use super::*;
    use crate::bir::{View, bridge_j};
    use crate::js_ir::arena::{JsArena, JsDepsProgram, JsProgram, StmtKind};
    use crate::js_ir::build::exp;
    use crate::lambda::lam_coercion::push_effect_expression;

    #[test]
    fn jm14_pure_effects_match_legacy_printed_text() {
        for input in 0..5 {
            let mut legacy = JsArena::new();
            let value = match input {
                0 => exp::undefined(true, &mut legacy),
                1 => exp::null(&mut legacy),
                2 => exp::bool(true, &mut legacy),
                3 => exp::string("discarded", &mut legacy),
                4 => exp::var(
                    crate::ident::Ident::new("value", 1, crate::ident::IdentFlags::NONE),
                    &mut legacy,
                ),
                _ => unreachable!(),
            };
            let statement = legacy.stmt(StmtKind::Exp(value));
            let source = JsDepsProgram {
                program: JsProgram::new_in(vec![statement], vec![], legacy),
                modules: vec![],
                side_effect: None,
            };
            let mut imported = bridge_j::import_js(&source).unwrap();
            let View::SBlock { statements } = imported.arena.view(imported.root) else {
                panic!("block")
            };
            let View::SExp { value: actual } = imported.arena.view(statements[0]) else {
                panic!("expression")
            };
            // The row consumes the cached predicate. The source lowering's
            // independent flag tests establish it for these same producers.
            let mut flags = imported.arena.node(actual).flags();
            flags.0 |= NodeFlags::STRICT;
            imported.arena.nodes[actual.index()].set_flags(flags);
            imported.arena.detach(actual);
            imported.arena.release(imported.root);
            discard_pure_effect(&mut imported.arena, actual);
            imported.root = imported.arena.new_node(View::SBlock { statements: &[] }, 0);
            let actual = bridge_j::export_js(&imported).unwrap();
            let mut expected = source;
            let mut block = Vec::new();
            push_effect_expression(&mut expected.program.arena, &mut block, value);
            expected.program.block = block;
            let print = |p: &JsDepsProgram| {
                crate::js_ir::print_deps_program_with_directives_and_options(
                    p,
                    None,
                    &[],
                    false,
                    false,
                    false,
                )
            };
            assert_eq!(print(&actual), print(&expected));
            imported.arena.validate(Some(imported.root), false).unwrap();
        }
    }
}
