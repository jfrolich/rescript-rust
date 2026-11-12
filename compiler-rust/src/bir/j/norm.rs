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
