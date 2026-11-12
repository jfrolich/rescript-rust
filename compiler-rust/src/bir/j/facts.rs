//! J facts, computed from immediate operands, never expression-depth walks.
use crate::bir::{Bir, Constant, JsPayload, NodeFlags, NodeId, PropertyKey, View};
use crate::js_ir::{BinOp, arena::FieldPos};

/// B:102 expression_has_no_side_effects and E:15 js_expr_no_side_effects.
/// Work is O(arity), with one cached fact read per immediate operand.
/// `None` identifies a non-J node (Var is shared between L and J).
pub(crate) fn purity(
    b: &Bir,
    id: NodeId,
    strict: bool,
    child: impl Fn(NodeId) -> bool,
) -> Option<bool> {
    let view = b.view(id);
    Some(match view {
        View::Var { .. }
        | View::JQualified { .. }
        | View::JNumber { .. }
        | View::JStr { .. }
        | View::JJson { .. }
        | View::JBool
        | View::JNull
        | View::JUndefined
        | View::JFun { .. } => true,
        View::JDot { object, .. } => child(object),
        View::JIndex { object, index } => child(object) && child(index),
        View::JIn { left, right } | View::JStrAppend { left, right } => child(left) && child(right),
        View::JSeq { first, second } => child(first) && child(second),
        View::JIsNullish { value }
        | View::JLength { value }
        | View::JTypeof { value }
        | View::JNot { value }
        | View::JBnot { value }
        | View::JOptional { value } => child(value),
        View::JArray { values }
        | View::JBlockLit { values, .. }
        | View::JTemplate { values, .. } => values.iter().all(|&v| child(v)),
        View::JObject { values, info } => {
            let JsPayload::Object(keys) = b.javascript(info) else {
                unreachable!()
            };
            keys.iter()
                .zip(values)
                .all(|(key, &v)| *key != PropertyKey::Spread && child(v))
        }
        View::JCond {
            condition,
            then_,
            else_,
        } => child(condition) && child(then_) && child(else_),
        View::JBin { left, right } => {
            let op = b.node(id).aux();
            op != BinOp::Eq as u16
                && child(left)
                && if strict
                    && [BinOp::Pow, BinOp::Div, BinOp::Mod]
                        .iter()
                        .any(|x| *x as u16 == op)
                {
                    match b.view(right) {
                        View::JNumber { value } => match b.constant(value) {
                            Constant::Int(n) => op == BinOp::Pow as u16 || *n != 0,
                            Constant::Char(n) => op == BinOp::Pow as u16 || *n != 0,
                            Constant::Float(_) => true,
                            Constant::BigInt(s) => {
                                let text = b.text(*s);
                                if op == BinOp::Pow as u16 {
                                    text.starts_with('+')
                                } else {
                                    &text[1..] != "0"
                                }
                            }
                            _ => false,
                        },
                        _ => false,
                    }
                } else {
                    child(right)
                }
        }
        View::JTagged { tag, values, .. } => child(tag) && values.iter().all(|&v| child(v)),
        View::JCall { callee, args, .. } => {
            args.len() == 1 && is_array_is_array(b, callee) && child(args[0])
        }
        View::JFlatCall { .. }
        | View::JNew { .. }
        | View::JRaw { .. }
        | View::JAwait { .. }
        | View::JSpread { .. }
        | View::JRecordRest { .. }
        | View::JJsx { .. } => false,
        _ => return None,
    })
}

/// B:164 is_array_is_array_callee. Persistent globals have source order zero.
pub fn is_array_is_array(b: &Bir, id: NodeId) -> bool {
    if let View::JDot {
        object,
        property,
        position,
    } = b.view(id)
    {
        if b.node(id).aux() == 0 && position == FieldPos::NONE && b.text(property) == "isArray" {
            if let View::Var { var } = b.view(object) {
                return b.vars.name(var).as_str() == "Array"
                    && b.vars.flags(var).contains(crate::bir::VarFlags::JS_IDENT);
            }
        }
    }
    false
}

/// A cached strict fact; a shared Var leaf is always pure in both languages.
pub fn strictly_pure(b: &Bir, id: NodeId) -> bool {
    matches!(b.view(id), View::Var { .. }) || b.node(id).flags().contains(NodeFlags::STRICT)
}
