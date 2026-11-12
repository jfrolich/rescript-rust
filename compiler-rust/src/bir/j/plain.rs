//! Non-normalising J construction. All operands are consumed detached roots.
use crate::bir::{Bir, Constant, NodeFlags, NodeId, View};
use crate::js_ir::BinOp;

/// Build precisely the requested node, with cached J purity facts.
pub fn node(b: &mut Bir, view: View<'_>, aux: u16) -> NodeId {
    let var = matches!(view, View::Var { .. });
    let id = b.new_node(view, aux);
    if var {
        let mut flags = b.node(id).flags();
        flags.0 |= NodeFlags::STRICT;
        b.nodes[id.index()].set_flags(flags);
    }
    id
}
/// Integer literal, with no source decoration.
pub fn int(b: &mut Bir, value: i32) -> NodeId {
    let value = b.intern_const(Constant::Int(i64::from(value)));
    node(b, View::JNumber { value }, 0)
}
/// Boolean literal.
pub fn boolean(b: &mut Bir, value: bool) -> NodeId {
    node(b, View::JBool, u16::from(value))
}
/// String literal.
pub fn string(b: &mut Bir, value: &str) -> NodeId {
    let text = b.intern_text(value);
    node(b, View::JStr { text }, 0)
}
/// Binary expression, deliberately bypassing J-E4.
pub fn bin(b: &mut Bir, op: BinOp, left: NodeId, right: NodeId) -> NodeId {
    node(b, View::JBin { left, right }, op as u16)
}
/// Comma expression, deliberately bypassing J-M1.
pub fn seq(b: &mut Bir, first: NodeId, second: NodeId) -> NodeId {
    node(b, View::JSeq { first, second }, 0)
}
/// Statement list wrapper (not an explicit block statement).
pub fn list(b: &mut Bir, statements: &[NodeId]) -> NodeId {
    node(b, View::SBlock { statements }, 0)
}

pub(super) fn pure(b: &Bir, id: NodeId) -> bool {
    b.node(id).flags().contains(NodeFlags::PURE)
}
pub(super) fn int_of(b: &Bir, id: NodeId) -> Option<i32> {
    if let View::JNumber { value } = b.view(id) {
        match b.constant(value) {
            Constant::Int(i) => Some(*i as i32),
            Constant::Char(i) => Some(*i as i32),
            _ => None,
        }
    } else {
        None
    }
}
pub(super) fn string_of(b: &Bir, id: NodeId) -> Option<&str> {
    match b.view(id) {
        View::JStr { text } => Some(b.text(text)),
        View::JTemplate { info, .. } if b.node(id).aux() == 1 => {
            let crate::bir::JsPayload::Template(parts) = b.javascript(info) else {
                unreachable!()
            };
            Some(parts[0].cooked.map_or("", |text| b.text(text)))
        }
        _ => None,
    }
}
pub(super) fn binary(b: &Bir, id: NodeId, op: BinOp) -> Option<(NodeId, NodeId)> {
    if b.node(id).aux() == op as u16 {
        if let View::JBin { left, right } = b.view(id) {
            return Some((left, right));
        }
    }
    None
}
pub(super) fn bool_of(b: &Bir, id: NodeId) -> Option<bool> {
    matches!(b.view(id), View::JBool).then(|| b.node(id).aux() != 0)
}
pub(super) fn undefined(b: &Bir, id: NodeId) -> bool {
    matches!(b.view(id), View::JUndefined)
}
pub(super) fn equal(b: &Bir, left: NodeId, right: NodeId) -> bool {
    super::equal::equal(b, left, right, &mut 0)
}
pub(super) fn same_var(b: &Bir, left: NodeId, right: NodeId) -> bool {
    matches!(b.view(left), View::Var { .. } | View::JQualified { .. }) && equal(b, left, right)
}
/// Retain disjoint descendants and release the replaced shells and discarded
/// operands. Detach before release: Bir skips edges that no longer belong to it.
pub(super) fn retain(b: &mut Bir, roots: &[NodeId], kept: &[NodeId]) {
    for &id in kept {
        if b.parents[id.index()].is_some() {
            b.detach(id);
        }
    }
    for &id in roots {
        if !kept.contains(&id) {
            b.release(id);
        }
    }
}
/// Transfer all cold metadata; unlike setting a location this preserves absence.
pub(super) fn copy_cold(b: &mut Bir, from: NodeId, to: NodeId) {
    if let Some(cold) = b.cold(from) {
        b.set_cold(to, cold);
    }
    if b.node(from).flags().contains(NodeFlags::JS_LOC_PRESENT) {
        let mut flags = b.node(to).flags();
        flags.0 |= NodeFlags::JS_LOC_PRESENT;
        b.nodes[to.index()].set_flags(flags);
    }
}
