//! The statement half of the first implementation of the lowering's
//! interface (THREE_TREES 11.4, "T6: the interface" (a) and (b)): J
//! statements of the lowering's `Bir`. Every function is the call the
//! lowering makes today, so the rows written are today's rows. Deleted by
//! the flip (T6s).
//!
//! Slice T6l built the bodies of the first table. The transition
//! functions are the representation.
//!
//! # What each body is
//!
//! | Function | Body |
//! | --- | --- |
//! | `stmt_kind` | `rows::kind_of` of the node's operation |
//! | `stmt_aux` | the node's `aux`: its low two bits for an `SDecl`, all of it for any other |
//! | `value_of` | the `value` of `SExp`, `SReturn`, `SThrow`, of an `SDecl` that has one; the `condition` of `SIf` and `SWhile`; the `scrutinee` of `SSwitch`; `None` otherwise |
//! | `list` | `Lists::push_iter(len, ..)` with the nodes of the statements |
//! | `len`, `kind_at` | `Lists::get(list)`: its length; `rows::kind_of` of the operation of entry `index` |
//! | `take_at` | entry `index` of `Lists::get(list)` (the entry stays: a pool list that no node holds is not read again) |
//! | `exp` | `Bir::new_node(View::SExp { value }, 0)` |
//! | `assign` | `bir::j::assign` |
//! | `declare` | with a value `bir::j::declare`; without one `plain::node(View::SDecl { var, value: None }, aux)` with the `aux` `bir::j::declare` computes |
//! | `return_` | `bir::j::return_value` |
//! | `throw`, `debugger` | `plain::node` with `View::SThrow { value }`, `View::SDebugger` and `aux` 0 |
//! | `break_`, `continue_` | `Bir::new_node` with `View::SBreak { label }`, `View::SContinue { label }` and `aux` 0 |
//! | `block_of`, `explicit_block` | `Bir::block_from_list`, `Bir::explicit_block_from_list` |
//! | `if_plain` | `block_from_list(yes)`, then `block_from_list(no)`, then `Bir::new_node(View::SIf { condition, then_, else_: Some(else_) }, 0)` |
//! | `while_` | `block_from_list(body)`, then `Bir::new_node(View::SWhile { .. }, 0)` |
//! | `for_range` | `block_from_list(body)`, then `Bir::new_node(View::SForRange { var, parts, label }, direction)` with `parts` `[init, end, body]`, or `[end, body]` without `init` |
//! | `for_of` | `block_from_list(body)`, then `Bir::new_node` with `View::SForOf` or, when `awaited`, `View::SForAwaitOf`, `parts` `[iterable, body]`, `aux` 0 |
//! | `switch` | `Bir::switch_from_list(scrutinee, actions, header, string as u16)` |
//! | `try_` | `block_from_list` of `body`, of the handler's list and of `finaliser`, each when there is one, in this order; then `Bir::new_node(View::STry { parts, exception }, 0)` with `parts` the two or three blocks and `exception` the handler's variable |
//! | `function` | `block_from_list(body)`, then `bir::j::pure_expression(View::JFun { body, header }, 0)` |
//! | `exp_rule` | `norm::js1_exp` |
//! | `if_` | `norm::js3_simplify_if` |
//! | `effect`, `effect_if_impure` | `norm::jm14_push_effect_expression`, `norm::jm14_push_s_if_empty`, with `Rows::operands` as the vector the rule pushes to: the statements pushed above its length on entry are given to `sink` in order and the vector is cut back |
//!
//! Bodies of later slices (`todo!` with the slice's name; each is built by
//! that slice, with its test in `js_stmt_tests.rs`):
//!
//! | Function | Slice | Body |
//! | --- | --- | --- |
//! | `locate_stmt` | T6m | `Bir::set_cold` with `loc` and the comment the node has, and `NodeFlags::JS_LOC_PRESENT` set |
//! | `take_value` | T6n | the `value` of `SExp`, `SReturn` or `SThrow`: `Bir::detach` of it, `Bir::release` of the statement; a panic for any other; one step |
//! | `unblock` | T6n | the statements of an `SBlock` copied above the length of `Rows::operands`; each `Bir::detach`ed and given to `sink` in order; the vector cut back; `Bir::release` of the block; one step and one per statement |
//! | `stmt_located` | T6o | `NodeFlags::JS_LOC_PRESENT` |
//!
//! Steps (`Js::steps`): one for every function that builds a statement or
//! a function literal, and one more per statement of each list it
//! consumes; `list` one and one per statement; `take_at` one; `effect` and
//! `effect_if_impure` one and one per statement given. A reader and the
//! transition functions count nothing.
use super::rows::{E, Rows, kind_of};
use super::{norm, plain};
use crate::bir::lower::js::Pools;
use crate::bir::lower::js_stmt::{JsStmt, Range};
use crate::bir::{FuncId, ListId, NodeId, StrId, SwitchId, VarId, View};
use crate::lambda::LamLoc;
use crate::emit::row::Kind;
use crate::lambda::lam_compat::LetKind;

/// A statement in flight on J rows: the row's id. 4 bytes; not `Copy`.
#[derive(Debug, PartialEq, Eq)]
pub struct S(NodeId);

impl JsStmt for Rows {
    type S = S;
    type L = ListId;

    #[inline]
    fn stmt_from_node(node: NodeId) -> S {
        S(node)
    }
    #[inline]
    fn stmt_node(s: S) -> NodeId {
        s.0
    }
    #[inline]
    fn list_from(list: ListId) -> ListId {
        list
    }
    #[inline]
    fn list_id(list: ListId) -> ListId {
        list
    }

    #[inline]
    fn stmt_kind(&self, a: &Pools, s: &S) -> Kind {
        kind_of(a.node(s.0).op())
    }
    #[inline]
    fn stmt_aux(&self, a: &Pools, s: &S) -> u8 {
        let node = a.node(s.0);
        if matches!(node.op(), crate::bir::Op::SDecl) { (node.aux() & 0b11) as u8 } else { node.aux() as u8 }
    }
    #[inline]
    fn value_of<'r>(&self, a: &'r Pools, s: &'r S) -> Option<NodeId> {
        match a.view(s.0) {
            View::SExp { value } | View::SReturn { value } | View::SThrow { value } => Some(value),
            View::SDecl { value, .. } => value,
            View::SIf { condition, .. } | View::SWhile { condition, .. } => Some(condition),
            View::SSwitch { scrutinee, .. } => Some(scrutinee),
            _ => None,
        }
    }

    #[inline]
    fn stmt_located(&self, a: &Pools, s: &S) -> bool {
        let _inputs = (a, s);
        todo!("T6o")
    }

    fn list(&mut self, a: &mut Pools, len: u32, statements: impl Iterator<Item = S>) -> ListId {
        self.steps += 1 + u64::from(len);
        a.lists.push_iter(len as usize, statements.map(|s| s.0))
    }
    #[inline]
    fn len(&self, a: &Pools, list: ListId) -> u32 {
        a.lists.get(list).len() as u32
    }
    #[inline]
    fn kind_at(&self, a: &Pools, list: ListId, index: u32) -> Kind {
        kind_of(a.node(a.lists.get(list)[index as usize]).op())
    }
    #[inline]
    fn take_at(&mut self, a: &mut Pools, list: ListId, index: u32) -> S {
        self.steps += 1;
        S(a.lists.get(list)[index as usize])
    }

    #[inline]
    fn exp(&mut self, a: &mut Pools, value: E) -> S {
        self.steps += 1;
        S(a.new_node(View::SExp { value: value.0 }, 0))
    }
    #[inline]
    fn assign(&mut self, a: &mut Pools, var: VarId, value: E) -> S {
        self.steps += 1;
        S(super::assign(a, var, value.0))
    }
    #[inline]
    fn declare(&mut self, a: &mut Pools, kind: LetKind, var: VarId, value: Option<E>) -> S {
        self.steps += 1;
        S(match value {
            Some(value) => super::declare(a, kind, var, value.0),
            None => {
                let aux = kind as u16 | ((crate::js_ir::op::UsedStats::Used as u16) << 2);
                plain::node(a, View::SDecl { var, value: None }, aux)
            }
        })
    }
    #[inline]
    fn return_(&mut self, a: &mut Pools, value: E) -> S {
        self.steps += 1;
        S(super::return_value(a, value.0))
    }
    #[inline]
    fn throw(&mut self, a: &mut Pools, value: E) -> S {
        self.steps += 1;
        S(plain::node(a, View::SThrow { value: value.0 }, 0))
    }
    #[inline]
    fn debugger(&mut self, a: &mut Pools) -> S {
        self.steps += 1;
        S(plain::node(a, View::SDebugger, 0))
    }
    #[inline]
    fn break_(&mut self, a: &mut Pools, label: Option<StrId>) -> S {
        self.steps += 1;
        S(a.new_node(View::SBreak { label }, 0))
    }
    #[inline]
    fn continue_(&mut self, a: &mut Pools, label: Option<StrId>) -> S {
        self.steps += 1;
        S(a.new_node(View::SContinue { label }, 0))
    }
    #[inline]
    fn block_of(&mut self, a: &mut Pools, list: ListId) -> S {
        S(self.adopt(a, list))
    }
    #[inline]
    fn explicit_block(&mut self, a: &mut Pools, list: ListId) -> S {
        self.steps += 1 + self.len(a, list) as u64;
        S(a.explicit_block_from_list(list))
    }
    fn if_plain(&mut self, a: &mut Pools, test: E, yes: ListId, no: ListId) -> S {
        self.steps += 1;
        let then_ = self.adopt_counted(a, yes);
        let else_ = self.adopt_counted(a, no);
        S(a.new_node(View::SIf { condition: test.0, then_, else_: Some(else_) }, 0))
    }
    fn while_(&mut self, a: &mut Pools, condition: E, body: ListId, label: Option<StrId>) -> S {
        let body = self.adopt(a, body);
        S(a.new_node(View::SWhile { condition: condition.0, body, label }, 0))
    }
    fn for_range(&mut self, a: &mut Pools, var: VarId, range: Range<E>, body: ListId, label: Option<StrId>) -> S {
        let body = self.adopt(a, body);
        let end = range.end.0;
        S(match range.init {
            Some(init) => a.new_node(View::SForRange { var, parts: &[init.0, end, body], label }, range.direction),
            None => a.new_node(View::SForRange { var, parts: &[end, body], label }, range.direction),
        })
    }
    fn for_of(&mut self, a: &mut Pools, var: VarId, iterable: E, body: ListId, label: Option<StrId>, awaited: bool) -> S {
        let body = self.adopt(a, body);
        let parts = [iterable.0, body];
        S(a.new_node(
            if awaited {
                View::SForAwaitOf { var, parts: &parts, label }
            } else {
                View::SForOf { var, parts: &parts, label }
            },
            0,
        ))
    }
    fn switch(&mut self, a: &mut Pools, scrutinee: E, actions: ListId, header: SwitchId, string: bool) -> S {
        self.steps += 1 + self.len(a, actions) as u64;
        S(a.switch_from_list(scrutinee.0, actions, header, u16::from(string)))
    }
    fn try_(&mut self, a: &mut Pools, body: ListId, handler: Option<(VarId, ListId)>, finaliser: Option<ListId>) -> S {
        assert!(handler.is_some() || finaliser.is_some(), "a try without a handler or a finaliser");
        self.steps += 1;
        let first = self.adopt_counted(a, body);
        let mut parts = [first; 3];
        let mut len = 1;
        for list in [handler.map(|(_, list)| list), finaliser].into_iter().flatten() {
            parts[len] = self.adopt_counted(a, list);
            len += 1;
        }
        S(a.new_node(View::STry { parts: &parts[..len], exception: handler.map(|(var, _)| var) }, 0))
    }
    fn function(&mut self, a: &mut Pools, header: FuncId, body: ListId) -> E {
        let body = self.adopt(a, body);
        E(super::pure_expression(a, View::JFun { body, header }, 0))
    }

    fn locate_stmt(&mut self, a: &mut Pools, s: &mut S, loc: LamLoc) {
        let _inputs = (a, s, loc);
        todo!("T6m")
    }
    fn take_value(&mut self, a: &mut Pools, s: S) -> E {
        let _inputs = (a, s);
        todo!("T6n")
    }
    fn unblock(&mut self, a: &mut Pools, s: S, sink: impl FnMut(S)) {
        let _inputs = (a, s, sink);
        todo!("T6n")
    }

    fn exp_rule(&mut self, a: &mut Pools, value: E) -> S {
        self.steps += 1;
        S(norm::js1_exp(a, value.0))
    }
    fn if_(&mut self, a: &mut Pools, test: E, yes: ListId, no: ListId) -> S {
        self.steps += 1 + self.len(a, yes) as u64 + self.len(a, no) as u64;
        S(norm::js3_simplify_if(a, test.0, yes, no))
    }
    fn effect(&mut self, a: &mut Pools, value: E, sink: impl FnMut(S)) {
        let start = self.operands.len();
        norm::jm14_push_effect_expression(a, value.0, &mut self.operands);
        self.give(start, sink);
    }
    fn effect_if_impure(&mut self, a: &mut Pools, value: E, sink: impl FnMut(S)) {
        let start = self.operands.len();
        norm::jm14_push_s_if_empty(a, value.0, &mut self.operands);
        self.give(start, sink);
    }
}

impl Rows {
    /// `Bir::block_from_list` of `list`: one step for the block and one per
    /// statement it adopts. O(statements).
    #[inline]
    fn adopt(&mut self, a: &mut Pools, list: ListId) -> NodeId {
        self.steps += 1;
        self.adopt_counted(a, list)
    }
    /// `Bir::block_from_list` of `list` within a statement whose own step is
    /// counted by the caller: one step per statement adopted. O(statements).
    #[inline]
    fn adopt_counted(&mut self, a: &mut Pools, list: ListId) -> NodeId {
        self.steps += self.len(a, list) as u64;
        a.block_from_list(list)
    }
    /// The statements a rule pushed onto the operand stack above `start`,
    /// given to `sink` in order; the stack is cut back to `start`. One step,
    /// and one per statement given. O(statements); allocates nothing.
    #[inline]
    fn give(&mut self, start: usize, mut sink: impl FnMut(S)) {
        self.steps += 1 + (self.operands.len() - start) as u64;
        for &statement in &self.operands[start..] {
            sink(S(statement));
        }
        self.operands.truncate(start);
    }
}
