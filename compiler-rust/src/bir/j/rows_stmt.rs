//! The statement half of the first implementation of the lowering's
//! interface (THREE_TREES 11.4, "T6: the interface" (a) and (b)): J
//! statements of the lowering's `Bir`. Every function is the call the
//! lowering makes today, so the rows written are today's rows. Deleted by
//! the flip (T6s).
//!
//! Slice T6l builds the bodies marked `todo!("T6l")`. The transition
//! functions are the representation and are built.
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
use super::rows::{E, Rows};
use crate::bir::lower::js::Pools;
use crate::bir::lower::js_stmt::{JsStmt, Range};
use crate::bir::{FuncId, ListId, NodeId, StrId, SwitchId, VarId};
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
        let _inputs = (a, s);
        todo!("T6l")
    }
    #[inline]
    fn stmt_aux(&self, a: &Pools, s: &S) -> u8 {
        let _inputs = (a, s);
        todo!("T6l")
    }
    #[inline]
    fn value_of<'r>(&self, a: &'r Pools, s: &'r S) -> Option<NodeId> {
        let _inputs = (a, s);
        todo!("T6l")
    }

    #[inline]
    fn stmt_located(&self, a: &Pools, s: &S) -> bool {
        let _inputs = (a, s);
        todo!("T6o")
    }

    fn list(&mut self, a: &mut Pools, len: u32, statements: impl Iterator<Item = S>) -> ListId {
        let _inputs = (a, len, statements);
        todo!("T6l")
    }
    #[inline]
    fn len(&self, a: &Pools, list: ListId) -> u32 {
        let _inputs = (a, list);
        todo!("T6l")
    }
    #[inline]
    fn kind_at(&self, a: &Pools, list: ListId, index: u32) -> Kind {
        let _inputs = (a, list, index);
        todo!("T6l")
    }
    #[inline]
    fn take_at(&mut self, a: &mut Pools, list: ListId, index: u32) -> S {
        let _inputs = (a, list, index);
        todo!("T6l")
    }

    #[inline]
    fn exp(&mut self, a: &mut Pools, value: E) -> S {
        let _inputs = (a, value);
        todo!("T6l")
    }
    #[inline]
    fn assign(&mut self, a: &mut Pools, var: VarId, value: E) -> S {
        let _inputs = (a, var, value);
        todo!("T6l")
    }
    #[inline]
    fn declare(&mut self, a: &mut Pools, kind: LetKind, var: VarId, value: Option<E>) -> S {
        let _inputs = (a, kind, var, value);
        todo!("T6l")
    }
    #[inline]
    fn return_(&mut self, a: &mut Pools, value: E) -> S {
        let _inputs = (a, value);
        todo!("T6l")
    }
    #[inline]
    fn throw(&mut self, a: &mut Pools, value: E) -> S {
        let _inputs = (a, value);
        todo!("T6l")
    }
    #[inline]
    fn debugger(&mut self, a: &mut Pools) -> S {
        let _inputs = a;
        todo!("T6l")
    }
    #[inline]
    fn break_(&mut self, a: &mut Pools, label: Option<StrId>) -> S {
        let _inputs = (a, label);
        todo!("T6l")
    }
    #[inline]
    fn continue_(&mut self, a: &mut Pools, label: Option<StrId>) -> S {
        let _inputs = (a, label);
        todo!("T6l")
    }
    #[inline]
    fn block_of(&mut self, a: &mut Pools, list: ListId) -> S {
        let _inputs = (a, list);
        todo!("T6l")
    }
    #[inline]
    fn explicit_block(&mut self, a: &mut Pools, list: ListId) -> S {
        let _inputs = (a, list);
        todo!("T6l")
    }
    fn if_plain(&mut self, a: &mut Pools, test: E, yes: ListId, no: ListId) -> S {
        let _inputs = (a, test, yes, no);
        todo!("T6l")
    }
    fn while_(&mut self, a: &mut Pools, condition: E, body: ListId, label: Option<StrId>) -> S {
        let _inputs = (a, condition, body, label);
        todo!("T6l")
    }
    fn for_range(&mut self, a: &mut Pools, var: VarId, range: Range<E>, body: ListId, label: Option<StrId>) -> S {
        let _inputs = (a, var, range, body, label);
        todo!("T6l")
    }
    fn for_of(&mut self, a: &mut Pools, var: VarId, iterable: E, body: ListId, label: Option<StrId>, awaited: bool) -> S {
        let _inputs = (a, var, iterable, body, label, awaited);
        todo!("T6l")
    }
    fn switch(&mut self, a: &mut Pools, scrutinee: E, actions: ListId, header: SwitchId, string: bool) -> S {
        let _inputs = (a, scrutinee, actions, header, string);
        todo!("T6l")
    }
    fn try_(&mut self, a: &mut Pools, body: ListId, handler: Option<(VarId, ListId)>, finaliser: Option<ListId>) -> S {
        let _inputs = (a, body, handler, finaliser);
        todo!("T6l")
    }
    fn function(&mut self, a: &mut Pools, header: FuncId, body: ListId) -> E {
        let _inputs = (a, header, body);
        todo!("T6l")
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
        let _inputs = (a, value);
        todo!("T6l")
    }
    fn if_(&mut self, a: &mut Pools, test: E, yes: ListId, no: ListId) -> S {
        let _inputs = (a, test, yes, no);
        todo!("T6l")
    }
    fn effect(&mut self, a: &mut Pools, value: E, sink: impl FnMut(S)) {
        let _inputs = (a, value, sink);
        todo!("T6l")
    }
    fn effect_if_impure(&mut self, a: &mut Pools, value: E, sink: impl FnMut(S)) {
        let _inputs = (a, value, sink);
        todo!("T6l")
    }
}
