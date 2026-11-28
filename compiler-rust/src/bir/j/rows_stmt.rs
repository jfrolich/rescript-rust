//! The statement half of the first implementation of the lowering's
//! interface (THREE_TREES 11.4, "T6: the interface" (a) and (b)): J
//! statements of the lowering's `Bir`. Every function is the call the
//! lowering makes today, so the rows written are today's rows. Deleted by
//! the flip (T6s).
//!
//! Slice T6l built the bodies of the first table. The interface has no
//! transition function since T6x-f; the four this file keeps for the
//! tests of rows (`stmt_from_node`, `stmt_node`, `list_from`, `list_id`)
//! are the representation.
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
//! | `with_stmt_at` | `read` on entry `index` of `Lists::get(list)` as a statement: the row is named for the length of the call and stays the list's; no row is read to find it |
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
//! | `if_head` | `norm::simplify_if_head`, the head `js3_simplify_if` runs over pool lists, over the caller's runs: `RunLists` gives the rule each function of `Runs` under the name `norm::IfLists` has for it |
//! | `effect`, `effect_if_impure` | `norm::jm14_effect_expression`, `norm::jm14_s_if_empty`: the rule gives each statement to `sink` as it makes it; nothing is collected |
//!
//! What the conversion slices T6m to T6q call beside the functions above
//! (the slice is the first that calls it):
//!
//! | Function | Slice | Body |
//! | --- | --- | --- |
//! | `locate_stmt` | T6m | `Bir::set_cold` with `loc` and the comment the node has, and `NodeFlags::JS_LOC_PRESENT` set |
//! | `take_value` | T6n | the `value` of `SExp`, `SReturn` or `SThrow`: `Bir::detach` of it, `Bir::release` of the statement; a panic for any other; one step |
//! | `unblock` | T6n | each statement of an `SBlock`, read by its index, `Bir::detach`ed and given to `sink`, in order; then `Bir::release` of the block; nothing is collected; one step and one per statement |
//! | `stmt_located` | T6o | `NodeFlags::JS_LOC_PRESENT` |
//! | `stmt_id` | T6x-a | the `NodeId` of the row, as `Js::id` of an expression |
//! | `is_empty_block` | T6n | an `SBlock` whose `statements` is empty |
//! | `branch_last_kind` | T6n | of an `SIf`: `rows::kind_of` of the operation of the last entry of the `statements` of `then_`, or of `else_` when `otherwise`; `None` for no entry or no `else_` |
//! | `copy_stmt` | T6o | `Bir::copy_subtree_with_scratch(s, &[], fresh, ..)` with the copy storage and the label vector of `Rows`, as `copy_fresh` |
//! | `declared` | T6q | the `var` of `SDecl` or `SRest` |
//! | `block_ids` | T6q | the ids of the `statements` of an `SBlock`, in order |
//! | `block_len` | T6x-e | the length of the `statements` of an `SBlock`, a detached entry counted |
//! | `with_block_stmt` | T6x-e | `read` on entry `index` of the `statements` of an `SBlock` as a statement: the row is named for the length of the call; a panic when the entry's parent is not the block (a hole) |
//! | `lend_block_stmt` | T6x-e | `edit` on the implementation, the pools and that entry as a statement; a panic when the reference names another row afterwards |
//! | `take_block_stmt` | T6x-e | that entry, `Bir::detach`ed: the parent link is cleared and the entry stays in the list, so the indexes after it stay; one step |
//! | `substitute` | T6x-e | a walk of the statement's subtree on `Rows::work`: a `Var` of exactly `var` is `Bir::replace`d by what `make` gives and not entered, any other node has its children pushed; it stops at `uses` replacements; one step per node popped |
//! | `alias_at` | T6x-e | the `var` of the `Var` that is the `value` of the `SDecl` `id`; `None` otherwise |
//! | `return_calls` | T6r | `return_calls_of` of the `value` of the `SReturn` that is entry `index` of the pool list, on `Rows::work`: a `JCond` pushes its else-branch and its then-branch, a `JSeq` is followed to its `second`, a `JCall` of a `Var` that is a site is given to `visit` with its row id |
//! | `binder` | T6r | the `var` of `SDecl`, `SRest`, `SForRange`, `SForOf` and `SForAwaitOf`; the `exception` of `STry`; `None` otherwise |
//! | `status` | T6r | of an `SDecl` or an `SRest`: the bits of `aux` above the two of the `LetKind`, bit 15 apart (an `SRest` keeps it for its descriptor); a panic for any other |
//! | `range_of` | T6r | of an `SForRange` its `var`, of an `SForRangeExisting` the `var` of its `variable` when that is a `Var`; with `rows::kind_of` of the operation of the part before the body (the bound); `None` for any other statement |
//! | `bodies` | T6r | 1 for an `SBlock`, an `SWhile` and the four loops; 1 or 2 for an `SIf` (its `else_`); the length of the `parts` of an `STry` and of the `actions` of an `SSwitch`; 0 otherwise |
//! | `body` | T6r | the pool list of the `SBlock` that is list `index` (`body_block`): the block itself, the `then_` or `else_` of an `SIf`, the `body` of an `SWhile`, the last part of a loop, part `index` of an `STry`, action `index` of an `SSwitch`; the statements stay the block's; one step |
//! | `set_body` | T6r | that block written again over the pool list given, with its flags and its `aux`; one step |
//! | `literal_body` | T6r | the pool list of the `SBlock` that is the `body` of the `JFun` `Bir::func_owners[header]` names; one step |
//! | `set_literal_body` | T6r | that block written again over the pool list given, as `set_body`; one step |
//! | `below` | T6r | a walk on `Rows::work`, above what it holds, of the children of the statement that are no statements and of everything below them: a `JFun` is given by its header and not entered, a `Var` of a variable with `VarFlags::JS_GLOBAL` is given and, when `visit` says so, `Bir::qualify_global`ed; every other node has its children pushed, the last first; every node is read, whatever `want` is |
//! | `effect_free` | T6q | the read `export.rs::has_toplevel_effect` made of a statement that is not a declaration row: a work stack (`Rows::work`) of the node's children for a compound statement, the `STRICT` flag of the value of `SExp` and `SReturn` and of every expression below a compound statement, `false` at `SThrow`, `SDebugger`, a jump, `SDecl`, `SRest`, `SForOf`, `SForAwaitOf`; one step per node read |
//! | `release_stmt` | T6n | `Bir::release`; one step per node it frees |
//! | `if_blocks` | T6n | `Bir::new_node(View::SIf { condition, then_, else_: Some(else_) }, 0)` over the two blocks; one step |
//! | `take_if` | T6n | of an `SIf`: `Bir::detach` of `condition`, `then_` and of `else_` when there is one, `Bir::release` of the statement; one step |
//!
//! Steps (`Js::steps`): one for every function that builds a statement or
//! a function literal, and one more per statement of each list it
//! consumes; `list` one and one per statement; `take_at` one; `effect` and
//! `effect_if_impure` one and one per statement given; `if_head` one (the
//! runs count what they release and take). A reader counts nothing.
use super::rows::{E, Rows, kind_of};
use super::{norm, plain};
use crate::bir::lower::js::Pools;
use crate::bir::lower::js_stmt::{Below, IfHead, JsStmt, Range, Runs};
use crate::bir::{FuncId, ListId, NodeFlags, NodeId, StrId, SwitchId, VarId, View};
use crate::lambda::LamLoc;
use crate::emit::row::{Kind, flag};
use crate::lambda::lam_compat::LetKind;

/// A statement in flight on J rows: the row's id. 4 bytes; not `Copy`.
#[derive(Debug, PartialEq, Eq)]
pub struct S(NodeId);

#[cfg(test)]
impl S {
    /// The row of the statement, for a test that reads the arena beside
    /// the handle. O(1).
    pub(crate) fn row(&self) -> NodeId {
        self.0
    }
}

impl JsStmt for Rows {
    type S = S;
    type L = ListId;

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
    fn value_of(&self, a: &Pools, s: &S) -> Option<NodeId> {
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
        a.node(s.0).flags().contains(NodeFlags::JS_LOC_PRESENT)
    }

    #[inline]
    fn stmt_id(&self, _: &Pools, s: &S) -> u32 {
        s.0.0
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
    fn with_stmt_at<R>(&self, a: &Pools, list: ListId, index: u32, read: impl FnOnce(&S) -> R) -> R {
        read(&S(a.lists.get(list)[index as usize]))
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
        debug_assert!(
            a.lists.get(actions).iter().all(|&action| a.node(action).op() == crate::bir::Op::SBlock),
            "an action of a switch that is no block"
        );
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
        let comment = a.cold(s.0).and_then(|cold| cold.comment);
        a.set_cold(s.0, crate::bir::Cold { loc, comment });
        let mut flags = a.node(s.0).flags();
        flags.0 |= NodeFlags::JS_LOC_PRESENT;
        a.nodes[s.0.index()].set_flags(flags);
    }
    fn take_value(&mut self, a: &mut Pools, s: S) -> E {
        let (View::SExp { value } | View::SReturn { value } | View::SThrow { value }) = a.view(s.0) else {
            panic!("a statement without a value to take")
        };
        self.steps += 1;
        a.detach(value);
        a.release(s.0);
        E(value)
    }
    fn unblock(&mut self, a: &mut Pools, s: S, mut sink: impl FnMut(S)) {
        let View::SBlock { statements } = a.view(s.0) else { panic!("not a block statement") };
        let count = statements.len();
        self.steps += 1 + count as u64;
        // Nothing is buffered: each statement is read from the block, taken
        // out of it and given on, so the width of a block costs no storage.
        for index in 0..count {
            let statement = a.view(s.0).child_at(index);
            a.detach(statement);
            sink(S(statement));
        }
        a.release(s.0);
    }
    #[inline]
    fn is_empty_block(&self, a: &Pools, s: &S) -> bool {
        matches!(a.view(s.0), View::SBlock { statements } if statements.is_empty())
    }
    fn branch_last_kind(&self, a: &Pools, s: &S, otherwise: bool) -> Option<Kind> {
        let View::SIf { then_, else_, .. } = a.view(s.0) else { panic!("not an if statement") };
        let block = if otherwise { else_? } else { then_ };
        let View::SBlock { statements } = a.view(block) else { panic!("a branch is a block") };
        statements.last().map(|&last| kind_of(a.node(last).op()))
    }
    fn copy_stmt(&mut self, a: &mut Pools, s: &S, fresh: &mut Vec<(VarId, VarId)>) -> S {
        S(self.copy_recording(a, s.0, fresh))
    }
    #[inline]
    fn declared(&self, a: &Pools, s: &S) -> Option<VarId> {
        match a.view(s.0) {
            View::SDecl { var, .. } | View::SRest { var, .. } => Some(var),
            _ => None,
        }
    }
    #[cfg(test)]
    fn block_ids(&self, a: &Pools, s: &S, mut sink: impl FnMut(u32)) {
        let View::SBlock { statements } = a.view(s.0) else { panic!("not a block statement") };
        for statement in statements {
            sink(statement.0);
        }
    }
    fn block_len(&self, a: &Pools, block: &S) -> u32 {
        let View::SBlock { statements } = a.view(block.0) else { panic!("not a block statement") };
        statements.len() as u32
    }
    fn with_block_stmt<R>(&self, a: &Pools, block: &S, index: u32, read: impl FnOnce(&S) -> R) -> R {
        read(&S(Self::block_entry(a, block, index)))
    }
    fn lend_block_stmt<R>(
        &mut self,
        a: &mut Pools,
        block: &mut S,
        index: u32,
        edit: impl FnOnce(&mut Self, &mut Pools, &mut S) -> R,
    ) -> R {
        let row = Self::block_entry(a, block, index);
        let mut statement = S(row);
        let result = edit(self, a, &mut statement);
        assert_eq!(statement.0, row, "a statement of a block replaced through its reference");
        result
    }
    fn take_block_stmt(&mut self, a: &mut Pools, block: &mut S, index: u32) -> S {
        let statement = Self::block_entry(a, block, index);
        a.detach(statement);
        self.steps += 1;
        S(statement)
    }
    fn substitute(
        &mut self,
        a: &mut Pools,
        s: &mut S,
        var: VarId,
        uses: u32,
        mut make: impl FnMut(&mut Self, &mut Pools) -> E,
    ) -> u32 {
        let mut replaced = 0;
        if uses == 0 {
            return replaced;
        }
        let mut work = std::mem::take(&mut self.work);
        debug_assert!(work.is_empty());
        work.push(s.0);
        while let Some(node) = work.pop() {
            self.steps += 1;
            match a.view(node) {
                View::Var { var: found } if found == var => {
                    // `make` may run a walk of its own (`copy_members`).
                    self.work = work;
                    let copy = make(self, a);
                    work = std::mem::take(&mut self.work);
                    a.replace(node, copy.0);
                    replaced += 1;
                    if replaced == uses {
                        break;
                    }
                }
                view => view.children_into(&mut work),
            }
        }
        work.clear();
        self.work = work;
        replaced
    }
    fn alias_at(&self, a: &Pools, id: u32) -> Option<VarId> {
        let View::SDecl { value: Some(value), .. } = a.view(NodeId(id)) else { return None };
        match a.view(value) {
            View::Var { var } => Some(var),
            _ => None,
        }
    }
    fn return_calls(
        &mut self,
        a: &mut Pools,
        list: ListId,
        index: u32,
        last: bool,
        visit: impl FnMut(&mut Pools, VarId, u32),
    ) -> u32 {
        let View::SReturn { value } = a.view(a.lists.get(list)[index as usize]) else { panic!("not a return statement") };
        return_calls_of(a, &mut self.work, value, last, visit)
    }
    #[inline]
    fn binder(&self, a: &Pools, s: &S) -> Option<VarId> {
        match a.view(s.0) {
            View::SDecl { var, .. }
            | View::SRest { var, .. }
            | View::SForRange { var, .. }
            | View::SForOf { var, .. }
            | View::SForAwaitOf { var, .. } => Some(var),
            View::STry { exception, .. } => exception,
            _ => None,
        }
    }
    #[inline]
    fn status(&self, a: &Pools, s: &S) -> u8 {
        let node = a.node(s.0);
        assert!(matches!(node.op(), crate::bir::Op::SDecl | crate::bir::Op::SRest), "not a declaration");
        // `SDecl` packs the `LetKind` in two bits and the status above;
        // `SRest` keeps bit 15 for its descriptor.
        ((node.aux() & 0x7fff) >> 2) as u8
    }
    fn range_of(&self, a: &Pools, s: &S) -> Option<(Option<VarId>, Kind)> {
        let (var, parts) = match a.view(s.0) {
            View::SForRange { var, parts, .. } => (Some(var), parts),
            View::SForRangeExisting { variable, parts, .. } => match a.view(variable) {
                View::Var { var } => (Some(var), parts),
                _ => (None, parts),
            },
            _ => return None,
        };
        // The bound is the part before the body, with or without a first
        // value.
        Some((var, kind_of(a.node(parts[parts.len() - 2]).op())))
    }
    fn bodies(&self, a: &Pools, s: &S) -> u32 {
        match a.view(s.0) {
            View::SBlock { .. }
            | View::SWhile { .. }
            | View::SForRange { .. }
            | View::SForRangeExisting { .. }
            | View::SForOf { .. }
            | View::SForAwaitOf { .. } => 1,
            View::SIf { else_, .. } => 1 + u32::from(else_.is_some()),
            View::STry { parts, .. } => parts.len() as u32,
            View::SSwitch { actions, .. } => actions.len() as u32,
            _ => 0,
        }
    }
    #[inline]
    fn body(&mut self, a: &mut Pools, s: &mut S, index: u32) -> ListId {
        self.steps += 1;
        let block = Self::body_block(a, s, index);
        a.node(block).block_list_id().expect("a statement list of a statement is a block")
    }
    fn set_body(&mut self, a: &mut Pools, s: &mut S, index: u32, body: ListId) {
        self.steps += 1;
        let block = Self::body_block(a, s, index);
        debug_assert!(
            a.lists.get(body).iter().all(|statement| a.parents[statement.index()] == Some(block)),
            "a statement put back into a list it was not taken from"
        );
        Self::write_block(a, block, body);
    }
    #[inline]
    fn literal_body(&mut self, a: &mut Pools, header: FuncId) -> ListId {
        self.steps += 1;
        a.node(Self::literal_block(a, header)).block_list_id().expect("the body of a function literal is a block")
    }
    fn set_literal_body(&mut self, a: &mut Pools, header: FuncId, body: ListId) {
        self.steps += 1;
        let block = Self::literal_block(a, header);
        debug_assert!(
            a.lists.get(body).iter().all(|statement| a.parents[statement.index()] == Some(block)),
            "a statement put back into a list it was not taken from"
        );
        Self::write_block(a, block, body);
    }
    fn below(&mut self, a: &mut Pools, s: &mut S, want: u16, mut visit: impl FnMut(Below) -> bool) -> u32 {
        assert!(want & !(flag::HAS_FUN | flag::HAS_GLOBAL) == 0, "a descent for a flag that is neither HAS_FUN nor HAS_GLOBAL");
        if want == 0 {
            return 0;
        }
        // The stack may hold the pending nodes of a walk that is under
        // way (`JsStmt::substitute`): the reads go above them.
        let mut work = std::mem::take(&mut self.work);
        let base = work.len();
        // The statement's own expressions, the last first so that they
        // are read in order: a child that is a statement is one of its
        // lists.
        let view = a.view(s.0);
        for at in (0..view.child_count()).rev() {
            let child = view.child_at(at);
            if !is_statement(a.node(child).op()) {
                work.push(child);
            }
        }
        let mut read = 0;
        while work.len() > base {
            let node = work.pop().expect("a pending node");
            read += 1;
            match a.view(node) {
                View::JFun { header, .. } => {
                    if want & flag::HAS_FUN != 0 {
                        visit(Below::Function(header));
                    }
                }
                View::Var { var } => {
                    if want & flag::HAS_GLOBAL != 0
                        && a.vars.flags(var).contains(crate::bir::VarFlags::JS_GLOBAL)
                        && visit(Below::Global(var))
                    {
                        a.qualify_global(node);
                    }
                }
                view => {
                    for at in (0..view.child_count()).rev() {
                        work.push(view.child_at(at));
                    }
                }
            }
        }
        self.work = work;
        read
    }
    fn effect_free(&mut self, a: &Pools, s: &S) -> bool {
        let mut work = std::mem::take(&mut self.work);
        debug_assert!(work.is_empty());
        work.push(s.0);
        let mut free = true;
        while let Some(node) = work.pop() {
            self.steps += 1;
            let ok = match a.view(node) {
                View::SExp { value } | View::SReturn { value } => a.node(value).flags().contains(NodeFlags::STRICT),
                View::SBlock { .. }
                | View::SIf { .. }
                | View::SWhile { .. }
                | View::SForRange { .. }
                | View::SForRangeExisting { .. }
                | View::SSwitch { .. }
                | View::STry { .. } => {
                    a.view(node).children_into(&mut work);
                    true
                }
                View::SThrow { .. }
                | View::SDebugger
                | View::SBreak { .. }
                | View::SContinue { .. }
                | View::SDecl { .. }
                | View::SRest { .. }
                | View::SForOf { .. }
                | View::SForAwaitOf { .. } => false,
                // An expression below a compound statement.
                _ => a.node(node).flags().contains(NodeFlags::STRICT),
            };
            if !ok {
                free = false;
                break;
            }
        }
        work.clear();
        self.work = work;
        free
    }
    #[inline]
    fn release_stmt(&mut self, a: &mut Pools, s: S) {
        self.steps += u64::from(a.release(s.0));
    }
    #[inline]
    fn if_blocks(&mut self, a: &mut Pools, test: E, yes: S, no: S) -> S {
        self.steps += 1;
        S(a.new_node(View::SIf { condition: test.0, then_: yes.0, else_: Some(no.0) }, 0))
    }
    fn take_if(&mut self, a: &mut Pools, s: S) -> (E, S, Option<S>) {
        let View::SIf { condition, then_, else_ } = a.view(s.0) else { panic!("not an if statement") };
        self.steps += 1;
        a.detach(condition);
        a.detach(then_);
        if let Some(else_) = else_ {
            a.detach(else_);
        }
        a.release(s.0);
        (E(condition), S(then_), else_.map(S))
    }

    fn exp_rule(&mut self, a: &mut Pools, value: E) -> S {
        self.steps += 1;
        S(norm::js1_exp(a, value.0))
    }
    fn if_(&mut self, a: &mut Pools, test: E, yes: ListId, no: ListId) -> S {
        self.steps += 1 + self.len(a, yes) as u64 + self.len(a, no) as u64;
        S(norm::js3_simplify_if(a, test.0, yes, no))
    }
    fn if_head<R: Runs<Rows>>(
        &mut self,
        a: &mut Pools,
        runs: &mut R,
        test: &mut E,
        yes: &mut R::Run,
        no: &mut R::Run,
    ) -> Option<IfHead<S, R::Run>> {
        self.steps += 1;
        let mut lists = RunLists { rows: self, runs };
        let head = norm::simplify_if_head(a, &mut lists, &mut test.0, yes, no)?;
        Some(IfHead { statement: head.statement.map(S), tail: head.tail })
    }
    fn effect(&mut self, a: &mut Pools, value: E, mut sink: impl FnMut(S)) {
        let mut given = 0u64;
        norm::jm14_effect_expression(a, value.0, &mut |statement| {
            given += 1;
            sink(S(statement));
        });
        self.steps += 1 + given;
    }
    fn effect_if_impure(&mut self, a: &mut Pools, value: E, mut sink: impl FnMut(S)) {
        let mut given = 0u64;
        norm::jm14_s_if_empty(a, value.0, &mut |statement| {
            given += 1;
            sink(S(statement));
        });
        self.steps += 1 + given;
    }
}

/// The caller's runs as `norm::simplify_if_head` reads and takes
/// branches: each function is the function of [`Runs`] with the same name,
/// and a statement read in place is given to the rule as its row. 16
/// bytes, made once per [`JsStmt::if_head`].
struct RunLists<'r, R> {
    rows: &'r mut Rows,
    runs: &'r mut R,
}

impl<R: Runs<Rows>> norm::IfLists for RunLists<'_, R> {
    type Handle = R::Run;
    #[inline]
    fn trim(&mut self, b: &mut Pools, run: R::Run) {
        self.runs.trim(self.rows, b, run);
    }
    #[inline]
    fn empty(&mut self, _: &mut Pools) -> R::Run {
        self.runs.empty()
    }
    #[inline]
    fn last(&mut self, _: &Pools, run: R::Run) -> Option<NodeId> {
        self.runs.last(run).map(|s| s.0)
    }
    #[inline]
    fn only(&mut self, _: &Pools, run: R::Run) -> Option<NodeId> {
        self.runs.only(run).map(|s| s.0)
    }
    #[inline]
    fn release(&mut self, b: &mut Pools, run: R::Run) {
        self.runs.release(self.rows, b, run);
    }
    #[inline]
    fn take(&mut self, b: &mut Pools, run: R::Run) -> ListId {
        self.runs.take(self.rows, b, run)
    }
}

/// [`JsStmt::return_calls`] of the returned value `value`, a row, over the
/// work stack `work`, above what it holds: the body of the function on
/// rows, apart so that `norm::simplify_if_head`, which builds a `return`
/// that passes no close of a list, runs the same walk until the flip
/// deletes it. A sequence at the top is followed to its last operand in a
/// loop and keeps `last`; from the first conditional on every pending node
/// is a branch, so the stack holds rows alone. Returns the nodes read. One
/// read per conditional, per sequence and per node they end in; nothing is
/// allocated once the stack has the depth of the nested conditionals.
pub(crate) fn return_calls_of(
    a: &mut Pools,
    work: &mut Vec<NodeId>,
    value: NodeId,
    last: bool,
    mut visit: impl FnMut(&mut Pools, VarId, u32),
) -> u32 {
    let base = work.len();
    let mut read = 0;
    let (mut node, mut site) = (value, last);
    loop {
        read += 1;
        match a.view(node) {
            View::JCond { then_, else_, .. } => {
                work.push(else_);
                work.push(then_);
            }
            View::JSeq { second, .. } => {
                node = second;
                continue;
            }
            View::JCall { callee, .. } if site => {
                if let View::Var { var } = a.view(callee) {
                    visit(a, var, node.0);
                }
            }
            _ => {}
        }
        if work.len() == base {
            return read;
        }
        node = work.pop().expect("a pending branch");
        site = true;
    }
}

/// Whether rows of `op` are statements: what tells an expression of a
/// statement from a statement of one of its lists ([`JsStmt::below`]).
/// O(1): one match.
fn is_statement(op: crate::bir::Op) -> bool {
    use crate::bir::Op;
    matches!(
        op,
        Op::SBlock
            | Op::SDecl
            | Op::SExp
            | Op::SIf
            | Op::SWhile
            | Op::SForRangeExisting
            | Op::SForRange
            | Op::SForOf
            | Op::SForAwaitOf
            | Op::SSwitch
            | Op::SReturn
            | Op::SThrow
            | Op::STry
            | Op::SBreak
            | Op::SContinue
            | Op::SDebugger
            | Op::SRest
    )
}

/// For the tests of rows (see the like block of `rows.rs`): a statement
/// is its row and a list its pool list.
#[cfg(test)]
impl Rows {
    /// The handle of a J statement built on the arena. O(1).
    pub(crate) fn stmt_from_node(node: NodeId) -> S {
        S(node)
    }
    /// The J row of a statement. O(1).
    pub(crate) fn stmt_node(s: S) -> NodeId {
        s.0
    }
    /// The list in flight of a pool list. O(1).
    pub(crate) fn list_from(list: ListId) -> ListId {
        list
    }
    /// The pool list of a list in flight. O(1).
    pub(crate) fn list_id(list: ListId) -> ListId {
        list
    }
}

impl Rows {
    /// The block that is statement list `index` of the statement `s`
    /// ([`JsStmt::bodies`]): the row of a statement the caller holds, or
    /// of an operand of it. O(1). Panics when `index` is not below
    /// `bodies`.
    fn body_block(a: &Pools, s: &S, index: u32) -> NodeId {
        let at = index as usize;
        let block = match a.view(s.0) {
            View::SBlock { .. } if at == 0 => Some(s.0),
            View::SIf { then_, .. } if at == 0 => Some(then_),
            View::SIf { else_, .. } if at == 1 => else_,
            View::SWhile { body, .. } if at == 0 => Some(body),
            View::SForRange { parts, .. }
            | View::SForRangeExisting { parts, .. }
            | View::SForOf { parts, .. }
            | View::SForAwaitOf { parts, .. }
                if at == 0 =>
            {
                parts.last().copied()
            }
            View::STry { parts, .. } => parts.get(at).copied(),
            View::SSwitch { actions, .. } => actions.get(at).copied(),
            _ => None,
        };
        block.unwrap_or_else(|| panic!("statement list {index} of a statement that has no such list"))
    }
    /// The block that is the body of the function literal of `header`,
    /// found in the arena's table of literals by header. O(1). Panics
    /// when no literal of `header` is live.
    fn literal_block(a: &Pools, header: FuncId) -> NodeId {
        let literal = a.func_owners.get(header.index()).copied().flatten().expect("a function literal that is not there");
        let View::JFun { body, .. } = a.view(literal) else { unreachable!("the owner of a header is a function literal") };
        body
    }
    /// The `SBlock` `block` written again over the pool list `list`: it
    /// keeps its row, so its flags and whether it is explicit, and its
    /// cold data (keyed by the row). O(1).
    fn write_block(a: &mut Pools, block: NodeId, list: ListId) {
        let node = a.node(block);
        assert!(node.block_list_id().is_some(), "a statement list of a statement is a block");
        let mut written =
            if node.aux() != 0 { crate::bir::Node::explicit_block_list(list) } else { crate::bir::Node::block_list(list) };
        written.set_flags(node.flags());
        a.nodes[block.index()] = written;
    }
    /// Entry `index` of the `statements` of the `SBlock` `block`. O(1).
    /// Panics on a statement that is not a block, on an index outside it
    /// and on an entry the block no longer holds (a hole).
    fn block_entry(a: &Pools, block: &S, index: u32) -> NodeId {
        let View::SBlock { statements } = a.view(block.0) else { panic!("not a block statement") };
        let statement = statements[index as usize];
        assert_eq!(a.parents[statement.index()], Some(block.0), "a statement taken out of its block");
        statement
    }
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
}

#[cfg(test)]
#[path = "rows_stmt_tests.rs"]
mod tests;
