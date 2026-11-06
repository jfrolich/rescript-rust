//! Storage for the typed tree.
//!
//! OCaml's `Typedtree` is a tree of immutable heap records that share
//! subterms freely (`compiler/ml/typedtree.ml`). Rust keeps the same
//! external shape but stores the nodes in dense `Vec` pools owned by the
//! compilation, the layout `ParseArena` gives the parse tree: a node refers
//! to its children by `u32` handles and to its child lists by
//! [`ArenaList`] ranges of a list pool. Copying a handle shares the node,
//! like OCaml's physical sharing, and the whole tree is freed at once.
//!
//! The type checker owns the arena while it builds the tree
//! ([`crate::types::typecore::TypeCheckContext::typed`]); afterwards it is
//! read-only and passed to every consumer next to the root structure or
//! signature.

use std::num::NonZeroU32;

use crate::parse_arena::ArenaList;

use super::typedtree::Expression;

/// Handle of a typed expression in a [`TypedArena`].
///
/// Stored as `index + 1` so `Option<TExprIdx>` is four bytes.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct TExprIdx(NonZeroU32);

impl TExprIdx {
    #[inline]
    fn from_index(index: usize) -> Self {
        let raw = u32::try_from(index + 1).expect("typed expression arena exceeds u32::MAX");
        Self(NonZeroU32::new(raw).expect("index + 1 is non-zero"))
    }

    #[inline]
    fn index(self) -> usize {
        (self.0.get() - 1) as usize
    }
}

impl std::fmt::Debug for TExprIdx {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "TExprIdx({})", self.index())
    }
}

/// A list of typed expressions (tuple, array and constructor arguments,
/// template values).
pub type TExprList = ArenaList<TExprIdx>;

/// One pool of list items. A list is a contiguous range, pushed in one go.
#[derive(Debug)]
struct ListPool<T> {
    items: Vec<T>,
}

impl<T> Default for ListPool<T> {
    fn default() -> Self {
        Self { items: Vec::new() }
    }
}

impl<T> ListPool<T> {
    fn push_iter(&mut self, items: impl IntoIterator<Item = T>) -> ArenaList<T> {
        let start = self.items.len();
        self.items.extend(items);
        let len = self.items.len() - start;
        if len == 0 {
            return ArenaList::EMPTY;
        }
        ArenaList::from_range(
            u32::try_from(start).expect("typed list pool exceeds u32::MAX"),
            u32::try_from(len).expect("typed list exceeds u32::MAX"),
        )
    }

    #[inline]
    fn get(&self, list: ArenaList<T>) -> &[T] {
        if list.is_empty() {
            return &[];
        }
        &self.items[list.start() as usize..][..list.len()]
    }

    fn reserve(&mut self, additional: usize) {
        self.items.reserve(additional);
    }
}

/// The nodes of one compilation's typed tree.
#[derive(Debug, Default)]
pub struct TypedArena {
    exprs: Vec<Expression>,
    expr_lists: ListPool<TExprIdx>,
}

impl TypedArena {
    pub fn new() -> Self {
        Self::default()
    }

    /// An arena sized for a source file of `source_len` bytes. The typed
    /// tree has roughly one expression per 24 source bytes.
    pub fn with_source_len(source_len: usize) -> Self {
        let mut arena = Self::default();
        arena.exprs.reserve(source_len / 24);
        arena.expr_lists.reserve(source_len / 64);
        arena
    }

    /// Store an expression.
    #[inline]
    pub fn push_expr(&mut self, expr: Expression) -> TExprIdx {
        let idx = TExprIdx::from_index(self.exprs.len());
        self.exprs.push(expr);
        idx
    }

    /// An expression by handle.
    #[inline]
    pub fn expr(&self, idx: TExprIdx) -> &Expression {
        &self.exprs[idx.index()]
    }

    /// A stored expression, for the few in-place updates the type checker
    /// makes to a node it has just built.
    #[inline]
    pub fn expr_mut(&mut self, idx: TExprIdx) -> &mut Expression {
        &mut self.exprs[idx.index()]
    }

    /// Store a list of expression handles.
    pub fn push_expr_list(&mut self, items: &[TExprIdx]) -> TExprList {
        self.expr_lists.push_iter(items.iter().copied())
    }

    /// Store each expression, then the list of their handles.
    pub fn push_exprs(&mut self, exprs: impl IntoIterator<Item = Expression>) -> TExprList {
        let handles: smallvec::SmallVec<[TExprIdx; 8]> =
            exprs.into_iter().map(|e| self.push_expr(e)).collect();
        self.push_expr_list(&handles)
    }

    /// The handles of an expression list.
    #[inline]
    pub fn expr_list(&self, list: TExprList) -> &[TExprIdx] {
        self.expr_lists.get(list)
    }

    /// The expressions of a list.
    pub fn exprs(&self, list: TExprList) -> impl ExactSizeIterator<Item = &Expression> + '_ {
        self.expr_list(list).iter().map(|&idx| self.expr(idx))
    }

    /// Number of stored expressions.
    pub fn expr_count(&self) -> usize {
        self.exprs.len()
    }
}
