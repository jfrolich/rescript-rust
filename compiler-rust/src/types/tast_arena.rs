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

use super::typedtree::{
    ApplyArg, Case, DictEntry, ExpExtra, Expression, ExtensionConstructor, FunctionParam, ModuleExpr,
    ModuleType, PatExtra, Pattern, RecordField, StructureItem, TypedCoreType, TypedSignatureItem,
    TypedValueDescription, ValueBinding,
};
use crate::parse_arena::LocIdx;
use crate::parser::ast::Attributes;

macro_rules! arena_handle {
    ($(#[$doc:meta])* $name:ident) => {
        $(#[$doc])*
        ///
        /// Stored as `index + 1` so the `Option` of a handle is four bytes.
        #[derive(Clone, Copy, PartialEq, Eq, Hash)]
        pub struct $name(NonZeroU32);

        impl $name {
            #[inline]
            fn from_index(index: usize) -> Self {
                let raw = u32::try_from(index + 1).expect("typed arena exceeds u32::MAX");
                Self(NonZeroU32::new(raw).expect("index + 1 is non-zero"))
            }

            #[inline]
            fn index(self) -> usize {
                (self.0.get() - 1) as usize
            }
        }

        impl std::fmt::Debug for $name {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(f, concat!(stringify!($name), "({})"), self.index())
            }
        }
    };
}

arena_handle!(
    /// Handle of a typed module type in a [`TypedArena`].
    TModTypeIdx
);

arena_handle!(
    /// Handle of a typed core type (a type annotation) in a [`TypedArena`].
    TCoreTypeIdx
);

arena_handle!(
    /// Handle of a typed pattern in a [`TypedArena`].
    TPatIdx
);

arena_handle!(
    /// Handle of the cold data (extras and attributes) of an expression.
    TExpColdIdx
);

arena_handle!(
    /// Handle of the cold data (extras and attributes) of a pattern.
    TPatColdIdx
);

/// One `exp_extra` entry: the wrapper, its location and its attributes.
pub type ExpExtraItem = (ExpExtra, LocIdx, Attributes);

/// One `pat_extra` entry: the wrapper, its location and its attributes.
pub type PatExtraItem = (PatExtra, LocIdx, Attributes);

/// The rarely present fields of an expression (`exp_extra`,
/// `exp_attributes`), kept out of the node. Only nodes with either one get
/// a record.
#[derive(Debug, Clone, Default)]
pub struct ExpCold {
    extra: Vec<ExpExtraItem>,
    attributes: Attributes,
}

/// The rarely present fields of a pattern (`pat_extra`, `pat_attributes`).
#[derive(Debug, Clone, Default)]
pub struct PatCold {
    extra: Vec<PatExtraItem>,
    attributes: Attributes,
}

arena_handle!(
    /// Handle of a typed extension constructor (`exception` or `type t +=`
    /// constructor) in a [`TypedArena`].
    TExtIdx
);

arena_handle!(
    /// Handle of a typed value description (`external` or signature `let`)
    /// in a [`TypedArena`].
    TValDescIdx
);

/// A list of typed patterns (tuple, constructor and array items).
pub type TPatList = ArenaList<TPatIdx>;

/// Handles with this bit set name patterns and pattern lists in an overlay
/// (the match compiler's synthesized patterns), not in a [`TypedArena`].
const OVERLAY_BIT: u32 = 1 << 31;

impl TPatIdx {
    /// The handle of the `index`th pattern of an overlay.
    pub(crate) fn overlay(index: usize) -> Self {
        let raw = u32::try_from(index + 1).expect("pattern overlay exceeds u32::MAX");
        assert!(raw < OVERLAY_BIT, "pattern overlay too large");
        Self(NonZeroU32::new(raw | OVERLAY_BIT).expect("non-zero"))
    }

    /// The overlay index, for an overlay handle.
    pub(crate) fn overlay_index(self) -> Option<usize> {
        let raw = self.0.get();
        (raw & OVERLAY_BIT != 0).then(|| ((raw & !OVERLAY_BIT) - 1) as usize)
    }
}

/// An overlay pattern list of `len` items at `index` in its list table.
pub(crate) fn overlay_pattern_list(index: usize, len: usize) -> TPatList {
    let start = u32::try_from(index).expect("pattern overlay exceeds u32::MAX");
    assert!(start < OVERLAY_BIT, "pattern overlay too large");
    ArenaList::from_range(
        start | OVERLAY_BIT,
        u32::try_from(len).expect("pattern list exceeds u32::MAX"),
    )
}

/// The overlay list-table index, for a non-empty overlay pattern list.
pub(crate) fn overlay_pattern_list_index(list: TPatList) -> Option<usize> {
    if list.is_empty() {
        return None;
    }
    let start = list.start();
    (start & OVERLAY_BIT != 0).then_some((start & !OVERLAY_BIT) as usize)
}

/// A list of typed core types (tuple and constructor arguments).
pub type TCoreTypeList = ArenaList<TCoreTypeIdx>;

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

/// Handle of a typed module expression in a [`TypedArena`].
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct TModExprIdx(NonZeroU32);

impl TModExprIdx {
    #[inline]
    fn from_index(index: usize) -> Self {
        let raw = u32::try_from(index + 1).expect("typed module arena exceeds u32::MAX");
        Self(NonZeroU32::new(raw).expect("index + 1 is non-zero"))
    }

    #[inline]
    fn index(self) -> usize {
        (self.0.get() - 1) as usize
    }
}

impl std::fmt::Debug for TModExprIdx {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "TModExprIdx({})", self.index())
    }
}

/// A list of typed expressions (tuple, array and constructor arguments,
/// template values).
pub type TExprList = ArenaList<TExprIdx>;

/// The cases of a `match` or `try`.
pub type TCaseList = ArenaList<Case>;
/// The bindings of a `let`.
pub type TVbList = ArenaList<ValueBinding>;
/// The arguments of an application.
pub type TArgList = ArenaList<ApplyArg>;
/// The parameters of a function.
pub type TParamList = ArenaList<FunctionParam>;
/// The fields of a record expression.
pub type TFieldList = ArenaList<RecordField>;
/// The entries of a dict literal.
pub type TDictList = ArenaList<DictEntry>;
/// The items of a structure.
pub type TStrItemList = ArenaList<StructureItem>;
/// The items of a signature.
pub type TSigItemList = ArenaList<TypedSignatureItem>;

/// One pool of list items. A list is a contiguous range, pushed in one go.
#[derive(Debug, Clone)]
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
    module_exprs: Vec<ModuleExpr>,
    module_types: Vec<ModuleType>,
    core_types: Vec<TypedCoreType>,
    patterns: Vec<Pattern>,
    pattern_lists: ListPool<TPatIdx>,
    extension_constructors: Vec<ExtensionConstructor>,
    value_descriptions: Vec<TypedValueDescription>,
    core_type_lists: ListPool<TCoreTypeIdx>,
    cases: ListPool<Case>,
    value_bindings: ListPool<ValueBinding>,
    apply_args: ListPool<ApplyArg>,
    function_params: ListPool<FunctionParam>,
    record_fields: ListPool<RecordField>,
    dict_entries: ListPool<DictEntry>,
    structure_items: ListPool<StructureItem>,
    signature_items: ListPool<TypedSignatureItem>,
    exp_colds: Vec<ExpCold>,
    pat_colds: Vec<PatCold>,
    /// What the checker recorded for `Tstr_derived` items, indexed by the
    /// plan's handles.
    pub derived: crate::types::derived::DerivedTable,
}

/// Accessors for the cold data of expressions and patterns. Records are
/// never updated in place: a node copy shares its record, so each change
/// stores a new one, which keeps OCaml's value semantics for
/// `exp_extra`/`pat_extra` (`compiler/ml/typedtree.ml`).
impl TypedArena {
    /// A pattern-only scratch copy for lowering dictionary patterns while
    /// the original typed arena is borrowed by translation. Preserve handles
    /// and cold records; expression and module pools are not needed.
    pub(crate) fn clone_pattern_storage(&self) -> Self {
        Self {
            patterns: self.patterns.clone(),
            pattern_lists: self.pattern_lists.clone(),
            pat_colds: self.pat_colds.clone(),
            ..Self::default()
        }
    }

    /// `exp_extra`, outermost wrapper first.
    #[inline]
    pub fn exp_extra(&self, e: &Expression) -> &[ExpExtraItem] {
        match e.exp_cold {
            Some(idx) => &self.exp_colds[idx.index()].extra,
            None => &[],
        }
    }

    /// `exp_attributes`.
    #[inline]
    pub fn exp_attributes(&self, e: &Expression) -> &Attributes {
        match e.exp_cold {
            Some(idx) => &self.exp_colds[idx.index()].attributes,
            None => &Attributes::EMPTY,
        }
    }

    fn update_exp_cold(&mut self, e: &mut Expression, f: impl FnOnce(&mut ExpCold)) {
        let mut cold = match e.exp_cold {
            Some(idx) => self.exp_colds[idx.index()].clone(),
            None => ExpCold::default(),
        };
        f(&mut cold);
        e.exp_cold = if cold.extra.is_empty() && cold.attributes.is_empty() {
            None
        } else {
            let idx = TExpColdIdx::from_index(self.exp_colds.len());
            self.exp_colds.push(cold);
            Some(idx)
        };
    }

    /// `e` with `exp_attributes` set to `attributes`.
    pub fn with_exp_attributes(&mut self, mut e: Expression, attributes: Attributes) -> Expression {
        if attributes.is_empty() && e.exp_cold.is_none() {
            return e;
        }
        self.update_exp_cold(&mut e, |cold| cold.attributes = attributes);
        e
    }

    /// Add an innermost `exp_extra` wrapper.
    pub fn push_exp_extra(&mut self, e: &mut Expression, item: ExpExtraItem) {
        self.update_exp_cold(e, |cold| cold.extra.push(item));
    }

    /// Add an outermost `exp_extra` wrapper.
    pub fn prepend_exp_extra(&mut self, e: &mut Expression, item: ExpExtraItem) {
        self.update_exp_cold(e, |cold| cold.extra.insert(0, item));
    }

    /// `pat_extra`, outermost wrapper first.
    #[inline]
    pub fn pat_extra(&self, p: &Pattern) -> &[PatExtraItem] {
        match p.pat_cold {
            Some(idx) => &self.pat_colds[idx.index()].extra,
            None => &[],
        }
    }

    /// `pat_attributes`.
    #[inline]
    pub fn pat_attributes(&self, p: &Pattern) -> &Attributes {
        match p.pat_cold {
            Some(idx) => &self.pat_colds[idx.index()].attributes,
            None => &Attributes::EMPTY,
        }
    }

    fn update_pat_cold(&mut self, p: &mut Pattern, f: impl FnOnce(&mut PatCold)) {
        let mut cold = match p.pat_cold {
            Some(idx) => self.pat_colds[idx.index()].clone(),
            None => PatCold::default(),
        };
        f(&mut cold);
        p.pat_cold = if cold.extra.is_empty() && cold.attributes.is_empty() {
            None
        } else {
            let idx = TPatColdIdx::from_index(self.pat_colds.len());
            self.pat_colds.push(cold);
            Some(idx)
        };
    }

    /// `p` with `pat_attributes` set to `attributes`.
    pub fn with_pat_attributes(&mut self, mut p: Pattern, attributes: Attributes) -> Pattern {
        if attributes.is_empty() && p.pat_cold.is_none() {
            return p;
        }
        self.update_pat_cold(&mut p, |cold| cold.attributes = attributes);
        p
    }

    /// Add an innermost `pat_extra` wrapper.
    pub fn push_pat_extra(&mut self, p: &mut Pattern, item: PatExtraItem) {
        self.update_pat_cold(p, |cold| cold.extra.push(item));
    }

    /// Replace `pat_extra`.
    pub fn set_pat_extra(&mut self, p: &mut Pattern, extra: Vec<PatExtraItem>) {
        self.update_pat_cold(p, |cold| cold.extra = extra);
    }

    /// Add an outermost `pat_extra` wrapper.
    pub fn prepend_pat_extra(&mut self, p: &mut Pattern, item: PatExtraItem) {
        self.update_pat_cold(p, |cold| cold.extra.insert(0, item));
    }
}

macro_rules! list_pool_accessors {
    ($($push:ident, $get:ident, $pool:ident, $item:ty;)*) => {
        impl TypedArena {
            $(
                /// Store a list.
                pub fn $push(&mut self, items: impl IntoIterator<Item = $item>) -> ArenaList<$item> {
                    self.$pool.push_iter(items)
                }

                /// The items of a stored list.
                #[inline]
                pub fn $get(&self, list: ArenaList<$item>) -> &[$item] {
                    self.$pool.get(list)
                }
            )*
        }
    };
}

list_pool_accessors! {
    push_cases, cases, cases, Case;
    push_value_bindings, value_bindings, value_bindings, ValueBinding;
    push_apply_args, apply_args, apply_args, ApplyArg;
    push_function_params, function_params, function_params, FunctionParam;
    push_record_fields, record_fields, record_fields, RecordField;
    push_dict_entries, dict_entries, dict_entries, DictEntry;
    push_structure_items, structure_items, structure_items, StructureItem;
    push_signature_items, signature_items, signature_items, TypedSignatureItem;
}

impl TypedArena {
    /// An empty arena.
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

    /// Store a module expression.
    #[inline]
    pub fn push_module_expr(&mut self, m: ModuleExpr) -> TModExprIdx {
        let idx = TModExprIdx::from_index(self.module_exprs.len());
        self.module_exprs.push(m);
        idx
    }

    /// A module expression by handle.
    #[inline]
    pub fn module_expr(&self, idx: TModExprIdx) -> &ModuleExpr {
        &self.module_exprs[idx.index()]
    }

    /// Store a module type.
    #[inline]
    pub fn push_module_type(&mut self, m: ModuleType) -> TModTypeIdx {
        let idx = TModTypeIdx::from_index(self.module_types.len());
        self.module_types.push(m);
        idx
    }

    /// A module type by handle.
    #[inline]
    pub fn module_type(&self, idx: TModTypeIdx) -> &ModuleType {
        &self.module_types[idx.index()]
    }

    /// Store a core type.
    #[inline]
    pub fn push_core_type(&mut self, t: TypedCoreType) -> TCoreTypeIdx {
        let idx = TCoreTypeIdx::from_index(self.core_types.len());
        self.core_types.push(t);
        idx
    }

    /// A core type by handle.
    #[inline]
    pub fn core_type(&self, idx: TCoreTypeIdx) -> &TypedCoreType {
        &self.core_types[idx.index()]
    }

    /// Store each core type, then the list of their handles.
    pub fn push_core_types(
        &mut self,
        types: impl IntoIterator<Item = TypedCoreType>,
    ) -> TCoreTypeList {
        let handles: smallvec::SmallVec<[TCoreTypeIdx; 8]> =
            types.into_iter().map(|t| self.push_core_type(t)).collect();
        self.core_type_lists.push_iter(handles)
    }

    /// Store a list of core type handles.
    pub fn push_core_type_list(&mut self, items: &[TCoreTypeIdx]) -> TCoreTypeList {
        self.core_type_lists.push_iter(items.iter().copied())
    }

    /// The handles of a core type list.
    #[inline]
    pub fn core_type_list(&self, list: TCoreTypeList) -> &[TCoreTypeIdx] {
        self.core_type_lists.get(list)
    }

    /// The core types of a list.
    pub fn core_types(
        &self,
        list: TCoreTypeList,
    ) -> impl ExactSizeIterator<Item = &TypedCoreType> + '_ {
        self.core_type_list(list)
            .iter()
            .map(|&idx| self.core_type(idx))
    }

    /// Store a pattern.
    #[inline]
    pub fn push_pattern(&mut self, p: Pattern) -> TPatIdx {
        let idx = TPatIdx::from_index(self.patterns.len());
        self.patterns.push(p);
        idx
    }

    /// A pattern by handle.
    #[inline]
    pub fn pattern(&self, idx: TPatIdx) -> &Pattern {
        &self.patterns[idx.index()]
    }

    /// The handle of `pat` when it is a pattern stored in this arena (found
    /// by address, since the match compiler works on pattern references).
    pub(crate) fn pattern_handle(&self, pat: &Pattern) -> Option<TPatIdx> {
        let size = std::mem::size_of::<Pattern>();
        let base = self.patterns.as_ptr() as usize;
        let addr = pat as *const Pattern as usize;
        let offset = addr.checked_sub(base)?;
        let index = offset / size;
        (offset % size == 0 && index < self.patterns.len()).then(|| TPatIdx::from_index(index))
    }

    /// A stored pattern, for the in-place updates the type checker makes
    /// to a pattern it has just built.
    #[inline]
    pub fn pattern_mut(&mut self, idx: TPatIdx) -> &mut Pattern {
        &mut self.patterns[idx.index()]
    }

    /// Store each pattern, then the list of their handles.
    pub fn push_patterns(&mut self, pats: impl IntoIterator<Item = Pattern>) -> TPatList {
        let handles: smallvec::SmallVec<[TPatIdx; 8]> =
            pats.into_iter().map(|p| self.push_pattern(p)).collect();
        self.pattern_lists.push_iter(handles)
    }

    /// Store a list of pattern handles.
    pub fn push_pattern_list(&mut self, items: &[TPatIdx]) -> TPatList {
        self.pattern_lists.push_iter(items.iter().copied())
    }

    /// The handles of a pattern list.
    #[inline]
    pub fn pattern_list(&self, list: TPatList) -> &[TPatIdx] {
        self.pattern_lists.get(list)
    }

    /// The patterns of a list.
    pub fn patterns(&self, list: TPatList) -> impl ExactSizeIterator<Item = &Pattern> + '_ {
        self.pattern_list(list).iter().map(|&idx| self.pattern(idx))
    }

    /// Store an extension constructor.
    #[inline]
    pub fn push_extension_constructor(&mut self, ext: ExtensionConstructor) -> TExtIdx {
        let idx = TExtIdx::from_index(self.extension_constructors.len());
        self.extension_constructors.push(ext);
        idx
    }

    /// An extension constructor by handle.
    #[inline]
    pub fn extension_constructor(&self, idx: TExtIdx) -> &ExtensionConstructor {
        &self.extension_constructors[idx.index()]
    }

    /// Store a value description.
    #[inline]
    pub fn push_value_description(&mut self, vd: TypedValueDescription) -> TValDescIdx {
        let idx = TValDescIdx::from_index(self.value_descriptions.len());
        self.value_descriptions.push(vd);
        idx
    }

    /// A value description by handle.
    #[inline]
    pub fn value_description(&self, idx: TValDescIdx) -> &TypedValueDescription {
        &self.value_descriptions[idx.index()]
    }

    /// Number of stored expressions.
    pub fn expr_count(&self) -> usize {
        self.exprs.len()
    }
}
