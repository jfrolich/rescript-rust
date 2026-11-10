//! Core type expressions for the type system.
//!
//! This module defines `TypeExpr` and `TypeDesc`, the fundamental types
//! for representing types in the ReScript type checker.
//!
//! # Memory Model
//!
//! Type expressions are allocated in a `TypeArena` owned by the `TypeContext`.
//! They use interior mutability (`RefCell`) for the unification algorithm,
//! which requires mutating the `desc` field to create `Tlink` chains.
//!
//! # Concurrency
//!
//! Type expressions are NOT thread-safe - they use `RefCell` for interior
//! mutability. However, this is fine because:
//! - Each compilation gets its own `TypeContext`
//! - Parallelism happens at the file level, not within type checking
//!
//! # Level-based Generalization
//!
//! Each type has a `level` that tracks its binding depth:
//! - `generic_level` (100000000): Fully polymorphic type variables
//! - Other levels: Track when the type was introduced
//! - Variables with level > current_level can be generalized

use super::asttypes::{ArgLabel, Label, PrivateFlag};
use super::decl_loc::DeclLoc;
use super::path::Path;
use crate::parser::longident::Longident;
use std::cell::{Cell, RefCell};
use std::hash::{Hash, Hasher};

/// The generic level for fully polymorphic types.
pub const GENERIC_LEVEL: i32 = 100_000_000;

/// The lowest level (used for marking during traversal).
pub const LOWEST_LEVEL: i32 = 0;

/// Pivot level for traversal marking.
pub const PIVOT_LEVEL: i32 = (2 * LOWEST_LEVEL) - 1;

/// A type expression.
///
/// This is the core type representation used throughout the type checker.
/// It uses interior mutability for the unification algorithm.
///
/// # Fields
///
/// - `desc`: The type descriptor (what kind of type this is)
/// - `level`: The binding level for generalization
/// - `id`: A unique identifier for this type expression
#[derive(Debug)]
pub struct TypeExpr {
    /// The type descriptor. Uses `RefCell` for unification.
    desc: RefCell<TypeDesc>,
    /// The binding level. Uses `Cell` for generalization.
    level: Cell<i32>,
    /// Unique identifier for this type expression.
    id: i32,
}

impl TypeExpr {
    /// Create a new type expression.
    pub fn new(desc: TypeDesc, level: i32, id: i32) -> Self {
        TypeExpr {
            desc: RefCell::new(desc),
            level: Cell::new(level),
            id,
        }
    }

    /// Get the type descriptor.
    ///
    /// # Panics
    ///
    /// Panics if the descriptor is currently borrowed mutably.
    pub fn desc(&self) -> std::cell::Ref<'_, TypeDesc> {
        self.desc.borrow()
    }

    /// Get a mutable reference to the type descriptor.
    ///
    /// # Panics
    ///
    /// Panics if the descriptor is currently borrowed.
    pub fn desc_mut(&self) -> std::cell::RefMut<'_, TypeDesc> {
        self.desc.borrow_mut()
    }

    /// Set the type descriptor.
    pub fn set_desc(&self, desc: TypeDesc) {
        *self.desc.borrow_mut() = desc;
    }

    /// Get the binding level.
    pub fn level(&self) -> i32 {
        self.level.get()
    }

    /// Set the binding level.
    pub fn set_level(&self, level: i32) {
        self.level.set(level);
    }

    /// Get the unique ID.
    pub fn id(&self) -> i32 {
        self.id
    }
}

impl PartialEq for TypeExpr {
    fn eq(&self, other: &Self) -> bool {
        // Two type expressions are equal if they have the same id
        self.id == other.id
    }
}

impl Eq for TypeExpr {}

impl Hash for TypeExpr {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.id.hash(state);
    }
}

impl Ord for TypeExpr {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.id.cmp(&other.id)
    }
}

impl PartialOrd for TypeExpr {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

/// Immutable list of type references in a type descriptor (constructor and
/// package arguments, tuple components, polymorphic variables).
///
/// Intentional Rust performance representation of the OCaml `type_expr list`
/// fields in `compiler/ml/types.ml:24-50`: a `Copy` handle to a range of an
/// append-only list pool, so descriptors hold no heap data. The pool is the
/// one of the tier that owns the list, chosen by the same tag bits as
/// [`TypeExprRef`]: the compilation-local [`TypeContext`] pool, the worker
/// store, or a published shared graph. Read the elements with
/// `TypeContext::types`. Lists are never mutated, so a handle can be copied
/// freely; element order and physical identities are unchanged. Handles have
/// no equality: compare the elements.
///
/// [`TypeContext`]: super::context::TypeContext
#[derive(Clone, Copy)]
pub struct TypeRefList {
    start: u32,
    len: u32,
}

/// The elements of a [`TypeRefList`], copied out of its pool.
pub type TypeRefs = smallvec::SmallVec<[TypeExprRef; 4]>;

impl TypeRefList {
    /// The empty list (no pool access).
    pub const EMPTY: Self = TypeRefList { start: 0, len: 0 };

    /// The empty list.
    #[inline]
    pub const fn new() -> Self {
        Self::EMPTY
    }

    #[inline]
    pub(crate) fn from_parts(start: u32, len: usize) -> Self {
        let len = u32::try_from(len).expect("type list too long");
        if len == 0 {
            return Self::EMPTY;
        }
        TypeRefList { start, len }
    }

    /// Number of elements.
    #[inline]
    pub fn len(self) -> usize {
        self.len as usize
    }

    /// Whether the list has no elements.
    #[inline]
    pub fn is_empty(self) -> bool {
        self.len == 0
    }

    /// Raw start position, including the tier tag bits.
    #[inline]
    pub(crate) fn raw_start(self) -> u32 {
        self.start
    }

    /// Whether the list lives outside the compilation.
    #[inline]
    pub(crate) fn is_store(self) -> bool {
        self.start & STORE_REF_TAG != 0
    }

    /// Whether the list lives in the process-wide shared pool.
    #[inline]
    pub(crate) fn is_shared(self) -> bool {
        self.start & SHARED_REF_BITS == SHARED_REF_BITS
    }
}

/// A `Copy` handle to one immutable payload of a type descriptor, stored in
/// the payload pool of the owning tier (see [`TypePayloadPool`]); the tier is
/// selected by the same tag bits as [`TypeExprRef`].
macro_rules! payload_handle {
    ($(#[$doc:meta])* $name:ident) => {
        $(#[$doc])*
        #[derive(Clone, Copy)]
        pub struct $name(u32);

        impl $name {
            #[inline]
            pub(crate) fn from_raw(raw: u32) -> Self {
                $name(raw)
            }

            #[inline]
            pub(crate) fn raw(self) -> u32 {
                self.0
            }

            #[inline]
            pub(crate) fn is_store(self) -> bool {
                self.0 & STORE_REF_TAG != 0
            }

            #[inline]
            pub(crate) fn is_shared(self) -> bool {
                self.0 & SHARED_REF_BITS == SHARED_REF_BITS
            }
        }

        impl From<&$name> for $name {
            #[inline]
            fn from(handle: &$name) -> Self {
                *handle
            }
        }

        impl std::fmt::Debug for $name {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(f, concat!(stringify!($name), "({:#x})"), self.0)
            }
        }
    };
}

payload_handle!(
    /// The row of a `Tvariant` (`compiler/ml/types.ml:42`): an immutable
    /// [`RowDesc`] in a payload pool. Read it with `TypeContext::row_desc`.
    RowDescRef
);

payload_handle!(
    /// The constraint names of a `Tpackage` (`compiler/ml/types.ml:50`).
    /// Read them with `TypeContext::package_lids`.
    PackageLidsRef
);

/// Append-only chunked storage with stable element addresses: chunk `k`
/// holds `1 << (FIRST_BITS + k)` slots, chunks are allocated on first use and
/// never moved, so a reader holds a plain shared reference into a chunk while
/// later appends fill other slots (the same layout as `TypeNodes`). `S` is
/// the slot type: a `Cell` for list elements written once when their list is
/// appended, a `OnceCell` for single payloads.
struct PayloadChunks<S, const FIRST_BITS: u32> {
    chunks: [std::cell::OnceCell<Box<[S]>>; 24],
    len: Cell<usize>,
}

impl<S, const FIRST_BITS: u32> Default for PayloadChunks<S, FIRST_BITS> {
    fn default() -> Self {
        PayloadChunks {
            chunks: std::array::from_fn(|_| std::cell::OnceCell::new()),
            len: Cell::new(0),
        }
    }
}

impl<S, const FIRST_BITS: u32> PayloadChunks<S, FIRST_BITS> {
    /// Chunk and offset of slot `idx`.
    #[inline(always)]
    fn locate(idx: usize) -> (usize, usize) {
        let biased = idx + (1 << FIRST_BITS);
        let bit = (usize::BITS - 1 - biased.leading_zeros()) as usize;
        (bit - FIRST_BITS as usize, biased - (1 << bit))
    }

    #[inline(always)]
    fn chunk_size(chunk: usize) -> usize {
        1 << (FIRST_BITS as usize + chunk)
    }

    #[inline(always)]
    fn chunk_base(chunk: usize) -> usize {
        Self::chunk_size(chunk) - (1 << FIRST_BITS)
    }

    /// Reserve `n` contiguous slots in one chunk and return their start, the
    /// chunk's slots (allocated with `init` on first use) and the offset of
    /// the first reserved slot. A run that does not fit in the current chunk
    /// starts the next chunk large enough for it; the skipped tail stays
    /// unused.
    fn reserve(&self, n: usize, init: impl FnOnce(usize) -> Box<[S]>) -> (usize, &[S], usize) {
        let mut start = self.len.get();
        let (mut chunk, mut offset) = Self::locate(start);
        if offset + n > Self::chunk_size(chunk) {
            chunk += 1;
            while Self::chunk_size(chunk) < n {
                chunk += 1;
            }
            start = Self::chunk_base(chunk);
            offset = 0;
        }
        assert!(
            u32::try_from(start + n).is_ok_and(|end| end & SHARED_REF_BITS == 0),
            "type payload pool index exceeds the tag range"
        );
        let slots = self.chunks[chunk].get_or_init(|| init(Self::chunk_size(chunk)));
        self.len.set(start + n);
        (start, slots, offset)
    }

    /// Slots `start..start + n`, all in one chunk.
    #[inline(always)]
    fn slots(&self, start: usize, n: usize) -> &[S] {
        let (chunk, offset) = Self::locate(start);
        &self.chunks[chunk]
            .get()
            .expect("type payload index refers to an unallocated chunk")[offset..offset + n]
    }
}

/// Lists of `Copy` elements (type lists, arrow parameters).
type ListChunks<T> = PayloadChunks<Cell<T>, 8>;

impl<T: Copy> ListChunks<T> {
    /// Append `items` (not empty) and return their untagged start.
    fn append(&self, items: &[T]) -> usize {
        let first = items[0];
        let (start, slots, offset) =
            self.reserve(items.len(), |size| vec![Cell::new(first); size].into_boxed_slice());
        for (slot, &item) in slots[offset..offset + items.len()].iter().zip(items) {
            slot.set(item);
        }
        start
    }
}

/// Single payloads written once (rows, package constraint names).
type OnceChunks<T> = PayloadChunks<std::cell::OnceCell<T>, 4>;

impl<T> OnceChunks<T> {
    /// Append `item` and return its untagged index.
    fn push(&self, item: T) -> usize {
        let (index, slots, offset) = self.reserve(1, |size| {
            (0..size).map(|_| std::cell::OnceCell::new()).collect()
        });
        if slots[offset].set(item).is_err() {
            unreachable!("payload slot written twice");
        }
        index
    }

    #[inline]
    fn get(&self, index: usize) -> &T {
        self.slots(index, 1)[0]
            .get()
            .expect("type payload index refers to an unwritten slot")
    }
}

/// A borrowed, read-only view of an immutable payload list: the slots of a
/// tier-local pool (written once, before the list's handle exists) or the
/// elements of a published shared graph. Reading an element copies it out;
/// holding a view does not block allocation in any pool.
#[derive(Clone, Copy)]
pub enum PoolSlice<'a, T: Copy> {
    /// A list in a compilation or worker-store pool.
    Cells(&'a [Cell<T>]),
    /// A list in a published shared graph (or the empty list).
    Plain(&'a [T]),
}

/// The elements of a [`TypeRefList`].
pub type TypeSlice<'a> = PoolSlice<'a, TypeExprRef>;
/// The parameters of a [`TypeArgList`].
pub type TypeArgSlice<'a> = PoolSlice<'a, TypeArg>;

impl<'a, T: Copy> PoolSlice<'a, T> {
    /// The empty view.
    pub const EMPTY: Self = PoolSlice::Plain(&[]);

    /// Number of elements.
    #[inline]
    pub fn len(self) -> usize {
        match self {
            PoolSlice::Cells(slots) => slots.len(),
            PoolSlice::Plain(items) => items.len(),
        }
    }

    /// Whether the view has no elements.
    #[inline]
    pub fn is_empty(self) -> bool {
        self.len() == 0
    }

    /// Element `index`, if in range.
    #[inline]
    pub fn get(self, index: usize) -> Option<T> {
        match self {
            PoolSlice::Cells(slots) => slots.get(index).map(Cell::get),
            PoolSlice::Plain(items) => items.get(index).copied(),
        }
    }

    /// Element `index`; panics when out of range, like slice indexing.
    #[inline]
    #[track_caller]
    pub fn at(self, index: usize) -> T {
        match self {
            PoolSlice::Cells(slots) => slots[index].get(),
            PoolSlice::Plain(items) => items[index],
        }
    }

    /// The first element.
    #[inline]
    pub fn first(self) -> Option<T> {
        self.get(0)
    }

    /// The last element.
    #[inline]
    pub fn last(self) -> Option<T> {
        self.len().checked_sub(1).and_then(|index| self.get(index))
    }

    /// The elements `range` as a view.
    #[inline]
    #[track_caller]
    pub fn slice(self, range: impl std::slice::SliceIndex<[Cell<T>], Output = [Cell<T>]> + std::slice::SliceIndex<[T], Output = [T]>) -> Self {
        match self {
            PoolSlice::Cells(slots) => PoolSlice::Cells(&slots[range]),
            PoolSlice::Plain(items) => PoolSlice::Plain(&items[range]),
        }
    }

    /// Iterate over copies of the elements.
    #[inline]
    pub fn iter(self) -> PoolIter<'a, T> {
        match self {
            PoolSlice::Cells(slots) => PoolIter::Cells(slots.iter()),
            PoolSlice::Plain(items) => PoolIter::Plain(items.iter()),
        }
    }

    /// The elements as a vector.
    pub fn to_vec(self) -> Vec<T> {
        self.iter().collect()
    }

    /// The elements as an inline-first vector.
    pub fn to_smallvec<const N: usize>(self) -> smallvec::SmallVec<[T; N]> {
        self.iter().collect()
    }
}

impl<'a, T: Copy> IntoIterator for PoolSlice<'a, T> {
    type Item = T;
    type IntoIter = PoolIter<'a, T>;

    #[inline]
    fn into_iter(self) -> PoolIter<'a, T> {
        self.iter()
    }
}

impl<T: Copy + PartialEq> PartialEq for PoolSlice<'_, T> {
    fn eq(&self, other: &Self) -> bool {
        self.len() == other.len() && self.iter().eq(other.iter())
    }
}

impl<T: Copy + std::fmt::Debug> std::fmt::Debug for PoolSlice<'_, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

/// Iterator over a [`PoolSlice`], yielding copies.
#[derive(Clone)]
pub enum PoolIter<'a, T: Copy> {
    Cells(std::slice::Iter<'a, Cell<T>>),
    Plain(std::slice::Iter<'a, T>),
}

impl<T: Copy> Iterator for PoolIter<'_, T> {
    type Item = T;

    #[inline]
    fn next(&mut self) -> Option<T> {
        match self {
            PoolIter::Cells(slots) => slots.next().map(Cell::get),
            PoolIter::Plain(items) => items.next().copied(),
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.len();
        (len, Some(len))
    }

    #[inline]
    fn nth(&mut self, n: usize) -> Option<T> {
        match self {
            PoolIter::Cells(slots) => slots.nth(n).map(Cell::get),
            PoolIter::Plain(items) => items.nth(n).copied(),
        }
    }
}

impl<T: Copy> DoubleEndedIterator for PoolIter<'_, T> {
    #[inline]
    fn next_back(&mut self) -> Option<T> {
        match self {
            PoolIter::Cells(slots) => slots.next_back().map(Cell::get),
            PoolIter::Plain(items) => items.next_back().copied(),
        }
    }
}

impl<T: Copy> ExactSizeIterator for PoolIter<'_, T> {
    #[inline]
    fn len(&self) -> usize {
        match self {
            PoolIter::Cells(slots) => slots.len(),
            PoolIter::Plain(items) => items.len(),
        }
    }
}

impl<T: Copy> std::iter::FusedIterator for PoolIter<'_, T> {}

/// Append-only pools of the immutable payloads of type descriptors for one
/// storage tier: type lists ([`TypeRefList`]), arrow parameter lists
/// ([`TypeArgList`]), rows ([`RowDescRef`]) and package constraint names
/// ([`PackageLidsRef`]). `tag` is the tier's tag bits, or-ed into every
/// handle it returns. Payloads never move once appended, so reads borrow
/// them without a borrow flag or a copy.
#[derive(Default)]
pub(crate) struct TypePayloadPool {
    items: ListChunks<TypeExprRef>,
    args: ListChunks<TypeArg>,
    rows: OnceChunks<RowDesc>,
    lids: OnceChunks<Vec<Longident>>,
    tag: u32,
}

impl TypePayloadPool {
    pub(crate) fn with_tag(tag: u32) -> Self {
        TypePayloadPool {
            tag,
            ..Default::default()
        }
    }

    #[inline]
    fn untag(&self, raw: u32) -> usize {
        (raw & !self.tag) as usize
    }

    /// Add a row.
    pub(crate) fn alloc_row(&self, row: RowDesc) -> RowDescRef {
        RowDescRef(self.rows.push(row) as u32 | self.tag)
    }

    /// A row allocated by this pool.
    #[inline]
    pub(crate) fn get_row(&self, row: RowDescRef) -> &RowDesc {
        self.rows.get(self.untag(row.raw()))
    }

    /// Add package constraint names.
    pub(crate) fn alloc_lids(&self, lids: Vec<Longident>) -> PackageLidsRef {
        PackageLidsRef(self.lids.push(lids) as u32 | self.tag)
    }

    /// Package constraint names allocated by this pool.
    pub(crate) fn get_lids(&self, lids: PackageLidsRef) -> &[Longident] {
        self.lids.get(self.untag(lids.raw()))
    }

    /// Append `items` as a new list.
    pub(crate) fn alloc(&self, items: &[TypeExprRef]) -> TypeRefList {
        if items.is_empty() {
            return TypeRefList::EMPTY;
        }
        TypeRefList::from_parts(self.items.append(items) as u32 | self.tag, items.len())
    }

    /// The elements of a list allocated by this pool.
    #[inline]
    pub(crate) fn get(&self, list: TypeRefList) -> TypeSlice<'_> {
        PoolSlice::Cells(self.items.slots(self.untag(list.raw_start()), list.len()))
    }

    /// One element of a list allocated by this pool.
    #[inline]
    pub(crate) fn get_at(&self, list: TypeRefList, index: usize) -> TypeExprRef {
        assert!(index < list.len(), "type list index out of range");
        self.items.slots(self.untag(list.raw_start()) + index, 1)[0].get()
    }

    /// Append `args` as a new arrow parameter list.
    pub(crate) fn alloc_args(&self, args: &[TypeArg]) -> TypeArgList {
        if args.is_empty() {
            return TypeArgList::EMPTY;
        }
        TypeArgList::from_parts(self.args.append(args) as u32 | self.tag, args.len())
    }

    /// The parameters of a list allocated by this pool.
    #[inline]
    pub(crate) fn get_args(&self, list: TypeArgList) -> TypeArgSlice<'_> {
        PoolSlice::Cells(self.args.slots(self.untag(list.raw_start()), list.len()))
    }
}

impl From<&TypeRefList> for TypeRefList {
    #[inline]
    fn from(list: &TypeRefList) -> Self {
        *list
    }
}

impl Default for TypeRefList {
    fn default() -> Self {
        Self::EMPTY
    }
}

impl std::fmt::Debug for TypeRefList {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "TypeRefList({:#x}, {})", self.start, self.len)
    }
}

/// Immutable list of arrow parameters: a `Copy` handle into the arrow
/// parameter pool of the owning tier, exactly like [`TypeRefList`]. Read the
/// parameters with `TypeContext::type_args`.
#[derive(Clone, Copy)]
pub struct TypeArgList {
    start: u32,
    len: u32,
}

/// The parameters of a [`TypeArgList`], copied out of its pool.
pub type TypeArgs = smallvec::SmallVec<[TypeArg; 4]>;

impl TypeArgList {
    /// The empty list (no pool access).
    pub const EMPTY: Self = TypeArgList { start: 0, len: 0 };

    #[inline]
    pub(crate) fn from_parts(start: u32, len: usize) -> Self {
        let len = u32::try_from(len).expect("arrow parameter list too long");
        if len == 0 {
            return Self::EMPTY;
        }
        TypeArgList { start, len }
    }

    /// Number of parameters.
    #[inline]
    pub fn len(self) -> usize {
        self.len as usize
    }

    /// Whether the list has no parameters.
    #[inline]
    pub fn is_empty(self) -> bool {
        self.len == 0
    }

    #[inline]
    pub(crate) fn raw_start(self) -> u32 {
        self.start
    }

    #[inline]
    pub(crate) fn is_store(self) -> bool {
        self.start & STORE_REF_TAG != 0
    }

    #[inline]
    pub(crate) fn is_shared(self) -> bool {
        self.start & SHARED_REF_BITS == SHARED_REF_BITS
    }
}

impl From<&TypeArgList> for TypeArgList {
    #[inline]
    fn from(list: &TypeArgList) -> Self {
        *list
    }
}

impl Default for TypeArgList {
    fn default() -> Self {
        Self::EMPTY
    }
}

impl std::fmt::Debug for TypeArgList {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "TypeArgList({:#x}, {})", self.start, self.len)
    }
}

/// Type descriptor - the actual content of a type expression. Every
/// payload is a handle, so descriptors are plain `Copy` values.
#[derive(Debug, Clone, Copy)]
pub enum TypeDesc {
    /// Type variable: `'a` or `'_a`
    Tvar(Option<crate::name::Name>),

    /// N-ary arrow (function) type: `(arg1, ..., argN) -> ret`.
    ///
    /// Mirrors `compiler/ml/types.ml`, where `Tarrow` stores the complete
    /// parameter list in one node rather than a chain of unary arrows.
    Tarrow {
        /// Arguments in source order.
        args: TypeArgList,
        /// The return type.
        ret: TypeExprRef,
    },

    /// Tuple type: `(t1, t2, ...)`
    Ttuple(TypeRefList),

    /// Type constructor: `int`, `list<'a>`, etc.
    Tconstr {
        /// The path to the type constructor
        path: Path,
        /// Type arguments
        args: TypeRefList,
        /// Abbreviation memo (for expansion caching)
        abbrev: AbbrevMemoRef,
    },

    /// Object type: `{"f1": t1, ..., "fn": tn}` (types.ml `Tobject`). The
    /// fields are a linked list of `Tfield`/`Tnil`, terminated by a row
    /// variable when the row is open.
    Tobject {
        /// Fields as a linked list of Tfield/Tnil
        fields: TypeExprRef,
    },

    /// Object field (types.ml `Tfield {name; mutability; typ; rest}`).
    Tfield {
        /// Field name
        name: crate::name::Name,
        /// The field's shared mutability cell; read its semantic value with
        /// `TypeContext::mutability_repr`.
        mutability: MutabilityRef,
        /// Field type
        typ: TypeExprRef,
        /// Rest of the fields
        rest: TypeExprRef,
    },

    /// End of object fields
    Tnil,

    /// Link to another type (used during unification)
    Tlink(TypeExprRef),

    /// Substitution marker (used during copying)
    Tsubst(TypeExprRef),

    /// Polymorphic variant type
    Tvariant(RowDescRef),

    /// Universal type variable (from forall quantifier)
    Tunivar(Option<crate::name::Name>),

    /// Polymorphic type: `'a1 ... 'an. ty`
    Tpoly {
        /// The body type
        body: TypeExprRef,
        /// Bound type variables
        vars: TypeRefList,
    },

    /// First-class module type (package)
    Tpackage {
        /// Module type path
        path: Path,
        /// Longidents for package constraints
        lids: PackageLidsRef,
        /// Type arguments
        args: TypeRefList,
    },
}

impl TypeDesc {

}

/// Top bit distinguishes worker-store indices from compilation-local indices.
pub(crate) const STORE_REF_TAG: u32 = 1 << 31;

/// Second bit (only with `STORE_REF_TAG`) selects the process-wide shared
/// pool of immutable dependency graphs (`types::shared_store`) instead of the
/// worker store. Shared references are also `is_store()`: every non-local
/// cell is read-only outside a store build and written through overlays.
pub(crate) const SHARED_REF_TAG: u32 = 1 << 30;
pub(crate) const SHARED_REF_BITS: u32 = STORE_REF_TAG | SHARED_REF_TAG;

/// Compact physical identity for a type node, matching OCaml `type_expr`
/// identity (`compiler/ml/types.ml:22`, `compiler/ml/btype.ml:46-48`).
/// The top bit selects the worker store; remaining bits index its arena or
/// the compilation-local arena. No structural equality or deduplication.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub struct TypeExprRef(pub u32);

impl TypeExprRef {
    /// Create a null reference (for placeholder purposes).
    pub fn null() -> Self {
        TypeExprRef(0)
    }

    #[inline]
    pub(crate) fn from_usize(idx: usize) -> Self {
        let raw = u32::try_from(idx).expect("type arena index exceeds u32::MAX");
        assert!(
            raw & STORE_REF_TAG == 0,
            "local type arena index collides with the store tag"
        );
        Self(raw)
    }

    /// Reference to the `idx`-th node of the per-thread store.
    #[inline]
    pub(crate) fn from_store_index(idx: usize) -> Self {
        let raw = u32::try_from(idx).expect("type store index exceeds u32::MAX");
        assert!(
            raw & SHARED_REF_BITS == 0,
            "type store index exceeds the tag range"
        );
        Self(raw | STORE_REF_TAG)
    }

    /// Reference to the `idx`-th node of the process-wide shared pool.
    #[inline]
    pub(crate) fn from_shared_index(idx: u32) -> Self {
        assert!(
            idx & SHARED_REF_BITS == 0,
            "shared type index exceeds the tag range"
        );
        Self(idx | SHARED_REF_BITS)
    }

    /// Whether this node lives outside the compilation (worker store or
    /// shared pool).
    #[inline]
    pub(crate) fn is_store(self) -> bool {
        self.0 & STORE_REF_TAG != 0
    }

    /// Whether this node lives in the process-wide shared pool.
    #[inline]
    pub(crate) fn is_shared(self) -> bool {
        self.0 & SHARED_REF_BITS == SHARED_REF_BITS
    }

    /// Index into the shared pool.
    #[inline]
    pub(crate) fn shared_index(self) -> u32 {
        debug_assert!(
            self.is_shared(),
            "non-shared type reference used as a shared index"
        );
        self.0 & !SHARED_REF_BITS
    }

    /// Index into the compilation-local arena.
    #[inline]
    pub(crate) fn index(self) -> usize {
        debug_assert!(
            !self.is_store(),
            "store type reference used as a local index"
        );
        self.0 as usize
    }

    /// Index into the per-thread store arena.
    #[inline]
    pub(crate) fn store_index(self) -> usize {
        debug_assert!(
            self.is_store() && !self.is_shared(),
            "local or shared type reference used as a store index"
        );
        (self.0 & !STORE_REF_TAG) as usize
    }

    /// Identity key for visited sets and side tables: unique across the local
    /// arena and the store, never an arena position.
    #[inline]
    pub(crate) fn key(self) -> usize {
        self.0 as usize
    }
}

/// Intentional Rust performance representation for short-lived type-node maps.
///
/// This preserves physical-identity semantics: the key is still the exact
/// `TypeExprRef`, matching the OCaml compiler's type-node identity model. The
/// reference node shape is compiler/ml/types.ml:22 and allocation path is
/// compiler/ml/btype.ml:46-48. The storage avoids hashing for short-lived
/// copy/substitution caches.
const TYPE_EXPR_MAP_INLINE_CAPACITY: usize = 8;
const TYPE_EXPR_MAP_DENSE_RATIO: usize = 8;
const TYPE_EXPR_MAP_MIN_SPARSE_SPAN: usize = 256;

#[derive(Debug, Clone)]
enum TypeExprRefMapStorage<T> {
    Inline {
        entries: [Option<(TypeExprRef, T)>; TYPE_EXPR_MAP_INLINE_CAPACITY],
        len: usize,
    },
    Dense {
        offset: u32,
        values: Vec<Option<T>>,
    },
    Sparse(crate::fast_hash::AHashMap<TypeExprRef, T>),
}

/// Identity-exact hybrid storage for short-lived type-copy maps.
///
/// Most record-label copies touch only a handful of far-apart arena handles,
/// while signature freshening touches hundreds of mostly dense handles. Keep
/// the common tiny case inline, then select dense or sparse storage from the
/// observed handle span. A later outlier can demote dense storage to sparse;
/// sufficiently dense sparse storage can promote once to direct indexing.
#[derive(Debug, Clone)]
pub(crate) struct TypeExprRefMap<T> {
    storage: TypeExprRefMapStorage<T>,
    entry_count: usize,
    min_key: Option<u32>,
    max_key: u32,
}

impl<T> TypeExprRefMap<T> {
    fn empty_inline() -> TypeExprRefMapStorage<T> {
        TypeExprRefMapStorage::Inline {
            entries: std::array::from_fn(|_| None),
            len: 0,
        }
    }

    pub(crate) fn new() -> Self {
        Self {
            storage: Self::empty_inline(),
            entry_count: 0,
            min_key: None,
            max_key: 0,
        }
    }

    #[inline]
    fn span(&self) -> usize {
        self.min_key
            .map_or(0, |min| ((self.max_key - min) as usize).saturating_add(1))
    }

    #[inline]
    fn record_new_key(&mut self, key: TypeExprRef) {
        match self.min_key {
            None => {
                self.min_key = Some(key.0);
                self.max_key = key.0;
            }
            Some(min) => {
                if key.0 < min {
                    self.min_key = Some(key.0);
                }
                self.max_key = self.max_key.max(key.0);
            }
        }
        self.entry_count += 1;
    }

    #[inline]
    pub(crate) fn get(&self, key: TypeExprRef) -> Option<&T> {
        match &self.storage {
            TypeExprRefMapStorage::Inline { entries, len } => {
                for entry in &entries[..*len] {
                    if let Some((stored, value)) = entry
                        && *stored == key
                    {
                        return Some(value);
                    }
                }
                None
            }
            TypeExprRefMapStorage::Dense { offset, values } => {
                let idx = key.0.checked_sub(*offset)? as usize;
                values.get(idx)?.as_ref()
            }
            TypeExprRefMapStorage::Sparse(values) => values.get(&key),
        }
    }

    fn dense_from_inline(
        entries: &mut [Option<(TypeExprRef, T)>; TYPE_EXPR_MAP_INLINE_CAPACITY],
        len: usize,
        min: u32,
        span: usize,
        key: TypeExprRef,
        value: T,
    ) -> TypeExprRefMapStorage<T> {
        let mut values = Vec::with_capacity(span);
        values.resize_with(span, || None);
        for entry in entries.iter_mut().take(len) {
            let (stored, stored_value) = entry.take().expect("occupied inline type-map slot");
            values[(stored.0 - min) as usize] = Some(stored_value);
        }
        values[(key.0 - min) as usize] = Some(value);
        TypeExprRefMapStorage::Dense {
            offset: min,
            values,
        }
    }

    fn sparse_from_inline(
        entries: &mut [Option<(TypeExprRef, T)>; TYPE_EXPR_MAP_INLINE_CAPACITY],
        len: usize,
        key: TypeExprRef,
        value: T,
    ) -> TypeExprRefMapStorage<T> {
        let mut values = crate::fast_hash::AHashMap::with_capacity(len + 1);
        for entry in entries.iter_mut().take(len) {
            let (stored, stored_value) = entry.take().expect("occupied inline type-map slot");
            values.insert(stored, stored_value);
        }
        values.insert(key, value);
        TypeExprRefMapStorage::Sparse(values)
    }

    #[inline]
    pub(crate) fn insert(&mut self, key: TypeExprRef, value: T) -> Option<T> {
        match &mut self.storage {
            TypeExprRefMapStorage::Inline { entries, len } => {
                for entry in entries.iter_mut().take(*len) {
                    let (stored, stored_value) =
                        entry.as_mut().expect("occupied inline type-map slot");
                    if *stored == key {
                        return Some(std::mem::replace(stored_value, value));
                    }
                }
                if *len < TYPE_EXPR_MAP_INLINE_CAPACITY {
                    entries[*len] = Some((key, value));
                    *len += 1;
                    self.record_new_key(key);
                    return None;
                }
            }
            TypeExprRefMapStorage::Dense { offset, values } => {
                if let Some(idx) = key.0.checked_sub(*offset).map(|idx| idx as usize)
                    && let Some(slot) = values.get_mut(idx)
                    && slot.is_some()
                {
                    return slot.replace(value);
                }
            }
            TypeExprRefMapStorage::Sparse(values) => {
                if let Some(stored) = values.get_mut(&key) {
                    return Some(std::mem::replace(stored, value));
                }
            }
        }

        self.record_new_key(key);
        let span = self.span();
        let entry_count = self.entry_count;

        match &mut self.storage {
            TypeExprRefMapStorage::Inline { .. } => {
                let mut old = std::mem::replace(&mut self.storage, Self::empty_inline());
                let TypeExprRefMapStorage::Inline { entries, len } = &mut old else {
                    unreachable!();
                };
                let min = self.min_key.expect("nonempty type-map bounds");
                if span <= entry_count.saturating_mul(TYPE_EXPR_MAP_DENSE_RATIO) {
                    self.storage = Self::dense_from_inline(entries, *len, min, span, key, value);
                } else {
                    self.storage = Self::sparse_from_inline(entries, *len, key, value);
                }
            }
            TypeExprRefMapStorage::Dense { offset, values } => {
                if span > TYPE_EXPR_MAP_MIN_SPARSE_SPAN
                    && span > entry_count.saturating_mul(TYPE_EXPR_MAP_DENSE_RATIO)
                {
                    let mut sparse = crate::fast_hash::AHashMap::with_capacity(entry_count);
                    for (idx, slot) in values.iter_mut().enumerate() {
                        if let Some(stored_value) = slot.take() {
                            sparse.insert(TypeExprRef(*offset + idx as u32), stored_value);
                        }
                    }
                    sparse.insert(key, value);
                    self.storage = TypeExprRefMapStorage::Sparse(sparse);
                } else {
                    let min = self.min_key.expect("nonempty type-map bounds");
                    if min < *offset {
                        let prepend = (*offset - min) as usize;
                        let mut copied = Vec::with_capacity(values.len() + prepend);
                        copied.resize_with(prepend, || None);
                        copied.append(values);
                        *values = copied;
                        *offset = min;
                    }
                    let idx = (key.0 - *offset) as usize;
                    if idx >= values.len() {
                        values.resize_with(idx + 1, || None);
                    }
                    values[idx] = Some(value);
                }
            }
            TypeExprRefMapStorage::Sparse(values) => {
                values.insert(key, value);
                if entry_count >= 32 && span <= entry_count.saturating_mul(4) {
                    let min = self.min_key.expect("nonempty type-map bounds");
                    let mut dense = Vec::with_capacity(span);
                    dense.resize_with(span, || None);
                    for (stored, stored_value) in values.drain() {
                        dense[(stored.0 - min) as usize] = Some(stored_value);
                    }
                    self.storage = TypeExprRefMapStorage::Dense {
                        offset: min,
                        values: dense,
                    };
                }
            }
        }
        None
    }
}

impl<T> Default for TypeExprRefMap<T> {
    fn default() -> Self {
        Self::new()
    }
}

/// Number of keys a `TypeExprRefSet` holds inline before it spills to a
/// hash set.
const TYPE_EXPR_SET_INLINE: usize = 16;

/// Multiplicative hash for `TypeExprRef` keys (arena indices).
#[derive(Default, Clone, Copy)]
struct TypeKeyHasher(u64);

impl Hasher for TypeKeyHasher {
    #[inline]
    fn finish(&self) -> u64 {
        self.0
    }

    #[inline]
    fn write(&mut self, bytes: &[u8]) {
        for &b in bytes {
            self.0 = (self.0.rotate_left(8) ^ u64::from(b)).wrapping_mul(0x9E37_79B9_7F4A_7C15);
        }
    }

    #[inline]
    fn write_u32(&mut self, n: u32) {
        self.0 = u64::from(n).wrapping_mul(0x9E37_79B9_7F4A_7C15);
    }
}

type TypeKeySet = std::collections::HashSet<u32, std::hash::BuildHasherDefault<TypeKeyHasher>>;

#[derive(Debug, Clone)]
pub(crate) struct TypeExprRefSet {
    /// Most traversals visit only a few nodes; keep those keys inline so the
    /// set allocates nothing.
    inline: [u32; TYPE_EXPR_SET_INLINE],
    inline_len: u8,
    /// Keys once the inline storage is full; storage comes from a per-thread
    /// pool so large traversals reuse capacity.
    spilled: Option<TypeKeySet>,
}

thread_local! {
    /// Cleared hash sets of dropped spilled `TypeExprRefSet`s.
    static SPILLED_SET_POOL: std::cell::RefCell<Vec<TypeKeySet>> = const { std::cell::RefCell::new(Vec::new()) };
}

const SPILLED_SET_POOL_MAX: usize = 8;
const SPILLED_SET_POOL_MAX_CAPACITY: usize = 1 << 16;

impl TypeExprRefSet {
    pub(crate) fn new() -> Self {
        Self {
            inline: [0; TYPE_EXPR_SET_INLINE],
            inline_len: 0,
            spilled: None,
        }
    }

    #[inline]
    pub(crate) fn insert(&mut self, key: TypeExprRef) -> bool {
        if let Some(spilled) = self.spilled.as_mut() {
            return spilled.insert(key.0);
        }
        let len = self.inline_len as usize;
        if self.inline[..len].contains(&key.0) {
            return false;
        }
        if len < TYPE_EXPR_SET_INLINE {
            self.inline[len] = key.0;
            self.inline_len += 1;
            return true;
        }
        self.spill().insert(key.0)
    }

    #[cold]
    fn spill(&mut self) -> &mut TypeKeySet {
        let mut set = SPILLED_SET_POOL
            .with(|pool| pool.borrow_mut().pop())
            .unwrap_or_default();
        set.extend(self.inline[..self.inline_len as usize].iter().copied());
        self.spilled.insert(set)
    }
}

impl Drop for TypeExprRefSet {
    fn drop(&mut self) {
        if let Some(mut set) = self.spilled.take() {
            if set.capacity() > SPILLED_SET_POOL_MAX_CAPACITY {
                return;
            }
            set.clear();
            SPILLED_SET_POOL.with(|pool| {
                let mut pool = pool.borrow_mut();
                if pool.len() < SPILLED_SET_POOL_MAX {
                    pool.push(set);
                }
            });
        }
    }
}

impl Default for TypeExprRefSet {
    fn default() -> Self {
        Self::new()
    }
}

/// The label of an arrow parameter, as stored in type descriptors.
///
/// Intentional Rust performance representation of `Asttypes.arg_label`
/// (`compiler/ml/asttypes.ml`) inside `Types.Tarrow` (`compiler/ml/types.ml:24`):
/// the name is interned and the location is a [`DeclLoc`] handle, so the
/// label is `Copy`. [`TypeArgLabel::to_arg_label`] gives the owned
/// [`ArgLabel`] with the same text and location.
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct TypeArgLabel {
    /// `None` for `Nolabel`.
    name: Option<crate::name::Name>,
    optional: bool,
    loc: DeclLoc,
}

impl TypeArgLabel {
    /// `Nolabel`.
    pub const NOLABEL: Self = TypeArgLabel {
        name: None,
        optional: false,
        loc: DeclLoc::none(),
    };

    /// The compact form of `label`.
    pub fn new(label: &ArgLabel) -> Self {
        match label {
            ArgLabel::Nolabel => Self::NOLABEL,
            ArgLabel::Labelled(l) => TypeArgLabel {
                name: Some(crate::name::Name::new(&l.txt)),
                optional: false,
                loc: l.loc,
            },
            ArgLabel::Optional(l) => TypeArgLabel {
                name: Some(crate::name::Name::new(&l.txt)),
                optional: true,
                loc: l.loc,
            },
        }
    }

    /// The owned label (same text and location).
    pub fn to_arg_label(self) -> ArgLabel {
        match self.name {
            None => ArgLabel::Nolabel,
            Some(name) if self.optional => ArgLabel::optional(name.as_str(), self.loc),
            Some(name) => ArgLabel::labelled(name.as_str(), self.loc),
        }
    }

    /// The label name, `None` for `Nolabel` (`ArgLabel::label_name`).
    #[inline]
    pub fn label_name(self) -> Option<&'static str> {
        self.name.map(|name| name.as_str())
    }

    /// Whether this is `Nolabel`.
    #[inline]
    pub fn is_nolabel(self) -> bool {
        self.name.is_none()
    }

    /// Whether this is an `Optional` label.
    #[inline]
    pub fn is_optional(self) -> bool {
        self.optional
    }

    /// Whether this is a `Labelled` label.
    #[inline]
    pub fn is_labelled(self) -> bool {
        self.name.is_some() && !self.optional
    }

    /// The label's location (`DeclLoc::none()` for `Nolabel`).
    #[inline]
    pub fn loc(self) -> DeclLoc {
        self.loc
    }

    /// `ArgLabel::same_label`: same kind and name.
    #[inline]
    pub fn same_label(self, other: TypeArgLabel) -> bool {
        self.name == other.name && self.optional == other.optional
    }
}

/// The constructor of an [`ArgLabel`], for matching on a [`TypeArgLabel`].
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ArgLabelKind {
    Nolabel,
    Labelled,
    Optional,
}

impl TypeArgLabel {
    /// The label's constructor.
    #[inline]
    pub fn to_kind(self) -> ArgLabelKind {
        match (self.name, self.optional) {
            (None, _) => ArgLabelKind::Nolabel,
            (Some(_), false) => ArgLabelKind::Labelled,
            (Some(_), true) => ArgLabelKind::Optional,
        }
    }
}

impl std::fmt::Debug for TypeArgLabel {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Debug::fmt(&self.to_arg_label(), f)
    }
}

/// An argument in a function type.
///
/// OCaml types.ml:24 and btype.ml:422-423 preserve labels while mapping types.
///
/// The label's fields are stored flat (see [`TypeArgLabel`]) so the
/// parameter packs into 24 bytes.
#[derive(Clone, Copy)]
pub struct TypeArg {
    name: Option<crate::name::Name>,
    loc: DeclLoc,
    /// The argument type (physical arena identity).
    pub typ: TypeExprRef,
    optional: bool,
}

impl std::fmt::Debug for TypeArg {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("TypeArg")
            .field("lbl", &self.label())
            .field("typ", &self.typ)
            .finish()
    }
}

impl TypeArg {
    /// Create a new type argument.
    pub fn new(lbl: ArgLabel, typ: TypeExprRef) -> Self {
        Self::with_label(TypeArgLabel::new(&lbl), typ)
    }

    /// Keep the compact label when changing a parameter's type.
    pub fn with_type(&self, typ: TypeExprRef) -> Self {
        Self { typ, ..*self }
    }

    /// Create a new type argument from a compact label.
    #[inline]
    pub fn with_label(label: TypeArgLabel, typ: TypeExprRef) -> Self {
        Self {
            name: label.name,
            loc: label.loc,
            typ,
            optional: label.optional,
        }
    }

    /// The parameter's label.
    #[inline]
    pub fn label(&self) -> TypeArgLabel {
        TypeArgLabel {
            name: self.name,
            optional: self.optional,
            loc: self.loc,
        }
    }

    /// Create an unlabeled argument.
    pub fn unlabeled(typ: TypeExprRef) -> Self {
        Self::with_label(TypeArgLabel::NOLABEL, typ)
    }
}

/// Abbreviation memo for type expansion caching.
#[derive(Debug, Clone)]
pub enum AbbrevMemo {
    /// No abbreviation
    Mnil,
    /// Abbreviation: (private_flag, path, abbrev, expansion, next)
    Mcons {
        private_flag: PrivateFlag,
        path: Path,
        abbrev: TypeExprRef,
        expansion: TypeExprRef,
        next: AbbrevMemoRef,
    },
    /// Link to another memo
    Mlink(AbbrevMemoRef),
}

/// Reference to an abbreviation memo.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct AbbrevMemoRef(pub u32);

impl AbbrevMemoRef {
    /// Create a nil memo reference.
    pub fn nil() -> Self {
        AbbrevMemoRef(0)
    }

    #[inline]
    pub(crate) fn from_usize(idx: usize) -> Self {
        let raw = u32::try_from(idx).expect("abbrev memo arena index exceeds u32::MAX");
        assert!(
            raw & STORE_REF_TAG == 0,
            "local abbrev memo index collides with the store tag"
        );
        Self(raw)
    }

    /// Reference to the `idx`-th abbreviation memo cell of the per-thread store.
    #[inline]
    pub(crate) fn from_store_index(idx: usize) -> Self {
        let raw = u32::try_from(idx).expect("abbrev memo store index exceeds u32::MAX");
        assert!(
            raw & SHARED_REF_BITS == 0,
            "abbrev memo store index exceeds the tag range"
        );
        Self(raw | STORE_REF_TAG)
    }

    /// Memo cell of the shared-pool `Tconstr` node with index `idx`; one cell
    /// per node, initially `Mnil` (`compiler/ml/subst.ml:173-177`).
    #[inline]
    pub(crate) fn from_shared_index(idx: u32) -> Self {
        assert!(
            idx & SHARED_REF_BITS == 0,
            "shared abbrev memo index exceeds the tag range"
        );
        Self(idx | SHARED_REF_BITS)
    }

    #[inline]
    pub(crate) fn is_shared(self) -> bool {
        self.0 & SHARED_REF_BITS == SHARED_REF_BITS
    }

    #[inline]
    pub(crate) fn shared_index(self) -> usize {
        debug_assert!(self.is_shared());
        (self.0 & !SHARED_REF_BITS) as usize
    }

    /// Whether this memo cell belongs to a per-thread store node.
    #[inline]
    pub(crate) fn is_store(self) -> bool {
        self.0 & STORE_REF_TAG != 0
    }

    #[inline]
    pub(crate) fn index(self) -> usize {
        debug_assert!(!self.is_store(), "store abbrev memo used as a local index");
        self.0 as usize
    }

    #[inline]
    pub(crate) fn store_index(self) -> usize {
        debug_assert!(
            self.is_store() && !self.is_shared(),
            "local or shared abbrev memo used as a store index"
        );
        (self.0 & !STORE_REF_TAG) as usize
    }
}

/// Assignment capability of an object field (types.ml `field_mutability`).
///
/// The semantic value is `Immutable` or `Mutable`; `Link` is an internal edge
/// between cells of the same class, not a third value. Code making a semantic
/// decision must use `TypeContext::mutability_repr`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum FieldMutability {
    Value(super::asttypes::MutableFlag),
    Link(MutabilityRef),
}

/// A `field_mutability ref` cell.
///
/// Cells of the compilation's own graph index its cell arena. Cells of
/// dependency graphs (worker store and shared pool) are persistent: they are
/// never written in place, carry a process-unique identity, and encode their
/// initial value (saved graphs only hold `Mutability_value` cells,
/// subst.ml `for_saving`); a compilation's writes to them go to its overlay.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct MutabilityRef(pub u32);

/// Next persistent cell identity, process-wide.
static NEXT_PERSISTENT_MUTABILITY: std::sync::atomic::AtomicU32 =
    std::sync::atomic::AtomicU32::new(0);

impl MutabilityRef {
    #[inline]
    pub(crate) fn from_usize(idx: usize) -> Self {
        let raw = u32::try_from(idx).expect("mutability cell index exceeds u32::MAX");
        assert!(
            raw & STORE_REF_TAG == 0,
            "local mutability cell index collides with the persistent tag"
        );
        Self(raw)
    }

    /// A fresh persistent cell holding `flag`.
    pub(crate) fn new_persistent(flag: super::asttypes::MutableFlag) -> Self {
        let id = NEXT_PERSISTENT_MUTABILITY.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        assert!(id < (1 << 30), "persistent mutability cells exhausted");
        let bit = match flag {
            super::asttypes::MutableFlag::Immutable => 0,
            super::asttypes::MutableFlag::Mutable => 1,
        };
        Self(STORE_REF_TAG | (id << 1) | bit)
    }

    #[inline]
    pub fn is_persistent(self) -> bool {
        self.0 & STORE_REF_TAG != 0
    }

    #[inline]
    pub(crate) fn index(self) -> usize {
        debug_assert!(!self.is_persistent());
        self.0 as usize
    }

    /// The initial value of a persistent cell.
    #[inline]
    pub(crate) fn persistent_value(self) -> super::asttypes::MutableFlag {
        debug_assert!(self.is_persistent());
        if self.0 & 1 != 0 {
            super::asttypes::MutableFlag::Mutable
        } else {
            super::asttypes::MutableFlag::Immutable
        }
    }
}

/// Row description for polymorphic variants.
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct RowDesc {
    /// The variant fields: (label, row_field). Shared copy-on-write, so
    /// snapshots of variant descriptors do not copy the field list.
    pub row_fields: super::decl::SharedVec<(Label, RowField)>,
    /// The row variable
    pub row_more: TypeExprRef,
    /// Is the row closed?
    pub row_closed: bool,
    /// Is the row fixed?
    pub row_fixed: bool,
    /// Optional row name
    pub row_name: Option<(Path, Vec<TypeExprRef>)>,
}

/// Row field for polymorphic variants.
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub enum RowField {
    /// Present variant: Some(type) for valued, None for constant
    Rpresent(Option<TypeExprRef>),
    /// Either variant (during type inference)
    Reither {
        /// Is this a constant constructor?
        constant: bool,
        /// Possible types
        types: Vec<TypeExprRef>,
        /// Is this a pattern match tag?
        matched: bool,
        /// Link to resolved field
        link: RowFieldRef,
    },
    /// Absent variant
    Rabsent,
}

/// Reference to a row field.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub struct RowFieldRef(pub u32);

impl RowFieldRef {
    /// Create a null reference.
    pub fn null() -> Self {
        RowFieldRef(u32::MAX)
    }

    /// Check if this is a null reference.
    pub fn is_null(&self) -> bool {
        self.0 == u32::MAX
    }

    #[inline]
    pub(crate) fn from_usize(idx: usize) -> Self {
        let raw = u32::try_from(idx).expect("row field arena index exceeds u32::MAX");
        assert!(
            raw & STORE_REF_TAG == 0,
            "local row field index collides with the store tag"
        );
        Self(raw)
    }

    /// Reference to the `idx`-th row field cell of the per-thread store.
    #[inline]
    pub(crate) fn from_store_index(idx: usize) -> Self {
        let raw = u32::try_from(idx).expect("row field store index exceeds u32::MAX");
        assert!(
            raw < STORE_REF_TAG - 1,
            "row field store index collides with null sentinel"
        );
        assert!(
            raw & STORE_REF_TAG == 0,
            "row field store index exceeds the tag range"
        );
        Self(raw | STORE_REF_TAG)
    }

    /// Whether this cell belongs to a per-thread store row. The null
    /// sentinel also has the top bit set and is excluded.
    #[inline]
    pub(crate) fn is_store(self) -> bool {
        self.0 & STORE_REF_TAG != 0 && !self.is_null()
    }

    #[inline]
    pub(crate) fn index(self) -> usize {
        debug_assert!(!self.is_store(), "store row field used as a local index");
        self.0 as usize
    }

    #[inline]
    pub(crate) fn store_index(self) -> usize {
        debug_assert!(self.is_store(), "local row field used as a store index");
        (self.0 & !STORE_REF_TAG) as usize
    }
}

#[cfg(test)]
mod tests {
    use super::*;



    #[test]
    fn compact_type_node_sizes() {
        use std::mem::size_of;
        assert_eq!(size_of::<crate::ident::Ident>(), 16);
        assert_eq!(size_of::<Path>(), 8);
        assert_eq!(size_of::<TypeRefList>(), 8);
        assert_eq!(size_of::<TypeDesc>(), 24);
        assert_eq!(size_of::<TypeExpr>(), 40);
    }

    #[test]
    fn store_tags_preserve_identity_and_sentinels() {
        for index in [0, 1, 255, 256, 10_000] {
            let local = TypeExprRef::from_usize(index);
            let store = TypeExprRef::from_store_index(index);
            assert!(!local.is_store());
            assert!(store.is_store());
            assert_eq!(local.index(), index);
            assert_eq!(store.store_index(), index);
            assert_ne!(local, store);
            assert_eq!(AbbrevMemoRef::from_store_index(index).store_index(), index);
            assert_eq!(RowFieldRef::from_store_index(index).store_index(), index);
        }
        assert!(!RowFieldRef::null().is_store());
        assert!(!RowFieldRef::from_store_index(0).is_null());
        assert_ne!(AbbrevMemoRef::nil(), AbbrevMemoRef::from_store_index(0));
        assert_eq!(std::mem::size_of::<TypeExprRef>(), 4);
    }

    #[test]
    #[should_panic(expected = "collides with the store tag")]
    fn local_index_cannot_use_store_bit() {
        TypeExprRef::from_usize(STORE_REF_TAG as usize);
    }

    #[test]
    #[should_panic(expected = "null sentinel")]
    fn store_row_index_cannot_use_null_sentinel() {
        RowFieldRef::from_store_index((STORE_REF_TAG - 1) as usize);
    }

    #[test]
    fn mixed_store_local_maps_and_sets_stay_small() {
        for store_first in [false, true] {
            let mut map = TypeExprRefMap::new();
            let mut set = TypeExprRefSet::new();
            for store in [store_first, !store_first] {
                for index in 0..40 {
                    let key = if store {
                        TypeExprRef::from_store_index(index)
                    } else {
                        TypeExprRef::from_usize(index)
                    };
                    assert!(set.insert(key));
                    assert!(!set.insert(key));
                    assert_eq!(map.insert(key, store), None);
                }
            }
            for index in 0..40 {
                assert_eq!(map.get(TypeExprRef::from_store_index(index)), Some(&true));
                assert_eq!(map.get(TypeExprRef::from_usize(index)), Some(&false));
            }
            assert!(matches!(map.storage, TypeExprRefMapStorage::Sparse(_)));
            assert_eq!(set.spilled.as_ref().unwrap().len(), 80);
        }
    }

    #[test]
    fn test_type_expr_creation() {
        let ty = TypeExpr::new(
            TypeDesc::Tvar(Some(crate::name::Name::new("a"))),
            GENERIC_LEVEL,
            1,
        );
        assert_eq!(ty.id(), 1);
        assert_eq!(ty.level(), GENERIC_LEVEL);
        assert!(matches!(*ty.desc.borrow(), TypeDesc::Tvar(..)));
    }

    #[test]
    fn test_type_expr_mutation() {
        let ty = TypeExpr::new(
            TypeDesc::Tvar(None),
            0,
            1,
        );
        ty.set_level(GENERIC_LEVEL);
        assert_eq!(ty.level(), GENERIC_LEVEL);

        ty.set_desc(TypeDesc::Tnil);
        assert!(matches!(*ty.desc(), TypeDesc::Tnil));
    }

    #[test]
    fn test_type_expr_equality() {
        let ty1 = TypeExpr::new(
            TypeDesc::Tvar(None),
            0,
            1,
        );
        let ty2 = TypeExpr::new(
            TypeDesc::Tvar(None),
            0,
            1,
        );
        let ty3 = TypeExpr::new(
            TypeDesc::Tvar(None),
            0,
            2,
        );

        assert_eq!(ty1, ty2); // Same id
        assert_ne!(ty1, ty3); // Different id
    }

    #[test]
    fn test_type_arg() {
        let arg = TypeArg::unlabeled(TypeExprRef(1));
        assert!(arg.label().is_nolabel());
        assert!(matches!(arg.label().to_arg_label(), ArgLabel::Nolabel));
        assert_eq!(arg.typ, TypeExprRef(1));
    }

    #[test]
    fn type_arg_labels_round_trip() {
        use crate::intern::StrIdx;
        use crate::location::{Location, Position};
        if cfg!(target_pointer_width = "64") {
            assert_eq!(std::mem::size_of::<TypeArg>(), 24);
        }
        let typ = TypeExprRef(u32::MAX);
        for arg in [
            TypeArg::unlabeled(typ),
            TypeArg::new(ArgLabel::Nolabel, typ),
        ] {
            assert!(arg.label().is_nolabel());
            assert_eq!(arg.label().to_kind(), ArgLabelKind::Nolabel);
            assert_eq!(arg.typ, typ);
            assert_eq!(
                format!("{:?}", arg),
                format!("TypeArg {{ lbl: Nolabel, typ: {:?} }}", typ)
            );
        }
        let ctx =
            crate::types::TypeContext::new(std::sync::Arc::new(crate::context::IdGenerator::new()));
        for ghost in [false, true] {
            let loc = Location {
                loc_start: Position::new(StrIdx(17), 3, 21, 24),
                loc_end: Position::new(StrIdx(29), 5, 44, 49),
                loc_ghost: ghost,
                origin: Default::default(),
            };
            for optional in [false, true] {
                let name = "long_owned_label_with_unicode_λ";
                let label = if optional {
                    ArgLabel::optional(name, ctx.intern_loc(loc))
                } else {
                    ArgLabel::labelled(name, ctx.intern_loc(loc))
                };
                let expected_debug = format!("TypeArg {{ lbl: {:?}, typ: {:?} }}", label, typ);
                let arg = TypeArg::new(label.clone(), typ);
                assert_eq!(format!("{:?}", arg), expected_debug);
                assert_eq!(arg.label().to_arg_label(), label);
                assert_eq!(arg.label().is_optional(), optional);
                assert_eq!(arg.label().label_name(), Some(name));
                assert!(arg.label().same_label(TypeArgLabel::new(&label)));
                assert!(!arg.label().same_label(TypeArgLabel::NOLABEL));
                let resolved = ctx.resolve_loc(arg.label().loc());
                assert_eq!(resolved.loc_start.file_name, StrIdx(17));
                assert_eq!(resolved.loc_start.line, 3);
                assert_eq!(resolved.loc_start.bol, 21);
                assert_eq!(resolved.loc_start.cnum, 24);
                assert_eq!(resolved.loc_end.file_name, StrIdx(29));
                assert_eq!(resolved.loc_end.line, 5);
                assert_eq!(resolved.loc_end.bol, 44);
                assert_eq!(resolved.loc_end.cnum, 49);
                assert_eq!(resolved.loc_ghost, ghost);
            }
        }
    }

    #[test]
    fn type_expr_ref_map_preserves_replace_and_clone_semantics() {
        let mut map = TypeExprRefMap::new();
        assert_eq!(map.insert(TypeExprRef(42), 1), None);
        assert_eq!(map.insert(TypeExprRef(42), 2), Some(1));
        assert_eq!(map.get(TypeExprRef(42)), Some(&2));

        let cloned = map.clone();
        assert_eq!(cloned.get(TypeExprRef(42)), Some(&2));
        assert_eq!(cloned.entry_count, 1);
    }

    #[test]
    fn type_expr_ref_map_keeps_far_apart_small_maps_sparse() {
        let mut map = TypeExprRefMap::new();
        for index in 0..12 {
            let key = TypeExprRef(index * 10_000);
            assert_eq!(map.insert(key, index), None);
        }
        for index in 0..12 {
            assert_eq!(map.get(TypeExprRef(index * 10_000)), Some(&index));
        }
        assert_eq!(map.entry_count, 12);
        assert_eq!(map.span(), 110_001);
        let TypeExprRefMapStorage::Sparse(values) = &map.storage else {
            panic!("expected sparse storage");
        };
        assert!(values.capacity() < map.span());
    }

    #[test]
    fn type_expr_ref_map_promotes_dense_runs_and_demotes_for_outliers() {
        let mut map = TypeExprRefMap::new();
        for index in 100..140 {
            assert_eq!(map.insert(TypeExprRef(index), index), None);
        }
        assert!(matches!(&map.storage, TypeExprRefMapStorage::Dense { .. }));
        assert_eq!(map.get(TypeExprRef(123)), Some(&123));

        assert_eq!(map.insert(TypeExprRef(100_000), 100_000), None);
        assert_eq!(map.entry_count, 41);
        assert!(matches!(&map.storage, TypeExprRefMapStorage::Sparse(_)));
        assert_eq!(map.get(TypeExprRef(100)), Some(&100));
        assert_eq!(map.get(TypeExprRef(100_000)), Some(&100_000));
    }

    #[test]
    fn type_expr_ref_map_matches_std_map_across_mixed_transitions() {
        let mut map = TypeExprRefMap::new();
        let mut expected = std::collections::HashMap::new();
        let mut state = 0x9e37_79b9_u32;

        for step in 0..5_000_u32 {
            state = state.wrapping_mul(1_664_525).wrapping_add(1_013_904_223);
            let key = match step % 4 {
                0 => state % 128,
                1 => 100_000 + state % 256,
                2 => 1_000_000 - state % 512,
                _ => state % 1_000_000,
            };
            let value = state ^ step;
            assert_eq!(
                map.insert(TypeExprRef(key), value),
                expected.insert(key, value)
            );

            let probe = state.rotate_left(11) % 1_000_256;
            assert_eq!(map.get(TypeExprRef(probe)), expected.get(&probe));
            assert_eq!(map.get(TypeExprRef(key)), expected.get(&key));

            if step % 317 == 0 {
                let cloned = map.clone();
                for (&stored, value) in &expected {
                    assert_eq!(cloned.get(TypeExprRef(stored)), Some(value));
                }
            }
        }
        assert_eq!(map.entry_count, expected.len());
    }

    #[test]
    fn type_expr_ref_map_bounds_and_sparse_promotion() {
        let mut map = TypeExprRefMap::new();
        for key in [0, u32::MAX, 1, u32::MAX - 1, 2, 3, 4, 5, 6] {
            assert_eq!(map.insert(TypeExprRef(key), key), None);
            assert_eq!(map.get(TypeExprRef(key)), Some(&key));
        }
        assert!(matches!(map.storage, TypeExprRefMapStorage::Sparse(_)));
        assert_eq!(map.get(TypeExprRef(u32::MAX - 2)), None);
        // Reset/reuse is assignment in the current API; there is no clear method.
        map = TypeExprRefMap::default();
        for key in (100..109).rev() {
            map.insert(TypeExprRef(key), key);
        }
        assert!(matches!(map.storage, TypeExprRefMapStorage::Dense { .. }));
        map.insert(TypeExprRef(99), 99);
        assert_eq!(map.get(TypeExprRef(98)), None);
        assert_eq!(map.get(TypeExprRef(110)), None);
        map.insert(TypeExprRef(300), 300);
        assert!(matches!(map.storage, TypeExprRefMapStorage::Dense { .. }));
        map.insert(TypeExprRef(400), 400);
        assert!(matches!(map.storage, TypeExprRefMapStorage::Sparse(_)));
        for key in 99..401 {
            map.insert(TypeExprRef(key), key);
        }
        assert!(matches!(map.storage, TypeExprRefMapStorage::Dense { .. }));
        let mut cloned = map.clone();
        cloned.insert(TypeExprRef(99), 0);
        for key in 99..401 {
            assert_eq!(map.get(TypeExprRef(key)), Some(&key));
        }
    }

    #[test]
    fn type_expr_ref_map_drops_owned_values_once() {
        struct Owned<'a>(&'a std::cell::Cell<usize>);
        impl Drop for Owned<'_> {
            fn drop(&mut self) {
                self.0.set(self.0.get() + 1);
            }
        }
        let drops = std::cell::Cell::new(0);
        let mut map = TypeExprRefMap::new();
        for key in 100..140 {
            map.insert(TypeExprRef(key), Owned(&drops));
        }
        map.insert(TypeExprRef(500), Owned(&drops));
        for key in 140..500 {
            map.insert(TypeExprRef(key), Owned(&drops));
        }
        assert_eq!(drops.get(), 0);
        let old = map.insert(TypeExprRef(100), Owned(&drops));
        assert_eq!(drops.get(), 0);
        drop(old);
        assert_eq!(drops.get(), 1);
        drop(map);
        assert_eq!(drops.get(), 402);
    }

    #[test]
    fn type_expr_ref_map_copy_fixture_preserves_cycles_and_identity() {
        use crate::context::IdGenerator;
        use crate::types::{
            TypeContext,
            decl::{ValueDescription, ValueKind},
        };
        let ctx = TypeContext::new(std::sync::Arc::new(IdGenerator::new()));
        let shared = ctx.new_var(None);
        let distinct = ctx.new_var(None);
        let cycle = ctx.new_var(None);
        let mut items = vec![shared, shared, distinct, cycle];
        // Force widely separated physical keys without allocating a huge arena.
        for _ in 0..12 {
            for _ in 0..300 {
                ctx.new_var(None);
            }
            items.push(ctx.new_var(None));
        }
        ctx.set_desc(cycle, TypeDesc::Ttuple(ctx.new_type_list(&items)));
        let value = ValueDescription {
            val_type: cycle,
            val_kind: ValueKind::ValReg,
            val_loc: crate::types::DeclLoc::none(),
            val_attributes: vec![],
            val_path: None,
        };
        let copied = crate::types::typecore::copy_lookup_value_description_for_subst(&value, &ctx);
        assert_ne!(copied.val_type, cycle);
        let desc = ctx.get_desc(copied.val_type);
        let TypeDesc::Ttuple(actual) = &*desc else {
            panic!("tuple expected")
        };
        let actual = ctx.type_list(actual).to_vec();
        assert_eq!(actual[0], shared);
        assert_eq!(actual[1], shared);
        assert_eq!(actual[2], distinct);
        assert_ne!(actual[0], actual[2]);
        assert_eq!(actual[3], copied.val_type);
        assert_eq!(&actual[4..], &items[4..]);
    }

    #[test]
    fn test_row_desc() {
        let row = RowDesc {
            row_fields: vec![].into(),
            row_more: TypeExprRef(1),
            row_closed: true,
            row_fixed: false,
            row_name: None,
        };
        assert!(row.row_closed);
        assert!(!row.row_fixed);
    }
}

impl<'a, T: Copy> From<&'a [T]> for PoolSlice<'a, T> {
    #[inline]
    fn from(items: &'a [T]) -> Self {
        PoolSlice::Plain(items)
    }
}

impl<'a, T: Copy> From<&'a Vec<T>> for PoolSlice<'a, T> {
    #[inline]
    fn from(items: &'a Vec<T>) -> Self {
        PoolSlice::Plain(items)
    }
}

impl<'a, T: Copy, const N: usize> From<&'a smallvec::SmallVec<[T; N]>> for PoolSlice<'a, T> {
    #[inline]
    fn from(items: &'a smallvec::SmallVec<[T; N]>) -> Self {
        PoolSlice::Plain(items)
    }
}
