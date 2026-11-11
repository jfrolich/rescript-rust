//! Module paths for the type system.
//!
//! This module provides the `Path` type, which represents qualified names
//! in the type system. Unlike `Longident` which is for parsing, `Path` uses
//! `Ident` with stamps for unique identification.
//!
//! # Example
//!
//! ```rust
//! use rescript_compiler::ident::Ident;
//! use rescript_compiler::types::Path;
//!
//! // A simple identifier path
//! let id = Ident::create_persistent("String");
//! let path = Path::pident(id);
//!
//! // A dotted path: Array.t
//! let array_id = Ident::create_persistent("Array");
//! let array_t = Path::pdot(Path::pident(array_id), "t");
//!
//! assert_eq!(array_t.name(), "Array.t");
//! ```

use crate::ident::Ident;
use crate::name::Name;
use serde::{Deserialize, Deserializer, Serialize, Serializer};
use std::cell::Cell;
use std::fmt;
use std::sync::{LazyLock, Mutex};

/// A module path in the type system (OCaml `Path.t`).
///
/// Paths are used to refer to types, modules, and values throughout
/// the type checker. Unlike `Longident`, they use `Ident` with stamps
/// for unique identification.
///
/// Intentional Rust performance representation of `compiler/ml/path.ml:18-21`:
/// paths are hash-consed process-wide (like [`Name`]), so a `Path` is one
/// `Copy` pointer to an immutable, never-freed node. Structurally identical
/// paths are the same node, and every node points at the representative of
/// its `Path.same` class (`compiler/ml/path.ml:23-29`: identifiers compared
/// with `Ident.same`, `Pdot` positions ignored), so `same` is one pointer
/// comparison and hashing reads a precomputed word. The set of distinct
/// paths in a build is small (a few hundred thousand on large projects).
/// Match on [`Path::view`] to inspect the constructor.
#[derive(Clone, Copy)]
pub struct Path(&'static PathNode);

/// [`Path::flatten`] failed: the path contains a functor application
/// (`Papply`), so it has no single head identifier and component list.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ContainsApply;

/// The constructor of a [`Path`], for pattern matching.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum PathView {
    /// A simple identifier: `String`, `int`
    Pident(Ident),
    /// A dotted access: `Array.t` is `Pdot(Pident(Array), "t", -1)`
    /// The integer is a position hint (usually -1 for no hint).
    Pdot(Path, Name, i32),
    /// Functor application: `F(X)` is `Papply(F, X)`
    Papply(Path, Path),
}

struct PathNode {
    view: PathView,
    /// Representative of this node's `Path.same` class; `None` when the node
    /// is the representative.
    same: Option<&'static PathNode>,
    /// Hash of the exact structure (identifier flags and positions included).
    node_hash: u64,
    /// Hash of the `Path.same` class: equal for `same` paths.
    same_hash: u64,
}

impl PathNode {
    #[inline]
    fn class(&'static self) -> &'static PathNode {
        self.same.unwrap_or(self)
    }
}

#[inline]
fn mix(a: u64, b: u64) -> u64 {
    // wyhash-style folded multiply: fixed constants, so hashes (and every
    // table keyed by them) are the same from run to run.
    let full = u128::from(a ^ 0xa076_1d64_78bd_642f) * u128::from(b ^ 0xe703_7ed1_a0b4_28db);
    (full as u64) ^ ((full >> 64) as u64)
}

fn node_hash(view: &PathView) -> u64 {
    match *view {
        PathView::Pident(id) => mix(
            mix(1, id.name_atom().content_hash()),
            (u64::from(id.stamp() as u32) << 8) | u64::from(id.flags().bits()),
        ),
        PathView::Pdot(parent, name, pos) => mix(
            mix(2, parent.0.node_hash),
            mix(name.content_hash(), u64::from(pos as u32)),
        ),
        PathView::Papply(functor, arg) => mix(mix(3, functor.0.node_hash), arg.0.node_hash),
    }
}

fn same_hash(view: &PathView) -> u64 {
    match *view {
        PathView::Pident(id) => {
            if id.stamp() != 0 {
                mix(4, u64::from(id.stamp() as u32))
            } else {
                mix(5, id.name_atom().content_hash())
            }
        }
        PathView::Pdot(parent, name, _) => mix(mix(6, parent.0.same_hash), name.content_hash()),
        PathView::Papply(functor, arg) => mix(mix(7, functor.0.same_hash), arg.0.same_hash),
    }
}

/// Exact structural identity of two views whose children are interned.
#[inline]
fn view_identical(a: &PathView, b: &PathView) -> bool {
    match (a, b) {
        (PathView::Pident(x), PathView::Pident(y)) => {
            x.name_atom() == y.name_atom() && x.stamp() == y.stamp() && x.flags() == y.flags()
        }
        (PathView::Pdot(p, s, i), PathView::Pdot(q, t, j)) => {
            std::ptr::eq(p.0, q.0) && s == t && i == j
        }
        (PathView::Papply(f, x), PathView::Papply(g, y)) => {
            std::ptr::eq(f.0, g.0) && std::ptr::eq(x.0, y.0)
        }
        _ => false,
    }
}

/// Whether `view` belongs to the `Path.same` class of representative `rep`.
#[inline]
fn view_same_class(view: &PathView, rep: &PathView) -> bool {
    match (view, rep) {
        (PathView::Pident(x), PathView::Pident(y)) => x.same(y),
        (PathView::Pdot(p, s, _), PathView::Pdot(q, t, _)) => s == t && p.same(q),
        (PathView::Papply(f, x), PathView::Papply(g, y)) => f.same(g) && x.same(y),
        _ => false,
    }
}

const SHARDS: usize = 64;
const LOCAL_CACHE: usize = 1 << 13;

type Table = hashbrown::HashTable<&'static PathNode>;

struct Interner {
    nodes: Box<[Mutex<Table>]>,
    classes: Box<[Mutex<Table>]>,
}

static INTERNER: LazyLock<Interner> = LazyLock::new(|| Interner {
    nodes: (0..SHARDS).map(|_| Mutex::new(Table::new())).collect(),
    classes: (0..SHARDS).map(|_| Mutex::new(Table::new())).collect(),
});

thread_local! {
    /// Direct-mapped cache of recently interned nodes, so repeated
    /// constructions skip the shared table and its lock. Bounded, unlike the
    /// table: a slot miss only costs a locked lookup.
    static LOCAL: Box<[Cell<Option<&'static PathNode>>]> =
        (0..LOCAL_CACHE).map(|_| Cell::new(None)).collect();
}

#[inline]
fn shard(hash: u64) -> usize {
    // The table uses the low bits; pick the shard from the high ones.
    (hash >> 58) as usize % SHARDS
}

fn intern(view: PathView) -> Path {
    let hash = node_hash(&view);
    let slot = (hash as usize) & (LOCAL_CACHE - 1);
    if let Ok(Some(node)) = LOCAL.try_with(|local| local[slot].get())
        && node.node_hash == hash
        && view_identical(&node.view, &view)
    {
        return Path(node);
    }
    let node = intern_shared(view, hash);
    // Unavailable only while the thread is being torn down.
    let _ = LOCAL.try_with(|local| local[slot].set(Some(node)));
    Path(node)
}

#[inline(never)]
fn intern_shared(view: PathView, hash: u64) -> &'static PathNode {
    let interner = &*INTERNER;
    let mut nodes = interner.nodes[shard(hash)]
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner());
    if let Some(node) = nodes.find(hash, |node| {
        node.node_hash == hash && view_identical(&node.view, &view)
    }) {
        return node;
    }
    let class_hash = same_hash(&view);
    // Lock order: node shard, then class shard.
    let mut classes = interner.classes[shard(class_hash)]
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner());
    let rep = classes
        .find(class_hash, |rep| {
            rep.same_hash == class_hash && view_same_class(&view, &rep.view)
        })
        .copied();
    let node: &'static PathNode = Box::leak(Box::new(PathNode {
        view,
        same: rep,
        node_hash: hash,
        same_hash: class_hash,
    }));
    if rep.is_none() {
        classes.insert_unique(class_hash, node, |rep| rep.same_hash);
    }
    nodes.insert_unique(hash, node, |node| node.node_hash);
    node
}

impl From<PathView> for Path {
    #[inline]
    fn from(view: PathView) -> Self {
        intern(view)
    }
}

/// `==` is OCaml's structural equality on paths: identifiers compare with
/// `Ident.same` and `Pdot` positions must match.
impl PartialEq for Path {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        std::ptr::eq(self.0, other.0) || (self.same(other) && self.positions_equal(other))
    }
}

impl Eq for Path {}

/// Consistent with `==` and with [`Path::same`]: the hash of the `same`
/// class, which ignores positions and never reads name text.
impl std::hash::Hash for Path {
    #[inline]
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        state.write_u64(self.0.same_hash);
    }
}

impl fmt::Debug for Path {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&self.0.view, f)
    }
}

impl Serialize for Path {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        self.0.view.serialize(serializer)
    }
}

impl<'de> Deserialize<'de> for Path {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        PathView::deserialize(deserializer).map(intern)
    }
}

/// Position constant for no position hint.
pub const NOPOS: i32 = -1;

impl Path {
    /// Create a path from a simple identifier.
    #[inline]
    pub fn pident(id: Ident) -> Self {
        intern(PathView::Pident(id))
    }

    /// Create a dotted path.
    #[inline]
    pub fn pdot(prefix: Path, name: impl Into<Name>) -> Self {
        intern(PathView::Pdot(prefix, name.into(), NOPOS))
    }

    /// Create a dotted path with position.
    #[inline]
    pub fn pdot_pos(prefix: Path, name: impl Into<Name>, pos: i32) -> Self {
        intern(PathView::Pdot(prefix, name.into(), pos))
    }

    /// Create a functor application path.
    #[inline]
    pub fn papply(functor: Path, arg: Path) -> Self {
        intern(PathView::Papply(functor, arg))
    }

    /// The constructor of this path.
    #[inline]
    pub fn view(self) -> &'static PathView {
        &self.0.view
    }

    /// The identifier of a `Pident` path.
    #[inline]
    pub fn as_pident(self) -> Option<&'static Ident> {
        match self.view() {
            PathView::Pident(id) => Some(id),
            _ => None,
        }
    }

    /// Get the parent module path (strip the last component).
    /// For `Pdot(parent, name, _)`, returns `Some(parent)`.
    /// For `Pident(_)` and `Papply(..)`, returns `None`.
    #[inline]
    pub fn parent(&self) -> Option<Path> {
        match self.view() {
            PathView::Pdot(parent, _, _) => Some(*parent),
            _ => None,
        }
    }

    /// The address of the interned node: equal exactly for identical paths
    /// (identifier flags and positions included), unlike `==`.
    #[inline]
    pub fn node_addr(self) -> usize {
        std::ptr::from_ref(self.0) as usize
    }

    /// Check if two paths refer to the same entity (`Path.same`,
    /// `compiler/ml/path.ml:23-29`): structural, with `Ident.same` on
    /// identifiers and `Pdot` positions ignored.
    #[inline]
    pub fn same(&self, other: &Path) -> bool {
        std::ptr::eq(self.0.class(), other.0.class())
    }

    /// Hash consistent with [`Path::same`] (and with `Hash`).
    #[inline]
    pub fn same_hash(&self) -> u64 {
        self.0.same_hash
    }

    /// For two `same` paths: whether their `Pdot` positions also agree.
    fn positions_equal(&self, other: &Path) -> bool {
        if std::ptr::eq(self.0, other.0) {
            return true;
        }
        match (self.view(), other.view()) {
            (PathView::Pident(_), PathView::Pident(_)) => true,
            (PathView::Pdot(p, _, i), PathView::Pdot(q, _, j)) => i == j && p.positions_equal(q),
            (PathView::Papply(f, x), PathView::Papply(g, y)) => {
                f.positions_equal(g) && x.positions_equal(y)
            }
            _ => false,
        }
    }

    /// Check if an identifier is free (appears) in this path.
    pub fn is_free(&self, id: &Ident) -> bool {
        match self.view() {
            PathView::Pident(id2) => id.same(id2),
            PathView::Pdot(p, _, _) => p.is_free(id),
            PathView::Papply(p1, p2) => p1.is_free(id) || p2.is_free(id),
        }
    }

    /// Get the binding time of this path.
    ///
    /// For a functor application this is the later of the two binding
    /// times (OCaml `Path.binding_time`).
    pub fn binding_time(&self) -> i32 {
        match self.view() {
            PathView::Pident(id) => id.binding_time(),
            PathView::Pdot(p, _, _) => p.binding_time(),
            PathView::Papply(p1, p2) => p1.binding_time().max(p2.binding_time()),
        }
    }

    /// Get the string name of this path.
    pub fn name(&self) -> String {
        self.name_with_paren(|_| false)
    }

    /// Whether `name()` equals `target`, without building the name.
    pub fn name_eq(&self, target: &str) -> bool {
        match self.view() {
            PathView::Pident(id) => id.name() == target,
            PathView::Pdot(parent, s, _) => target
                .strip_suffix(s.as_str())
                .and_then(|prefix| prefix.strip_suffix('.'))
                .is_some_and(|prefix| parent.name_eq(prefix)),
            PathView::Papply(_, _) => self.name() == target,
        }
    }

    /// Get the last component name of the path (e.g., "ref" for both "ref" and "Pervasives.ref").
    pub fn head_name(&self) -> &'static str {
        match self.view() {
            PathView::Pident(id) => id.name(),
            PathView::Pdot(_, s, _) => s.as_str(),
            PathView::Papply(_, arg) => arg.head_name(),
        }
    }

    /// Whether `name()` equals `other.name()`, without building either.
    pub fn name_equals(&self, other: &Path) -> bool {
        if std::ptr::eq(self.0, other.0) {
            return true;
        }
        let mut left = smallvec::SmallVec::<[&'static str; 8]>::new();
        let mut right = smallvec::SmallVec::<[&'static str; 8]>::new();
        self.name_pieces(&mut left);
        other.name_pieces(&mut right);
        left.iter()
            .flat_map(|piece| piece.bytes())
            .eq(right.iter().flat_map(|piece| piece.bytes()))
    }

    /// The pieces `name()` concatenates.
    fn name_pieces(&self, out: &mut smallvec::SmallVec<[&'static str; 8]>) {
        match self.view() {
            PathView::Pident(id) => out.push(id.name()),
            PathView::Pdot(p, s, _) => {
                p.name_pieces(out);
                out.push(".");
                out.push(s.as_str());
            }
            PathView::Papply(p1, p2) => {
                p1.name_pieces(out);
                out.push("(");
                p2.name_pieces(out);
                out.push(")");
            }
        }
    }

    /// Get the string name with parenthesization for operators.
    pub fn name_with_paren(&self, paren: impl Fn(&str) -> bool + Copy) -> String {
        let mut out = String::with_capacity(self.name_len_hint());
        self.write_name_with_paren(&mut out, paren);
        out
    }

    /// Append the (parenthesized) name to `out` without intermediate strings.
    pub fn write_name_with_paren(&self, out: &mut String, paren: impl Fn(&str) -> bool + Copy) {
        match self.view() {
            PathView::Pident(id) => out.push_str(id.name()),
            PathView::Pdot(p, s, _) => {
                p.write_name_with_paren(out, paren);
                if paren(s) {
                    out.push_str(".( ");
                    out.push_str(s);
                    out.push_str(" )");
                } else {
                    out.push('.');
                    out.push_str(s);
                }
            }
            PathView::Papply(p1, p2) => {
                p1.write_name_with_paren(out, paren);
                out.push('(');
                p2.write_name_with_paren(out, paren);
                out.push(')');
            }
        }
    }

    fn name_len_hint(&self) -> usize {
        match self.view() {
            PathView::Pident(id) => id.name().len(),
            PathView::Pdot(p, s, _) => p.name_len_hint() + 1 + s.len(),
            PathView::Papply(p1, p2) => p1.name_len_hint() + p2.name_len_hint() + 2,
        }
    }

    /// Get the head identifier of this path.
    ///
    /// # Panics
    ///
    /// Panics if the path is a `Papply`.
    pub fn head(&self) -> &'static Ident {
        self.head_opt().expect("Path::head called on Papply")
    }

    /// Return the identifier at the root of a non-application path.
    pub fn head_opt(&self) -> Option<&'static Ident> {
        match self.view() {
            PathView::Pident(id) => Some(id),
            PathView::Pdot(parent, _, _) => parent.head_opt(),
            PathView::Papply(_, _) => None,
        }
    }

    /// Get the last component of this path.
    pub fn last_name(&self) -> Name {
        match self.view() {
            PathView::Pident(id) => id.name_atom(),
            PathView::Pdot(_, s, _) => *s,
            PathView::Papply(_, p) => p.last_name(),
        }
    }

    /// The last component name, as text.
    pub fn last(&self) -> &'static str {
        match self.view() {
            PathView::Pident(id) => id.name(),
            PathView::Pdot(_, s, _) => s.as_str(),
            PathView::Papply(_, p) => p.last(),
        }
    }

    /// Whether `flatten` would fail, i.e. the non-`Pdot` root is a functor
    /// application. Allocation-free.
    pub fn has_apply_prefix(&self) -> bool {
        match self.view() {
            PathView::Pident(_) => false,
            PathView::Pdot(parent, _, _) => parent.has_apply_prefix(),
            PathView::Papply(_, _) => true,
        }
    }

    /// Flatten this path to an identifier and list of component names.
    ///
    /// Fails with [`ContainsApply`] if the path contains a `Papply`.
    pub fn flatten(&self) -> Result<(&'static Ident, Vec<&'static str>), ContainsApply> {
        fn go(path: Path, acc: &mut Vec<&'static str>) -> Result<&'static Ident, ContainsApply> {
            match path.view() {
                PathView::Pident(id) => Ok(id),
                PathView::Pdot(p, s, _) => {
                    let id = go(*p, acc)?;
                    acc.push(s.as_str());
                    Ok(id)
                }
                PathView::Papply(_, _) => Err(ContainsApply),
            }
        }

        let mut components = Vec::new();
        let id = go(*self, &mut components)?;
        Ok((id, components))
    }

    /// Get all head identifiers in the path (including through `Papply`).
    pub fn heads(&self) -> Vec<&'static Ident> {
        let mut result = Vec::new();
        self.collect_heads(&mut result);
        result
    }

    fn collect_heads(&self, acc: &mut Vec<&'static Ident>) {
        match self.view() {
            PathView::Pident(id) => acc.push(id),
            PathView::Pdot(p, _, _) => p.collect_heads(acc),
            PathView::Papply(p1, p2) => {
                p1.collect_heads(acc);
                p2.collect_heads(acc);
            }
        }
    }

    /// Check if the last component starts with an uppercase letter.
    pub fn is_uident(&self) -> bool {
        is_uident_str(self.last())
    }
}

impl Ord for Path {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        if std::ptr::eq(self.0, other.0) {
            return std::cmp::Ordering::Equal;
        }
        match (self.view(), other.view()) {
            (PathView::Pident(id1), PathView::Pident(id2)) => id1.cmp(id2),
            (PathView::Pdot(p1, s1, _), PathView::Pdot(p2, s2, _)) => match p1.cmp(p2) {
                std::cmp::Ordering::Equal => s1.cmp(s2),
                other => other,
            },
            (PathView::Papply(f1, a1), PathView::Papply(f2, a2)) => match f1.cmp(f2) {
                std::cmp::Ordering::Equal => a1.cmp(a2),
                other => other,
            },
            // Ordering: Pident < Pdot < Papply
            (PathView::Pident(_), _) => std::cmp::Ordering::Less,
            (_, PathView::Pident(_)) => std::cmp::Ordering::Greater,
            (PathView::Pdot(_, _, _), PathView::Papply(_, _)) => std::cmp::Ordering::Less,
            (PathView::Papply(_, _), PathView::Pdot(_, _, _)) => std::cmp::Ordering::Greater,
        }
    }
}

impl PartialOrd for Path {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl fmt::Display for Path {
    /// Same text as `name()`, written without an intermediate `String`.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.view() {
            PathView::Pident(id) => f.write_str(id.name()),
            PathView::Pdot(p, s, _) => {
                fmt::Display::fmt(p, f)?;
                f.write_str(".")?;
                f.write_str(s)
            }
            PathView::Papply(p1, p2) => {
                fmt::Display::fmt(p1, f)?;
                f.write_str("(")?;
                fmt::Display::fmt(p2, f)?;
                f.write_str(")")
            }
        }
    }
}

/// Categorization of paths for constructor handling.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Typath {
    /// Regular type path
    Regular(Path),
    /// Extension type: `A.B` where B is uppercase (extension constructor)
    Ext(Path, String),
    /// Local extension: single uppercase identifier
    LocalExt(Ident),
    /// Constructor path: `A.B` where A is lowercase, B is uppercase
    Cstr(Path, String),
}

impl Path {
    /// Categorize this path for constructor handling.
    pub fn constructor_typath(&self) -> Typath {
        match self.view() {
            PathView::Pident(id) if is_uident_str(id.name()) => Typath::LocalExt(*id),
            PathView::Pdot(ty_path, s, _) if is_uident_str(s) => {
                if is_uident_str(ty_path.last()) {
                    Typath::Ext(*ty_path, s.to_string())
                } else {
                    Typath::Cstr(*ty_path, s.to_string())
                }
            }
            _ => Typath::Regular(*self),
        }
    }

    /// Check if this path refers to a constructor type.
    pub fn is_constructor_typath(&self) -> bool {
        // Same cases as `constructor_typath`, without building the result.
        match self.view() {
            PathView::Pident(id) => is_uident_str(id.name()),
            PathView::Pdot(_, s, _) => is_uident_str(s),
            PathView::Papply(..) => false,
        }
    }
}

/// Check if a string starts with an uppercase letter.
fn is_uident_str(s: &str) -> bool {
    !s.is_empty()
        && s.chars()
            .next()
            .map(|c| c.is_ascii_uppercase())
            .unwrap_or(false)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_name_eq_matches_name() {
        let a = Path::pident(Ident::create_persistent("A"));
        let ab = Path::pdot(a, "B");
        let abc = Path::pdot(ab, "c");
        for path in [&a, &ab, &abc] {
            assert!(path.name_eq(&path.name()));
        }
        assert!(!abc.name_eq("A.Bc"));
        assert!(!abc.name_eq("AB.c"));
        assert!(!abc.name_eq("B.c"));
        assert!(!ab.name_eq("A.B.c"));
        let applied = Path::papply(a, ab);
        assert!(applied.name_eq(&applied.name()));
    }

    #[test]
    fn test_pident() {
        let id = Ident::create_persistent("String");
        let path = Path::pident(id);

        assert_eq!(path.name(), "String");
        assert_eq!(path.last(), "String");
        assert_eq!(path.head(), &id);
    }

    #[test]
    fn test_pdot() {
        let array_id = Ident::create_persistent("Array");
        let path = Path::pdot(Path::pident(array_id), "t");

        assert_eq!(path.name(), "Array.t");
        assert_eq!(path.last(), "t");
        assert_eq!(path.head(), &array_id);
    }

    #[test]
    fn test_papply() {
        let f_id = Ident::create_persistent("F");
        let x_id = Ident::create_persistent("X");
        let path = Path::papply(Path::pident(f_id), Path::pident(x_id));

        assert_eq!(path.name(), "F(X)");
        assert_eq!(path.head_opt(), None);
        assert_eq!(Path::pdot(path, "t").head_opt(), None);
    }

    #[test]
    fn test_same() {
        let id1 = Ident::create_persistent("String");
        let id2 = Ident::create_persistent("String");
        let id3 = Ident::create_persistent("Int");

        let p1 = Path::pident(id1);
        let p2 = Path::pident(id2);
        let p3 = Path::pident(id3);

        assert!(p1.same(&p2));
        assert!(!p1.same(&p3));
    }

    #[test]
    fn test_flatten() {
        let array_id = Ident::create_persistent("Array");
        let path = Path::pdot(Path::pident(array_id), "t");

        let (id, components) = path.flatten().unwrap();
        assert!(id.same(&array_id));
        assert_eq!(components, vec!["t"]);
    }

    #[test]
    fn test_is_uident() {
        let upper = Path::pident(Ident::create_persistent("String"));
        let lower = Path::pident(Ident::create_persistent("string"));

        assert!(upper.is_uident());
        assert!(!lower.is_uident());
    }

    #[test]
    fn test_constructor_typath() {
        let id = Ident::create_persistent("Foo");
        let path = Path::pident(id);

        match path.constructor_typath() {
            Typath::LocalExt(_) => {}
            _ => panic!("Expected LocalExt"),
        }

        let module_id = Ident::create_persistent("Array");
        let t_path = Path::pdot(Path::pident(module_id), "t");

        match t_path.constructor_typath() {
            Typath::Regular(_) => {}
            _ => panic!("Expected Regular"),
        }
    }

    #[test]
    fn test_display() {
        let array_id = Ident::create_persistent("Belt");
        let map_id = Path::pdot(Path::pident(array_id), "Map");
        let int_id = Path::pdot(map_id, "Int");

        assert_eq!(format!("{}", int_id), "Belt.Map.Int");
    }

    #[test]
    fn test_is_free() {
        let id = Ident::create_persistent("X");
        let other = Ident::create_persistent("Y");
        let path = Path::pdot(Path::pident(id), "t");

        assert!(path.is_free(&id));
        assert!(!path.is_free(&other));
    }

    #[test]
    fn test_send_sync() {
        fn assert_send_sync<T: Send + Sync>() {}
        assert_send_sync::<Path>();
    }
}
