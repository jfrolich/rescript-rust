//! Type environment.
//!
//! This module provides `Env`, the typing environment that tracks all
//! bindings during type checking. The environment is immutable and uses
//! a persistent structure for efficient scope management.
//!
//! # Design
//!
//! The environment is modeled as a linked list of bindings, allowing
//! efficient shadowing and scope nesting. Each binding type (values,
//! types, modules) is tracked separately for fast lookup.
//!
//! # Key Components
//!
//! - `Env` - The main environment type
//! - Lookup functions for values, types, and modules

use super::asttypes::PrivateFlag;
use super::context::TypeContext;
use super::decl::{
    ConstructorArguments, ConstructorDeclaration, ConstructorDescription, ConstructorKind,
    LabelDescription, ModtypeDeclaration, ModuleDeclaration, ModuleType, Signature, SignatureItem,
    TypeDeclaration, TypeKind, ValueDescription,
};
use super::path::Path;
use super::type_expr::{TypeDesc, TypeExprRef};
use crate::fast_hash::{AHashMap as HashMap, AHashSet as HashSet};
use crate::ident::Ident;
use crate::location::Location;
use crate::types::path::PathView;
use std::cell::RefCell;
use std::rc::Rc;
use std::sync::Arc;

use crate::name::Name;
use smol_str::SmolStr;

type PersistentHashMap<K, V> = im_rc::HashMap<K, V, ahash::RandomState>;
type PersistentHashSet<T> = im_rc::HashSet<T, ahash::RandomState>;
/// Component table of one opened layer. Built once when the layer is opened
/// and only read afterwards (a rare in-place update copies the layer), so a
/// flat hash table replaces the persistent map: one allocation to build and
/// to drop instead of a tree of reference-counted nodes.
type OpenedMap<V> = crate::fast_hash::AHashMap<Name, V>;

/// Collect free type variables (Tvar nodes) from a type expression.
/// Matches OCaml's Datarepr.free_vars.
fn free_vars(ctx: &TypeContext, ty: TypeExprRef) -> HashSet<TypeExprRef> {
    let mut result = HashSet::new();
    let mut visited = HashSet::new();
    free_vars_rec(ctx, ty, &mut result, &mut visited);
    result
}

fn free_vars_rec(
    ctx: &TypeContext,
    ty: TypeExprRef,
    result: &mut HashSet<TypeExprRef>,
    visited: &mut HashSet<TypeExprRef>,
) {
    let ty = ctx.repr(ty);
    if !visited.insert(ty) {
        return;
    }
    let desc = ctx.get_desc(ty);
    match &*desc {
        TypeDesc::Tvar(..) => {
            result.insert(ty);
        }
        _ => {
            super::btype::iter_type_expr(ctx, ty, |child| {
                free_vars_rec(ctx, child, result, visited);
            });
        }
    }
}

/// OCaml `Datarepr.free_vars ~param:true (newgenty (Ttuple tys))`
/// (datarepr.ml:24-44) as `Type_set.elements`: the free type variables of
/// `tys`, where a non-static polymorphic variant whose row variable is free
/// counts as one parameter itself, ordered by node (allocation order,
/// OCaml's `type_expr.id`).
pub(crate) fn free_vars_param(ctx: &TypeContext, tys: &[TypeExprRef]) -> Vec<TypeExprRef> {
    fn walk(
        ctx: &TypeContext,
        ty: TypeExprRef,
        result: &mut Vec<TypeExprRef>,
        visited: &mut HashSet<TypeExprRef>,
    ) {
        let ty = ctx.repr(ty);
        if !visited.insert(ty) {
            return;
        }
        let desc = ctx.get_desc(ty).into_desc();
        match desc {
            TypeDesc::Tvar(..) => result.push(ty),
            TypeDesc::Tvariant(row) => {
                let row = super::btype::row_repr(ctx, &ctx.row_desc(row));
                // `iter_row loop row`: the fields, and the name's arguments.
                for (_, field) in row.row_fields.iter() {
                    match super::btype::row_field_repr(ctx, field) {
                        super::type_expr::RowField::Rpresent(Some(arg)) => {
                            walk(ctx, arg, result, visited)
                        }
                        super::type_expr::RowField::Reither { types, .. } => {
                            for arg in types.iter() {
                                walk(ctx, *arg, result, visited);
                            }
                        }
                        _ => {}
                    }
                }
                if let Some((_, args)) = &row.row_name {
                    for arg in args.iter() {
                        walk(ctx, *arg, result, visited);
                    }
                }
                if !super::btype::static_row(ctx, &row) {
                    let more = ctx.repr(row.row_more);
                    if matches!(&*ctx.get_desc(more), TypeDesc::Tvar(..)) {
                        result.push(ty);
                    } else {
                        walk(ctx, more, result, visited);
                    }
                }
            }
            _ => super::btype::iter_type_expr(ctx, ty, |child| {
                walk(ctx, child, result, visited);
            }),
        }
    }
    let mut result = Vec::new();
    let mut visited = HashSet::new();
    for &ty in tys {
        walk(ctx, ty, &mut result, &mut visited);
    }
    result.sort_by_key(|ty| ty.0);
    result.dedup();
    result
}

/// Compute existential type variables for a GADT constructor.
/// Existentials are type variables that appear in the args but not in the result type.
/// Matches OCaml's Datarepr.constructor_existentials.
pub fn constructor_existentials(
    ctx: &TypeContext,
    cstr_args: &[TypeExprRef],
    cd_res: Option<TypeExprRef>,
) -> Vec<TypeExprRef> {
    match cd_res {
        None => vec![],
        Some(res_ty) => {
            // Collect free vars from all args (via a Ttuple wrapper like OCaml)
            let mut arg_vars = HashSet::new();
            for &arg in cstr_args {
                for v in free_vars(ctx, arg) {
                    arg_vars.insert(v);
                }
            }
            // Collect free vars from the result type
            let res_vars = free_vars(ctx, res_ty);
            // Existentials = args vars - result vars, as
            // `Type_set.elements`: ordered by node (allocation order, OCaml's
            // `type_expr.id`), which is the order `instance_constructor`
            // allocates their abstract types in.
            let mut existentials: Vec<TypeExprRef> =
                arg_vars.difference(&res_vars).copied().collect();
            existentials.sort_by_key(|ty| ty.0);
            existentials
        }
    }
}

// ============================================================================
// Environment Errors
// ============================================================================

/// Errors that can occur during environment operations.
#[derive(Debug, Clone)]
pub enum EnvError {
    /// Value not found.
    ValueNotFound(SmolStr),
    /// Type not found.
    TypeNotFound(SmolStr),
    /// Module not found.
    ModuleNotFound(SmolStr),
    /// Module type not found.
    ModtypeNotFound(SmolStr),
    /// Constructor not found.
    ConstructorNotFound(SmolStr),
    /// Label not found.
    LabelNotFound(SmolStr),
    /// Inconsistent import.
    InconsistentImport {
        /// The unit imported.
        name: String,
        /// One interface file it was compiled against.
        source1: String,
        /// The other, which disagrees.
        source2: String,
    },
    /// Illegal value name.
    IllegalValueName(Location, String),
}

/// Result type for environment operations.
pub type EnvResult<T> = Result<T, EnvError>;

/// Check that a value identifier is accepted by the environment.
///
/// Mirrors OCaml `Env.check_value_name`: most lexical validity is enforced
/// before this point, but forged AST/CMI values named `->` or multi-`#`
/// method identifiers must be rejected when values enter the environment.
pub fn check_value_name(name: &str, loc: Location) -> EnvResult<()> {
    if name == "->" {
        return Err(EnvError::IllegalValueName(loc, name.to_string()));
    }
    if let Some(rest) = name.strip_prefix('#') {
        if rest.as_bytes().contains(&b'#') {
            return Err(EnvError::IllegalValueName(loc, name.to_string()));
        }
    }
    Ok(())
}

// ============================================================================
// Binding Tables
// ============================================================================

#[cfg(test)]
thread_local! {
    /// Items put into opened layer tables on this thread.
    pub(crate) static OPEN_TABLE_INSERTS: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
}

#[inline]
fn count_open_table_insert() {
    #[cfg(test)]
    OPEN_TABLE_INSERTS.with(|inserts| inserts.set(inserts.get() + 1));
}

fn id_open_table<T>(components: Vec<(Ident, T, i32)>) -> OpenedMap<(Ident, T, i32)> {
    let mut table = OpenedMap::with_capacity_and_hasher(components.len(), Default::default());
    for (id, value, pos) in components {
        count_open_table_insert();
        table.insert(id.name_atom(), (id, value, pos));
    }
    table
}

fn tycomp_open_table<T>(components: Vec<(Ident, T)>) -> OpenedMap<Vec<(Ident, T)>> {
    let mut table: OpenedMap<Vec<(Ident, T)>> =
        OpenedMap::with_capacity_and_hasher(components.len(), Default::default());
    for (id, value) in components {
        count_open_table_insert();
        let name = id.name_atom();
        match table.get_mut(&name) {
            Some(entries) => entries.insert(0, (id, value)),
            None => {
                table.insert(name, vec![(id, value)]);
            }
        }
    }
    table
}

/// The constructors or labels that share a name, with their identifiers.
type Candidates<T> = Vec<(Ident, Arc<T>)>;

/// `TycompTbl`'s `mk_callback` data for a candidate found in an opened
/// layer: the layer's slot and the first candidate it hides.
pub type OpenSlotMark<'a, T> = Option<(u32, Option<&'a T>)>;

/// The layer tables that opening one signature adds to an Env. Built once
/// and attachable to any number of Envs (see `Env::add_prebuilt_open_layers`).
#[derive(Debug)]
pub(crate) struct OpenedLayers {
    values: Rc<OpenedMap<(Ident, Arc<ValueDescription>, i32)>>,
    types: Rc<OpenedMap<(Ident, Arc<TypeDeclaration>, i32)>>,
    constrs: Rc<OpenedMap<Candidates<ConstructorDescription>>>,
    labels: Rc<OpenedMap<Candidates<LabelDescription>>>,
    modules: Rc<OpenedMap<(Ident, Arc<ModuleDeclaration>, i32)>>,
    module_components: Rc<OpenedMap<(Ident, Rc<super::env_lazy::StoredModuleComponents>, i32)>>,
    modtypes: Rc<OpenedMap<(Ident, Arc<ModtypeDeclaration>, i32)>>,
}

impl OpenedLayers {
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn build(
        values: Vec<(Ident, ValueDescription, i32)>,
        types: Vec<(Ident, Arc<TypeDeclaration>)>,
        constructors: Vec<(Ident, ConstructorDescription)>,
        labels: Vec<(Ident, LabelDescription)>,
        modules: Vec<(Ident, ModuleDeclaration, i32)>,
        module_components: Vec<(Ident, Rc<super::env_lazy::StoredModuleComponents>, i32)>,
        modtypes: Vec<(Ident, ModtypeDeclaration)>,
    ) -> Self {
        OpenedLayers {
            values: Rc::new(id_open_table(
                values
                    .into_iter()
                    .map(|(id, desc, pos)| (id, Arc::new(desc), pos))
                    .collect(),
            )),
            types: Rc::new(id_open_table(
                types
                    .into_iter()
                    .map(|(id, decl)| (id, decl, crate::types::path::NOPOS))
                    .collect(),
            )),
            constrs: Rc::new(tycomp_open_table(
                constructors
                    .into_iter()
                    .map(|(id, desc)| (id, Arc::new(desc)))
                    .collect(),
            )),
            labels: Rc::new(tycomp_open_table(
                labels
                    .into_iter()
                    .map(|(id, desc)| (id, Arc::new(desc)))
                    .collect(),
            )),
            modules: Rc::new(id_open_table(
                modules
                    .into_iter()
                    .map(|(id, decl, pos)| (id, Arc::new(decl), pos))
                    .collect(),
            )),
            module_components: Rc::new(id_open_table(module_components)),
            modtypes: Rc::new(id_open_table(
                modtypes
                    .into_iter()
                    .map(|(id, decl)| (id, Arc::new(decl), crate::types::path::NOPOS))
                    .collect(),
            )),
        }
    }

    /// The layer tables of a world view's opened items. One hash insert
    /// and one reference-count increment per item; no type node.
    pub(crate) fn from_view(
        items: &super::module_view::OpenedItems,
        module_components: Vec<(Ident, Rc<super::env_lazy::StoredModuleComponents>, i32)>,
    ) -> Self {
        let no_pos = crate::types::path::NOPOS;
        OpenedLayers {
            values: Rc::new(id_open_table(items.values.clone())),
            types: Rc::new(id_open_table(
                items
                    .types
                    .iter()
                    .map(|(id, decl)| (*id, decl.clone(), no_pos))
                    .collect(),
            )),
            constrs: Rc::new(tycomp_open_table(items.constructors.clone())),
            labels: Rc::new(tycomp_open_table(items.labels.clone())),
            modules: Rc::new(id_open_table(
                items
                    .modules
                    .iter()
                    .map(|module| (module.id, module.decl.clone(), module.pos))
                    .collect(),
            )),
            module_components: Rc::new(id_open_table(module_components)),
            modtypes: Rc::new(id_open_table(
                items
                    .modtypes
                    .iter()
                    .map(|(id, decl)| (*id, decl.clone(), no_pos))
                    .collect(),
            )),
        }
    }

    /// R4 oracle: every member of the layer; the candidates of one
    /// constructor or label name in the order a lookup finds them.
    #[cfg(debug_assertions)]
    fn trace_members(&self) -> Vec<crate::tc::scope_trace::Member> {
        use crate::tc::scope_trace::Ns;
        let mut members = Vec::new();
        members.extend(self.values.values().map(|(id, _, _)| (Ns::Value, id.name(), id.stamp())));
        members.extend(self.types.values().map(|(id, _, _)| (Ns::Type, id.name(), id.stamp())));
        members.extend(self.modules.values().map(|(id, _, _)| (Ns::Module, id.name(), id.stamp())));
        members.extend(self.modtypes.values().map(|(id, _, _)| (Ns::ModuleType, id.name(), id.stamp())));
        for candidates in self.constrs.values() {
            members.extend(candidates.iter().map(|(id, _)| (Ns::Constructor, id.name(), id.stamp())));
        }
        for candidates in self.labels.values() {
            members.extend(candidates.iter().map(|(id, _)| (Ns::Label, id.name(), id.stamp())));
        }
        members
    }

    fn is_empty(&self) -> bool {
        self.values.is_empty()
            && self.types.is_empty()
            && self.constrs.is_empty()
            && self.labels.is_empty()
            && self.modules.is_empty()
            && self.module_components.is_empty()
            && self.modtypes.is_empty()
    }
}

/// Symbolic opened layer for identifier-indexed tables.
///
/// Mirrors OCaml `Env.IdTbl.opened`: one open layer contains the opened
/// module root, its component table, and the table that existed before the
/// open.
#[derive(Debug, Clone)]
struct IdOpened<T> {
    /// The open's root path, one block shared by every lookup through the
    /// open and by all the tables it opens (env.ml `add_components`).
    root: Option<Arc<Path>>,
    components: Rc<OpenedMap<(Ident, T, i32)>>,
    next: Rc<IdTbl<T>>,
    /// The open's `using` callback (OCaml `IdTbl.opened.using`), as a slot
    /// registered with the type checker.
    slot: Option<u32>,
}

/// The environment table a source name is looked up in (OCaml's `proj1`
/// argument of `Env.lookup`, or the table `lookup_module{,_descr}` reads).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OpenLookupKind {
    /// The value table.
    Value,
    /// The type table.
    Type,
    /// The module table, read for a module's declaration.
    Module,
    /// The module component table, read for a module's components.
    Component,
    /// The module type table.
    Modtype,
}

impl OpenLookupKind {
    /// The kind `Env.check_shadowing` reports.
    pub fn shadow_kind(self) -> &'static str {
        match self {
            OpenLookupKind::Value => "value",
            OpenLookupKind::Type => "type",
            OpenLookupKind::Module | OpenLookupKind::Component => "module",
            OpenLookupKind::Modtype => "module type",
        }
    }
}

/// A name found through an opened layer that has a usage slot (OCaml
/// `IdTbl.find_name ~mark:true` calling `using name shadowed`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct OpenSlotUse {
    /// The open's slot.
    pub slot: u32,
    /// Whether an earlier binding of the name is hidden by the open.
    pub shadowed: bool,
}

/// A fold that conses every visited name (`fun x xs -> x :: xs`) returns
/// them in reverse visit order.
fn fold_names_list(order: Vec<&str>) -> Vec<String> {
    order.into_iter().rev().map(str::to_string).collect()
}

/// Visit order of OCaml `Ident.fold_name` (compiler/ext/ident.ml:144-189)
/// over a table whose names were first added in stamp order. `Ident.add`
/// builds an AVL tree keyed by name (re-adding a name keeps the node), and
/// `fold_aux` visits a node, then its right subtree, then the pending left
/// subtrees.
fn ident_tbl_fold_name_order<'a>(names: impl Iterator<Item = (&'a str, i32)>) -> Vec<&'a str> {
    struct Node<'a> {
        name: &'a str,
        left: Option<usize>,
        right: Option<usize>,
        height: i32,
    }
    fn height(nodes: &[Node<'_>], n: Option<usize>) -> i32 {
        n.map_or(0, |n| nodes[n].height)
    }
    fn mknode<'a>(
        nodes: &mut Vec<Node<'a>>,
        left: Option<usize>,
        name: &'a str,
        right: Option<usize>,
    ) -> usize {
        let (hl, hr) = (height(nodes, left), height(nodes, right));
        nodes.push(Node {
            name,
            left,
            right,
            height: if hl >= hr { hl + 1 } else { hr + 1 },
        });
        nodes.len() - 1
    }
    fn balance<'a>(
        nodes: &mut Vec<Node<'a>>,
        l: Option<usize>,
        d: &'a str,
        r: Option<usize>,
    ) -> usize {
        let (hl, hr) = (height(nodes, l), height(nodes, r));
        if hl > hr + 1 {
            let l = l.expect("unbalanced left subtree");
            let (ll, ld, lr) = (nodes[l].left, nodes[l].name, nodes[l].right);
            if height(nodes, ll) >= height(nodes, lr) {
                let right = mknode(nodes, lr, d, r);
                mknode(nodes, ll, ld, Some(right))
            } else {
                let lr = lr.expect("unbalanced left-right subtree");
                let (lrl, lrd, lrr) = (nodes[lr].left, nodes[lr].name, nodes[lr].right);
                let left = mknode(nodes, ll, ld, lrl);
                let right = mknode(nodes, lrr, d, r);
                mknode(nodes, Some(left), lrd, Some(right))
            }
        } else if hr > hl + 1 {
            let r = r.expect("unbalanced right subtree");
            let (rl, rd, rr) = (nodes[r].left, nodes[r].name, nodes[r].right);
            if height(nodes, rr) >= height(nodes, rl) {
                let left = mknode(nodes, l, d, rl);
                mknode(nodes, Some(left), rd, rr)
            } else {
                let rl = rl.expect("unbalanced right-left subtree");
                let (rll, rld, rlr) = (nodes[rl].left, nodes[rl].name, nodes[rl].right);
                let left = mknode(nodes, l, d, rll);
                let right = mknode(nodes, rlr, rd, rr);
                mknode(nodes, Some(left), rld, Some(right))
            }
        } else {
            mknode(nodes, l, d, r)
        }
    }
    fn add<'a>(nodes: &mut Vec<Node<'a>>, name: &'a str, tree: Option<usize>) -> usize {
        let Some(t) = tree else {
            return mknode(nodes, None, name, None);
        };
        let (l, k, r) = (nodes[t].left, nodes[t].name, nodes[t].right);
        match name.as_bytes().cmp(k.as_bytes()) {
            std::cmp::Ordering::Equal => t,
            std::cmp::Ordering::Less => {
                let l = add(nodes, name, l);
                balance(nodes, Some(l), k, r)
            }
            std::cmp::Ordering::Greater => {
                let r = add(nodes, name, r);
                balance(nodes, l, k, Some(r))
            }
        }
    }

    let mut insertion: Vec<(&'a str, i32)> = names.collect();
    insertion.sort_by_key(|&(_, stamp)| stamp);
    let mut nodes = Vec::with_capacity(insertion.len() * 2);
    let mut root = None;
    for (name, _) in insertion {
        root = Some(add(&mut nodes, name, root));
    }
    let mut order = Vec::new();
    let mut stack = Vec::new();
    let mut current = root;
    loop {
        match current {
            Some(n) => {
                order.push(nodes[n].name);
                stack.push(nodes[n].left);
                current = nodes[n].right;
            }
            None => match stack.pop() {
                Some(next) => current = next,
                None => break,
            },
        }
    }
    order
}

/// The persistent map of one layer of an Env table. It allocates nothing
/// until its first insertion: every `open` starts a new layer in each of the
/// environment's tables, most layers never get a binding of their own, and
/// an empty persistent map still owns a root node and a hasher.
#[derive(Clone)]
struct LayerMap<K, V>(Option<PersistentHashMap<K, V>>);

impl<K, V> std::fmt::Debug for LayerMap<K, V>
where
    K: std::fmt::Debug + std::hash::Hash + Eq,
    V: std::fmt::Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.0 {
            Some(map) => map.fmt(f),
            None => f.write_str("{}"),
        }
    }
}

impl<K, V> Default for LayerMap<K, V> {
    fn default() -> Self {
        LayerMap(None)
    }
}

impl<K: std::hash::Hash + Eq + Clone, V: Clone> LayerMap<K, V> {
    #[inline]
    fn is_empty(&self) -> bool {
        self.0.as_ref().is_none_or(|map| map.is_empty())
    }

    fn len(&self) -> usize {
        self.0.as_ref().map_or(0, |map| map.len())
    }

    #[inline]
    fn get(&self, key: &K) -> Option<&V> {
        self.0.as_ref()?.get(key)
    }

    #[inline]
    fn contains_key(&self, key: &K) -> bool {
        self.0.as_ref().is_some_and(|map| map.contains_key(key))
    }

    fn get_mut(&mut self, key: &K) -> Option<&mut V> {
        self.0.as_mut()?.get_mut(key)
    }

    fn insert(&mut self, key: K, value: V) {
        self.0.get_or_insert_with(Default::default).insert(key, value);
    }

    fn iter(&self) -> impl Iterator<Item = (&K, &V)> {
        self.0.iter().flat_map(|map| map.iter())
    }

    fn keys(&self) -> impl Iterator<Item = &K> {
        self.iter().map(|(key, _)| key)
    }

    fn values(&self) -> impl Iterator<Item = &V> {
        self.iter().map(|(_, value)| value)
    }

    /// Whether both are the same map, sharing every node.
    #[cfg(test)]
    fn ptr_eq(&self, other: &Self) -> bool {
        match (&self.0, &other.0) {
            (Some(left), Some(right)) => left.ptr_eq(right),
            (None, None) => true,
            _ => false,
        }
    }
}

/// Same-name bindings in an Env table, oldest first. Most names are bound
/// once, so a single binding is stored inline; a name bound again moves its
/// bindings to a shared vector, so copying a persistent-map node on insert
/// only bumps reference counts.
#[derive(Debug, Clone)]
enum IdBucket<T> {
    One([(Ident, T); 1]),
    Many(std::rc::Rc<Vec<(Ident, T)>>),
}

impl<T: Clone> IdBucket<T> {
    fn push(&mut self, id: Ident, value: T) {
        match self {
            IdBucket::One([first]) => {
                *self = IdBucket::Many(std::rc::Rc::new(vec![first.clone(), (id, value)]));
            }
            IdBucket::Many(entries) => std::rc::Rc::make_mut(entries).push((id, value)),
        }
    }

    fn last_mut(&mut self) -> Option<&mut (Ident, T)> {
        match self {
            IdBucket::One([entry]) => Some(entry),
            IdBucket::Many(entries) => std::rc::Rc::make_mut(entries).last_mut(),
        }
    }
}

impl<T> std::ops::Deref for IdBucket<T> {
    type Target = [(Ident, T)];

    #[inline]
    fn deref(&self) -> &[(Ident, T)] {
        match self {
            IdBucket::One(entry) => entry,
            IdBucket::Many(entries) => entries,
        }
    }
}

/// A binding added to an `IdTbl` since its map was last extended, heading
/// the list of the bindings added before it.
#[derive(Debug)]
struct Recent<T> {
    id: Ident,
    value: T,
    next: Option<std::rc::Rc<Recent<T>>>,
    /// Bindings in the list headed by this one.
    len: u32,
    /// One bit per name bound in the list headed by this one (see
    /// `recent_name_bit`): a lookup of a name whose bit is clear skips the
    /// list.
    names: u64,
}

/// How many bindings an `IdTbl` keeps in its recent list before moving them
/// into its map. Larger batches copy the map less often but make every
/// lookup of a listed name walk further; 16 measured best of 8 to 64 on a
/// 3,735-module application.
const RECENT_LIMIT: u32 = 16;

#[inline]
fn recent_name_bit(name: Name) -> u64 {
    1 << (name.content_hash() & 63)
}

/// A table of bindings indexed by identifier.
///
/// This matches OCaml `Env.IdTbl`: local bindings live in `current`, and each
/// open is represented symbolically as an `opened` layer rather than flattening
/// every opened binding into the same name map with an origin boolean.
///
/// The local bindings are a persistent map plus the list of the bindings
/// added since the map was last extended, newest first. Every snapshot of an
/// environment keeps its version of the table alive, and adding to a shared
/// map copies whole map nodes, which the snapshot then holds until the module
/// is torn down. Adding to the list allocates one small node instead; the
/// list is moved into the map once it holds `RECENT_LIMIT` bindings, so the
/// map is copied once per batch. Every reader looks in the list first.
#[derive(Debug, Clone)]
pub struct IdTbl<T> {
    current: LayerMap<Name, IdBucket<T>>,
    recent: Option<std::rc::Rc<Recent<T>>>,
    opened: Option<Rc<IdOpened<T>>>,
}

impl<T: Clone> IdTbl<T> {
    /// An empty table.
    pub fn new() -> Self {
        Self {
            current: LayerMap::default(),
            recent: None,
            opened: None,
        }
    }

    /// Bind `id` to `value`, shadowing earlier bindings of its name.
    pub fn add(&mut self, id: Ident, value: T) {
        let (len, names) = self
            .recent
            .as_ref()
            .map_or((0, 0), |recent| (recent.len, recent.names));
        self.recent = Some(std::rc::Rc::new(Recent {
            names: names | recent_name_bit(id.name_atom()),
            len: len + 1,
            id,
            value,
            next: self.recent.take(),
        }));
        if len + 1 >= RECENT_LIMIT {
            self.move_recent_to_map();
        }
    }

    /// Move the recent bindings into the map, oldest first.
    fn move_recent_to_map(&mut self) {
        let mut next = self.recent.take();
        let mut newest_first = Vec::with_capacity(next.as_ref().map_or(0, |r| r.len as usize));
        while let Some(node) = next {
            // A snapshot may still hold the list; then copy the binding out.
            match std::rc::Rc::try_unwrap(node) {
                Ok(node) => {
                    newest_first.push((node.id, node.value));
                    next = node.next;
                }
                Err(node) => {
                    newest_first.push((node.id, node.value.clone()));
                    next = node.next.clone();
                }
            }
        }
        for (id, value) in newest_first.into_iter().rev() {
            self.add_to_map(id, value);
        }
    }

    /// The recent bindings of `key`, newest first.
    #[inline]
    fn recent_named(&self, key: Name) -> impl Iterator<Item = (&Ident, &T)> {
        let bit = recent_name_bit(key);
        let has_name = move |node: &&Recent<T>| node.names & bit != 0;
        std::iter::successors(self.recent.as_deref().filter(has_name), move |node| {
            node.next.as_deref().filter(has_name)
        })
        .filter(move |node| node.id.name_atom() == key)
        .map(|node| (&node.id, &node.value))
    }

    /// Every recent binding, newest first.
    fn recent_entries(&self) -> impl Iterator<Item = (&Ident, &T)> {
        std::iter::successors(self.recent.as_deref(), |node| node.next.as_deref())
            .map(|node| (&node.id, &node.value))
    }

    fn add_to_map(&mut self, id: Ident, value: T) {
        let key = id.name_atom();
        // `get_mut` copies the shared map path even when the key is absent,
        // so probe first: most added names are new.
        if self.current.contains_key(&key)
            && let Some(entries) = self.current.get_mut(&key)
        {
            entries.push(id, value);
        } else {
            self.current.insert(key, IdBucket::One([(id, value)]));
        }
    }

    /// Add the components of an opened module, rooted at `root`, as a new
    /// layer; `slot` identifies the open for unused-open warnings.
    pub fn add_open_layer(
        &mut self,
        root: Path,
        components: Vec<(Ident, T, i32)>,
        slot: Option<u32>,
    ) {
        self.add_open_layer_table(Arc::new(root), Rc::new(id_open_table(components)), slot);
    }

    /// Open a prebuilt layer table (possibly shared with other Envs).
    fn add_open_layer_table(
        &mut self,
        root: Arc<Path>,
        components: Rc<OpenedMap<(Ident, T, i32)>>,
        slot: Option<u32>,
    ) {
        if components.is_empty() {
            return;
        }
        let next = std::mem::take(self);
        *self = Self {
            current: LayerMap::default(),
            recent: None,
            opened: Some(Rc::new(IdOpened {
                root: Some(root),
                components,
                next: Rc::new(next),
                slot,
            })),
        };
    }

    /// The `using` call of OCaml `IdTbl.find_name ~mark:true` for `name`:
    /// the slot of the opened layer the name resolves to, and whether that
    /// layer hides an earlier binding (`find_name ~mark:false name next`).
    pub fn open_slot_use(&self, name: impl crate::name::NameKey) -> Option<OpenSlotUse> {
        // A name never interned is in no table.
        self.open_slot_use_by_key(name.name_key()?)
    }

    fn open_slot_use_by_key(&self, key: Name) -> Option<OpenSlotUse> {
        if self.recent_named(key).next().is_some()
            || self
                .current
                .get(&key)
                .is_some_and(|entries| !entries.is_empty())
        {
            return None;
        }
        let opened = self.opened.as_ref()?;
        if opened.components.contains_key(&key) {
            return opened.slot.map(|slot| OpenSlotUse {
                slot,
                shadowed: opened.next.find_name_entry_key(key).is_some(),
            });
        }
        opened.next.open_slot_use_by_key(key)
    }

    fn find_current_by_ident(&self, id: &Ident) -> Option<&T> {
        let stamp = id.stamp();
        let is_id = |entry_id: &Ident| {
            if stamp == 0 {
                entry_id.is_persistent() && entry_id.name_atom() == id.name_atom()
            } else {
                entry_id.same(id) && entry_id.name_atom() == id.name_atom()
            }
        };
        if let Some((_, value)) = self
            .recent_named(id.name_atom())
            .find(|(entry_id, _)| is_id(entry_id))
        {
            return Some(value);
        }
        // Opening a module starts a fresh, usually empty, local layer; skip
        // hashing the name for those.
        if self.current.is_empty() {
            return None;
        }
        self.current.get(&id.name_atom()).and_then(|entries| {
            entries
                .iter()
                .rev()
                .find(|(entry_id, _)| is_id(entry_id))
                .map(|(_, value)| value)
        })
    }

    fn find_name_entry(&self, name: impl crate::name::NameKey) -> Option<(&Ident, &T)> {
        self.find_name_entry_key(name.name_key()?)
    }

    fn find_name_entry_key(&self, key: Name) -> Option<(&Ident, &T)> {
        if let Some(found) = self.recent_named(key).next() {
            return Some(found);
        }
        if !self.current.is_empty()
            && let Some((id, value)) = self.current.get(&key).and_then(|entries| entries.last())
        {
            return Some((id, value));
        }

        match &self.opened {
            Some(opened) => opened
                .components
                .get(&key)
                .map(|(id, value, _)| (id, value))
                .or_else(|| opened.next.find_name_entry_key(key)),
            None => None,
        }
    }

    /// The innermost binding of `name`.
    pub fn find_by_name(&self, name: impl crate::name::NameKey) -> Option<&T> {
        self.find_name_entry(name).map(|(_, value)| value)
    }

    /// The innermost binding of `name`, with its identifier.
    pub fn find_by_name_with_id(&self, name: impl crate::name::NameKey) -> Option<(&Ident, &T)> {
        self.find_name_entry(name)
    }

    /// The innermost binding of `name`, with its path.
    pub fn find_by_name_with_path(&self, name: impl crate::name::NameKey) -> Option<(Path, &T)> {
        self.find_by_key_with_path(name.name_key()?)
    }

    fn find_by_key_with_path(&self, key: Name) -> Option<(Path, &T)> {
        if let Some((id, value)) = self.recent_named(key).next() {
            return Some((Path::pident(*id), value));
        }
        if !self.current.is_empty()
            && let Some((id, value)) = self.current.get(&key).and_then(|entries| entries.last())
        {
            return Some((Path::pident(*id), value));
        }

        match &self.opened {
            Some(opened) => opened
                .components
                .get(&key)
                .map(|(id, value, pos)| {
                    let path = opened
                        .root
                        .as_ref()
                        // env.ml:293: `Pdot (root, name, pos)`.
                        .map(|root| Path::pdot_pos(**root, key, *pos))
                        .unwrap_or_else(|| Path::pident(*id));
                    (path, value)
                })
                .or_else(|| opened.next.find_by_key_with_path(key)),
            None => None,
        }
    }

    /// Find a binding by identifier, matching OCaml `IdTbl.find_same`.
    ///
    /// Exact identifier lookup walks `current` bindings through open layers and
    /// intentionally skips opened component tables.
    pub fn find_by_ident(&self, id: &Ident) -> Option<&T> {
        if let Some(value) = self.find_current_by_ident(id) {
            return Some(value);
        }
        self.opened
            .as_ref()
            .and_then(|opened| opened.next.find_by_ident(id))
    }

    /// The local binding of exactly `id`.
    pub fn find_local_by_ident(&self, id: &Ident) -> Option<&T> {
        self.find_by_ident(id)
    }

    /// Replace the innermost binding of `name` by `f` of it, returning the new
    /// binding.
    pub fn update_by_name<F>(&mut self, name: &str, f: &mut F) -> Option<(Ident, T)>
    where
        F: FnMut(&T) -> T,
    {
        self.update_by_key(Name::lookup(name)?, f)
    }

    fn update_by_key<F>(&mut self, key: Name, f: &mut F) -> Option<(Ident, T)>
    where
        F: FnMut(&T) -> T,
    {
        // The map holds the bindings that can be changed in place.
        if self.recent_named(key).next().is_some() {
            self.move_recent_to_map();
        }
        if self.current.contains_key(&key)
            && let Some(entries) = self.current.get_mut(&key)
            && let Some((id, value)) = entries.last_mut()
        {
            let updated = f(value);
            *value = updated.clone();
            return Some((*id, updated));
        }

        if let Some(opened) = self.opened.as_mut() {
            let opened = Rc::make_mut(opened);
            if let Some((id, value, _)) = Rc::make_mut(&mut opened.components).get_mut(&key) {
                let updated = f(value);
                *value = updated.clone();
                return Some((*id, updated));
            }
            return Rc::make_mut(&mut opened.next).update_by_key(key, f);
        }

        None
    }

    /// Every binding of `name`, innermost first.
    pub fn find_all(&self, name: impl crate::name::NameKey) -> Vec<&T> {
        let mut items = Vec::new();
        if let Some(key) = name.name_key() {
            self.collect_all_key(key, &mut items);
        }
        items
    }

    fn collect_all_key<'a>(&'a self, key: Name, items: &mut Vec<&'a T>) {
        items.extend(self.recent_named(key).map(|(_, value)| value));
        if let Some(entries) = self.current.get(&key) {
            items.extend(entries.iter().rev().map(|(_, value)| value));
        }
        if let Some(opened) = &self.opened {
            if let Some((_, value, _)) = opened.components.get(&key) {
                items.push(value);
            }
            opened.next.collect_all_key(key, items);
        }
    }

    /// Whether `name` is bound.
    pub fn contains(&self, name: impl crate::name::NameKey) -> bool {
        self.find_by_name(name).is_some()
    }

    /// Every binding in the table.
    pub fn iter(&self) -> impl Iterator<Item = (&Ident, &T)> {
        let mut items = Vec::new();
        self.collect_iter(&mut items);
        items.into_iter()
    }

    fn collect_iter<'a>(&'a self, items: &mut Vec<(&'a Ident, &'a T)>) {
        items.extend(self.recent_entries());
        for entries in self.current.values() {
            items.extend(entries.iter().map(|(id, value)| (id, value)));
        }
        if let Some(opened) = &self.opened {
            items.extend(opened.components.values().map(|(id, value, _)| (id, value)));
            opened.next.collect_iter(items);
        }
    }

    /// The names visited by OCaml `IdTbl.fold_name` (compiler/ml/env.ml:345-358),
    /// in visit order: the current layer through `Ident.fold_name`, then the
    /// opened components through `Tbl.fold`, then the next layer.
    pub fn fold_name_order(&self) -> Vec<&str> {
        let mut names = Vec::new();
        self.collect_fold_name_order(&mut names);
        names
    }

    fn collect_fold_name_order<'a>(&'a self, names: &mut Vec<&'a str>) {
        // Read the local layer as one map, so the names come out in the
        // order they would without a recent list.
        let mut local = self.clone();
        local.move_recent_to_map();
        names.extend(ident_tbl_fold_name_order(local.current.iter().map(
            |(name, entries)| {
                (
                    name.as_str(),
                    entries.first().map_or(0, |(id, _)| id.stamp()),
                )
            },
        )));
        if let Some(opened) = &self.opened {
            let mut components: Vec<&str> =
                opened.components.keys().map(|name| name.as_str()).collect();
            components.sort_unstable();
            names.extend(components);
            opened.next.collect_fold_name_order(names);
        }
    }

    /// The local bindings that neither a later local binding nor an open
    /// shadows.
    pub fn visible_local_entries(&self) -> impl Iterator<Item = (&Ident, &T)> {
        let mut seen = HashSet::new();
        let mut shadowing_opens = Vec::new();
        let mut items = Vec::new();
        self.collect_visible_local_entries(&mut seen, &mut shadowing_opens, &mut items);
        items.into_iter()
    }

    /// `seen` holds the local names of shallower layers and `shadowing_opens`
    /// the opened tables above this layer; a local binding is visible when
    /// neither shadows its name. Opened tables are probed per local name
    /// rather than copied into `seen`, since they are much larger.
    fn collect_visible_local_entries<'a>(
        &'a self,
        seen: &mut HashSet<Name>,
        shadowing_opens: &mut Vec<&'a OpenedMap<(Ident, T, i32)>>,
        items: &mut Vec<(&'a Ident, &'a T)>,
    ) {
        // Newest first, so the first binding seen for a name is its latest.
        let recent = self.recent_entries();
        let mapped = self
            .current
            .values()
            .filter_map(|entries| entries.last().map(|(id, value)| (id, value)));
        for (id, value) in recent.chain(mapped) {
            let name = id.name_atom();
            if !shadowing_opens
                .iter()
                .any(|opened| opened.contains_key(&name))
                && seen.insert(name)
            {
                items.push((id, value));
            }
        }
        if let Some(opened) = &self.opened {
            shadowing_opens.push(&opened.components);
            opened
                .next
                .collect_visible_local_entries(seen, shadowing_opens, items);
        }
    }
}

impl<T: Clone> Default for IdTbl<T> {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Debug, Clone)]
struct TycompOpened<T> {
    components: Rc<OpenedMap<Vec<(Ident, T)>>>,
    next: Rc<TycompTbl<T>>,
    /// The open's `using` callback slot.
    slot: Option<u32>,
}

/// OCaml-shaped table for constructors and labels.
///
/// This mirrors `Env.TycompTbl`: local bindings are kept in `current`; opened
/// constructor/label buckets stay in symbolic `opened` layers and are returned
/// as lists.
#[derive(Debug, Clone)]
pub struct TycompTbl<T> {
    current: LayerMap<Name, IdBucket<T>>,
    /// Order in which each name of `current` was first added: the `Ident.add`
    /// sequence that shapes OCaml's AVL tree (compiler/ext/ident.ml:144-150).
    current_first_add: LayerMap<Name, i32>,
    opened: Option<Rc<TycompOpened<T>>>,
}

impl<T: Clone> TycompTbl<T> {
    /// An empty table.
    pub fn new() -> Self {
        Self {
            current: LayerMap::default(),
            current_first_add: LayerMap::default(),
            opened: None,
        }
    }

    /// Bind `id` to `value`, shadowing earlier bindings of its name.
    pub fn add(&mut self, id: Ident, value: T) {
        let key = id.name_atom();
        if self.current.contains_key(&key)
            && let Some(entries) = self.current.get_mut(&key)
        {
            entries.push(id, value);
        } else {
            let seq = self.current_first_add.len() as i32;
            self.current_first_add.insert(key, seq);
            self.current.insert(key, IdBucket::One([(id, value)]));
        }
    }

    /// Add the components of an opened module as a new layer; `slot`
    /// identifies the open for unused-open warnings.
    pub fn add_open_layer(&mut self, components: Vec<(Ident, T)>, slot: Option<u32>) {
        self.add_open_layer_table(Rc::new(tycomp_open_table(components)), slot);
    }

    /// Open a prebuilt layer table (possibly shared with other Envs).
    fn add_open_layer_table(
        &mut self,
        components: Rc<OpenedMap<Vec<(Ident, T)>>>,
        slot: Option<u32>,
    ) {
        if components.is_empty() {
            return;
        }
        let next = std::mem::take(self);
        *self = Self {
            current: LayerMap::default(),
            current_first_add: LayerMap::default(),
            opened: Some(Rc::new(TycompOpened {
                components,
                next: Rc::new(next),
                slot,
            })),
        };
    }

    /// The innermost binding of `name`.
    pub fn find_by_name(&self, name: impl crate::name::NameKey) -> Option<&T> {
        self.find_by_key(name.name_key()?)
    }

    fn find_by_key(&self, key: Name) -> Option<&T> {
        if !self.current.is_empty()
            && let Some((_, value)) = self.current.get(&key).and_then(|entries| entries.last())
        {
            return Some(value);
        }
        match &self.opened {
            Some(opened) => opened
                .components
                .get(&key)
                .and_then(|entries| entries.first())
                .map(|(_, value)| value)
                .or_else(|| opened.next.find_by_key(key)),
            None => None,
        }
    }

    /// The innermost binding of `name`, with its identifier and whether it is
    /// local rather than opened.
    pub fn find_by_name_with_origin(
        &self,
        name: impl crate::name::NameKey,
    ) -> Option<(&Ident, &T, bool)> {
        self.find_by_key_with_origin(name.name_key()?)
    }

    fn find_by_key_with_origin(&self, key: Name) -> Option<(&Ident, &T, bool)> {
        if let Some((id, value)) = self.current.get(&key).and_then(|entries| entries.last()) {
            return Some((id, value, true));
        }
        match &self.opened {
            Some(opened) => opened
                .components
                .get(&key)
                .and_then(|entries| entries.first())
                .map(|(id, value)| (id, value, false))
                .or_else(|| opened.next.find_by_key_with_origin(key)),
            None => None,
        }
    }

    /// The binding of exactly `id`.
    pub fn find_by_ident(&self, id: &Ident) -> Option<&T> {
        let stamp = id.stamp();
        if !self.current.is_empty()
            && let Some(value) = self.current.get(&id.name_atom()).and_then(|entries| {
                entries
                    .iter()
                    .rev()
                    .find(|(entry_id, _)| {
                        if stamp == 0 {
                            entry_id.is_persistent() && entry_id.name_atom() == id.name_atom()
                        } else {
                            entry_id.same(id) && entry_id.name_atom() == id.name_atom()
                        }
                    })
                    .map(|(_, value)| value)
            })
        {
            return Some(value);
        }
        self.opened
            .as_ref()
            .and_then(|opened| opened.next.find_by_ident(id))
    }

    /// Every binding of `name`, innermost first.
    pub fn find_all(&self, name: impl crate::name::NameKey) -> Vec<&T> {
        let mut items = Vec::new();
        if let Some(key) = name.name_key() {
            self.collect_all_key(key, &mut items);
        }
        items
    }

    fn collect_all_key<'a>(&'a self, key: Name, items: &mut Vec<&'a T>) {
        if let Some(entries) = self.current.get(&key) {
            items.extend(entries.iter().rev().map(|(_, value)| value));
        }
        if let Some(opened) = &self.opened {
            if let Some(entries) = opened.components.get(&key) {
                items.extend(entries.iter().map(|(_, value)| value));
            }
            opened.next.collect_all_key(key, items);
        }
    }

    /// R4 oracle: the stamps of `collect_all_key`'s candidates, in its order.
    #[cfg(debug_assertions)]
    fn trace_candidates(&self, key: Name, stamps: &mut Vec<i32>) {
        if let Some(entries) = self.current.get(&key) {
            stamps.extend(entries.iter().rev().map(|(id, _)| id.stamp()));
        }
        if let Some(opened) = &self.opened {
            if let Some(entries) = opened.components.get(&key) {
                stamps.extend(entries.iter().map(|(id, _)| id.stamp()));
            }
            opened.next.trace_candidates(key, stamps);
        }
    }

    /// OCaml `TycompTbl.find_all`: each candidate with the `mk_callback`
    /// data of its opened layer, `(slot, first hidden candidate)`.
    pub fn find_all_marking(
        &self,
        name: impl crate::name::NameKey,
    ) -> Vec<(&T, OpenSlotMark<'_, T>)> {
        let mut items: Vec<(&T, OpenSlotMark<'_, T>)> = Vec::new();
        let Some(key) = name.name_key() else {
            return items;
        };
        // Each layer's own entries, then its opened components, then the
        // layers below. An opened component's `hidden` value is the first
        // entry of the layers below it: the item emitted right after its
        // block, filled in once the walk is done.
        let mut opened_blocks: smallvec::SmallVec<[(usize, usize, u32); 4]> =
            smallvec::SmallVec::new();
        let mut table = self;
        loop {
            if let Some(entries) = table.current.get(&key) {
                items.extend(entries.iter().rev().map(|(_, value)| (value, None)));
            }
            let Some(opened) = &table.opened else {
                break;
            };
            if let Some(entries) = opened.components.get(&key) {
                let start = items.len();
                items.extend(entries.iter().map(|(_, value)| (value, None)));
                if let Some(slot) = opened.slot {
                    opened_blocks.push((start, items.len(), slot));
                }
            }
            table = opened.next.as_ref();
        }
        for (start, end, slot) in opened_blocks {
            let hidden = items.get(end).map(|(value, _)| *value);
            for item in &mut items[start..end] {
                item.1 = Some((slot, hidden));
            }
        }
        items
    }

    /// Every binding in the table.
    pub fn iter(&self) -> impl Iterator<Item = (&Ident, &T)> {
        let mut items = Vec::new();
        self.collect_iter(&mut items);
        items.into_iter()
    }

    fn collect_iter<'a>(&'a self, items: &mut Vec<(&'a Ident, &'a T)>) {
        for entries in self.current.values() {
            items.extend(entries.iter().map(|(id, value)| (id, value)));
        }
        if let Some(opened) = &self.opened {
            for entries in opened.components.values() {
                items.extend(entries.iter().map(|(id, value)| (id, value)));
            }
            opened.next.collect_iter(items);
        }
    }

    /// The names of the descriptions visited by OCaml `TycompTbl.fold_name`
    /// (compiler/ml/env.ml:221-228), in visit order.
    pub fn fold_name_order(&self) -> Vec<&str> {
        let mut names = Vec::new();
        self.collect_fold_name_order(&mut names);
        names
    }

    fn collect_fold_name_order<'a>(&'a self, names: &mut Vec<&'a str>) {
        names.extend(ident_tbl_fold_name_order(self.current.keys().map(|name| {
            (
                name.as_str(),
                self.current_first_add.get(name).copied().unwrap_or(0),
            )
        })));
        if let Some(opened) = &self.opened {
            let mut components: Vec<(&str, usize)> = opened
                .components
                .iter()
                .map(|(name, entries)| (name.as_str(), entries.len()))
                .collect();
            components.sort_unstable();
            for (name, count) in components {
                // `List.fold_right (fun desc -> f desc)` visits every
                // description of the bucket.
                names.extend(std::iter::repeat_n(name, count));
            }
            opened.next.collect_fold_name_order(names);
        }
    }
}

impl<T: Clone> Default for TycompTbl<T> {
    fn default() -> Self {
        Self::new()
    }
}

// ============================================================================
// The Environment
// ============================================================================

/// Process-wide allocator of per-thread Env id blocks.
///
/// Env ids only need to be unique; they are compared for equality (abbreviation
/// memo validity, `TypeContext` lookup-cache keys) and never ordered. Every
/// `Env` mutation allocates a fresh id, which in an in-process build happens
/// millions of times from every worker thread at once. A single shared
/// counter turns each mutation into a contended cache-line transfer, so each
/// thread instead claims a 2^40-id block once and hands out ids from that
/// block without touching shared memory.
static NEXT_ENV_ID_BLOCK: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(1);

const ENV_ID_BLOCK_SHIFT: u32 = 40;

thread_local! {
    /// Next id to hand out on this thread; `0` means no block claimed yet.
    static NEXT_ENV_ID: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
}

#[inline]
fn next_env_id() -> u64 {
    NEXT_ENV_ID.with(|next| {
        let mut id = next.get();
        if id == 0 {
            let block = NEXT_ENV_ID_BLOCK.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            id = block << ENV_ID_BLOCK_SHIFT;
        }
        next.set(id + 1);
        id
    })
}

/// Memo tables derived from an Env's module bindings (see `Env::scope_caches`).
///
/// Intentional Rust performance caches: OCaml walks the current Env tables
/// when resolving module components (compiler/ml/env.ml:781-813, 1516-1538).
/// Both tables stay derived from bindings only; they must not become a
/// path-spelling alias-equivalence shortcut.
#[derive(Debug, Default)]
struct ScopeCaches {
    /// Active local module aliases.
    local_module_aliases: RefCell<Option<Vec<(Ident, Path)>>>,
    /// Whether a module path needs an env-scoped component cache key.
    module_path_requires_env_scoped: RefCell<HashMap<String, bool>>,
}

/// Opaque identity of an environment snapshot. Only equality and hashing matter.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct EnvId(u64);

/// Opaque identity of the bindings used by module-path resolution.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ScopeId(u64);

/// The typing environment.
///
/// This tracks all bindings visible during type checking.
/// The environment is immutable - extending it creates a new environment.
#[derive(Debug)]
pub struct Env {
    /// Identity of this environment version, shared by unchanged clones.
    /// Incremented when bindings are added, to detect env changes.
    id: u64,

    /// Identity of the bindings that module-path resolution reads: modules
    /// and their component tables, module types, types, opens, functor
    /// arguments, and local constraints. Unlike `id`, clones keep it and
    /// value/constructor/label bindings do not change it, so caches of
    /// resolved dotted paths stay valid across ordinary `let` bindings.
    scope_id: u64,

    /// Bindings and derived tables, shared copy-on-write between the
    /// snapshots and clones of one logical environment. Cloning or dropping
    /// an Env touches one reference count instead of one per table.
    data: std::rc::Rc<EnvData>,
}

#[derive(Debug, Clone)]
struct EnvData {
    /// Value bindings.
    values: IdTbl<Arc<ValueDescription>>,

    /// Type bindings.
    types: IdTbl<Arc<TypeDeclaration>>,

    /// Constructor bindings (for variant types).
    constrs: TycompTbl<Arc<ConstructorDescription>>,

    /// Label bindings (for record fields).
    labels: TycompTbl<Arc<LabelDescription>>,

    /// Module bindings.
    modules: IdTbl<Arc<ModuleDeclaration>>,

    /// Lazily-forced qualified component views for local module bindings.
    /// This mirrors OCaml's `env.components` table for local `Pident` paths.
    module_components: IdTbl<Rc<super::env_lazy::StoredModuleComponents>>,

    /// Module type bindings.
    modtypes: IdTbl<Arc<ModtypeDeclaration>>,

    /// Module identifiers that are functor parameters.
    /// Mirrors OCaml `Env.functor_args` and drives aliasability checks.
    functor_args: HashSet<Ident>,

    /// Memo tables derived from the module bindings. They are shared by every
    /// clone with the same `scope_id` and replaced whenever the scope changes.
    scope_caches: std::rc::Rc<ScopeCaches>,

    /// Persistent roots opened by the initial environment.
    ///
    /// OCaml compiler/core/res_compmisc.ml:48-63 installs implicit opens before
    /// typechecking source items. `Env.normalize_path` can still force those
    /// roots through compiler/ml/env.ml:865-875 because no source open selected
    /// them. Source-level opens use the same component tables but should not be
    /// classified as initial-env roots.
    implicit_open_roots: PersistentHashSet<String>,

    /// Local constraints (for GADTs).
    local_constraints: PersistentHashMap<Path, Arc<TypeDeclaration>>,

    /// The label array `store_type` described with each local record type
    /// (compiler/ml/env.ml:1561-1569 stores `(decl, (constructors, labels))`
    /// in `env.types`): what `find_type_descrs (Pident id)` returns.
    type_label_families: PersistentHashMap<Ident, super::decl::LabelArrayRef>,

    /// Environment flags.
    flags: EnvFlags,
}

impl Clone for Env {
    fn clone(&self) -> Self {
        Env {
            // A clone is the same version until either copy is extended.
            id: self.id,
            scope_id: self.scope_id,
            data: self.data.clone(),
        }
    }
}

/// Environment flags.
#[derive(Debug, Clone, Copy, Default)]
pub struct EnvFlags {
    /// `in_signature_flag` (env.ml:388).
    pub in_signature: bool,
    /// `implicit_coercion_flag` (env.ml:389).
    pub implicit_coercion: bool,
}

impl Env {
    /// Bindings for mutation, copying them first when another Env shares them.
    #[inline]
    fn data_mut(&mut self) -> &mut EnvData {
        std::rc::Rc::make_mut(&mut self.data)
    }

    /// `Env.implicit_coercion env` (env.ml:502-503).
    pub fn implicit_coercion(&self) -> Env {
        let mut env = self.clone();
        env.bump_id();
        env.data_mut().flags.implicit_coercion = true;
        env
    }

    /// `Env.is_in_signature` (env.ml:505).
    pub fn is_in_signature(&self) -> bool {
        self.data.flags.in_signature
    }

    /// `Env.is_implicit_coercion` (env.ml:506).
    pub fn is_implicit_coercion(&self) -> bool {
        self.data.flags.implicit_coercion
    }

    /// Create an empty environment.
    pub fn empty() -> Self {
        // Cloning shares the empty version and its persistent-map roots.
        thread_local! {
            static EMPTY_ENV: Env = Env::build_empty();
        }
        EMPTY_ENV.with(Env::clone)
    }

    fn build_empty() -> Self {
        let id = next_env_id();
        Env {
            id,
            scope_id: id,
            data: std::rc::Rc::new(EnvData {
                values: IdTbl::new(),
                types: IdTbl::new(),
                constrs: TycompTbl::new(),
                labels: TycompTbl::new(),
                modules: IdTbl::new(),
                module_components: IdTbl::new(),
                modtypes: IdTbl::new(),
                functor_args: HashSet::new(),
                scope_caches: std::rc::Rc::default(),
                implicit_open_roots: PersistentHashSet::default(),
                local_constraints: PersistentHashMap::default(),
                type_label_families: PersistentHashMap::default(),
                flags: EnvFlags::default(),
            }),
        }
    }

    /// OCaml `IdTbl.find_name ~mark:true` usage of an unqualified source
    /// name in the table `kind` selects.
    pub(crate) fn open_slot_use(
        &self,
        kind: OpenLookupKind,
        name: impl crate::name::NameKey,
    ) -> Option<OpenSlotUse> {
        let name = name.name_key()?;
        match kind {
            OpenLookupKind::Value => self.data.values.open_slot_use(name),
            OpenLookupKind::Type => self.data.types.open_slot_use(name),
            OpenLookupKind::Module => self.data.modules.open_slot_use(name),
            OpenLookupKind::Component => self.data.module_components.open_slot_use(name),
            OpenLookupKind::Modtype => self.data.modtypes.open_slot_use(name),
        }
    }

    /// OCaml `TycompTbl.find_all` for constructors, with each candidate's
    /// `mk_callback` data `(slot, first hidden candidate)`.
    pub(crate) fn find_all_constructors_marking(
        &self,
        name: &str,
    ) -> Vec<(
        &ConstructorDescription,
        OpenSlotMark<'_, ConstructorDescription>,
    )> {
        #[cfg(debug_assertions)]
        self.trace_lookup(crate::tc::scope_trace::Ns::Constructor, name, true);
        self.data
            .constrs
            .find_all_marking(name)
            .into_iter()
            .map(|(desc, mark)| {
                (
                    desc.as_ref(),
                    mark.map(|(slot, hidden)| (slot, hidden.map(|h| h.as_ref()))),
                )
            })
            .collect()
    }

    /// OCaml `TycompTbl.find_all` for labels, with `mk_callback` data.
    pub(crate) fn find_all_labels_marking(
        &self,
        name: &str,
    ) -> Vec<(&LabelDescription, OpenSlotMark<'_, LabelDescription>)> {
        #[cfg(debug_assertions)]
        self.trace_lookup(crate::tc::scope_trace::Ns::Label, name, true);
        self.data
            .labels
            .find_all_marking(name)
            .into_iter()
            .map(|(desc, mark)| {
                (
                    desc.as_ref(),
                    mark.map(|(slot, hidden)| (slot, hidden.map(|h| h.as_ref()))),
                )
            })
            .collect()
    }

    /// Identity of this environment version.
    pub fn id(&self) -> EnvId {
        EnvId(self.id)
    }

    /// Mark this environment as changed.
    fn bump_id(&mut self) {
        #[cfg(debug_assertions)]
        let from = self.id;
        self.id = next_env_id();
        #[cfg(debug_assertions)]
        if crate::tc::scope_trace::on() {
            crate::tc::scope_trace::push(crate::tc::scope_trace::Event::Version { from, to: self.id });
        }
    }

    /// R4 oracle: report a binding this version added. One thread-local load
    /// while no capture runs; absent from a release build.
    #[cfg(debug_assertions)]
    fn trace_bind(&self, ns: crate::tc::scope_trace::Ns, id: &Ident) {
        if crate::tc::scope_trace::on() {
            crate::tc::scope_trace::push(crate::tc::scope_trace::Event::Bind {
                env: self.id,
                ns,
                name: id.name(),
                stamp: id.stamp(),
            });
        }
    }

    /// R4 oracle: report a lookup by name with the stamps it finds, by a
    /// second read of the same table. O(candidates) while a capture runs,
    /// one thread-local load otherwise; absent from a release build.
    #[cfg(debug_assertions)]
    fn trace_lookup(&self, ns: crate::tc::scope_trace::Ns, name: impl crate::name::NameKey, all: bool) {
        use crate::tc::scope_trace::Ns;
        if !crate::tc::scope_trace::on() {
            return;
        }
        let mut found = Vec::new();
        let first = |entry: Option<&Ident>, found: &mut Vec<i32>| found.extend(entry.map(Ident::stamp));
        match ns {
            Ns::Value => first(self.data.values.find_by_name_with_id(name).map(|e| e.0), &mut found),
            Ns::Type => first(self.data.types.find_by_name_with_id(name).map(|e| e.0), &mut found),
            Ns::Module => first(self.data.modules.find_by_name_with_id(name).map(|e| e.0), &mut found),
            Ns::ModuleType => first(self.data.modtypes.find_by_name_with_id(name).map(|e| e.0), &mut found),
            Ns::Constructor => {
                if let Some(key) = name.name_key() {
                    self.data.constrs.trace_candidates(key, &mut found);
                }
            }
            Ns::Label => {
                if let Some(key) = name.name_key() {
                    self.data.labels.trace_candidates(key, &mut found);
                }
            }
        }
        if !all {
            found.truncate(1);
        }
        crate::tc::scope_trace::push(crate::tc::scope_trace::Event::Lookup {
            env: self.id,
            ns,
            name: name.text().to_string(),
            all,
            found,
        });
    }

    /// Mark a change to the bindings that module-path resolution reads.
    fn bump_scope(&mut self) {
        self.bump_id();
        self.scope_id = self.id;
        self.data_mut().scope_caches = std::rc::Rc::default();
    }

    /// Identity of the module-level bindings (see the `scope_id` field).
    pub fn scope_id(&self) -> ScopeId {
        ScopeId(self.scope_id)
    }

    fn invalidate_module_alias_caches(&mut self) {
        // These caches are purely derived from visible bindings. Every Env
        // mutation that can change OCaml component lookup visibility must drop
        // them before later lookups rebuild the same derived view. Clones that
        // still share the previous scope keep the previous tables.
        self.data_mut().scope_caches = std::rc::Rc::default();
    }

    fn path_has_prefix(path: &Path, prefix: &Path) -> bool {
        if path.same(prefix) {
            return true;
        }
        match path.view() {
            PathView::Pdot(parent, _, _) => Self::path_has_prefix(parent, prefix),
            PathView::Pident(_) | PathView::Papply(_, _) => false,
        }
    }

    fn module_path_scope_cache_key(path: &Path) -> Option<String> {
        // Match `Path.flatten` in compiler/ml/path.ml:63-69: any nested
        // `Papply` is `Contains_apply`, so env-scoped cache keys that need a
        // single head identifier are only valid for regular dotted paths.
        let (head, _) = path.flatten().ok()?;
        let name = path.name();
        if head.is_persistent() || head.stamp() == 0 {
            Some(name)
        } else {
            Some(format!("{name}#{}", head.stamp()))
        }
    }

    pub(crate) fn with_current_local_module_aliases<R>(
        &self,
        f: impl FnOnce(&[(Ident, Path)]) -> R,
    ) -> R {
        if self
            .data
            .scope_caches
            .local_module_aliases
            .borrow()
            .is_none()
        {
            let mut aliases: Vec<_> = self
                .data
                .modules
                .visible_local_entries()
                .filter_map(|(id, decl)| match &decl.md_type {
                    ModuleType::MtyAlias(..) | ModuleType::MtyIdent(_) => {
                        let target = decl.md_type.ident_or_alias_path().unwrap();
                        Some((*id, *target))
                    }
                    _ => None,
                })
                .collect();
            aliases.sort_by(|(left_id, left_target), (right_id, right_target)| {
                right_target
                    .name()
                    .len()
                    .cmp(&left_target.name().len())
                    .then_with(|| right_target.name().cmp(&left_target.name()))
                    .then_with(|| right_id.stamp().cmp(&left_id.stamp()))
            });
            *self.data.scope_caches.local_module_aliases.borrow_mut() = Some(aliases);
        }

        let cache = self.data.scope_caches.local_module_aliases.borrow();
        f(cache.as_deref().unwrap_or(&[]))
    }

    pub(crate) fn module_path_requires_env_scoped_cache(&self, module_path: &Path) -> bool {
        if module_path.head().is_persistent() {
            return false;
        }

        let Some(cache_key) = Self::module_path_scope_cache_key(module_path) else {
            return false;
        };

        if let Some(cached) = self
            .data
            .scope_caches
            .module_path_requires_env_scoped
            .borrow()
            .get(&cache_key)
            .copied()
        {
            return cached;
        }

        let requires = self.with_current_local_module_aliases(|aliases| {
            aliases.iter().any(|(_, target_path)| {
                let target_head = target_path.head();
                self.has_module_ident(target_head)
                    && Self::path_has_prefix(module_path, target_path)
            })
        });
        self.data
            .scope_caches
            .module_path_requires_env_scoped
            .borrow_mut()
            .insert(cache_key, requires);
        requires
    }

    // ========================================================================
    // Value Bindings
    // ========================================================================

    /// Add a value binding.
    pub fn add_value(&mut self, id: Ident, desc: ValueDescription) {
        self.bump_id();
        #[cfg(debug_assertions)]
        self.trace_bind(crate::tc::scope_trace::Ns::Value, &id);
        let desc = Arc::new(desc);
        self.data_mut().values.add(id, desc);
    }

    /// Find a value by name.
    pub fn find_value(&self, name: impl crate::name::NameKey) -> EnvResult<&ValueDescription> {
        #[cfg(debug_assertions)]
        self.trace_lookup(crate::tc::scope_trace::Ns::Value, name, false);
        self.data
            .values
            .find_by_name(name)
            .map(|v| v.as_ref())
            .ok_or_else(|| EnvError::ValueNotFound(name.text().into()))
    }

    /// Find a value by name, returning both the identifier and description.
    pub fn find_value_with_id(&self, name: impl crate::name::NameKey) -> EnvResult<(&Ident, &ValueDescription)> {
        #[cfg(debug_assertions)]
        self.trace_lookup(crate::tc::scope_trace::Ns::Value, name, false);
        self.data
            .values
            .find_by_name_with_id(name)
            .map(|(id, v)| (id, v.as_ref()))
            .ok_or_else(|| EnvError::ValueNotFound(name.text().into()))
    }

    /// Find a value and its local or opened path, sharing the stored description.
    pub fn find_value_arc_with_path(
        &self,
        name: impl crate::name::NameKey,
    ) -> EnvResult<(Path, &Arc<ValueDescription>)> {
        #[cfg(debug_assertions)]
        self.trace_lookup(crate::tc::scope_trace::Ns::Value, name, false);
        self.data
            .values
            .find_by_name_with_path(name)
            .ok_or_else(|| EnvError::ValueNotFound(name.text().into()))
    }

    /// Iterate over visible value bindings.
    pub fn iter_values(&self) -> impl Iterator<Item = (&Ident, &ValueDescription)> {
        self.data.values.iter().map(|(id, v)| (id, v.as_ref()))
    }

    /// Update the visible value binding for `name` with a replacement type.
    /// This replaces the current binding in-place rather than adding a shadowing entry.
    pub fn update_value_type_by_name(&mut self, name: &str, new_type: TypeExprRef) -> bool {
        let mut update = |desc: &Arc<ValueDescription>| {
            let mut updated = (**desc).clone();
            updated.val_type = new_type;
            Arc::new(updated)
        };
        if self
            .data_mut()
            .values
            .update_by_name(name, &mut update)
            .is_none()
        {
            return false;
        }

        self.bump_id();
        true
    }

    /// Find a value by path.
    pub fn lookup_value(&self, path: &Path) -> EnvResult<&ValueDescription> {
        match path.view() {
            PathView::Pident(id) => self
                .data
                .values
                .find_by_ident(id)
                .map(|v| v.as_ref())
                .ok_or_else(|| EnvError::ValueNotFound(id.name().into())),
            PathView::Pdot(_, name, _) => self.find_value(name),
            PathView::Papply(_, _) => Err(EnvError::ValueNotFound("(functor application)".into())),
        }
    }

    // ========================================================================
    // Type Bindings
    // ========================================================================

    /// Add a type binding.
    /// Add a type binding without describing its labels: OCaml
    /// `store_type_infos` (env.ml:1605-1612), what `components_of_module_maker`
    /// uses (env.ml:1488), or an abstract placeholder. A previous binding of
    /// `id` loses its labels' array. Use [`Env::store_type`] for `Env.add_type`.
    pub fn add_type(&mut self, id: Ident, decl: impl Into<Arc<TypeDeclaration>>) {
        self.bump_scope();
        #[cfg(debug_assertions)]
        self.trace_bind(crate::tc::scope_trace::Ns::Type, &id);
        let decl = decl.into();
        let data = self.data_mut();
        data.types.add(id, decl);
        data.type_label_families.remove(&id);
    }

    /// OCaml `Env.add_type` = `store_type` (env.ml:1561-1569, 1701): the
    /// binding plus the labels `Datarepr.labels_of_type (Pident id) decl`
    /// describes for a record, added with `List.fold_right`. Constructors
    /// are added by the callers that need them.
    pub fn store_type(
        &mut self,
        ctx: &TypeContext,
        id: Ident,
        decl: impl Into<Arc<TypeDeclaration>>,
    ) {
        let decl = decl.into();
        self.add_type(id, decl.clone());
        if let TypeKind::TypeRecord(labels, _) = &decl.type_kind
            && !labels.is_empty()
        {
            let res_ty = ctx.new_generic_constr(Path::pident(id), decl.type_params.clone());
            let descs = crate::types::env_lazy::label_descrs(
                res_ty,
                &decl,
                decl.type_private,
                ctx,
                |_| {},
            );
            self.add_type_label_family(id, descs[0].lbl_all);
            for (ld, desc) in labels.iter().zip(descs).rev() {
                self.add_label(ld.ld_id, desc);
            }
        }
    }

    /// Rebind the type `id` with its declaration's `type_variance` replaced
    /// by `variance`, keeping its labels and their array (labels do not
    /// describe variance). Returns the new declaration, or `None` when `id`
    /// is not bound.
    pub fn update_type_variance(
        &mut self,
        id: Ident,
        variance: Vec<super::variance::Variance>,
    ) -> Option<Arc<TypeDeclaration>> {
        let mut decl = self.find_type_arc_by_ident(&id)?.as_ref().clone();
        decl.type_variance = variance;
        let decl = Arc::new(decl);
        self.bump_scope();
        #[cfg(debug_assertions)]
        self.trace_bind(crate::tc::scope_trace::Ns::Type, &id);
        self.data_mut().types.add(id, decl.clone());
        Some(decl)
    }

    /// Find a type by name.
    pub fn find_type(&self, name: impl crate::name::NameKey) -> EnvResult<&TypeDeclaration> {
        #[cfg(debug_assertions)]
        self.trace_lookup(crate::tc::scope_trace::Ns::Type, name, false);
        self.data
            .types
            .find_by_name(name)
            .map(|t| t.as_ref())
            .ok_or_else(|| EnvError::TypeNotFound(name.text().into()))
    }

    /// Find a type by name with the path selected by OCaml `IdTbl.find_name`.
    ///
    /// Local bindings resolve to `Pident(id)`, while opened bindings resolve to
    /// `Pdot(root, name, pos)` from the symbolic open layer.
    pub fn find_type_with_path(&self, name: impl crate::name::NameKey) -> EnvResult<(Path, &TypeDeclaration)> {
        #[cfg(debug_assertions)]
        self.trace_lookup(crate::tc::scope_trace::Ns::Type, name, false);
        self.data
            .types
            .find_by_name_with_path(name)
            .map(|(path, decl)| (path, decl.as_ref()))
            .ok_or_else(|| EnvError::TypeNotFound(name.text().into()))
    }

    /// Like `find_type_with_path`, sharing the stored declaration.
    pub fn find_type_arc_with_path(
        &self,
        name: impl crate::name::NameKey,
    ) -> EnvResult<(Path, &Arc<TypeDeclaration>)> {
        #[cfg(debug_assertions)]
        self.trace_lookup(crate::tc::scope_trace::Ns::Type, name, false);
        self.data
            .types
            .find_by_name_with_path(name)
            .ok_or_else(|| EnvError::TypeNotFound(name.text().into()))
    }

    /// The name list OCaml builds with `Env.fold_types (fun x _ _ xs -> x :: xs)
    /// None env []` (compiler/ml/env.ml:1932-1937, 2001).
    pub fn fold_type_names(&self) -> Vec<String> {
        fold_names_list(self.data.types.fold_name_order())
    }

    /// `Env.fold_values` with no module prefix (compiler/ml/env.ml:1992).
    pub fn fold_value_names(&self) -> Vec<String> {
        fold_names_list(self.data.values.fold_name_order())
    }

    /// `Env.fold_modules` over `env.modules` (compiler/ml/env.ml:1962-1970).
    pub fn fold_module_names(&self) -> Vec<String> {
        fold_names_list(self.data.modules.fold_name_order())
    }

    /// `Env.fold_modtypes` with no module prefix (compiler/ml/env.ml:2003).
    pub fn fold_modtype_names(&self) -> Vec<String> {
        fold_names_list(self.data.modtypes.fold_name_order())
    }

    /// `Env.fold_constructors` with no module prefix (compiler/ml/env.ml:1995).
    pub fn fold_constructor_names(&self) -> Vec<String> {
        fold_names_list(self.data.constrs.fold_name_order())
    }

    /// `Env.fold_labels` with no module prefix (compiler/ml/env.ml:1998).
    pub fn fold_label_names(&self) -> Vec<String> {
        fold_names_list(self.data.labels.fold_name_order())
    }

    pub(crate) fn find_type_by_ident(&self, id: &Ident) -> EnvResult<&TypeDeclaration> {
        // OCaml compiler/ml/env.ml:800-813 dispatches Pident type lookup to
        // `IdTbl.find_same`, so same-name bindings must not be treated as an
        // exact hit when expanding a constructor path by identifier.
        self.data
            .types
            .find_by_ident(id)
            .map(|t| t.as_ref())
            .ok_or_else(|| EnvError::TypeNotFound(id.name().into()))
    }

    /// Shared-declaration form of [`Env::find_type_by_ident`].
    pub(crate) fn find_type_arc_by_ident(&self, id: &Ident) -> Option<&Arc<TypeDeclaration>> {
        self.data.types.find_by_ident(id)
    }

    /// Shared-declaration form of [`Env::lookup_type`] for `Pident` paths.
    pub(crate) fn lookup_type_arc_by_ident(&self, id: &Ident) -> Option<&Arc<TypeDeclaration>> {
        self.data
            .types
            .find_by_ident(id)
            .or_else(|| self.data.types.find_by_name(id.name_atom()))
    }

    /// Find a type by path.
    pub fn lookup_type(&self, path: &Path) -> EnvResult<&TypeDeclaration> {
        match path.view() {
            PathView::Pident(id) => self
                .data
                .types
                .find_by_ident(id)
                .or_else(|| {
                    // Some in-process callers still pass copied signature ids
                    // whose stamp does not match the current table entry. Keep
                    // the existing recovery here; expansion paths that must
                    // mirror OCaml `IdTbl.find_same` use
                    // `lookup_type_ident_exact` instead
                    // (compiler/ml/env.ml:800-813,862).
                    self.data.types.find_by_name(id.name_atom())
                })
                .map(|t| t.as_ref())
                .ok_or_else(|| EnvError::TypeNotFound(id.name().into())),
            PathView::Pdot(parent, name, _) => {
                // Try to find the type through the parent module's signature first.
                // Follow MtyIdent/MtyAlias to resolve the module type to a signature.
                if let Ok(parent_md) = self.lookup_module(parent) {
                    // Search parent module's signature for the type
                    fn find_type_in_module_type<'a>(
                        env: &'a Env,
                        mty: &'a super::decl::ModuleType,
                        name: &str,
                        depth: usize,
                    ) -> Option<&'a super::decl::TypeDeclaration> {
                        if depth > 10 {
                            return None;
                        }
                        match mty {
                            super::decl::ModuleType::MtySignature(sig) => {
                                for item in sig.iter() {
                                    if let super::decl::SignatureItem::SigType(id, decl, _) = item {
                                        if id.name() == name {
                                            return Some(decl);
                                        }
                                    }
                                }
                                None
                            }
                            super::decl::ModuleType::MtyIdent(_)
                            | super::decl::ModuleType::MtyAlias(..) => {
                                let type_path = mty.ident_or_alias_path().unwrap();
                                if let Ok(mtd) = env.lookup_modtype(type_path) {
                                    if let Some(resolved) = &mtd.mtd_type {
                                        return find_type_in_module_type(
                                            env,
                                            resolved,
                                            name,
                                            depth + 1,
                                        );
                                    }
                                }
                                if let Ok(md) = env.lookup_module(type_path) {
                                    return find_type_in_module_type(
                                        env,
                                        &md.md_type,
                                        name,
                                        depth + 1,
                                    );
                                }
                                None
                            }
                            _ => None,
                        }
                    }
                    if let Some(decl) = find_type_in_module_type(self, &parent_md.md_type, name, 0)
                    {
                        return Ok(decl);
                    }
                }
                // Fallback to name-based lookup
                self.find_type(name)
            }
            PathView::Papply(_, _) => Err(EnvError::TypeNotFound("(functor application)".into())),
        }
    }

    // ========================================================================
    // Constructor Bindings
    // ========================================================================

    /// Add a constructor binding.
    pub fn add_constructor(&mut self, id: Ident, desc: ConstructorDescription) {
        self.bump_id();
        #[cfg(debug_assertions)]
        self.trace_bind(crate::tc::scope_trace::Ns::Constructor, &id);
        let desc = Arc::new(desc);
        self.data_mut().constrs.add(id, desc);
    }

    /// Find a constructor by name.
    pub fn find_constructor(&self, name: impl crate::name::NameKey) -> EnvResult<&ConstructorDescription> {
        #[cfg(debug_assertions)]
        self.trace_lookup(crate::tc::scope_trace::Ns::Constructor, name, false);
        self.data
            .constrs
            .find_by_name(name)
            .map(|c| c.as_ref())
            .ok_or_else(|| EnvError::ConstructorNotFound(name.text().into()))
    }

    /// Find all constructors with a given name.
    pub fn find_all_constructors(&self, name: impl crate::name::NameKey) -> Vec<&ConstructorDescription> {
        #[cfg(debug_assertions)]
        self.trace_lookup(crate::tc::scope_trace::Ns::Constructor, name, true);
        self.data
            .constrs
            .find_all(name)
            .into_iter()
            .map(|c| c.as_ref())
            .collect()
    }

    // ========================================================================
    // Label Bindings
    // ========================================================================

    /// Add a label binding.
    pub fn add_label(&mut self, id: Ident, desc: LabelDescription) {
        self.bump_id();
        #[cfg(debug_assertions)]
        self.trace_bind(crate::tc::scope_trace::Ns::Label, &id);
        let desc = Arc::new(desc);
        self.data_mut().labels.add(id, desc);
    }

    /// Record that the labels installed for the record type `id` share the
    /// array `lbl_all` (the labels half of `store_type`, env.ml:1561-1569).
    pub fn add_type_label_family(&mut self, id: Ident, lbl_all: super::decl::LabelArrayRef) {
        self.bump_id();
        self.data_mut().type_label_families.insert(id, lbl_all);
    }

    /// `snd (find_type_descrs (Pident id))` of a record type: the array its
    /// labels were installed with.
    pub fn type_label_family(&self, id: &Ident) -> Option<super::decl::LabelArrayRef> {
        self.data.type_label_families.get(id).copied()
    }

    /// Find a label by name.
    pub fn find_label(&self, name: impl crate::name::NameKey) -> EnvResult<&LabelDescription> {
        #[cfg(debug_assertions)]
        self.trace_lookup(crate::tc::scope_trace::Ns::Label, name, false);
        self.data
            .labels
            .find_by_name(name)
            .map(|l| l.as_ref())
            .ok_or_else(|| EnvError::LabelNotFound(name.text().into()))
    }

    /// Find all labels with a given name.
    pub fn find_all_labels(&self, name: impl crate::name::NameKey) -> Vec<&LabelDescription> {
        #[cfg(debug_assertions)]
        self.trace_lookup(crate::tc::scope_trace::Ns::Label, name, true);
        self.data
            .labels
            .find_all(name)
            .into_iter()
            .map(|l| l.as_ref())
            .collect()
    }

    // ========================================================================
    // Module Bindings
    // ========================================================================

    pub(crate) fn add_module_with_component_path(
        &mut self,
        id: Ident,
        decl: ModuleDeclaration,
        component_path: Path,
    ) {
        self.add_module_with_component_context(id, decl.clone(), decl, component_path, None);
    }

    pub(crate) fn add_module_with_component_context(
        &mut self,
        id: Ident,
        decl: ModuleDeclaration,
        component_decl: ModuleDeclaration,
        component_path: Path,
        parent_context: Option<(Path, Arc<Signature>)>,
    ) {
        let seed_env = self.clone();
        let stored_components = Rc::new(
            super::env_lazy::StoredModuleComponents::new_with_parent_context(
                seed_env,
                component_path,
                component_decl,
                parent_context,
            ),
        );
        self.bump_scope();
        self.invalidate_module_alias_caches();
        #[cfg(debug_assertions)]
        self.trace_bind(crate::tc::scope_trace::Ns::Module, &id);
        let decl = Arc::new(decl);
        self.data_mut().modules.add(id, decl);
        self.data_mut().module_components.add(id, stored_components);
    }

    /// Add a module binding.
    pub fn add_module(&mut self, id: Ident, decl: ModuleDeclaration) {
        self.add_module_with_component_path(id, decl, Path::pident(id));
    }

    /// Add a functor-parameter module binding.
    pub fn add_module_arg(&mut self, id: Ident, decl: ModuleDeclaration) {
        self.add_module(id, decl);
        // `add_module` above already started a new scope.
        self.data_mut().functor_args.insert(id);
    }

    /// Check whether a module path is rooted in a functor parameter.
    pub fn is_functor_arg_path(&self, path: &Path) -> bool {
        match path.view() {
            PathView::Pident(id) => self.data.functor_args.contains(id),
            PathView::Pdot(parent, _, _) => self.is_functor_arg_path(parent),
            PathView::Papply(_, _) => true,
        }
    }

    /// Open `layers` (the component tables of one signature) under `root`.
    pub(crate) fn add_prebuilt_open_layers(
        &mut self,
        root: Path,
        layers: &OpenedLayers,
        slot: Option<u32>,
    ) {
        if layers.is_empty() {
            return;
        }
        self.bump_scope();
        #[cfg(debug_assertions)]
        if crate::tc::scope_trace::on() {
            crate::tc::scope_trace::push(crate::tc::scope_trace::Event::Open {
                env: self.id,
                members: layers.trace_members(),
            });
        }
        self.invalidate_module_alias_caches();
        let root = Arc::new(root);
        let data = self.data_mut();
        data.values
            .add_open_layer_table(root.clone(), layers.values.clone(), slot);
        data.types
            .add_open_layer_table(root.clone(), layers.types.clone(), slot);
        data.constrs
            .add_open_layer_table(layers.constrs.clone(), slot);
        data.labels
            .add_open_layer_table(layers.labels.clone(), slot);
        data.modules
            .add_open_layer_table(root.clone(), layers.modules.clone(), slot);
        data.module_components.add_open_layer_table(
            root.clone(),
            layers.module_components.clone(),
            slot,
        );
        data.modtypes
            .add_open_layer_table(root, layers.modtypes.clone(), slot);
    }

    /// Find a module by name.
    pub fn find_module(&self, name: impl crate::name::NameKey) -> EnvResult<&ModuleDeclaration> {
        #[cfg(debug_assertions)]
        self.trace_lookup(crate::tc::scope_trace::Ns::Module, name, false);
        self.data
            .modules
            .find_by_name(name)
            .map(|m| m.as_ref())
            .ok_or_else(|| EnvError::ModuleNotFound(name.text().into()))
    }

    /// Find a module by name, returning both the identifier and declaration.
    pub fn find_module_with_id(&self, name: impl crate::name::NameKey) -> EnvResult<(&Ident, &ModuleDeclaration)> {
        #[cfg(debug_assertions)]
        self.trace_lookup(crate::tc::scope_trace::Ns::Module, name, false);
        self.data
            .modules
            .find_by_name_with_id(name)
            .map(|(id, m)| (id, m.as_ref()))
            .ok_or_else(|| EnvError::ModuleNotFound(name.text().into()))
    }

    /// Find a module by name with the path selected by OCaml `IdTbl.find_name`.
    ///
    /// Local bindings resolve to `Pident(id)`, while opened bindings resolve to
    /// `Pdot(root, name, pos)` from the symbolic open layer.
    pub fn find_module_with_path(&self, name: impl crate::name::NameKey) -> EnvResult<(Path, &ModuleDeclaration)> {
        #[cfg(debug_assertions)]
        self.trace_lookup(crate::tc::scope_trace::Ns::Module, name, false);
        self.data
            .modules
            .find_by_name_with_path(name)
            .map(|(path, decl)| (path, decl.as_ref()))
            .ok_or_else(|| EnvError::ModuleNotFound(name.text().into()))
    }

    fn first_dotted_component_path(path: &Path) -> Option<Path> {
        match path.view() {
            PathView::Pdot(parent, name, pos) => match parent.view() {
                PathView::Pident(_) => Some(Path::pdot_pos(*parent, *name, *pos)),
                _ => Self::first_dotted_component_path(parent),
            },
            PathView::Pident(_) | PathView::Papply(_, _) => None,
        }
    }

    pub(crate) fn path_starts_with_opened_component(&self, path: &Path) -> bool {
        // OCaml compiler/core/res_compmisc.ml:56-62 installs implicit opens
        // through Env.open_signature; compiler/ml/env.ml:1874-1877 adds the
        // opened components without a root module binding. Detect those
        // component-origin paths from the Env binding itself, not by spelling
        // roots such as `Stdlib` or `Pervasives`.
        let Some(component_path) = Self::first_dotted_component_path(path) else {
            return false;
        };
        self.find_module_with_path(component_path.last())
            .ok()
            .is_some_and(|(selected_path, _)| selected_path.same(&component_path))
    }

    pub(crate) fn mark_implicit_open_root(&mut self, name: &str) {
        self.data_mut().implicit_open_roots.insert(name.to_string());
        self.bump_scope();
    }

    pub(crate) fn path_starts_with_implicit_opened_component(&self, path: &Path) -> bool {
        let Some(component_path) = Self::first_dotted_component_path(path) else {
            return false;
        };
        self.data
            .implicit_open_roots
            .contains(component_path.head().name())
            && self.path_starts_with_opened_component(path)
    }

    pub(crate) fn has_module_ident(&self, id: &Ident) -> bool {
        self.data.modules.find_by_ident(id).is_some()
    }

    pub(crate) fn lookup_module_ident_exact(&self, id: &Ident) -> EnvResult<&ModuleDeclaration> {
        // OCaml compiler/ml/env.ml:781-788 uses `IdTbl.find_same` for
        // path-based `Pident` lookup. Source `Longident.Lident` lookup has its
        // own name fallback in env.ml:1000-1007; exact paths must not resolve to
        // a local/opened same-name module.
        self.data
            .modules
            .find_by_ident(id)
            .map(|m| m.as_ref())
            .ok_or_else(|| EnvError::ModuleNotFound(id.name().into()))
    }

    pub(crate) fn find_module_same(&self, id: &Ident) -> EnvResult<&ModuleDeclaration> {
        // OCaml compiler/ml/env.ml:865-875 uses `IdTbl.find_same` for
        // `Path.Pident` module lookup, and IdTbl.find_same at env.ml:285-290
        // skips opened components. This keeps alias scraping from resolving a
        // persistent alias target through an unrelated opened component with
        // the same name.
        self.data
            .modules
            .find_local_by_ident(id)
            .map(|m| m.as_ref())
            .ok_or_else(|| EnvError::ModuleNotFound(id.name().into()))
    }

    pub(crate) fn with_local_module_components<R>(
        &self,
        path: &Path,
        f: impl FnOnce(&super::env_lazy::StoredModuleComponents) -> R,
    ) -> Option<R> {
        let PathView::Pident(id) = path.view() else {
            return None;
        };
        let components = self.data.module_components.find_by_ident(id)?;
        Some(f(components.as_ref()))
    }

    pub(crate) fn local_module_components_shared(
        &self,
        path: &Path,
    ) -> Option<Rc<super::env_lazy::StoredModuleComponents>> {
        let PathView::Pident(id) = path.view() else {
            return None;
        };
        // OCaml compiler/ml/env.ml:1573-1578 stores component thunks in the
        // component table and shares the forced lazy value. Return the stored
        // Rc directly so child component maps keep the same thunk instead of
        // deep-cloning its captured seed environment.
        self.data.module_components.find_by_ident(id).cloned()
    }

    /// Find a module by path.
    pub fn lookup_module(&self, path: &Path) -> EnvResult<&ModuleDeclaration> {
        fn lookup_submodule_in_module_type<'a>(
            env: &'a Env,
            mty: &'a ModuleType,
            name: &str,
            visiting: &mut smallvec::SmallVec<[Path; 4]>,
        ) -> Option<&'a ModuleDeclaration> {
            match mty {
                ModuleType::MtySignature(sig) => sig.iter().find_map(|item| match item {
                    SignatureItem::SigModule(id, md, _) if id.name() == name => Some(md),
                    _ => None,
                }),
                ModuleType::MtyAlias(..) | ModuleType::MtyIdent(_) => {
                    let alias_path = mty.ident_or_alias_path().unwrap();
                    let md = lookup_module_inner(env, alias_path, visiting).ok()?;
                    lookup_submodule_in_module_type(env, &md.md_type, name, visiting)
                }
                ModuleType::MtyFunctor { .. } => None,
            }
        }

        fn lookup_module_inner<'a>(
            env: &'a Env,
            path: &Path,
            visiting: &mut smallvec::SmallVec<[Path; 4]>,
        ) -> EnvResult<&'a ModuleDeclaration> {
            if visiting.contains(path) {
                return Err(EnvError::ModuleNotFound(path.name().into()));
            }
            visiting.push(*path);

            match path.view() {
                PathView::Pident(id) => {
                    env.data
                        .modules
                        .find_by_ident(id)
                        .or_else(|| {
                            // Fallback: try name-based lookup for stamp mismatches
                            env.data.modules.find_by_name(id.name_atom())
                        })
                        .map(|m| m.as_ref())
                        .ok_or_else(|| EnvError::ModuleNotFound(id.name().into()))
                }
                PathView::Pdot(parent, name, _) => {
                    let parent_md = lookup_module_inner(env, parent, visiting)?;
                    lookup_submodule_in_module_type(env, &parent_md.md_type, name, visiting)
                        .ok_or_else(|| EnvError::ModuleNotFound((*name).into()))
                }
                PathView::Papply(_, _) => {
                    Err(EnvError::ModuleNotFound("(functor application)".into()))
                }
            }
        }

        let mut visiting = smallvec::SmallVec::new();
        lookup_module_inner(self, path, &mut visiting)
    }

    /// Normalize a path by following module aliases.
    /// Equivalent to OCaml's `Env.normalize_path` (env.ml:868-888): every
    /// `Pdot` is rebuilt with a fresh block around its normalized prefix and
    /// keeps its suffix string; an unchanged `Pident` is returned itself.
    pub fn normalize_path(&self, ctx: &TypeContext, path: &Path) -> Path {
        *self.normalize_shared_path(ctx, &Arc::new(*path), 0)
    }

    /// Normalize the prefix of a value/extension path by following module aliases.
    /// Equivalent to OCaml's `Env.normalize_path_prefix` (env.ml:898-902),
    /// which always builds a fresh `Pdot`.
    pub fn normalize_path_prefix(&self, ctx: &TypeContext, path: &Path) -> Path {
        match path.view() {
            PathView::Pdot(..) => {
                ctx.rebuild_dotted(path, |prefix| self.normalize_shared_path(ctx, prefix, 0))
            }
            PathView::Pident(_) => *path,
            PathView::Papply(_, _) => panic!("normalize_path_prefix called on Papply"),
        }
    }

    /// `normalize_path` of a path block: a fresh `Pdot` around the normalized
    /// prefix, then an alias's own stored target block (env.ml:868-878); a
    /// `Pident` that is not an alias is the block itself.
    fn normalize_shared_path(
        &self,
        ctx: &TypeContext,
        path: &Arc<Path>,
        depth: usize,
    ) -> Arc<Path> {
        if depth > 20 {
            return path.clone(); // Prevent infinite loops
        }
        let path = match path.view() {
            PathView::Pdot(..) => Arc::new(ctx.rebuild_dotted(path, |prefix| {
                self.normalize_shared_path(ctx, prefix, depth + 1)
            })),
            _ => path.clone(),
        };
        if let Ok(md) = self.lookup_module(&path)
            && let super::decl::ModuleType::MtyAlias(_, alias_path) = &md.md_type
        {
            return self.normalize_shared_path(ctx, alias_path, depth + 1);
        }
        path
    }

    // ========================================================================
    // Module Type Bindings
    // ========================================================================

    /// Add a module type binding.
    pub fn add_modtype(&mut self, id: Ident, decl: ModtypeDeclaration) {
        self.bump_scope();
        #[cfg(debug_assertions)]
        self.trace_bind(crate::tc::scope_trace::Ns::ModuleType, &id);
        let decl = Arc::new(decl);
        self.data_mut().modtypes.add(id, decl);
    }

    /// Find a module type by name.
    pub fn find_modtype(&self, name: impl crate::name::NameKey) -> EnvResult<&ModtypeDeclaration> {
        #[cfg(debug_assertions)]
        self.trace_lookup(crate::tc::scope_trace::Ns::ModuleType, name, false);
        self.data
            .modtypes
            .find_by_name(name)
            .map(|m| m.as_ref())
            .ok_or_else(|| EnvError::ModtypeNotFound(name.text().into()))
    }

    /// Find a module type by name with the path selected by OCaml `IdTbl.find_name`.
    ///
    /// Local bindings resolve to `Pident(id)`, while opened bindings resolve to
    /// `Pdot(root, name, pos)` from the symbolic open layer.
    pub fn find_modtype_with_path(&self, name: impl crate::name::NameKey) -> EnvResult<(Path, &ModtypeDeclaration)> {
        #[cfg(debug_assertions)]
        self.trace_lookup(crate::tc::scope_trace::Ns::ModuleType, name, false);
        self.data
            .modtypes
            .find_by_name_with_path(name)
            .map(|(path, decl)| (path, decl.as_ref()))
            .ok_or_else(|| EnvError::ModtypeNotFound(name.text().into()))
    }

    /// Find a module type by path.
    pub fn lookup_modtype(&self, path: &Path) -> EnvResult<&ModtypeDeclaration> {
        match path.view() {
            PathView::Pident(id) => self
                .data
                .modtypes
                .find_by_ident(id)
                .map(|m| m.as_ref())
                .ok_or_else(|| EnvError::ModtypeNotFound(id.name().into())),
            PathView::Pdot(parent, name, _) => {
                // Try to find the modtype through the parent module's signature.
                // First try ident-based lookup, then name-based for stamp mismatches.
                let parent_md = self.lookup_module(parent).or_else(|_| {
                    // Fallback: try by name if stamp doesn't match
                    self.find_module(parent.last())
                });
                if let Ok(parent_md) = parent_md {
                    if let super::decl::ModuleType::MtySignature(ref sig) = parent_md.md_type {
                        for item in sig.iter() {
                            if let super::decl::SignatureItem::SigModtype(id, decl) = item {
                                if id.name() == name {
                                    return Ok(decl);
                                }
                            }
                        }
                    }
                }
                Err(EnvError::ModtypeNotFound((*name).into()))
            }
            PathView::Papply(_, _) => {
                Err(EnvError::ModtypeNotFound("(functor application)".into()))
            }
        }
    }

    // ========================================================================
    // GADT Support
    // ========================================================================

    /// Check if the environment has local constraints.
    pub fn has_local_constraints(&self) -> bool {
        !self.data.local_constraints.is_empty()
    }

    /// Add a local constraint.
    pub fn add_local_constraint(&mut self, path: Path, decl: TypeDeclaration) {
        self.bump_scope();
        self.data_mut()
            .local_constraints
            .insert(path, Arc::new(decl));
    }

    /// Find a local constraint.
    pub fn find_local_constraint(&self, path: &Path) -> Option<&TypeDeclaration> {
        // Local constraints only exist under GADT pattern refinement; skip
        // hashing the path in the common empty case.
        if self.data.local_constraints.is_empty() {
            return None;
        }
        self.data.local_constraints.get(path).map(|d| d.as_ref())
    }

    /// Iterate over all local constraints.
    pub fn iter_local_constraints(&self) -> impl Iterator<Item = (&Path, &TypeDeclaration)> {
        self.data
            .local_constraints
            .iter()
            .map(|(p, d)| (p, d.as_ref()))
    }

    /// `Env.add_gadt_instance_level` (env.ml) returns a fresh Env record.
    /// Rust does not track GADT instances, so only the fresh scope identity
    /// that the scope-keyed caches observe is kept.
    pub fn add_gadt_instance_level(&mut self) {
        self.bump_scope();
    }

    // ========================================================================
    // Environment Extension
    // ========================================================================

    /// Create a new environment with an additional value.
    #[cfg(test)]
    pub fn with_value(&self, id: Ident, desc: ValueDescription) -> Env {
        let mut env = self.clone();
        env.add_value(id, desc);
        env
    }
}

impl Default for Env {
    fn default() -> Self {
        Self::empty()
    }
}

// ============================================================================
// Initial Environment
// ============================================================================

/// The initial environment (OCaml `Predef.build_initial_env`,
/// compiler/ml/predef.ml:239-424, as installed by `Env.initial_safe_string`).
///
/// OCaml builds the predefined declarations once per process. Here they are
/// built once per build and frozen in the world; each worker builds its
/// tables over them once and every compilation starts from a copy.
pub fn initial_env(ctx: &TypeContext) -> Env {
    ctx.world().initial_env()
}

/// The additions `Predef.build_initial_env` makes, in its order.
struct PredefDeclarations(Vec<crate::types::world::PredefItem>);

impl PredefDeclarations {
    fn add_type(&mut self, id: Ident, decl: TypeDeclaration) {
        self.0
            .push(crate::types::world::PredefItem::Type(id, Arc::new(decl)));
    }

    fn add_constructor(&mut self, id: Ident, desc: ConstructorDescription) {
        self.0
            .push(crate::types::world::PredefItem::Constructor(id, desc));
    }
}

/// The blocks of the shape of the builtin declaration numbered `block`:
/// `Predef.common_initial_env` makes each builtin declaration once.
fn predef_shape(block: u32) -> crate::types::ShapeBlocks {
    crate::types::ShapeBlocks {
        block: crate::types::ShapeAllocation::predef(block),
    }
}

/// The predefined declarations, built on `ctx` (a scratch context: the world
/// freezes them, see `World::predef`).
pub(crate) fn predef_declarations(ctx: &TypeContext) -> Vec<crate::types::world::PredefItem> {
    let mut env = PredefDeclarations(Vec::new());

    // Helper: create an abstract type declaration
    let decl_abstr = |arity: i32, immediate: bool| TypeDeclaration {
        type_params: vec![],
        type_arity: arity,
        type_kind: TypeKind::TypeAbstract,
        type_private: PrivateFlag::Public,
        type_manifest: None,
        type_variance: vec![],
        type_newtype_level: None,
        type_loc: crate::types::DeclLoc::none(),
        type_attributes: vec![],
        type_immediate: immediate,
        type_representation: crate::types::TypeRepresentation::Boxed,
        type_shape: crate::types::ValueShape::Unstated,
        type_inlined_types: vec![],
        type_path: None,
    };

    // Helper: create a constructor declaration (like OCaml's Predef.cstr)
    let cstr = |id: Ident, args: Vec<TypeExprRef>| ConstructorDeclaration {
        cd_id: id,
        cd_runtime_tag: None,
        cd_args: ConstructorArguments::CstrTuple(args),
        cd_res: None,
        cd_loc: crate::types::DeclLoc::none(),
        cd_attributes: vec![],
    };
    let variant_kind = |constructors: Vec<ConstructorDeclaration>| {
        let layout = crate::types::variant_runtime::plain_layout(
            ctx,
            constructors.iter().map(|constructor| {
                (
                    constructor.cd_id.name().to_string(),
                    !matches!(
                        &constructor.cd_args,
                        ConstructorArguments::CstrTuple(args) if args.is_empty()
                    ),
                )
            }),
        );
        TypeKind::TypeVariant(crate::types::decl::SharedVec::from(constructors), layout)
    };

    // Helper: add a type with its constructors to the environment
    // This matches OCaml's Env.store_type which calls Datarepr.constructors_of_type
    let add_type_with_constrs = |env: &mut PredefDeclarations,
                                 id: Ident,
                                 decl: TypeDeclaration,
                                 ctx: &TypeContext| {
        let type_path = Path::pident(id);

        // Extract constructors/labels from predef declarations so they are
        // available for disambiguation just like OCaml's initial environment.
        match &decl.type_kind {
            TypeKind::TypeVariant(constrs, _) => {
                let layout_ref = decl.variant_layout_ref().unwrap_or_else(|| {
                    crate::types::variant_runtime::plain_layout(
                        ctx,
                        constrs.iter().map(|cd| (
                            cd.cd_id.name().to_string(),
                            !matches!(&cd.cd_args, ConstructorArguments::CstrTuple(args) if args.is_empty()),
                        )),
                    )
                });

                for (position, cd) in constrs.iter().enumerate() {
                    let (cstr_args, cstr_arity) = match &cd.cd_args {
                        ConstructorArguments::CstrTuple(args) => (args.clone(), args.len() as i32),
                        ConstructorArguments::CstrRecord(labels) => {
                            let args: Vec<TypeExprRef> = labels.iter().map(|l| l.ld_type).collect();
                            let arity = args.len() as i32;
                            (args, arity)
                        }
                    };

                    let cstr_res = if let Some(res_ty) = cd.cd_res {
                        res_ty
                    } else {
                        ctx.new_generic_constr(type_path, decl.type_params.clone())
                    };

                    let cstr_existentials = constructor_existentials(ctx, &cstr_args, cd.cd_res);

                    let cstr_desc = ConstructorDescription {
                        cstr_name: cd.cd_id.name().to_string(),
                        cstr_res,
                        cstr_existentials,
                        cstr_args,
                        cstr_arity,
                        cstr_kind: ConstructorKind::Ordinary(crate::types::ConstructorReference {
                            variant: layout_ref,
                            position,
                        }),
                        cstr_generalized: cd.cd_res.is_some(),
                        cstr_private: decl.type_private,
                        cstr_loc: crate::types::DeclLoc::none(),
                        cstr_attributes:
                            crate::types::decl::constructor_description_attrs_for_variant(
                                constrs, cd,
                            ),
                        cstr_inlined: None,
                    };

                    env.add_constructor(cd.cd_id, cstr_desc);
                }
            }
            // predef.ml:239-424 declares no record type.
            TypeKind::TypeRecord(..) => unreachable!("a predefined record type"),
            TypeKind::TypeAbstract | TypeKind::TypeOpen => {}
        }
        env.add_type(id, decl);
    };

    use super::predef;
    use super::variant_runtime::{BlockType, ValueShape};

    // ---- Abstract types ----
    // Order matches OCaml's Predef.common_initial_env add_type order
    add_type_with_constrs(
        &mut env,
        predef::ident_bool(),
        TypeDeclaration {
            type_kind: variant_kind(vec![
                cstr(predef::ident_false(), vec![]),
                cstr(predef::ident_true(), vec![]),
            ]),
            type_immediate: true,
            type_shape: ValueShape::recognized_as(BlockType::Boolean, predef_shape(1)),
            ..decl_abstr(0, true)
        },
        ctx,
    );
    // predef.ml `recognized_as`: what `typeof` or `instanceof` recognizes a
    // builtin type's values by, as an annotation states it for a declared
    // type.
    let recognized_as =
        |block_type: BlockType, block: u32, decl: TypeDeclaration| TypeDeclaration {
            type_shape: ValueShape::recognized_as(block_type, predef_shape(block)),
            ..decl
        };
    add_type_with_constrs(
        &mut env,
        predef::ident_int(),
        recognized_as(BlockType::Number, 2, decl_abstr(0, true)),
        ctx,
    );
    add_type_with_constrs(
        &mut env,
        predef::ident_float(),
        recognized_as(BlockType::Number, 3, decl_abstr(0, false)),
        ctx,
    );
    add_type_with_constrs(
        &mut env,
        predef::ident_bigint(),
        recognized_as(BlockType::Bigint, 4, decl_abstr(0, false)),
        ctx,
    );
    add_type_with_constrs(
        &mut env,
        predef::ident_string(),
        recognized_as(BlockType::String, 5, decl_abstr(0, false)),
        ctx,
    );
    add_type_with_constrs(
        &mut env,
        predef::ident_unit(),
        TypeDeclaration {
            type_kind: variant_kind(vec![cstr(predef::ident_void(), vec![])]),
            type_immediate: true,
            ..decl_abstr(0, true)
        },
        ctx,
    );
    add_type_with_constrs(
        &mut env,
        predef::ident_exn(),
        TypeDeclaration {
            type_kind: TypeKind::TypeOpen,
            ..decl_abstr(0, false)
        },
        ctx,
    );
    {
        let tvar = ctx.new_generic_var(None);
        add_type_with_constrs(
            &mut env,
            predef::ident_option(),
            TypeDeclaration {
                type_params: vec![tvar],
                type_arity: 1,
                type_kind: variant_kind(vec![
                    cstr(predef::ident_none(), vec![]),
                    cstr(predef::ident_some(), vec![tvar]),
                ]),
                type_variance: vec![crate::types::variance::Variance::covariant()],
                ..decl_abstr(1, false)
            },
            ctx,
        );
    }
    {
        let tvar1 = ctx.new_generic_var(None);
        let tvar2 = ctx.new_generic_var(None);
        add_type_with_constrs(
            &mut env,
            predef::ident_result(),
            TypeDeclaration {
                type_params: vec![tvar1, tvar2],
                type_arity: 2,
                type_kind: variant_kind(vec![
                    cstr(predef::ident_ok(), vec![tvar1]),
                    cstr(predef::ident_error(), vec![tvar2]),
                ]),
                type_variance: vec![
                    crate::types::variance::Variance::covariant(),
                    crate::types::variance::Variance::covariant(),
                ],
                ..decl_abstr(2, false)
            },
            ctx,
        );
    }
    {
        let tvar = ctx.new_generic_var(None);
        add_type_with_constrs(
            &mut env,
            predef::ident_promise(),
            TypeDeclaration {
                type_params: vec![tvar],
                type_arity: 1,
                type_variance: vec![crate::types::variance::Variance::covariant()],
                // A constant: its blocks and its name string are static.
                type_shape: ValueShape::recognized_as(
                    BlockType::Instance(crate::types::VariantInstance::Class {
                        name: "Promise".to_string(),
                        ancestors: Vec::new(),
                        blocks: crate::types::ClassBlocks {
                            block: crate::types::ShapeAllocation::predef(10),
                            name: crate::types::ShapeString::Allocation(
                                crate::types::ShapeAllocation::predef(11),
                            ),
                            ancestors: Vec::new(),
                        },
                    }),
                    predef_shape(6),
                ),
                ..decl_abstr(1, false)
            },
            ctx,
        );
    }
    {
        // Upstream compiler/ml/predef.ml:364-372: first-class tags are an
        // abstract two-parameter builtin type, contravariant in the
        // parameter and covariant in the output.
        let param = ctx.new_generic_var(None);
        let output = ctx.new_generic_var(None);
        add_type_with_constrs(
            &mut env,
            predef::ident_tagged_template(),
            TypeDeclaration {
                type_params: vec![param, output],
                type_arity: 2,
                type_variance: vec![
                    crate::types::variance::Variance::covariant().conjugate(),
                    crate::types::variance::Variance::covariant(),
                ],
                ..decl_abstr(2, false)
            },
            ctx,
        );
    }
    // predef.ml:248-271: one generic parameter.
    add_type_with_constrs(
        &mut env,
        predef::ident_array(),
        TypeDeclaration {
            type_params: vec![ctx.new_generic_var(None)],
            type_variance: vec![crate::types::variance::Variance::full()],
            type_shape: ValueShape::recognized_as(
                // A constant: its `InstanceType Array` block is static.
                BlockType::Instance(crate::types::VariantInstance::Array(
                    crate::types::ShapeAllocation::predef(12),
                )),
                predef_shape(8),
            ),
            ..decl_abstr(1, false)
        },
        ctx,
    );
    // Upstream #8355: iterable / asyncIterable predef types (abstract,
    // covariant, 1 type parameter).
    // predef.ml:248-271: one generic parameter.
    add_type_with_constrs(
        &mut env,
        predef::ident_iterable(),
        TypeDeclaration {
            type_params: vec![ctx.new_generic_var(None)],
            type_variance: vec![crate::types::variance::Variance::covariant()],
            ..decl_abstr(1, false)
        },
        ctx,
    );
    // predef.ml:248-271: one generic parameter.
    add_type_with_constrs(
        &mut env,
        predef::ident_async_iterable(),
        TypeDeclaration {
            type_params: vec![ctx.new_generic_var(None)],
            type_variance: vec![crate::types::variance::Variance::covariant()],
            ..decl_abstr(1, false)
        },
        ctx,
    );
    {
        let tvar = ctx.new_generic_var(None);
        let list_ty = ctx.new_generic_predef_constr(predef::path_list(), vec![tvar]);
        add_type_with_constrs(
            &mut env,
            predef::ident_list(),
            TypeDeclaration {
                type_params: vec![tvar],
                type_arity: 1,
                type_kind: variant_kind(vec![
                    cstr(predef::ident_nil(), vec![]),
                    cstr(predef::ident_cons(), vec![tvar, list_ty]),
                ]),
                type_variance: vec![crate::types::variance::Variance::covariant()],
                ..decl_abstr(1, false)
            },
            ctx,
        );
    }
    {
        let tvar = ctx.new_generic_var(None);
        add_type_with_constrs(
            &mut env,
            predef::ident_dict(),
            TypeDeclaration {
                type_params: vec![tvar],
                type_arity: 1,
                type_variance: vec![crate::types::variance::Variance::full()],
                type_shape: ValueShape::recognized_as(BlockType::Object, predef_shape(9)),
                ..decl_abstr(1, false)
            },
            ctx,
        );
    }
    {
        let tvar = ctx.new_generic_var(None);
        let type_unknown = ctx.new_generic_predef_constr(predef::path_unknown(), vec![]);
        add_type_with_constrs(
            &mut env,
            predef::ident_unknown(),
            TypeDeclaration {
                type_params: vec![],
                type_arity: 0,
                type_kind: variant_kind(vec![ConstructorDeclaration {
                    cd_id: predef::ident_ctor_unknown(),
                    cd_runtime_tag: None,
                    cd_args: ConstructorArguments::CstrTuple(vec![tvar]),
                    cd_res: Some(type_unknown),
                    cd_loc: crate::types::DeclLoc::none(),
                    cd_attributes: vec![],
                }]),
                type_representation: super::decl::TypeRepresentation::Unboxed,
                ..decl_abstr(0, false)
            },
            ctx,
        );
    }

    // Standard exception constructors (extension constructors of exn)
    {
        let exn_ty = ctx.new_generic_predef_constr(predef::path_exn(), vec![]);
        let string_ty_for_exn = ctx.new_generic_predef_constr(predef::path_string(), vec![]);
        let int_ty_for_exn = ctx.new_generic_predef_constr(predef::path_int(), vec![]);

        let add_exception =
            |env: &mut PredefDeclarations, id: Ident, args: Vec<TypeExprRef>, exn_ty: TypeExprRef| {
                let path = Path::pident(id);
                let warn_on_literal_pattern_attr = crate::types::decl::Attribute {
                    attr_name: crate::types::asttypes::Located::noloc(
                        "warn_on_literal_pattern".to_string(),
                    ),
                    attr_payload: crate::types::decl::AttributePayload::Structure(vec![]),
                    attr_loc: crate::types::DeclLoc::none(),
                };
                let cstr_desc = ConstructorDescription {
                    cstr_name: id.name().to_string(),
                    cstr_res: exn_ty,
                    cstr_existentials: vec![],
                    cstr_arity: args.len() as i32,
                    cstr_args: args,
                    cstr_kind: ConstructorKind::Extension(path),
                    cstr_generalized: false,
                    cstr_private: PrivateFlag::Public,
                    cstr_loc: crate::types::DeclLoc::none(),
                    cstr_attributes: vec![warn_on_literal_pattern_attr],
                    cstr_inlined: None,
                };
                env.add_constructor(id, cstr_desc);
            };

        // predef.ml:412-423: exactly these exceptions, in this order.
        let loc_tuple = |ctx: &TypeContext| {
            ctx.new_generic_type(crate::types::type_expr::TypeDesc::Ttuple(
                ctx.new_type_list(&[string_ty_for_exn, int_ty_for_exn, int_ty_for_exn]),
            ))
        };
        add_exception(
            &mut env,
            predef::ident_undefined_recursive_module(),
            vec![loc_tuple(ctx)],
            exn_ty,
        );
        add_exception(
            &mut env,
            predef::ident_assert_failure(),
            vec![loc_tuple(ctx)],
            exn_ty,
        );
        add_exception(&mut env, predef::ident_division_by_zero(), vec![], exn_ty);
        add_exception(&mut env, predef::ident_end_of_file(), vec![], exn_ty);
        add_exception(&mut env, predef::ident_not_found(), vec![], exn_ty);
        add_exception(
            &mut env,
            predef::ident_failure(),
            vec![string_ty_for_exn],
            exn_ty,
        );
        let unknown_ty_for_exn = ctx.new_generic_predef_constr(predef::path_unknown(), vec![]);
        add_exception(
            &mut env,
            predef::ident_js_exn(),
            vec![unknown_ty_for_exn],
            exn_ty,
        );
        add_exception(
            &mut env,
            predef::ident_invalid_argument(),
            vec![string_ty_for_exn],
            exn_ty,
        );
        add_exception(
            &mut env,
            predef::ident_match_failure(),
            vec![loc_tuple(ctx)],
            exn_ty,
        );
    }

    // predef.ml build_initial_env: `char` is an alias of `int`, so a char
    // literal is its code point.
    add_type_with_constrs(
        &mut env,
        predef::ident_char(),
        TypeDeclaration {
            type_manifest: Some(ctx.new_generic_predef_constr(predef::path_int(), vec![])),
            ..decl_abstr(0, true)
        },
        ctx,
    );

    // OCaml's initial environment stops at predef types/exceptions
    // (compiler/ml/predef.ml:419-424). Pervasives values enter through
    // implicit opens (compiler/core/res_compmisc.ml:56-62,
    // compiler/ml/env.ml:1874-1877).
    env.0
}

/// The environment as a version log, built beside the tables and compared
/// with them (docs/CHECKER_REDESIGN.md, H.2.8 step 4).
#[cfg(test)]
#[path = "env_log.rs"]
mod env_log;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn identities_and_open_slots_remain_independent() {
        let mut env = Env::empty();
        let snapshot = env.clone();
        let clone = env.clone();
        assert_eq!(env.id(), snapshot.id());
        assert_eq!(env.id(), clone.id());
        assert_eq!(env.scope_id(), clone.scope_id());
        let id = Ident::create_persistent("x");
        let desc = ValueDescription {
            val_type: TypeExprRef(0),
            val_kind: super::super::decl::ValueKind::ValReg,
            val_loc: crate::types::DeclLoc::none(),
            val_attributes: Default::default(),
            val_path: None,
        };
        env.add_value(id, desc.clone());
        assert_ne!(env.id(), snapshot.id());
        assert_eq!(env.scope_id(), snapshot.scope_id());
        let layers = OpenedLayers::build(
            vec![(id, desc, 0)],
            vec![],
            vec![],
            vec![],
            vec![],
            vec![],
            vec![],
        );
        let root = Path::pident(Ident::create_persistent("M"));
        env.add_prebuilt_open_layers(root, &layers, Some(7));
        assert_ne!(env.scope_id(), snapshot.scope_id());
        assert_eq!(
            env.open_slot_use(OpenLookupKind::Value, "x"),
            Some(OpenSlotUse {
                slot: 7,
                shadowed: true
            })
        );
        let opened = env.clone();
        env.add_prebuilt_open_layers(root, &layers, None);
        assert_eq!(env.open_slot_use(OpenLookupKind::Value, "x"), None);
        assert_eq!(
            opened
                .open_slot_use(OpenLookupKind::Value, "x")
                .unwrap()
                .slot,
            7
        );
        assert!(snapshot.find_value("x").is_err());
    }

    #[test]
    fn extending_retained_clones_changes_only_the_extended_version() {
        use super::super::decl::{LabelArrayRef, ModuleType, ValueKind};
        use crate::context::IdGenerator;

        let ctx = TypeContext::new(Arc::new(IdGenerator::new()));
        let mut source = initial_env(&ctx);
        let id = Ident::create_local("x");
        let value = ValueDescription {
            val_type: TypeExprRef(0),
            val_kind: ValueKind::ValReg,
            val_loc: crate::types::DeclLoc::none(),
            val_attributes: Default::default(),
            val_path: None,
        };
        source.add_value(id, value.clone());
        let retained = source.clone();
        let original_id = source.id();
        let declaration = source.find_type("int").unwrap().clone();
        let module = ModuleDeclaration {
            md_type: ModuleType::MtySignature(Arc::new(vec![])),
            md_attributes: vec![],
            md_loc: crate::types::DeclLoc::none(),
            md_path: None,
        };
        // Each operation starts from the same retained version, including
        // after other branches have already extended it.
        macro_rules! extends {
            ($env:ident, $operation:expr) => {{
                let mut $env = retained.clone();
                assert_eq!($env.id(), original_id);
                $operation;
                assert_ne!($env.id(), original_id);
                assert_eq!(retained.id(), original_id);
                assert_eq!(source.id(), original_id);
            }};
        }
        extends!(env, env.add_value(id, value.clone()));
        extends!(
            env,
            assert!(env.update_value_type_by_name("x", TypeExprRef(1)))
        );
        extends!(env, env.add_type(id, declaration.clone()));
        extends!(env, env.store_type(&ctx, id, declaration.clone()));
        extends!(
            env,
            assert!(
                env.update_type_variance(super::super::predef::ident_int(), vec![])
                    .is_some()
            )
        );
        extends!(env, env.add_type_label_family(id, LabelArrayRef(0)));
        extends!(
            env,
            env.add_constructor(id, source.find_constructor("Some").unwrap().clone())
        );
        extends!(
            env,
            env.add_modtype(
                id,
                ModtypeDeclaration {
                    mtd_type: None,
                    mtd_attributes: vec![],
                    mtd_loc: crate::types::DeclLoc::none(),
                }
            )
        );
        extends!(
            env,
            env.add_label(id, LabelDescription {
                lbl_name: crate::name::Name::new("field"),
                lbl_runtime_name: crate::name::Name::new("field"),
                lbl_res: TypeExprRef(0),
                lbl_arg: TypeExprRef(0),
                lbl_mut: crate::types::MutableFlag::Immutable,
                lbl_optional: false,
                lbl_pos: 0,
                lbl_all: LabelArrayRef::NONE,
                lbl_repres: crate::types::RecordRepresentation::RecordRegular,
                lbl_private: PrivateFlag::Public,
                lbl_loc: crate::types::DeclLoc::none(),
            })
        );
        extends!(env, env.add_module(id, module.clone()));
        extends!(env, env.add_module_arg(id, module.clone()));
        extends!(
            env,
            env.add_local_constraint(Path::pident(id), declaration.clone())
        );
        extends!(env, env.add_gadt_instance_level());
        extends!(env, env.mark_implicit_open_root("Stdlib"));
        let coerced = retained.implicit_coercion();
        assert_ne!(coerced.id(), original_id);
        assert!(!retained.is_implicit_coercion());
        assert!(coerced.is_implicit_coercion());
        assert_eq!(retained.find_value("x").unwrap().val_type, TypeExprRef(0));
        assert!(retained.type_label_family(&id).is_none());
        assert!(retained.find_module("x").is_err());
        assert!(!retained.has_local_constraints());
    }

    #[test]
    fn initial_env_is_a_copy_of_the_workers_tables_over_frozen_declarations() {
        use crate::context::IdGenerator;
        use crate::types::predef;
        let first_ctx = TypeContext::new(std::sync::Arc::new(IdGenerator::new()));
        let first = initial_env(&first_ctx);
        let second_ctx = TypeContext::new(std::sync::Arc::new(IdGenerator::new()));
        assert!(std::sync::Arc::ptr_eq(first_ctx.world(), second_ctx.world()));
        let before = second_ctx.type_expr_count();
        let second = initial_env(&second_ctx);
        // The worker's tables are built once; a compilation takes a copy
        // and allocates no type node for it.
        assert_eq!(first.id(), second.id());
        assert_eq!(second_ctx.type_expr_count(), before);
        let int_path = Path::pident(predef::ident_int());
        assert!(first.lookup_type(&int_path).is_ok());
        assert!(second.lookup_type(&int_path).is_ok());
        let option = second
            .lookup_type(&Path::pident(predef::ident_option()))
            .expect("option");
        assert_eq!(option.type_params.len(), 1);
        for param in &option.type_params {
            assert!(param.is_shared(), "predefined declarations are frozen");
            // Any compilation of the build reads the frozen node.
            for ctx in [&first_ctx, &second_ctx] {
                assert!(matches!(
                    ctx.get_desc(*param).into_desc(),
                    crate::types::type_expr::TypeDesc::Tvar(None)
                ));
                assert_eq!(
                    ctx.get_level(*param),
                    crate::types::type_expr::GENERIC_LEVEL
                );
            }
        }
        let some = second.find_constructor("Some").expect("Some");
        // `Some`'s argument is the declaration's parameter: one node.
        assert_eq!(some.cstr_args, option.type_params);
    }

    /// Everything a reader can ask an `IdTbl`, in a comparable form.
    fn id_tbl_readings(tbl: &IdTbl<i32>, names: &[&str], ids: &[Ident]) -> Vec<String> {
        let mut readings = Vec::new();
        for name in names {
            readings.push(format!(
                "{name}: {:?} {:?} {:?} {:?}",
                tbl.find_by_name_with_id(*name),
                tbl.find_by_name_with_path(*name),
                tbl.find_all(*name),
                tbl.open_slot_use(*name),
            ));
        }
        for id in ids {
            readings.push(format!("{id:?}: {:?}", tbl.find_by_ident(id)));
        }
        let mut all: Vec<_> = tbl.iter().map(|(id, value)| (id.stamp(), *value)).collect();
        all.sort_unstable();
        readings.push(format!("all: {all:?}"));
        let mut visible: Vec<_> = tbl
            .visible_local_entries()
            .map(|(id, value)| (id.stamp(), *value))
            .collect();
        visible.sort_unstable();
        readings.push(format!("visible: {visible:?}"));
        readings.push(format!("fold order: {:?}", tbl.fold_name_order()));
        readings
    }

    #[test]
    fn recent_bindings_read_like_map_bindings() {
        let names = ["a", "b", "c", "d", "e", "f", "g", "opened", "missing"];
        // `listed` adds through the recent list, `mapped` straight to the map.
        let mut listed = IdTbl::new();
        let mut mapped = IdTbl::new();
        let mut ids = vec![Ident::create_local("missing")];
        let steps = 3 * RECENT_LIMIT as usize + 5;
        for step in 0..steps {
            if step == RECENT_LIMIT as usize + 3 {
                // An open in the middle of a batch: the bindings before it
                // stay readable below the opened layer.
                let root = Path::pident(Ident::create_persistent("Opened"));
                for tbl in [&mut listed, &mut mapped] {
                    let components = vec![
                        (Ident::create_persistent("opened"), -1, 0),
                        (Ident::create_persistent("a"), -2, 1),
                    ];
                    tbl.add_open_layer(root, components, Some(7));
                }
            }
            // Rebind a few names many times, in an irregular order.
            let id = Ident::create_local(names[(step * 5 + step / 4) % 7]);
            ids.push(id);
            listed.add(id, step as i32);
            mapped.add_to_map(id, step as i32);
            assert_eq!(
                id_tbl_readings(&listed, &names, &ids),
                id_tbl_readings(&mapped, &names, &ids),
                "after {} additions",
                step + 1
            );
        }
        assert!(
            mapped.recent.is_none() && listed.recent.is_some(),
            "the comparison must end with bindings still in the list"
        );
    }

    #[test]
    fn adding_to_a_table_leaves_a_snapshot_and_its_map_alone() {
        let mut tbl = IdTbl::new();
        let first = Ident::create_local("x");
        tbl.add(first, 1);
        tbl.move_recent_to_map();
        let snapshot = tbl.clone();

        let second = Ident::create_local("x");
        tbl.add(second, 2);
        tbl.add(Ident::create_local("y"), 3);
        assert!(
            tbl.current.ptr_eq(&snapshot.current),
            "a binding added after a snapshot must not copy the map"
        );
        assert_eq!(tbl.find_by_name_with_id("x"), Some((&second, &2)));
        assert_eq!(tbl.find_by_ident(&first), Some(&1));
        assert_eq!(snapshot.find_by_name_with_id("x"), Some((&first, &1)));
        assert_eq!(snapshot.find_by_name("y"), None);

        // Filling the batch moves it into the table's own copy of the map.
        for n in 0..RECENT_LIMIT {
            tbl.add(Ident::create_local("z"), 10 + n as i32);
        }
        assert!(!tbl.current.ptr_eq(&snapshot.current));
        assert_eq!(tbl.find_by_name_with_id("x"), Some((&second, &2)));
        assert_eq!(tbl.find_all("x"), vec![&2, &1]);
        assert_eq!(snapshot.find_all("x"), vec![&1]);
        assert_eq!(snapshot.find_by_name("z"), None);
    }

    #[test]
    fn a_table_layer_has_no_map_until_a_binding_is_moved_into_it() {
        let mut values: IdTbl<i32> = IdTbl::new();
        assert!(values.current.0.is_none());
        let first = Ident::create_local("x");
        values.add(first, 1);
        assert!(
            values.current.0.is_none(),
            "a recent binding needs no map"
        );
        for n in 1..RECENT_LIMIT {
            values.add(Ident::create_local("y"), n as i32);
        }
        assert!(values.current.0.is_some());
        assert_eq!(values.current.len(), 2);

        // An open starts a new layer, which again has no map; the layer
        // below keeps its own.
        let root = Path::pident(Ident::create_persistent("Opened"));
        values.add_open_layer(root, vec![(Ident::create_persistent("z"), 7, 0)], None);
        assert!(values.current.0.is_none() && values.current.is_empty());
        assert_eq!(values.find_by_name("x"), Some(&1));
        assert_eq!(values.find_by_ident(&first), Some(&1));
        assert_eq!(values.find_by_name("z"), Some(&7));
        // Every binding of both layers: `x`, each `y` and the opened `z`.
        assert_eq!(values.iter().count(), RECENT_LIMIT as usize + 1);

        let mut labels: TycompTbl<i32> = TycompTbl::new();
        assert!(labels.current.0.is_none() && labels.current_first_add.0.is_none());
        assert_eq!(labels.find_by_name("l"), None);
        assert!(labels.fold_name_order().is_empty());
        labels.add(Ident::create_local("l"), 1);
        assert!(labels.current.0.is_some() && labels.current_first_add.0.is_some());
        labels.add_open_layer(vec![(Ident::create_persistent("m"), 2)], None);
        assert!(labels.current.0.is_none() && labels.current_first_add.0.is_none());
        assert_eq!(labels.find_by_name("l"), Some(&1));
        assert_eq!(labels.find_all("m"), vec![&2]);
    }

    #[test]
    fn updating_a_recent_binding_leaves_a_snapshot_alone() {
        let mut tbl = IdTbl::new();
        tbl.add(Ident::create_local("x"), 1);
        let id = Ident::create_local("x");
        tbl.add(id, 2);
        let snapshot = tbl.clone();

        let updated = tbl.update_by_name("x", &mut |value| value * 10);
        assert_eq!(updated, Some((id, 20)));
        assert_eq!(tbl.find_all("x"), vec![&20, &1]);
        assert_eq!(snapshot.find_all("x"), vec![&2, &1]);
        assert_eq!(tbl.update_by_name("unbound", &mut |value| *value), None);
    }

    #[test]
    fn opened_table_updates_preserve_shared_snapshots() {
        let root = Path::pident(Ident::create_persistent("M"));
        let mut table = IdTbl::new();
        table.add_open_layer(root, vec![(Ident::create_local("x"), 1, 0)], None);
        table.add_open_layer(root, vec![(Ident::create_local("y"), 2, 0)], None);
        let snapshot = table.clone();
        assert!(Rc::ptr_eq(
            table.opened.as_ref().unwrap(),
            snapshot.opened.as_ref().unwrap(),
        ));

        // Exercise copy-on-write both in the newest layer and through `next`.
        assert!(table.update_by_name("y", &mut |value| value + 10).is_some());
        assert!(table.update_by_name("x", &mut |value| value + 10).is_some());
        assert_eq!(table.find_by_name("x"), Some(&11));
        assert_eq!(table.find_by_name("y"), Some(&12));
        assert_eq!(snapshot.find_by_name("x"), Some(&1));
        assert_eq!(snapshot.find_by_name("y"), Some(&2));
    }

    #[test]
    fn test_empty_env() {
        let env = Env::empty();
        assert!(env.find_value("x").is_err());
        assert!(env.find_type("t").is_err());
    }

    #[test]
    fn test_add_and_find_value() {
        let mut env = Env::empty();
        let id = Ident::create_persistent("x");
        let desc = ValueDescription {
            val_type: TypeExprRef(0),
            val_kind: super::super::decl::ValueKind::ValReg,
            val_loc: crate::types::DeclLoc::none(),
            val_attributes: Default::default(),
            val_path: None,
        };
        env.add_value(id, desc);

        assert!(env.find_value("x").is_ok());
        assert!(env.find_value("y").is_err());
    }

    #[test]
    fn test_add_and_find_type() {
        let mut env = Env::empty();
        let id = Ident::create_persistent("t");
        let decl = TypeDeclaration {
            type_params: vec![],
            type_arity: 0,
            type_kind: super::super::decl::TypeKind::TypeAbstract,
            type_private: super::super::asttypes::PrivateFlag::Public,
            type_manifest: None,
            type_variance: vec![],
            type_newtype_level: None,
            type_loc: crate::types::DeclLoc::none(),
            type_attributes: vec![],
            type_immediate: false,
            type_representation: crate::types::TypeRepresentation::Boxed,
            type_shape: crate::types::ValueShape::Unstated,
            type_inlined_types: vec![],
            type_path: None,
        };
        env.add_type(id, decl);

        assert!(env.find_type("t").is_ok());
        assert!(env.find_type("u").is_err());
    }

    #[test]
    fn test_shadowing() {
        let mut env = Env::empty();
        let id1 = Ident::create_local("x");
        let id2 = Ident::create_local("x");

        let desc1 = ValueDescription {
            val_type: TypeExprRef(1),
            val_kind: super::super::decl::ValueKind::ValReg,
            val_loc: crate::types::DeclLoc::none(),
            val_attributes: Default::default(),
            val_path: None,
        };
        let desc2 = ValueDescription {
            val_type: TypeExprRef(2),
            val_kind: super::super::decl::ValueKind::ValReg,
            val_loc: crate::types::DeclLoc::none(),
            val_attributes: Default::default(),
            val_path: None,
        };

        env.add_value(id1, desc1);
        env.add_value(id2, desc2);

        // Should find the most recent binding
        let found = env.find_value("x").unwrap();
        assert_eq!(found.val_type, TypeExprRef(2));
    }

    #[test]
    fn test_with_value() {
        let env = Env::empty();
        let id = Ident::create_persistent("x");
        let desc = ValueDescription {
            val_type: TypeExprRef(0),
            val_kind: super::super::decl::ValueKind::ValReg,
            val_loc: crate::types::DeclLoc::none(),
            val_attributes: Default::default(),
            val_path: None,
        };

        let env2 = env.with_value(id, desc);

        // Original env unchanged
        assert!(env.find_value("x").is_err());
        // New env has the binding
        assert!(env2.find_value("x").is_ok());
    }

    #[test]
    fn test_lookup_by_path() {
        let mut env = Env::empty();
        let id = Ident::create_persistent("x");
        let desc = ValueDescription {
            val_type: TypeExprRef(0),
            val_kind: super::super::decl::ValueKind::ValReg,
            val_loc: crate::types::DeclLoc::none(),
            val_attributes: Default::default(),
            val_path: None,
        };
        env.add_value(id, desc);

        let path = Path::pident(id);
        assert!(env.lookup_value(&path).is_ok());
    }

    #[test]
    fn test_module_path_requires_env_scoped_cache_tracks_active_aliases() {
        use super::super::decl::{AliasPresence, ModuleDeclaration, ModuleType};

        let mut env = Env::empty();
        let target_id = Ident::create_local("Target");
        env.add_module(
            target_id,
            ModuleDeclaration {
                md_type: ModuleType::MtySignature(std::sync::Arc::new(vec![])),
                md_attributes: vec![],
                md_loc: crate::types::DeclLoc::none(),
                md_path: None,
            },
        );

        let alias_id = Ident::create_local("Alias");
        env.add_module(
            alias_id,
            ModuleDeclaration {
                md_type: ModuleType::MtyAlias(
                    AliasPresence::MtaPresent,
                    std::sync::Arc::new(Path::pident(target_id)),
                ),
                md_attributes: vec![],
                md_loc: crate::types::DeclLoc::none(),
                md_path: None,
            },
        );

        let target_child_path = Path::pdot(Path::pident(target_id), "Inner");
        assert!(env.module_path_requires_env_scoped_cache(&target_child_path));

        env.add_module(
            alias_id,
            ModuleDeclaration {
                md_type: ModuleType::MtySignature(std::sync::Arc::new(vec![])),
                md_attributes: vec![],
                md_loc: crate::types::DeclLoc::none(),
                md_path: None,
            },
        );

        assert!(!env.module_path_requires_env_scoped_cache(&target_child_path));
    }
}
