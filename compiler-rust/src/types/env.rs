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
use std::cell::RefCell;
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
            drop(desc);
            super::btype::iter_type_expr(ctx, ty, |child| {
                free_vars_rec(ctx, child, result, visited);
            });
        }
    }
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
        name: String,
        source1: String,
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

fn id_open_table<T>(components: Vec<(Ident, T, i32)>) -> OpenedMap<(Ident, T, i32)> {
    let mut table = OpenedMap::with_capacity_and_hasher(components.len(), Default::default());
    for (id, value, pos) in components {
        table.insert(id.name_atom(), (id, value, pos));
    }
    table
}

fn tycomp_open_table<T>(components: Vec<(Ident, T)>) -> OpenedMap<Vec<(Ident, T)>> {
    let mut table: OpenedMap<Vec<(Ident, T)>> =
        OpenedMap::with_capacity_and_hasher(components.len(), Default::default());
    for (id, value) in components {
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

/// The layer tables that opening one signature adds to an Env. Built once
/// and attachable to any number of Envs (see `Env::add_prebuilt_open_layers`).
#[derive(Debug)]
pub(crate) struct OpenedLayers {
    values: Arc<OpenedMap<(Ident, Arc<ValueDescription>, i32)>>,
    types: Arc<OpenedMap<(Ident, Arc<TypeDeclaration>, i32)>>,
    constrs: Arc<OpenedMap<Vec<(Ident, Arc<ConstructorDescription>)>>>,
    labels: Arc<OpenedMap<Vec<(Ident, Arc<LabelDescription>)>>>,
    modules: Arc<OpenedMap<(Ident, Arc<ModuleDeclaration>, i32)>>,
    module_components: Arc<OpenedMap<(Ident, Arc<super::env_lazy::StoredModuleComponents>, i32)>>,
    modtypes: Arc<OpenedMap<(Ident, Arc<ModtypeDeclaration>, i32)>>,
}

impl OpenedLayers {
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn build(
        values: Vec<(Ident, ValueDescription, i32)>,
        types: Vec<(Ident, Arc<TypeDeclaration>)>,
        constructors: Vec<(Ident, ConstructorDescription)>,
        labels: Vec<(Ident, LabelDescription)>,
        modules: Vec<(Ident, ModuleDeclaration, i32)>,
        module_components: Vec<(Ident, Arc<super::env_lazy::StoredModuleComponents>, i32)>,
        modtypes: Vec<(Ident, ModtypeDeclaration)>,
    ) -> Self {
        OpenedLayers {
            values: Arc::new(id_open_table(
                values
                    .into_iter()
                    .map(|(id, desc, pos)| (id, Arc::new(desc), pos))
                    .collect(),
            )),
            types: Arc::new(id_open_table(
                types
                    .into_iter()
                    .map(|(id, decl)| (id, decl, crate::types::path::NOPOS))
                    .collect(),
            )),
            constrs: Arc::new(tycomp_open_table(
                constructors
                    .into_iter()
                    .map(|(id, desc)| (id, Arc::new(desc)))
                    .collect(),
            )),
            labels: Arc::new(tycomp_open_table(
                labels
                    .into_iter()
                    .map(|(id, desc)| (id, Arc::new(desc)))
                    .collect(),
            )),
            modules: Arc::new(id_open_table(
                modules
                    .into_iter()
                    .map(|(id, decl, pos)| (id, Arc::new(decl), pos))
                    .collect(),
            )),
            module_components: Arc::new(id_open_table(module_components)),
            modtypes: Arc::new(id_open_table(
                modtypes
                    .into_iter()
                    .map(|(id, decl)| (id, Arc::new(decl), crate::types::path::NOPOS))
                    .collect(),
            )),
        }
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
    root: Option<Path>,
    components: Arc<OpenedMap<(Ident, T, i32)>>,
    next: Arc<IdTbl<T>>,
    /// The open's `using` callback (OCaml `IdTbl.opened.using`), as a slot
    /// registered with the type checker.
    slot: Option<u32>,
}

/// The environment table a source name is looked up in (OCaml's `proj1`
/// argument of `Env.lookup`, or the table `lookup_module{,_descr}` reads).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OpenLookupKind {
    Value,
    Type,
    Module,
    Component,
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

/// Same-name bindings in an Env table, oldest first. Shared so that copying a
/// persistent-map node on insert only bumps reference counts.
type IdBucket<T> = std::rc::Rc<Vec<(Ident, T)>>;

/// A table of bindings indexed by identifier.
///
/// This matches OCaml `Env.IdTbl`: local bindings live in `current`, and each
/// open is represented symbolically as an `opened` layer rather than flattening
/// every opened binding into the same name map with an origin boolean.
#[derive(Debug, Clone)]
pub struct IdTbl<T> {
    current: PersistentHashMap<Name, IdBucket<T>>,
    opened: Option<Arc<IdOpened<T>>>,
}

impl<T: Clone> IdTbl<T> {
    pub fn new() -> Self {
        Self {
            current: PersistentHashMap::default(),
            opened: None,
        }
    }

    pub fn add(&mut self, id: Ident, value: T) {
        let key = id.name_atom();
        match self.current.get_mut(&key) {
            Some(entries) => std::rc::Rc::make_mut(entries).push((id, value)),
            None => {
                self.current
                    .insert(key, std::rc::Rc::new(vec![(id, value)]));
            }
        }
    }

    pub fn add_open_layer(
        &mut self,
        root: Path,
        components: Vec<(Ident, T, i32)>,
        slot: Option<u32>,
    ) {
        self.add_open_layer_table(root, Arc::new(id_open_table(components)), slot);
    }

    /// Open a prebuilt layer table (possibly shared with other Envs).
    fn add_open_layer_table(
        &mut self,
        root: Path,
        components: Arc<OpenedMap<(Ident, T, i32)>>,
        slot: Option<u32>,
    ) {
        if components.is_empty() {
            return;
        }
        let next = std::mem::take(self);
        *self = Self {
            current: PersistentHashMap::default(),
            opened: Some(Arc::new(IdOpened {
                root: Some(root),
                components,
                next: Arc::new(next),
                slot,
            })),
        };
    }

    /// The `using` call of OCaml `IdTbl.find_name ~mark:true` for `name`:
    /// the slot of the opened layer the name resolves to, and whether that
    /// layer hides an earlier binding (`find_name ~mark:false name next`).
    pub fn open_slot_use(&self, name: &str) -> Option<OpenSlotUse> {
        // A name never interned is in no table.
        self.open_slot_use_by_key(Name::lookup(name)?)
    }

    fn open_slot_use_by_key(&self, key: Name) -> Option<OpenSlotUse> {
        if self
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
        // Opening a module starts a fresh, usually empty, local layer; skip
        // hashing the name for those.
        if self.current.is_empty() {
            return None;
        }
        let stamp = id.stamp();
        self.current.get(&id.name_atom()).and_then(|entries| {
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
    }

    fn find_name_entry(&self, name: &str) -> Option<(&Ident, &T)> {
        self.find_name_entry_key(Name::lookup(name)?)
    }

    fn find_name_entry_key(&self, key: Name) -> Option<(&Ident, &T)> {
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

    pub fn find_by_name(&self, name: &str) -> Option<&T> {
        self.find_name_entry(name).map(|(_, value)| value)
    }

    pub fn find_by_name_with_id(&self, name: &str) -> Option<(&Ident, &T)> {
        self.find_name_entry(name)
    }

    pub fn find_by_name_with_path(&self, name: &str) -> Option<(Path, &T)> {
        self.find_by_key_with_path(Name::lookup(name)?)
    }

    fn find_by_key_with_path(&self, key: Name) -> Option<(Path, &T)> {
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
                        .map(|root| Path::pdot_pos(root.clone(), key, *pos))
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

    pub fn find_local_by_ident(&self, id: &Ident) -> Option<&T> {
        self.find_by_ident(id)
    }

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
        if let Some(entries) = self.current.get_mut(&key)
            && let Some((id, value)) = std::rc::Rc::make_mut(entries).last_mut()
        {
            let updated = f(value);
            *value = updated.clone();
            return Some((*id, updated));
        }

        if let Some(opened) = self.opened.as_mut() {
            let opened = Arc::make_mut(opened);
            if let Some((id, value, _)) = Arc::make_mut(&mut opened.components).get_mut(&key) {
                let updated = f(value);
                *value = updated.clone();
                return Some((*id, updated));
            }
            return Arc::make_mut(&mut opened.next).update_by_key(key, f);
        }

        None
    }

    pub fn find_all(&self, name: &str) -> Vec<&T> {
        let mut items = Vec::new();
        if let Some(key) = Name::lookup(name) {
            self.collect_all_key(key, &mut items);
        }
        items
    }

    fn collect_all_key<'a>(&'a self, key: Name, items: &mut Vec<&'a T>) {
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

    pub fn contains(&self, name: &str) -> bool {
        self.find_by_name(name).is_some()
    }

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
        names.extend(ident_tbl_fold_name_order(self.current.iter().map(
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
        for (name, entries) in self.current.iter() {
            if !shadowing_opens
                .iter()
                .any(|opened| opened.contains_key(name))
                && seen.insert(*name)
                && let Some((id, value)) = entries.last()
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
    components: Arc<OpenedMap<Vec<(Ident, T)>>>,
    next: Arc<TycompTbl<T>>,
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
    current: PersistentHashMap<Name, IdBucket<T>>,
    /// Order in which each name of `current` was first added: the `Ident.add`
    /// sequence that shapes OCaml's AVL tree (compiler/ext/ident.ml:144-150).
    current_first_add: PersistentHashMap<Name, i32>,
    opened: Option<Arc<TycompOpened<T>>>,
}

impl<T: Clone> TycompTbl<T> {
    pub fn new() -> Self {
        Self {
            current: PersistentHashMap::default(),
            current_first_add: PersistentHashMap::default(),
            opened: None,
        }
    }

    pub fn add(&mut self, id: Ident, value: T) {
        let key = id.name_atom();
        match self.current.get_mut(&key) {
            Some(entries) => std::rc::Rc::make_mut(entries).push((id, value)),
            None => {
                let seq = self.current_first_add.len() as i32;
                self.current_first_add.insert(key, seq);
                self.current
                    .insert(key, std::rc::Rc::new(vec![(id, value)]));
            }
        }
    }

    pub fn add_open_layer(&mut self, components: Vec<(Ident, T)>, slot: Option<u32>) {
        self.add_open_layer_table(Arc::new(tycomp_open_table(components)), slot);
    }

    /// Open a prebuilt layer table (possibly shared with other Envs).
    fn add_open_layer_table(
        &mut self,
        components: Arc<OpenedMap<Vec<(Ident, T)>>>,
        slot: Option<u32>,
    ) {
        if components.is_empty() {
            return;
        }
        let next = std::mem::take(self);
        *self = Self {
            current: PersistentHashMap::default(),
            current_first_add: PersistentHashMap::default(),
            opened: Some(Arc::new(TycompOpened {
                components,
                next: Arc::new(next),
                slot,
            })),
        };
    }

    pub fn find_by_name(&self, name: &str) -> Option<&T> {
        self.find_by_key(Name::lookup(name)?)
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

    pub fn find_by_name_with_origin(&self, name: &str) -> Option<(&Ident, &T, bool)> {
        self.find_by_key_with_origin(Name::lookup(name)?)
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

    pub fn find_all(&self, name: &str) -> Vec<&T> {
        let mut items = Vec::new();
        if let Some(key) = Name::lookup(name) {
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

    /// OCaml `TycompTbl.find_all`: each candidate with the `mk_callback`
    /// data of its opened layer, `(slot, first hidden candidate)`.
    pub fn find_all_marking(&self, name: &str) -> Vec<(&T, Option<(u32, Option<&T>)>)> {
        let mut items: Vec<(&T, Option<(u32, Option<&T>)>)> = Vec::new();
        let Some(key) = Name::lookup(name) else {
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

/// The typing environment.
///
/// This tracks all bindings visible during type checking.
/// The environment is immutable - extending it creates a new environment.
#[derive(Debug)]
pub struct Env {
    /// Unique identity for this environment instance.
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
    module_components: IdTbl<Arc<super::env_lazy::StoredModuleComponents>>,

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

    /// Environment flags.
    flags: EnvFlags,

    /// The usage slot the next opened component layers take (the `slot`
    /// OCaml `Env.open_signature` passes to `add_components`).
    pending_open_slot: Option<u32>,
}

impl Clone for Env {
    fn clone(&self) -> Self {
        Env {
            // Keep clone-induced env changes visible to abbreviation caching by
            // default. Callers that are only snapshotting the same logical env
            // must opt into `clone_preserve_id()`.
            id: next_env_id(),
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

    /// `Env.in_signature b env` (env.ml:495-499).
    pub fn in_signature(&self, b: bool) -> Env {
        let mut env = self.clone();
        env.data_mut().flags.in_signature = b;
        env
    }

    /// `Env.implicit_coercion env` (env.ml:502-503).
    pub fn implicit_coercion(&self) -> Env {
        let mut env = self.clone();
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
        // Cloning shares the empty persistent-map roots and assigns a fresh
        // env id, so it is equivalent to building a new empty env without
        // allocating a root node per table.
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
                flags: EnvFlags::default(),
                pending_open_slot: None,
            }),
        }
    }

    /// OCaml `IdTbl.find_name ~mark:true` usage of an unqualified source
    /// name in the table `kind` selects.
    pub(crate) fn open_slot_use(&self, kind: OpenLookupKind, name: &str) -> Option<OpenSlotUse> {
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
        Option<(u32, Option<&ConstructorDescription>)>,
    )> {
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
    ) -> Vec<(&LabelDescription, Option<(u32, Option<&LabelDescription>)>)> {
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

    /// Set the usage slot of the opened layers the next open adds (OCaml
    /// `open_signature (Some slot)`); `None` after the open.
    pub(crate) fn set_pending_open_slot(&mut self, slot: Option<u32>) {
        self.data_mut().pending_open_slot = slot;
    }

    /// Unique identifier for this environment instance.
    pub fn id(&self) -> u64 {
        self.id
    }

    /// Clone an environment while preserving its current identity.
    /// This is for storing a snapshot of the same logical env value rather
    /// than creating a fresh env instance.
    pub fn clone_preserve_id(&self) -> Self {
        Env {
            id: self.id,
            scope_id: self.scope_id,
            data: self.data.clone(),
        }
    }

    /// Mark this environment as changed.
    fn bump_id(&mut self) {
        self.id = next_env_id();
    }

    /// Mark a change to the bindings that module-path resolution reads.
    fn bump_scope(&mut self) {
        self.bump_id();
        self.scope_id = self.id;
        self.data_mut().scope_caches = std::rc::Rc::default();
    }

    /// Identity of the module-level bindings (see the `scope_id` field).
    pub fn scope_id(&self) -> u64 {
        self.scope_id
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
        match path {
            Path::Pdot(parent, _, _) => Self::path_has_prefix(parent, prefix),
            Path::Pident(_) | Path::Papply(_, _) => false,
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
                    ModuleType::MtyAlias(_, target) | ModuleType::MtyIdent(target) => {
                        Some((*id, target.clone()))
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
        let desc = Arc::new(desc);
        self.data_mut().values.add(id, desc);
    }

    /// Find a value by name.
    pub fn find_value(&self, name: &str) -> EnvResult<&ValueDescription> {
        self.data
            .values
            .find_by_name(name)
            .map(|v| v.as_ref())
            .ok_or_else(|| EnvError::ValueNotFound(name.into()))
    }

    /// Find a value by name, returning both the identifier and description.
    pub fn find_value_with_id(&self, name: &str) -> EnvResult<(&Ident, &ValueDescription)> {
        self.data
            .values
            .find_by_name_with_id(name)
            .map(|(id, v)| (id, v.as_ref()))
            .ok_or_else(|| EnvError::ValueNotFound(name.into()))
    }

    /// Find a value by name with the path selected by OCaml `IdTbl.find_name`.
    ///
    /// Local bindings resolve to `Pident(id)`, while opened bindings resolve to
    /// `Pdot(root, name, pos)` from the symbolic open layer.
    pub fn find_value_with_path(&self, name: &str) -> EnvResult<(Path, &ValueDescription)> {
        self.data
            .values
            .find_by_name_with_path(name)
            .map(|(path, desc)| (path, desc.as_ref()))
            .ok_or_else(|| EnvError::ValueNotFound(name.into()))
    }

    /// Like `find_value_with_path`, sharing the stored description.
    pub fn find_value_arc_with_path(
        &self,
        name: &str,
    ) -> EnvResult<(Path, &Arc<ValueDescription>)> {
        self.data
            .values
            .find_by_name_with_path(name)
            .ok_or_else(|| EnvError::ValueNotFound(name.into()))
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
        match path {
            Path::Pident(id) => self
                .data
                .values
                .find_by_ident(id)
                .map(|v| v.as_ref())
                .ok_or_else(|| EnvError::ValueNotFound(id.name().into())),
            Path::Pdot(_, name, _) => self.find_value(name),
            Path::Papply(_, _) => Err(EnvError::ValueNotFound("(functor application)".into())),
        }
    }

    // ========================================================================
    // Type Bindings
    // ========================================================================

    /// Add a type binding.
    pub fn add_type(&mut self, id: Ident, decl: impl Into<Arc<TypeDeclaration>>) {
        self.bump_scope();
        let decl = decl.into();
        self.data_mut().types.add(id, decl);
    }

    /// Find a type by name.
    pub fn find_type(&self, name: &str) -> EnvResult<&TypeDeclaration> {
        self.data
            .types
            .find_by_name(name)
            .map(|t| t.as_ref())
            .ok_or_else(|| EnvError::TypeNotFound(name.into()))
    }

    /// Find a type by name, returning the identifier and declaration.
    /// The returned identifier has the canonical stamp from the environment
    /// (e.g., persistent ident for predef types).
    pub fn find_type_with_id(&self, name: &str) -> EnvResult<(&Ident, &TypeDeclaration)> {
        self.data
            .types
            .find_by_name_with_id(name)
            .map(|(id, decl)| (id, decl.as_ref()))
            .ok_or_else(|| EnvError::TypeNotFound(name.into()))
    }

    /// Find a type by name with the path selected by OCaml `IdTbl.find_name`.
    ///
    /// Local bindings resolve to `Pident(id)`, while opened bindings resolve to
    /// `Pdot(root, name, pos)` from the symbolic open layer.
    pub fn find_type_with_path(&self, name: &str) -> EnvResult<(Path, &TypeDeclaration)> {
        self.data
            .types
            .find_by_name_with_path(name)
            .map(|(path, decl)| (path, decl.as_ref()))
            .ok_or_else(|| EnvError::TypeNotFound(name.into()))
    }

    /// Iterate over visible type bindings.
    pub fn iter_types(&self) -> impl Iterator<Item = (&Ident, &TypeDeclaration)> {
        self.data.types.iter().map(|(id, decl)| (id, decl.as_ref()))
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
            .or_else(|| self.data.types.find_by_name(id.name()))
    }

    /// Find a type by path.
    pub fn lookup_type(&self, path: &Path) -> EnvResult<&TypeDeclaration> {
        match path {
            Path::Pident(id) => self
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
                    self.data.types.find_by_name(id.name())
                })
                .map(|t| t.as_ref())
                .ok_or_else(|| EnvError::TypeNotFound(id.name().into())),
            Path::Pdot(parent, name, _) => {
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
                            super::decl::ModuleType::MtyIdent(type_path)
                            | super::decl::ModuleType::MtyAlias(_, type_path) => {
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
            Path::Papply(_, _) => Err(EnvError::TypeNotFound("(functor application)".into())),
        }
    }

    // ========================================================================
    // Constructor Bindings
    // ========================================================================

    /// Add a constructor binding.
    pub fn add_constructor(&mut self, id: Ident, desc: ConstructorDescription) {
        self.bump_id();
        let desc = Arc::new(desc);
        self.data_mut().constrs.add(id, desc);
    }

    /// Find a constructor by name.
    pub fn find_constructor(&self, name: &str) -> EnvResult<&ConstructorDescription> {
        self.data
            .constrs
            .find_by_name(name)
            .map(|c| c.as_ref())
            .ok_or_else(|| EnvError::ConstructorNotFound(name.into()))
    }

    /// Find a constructor by name with its local/opened origin flag.
    pub fn find_constructor_with_origin(
        &self,
        name: &str,
    ) -> EnvResult<(&Ident, &ConstructorDescription, bool)> {
        self.data
            .constrs
            .find_by_name_with_origin(name)
            .map(|(id, c, is_local)| (id, c.as_ref(), is_local))
            .ok_or_else(|| EnvError::ConstructorNotFound(name.into()))
    }

    /// Find all constructors with a given name.
    pub fn find_all_constructors(&self, name: &str) -> Vec<&ConstructorDescription> {
        self.data
            .constrs
            .find_all(name)
            .into_iter()
            .map(|c| c.as_ref())
            .collect()
    }

    /// Iterate over visible constructor bindings.
    pub fn iter_constructors(&self) -> impl Iterator<Item = (&Ident, &ConstructorDescription)> {
        self.data.constrs.iter().map(|(id, c)| (id, c.as_ref()))
    }

    // ========================================================================
    // Label Bindings
    // ========================================================================

    /// Add a label binding.
    pub fn add_label(&mut self, id: Ident, desc: LabelDescription) {
        self.bump_id();
        let desc = Arc::new(desc);
        self.data_mut().labels.add(id, desc);
    }

    /// Find a label by name.
    pub fn find_label(&self, name: &str) -> EnvResult<&LabelDescription> {
        self.data
            .labels
            .find_by_name(name)
            .map(|l| l.as_ref())
            .ok_or_else(|| EnvError::LabelNotFound(name.into()))
    }

    /// Find a label by name with its local/opened origin flag.
    pub fn find_label_with_origin(
        &self,
        name: &str,
    ) -> EnvResult<(&Ident, &LabelDescription, bool)> {
        self.data
            .labels
            .find_by_name_with_origin(name)
            .map(|(id, l, is_local)| (id, l.as_ref(), is_local))
            .ok_or_else(|| EnvError::LabelNotFound(name.into()))
    }

    /// Find all labels with a given name.
    pub fn find_all_labels(&self, name: &str) -> Vec<&LabelDescription> {
        self.data
            .labels
            .find_all(name)
            .into_iter()
            .map(|l| l.as_ref())
            .collect()
    }

    /// Iterate over visible label bindings.
    pub fn iter_labels(&self) -> impl Iterator<Item = (&Ident, &LabelDescription)> {
        self.data.labels.iter().map(|(id, l)| (id, l.as_ref()))
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
        let seed_env = self.clone_preserve_id();
        let stored_components = Arc::new(
            super::env_lazy::StoredModuleComponents::new_with_parent_context(
                seed_env,
                component_path,
                component_decl,
                parent_context,
            ),
        );
        self.bump_scope();
        self.invalidate_module_alias_caches();
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
        match path {
            Path::Pident(id) => self.data.functor_args.contains(id),
            Path::Pdot(parent, _, _) => self.is_functor_arg_path(parent),
            Path::Papply(_, _) => true,
        }
    }

    /// Open `layers` (the component tables of one signature) under `root`.
    pub(crate) fn add_prebuilt_open_layers(&mut self, root: Path, layers: &OpenedLayers) {
        if layers.is_empty() {
            return;
        }
        self.bump_scope();
        self.invalidate_module_alias_caches();
        let slot = self.data.pending_open_slot;
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
    pub fn find_module(&self, name: &str) -> EnvResult<&ModuleDeclaration> {
        self.data
            .modules
            .find_by_name(name)
            .map(|m| m.as_ref())
            .ok_or_else(|| EnvError::ModuleNotFound(name.into()))
    }

    /// Find a module by name, returning both the identifier and declaration.
    pub fn find_module_with_id(&self, name: &str) -> EnvResult<(&Ident, &ModuleDeclaration)> {
        self.data
            .modules
            .find_by_name_with_id(name)
            .map(|(id, m)| (id, m.as_ref()))
            .ok_or_else(|| EnvError::ModuleNotFound(name.into()))
    }

    /// Find a module by name with the path selected by OCaml `IdTbl.find_name`.
    ///
    /// Local bindings resolve to `Pident(id)`, while opened bindings resolve to
    /// `Pdot(root, name, pos)` from the symbolic open layer.
    pub fn find_module_with_path(&self, name: &str) -> EnvResult<(Path, &ModuleDeclaration)> {
        self.data
            .modules
            .find_by_name_with_path(name)
            .map(|(path, decl)| (path, decl.as_ref()))
            .ok_or_else(|| EnvError::ModuleNotFound(name.into()))
    }

    fn first_dotted_component_path(path: &Path) -> Option<Path> {
        match path {
            Path::Pdot(parent, name, pos) => match parent.as_ref() {
                Path::Pident(_) => Some(Path::pdot_pos(parent.as_ref().clone(), *name, *pos)),
                _ => Self::first_dotted_component_path(parent),
            },
            Path::Pident(_) | Path::Papply(_, _) => None,
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
        // Only path resolution reads this, so keep `id` unchanged.
        self.scope_id = next_env_id();
        self.data_mut().scope_caches = std::rc::Rc::default();
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

    /// Iterate over visible module bindings.
    pub fn iter_modules(&self) -> impl Iterator<Item = (&Ident, &ModuleDeclaration)> {
        self.data.modules.iter().map(|(id, m)| (id, m.as_ref()))
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
        let Path::Pident(id) = path else {
            return None;
        };
        let components = self.data.module_components.find_by_ident(id)?;
        Some(f(components.as_ref()))
    }

    pub(crate) fn local_module_components_arc(
        &self,
        path: &Path,
    ) -> Option<Arc<super::env_lazy::StoredModuleComponents>> {
        let Path::Pident(id) = path else {
            return None;
        };
        // OCaml compiler/ml/env.ml:1573-1578 stores component thunks in the
        // component table and shares the forced lazy value. Return the stored
        // Arc directly so child component maps keep the same thunk instead of
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
                ModuleType::MtyAlias(_, alias_path) | ModuleType::MtyIdent(alias_path) => {
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
            visiting.push(path.clone());

            match path {
                Path::Pident(id) => {
                    env.data
                        .modules
                        .find_by_ident(id)
                        .or_else(|| {
                            // Fallback: try name-based lookup for stamp mismatches
                            env.data.modules.find_by_name(id.name())
                        })
                        .map(|m| m.as_ref())
                        .ok_or_else(|| EnvError::ModuleNotFound(id.name().into()))
                }
                Path::Pdot(parent, name, _) => {
                    let parent_md = lookup_module_inner(env, parent, visiting)?;
                    lookup_submodule_in_module_type(env, &parent_md.md_type, name, visiting)
                        .ok_or_else(|| EnvError::ModuleNotFound((*name).into()))
                }
                Path::Papply(_, _) => Err(EnvError::ModuleNotFound("(functor application)".into())),
            }
        }

        let mut visiting = smallvec::SmallVec::new();
        lookup_module_inner(self, path, &mut visiting)
    }

    /// Normalize a path by following module aliases.
    /// Equivalent to OCaml's `Env.normalize_path`.
    /// For `Pdot(p, s)`, first normalizes the prefix `p`, then checks
    /// if the resulting module is an alias and follows it.
    /// For `Pident(id)`, checks if it's a module alias and follows it.
    pub fn normalize_path(&self, path: &Path) -> Path {
        self.normalize_path_inner(path, 0)
    }

    /// Normalize the prefix of a value/extension path by following module aliases.
    /// Equivalent to OCaml's `Env.normalize_path_prefix`.
    pub fn normalize_path_prefix(&self, path: &Path) -> Path {
        match path {
            Path::Pdot(prefix, name, pos) => {
                let normalized_prefix = self.normalize_path(prefix);
                if normalized_prefix == **prefix {
                    path.clone()
                } else {
                    Path::Pdot(std::sync::Arc::new(normalized_prefix), *name, *pos)
                }
            }
            Path::Pident(_) => path.clone(),
            Path::Papply(_, _) => panic!("normalize_path_prefix called on Papply"),
        }
    }

    fn normalize_path_inner(&self, path: &Path, depth: usize) -> Path {
        if depth > 20 {
            return path.clone(); // Prevent infinite loops
        }
        // First, recursively normalize the prefix for Pdot paths
        let path = match path {
            Path::Pdot(p, s, pos) => {
                let p_norm = self.normalize_path_inner(p, depth + 1);
                if p_norm == **p {
                    path.clone()
                } else {
                    Path::Pdot(std::sync::Arc::new(p_norm), *s, *pos)
                }
            }
            _ => path.clone(),
        };

        // Then check if the path itself is a module alias
        if let Ok(md) = self.lookup_module(&path) {
            if let super::decl::ModuleType::MtyAlias(_, alias_path) = &md.md_type {
                return self.normalize_path_inner(alias_path, depth + 1);
            }
        }
        path
    }

    // ========================================================================
    // Module Type Bindings
    // ========================================================================

    /// Add a module type binding.
    pub fn add_modtype(&mut self, id: Ident, decl: ModtypeDeclaration) {
        self.bump_scope();
        let decl = Arc::new(decl);
        self.data_mut().modtypes.add(id, decl);
    }

    /// Find a module type by name.
    pub fn find_modtype(&self, name: &str) -> EnvResult<&ModtypeDeclaration> {
        self.data
            .modtypes
            .find_by_name(name)
            .map(|m| m.as_ref())
            .ok_or_else(|| EnvError::ModtypeNotFound(name.into()))
    }

    /// Find a module type by name, returning both the identifier and declaration.
    pub fn find_modtype_with_id(&self, name: &str) -> EnvResult<(&Ident, &ModtypeDeclaration)> {
        self.data
            .modtypes
            .find_by_name_with_id(name)
            .map(|(id, decl)| (id, decl.as_ref()))
            .ok_or_else(|| EnvError::ModtypeNotFound(name.into()))
    }

    /// Find a module type by name with the path selected by OCaml `IdTbl.find_name`.
    ///
    /// Local bindings resolve to `Pident(id)`, while opened bindings resolve to
    /// `Pdot(root, name, pos)` from the symbolic open layer.
    pub fn find_modtype_with_path(&self, name: &str) -> EnvResult<(Path, &ModtypeDeclaration)> {
        self.data
            .modtypes
            .find_by_name_with_path(name)
            .map(|(path, decl)| (path, decl.as_ref()))
            .ok_or_else(|| EnvError::ModtypeNotFound(name.into()))
    }

    /// Iterate over visible module type bindings.
    pub fn iter_modtypes(&self) -> impl Iterator<Item = (&Ident, &ModtypeDeclaration)> {
        self.data
            .modtypes
            .iter()
            .map(|(id, mtd)| (id, mtd.as_ref()))
    }

    /// Find a module type by path.
    pub fn lookup_modtype(&self, path: &Path) -> EnvResult<&ModtypeDeclaration> {
        match path {
            Path::Pident(id) => self
                .data
                .modtypes
                .find_by_ident(id)
                .map(|m| m.as_ref())
                .ok_or_else(|| EnvError::ModtypeNotFound(id.name().into())),
            Path::Pdot(parent, name, _) => {
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
            Path::Papply(_, _) => Err(EnvError::ModtypeNotFound("(functor application)".into())),
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
/// OCaml builds the predefined declarations once per process. The worker
/// store keeps one copy per worker: the first compilation builds it as a
/// store build, and later compilations clone the environment and replay
/// the build's effects instead of rebuilding every predefined type.
pub fn initial_env(ctx: &TypeContext) -> Env {
    if let Some((env, piece)) = ctx.thread_store().cached_initial_env() {
        ctx.touch_store_piece(&piece);
        return env;
    }
    let (env, piece) = ctx.build_in_store(|| build_initial_env(ctx));
    if let Some(piece) = piece {
        ctx.thread_store().publish_initial_env(env.clone(), piece);
    }
    env
}

fn build_initial_env(ctx: &TypeContext) -> Env {
    let mut env = Env::empty();

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
    let add_type_with_constrs = |env: &mut Env,
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
                        ctx.new_generic_constr(type_path.clone(), decl.type_params.clone())
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
            TypeKind::TypeRecord(labels, repr) => {
                let res_ty = ctx.new_generic_constr(type_path.clone(), decl.type_params.clone());
                for (pos, ld) in labels.iter().enumerate() {
                    let label_desc = LabelDescription {
                        lbl_name: ld.ld_id.name().to_string(),
                        lbl_runtime_name: ld.declaration_name(),
                        lbl_res: res_ty,
                        lbl_arg: crate::types::ctype::remap_label_type_to_params(
                            ctx,
                            ld.ld_type,
                            &decl.type_params,
                        ),
                        lbl_mut: ld.ld_mutable,
                        lbl_optional: ld.ld_optional,
                        lbl_pos: pos as i32,
                        lbl_all: crate::types::decl::LabelArrayRef(0),
                        lbl_repres: repr.clone(),
                        lbl_private: decl.type_private,
                        lbl_loc: ld.ld_loc,
                        lbl_attributes: ld.ld_attributes.clone(),
                    };
                    env.add_label(ld.ld_id, label_desc);
                }
            }
            _ => {}
        }
        env.add_type(id, decl);
    };

    use super::predef;

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
            ..decl_abstr(0, true)
        },
        ctx,
    );
    add_type_with_constrs(&mut env, predef::ident_int(), decl_abstr(0, true), ctx);
    add_type_with_constrs(&mut env, predef::ident_float(), decl_abstr(0, false), ctx);
    add_type_with_constrs(&mut env, predef::ident_bigint(), decl_abstr(0, false), ctx);
    add_type_with_constrs(&mut env, predef::ident_string(), decl_abstr(0, false), ctx);
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
            |env: &mut Env, id: Ident, args: Vec<TypeExprRef>, exn_ty: TypeExprRef| {
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
                    cstr_kind: ConstructorKind::Extension(path.clone()),
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
                vec![string_ty_for_exn, int_ty_for_exn, int_ty_for_exn].into(),
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
    env
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn initial_env_is_built_once_per_worker_store() {
        use crate::context::IdGenerator;
        use crate::types::predef;
        let first_ctx = TypeContext::new(std::sync::Arc::new(IdGenerator::new()));
        let first = initial_env(&first_ctx);
        assert!(
            first_ctx.thread_store().cached_initial_env().is_some(),
            "building the predefined environment must not touch compilation-local state"
        );
        let second_ctx = TypeContext::new(std::sync::Arc::new(IdGenerator::new()));
        let second = initial_env(&second_ctx);
        assert_ne!(first.id(), second.id());
        let int_path = Path::Pident(predef::ident_int());
        assert!(first.lookup_type(&int_path).is_ok());
        assert!(second.lookup_type(&int_path).is_ok());
        let option = second
            .lookup_type(&Path::Pident(predef::ident_option()))
            .expect("option");
        for param in &option.type_params {
            assert!(
                param.is_store(),
                "predef declarations live in the worker store"
            );
        }
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
            val_attributes: vec![],
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
            val_attributes: vec![],
            val_path: None,
        };
        let desc2 = ValueDescription {
            val_type: TypeExprRef(2),
            val_kind: super::super::decl::ValueKind::ValReg,
            val_loc: crate::types::DeclLoc::none(),
            val_attributes: vec![],
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
            val_attributes: vec![],
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
            val_attributes: vec![],
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
                md_type: ModuleType::MtyAlias(AliasPresence::MtaPresent, Path::pident(target_id)),
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
