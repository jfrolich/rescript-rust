//! The world of one build: everything every worker of the build reads and
//! none of them writes (docs/CHECKER_REDESIGN.md, J.3).
//!
//! OCaml keeps one `persistent_structures` table per process
//! (`compiler/ml/env.ml:669-678`). An in-process build checks many units on
//! several threads, so what OCaml keeps in that table lives here, once per
//! build generation:
//!
//! - the frozen pool (`types/shared_store.rs`): immutable type graphs, each
//!   complete before its pages are published;
//! - the unit table: one slot per dependency unit, holding the unit's
//!   internalized signature and the name index of that signature;
//! - the predefined environment's declarations (OCaml
//!   `Predef.build_initial_env`), frozen once per build.
//!
//! Frozen data other than a unit's is built on a [`ViewScratch`], a checker
//! context of the worker that no compilation uses, and moved into the pool by
//! [`freeze`]. A builder sees the world and its scratch context and never a
//! compilation, so what it builds is the same whichever worker builds it.
//!
//! Every cross-thread write is a `OnceLock::set` of a complete value or a
//! short `Mutex` section around a hash table.

use super::context::TypeContext;
use super::decl::{
    ConstructorDescription, ConstructorKind, LabelDescription, ModuleDeclaration, Signature,
    TypeDeclaration, ValueDescription,
};
use super::decl_loc::DeclLocKind;
use super::env::Env;
use super::env_lazy::SignatureIndex;
use super::shared_store::{
    SharedGraphParts, SharedGraphPayloads, SharedGraphSizes, SharedTypePool, shared_ref,
};
use super::type_expr::{
    AbbrevMemoRef, MutabilityRef, PackageLidsRef, RowDesc, RowDescRef, RowField, RowFieldRef,
    SHARED_REF_BITS, TypeArgList, TypeDesc, TypeExprRef, TypeRefList,
};
use super::variant_runtime::{Layout, LayoutRef};
use crate::cmi::persistent_env::PersStruct;
use crate::cmi::portable_types::{
    PortablePersStruct, SignatureRefMap, remap_module_decl_refs, remap_signature_refs,
    remap_type_decl_refs, remap_value_desc_refs,
};
use crate::fast_hash::AHashMap;
use crate::ident::Ident;
use crate::parser::longident::Longident;
use std::cell::RefCell;
use std::sync::atomic::{AtomicU32, Ordering};
use std::sync::{Arc, Mutex, OnceLock};

/// One unit of the build, internalized into the frozen pool.
pub(crate) struct UnitSlot {
    /// Keeps the portable struct alive so its address cannot be reused as a
    /// key for another unit.
    _owner: Arc<PortablePersStruct>,
    /// `None` when the unit's graph could not be placed in the pool.
    ps: OnceLock<Option<Arc<PersStruct>>>,
    /// Name index of `ps.ps_sig`, built by the first worker that asks.
    index: OnceLock<Arc<SignatureIndex>>,
}

/// One per build generation; workers and contexts hold `Arc<World>`.
pub(crate) struct World {
    generation: u64,
    pool: SharedTypePool,
    /// Units internalized in this build, by the identity of their stored
    /// form.
    units: Mutex<AHashMap<usize, Arc<UnitSlot>>>,
    /// The same slots by the address of the internalized signature (kept
    /// alive by the slot), for a reader that holds only the signature.
    unit_signatures: Mutex<AHashMap<usize, Arc<UnitSlot>>>,
    /// The predefined environment's declarations, frozen by the first
    /// worker that needs them.
    predef: OnceLock<Arc<PredefView>>,
    /// How many times this world built `predef` (1 once it is set).
    predef_builds: AtomicU32,
}

const fn assert_send_sync<T: Send + Sync>() {}
const _: () = assert_send_sync::<World>();
const _: () = assert_send_sync::<PredefView>();

static CURRENT: Mutex<Option<Arc<World>>> = Mutex::new(None);

#[cfg(test)]
thread_local! {
    /// Hash probes of the unit table made by this thread.
    static UNIT_TABLE_PROBES: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
}

#[cfg(test)]
thread_local! {
    /// Probes of a freeze's position map made by this thread.
    static FREEZE_PROBES: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
}

#[inline]
fn count_unit_probe() {
    #[cfg(test)]
    UNIT_TABLE_PROBES.with(|probes| probes.set(probes.get() + 1));
}

impl World {
    fn new(generation: u64) -> Self {
        World {
            generation,
            pool: SharedTypePool::new(),
            units: Mutex::new(AHashMap::new()),
            unit_signatures: Mutex::new(AHashMap::new()),
            predef: OnceLock::new(),
            predef_builds: AtomicU32::new(0),
        }
    }

    /// The world of the current build generation
    /// (`thread_store::build_generation`). The world of an earlier build is
    /// replaced, and freed once the last worker holding it lets go.
    pub(crate) fn current() -> Arc<World> {
        let generation = super::thread_store::build_generation();
        let mut slot = CURRENT.lock().unwrap();
        match &*slot {
            Some(world) if world.generation == generation => world.clone(),
            _ => {
                let world = Arc::new(World::new(generation));
                *slot = Some(world.clone());
                world
            }
        }
    }

    /// The frozen pool.
    #[inline]
    pub(crate) fn pool(&self) -> &SharedTypePool {
        &self.pool
    }

    /// The internalization of unit `pps`, built with `build` the first time
    /// any worker asks. Concurrent requests for one unit wait for the first
    /// builder. `None` when `build` could not place the graph in the pool.
    ///
    /// One hash probe, whatever the number of units.
    pub(crate) fn unit(
        &self,
        pps: &Arc<PortablePersStruct>,
        build: impl FnOnce() -> Option<Arc<PersStruct>>,
    ) -> Option<Arc<PersStruct>> {
        count_unit_probe();
        let slot = self
            .units
            .lock()
            .unwrap()
            .entry(Arc::as_ptr(pps) as usize)
            .or_insert_with(|| {
                Arc::new(UnitSlot {
                    _owner: pps.clone(),
                    ps: OnceLock::new(),
                    index: OnceLock::new(),
                })
            })
            .clone();
        slot.ps
            .get_or_init(|| {
                let ps = build()?;
                self.unit_signatures
                    .lock()
                    .unwrap()
                    .insert(Arc::as_ptr(&ps.ps_sig) as usize, slot.clone());
                Some(ps)
            })
            .clone()
    }

    fn unit_of_signature(&self, sig: &Arc<Signature>) -> Option<Arc<UnitSlot>> {
        count_unit_probe();
        self.unit_signatures
            .lock()
            .unwrap()
            .get(&(Arc::as_ptr(sig) as usize))
            .cloned()
    }

    /// Whether `sig` is the signature of a unit of this world: its items are
    /// frozen and keep one address for the whole build.
    pub(crate) fn is_unit_signature(&self, sig: &Arc<Signature>) -> bool {
        self.unit_of_signature(sig).is_some()
    }

    /// The name index of a unit's signature, built once per build; `None`
    /// when `sig` is no unit's signature. One hash probe, whatever the number
    /// of units.
    pub(crate) fn unit_signature_index(&self, sig: &Arc<Signature>) -> Option<Arc<SignatureIndex>> {
        let slot = self.unit_of_signature(sig)?;
        Some(
            slot.index
                .get_or_init(|| Arc::new(SignatureIndex::build(sig)))
                .clone(),
        )
    }
}

// ============================================================================
// Freezing
// ============================================================================

/// A value whose type nodes can be moved into the frozen pool.
///
/// `rewrite_handles` renames every type handle and every variant-layout
/// handle the value holds, each exactly once. [`freeze`] calls it twice: once
/// to learn which nodes the value reaches (renaming them to positions in the
/// graph being built) and once to give them their pool addresses.
pub(crate) trait FrozenExport {
    fn rewrite_handles(&mut self, map: &impl SignatureRefMap);
}

impl FrozenExport for Signature {
    fn rewrite_handles(&mut self, map: &impl SignatureRefMap) {
        remap_signature_refs(self, map);
    }
}

impl FrozenExport for ValueDescription {
    fn rewrite_handles(&mut self, map: &impl SignatureRefMap) {
        remap_value_desc_refs(self, map);
    }
}

impl FrozenExport for TypeDeclaration {
    fn rewrite_handles(&mut self, map: &impl SignatureRefMap) {
        remap_type_decl_refs(self, map);
    }
}

impl FrozenExport for ModuleDeclaration {
    fn rewrite_handles(&mut self, map: &impl SignatureRefMap) {
        remap_module_decl_refs(self, map);
    }
}

impl FrozenExport for ConstructorDescription {
    fn rewrite_handles(&mut self, map: &impl SignatureRefMap) {
        self.cstr_res = map.ty(self.cstr_res);
        for existential in &mut self.cstr_existentials {
            *existential = map.ty(*existential);
        }
        for arg in &mut self.cstr_args {
            *arg = map.ty(*arg);
        }
        match &mut self.cstr_kind {
            ConstructorKind::Ordinary(reference) => {
                reference.variant = map.layout(reference.variant)
            }
            ConstructorKind::Extension(_) => {}
        }
        if let Some(inlined) = &mut self.cstr_inlined {
            inlined.rewrite_handles(map);
        }
    }
}

/// `lbl_all` names the label array of the record and is not a type handle:
/// it is left as it is, so a frozen label keeps the array it was built with.
impl FrozenExport for LabelDescription {
    fn rewrite_handles(&mut self, map: &impl SignatureRefMap) {
        self.lbl_res = map.ty(self.lbl_res);
        self.lbl_arg = map.ty(self.lbl_arg);
    }
}

impl<T: FrozenExport> FrozenExport for Vec<T> {
    fn rewrite_handles(&mut self, map: &impl SignatureRefMap) {
        for value in self {
            value.rewrite_handles(map);
        }
    }
}

impl<T: FrozenExport + Clone> FrozenExport for Arc<T> {
    fn rewrite_handles(&mut self, map: &impl SignatureRefMap) {
        Arc::make_mut(self).rewrite_handles(map);
    }
}

/// Why a value cannot be frozen. The value is consumed either way.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Unfreezable {
    /// A node of a worker store: only that worker can read it.
    WorkerStoreNode,
    /// A `Tsubst` node: a copy session was open on the scratch context.
    CopyInProgress,
    /// An arrow label located in the scratch context's own location table.
    LocalLocation,
    /// A package constraint name only a parse tree can resolve.
    UnresolvedName,
    /// The pool has no room for the graph.
    PoolFull,
}

/// A value whose every type node is frozen.
pub(crate) struct Frozen<T> {
    pub(crate) value: T,
    /// Base index of the graph holding the nodes the freeze created; `None`
    /// when the value reached only nodes that were frozen already.
    pub(crate) graph: Option<u32>,
    /// Number of nodes the freeze created.
    pub(crate) nodes: usize,
}

/// The graph a freeze is building: nodes and payloads at dense positions,
/// relocated to pool addresses once their number is known.
#[derive(Default)]
struct FreezeGraph {
    nodes: Vec<(TypeDesc, i32)>,
    payloads: SharedGraphPayloads,
    layouts: Vec<Layout>,
    /// Scratch handle -> position in `nodes`: one stored node per scratch
    /// node, however many positions name it (CHECKER_REDESIGN.md, I.3.3
    /// rule 5).
    positions: AHashMap<TypeExprRef, u32>,
    layout_positions: AHashMap<LayoutRef, u32>,
    /// Scratch mutability cell -> its frozen cell, so fields that shared a
    /// cell still share one.
    cells: AHashMap<MutabilityRef, MutabilityRef>,
    /// Nodes with a position whose descriptor is not copied yet.
    pending: Vec<(TypeExprRef, u32)>,
    failure: Option<Unfreezable>,
}

struct Freezer<'a> {
    ctx: &'a TypeContext,
    pool: &'a SharedTypePool,
    graph: RefCell<FreezeGraph>,
}

impl FreezeGraph {
    /// The handle that stands for `r` in the graph: `r` itself when it is
    /// frozen already, else its position (an untagged handle).
    fn ty(&mut self, r: TypeExprRef) -> TypeExprRef {
        if r.is_shared() {
            return r;
        }
        if r.is_store() {
            self.failure.get_or_insert(Unfreezable::WorkerStoreNode);
            return r;
        }
        #[cfg(test)]
        FREEZE_PROBES.with(|probes| probes.set(probes.get() + 1));
        if let Some(&position) = self.positions.get(&r) {
            return TypeExprRef::from_usize(position as usize);
        }
        let position = self.nodes.len() as u32;
        self.nodes.push((TypeDesc::Tnil, 0));
        self.positions.insert(r, position);
        self.pending.push((r, position));
        TypeExprRef::from_usize(position as usize)
    }

    fn list(&mut self, items: impl Iterator<Item = TypeExprRef>) -> TypeRefList {
        let start = self.payloads.lists.len();
        for item in items {
            let item = self.ty(item);
            self.payloads.lists.push(item);
        }
        TypeRefList::from_parts(start as u32, self.payloads.lists.len() - start)
    }

    fn lid(&mut self, freezer: &Freezer<'_>, lid: &Longident) -> Longident {
        let mut name = |idx| {
            // A name the pool owns already stays; any other must be one the
            // scratch context can spell.
            if freezer.pool.longident_name(idx).is_some() {
                return idx;
            }
            match freezer.ctx.resolve_cmi_longident_component(idx) {
                Some(name) => freezer.pool.intern_longident_name(&name),
                None => {
                    self.failure.get_or_insert(Unfreezable::UnresolvedName);
                    idx
                }
            }
        };
        fn walk(
            lid: &Longident,
            name: &mut impl FnMut(crate::intern::StrIdx) -> crate::intern::StrIdx,
        ) -> Longident {
            match lid {
                Longident::Lident(n) => Longident::Lident(name(*n)),
                Longident::Ldot(parent, n) => {
                    let parent = walk(parent, name);
                    Longident::Ldot(Box::new(parent), name(*n))
                }
                Longident::Lapply(f, a) => {
                    let f = walk(f, name);
                    Longident::Lapply(Box::new(f), Box::new(walk(a, name)))
                }
            }
        }
        walk(lid, &mut name)
    }

    /// The descriptor of scratch node `r`, over positions in this graph.
    fn describe(&mut self, freezer: &Freezer<'_>, r: TypeExprRef) -> TypeDesc {
        let ctx = freezer.ctx;
        match ctx.get_desc(r).into_desc() {
            TypeDesc::Tvar(name) => TypeDesc::Tvar(name),
            TypeDesc::Tunivar(name) => TypeDesc::Tunivar(name),
            TypeDesc::Tnil => TypeDesc::Tnil,
            TypeDesc::Tarrow { args, ret } => {
                let start = self.payloads.args.len();
                for arg in ctx.type_args(args).iter() {
                    if arg.label().loc().kind() == DeclLocKind::Local {
                        self.failure.get_or_insert(Unfreezable::LocalLocation);
                    }
                    let typ = self.ty(arg.typ);
                    self.payloads.args.push(arg.with_type(typ));
                }
                let args =
                    TypeArgList::from_parts(start as u32, self.payloads.args.len() - start);
                TypeDesc::Tarrow {
                    args,
                    ret: self.ty(ret),
                }
            }
            TypeDesc::Ttuple(items) => TypeDesc::Ttuple(self.list(ctx.type_list(items).iter())),
            TypeDesc::Tconstr { path, args, .. } => TypeDesc::Tconstr {
                path,
                args: self.list(ctx.type_list(args).iter()),
                // Placed at the node's own index when the graph is relocated.
                abbrev: AbbrevMemoRef::nil(),
            },
            TypeDesc::Tobject { fields } => TypeDesc::Tobject {
                fields: self.ty(fields),
            },
            TypeDesc::Tfield {
                name,
                mutability,
                typ,
                rest,
            } => {
                let cell = ctx.mutability_ref_repr(mutability);
                let mutability = if cell.is_persistent() {
                    cell
                } else {
                    *self.cells.entry(cell).or_insert_with(|| {
                        MutabilityRef::new_persistent(ctx.mutability_repr(cell))
                    })
                };
                TypeDesc::Tfield {
                    name,
                    mutability,
                    typ: self.ty(typ),
                    rest: self.ty(rest),
                }
            }
            TypeDesc::Tlink(target) => TypeDesc::Tlink(self.ty(target)),
            TypeDesc::Tsubst(target) => {
                self.failure.get_or_insert(Unfreezable::CopyInProgress);
                TypeDesc::Tsubst(target)
            }
            TypeDesc::Tpoly { body, vars } => TypeDesc::Tpoly {
                body: self.ty(body),
                vars: self.list(ctx.type_list(vars).iter()),
            },
            TypeDesc::Tpackage { path, lids, args } => {
                let lids = ctx
                    .package_lids(lids)
                    .iter()
                    .map(|lid| self.lid(freezer, lid))
                    .collect();
                let args = self.list(ctx.type_list(args).iter());
                let index = self.payloads.lids.len();
                self.payloads.lids.push(lids);
                TypeDesc::Tpackage {
                    path,
                    lids: PackageLidsRef::from_raw(index as u32),
                    args,
                }
            }
            TypeDesc::Tvariant(row) => {
                let row = ctx.row_desc(row);
                let row_fields = row
                    .row_fields
                    .iter()
                    .map(|(label, field)| {
                        // A frozen row has no field cell: the field is stored
                        // as it stands (`Btype.row_field_repr`).
                        let field = match super::btype::row_field_repr(ctx, field) {
                            RowField::Rpresent(payload) => {
                                RowField::Rpresent(payload.map(|r| self.ty(r)))
                            }
                            RowField::Reither {
                                constant,
                                types,
                                matched,
                                ..
                            } => RowField::Reither {
                                constant,
                                types: types.iter().map(|r| self.ty(*r)).collect(),
                                matched,
                                link: RowFieldRef::null(),
                            },
                            RowField::Rabsent => RowField::Rabsent,
                        };
                        (label.clone(), field)
                    })
                    .collect();
                let row_more = self.ty(row.row_more);
                let row_name = row
                    .row_name
                    .as_ref()
                    .map(|(path, args)| (*path, args.iter().map(|r| self.ty(*r)).collect()));
                let index = self.payloads.rows.len();
                self.payloads.rows.push(RowDesc {
                    row_fields,
                    row_more,
                    row_closed: row.row_closed,
                    row_fixed: row.row_fixed,
                    row_name,
                });
                TypeDesc::Tvariant(RowDescRef::from_raw(index as u32))
            }
        }
    }

    fn sizes(&self) -> SharedGraphSizes {
        SharedGraphSizes {
            nodes: self.nodes.len(),
            list_items: self.payloads.lists.len(),
            arg_items: self.payloads.args.len(),
            rows: self.payloads.rows.len(),
            lids: self.payloads.lids.len(),
            layouts: self.layouts.len(),
        }
    }
}

impl SignatureRefMap for Freezer<'_> {
    fn ty(&self, r: TypeExprRef) -> TypeExprRef {
        self.graph.borrow_mut().ty(r)
    }

    fn layout(&self, r: LayoutRef) -> LayoutRef {
        if r.is_shared() {
            return r;
        }
        let mut graph = self.graph.borrow_mut();
        if r.is_store() {
            graph.failure.get_or_insert(Unfreezable::WorkerStoreNode);
            return r;
        }
        if let Some(&position) = graph.layout_positions.get(&r) {
            return LayoutRef::from_usize(position as usize);
        }
        let position = graph.layouts.len() as u32;
        graph.layouts.push(self.ctx.variant_layout(r));
        graph.layout_positions.insert(r, position);
        LayoutRef::from_usize(position as usize)
    }
}

/// Positions of a freeze become addresses of the graph published at the
/// base; handles that were frozen before the freeze stay.
struct Relocation {
    base: u32,
}

impl SignatureRefMap for Relocation {
    fn ty(&self, r: TypeExprRef) -> TypeExprRef {
        if r.is_store() {
            r
        } else {
            shared_ref(self.base, r.index())
        }
    }

    fn layout(&self, r: LayoutRef) -> LayoutRef {
        if r.is_store() {
            r
        } else {
            LayoutRef::from_shared_index(self.base + r.index() as u32)
        }
    }
}

/// Give the nodes and payloads of a freeze their pool addresses.
fn relocate(
    nodes: &mut [(TypeDesc, i32)],
    payloads: &mut SharedGraphPayloads,
    sizes: SharedGraphSizes,
    to: &Relocation,
) {
    let base = to.base;
    let ty = |r: &mut TypeExprRef| *r = to.ty(*r);
    let list = |xs: &mut TypeRefList| {
        *xs = TypeRefList::from_parts(
            SHARED_REF_BITS | (base + sizes.lists_start() as u32 + xs.raw_start()),
            xs.len(),
        )
    };
    for (position, (desc, _)) in nodes.iter_mut().enumerate() {
        match desc {
            TypeDesc::Tarrow { args, ret } => {
                *args = TypeArgList::from_parts(
                    SHARED_REF_BITS | (base + sizes.args_start() as u32 + args.raw_start()),
                    args.len(),
                );
                ty(ret);
            }
            TypeDesc::Ttuple(items) => list(items),
            TypeDesc::Tconstr { args, abbrev, .. } => {
                list(args);
                *abbrev = AbbrevMemoRef::from_shared_index(base + position as u32);
            }
            TypeDesc::Tobject { fields } => ty(fields),
            TypeDesc::Tfield { typ, rest, .. } => {
                ty(typ);
                ty(rest);
            }
            TypeDesc::Tlink(target) | TypeDesc::Tsubst(target) => ty(target),
            TypeDesc::Tvariant(row) => {
                *row = RowDescRef::from_raw(
                    SHARED_REF_BITS | (base + sizes.rows_start() as u32 + row.raw()),
                )
            }
            TypeDesc::Tpoly { body, vars } => {
                ty(body);
                list(vars);
            }
            TypeDesc::Tpackage { lids, args, .. } => {
                *lids = PackageLidsRef::from_raw(
                    SHARED_REF_BITS | (base + sizes.lids_start() as u32 + lids.raw()),
                );
                list(args);
            }
            TypeDesc::Tvar(_) | TypeDesc::Tunivar(_) | TypeDesc::Tnil => {}
        }
    }
    for item in &mut payloads.lists {
        ty(item);
    }
    for arg in &mut payloads.args {
        *arg = arg.with_type(to.ty(arg.typ));
    }
    for row in &mut payloads.rows {
        ty(&mut row.row_more);
        for (_, field) in &mut row.row_fields {
            match field {
                RowField::Rpresent(Some(r)) => ty(r),
                RowField::Reither { types, .. } => types.iter_mut().for_each(ty),
                RowField::Rpresent(None) | RowField::Rabsent => {}
            }
        }
        if let Some((_, args)) = &mut row.row_name {
            args.iter_mut().for_each(ty);
        }
    }
}

/// Move every type node and variant layout `value` reaches on the scratch
/// context into one new graph of `world`'s pool, and rename the value's
/// handles to it.
///
/// What the walk keeps (CHECKER_REDESIGN.md, I.3.3 rules 5 and 8):
///
/// - one stored node per scratch node: a node named at two positions is one
///   stored node, two equal nodes stay two;
/// - each node's descriptor and level as they stand, links included (a
///   non-generic node stays non-generic);
/// - handles that are frozen already (nodes of units or of earlier freezes
///   of this world) are kept, not copied;
/// - a mutability cell shared by two fields is one frozen cell; a row field
///   is stored resolved, as an interface is saved.
///
/// What the caller owes: `value` holds no declaration location of the
/// scratch context's own table (arrow labels are checked, declaration fields
/// are not), and shape identities in its declarations are process-wide.
/// The predefined declarations satisfy both: they have no locations and
/// their shapes are the static predefined ones.
///
/// Cost: one hash probe per handle of the value and of the copied nodes,
/// one descriptor read and one push per copied node, one pass over the
/// copied nodes to relocate them. Nothing depends on the size of the pool.
pub(crate) fn freeze<T: FrozenExport>(
    world: &World,
    scratch: &ViewScratch,
    mut value: T,
) -> Result<Frozen<T>, Unfreezable> {
    let freezer = Freezer {
        ctx: &scratch.ctx,
        pool: &world.pool,
        graph: RefCell::new(FreezeGraph::default()),
    };
    value.rewrite_handles(&freezer);
    loop {
        let next = freezer.graph.borrow_mut().pending.pop();
        let Some((node, position)) = next else {
            break;
        };
        let mut graph = freezer.graph.borrow_mut();
        let desc = graph.describe(&freezer, node);
        graph.nodes[position as usize] = (desc, freezer.ctx.get_level(node));
    }
    let mut graph = freezer.graph.into_inner();
    if let Some(failure) = graph.failure {
        return Err(failure);
    }
    let sizes = graph.sizes();
    if sizes.nodes == 0 && sizes.layouts == 0 {
        return Ok(Frozen {
            value,
            graph: None,
            nodes: 0,
        });
    }
    let base = world
        .pool
        .publish(sizes, |base| {
            relocate(
                &mut graph.nodes,
                &mut graph.payloads,
                sizes,
                &Relocation { base },
            );
            SharedGraphParts {
                nodes: std::mem::take(&mut graph.nodes),
                payloads: std::mem::take(&mut graph.payloads),
                layouts: std::mem::take(&mut graph.layouts),
                locations: Default::default(),
                carried: Default::default(),
            }
        })
        .ok_or(Unfreezable::PoolFull)?;
    value.rewrite_handles(&Relocation { base });
    Ok(Frozen {
        value,
        graph: Some(base),
        nodes: sizes.nodes,
    })
}

// ============================================================================
// Scratch contexts
// ============================================================================

/// A checker context owned by a worker thread that no compilation uses:
/// frozen data is built on it and then moved into the pool by [`freeze`].
/// Only this module can reach the context, so a builder that receives a
/// `ViewScratch` cannot read a compilation's state through it.
pub(crate) struct ViewScratch {
    ctx: TypeContext,
    generation: u64,
}

thread_local! {
    static SCRATCH: RefCell<Option<ViewScratch>> = const { RefCell::new(None) };
}

impl ViewScratch {
    fn new() -> Self {
        ViewScratch {
            generation: super::thread_store::build_generation(),
            ctx: TypeContext::new(Arc::new(crate::context::IdGenerator::new())),
        }
    }

    /// The context to build on.
    pub(crate) fn ctx(&self) -> &TypeContext {
        &self.ctx
    }

    /// Run `build` on this worker's scratch context, creating it on first
    /// use in a build. A build must not start another one on the same
    /// thread.
    pub(crate) fn with<R>(build: impl FnOnce(&ViewScratch) -> R) -> R {
        SCRATCH.with(|slot| {
            let mut slot = slot
                .try_borrow_mut()
                .expect("a scratch build started another scratch build");
            let generation = super::thread_store::build_generation();
            if slot
                .as_ref()
                .is_none_or(|scratch| scratch.generation != generation)
            {
                // Drop the scratch of an earlier build before leasing a
                // store for the new one.
                *slot = None;
                *slot = Some(ViewScratch::new());
            }
            build(slot.as_ref().expect("scratch context"))
        })
    }
}

// ============================================================================
// The predefined environment
// ============================================================================

/// One addition to the predefined environment, in the order
/// `Predef.build_initial_env` makes them (compiler/ml/predef.ml:239-424).
#[derive(Clone)]
pub(crate) enum PredefItem {
    Type(Ident, Arc<TypeDeclaration>),
    Constructor(Ident, ConstructorDescription),
}

impl FrozenExport for PredefItem {
    fn rewrite_handles(&mut self, map: &impl SignatureRefMap) {
        match self {
            PredefItem::Type(_, decl) => decl.rewrite_handles(map),
            PredefItem::Constructor(_, constructor) => constructor.rewrite_handles(map),
        }
    }
}

/// The predefined declarations of a build. Every type node in them is
/// frozen, so any worker's environment can hold them.
///
/// `Predef` declares no record type, so the view has no label array.
pub(crate) struct PredefView {
    items: Vec<PredefItem>,
}

impl PredefView {
    /// The environment holding these declarations (worker-local tables over
    /// frozen declarations; allocates no type node).
    fn env(&self) -> Env {
        let mut env = Env::empty();
        for item in &self.items {
            match item {
                PredefItem::Type(id, decl) => env.add_type(*id, decl.clone()),
                PredefItem::Constructor(id, constructor) => {
                    env.add_constructor(*id, constructor.clone())
                }
            }
        }
        env
    }
}

thread_local! {
    /// This worker's predefined environment and the world it was built over.
    static WORKER_INITIAL_ENV: RefCell<Option<(Arc<World>, Env)>> = const { RefCell::new(None) };
}

impl World {
    /// The predefined declarations, built on the calling worker's scratch
    /// context and frozen the first time any worker asks.
    pub(crate) fn predef(&self) -> &Arc<PredefView> {
        self.predef.get_or_init(|| {
            self.predef_builds.fetch_add(1, Ordering::Relaxed);
            let frozen = ViewScratch::with(|scratch| {
                freeze(
                    self,
                    scratch,
                    super::env::predef_declarations(scratch.ctx()),
                )
            })
            .unwrap_or_else(|failure| {
                panic!("the predefined environment cannot be frozen: {failure:?}")
            });
            crate::perf_counters::world::record_predef_build(frozen.nodes);
            Arc::new(PredefView {
                items: frozen.value,
            })
        })
    }

    /// The initial environment of a compilation on this worker: the worker
    /// builds its tables over the frozen declarations once per build and
    /// every compilation starts from a copy.
    pub(crate) fn initial_env(self: &Arc<World>) -> Env {
        WORKER_INITIAL_ENV.with(|slot| {
            if let Some((world, env)) = &*slot.borrow()
                && Arc::ptr_eq(world, self)
            {
                return env.clone();
            }
            let env = self.predef().env();
            *slot.borrow_mut() = Some((self.clone(), env.clone()));
            env
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::context::IdGenerator;
    use crate::types::context::TypeContext;
    use std::sync::atomic::{AtomicUsize, Ordering};

    fn unit_probes() -> u64 {
        UNIT_TABLE_PROBES.with(|probes| probes.get())
    }

    fn pers_struct(name: &str) -> PersStruct {
        PersStruct {
            ps_name: name.into(),
            ps_sig: Arc::new(vec![]),
            ps_filename: format!("{name}.res"),
            ps_deprecated: None,
            ps_crcs: vec![],
            ps_alias_rewrites: Default::default(),
        }
    }

    /// `count` units registered in a fresh world, with their signatures.
    fn world_with_units(
        ctx: &TypeContext,
        count: usize,
    ) -> (World, Vec<(Arc<PortablePersStruct>, Arc<Signature>)>) {
        let world = World::new(u64::MAX);
        let units = (0..count)
            .map(|i| {
                let ps = pers_struct(&format!("Unit{i}"));
                let pps = Arc::new(crate::cmi::portable_types::serialize_pers_struct(
                    &ps, ctx, None,
                ));
                let ps = world.unit(&pps, || Some(Arc::new(ps))).unwrap();
                (pps, ps.ps_sig.clone())
            })
            .collect();
        (world, units)
    }

    #[test]
    fn unit_is_internalized_once_for_all_threads() {
        let ctx = TypeContext::new(Arc::new(IdGenerator::new()));
        let world = Arc::new(World::new(u64::MAX));
        let pps = Arc::new(crate::cmi::portable_types::serialize_pers_struct(
            &pers_struct("Shared"),
            &ctx,
            None,
        ));
        let builds = Arc::new(AtomicUsize::new(0));
        let barrier = Arc::new(std::sync::Barrier::new(8));
        let threads: Vec<_> = (0..8)
            .map(|_| {
                let (world, pps, builds, barrier) =
                    (world.clone(), pps.clone(), builds.clone(), barrier.clone());
                std::thread::spawn(move || {
                    barrier.wait();
                    world
                        .unit(&pps, || {
                            builds.fetch_add(1, Ordering::SeqCst);
                            Some(Arc::new(pers_struct("Shared")))
                        })
                        .unwrap()
                })
            })
            .collect();
        let units: Vec<_> = threads.into_iter().map(|t| t.join().unwrap()).collect();
        assert_eq!(builds.load(Ordering::SeqCst), 1);
        for unit in &units {
            assert!(Arc::ptr_eq(unit, &units[0]));
            assert!(world.is_unit_signature(&unit.ps_sig));
        }
        let index = world.unit_signature_index(&units[0].ps_sig).unwrap();
        assert!(Arc::ptr_eq(
            &index,
            &world.unit_signature_index(&units[0].ps_sig).unwrap()
        ));
        assert!(
            world
                .unit_signature_index(&Arc::new(Signature::new()))
                .is_none()
        );
    }

    /// Step count: a unit lookup is one hash probe whether the world holds
    /// ten units or five thousand.
    #[test]
    fn unit_lookups_cost_one_probe_whatever_the_number_of_units() {
        let ctx = TypeContext::new(Arc::new(IdGenerator::new()));
        let mut steps = Vec::new();
        for count in [10, 5_000] {
            let (world, units) = world_with_units(&ctx, count);
            let (pps, sig) = &units[count / 2];
            let before = unit_probes();
            world
                .unit(pps, || panic!("the unit is already internalized"))
                .unwrap();
            let by_unit = unit_probes() - before;
            let before = unit_probes();
            world.unit_signature_index(sig).unwrap();
            let by_signature = unit_probes() - before;
            let before = unit_probes();
            assert!(!world.is_unit_signature(&Arc::new(Signature::new())));
            let miss = unit_probes() - before;
            steps.push((by_unit, by_signature, miss));
        }
        assert_eq!(steps, [(1, 1, 1), (1, 1, 1)]);
    }

    /// Step count: a compilation asks the world for a signature's index
    /// once; later requests do not reach the unit table.
    #[test]
    fn a_compilation_reads_a_unit_index_from_the_world_once() {
        let ctx = TypeContext::new(Arc::new(IdGenerator::new()));
        let ps = pers_struct("Indexed");
        let pps = Arc::new(crate::cmi::portable_types::serialize_pers_struct(
            &ps, &ctx, None,
        ));
        let ps = ctx.world().unit(&pps, || Some(Arc::new(ps))).unwrap();
        let before = unit_probes();
        let first = ctx.signature_index(&ps.ps_sig);
        assert_eq!(unit_probes() - before, 1);
        let before = unit_probes();
        for _ in 0..100 {
            assert!(Arc::ptr_eq(&first, &ctx.signature_index(&ps.ps_sig)));
        }
        assert_eq!(unit_probes() - before, 0);
        assert!(Arc::ptr_eq(
            &first,
            &ctx.world().unit_signature_index(&ps.ps_sig).unwrap()
        ));
    }

    fn scratch_of(ctx: TypeContext) -> ViewScratch {
        ViewScratch {
            ctx,
            generation: u64::MAX,
        }
    }

    fn int(ctx: &TypeContext) -> TypeExprRef {
        ctx.new_generic_predef_constr(crate::types::predef::path_int(), vec![])
    }

    /// A value over a handful of handles, for freezing.
    struct Handles(Vec<TypeExprRef>);

    impl FrozenExport for Handles {
        fn rewrite_handles(&mut self, map: &impl SignatureRefMap) {
            for r in &mut self.0 {
                *r = map.ty(*r);
            }
        }
    }

    /// The structure under `r`, with a number per distinct node (so sharing
    /// shows) and each node's level.
    fn shape(ctx: &TypeContext, r: TypeExprRef, seen: &mut Vec<TypeExprRef>) -> String {
        if let Some(position) = seen.iter().position(|s| *s == r) {
            return format!("#{position}");
        }
        seen.push(r);
        let position = seen.len() - 1;
        let level = ctx.get_level(r);
        let children = |seen: &mut Vec<TypeExprRef>, rs: Vec<TypeExprRef>| {
            rs.into_iter()
                .map(|r| shape(ctx, r, seen))
                .collect::<Vec<_>>()
                .join(", ")
        };
        let body = match ctx.get_desc(r).into_desc() {
            TypeDesc::Tvar(name) => format!("var {name:?}"),
            TypeDesc::Tunivar(name) => format!("univar {name:?}"),
            TypeDesc::Tnil => "nil".to_string(),
            TypeDesc::Tarrow { args, ret } => {
                let args: Vec<_> = ctx.type_args(args).iter().collect();
                let labels: Vec<_> = args.iter().map(|a| format!("{:?}", a.label())).collect();
                let types = children(seen, args.iter().map(|a| a.typ).collect());
                format!("arrow [{}] ({types}) -> {}", labels.join(","), shape(ctx, ret, seen))
            }
            TypeDesc::Ttuple(items) => {
                format!("tuple ({})", children(seen, ctx.type_list(items).iter().collect()))
            }
            TypeDesc::Tconstr { path, args, abbrev } => {
                assert!(matches!(
                    ctx.get_abbrev_memo(abbrev),
                    crate::types::type_expr::AbbrevMemo::Mnil
                ));
                format!(
                    "constr {path:?} ({})",
                    children(seen, ctx.type_list(args).iter().collect())
                )
            }
            TypeDesc::Tobject { fields } => format!("object {}", shape(ctx, fields, seen)),
            TypeDesc::Tfield {
                name,
                mutability,
                typ,
                rest,
            } => format!(
                "field {name:?} {:?} {} ; {}",
                ctx.mutability_repr(mutability),
                shape(ctx, typ, seen),
                shape(ctx, rest, seen)
            ),
            TypeDesc::Tlink(target) => format!("link {}", shape(ctx, target, seen)),
            TypeDesc::Tsubst(target) => format!("subst {}", shape(ctx, target, seen)),
            TypeDesc::Tpoly { body, vars } => format!(
                "poly ({}) {}",
                children(seen, ctx.type_list(vars).iter().collect()),
                shape(ctx, body, seen)
            ),
            TypeDesc::Tpackage { path, args, .. } => format!(
                "package {path:?} ({})",
                children(seen, ctx.type_list(args).iter().collect())
            ),
            TypeDesc::Tvariant(row) => {
                let row = ctx.row_desc(row);
                let fields: Vec<_> = row
                    .row_fields
                    .iter()
                    .map(|(label, field)| match field {
                        RowField::Rpresent(None) => format!("{label}"),
                        RowField::Rpresent(Some(r)) => format!("{label} {}", shape(ctx, *r, seen)),
                        RowField::Reither { types, .. } => {
                            format!("{label}? ({})", children(seen, types.clone()))
                        }
                        RowField::Rabsent => format!("{label}-"),
                    })
                    .collect();
                format!(
                    "variant [{}] closed={} more={}",
                    fields.join(" | "),
                    row.row_closed,
                    shape(ctx, row.row_more, seen)
                )
            }
        };
        format!("#{position}@{level}:{body}")
    }

    /// I.3.3 rule 5: a node named at two positions is one stored node, two
    /// equal nodes stay two, and a node that is not generic keeps its level.
    #[test]
    fn freeze_keeps_sharing_and_levels() {
        let scratch = scratch_of(TypeContext::new(Arc::new(IdGenerator::new())));
        let ctx = scratch.ctx();
        let world = ctx.world().clone();
        let shared = ctx.new_generic_var(None);
        let weak = ctx.new_var(None);
        ctx.set_level(weak, 7);
        let (int_a, int_b) = (int(ctx), int(ctx));
        let tuple = ctx.new_generic_type(TypeDesc::Ttuple(
            ctx.new_type_list(&[shared, shared, weak, int_a, int_b]),
        ));
        let before = shape(ctx, tuple, &mut Vec::new());
        let nodes_before = ctx.type_expr_count();
        let frozen = freeze(&world, &scratch, Handles(vec![tuple, shared])).unwrap();
        assert_eq!(ctx.type_expr_count(), nodes_before, "freezing allocates no scratch node");
        // tuple, shared, weak and two `int` nodes: as many as the scratch had.
        assert_eq!(frozen.nodes, 5);
        let [tuple, shared] = frozen.value.0[..] else {
            panic!("two handles")
        };
        assert!(tuple.is_shared() && shared.is_shared());
        // Another compilation of the build reads the same structure.
        let reader = TypeContext::new(Arc::new(IdGenerator::new()));
        assert!(Arc::ptr_eq(reader.world(), &world));
        assert_eq!(shape(&reader, tuple, &mut Vec::new()), before);
        let TypeDesc::Ttuple(items) = reader.get_desc(tuple).into_desc() else {
            panic!("tuple")
        };
        let items: Vec<_> = reader.type_list(items).iter().collect();
        assert_eq!(items[0], shared);
        assert_eq!(items[1], shared);
        assert_ne!(items[3], items[4]);
        assert_eq!(reader.get_level(items[2]), 7);
        assert_eq!(
            reader.get_level(shared),
            crate::types::type_expr::GENERIC_LEVEL
        );
    }

    /// Every payload kind survives: arrow parameters with labels, tuples,
    /// constructor arguments, object fields with their mutability cells,
    /// links, polymorphic types and rows.
    #[test]
    fn freeze_keeps_every_payload_kind() {
        use crate::types::asttypes::MutableFlag;
        use crate::types::type_expr::{FieldMutability, TypeArg};
        let scratch = scratch_of(TypeContext::new(Arc::new(IdGenerator::new())));
        let ctx = scratch.ctx();
        let world = ctx.world().clone();
        let var = ctx.new_generic_var(Some("a".into()));
        let link = ctx.new_generic_type(TypeDesc::Tlink(var));
        let cell = ctx.alloc_mutability(FieldMutability::Value(MutableFlag::Mutable));
        let alias = ctx.alloc_mutability(FieldMutability::Link(cell));
        let nil = ctx.new_generic_type(TypeDesc::Tnil);
        let field_b = ctx.new_generic_type(TypeDesc::Tfield {
            name: "b".into(),
            mutability: alias,
            typ: link,
            rest: nil,
        });
        let field_a = ctx.new_generic_type(TypeDesc::Tfield {
            name: "a".into(),
            mutability: cell,
            typ: int(ctx),
            rest: field_b,
        });
        let object = ctx.new_generic_type(TypeDesc::Tobject { fields: field_a });
        let univar = ctx.new_generic_type(TypeDesc::Tunivar(None));
        let poly = ctx.new_generic_type(TypeDesc::Tpoly {
            body: univar,
            vars: ctx.new_type_list(&[univar]),
        });
        let row_more = ctx.new_generic_var(None);
        let variant = ctx.new_generic_type(TypeDesc::Tvariant(ctx.new_row_desc(RowDesc {
            row_fields: vec![
                ("A".into(), RowField::Rpresent(None)),
                ("B".into(), RowField::Rpresent(Some(object))),
            ]
            .into(),
            row_more,
            row_closed: true,
            row_fixed: false,
            row_name: None,
        })));
        let label = crate::types::type_expr::TypeArgLabel::new(
            &crate::types::asttypes::ArgLabel::Labelled(crate::types::asttypes::Located::noloc(
                "x".to_string(),
            )),
        );
        let arrow = ctx.new_generic_type(TypeDesc::Tarrow {
            args: ctx.new_type_args(&[TypeArg::with_label(label, poly), TypeArg::unlabeled(variant)]),
            ret: ctx.new_generic_constr(
                crate::types::predef::path_option(),
                vec![ctx.new_generic_type(TypeDesc::Ttuple(ctx.new_type_list(&[var, object])))],
            ),
        });
        let before = shape(ctx, arrow, &mut Vec::new());
        let frozen = freeze(&world, &scratch, Handles(vec![arrow])).unwrap();
        let reader = TypeContext::new(Arc::new(IdGenerator::new()));
        assert_eq!(shape(&reader, frozen.value.0[0], &mut Vec::new()), before);
        // The two fields shared one mutability cell and still do.
        let cells = |ctx: &TypeContext, mut fields: TypeExprRef| {
            let mut cells = Vec::new();
            while let TypeDesc::Tfield {
                mutability, rest, ..
            } = ctx.get_desc(fields).into_desc()
            {
                cells.push(ctx.mutability_ref_repr(mutability));
                fields = rest;
            }
            cells
        };
        let frozen_object = *reader
            .type_list(match reader.get_desc(frozen.value.0[0]).into_desc() {
                TypeDesc::Tarrow { ret, .. } => match reader.get_desc(ret).into_desc() {
                    TypeDesc::Tconstr { args, .. } => {
                        match reader.get_desc(reader.type_list(args).iter().next().unwrap()).into_desc() {
                            TypeDesc::Ttuple(items) => items,
                            _ => panic!("tuple"),
                        }
                    }
                    _ => panic!("constr"),
                },
                _ => panic!("arrow"),
            })
            .iter()
            .collect::<Vec<_>>()
            .last()
            .unwrap();
        let TypeDesc::Tobject { fields } = reader.get_desc(frozen_object).into_desc() else {
            panic!("object")
        };
        let frozen_cells = cells(&reader, fields);
        assert_eq!(frozen_cells.len(), 2);
        assert_eq!(frozen_cells[0], frozen_cells[1]);
        assert!(frozen_cells[0].is_persistent());
    }

    /// A handle that is frozen already is kept, and a value that reaches no
    /// scratch node publishes nothing.
    #[test]
    fn freeze_keeps_frozen_handles() {
        let scratch = scratch_of(TypeContext::new(Arc::new(IdGenerator::new())));
        let ctx = scratch.ctx();
        let world = ctx.world().clone();
        let first = freeze(&world, &scratch, Handles(vec![int(ctx)])).unwrap();
        let frozen_int = first.value.0[0];
        let again = freeze(&world, &scratch, Handles(vec![frozen_int])).unwrap();
        assert_eq!((again.graph, again.nodes), (None, 0));
        assert_eq!(again.value.0[0], frozen_int);
        let tuple =
            ctx.new_generic_type(TypeDesc::Ttuple(ctx.new_type_list(&[frozen_int, frozen_int])));
        let mixed = freeze(&world, &scratch, Handles(vec![tuple])).unwrap();
        assert_eq!(mixed.nodes, 1);
        let TypeDesc::Ttuple(items) = ctx.get_desc(mixed.value.0[0]).into_desc() else {
            panic!("tuple")
        };
        assert_eq!(
            ctx.type_list(items).iter().collect::<Vec<_>>(),
            [frozen_int, frozen_int]
        );
    }

    #[test]
    fn freeze_rejects_a_copy_in_progress() {
        let scratch = scratch_of(TypeContext::new(Arc::new(IdGenerator::new())));
        let ctx = scratch.ctx();
        let world = ctx.world().clone();
        let subst = ctx.new_generic_type(TypeDesc::Tsubst(int(ctx)));
        assert_eq!(
            freeze(&world, &scratch, Handles(vec![subst])).err(),
            Some(Unfreezable::CopyInProgress)
        );
    }

    /// Step count: freezing costs one position-map probe per handle of the
    /// value and of the copied nodes, whether the pool is empty or holds a
    /// thousand graphs and units.
    #[test]
    fn freeze_cost_does_not_depend_on_what_the_world_holds() {
        let build = |ctx: &TypeContext| {
            let var = ctx.new_generic_var(None);
            let pair = ctx.new_generic_type(TypeDesc::Ttuple(ctx.new_type_list(&[var, var])));
            Handles(vec![pair, pair, var])
        };
        let probes = |world: &World| {
            let scratch = scratch_of(TypeContext::new(Arc::new(IdGenerator::new())));
            let value = build(scratch.ctx());
            let before = FREEZE_PROBES.with(|probes| probes.get());
            let frozen = freeze(world, &scratch, value).unwrap();
            assert_eq!(frozen.nodes, 2);
            FREEZE_PROBES.with(|probes| probes.get()) - before
        };
        let empty = World::new(u64::MAX);
        let ctx = TypeContext::new(Arc::new(IdGenerator::new()));
        let (full, _units) = world_with_units(&ctx, 1_000);
        let scratch = scratch_of(TypeContext::new(Arc::new(IdGenerator::new())));
        for _ in 0..1_000 {
            freeze(&full, &scratch, build(scratch.ctx())).unwrap();
        }
        // Three handles in the value, two in the tuple's list.
        assert_eq!(probes(&empty), 5);
        assert_eq!(probes(&full), 5);
    }

    #[test]
    fn predef_is_frozen_once_per_build() {
        use crate::types::path::Path;
        use crate::types::predef;
        let world = Arc::new(World::new(u64::MAX));
        let barrier = Arc::new(std::sync::Barrier::new(8));
        let threads: Vec<_> = (0..8)
            .map(|_| {
                let (world, barrier) = (world.clone(), barrier.clone());
                std::thread::spawn(move || {
                    barrier.wait();
                    let env = world.initial_env();
                    // A second compilation on the worker takes a copy of the
                    // worker's tables.
                    assert_eq!(world.initial_env().id(), env.id());
                    let option = env
                        .lookup_type(&Path::pident(predef::ident_option()))
                        .expect("option");
                    let some = env.find_constructor("Some").expect("Some");
                    (option.type_params.clone(), some.cstr_args.clone())
                })
            })
            .collect();
        let seen: Vec<_> = threads.into_iter().map(|t| t.join().unwrap()).collect();
        assert_eq!(world.predef_builds.load(Ordering::Relaxed), 1);
        // Every worker holds the same frozen nodes.
        for (params, args) in &seen {
            assert_eq!(params, &seen[0].0);
            assert_eq!(args, params);
        }
        // Every type handle of every predefined declaration is frozen.
        struct AllFrozen(std::cell::Cell<usize>);
        impl SignatureRefMap for AllFrozen {
            fn ty(&self, r: TypeExprRef) -> TypeExprRef {
                assert!(r.is_shared(), "a predefined type node is not frozen");
                self.0.set(self.0.get() + 1);
                r
            }
            fn layout(&self, r: LayoutRef) -> LayoutRef {
                assert!(r.is_shared(), "a predefined variant layout is not frozen");
                r
            }
        }
        let checked = AllFrozen(std::cell::Cell::new(0));
        let mut items = world.predef().items.clone();
        items.rewrite_handles(&checked);
        assert!(checked.0.get() > 30);
        assert_eq!(world.predef_builds.load(Ordering::Relaxed), 1);
    }
}

