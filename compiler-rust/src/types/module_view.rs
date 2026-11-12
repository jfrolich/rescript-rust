//! Module views: the components of one module path of a dependency, built
//! once per build and read by every worker (docs/CHECKER_REDESIGN.md, J.3).
//!
//! OCaml keeps one component table per persistent unit and process
//! (`ps_comps`, compiler/ml/env.ml:669-678, built by
//! `components_of_module_maker`, env.ml:1513-1588). A [`ModuleView`] is that
//! table with every entry forced: the values after the component
//! substitution, the constructor and label descriptions, the module types,
//! and what `open` installs. Every type node in it is frozen, so a lookup
//! through a view is a table read on any worker.
//!
//! A view is built by [`build_module_view`], which receives the world and a
//! scratch context and never a compilation, so what it builds is a function
//! of its key whichever worker builds it. A compilation uses a view through
//! `TypeContext::adopt_view`.
//!
//! Covered keys: the path of a unit the world owns (`ViewKey::Unit`). Paths
//! with a module alias or a functor application on them, and child paths,
//! are built by `types/env_lazy.rs` (see `Components::Local`).

use super::context::TypeContext;
use super::decl::{
    ConstructorDescription, LabelArrayRef, LabelDescription, ModtypeDeclaration, ModuleDeclaration,
    ModuleType, Signature, SignatureItem, TypeDeclaration, TypeKind, ValueDescription, ValueKind,
};
use super::env_lazy::SignatureIndex;
use super::path::Path;
use super::world::{FrozenExport, ViewScratch, World, freeze};
use crate::cmi::persistent_env::PersStruct;
use crate::cmi::portable_types::SignatureRefMap;
use crate::fast_hash::AHashMap;
use crate::ident::Ident;
use smol_str::SmolStr;
use std::sync::atomic::{AtomicU32, Ordering};
use std::sync::{Arc, OnceLock};

/// Identity of a view within its world: a dense number, so a worker keeps
/// what it derives from a view (the layer tables of `open`) in a table
/// indexed by it. Assigned in build order, which depends on the schedule:
/// it has no `Ord` and is never printed or hashed into output.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct ViewId(u32);

impl ViewId {
    #[inline]
    pub(crate) fn index(self) -> usize {
        self.0 as usize
    }
}

/// Where what the world knows of one module path is published. The cell of
/// a unit's own path lives in the unit (`PersStruct::ps_view`), and the cell
/// of a child path in its parent's view (`ModuleView::children`, by the
/// child's ordinal among the module items), so a holder of the unit or of
/// the parent view reaches it without a table.
#[derive(Default)]
pub(crate) struct ViewCell {
    /// `None` inside: the pool had no room for the view. Every compilation
    /// then builds the unit's components for itself, as it does for a unit
    /// the world does not own.
    view: OnceLock<Option<Arc<ModuleView>>>,
    /// The forced declaration of the module at this path, a child of its
    /// parent's view (`comp_modules`, env.ml:1568), built by the first
    /// worker that looks the child up with `find_module`; `None` inside
    /// when the pool had no room for it. Never set for a unit's own path.
    decl: OnceLock<Option<Arc<ViewModule>>>,
    /// Builds of this cell's view.
    #[cfg(test)]
    builds: AtomicU32,
}

impl std::fmt::Debug for ViewCell {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(if self.view.get().is_some() {
            "ViewCell(built)"
        } else {
            "ViewCell(unbuilt)"
        })
    }
}

/// What a view is a function of.
#[derive(Clone, Copy)]
pub(crate) enum ViewKey<'a> {
    /// The path of a unit the world owns.
    Unit(&'a Arc<PersStruct>),
    /// The path of a structure-typed child module of a view: the parent
    /// view and the child's ordinal among the parent's module items
    /// ([`ModuleView::structure_child`]).
    Child(&'a Arc<ModuleView>, u32),
}

impl ViewKey<'_> {
    fn name(&self) -> String {
        match self {
            ViewKey::Unit(unit) => unit.ps_name.clone(),
            ViewKey::Child(parent, ordinal) => {
                let (idx, _) = parent.index.module_item(*ordinal as usize);
                match &parent.signature[idx] {
                    SignatureItem::SigModule(id, ..) => {
                        format!("{}.{}", parent.access_path.name(), id.name())
                    }
                    _ => parent.access_path.name(),
                }
            }
        }
    }

    fn cell(&self) -> Option<&ViewCell> {
        match self {
            ViewKey::Unit(unit) => unit.ps_view.get().map(|cell| cell.as_ref()),
            ViewKey::Child(parent, ordinal) => parent.children.get(*ordinal as usize),
        }
    }
}

/// The unit a module path names when the path is a unit key: a persistent
/// identifier. This is all that decides it: a unit that some namespace or
/// library module aliases (`module JSON = Stdlib_JSON`) is still reached by
/// its own path through its own components (compiler/ml/env.ml:1000-1007),
/// so the answer does not depend on which aliases a compilation has met.
/// One tag test and one flag test.
#[inline]
pub(crate) fn unit_key_name(path: &Path) -> Option<&str> {
    match path.view() {
        super::path::PathView::Pident(id) if id.is_persistent() => Some(id.name()),
        _ => None,
    }
}

/// The views of one world.
pub(crate) struct ViewTable {
    next_id: AtomicU32,
}

impl ViewTable {
    pub(crate) fn new() -> Self {
        ViewTable {
            next_id: AtomicU32::new(0),
        }
    }

    /// The view of `key`, built on the calling worker the first time any
    /// worker asks; a second worker asking meanwhile waits for it. `None`
    /// when the key has no cell (the world does not own the unit) or the
    /// pool had no room for the view; the failure is stored, so no worker
    /// tries again and every compilation gets the same answer.
    ///
    /// A view that is built already costs one load of a write-once cell and
    /// one reference-count increment: no lock, no hash.
    pub(crate) fn get_or_build(&self, world: &World, key: &ViewKey<'_>) -> Option<Arc<ModuleView>> {
        let cell = key.cell()?;
        if let Some(view) = cell.view.get() {
            return view.clone();
        }
        cell.view
            .get_or_init(|| {
                #[cfg(test)]
                cell.builds.fetch_add(1, Ordering::Relaxed);
                let scratch = ViewScratch::fresh();
                build_module_view(world, &scratch, key).map(Arc::new)
            })
            .clone()
    }
}

/// A value of a view: its runtime position, identifier and description
/// after the component substitution (`comp_values`, env.ml:1537).
#[derive(Clone)]
pub(crate) struct ViewValue {
    pub(crate) pos: u32,
    pub(crate) id: Ident,
    pub(crate) desc: ValueDescription,
}

/// A child module of an opened view.
#[derive(Clone)]
pub(crate) struct OpenedModule {
    pub(crate) id: Ident,
    pub(crate) decl: Arc<ModuleDeclaration>,
    pub(crate) pos: i32,
    /// The declaration is an alias of a persistent unit: its components are
    /// that unit's, reached through the declaration alone.
    pub(crate) direct_persistent_alias: bool,
}

/// What `open` installs for a view (env.ml:1841-1877), in signature order.
/// A worker builds its layer tables from these once: one hash insert and
/// one reference-count increment per item, no type node.
#[derive(Default)]
pub(crate) struct OpenedItems {
    pub(crate) values: Vec<(Ident, Arc<ValueDescription>, i32)>,
    pub(crate) types: Vec<(Ident, Arc<TypeDeclaration>)>,
    pub(crate) constructors: Vec<(Ident, Arc<ConstructorDescription>)>,
    pub(crate) labels: Vec<(Ident, Arc<LabelDescription>)>,
    pub(crate) modules: Vec<OpenedModule>,
    pub(crate) modtypes: Vec<(Ident, Arc<ModtypeDeclaration>)>,
}

/// A forced child declaration: frozen, with the child's identifier.
pub(crate) struct ViewModule {
    pub(crate) id: Ident,
    pub(crate) decl: Arc<ModuleDeclaration>,
}

/// A forced child declaration with its identifier; `None` when the pool had
/// no room for it.
pub(crate) type ForcedDeclaration = Option<(Ident, Arc<ModuleDeclaration>)>;

impl std::fmt::Debug for ModuleView {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "ModuleView({})", self.access_path.name())
    }
}

/// The components of one module path. Immutable once published; every type
/// handle in it is frozen.
pub(crate) struct ModuleView {
    id: ViewId,
    access_path: Path,
    /// The signature the tables are built from. A unit's own: its items
    /// name each other by local identifier. A child's: its declared
    /// signature with its own items at the access path and its ancestors'
    /// at theirs (`Subst.signature sub sg` and `prefix_idents`,
    /// env.ml:1516-1531), created by the view's build.
    signature: Arc<Signature>,
    /// The signature as the unit declares it: a unit's own again, a child's
    /// as it stands inside the unit's. A worker's tables for the children
    /// whose paths have no view are seeded from it.
    raw: Arc<Signature>,
    /// The view this one is a child of, and its ordinal there.
    parent: Option<(std::sync::Weak<ModuleView>, u32)>,
    index: Arc<SignatureIndex>,
    /// By signature item: `Some` for the value item a name lookup reaches.
    values: Box<[Option<ViewValue>]>,
    /// Keyed by name: a signature gives its names no dense index.
    constructors: AHashMap<SmolStr, Arc<Vec<ConstructorDescription>>>,
    labels: AHashMap<SmolStr, Arc<Vec<LabelDescription>>>,
    /// The label array of each record type, by type name.
    label_families: AHashMap<SmolStr, LabelArrayRef>,
    modtypes: AHashMap<SmolStr, (Ident, ModtypeDeclaration)>,
    /// The substituted target of each child whose type is a path, and
    /// whether it is an alias (`Mty_alias`) or a module type (`Mty_ident`).
    alias_targets: AHashMap<SmolStr, (bool, Arc<Path>)>,
    /// The cell of each child module, by its ordinal among the module
    /// items (`SignatureIndex::module_cell`).
    children: Box<[ViewCell]>,
    /// The component substitution of this view (`prefix_idents`,
    /// env.ml:1530): built once, by the build when an item needs it or by
    /// the first forced child, and read by every later force.
    subst: OnceLock<crate::cmi::persistent_env::ComponentSubst>,
    /// (component path, alias source) of every child that is a path
    /// (env.ml:1517 `scrape_alias`): what adopting the view registers.
    alias_sources: Box<[(Path, Path)]>,
    opened: OpenedItems,
    no_constructors: Arc<Vec<ConstructorDescription>>,
    no_labels: Arc<Vec<LabelDescription>>,
    /// Type nodes the build created (the rest are the unit's).
    nodes: usize,
}

/// Rewrites every handle the view's tables hold, each once. A unit's
/// signature is frozen already; a child's was created by its build.
impl FrozenExport for ModuleView {
    fn rewrite_handles(&mut self, map: &impl SignatureRefMap) {
        if self.parent.is_some() {
            self.signature.rewrite_handles(map);
        }
        for value in self.values.iter_mut().flatten() {
            value.desc.rewrite_handles(map);
        }
        for constructors in self.constructors.values_mut() {
            constructors.rewrite_handles(map);
        }
        for labels in self.labels.values_mut() {
            labels.rewrite_handles(map);
        }
        for family in self.label_families.values_mut() {
            *family = map.label_array(*family);
        }
        for (_, modtype) in self.modtypes.values_mut() {
            modtype.rewrite_handles(map);
        }
        let OpenedItems {
            values,
            types,
            constructors,
            labels,
            modules,
            modtypes,
        } = &mut self.opened;
        for (_, value, _) in values {
            value.rewrite_handles(map);
        }
        for (_, decl) in types {
            decl.rewrite_handles(map);
        }
        for (_, constructor) in constructors {
            constructor.rewrite_handles(map);
        }
        for (_, label) in labels {
            label.rewrite_handles(map);
        }
        for module in modules {
            module.decl.rewrite_handles(map);
        }
        for (_, modtype) in modtypes {
            modtype.rewrite_handles(map);
        }
    }
}

#[cfg(test)]
thread_local! {
    /// Signature items visited by view builds on this thread.
    static BUILD_STEPS: std::sync::atomic::AtomicU64 = const { std::sync::atomic::AtomicU64::new(0) };
}

#[inline]
fn count_build_step() {
    #[cfg(test)]
    BUILD_STEPS.with(|steps| steps.fetch_add(1, Ordering::Relaxed));
}

/// Build the view of `key` on `scratch` and freeze it into `world`: one
/// [`describe_view`] and one [`freeze`] of what it created.
pub(crate) fn build_module_view(
    world: &World,
    scratch: &ViewScratch,
    key: &ViewKey<'_>,
) -> Option<ModuleView> {
    let view = describe_view(world, scratch, key)?;
    let frozen = match freeze(world, scratch, view) {
        Ok(frozen) => frozen,
        Err(failure) => {
            debug_assert_unfreezable_is_pool_full(failure, &key.name());
            crate::perf_counters::world::record_view_failure();
            return None;
        }
    };
    let mut view = frozen.value;
    view.id = ViewId(world.views().next_id.fetch_add(1, Ordering::Relaxed));
    view.nodes = frozen.nodes;
    if crate::perf_counters::enabled() {
        crate::perf_counters::world::record_view_build(
            frozen.nodes,
            [
                view.signature.len(),
                view.values.iter().flatten().count(),
                view.constructors.values().map(|bucket| bucket.len()).sum(),
                view.labels.values().map(|bucket| bucket.len()).sum(),
                view.opened.values.len(),
                view.opened.types.len(),
                view.opened.constructors.len(),
                view.opened.labels.len(),
            ],
        );
    }
    Some(view)
}

/// A full pool is the one reason a view or a forced child cannot be frozen.
/// The others cannot happen: a unit the world owns has only frozen nodes
/// (`World::unit` refuses any other), so the build reaches no worker-store
/// node; no copy session is open when a description is complete; the build
/// interns no location (it copies the unit's shared ones); package
/// constraint names of a unit are the pool's; and every label array a view
/// names was created on its scratch context.
fn debug_assert_unfreezable_is_pool_full(failure: super::world::Unfreezable, name: &str) {
    debug_assert!(
        failure == super::world::Unfreezable::PoolFull,
        "the view of {name} cannot be frozen: {failure:?}"
    );
}

/// The tables of the view of `key`, described on `scratch`: what the build
/// created is still the scratch context's, and nothing is published.
///
/// Cost: [`describe_tables`] for the signature of the key's module; for a
/// child also one copy of its declared signature and one walk of it under
/// the parent's substitution, which is the parent view's and built once.
fn describe_view(world: &World, scratch: &ViewScratch, key: &ViewKey<'_>) -> Option<ModuleView> {
    let ctx = scratch.ctx();
    match key {
        ViewKey::Unit(unit) => {
            let access_path = Path::pident(Ident::create_persistent(&unit.ps_name));
            let signature = unit.ps_sig.clone();
            let index = world
                .unit_signature_index(&signature)
                .unwrap_or_else(|| Arc::new(SignatureIndex::build(&signature)));
            Some(describe_tables(
                access_path,
                signature.clone(),
                index,
                signature,
                None,
                ctx,
            ))
        }
        ViewKey::Child(parent, ordinal) => {
            let (idx, runtime_pos) = parent.index.module_item(*ordinal as usize);
            let SignatureItem::SigModule(id, md, _) = &parent.raw[idx] else {
                return None;
            };
            let ModuleType::MtySignature(raw) = &md.md_type else {
                return None;
            };
            // env.ml:1573-1578: the child's component thunk holds its
            // declared signature and the parent's substitution;
            // env.ml:1516-1531 applies that substitution and prefixes the
            // child's own items with its path.
            let access_path = ctx.dotted_from_ident(
                Arc::new(parent.access_path),
                *id,
                runtime_pos as i32,
            );
            let mut signature = super::typecore::qualify_resolved_signature_for_local_components(
                &access_path,
                &md.md_type,
                raw,
                None,
                &mut None,
                ctx,
            );
            parent.component_subst(ctx).substitute_child_signature(
                &mut signature,
                &parent.signature,
                &parent.access_path,
                ctx,
            );
            let signature = Arc::new(signature);
            let index = Arc::new(SignatureIndex::build(&signature));
            Some(describe_tables(
                access_path,
                signature,
                index,
                raw.clone(),
                Some((Arc::downgrade(parent), *ordinal)),
                ctx,
            ))
        }
    }
}

/// The tables of the view of the module with `signature` at `access_path`.
///
/// What OCaml does when it forces a module's components (env.ml:1513-1588),
/// for every item instead of on first use: the component substitution
/// (`prefix_idents`) applied to each value and module type, the constructor
/// and label descriptions of each type (`Datarepr`), and the tables `open`
/// installs. The build loads no unit and reads no compilation.
///
/// Cost: a fixed number of passes over the signature, each doing work in
/// proportion to the item it visits (one copy of a value's type, one
/// description per constructor and label); the component substitution is
/// built at most three times, each one pass.
fn describe_tables(
    access_path: Path,
    signature: Arc<Signature>,
    index: Arc<SignatureIndex>,
    raw: Arc<Signature>,
    parent: Option<(std::sync::Weak<ModuleView>, u32)>,
    ctx: &TypeContext,
) -> ModuleView {
    let shared_access_path = Arc::new(access_path);

    let mut values: Vec<Option<ViewValue>> = Vec::with_capacity(signature.len());
    let mut labels: AHashMap<SmolStr, Vec<LabelDescription>> = AHashMap::default();
    let mut label_families: AHashMap<SmolStr, LabelArrayRef> = AHashMap::default();
    let mut modtypes: AHashMap<SmolStr, (Ident, ModtypeDeclaration)> = AHashMap::default();
    let mut alias_targets: AHashMap<SmolStr, (bool, Arc<Path>)> = AHashMap::default();
    let mut alias_sources = Vec::with_capacity(index.alias_module_count());
    let mut value_maps = None;
    let mut subst = None;
    let mut runtime_pos = 0usize;
    for (idx, item) in signature.iter().enumerate() {
        count_build_step();
        let mut value = None;
        match item {
            SignatureItem::SigValue(id, desc) => {
                // A later value of the same name hides this one from every
                // lookup (`Tbl.add`, env.ml:1537).
                if index.value(id.name()) == Some((idx, runtime_pos)) {
                    // env.ml:1537 `Subst.value_description sub decl`.
                    let mut desc =
                        super::typecore::copy_lookup_value_description_for_subst(desc, ctx);
                    let maps = value_maps.get_or_insert_with(|| {
                        crate::cmi::persistent_env::build_value_subst_maps(
                            &signature,
                            &access_path,
                            ctx,
                        )
                    });
                    crate::cmi::persistent_env::substitute_type_paths_in_value_with_maps(
                        &mut desc,
                        maps,
                        &signature,
                        &access_path,
                        ctx,
                    );
                    value = Some(ViewValue {
                        pos: runtime_pos as u32,
                        id: *id,
                        desc,
                    });
                }
                if !matches!(desc.val_kind, ValueKind::ValPrim(_)) {
                    runtime_pos += 1;
                }
            }
            SignatureItem::SigType(id, decl, _) => {
                if let TypeKind::TypeRecord(declared, _) = &decl.type_kind
                    && !declared.is_empty()
                {
                    // env.ml:1470-1475 `Datarepr.labels_of_type path decl'`:
                    // one array per type name.
                    let family = *label_families
                        .entry(SmolStr::new_static(id.name()))
                        .or_insert_with(|| {
                            let type_path = Path::pdot(access_path, id.name());
                            let res_ty =
                                ctx.new_generic_constr(type_path, decl.type_params.clone());
                            super::env_lazy::label_descrs_array(res_ty, decl, ctx, |_| {})
                        });
                    let family = ctx
                        .label_family(family)
                        .expect("a component label family is registered");
                    for (pos, label) in declared.iter().enumerate() {
                        labels
                            .entry(SmolStr::new_static(label.ld_id.name()))
                            .or_default()
                            .push(family[pos].clone());
                    }
                }
            }
            SignatureItem::SigTypext(..) | SignatureItem::SigClass => runtime_pos += 1,
            SignatureItem::SigModule(id, md, _) => {
                if let ModuleType::MtyAlias(..) | ModuleType::MtyIdent(_) = &md.md_type {
                    let source = md.md_type.ident_or_alias_path().unwrap();
                    alias_sources.push((
                        ctx.dotted_from_ident(shared_access_path.clone(), *id, runtime_pos as i32),
                        *source,
                    ));
                    // env.ml:446-448, 1568: the declaration under the
                    // component substitution; a path renames no binder.
                    let subst = subst.get_or_insert_with(|| {
                        crate::cmi::persistent_env::ComponentSubst::new(
                            &signature,
                            &access_path,
                            ctx,
                        )
                    });
                    let target = match subst.module_type_path(&md.md_type, ctx) {
                        Some(ModuleType::MtyAlias(_, target)) => Some((true, target)),
                        Some(ModuleType::MtyIdent(target)) => Some((false, Arc::new(target))),
                        _ => None,
                    };
                    if index.module(id.name()) == Some((idx, runtime_pos))
                        && let Some(target) = target
                    {
                        alias_targets.insert(SmolStr::new_static(id.name()), target);
                    }
                }
                runtime_pos += 1;
            }
            SignatureItem::SigModtype(id, mtd) => {
                // env.ml:1581-1585 `Subst.modtype_declaration sub decl`.
                let mut component_mtd = mtd.clone();
                let subst = subst.get_or_insert_with(|| {
                    crate::cmi::persistent_env::ComponentSubst::new(&signature, &access_path, ctx)
                });
                subst.freshen_modtype_declaration(&mut component_mtd, ctx);
                modtypes.insert(SmolStr::new_static(id.name()), (*id, component_mtd));
            }
            SignatureItem::SigClassType => {}
        }
        values.push(value);
    }

    let constructors = super::env_lazy::build_all_constructors(&access_path, &signature, ctx)
        .into_iter()
        .map(|(name, bucket)| (name, Arc::new(bucket)))
        .collect();
    let labels = labels
        .into_iter()
        .map(|(name, mut bucket)| {
            // Later declarations shadow earlier ones (`comp_labels` is a
            // `find_all` table, newest first).
            bucket.reverse();
            (name, Arc::new(bucket))
        })
        .collect();

    let view = ModuleView {
        // Numbered when it is published.
        id: ViewId(u32::MAX),
        access_path,
        children: (0..index.module_count())
            .map(|_| ViewCell::default())
            .collect(),
        subst: subst.map(OnceLock::from).unwrap_or_default(),
        signature,
        raw,
        parent,
        index,
        values: values.into_boxed_slice(),
        constructors,
        labels,
        label_families,
        modtypes,
        alias_targets,
        alias_sources: alias_sources.into_boxed_slice(),
        opened: OpenedItems::default(),
        no_constructors: Arc::new(Vec::new()),
        no_labels: Arc::new(Vec::new()),
        nodes: 0,
    };
    // The opened items are described from the tables above, through the
    // lookups any reader of the view uses.
    let view = Arc::new(view);
    let opened = crate::cmi::persistent_env::opened_items_of_view(&view, ctx);
    let mut view = Arc::into_inner(view).expect("the view under construction has one owner");
    view.opened = opened;
    view
}

impl ModuleView {
    #[inline]
    pub(crate) fn id(&self) -> ViewId {
        self.id
    }

    #[inline]
    pub(crate) fn access_path(&self) -> &Path {
        &self.access_path
    }

    #[inline]
    pub(crate) fn signature(&self) -> &[SignatureItem] {
        self.signature.as_slice()
    }

    #[inline]
    pub(crate) fn signature_arc(&self) -> Arc<Signature> {
        self.signature.clone()
    }

    #[inline]
    pub(crate) fn signature_ref(&self) -> &Arc<Signature> {
        &self.signature
    }

    /// The signature as the unit declares it (see the field).
    #[inline]
    pub(crate) fn raw_signature(&self) -> &Arc<Signature> {
        &self.raw
    }

    /// The view this one is a child of and the child's name there; `None`
    /// for a unit's view. One upgrade of a weak reference.
    pub(crate) fn parent(&self) -> Option<(Arc<ModuleView>, &str)> {
        let (parent, _) = self.parent.as_ref()?;
        // A child view is reached through its parent, which the unit holds.
        let parent = parent.upgrade()?;
        Some((parent, self.access_path.last()))
    }

    /// The component substitution of this view (`prefix_idents`,
    /// env.ml:1530). One load of a write-once cell once it is built; the
    /// build is one pass over the signature.
    fn component_subst(&self, ctx: &TypeContext) -> &crate::cmi::persistent_env::ComponentSubst {
        self.subst.get_or_init(|| {
            crate::cmi::persistent_env::ComponentSubst::new(&self.signature, &self.access_path, ctx)
        })
    }

    /// The ordinal of child module `name` when its path is a view key of
    /// its own: the child is declared with a signature. A child that is a
    /// path, or a functor, has none. One probe of the name index.
    pub(crate) fn structure_child(&self, name: &str) -> Option<u32> {
        let (idx, _, ordinal) = self.index.module_cell(name)?;
        match &self.raw[idx] {
            SignatureItem::SigModule(_, md, _)
                if matches!(md.md_type, ModuleType::MtySignature(_)) =>
            {
                Some(ordinal as u32)
            }
            _ => None,
        }
    }

    #[inline]
    pub(crate) fn opened_items(&self) -> &OpenedItems {
        &self.opened
    }

    #[inline]
    pub(crate) fn alias_sources(&self) -> &[(Path, Path)] {
        &self.alias_sources
    }

    /// `comp_values` after the component substitution. One probe of the
    /// name index and one read of the value table; the description is
    /// cloned for the caller (its attribute list is shared).
    pub(crate) fn lookup_value_for_access(
        &self,
        name: &str,
    ) -> Option<(usize, Ident, ValueDescription)> {
        let (idx, _) = self.index.value(name)?;
        let value = self.values[idx].as_ref()?;
        Some((value.pos as usize, value.id, value.desc.clone()))
    }

    /// `comp_constrs` for `name`, latest declaration first. One probe.
    pub(crate) fn lookup_constructors(&self, name: &str) -> Arc<Vec<ConstructorDescription>> {
        self.constructors
            .get(name)
            .unwrap_or(&self.no_constructors)
            .clone()
    }

    /// `comp_labels` for `name`, latest declaration first. One probe.
    pub(crate) fn lookup_labels(&self, name: &str) -> Arc<Vec<LabelDescription>> {
        self.labels.get(name).unwrap_or(&self.no_labels).clone()
    }

    /// The label array of record type `name` (`find_type_descrs`,
    /// env.ml:828). Two probes.
    pub(crate) fn type_label_family(&self, name: &str) -> Option<LabelArrayRef> {
        let idx = self.index.type_item(name)?;
        let SignatureItem::SigType(_, decl, _) = &self.signature[idx] else {
            return None;
        };
        if !matches!(&decl.type_kind, TypeKind::TypeRecord(labels, _) if !labels.is_empty()) {
            return None;
        }
        self.label_families.get(name).copied()
    }

    /// One probe of the name index.
    pub(crate) fn lookup_type(&self, name: &str) -> Option<(&Ident, &Arc<TypeDeclaration>)> {
        let idx = self.index.type_item(name)?;
        match &self.signature[idx] {
            SignatureItem::SigType(id, decl, _) => Some((id, decl)),
            _ => None,
        }
    }

    /// The child module as the unit declares it. One probe.
    pub(crate) fn lookup_module(&self, name: &str) -> Option<(usize, &Ident, &ModuleDeclaration)> {
        let (idx, runtime_pos) = self.index.module(name)?;
        match &self.signature[idx] {
            SignatureItem::SigModule(id, md, _) => Some((runtime_pos, id, md)),
            _ => None,
        }
    }

    /// The substituted target of child `name` when it is a module alias
    /// (or, with `include_ident`, a module type path). One probe.
    pub(crate) fn lookup_module_alias_target(
        &self,
        name: &str,
        include_ident: bool,
    ) -> Option<Arc<Path>> {
        let (alias, target) = self.alias_targets.get(name)?;
        (include_ident || *alias).then(|| target.clone())
    }

    /// `comp_modtypes`. One probe; the declaration is cloned for the caller.
    pub(crate) fn lookup_modtype(&self, name: &str) -> Option<(Ident, ModtypeDeclaration)> {
        self.modtypes.get(name).cloned()
    }

    /// The forced declaration of child module `name` (`find_module`,
    /// env.ml:865-882, forcing the `comp_modules` thunk of env.ml:1568):
    /// `Subst.modtype` under the component substitution, which renames the
    /// bound identifiers of a child signature. Forced once per build, on a
    /// scratch context of the first worker that asks, into the child's
    /// cell ([`ViewCell`]).
    ///
    /// Forced already: one probe of the name index and one load of a
    /// write-once cell. Forcing: one copy of the child's module type. The
    /// component substitution is this view's, built once (one pass over the
    /// signature) whatever the number of children forced.
    /// Returns the child's signature item, runtime position, and its
    /// identifier and declaration; `None` for those when the pool had no
    /// room for the declaration (the caller then forces it for itself).
    pub(crate) fn lookup_forced_module(
        &self,
        world: &World,
        name: &str,
    ) -> Option<(usize, usize, ForcedDeclaration)> {
        let (idx, runtime_pos, ordinal) = self.index.module_cell(name)?;
        let SignatureItem::SigModule(id, md, _) = &self.signature[idx] else {
            return None;
        };
        let forced = self.children[ordinal].decl.get_or_init(|| {
            let scratch = ViewScratch::fresh();
            let ctx = scratch.ctx();
            let subst = self.component_subst(ctx);
            let mut md = md.clone();
            subst.freshen_module_declaration(&mut md, ctx);
            match freeze(world, &scratch, Arc::new(md)) {
                Ok(frozen) => {
                    crate::perf_counters::world::record_forced_child(frozen.nodes);
                    Some(Arc::new(ViewModule {
                        id: *id,
                        decl: frozen.value,
                    }))
                }
                Err(failure) => {
                    debug_assert_unfreezable_is_pool_full(failure, name);
                    None
                }
            }
        });
        let forced = forced
            .as_ref()
            .map(|module| (module.id, module.decl.clone()));
        Some((idx, runtime_pos, forced))
    }

    /// The text `RESCRIPT_WORLD_VERIFY` compares: every table of the view
    /// printed without node identity, stamps or handles.
    pub(crate) fn canonical(&self, ctx: &TypeContext) -> String {
        fn sorted<V>(map: &AHashMap<SmolStr, V>) -> Vec<(&SmolStr, &V)> {
            let mut entries: Vec<_> = map.iter().collect();
            entries.sort_by(|a, b| a.0.cmp(b.0));
            entries
        }
        let value = |name: String, ty| {
            SignatureItem::SigValue(
                Ident::create_persistent(name),
                ValueDescription {
                    val_type: ty,
                    val_kind: ValueKind::ValReg,
                    val_loc: super::DeclLoc::none(),
                    val_attributes: Default::default(),
                    val_path: None,
                },
            )
        };
        let mut items = Vec::new();
        for entry in self.values.iter().flatten() {
            items.push(SignatureItem::SigValue(entry.id, entry.desc.clone()));
        }
        for (name, constructors) in sorted(&self.constructors) {
            for (n, constructor) in constructors.iter().enumerate() {
                items.push(value(
                    format!("constructor {name} {n} result"),
                    constructor.cstr_res,
                ));
                for (k, arg) in constructor.cstr_args.iter().enumerate() {
                    items.push(value(format!("constructor {name} {n} argument {k}"), *arg));
                }
            }
        }
        for (name, labels) in sorted(&self.labels) {
            for (n, label) in labels.iter().enumerate() {
                items.push(value(format!("label {name} {n} record"), label.lbl_res));
                items.push(value(format!("label {name} {n} field"), label.lbl_arg));
                let family = ctx.label_family(label.lbl_all).map_or(0, |all| all.len());
                items.push(value(
                    format!("label {name} {n} position {} of {family}", label.lbl_pos),
                    label.lbl_res,
                ));
            }
        }
        for (name, (id, modtype)) in sorted(&self.modtypes) {
            let _ = name;
            items.push(SignatureItem::SigModtype(*id, modtype.clone()));
        }
        for (id, decl) in &self.opened.types {
            items.push(SignatureItem::SigType(
                *id,
                decl.clone(),
                super::decl::RecStatus::TrecNot,
            ));
        }
        for (_, desc, pos) in &self.opened.values {
            items.push(value(format!("opened value at {pos}"), desc.val_type));
        }
        for (id, constructor) in &self.opened.constructors {
            items.push(value(
                format!("opened constructor {}", id.name()),
                constructor.cstr_res,
            ));
        }
        let mut text = super::canonical_sig::canonical_signature(
            ctx,
            self.access_path.head().name(),
            &items,
            None,
            None,
        );
        for (name, (alias, target)) in sorted(&self.alias_targets) {
            text.push_str(&format!("target {name} {alias} {}\n", target.name()));
        }
        for (component, source) in self.alias_sources.iter() {
            text.push_str(&format!("alias {} = {}\n", component.name(), source.name()));
        }
        text
    }
}

/// `RESCRIPT_WORLD_VERIFY=1`: every adoption rebuilds the view on the
/// adopting worker and compares it with the published one.
pub(crate) fn world_verify_enabled() -> bool {
    static ENABLED: OnceLock<bool> = OnceLock::new();
    *ENABLED.get_or_init(|| std::env::var_os("RESCRIPT_WORLD_VERIFY").is_some())
}

/// Describe `view` again on this worker and abort unless the description
/// prints as the published view does (J.3.6, point 1: a view is a function
/// of its key). The description stays on its scratch context: nothing is
/// published. One [`describe_view`] and two prints; only under
/// `RESCRIPT_WORLD_VERIFY`.
pub(crate) fn verify_view(world: &World, key: &ViewKey<'_>, view: &ModuleView) {
    let scratch = ViewScratch::fresh();
    let rebuilt =
        describe_view(world, &scratch, key).expect("a published view rebuilds on any worker");
    let published = view.canonical(scratch.ctx());
    let rebuilt = rebuilt.canonical(scratch.ctx());
    if published != rebuilt {
        eprintln!(
            "RESCRIPT_WORLD_VERIFY: the view of {} differs between workers\n--- published\n{published}\n--- rebuilt\n{rebuilt}",
            view.access_path.name()
        );
        std::process::abort();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::context::IdGenerator;
    use crate::types::asttypes::{MutableFlag, PrivateFlag};
    use crate::types::context::QualifiedModuleComponentsCacheKey;
    use crate::types::decl::{
        AliasPresence, LabelArrayTier, LabelDeclaration, RecStatus, RecordRepresentation,
    };
    use crate::types::env_lazy::Components;
    use std::sync::atomic::AtomicUsize;

    fn build_steps() -> u64 {
        BUILD_STEPS.with(|steps| steps.load(Ordering::Relaxed))
    }

    fn subst_map_builds() -> u64 {
        crate::cmi::persistent_env::SUBST_MAP_BUILDS.with(|builds| builds.get())
    }

    fn compilation() -> TypeContext {
        TypeContext::new(Arc::new(IdGenerator::new()))
    }

    /// What a test unit holds besides its fixed items.
    #[derive(Default, Clone, Copy)]
    struct Shape {
        /// Values `v<n>: t`.
        values: usize,
        /// Variant types `k<n>`, each with `constructors` constructors
        /// `C<n>_<m>(int)`.
        variants: usize,
        constructors: usize,
        /// Record types `r<n> = {a<n>: int, b<n>: int}`.
        records: usize,
        /// Child modules `M<n>: { type u }`.
        children: usize,
        /// A chain `Chain: { module Chain: { ... { type u } } }` this deep.
        chain: usize,
        /// Leave out the module type `S` and the modules `Alias` and
        /// `Inner`: no item of the unit then needs the component
        /// substitution when the view is built.
        bare: bool,
    }

    fn unit(name: &str, values: usize) -> Arc<PersStruct> {
        unit_of(
            name,
            Shape {
                values,
                ..Shape::default()
            },
        )
    }

    /// A unit the current world owns, named `name`, with:
    /// `type t = {first: int, second: t}`, what `shape` asks for,
    /// a module type `S`, and child modules `Alias = Other_unit` and
    /// `Inner: { type u }`.
    fn unit_of(name: &str, shape: Shape) -> Arc<PersStruct> {
        let values = shape.values;
        static NEXT: AtomicUsize = AtomicUsize::new(0);
        let name = format!("{name}{}", NEXT.fetch_add(1, Ordering::Relaxed));
        let world = World::current();
        let scratch = ViewScratch::fresh();
        let ctx = scratch.ctx();
        let t = Ident::create_local("t");
        let t_type = || ctx.new_generic_constr(Path::pident(t), vec![]);
        let int = ctx.new_generic_predef_constr(crate::types::predef::path_int(), vec![]);
        let label = |name: &str, ty| LabelDeclaration {
            ld_id: Ident::create_local(name.to_string()),
            ld_runtime_name: None,
            ld_mutable: MutableFlag::Immutable,
            ld_optional: false,
            ld_type: ty,
            ld_loc: crate::types::DeclLoc::none(),
            ld_attributes: vec![],
        };
        let abstract_decl = || TypeDeclaration {
            type_params: vec![],
            type_arity: 0,
            type_kind: TypeKind::TypeAbstract,
            type_private: PrivateFlag::Public,
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
        let record = TypeDeclaration {
            type_kind: TypeKind::TypeRecord(
                crate::types::decl::SharedVec::from(vec![
                    label("first", int),
                    label("second", t_type()),
                ]),
                RecordRepresentation::RecordRegular,
            ),
            ..abstract_decl()
        };
        let module = |name: &str, md_type| {
            SignatureItem::SigModule(
                Ident::create_local(name.to_string()),
                ModuleDeclaration {
                    md_type,
                    md_attributes: vec![],
                    md_loc: crate::types::DeclLoc::none(),
                    md_path: None,
                },
                RecStatus::TrecNot,
            )
        };
        let mut signature = vec![SignatureItem::SigType(
            t,
            Arc::new(record),
            RecStatus::TrecNot,
        )];
        for n in 0..values {
            signature.push(SignatureItem::SigValue(
                Ident::create_local(format!("v{n}")),
                ValueDescription {
                    val_type: t_type(),
                    val_kind: ValueKind::ValReg,
                    val_loc: crate::types::DeclLoc::none(),
                    val_attributes: Default::default(),
                    val_path: None,
                },
            ));
        }
        for n in 0..shape.variants {
            let constructors: Vec<_> = (0..shape.constructors)
                .map(|m| crate::types::decl::ConstructorDeclaration {
                    cd_id: Ident::create_local(format!("C{n}_{m}")),
                    cd_runtime_tag: None,
                    cd_args: crate::types::decl::ConstructorArguments::CstrTuple(vec![int]),
                    cd_res: None,
                    cd_loc: crate::types::DeclLoc::none(),
                    cd_attributes: vec![],
                })
                .collect();
            let layout = crate::types::variant_runtime::plain_layout(
                ctx,
                constructors
                    .iter()
                    .map(|constructor| (constructor.cd_id.name().to_string(), true)),
            );
            signature.push(SignatureItem::SigType(
                Ident::create_local(format!("k{n}")),
                Arc::new(TypeDeclaration {
                    type_kind: TypeKind::TypeVariant(
                        crate::types::decl::SharedVec::from(constructors),
                        layout,
                    ),
                    ..abstract_decl()
                }),
                RecStatus::TrecNot,
            ));
        }
        for n in 0..shape.records {
            signature.push(SignatureItem::SigType(
                Ident::create_local(format!("r{n}")),
                Arc::new(TypeDeclaration {
                    type_kind: TypeKind::TypeRecord(
                        crate::types::decl::SharedVec::from(vec![
                            label(&format!("a{n}"), int),
                            label(&format!("b{n}"), int),
                        ]),
                        RecordRepresentation::RecordRegular,
                    ),
                    ..abstract_decl()
                }),
                RecStatus::TrecNot,
            ));
        }
        let value = |name: &str, ty| {
            SignatureItem::SigValue(
                Ident::create_local(name.to_string()),
                ValueDescription {
                    val_type: ty,
                    val_kind: ValueKind::ValReg,
                    val_loc: crate::types::DeclLoc::none(),
                    val_attributes: Default::default(),
                    val_path: None,
                },
            )
        };
        for n in 0..shape.children {
            // `M<n>: { type u; let own: u; let outer: t }`.
            let u = Ident::create_local("u");
            signature.push(module(
                &format!("M{n}"),
                ModuleType::MtySignature(Arc::new(vec![
                    SignatureItem::SigType(u, Arc::new(abstract_decl()), RecStatus::TrecNot),
                    value("own", ctx.new_generic_constr(Path::pident(u), vec![])),
                    value("outer", t_type()),
                ])),
            ));
        }
        if shape.chain > 0 {
            let mut inner = ModuleType::MtySignature(Arc::new(vec![SignatureItem::SigType(
                Ident::create_local("u"),
                Arc::new(abstract_decl()),
                RecStatus::TrecNot,
            )]));
            for _ in 1..shape.chain {
                inner = ModuleType::MtySignature(Arc::new(vec![module("Chain", inner)]));
            }
            signature.push(module("Chain", inner));
        }
        if !shape.bare {
            signature.push(SignatureItem::SigModtype(
                Ident::create_local("S"),
                ModtypeDeclaration {
                    mtd_type: None,
                    mtd_attributes: vec![],
                    mtd_loc: crate::types::DeclLoc::none(),
                },
            ));
            signature.push(module(
                "Alias",
                ModuleType::MtyAlias(
                    AliasPresence::MtaAbsent,
                    Arc::new(Path::pident(Ident::create_persistent("Other_unit"))),
                ),
            ));
            signature.push(module(
                "Inner",
                ModuleType::MtySignature(Arc::new(vec![SignatureItem::SigType(
                    Ident::create_local("u"),
                    Arc::new(abstract_decl()),
                    RecStatus::TrecNot,
                )])),
            ));
        }
        let signature = freeze(&world, &scratch, signature)
            .expect("the unit's signature freezes")
            .value;
        let ps = PersStruct {
            ps_name: name.clone(),
            ps_sig: Arc::new(signature),
            ps_filename: format!("{name}.res"),
            ps_deprecated: None,
            ps_crcs: vec![],
            ps_alias_rewrites: Default::default(),
            ps_view: Default::default(),
        };
        let pps = Arc::new(crate::cmi::portable_types::serialize_pers_struct(
            &ps, ctx, None,
        ));
        world
            .unit(&pps, || Some(Arc::new(ps)))
            .expect("the world takes the unit")
    }

    fn view_of(unit: &Arc<PersStruct>) -> Arc<ModuleView> {
        let world = World::current();
        world
            .views()
            .get_or_build(&world, &ViewKey::Unit(unit))
            .expect("the view builds")
    }

    fn key_of(unit: &PersStruct) -> QualifiedModuleComponentsCacheKey {
        QualifiedModuleComponentsCacheKey::new(
            Path::pident(Ident::create_persistent(&unit.ps_name)),
            None,
        )
    }

    #[test]
    fn view_is_built_once_under_contention() {
        let unit = unit("Contended", 50);
        let barrier = Arc::new(std::sync::Barrier::new(16));
        let threads: Vec<_> = (0..16)
            .map(|_| {
                let (unit, barrier) = (unit.clone(), barrier.clone());
                std::thread::spawn(move || {
                    barrier.wait();
                    view_of(&unit)
                })
            })
            .collect();
        let views: Vec<_> = threads.into_iter().map(|t| t.join().unwrap()).collect();
        let cell = unit.ps_view.get().expect("a world unit has a view cell");
        assert_eq!(cell.builds.load(Ordering::Relaxed), 1);
        for view in &views {
            assert!(Arc::ptr_eq(view, &views[0]));
        }
    }

    #[test]
    fn a_unit_the_world_does_not_own_has_no_view() {
        let ps = Arc::new(PersStruct {
            ps_name: "Private_unit".into(),
            ps_sig: Arc::new(vec![]),
            ps_filename: "Private_unit.res".into(),
            ps_deprecated: None,
            ps_crcs: vec![],
            ps_alias_rewrites: Default::default(),
            ps_view: Default::default(),
        });
        let world = World::current();
        assert!(
            world
                .views()
                .get_or_build(&world, &ViewKey::Unit(&ps))
                .is_none()
        );
    }

    #[test]
    fn second_lookup_through_a_view_allocates_nothing() {
        let unit = unit("Looked_up", 20);
        let ctx = compilation();
        let view = view_of(&unit);
        ctx.adopt_view(key_of(&unit), view.clone());
        let components = Components::World(&view);
        let first = components
            .lookup_value_for_access("v7", &ctx)
            .expect("the value is in the view");
        let (nodes, adoptions) = (ctx.type_expr_count(), ctx.view_adoptions.get());
        let cell = unit.ps_view.get().unwrap();
        let builds = cell.builds.load(Ordering::Relaxed);
        let second = components
            .lookup_value_for_access("v7", &ctx)
            .expect("the value is in the view");
        // Looked up again through the compilation's component cache.
        let third = ctx
            .with_qualified_module_components(&key_of(&unit), |components| {
                components.lookup_value_for_access("v7", &ctx)
            })
            .flatten()
            .expect("the adopted view answers");
        assert_eq!(first.2.val_type, second.2.val_type);
        assert_eq!(first.2.val_type, third.2.val_type);
        assert!(first.2.val_type.is_shared(), "a view's types are frozen");
        assert_eq!(ctx.type_expr_count(), nodes);
        assert_eq!(ctx.view_adoptions.get(), adoptions);
        assert_eq!(cell.builds.load(Ordering::Relaxed), builds);
        // The value's type names the unit's type through the unit.
        let printed = match ctx.get_desc(first.2.val_type).into_desc() {
            crate::types::type_expr::TypeDesc::Tconstr { path, .. } => path.name(),
            _ => panic!("a constructor type"),
        };
        assert_eq!(printed, format!("{}.t", unit.ps_name));
    }

    #[test]
    fn adoption_happens_once_and_registers_the_views_aliases() {
        let unit = unit("Adopted", 3);
        let ctx = compilation();
        let view = view_of(&unit);
        ctx.adopt_view(key_of(&unit), view.clone());
        ctx.adopt_view(key_of(&unit), view.clone());
        assert_eq!(ctx.view_adoptions.get(), 1);
        let component = Path::pdot(*view.access_path(), "Alias");
        let sources = ctx.alias_sources_for_component_path(&component);
        assert_eq!(sources.len(), 1);
        assert_eq!(sources[0].name(), "Other_unit");
        assert_eq!(
            view.lookup_module_alias_target("Alias", false)
                .expect("an alias child has its target")
                .name(),
            "Other_unit"
        );
        assert!(view.lookup_module_alias_target("Inner", true).is_none());
    }

    #[test]
    fn a_views_label_array_is_frozen_and_tied() {
        let unit = unit("Labelled", 1);
        let ctx = compilation();
        let view = view_of(&unit);
        let family = view
            .type_label_family("t")
            .expect("a record type has its label array");
        assert!(matches!(family.tier(), Some(LabelArrayTier::Frozen(_))));
        let labels = ctx.label_family(family).expect("any compilation reads it");
        assert_eq!(labels.len(), 2);
        for label in labels.iter() {
            assert_eq!(label.lbl_all, family);
            assert!(label.lbl_res.is_shared() && label.lbl_arg.is_shared());
        }
        // A lookup by name returns the array's own label.
        let second = view.lookup_labels("second");
        assert_eq!(second.len(), 1);
        assert_eq!(second[0].lbl_all, family);
        assert_eq!(second[0].lbl_pos, 1);
        assert!(view.lookup_labels("missing").is_empty());
        // The opened labels are the same array's.
        assert_eq!(view.opened_items().labels.len(), 2);
        assert_eq!(view.opened_items().labels[0].1.lbl_all, family);
    }

    #[test]
    fn a_child_declaration_is_forced_once_for_all_workers() {
        let unit = unit("Parent", 1);
        let view = view_of(&unit);
        let world = World::current();
        let threads: Vec<_> = (0..8)
            .map(|_| {
                let (view, world) = (view.clone(), world.clone());
                std::thread::spawn(move || {
                    view.lookup_forced_module(&world, "Inner")
                        .expect("the child module exists")
                })
            })
            .collect();
        let forced: Vec<_> = threads.into_iter().map(|t| t.join().unwrap()).collect();
        let first = forced[0].2.as_ref().expect("the pool has room");
        for (_, _, forced) in &forced {
            let (id, md) = forced.as_ref().expect("the pool has room");
            assert!(Arc::ptr_eq(md, &first.1));
            assert!(id.same(&first.0));
        }
        assert!(view.lookup_forced_module(&world, "Missing").is_none());
        // A compilation registers the forced declaration once.
        let ctx = compilation();
        ctx.adopt_view(key_of(&unit), view.clone());
        let components = Components::World(&view);
        let (_, id, md) = components
            .lookup_qualified_module_shared("Inner", &ctx)
            .expect("the child module exists");
        let (registered_id, registered) = ctx
            .find_qualified_module_decl(view.access_path(), "Inner")
            .expect("the forced declaration is registered");
        assert!(Arc::ptr_eq(&registered, &md) && registered_id.same(&id));
    }

    #[test]
    fn view_build_cost_is_linear_in_the_signature() {
        // 10,000 values of a unit whose every value names the unit's type:
        // one visit per item, a constant number of substitution builds, and
        // nodes in proportion to the items.
        let measure = |values: usize| {
            let unit = unit("Large", values);
            let (steps, maps) = (build_steps(), subst_map_builds());
            let view = view_of(&unit);
            (
                build_steps() - steps,
                subst_map_builds() - maps,
                view.nodes,
                view,
            )
        };
        let (small_steps, small_maps, small_nodes, _) = measure(1_000);
        let (large_steps, large_maps, large_nodes, view) = measure(10_000);
        // The items: one type, the values, a module type and two modules.
        assert_eq!(small_steps, 1_004);
        assert_eq!(large_steps, 10_004);
        assert_eq!(small_maps, large_maps);
        assert!(large_maps <= 4, "{large_maps} substitution builds");
        assert!(
            large_nodes <= small_nodes * 10 + 16,
            "{small_nodes} nodes for 1,000 values, {large_nodes} for 10,000"
        );
        assert_eq!(view.opened_items().values.len(), 10_000);
        assert!(view.lookup_value_for_access("v9999").is_some());
    }

    #[test]
    fn forced_child_note_costs_one_bit_per_child() {
        // 10,000 distinct children noted twice: each registers once.
        let unit = unit("Noted", 1);
        let view = view_of(&unit);
        let world = World::current();
        let ctx = compilation();
        let (item, _, forced) = view.lookup_forced_module(&world, "Inner").unwrap();
        let (id, md) = forced.expect("the pool has room");
        for round in 0..2 {
            for child in 0..10_000 {
                ctx.note_forced_view_module(&view, item + child, "Inner", id, &md);
            }
            assert!(
                ctx.find_qualified_module_decl(view.access_path(), "Inner")
                    .is_some(),
                "round {round}"
            );
        }
    }

    #[test]
    fn sizes_are_pinned() {
        assert_eq!(std::mem::size_of::<ViewId>(), 4);
        assert_eq!(std::mem::size_of::<Components<'static>>(), 16);
        assert_eq!(std::mem::size_of::<ViewKey<'static>>(), 16);
        // Stored per child module of a view.
        // (and, in a test build, its 8-byte build counter).
        assert_eq!(std::mem::size_of::<ViewCell>(), 32 + 8);
        // Stored per value of a view.
        assert_eq!(
            std::mem::size_of::<ViewValue>(),
            std::mem::size_of::<ValueDescription>() + 24
        );
    }

    #[test]
    fn a_published_view_prints_like_a_rebuild() {
        let unit = unit("Verified", 5);
        let view = view_of(&unit);
        let world = World::current();
        let ctx = compilation();
        let scratch = ViewScratch::fresh();
        let rebuilt = describe_view(&world, &scratch, &ViewKey::Unit(&unit)).unwrap();
        let published = view.canonical(&ctx);
        assert_eq!(published, rebuilt.canonical(scratch.ctx()));
        assert!(published.contains("v4"));
        // A description publishes nothing: no view is numbered by it.
        let ids = world.views().next_id.load(Ordering::Relaxed);
        // `verify_view` returns when they agree (it aborts otherwise).
        verify_view(&world, &ViewKey::Unit(&unit), &view);
        if world.views().next_id.load(Ordering::Relaxed) != ids {
            // Another test built a view meanwhile; the description itself
            // holds the unpublished number.
            assert_eq!(rebuilt.id, ViewId(u32::MAX));
        }
    }

    fn constructor_descriptions() -> u64 {
        crate::types::env_lazy::CONSTRUCTOR_DESCRIPTIONS.with(|count| count.get())
    }

    fn label_array_copies() -> u64 {
        crate::types::world::LABEL_ARRAY_COPIES.with(|copies| copies.get())
    }

    /// Steps of one view build of a unit of `shape`: signature items
    /// visited, substitution builds, constructors described by the lookup
    /// tables, label arrays copied by the freeze.
    fn build_counts(name: &str, shape: Shape) -> (u64, u64, u64, u64, Arc<ModuleView>) {
        let unit = unit_of(name, shape);
        let before = (
            build_steps(),
            subst_map_builds(),
            constructor_descriptions(),
            label_array_copies(),
        );
        let view = view_of(&unit);
        (
            build_steps() - before.0,
            subst_map_builds() - before.1,
            constructor_descriptions() - before.2,
            label_array_copies() - before.3,
            view,
        )
    }

    #[test]
    fn view_build_describes_each_constructor_once_per_table() {
        // 10,000 constructors in one variant type, and 10,000 variant
        // types of one constructor: the lookup table describes each
        // constructor once and the opened items hold each once.
        for (name, variants, constructors) in
            [("One_variant", 1, 10_000), ("Many_variants", 10_000, 1)]
        {
            let (steps, maps, described, _, view) = build_counts(
                name,
                Shape {
                    variants,
                    constructors,
                    ..Shape::default()
                },
            );
            assert_eq!(steps, variants as u64 + 4, "{name}");
            assert_eq!(described, 10_000, "{name}");
            assert!(maps <= 4, "{name}: {maps} substitution builds");
            assert_eq!(view.opened_items().constructors.len(), 10_000, "{name}");
            assert_eq!(view.constructors.len(), 10_000, "{name}");
            let last = format!("C{}_{}", variants - 1, constructors - 1);
            let found = view.lookup_constructors(&last);
            assert_eq!(found.len(), 1, "{name}");
            assert!(found[0].cstr_res.is_shared(), "{name}");
        }
    }

    #[test]
    fn view_build_copies_each_label_array_once() {
        // 10,000 record types of two labels. Every array is named by its
        // two labels in the label table, by the family table and by the
        // two opened labels; the freeze copies it once.
        let (steps, _, _, copies, view) = build_counts(
            "Records",
            Shape {
                records: 10_000,
                ..Shape::default()
            },
        );
        assert_eq!(steps, 10_004);
        // The fixed record type `t` and the 10,000.
        assert_eq!(copies, 10_001);
        assert_eq!(view.label_families.len(), 10_001);
        assert_eq!(view.opened_items().labels.len(), 20_002);
        let family = view.type_label_family("r9999").expect("the record's array");
        let world = World::current();
        let Some(LabelArrayTier::Frozen(index)) = family.tier() else {
            panic!("a view's label array is frozen");
        };
        let labels = world.label_array(index).expect("published");
        assert_eq!(labels.len(), 2);
        assert!(labels.iter().all(|label| label.lbl_all == family));
        assert_eq!(view.lookup_labels("b9999")[0].lbl_all, family);
    }

    #[test]
    fn opened_layers_take_one_insert_per_item() {
        let shape = Shape {
            values: 10_000,
            variants: 100,
            constructors: 100,
            records: 5_000,
            children: 10,
            bare: false,
            chain: 0,
        };
        let unit = unit_of("Opened", shape);
        let view = view_of(&unit);
        let ctx = compilation();
        let tables = ctx.thread_store().view_tables(&view);
        let inserts = || crate::types::env::OPEN_TABLE_INSERTS.with(|inserts| inserts.get());
        let (before, nodes) = (inserts(), ctx.type_expr_count());
        let layers = tables.opened_layers(&view, &ctx);
        let items = view.opened_items();
        // Values, types, constructors, labels, modules, module types, and
        // the component tables of the children (`Alias`, `Inner` and the
        // ten).
        let expected = items.values.len()
            + items.types.len()
            + items.constructors.len()
            + items.labels.len()
            + items.modules.len()
            + items.modtypes.len()
            + 12;
        assert_eq!(items.values.len(), 10_000);
        assert_eq!(items.constructors.len(), 10_000);
        assert_eq!(items.labels.len(), 10_002);
        assert_eq!((inserts() - before) as usize, expected);
        // No type node, and the second open reads the worker's tables.
        assert_eq!(ctx.type_expr_count(), nodes);
        let again = tables.opened_layers(&view, &ctx);
        assert!(std::rc::Rc::ptr_eq(&layers, &again));
        assert_eq!((inserts() - before) as usize, expected);
    }

    #[test]
    fn child_lookups_scan_the_signature_once() {
        // 10,000 children looked up last to first, then all again: the
        // scan visits each signature item once in total.
        let shape = Shape {
            children: 10_000,
            ..Shape::default()
        };
        let (steps, maps, _, _, view) = build_counts("Children", shape);
        assert_eq!(steps, 10_004);
        assert!(maps <= 4, "{maps} substitution builds");
        let ctx = compilation();
        let tables = ctx.thread_store().view_tables(&view);
        let scanned = || crate::types::env_lazy::CHILD_SCAN_STEPS.with(|steps| steps.get());
        let before = scanned();
        for round in 0..2 {
            for n in (0..10_000).rev() {
                assert!(
                    tables
                        .child_components(&view, &format!("M{n}"), &ctx)
                        .is_some(),
                    "round {round}, child {n}"
                );
            }
        }
        assert!(tables.child_components(&view, "Missing", &ctx).is_none());
        assert_eq!(scanned() - before, 10_004);
    }

    #[test]
    fn forcing_every_child_builds_the_parents_substitution_once() {
        // 10,000 children forced, twice over. A unit with an item that
        // needs the component substitution has it from its build; a bare
        // one builds it on the first force. Neither builds it again.
        for bare in [false, true] {
            let shape = Shape {
                children: 10_000,
                bare,
                ..Shape::default()
            };
            let before = subst_map_builds();
            let unit = unit_of("Forced", shape);
            let view = view_of(&unit);
            let built = subst_map_builds() - before;
            // The component substitution when an item needs it, and the
            // one the opened module types are described with.
            assert_eq!(built, if bare { 0 } else { 2 }, "bare: {bare}");
            let world = World::current();
            for round in 0..2 {
                for n in 0..10_000 {
                    let (_, _, forced) = view
                        .lookup_forced_module(&world, &format!("M{n}"))
                        .expect("the child exists");
                    let (_, md) = forced.expect("the pool has room");
                    assert!(
                        matches!(md.md_type, ModuleType::MtySignature(_)),
                        "round {round}, child {n}"
                    );
                }
            }
            assert_eq!(
                subst_map_builds() - before,
                if bare { 1 } else { 2 },
                "bare: {bare}"
            );
            // A cell per child module, none per other item.
            assert_eq!(view.children.len(), if bare { 10_000 } else { 10_002 });
        }
    }

    #[test]
    fn a_view_the_pool_has_no_room_for_fails_once_for_every_compilation() {
        use crate::types::world::FAIL_NEXT_FREEZE;
        let failed = unit("No_room", 3);
        let world = World::current();
        FAIL_NEXT_FREEZE.with(|fail| fail.set(true));
        assert!(
            world
                .views()
                .get_or_build(&world, &ViewKey::Unit(&failed))
                .is_none()
        );
        assert!(!FAIL_NEXT_FREEZE.with(|fail| fail.get()), "the build ran");
        // The failure is stored: no worker builds again.
        let threads: Vec<_> = (0..8)
            .map(|_| {
                let (failed, world) = (failed.clone(), world.clone());
                std::thread::spawn(move || {
                    world
                        .views()
                        .get_or_build(&world, &ViewKey::Unit(&failed))
                        .is_none()
                })
            })
            .collect();
        assert!(threads.into_iter().all(|t| t.join().unwrap()));
        let cell = failed.ps_view.get().unwrap();
        assert_eq!(cell.builds.load(Ordering::Relaxed), 1);

        // A compilation looking the unit up builds its components for
        // itself, and reads the same value type through them as through
        // the view of a unit that did fit.
        let fits = unit("Room", 3);
        let ctx = compilation();
        let mut pers = crate::cmi::persistent_env::PersistentEnv::new();
        pers.set_in_process_mode(true);
        pers.insert_loaded_unit(failed.clone());
        pers.insert_loaded_unit(fits.clone());
        ctx.set_persistent_env(pers.clone());
        let mut pers = Some(pers);
        let env = crate::types::env::Env::empty();
        let mut lookup = |unit: &PersStruct| {
            let path = Path::pident(Ident::create_persistent(&unit.ps_name));
            crate::types::typecore::with_resolved_module_components_for_path(
                &path,
                &env,
                &mut pers,
                &ctx,
                |components| {
                    let (_, _, desc) = components
                        .lookup_value_for_access("v2", &ctx)
                        .expect("the value is found");
                    let printed = match ctx.get_desc(desc.val_type).into_desc() {
                        crate::types::type_expr::TypeDesc::Tconstr { path, .. } => path.name(),
                        _ => panic!("a constructor type"),
                    };
                    (matches!(components, Components::World(_)), printed)
                },
            )
            .expect("the unit has components")
        };
        assert_eq!(lookup(&failed), (false, format!("{}.t", failed.ps_name)));
        assert_eq!(lookup(&fits), (true, format!("{}.t", fits.ps_name)));
        assert_eq!(ctx.view_adoptions.get(), 1);
    }

    fn child_view_of(parent: &Arc<ModuleView>, name: &str) -> Arc<ModuleView> {
        let world = World::current();
        let ordinal = parent
            .structure_child(name)
            .expect("the child is declared with a signature");
        world
            .views()
            .get_or_build(&world, &ViewKey::Child(parent, ordinal))
            .expect("the child view builds")
    }

    fn printed_type(ctx: &TypeContext, desc: &ValueDescription) -> String {
        match ctx.get_desc(desc.val_type).into_desc() {
            crate::types::type_expr::TypeDesc::Tconstr { path, .. } => path.name(),
            _ => panic!("a constructor type"),
        }
    }

    #[test]
    fn a_child_view_is_built_once_under_contention() {
        let shape = Shape {
            children: 1,
            ..Shape::default()
        };
        let parent = view_of(&unit_of("Contended_parent", shape));
        let barrier = Arc::new(std::sync::Barrier::new(16));
        let threads: Vec<_> = (0..16)
            .map(|_| {
                let (parent, barrier) = (parent.clone(), barrier.clone());
                std::thread::spawn(move || {
                    barrier.wait();
                    child_view_of(&parent, "M0")
                })
            })
            .collect();
        let views: Vec<_> = threads.into_iter().map(|t| t.join().unwrap()).collect();
        let ordinal = parent.structure_child("M0").unwrap();
        let cell = &parent.children[ordinal as usize];
        assert_eq!(cell.builds.load(Ordering::Relaxed), 1);
        for view in &views {
            assert!(Arc::ptr_eq(view, &views[0]));
        }
        // A child that is a path, and one that does not exist, are no
        // view keys.
        assert!(parent.structure_child("Alias").is_none());
        assert!(parent.structure_child("Missing").is_none());
    }

    #[test]
    fn a_child_view_names_its_items_and_its_parents_through_their_paths() {
        let shape = Shape {
            children: 2,
            ..Shape::default()
        };
        let unit = unit_of("Family", shape);
        let parent = view_of(&unit);
        let ctx = compilation();
        ctx.adopt_view(key_of(&unit), parent.clone());
        let ordinal = parent.structure_child("M1").unwrap();
        let child = crate::types::typecore::adopt_child_view(&parent, ordinal, &ctx)
            .expect("the child view builds");
        assert_eq!(
            child.access_path().name(),
            format!("{}.M1", unit.ps_name)
        );
        let (_, _, own) = child.lookup_value_for_access("own").unwrap();
        let (_, _, outer) = child.lookup_value_for_access("outer").unwrap();
        assert_eq!(printed_type(&ctx, &own), format!("{}.M1.u", unit.ps_name));
        assert_eq!(printed_type(&ctx, &outer), format!("{}.t", unit.ps_name));
        assert!(own.val_type.is_shared() && outer.val_type.is_shared());
        // Adopted once, and found again through the compilation's cache
        // under the child's path.
        let adoptions = ctx.view_adoptions.get();
        let again = crate::types::typecore::adopt_child_view(&parent, ordinal, &ctx).unwrap();
        assert!(Arc::ptr_eq(&again, &child));
        assert_eq!(ctx.view_adoptions.get(), adoptions);
        let key = QualifiedModuleComponentsCacheKey::new(*child.access_path(), None);
        let cached = ctx
            .with_qualified_module_components(&key, |components| {
                matches!(components, Components::World(view) if Arc::ptr_eq(view, &child))
            })
            .expect("the child view is in the component cache");
        assert!(cached);
        // The published view prints as a rebuild on another context does.
        let world = World::current();
        verify_view(&world, &ViewKey::Child(&parent, ordinal), &child);
    }

    #[test]
    fn child_views_of_one_parent_read_its_substitution() {
        // 10,000 children of one parent, each with its own view: the
        // parent's substitution (10,000 items) is built once, not once per
        // child, so the substitution builds of all the children together
        // visit items in proportion to the children.
        let shape = Shape {
            children: 10_000,
            ..Shape::default()
        };
        let parent = view_of(&unit_of("Siblings", shape));
        let items = || crate::cmi::persistent_env::SUBST_MAP_ITEMS.with(|items| items.get());
        let (before, steps) = (items(), build_steps());
        for n in 0..10_000 {
            let child = child_view_of(&parent, &format!("M{n}"));
            assert!(child.lookup_value_for_access("outer").is_some(), "child {n}");
        }
        // Three items per child, visited by a constant number of
        // substitution builds of the child's own signature.
        let visited = items() - before;
        assert!(visited <= 10_000 * 3 * 8, "{visited} items visited");
        assert_eq!(build_steps() - steps, 10_000 * 3);
        for n in [0, 9_999] {
            let ordinal = parent.structure_child(&format!("M{n}")).unwrap();
            assert_eq!(
                parent.children[ordinal as usize]
                    .builds
                    .load(Ordering::Relaxed),
                1
            );
        }
    }

    #[test]
    fn a_chain_of_children_costs_one_build_per_link() {
        // 500 deep is what the representation allows here: a nested
        // signature is copied, substituted and frozen by recursion over the
        // nesting, and a chain 1,000 deep overflows a test thread's 2 MB
        // stack in a debug build. One view is built per link and none
        // twice. A link's build copies the signature declared below it
        // (`Subst.signature sub sg`, env.ml:1516), so the items copied by
        // the whole chain grow with the square of its depth, as they do
        // when OCaml forces each level.
        const DEPTH: usize = 500;
        let shape = Shape {
            chain: DEPTH,
            bare: true,
            ..Shape::default()
        };
        let unit = unit_of("Chained", shape);
        let mut view = view_of(&unit);
        let steps = build_steps();
        let mut links = Vec::new();
        for _ in 0..DEPTH {
            let child = child_view_of(&view, "Chain");
            links.push((view.clone(), child.clone()));
            view = child;
        }
        // One item per link (the next module; the last link holds the type).
        assert_eq!(build_steps() - steps, DEPTH as u64);
        assert_eq!(view.access_path().name().matches(".Chain").count(), DEPTH);
        assert!(view.lookup_type("u").is_some());
        for (parent, child) in &links {
            let ordinal = parent.structure_child("Chain").unwrap();
            let cell = &parent.children[ordinal as usize];
            assert_eq!(cell.builds.load(Ordering::Relaxed), 1);
            // Asking again reads the cell.
            assert!(Arc::ptr_eq(&child_view_of(parent, "Chain"), child));
            assert_eq!(cell.builds.load(Ordering::Relaxed), 1);
        }
    }

    #[test]
    fn a_unit_path_is_a_unit_key_whatever_aliases_the_compilation_met() {
        let backing = unit("Backing", 3);
        let name = backing.ps_name.as_str();
        // `Namespace` holds `module Alias = <backing>`.
        let namespace = Arc::new(PersStruct {
            ps_name: "Namespace".into(),
            ps_sig: Arc::new(vec![SignatureItem::SigModule(
                Ident::create_local("Alias"),
                ModuleDeclaration {
                    md_type: ModuleType::MtyAlias(
                        AliasPresence::MtaAbsent,
                        Arc::new(Path::pident(Ident::create_persistent(name))),
                    ),
                    md_attributes: vec![],
                    md_loc: crate::types::DeclLoc::none(),
                    md_path: None,
                },
                RecStatus::TrecNot,
            )]),
            ps_filename: "Namespace.res".into(),
            ps_deprecated: None,
            ps_crcs: vec![],
            ps_alias_rewrites: Default::default(),
            ps_view: Default::default(),
        });
        let path = Path::pident(Ident::create_persistent(name));
        assert_eq!(unit_key_name(&path), Some(name));
        assert_eq!(unit_key_name(&Path::pdot(path, "Inner")), None);
        assert_eq!(
            unit_key_name(&Path::pident(Ident::create_local(name.to_string()))),
            None
        );
        let env = crate::types::env::Env::empty();
        let is_world_view = |ctx: &TypeContext,
                             pers: &mut Option<crate::cmi::persistent_env::PersistentEnv>| {
            crate::types::typecore::with_resolved_module_components_for_path(
                &path,
                &env,
                pers,
                ctx,
                |components| matches!(components, Components::World(_)),
            )
            .expect("the unit has components")
        };
        // One compilation has loaded the namespace and so knows the unit as
        // the backing unit of `Namespace.Alias`; the other has not; a third
        // looks the unit up without a persistent environment at hand.
        for (met_alias, with_env) in [(true, true), (false, true), (true, false)] {
            let ctx = compilation();
            let mut pers = crate::cmi::persistent_env::PersistentEnv::new();
            pers.set_in_process_mode(true);
            pers.insert_loaded_unit(backing.clone());
            pers.insert_loaded_unit(namespace.clone());
            if met_alias {
                pers.find_pers_struct("Namespace", &ctx)
                    .expect("the namespace is loaded");
            }
            assert_eq!(
                pers.qualified_alias_path_for_flattened_head(name).is_some(),
                met_alias
            );
            ctx.set_persistent_env(pers.clone());
            let mut pers = with_env.then_some(pers);
            assert!(is_world_view(&ctx, &mut pers), "{met_alias} {with_env}");
            assert_eq!(ctx.view_adoptions.get(), 1);
        }
        assert_eq!(
            backing.ps_view.get().unwrap().builds.load(Ordering::Relaxed),
            1
        );
    }

    #[test]
    fn a_child_the_pool_has_no_room_for_is_forced_by_the_compilation() {
        use crate::types::world::FAIL_NEXT_FREEZE;
        let unit = unit("No_room_child", 1);
        let view = view_of(&unit);
        let world = World::current();
        FAIL_NEXT_FREEZE.with(|fail| fail.set(true));
        let (_, _, forced) = view.lookup_forced_module(&world, "Inner").unwrap();
        assert!(forced.is_none());
        // Stored: a later lookup does not try the pool again.
        let (_, _, forced) = view.lookup_forced_module(&world, "Inner").unwrap();
        assert!(forced.is_none());
        let ctx = compilation();
        ctx.adopt_view(key_of(&unit), view.clone());
        let components = Components::World(&view);
        let (_, id, md) = components
            .lookup_qualified_module_shared("Inner", &ctx)
            .expect("the compilation forces the child");
        let maps = subst_map_builds();
        let (_, again_id, again) = components
            .lookup_qualified_module_shared("Inner", &ctx)
            .expect("the compilation forces the child");
        // Forced once per compilation.
        assert!(Arc::ptr_eq(&md, &again) && id.same(&again_id));
        assert_eq!(subst_map_builds(), maps);
        assert!(matches!(md.md_type, ModuleType::MtySignature(_)));
    }
}
