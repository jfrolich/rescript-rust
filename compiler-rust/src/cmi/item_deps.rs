//! Per-item interface digests and read sets, for incremental builds.
//!
//! A compiled unit publishes a digest for each of its top-level items (its
//! declaration plus the JS metadata other modules' code generation reads for
//! it: constants, arities, inlinable lambdas, hoisted exports) and one
//! module-level part (`@`: purity, package, file). A dependent records which
//! items of each unit it read: the paths its typed tree mentions, closed over
//! the declarations of what it read (reading `N.f : M.t => unit` also reads
//! `M.t`, and `M.t`'s manifest and constructors in turn) and over module
//! aliases (`NS.Child.x` reads `Child`'s `x`). A use of a whole module
//! (`open`, `include`, a module alias or functor argument) reads every item
//! (`*`). The dependent then has to be recompiled only when the digest of an
//! item it read changed.

use crate::types::path::PathView;
use std::collections::BTreeMap;
use std::hash::{Hash, Hasher};
use std::sync::Arc;

use smallvec::SmallVec;

use super::persistent_env::InMemoryModuleInfo;
use super::portable_types::{
    PortablePersStruct, PortableRowField, PortableTypeDesc, PortableTypeEntry,
};
use crate::name::Name;
use crate::types::decl::{
    ConstructorArguments, LabelDeclaration, ModuleType, Signature, SignatureItem, TypeInlinedType,
    TypeKind,
};
use crate::types::path::Path;

/// Every item of a unit.
pub const WHOLE: &str = "*";
/// The unit's module-level facts (always read with any item).
pub const MODULE_LEVEL: &str = "@";

/// The namespace of a top-level item.
#[derive(
    Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, serde::Serialize, serde::Deserialize,
)]
pub enum Kind {
    Value,
    Type,
    Module,
    Modtype,
    Extension,
}

impl Kind {
    fn tag(self) -> char {
        match self {
            Kind::Value => 'v',
            Kind::Type => 't',
            Kind::Module => 'm',
            Kind::Modtype => 'y',
            Kind::Extension => 'x',
        }
    }
}

/// The key of an item: its kind and name.
pub fn item_key(kind: Kind, name: &str) -> String {
    format!("{}:{name}", kind.tag())
}

/// What a compile read of a unit: every item, the module-level facts, or one
/// top-level item. Stored as the strings [`WHOLE`], [`MODULE_LEVEL`] and
/// [`item_key`] (see [`ItemKey::to_key_string`]); orders as those strings.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ItemKey {
    Whole,
    ModuleLevel,
    Item(Kind, Name),
}

impl ItemKey {
    /// The key as stored.
    pub fn to_key_string(self) -> String {
        match self {
            ItemKey::Whole => WHOLE.to_string(),
            ItemKey::ModuleLevel => MODULE_LEVEL.to_string(),
            ItemKey::Item(kind, name) => item_key(kind, &name),
        }
    }
}

impl Ord for ItemKey {
    /// The order of the stored strings: `*` < `@` < `k:name`, items by
    /// kind tag and then name (every item key has `:` second).
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        fn rank(key: &ItemKey) -> u8 {
            match key {
                ItemKey::Whole => 0,
                ItemKey::ModuleLevel => 1,
                ItemKey::Item(..) => 2,
            }
        }
        match (self, other) {
            (ItemKey::Item(ka, na), ItemKey::Item(kb, nb)) => {
                (ka.tag(), na.as_str()).cmp(&(kb.tag(), nb.as_str()))
            }
            _ => rank(self).cmp(&rank(other)),
        }
    }
}

impl PartialOrd for ItemKey {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

/// The items read of each unit, by unit name. Unordered: sort units by
/// name and keys by [`ItemKey`]'s order (the stored strings' order) where
/// the order matters.
pub type ResolvedReads = ahash::AHashMap<Name, ahash::AHashSet<ItemKey>>;

/// The path segments of a read; most paths have few.
pub type Segs = SmallVec<[Name; 3]>;

/// A reference to something in a unit: `unit.segs`, where the last segment
/// is of `kind`. Empty `segs` is the unit itself, as a whole module.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct UnitRead {
    pub unit: Name,
    pub segs: Segs,
    pub kind: Kind,
}

/// The root of a dotted path and its segments, `None` under a functor
/// application.
fn flatten_names(path: Path, segs: &mut Segs) -> Option<&'static crate::ident::Ident> {
    match path.view() {
        PathView::Pident(id) => Some(id),
        PathView::Pdot(parent, name, _) => {
            let root = flatten_names(*parent, segs)?;
            segs.push(*name);
            Some(root)
        }
        PathView::Papply(_, _) => None,
    }
}

/// The read a path denotes. Paths rooted at a persistent unit read that unit;
/// with `own_unit`, paths rooted at a local identifier are read in it (used
/// for the declarations of a unit's own signature). Functor applications
/// read the functor and the argument as whole modules.
pub fn read_of_path(path: &Path, kind: Kind, own_unit: Option<Name>, out: &mut Vec<UnitRead>) {
    // Without `own_unit` only paths with a persistent root read anything.
    if own_unit.is_none() && !has_persistent_head(path) {
        return;
    }
    if let PathView::Papply(f, x) = path.view() {
        read_of_path(f, Kind::Module, own_unit, out);
        read_of_path(x, Kind::Module, own_unit, out);
        return;
    }
    let mut segs = Segs::new();
    let Some(root) = flatten_names(*path, &mut segs) else {
        // A dotted path under a functor application.
        for head in path.heads() {
            read_of_path(&Path::pident(*head), Kind::Module, own_unit, out);
        }
        return;
    };
    if root.is_persistent() {
        out.push(UnitRead {
            unit: root.name_atom(),
            segs,
            kind,
        });
    } else if let Some(unit) = own_unit {
        segs.insert(0, root.name_atom());
        out.push(UnitRead { unit, segs, kind });
    }
}

fn has_persistent_head(path: &Path) -> bool {
    match path.view() {
        PathView::Pident(id) => id.is_persistent(),
        PathView::Pdot(parent, _, _) => has_persistent_head(parent),
        PathView::Papply(f, x) => has_persistent_head(f) || has_persistent_head(x),
    }
}

/// The kind and name of a top-level item, `None` for class items.
fn sig_item_kind_name(item: &SignatureItem) -> Option<(Kind, Name)> {
    Some(match item {
        SignatureItem::SigValue(id, _) => (Kind::Value, id.name_atom()),
        SignatureItem::SigType(id, _, _) => (Kind::Type, id.name_atom()),
        SignatureItem::SigTypext(id, _, _) => (Kind::Extension, id.name_atom()),
        SignatureItem::SigModule(id, _, _) => (Kind::Module, id.name_atom()),
        SignatureItem::SigModtype(id, _) => (Kind::Modtype, id.name_atom()),
        SignatureItem::SigClass | SignatureItem::SigClassType => return None,
    })
}

fn hash_one(value: &impl Hash) -> u64 {
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    value.hash(&mut hasher);
    hasher.finish()
}

/// The digest of every top-level item of a unit, keyed by [`item_key`], plus
/// [`MODULE_LEVEL`] and [`WHOLE`] (a digest of all of them).
pub fn item_digests(
    ps: Option<&PortablePersStruct>,
    info: Option<&InMemoryModuleInfo>,
) -> BTreeMap<String, u64> {
    let mut digests: BTreeMap<String, u64> = BTreeMap::new();
    if let Some(ps) = ps {
        // Hoisted exports grouped by their top-level name, in their original
        // relative order.
        let mut hoisted_by_name: ahash::AHashMap<&str, Vec<&crate::lambda::HoistedExport>> =
            ahash::AHashMap::new();
        if let Some(info) = info {
            for hoisted in info.cmj_hoisted_exports.iter() {
                if let Some(first) = hoisted.path.first() {
                    hoisted_by_name
                        .entry(first.as_str())
                        .or_default()
                        .push(hoisted);
                }
            }
        }
        for &(kind, name, declaration) in &ps.summary().item_hashes {
            let key = item_key(kind, &name);
            let mut hasher = std::collections::hash_map::DefaultHasher::new();
            if let Some(previous) = digests.get(&key) {
                previous.hash(&mut hasher);
            }
            declaration.hash(&mut hasher);
            // The JS metadata dependents' code generation reads for the item,
            // without locations and identifier stamps (see `digest_ser`).
            if let (Some(info), Kind::Value | Kind::Module) = (info, kind) {
                let name = name.as_str();
                let mut canonical = super::digest_ser::Canonical::new(&mut hasher);
                canonical.hash(&info.cmj_export_constants.get(name));
                canonical.hash(&info.cmj_export_arities.get(name));
                canonical.hash(&info.cmj_export_lambdas.get(name));
                for hoisted in hoisted_by_name.get(name).into_iter().flatten() {
                    canonical.hash(*hoisted);
                }
            }
            digests.insert(key, hasher.finish());
        }
    }
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    if let Some(ps) = ps {
        ps.ps_deprecated.hash(&mut hasher);
        ps.ps_filename.hash(&mut hasher);
    }
    if let Some(info) = info {
        info.source_path.hash(&mut hasher);
        info.is_pure.hash(&mut hasher);
        info.package_name.hash(&mut hasher);
        info.js_output_suffix.hash(&mut hasher);
        info.package_outputs.hash(&mut hasher);
        info.is_runtime.hash(&mut hasher);
    }
    digests.insert(MODULE_LEVEL.to_string(), hasher.finish());
    let whole = hash_one(&digests);
    digests.insert(WHOLE.to_string(), whole);
    digests
}

/// Collects the references of a unit's declarations.
struct RefWalker<'a> {
    unit: Name,
    /// The unit's top-level item keys: a local identifier that names none of
    /// them is predefined (`int`, `option`) or bound inside the item being
    /// walked (a functor parameter, a sibling in a submodule).
    own_keys: &'a ahash::AHashSet<(Kind, Name)>,
    entries: &'a [PortableTypeEntry],
    /// `seen[idx] == epoch` when entry `idx` was walked for the current item.
    seen: Vec<u32>,
    epoch: u32,
    out: Vec<UnitRead>,
}

impl RefWalker<'_> {
    fn path(&mut self, path: &Path, kind: Kind) {
        let start = self.out.len();
        read_of_path(path, kind, Some(self.unit), &mut self.out);
        let own_keys = self.own_keys;
        let unit = self.unit;
        let mut index = start;
        while index < self.out.len() {
            let read = &self.out[index];
            let keep = read.unit != unit
                || read.segs.first().is_some_and(|first| {
                    let first_kind = if read.segs.len() > 1 {
                        Kind::Module
                    } else {
                        read.kind
                    };
                    own_keys.contains(&(first_kind, *first))
                });
            if keep {
                index += 1;
            } else {
                self.out.swap_remove(index);
            }
        }
    }

    fn ty(&mut self, idx: usize) {
        if idx >= self.entries.len() || self.seen[idx] == self.epoch {
            return;
        }
        self.seen[idx] = self.epoch;
        match &self.entries[idx].desc {
            PortableTypeDesc::Tvar(_) | PortableTypeDesc::Tunivar(_) | PortableTypeDesc::Tnil => {}
            PortableTypeDesc::Tarrow { args, ret } => {
                for (_, arg) in args {
                    self.ty(*arg);
                }
                self.ty(*ret);
            }
            PortableTypeDesc::Ttuple(elems) => {
                for elem in elems {
                    self.ty(*elem);
                }
            }
            PortableTypeDesc::Tconstr { path, args } => {
                self.path(path, Kind::Type);
                for arg in args {
                    self.ty(*arg);
                }
            }
            PortableTypeDesc::Tobject { fields } => self.ty(*fields),
            PortableTypeDesc::Tfield { typ, rest, .. } => {
                self.ty(*typ);
                self.ty(*rest);
            }
            PortableTypeDesc::Tlink(idx) | PortableTypeDesc::Tsubst(idx) => self.ty(*idx),
            PortableTypeDesc::Tvariant(row) => {
                for (_, field) in &row.row_fields {
                    match field {
                        PortableRowField::Rpresent(Some(idx)) => self.ty(*idx),
                        PortableRowField::Reither { types, .. } => {
                            for idx in types {
                                self.ty(*idx);
                            }
                        }
                        PortableRowField::Rpresent(None) | PortableRowField::Rabsent => {}
                    }
                }
                self.ty(row.row_more);
                if let Some((path, args)) = &row.row_name {
                    self.path(path, Kind::Type);
                    for arg in args {
                        self.ty(*arg);
                    }
                }
            }
            PortableTypeDesc::Tpoly { body, vars } => {
                self.ty(*body);
                for var in vars {
                    self.ty(*var);
                }
            }
            PortableTypeDesc::Tpackage { path, args, .. } => {
                self.path(path, Kind::Modtype);
                for arg in args {
                    self.ty(*arg);
                }
            }
        }
    }

    fn labels(&mut self, labels: &[LabelDeclaration]) {
        for label in labels {
            self.ty(label.ld_type.index());
        }
    }

    fn cstr_args(&mut self, args: &ConstructorArguments) {
        match args {
            ConstructorArguments::CstrTuple(types) => {
                for t in types {
                    self.ty(t.index());
                }
            }
            ConstructorArguments::CstrRecord(labels) => self.labels(labels),
        }
    }

    fn module_type(&mut self, mty: &ModuleType) {
        match mty {
            ModuleType::MtyIdent(path) => self.path(path, Kind::Modtype),
            ModuleType::MtyAlias(_, path) => self.path(path, Kind::Module),
            ModuleType::MtySignature(sig) => self.signature(sig),
            ModuleType::MtyFunctor {
                param_type, result, ..
            } => {
                if let Some(param_type) = param_type {
                    self.module_type(param_type);
                }
                self.module_type(result);
            }
        }
    }

    fn signature(&mut self, sig: &Signature) {
        for item in sig {
            self.item(item);
        }
    }

    fn item(&mut self, item: &SignatureItem) {
        match item {
            SignatureItem::SigValue(_, vd) => {
                self.ty(vd.val_type.index());
                if let Some(path) = &vd.val_path {
                    self.path(path, Kind::Value);
                }
            }
            SignatureItem::SigType(_, td, _) => {
                for param in &td.type_params {
                    self.ty(param.index());
                }
                if let Some(manifest) = td.type_manifest {
                    self.ty(manifest.index());
                }
                match &td.type_kind {
                    TypeKind::TypeAbstract | TypeKind::TypeOpen => {}
                    TypeKind::TypeRecord(labels, _) => self.labels(labels),
                    TypeKind::TypeVariant(ctors, _) => {
                        for ctor in ctors {
                            self.cstr_args(&ctor.cd_args);
                            if let Some(res) = ctor.cd_res {
                                self.ty(res.index());
                            }
                        }
                    }
                }
                for inlined in &td.type_inlined_types {
                    match inlined {
                        TypeInlinedType::Record { labels, .. } => self.labels(labels),
                    }
                }
            }
            SignatureItem::SigTypext(_, ext, _) => {
                self.path(&ext.ext_type_path, Kind::Type);
                for param in &ext.ext_type_params {
                    self.ty(param.index());
                }
                self.cstr_args(&ext.ext_args);
                if let Some(ret) = ext.ext_ret_type {
                    self.ty(ret.index());
                }
            }
            SignatureItem::SigModule(_, md, _) => self.module_type(&md.md_type),
            SignatureItem::SigModtype(_, mtd) => {
                if let Some(mty) = &mtd.mtd_type {
                    self.module_type(mty);
                }
            }
            SignatureItem::SigClass | SignatureItem::SigClassType => {}
        }
    }
}

/// The references of the items of one unit's signature, computed once.
#[derive(Debug, Clone, PartialEq)]
pub struct UnitRefs {
    /// Item (kind and name) to the references of its declaration(s) and
    /// inlinable lambda.
    pub refs: ahash::AHashMap<(Kind, Name), Vec<UnitRead>>,
    /// The module aliases among the items: item to alias targets.
    pub aliases: ahash::AHashMap<(Kind, Name), Vec<UnitRead>>,
}

/// What incremental builds read of a published signature: computed from the
/// decoded signature once, so that neither item digests nor reference
/// resolution decode it again.
#[derive(Debug)]
pub struct SignatureSummary {
    /// The unit `refs` belong to.
    pub unit: Name,
    /// Kind, name and declaration digest of each top-level item, in
    /// signature order (a shadowed name appears once per declaration).
    pub item_hashes: Vec<(Kind, Name, u64)>,
    /// The references of each item's declaration ([`signature_refs`]).
    pub refs: Arc<UnitRefs>,
}

impl SignatureSummary {
    pub fn of(unit: &str, sig: &super::portable_types::PortableSignature) -> Self {
        let unit = Name::new(unit);
        let graph = super::portable_types::HashGraph::of(&sig.type_graph);
        let item_hashes = sig
            .ps_sig
            .iter()
            .filter_map(|item| {
                let (kind, name) = sig_item_kind_name(item)?;
                let mut hasher = std::collections::hash_map::DefaultHasher::new();
                super::portable_types::hash_sig_item(&mut hasher, item, &graph);
                Some((kind, name, hasher.finish()))
            })
            .collect();
        SignatureSummary {
            unit,
            item_hashes,
            refs: Arc::new(signature_refs(unit, sig)),
        }
    }
}

fn sort_refs(refs: &mut Vec<UnitRead>) {
    refs.sort_by(|a, b| (a.unit, &a.segs, a.kind).cmp(&(b.unit, &b.segs, b.kind)));
    refs.dedup();
}

/// The references of the declaration of every item of `unit`'s signature,
/// without what inlinable bodies refer to.
pub fn signature_refs(unit: Name, ps: &super::portable_types::PortableSignature) -> UnitRefs {
    let own_keys: ahash::AHashSet<(Kind, Name)> =
        ps.ps_sig.iter().filter_map(sig_item_kind_name).collect();
    let mut refs: ahash::AHashMap<(Kind, Name), Vec<UnitRead>> = ahash::AHashMap::new();
    let mut aliases: ahash::AHashMap<(Kind, Name), Vec<UnitRead>> = ahash::AHashMap::new();
    // One `seen` buffer for all items; each item's walk uses a fresh epoch.
    let mut walker = RefWalker {
        unit,
        own_keys: &own_keys,
        entries: &ps.type_graph.entries,
        seen: vec![0; ps.type_graph.entries.len()],
        epoch: 0,
        out: Vec::new(),
    };
    for item in &ps.ps_sig {
        let Some(key) = sig_item_kind_name(item) else {
            continue;
        };
        walker.epoch += 1;
        // A top-level module alias reads its target only through a path
        // into it (see `aliases`); its digest covers the target's name.
        if let SignatureItem::SigModule(_, md, _) = item
            && let ModuleType::MtyAlias(_, target) = &md.md_type
        {
            let mut targets = Vec::new();
            read_of_path(target, Kind::Module, Some(unit), &mut targets);
            aliases.entry(key).or_default().extend(targets);
        } else {
            walker.item(item);
        }
        let mut out = std::mem::take(&mut walker.out);
        sort_refs(&mut out);
        refs.entry(key).or_default().extend(out);
    }
    UnitRefs { refs, aliases }
}

/// `refs` (the [`signature_refs`] of `unit`) plus the units the inlinable
/// body of each value and module refers to.
pub fn with_lambda_units(refs: &UnitRefs, unit: Name, source: &dyn UnitSource) -> UnitRefs {
    let mut refs = refs.clone();
    for ((kind, name), item_refs) in refs.refs.iter_mut() {
        if !matches!(kind, Kind::Value | Kind::Module) {
            continue;
        }
        let lambda_units = source.lambda_units(unit, name.as_str());
        if lambda_units.is_empty() {
            continue;
        }
        item_refs.extend(lambda_units.into_iter().map(|lambda_unit| UnitRead {
            unit: lambda_unit,
            segs: Segs::new(),
            kind: Kind::Module,
        }));
        sort_refs(item_refs);
    }
    refs
}

/// What resolving reads needs to know about the units.
pub trait UnitSource {
    /// The units an inlinable lambda exported under `name` refers to.
    fn lambda_units(&self, unit: Name, name: &str) -> Vec<Name>;
    /// Units whose reads need no recording (the runtime, which does not
    /// change within a build).
    fn ignored(&self, unit: Name) -> bool;
    /// The item references of a unit ([`unit_refs`] of its signature),
    /// `None` when it is not known.
    fn refs(&self, unit: Name) -> Option<Arc<UnitRefs>>;
}

/// Resolve `initial` reads to the items read in each unit, closed over the
/// declarations of the items read and over module aliases.
pub fn resolve_reads(
    initial: impl IntoIterator<Item = UnitRead>,
    source: &dyn UnitSource,
) -> ResolvedReads {
    /// What is known of a unit reached: its references (`None` when the
    /// unit is ignored, `Some(None)` when its signature is not known) and
    /// the keys read so far.
    struct UnitState {
        refs: Option<Option<Arc<UnitRefs>>>,
        keys: ahash::AHashSet<ItemKey>,
    }
    let mut work: Vec<UnitRead> = initial.into_iter().collect();
    let mut done: ahash::AHashSet<UnitRead> = ahash::AHashSet::with_capacity(work.len());
    let mut units: ahash::AHashMap<Name, UnitState> = ahash::AHashMap::new();
    while let Some(read) = work.pop() {
        if !done.insert(read.clone()) {
            continue;
        }
        let UnitState { refs, keys } = units.entry(read.unit).or_insert_with(|| {
            let refs = (!source.ignored(read.unit)).then(|| source.refs(read.unit));
            let mut keys = ahash::AHashSet::new();
            if refs.is_some() {
                keys.insert(ItemKey::ModuleLevel);
            }
            UnitState { refs, keys }
        });
        // An ignored unit.
        let Some(refs) = refs else {
            continue;
        };
        let Some(refs) = refs else {
            keys.insert(ItemKey::Whole);
            continue;
        };
        if read.segs.is_empty() {
            if keys.insert(ItemKey::Whole) {
                for item_refs in refs.refs.values() {
                    work.extend(item_refs.iter().cloned());
                }
            }
        } else {
            let rest = &read.segs[1..];
            let kind = if rest.is_empty() {
                read.kind
            } else {
                Kind::Module
            };
            let key = (kind, read.segs[0]);
            if keys.insert(ItemKey::Item(kind, read.segs[0]))
                && let Some(item_refs) = refs.refs.get(&key)
            {
                work.extend(item_refs.iter().cloned());
            }
            // Through a module alias, the rest of the path is read in the
            // alias target.
            if let Some(targets) = refs.aliases.get(&key) {
                for target in targets {
                    let mut target = target.clone();
                    target.segs.extend(rest.iter().copied());
                    target.kind = read.kind;
                    work.push(target);
                }
            }
        }
    }
    units
        .into_iter()
        .filter_map(|(unit, state)| state.refs.is_some().then_some((unit, state.keys)))
        .collect()
}

/// The digest of the items `keys` of a unit with the given item digests;
/// a missing item counts as such.
pub fn read_digest<'a>(
    digests: &BTreeMap<String, u64>,
    keys: impl IntoIterator<Item = &'a String>,
) -> u64 {
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    for key in keys {
        key.hash(&mut hasher);
        digests.get(key).hash(&mut hasher);
    }
    hasher.finish()
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Units by name, each with the references and aliases of its items.
    #[derive(Default)]
    struct Units {
        units: ahash::AHashMap<Name, Arc<UnitRefs>>,
        ignored: ahash::AHashSet<Name>,
    }

    impl UnitSource for Units {
        fn lambda_units(&self, _unit: Name, _name: &str) -> Vec<Name> {
            Vec::new()
        }
        fn ignored(&self, unit: Name) -> bool {
            self.ignored.contains(&unit)
        }
        fn refs(&self, unit: Name) -> Option<Arc<UnitRefs>> {
            self.units.get(&unit).cloned()
        }
    }

    fn read(unit: &str, segs: &[&str], kind: Kind) -> UnitRead {
        UnitRead {
            unit: Name::new(unit),
            segs: segs.iter().map(|seg| Name::new(seg)).collect(),
            kind,
        }
    }

    fn unit(
        items: &[(Kind, &str, Vec<UnitRead>)],
        aliases: &[(&str, UnitRead)],
    ) -> Arc<UnitRefs> {
        Arc::new(UnitRefs {
            refs: items
                .iter()
                .map(|(kind, name, refs)| ((*kind, Name::new(name)), refs.clone()))
                .collect(),
            aliases: aliases
                .iter()
                .map(|(name, target)| ((Kind::Module, Name::new(name)), vec![target.clone()]))
                .collect(),
        })
    }

    /// The resolved reads as sorted `Unit.key` strings.
    fn resolved(initial: Vec<UnitRead>, source: &Units) -> Vec<String> {
        let mut out: Vec<String> = resolve_reads(initial, source)
            .into_iter()
            .flat_map(|(unit, keys)| {
                keys.into_iter()
                    .map(move |key| format!("{unit}.{}", key.to_key_string()))
            })
            .collect();
        out.sort();
        out
    }

    /// The published signature of a unit `Unit` with `type t = Dep.t` and
    /// `let make: Dep.Sub.u => t`.
    fn published_unit() -> PortablePersStruct {
        use crate::ident::Ident;
        use crate::types::decl::{RecStatus, TypeDeclaration, ValueDescription, ValueKind};
        let ctx = crate::types::TypeContext::new(Arc::new(crate::context::IdGenerator::new()));
        let dep = Path::pident(Ident::create_persistent("Dep"));
        let t_id = Ident::create_local("t");
        let dep_t = ctx.new_constr(Path::pdot(dep, "t"), vec![]);
        let dep_sub_u = ctx.new_constr(Path::pdot(Path::pdot(dep, "Sub"), "u"), vec![]);
        let own_t = ctx.new_constr(Path::pident(t_id), vec![]);
        let signature = vec![
            SignatureItem::SigType(
                t_id,
                Arc::new(TypeDeclaration {
                    type_params: vec![],
                    type_arity: 0,
                    type_kind: TypeKind::TypeAbstract,
                    type_private: crate::types::PrivateFlag::Public,
                    type_manifest: Some(dep_t),
                    type_variance: vec![],
                    type_newtype_level: None,
                    type_loc: crate::types::DeclLoc::none(),
                    type_attributes: vec![],
                    type_immediate: false,
                    type_representation: crate::types::TypeRepresentation::Boxed,
                    type_inlined_types: vec![],
                    type_path: None,
                }),
                RecStatus::TrecNot,
            ),
            SignatureItem::SigValue(
                Ident::create_local("make"),
                ValueDescription {
                    val_type: ctx.new_arrow_simple(dep_sub_u, own_t),
                    val_kind: ValueKind::ValReg,
                    val_loc: crate::types::DeclLoc::none(),
                    val_attributes: Default::default(),
                    val_path: None,
                },
            ),
        ];
        super::super::portable_types::serialize_pers_struct(
            &super::super::persistent_env::PersStruct {
                ps_name: "Unit".to_string(),
                ps_sig: Arc::new(signature),
                ps_filename: "Unit.res".to_string(),
                ps_deprecated: None,
                ps_crcs: vec![],
            },
            &ctx,
            None,
        )
    }

    #[test]
    fn a_signature_read_from_storage_summarizes_like_the_published_one() {
        let published = published_unit();
        let summary = published.summary();
        assert_eq!(summary.unit, Name::new("Unit"));
        assert_eq!(
            summary
                .item_hashes
                .iter()
                .map(|(kind, name, _)| item_key(*kind, name))
                .collect::<Vec<_>>(),
            ["t:t", "v:make"]
        );
        assert_eq!(
            summary.refs.refs[&(Kind::Type, Name::new("t"))],
            [read("Dep", &["t"], Kind::Type)]
        );
        assert_eq!(
            summary.refs.refs[&(Kind::Value, Name::new("make"))],
            [read("Dep", &["Sub", "u"], Kind::Type), read("Unit", &["t"], Kind::Type)]
        );

        // Stored and read back, the summary is not there: it is computed
        // from the decoded signature, with the same result.
        let stored: PortablePersStruct =
            crate::binser::from_slice(&crate::binser::to_vec(&published).unwrap()).unwrap();
        let restored = stored.summary();
        assert_eq!(restored.item_hashes, summary.item_hashes);
        assert_eq!(restored.refs, summary.refs);
        assert_eq!(
            item_digests(Some(&stored), None),
            item_digests(Some(&published), None)
        );
    }

    #[test]
    fn lambda_units_extend_value_and_module_references() {
        struct Lambdas;
        impl UnitSource for Lambdas {
            fn lambda_units(&self, _unit: Name, name: &str) -> Vec<Name> {
                if name == "make" {
                    vec![Name::new("Inlined"), Name::new("Dep")]
                } else {
                    Vec::new()
                }
            }
            fn ignored(&self, _unit: Name) -> bool {
                false
            }
            fn refs(&self, _unit: Name) -> Option<Arc<UnitRefs>> {
                None
            }
        }
        let published = published_unit();
        let base = &published.summary().refs;
        let extended = with_lambda_units(base, Name::new("Unit"), &Lambdas);
        let whole = |unit: &str| read(unit, &[], Kind::Module);
        let mut expected = base.refs[&(Kind::Value, Name::new("make"))].clone();
        expected.extend([whole("Inlined"), whole("Dep")]);
        sort_refs(&mut expected);
        assert_eq!(extended.refs[&(Kind::Value, Name::new("make"))], expected);
        assert_eq!(
            extended.refs[&(Kind::Type, Name::new("t"))],
            base.refs[&(Kind::Type, Name::new("t"))]
        );
        assert_eq!(extended.aliases, base.aliases);
    }

    #[test]
    fn reads_close_over_declarations_and_aliases() {
        let mut source = Units::default();
        // `A.f : B.t => C.Sub.u`, `B.t = D.t` (a cycle back through `D.t = B.t`),
        // `C.Sub` a plain submodule, `NS.Child = Child`, `Child.x : B.t`.
        source.units.insert(
            Name::new("A"),
            unit(
                &[(
                    Kind::Value,
                    "f",
                    vec![read("B", &["t"], Kind::Type), read("C", &["Sub", "u"], Kind::Type)],
                )],
                &[],
            ),
        );
        source.units.insert(
            Name::new("B"),
            unit(&[(Kind::Type, "t", vec![read("D", &["t"], Kind::Type)])], &[]),
        );
        source.units.insert(
            Name::new("D"),
            unit(&[(Kind::Type, "t", vec![read("B", &["t"], Kind::Type)])], &[]),
        );
        source.units.insert(
            Name::new("C"),
            unit(&[(Kind::Module, "Sub", vec![read("Rt", &["x"], Kind::Value)])], &[]),
        );
        source.units.insert(
            Name::new("NS"),
            unit(
                &[(Kind::Module, "Child", vec![])],
                &[("Child", read("Child", &[], Kind::Module))],
            ),
        );
        source.units.insert(
            Name::new("Child"),
            unit(
                &[
                    (Kind::Value, "x", vec![read("B", &["t"], Kind::Type)]),
                    (Kind::Value, "y", vec![read("Unknown", &["t"], Kind::Type)]),
                ],
                &[],
            ),
        );
        source.ignored.insert(Name::new("Rt"));

        // One value: its declaration's types, transitively; the runtime
        // unit is not recorded.
        assert_eq!(
            resolved(vec![read("A", &["f"], Kind::Value)], &source),
            ["A.@", "A.v:f", "B.@", "B.t:t", "C.@", "C.m:Sub", "D.@", "D.t:t"]
        );
        // Through an alias the rest of the path is read in the target, and
        // the same alias read with another rest is followed again.
        assert_eq!(
            resolved(
                vec![
                    read("NS", &["Child", "x"], Kind::Value),
                    read("NS", &["Child", "x"], Kind::Value),
                    read("NS", &["Child", "missing"], Kind::Value),
                ],
                &source
            ),
            ["B.@", "B.t:t", "Child.@", "Child.v:missing", "Child.v:x", "D.@", "D.t:t", "NS.@", "NS.m:Child"]
        );
        // The alias itself reads the whole target; a unit without a known
        // signature is read whole.
        assert_eq!(
            resolved(vec![read("NS", &["Child"], Kind::Module)], &source),
            ["B.@", "B.t:t", "Child.*", "Child.@", "D.@", "D.t:t", "NS.@", "NS.m:Child", "Unknown.*", "Unknown.@"]
        );
    }
}
