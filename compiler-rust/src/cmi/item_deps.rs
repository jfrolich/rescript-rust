//! Per-item interface digests and read sets, for incremental builds.
//!
//! A compiled unit publishes a digest for each of its top-level items (its
//! declaration plus the JS metadata other modules' code generation reads for
//! it: constants, arities and inlinable lambdas; the flat `make` exports
//! follow from the declaration) and one
//! module-level part (`@`: purity, package, file). A dependent records which
//! items of each unit it read: the paths its typed tree mentions, closed over
//! the declarations of what it read (reading `N.f : M.t => unit` also reads
//! `M.t`, and `M.t`'s manifest and constructors in turn) and over module
//! aliases (`NS.Child.x` reads `Child`'s `x`). A use of a whole module
//! (`open`, `include`, a module alias or functor argument) reads every item
//! (`*`). The dependent then has to be recompiled only when the digest of an
//! item it read changed.

use std::collections::{BTreeMap, BTreeSet};
use std::hash::{Hash, Hasher};
use std::sync::Arc;

use super::persistent_env::InMemoryModuleInfo;
use super::portable_types::{
    PortablePersStruct, PortableRowField, PortableTypeDesc, PortableTypeEntry,
};
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

/// A reference to something in a unit: `unit.segs`, where the last segment
/// is of `kind`. Empty `segs` is the unit itself, as a whole module.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct UnitRead {
    pub unit: String,
    pub segs: Vec<String>,
    pub kind: Kind,
}

/// The read a path denotes. Paths rooted at a persistent unit read that unit;
/// with `own_unit`, paths rooted at a local identifier are read in it (used
/// for the declarations of a unit's own signature). Functor applications
/// read the functor and the argument as whole modules.
pub fn read_of_path(path: &Path, kind: Kind, own_unit: Option<&str>, out: &mut Vec<UnitRead>) {
    // Without `own_unit` only paths with a persistent root read anything.
    if own_unit.is_none() && !has_persistent_head(path) {
        return;
    }
    if let Path::Papply(f, x) = path {
        read_of_path(f, Kind::Module, own_unit, out);
        read_of_path(x, Kind::Module, own_unit, out);
        return;
    }
    let Ok((root, segs)) = path.flatten() else {
        // A dotted path under a functor application.
        for head in path.heads() {
            read_of_path(&Path::Pident(*head), Kind::Module, own_unit, out);
        }
        return;
    };
    let segs: Vec<String> = segs.into_iter().map(str::to_string).collect();
    if root.is_persistent() {
        out.push(UnitRead {
            unit: root.name().to_string(),
            segs,
            kind,
        });
    } else if let Some(unit) = own_unit {
        let mut full = vec![root.name().to_string()];
        full.extend(segs);
        out.push(UnitRead {
            unit: unit.to_string(),
            segs: full,
            kind,
        });
    }
}

fn has_persistent_head(path: &Path) -> bool {
    match path {
        Path::Pident(id) => id.is_persistent(),
        Path::Pdot(parent, _, _) => has_persistent_head(parent),
        Path::Papply(f, x) => has_persistent_head(f) || has_persistent_head(x),
    }
}

/// The kind and name of a top-level item, `None` for class items.
fn sig_item_kind_name(item: &SignatureItem) -> Option<(Kind, &'static str)> {
    Some(match item {
        SignatureItem::SigValue(id, _) => (Kind::Value, id.name()),
        SignatureItem::SigType(id, _, _) => (Kind::Type, id.name()),
        SignatureItem::SigTypext(id, _, _) => (Kind::Extension, id.name()),
        SignatureItem::SigModule(id, _, _) => (Kind::Module, id.name()),
        SignatureItem::SigModtype(id, _) => (Kind::Modtype, id.name()),
        SignatureItem::SigClass | SignatureItem::SigClassType => return None,
    })
}

fn sig_item_key(item: &SignatureItem) -> Option<String> {
    sig_item_kind_name(item).map(|(kind, name)| item_key(kind, name))
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
        let ps = ps.signature();
        let graph = super::portable_types::HashGraph::of(&ps.type_graph);
        for item in &ps.ps_sig {
            let Some(key) = sig_item_key(item) else {
                continue;
            };
            let mut hasher = std::collections::hash_map::DefaultHasher::new();
            if let Some(previous) = digests.get(&key) {
                previous.hash(&mut hasher);
            }
            super::portable_types::hash_sig_item(&mut hasher, item, &graph);
            // The JS metadata dependents' code generation reads for the item,
            // without locations and identifier stamps (see `digest_ser`).
            if let (Some(info), Some(name)) =
                (info, key.strip_prefix("v:").or(key.strip_prefix("m:")))
            {
                let mut canonical = super::digest_ser::Canonical::new(&mut hasher);
                canonical.hash(&info.cmj_export_constants.get(name));
                canonical.hash(&info.cmj_export_arities.get(name));
                canonical.hash(&info.cmj_export_lambdas.get(name));
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
    unit: &'a str,
    /// The unit's top-level item keys: a local identifier that names none of
    /// them is predefined (`int`, `option`) or bound inside the item being
    /// walked (a functor parameter, a sibling in a submodule).
    own_keys: &'a ahash::AHashSet<(Kind, &'static str)>,
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
                    own_keys.contains(&(first_kind, first.as_str()))
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
pub struct UnitRefs {
    /// Item key to the references of its declaration(s) and inlinable
    /// lambda.
    pub refs: ahash::AHashMap<String, Vec<UnitRead>>,
    /// The module aliases among the items: key to alias targets.
    pub aliases: ahash::AHashMap<String, Vec<UnitRead>>,
}

/// The references of every item of `ps`.
pub fn unit_refs(unit: &str, ps: &PortablePersStruct, source: &dyn UnitSource) -> UnitRefs {
    let ps = ps.signature();
    let own_keys: ahash::AHashSet<(Kind, &'static str)> =
        ps.ps_sig.iter().filter_map(sig_item_kind_name).collect();
    let mut refs: ahash::AHashMap<String, Vec<UnitRead>> = ahash::AHashMap::new();
    let mut aliases: ahash::AHashMap<String, Vec<UnitRead>> = ahash::AHashMap::new();
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
        let Some(key) = sig_item_key(item) else {
            continue;
        };
        walker.epoch += 1;
        // A top-level module alias reads its target only through a path
        // into it (see `aliases`); its digest covers the target's name.
        let is_alias = matches!(
            item,
            SignatureItem::SigModule(_, md, _) if matches!(md.md_type, ModuleType::MtyAlias(..))
        );
        if !is_alias {
            walker.item(item);
        }
        let mut out = std::mem::take(&mut walker.out);
        match item {
            SignatureItem::SigValue(id, _) | SignatureItem::SigModule(id, _, _) => {
                for lambda_unit in source.lambda_units(unit, id.name()) {
                    out.push(UnitRead {
                        unit: lambda_unit,
                        segs: Vec::new(),
                        kind: Kind::Module,
                    });
                }
            }
            _ => {}
        }
        if let SignatureItem::SigModule(_, md, _) = item
            && let ModuleType::MtyAlias(_, target) = &md.md_type
        {
            let mut targets = Vec::new();
            read_of_path(target, Kind::Module, Some(unit), &mut targets);
            aliases.entry(key.clone()).or_default().extend(targets);
        }
        out.sort_by(|a, b| (&a.unit, &a.segs, a.kind).cmp(&(&b.unit, &b.segs, b.kind)));
        out.dedup();
        refs.entry(key).or_default().extend(out);
    }
    UnitRefs { refs, aliases }
}

/// What resolving reads needs to know about the units.
pub trait UnitSource {
    /// The unit's published signature, `None` when it is not known.
    fn portable(&self, unit: &str) -> Option<Arc<PortablePersStruct>>;
    /// The units an inlinable lambda exported under `name` refers to.
    fn lambda_units(&self, unit: &str, name: &str) -> Vec<String>;
    /// Units whose reads need no recording (the runtime, which does not
    /// change within a build).
    fn ignored(&self, unit: &str) -> bool;
    /// The item references of a unit ([`unit_refs`] of its signature),
    /// `None` when it is not known.
    fn refs(&self, unit: &str) -> Option<Arc<UnitRefs>>;
}

/// Resolve `initial` reads to the item keys read in each unit, closed over
/// the declarations of the items read and over module aliases.
pub fn resolve_reads(
    initial: impl IntoIterator<Item = UnitRead>,
    source: &dyn UnitSource,
) -> BTreeMap<String, BTreeSet<String>> {
    let mut result: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    let mut work: Vec<UnitRead> = initial.into_iter().collect();
    let mut done: ahash::AHashSet<UnitRead> = ahash::AHashSet::new();
    // Per unit: `None` when ignored, else its references if known.
    let mut units: ahash::AHashMap<String, Option<Option<Arc<UnitRefs>>>> = ahash::AHashMap::new();
    while let Some(read) = work.pop() {
        if done.contains(&read) {
            continue;
        }
        let unit_refs = match units.get(&read.unit) {
            Some(known) => known.clone(),
            None => {
                let known = (!source.ignored(&read.unit)).then(|| source.refs(&read.unit));
                units.insert(read.unit.clone(), known.clone());
                known
            }
        };
        // An ignored unit.
        let Some(unit_refs) = unit_refs else {
            done.insert(read);
            continue;
        };
        let keys = result.entry(read.unit.clone()).or_default();
        keys.insert(MODULE_LEVEL.to_string());
        let Some(refs) = unit_refs else {
            keys.insert(WHOLE.to_string());
            done.insert(read);
            continue;
        };
        if read.segs.is_empty() {
            if keys.insert(WHOLE.to_string()) {
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
            let key = item_key(kind, &read.segs[0]);
            if keys.insert(key.clone())
                && let Some(item_refs) = refs.refs.get(&key)
            {
                work.extend(item_refs.iter().cloned());
            }
            // Through a module alias, the rest of the path is read in the
            // alias target.
            if let Some(targets) = refs.aliases.get(&key) {
                for target in targets {
                    let mut target = target.clone();
                    target.segs.extend(rest.iter().cloned());
                    target.kind = read.kind;
                    work.push(target);
                }
            }
        }
        done.insert(read);
    }
    result
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
