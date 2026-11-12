//! What a compiled module read of other units, from its typed tree: every
//! path rooted at a unit (values, constructors, labels, types, module types,
//! modules used as a whole), and every type the typed tree carries. Paired
//! with [`crate::cmi::item_deps::resolve_reads`], which closes these over the
//! declarations they reach.

use super::context::TypeContext;
use super::decl::{ConstructorDescription, ConstructorKind, LabelDescription};
use super::tast_iterator::{self as ti, TastIterator};
use super::type_expr::{SHARED_REF_BITS, SHARED_REF_TAG, STORE_REF_TAG, TypeDesc, TypeExprRef};
use super::typedtree::*;
use crate::cmi::item_deps::{Kind, Segs, UnitRead, read_of_path};
use crate::name::Name;
use crate::types::path::Path;

/// Visited type nodes: one bitset per reference space (local arena,
/// per-thread store, shared store), indexed by node index.
#[derive(Default)]
struct SeenTypes {
    spaces: [Vec<u64>; 3],
}

impl SeenTypes {
    /// Mark `ty`; false when it was already marked.
    #[inline]
    fn insert(&mut self, ty: TypeExprRef) -> bool {
        let raw = ty.0;
        let (space, index) = if raw & STORE_REF_TAG == 0 {
            (0, raw)
        } else if raw & SHARED_REF_TAG == 0 {
            (1, raw & !SHARED_REF_BITS)
        } else {
            (2, raw & !SHARED_REF_BITS)
        };
        let index = index as usize;
        let bits = &mut self.spaces[space];
        let word = index / 64;
        if word >= bits.len() {
            bits.resize((word + 1).max(bits.len() * 2), 0);
        }
        let mask = 1u64 << (index % 64);
        let fresh = bits[word] & mask == 0;
        bits[word] |= mask;
        fresh
    }
}

/// Reads recorded as typed nodes are constructed. Type roots are retained until
/// checking finishes: unification can change their descendants after creation.
/// Owned paths keep the interned nodes alive for address-based deduplication.
#[derive(Default)]
pub struct ReadLog {
    paths: ahash::AHashMap<(usize, Kind), Path>,
    seen: SeenTypes,
    types: Vec<TypeExprRef>,
}

impl ReadLog {
    /// Record a resolved path in its namespace.
    pub fn path(&mut self, path: &Path, kind: Kind) {
        self.paths.entry((path.node_addr(), kind)).or_insert(*path);
    }

    /// Record a type root without observing its still-mutable descendants.
    pub fn ty(&mut self, ty: TypeExprRef) {
        if self.seen.insert(ty) {
            self.types.push(ty);
        }
    }
}

struct Collector<'a> {
    ctx: &'a TypeContext,
    ta: &'a TypedArena,
    seen: SeenTypes,
    /// The walk stack of [`Collector::ty`], kept to reuse its buffer.
    stack: Vec<TypeExprRef>,
    /// The paths already read, by interned node and kind: a path's reads
    /// depend only on those, and many type nodes share a path.
    paths: ahash::AHashSet<(usize, Kind)>,
    out: Vec<UnitRead>,
}

impl Collector<'_> {
    fn path(&mut self, path: &Path, kind: Kind) {
        if self.paths.insert((path.node_addr(), kind)) {
            read_of_path(path, kind, None, &mut self.out);
        }
    }

    fn ty(&mut self, root: TypeExprRef) {
        let ctx = self.ctx;
        let mut stack = std::mem::take(&mut self.stack);
        stack.push(root);
        while let Some(ty) = stack.pop() {
            if !self.seen.insert(ty) {
                continue;
            }
            // The children are those `btype::iter_type_expr` visits; only a
            // variant goes through it, for its row walk.
            let desc = ctx.borrow_desc(ty);
            match &*desc {
                TypeDesc::Tconstr { path, args, .. } => {
                    self.path(path, Kind::Type);
                    stack.extend(ctx.type_list(args).iter());
                }
                TypeDesc::Tpackage { path, args, .. } => {
                    self.path(path, Kind::Modtype);
                    stack.extend(ctx.type_list(args).iter());
                }
                TypeDesc::Tarrow { args, ret } => {
                    stack.extend(ctx.type_args(args).iter().map(|arg| arg.typ));
                    stack.push(*ret);
                }
                TypeDesc::Ttuple(types) => stack.extend(ctx.type_list(types).iter()),
                TypeDesc::Tobject { fields } => stack.push(*fields),
                TypeDesc::Tfield { typ, rest, .. } => {
                    stack.push(*typ);
                    stack.push(*rest);
                }
                TypeDesc::Tlink(t) | TypeDesc::Tsubst(t) => stack.push(*t),
                TypeDesc::Tpoly { body, vars } => {
                    stack.push(*body);
                    stack.extend(ctx.type_list(vars).iter());
                }
                TypeDesc::Tvar(..) | TypeDesc::Tunivar(..) | TypeDesc::Tnil => {}
                TypeDesc::Tvariant(row) => {
                    let row = &ctx.row_desc(row);
                    if let Some((path, _)) = &row.row_name {
                        self.path(path, Kind::Type);
                    }
                    super::btype::iter_type_expr(ctx, ty, |child| stack.push(child));
                }
            }
        }
        self.stack = stack;
    }

    fn constructor(&mut self, cd: &ConstructorDescription) {
        if let ConstructorKind::Extension(path) = &cd.cstr_kind {
            self.path(path, Kind::Extension);
        }
        self.ty(cd.cstr_res);
        for arg in &cd.cstr_args {
            self.ty(*arg);
        }
    }

    fn label(&mut self, ld: &LabelDescription) {
        self.ty(ld.lbl_res);
        self.ty(ld.lbl_arg);
    }
}

impl ReadLog {
    fn resolve(&self, ctx: &TypeContext, ta: &TypedArena, opens: &[String]) -> Vec<UnitRead> {
        let mut reader = Collector {
            ctx,
            ta,
            seen: SeenTypes::default(),
            stack: Vec::new(),
            paths: ahash::AHashSet::new(),
            out: opened(opens).collect(),
        };
        for ((_, kind), path) in &self.paths {
            reader.path(path, *kind);
        }
        for ty in &self.types {
            reader.ty(*ty);
        }
        reader.out
    }

    /// Compare raw reads as sets, before alias resolution or dependency closure.
    /// Debug builds always check; optimized corpus runs opt in with
    /// `RESCRIPT_CHECK_UNIT_READS=1`.
    pub fn check(
        &self,
        ctx: &TypeContext,
        ta: &TypedArena,
        opens: &[String],
        walked: &[UnitRead],
        unit: &str,
    ) {
        if !cfg!(debug_assertions) && std::env::var_os("RESCRIPT_CHECK_UNIT_READS").is_none() {
            return;
        }
        let logged: ahash::AHashSet<_> = self.resolve(ctx, ta, opens).into_iter().collect();
        let walked: ahash::AHashSet<_> = walked.iter().cloned().collect();
        let extra: Vec<_> = logged.difference(&walked).collect();
        let missing: Vec<_> = walked.difference(&logged).collect();
        assert!(
            extra.is_empty() && missing.is_empty(),
            "unit read mismatch in {unit}: logged-only {extra:?}; walked-only {missing:?}"
        );
        if std::env::var_os("RESCRIPT_CHECK_UNIT_READS").is_some() {
            eprintln!(
                "unit-read-check: {unit}: {} reads, zero differences",
                walked.len()
            );
        }
    }
}

// These callbacks inspect only the node just constructed, never its children.
pub(crate) trait ReadNode {
    fn log_reads(&self, log: &mut ReadLog, ta: &TypedArena);
}

#[inline]
pub(crate) fn record<T: ReadNode>(node: T, log: &mut Option<ReadLog>, ta: &TypedArena) -> T {
    if let Some(log) = log {
        node.log_reads(log, ta);
    }
    node
}

impl ReadNode for Expression {
    fn log_reads(&self, log: &mut ReadLog, ta: &TypedArena) {
        let e = self;
        for (extra, _, _) in ta.exp_extra(e).iter() {
            if let ExpExtra::Texp_open(_, path, _, _) = extra {
                log.path(path, Kind::Module);
            }
        }
        match &e.exp_desc {
            ExpressionDesc::Texp_ident(path, _, _) => log.path(path, Kind::Value),
            ExpressionDesc::Texp_construct(_, cd, _) => log.constructor(cd),
            ExpressionDesc::Texp_field(_, _, ld) | ExpressionDesc::Texp_setfield(_, _, ld, _) => {
                log.label(ld)
            }
            ExpressionDesc::Texp_record { fields, .. } => {
                for (ld, _, _) in ta.record_fields(*fields) {
                    log.label(ld);
                }
            }
            _ => {}
        }
        log.ty(e.exp_type);
    }
}

impl ReadNode for Pattern {
    fn log_reads(&self, log: &mut ReadLog, ta: &TypedArena) {
        let p = self;
        for (extra, _, _) in ta.pat_extra(p).iter() {
            if let PatExtra::Tpat_type(path, _) = extra {
                log.path(path, Kind::Type);
            }
        }
        match &p.pat_desc {
            PatternDesc::Tpat_construct(_, cd, _) => log.constructor(cd),
            PatternDesc::Tpat_record(fields, _, rest) => {
                for (_, ld, _, _) in fields {
                    log.label(ld);
                }
                if let Some(rest) = rest {
                    log.ty(rest.rest_type);
                }
            }
            _ => {}
        }
        log.ty(p.pat_type);
    }
}

impl ReadNode for TypedCoreType {
    fn log_reads(&self, log: &mut ReadLog, _ta: &TypedArena) {
        let t = self;
        match &t.ctyp_desc {
            TypedCoreTypeDesc::Ttyp_constr(path, _, _) => log.path(path, Kind::Type),
            TypedCoreTypeDesc::Ttyp_package(pack) => log.path(&pack.pack_path, Kind::Modtype),
            _ => {}
        }
        log.ty(t.ctyp_type);
    }
}

impl ReadNode for ModuleExpr {
    fn log_reads(&self, log: &mut ReadLog, _ta: &TypedArena) {
        let m = self;
        if let ModuleExprDesc::Tmod_ident(path, _) = &m.mod_desc {
            log.path(path, Kind::Module);
        }
    }
}

impl ReadNode for ModuleType {
    fn log_reads(&self, log: &mut ReadLog, _ta: &TypedArena) {
        let m = self;
        match &m.mty_desc {
            ModuleTypeDesc::Tmty_ident(path, _) => log.path(path, Kind::Modtype),
            ModuleTypeDesc::Tmty_alias(path, _) => log.path(path, Kind::Module),
            ModuleTypeDesc::Tmty_with(_, constraints) => {
                for (_, _, constraint) in constraints {
                    if let WithConstraint::Twith_module(path, _)
                    | WithConstraint::Twith_modsubst(path, _) = constraint
                    {
                        log.path(path, Kind::Module);
                    }
                }
            }
            _ => {}
        }
    }
}

impl ReadNode for StructureItem {
    fn log_reads(&self, log: &mut ReadLog, _ta: &TypedArena) {
        let item = self;
        match &item.str_desc {
            StructureItemDesc::Tstr_open(od) => log.path(&od.open_path, Kind::Module),
            StructureItemDesc::Tstr_typext(te) => log.path(&te.tyext_path, Kind::Type),
            _ => {}
        }
    }
}

impl ReadNode for TypedSignatureItem {
    fn log_reads(&self, log: &mut ReadLog, _ta: &TypedArena) {
        let item = self;
        match &item.sig_desc {
            TypedSignatureItemDesc::Tsig_open(od) => log.path(&od.open_path, Kind::Module),
            TypedSignatureItemDesc::Tsig_typext(te) => log.path(&te.tyext_path, Kind::Type),
            _ => {}
        }
    }
}

impl ReadNode for ExtensionConstructor {
    fn log_reads(&self, log: &mut ReadLog, _ta: &TypedArena) {
        let ext = self;
        if let ExtensionConstructorKind::Text_rebind(path, _) = &ext.ext_kind {
            log.path(path, Kind::Extension);
        }
    }
}

impl ReadLog {
    fn constructor(&mut self, cd: &ConstructorDescription) {
        if let ConstructorKind::Extension(path) = &cd.cstr_kind {
            self.path(path, Kind::Extension);
        }
        self.ty(cd.cstr_res);
        for arg in &cd.cstr_args {
            self.ty(*arg);
        }
    }

    fn label(&mut self, ld: &LabelDescription) {
        self.ty(ld.lbl_res);
        self.ty(ld.lbl_arg);
    }
}

impl<'a> TastIterator<'a> for Collector<'a> {
    fn arena(&self) -> &'a TypedArena {
        self.ta
    }

    fn expr(&mut self, e: &Expression) {
        for (extra, _, _) in self.ta.exp_extra(e).iter() {
            if let ExpExtra::Texp_open(_, path, _, _) = extra {
                self.path(path, Kind::Module);
            }
        }
        match &e.exp_desc {
            ExpressionDesc::Texp_ident(path, _, _) => self.path(path, Kind::Value),
            ExpressionDesc::Texp_construct(_, cd, _) => self.constructor(cd),
            ExpressionDesc::Texp_field(_, _, ld) | ExpressionDesc::Texp_setfield(_, _, ld, _) => {
                self.label(ld)
            }
            ExpressionDesc::Texp_record { fields, .. } => {
                for (ld, _, _) in self.ta.record_fields(*fields) {
                    self.label(ld);
                }
            }
            _ => {}
        }
        self.ty(e.exp_type);
        ti::walk_expr(self, e);
    }

    fn pat(&mut self, p: &Pattern) {
        for (extra, _, _) in self.ta.pat_extra(p).iter() {
            if let PatExtra::Tpat_type(path, _) = extra {
                self.path(path, Kind::Type);
            }
        }
        match &p.pat_desc {
            PatternDesc::Tpat_construct(_, cd, _) => self.constructor(cd),
            PatternDesc::Tpat_record(fields, _, rest) => {
                for (_, ld, _, _) in fields {
                    self.label(ld);
                }
                if let Some(rest) = rest {
                    self.ty(rest.rest_type);
                }
            }
            _ => {}
        }
        self.ty(p.pat_type);
        ti::walk_pat(self, p);
    }

    fn typ(&mut self, t: &TypedCoreType) {
        match &t.ctyp_desc {
            TypedCoreTypeDesc::Ttyp_constr(path, _, _) => self.path(path, Kind::Type),
            TypedCoreTypeDesc::Ttyp_package(pack) => self.path(&pack.pack_path, Kind::Modtype),
            _ => {}
        }
        self.ty(t.ctyp_type);
        ti::walk_typ(self, t);
    }

    fn module_expr(&mut self, m: &ModuleExpr) {
        if let ModuleExprDesc::Tmod_ident(path, _) = &m.mod_desc {
            self.path(path, Kind::Module);
        }
        ti::walk_module_expr(self, m);
    }

    fn module_type(&mut self, m: &ModuleType) {
        match &m.mty_desc {
            ModuleTypeDesc::Tmty_ident(path, _) => self.path(path, Kind::Modtype),
            ModuleTypeDesc::Tmty_alias(path, _) => self.path(path, Kind::Module),
            ModuleTypeDesc::Tmty_with(_, constraints) => {
                for (_, _, constraint) in constraints {
                    if let WithConstraint::Twith_module(path, _)
                    | WithConstraint::Twith_modsubst(path, _) = constraint
                    {
                        self.path(path, Kind::Module);
                    }
                }
            }
            _ => {}
        }
        ti::walk_module_type(self, m);
    }

    fn structure_item(&mut self, item: &StructureItem) {
        match &item.str_desc {
            StructureItemDesc::Tstr_open(od) => self.path(&od.open_path, Kind::Module),
            StructureItemDesc::Tstr_typext(te) => self.path(&te.tyext_path, Kind::Type),
            _ => {}
        }
        ti::walk_structure_item(self, item);
    }

    fn signature_item(&mut self, item: &TypedSignatureItem) {
        match &item.sig_desc {
            TypedSignatureItemDesc::Tsig_open(od) => self.path(&od.open_path, Kind::Module),
            TypedSignatureItemDesc::Tsig_typext(te) => self.path(&te.tyext_path, Kind::Type),
            _ => {}
        }
        ti::walk_signature_item(self, item);
    }

    fn extension_constructor(&mut self, ext: &ExtensionConstructor) {
        if let ExtensionConstructorKind::Text_rebind(path, _) = &ext.ext_kind {
            self.path(path, Kind::Extension);
        }
        ti::walk_extension_constructor(self, ext);
    }
}

fn opened(opens: &[String]) -> impl Iterator<Item = UnitRead> + '_ {
    opens.iter().map(|unit| UnitRead {
        unit: Name::new(unit),
        segs: Segs::new(),
        kind: Kind::Module,
    })
}

/// The reads of an implementation; `opens` are the units opened by the
/// command line (read as whole modules).
pub fn structure_reads(
    ctx: &TypeContext,
    ta: &TypedArena,
    structure: &Structure,
    opens: &[String],
) -> Vec<UnitRead> {
    let mut collector = Collector {
        ctx,
        ta,
        seen: SeenTypes::default(),
        stack: Vec::new(),
        paths: ahash::AHashSet::new(),
        out: opened(opens).collect(),
    };
    collector.structure(structure);
    collector.out
}

/// The reads of an interface.
pub fn signature_reads(
    ctx: &TypeContext,
    ta: &TypedArena,
    signature: &TypedSignature,
    opens: &[String],
) -> Vec<UnitRead> {
    let mut collector = Collector {
        ctx,
        ta,
        seen: SeenTypes::default(),
        stack: Vec::new(),
        paths: ahash::AHashSet::new(),
        out: opened(opens).collect(),
    };
    collector.signature(signature);
    collector.out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn read_log_observes_unification_after_recording_a_root() {
        let ctx = TypeContext::new(std::sync::Arc::new(crate::IdGenerator::new()));
        let ta = TypedArena::new();
        let root = ctx.new_var(None);
        let mut log = ReadLog::default();
        log.ty(root);
        let path = Path::pdot(
            Path::pident(crate::ident::Ident::create_persistent("Dependency")),
            "t",
        );
        let target = ctx.new_constr(path, vec![]);
        ctx.set_desc(root, TypeDesc::Tlink(target));
        log.path(&path, Kind::Value);
        log.path(&path, Kind::Value);
        assert_eq!(log.paths.len(), 1);
        let reads: ahash::AHashSet<_> = log.resolve(&ctx, &ta, &[]).into_iter().collect();
        let expected: ahash::AHashSet<_> = [Kind::Type, Kind::Value]
            .into_iter()
            .map(|kind| UnitRead {
                unit: Name::new("Dependency"),
                segs: [Name::new("t")].into_iter().collect(),
                kind,
            })
            .collect();
        assert_eq!(reads, expected);
    }

    #[test]
    fn read_log_deduplicates_each_type_reference_space() {
        let mut log = ReadLog::default();
        for ty in [TypeExprRef(7), TypeExprRef(STORE_REF_TAG | 7),
                   TypeExprRef(STORE_REF_TAG | SHARED_REF_TAG | 7)] {
            log.ty(ty);
            log.ty(ty);
        }
        assert_eq!(log.types.len(), 3);
    }
}
