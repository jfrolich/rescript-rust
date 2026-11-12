//! What a compiled module read of other units, recorded by the checker: every
//! path rooted at a unit (values, constructors, labels, types, module types,
//! modules used as a whole), and every type the typed tree carries. Paired
//! with [`crate::cmi::item_deps::resolve_reads`], which closes these over the
//! declarations they reach.

use super::context::TypeContext;
use super::decl::{ConstructorDescription, ConstructorKind, LabelDescription};
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
    /// Mark `ty`; false when it was already marked. One indexed bit probe;
    /// growing the bitset costs O(new words), amortized over its largest index.
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
/// Paths are immutable, process-interned pointers, not dense arena indices.
#[derive(Default)]
pub struct ReadLog {
    paths: ahash::AHashSet<(usize, Kind)>,
    out: Vec<UnitRead>,
    seen: SeenTypes,
    types: Vec<TypeExprRef>,
    #[cfg(test)]
    root_events: usize,
    #[cfg(test)]
    path_events: usize,
    #[cfg(test)]
    type_steps: usize,
    #[cfg(test)]
    expanded_nodes: usize,
}

impl ReadLog {
    /// Record a path: expected O(1) for a duplicate; for a fresh path, the
    /// cost of `read_of_path` (its path edges plus emitted segments).
    #[inline]
    pub fn path(&mut self, path: &Path, kind: Kind) {
        #[cfg(test)]
        {
            self.path_events += 1;
        }
        if self.paths.insert((path.node_addr(), kind)) {
            read_of_path(path, kind, None, &mut self.out);
        }
    }

    /// Record a root without observing its still-mutable descendants.
    /// One bitset probe, and one amortized O(1) pool push for a new root.
    #[inline]
    pub fn ty(&mut self, ty: TypeExprRef) {
        #[cfg(test)]
        {
            self.root_events += 1;
        }
        if self.seen.insert(ty) {
            self.types.push(ty);
        }
    }
}

struct TypeReader<'a> {
    ctx: &'a TypeContext,
    seen: SeenTypes,
    /// The walk stack of [`TypeReader::ty`], kept to reuse its buffer.
    stack: Vec<TypeExprRef>,
    /// The paths already read, by interned node and kind: a path's reads
    /// depend only on those, and many type nodes share a path.
    paths: ahash::AHashSet<(usize, Kind)>,
    out: Vec<UnitRead>,
    #[cfg(test)]
    steps: usize,
    #[cfg(test)]
    expanded: usize,
}

impl TypeReader<'_> {
    /// Expected O(1) deduplication, plus `read_of_path` for a fresh path.
    #[inline]
    fn path(&mut self, path: &Path, kind: Kind) {
        if self.paths.insert((path.node_addr(), kind)) {
            read_of_path(path, kind, None, &mut self.out);
        }
    }

    /// Traverse the recorded roots in O(V + E) type steps: each reachable
    /// node is expanded once and each outgoing edge is pushed once.
    fn types(&mut self) {
        let ctx = self.ctx;
        let mut stack = std::mem::take(&mut self.stack);
        while let Some(ty) = stack.pop() {
            #[cfg(test)]
            {
                self.steps += 1;
            }
            if !self.seen.insert(ty) {
                continue;
            }
            #[cfg(test)]
            {
                self.expanded += 1;
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
}

impl ReadLog {
    /// Resolve a unit in O(R + V + E + P): roots, reachable type nodes,
    /// type edges and path decoding. Reuses the recording buffers; no tree walk.
    fn resolve(&mut self, ctx: &TypeContext, opens: &[String]) -> Vec<UnitRead> {
        for space in &mut self.seen.spaces {
            space.fill(0);
        }
        let mut reader = TypeReader {
            ctx,
            seen: std::mem::take(&mut self.seen),
            stack: std::mem::take(&mut self.types),
            paths: std::mem::take(&mut self.paths),
            out: std::mem::take(&mut self.out),
            #[cfg(test)]
            steps: 0,
            #[cfg(test)]
            expanded: 0,
        };
        reader.out.extend(opened(opens));
        reader.types();
        #[cfg(test)]
        {
            self.type_steps = reader.steps;
            self.expanded_nodes = reader.expanded;
        }
        reader.out
    }
}

// These callbacks inspect only the node just constructed, never its children.
pub(crate) trait ReadNode {
    /// O(1) plus this node's immediate extras, fields or constructor arguments;
    /// never visits a child node or allocates a per-node traversal buffer.
    fn log_reads(&self, log: &mut ReadLog, ta: &TypedArena);
}

/// One option test when disabled; otherwise the node-specific `log_reads`
/// cost. The node is moved through its construction site, not cloned or walked.
#[inline]
pub(crate) fn record<T: ReadNode>(node: T, log: &mut Option<ReadLog>, ta: &TypedArena) -> T {
    if let Some(log) = log {
        node.log_reads(log, ta);
    }
    node
}

impl ReadNode for Expression {
    /// O(extras + record fields + constructor arity), no child traversal.
    #[inline]
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
    /// O(extras + record fields + constructor arity), no child traversal.
    #[inline]
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
    /// O(1) root recording plus fresh-path decoding; no child traversal.
    #[inline]
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
    /// O(1) except decoding a fresh module path; no child traversal.
    #[inline]
    fn log_reads(&self, log: &mut ReadLog, _ta: &TypedArena) {
        let m = self;
        if let ModuleExprDesc::Tmod_ident(path, _) = &m.mod_desc {
            log.path(path, Kind::Module);
        }
    }
}

impl ReadNode for ModuleType {
    /// O(with constraints) plus fresh-path decoding; no child traversal.
    #[inline]
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
    /// O(1) except decoding a fresh open/extension path.
    #[inline]
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
    /// O(1) except decoding a fresh open/extension path.
    #[inline]
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
    /// O(1) except decoding a fresh rebound extension path.
    #[inline]
    fn log_reads(&self, log: &mut ReadLog, _ta: &TypedArena) {
        let ext = self;
        if let ExtensionConstructorKind::Text_rebind(path, _) = &ext.ext_kind {
            log.path(path, Kind::Extension);
        }
    }
}

impl ReadLog {
    /// O(arity) root insertions plus extension-path decoding, no type walk.
    #[inline]
    fn constructor(&mut self, cd: &ConstructorDescription) {
        if let ConstructorKind::Extension(path) = &cd.cstr_kind {
            self.path(path, Kind::Extension);
        }
        self.ty(cd.cstr_res);
        for arg in &cd.cstr_args {
            self.ty(*arg);
        }
    }

    /// Two O(1) amortized root insertions, no type walk.
    #[inline]
    fn label(&mut self, ld: &LabelDescription) {
        self.ty(ld.lbl_res);
        self.ty(ld.lbl_arg);
    }
}

/// O(1) to create the iterator; O(total name bytes) to consume it.
fn opened(opens: &[String]) -> impl Iterator<Item = UnitRead> + '_ {
    opens.iter().map(|unit| UnitRead {
        unit: Name::new(unit),
        segs: Segs::new(),
        kind: Kind::Module,
    })
}

/// The reads of an implementation; `opens` are the units opened by the
/// command line (read as whole modules). No typed tree is needed.
/// O(roots + reachable type nodes and edges + decoded path segments).
pub fn structure_reads(ctx: &TypeContext, log: &mut ReadLog, opens: &[String]) -> Vec<UnitRead> {
    log.resolve(ctx, opens)
}

/// The reads of an interface. No typed tree is needed.
/// O(roots + reachable type nodes and edges + decoded path segments).
pub fn signature_reads(ctx: &TypeContext, log: &mut ReadLog, opens: &[String]) -> Vec<UnitRead> {
    log.resolve(ctx, opens)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ten_thousand_immediate_fields_extras_and_constraints_are_linear() {
        use crate::parse_arena::{LidentIdx, LocIdx, Located};
        use crate::parser::ast::ClosedFlag;
        use crate::types::DeclLoc;
        use crate::types::asttypes::{MutableFlag, PrivateFlag};
        use crate::types::decl::{LabelArrayRef, RecordRepresentation};
        use std::sync::Arc;

        const N: usize = 10_000;
        let ty = TypeExprRef(0);
        let path = Path::pident(crate::ident::Ident::create_persistent("Dependency"));
        let loc = Located {
            txt: LidentIdx(0),
            loc: LocIdx(0),
        };
        let label = Arc::new(LabelDescription {
            lbl_name: Name::new("field"),
            lbl_runtime_name: Name::new("field"),
            lbl_res: ty,
            lbl_arg: ty,
            lbl_mut: MutableFlag::Immutable,
            lbl_optional: false,
            lbl_pos: 0,
            lbl_all: LabelArrayRef::NONE,
            lbl_repres: RecordRepresentation::RecordRegular,
            lbl_private: PrivateFlag::Public,
            lbl_loc: DeclLoc::none(),
        });
        let mut ta = TypedArena::new();
        let child = ta.push_expr(Expression::new(
            ExpressionDesc::Texp_break,
            LocIdx(0),
            ty,
            EnvRef(0),
        ));
        let fields = vec![(label.clone(), loc, child); N];
        let mut expr = Expression::new(
            ExpressionDesc::Texp_record {
                fields: ta.push_record_fields(fields),
                empty_representation: None,
                extended_expression: None,
            },
            LocIdx(0),
            ty,
            EnvRef(0),
        );
        for _ in 0..N {
            ta.push_exp_extra(
                &mut expr,
                (
                    ExpExtra::Texp_open(
                        crate::parser::ast::OverrideFlag::Fresh,
                        path,
                        loc,
                        EnvRef(0),
                    ),
                    LocIdx(0),
                    Default::default(),
                ),
            );
        }
        let mut log = ReadLog::default();
        expr.log_reads(&mut log, &ta);
        assert_eq!(log.root_events, 2 * N + 1);
        assert_eq!(log.path_events, N);

        let child = ta.push_pattern(Pattern::new(
            PatternDesc::Tpat_any,
            LocIdx(0),
            ty,
            EnvRef(0),
        ));
        let mut pat = Pattern::new(
            PatternDesc::Tpat_record(
                vec![(loc, label, child, false); N],
                ClosedFlag::Closed,
                None,
            ),
            LocIdx(0),
            ty,
            EnvRef(0),
        );
        ta.set_pat_extra(
            &mut pat,
            vec![
                (
                    PatExtra::Tpat_type(path, loc),
                    LocIdx(0),
                    Default::default()
                );
                N
            ],
        );
        let mut log = ReadLog::default();
        pat.log_reads(&mut log, &ta);
        assert_eq!(log.root_events, 2 * N + 1);
        assert_eq!(log.path_events, N);

        let child = ta.push_module_type(ModuleType {
            mty_desc: ModuleTypeDesc::Tmty_alias(path, loc),
            mty_type: super::super::decl::ModuleType::MtySignature(Arc::new(vec![])),
            mty_env: EnvRef(0),
            mty_loc: LocIdx(0),
            mty_attributes: Default::default(),
        });
        let module = ModuleType {
            mty_desc: ModuleTypeDesc::Tmty_with(
                child,
                vec![(path, loc, WithConstraint::Twith_module(path, loc)); N],
            ),
            mty_type: super::super::decl::ModuleType::MtySignature(Arc::new(vec![])),
            mty_env: EnvRef(0),
            mty_loc: LocIdx(0),
            mty_attributes: Default::default(),
        };
        let mut log = ReadLog::default();
        module.log_reads(&mut log, &ta);
        assert_eq!(log.path_events, N);
        assert_eq!(log.paths.len(), 1);

        let constructor = ConstructorDescription {
            cstr_name: "Extension".into(),
            cstr_res: ty,
            cstr_existentials: vec![],
            cstr_args: vec![ty; N],
            cstr_arity: N as i32,
            cstr_kind: ConstructorKind::Extension(path),
            cstr_generalized: false,
            cstr_private: PrivateFlag::Public,
            cstr_loc: DeclLoc::none(),
            cstr_attributes: vec![],
            cstr_inlined: None,
        };
        let mut log = ReadLog::default();
        log.constructor(&constructor);
        assert_eq!(log.root_events, N + 1);
        assert_eq!(log.path_events, 1);
    }

    #[test]
    fn ten_thousand_shared_type_edges_are_visited_once() {
        let ctx = TypeContext::new(std::sync::Arc::new(crate::IdGenerator::new()));
        let mut log = ReadLog::default();
        let mut root = ctx.new_var(None);
        let leaf = root;
        for _ in 0..10_000 {
            root = ctx.new_tuple(vec![root, leaf]);
            log.ty(root);
            log.ty(root);
        }
        assert_eq!(log.root_events, 20_000);
        assert_eq!(log.types.len(), 10_000);
        assert!(log.resolve(&ctx, &[]).is_empty());
        assert_eq!(log.expanded_nodes, 10_001);
        assert_eq!(log.type_steps, 30_000); // 10,000 roots + 20,000 edges
    }

    #[test]
    fn read_walk_handles_fit_in_sixteen_bytes() {
        assert_eq!(std::mem::size_of::<TypeExprRef>(), 4);
        assert_eq!(std::mem::size_of::<Path>(), 8);
        assert_eq!(std::mem::size_of::<(usize, Kind)>(), 16);
        assert_eq!(std::mem::size_of::<&mut ReadLog>(), 8);
        assert_eq!(std::mem::size_of::<&mut TypeReader<'_>>(), 8);
        // ReadLog/TypeReader are per-compilation buffers, never per-node values.
    }

    #[test]
    fn read_log_observes_unification_after_recording_a_root() {
        let ctx = TypeContext::new(std::sync::Arc::new(crate::IdGenerator::new()));
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
        let reads: ahash::AHashSet<_> = log.resolve(&ctx, &[]).into_iter().collect();
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
