//! Inactive indexed pre-JS optimizer and ownership boundary.
//!
//! This ports the optimizer, coercion, grouping, hoisted-alias, and required-
//! module stages from `compiler/core/lam_compile_main.ml:278-427` without
//! materializing recursive Lambda between passes. Production remains on the
//! recursive pipeline until the JS consumer is migrated in M6.

use std::sync::Arc;

use ahash::{AHashMap, AHashSet};

use crate::cmi::persistent_env::{CmjExportArity, CmjExportConstant};
use crate::context::IdGenerator;
use crate::diagnostics::{Warning, WarningConfig};
use crate::ident::Ident;
use crate::js_ir::ModuleId;
use crate::js_ir::op::Kind;
use crate::lambda::indexed::{IndexedLambda, IndexedLambdaContext, NodeId, NodeSnapshot, NodeView};
use crate::lambda::lam_analysis_indexed::no_side_effects;
use crate::lambda::lam_compat::{FieldDbgInfo, LetKind};
use crate::lambda::lam_compile_context::RecFlag;
use crate::lambda::lam_pass_collect::ExternalArityResolver;
use crate::lambda::lam_pass_collect_indexed::{IndexedElement, IndexedIdKind, get_arity_external};
use crate::lambda::lam_pass_remove_alias_indexed::IndexedExternalInlineResolver;
use crate::lambda::lam_primitive::{Mutable, Primitive};
use crate::lambda::lam_tag_info::TagInfo;
use crate::lambda::{HoistedExport, HoistedFunction, Lambda};

#[derive(Clone, Debug, PartialEq, Eq)]
enum IndexedGroup {
    Single(LetKind, NodeId),
    Recursive(Vec<(Ident, NodeId)>),
    Nop(NodeId),
}

impl IndexedGroup {
    fn roots(&self) -> impl Iterator<Item = NodeId> + '_ {
        let single = match self {
            Self::Single(_, root) | Self::Nop(root) => Some(*root),
            Self::Recursive(_) => None,
        };
        single.into_iter().chain(
            match self {
                Self::Recursive(bindings) => Some(bindings.as_slice()),
                _ => None,
            }
            .into_iter()
            .flatten()
            .map(|(_, root)| *root),
        )
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum IndexedPreJsError {
    DuplicateExport(String),
    MissingExportBlock,
    HoistedNameCollision {
        name: String,
        loc: crate::location::Location,
    },
    FatalWarnings,
}

impl std::fmt::Display for IndexedPreJsError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::DuplicateExport(name) => write!(formatter, "Duplicate export `{name}`"),
            Self::MissingExportBlock => formatter.write_str("Missing final export block"),
            Self::HoistedNameCollision { name, .. } => write!(
                formatter,
                "Cannot hoist this function as `{name}` because that name is already used by a top-level binding."
            ),
            Self::FatalWarnings => formatter.write_str("Hoisted-function warning treated as error"),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct IndexedHoistedWarning {
    pub(crate) path: Vec<String>,
    pub(crate) loc: crate::location::Location,
    pub(crate) warning: Warning,
    pub(crate) is_error: bool,
}

/// One owning pre-JS result. All node handles are private and remain paired
/// with `context`; M6 can add owner-scoped JS traversal methods without
/// exposing a caller-provided root. The same generator is retained for later
/// JS temporaries.
pub(crate) enum IndexedDiagnosticGroup {
    Single(LetKind, Ident, Lambda),
    Recursive(Vec<(Ident, Lambda)>),
    Nop(Lambda),
}

pub(crate) trait IndexedDiagnosticsObserver {
    fn lambda(&mut self, pass: &'static str, lambda: Lambda);
    fn groups(&mut self, groups: Vec<IndexedDiagnosticGroup>);
    fn warning(&mut self, _warning: &IndexedHoistedWarning) {}
}

pub(crate) struct IndexedCmjExports {
    pub(crate) arities: AHashMap<String, CmjExportArity>,
    pub(crate) constants: AHashMap<String, CmjExportConstant>,
}

pub(crate) struct IndexedPreJsBackend {
    context: IndexedLambdaContext,
    groups: Vec<(Option<Ident>, IndexedGroup)>,
    export_map: Vec<(Ident, NodeId)>,
    hoisted_exports: Vec<HoistedExport>,
    possible_required_modules: AHashSet<ModuleId>,
    /// First effectful top-level group. `None` means local groups are pure
    /// before dependency effects are added.
    maybe_pure: Option<String>,
    id_gen: Arc<IdGenerator>,
    hoisted_warnings: Vec<IndexedHoistedWarning>,
    /// Selected CMJ payloads remain owner-paired. Only the explicit CMJ
    /// serializer boundary materializes these roots.
    cmj_inline_roots: Vec<(String, NodeId)>,
    fatal_warnings_pending: bool,
}

fn materialize_diagnostic_groups(
    context: &IndexedLambdaContext,
    groups: &[(Option<Ident>, IndexedGroup)],
) -> Vec<IndexedDiagnosticGroup> {
    groups
        .iter()
        .map(|(id, group)| match group {
            IndexedGroup::Single(kind, root) => IndexedDiagnosticGroup::Single(
                *kind,
                id.as_ref().unwrap().clone(),
                context.store().materialize_node(*root),
            ),
            IndexedGroup::Recursive(bindings) => IndexedDiagnosticGroup::Recursive(
                bindings
                    .iter()
                    .map(|(id, root)| (id.clone(), context.store().materialize_node(*root)))
                    .collect(),
            ),
            IndexedGroup::Nop(root) => {
                IndexedDiagnosticGroup::Nop(context.store().materialize_node(*root))
            }
        })
        .collect()
}

impl IndexedPreJsBackend {
    pub(crate) fn generator(&self) -> &Arc<IdGenerator> {
        &self.id_gen
    }

    pub(crate) fn possible_required_modules(&self) -> &AHashSet<ModuleId> {
        &self.possible_required_modules
    }

    pub(crate) fn maybe_pure(&self) -> Option<&str> {
        self.maybe_pure.as_deref()
    }

    pub(crate) fn hoisted_warnings(&self) -> &[IndexedHoistedWarning] {
        &self.hoisted_warnings
    }

    /// M6 calls this after JS lowering and required-module collection, directly
    /// before effect/CMJ export, matching `Warnings.check_fatal`.
    pub(crate) fn check_fatal_warnings(&self) -> Result<(), IndexedPreJsError> {
        if self.fatal_warnings_pending {
            Err(IndexedPreJsError::FatalWarnings)
        } else {
            Ok(())
        }
    }

    pub(crate) fn storage_measurements(
        &self,
    ) -> crate::lambda::indexed::IndexedStorageMeasurements {
        self.context.storage_measurements()
    }

    /// Indexed `Lam_stats_export.values_of_export`. Arity and persistent
    /// payload selection run together so the two omit gates stay coupled.
    pub(crate) fn collect_cmj_exports(
        &mut self,
        cross_module_inline: bool,
        external_arity: &mut ExternalArityResolver<'_>,
    ) -> IndexedCmjExports {
        enum Persistent {
            None,
            ModuleAlias,
            Root(NodeId),
        }
        let exports = self.context.metadata().exports.clone();
        let mut arities = AHashMap::new();
        let mut constants = AHashMap::new();
        let mut inline_roots = Vec::new();
        for export in exports {
            let root = self.export_root(&export);
            let kind = self.context.metadata().ident_tbl.get(&export).cloned();
            let arity = match kind {
                Some(IndexedIdKind::FunctionId { arity, .. }) => CmjExportArity::Single(arity),
                Some(IndexedIdKind::ImmutableBlock(elements)) => {
                    let mut fields = Vec::with_capacity(elements.len());
                    for element in elements {
                        fields.push(match element {
                            IndexedElement::Na => crate::lambda::lam_arity::Arity::na(),
                            IndexedElement::SimpleForm(root) => {
                                let (store, metadata, _) = self.context.optimizer_parts_mut();
                                get_arity_external(store, metadata, root, external_arity)
                            }
                        });
                    }
                    CmjExportArity::Submodule(fields)
                }
                _ => {
                    let fields = root.and_then(|root| match self.context.store().view(root) {
                        NodeView::Prim(Primitive::Pmakeblock(_, Mutable::Immutable), args, _) => {
                            Some(args.to_vec())
                        }
                        _ => None,
                    });
                    match fields {
                        Some(fields) => {
                            let mut arities = Vec::with_capacity(fields.len());
                            for root in fields {
                                let (store, metadata, _) = self.context.optimizer_parts_mut();
                                arities.push(get_arity_external(
                                    store,
                                    metadata,
                                    root,
                                    external_arity,
                                ));
                            }
                            CmjExportArity::Submodule(arities)
                        }
                        None => CmjExportArity::Single(crate::lambda::lam_arity::Arity::na()),
                    }
                }
            };
            let persistent = match root {
                Some(root) => match self.context.store().view(root) {
                    NodeView::Const(crate::lambda::Constant::ModuleAlias) => {
                        Persistent::ModuleAlias
                    }
                    NodeView::Const(
                        crate::lambda::Constant::JsNull
                        | crate::lambda::Constant::JsUndefined { .. }
                        | crate::lambda::Constant::JsTrue
                        | crate::lambda::Constant::JsFalse,
                    ) => Persistent::Root(root),
                    NodeView::Function(_, _, _, attr)
                        if cross_module_inline
                            && (matches!(attr.inline, crate::lambda::InlineAttribute::Always)
                                || attr.is_a_functor)
                            && crate::lambda::lam_analysis_indexed::is_closed(
                                self.context.store(),
                                root,
                            ) =>
                    {
                        Persistent::Root(root)
                    }
                    NodeView::Const(
                        crate::lambda::Constant::Constructor(_)
                        | crate::lambda::Constant::Pointer(_)
                        | crate::lambda::Constant::Int {
                            comment: Some(crate::lambda::lam_constant::PointerInfo::Constructor(_)),
                            ..
                        },
                    ) if cross_module_inline
                        && crate::lambda::lam_pass_collect_indexed::indexed_size(
                            self.context.store(),
                            root,
                        ) < crate::lambda::lam_analysis::SMALL_INLINE_SIZE
                        && pass_free_variables(self.context.store(), root).is_empty() =>
                    {
                        Persistent::Root(root)
                    }
                    _ => Persistent::None,
                },
                None => Persistent::None,
            };
            let omit = match (&arity, &persistent) {
                (CmjExportArity::Single(arity), Persistent::None | Persistent::ModuleAlias) => {
                    arity.first_arity_na()
                }
                (CmjExportArity::Submodule(fields), Persistent::None) => fields.is_empty(),
                _ => false,
            };
            if omit {
                continue;
            }
            let name = export.name().to_string();
            if let Some(root) = root {
                let constant = match self.context.store().view(root) {
                    NodeView::Const(crate::lambda::Constant::JsNull) => {
                        Some(CmjExportConstant::Null)
                    }
                    NodeView::Const(crate::lambda::Constant::JsUndefined { is_unit }) => {
                        Some(CmjExportConstant::Undefined { is_unit: *is_unit })
                    }
                    NodeView::Const(crate::lambda::Constant::JsTrue) => {
                        Some(CmjExportConstant::Bool(true))
                    }
                    NodeView::Const(crate::lambda::Constant::JsFalse) => {
                        Some(CmjExportConstant::Bool(false))
                    }
                    _ => None,
                };
                if let Some(constant) = constant {
                    constants.insert(name.clone(), constant);
                }
            }
            if let Persistent::Root(root) = persistent {
                inline_roots.push((name.clone(), root));
            }
            arities.insert(name, arity);
        }
        self.cmj_inline_roots = inline_roots;
        IndexedCmjExports { arities, constants }
    }

    #[cfg(test)]
    fn cmj_inline_names(&self) -> Vec<&str> {
        self.cmj_inline_roots
            .iter()
            .map(|(name, _)| name.as_str())
            .collect()
    }

    pub(crate) fn materialize_cmj_inline_lambdas(&self) -> Vec<(String, Lambda)> {
        self.cmj_inline_roots
            .iter()
            .map(|(name, root)| (name.clone(), self.context.store().materialize_node(*root)))
            .collect()
    }

    fn export_root(&self, export: &Ident) -> Option<NodeId> {
        self.export_map
            .iter()
            .rev()
            .find_map(|(id, root)| id.same(export).then_some(*root))
    }

    #[cfg(test)]
    fn materialize_groups(&self) -> Vec<(Option<Ident>, Lambda)> {
        self.groups
            .iter()
            .map(|(id, group)| {
                (
                    id.clone(),
                    match group {
                        IndexedGroup::Single(_, root) | IndexedGroup::Nop(root) => {
                            self.context.store().materialize_node(*root)
                        }
                        IndexedGroup::Recursive(bindings) => Lambda::Lletrec(
                            bindings
                                .iter()
                                .map(|(id, root)| {
                                    (id.clone(), self.context.store().materialize_node(*root))
                                })
                                .collect(),
                            Box::new(Lambda::unit()),
                        ),
                    },
                )
            })
            .collect()
    }

    #[cfg(test)]
    pub(crate) fn exports(&self) -> &[Ident] {
        &self.context.metadata().exports
    }

    #[cfg(test)]
    fn export_map(&self) -> Vec<(Ident, Lambda)> {
        self.export_map
            .iter()
            .map(|(id, root)| (id.clone(), self.context.store().materialize_node(*root)))
            .collect()
    }

    #[cfg(test)]
    fn hoisted_exports(&self) -> &[HoistedExport] {
        &self.hoisted_exports
    }
}

fn extract_export_idents(lambda: &Lambda) -> Vec<Ident> {
    match lambda {
        Lambda::Llet(_, _, _, body) | Lambda::Lletrec(_, body) => extract_export_idents(body),
        Lambda::Lsequence(_, body) => extract_export_idents(body),
        Lambda::Lprim(info) => match &info.primitive {
            Primitive::Pmakeblock(TagInfo::ModuleExport(exports), _) => exports.clone(),
            _ => Vec::new(),
        },
        _ => Vec::new(),
    }
}

fn flatten(
    store: &IndexedLambda,
    node: NodeId,
    acc: Vec<(Option<Ident>, IndexedGroup)>,
) -> (NodeId, Vec<(Option<Ident>, IndexedGroup)>) {
    match store.view(node) {
        NodeView::Let(kind, id, value, body) => {
            let id = id.clone();
            let (value, mut groups) = flatten(store, value, acc);
            groups.insert(0, (Some(id), IndexedGroup::Single(kind, value)));
            flatten(store, body, groups)
        }
        NodeView::LetRec(bindings, body) => {
            let mut groups = acc;
            groups.insert(0, (None, IndexedGroup::Recursive(bindings.to_vec())));
            flatten(store, body, groups)
        }
        NodeView::Sequence(left, right) => {
            let (left, mut groups) = flatten(store, left, acc);
            if !matches!(
                store.view(left),
                NodeView::Var(_) | NodeView::Const(_) | NodeView::Function(_, _, _, _)
            ) {
                groups.insert(0, (None, IndexedGroup::Nop(left)));
            }
            flatten(store, right, groups)
        }
        _ => (node, acc),
    }
}

fn set_insert(set: &mut Vec<Ident>, id: Ident) -> bool {
    match set.binary_search_by(|existing| ident_order(existing, &id)) {
        Ok(_) => false,
        Err(index) => {
            set.insert(index, id);
            true
        }
    }
}

fn set_remove(set: &mut Vec<Ident>, id: &Ident) {
    if let Ok(index) = set.binary_search_by(|existing| ident_order(existing, id)) {
        set.remove(index);
    }
}

fn pass_free_variables(store: &IndexedLambda, root: NodeId) -> Vec<Ident> {
    fn visit(store: &IndexedLambda, node: NodeId, free: &mut Vec<Ident>) {
        match store.view(node) {
            NodeView::Var(id) => {
                set_insert(free, id.clone());
            }
            NodeView::Assign(id, value) => {
                visit(store, value, free);
                set_insert(free, id.clone());
            }
            NodeView::Apply(function, args, _, _) => {
                visit(store, function, free);
                for child in args {
                    visit(store, *child, free);
                }
            }
            NodeView::Function(_, params, body, _) => {
                visit(store, body, free);
                for id in params {
                    set_remove(free, id);
                }
            }
            NodeView::Let(_, id, value, body) => {
                visit(store, value, free);
                visit(store, body, free);
                set_remove(free, id);
            }
            NodeView::LetRec(bindings, body) => {
                visit(store, body, free);
                for (_, value) in bindings {
                    visit(store, *value, free);
                }
                for (id, _) in bindings {
                    set_remove(free, id);
                }
            }
            NodeView::Prim(_, args, _) | NodeView::StaticRaise(_, args) => {
                for child in args {
                    visit(store, *child, free);
                }
            }
            NodeView::Switch {
                scrutinee,
                consts,
                blocks,
                fail_action,
                ..
            } => {
                visit(store, scrutinee, free);
                for (_, child) in consts {
                    visit(store, *child, free);
                }
                for (_, child) in blocks {
                    visit(store, *child, free);
                }
                if let Some(child) = fail_action {
                    visit(store, child, free);
                }
            }
            NodeView::StringSwitch(scrutinee, cases, default) => {
                visit(store, scrutinee, free);
                for (_, child) in cases {
                    visit(store, *child, free);
                }
                if let Some(child) = default {
                    visit(store, child, free);
                }
            }
            NodeView::StaticCatch(body, _, params, handler) => {
                visit(store, body, free);
                visit(store, handler, free);
                for id in params {
                    set_remove(free, id);
                }
            }
            NodeView::TryWith(body, id, handler) => {
                visit(store, body, free);
                visit(store, handler, free);
                set_remove(free, id);
            }
            NodeView::IfThenElse(a, b, c) | NodeView::For(_, a, b, _, c) => {
                visit(store, a, free);
                visit(store, b, free);
                visit(store, c, free);
                if let NodeView::For(id, _, _, _, _) = store.view(node) {
                    set_remove(free, id);
                }
            }
            NodeView::Sequence(a, b) | NodeView::While(a, b) => {
                visit(store, a, free);
                visit(store, b, free);
            }
            NodeView::ForOf(id, iterable, body) | NodeView::ForAwaitOf(id, iterable, body) => {
                visit(store, iterable, free);
                visit(store, body, free);
                set_remove(free, id);
            }
            NodeView::GlobalModule(_, _)
            | NodeView::Const(_)
            | NodeView::Break
            | NodeView::Continue => {}
        }
    }
    let mut free = Vec::new();
    visit(store, root, &mut free);
    free
}

fn ident_order(left: &Ident, right: &Ident) -> std::cmp::Ordering {
    left.stamp()
        .cmp(&right.stamp())
        .then_with(|| left.name().cmp(right.name()))
        .then_with(|| left.flags().bits().cmp(&right.flags().bits()))
}

fn remove_dead_groups(
    store: &IndexedLambda,
    exports: &[Ident],
    groups: Vec<(Option<Ident>, IndexedGroup)>,
) -> Vec<(Option<Ident>, IndexedGroup)> {
    let mut free_by_ident = Vec::<(Ident, Vec<Ident>)>::new();
    let mut initial = exports.to_vec();
    for (id, group) in &groups {
        match group {
            IndexedGroup::Single(kind, root) => {
                let id = id.as_ref().expect("single group has an identifier");
                free_by_ident.push((id.clone(), pass_free_variables(store, *root)));
                if matches!(kind, LetKind::Strict | LetKind::Variable) {
                    initial.insert(0, id.clone());
                }
            }
            IndexedGroup::Recursive(bindings) => {
                for (id, value) in bindings {
                    free_by_ident.push((id.clone(), pass_free_variables(store, *value)));
                    if !matches!(store.view(*value), NodeView::Function(_, _, _, _)) {
                        initial.insert(0, id.clone());
                    }
                }
            }
            IndexedGroup::Nop(root) => {
                if !no_side_effects(store, *root) {
                    for id in pass_free_variables(store, *root) {
                        initial.insert(0, id);
                    }
                }
            }
        }
    }
    fn dfs(id: &Ident, free_by_ident: &[(Ident, Vec<Ident>)], visited: &mut Vec<Ident>) {
        if id.is_global() || id.is_js() || visited.iter().any(|seen| seen.same(id)) {
            return;
        }
        visited.push(id.clone());
        let free = free_by_ident
            .iter()
            .rev()
            .find_map(|(key, free)| key.same(id).then_some(free))
            .unwrap_or_else(|| {
                panic!(
                    "indexed Lam_dce missing local binding {}/{}",
                    id.name(),
                    id.stamp()
                )
            });
        for dependency in free {
            dfs(dependency, free_by_ident, visited);
        }
    }
    let mut visited = Vec::new();
    for id in &initial {
        dfs(id, &free_by_ident, &mut visited);
    }
    groups
        .into_iter()
        .filter_map(|(id, group)| match group {
            IndexedGroup::Single(_, _)
                if !visited.iter().any(|seen| seen.same(id.as_ref().unwrap())) =>
            {
                None
            }
            IndexedGroup::Recursive(mut bindings) => {
                bindings.retain(|(id, _)| visited.iter().any(|seen| seen.same(id)));
                (!bindings.is_empty()).then_some((id, IndexedGroup::Recursive(bindings)))
            }
            group => Some((id, group)),
        })
        .collect()
}

fn coerce_and_group(
    context: &mut IndexedLambdaContext,
    id_gen: &IdGenerator,
    external_arity: &mut ExternalArityResolver<'_>,
) -> Result<(Vec<(Option<Ident>, IndexedGroup)>, Vec<(Ident, NodeId)>), IndexedPreJsError> {
    let root = context.current_root();
    let (export_block, reverse_input) = flatten(context.store(), root, Vec::new());
    let original_exports = context.metadata().exports.clone();
    let lambda_exports = match context.store().view(export_block) {
        NodeView::Prim(Primitive::Pmakeblock(_, _), args, _) => args.to_vec(),
        _ => return Err(IndexedPreJsError::MissingExportBlock),
    };
    if original_exports.len() != lambda_exports.len() {
        return Err(IndexedPreJsError::MissingExportBlock);
    }

    // `Ext_list.fold_right2` invokes the callback right-to-left, while consing
    // creates source-order export and coercion lists (lam_coercion.ml:88-158).
    let mut names = AHashSet::new();
    let mut export_list = Vec::new();
    let mut export_set = context.metadata().export_idents.clone();
    let mut export_map = Vec::new();
    let mut coercions = Vec::new();
    for (original, value) in original_exports.into_iter().zip(lambda_exports).rev() {
        if !names.insert(original.name().to_string()) {
            return Err(IndexedPreJsError::DuplicateExport(
                original.name().to_string(),
            ));
        }
        match context.store().view(value) {
            NodeView::Var(id) if id.name() == original.name() => {
                let id = id.clone();
                export_list.insert(0, id.clone());
                if id.stamp() != original.stamp() {
                    export_set.remove(&original);
                    export_set.insert(id);
                }
            }
            NodeView::Var(id) => {
                let source = id.clone();
                let newid = original.rename(id_gen);
                if let Some(kind) = context.metadata().ident_tbl.get(&source).cloned() {
                    context
                        .metadata_mut_for_backend()
                        .ident_tbl
                        .insert(newid.clone(), kind);
                }
                export_list.insert(0, newid.clone());
                export_map.insert(0, (newid.clone(), value));
                coercions.insert(
                    0,
                    (
                        Some(newid.clone()),
                        IndexedGroup::Single(LetKind::Alias, value),
                    ),
                );
                let _ = source;
            }
            _ => {
                let newid = original.rename(id_gen);
                let arity = {
                    let (store, metadata, _) = context.optimizer_parts_mut();
                    get_arity_external(store, metadata, value, external_arity)
                };
                if !arity.first_arity_na() {
                    let lambda =
                        matches!(context.store().view(value), NodeView::Function(_, _, _, _))
                            .then_some((value, RecFlag::NonRec));
                    context
                        .metadata_mut_for_backend()
                        .ident_tbl
                        .insert(newid.clone(), IndexedIdKind::FunctionId { arity, lambda });
                }
                export_list.insert(0, newid.clone());
                export_map.insert(0, (newid.clone(), value));
                coercions.insert(
                    0,
                    (
                        Some(newid.clone()),
                        IndexedGroup::Single(LetKind::Strict, value),
                    ),
                );
                let _ = original;
            }
        }
    }

    context.metadata_mut_for_backend().exports = export_list.clone();
    context.metadata_mut_for_backend().export_idents = export_set.clone();

    let mut groups = coercions;
    for group in reverse_input {
        if let (Some(id), IndexedGroup::Single(_, root)) = &group
            && export_set.contains(id)
        {
            if let Some((_, existing)) = export_map.iter_mut().find(|(key, _)| key.same(id)) {
                *existing = *root;
            } else {
                export_map.push((id.clone(), *root));
            }
        }
        groups.insert(0, group);
    }
    let groups = remove_dead_groups(context.store(), &export_list, groups);
    Ok((groups, export_map))
}

fn group_side_effect_reason(
    store: &IndexedLambda,
    groups: &[(Option<Ident>, IndexedGroup)],
) -> Option<String> {
    for (id, group) in groups {
        match group {
            IndexedGroup::Single(LetKind::Strict | LetKind::Variable, root)
                if !no_side_effects(store, *root) =>
            {
                return Some(id.as_ref().unwrap().name().to_string());
            }
            IndexedGroup::Recursive(bindings) => {
                if let Some((id, _)) = bindings
                    .iter()
                    .find(|(_, root)| !no_side_effects(store, *root))
                {
                    return Some(id.name().to_string());
                }
            }
            IndexedGroup::Nop(root) if !no_side_effects(store, *root) => {
                return Some(String::new());
            }
            IndexedGroup::Single(_, _) | IndexedGroup::Nop(_) => {}
        }
    }
    None
}

fn collect_group_bindings(
    _store: &IndexedLambda,
    groups: &[(Option<Ident>, IndexedGroup)],
) -> AHashMap<Ident, NodeId> {
    let mut bindings = AHashMap::new();
    for (id, group) in groups {
        match group {
            IndexedGroup::Single(_, root) => {
                bindings.insert(id.as_ref().unwrap().clone(), *root);
            }
            IndexedGroup::Recursive(items) => {
                bindings.extend(items.iter().cloned());
            }
            IndexedGroup::Nop(_) => {}
        }
    }
    bindings
}

fn resolve_binding(
    store: &IndexedLambda,
    groups: &AHashMap<Ident, NodeId>,
    node: NodeId,
    seen: &mut AHashSet<Ident>,
) -> (NodeId, Option<Ident>) {
    match store.view(node) {
        NodeView::Var(id) => {
            let id = id.clone();
            if !seen.insert(id.clone()) {
                return (node, Some(id));
            }
            match groups.get(&id).copied() {
                Some(alias)
                    if matches!(
                        store.view(alias),
                        NodeView::Var(_) | NodeView::Prim(Primitive::Pfield(_, _), _, _)
                    ) =>
                {
                    resolve_binding(store, groups, alias, seen)
                }
                Some(resolved) => (resolved, Some(id)),
                None => (node, Some(id)),
            }
        }
        NodeView::Prim(Primitive::Pfield(pos, _), [base], _) => {
            let (base, _) = resolve_binding(store, groups, *base, seen);
            if let NodeView::Prim(Primitive::Pmakeblock(TagInfo::Module(_), _), args, _) =
                store.view(base)
                && let Some(field) = usize::try_from(*pos).ok().and_then(|pos| args.get(pos))
            {
                return resolve_binding(store, groups, *field, seen);
            }
            (node, None)
        }
        _ => (node, None),
    }
}

fn find_path(
    store: &IndexedLambda,
    groups: &AHashMap<Ident, NodeId>,
    node: NodeId,
    fields: &[String],
    positions: &mut Vec<(i32, String)>,
) -> Option<(NodeId, Option<Ident>)> {
    if fields.is_empty() {
        return Some(resolve_binding(store, groups, node, &mut AHashSet::new()));
    }
    let (resolved, _) = resolve_binding(store, groups, node, &mut AHashSet::new());
    let NodeView::Prim(Primitive::Pmakeblock(TagInfo::Module(names), _), args, _) =
        store.view(resolved)
    else {
        return None;
    };
    let position = names.iter().position(|name| name == &fields[0])?;
    positions.push((position as i32, fields[0].clone()));
    find_path(store, groups, args[position], &fields[1..], positions)
}

fn add_hoisted_aliases(
    context: &mut IndexedLambdaContext,
    groups: &mut Vec<(Option<Ident>, IndexedGroup)>,
    export_map: &mut Vec<(Ident, NodeId)>,
    hoisted: &[HoistedFunction],
    id_gen: &IdGenerator,
    warning_config: &WarningConfig,
    diagnostics: &mut Option<&mut dyn IndexedDiagnosticsObserver>,
) -> Result<(Vec<HoistedExport>, Vec<IndexedHoistedWarning>), IndexedPreJsError> {
    let group_map = collect_group_bindings(context.store(), groups);
    let exported_modules = context
        .metadata()
        .exports
        .iter()
        .map(|id| (id.name().to_string(), id.clone()))
        .collect::<AHashMap<_, _>>();
    let mut occupied = groups
        .iter()
        .filter_map(|(id, _)| id.as_ref())
        .map(|id| crate::js_ir::printer::convert_ident_name(id.name()))
        .collect::<AHashSet<_>>();
    let mut aliases = Vec::new();
    let mut metadata = Vec::new();
    let mut warnings = Vec::new();
    let mut misplaced = |warnings: &mut Vec<IndexedHoistedWarning>, item: &HoistedFunction| {
        let warning = Warning::MisplacedAttribute {
            name: "res.hoistedFunction".to_string(),
        };
        if warning_config.is_active(&warning) {
            let delivered = IndexedHoistedWarning {
                path: item.path.clone(),
                loc: item.loc,
                is_error: warning_config.is_error(&warning),
                warning,
            };
            if let Some(diagnostics) = diagnostics.as_deref_mut() {
                diagnostics.warning(&delivered);
            }
            warnings.push(delivered);
        }
    };
    for item in hoisted {
        let Some((top, fields)) = item.path.split_first() else {
            misplaced(&mut warnings, item);
            continue;
        };
        let Some(top_id) = exported_modules.get(top) else {
            misplaced(&mut warnings, item);
            continue;
        };
        let Some(module) = group_map.get(top_id).copied() else {
            misplaced(&mut warnings, item);
            continue;
        };
        let mut positions = Vec::new();
        let Some((target, Some(target_id))) =
            find_path(context.store(), &group_map, module, fields, &mut positions)
        else {
            misplaced(&mut warnings, item);
            continue;
        };
        if !target_id.same(&item.binding) {
            misplaced(&mut warnings, item);
            continue;
        }
        let name = item
            .path
            .iter()
            .map(|part| {
                if part.len() >= 3 && part.starts_with("\\\"") && part.ends_with('"') {
                    &part[2..part.len() - 1]
                } else {
                    part.as_str()
                }
            })
            .collect::<Vec<_>>()
            .join("$");
        let js_name = crate::js_ir::printer::convert_ident_name(&name);
        if !occupied.insert(js_name) {
            let loc = if matches!(context.store().view(target), NodeView::Function(_, _, _, _)) {
                item.target_loc
            } else {
                item.loc
            };
            return Err(IndexedPreJsError::HoistedNameCollision { name, loc });
        }
        let alias_id = id_gen.create(&name);
        let mut access = context
            .store_mut()
            .append(NodeSnapshot::Var(top_id.clone()));
        for (position, field) in positions {
            access = context.store_mut().append(NodeSnapshot::Prim(
                Primitive::Pfield(position, FieldDbgInfo::Module { name: field }),
                vec![access],
                item.loc,
            ));
        }
        aliases.insert(0, (alias_id, access, item.path.clone(), name));
        let _ = target;
    }
    // `js_hoisted_aliases` returns reverse source order. The next fold conses
    // again, then groups/exports use `List.rev`, leaving those aliases in
    // reverse source order. Hoisted CMJ metadata keeps source order.
    for (id, root, path, name) in aliases {
        groups.push((Some(id.clone()), IndexedGroup::Single(LetKind::Alias, root)));
        context.metadata_mut_for_backend().exports.push(id.clone());
        context
            .metadata_mut_for_backend()
            .export_idents
            .insert(id.clone());
        export_map.push((id, root));
        metadata.insert(
            0,
            HoistedExport {
                path,
                export_name: name,
            },
        );
    }
    Ok((metadata, warnings))
}

fn collect_required_modules(
    store: &IndexedLambda,
    roots: impl IntoIterator<Item = NodeId>,
) -> AHashSet<ModuleId> {
    fn visit(store: &IndexedLambda, node: NodeId, modules: &mut AHashSet<ModuleId>) {
        if let NodeView::GlobalModule(id, dynamic_import) = store.view(node) {
            modules.insert(ModuleId {
                id: id.clone(),
                kind: Kind::Ml,
                dynamic_import,
            });
            return;
        }
        match store.view(node) {
            NodeView::Apply(f, args, _, _) => {
                visit(store, f, modules);
                for n in args {
                    visit(store, *n, modules);
                }
            }
            NodeView::Function(_, _, body, _) => visit(store, body, modules),
            NodeView::Let(_, _, value, body) => {
                visit(store, value, modules);
                visit(store, body, modules);
            }
            NodeView::LetRec(bindings, body) => {
                for (_, n) in bindings {
                    visit(store, *n, modules);
                }
                visit(store, body, modules);
            }
            NodeView::Prim(_, args, _) | NodeView::StaticRaise(_, args) => {
                for n in args {
                    visit(store, *n, modules);
                }
            }
            NodeView::Switch {
                scrutinee,
                consts,
                blocks,
                fail_action,
                ..
            } => {
                visit(store, scrutinee, modules);
                for (_, n) in consts {
                    visit(store, *n, modules);
                }
                for (_, n) in blocks {
                    visit(store, *n, modules);
                }
                if let Some(n) = fail_action {
                    visit(store, n, modules);
                }
            }
            NodeView::StringSwitch(scrutinee, cases, default) => {
                visit(store, scrutinee, modules);
                for (_, n) in cases {
                    visit(store, *n, modules);
                }
                if let Some(n) = default {
                    visit(store, n, modules);
                }
            }
            NodeView::StaticCatch(body, _, _, handler) | NodeView::TryWith(body, _, handler) => {
                visit(store, body, modules);
                visit(store, handler, modules);
            }
            NodeView::IfThenElse(a, b, c) | NodeView::For(_, a, b, _, c) => {
                visit(store, a, modules);
                visit(store, b, modules);
                visit(store, c, modules);
            }
            NodeView::Sequence(a, b)
            | NodeView::While(a, b)
            | NodeView::ForOf(_, a, b)
            | NodeView::ForAwaitOf(_, a, b) => {
                visit(store, a, modules);
                visit(store, b, modules);
            }
            NodeView::Assign(_, value) => visit(store, value, modules),
            NodeView::Var(_)
            | NodeView::GlobalModule(_, _)
            | NodeView::Const(_)
            | NodeView::Break
            | NodeView::Continue => {}
        }
    }
    let mut modules = AHashSet::new();
    for root in roots {
        visit(store, root, &mut modules);
    }
    modules
}

/// Candidate producer boundary: Raw Lambda lowers once into the indexed
/// optimizer using the same caller-owned generator that the owning result
/// carries into M6.
pub(crate) fn lower_and_optimize_for_pre_js_indexed(
    indexed_raw: crate::raw_lambda::convert::IndexedRawLambda,
    export_idents: Vec<Ident>,
    hoisted: &[HoistedFunction],
    possible_required_modules: &AHashSet<ModuleId>,
    jsx_preserve: bool,
    external_inline: &mut IndexedExternalInlineResolver<'_>,
    external_arity: &mut ExternalArityResolver<'_>,
) -> Result<IndexedPreJsBackend, IndexedPreJsError> {
    lower_and_optimize_for_pre_js_indexed_with_diagnostics(
        indexed_raw,
        export_idents,
        hoisted,
        possible_required_modules,
        jsx_preserve,
        external_inline,
        external_arity,
        &WarningConfig::new(),
        None,
    )
}

pub(crate) fn lower_and_optimize_for_pre_js_indexed_with_diagnostics(
    indexed_raw: crate::raw_lambda::convert::IndexedRawLambda,
    export_idents: Vec<Ident>,
    hoisted: &[HoistedFunction],
    possible_required_modules: &AHashSet<ModuleId>,
    jsx_preserve: bool,
    external_inline: &mut IndexedExternalInlineResolver<'_>,
    external_arity: &mut ExternalArityResolver<'_>,
    warning_config: &WarningConfig,
    diagnostics: Option<&mut dyn IndexedDiagnosticsObserver>,
) -> Result<IndexedPreJsBackend, IndexedPreJsError> {
    let (raw, id_gen) = indexed_raw.into_parts();
    let lambda = crate::raw_lambda::lower::lower_to_lambda_with_id_gen(raw, id_gen.clone());
    optimize_for_pre_js_indexed_with_diagnostics(
        lambda,
        export_idents,
        hoisted,
        possible_required_modules,
        jsx_preserve,
        id_gen,
        external_inline,
        external_arity,
        warning_config,
        diagnostics,
    )
}

/// Runs the complete inactive M1-M5 optimizer in the reference sequence. One
/// compatibility import occurs at entry; no pass or grouped result converts
/// back to recursive Lambda.
pub(crate) fn optimize_for_pre_js_indexed(
    lambda: Lambda,
    export_idents: Vec<Ident>,
    hoisted: &[HoistedFunction],
    possible_required_modules: &AHashSet<ModuleId>,
    jsx_preserve: bool,
    id_gen: Arc<IdGenerator>,
    external_inline: &mut IndexedExternalInlineResolver<'_>,
    external_arity: &mut ExternalArityResolver<'_>,
) -> Result<IndexedPreJsBackend, IndexedPreJsError> {
    optimize_for_pre_js_indexed_with_diagnostics(
        lambda,
        export_idents,
        hoisted,
        possible_required_modules,
        jsx_preserve,
        id_gen,
        external_inline,
        external_arity,
        &WarningConfig::new(),
        None,
    )
}

pub(crate) fn optimize_for_pre_js_indexed_with_diagnostics(
    lambda: Lambda,
    export_idents: Vec<Ident>,
    hoisted: &[HoistedFunction],
    possible_required_modules: &AHashSet<ModuleId>,
    jsx_preserve: bool,
    id_gen: Arc<IdGenerator>,
    external_inline: &mut IndexedExternalInlineResolver<'_>,
    external_arity: &mut ExternalArityResolver<'_>,
    warning_config: &WarningConfig,
    mut diagnostics: Option<&mut dyn IndexedDiagnosticsObserver>,
) -> Result<IndexedPreJsBackend, IndexedPreJsError> {
    fn dump(
        diagnostics: &mut Option<&mut dyn IndexedDiagnosticsObserver>,
        pass: &'static str,
        context: &IndexedLambdaContext,
    ) {
        if let Some(diagnostics) = diagnostics.as_deref_mut() {
            diagnostics.lambda(pass, context.materialize());
        }
    }

    let mut context = IndexedLambdaContext::from_lambda(lambda, export_idents);
    dump(&mut diagnostics, "initial", &context);
    // `Lam_convert.convert` records possible modules before optimizer erasure
    // (`lam_compile_main.ml:278`, `lam_convert.ml:357-474`).
    let mut required =
        collect_required_modules(context.store(), std::iter::once(context.current_root()));
    required.extend(possible_required_modules.iter().cloned());
    context.deep_flatten(&id_gen);
    dump(&mut diagnostics, "flatten0", &context);
    context.collect_info_with_external_arity(external_arity);
    dump(&mut diagnostics, "flatten1", &context);
    context.simplify_exits(&id_gen);
    dump(&mut diagnostics, "simplify_exits", &context);
    context.collect_info_with_external_arity(external_arity);
    context.simplify_alias(&id_gen, jsx_preserve, external_inline);
    dump(&mut diagnostics, "simplify_alias", &context);
    context.deep_flatten(&id_gen);
    dump(&mut diagnostics, "flatten2", &context);
    context.collect_info_with_external_arity(external_arity);
    context.simplify_alias(&id_gen, jsx_preserve, external_inline);
    context.deep_flatten(&id_gen);
    context.collect_info_with_external_arity(external_arity);
    dump(&mut diagnostics, "alpha_before", &context);
    context.alpha_conversion_with_external_arity(&id_gen, external_arity);
    dump(&mut diagnostics, "alpha_after", &context);
    context.simplify_exits(&id_gen);
    context.collect_info_with_external_arity(external_arity);
    dump(&mut diagnostics, "simplify_alias_before", &context);
    context.simplify_alias(&id_gen, jsx_preserve, external_inline);
    dump(&mut diagnostics, "alpha_conversion", &context);
    context.alpha_conversion_with_external_arity(&id_gen, external_arity);
    dump(&mut diagnostics, "before-simplify_lets", &context);
    context.simplify_lets();
    dump(&mut diagnostics, "before-simplify-exits", &context);
    context.simplify_exits(&id_gen);
    dump(&mut diagnostics, "simplify_lets", &context);

    let (mut groups, mut export_map) = coerce_and_group(&mut context, &id_gen, external_arity)?;
    if let Some(diagnostics) = diagnostics.as_deref_mut() {
        diagnostics.groups(materialize_diagnostic_groups(&context, &groups));
    }
    let maybe_pure = group_side_effect_reason(context.store(), &groups);
    let (hoisted_exports, hoisted_warnings) = add_hoisted_aliases(
        &mut context,
        &mut groups,
        &mut export_map,
        hoisted,
        &id_gen,
        warning_config,
        &mut diagnostics,
    )?;
    let fatal_warnings_pending = hoisted_warnings.iter().any(|warning| warning.is_error);
    let roots = groups
        .iter()
        .flat_map(|(_, group)| group.roots())
        .chain(export_map.iter().map(|(_, root)| *root))
        .collect::<Vec<_>>();
    context.register_backend_roots(roots);
    Ok(IndexedPreJsBackend {
        context,
        groups,
        export_map,
        hoisted_exports,
        possible_required_modules: required,
        maybe_pure,
        id_gen,
        hoisted_warnings,
        cmj_inline_roots: Vec::new(),
        fatal_warnings_pending,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ident::IdentFlags;
    use crate::lambda::lam_constant::Constant;
    use crate::location::Location;

    fn id(name: &str, stamp: i32) -> Ident {
        Ident::new(name, stamp, IdentFlags::NONE)
    }
    fn module_export(exports: Vec<Ident>, args: Vec<Lambda>) -> Lambda {
        Lambda::prim(
            Primitive::Pmakeblock(TagInfo::ModuleExport(exports), Mutable::Immutable),
            args,
            Location::none(),
        )
    }
    fn run(
        lambda: Lambda,
        hoisted: &[HoistedFunction],
        generator: Arc<IdGenerator>,
    ) -> Result<IndexedPreJsBackend, IndexedPreJsError> {
        let mut inline = |_: &Ident, _: bool, _: &str| None;
        let mut arity = |_: &Ident, _: bool, _: &str| None;
        let exports = extract_export_idents(&lambda);
        optimize_for_pre_js_indexed(
            lambda,
            exports,
            hoisted,
            &AHashSet::new(),
            false,
            generator,
            &mut inline,
            &mut arity,
        )
    }

    #[test]
    fn coercion_allocates_right_to_left_but_keeps_source_export_order() {
        let a = id("a", 1);
        let b = id("b", 2);
        let generator = Arc::new(IdGenerator::with_start_stamp(100));
        let result = run(
            module_export(
                vec![a.clone(), b.clone()],
                vec![
                    Lambda::const_(Constant::int(1)),
                    Lambda::const_(Constant::int(2)),
                ],
            ),
            &[],
            generator.clone(),
        )
        .unwrap();
        assert_eq!(
            result
                .exports()
                .iter()
                .map(|id| (id.name(), id.stamp()))
                .collect::<Vec<_>>(),
            vec![("a", 102), ("b", 101)]
        );
        assert_eq!(generator.current_stamp(), 102);
        assert!(Arc::ptr_eq(result.generator(), &generator));
        assert_eq!(
            result
                .materialize_groups()
                .iter()
                .filter_map(|(id, _)| id.as_ref().map(|id| id.name()))
                .collect::<Vec<_>>(),
            vec!["a", "b"]
        );
    }

    #[test]
    fn same_name_variable_export_reuses_identity_and_flags() {
        let original = id("value", 10);
        let target = Ident::new("value", 7, IdentFlags::GLOBAL);
        let result = run(
            module_export(vec![original], vec![Lambda::var(target.clone())]),
            &[],
            Arc::new(IdGenerator::with_start_stamp(20)),
        )
        .unwrap();
        assert_eq!(result.exports().len(), 1);
        assert!(result.exports()[0].same(&target));
        assert_eq!(result.exports()[0].flags(), IdentFlags::GLOBAL);
    }

    #[test]
    fn dce_reports_first_missing_ident_in_reference_set_order() {
        let low = id("low", 4);
        let high = id("high", 9);
        let effect = Lambda::prim(
            Primitive::Pdebugger,
            vec![Lambda::var(low), Lambda::var(high)],
            Location::none(),
        );
        let context = IndexedLambdaContext::from_lambda(effect, []);
        let groups = vec![(None, IndexedGroup::Nop(context.current_root()))];
        let panic = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let _ = remove_dead_groups(context.store(), &[], groups);
        }))
        .unwrap_err();
        let message = panic
            .downcast_ref::<String>()
            .map(String::as_str)
            .or_else(|| panic.downcast_ref::<&str>().copied())
            .unwrap();
        assert_eq!(message, "indexed Lam_dce missing local binding high/9");
    }

    #[test]
    fn dce_skips_global_flags_but_not_stamp_zero_locals() {
        let global = Ident::new("global", 8, IdentFlags::GLOBAL);
        let context = IndexedLambdaContext::from_lambda(
            Lambda::prim(
                Primitive::Pdebugger,
                vec![Lambda::var(global)],
                Location::none(),
            ),
            [],
        );
        let groups = vec![(None, IndexedGroup::Nop(context.current_root()))];
        assert_eq!(remove_dead_groups(context.store(), &[], groups).len(), 1);

        let js = Ident::create_js("Math");
        let context = IndexedLambdaContext::from_lambda(
            Lambda::prim(
                Primitive::Pdebugger,
                vec![Lambda::var(js.clone())],
                Location::none(),
            ),
            [],
        );
        let groups = vec![(None, IndexedGroup::Nop(context.current_root()))];
        assert_eq!(remove_dead_groups(context.store(), &[], groups).len(), 1);
        assert!(!js.is_global());
        assert!(js.is_js());
        assert_eq!(js.flags().bits(), 8);
        for args in [
            vec![Lambda::var(js.clone()), Lambda::var(id("Math", 0))],
            vec![Lambda::var(id("Math", 0)), Lambda::var(js.clone())],
        ] {
            let context = IndexedLambdaContext::from_lambda(
                Lambda::prim(Primitive::Pdebugger, args, Location::none()),
                [],
            );
            let groups = vec![(None, IndexedGroup::Nop(context.current_root()))];
            let panic = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                let _ = remove_dead_groups(context.store(), &[], groups);
            }));
            assert!(panic.is_err());
        }

        let persistent_without_global_flag = id("localStampZero", 0);
        let context = IndexedLambdaContext::from_lambda(
            Lambda::prim(
                Primitive::Pdebugger,
                vec![Lambda::var(persistent_without_global_flag)],
                Location::none(),
            ),
            [],
        );
        let groups = vec![(None, IndexedGroup::Nop(context.current_root()))];
        assert!(
            std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                let _ = remove_dead_groups(context.store(), &[], groups);
            }))
            .is_err()
        );
    }

    #[test]
    fn dce_retains_transitive_alias_dependencies_in_source_order() {
        let first = id("first", 1);
        let second = id("second", 2);
        let mut context = IndexedLambdaContext::from_lambda(Lambda::unit(), []);
        let first_root = context
            .store_mut()
            .append_compat_lambda(Lambda::const_(Constant::int(1)));
        let second_root = context
            .store_mut()
            .append_compat_lambda(Lambda::var(first.clone()));
        let groups = vec![
            (
                Some(first.clone()),
                IndexedGroup::Single(LetKind::Alias, first_root),
            ),
            (
                Some(second.clone()),
                IndexedGroup::Single(LetKind::Alias, second_root),
            ),
        ];
        let kept = remove_dead_groups(context.store(), &[second], groups);
        assert_eq!(
            kept.iter()
                .map(|(id, _)| id.as_ref().unwrap().name())
                .collect::<Vec<_>>(),
            vec!["first", "second"]
        );
    }

    #[test]
    fn dce_visited_membership_uses_ident_same_while_free_sets_keep_flags() {
        for (binding, export) in [
            (
                Ident::new("nonzero", 7, IdentFlags::GLOBAL),
                Ident::new("different", 7, IdentFlags::NONE),
            ),
            (
                Ident::new("stampzero", 0, IdentFlags::PREDEF_EXN),
                Ident::new("stampzero", 0, IdentFlags::NONE),
            ),
        ] {
            assert!(binding.same(&export));
            let mut context = IndexedLambdaContext::from_lambda(Lambda::unit(), []);
            let root = context
                .store_mut()
                .append_compat_lambda(Lambda::const_(Constant::int(1)));
            let groups = vec![(
                Some(binding.clone()),
                IndexedGroup::Single(LetKind::Alias, root),
            )];
            let kept = remove_dead_groups(context.store(), &[export], groups);
            assert_eq!(kept.len(), 1);
            assert_eq!(kept[0].0.as_ref().unwrap().flags(), binding.flags());
        }
    }

    #[test]
    fn coercion_keeps_export_list_set_and_map_as_independent_reference_values() {
        let original_same = id("same", 1);
        let replacement_same = id("same", 11);
        let original_renamed = id("renamed", 2);
        let source = id("source", 12);
        let original_nonvar = id("computed", 3);
        let input = Lambda::let_(
            LetKind::Alias,
            replacement_same.clone(),
            Lambda::unit(),
            Lambda::let_(
                LetKind::Alias,
                source.clone(),
                Lambda::unit(),
                Lambda::let_(
                    LetKind::Alias,
                    original_renamed.clone(),
                    Lambda::const_(Constant::int(9)),
                    module_export(
                        vec![
                            original_same.clone(),
                            original_renamed.clone(),
                            original_nonvar.clone(),
                        ],
                        vec![
                            Lambda::var(replacement_same.clone()),
                            Lambda::var(source),
                            Lambda::const_(Constant::int(7)),
                        ],
                    ),
                ),
            ),
        );
        let mut context = IndexedLambdaContext::from_lambda(
            input,
            vec![
                original_same.clone(),
                original_renamed.clone(),
                original_nonvar.clone(),
            ],
        );
        context.collect_info();
        let generator = IdGenerator::with_start_stamp(100);
        let mut arity = |_: &Ident, _: bool, _: &str| None;
        let (_, export_map) = coerce_and_group(&mut context, &generator, &mut arity).unwrap();
        assert_eq!(
            context
                .metadata()
                .exports
                .iter()
                .map(|id| (id.name(), id.stamp()))
                .collect::<Vec<_>>(),
            vec![("same", 11), ("renamed", 102), ("computed", 101)]
        );
        assert!(context.metadata().export_idents.contains(&replacement_same));
        assert!(!context.metadata().export_idents.contains(&original_same));
        assert!(context.metadata().export_idents.contains(&original_renamed));
        assert!(context.metadata().export_idents.contains(&original_nonvar));
        assert!(
            !context
                .metadata()
                .export_idents
                .contains(&context.metadata().exports[1])
        );
        assert!(
            !context
                .metadata()
                .export_idents
                .contains(&context.metadata().exports[2])
        );
        assert!(export_map.iter().any(|(id, _)| id.same(&original_renamed)));
        assert!(
            export_map
                .iter()
                .any(|(id, _)| id.same(&context.metadata().exports[1]))
        );
        assert!(
            export_map
                .iter()
                .any(|(id, _)| id.same(&context.metadata().exports[2]))
        );
    }

    #[test]
    fn coercion_uses_metadata_exports_and_accepts_any_final_makeblock_tag() {
        let export = id("value", 1);
        let input = Lambda::prim(
            Primitive::Pmakeblock(
                TagInfo::Module(vec!["notExportTag".into()]),
                Mutable::Immutable,
            ),
            vec![Lambda::const_(Constant::int(4))],
            Location::none(),
        );
        let mut inline = |_: &Ident, _: bool, _: &str| None;
        let mut arity = |_: &Ident, _: bool, _: &str| None;
        let result = optimize_for_pre_js_indexed(
            input,
            vec![export],
            &[],
            &AHashSet::new(),
            false,
            Arc::new(IdGenerator::with_start_stamp(10)),
            &mut inline,
            &mut arity,
        )
        .unwrap();
        assert_eq!(result.exports()[0].name(), "value");
    }

    #[test]
    fn duplicate_exports_fail_before_group_ownership() {
        let error = run(
            module_export(
                vec![id("x", 1), id("x", 2)],
                vec![Lambda::unit(), Lambda::unit()],
            ),
            &[],
            Arc::new(IdGenerator::with_start_stamp(2)),
        )
        .err()
        .unwrap();
        assert_eq!(error, IndexedPreJsError::DuplicateExport("x".into()));
    }

    #[test]
    fn hoisted_alias_and_metadata_share_retained_store_roots() {
        let binding = id("make", 3);
        let module = id("A", 1);
        let module_value = Lambda::prim(
            Primitive::Pmakeblock(TagInfo::Module(vec!["make".into()]), Mutable::Immutable),
            vec![Lambda::var(binding.clone())],
            Location::none(),
        );
        let input = Lambda::let_(
            LetKind::Strict,
            binding.clone(),
            Lambda::function_(0, vec![], Lambda::unit(), Default::default()),
            Lambda::let_(
                LetKind::Strict,
                module.clone(),
                module_value,
                module_export(vec![module.clone()], vec![Lambda::var(module.clone())]),
            ),
        );
        let hoisted = HoistedFunction {
            binding,
            path: vec!["A".into(), "make".into()],
            loc: Location::none(),
            target_loc: Location::none(),
        };
        let result = run(
            input,
            &[hoisted],
            Arc::new(IdGenerator::with_start_stamp(20)),
        )
        .unwrap();
        assert!(result.hoisted_warnings.is_empty());
        assert_eq!(
            result.hoisted_exports(),
            &[HoistedExport {
                path: vec!["A".into(), "make".into()],
                export_name: "A$make".into()
            }]
        );
        assert!(result.exports().iter().any(|id| id.name() == "A$make"));
        assert!(!result.context.backend_roots().is_empty());
        assert!(result.storage_measurements().metadata_unique_nodes > 0);
    }

    #[test]
    fn group_effect_reason_is_captured_before_hoisted_aliases() {
        let pure = run(
            module_export(vec![id("pure", 1)], vec![Lambda::unit()]),
            &[],
            Arc::new(IdGenerator::with_start_stamp(5)),
        )
        .unwrap();
        assert_eq!(pure.maybe_pure(), None);

        let effectful = run(
            module_export(
                vec![id("effectful", 1)],
                vec![Lambda::prim(Primitive::Pdebugger, vec![], Location::none())],
            ),
            &[],
            Arc::new(IdGenerator::with_start_stamp(5)),
        )
        .unwrap();
        assert_eq!(effectful.maybe_pure(), Some("effectful"));
    }

    #[test]
    fn required_modules_include_dynamic_and_metadata_only_roots() {
        let export = id("value", 1);
        let dead = id("deadModuleAlias", 2);
        let dep = id("Dep", 0);
        let input = Lambda::let_(
            LetKind::Alias,
            dead,
            Lambda::global_module(dep.clone(), true),
            module_export(vec![export], vec![Lambda::unit()]),
        );
        let extra = ModuleId {
            id: id("Extra", 0),
            kind: Kind::Ml,
            dynamic_import: false,
        };
        let mut extras = AHashSet::new();
        extras.insert(extra.clone());
        let mut inline = |_: &Ident, _: bool, _: &str| None;
        let mut arity = |_: &Ident, _: bool, _: &str| None;
        let exports = extract_export_idents(&input);
        let result = optimize_for_pre_js_indexed(
            input,
            exports,
            &[],
            &extras,
            false,
            Arc::new(IdGenerator::with_start_stamp(5)),
            &mut inline,
            &mut arity,
        )
        .unwrap();
        assert!(result.possible_required_modules().contains(&extra));
        assert!(
            result
                .possible_required_modules()
                .iter()
                .any(|module| module.id.same(&dep) && module.dynamic_import)
        );
        assert_eq!(
            result.storage_measurements(),
            crate::lambda::indexed::IndexedStorageMeasurements {
                node_allocations: 26,
                current_root_edge_visits: 0,
                current_root_unique_nodes: 0,
                metadata_unique_nodes: 0,
                backend_unique_nodes: 1,
                live_unique_nodes: 1,
                superseded_nodes: 25,
                hot_node_occupied_bytes: 208,
                hot_node_capacity_bytes: 256,
                side_payload_shallow_occupied_bytes: 6628,
                side_payload_shallow_capacity_bytes: 8896,
                nested_heap_bytes_included: false,
                current_live_side_payload_shallow_bytes: 0,
                backend_retained_only_side_payload_shallow_bytes: 184,
                metadata_retained_only_side_payload_shallow_bytes: 0,
                superseded_unreachable_side_payload_shallow_bytes: 6444,
            }
        );
    }

    #[test]
    fn cmj_metadata_keeps_constants_and_only_eligible_function_payloads() {
        let null = id("nullValue", 1);
        let always = id("always", 2);
        let ordinary = id("ordinary", 3);
        let input = module_export(
            vec![null, always, ordinary],
            vec![
                Lambda::const_(Constant::JsNull),
                Lambda::function_(
                    1,
                    vec![id("x", 4)],
                    Lambda::unit(),
                    crate::lambda::FunctionAttribute {
                        inline: crate::lambda::InlineAttribute::Always,
                        ..Default::default()
                    },
                ),
                Lambda::function_(1, vec![id("y", 5)], Lambda::unit(), Default::default()),
            ],
        );
        let mut result = run(input, &[], Arc::new(IdGenerator::with_start_stamp(20))).unwrap();
        let mut resolver = |_: &Ident, _: bool, _: &str| None;
        let disabled = result.collect_cmj_exports(false, &mut resolver);
        assert_eq!(
            disabled.constants.get("nullValue"),
            Some(&CmjExportConstant::Null)
        );
        assert!(matches!(
            disabled.arities.get("always"),
            Some(CmjExportArity::Single(arity)) if !arity.first_arity_na()
        ));
        assert_eq!(result.cmj_inline_names(), vec!["nullValue"]);
        let _enabled = result.collect_cmj_exports(true, &mut resolver);
        assert_eq!(result.cmj_inline_names(), vec!["nullValue", "always"]);
        assert_eq!(
            result
                .materialize_cmj_inline_lambdas()
                .into_iter()
                .map(|(name, _)| name)
                .collect::<Vec<_>>(),
            vec!["nullValue", "always"]
        );
    }

    #[test]
    fn cmj_combined_omit_gates_and_constructor_inline_flag_match_reference() {
        let plain = id("plain", 1);
        let alias = id("alias", 2);
        let empty = id("empty", 3);
        let constructor = id("constructor", 4);
        let null = id("null", 5);
        let input = module_export(
            vec![plain, alias, empty, constructor, null],
            vec![
                Lambda::const_(Constant::int(1)),
                Lambda::const_(Constant::ModuleAlias),
                Lambda::prim(
                    Primitive::Pmakeblock(TagInfo::Module(vec![]), Mutable::Immutable),
                    vec![],
                    Location::none(),
                ),
                Lambda::const_(Constant::Constructor(crate::types::VariantTag {
                    name: "Done".into(),
                    tag_type: None,
                })),
                Lambda::const_(Constant::JsNull),
            ],
        );
        let mut result = run(input, &[], Arc::new(IdGenerator::with_start_stamp(20))).unwrap();
        let mut resolver = |_: &Ident, _: bool, _: &str| None;
        let disabled = result.collect_cmj_exports(false, &mut resolver);
        assert_eq!(
            disabled.arities.keys().cloned().collect::<AHashSet<_>>(),
            AHashSet::from_iter(["null".to_string()])
        );
        assert_eq!(result.cmj_inline_names(), vec!["null"]);
        let enabled = result.collect_cmj_exports(true, &mut resolver);
        assert_eq!(
            enabled.arities.keys().cloned().collect::<AHashSet<_>>(),
            AHashSet::from_iter(["constructor".to_string(), "null".to_string()])
        );
        assert_eq!(result.cmj_inline_names(), vec!["constructor", "null"]);
    }

    #[test]
    fn cmj_submodule_external_arity_queries_source_order_then_use_cache() {
        let export = id("submodule", 1);
        let first_module = id("First", 0);
        let second_module = id("Second", 0);
        let field = |module: Ident, dynamic, name: &str| {
            Lambda::prim(
                Primitive::Pfield(0, FieldDbgInfo::Module { name: name.into() }),
                vec![Lambda::global_module(module, dynamic)],
                Location::none(),
            )
        };
        let value = Lambda::prim(
            Primitive::Pmakeblock(
                TagInfo::Module(vec!["a".into(), "b".into()]),
                Mutable::Immutable,
            ),
            vec![
                field(first_module.clone(), false, "a"),
                field(second_module.clone(), true, "b"),
            ],
            Location::none(),
        );
        let input = Lambda::let_(
            LetKind::Strict,
            export.clone(),
            value,
            module_export(vec![export.clone()], vec![Lambda::var(export.clone())]),
        );
        let mut context = IndexedLambdaContext::from_lambda(input, vec![export]);
        context.collect_info();
        let generator = Arc::new(IdGenerator::with_start_stamp(10));
        let mut ignored = |_: &Ident, _: bool, _: &str| None;
        let (groups, export_map) =
            coerce_and_group(&mut context, &generator, &mut ignored).unwrap();
        let roots = groups
            .iter()
            .flat_map(|(_, group)| group.roots())
            .chain(export_map.iter().map(|(_, root)| *root))
            .collect::<Vec<_>>();
        context.register_backend_roots(roots);
        let mut backend = IndexedPreJsBackend {
            context,
            groups,
            export_map,
            hoisted_exports: vec![],
            possible_required_modules: AHashSet::new(),
            maybe_pure: None,
            id_gen: generator,
            hoisted_warnings: vec![],
            cmj_inline_roots: vec![],
            fatal_warnings_pending: false,
        };
        let mut trace = Vec::new();
        let values = {
            let mut resolver = |module: &Ident, dynamic: bool, field: &str| {
                trace.push((module.name().to_string(), dynamic, field.to_string()));
                Some(
                    crate::lambda::lam_compile_context::ExternalArityInfo::Single(
                        crate::lambda::lam_arity::Arity::info(vec![1], false),
                    ),
                )
            };
            backend.collect_cmj_exports(false, &mut resolver)
        };
        assert!(
            matches!(values.arities.get("submodule"), Some(CmjExportArity::Submodule(fields)) if fields.len() == 2 && fields.iter().all(|arity| !arity.first_arity_na()))
        );
        assert_eq!(
            trace,
            vec![
                ("First".into(), false, "a".into()),
                ("Second".into(), true, "b".into())
            ]
        );
        trace.clear();
        {
            let mut resolver = |module: &Ident, dynamic: bool, field: &str| {
                trace.push((module.name().to_string(), dynamic, field.to_string()));
                None
            };
            let _ = backend.collect_cmj_exports(false, &mut resolver);
        }
        assert!(trace.is_empty());
    }

    #[test]
    fn every_misplaced_hoisted_gate_retains_warning_variant_and_location() {
        let binding = id("make", 2);
        let module = id("A", 1);
        let no_group = Ident::new("NoGroup", 0, IdentFlags::GLOBAL);
        let module_value = Lambda::prim(
            Primitive::Pmakeblock(TagInfo::Module(vec!["make".into()]), Mutable::Immutable),
            vec![Lambda::var(binding.clone())],
            Location::none(),
        );
        let input = Lambda::let_(
            LetKind::Strict,
            binding.clone(),
            Lambda::function_(0, vec![], Lambda::unit(), Default::default()),
            Lambda::let_(
                LetKind::Strict,
                module.clone(),
                module_value,
                module_export(
                    vec![module.clone(), no_group.clone()],
                    vec![Lambda::var(module), Lambda::var(no_group)],
                ),
            ),
        );
        let locations = (0..5)
            .map(|index| Location::new_for_error("warnings.res", index, index + 1))
            .collect::<Vec<_>>();
        let items = vec![
            HoistedFunction {
                binding: binding.clone(),
                path: vec![],
                loc: locations[0],
                target_loc: Location::none(),
            },
            HoistedFunction {
                binding: binding.clone(),
                path: vec!["Missing".into(), "make".into()],
                loc: locations[1],
                target_loc: Location::none(),
            },
            HoistedFunction {
                binding: binding.clone(),
                path: vec!["NoGroup".into(), "make".into()],
                loc: locations[2],
                target_loc: Location::none(),
            },
            HoistedFunction {
                binding: binding.clone(),
                path: vec!["A".into(), "absent".into()],
                loc: locations[3],
                target_loc: Location::none(),
            },
            HoistedFunction {
                binding: id("wrong", 99),
                path: vec!["A".into(), "make".into()],
                loc: locations[4],
                target_loc: Location::none(),
            },
        ];
        let result = run(input, &items, Arc::new(IdGenerator::with_start_stamp(100))).unwrap();
        assert_eq!(
            result.hoisted_warnings,
            items
                .iter()
                .map(|item| IndexedHoistedWarning {
                    path: item.path.clone(),
                    loc: item.loc,
                    warning: Warning::MisplacedAttribute {
                        name: "res.hoistedFunction".into(),
                    },
                    is_error: false,
                })
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn hoisted_warning_config_controls_delivery_and_fatal_gate() {
        #[derive(Default)]
        struct Observer(Vec<IndexedHoistedWarning>);
        impl IndexedDiagnosticsObserver for Observer {
            fn lambda(&mut self, _: &'static str, _: Lambda) {}
            fn groups(&mut self, _: Vec<IndexedDiagnosticGroup>) {}
            fn warning(&mut self, warning: &IndexedHoistedWarning) {
                self.0.push(warning.clone());
            }
        }
        let item = HoistedFunction {
            binding: id("missing", 9),
            path: vec!["Missing".into()],
            loc: Location::new_for_error("warning-config.res", 2, 5),
            target_loc: Location::none(),
        };
        let compile = |config: &WarningConfig, observer: &mut Observer| {
            let input = module_export(vec![id("value", 1)], vec![Lambda::unit()]);
            let mut inline = |_: &Ident, _: bool, _: &str| None;
            let mut arity = |_: &Ident, _: bool, _: &str| None;
            optimize_for_pre_js_indexed_with_diagnostics(
                input,
                vec![id("value", 1)],
                std::slice::from_ref(&item),
                &AHashSet::new(),
                false,
                Arc::new(IdGenerator::with_start_stamp(10)),
                &mut inline,
                &mut arity,
                config,
                Some(observer),
            )
        };

        let mut disabled = WarningConfig::new();
        disabled.parse("-53").unwrap();
        let mut observer = Observer::default();
        let result = compile(&disabled, &mut observer).unwrap();
        assert!(result.hoisted_warnings().is_empty());
        assert!(observer.0.is_empty());

        let enabled = WarningConfig::new();
        let mut observer = Observer::default();
        let result = compile(&enabled, &mut observer).unwrap();
        assert_eq!(observer.0, result.hoisted_warnings());
        assert_eq!(observer.0[0].warning.number(), 53);
        assert_eq!(
            observer.0[0].warning.message(),
            "the @res.hoistedFunction attribute cannot appear in this context"
        );
        assert_eq!(observer.0[0].loc, item.loc);
        assert!(!observer.0[0].is_error);

        let mut fatal = WarningConfig::new();
        fatal.parse_as_error("@53").unwrap();
        let mut observer = Observer::default();
        let result = compile(&fatal, &mut observer).unwrap();
        assert_eq!(
            result.check_fatal_warnings(),
            Err(IndexedPreJsError::FatalWarnings)
        );
        assert!(observer.0[0].is_error);
    }

    #[test]
    fn hoisted_name_collision_preserves_the_reference_error_gate() {
        let binding = id("make", 2);
        let module = id("A", 1);
        let occupied = id("A$make", 3);
        let module_value = Lambda::prim(
            Primitive::Pmakeblock(TagInfo::Module(vec!["make".into()]), Mutable::Immutable),
            vec![Lambda::var(binding.clone())],
            Location::none(),
        );
        let input = Lambda::let_(
            LetKind::Strict,
            occupied.clone(),
            Lambda::function_(0, vec![], Lambda::unit(), Default::default()),
            Lambda::let_(
                LetKind::Strict,
                binding.clone(),
                Lambda::function_(0, vec![], Lambda::unit(), Default::default()),
                Lambda::let_(
                    LetKind::Strict,
                    module.clone(),
                    module_value,
                    module_export(
                        vec![module.clone(), occupied.clone()],
                        vec![Lambda::var(module), Lambda::var(occupied)],
                    ),
                ),
            ),
        );
        let hoisted_loc = Location::new_for_error("hoisted.res", 1, 2);
        let target_loc = Location::new_for_error("hoisted.res", 10, 20);
        let hoisted = HoistedFunction {
            binding,
            path: vec!["A".into(), "make".into()],
            loc: hoisted_loc,
            target_loc,
        };
        assert_eq!(
            run(
                input,
                &[hoisted],
                Arc::new(IdGenerator::with_start_stamp(20))
            )
            .err()
            .unwrap(),
            IndexedPreJsError::HoistedNameCollision {
                name: "A$make".into(),
                loc: target_loc,
            }
        );
    }

    #[test]
    fn hoisted_nonfunction_collision_uses_attribute_location() {
        let binding = id("make", 2);
        let module = id("A", 1);
        let occupied = id("A$make", 3);
        let mut context = IndexedLambdaContext::from_lambda(Lambda::unit(), [module.clone()]);
        let target = context
            .store_mut()
            .append_compat_lambda(Lambda::const_(Constant::int(1)));
        let target_var = context
            .store_mut()
            .append(NodeSnapshot::Var(binding.clone()));
        let module_root = context.store_mut().append(NodeSnapshot::Prim(
            Primitive::Pmakeblock(TagInfo::Module(vec!["make".into()]), Mutable::Immutable),
            vec![target_var],
            Location::none(),
        ));
        let occupied_root = context
            .store_mut()
            .append_compat_lambda(Lambda::const_(Constant::int(2)));
        let mut groups = vec![
            (
                Some(binding.clone()),
                IndexedGroup::Single(LetKind::Strict, target),
            ),
            (
                Some(module),
                IndexedGroup::Single(LetKind::Strict, module_root),
            ),
            (
                Some(occupied),
                IndexedGroup::Single(LetKind::Strict, occupied_root),
            ),
        ];
        let mut export_map = Vec::new();
        let hoisted_loc = Location::new_for_error("nonfunction.res", 3, 7);
        #[derive(Default)]
        struct Observer(Vec<IndexedHoistedWarning>);
        impl IndexedDiagnosticsObserver for Observer {
            fn lambda(&mut self, _: &'static str, _: Lambda) {}
            fn groups(&mut self, _: Vec<IndexedDiagnosticGroup>) {}
            fn warning(&mut self, warning: &IndexedHoistedWarning) {
                self.0.push(warning.clone());
            }
        }
        let missing_loc = Location::new_for_error("nonfunction.res", 1, 2);
        let mut observer = Observer::default();
        let mut diagnostics: Option<&mut dyn IndexedDiagnosticsObserver> = Some(&mut observer);
        let error = add_hoisted_aliases(
            &mut context,
            &mut groups,
            &mut export_map,
            &[
                HoistedFunction {
                    binding: id("missing", 99),
                    path: vec!["Missing".into()],
                    loc: missing_loc,
                    target_loc: Location::none(),
                },
                HoistedFunction {
                    binding: binding.clone(),
                    path: vec!["A".into(), "make".into()],
                    loc: hoisted_loc,
                    target_loc: Location::new_for_error("nonfunction.res", 20, 30),
                },
            ],
            &IdGenerator::with_start_stamp(10),
            &WarningConfig::new(),
            &mut diagnostics,
        )
        .unwrap_err();
        assert_eq!(
            error,
            IndexedPreJsError::HoistedNameCollision {
                name: "A$make".into(),
                loc: hoisted_loc,
            }
        );
        assert_eq!(observer.0.len(), 1);
        assert_eq!(observer.0[0].loc, missing_loc);
        assert_eq!(observer.0[0].warning.number(), 53);

        let mut reverse_observer = Observer::default();
        let mut reverse_diagnostics: Option<&mut dyn IndexedDiagnosticsObserver> =
            Some(&mut reverse_observer);
        let reverse = add_hoisted_aliases(
            &mut context,
            &mut groups,
            &mut export_map,
            &[
                HoistedFunction {
                    binding,
                    path: vec!["A".into(), "make".into()],
                    loc: hoisted_loc,
                    target_loc: Location::new_for_error("nonfunction.res", 20, 30),
                },
                HoistedFunction {
                    binding: id("missing", 99),
                    path: vec!["Missing".into()],
                    loc: missing_loc,
                    target_loc: Location::none(),
                },
            ],
            &IdGenerator::with_start_stamp(10),
            &WarningConfig::new(),
            &mut reverse_diagnostics,
        );
        assert_eq!(
            reverse.unwrap_err(),
            IndexedPreJsError::HoistedNameCollision {
                name: "A$make".into(),
                loc: hoisted_loc,
            }
        );
        assert!(reverse_observer.0.is_empty());
    }

    #[test]
    fn hoisted_group_order_is_reverse_source_but_cmj_metadata_is_source_order() {
        let first = id("first", 2);
        let second = id("second", 3);
        let module = id("A", 1);
        let module_value = Lambda::prim(
            Primitive::Pmakeblock(
                TagInfo::Module(vec!["first".into(), "second".into()]),
                Mutable::Immutable,
            ),
            vec![Lambda::var(first.clone()), Lambda::var(second.clone())],
            Location::none(),
        );
        let input = Lambda::let_(
            LetKind::Strict,
            first.clone(),
            Lambda::function_(0, vec![], Lambda::unit(), Default::default()),
            Lambda::let_(
                LetKind::Strict,
                second.clone(),
                Lambda::function_(0, vec![], Lambda::unit(), Default::default()),
                Lambda::let_(
                    LetKind::Strict,
                    module.clone(),
                    module_value,
                    module_export(vec![module.clone()], vec![Lambda::var(module)]),
                ),
            ),
        );
        let make = |binding, field: &str| HoistedFunction {
            binding,
            path: vec!["A".into(), field.into()],
            loc: Location::none(),
            target_loc: Location::none(),
        };
        let result = run(
            input,
            &[make(first, "first"), make(second, "second")],
            Arc::new(IdGenerator::with_start_stamp(20)),
        )
        .unwrap();
        assert_eq!(
            result
                .exports()
                .iter()
                .rev()
                .take(2)
                .map(|id| id.name())
                .collect::<Vec<_>>(),
            vec!["A$first", "A$second"]
        );
        assert_eq!(
            result
                .hoisted_exports()
                .iter()
                .map(|entry| entry.export_name.as_str())
                .collect::<Vec<_>>(),
            vec!["A$first", "A$second"]
        );
    }

    #[test]
    fn diagnostics_observer_receives_every_reference_pass_label_and_groups() {
        #[derive(Default)]
        struct Observer {
            labels: Vec<&'static str>,
            groups: usize,
        }
        impl IndexedDiagnosticsObserver for Observer {
            fn lambda(&mut self, pass: &'static str, _lambda: Lambda) {
                self.labels.push(pass);
            }
            fn groups(&mut self, groups: Vec<IndexedDiagnosticGroup>) {
                self.groups = groups.len();
            }
        }
        let input = module_export(vec![id("value", 1)], vec![Lambda::unit()]);
        let mut inline = |_: &Ident, _: bool, _: &str| None;
        let mut arity = |_: &Ident, _: bool, _: &str| None;
        let mut observer = Observer::default();
        optimize_for_pre_js_indexed_with_diagnostics(
            input,
            vec![id("value", 1)],
            &[],
            &AHashSet::new(),
            false,
            Arc::new(IdGenerator::with_start_stamp(10)),
            &mut inline,
            &mut arity,
            &WarningConfig::new(),
            Some(&mut observer),
        )
        .unwrap();
        assert_eq!(
            observer.labels,
            vec![
                "initial",
                "flatten0",
                "flatten1",
                "simplify_exits",
                "simplify_alias",
                "flatten2",
                "alpha_before",
                "alpha_after",
                "simplify_alias_before",
                "alpha_conversion",
                "before-simplify_lets",
                "before-simplify-exits",
                "simplify_lets",
            ]
        );
        assert_eq!(observer.groups, 1);
    }

    #[test]
    fn diagnostic_group_materialization_preserves_every_group_kind() {
        let exotic = Ident::new("\\\"odd-name\"", 1, IdentFlags::GLOBAL);
        let recursive = id("recursive", 2);
        let mut context = IndexedLambdaContext::from_lambda(Lambda::unit(), []);
        let single = context.store_mut().append_compat_lambda(Lambda::prim(
            Primitive::Pidentity,
            vec![Lambda::var(exotic.clone())],
            Location::new_for_error("groups.res", 4, 8),
        ));
        let rec_root = context.store_mut().append_compat_lambda(Lambda::function_(
            0,
            vec![],
            Lambda::unit(),
            Default::default(),
        ));
        let nop = context.store_mut().append_compat_lambda(Lambda::Lbreak);
        let groups = vec![
            (
                Some(exotic.clone()),
                IndexedGroup::Single(LetKind::Alias, single),
            ),
            (
                None,
                IndexedGroup::Recursive(vec![(recursive.clone(), rec_root)]),
            ),
            (None, IndexedGroup::Nop(nop)),
        ];
        let materialized = materialize_diagnostic_groups(&context, &groups);
        match &materialized[..] {
            [
                IndexedDiagnosticGroup::Single(LetKind::Alias, id, Lambda::Lprim(info)),
                IndexedDiagnosticGroup::Recursive(bindings),
                IndexedDiagnosticGroup::Nop(Lambda::Lbreak),
            ] => {
                assert_eq!(
                    (id.name(), id.stamp(), id.is_global()),
                    ("\\\"odd-name\"", 1, true)
                );
                assert_eq!(info.loc, Location::new_for_error("groups.res", 4, 8));
                assert_eq!(bindings[0].0, recursive);
            }
            _ => panic!("unexpected diagnostic groups"),
        }
    }

    #[test]
    fn empty_grouped_output_consumes_the_optimizer_root_authority() {
        let export = Ident::new("value", 1, IdentFlags::GLOBAL);
        let input = module_export(vec![export.clone()], vec![Lambda::var(export)]);
        let result = run(input, &[], Arc::new(IdGenerator::with_start_stamp(2))).unwrap();
        assert!(result.groups.is_empty());
        assert!(result.context.backend_roots().is_empty());
        assert!(
            std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                let _ = result.context.materialize();
            }))
            .is_err()
        );
        assert_eq!(
            result.storage_measurements(),
            crate::lambda::indexed::IndexedStorageMeasurements {
                node_allocations: 14,
                current_root_edge_visits: 0,
                current_root_unique_nodes: 0,
                metadata_unique_nodes: 0,
                backend_unique_nodes: 0,
                live_unique_nodes: 0,
                superseded_nodes: 14,
                hot_node_occupied_bytes: 112,
                hot_node_capacity_bytes: 128,
                side_payload_shallow_occupied_bytes: 5908,
                side_payload_shallow_capacity_bytes: 7360,
                nested_heap_bytes_included: false,
                current_live_side_payload_shallow_bytes: 0,
                backend_retained_only_side_payload_shallow_bytes: 0,
                metadata_retained_only_side_payload_shallow_bytes: 0,
                superseded_unreachable_side_payload_shallow_bytes: 5908,
            }
        );
    }

    #[test]
    fn moving_owner_preserves_store_metadata_and_generator_identity() {
        fn move_boundary(value: IndexedPreJsBackend) -> IndexedPreJsBackend {
            value
        }
        let generator = Arc::new(IdGenerator::with_start_stamp(4));
        let before = run(
            module_export(vec![id("x", 1)], vec![Lambda::unit()]),
            &[],
            generator.clone(),
        )
        .unwrap();
        let nodes = before.storage_measurements().node_allocations;
        let after = move_boundary(before);
        assert_eq!(after.storage_measurements().node_allocations, nodes);
        assert!(Arc::ptr_eq(after.generator(), &generator));
        let fresh = after.generator().create("later");
        assert_eq!(fresh.stamp(), generator.current_stamp());
    }
}
