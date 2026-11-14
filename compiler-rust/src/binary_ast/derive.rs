//! The single seam for built-in derives. Deleting `spice_ppx` means deleting
//! the bodies here, returning unchanged items and `false` for mapper detection.

/// Optional derived-code measurement, owned by one compilation.
pub mod census;
#[cfg(test)]
pub(crate) mod fixtures;
/// The plan of a derived item, stored in the `ParseArena`.
pub mod plan;
mod shape;
pub(super) use shape::record as record_shapes;

use crate::parse_arena::ParseArena;
use crate::parser::ast::{RecFlag, SignatureItem, StructureItem, StructureItemDesc};
use plan::DerivedIdx;

/// First unsupported form in declaration traversal order, after Q5 exclusions.
/// One byte carried with a classification; no names or allocated payloads.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum UnplannedForm {
    /// Identity codec of JSON.t.
    JsonIdentity,
    /// User codec with type arguments.
    AppliedUserCodec,
    /// A functor application in a type path.
    AppliedModulePath,
    /// A type form without a codec plan.
    UnsupportedType,
    /// A constant fallback on the declaration.
    ConstantFallback,
    /// A record with no fields.
    EmptyRecord,
    /// A template key or default rather than a literal node.
    TemplateLiteral,
    /// A manifest record or another unsupported declaration shape.
    DeclarationShape,
}

/// Why a derived declaration stays on the general path: the rows of the
/// table in `compiler-rust/docs/DERIVED_CODECS.md`, Q5, and the shapes later
/// slices plan.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum GeneralReason {
    /// `@spice.codec(e)` on a type of the declaration: a user expression.
    CustomCodec,
    /// `@spice.default`, `@spice.key` or `@spice.fallback` whose payload is
    /// not a constant: a user expression that can capture the body's binders.
    UserExpression,
    /// The declaration has type parameters.
    TypeParameters,
    /// The declaration is in a recursive group.
    RecursiveGroup,
    /// Two declarations of the group share a label or a constructor name.
    SharedNames,
    /// A `@spice.serde` declaration, a polymorphic variant or a tuple: not
    /// among the measured shapes.
    UnmeasuredShape,
    /// An `@unboxed` declaration.
    Unboxed,
    /// A record or constructor application needing forms not yet planned.
    NotYetPlanned(UnplannedForm),
    /// A variant with a representation, attribute or payload codec outside
    /// the plan language; classify it before checking rather than retrying.
    UnsupportedVariant,
    /// An exposed JSON identity argument needs application abbreviation inference.
    JsonIdentityArgument,
    /// A preceding local constructor shadows Ok or Error used by the decoder.
    ShadowedResultConstructor,
    /// Plans are off for the tree: the switch `RESCRIPT_DERIVED_PATH=general`,
    /// or a tree that is stored or printed instead of compiled.
    Switch,
    /// An obligation of a plan of the unit failed in the checker, and the
    /// unit is compiled again with every declaration on the general path.
    FailedObligation,
}

impl GeneralReason {
    /// Dense census bucket, shared by counts and timing. Cost: O(1).
    pub(crate) fn census_index(self) -> usize {
        match self {
            Self::CustomCodec => 0,
            Self::UserExpression => 1,
            Self::TypeParameters => 2,
            Self::RecursiveGroup => 3,
            Self::SharedNames => 4,
            Self::UnmeasuredShape => 5,
            Self::Unboxed => 6,
            Self::NotYetPlanned(_) => 7,
            Self::UnsupportedVariant => 8,
            Self::Switch => 9,
            Self::FailedObligation => 10,
            Self::JsonIdentityArgument => 11,
            Self::ShadowedResultConstructor => 12,
        }
    }
}

/// The path a derived declaration takes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Classification {
    /// The declaration reaches the checker and the backend as a plan.
    Plan,
    /// The declaration is expanded to syntax, as before plans.
    General(GeneralReason),
}

/// How many derived bindings took each path, for the census.
#[derive(Debug, Clone, Copy, Default, serde::Serialize)]
pub struct PathCounts {
    /// Bindings of items that are plans.
    pub plan: u64,
    /// Bindings on the general path, per reason.
    pub custom_codec: u64,
    /// See [`GeneralReason::UserExpression`].
    pub user_expression: u64,
    /// See [`GeneralReason::TypeParameters`].
    pub type_parameters: u64,
    /// See [`GeneralReason::RecursiveGroup`].
    pub recursive_group: u64,
    /// See [`GeneralReason::SharedNames`].
    pub shared_names: u64,
    /// See [`GeneralReason::UnmeasuredShape`].
    pub unmeasured_shape: u64,
    /// See [`GeneralReason::Unboxed`].
    pub unboxed: u64,
    /// See [`GeneralReason::NotYetPlanned`].
    pub not_yet_planned: u64,
    /// Counts indexed by `UnplannedForm`, exactly one per unplanned binding.
    pub unplanned_forms: [u64; 8],
    /// See [`GeneralReason::UnsupportedVariant`].
    pub unsupported_variant: u64,
    /// See [`GeneralReason::JsonIdentityArgument`].
    pub json_identity_argument: u64,
    /// See [`GeneralReason::ShadowedResultConstructor`].
    pub shadowed_result_constructor: u64,
    /// See [`GeneralReason::Switch`].
    pub switch: u64,
    /// See [`GeneralReason::FailedObligation`].
    pub failed_obligation: u64,
}

impl PathCounts {
    /// Add the counts of another group. Cost: O(1).
    pub fn merge(&mut self, other: PathCounts) {
        self.plan += other.plan;
        self.custom_codec += other.custom_codec;
        self.user_expression += other.user_expression;
        self.type_parameters += other.type_parameters;
        self.recursive_group += other.recursive_group;
        self.shared_names += other.shared_names;
        self.unmeasured_shape += other.unmeasured_shape;
        self.unboxed += other.unboxed;
        self.not_yet_planned += other.not_yet_planned;
        for (count, increment) in self.unplanned_forms.iter_mut().zip(other.unplanned_forms) {
            *count += increment;
        }
        self.unsupported_variant += other.unsupported_variant;
        self.json_identity_argument += other.json_identity_argument;
        self.shadowed_result_constructor += other.shadowed_result_constructor;
        self.switch += other.switch;
        self.failed_obligation += other.failed_obligation;
    }

    /// Count `bindings` bindings of one classification. Cost: O(1).
    pub fn add(&mut self, classification: Classification, bindings: u64) {
        let counter = match classification {
            Classification::Plan => &mut self.plan,
            Classification::General(reason) => match reason {
                GeneralReason::CustomCodec => &mut self.custom_codec,
                GeneralReason::UserExpression => &mut self.user_expression,
                GeneralReason::TypeParameters => &mut self.type_parameters,
                GeneralReason::RecursiveGroup => &mut self.recursive_group,
                GeneralReason::SharedNames => &mut self.shared_names,
                GeneralReason::UnmeasuredShape => &mut self.unmeasured_shape,
                GeneralReason::Unboxed => &mut self.unboxed,
                GeneralReason::NotYetPlanned(form) => {
                    self.unplanned_forms[form as usize] += bindings;
                    &mut self.not_yet_planned
                },
                GeneralReason::UnsupportedVariant => &mut self.unsupported_variant,
                GeneralReason::JsonIdentityArgument => &mut self.json_identity_argument,
                GeneralReason::ShadowedResultConstructor => &mut self.shadowed_result_constructor,
                GeneralReason::Switch => &mut self.switch,
                GeneralReason::FailedObligation => &mut self.failed_obligation,
            },
        };
        *counter += bindings;
    }
}

/// Classify one type declaration that derives codecs: a plan, or the general
/// path with its reason. `shares_names` says whether two declarations of its
/// group share a label or constructor name ([`group_shares_names`]).
/// Cost: O(type nodes and attributes of the declaration); no allocation.
pub fn classify(
    arena: &ParseArena,
    decl: &crate::parser::ast::TypeDeclaration,
    rec_flag: RecFlag,
    shares_names: bool,
) -> Classification {
    super::spice_ppx::plan::classify(arena, decl, rec_flag, shares_names)
}

/// Whether two declarations of a group share a label or constructor name.
/// Cost: O(n log n) for the n labels and constructors of the group.
pub fn group_shares_names(
    arena: &ParseArena,
    group: &[crate::parser::ast::TypeDeclaration],
) -> bool {
    super::spice_ppx::plan::group_shares_names(group, arena)
}

/// The names a planned item resolves in the environment of its declaration:
/// one per obligation, in typing order. The modules they are qualified with
/// are the modules the item depends on.
/// Cost: O(1) to obtain; one slot read per obligation yielded.
pub fn free_names(
    arena: &ParseArena,
    idx: DerivedIdx,
) -> impl Iterator<Item = crate::parse_arena::LidentIdx> + '_ {
    let plans = arena.plans();
    plans
        .bindings(plans.item(idx))
        .iter()
        .flat_map(|binding| binding.obligations.range())
        .filter_map(move |slot| plans.obligation(plan::ObligationIdx(slot as u32)).name())
}

/// The names of the values a planned item uses: what the identifier
/// expressions of its syntax would name, in typing order.
/// Cost: O(1) to obtain; one slot read per obligation of the item.
pub fn value_names(
    arena: &ParseArena,
    idx: DerivedIdx,
) -> impl Iterator<Item = crate::parse_arena::LidentIdx> + '_ {
    let plans = arena.plans();
    plans
        .bindings(plans.item(idx))
        .iter()
        .flat_map(|binding| binding.obligations.range())
        .filter_map(move |slot| match plans.obligation(plan::ObligationIdx(slot as u32)) {
            plan::Obligation::Value { name, .. } => Some(name),
            plan::Obligation::Type { .. }
            | plan::Obligation::Label { .. }
            | plan::Obligation::Constructor { .. }
            | plan::Obligation::Literal { .. }
            | plan::Obligation::Equal { .. } | plan::Obligation::NotJsonIdentity { .. } => None,
        })
}

/// What a planned item stands for is not in its tree: the walks that store
/// or print syntax run on trees the seam was told not to plan
/// (`ParseArena::set_derived_plans`).
pub(crate) const NO_SYNTAX: &str =
    "a tree that is stored or printed is derived without plans";

/// Detect derives in a structure. O(items and visited attributes), delegating to
/// the existing mapper scan; no additional traversal.
pub fn structure_uses_spice_mapper(items: &[StructureItem], arena: &ParseArena) -> bool {
    super::spice_ppx::structure_uses_spice_mapper(items, arena)
}

/// Index learned by the existing mapper-presence scan; stops at the first
/// deriving item. O(visited items and attributes), no allocation.
pub(crate) fn first_spice_item(items: &[StructureItem], arena: &ParseArena) -> Option<usize> {
    super::spice_ppx::first_spice_item(items, arena)
}

/// Detect derives in a signature. O(items and visited attributes), delegating to
/// the existing mapper scan; no additional traversal.
pub fn signature_uses_spice_mapper(items: &[SignatureItem], arena: &ParseArena) -> bool {
    super::spice_ppx::signature_uses_spice_mapper(items, arena)
}

/// Expand built-in derives on a structure item. O(generated syntax plus mapper
/// work), with O(1) timing overhead only when the census is enabled.
pub fn expand_structure_item_with_mapper(item: &StructureItem, arena: &mut ParseArena, active: bool) -> Result<Vec<StructureItem>, String> {
    expand_structure_item_in_scope(item, arena, active, Scope { result_shadowed: active && shadows_result(item, arena), ..Scope::default() })
}

/// Per-arena test instrumentation, erased entirely from production builds.
#[cfg(test)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct ScopeSteps {
    pub prefix_items: usize,
    pub shadow_items: usize,
    pub constructors: usize,
    pub nested_items: usize,
    pub presence_items: usize,
}

/// Borrowed source-order facts. A position is necessary because the frontend
/// may map items backwards after collecting a later prefix.
#[derive(Clone, Copy, Default)]
pub struct Scope<'a> {
    /// A preceding declaration shadows a predefined result constructor.
    pub result_shadowed: bool,
    pub(super) opaque_imports: bool,
    pub(super) prefix: Option<(&'a PrefixScope<'a>, usize)>,
}

impl Scope<'_> {
    /// O(1): an expression-level open hides inherited syntax facts from a
    /// module body below it. Restoring the previous scope restores those facts.
    pub(crate) fn after_open(self) -> Self {
        Self { result_shadowed: self.result_shadowed, opaque_imports: true, prefix: None }
    }

    /// O(name bytes + alias-version/scope depth), using canonical spelling
    /// slots and borrowed strings; no string allocation.
    pub(crate) fn is_json_identity(self, lid: crate::parse_arena::LidentIdx, arena: &ParseArena) -> bool {
        self.identity_fact(lid, arena) == Some(true)
    }

    /// Syntactically known JSON/non-JSON declaration, or unresolved. Import
    /// epochs invalidate builtin spellings too: none are assumed immune to
    /// rebinding here. A subsequent concrete declaration establishes a new fact.
    /// Epoch checks cost O(1) per scope level, with no additional source scan.
    pub(crate) fn identity_fact(self, lid: crate::parse_arena::LidentIdx, arena: &ParseArena) -> Option<bool> {
        if super::spice_ppx::is_json_identifier(lid, arena) {
            return (!self.opaque_imports).then_some(true);
        }
        let crate::parser::Longident::Lident(name) = arena.get_longident(lid) else { return None };
        let fact = match arena.find_interned_string(arena.get_string(*name)) {
            Some(canonical) => self.alias(canonical.raw() as usize),
            None if self.opaque_imports => AliasFact::Unknown,
            None => AliasFact::Unbound,
        };
        match fact {
            AliasFact::Known(identity) => Some(identity),
            AliasFact::Unknown => None,
            AliasFact::Unbound => match arena.get_string(*name) {
                "int" | "float" | "string" | "bool" | "unit" | "char" | "array" | "list" | "option" | "result" | "dict" => Some(false),
                _ => None,
            },
        }
    }

    fn alias(self, name: usize) -> AliasFact {
        let Some((prefix, position)) = self.prefix else {
            return if self.opaque_imports { AliasFact::Unknown } else { AliasFact::Unbound };
        };
        let epoch = prefix.facts[position].import_epoch;
        let mut slot = prefix.names.get(name).copied().unwrap_or(0);
        while slot != 0 {
            let entry = &prefix.aliases[slot as usize - 1];
            if entry.position <= position {
                if epoch != NO_IMPORT && entry.position < epoch { return AliasFact::Unknown; }
                return entry.identity.map_or(AliasFact::Unknown, AliasFact::Known);
            }
            slot = entry.previous;
        }
        if epoch != NO_IMPORT { AliasFact::Unknown } else { prefix.parent.alias(name) }
    }
}

enum AliasFact {
    Known(bool),
    Unknown,
    Unbound,
}

const NO_IMPORT: usize = usize::MAX;

// The existing dense prefix rows also snapshot the latest import position.
// One current epoch alone cannot answer reverse-order queries across multiple
// imports. This adds no per-item allocation and keeps epoch queries O(1).
struct PrefixFacts {
    shadowed: bool,
    import_epoch: usize,
}

struct Alias {
    position: usize,
    previous: u32,
    identity: Option<bool>,
}

/// Dense prefix facts and a flat version pool, shared by constructor and alias
/// classification. No per-item allocation; a nested scope borrows its parent.
pub(crate) struct PrefixScope<'a> {
    parent: Scope<'a>,
    facts: Vec<PrefixFacts>,
    latest_import: usize,
    names: Vec<u32>,
    aliases: Vec<Alias>,
}

impl Default for PrefixScope<'_> {
    fn default() -> Self {
        Self { parent: Scope::default(), facts: Vec::new(), latest_import: NO_IMPORT,
            names: Vec::new(), aliases: Vec::new() }
    }
}

impl<'a> PrefixScope<'a> {
    pub(crate) fn new(parent: Scope<'a>) -> Self { Self { parent, ..Self::default() } }
    pub(crate) fn len(&self) -> usize { self.facts.len() }
    pub(crate) fn at(&self, position: usize) -> Scope<'_> {
        Scope { result_shadowed: self.facts[position].shadowed,
            opaque_imports: self.facts[position].import_epoch != NO_IMPORT || self.parent.opaque_imports,
            prefix: Some((self, position)) }
    }

    /// O(constructors + declarations + newly allocated name slots). Each
    /// declaration appends one version; only its immediate manifest is read.
    pub(crate) fn push(&mut self, item: &StructureItem, arena: &mut ParseArena) {
        #[cfg(test)]
        {
            let mut steps = arena.derived_scope_steps.get();
            steps.prefix_items += 1;
            arena.derived_scope_steps.set(steps);
        }
        let position = self.len();
        let own_shadow = shadows_result(item, arena);
        let shadowed = self.facts.last().map_or(self.parent.result_shadowed, |fact| fact.shadowed)
            || own_shadow;
        if matches!(item.pstr_desc, StructureItemDesc::Pstr_open(_) | StructureItemDesc::Pstr_include(_)) {
            self.latest_import = position;
        }
        self.facts.push(PrefixFacts { shadowed, import_epoch: self.latest_import });
        if let StructureItemDesc::Pstr_type(group) = &item.pstr_desc {
            self.names.resize(self.names.len().max(arena.string_count()), 0);
            for decl in &group.1 {
                let identity = if !decl.ptype_params.is_empty() {
                    None
                } else if let Some(ty) = decl.ptype_manifest {
                    match &arena.get_core_type(ty).ptyp_desc {
                        crate::parser::ast::CoreTypeDesc::Ptyp_constr((lid, args)) if args.is_empty() =>
                            self.at(position).identity_fact(lid.txt, arena),
                        crate::parser::ast::CoreTypeDesc::Ptyp_constr((lid, _)) =>
                            self.at(position).identity_fact(lid.txt, arena).filter(|identity| !identity),
                        _ => None,
                    }
                } else { Some(false) };
                let name = arena.intern_existing_string(decl.ptype_name.txt).raw() as usize;
                let previous = self.names[name];
                self.aliases.push(Alias { position, previous, identity });
                self.names[name] = self.aliases.len() as u32;
            }
        }
    }
}

/// Whether this item introduces a local result-constructor name.
/// Cost: O(constructors), borrowed name comparisons and no allocation.
pub(crate) fn shadows_result(item: &StructureItem, arena: &ParseArena) -> bool {
    #[cfg(test)]
    {
        let mut steps = arena.derived_scope_steps.get();
        steps.shadow_items += 1;
        arena.derived_scope_steps.set(steps);
    }
    let is_result = |name| {
        #[cfg(test)]
        {
            let mut steps = arena.derived_scope_steps.get();
            steps.constructors += 1;
            arena.derived_scope_steps.set(steps);
        }
        matches!(arena.get_string(name), "Ok" | "Error")
    };
    match &item.pstr_desc {
        StructureItemDesc::Pstr_type(group) => group.1.iter().any(|decl| match &decl.ptype_kind {
            crate::parser::ast::TypeKind::Ptype_variant(constructors) =>
                constructors.iter().any(|c| is_result(c.pcd_name.txt)),
            _ => false,
        }),
        StructureItemDesc::Pstr_exception(constructor) => is_result(constructor.pext_name.txt),
        StructureItemDesc::Pstr_typext(extension) => extension.ptyext_constructors.iter()
            .any(|c| is_result(c.pext_name.txt)),
        _ => false,
    }
}

/// Expand with the constructor scope determined in source order.
/// Cost: the same mapper work as the unscoped entry point.
pub fn expand_structure_item_in_scope(
    item: &StructureItem,
    arena: &mut ParseArena,
    active: bool,
    scope: Scope<'_>,
) -> Result<Vec<StructureItem>, String> {
    // O(1) disabled probe: retain the direct call without saving profiling state
    // across a mapper that mutably borrows the arena.
    if arena.derived_census.is_none() {
        return super::spice_ppx::expand_structure_item_in_scope(item, arena, active, scope);
    }
    expand_with_census(item, arena, active, scope)
}

/// O(1) census bookkeeping plus the existing expansion and optional key encoder.
/// Keeping this cold leaves no profiling locals in the ordinary mapper's frame.
#[cold]
#[inline(never)]
fn expand_with_census(
    item: &StructureItem,
    arena: &mut ParseArena,
    active: bool,
    scope: Scope<'_>,
) -> Result<Vec<StructureItem>, String> {
    let start = census::start(true);
    let observer_before = arena.derived_census.as_ref().map_or(0, |c| c.observer_ns);
    let result = super::spice_ppx::expand_structure_item_in_scope(item, arena, active, scope);
    if let (Some(start), Some(census)) = (start, arena.derived_census.as_mut()) {
        census.generation.add(active, census::nanos(start.elapsed()).saturating_sub(census.observer_ns - observer_before));
    }
    result
}

/// Expand built-in derives on a signature item. O(generated declarations plus
/// mapper work); no additional traversal.
pub fn expand_signature_item_with_mapper(
    item: &SignatureItem,
    arena: &mut ParseArena,
    active: bool,
) -> Result<Vec<SignatureItem>, String> {
    super::spice_ppx::expand_signature_item_with_mapper(item, arena, active)
}

/// Record provenance at generation, including derives inside nested modules.
/// All structure items produced by the builtin derive are value groups.
/// Cost: one tag test and one bitmap write; growing the bitmap zeroes only
/// newly reached binding-pool words (one word per 64 binding slots).
pub(super) fn mark_generated_item(item: &StructureItem, arena: &mut ParseArena) {
    if let crate::parser::ast::StructureItemDesc::Pstr_value((_, bindings)) = item.pstr_desc {
        arena.mark_derived_value_group(bindings);
    }
}

/// Generic provenance query; consumers need not know which derive produced it.
/// Cost: O(1), one tag test and at most one bitmap-word read; no allocation,
/// hashing, synchronization or traversal.
pub fn is_derived_item(item: &StructureItem, arena: &ParseArena) -> bool {
    match item.pstr_desc {
        StructureItemDesc::Pstr_value((_, bindings)) => arena.is_derived_value_group(bindings),
        StructureItemDesc::Pstr_derived(_) => true,
        StructureItemDesc::Pstr_eval(_)
        | StructureItemDesc::Pstr_primitive(_)
        | StructureItemDesc::Pstr_type(_)
        | StructureItemDesc::Pstr_typext(_)
        | StructureItemDesc::Pstr_exception(_)
        | StructureItemDesc::Pstr_module(_)
        | StructureItemDesc::Pstr_recmodule(_)
        | StructureItemDesc::Pstr_modtype(_)
        | StructureItemDesc::Pstr_open(_)
        | StructureItemDesc::Pstr_include(_)
        | StructureItemDesc::Pstr_attribute(_)
        | StructureItemDesc::Pstr_extension(_)
        | StructureItemDesc::Pstr_raw(_) => false,
    }
}

#[cfg(test)]
#[test]
fn derive_error_fixture_messages() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../tests/ppx_spice/errors");
    let manifest = std::fs::read_to_string(root.join("cases.tsv")).unwrap();
    for line in manifest.lines() {
        let (name, expected) = line.split_once('\t').unwrap();
        let source = std::fs::read_to_string(root.join(name)).unwrap();
        let mut parser = crate::parser::Parser::new(name, &source);
        let items = crate::parser::module::parse_structure(&mut parser);
        assert!(!parser.has_errors(), "{name}: fixture must reach the derive");
        let mut arena = parser.into_arena();
        let result: Result<Vec<_>, _> = items.iter().map(|item|
            expand_structure_item_with_mapper(item, &mut arena, true)).collect();
        let error = result.expect_err(name);
        assert!(error.contains(expected), "{name}: expected {expected:?}, got {error:?}");
    }
}

#[cfg(test)]
mod census_reason_tests {
    use super::*;

    #[test]
    fn unplanned_forms_count_each_binding_once_at_ten_thousand() {
        assert_eq!(std::mem::size_of::<UnplannedForm>(), 1);
        assert_eq!(std::mem::size_of::<GeneralReason>(), 1);
        assert_eq!(std::mem::size_of::<Classification>(), 1);
        let mut counts = PathCounts::default();
        for _ in 0..10_000 {
            let mut group = PathCounts::default();
            group.add(Classification::General(GeneralReason::NotYetPlanned(
                UnplannedForm::JsonIdentity,
            )), 1);
            group.add(Classification::General(GeneralReason::JsonIdentityArgument), 1);
            counts.merge(group);
        }
        assert_eq!(counts.json_identity_argument, 10_000);
        assert_eq!(counts.not_yet_planned, 10_000);
        assert_eq!(counts.unplanned_forms.iter().sum::<u64>(), 10_000);
        assert_eq!(counts.unplanned_forms[UnplannedForm::JsonIdentity as usize], 10_000);
    }
}
