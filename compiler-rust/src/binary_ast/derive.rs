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
            | plan::Obligation::Equal { .. } => None,
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

/// Detect derives in a signature. O(items and visited attributes), delegating to
/// the existing mapper scan; no additional traversal.
pub fn signature_uses_spice_mapper(items: &[SignatureItem], arena: &ParseArena) -> bool {
    super::spice_ppx::signature_uses_spice_mapper(items, arena)
}

/// Expand built-in derives on a structure item. O(generated syntax plus mapper
/// work), with O(1) timing overhead only when the census is enabled.
pub fn expand_structure_item_with_mapper(
    item: &StructureItem,
    arena: &mut ParseArena,
    active: bool,
) -> Result<Vec<StructureItem>, String> {
    // O(1) disabled probe: retain the direct call without saving profiling state
    // across a mapper that mutably borrows the arena.
    if arena.derived_census.is_none() {
        return super::spice_ppx::expand_structure_item_with_mapper(item, arena, active);
    }
    expand_with_census(item, arena, active)
}

/// O(1) census bookkeeping plus the existing expansion and optional key encoder.
/// Keeping this cold leaves no profiling locals in the ordinary mapper's frame.
#[cold]
#[inline(never)]
fn expand_with_census(
    item: &StructureItem,
    arena: &mut ParseArena,
    active: bool,
) -> Result<Vec<StructureItem>, String> {
    let start = census::start(true);
    let observer_before = arena.derived_census.as_ref().map_or(0, |c| c.observer_ns);
    let result = super::spice_ppx::expand_structure_item_with_mapper(item, arena, active);
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
