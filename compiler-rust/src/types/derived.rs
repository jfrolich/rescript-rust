//! The checker's side of a derived item (`Pstr_derived`).
//!
//! [`discharge`] establishes the obligations of the item's plan in order and
//! enters its bindings in the environment without typing a body: per value
//! obligation one lookup, one instance and one unification with the
//! obligation's skeleton. When an obligation fails it reports [`Fallback`]:
//! the checking of the unit is abandoned, and the unit is compiled again
//! with its derived items as syntax, so every diagnostic comes from the code
//! that types syntax. Nothing is generated for an item whose plan holds.
//!
//! What a discharge records is in two dense tables of the typed arena,
//! indexed by the plan's binding and obligation handles: the identifier,
//! type and environment of each binding, and what each obligation resolved
//! to. The readers of the typed tree (`Tstr_derived`) reach them without a
//! lookup structure.
//! (`compiler-rust/docs/DERIVED_CODECS.md`, "The cheapest sound path".)

use smallvec::SmallVec;
use std::borrow::Cow;

use crate::binary_ast::derive::plan::{
    Binding, BindingIdx, DerivedIdx, ExprLoc, LabelUse, NO_VAR, Obligation, ObligationIdx, Owner,
    Plans, Predef, Site, SkeletonNode, Span, TypeSource,
};
use crate::types::decl::{ConstructorDescription, LabelDescription, ValueDescription};
use std::sync::Arc;
use crate::ident::Ident;
use crate::parse_arena::ParseArena;
use crate::types::env::Env;
use crate::types::path::Path;
use crate::types::asttypes::ArgLabel;
use crate::types::type_expr::{TypeArg, TypeDesc, TypeExprRef};
use crate::types::typecore::{RecArg, TypeCheckContext};
use crate::types::typedtree::EnvRef;

/// What a discharged obligation resolved to.
#[derive(Debug, Clone, Copy)]
pub enum Resolved {
    /// A body-shape equation discharged by unification; no runtime payload.
    Equation,
    /// A value: the path its name resolved to, and the instance of its type
    /// that its skeleton was unified with.
    Value {
        /// The value's path.
        path: Path,
        /// The instance of the value's type.
        instance: TypeExprRef,
    },
    /// A type constructor: the path its name resolved to.
    Type(Path),
    /// A label: its description, in [`DerivedTable::label`].
    Label(u32),
    /// A constructor: its description, in [`DerivedTable::constructor`], and
    /// the instances of its arguments and result that were unified with its
    /// skeletons.
    Constructor {
        /// Slot of the description.
        desc: u32,
        /// The first slot of the instances of its arguments' types in
        /// [`DerivedTable::constructor_args`]; there are as many as the
        /// obligation's `args`.
        args: u32,
        /// The instance of the result type.
        res: TypeExprRef,
    },
    /// A constant: the typed constant, in [`DerivedTable::constant`].
    Literal(u32),
}

impl Resolved {
    /// The path the name resolved to. Cost: O(1).
    #[inline]
    pub fn path(self) -> Path {
        match self {
            Resolved::Value { path, .. } | Resolved::Type(path) => path,
            Resolved::Equation | Resolved::Label(_) | Resolved::Constructor { .. } | Resolved::Literal(_) => {
                unreachable!("a skeleton names a type obligation, a body's free node a value")
            }
        }
    }

    /// The instance of a value's type. Cost: O(1).
    #[inline]
    pub fn instance(self) -> TypeExprRef {
        match self {
            Resolved::Value { instance, .. } => instance,
            Resolved::Equation
            | Resolved::Type(_)
            | Resolved::Label(_)
            | Resolved::Constructor { .. }
            | Resolved::Literal(_) => {
                unreachable!("a body and a type source name value obligations")
            }
        }
    }
}

/// The slots of a discharged item in the tables.
#[derive(Debug, Clone, Copy)]
struct Slots {
    bindings: Span,
    obligations: Span,
}

/// A binding of a discharged item, as entered in the environment.
#[derive(Debug, Clone, Copy)]
pub struct Bound {
    /// The bound identifier.
    pub ident: Ident,
    /// The generalised type of the binding.
    pub ty: TypeExprRef,
    /// The environment the item was checked in.
    pub env: EnvRef,
    /// The obligations of the binding: its slots of the result table.
    pub obligations: Span,
}

/// The tables of one typed arena. `reserve` sizes them once per compilation.
#[derive(Debug, Default)]
pub struct DerivedTable {
    resolved: Vec<Option<Resolved>>,
    bound: Vec<Option<Bound>>,
    /// The slots of each item, so a reader of the typed tree needs no parse
    /// arena to find them.
    items: Vec<Slots>,
    /// The types of the bindings of the item being discharged, before they
    /// are generalised and entered.
    pending: Vec<TypeExprRef>,
    /// The skeleton variables of the binding being discharged: one buffer
    /// for the whole compilation.
    vars: Vec<Option<TypeExprRef>>,
    /// The description of each value obligation that resolved to a
    /// primitive, indexed by obligation.
    primitives: Vec<Option<Arc<ValueDescription>>>,
    /// The descriptions `Resolved::Label` names.
    labels: Vec<Arc<LabelDescription>>,
    /// The descriptions `Resolved::Constructor` names.
    constructors: Vec<Arc<ConstructorDescription>>,
    /// Unqualified names: (binding obligation start, description slot + 1).
    /// A binding has one immutable environment; epochs prevent cross-binding reuse.
    constructor_names: Vec<(u32, u32)>,
    /// The constants `Resolved::Literal` names.
    constants: Vec<crate::types::typedtree::Constant>,
    /// The instances of the argument types of the constructors
    /// `Resolved::Constructor` names, consecutive per constructor.
    constructor_args: Vec<TypeExprRef>,
}

impl DerivedTable {
    /// Make room for every binding and obligation of `plans`.
    /// Cost: O(1) when the tables already have that size, which is every call
    /// but the first of a compilation; the first is O(bindings + obligations
    /// of the unit), one allocation per table.
    pub fn reserve(&mut self, plans: &Plans) {
        if self.resolved.len() != plans.obligation_count() {
            self.resolved.resize(plans.obligation_count(), None);
            self.primitives.resize(plans.obligation_count(), None);
        }
        if self.bound.len() != plans.binding_count() {
            self.bound.resize(plans.binding_count(), None);
        }
        if self.items.len() != plans.item_count() {
            let empty = Span { start: 0, len: 0 };
            self.items.resize(
                plans.item_count(),
                Slots {
                    bindings: empty,
                    obligations: empty,
                },
            );
        }
        if self.pending.len() != plans.binding_count() {
            self.pending.resize(plans.binding_count(), TypeExprRef::null());
        }
    }

    /// Record what an obligation resolved to. Cost: O(1), one slot write.
    #[inline]
    pub fn set_resolved(&mut self, idx: ObligationIdx, resolved: Resolved) {
        self.resolved[idx.index()] = Some(resolved);
    }

    /// Hold the type of a binding until its item is discharged. Cost: O(1).
    #[inline]
    fn pending_type(&mut self, idx: BindingIdx, ty: TypeExprRef) {
        self.pending[idx.index()] = ty;
    }

    /// Record a binding. Cost: O(1), one slot write.
    #[inline]
    pub fn set_bound(&mut self, idx: BindingIdx, bound: Bound) {
        self.bound[idx.index()] = Some(bound);
    }

    /// What an obligation of a discharged item resolved to. Cost: O(1).
    #[inline]
    pub fn resolved(&self, idx: ObligationIdx) -> Resolved {
        self.resolved[idx.index()].expect("the obligations of a typed derived item are discharged")
    }

    /// The description of the primitive a value obligation resolved to, or
    /// `None` for a regular value. Cost: O(1).
    #[inline]
    pub fn primitive(&self, idx: ObligationIdx) -> Option<&Arc<ValueDescription>> {
        self.primitives[idx.index()].as_ref()
    }

    /// The label a label obligation resolved to. Cost: O(1).
    #[inline]
    pub fn label(&self, idx: ObligationIdx) -> &Arc<LabelDescription> {
        match self.resolved(idx) {
            Resolved::Label(slot) => &self.labels[slot as usize],
            _ => unreachable!("a field names a label obligation"),
        }
    }

    /// The constructor a constructor obligation resolved to, with the
    /// instances of its first argument (null when it has none) and result.
    /// Cost: O(1).
    #[inline]
    pub fn constructor(
        &self,
        idx: ObligationIdx,
    ) -> (&Arc<ConstructorDescription>, TypeExprRef, TypeExprRef) {
        match self.resolved(idx) {
            Resolved::Constructor { desc, args, res } => {
                let desc = &self.constructors[desc as usize];
                let arg = match desc.cstr_args.is_empty() {
                    true => TypeExprRef::null(),
                    false => self.constructor_args[args as usize],
                };
                (desc, arg, res)
            }
            _ => unreachable!("a construction or a case names a constructor obligation"),
        }
    }

    /// The instances of the argument types of the constructor a constructor
    /// obligation resolved to, in order. Cost: O(1).
    #[inline]
    pub fn constructor_args(&self, idx: ObligationIdx) -> &[TypeExprRef] {
        match self.resolved(idx) {
            Resolved::Constructor { desc, args, .. } => {
                let len = self.constructors[desc as usize].cstr_args.len();
                &self.constructor_args[args as usize..args as usize + len]
            }
            _ => unreachable!("a construction or a case names a constructor obligation"),
        }
    }

    /// The constant of a literal obligation. Cost: O(1).
    #[inline]
    pub fn constant(&self, idx: ObligationIdx) -> &crate::types::typedtree::Constant {
        match self.resolved(idx) {
            Resolved::Literal(slot) => &self.constants[slot as usize],
            _ => unreachable!("a literal node names a literal obligation"),
        }
    }

    /// Record the slots of a discharged item: its bindings, and their
    /// obligations, which are consecutive. Cost: O(1).
    #[inline]
    fn set_item(&mut self, idx: DerivedIdx, bindings: Span, obligations: Span) {
        self.items[idx.index()] = Slots {
            bindings,
            obligations,
        };
    }

    /// The bindings of a discharged item, in declaration order.
    /// Cost: O(1) to obtain; one slot read per binding yielded.
    pub fn bound(&self, idx: DerivedIdx) -> impl Iterator<Item = Bound> + '_ {
        self.bound[self.items[idx.index()].bindings.range()]
            .iter()
            .map(|bound| bound.expect("the bindings of a typed derived item are entered"))
    }

    /// The paths of the values a binding of a discharged item uses, in typing
    /// order: what the identifier expressions of its general form resolve
    /// to. Cost: O(1) to obtain; one slot read per obligation of the binding.
    pub fn values_of(&self, bound: &Bound) -> impl Iterator<Item = Path> + '_ {
        self.resolved[bound.obligations.range()]
            .iter()
            .filter_map(|resolved| match resolved {
                Some(Resolved::Value { path, .. }) => Some(*path),
                Some(
                    Resolved::Equation
                    | Resolved::Type(_)
                    | Resolved::Label(_)
                    | Resolved::Constructor { .. }
                    | Resolved::Literal(_),
                ) => None,
                None => unreachable!("the obligations of a typed derived item are discharged"),
            })
    }

    /// The number of items that were discharged, wherever they are nested.
    #[cfg(test)]
    pub(crate) fn discharged(&self) -> usize {
        self.items.iter().filter(|slots| slots.bindings.len > 0).count()
    }

    /// The results of the obligations of a discharged item, in typing order.
    /// Cost: O(1) to obtain; one slot read per obligation yielded.
    pub fn resolved_of(&self, idx: DerivedIdx) -> impl Iterator<Item = Resolved> + '_ {
        self.resolved[self.items[idx.index()].obligations.range()]
            .iter()
            .map(|resolved| resolved.expect("the obligations of a typed derived item are discharged"))
    }
}

/// The item cannot be established from its plan. The type state, the
/// warnings and the deprecated uses of the failed discharge are left as they
/// are: the caller abandons the checking of the unit, which is compiled
/// again with plans off.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Fallback;

/// A discharged item: `Tstr_derived` with its tables filled.
#[derive(Debug)]
pub struct Discharged {
    /// The environment extended with the item's bindings.
    pub env: Env,
    /// The item's bindings as signature items, in binding order: the value
    /// descriptions that were entered in `env`.
    pub sig_items: Vec<crate::types::decl::SignatureItem>,
}

/// The steps of a discharge, for the tests that prove its cost. The checker
/// passes `()`, whose methods are empty.
pub trait Steps {
    /// O(1): observe the current obligation; the normal path erases this call.
    fn obligation(&mut self, _obligation: Obligation) {}
    /// Census-only scheme level before instantiation. The normal path erases
    /// this call without even reading the level. Cost: O(1).
    fn value_scheme(&mut self, _ctx: &crate::types::context::TypeContext, _ty: TypeExprRef) {}
    /// An environment lookup.
    fn lookup(&mut self);
    /// An instance of a looked-up value's type.
    fn instance(&mut self);
    /// A unification.
    fn unification(&mut self);
}

impl Steps for () {
    #[inline(always)]
    fn lookup(&mut self) {}
    #[inline(always)]
    fn instance(&mut self) {}
    #[inline(always)]
    fn unification(&mut self) {}
}

/// Last obligation visited, only when the census is enabled.
#[derive(Default)]
struct CensusSteps {
    last: Option<Obligation>,
    value_schemes: [u64; 2],
}

impl Steps for CensusSteps {
    fn value_scheme(&mut self, ctx: &crate::types::context::TypeContext, ty: TypeExprRef) {
        let generic = ctx.get_level(ctx.repr(ty)) == crate::types::type_expr::GENERIC_LEVEL;
        self.value_schemes[usize::from(generic)] += 1;
    }
    /// O(1): overwrite the inline observation without allocating.
    fn obligation(&mut self, obligation: Obligation) { self.last = Some(obligation); }
    /// O(1): no additional operation counters in this observer.
    fn lookup(&mut self) {}
    /// O(1): no additional operation counters in this observer.
    fn instance(&mut self) {}
    /// O(1): no additional operation counters in this observer.
    fn unification(&mut self) {}
}

/// Discharge the obligations of a derived item and enter its bindings.
/// Cost: O(obligations + skeleton nodes of the item): per value obligation
/// one environment lookup, one instance of the value's type and one
/// unification; per label or constructor obligation one lookup, one instance
/// and two unifications; per literal one unification; per binding one function type, one environment entry and one
/// signature item made of the same value description, without a lookup. No
/// allocation per obligation beyond the type nodes of the instances and
/// skeletons; one buffer of signature items per item. The first item sizes a
/// dense constructor-name table in O(interned names); later items reuse it.
/// Unqualified constructor descriptions are copied once per name per binding,
/// while all lookup, usage, instance and unification work remains ordered.
pub fn discharge(
    tctx: &mut TypeCheckContext<'_>,
    env: &Env,
    item: DerivedIdx,
) -> Result<Discharged, Fallback> {
    if tctx.derived_census.is_none() {
        return discharge_counting(tctx, env, item, &mut ());
    }
    let mut steps = CensusSteps::default();
    let result = discharge_counting(tctx, env, item, &mut steps);
    for (total, count) in tctx.derived_census.as_mut().unwrap().value_schemes.iter_mut().zip(steps.value_schemes) {
        *total += count;
    }
    if result.is_err() {
        let (kind, shape) = match steps.last {
            Some(Obligation::Equal { .. }) => ("equation", "body_shape"),
            Some(Obligation::Value { .. }) => ("value", "codec_function"),
            Some(Obligation::Type { .. }) => ("type", "named_type"),
            Some(Obligation::Label { .. }) => ("label", "record"),
            Some(Obligation::Constructor { of, .. }) => ("constructor", match of {
                Owner::Option => "option",
                Owner::Result => "result",
                Owner::Declared => "declared_variant",
                Owner::Type => "qualified_variant",
            }),
            Some(Obligation::Literal { .. }) => ("literal", "constant"),
            None => ("binding", "binding_type"),
        };
        tctx.derived_census.as_ref().unwrap().failed_obligation(kind, shape);
    }
    result
}

/// [`discharge`], counting its steps.
pub fn discharge_counting(
    tctx: &mut TypeCheckContext<'_>,
    env: &Env,
    idx: DerivedIdx,
    steps: &mut impl Steps,
) -> Result<Discharged, Fallback> {
    let arena = tctx.arena;
    let plans = arena.plans();
    let item = plans.item(idx);
    let bindings = plans.bindings(item);
    tctx.typed.derived.reserve(plans);
    // One dense name table per unit, not per binding or constructor visit.
    tctx.typed.derived.constructor_names.resize(arena.string_count(), (0, 0));

    // `Typecore.type_binding` starts with `Typetexp.reset_type_variables`.
    tctx.reset_type_variables();
    tctx.set_unify_env(env);
    let ctx = tctx.type_ctx;
    ctx.begin_def();
    let mut vars = std::mem::take(&mut tctx.typed.derived.vars);
    let mut established = Ok(());
    for (i, binding) in bindings.iter().enumerate() {
        // typecore.ml `type_let` scopes a binding's attributes around the
        // typing of its expression.
        let result = crate::types::typemod::with_warning_scope(
            tctx,
            arena,
            &binding.attributes,
            true,
            |tctx| {
                Ok::<_, crate::types::typecore::TypeCoreError>(discharge_binding(
                    tctx, env, arena, binding, &mut vars, steps,
                ))
            },
        );
        match result {
            Ok(Ok(ty)) => {
                let binding_idx = BindingIdx(item.bindings.start + i as u32);
                tctx.typed.derived.pending_type(binding_idx, ty);
            }
            Ok(Err(Fallback)) | Err(_) => {
                established = Err(Fallback);
                break;
            }
        }
    }
    tctx.typed.derived.vars = vars;
    ctx.end_def();
    established?;

    // typecore.ml `type_let`: every binding is a function, so its type is
    // generalised in full, and the bound variables enter the environment in
    // binding order with the description of a let-bound variable.
    let mut new_env = env.clone();
    let env_ref = ctx.store_typed_env(env);
    let val_loc = tctx.intern_ast_loc(arena, arena.none_loc());
    let mut sig_items = Vec::with_capacity(bindings.len());
    for (i, binding) in bindings.iter().enumerate() {
        let binding_idx = BindingIdx(item.bindings.start + i as u32);
        let ty = tctx.typed.derived.pending[binding_idx.index()];
        crate::types::ctype::generalize(ctx, ty);
        let ident = ctx.create_ident(arena.name(binding.name));
        // typemod.ml `type_structure`: the signature holds the value
        // description the binding has in the environment. It is made once
        // and entered in both.
        let description = crate::types::decl::ValueDescription {
            val_type: ty,
            val_kind: crate::types::decl::ValueKind::ValReg,
            val_loc,
            val_attributes: Default::default(),
            val_path: None,
        };
        new_env.add_value(ident, description.clone());
        sig_items.push(crate::types::decl::SignatureItem::SigValue(ident, description));
        tctx.typed.derived.set_bound(
            binding_idx,
            Bound {
                ident,
                ty,
                env: env_ref,
                obligations: binding.obligations,
            },
        );
    }
    let obligations = match (bindings.first(), bindings.last()) {
        (Some(first), Some(last)) => Span {
            start: first.obligations.start,
            len: last.obligations.start + last.obligations.len - first.obligations.start,
        },
        _ => Span { start: 0, len: 0 },
    };
    tctx.typed.derived.set_item(idx, item.bindings, obligations);
    Ok(Discharged {
        env: new_env,
        sig_items,
    })
}

/// Discharge the obligations of one binding and give its type.
/// Cost: O(obligations + skeleton nodes of the binding).
fn discharge_binding(
    tctx: &mut TypeCheckContext<'_>,
    env: &Env,
    arena: &ParseArena,
    binding: &Binding,
    vars: &mut Vec<Option<TypeExprRef>>,
    steps: &mut impl Steps,
) -> Result<TypeExprRef, Fallback> {
    let plans = arena.plans();
    let ctx = tctx.type_ctx;
    vars.clear();
    vars.resize(binding.vars as usize, None);
    // The record expression or pattern whose labels are being discharged:
    // its labels, the position of the next one, and how many it has.
    let mut record_expression: Option<(crate::types::decl::LabelArrayRef, u32, u32)> = None;
    for slot in binding.obligations.range() {
        let obligation = ObligationIdx(slot as u32);
        steps.obligation(plans.obligation(obligation));
        // Whether the obligation is a label of the record expression or
        // pattern being discharged.
        let grouped = matches!(
            plans.obligation(obligation),
            Obligation::Label {
                usage: LabelUse::Construct | LabelUse::Pattern | LabelUse::ConstructInline,
                ..
            }
        );
        let resolved = match plans.obligation(obligation) {
            Obligation::Equal { expected, actual } => {
                let (expected, _) = instantiate(ctx, arena, &tctx.typed.derived,
                    plans.skeleton_from(expected), vars);
                let (actual, _) = instantiate(ctx, arena, &tctx.typed.derived,
                    plans.skeleton_from(actual), vars);
                steps.unification();
                crate::types::ctype::unify(ctx, &mut tctx.unify_state, expected, actual)
                    .map_err(|_| Fallback)?;
                Resolved::Equation
            }
            Obligation::Value {
                name,
                name_loc,
                skeleton,
                expr_loc,
                called,
            } => {
                let longident = arena.get_longident(name);
                steps.lookup();
                let (path, desc) =
                    crate::types::typecore::lookup_value_ident(tctx, env, longident, name_loc)
                        .map_err(|_| Fallback)?;
                // A primitive is applied by the backend from its declared
                // type; one that reads the syntax of its arguments has no
                // meaning in a body without syntax.
                let primitive = match &desc.val_kind {
                    crate::types::decl::ValueKind::ValReg => false,
                    crate::types::decl::ValueKind::ValPrim(prim) => {
                        // An optional parameter of an external is part of
                        // its FFI specification, not an option.
                        if crate::raw_lambda::convert::primitive_reads_syntax(prim)
                            || matches!(
                                plans.skeleton_from(skeleton).get(1),
                                Some(SkeletonNode::Optional(_))
                            )
                        {
                            return Err(Fallback);
                        }
                        true
                    }
                };
                crate::types::typecore::note_value_ident_use(
                    tctx, env, longident, name_loc, &path, &desc, called,
                )
                .map_err(|_| Fallback)?;
                let expr_loc = match expr_loc {
                    ExprLoc::OfName => name_loc,
                    ExprLoc::Dummy => arena.dummy_loc(),
                };
                crate::types::typecore::check_inlined_record_escape(
                    ctx,
                    expr_loc,
                    desc.val_type,
                    RecArg::Rejected,
                )
                .map_err(|_| Fallback)?;
                steps.value_scheme(ctx, desc.val_type);
                steps.instance();
                let instance = crate::types::ctype::instance(ctx, desc.val_type);
                let nodes = plans.skeleton_from(skeleton);
                // typecore.ml `type_application` reads the parameters off the
                // function's own type: a value the body applies must be a
                // function of that many parameters before anything is
                // unified, or inference would have made the arrow itself.
                if let SkeletonNode::Arrow { params } = nodes[0] {
                    let head = crate::types::ctype::expand_head(ctx, env, instance);
                    let arity = match &*ctx.borrow_desc(ctx.repr(head)) {
                        TypeDesc::Tarrow { args, .. } => ctx.type_args(*args).len(),
                        _ => return Err(Fallback),
                    };
                    if arity != params as usize {
                        return Err(Fallback);
                    }
                }
                let (expected, _) = instantiate(ctx, arena, &tctx.typed.derived, nodes, vars);
                if primitive {
                    tctx.typed.derived.primitives[obligation.index()] = Some(desc.clone());
                }
                // typecore.ml `type_expect` of an identifier: the instance
                // against the expected type, in this order.
                steps.unification();
                crate::types::ctype::unify(ctx, &mut tctx.unify_state, instance, expected)
                    .map_err(|_| Fallback)?;
                Resolved::Value { path, instance }
            }
            Obligation::Label {
                name,
                skeleton,
                usage,
            } => {
                let nodes = plans.skeleton_from(skeleton);
                let (arg, used) = instantiate(ctx, arena, &tctx.typed.derived, nodes, vars);
                let (record, _) =
                    instantiate(ctx, arena, &tctx.typed.derived, &nodes[used..], vars);
                let longident = arena.get_longident(name);
                steps.lookup();
                let (label, ty_arg, ty_res) = match usage {
                    // A field access: the checker's own lookup, by the
                    // record's type when it is known, else by name. The
                    // field a record update writes is found by the type of
                    // its base (typecore.ml `type_expect_`, `Pexp_record`
                    // with a base, types the base first).
                    LabelUse::Access | LabelUse::AccessDummy | LabelUse::Update => {
                        let loc = match usage {
                            LabelUse::Access => arena.none_loc(),
                            _ => arena.dummy_loc(),
                        };
                        crate::types::typecore::label_access(tctx, env, record, longident, loc)
                            .map_err(|_| Fallback)?
                    }
                    // A field of a pattern or an expression of an inline
                    // record: its labels are not in the environment, and
                    // inference finds them by the expected type, which the
                    // constructor obligation before them fixed. The plan
                    // holds when they are the record's, all of them, in
                    // order.
                    LabelUse::Pattern | LabelUse::ConstructInline => {
                        let (label, ty_arg, ty_res) = crate::types::typecore::label_access(
                            tctx,
                            env,
                            record,
                            longident,
                            arena.none_loc(),
                        )
                        .map_err(|_| Fallback)?;
                        // Each lookup of an inline record makes its labels
                        // anew, so they are told apart by position only:
                        // the unification of each label's record with the
                        // one type below makes them one record's.
                        let position = match record_expression {
                            Some((_, position, _)) => position,
                            None => {
                                let len =
                                    ctx.label_family(label.lbl_all).map_or(0, |all| all.len());
                                record_expression = Some((label.lbl_all, 0, len as u32));
                                0
                            }
                        };
                        if label.lbl_pos as u32 != position {
                            return Err(Fallback);
                        }
                        if let Some((_, position, _)) = &mut record_expression {
                            *position += 1;
                        }
                        (label, ty_arg, ty_res)
                    }
                    // A field of the record expression the body makes of the
                    // declaration being derived. typecore.ml
                    // `type_label_a_list` chooses the labels from all the
                    // names of the expression; it chooses these when each
                    // name's first candidate is the label at the field's
                    // position of one record, whose every label is written.
                    // Anything else is left to the general form.
                    LabelUse::Construct => {
                        let last = arena.get_string(longident.last_idx());
                        let label = env.find_label(last).map_err(|_| Fallback)?.clone();
                        let (family, position) = match record_expression {
                            Some((family, position, _)) => (family, position),
                            None => {
                                let len = ctx.label_family(label.lbl_all).map_or(0, |all| all.len());
                                record_expression = Some((label.lbl_all, 0, len as u32));
                                // `Label.disambiguate` marks the type of the
                                // chosen labels (env.ml:1230-1238), once here.
                                if let Some(path) =
                                    crate::types::typecore::label_result_path(ctx, &label)
                                {
                                    crate::types::typecore::mark_type_path(ctx, env, &path);
                                }
                                (label.lbl_all, 0)
                            }
                        };
                        // typecore.ml `type_label_a_list` rejects the
                        // construction of a private record.
                        if label.lbl_all != family
                            || label.lbl_pos as u32 != position
                            || label.lbl_private == crate::types::PrivateFlag::Private
                        {
                            return Err(Fallback);
                        }
                        // With several candidates inference may report the
                        // choice (warning 41).
                        if crate::types::typecore::ambiguous_name_warning_is_active(tctx)
                            && env.find_all_labels(last).len() > 1
                        {
                            return Err(Fallback);
                        }
                        if let Some((_, position, _)) = &mut record_expression {
                            *position += 1;
                        }
                        steps.instance();
                        let (_, ty_arg, ty_res) =
                            crate::types::ctype::instance_label(ctx, true, &label);
                        (label, ty_arg, ty_res)
                    }
                };
                steps.unification();
                crate::types::ctype::unify(ctx, &mut tctx.unify_state, record, ty_res)
                    .map_err(|_| Fallback)?;
                crate::types::ctype::unify(ctx, &mut tctx.unify_state, ty_arg, arg)
                    .map_err(|_| Fallback)?;
                let table = &mut tctx.typed.derived;
                table.labels.push(Arc::new(label));
                Resolved::Label(table.labels.len() as u32 - 1)
            }
            Obligation::Constructor {
                name,
                skeleton,
                of,
                site,
                args: arity,
            } => {
                let nodes = plans.skeleton_from(skeleton);
                let mut expected: SmallVec<[TypeExprRef; 4]> = SmallVec::new();
                let mut used = 0;
                for _ in 0..arity {
                    let (arg, span) =
                        instantiate(ctx, arena, &tctx.typed.derived, &nodes[used..], vars);
                    expected.push(arg);
                    used += span;
                }
                let (result, _) =
                    instantiate(ctx, arena, &tctx.typed.derived, &nodes[used..], vars);
                let longident = arena.get_longident(name);
                let last = arena.get_string(longident.last_idx());
                let (loc, usage) = match site {
                    Site::Construct => (
                        arena.dummy_loc(),
                        crate::types::usage::ConstructorUsage::Positive,
                    ),
                    Site::ConstructAt => (
                        plans.constructor_loc(obligation),
                        crate::types::usage::ConstructorUsage::Positive,
                    ),
                    Site::ConstructNone => (
                        arena.none_loc(),
                        crate::types::usage::ConstructorUsage::Positive,
                    ),
                    Site::Pattern => (arena.none_loc(), crate::types::usage::ConstructorUsage::Pattern),
                    Site::PatternDummy => (
                        arena.dummy_loc(),
                        crate::types::usage::ConstructorUsage::Pattern,
                    ),
                };
                steps.lookup();
                let desc = match of {
                    // An unqualified name: inference takes the first
                    // candidate in scope unless the expected type names
                    // another. The plan holds when that candidate is the
                    // predefined constructor; the unification below fails
                    // when the expected type is another.
                    Owner::Option | Owner::Result => {
                        let desc = env.find_constructor(last).map_err(|_| Fallback)?;
                        let predefined = match of {
                            Owner::Option => crate::types::predef::path_option(),
                            _ => crate::types::predef::path_result(),
                        };
                        let is_predefined = matches!(
                            &*ctx.borrow_desc(ctx.repr(desc.cstr_res)),
                            TypeDesc::Tconstr { path, .. } if path.same(&predefined)
                        );
                        if !is_predefined {
                            return Err(Fallback);
                        }
                        Cow::Borrowed(desc)
                    }
                    // A constructor of the declaration being derived, which
                    // the item follows: an unqualified name whose first
                    // candidate in scope is the declaration's
                    // (typecore.ml `type_construct`, `Constructor.disambiguate`
                    // without an expected type). The skeletons of the
                    // declaration's constructors share their result, so a
                    // candidate of another type fails a unification below.
                    Owner::Declared => {
                        // With several candidates inference may report the
                        // choice (warning 41).
                        if crate::types::typecore::ambiguous_name_warning_is_active(tctx)
                            && env.find_all_constructors(last).len() > 1
                        {
                            return Err(Fallback);
                        }
                        Cow::Borrowed(env.find_constructor(last).map_err(|_| Fallback)?)
                    }
                    // A qualified name: the lookup of typecore.ml
                    // `type_construct`, in the module that qualifies it. That
                    // it is a constructor of the stated type is the
                    // unification of its result below.
                    Owner::Type => {
                        crate::types::typecore::mark_open_lid_use(
                            ctx,
                            env,
                            arena,
                            longident,
                            crate::types::env::OpenLookupKind::Component,
                            Some(loc),
                        );
                        Cow::Owned(crate::types::typecore::lookup_constructor_in_module(
                            longident,
                            arena,
                            env,
                            &mut tctx.persistent_env,
                            ctx,
                            Some(result),
                        )
                        .ok_or(Fallback)?
                        .1)
                    }
                };
                // A plan describes an ordinary constructor of a regular
                // variant, applied to what it takes; only the declaration's
                // own may take an inline record. typecore.ml
                // `type_construct` rejects the construction of a private
                // one.
                if desc.cstr_generalized
                    || (desc.cstr_inlined.is_some() && of != Owner::Declared)
                    || desc.cstr_arity != i32::from(arity)
                    || desc.cstr_args.len() != usize::from(arity)
                    || !matches!(desc.cstr_kind, crate::types::ConstructorKind::Ordinary(_))
                    || (matches!(site, Site::Construct | Site::ConstructNone | Site::ConstructAt)
                        && desc.cstr_private == crate::types::PrivateFlag::Private)
                {
                    return Err(Fallback);
                }
                crate::types::typecore::mark_type_path_of(ctx, env, desc.cstr_res);
                crate::types::typecore::note_constructor_use(tctx, env, loc, usage, last, &desc)
                    .map_err(|_| Fallback)?;
                steps.instance();
                let (args, res) = crate::types::instance_constructor(ctx, &desc);
                steps.unification();
                crate::types::ctype::unify(ctx, &mut tctx.unify_state, res, result)
                    .map_err(|_| Fallback)?;
                for (instance, expected) in args.iter().zip(&expected) {
                    crate::types::ctype::unify(ctx, &mut tctx.unify_state, *instance, *expected)
                        .map_err(|_| Fallback)?;
                }
                let table = &mut tctx.typed.derived;
                // Names are interned by the plan builder. Reuse only the stored
                // description, never a lookup, usage mark, instance or unification.
                let name_slot = match longident {
                    crate::parser::Longident::Lident(name) => Some(name.raw() as usize),
                    crate::parser::Longident::Ldot(..) | crate::parser::Longident::Lapply(..) => None,
                };
                let cached = name_slot.map(|slot| table.constructor_names[slot]);
                let desc_slot = if let Some((epoch, slot)) = cached
                    && epoch == binding.obligations.start && slot != 0
                {
                    slot - 1
                } else {
                    let slot = table.constructors.len() as u32;
                    table.constructors.push(Arc::new(desc.into_owned()));
                    if let Some(name_slot) = name_slot {
                        table.constructor_names[name_slot] = (binding.obligations.start, slot + 1);
                    }
                    slot
                };
                let first_arg = table.constructor_args.len() as u32;
                table.constructor_args.extend_from_slice(&args);
                Resolved::Constructor {
                    desc: desc_slot,
                    args: first_arg,
                    res,
                }
            }
            Obligation::Literal { expr, skeleton } => {
                let expr = arena.get_expanded_expr(expr);
                let crate::parser::ast::ExpressionDesc::Pexp_constant(constant) = &expr.pexp_desc
                else {
                    return Err(Fallback);
                };
                // typecore.ml `type_expect` of a constant.
                let constant =
                    crate::types::typecore::convert_constant(constant, expr.pexp_loc, arena)
                        .map_err(|_| Fallback)?;
                let ty = crate::types::typecore::type_constant(ctx, env, &constant);
                let (expected, _) = instantiate(
                    ctx,
                    arena,
                    &tctx.typed.derived,
                    plans.skeleton_from(skeleton),
                    vars,
                );
                steps.unification();
                crate::types::ctype::unify(ctx, &mut tctx.unify_state, ty, expected)
                    .map_err(|_| Fallback)?;
                let table = &mut tctx.typed.derived;
                table.constants.push(constant);
                Resolved::Literal(table.constants.len() as u32 - 1)
            }
            Obligation::Type {
                name,
                name_loc,
                arity,
                var,
            } => {
                steps.lookup();
                let (path, decl) = crate::types::typecore::find_type_for_lid(
                    tctx,
                    env,
                    name_loc,
                    arena.get_longident(name),
                )
                .map_err(|_| Fallback)?;
                crate::types::typecore::note_type_use(tctx, name_loc, &path, &decl)
                    .map_err(|_| Fallback)?;
                // A skeleton applies the constructor to `arity` types without
                // unifying them with its parameters: sound when each
                // parameter is an unconstrained variable.
                let plain_params = decl.type_arity as usize == arity as usize
                    && decl.type_params.iter().all(|param| {
                        matches!(&*ctx.borrow_desc(ctx.repr(*param)), TypeDesc::Tvar(..))
                    });
                if !plain_params {
                    return Err(Fallback);
                }
                // An annotation `(e: t)`: the annotated type is `t`.
                if var != NO_VAR {
                    let annotated =
                        *vars[var as usize].get_or_insert_with(|| ctx.new_var(None));
                    steps.unification();
                    crate::types::ctype::unify(
                        ctx,
                        &mut tctx.unify_state,
                        annotated,
                        ctx.new_constr(path, Vec::new()),
                    )
                    .map_err(|_| Fallback)?;
                }
                Resolved::Type(path)
            }
        };
        // The labels of a record expression or pattern are consecutive, and
        // all of the record's.
        if !grouped
            && let Some((_, position, len)) = record_expression.take()
            && position != len
        {
            return Err(Fallback);
        }
        tctx.typed.derived.set_resolved(obligation, resolved);
    }
    if let Some((_, position, len)) = record_expression
        && position != len
    {
        return Err(Fallback);
    }

    // The type source `ResultOf(obligation, applied)`: of the function the
    // obligation resolved, the one parameter that remains after `applied`
    // were supplied, and its result (typecore.ml `type_application`, total
    // application of a partial application's result).
    let (result_of, applied) = match binding.ty {
        TypeSource::ResultOf {
            obligation,
            applied,
        } => (obligation, applied),
        // The type the body's own shape states, its variables unified by
        // the obligations.
        TypeSource::Stated(skeleton) => {
            let (ty, _) = instantiate(
                ctx,
                arena,
                &tctx.typed.derived,
                plans.skeleton_from(skeleton),
                vars,
            );
            return Ok(ty);
        }
    };
    let head = tctx.typed.derived.resolved(result_of).instance();
    let head = crate::types::ctype::expand_head(ctx, env, head);
    let (param, result) = match &*ctx.borrow_desc(ctx.repr(head)) {
        TypeDesc::Tarrow { args, ret } => {
            let args = ctx.type_args(*args);
            if args.len() != applied as usize + 1 {
                return Err(Fallback);
            }
            let Some(param) = args.get(applied as usize) else {
                return Err(Fallback);
            };
            (param.typ, *ret)
        }
        _ => return Err(Fallback),
    };
    Ok(ctx.new_type(TypeDesc::Tarrow {
        args: ctx.new_type_args_from([TypeArg::new(ArgLabel::Nolabel, param)]),
        ret: result,
    }))
}

/// Instantiate the skeleton that starts `nodes`: the type, and the number of
/// nodes it spans. A variable slot is made at its first use and denoted by
/// its later uses.
/// Cost: O(nodes of the skeleton), one type node per skeleton node that is
/// not a repeated variable; recursion depth is the skeleton's depth. The
/// parameters of one arrow are gathered inline, up to four without a heap
/// allocation.
fn instantiate(
    ctx: &crate::types::context::TypeContext,
    arena: &ParseArena,
    table: &DerivedTable,
    nodes: &[SkeletonNode],
    vars: &mut [Option<TypeExprRef>],
) -> (TypeExprRef, usize) {
    // The `count` skeletons after the node, and the nodes they span.
    let children = |count: usize, vars: &mut [Option<TypeExprRef>]| {
        let mut used = 1;
        let mut types: SmallVec<[TypeExprRef; 4]> = SmallVec::new();
        for _ in 0..count {
            let (ty, span) = instantiate(ctx, arena, table, &nodes[used..], vars);
            types.push(ty);
            used += span;
        }
        (types, used)
    };
    match nodes[0] {
        SkeletonNode::Var(slot) => {
            (*vars[slot as usize].get_or_insert_with(|| ctx.new_var(None)), 1)
        }
        SkeletonNode::Arrow { params } => {
            let mut used = 1;
            let mut args: SmallVec<[TypeArg; 4]> = SmallVec::new();
            for _ in 0..params {
                // An optional parameter holds an option of its type
                // (typecore.ml `type_function`, `type_option`).
                let label = match nodes[used] {
                    SkeletonNode::Optional(label) => {
                        used += 1;
                        Some(label)
                    }
                    _ => None,
                };
                let (param, span) = instantiate(ctx, arena, table, &nodes[used..], vars);
                used += span;
                args.push(match label {
                    None => TypeArg::new(ArgLabel::Nolabel, param),
                    Some(label) => TypeArg::new(
                        ArgLabel::optional(arena.get_string(label), crate::types::DeclLoc::none()),
                        ctx.new_predef_constr(crate::types::predef::path_option(), vec![param]),
                    ),
                });
            }
            let (ret, span) = instantiate(ctx, arena, table, &nodes[used..], vars);
            let arrow = ctx.new_type(TypeDesc::Tarrow {
                args: ctx.new_type_args_from(args),
                ret,
            });
            (arrow, used + span)
        }
        SkeletonNode::Named { ty, args } => {
            let (types, used) = children(args as usize, vars);
            (ctx.new_constr(table.resolved(ty).path(), types.into_vec()), used)
        }
        SkeletonNode::Tuple { len } => {
            let (types, used) = children(len as usize, vars);
            (ctx.new_type(TypeDesc::Ttuple(ctx.new_type_list(&types))), used)
        }
        SkeletonNode::Predef { ty, args } => {
            let (types, used) = children(args as usize, vars);
            let ty = match ty {
                Predef::String => crate::types::ctype::instance(ctx, ctx.predef_string()),
                Predef::Option => {
                    ctx.new_predef_constr(crate::types::predef::path_option(), types.into_vec())
                }
                Predef::Array => {
                    ctx.new_predef_constr(crate::types::predef::path_array(), types.into_vec())
                }
                Predef::Result => {
                    ctx.new_predef_constr(crate::types::predef::path_result(), types.into_vec())
                }
                Predef::Int => crate::types::ctype::instance(ctx, ctx.predef_int()),
                Predef::Bool => crate::types::ctype::instance(ctx, ctx.predef_bool()),
            };
            (ty, used)
        }
        SkeletonNode::Optional(_) => unreachable!("an optional marker precedes a parameter"),
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use crate::binary_ast::derive::fixtures::{
        CURRIED_LIBRARY, DECLARATIONS, FAILING, derive_source,
    };
    use crate::context::IdGenerator;
    use crate::parser::ast::Attributes;
    use crate::parser::{Parser, module};
    use crate::types::context::TypeContext;
    use crate::types::decl::SignatureItem;
    use crate::types::initial_env;

    #[test]
    fn census_counts_value_scheme_levels_without_changing_them() {
        let ctx = type_context();
        let local = ctx.new_var(None);
        let generic = ctx.new_generic_type(TypeDesc::Tvar(None));
        let mut steps = CensusSteps::default();
        for _ in 0..10_000 {
            steps.value_scheme(&ctx, local);
            steps.value_scheme(&ctx, generic);
        }
        assert_eq!(steps.value_schemes, [10_000, 10_000]);
        assert_ne!(ctx.get_level(local), crate::types::type_expr::GENERIC_LEVEL);
        assert_eq!(ctx.get_level(generic), crate::types::type_expr::GENERIC_LEVEL);
    }

    #[test]
    fn sizes_are_pinned() {
        assert_eq!(std::mem::size_of::<Option<Resolved>>(), 16);
        assert_eq!(std::mem::size_of::<Option<Bound>>(), 32);
    }

    pub(crate) fn type_context() -> TypeContext {
        crate::ident::Ident::set_current_time(999);
        let id_gen = IdGenerator::with_start_stamp(999);
        let _ = id_gen.next_stamp();
        TypeContext::new(std::sync::Arc::new(id_gen))
    }

    /// The values a program declares, with their printed types, and how many
    /// items were discharged; `Err` is the type error. With `plans`, a
    /// program one of whose plans cannot be used is checked again without,
    /// as the driver does, and reports no discharged item.
    fn check(source: &str, plans: bool) -> Result<(Vec<(String, String)>, usize), String> {
        check_with(derive_source, source, plans)
    }

    /// [`check`] of a program after the record library, through the whole
    /// front end.
    fn check_records(source: &str, plans: bool) -> Result<(Vec<(String, String)>, usize), String> {
        check_with(crate::binary_ast::derive::fixtures::frontend_source, source, plans)
    }

    fn check_with(
        parse: fn(&str, bool) -> (Parser<'static>, Vec<crate::parser::ast::StructureItem>),
        source: &str,
        plans: bool,
    ) -> Result<(Vec<(String, String)>, usize), String> {
        let (parser, structure) = parse(source, plans);
        let arena = parser.arena();
        let type_ctx = type_context();
        let mut tctx = TypeCheckContext::new(&type_ctx, arena);
        let env = initial_env(&type_ctx);
        let typed = crate::types::typemod::type_structure(&mut tctx, &env, arena, &structure);
        if tctx.derived_fallback {
            assert!(plans && typed.is_err());
            return check_with(parse, source, false);
        }
        let (typed, _) = typed.map_err(|error| format!("{error:?}"))?;
        let values = typed
            .str_type
            .iter()
            .filter_map(|item| match item {
                SignatureItem::SigValue(id, desc) => Some((
                    id.name().to_string(),
                    crate::types::printtyp::Printtyp::new(&type_ctx).type_expr(desc.val_type),
                )),
                _ => None,
            })
            .collect();
        Ok((values, tctx.typed.derived.discharged()))
    }

    /// A discharged binding has the type inference gives its general form.
    #[test]
    fn a_discharge_records_the_types_of_the_general_form() {
        for source in DECLARATIONS {
            let (planned, discharged) = check(source, true).unwrap();
            let (general, none) = check(source, false).unwrap();
            assert_eq!(discharged, source.matches("type ").count());
            assert_eq!(none, 0);
            assert_eq!(planned, general, "{source}");
        }
    }

    /// A declaration inside a module expression is discharged like one at
    /// the top level, and its bindings get the types of the general form.
    #[test]
    fn a_nested_item_is_discharged() {
        for (source, items) in crate::binary_ast::derive::fixtures::NESTED {
            let (planned, discharged) = check(source, true).unwrap();
            let (general, none) = check(source, false).unwrap();
            assert_eq!(discharged, items, "{source}");
            assert_eq!(none, 0);
            assert!(!planned.is_empty());
            assert_eq!(planned, general, "{source}");
        }
    }

    /// The bindings of a record's plan get the types inference gives its
    /// general form: fields of every kind, constant keys and defaults, a
    /// record of records, and labels another record declares too. The
    /// library's `Dict.fromArray`, `Dict.get` and `++` are primitives.
    #[test]
    fn a_record_is_discharged_with_the_types_of_the_general_form() {
        for (source, items) in [
            ("@spice type t = {x: int}", 1),
            ("@spice type t = {label: string, value: array<option<int>>}", 1),
            ("@spice type t = {a: option<string>, b?: int, c: Null.t<float>}", 1),
            (
                "@spice type t = {@spice.key(\"k\") a: int, @spice.default(0) b: int, @spice.default(1.5) c: float, d?: bool}",
                1,
            ),
            ("@spice type inner = {value: int}\n@spice.decode type outer = {one: inner}", 2),
            ("@spice type a = {x: int}\n@spice.encode type b = {x: int, y: string}", 2),
        ] {
            let (planned, discharged) = check_records(source, true).unwrap();
            let (general, none) = check_records(source, false).unwrap();
            assert_eq!(discharged, items, "{source}");
            assert_eq!(none, 0);
            let codecs = |values: &[(String, String)]| {
                values
                    .iter()
                    .filter(|(name, _)| name.contains("_encode") || name.contains("_decode"))
                    .cloned()
                    .collect::<Vec<_>>()
            };
            assert!(!codecs(&planned).is_empty());
            assert_eq!(codecs(&planned), codecs(&general), "{source}");
        }
    }

    /// A record whose plan does not hold is left to the general form, with
    /// its diagnostic: a shadowed `Ok`, a default of another type, a field
    /// type without codecs, a label a later record redeclares.
    #[test]
    fn a_record_with_a_failed_obligation_is_general() {
        for source in [
            "type mine = Ok(int) | Bad\n@spice type r = {a: int}",
            "@spice type t = {@spice.default(\"x\") b: int}",
            "@spice type t = {@spice.key(1) b: int}",
            "type plain = {p: int}\n@spice type t = {a: plain}",
            "@spice.decode type t = private {a: int}",
        ] {
            let planned = check_records(source, true).unwrap_err();
            let general = check_records(source, false).unwrap_err();
            assert_eq!(planned, general, "{source}");
        }
    }

    /// A failed obligation abandons the unit, which is then checked from
    /// the syntax of its derived code.
    #[test]
    fn a_failed_obligation_abandons_the_unit() {
        for source in FAILING {
            let planned = check(source, true).unwrap_err();
            let general = check(source, false).unwrap_err();
            assert_eq!(planned, general, "{source}");
        }
        // A library of another shape: the obligation fails and the syntax
        // types.
        let curried = CURRIED_LIBRARY;
        let (planned, discharged) = check(curried, true).unwrap();
        assert_eq!(discharged, 0);
        assert_eq!(planned, check(curried, false).unwrap().0);
    }

    #[derive(Default, Debug, PartialEq)]
    struct Counted {
        lookups: usize,
        instances: usize,
        unifications: usize,
    }

    impl Steps for Counted {
        fn lookup(&mut self) {
            self.lookups += 1;
        }
        fn instance(&mut self) {
            self.instances += 1;
        }
        fn unification(&mut self) {
            self.unifications += 1;
        }
    }

    /// Push an item of one binding with `count` value obligations for the
    /// names `names(i)`, each used at its own fresh type, whose type is that
    /// of the first.
    fn push_item(
        arena: &mut ParseArena,
        count: u32,
        names: impl Fn(u32) -> &'static str,
    ) -> DerivedIdx {
        use crate::binary_ast::derive::plan::BodyIdx;
        let first = arena.plans().next_binding();
        let start = arena.plans().next_obligation();
        for i in 0..count {
            let name = arena.intern_string(names(i));
            let name = arena.push_lident_from_idx(name);
            let name_loc = arena.none_loc();
            let plans = arena.plans_mut();
            let skeleton = plans.push_skeleton(SkeletonNode::Var(i));
            plans.push_obligation(Obligation::Value {
                name,
                name_loc,
                skeleton,
                expr_loc: ExprLoc::Dummy,
                called: false,
            });
        }
        let name = arena.intern_string("derived");
        let plans = arena.plans_mut();
        plans.push_binding(Binding {
            name,
            attributes: Attributes::new(),
            obligations: Span {
                start: start.0,
                len: count,
            },
            body: BodyIdx(0),
            vars: count,
            ty: TypeSource::ResultOf {
                obligation: start,
                applied: 0,
            },
        });
        plans.push_item(first)
    }

    /// Type `source`, then run `test` on a context whose arena holds the
    /// item `push_item` made.
    fn with_item(
        source: &'static str,
        count: u32,
        names: impl Fn(u32) -> &'static str,
        test: impl FnOnce(&mut TypeCheckContext<'_>, &Env, DerivedIdx, &TypeContext),
    ) {
        let mut parser = Parser::new("Test.res", source);
        let structure = module::parse_structure(&mut parser);
        assert!(!parser.has_errors());
        let item = push_item(parser.arena_mut(), count, names);
        crate::types::typecore::prepare_typecheck_arena(parser.arena_mut());
        let arena = parser.arena();
        let type_ctx = type_context();
        let mut tctx = TypeCheckContext::new(&type_ctx, arena);
        let env = initial_env(&type_ctx);
        let (_, env) =
            crate::types::typemod::type_structure(&mut tctx, &env, arena, &structure).unwrap();
        test(&mut tctx, &env, item, &type_ctx);
    }

    /// A record of `fields` `int` fields, typed up to its derived item:
    /// `test` gets the context, the environment before the item, the item
    /// and the parse arena's plans.
    pub(crate) fn with_record(
        fields: usize,
        test: impl FnOnce(&mut TypeCheckContext<'_>, &Env, DerivedIdx, &TypeContext),
    ) {
        with_record_type(fields, "int", test);
    }

    /// Test-only setup: O(fields) generated source and normal frontend work.
    pub(crate) fn with_record_type(
        fields: usize,
        typ: &str,
        test: impl FnOnce(&mut TypeCheckContext<'_>, &Env, DerivedIdx, &TypeContext),
    ) {
        let labels: Vec<String> = (0..fields).map(|i| format!("f{i}: {typ}")).collect();
        let source = format!("@spice type t = {{{}}}", labels.join(", "));
        let (parser, structure) =
            crate::binary_ast::derive::fixtures::frontend_source(&source, true);
        let (derived, before) = structure.split_last().unwrap();
        let crate::parser::ast::StructureItemDesc::Pstr_derived(item) = derived.pstr_desc else {
            panic!("the record takes a plan")
        };
        let arena = parser.arena();
        let type_ctx = type_context();
        let mut tctx = TypeCheckContext::new(&type_ctx, arena);
        let env = initial_env(&type_ctx);
        let (_, env) =
            crate::types::typemod::type_structure(&mut tctx, &env, arena, before).unwrap();
        test(&mut tctx, &env, item, &type_ctx);
    }

    /// Count the discharge of one-argument constructors. Test-only cost:
    /// O(constructors), plus parsing and checking the declaration.
    fn variant_discharge(constructors: usize) -> Counted {
        use std::fmt::Write;
        let mut source = String::from("@spice type t = ");
        for i in 0..constructors {
            write!(source, " | C{i}(int)").unwrap();
        }
        let (parser, structure) =
            crate::binary_ast::derive::fixtures::frontend_source(&source, true);
        let (derived, before) = structure.split_last().unwrap();
        let crate::parser::ast::StructureItemDesc::Pstr_derived(item) = derived.pstr_desc else {
            panic!("the variant takes a plan")
        };
        let arena = parser.arena();
        let type_ctx = type_context();
        let mut tctx = TypeCheckContext::new(&type_ctx, arena);
        let env = initial_env(&type_ctx);
        let (_, env) = crate::types::typemod::type_structure(&mut tctx, &env, arena, before).unwrap();
        let mut steps = Counted::default();
        discharge_counting(&mut tctx, &env, item, &mut steps).unwrap();
        steps
    }

    #[test]
    fn ten_thousand_variant_constructors_discharge_in_linear_steps() {
        let one = variant_discharge(1);
        let two = variant_discharge(2);
        let many = variant_discharge(10_000);
        assert_eq!(one, Counted { lookups: 33, instances: 27, unifications: 30 });
        assert_eq!(two, Counted { lookups: 56, instances: 47, unifications: 53 });
        assert_eq!(many, Counted { lookups: 230_010, instances: 200_007, unifications: 230_007 });
        assert_eq!(many.lookups, one.lookups + 9_999 * (two.lookups - one.lookups));
        assert_eq!(many.instances, one.instances + 9_999 * (two.instances - one.instances));
        assert_eq!(many.unifications, one.unifications + 9_999 * (two.unifications - one.unifications));
    }

    /// The discharge of a record's item is linear in its fields, with an
    /// exact count per field: its 22 obligations (3 in the encoder, 3 in
    /// its JSON twin, 16 in the decoder) take one lookup each, the 16 that
    /// are values, constructors or labels of the record expression one
    /// instance each (a field access instantiates inside the checker's
    /// lookup, a type has none), and one counted unification each (a label
    /// or a constructor unifies its argument and its result).
    #[test]
    fn ten_thousand_json_fields_discharge_in_linear_steps() {
        let count = |fields| {
            let mut steps = Counted::default();
            with_record_type(fields, "JSON.t", |tctx, env, item, _| {
                discharge_counting(tctx, env, item, &mut steps).unwrap();
            });
            steps
        };
        let (one, two, many) = (count(1), count(2), count(10_000));
        assert_eq!(one, Counted { lookups: 32, instances: 23, unifications: 32 });
        assert_eq!(two, Counted { lookups: 52, instances: 37, unifications: 55 });
        assert_eq!(many, Counted { lookups: 200_012, instances: 140_009, unifications: 230_009 });
        assert_eq!(many.lookups, one.lookups + 9_999 * (two.lookups - one.lookups));
        assert_eq!(many.instances, one.instances + 9_999 * (two.instances - one.instances));
        assert_eq!(many.unifications, one.unifications + 9_999 * (two.unifications - one.unifications));
    }

    #[test]
    fn constructor_descriptions_are_shared_within_each_binding() {
        assert_eq!(std::mem::size_of::<(u32, u32)>(), 8);
        let mut sizes = Vec::new();
        for fields in [1, 2, 10_000] {
            with_record(fields, |tctx, env, item, _| {
                discharge_counting(tctx, env, item, &mut ()).unwrap();
                sizes.push(tctx.typed.derived.constructors.len());
                assert_eq!(tctx.typed.derived.constructor_names.len(), tctx.arena.string_count());
            });
        }
        assert_eq!(sizes, [7, 7, 7]);
    }

    #[test]
    fn a_record_of_ten_thousand_fields_is_discharged_in_linear_steps() {
        let steps = |fields: usize| {
            let mut steps = Counted::default();
            with_record(fields, |tctx, env, item, _| {
                discharge_counting(tctx, env, item, &mut steps).unwrap();
            });
            steps
        };
        let (one, two, many) = (steps(1), steps(2), steps(10_000));
        let per_field = Counted {
            lookups: two.lookups - one.lookups,
            instances: two.instances - one.instances,
            unifications: two.unifications - one.unifications,
        };
        assert_eq!(
            per_field,
            Counted {
                lookups: 22,
                instances: 16,
                unifications: 22
            }
        );
        assert_eq!(many.lookups, one.lookups + 9_999 * per_field.lookups);
        assert_eq!(many.instances, one.instances + 9_999 * per_field.instances);
        assert_eq!(many.unifications, one.unifications + 9_999 * per_field.unifications);
    }

    /// An item with 10,000 obligations performs exactly 10,000 lookups,
    /// 10,000 instances and 10,000 unifications.
    #[test]
    fn ten_thousand_obligations_take_ten_thousand_steps_each() {
        with_item("let f = (x: int) => x", 10_000, |_| "f", |tctx, env, item, type_ctx| {
            let mut steps = Counted::default();
            let discharged = discharge_counting(tctx, env, item, &mut steps).unwrap();
            assert_eq!(
                steps,
                Counted {
                    lookups: 10_000,
                    instances: 10_000,
                    unifications: 10_000
                }
            );
            let bound: Vec<Bound> = tctx.typed.derived.bound(item).collect();
            assert_eq!(bound.len(), 1);
            assert_eq!(bound[0].ident.name(), "derived");
            assert_eq!(
                crate::types::printtyp::Printtyp::new(type_ctx).type_expr(bound[0].ty),
                "int => int"
            );
            // The signature item is the description that was entered.
            let entered = discharged.env.lookup_value(&Path::pident(bound[0].ident)).unwrap();
            assert_eq!(
                discharged.sig_items,
                [SignatureItem::SigValue(bound[0].ident, entered.clone())]
            );
        });
    }

    /// A discharge stops at the first obligation that fails, and records
    /// the deprecated uses of the ones that hold.
    #[test]
    fn a_discharge_stops_at_the_first_failed_obligation() {
        use crate::binary_ast::derive::plan::BodyIdx;
        let source = "module M = {\n  @deprecated(\"old\") let take = (x: int) => x\n}\nlet one = 1";
        // `M.take` at 'a => 'b, `one` at 'a, then, unless `complete`, a name
        // that is not bound.
        let run = |complete: bool| {
            let mut parser = Parser::new("Test.res", source);
            let structure = module::parse_structure(&mut parser);
            assert!(!parser.has_errors());
            let arena = parser.arena_mut();
            let first = arena.plans().next_binding();
            let start = arena.plans().next_obligation();
            let name_loc = arena.none_loc();
            let obligation = |arena: &mut ParseArena, name: &[&str], skeleton: &[SkeletonNode]| {
                let mut lid = crate::parser::longident::Longident::Lident(arena.intern_string(name[0]));
                for part in &name[1..] {
                    lid = crate::parser::longident::Longident::Ldot(Box::new(lid), arena.intern_string(part));
                }
                let name = arena.push_longident(lid);
                let plans = arena.plans_mut();
                let first = plans.push_skeleton(skeleton[0]);
                for node in &skeleton[1..] {
                    plans.push_skeleton(*node);
                }
                plans.push_obligation(Obligation::Value {
                    name,
                    name_loc,
                    skeleton: first,
                    expr_loc: ExprLoc::Dummy,
                    called: true,
                });
            };
            let take = [
                SkeletonNode::Arrow { params: 1 },
                SkeletonNode::Var(0),
                SkeletonNode::Var(1),
            ];
            obligation(arena, &["M", "take"], &take);
            obligation(arena, &["one"], &[SkeletonNode::Var(0)]);
            if !complete {
                obligation(arena, &["missing"], &[SkeletonNode::Var(2)]);
            }
            let name = arena.intern_string("derived");
            let plans = arena.plans_mut();
            let len = plans.next_obligation().0 - start.0;
            plans.push_binding(Binding {
                name,
                attributes: Attributes::new(),
                obligations: Span { start: start.0, len },
                body: BodyIdx(0),
                vars: 3,
                ty: TypeSource::ResultOf {
                    obligation: start,
                    applied: 0,
                },
            });
            let item = plans.push_item(first);
            crate::types::typecore::prepare_typecheck_arena(parser.arena_mut());
            let arena = parser.arena();
            let type_ctx = type_context();
            let mut tctx = TypeCheckContext::new(&type_ctx, arena);
            let env = initial_env(&type_ctx);
            let (_, env) =
                crate::types::typemod::type_structure(&mut tctx, &env, arena, &structure).unwrap();
            let warnings = tctx.warnings.len();
            let mut steps = Counted::default();
            let result = discharge_counting(&mut tctx, &env, item, &mut steps);
            (result.map(|_| ()), steps, tctx.warnings.len() - warnings)
        };

        let (result, steps, _) = run(false);
        assert_eq!(result, Err(Fallback));
        assert_eq!(
            steps,
            Counted {
                lookups: 3,
                instances: 2,
                unifications: 2
            }
        );
        let (result, _, warnings) = run(true);
        assert_eq!(result, Ok(()));
        assert_eq!(warnings, 1);
    }

    /// A type obligation resolves a constructor that skeletons then name.
    #[test]
    fn a_type_obligation_names_a_constructor() {
        use crate::binary_ast::derive::plan::BodyIdx;
        let source = "type box<'a> = {v: 'a}\nlet make = (x: int): box<int> => {v: x}";
        for (arity, discharges) in [(1u16, true), (2, false)] {
            let mut parser = Parser::new("Test.res", source);
            let structure = module::parse_structure(&mut parser);
            let arena = parser.arena_mut();
            let first = arena.plans().next_binding();
            let box_name = arena.intern_string("box");
            let box_name = arena.push_lident_from_idx(box_name);
            let make = arena.intern_string("make");
            let make = arena.push_lident_from_idx(make);
            let name_loc = arena.none_loc();
            let name = arena.intern_string("derived");
            let plans = arena.plans_mut();
            let ty = plans.push_obligation(Obligation::Type {
                name: box_name,
                name_loc,
                arity,
                var: crate::binary_ast::derive::plan::NO_VAR,
            });
            // make : 'a => box<'a>
            let skeleton = plans.push_skeleton(SkeletonNode::Arrow { params: 1 });
            plans.push_skeleton(SkeletonNode::Var(0));
            plans.push_skeleton(SkeletonNode::Named { ty, args: 1 });
            plans.push_skeleton(SkeletonNode::Var(0));
            let value = plans.push_obligation(Obligation::Value {
                name: make,
                name_loc,
                skeleton,
                expr_loc: ExprLoc::Dummy,
                called: true,
            });
            plans.push_binding(Binding {
                name,
                attributes: Attributes::new(),
                obligations: Span { start: ty.0, len: 2 },
                body: BodyIdx(0),
                vars: 1,
                ty: TypeSource::ResultOf {
                    obligation: value,
                    applied: 0,
                },
            });
            let item = plans.push_item(first);
            crate::types::typecore::prepare_typecheck_arena(parser.arena_mut());
            let arena = parser.arena();
            let type_ctx = type_context();
            let mut tctx = TypeCheckContext::new(&type_ctx, arena);
            let env = initial_env(&type_ctx);
            let (_, env) =
                crate::types::typemod::type_structure(&mut tctx, &env, arena, &structure).unwrap();
            let result = discharge(&mut tctx, &env, item);
            assert_eq!(result.is_ok(), discharges);
            if discharges {
                let bound: Vec<Bound> = tctx.typed.derived.bound(item).collect();
                assert_eq!(
                    crate::types::printtyp::Printtyp::new(&type_ctx).type_expr(bound[0].ty),
                    "int => box<int>"
                );
                assert_eq!(tctx.typed.derived.resolved(ty).path().name(), "box");
            }
        }
    }
}

#[cfg(test)]
#[test]
fn census_observer_has_one_inline_obligation_and_two_counts() {
    assert_eq!(std::mem::size_of::<CensusSteps>(), 32);
    let mut observer = CensusSteps::default();
    for _ in 0..10_000 {
        observer.obligation(Obligation::Type {
            name: crate::parse_arena::LidentIdx(0),
            name_loc: crate::parse_arena::LocIdx(0), arity: 0, var: NO_VAR,
        });
    }
    assert!(matches!(observer.last, Some(Obligation::Type { .. })));
}
