//! The checker's side of a derived item (`Pstr_derived`).
//!
//! [`discharge`] establishes the obligations of the item's plan in order and
//! enters its bindings in the environment without typing a body: per value
//! obligation one lookup, one instance and one unification with the
//! obligation's skeleton. When an obligation fails it undoes what it did and
//! reports [`Fallback`]; the caller then types the item's general form, so
//! every diagnostic comes from the code that types syntax.
//!
//! What a discharge records is in two dense tables of the typed arena,
//! indexed by the plan's binding and obligation handles: the identifier,
//! type and environment of each binding, and what each obligation resolved
//! to. The readers of the typed tree (`Tstr_derived`) reach them without a
//! lookup structure.
//! (`compiler-rust/docs/DERIVED_CODECS.md`, "The cheapest sound path".)

use smallvec::SmallVec;

use crate::binary_ast::derive::plan::{
    Binding, BindingIdx, DerivedIdx, ExprLoc, Obligation, ObligationIdx, Plans, SkeletonNode, Span,
};
use crate::ident::Ident;
use crate::parse_arena::ParseArena;
use crate::types::env::Env;
use crate::types::path::Path;
use crate::types::asttypes::ArgLabel;
use crate::types::type_expr::{TypeArg, TypeDesc, TypeExprRef};
use crate::types::typecore::{RecArg, TypeCheckContext};
use crate::types::typedtree::EnvRef;

/// Why the walks over the structure of a module expression have no case for
/// a derived item: the seam plans an item only at the top level of a unit
/// (`derive::Scope`), and everything nested keeps its value group.
pub(crate) const TOP_LEVEL_ONLY: &str =
    "a derived item is planned only at the top level of a unit";

/// What a discharged obligation resolved to.
#[derive(Debug, Clone, Copy)]
pub enum Resolved {
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
}

impl Resolved {
    /// The path the name resolved to. Cost: O(1).
    #[inline]
    pub fn path(self) -> Path {
        match self {
            Resolved::Value { path, .. } | Resolved::Type(path) => path,
        }
    }

    /// The instance of a value's type. Cost: O(1).
    #[inline]
    pub fn instance(self) -> TypeExprRef {
        match self {
            Resolved::Value { instance, .. } => instance,
            Resolved::Type(_) => unreachable!("a body and a type source name value obligations"),
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
}

impl DerivedTable {
    /// Make room for every binding and obligation of `plans`.
    /// Cost: O(1) when the tables already have that size, which is every call
    /// but the first of a compilation; the first is O(bindings + obligations
    /// of the unit), one allocation per table.
    pub fn reserve(&mut self, plans: &Plans) {
        if self.resolved.len() != plans.obligation_count() {
            self.resolved.resize(plans.obligation_count(), None);
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

    /// The results of the obligations of a discharged item, in typing order.
    /// Cost: O(1) to obtain; one slot read per obligation yielded.
    pub fn resolved_of(&self, idx: DerivedIdx) -> impl Iterator<Item = Resolved> + '_ {
        self.resolved[self.items[idx.index()].obligations.range()]
            .iter()
            .map(|resolved| resolved.expect("the obligations of a typed derived item are discharged"))
    }
}

/// The item cannot be established from its plan: the checker types its
/// general form instead. Nothing the failed discharge did remains: the type
/// state is restored, and the warnings and deprecated uses it recorded are
/// dropped.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Fallback;

/// A discharged item: `Tstr_derived` with its tables filled.
#[derive(Debug)]
pub struct Discharged {
    /// The environment extended with the item's bindings.
    pub env: Env,
}

/// The steps of a discharge, for the tests that prove its cost. The checker
/// passes `()`, whose methods are empty.
pub trait Steps {
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

/// Discharge the obligations of a derived item and enter its bindings.
/// Cost: O(obligations + skeleton nodes of the item): per value obligation
/// one environment lookup, one instance of the value's type and one
/// unification; per binding one function type and one environment entry. One
/// snapshot of the type state per item; no allocation per obligation beyond
/// the type nodes of the instances and skeletons.
pub fn discharge(
    tctx: &mut TypeCheckContext<'_>,
    env: &Env,
    item: DerivedIdx,
) -> Result<Discharged, Fallback> {
    discharge_counting(tctx, env, item, &mut ())
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

    let warnings = tctx.warnings.len();
    let deprecated_uses = tctx.type_ctx.deprecated_use_count();
    // `Typecore.type_binding` starts with `Typetexp.reset_type_variables`.
    tctx.reset_type_variables();
    tctx.set_unify_env(env);
    let ctx = tctx.type_ctx;
    let snapshot = ctx.snapshot_type_state();
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
    if established.is_err() {
        ctx.restore_type_state(snapshot);
        tctx.warnings.truncate(warnings);
        ctx.truncate_deprecated_uses(deprecated_uses);
        return Err(Fallback);
    }
    drop(snapshot);

    // typecore.ml `type_let`: every binding is a function, so its type is
    // generalised in full, and the bound variables enter the environment in
    // binding order with the description of a let-bound variable.
    let mut new_env = env.clone();
    let env_ref = ctx.store_typed_env(env);
    let val_loc = tctx.intern_ast_loc(arena, arena.none_loc());
    for (i, binding) in bindings.iter().enumerate() {
        let binding_idx = BindingIdx(item.bindings.start + i as u32);
        let ty = tctx.typed.derived.pending[binding_idx.index()];
        crate::types::ctype::generalize(ctx, ty);
        let ident = ctx.create_ident(arena.name(binding.name));
        new_env.add_value(
            ident,
            crate::types::decl::ValueDescription {
                val_type: ty,
                val_kind: crate::types::decl::ValueKind::ValReg,
                val_loc,
                val_attributes: Default::default(),
                val_path: None,
            },
        );
        tctx.typed.derived.set_bound(
            binding_idx,
            Bound {
                ident,
                ty,
                env: env_ref,
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
    Ok(Discharged { env: new_env })
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
    for slot in binding.obligations.range() {
        let obligation = ObligationIdx(slot as u32);
        let resolved = match plans.obligation(obligation) {
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
                // A primitive is not a plain value to the backend.
                if !matches!(desc.val_kind, crate::types::decl::ValueKind::ValReg) {
                    return Err(Fallback);
                }
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
                steps.instance();
                let instance = crate::types::ctype::instance(ctx, desc.val_type);
                let (expected, _) = instantiate(
                    ctx,
                    &tctx.typed.derived,
                    plans.skeleton_from(skeleton),
                    vars,
                );
                // typecore.ml `type_expect` of an identifier: the instance
                // against the expected type, in this order.
                steps.unification();
                crate::types::ctype::unify(ctx, &mut tctx.unify_state, instance, expected)
                    .map_err(|_| Fallback)?;
                Resolved::Value { path, instance }
            }
            Obligation::Type {
                name,
                name_loc,
                arity,
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
                Resolved::Type(path)
            }
        };
        tctx.typed.derived.set_resolved(obligation, resolved);
    }

    // The type source `ResultOf(obligation, applied)`: of the function the
    // obligation resolved, the one parameter that remains after `applied`
    // were supplied, and its result (typecore.ml `type_application`, total
    // application of a partial application's result).
    let head = tctx.typed.derived.resolved(binding.result_of).instance();
    let head = crate::types::ctype::expand_head(ctx, env, head);
    let (param, result) = match &*ctx.borrow_desc(ctx.repr(head)) {
        TypeDesc::Tarrow { args, ret } => {
            let args = ctx.type_args(*args);
            if args.len() != binding.applied as usize + 1 {
                return Err(Fallback);
            }
            let Some(param) = args.get(binding.applied as usize) else {
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
    table: &DerivedTable,
    nodes: &[SkeletonNode],
    vars: &mut [Option<TypeExprRef>],
) -> (TypeExprRef, usize) {
    match nodes[0] {
        SkeletonNode::Var(slot) => {
            (*vars[slot as usize].get_or_insert_with(|| ctx.new_var(None)), 1)
        }
        SkeletonNode::Arrow { params } => {
            let mut used = 1;
            let mut args: SmallVec<[TypeArg; 4]> = SmallVec::new();
            for _ in 0..params {
                let (param, span) = instantiate(ctx, table, &nodes[used..], vars);
                args.push(TypeArg::new(ArgLabel::Nolabel, param));
                used += span;
            }
            let (ret, span) = instantiate(ctx, table, &nodes[used..], vars);
            let arrow = ctx.new_type(TypeDesc::Tarrow {
                args: ctx.new_type_args_from(args),
                ret,
            });
            (arrow, used + span)
        }
        SkeletonNode::Named { ty, args } => {
            let mut used = 1;
            let mut types: SmallVec<[TypeExprRef; 4]> = SmallVec::new();
            for _ in 0..args {
                let (arg, span) = instantiate(ctx, table, &nodes[used..], vars);
                types.push(arg);
                used += span;
            }
            (ctx.new_constr(table.resolved(ty).path(), types.into_vec()), used)
        }
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use crate::binary_ast::derive::Scope;
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
    fn sizes_are_pinned() {
        assert_eq!(std::mem::size_of::<Option<Resolved>>(), 16);
        assert_eq!(std::mem::size_of::<Option<Bound>>(), 24);
    }

    pub(crate) fn type_context() -> TypeContext {
        crate::ident::Ident::set_current_time(999);
        let id_gen = IdGenerator::with_start_stamp(999);
        let _ = id_gen.next_stamp();
        TypeContext::new(std::sync::Arc::new(id_gen))
    }

    /// The values a program declares, with their printed types, and how many
    /// items were discharged; `Err` is the type error.
    fn check(source: &str, scope: Scope) -> Result<(Vec<(String, String)>, usize), String> {
        let (parser, structure) = derive_source(source, scope);
        let arena = parser.arena();
        let type_ctx = type_context();
        let mut tctx = TypeCheckContext::new(&type_ctx, arena);
        let env = initial_env(&type_ctx);
        let (typed, _) =
            crate::types::typemod::type_structure(&mut tctx, &env, arena, &structure)
                .map_err(|error| without_type_handles(&format!("{error:?}")))?;
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
        let discharged = tctx
            .typed
            .structure_items(typed.str_items)
            .iter()
            .filter(|item| matches!(item.str_desc, crate::types::typedtree::StructureItemDesc::Tstr_derived(_)))
            .count();
        Ok((values, discharged))
    }

    /// A printed error without the numbers of its type handles: a failed
    /// discharge leaves type nodes behind, so the general form's are later.
    fn without_type_handles(error: &str) -> String {
        let mut out = String::new();
        let mut rest = error;
        while let Some(at) = rest.find("TypeExprRef(") {
            let end = at + "TypeExprRef(".len();
            out.push_str(&rest[..end]);
            rest = rest[end..].trim_start_matches(|c: char| c.is_ascii_digit());
        }
        out + rest
    }

    /// A discharged binding has the type inference gives its general form.
    #[test]
    fn a_discharge_records_the_types_of_the_general_form() {
        for source in DECLARATIONS {
            let (planned, discharged) = check(source, Scope::TopLevel).unwrap();
            let (general, none) = check(source, Scope::Nested).unwrap();
            assert_eq!(discharged, source.matches("type ").count());
            assert_eq!(none, 0);
            assert_eq!(planned, general, "{source}");
        }
    }

    /// A failed obligation gives the diagnostic of the general form.
    #[test]
    fn a_failed_obligation_reports_as_the_general_form() {
        for source in FAILING {
            let planned = check(source, Scope::TopLevel).unwrap_err();
            let general = check(source, Scope::Nested).unwrap_err();
            assert_eq!(planned, general, "{source}");
        }
        // A library of another shape: the obligation fails, the general form
        // types, and the result is the same.
        let curried = CURRIED_LIBRARY;
        let (planned, discharged) = check(curried, Scope::TopLevel).unwrap();
        assert_eq!(discharged, 0);
        assert_eq!(planned, check(curried, Scope::Nested).unwrap().0);
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
        use crate::parse_arena::VbList;
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
            result_of: start,
            applied: 0,
        });
        plans.push_item(first, VbList::EMPTY)
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
            assert!(discharged.env.lookup_value(&Path::pident(bound[0].ident)).is_ok());
        });
    }

    /// A failed discharge leaves no warning, no deprecated use and no change
    /// of the type state behind.
    #[test]
    fn a_failed_discharge_restores_what_it_did() {
        use crate::binary_ast::derive::plan::BodyIdx;
        use crate::parse_arena::VbList;
        let source = "type cell<'a> = {mutable contents: option<'a>}\n\
            let weak = {contents: None}\n\
            module M = {\n  @deprecated(\"old\") let take = (x: cell<int>) => x\n}";
        // `weak` at 'a, then `take` at 'a => 'b, which makes the weak
        // variable `int`, then, unless `complete`, a name that is not bound.
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
            obligation(arena, &["weak"], &[SkeletonNode::Var(0)]);
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
                result_of: start,
                applied: 0,
            });
            let item = plans.push_item(first, VbList::EMPTY);
            crate::types::typecore::prepare_typecheck_arena(parser.arena_mut());
            let arena = parser.arena();
            let type_ctx = type_context();
            let mut tctx = TypeCheckContext::new(&type_ctx, arena);
            let env = initial_env(&type_ctx);
            let (_, env) =
                crate::types::typemod::type_structure(&mut tctx, &env, arena, &structure).unwrap();
            let state = |tctx: &TypeCheckContext<'_>| {
                let (_, weak) = env.find_value_arc_with_path(crate::name::Name::new("weak")).unwrap();
                (
                    tctx.warnings.len(),
                    type_ctx.deprecated_use_count(),
                    crate::types::printtyp::Printtyp::new(&type_ctx).type_expr(weak.val_type),
                    type_ctx.current_level(),
                )
            };
            let before = state(&tctx);
            let mut steps = Counted::default();
            let result = discharge_counting(&mut tctx, &env, item, &mut steps);
            (before, state(&tctx), result.map(|_| ()), steps)
        };

        let (before, after, result, steps) = run(false);
        assert_eq!(result, Err(Fallback));
        assert_eq!(
            steps,
            Counted {
                lookups: 3,
                instances: 2,
                unifications: 2
            }
        );
        assert_eq!(after, before);
        assert!(before.2.contains("cell<'"), "{}", before.2);

        // Without the unbound name the same obligations hold: the deprecated
        // use is recorded and warned about, and the weak variable is `int`.
        let (before, after, result, _) = run(true);
        assert_eq!(result, Ok(()));
        assert_eq!((after.0, after.1), (before.0 + 1, before.1 + 1));
        assert_eq!(after.2, "cell<int>");
        assert_eq!(after.3, before.3);
    }

    /// A type obligation resolves a constructor that skeletons then name.
    #[test]
    fn a_type_obligation_names_a_constructor() {
        use crate::binary_ast::derive::plan::BodyIdx;
        use crate::parse_arena::VbList;
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
                result_of: value,
                applied: 0,
            });
            let item = plans.push_item(first, VbList::EMPTY);
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
