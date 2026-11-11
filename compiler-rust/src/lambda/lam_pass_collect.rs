//! `Lam_pass_collect.collect_info` and `Lam_arity_analysis.get_arity` over
//! the Lambda arena.

use crate::ident::Ident;
use crate::lambda::arena::{Lam, LamArena, Node};
use crate::lambda::lam_arity::Arity;
use crate::lambda::lam_compat::FieldDbgInfo;
use crate::lambda::lam_compile_context::{
    BoxedNullable, ExternalArityInfo, ExternalArityTable, RecFlag,
};
use crate::lambda::lam_primitive::{Mutable, Primitive};
use crate::lambda::lam_stats::{Element, IdKind, IdentTable, LamStats};

/// Rust counterpart to `Lam_compile_env.query_external_id_info` for
/// `Lam_arity_analysis.get_arity` (compiler/core/lam_arity_analysis.ml:43-71).
pub type ExternalArityResolver<'a> = dyn FnMut(&Ident, &str) -> Option<ExternalArityInfo> + 'a;

/// `Lam_util.element_of_lambda` (lam_util.ml:188-196).
pub(crate) fn element_of_lambda(a: &LamArena, lam: Lam) -> Element {
    match a.node(lam) {
        Node::Var(_) | Node::Const(_) => Element::SimpleForm(lam),
        Node::Prim { .. } => match a.as_prim(lam) {
            Some((Primitive::Pfield(_, FieldDbgInfo::Module { .. }), [x], _))
                if matches!(a.node(*x), Node::GlobalModule(_) | Node::Var(_)) =>
            {
                Element::SimpleForm(lam)
            }
            _ => Element::Na,
        },
        _ => Element::Na,
    }
}

/// `Lam_util.kind_of_lambda_block` (lam_util.ml:198-200).
pub(crate) fn kind_of_lambda_block(a: &LamArena, xs: &[Lam]) -> IdKind {
    IdKind::ImmutableBlock(xs.iter().map(|x| element_of_lambda(a, *x)).collect())
}

/// `Lam_util.alias_ident_or_global` (lam_util.ml:140-152).
fn alias_ident_or_global(meta: &mut LamStats, k: Ident, v: &Ident, v_kind: IdKind) {
    match v_kind {
        IdKind::Na => {
            if let Some(info) = meta.ident_tbl.get(v).cloned() {
                meta.ident_tbl.insert(k, info);
            }
        }
        info => {
            meta.ident_tbl.insert(k, info);
        }
    }
}

fn lookup_external_arity_entry<'a>(
    external_arities: &'a ExternalArityTable,
    module_id: &Ident,
    field_name: &str,
) -> Option<&'a Option<ExternalArityInfo>> {
    external_arities
        .get(module_id.name())
        .and_then(|fields| fields.get(field_name))
}

fn resolve_external_arity(
    external_arities: &mut ExternalArityTable,
    module_id: &Ident,
    field_name: &str,
    resolver: &mut ExternalArityResolver<'_>,
) -> Option<ExternalArityInfo> {
    if let Some(cached) = lookup_external_arity_entry(external_arities, module_id, field_name) {
        return cached.clone();
    }
    let resolved = resolver(module_id, field_name);
    external_arities
        .entry(module_id.name().to_string())
        .or_default()
        .insert(field_name.to_string(), resolved.clone());
    resolved
}

/// `Lam_arity_analysis.get_arity` (lam_arity_analysis.ml:38-132).
fn get_arity_impl<F>(a: &LamArena, ident_tbl: &IdentTable, lam: Lam, external: &mut F) -> Arity
where
    F: FnMut(&Ident, &str) -> Option<ExternalArityInfo>,
{
    match a.node(lam) {
        // lam_arity_analysis.ml:25-31,40
        Node::Var(v) => match ident_tbl.get(&a.ident(v)) {
            Some(IdKind::FunctionId { arity, .. }) => arity.clone(),
            _ => Arity::na(),
        },
        Node::Const(_) => Arity::non_function(),
        Node::Let { body, .. } | Node::LetRec { body, .. } => {
            get_arity_impl(a, ident_tbl, body, external)
        }
        Node::Prim { .. } => {
            let (primitive, args, _) = a.as_prim(lam).expect("checked primitive");
            match (primitive, args) {
                // lam_arity_analysis.ml:43-56
                (Primitive::Pfield(_, FieldDbgInfo::Module { name }), [m])
                    if matches!(a.node(*m), Node::GlobalModule(_)) =>
                {
                    let Node::GlobalModule(id) = a.node(*m) else {
                        unreachable!()
                    };
                    match external(&a.ident(id), name) {
                        Some(ExternalArityInfo::Single(arity)) => arity,
                        Some(ExternalArityInfo::Submodule(_)) | None => Arity::na(),
                    }
                }
                // lam_arity_analysis.ml:57-71
                (Primitive::Pfield(index, _), [inner])
                    if matches!(
                        a.as_prim(*inner),
                        Some((Primitive::Pfield(_, FieldDbgInfo::Module { .. }), [m], _))
                            if matches!(a.node(*m), Node::GlobalModule(_))
                    ) =>
                {
                    let Some((Primitive::Pfield(_, FieldDbgInfo::Module { name }), [m], _)) =
                        a.as_prim(*inner)
                    else {
                        unreachable!()
                    };
                    let Node::GlobalModule(id) = a.node(*m) else {
                        unreachable!()
                    };
                    match external(&a.ident(id), name) {
                        Some(ExternalArityInfo::Submodule(arities)) => arities
                            .get(*index as usize)
                            .cloned()
                            .unwrap_or_else(Arity::na),
                        Some(ExternalArityInfo::Single(_)) | None => Arity::na(),
                    }
                }
                // lam_arity_analysis.ml:72
                (Primitive::Praise, _) => Arity::raise(),
                // lam_arity_analysis.ml:73-74
                _ => Arity::na(),
            }
        }
        Node::GlobalModule(_) => Arity::na(),
        // lam_arity_analysis.ml:88-105
        Node::Apply { func, args, .. } => match get_arity_impl(a, ident_tbl, func, external) {
            Arity::Na => Arity::na(),
            Arity::Info {
                mut arities,
                variadic,
            } => {
                let mut arg_length = a.list_len(args) as i32;
                loop {
                    match arities.first().copied() {
                        Some(x) if arg_length == x => {
                            arities.remove(0);
                            return Arity::info(arities, variadic);
                        }
                        Some(x) if arg_length > x => {
                            arities.remove(0);
                            arg_length -= x;
                        }
                        Some(x) => {
                            arities[0] = x - arg_length;
                            return Arity::info(arities, variadic);
                        }
                        None => {
                            return if variadic {
                                Arity::raise()
                            } else {
                                Arity::na()
                            };
                        }
                    }
                }
            }
        },
        // lam_arity_analysis.ml:106
        Node::Function { body, info } => {
            get_arity_impl(a, ident_tbl, body, external).merge(a.func_payload(info).arity)
        }
        // lam_arity_analysis.ml:107-122: the fail action comes first.
        Node::Switch { actions, info, .. } => {
            let acts = a.switch_actions(info, actions);
            let all: smallvec::SmallVec<[Lam; 8]> = acts
                .fail
                .into_iter()
                .chain(acts.consts.iter().copied())
                .chain(acts.blocks.iter().copied())
                .collect();
            all_lambdas(a, ident_tbl, &all, external)
        }
        // lam_arity_analysis.ml:123-126: the default comes first.
        Node::StringSwitch { actions, info, .. } => {
            let p = a.str_switch_payload(info);
            let acts = a.list(actions);
            let n = p.n_cases();
            let all: smallvec::SmallVec<[Lam; 8]> =
                acts[n..].iter().chain(acts[..n].iter()).copied().collect();
            all_lambdas(a, ident_tbl, &all, external)
        }
        // lam_arity_analysis.ml:127
        Node::StaticCatch { handler, .. } => get_arity_impl(a, ident_tbl, handler, external),
        // lam_arity_analysis.ml:128
        Node::TryWith { body, handler, .. } => {
            all_lambdas(a, ident_tbl, &[body, handler], external)
        }
        // lam_arity_analysis.ml: `Ltryfinally (body, _) -> get_arity meta body`
        Node::TryFinally { body, .. } => get_arity_impl(a, ident_tbl, body, external),
        // lam_arity_analysis.ml:129
        Node::If { then_, else_, .. } => all_lambdas(a, ident_tbl, &[then_, else_], external),
        // lam_arity_analysis.ml:130
        Node::Sequence(_, second) => get_arity_impl(a, ident_tbl, second, external),
        // lam_arity_analysis.ml:131
        Node::StaticRaise { .. } => Arity::na(),
        // lam_arity_analysis.ml:132
        Node::While(..)
        | Node::For { .. }
        | Node::ForOf { .. }
        | Node::ForAwaitOf { .. }
        | Node::Break
        | Node::Continue
        | Node::Assign { .. } => Arity::non_function(),
    }
}

/// `Lam_arity_analysis.all_lambdas` (lam_arity_analysis.ml:134-149).
fn all_lambdas<F>(a: &LamArena, ident_tbl: &IdentTable, xs: &[Lam], external: &mut F) -> Arity
where
    F: FnMut(&Ident, &str) -> Option<ExternalArityInfo>,
{
    let Some((y, ys)) = xs.split_first() else {
        return Arity::na();
    };
    let mut acc = get_arity_impl(a, ident_tbl, *y, external);
    for x in ys {
        let Arity::Info { arities, variadic } = acc else {
            return Arity::na();
        };
        match get_arity_impl(a, ident_tbl, *x, external) {
            Arity::Na => return Arity::na(),
            Arity::Info {
                arities: ya,
                variadic: vy,
            } => acc = Arity::merge_arities(&arities, &ya, variadic, vy),
        }
    }
    acc
}

/// Arity from the collected metadata and the external arities already
/// fetched.
pub fn get_arity(a: &LamArena, meta: &LamStats, lam: Lam) -> Arity {
    let external_arities = &meta.external_arities;
    let mut lookup = |module_id: &Ident, field_name: &str| {
        lookup_external_arity_entry(external_arities, module_id, field_name)
            .and_then(Option::as_ref)
            .cloned()
    };
    get_arity_impl(a, &meta.ident_tbl, lam, &mut lookup)
}

/// Arity, querying `resolver` for external modules not fetched yet.
pub(crate) fn get_arity_with_external_arity(
    a: &LamArena,
    meta: &mut LamStats,
    lam: Lam,
    resolver: &mut ExternalArityResolver<'_>,
) -> Arity {
    let ident_tbl = &meta.ident_tbl;
    let external_arities = &mut meta.external_arities;
    let mut lookup = |module_id: &Ident, field_name: &str| {
        resolve_external_arity(external_arities, module_id, field_name, resolver)
    };
    get_arity_impl(a, ident_tbl, lam, &mut lookup)
}

struct Collector<'m, 'r, 's> {
    meta: &'m mut LamStats,
    resolver: Option<&'r mut ExternalArityResolver<'s>>,
}

impl Collector<'_, '_, '_> {
    fn arity(&mut self, a: &LamArena, lam: Lam) -> Arity {
        match self.resolver.as_deref_mut() {
            Some(resolver) => get_arity_with_external_arity(a, self.meta, lam, resolver),
            None => get_arity(a, self.meta, lam),
        }
    }

    /// `Lam_pass_collect.annotate` (lam_pass_collect.ml:34-37).
    fn annotate(&mut self, rec_flag: RecFlag, k: Ident, arity: Arity, lambda: Lam) {
        self.meta.ident_tbl.insert(
            k,
            IdKind::FunctionId {
                arity,
                lambda: Some((lambda, rec_flag)),
            },
        );
    }

    fn params(&mut self, a: &LamArena, info: crate::lambda::arena::FuncId) {
        for p in a.params(info) {
            self.meta.ident_tbl.insert(*p, IdKind::Parameter);
        }
    }

    /// `Lam_pass_collect.collect_bind` (lam_pass_collect.ml:58-93).
    fn collect_bind(&mut self, a: &LamArena, rec_flag: RecFlag, ident: Ident, lam: Lam) {
        match a.node(lam) {
            // lam_pass_collect.ml:60
            Node::Const(c) => {
                self.meta.ident_tbl.insert(ident, IdKind::Constant(c));
            }
            Node::Prim { args, info } => {
                let primitive = &a.prim_payload(info).primitive;
                let list = a.list(args);
                match primitive {
                    // lam_pass_collect.ml:61-63
                    Primitive::Pmakeblock(_, Mutable::Immutable) => {
                        let kind = kind_of_lambda_block(a, list);
                        self.meta.ident_tbl.insert(ident, kind);
                        for x in list {
                            self.collect(a, *x);
                        }
                    }
                    // lam_pass_collect.ml:64-66
                    Primitive::Psome | Primitive::PsomeNotNest if list.len() == 1 => {
                        let x = list[0];
                        self.meta.ident_tbl.insert(ident, IdKind::NormalOptional(x));
                        self.collect(a, x);
                    }
                    // lam_pass_collect.ml:67-71
                    Primitive::PnullToOpt | Primitive::PnullUndefinedToOpt if matches!(list, [x] if matches!(a.node(*x), Node::Var(_))) =>
                    {
                        let nullable = if matches!(primitive, Primitive::PnullToOpt) {
                            BoxedNullable::Null
                        } else {
                            BoxedNullable::NullUndefined
                        };
                        self.meta
                            .ident_tbl
                            .insert(ident, IdKind::OptionalBlock(list[0], nullable));
                    }
                    _ => self.collect_fallback(a, rec_flag, ident, lam),
                }
            }
            // lam_pass_collect.ml:72-73
            Node::GlobalModule(v) => {
                let v = a.ident(v);
                alias_ident_or_global(self.meta, ident, &v, IdKind::Module(v));
            }
            // lam_pass_collect.ml:74-77
            Node::Var(v) => {
                let v = a.ident(v);
                alias_ident_or_global(self.meta, ident, &v, IdKind::Na);
            }
            // lam_pass_collect.ml:79-89
            Node::Function { body, info } => {
                self.params(a, info);
                let arity = self.arity(a, lam);
                self.annotate(rec_flag, ident, arity, lam);
                self.collect(a, body);
            }
            _ => self.collect_fallback(a, rec_flag, ident, lam),
        }
    }

    /// lam_pass_collect.ml:90-93.
    fn collect_fallback(&mut self, a: &LamArena, rec_flag: RecFlag, ident: Ident, lam: Lam) {
        self.collect(a, lam);
        if self.meta.export_idents.contains(&ident) {
            let arity = self.arity(a, lam);
            self.annotate(rec_flag, ident, arity, lam);
        }
    }

    /// `Lam_pass_collect.collect` (lam_pass_collect.ml:94-150).
    fn collect(&mut self, a: &LamArena, lam: Lam) {
        match a.node(lam) {
            Node::Const(_)
            | Node::Var(_)
            | Node::GlobalModule(_)
            | Node::Break
            | Node::Continue => {}
            Node::Function { body, info } => {
                self.params(a, info);
                self.collect(a, body);
            }
            Node::Let {
                id, value, body, ..
            } => {
                self.collect_bind(a, RecFlag::NonRec, a.ident(id), value);
                self.collect(a, body);
            }
            Node::LetRec { ids, values, body } => {
                let values = a.list(values);
                let ids = a.ident_run(ids, values.len());
                if let ([id], [value]) = (ids, values) {
                    self.collect_bind(a, RecFlag::SelfRec, *id, *value);
                } else {
                    for (id, value) in ids.iter().zip(values) {
                        self.collect_bind(a, RecFlag::Rec, *id, *value);
                    }
                }
                self.collect(a, body);
            }
            // Children in source order: apply/prim/switches/raise/catch/try/
            // if/sequence/while/for/assign (lam_pass_collect.ml:98-150).
            _ => a.iter_children(lam, |x| self.collect(a, x)),
        }
    }
}

/// `Lam_pass_collect.collect_info` (lam_pass_collect.ml:57-152).
pub fn collect_info(a: &LamArena, meta: &mut LamStats, lam: Lam) {
    Collector {
        meta,
        resolver: None,
    }
    .collect(a, lam);
}

/// [`collect_info`], answering arity queries on external module fields
/// through `resolver`.
pub fn collect_info_with_external_arity(
    a: &LamArena,
    meta: &mut LamStats,
    lam: Lam,
    resolver: &mut ExternalArityResolver<'_>,
) {
    Collector {
        meta,
        resolver: Some(resolver),
    }
    .collect(a, lam);
}
