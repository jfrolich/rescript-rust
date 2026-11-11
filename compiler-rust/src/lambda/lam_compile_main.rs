//! The JS-backend Lambda simplification pipeline over the Lambda arena.
//!
//! Port of `compiler/core/lam_compile_main.ml:148-200` and
//! `Lam_coercion.coerce_and_group_big_lambda` (lam_coercion.ml:82-208). Each
//! pass reads and appends to one [`LamArena`]; a pass that leaves a subterm
//! unchanged returns its handle, as OCaml's physical sharing does.

use ahash::{AHashMap, AHashSet};

use crate::cmi::persistent_env::CmjExportArity;
use crate::ident::Ident;
use crate::lambda::arena::{Lam, LamArena, Node};
use crate::lambda::lam_arity::Arity;
use crate::lambda::lam_compat::{FieldDbgInfo, LetKind};
use crate::lambda::lam_compile_context::RecFlag;
use crate::lambda::lam_pass_alpha_conversion::alpha_conversion;
use crate::lambda::lam_pass_collect::ExternalArityResolver;
use crate::lambda::lam_pass_collect::{collect_info_with_external_arity, get_arity};
use crate::lambda::lam_pass_deep_flatten::deep_flatten;
use crate::lambda::lam_pass_exits::simplify_exits;
use crate::lambda::lam_pass_lets_dce::simplify_lets;
use crate::lambda::lam_pass_remove_alias::ExternalInlineResolver;
use crate::lambda::lam_pass_remove_alias::simplify_alias;
use crate::lambda::lam_primitive::{Mutable, Primitive};
use crate::lambda::lam_stats::{Element, IdKind, LamStats};
use crate::lambda::lam_tag_info::TagInfo;
use crate::lambda::{HoistedFunction, lam_pass_guard_raises, lam_pass_sroa};

/// The simplified program and the `Lam_stats.t` it was simplified with
/// (lam_coercion.ml:200-208). CMJ export arities are read from the final
/// metadata rather than recollected.
pub struct Simplified {
    /// The arena holding the simplified program.
    pub arena: LamArena,
    /// The simplified program.
    pub lam: Lam,
    /// The metadata the program was simplified with.
    pub meta: LamStats,
}

/// The idents of the module-export `Pmakeblock` at the end of the top-level
/// `let`/`let rec`/sequence spine, with its arguments.
fn module_export(a: &LamArena, mut lam: Lam) -> Option<(&[Ident], &[Lam])> {
    loop {
        match a.node(lam) {
            Node::Let { body, .. } | Node::LetRec { body, .. } | Node::Sequence(_, body) => {
                lam = body
            }
            Node::Prim { .. } => {
                return match a.as_prim(lam)? {
                    (Primitive::Pmakeblock(TagInfo::ModuleExport(ids), _), args, _) => {
                        Some((ids, args))
                    }
                    _ => None,
                };
            }
            _ => return None,
        }
    }
}

/// `Lam_coercion.handle_exports` raises `Bs_duplicate_exports` for the first
/// export name seen twice folding the export list from the right
/// (lam_coercion.ml:83-98).
pub fn duplicate_export_name(a: &LamArena, lam: Lam) -> Option<String> {
    let (export_ids, _) = module_export(a, lam)?;
    let mut seen = AHashSet::new();
    export_ids
        .iter()
        .rev()
        .find(|id| !seen.insert(id.name().to_string()))
        .map(|id| id.name().to_string())
}

/// Flat export name for a hoisted function path: each `\"quoted"` segment is
/// unquoted and the segments are joined with `$`.
pub(crate) fn hoisted_export_name(path: &[String]) -> String {
    path.iter()
        .map(|part| {
            if part.len() >= 3 && part.starts_with("\\\"") && part.ends_with('"') {
                &part[2..part.len() - 1]
            } else {
                part.as_str()
            }
        })
        .collect::<Vec<_>>()
        .join("$")
}

/// lam_compile_main.ml:148-200, then `Lam_coercion.handle_exports`.
pub fn simplify_for_js_backend(
    lam: &crate::lambda::Lambda,
    jsx_preserve: bool,
    external_inline: &mut ExternalInlineResolver<'_>,
    external_arity: &mut ExternalArityResolver<'_>,
) -> Simplified {
    let mut a = LamArena::with_capacity(1024);
    let lam = a.import(lam);
    simplify_in_arena(a, lam, jsx_preserve, external_inline, external_arity)
}

/// [`simplify_for_js_backend`] over a program already in `a`.
pub fn simplify_in_arena(
    mut a: LamArena,
    lam: Lam,
    jsx_preserve: bool,
    external_inline: &mut ExternalInlineResolver<'_>,
    external_arity: &mut ExternalArityResolver<'_>,
) -> Simplified {
    // `meta` is built once with the `Translmod.transl_implementation`
    // exports (lam_compile_main.ml:150-153), which the lowered Lambda carries
    // in its module-export block.
    let exports = module_export(&a, lam)
        .map(|(ids, _)| ids.to_vec())
        .unwrap_or_default();
    let mut meta = LamStats::new(exports);
    // OCaml's `Ident.rename` reads the global `Ident.currentstamp`; start the
    // shared counter past every stamp of the program.
    meta.id_gen.set_current_stamp(a.ident_stamp_bound());
    let id_gen = meta.id_gen.clone();
    let a = &mut a;

    // lam_compile_main.ml:148
    let lam = deep_flatten(a, lam, &id_gen);
    // lam_compile_main.ml:154
    collect_info_with_external_arity(a, &mut meta, lam, external_arity);
    // lam_compile_main.ml:159
    let lam = simplify_exits(a, lam, &id_gen);
    // lam_compile_main.ml:161-167
    collect_info_with_external_arity(a, &mut meta, lam, external_arity);
    let lam = simplify_alias(a, &mut meta, lam, jsx_preserve, external_inline);
    // lam_compile_main.ml:169-174
    let lam = deep_flatten(a, lam, &id_gen);
    collect_info_with_external_arity(a, &mut meta, lam, external_arity);
    let lam = simplify_alias(a, &mut meta, lam, jsx_preserve, external_inline);
    // lam_compile_main.ml:175-176
    let lam = deep_flatten(a, lam, &id_gen);
    collect_info_with_external_arity(a, &mut meta, lam, external_arity);
    // lam_compile_main.ml:180-188
    let lam = alpha_conversion(a, &mut meta, lam, external_arity);
    let lam = simplify_exits(a, lam, &id_gen);
    collect_info_with_external_arity(a, &mut meta, lam, external_arity);
    let lam = simplify_alias(a, &mut meta, lam, jsx_preserve, external_inline);
    // The second `alpha_conversion` (lam_compile_main.ml:190) rewrote no
    // module of a 3,355-module application and is not run, as in the tree
    // pipeline: the first pass already uncurries every application of known
    // arity, and the passes in between create no new candidates.
    // lam_compile_main.ml:193
    let lam = simplify_lets(a, lam);
    // Scalar replacement of local mutable blocks.
    let lam = lam_pass_sroa::simplify(a, lam, &id_gen);
    // lam_compile_main.ml:200
    let lam = simplify_exits(a, lam, &id_gen);
    // Last, after every pass that can produce `if a then raise e else c`.
    let lam = lam_pass_guard_raises::guard_raises(a, lam);
    // lam_compile_main.ml:212, lam_coercion.ml:196
    let lam = handle_exports(a, &mut meta, lam);
    let arena = std::mem::take(a);
    Simplified { arena, lam, meta }
}

/// `Lam_coercion.handle_exports` (lam_coercion.ml:82-172) on the trailing
/// module-export block. OCaml splits the program into `Lam_group.t`s and
/// binds every export argument that is not a same-named variable to a fresh
/// group; the JS compiler here walks one term, so those groups become `let`s
/// just outside the block, the first export's outermost.
fn handle_exports(a: &mut LamArena, meta: &mut LamStats, lam: Lam) -> Lam {
    match a.node(lam) {
        Node::Let {
            kind,
            id,
            value,
            body,
        } => {
            let body = handle_exports(a, meta, body);
            a.let_with(kind, id, value, body)
        }
        Node::LetRec { ids, values, body } => {
            let body = handle_exports(a, meta, body);
            a.letrec_with(ids, values, body)
        }
        Node::Sequence(first, second) => {
            let second = handle_exports(a, meta, second);
            a.seq_raw(first, second)
        }
        Node::Prim { args, info }
            if matches!(
                a.prim_payload(info).primitive,
                Primitive::Pmakeblock(TagInfo::ModuleExport(_), _)
            ) =>
        {
            let p = a.prim_payload(info);
            let Primitive::Pmakeblock(TagInfo::ModuleExport(export_ids), mutable_) = &p.primitive
            else {
                unreachable!("guarded by the match arm")
            };
            let (export_ids, mutable_, loc) = (export_ids.clone(), *mutable_, p.loc);
            let args = a.list_vec(args);
            let mut new_args = Vec::with_capacity(args.len());
            let mut new_ids = Vec::with_capacity(export_ids.len());
            let mut hoisted = Vec::new();
            for (export_id, arg) in export_ids.into_iter().zip(args) {
                match a.as_var(arg) {
                    // lam_coercion.ml:100-111
                    Some(id) if id.name() == export_id.name() => {
                        new_ids.push(id);
                        new_args.push(arg);
                    }
                    // lam_coercion.ml:112-121
                    Some(id) => {
                        let new_id = export_id.rename(&meta.id_gen);
                        if let Some(kind) = meta.ident_tbl.get(&id).cloned() {
                            meta.ident_tbl.insert(new_id, kind);
                        }
                        new_ids.push(new_id);
                        new_args.push(a.var(new_id));
                        hoisted.push((new_id, arg, LetKind::Alias));
                    }
                    // lam_coercion.ml:122-157
                    None => {
                        let new_id = export_id.rename(&meta.id_gen);
                        let arity = get_arity(a, meta, arg);
                        if !arity.first_arity_na() {
                            let lambda = matches!(a.node(arg), Node::Function { .. })
                                .then_some((arg, RecFlag::NonRec));
                            meta.ident_tbl
                                .insert(new_id, IdKind::FunctionId { arity, lambda });
                        }
                        new_ids.push(new_id);
                        new_args.push(a.var(new_id));
                        hoisted.push((new_id, arg, LetKind::Strict));
                    }
                }
            }
            // lam_coercion.ml:200-205
            meta.exports = new_ids.clone();
            meta.export_idents = new_ids.iter().copied().collect();
            let mut result = a.prim_raw(
                Primitive::Pmakeblock(TagInfo::ModuleExport(new_ids), mutable_),
                &new_args,
                loc,
            );
            for (id, value, kind) in hoisted.into_iter().rev() {
                result = a.let_(kind, id, value, result);
            }
            result
        }
        _ => lam,
    }
}

/// `js_hoisted_aliases` and the group append of `lam_compile_main.ml`: an
/// export alias for each hoisted function reachable from an export through
/// module blocks.
pub fn add_hoisted_function_aliases(s: &mut Simplified, hoisted: &[HoistedFunction]) {
    if hoisted.is_empty() {
        return;
    }
    let a = &mut s.arena;
    let mut groups: AHashMap<Ident, Lam> = AHashMap::new();
    collect_groups(a, s.lam, &mut groups);
    let exported: AHashMap<String, Ident> = module_export(a, s.lam)
        .map(|(ids, _)| ids.iter().map(|id| (id.name().to_string(), *id)).collect())
        .unwrap_or_default();
    let mut aliases = Vec::new();
    for item in hoisted {
        let Some((top, fields)) = item.path.split_first() else {
            continue;
        };
        let Some(top_id) = exported.get(top) else {
            continue;
        };
        let Some(&module) = groups.get(top_id) else {
            continue;
        };
        let mut positions = Vec::new();
        let Some(Some(target)) = find_path(a, module, fields, &groups, &mut positions) else {
            continue;
        };
        if !target.same(&item.binding) {
            continue;
        }
        let id = s.meta.id_gen.create(hoisted_export_name(&item.path));
        let mut access = a.var(*top_id);
        for (pos, name) in positions {
            access = a.prim(
                Primitive::Pfield(pos, FieldDbgInfo::Module { name }),
                &[access],
                item.loc,
            );
        }
        aliases.push((id, access));
    }
    // Each new alias was prepended in OCaml order.
    aliases.reverse();
    s.lam = append_aliases(a, s.lam, &aliases);
    let ids: Vec<Ident> = aliases.iter().map(|(id, _)| *id).collect();
    s.meta.exports.extend(ids.iter().copied());
    s.meta.export_idents.extend(ids);
}

fn collect_groups(a: &LamArena, mut lam: Lam, groups: &mut AHashMap<Ident, Lam>) {
    loop {
        match a.node(lam) {
            Node::Let {
                id, value, body, ..
            } => {
                groups.insert(a.ident(id), value);
                lam = body;
            }
            Node::LetRec { ids, values, body } => {
                let values = a.list(values);
                for (id, value) in a.ident_run(ids, values.len()).iter().zip(values) {
                    groups.insert(*id, *value);
                }
                lam = body;
            }
            Node::Sequence(_, body) => lam = body,
            _ => return,
        }
    }
}

/// The binding `lam` names through variable aliases and module-block field
/// reads, and the last variable on the way.
fn resolve_binding(
    a: &LamArena,
    lam: Lam,
    groups: &AHashMap<Ident, Lam>,
    seen: &mut AHashSet<Ident>,
) -> (Lam, Option<Ident>) {
    match a.node(lam) {
        Node::Var(id) => {
            let id = a.ident(id);
            if !seen.insert(id) {
                return (lam, Some(id));
            }
            match groups.get(&id).copied() {
                Some(alias) if matches!(a.node(alias), Node::Var(_) | Node::Prim { .. }) => {
                    resolve_binding(a, alias, groups, seen)
                }
                Some(resolved) => (resolved, Some(id)),
                None => (lam, Some(id)),
            }
        }
        Node::Prim { .. } => {
            let Some((Primitive::Pfield(pos, _), [arg], _)) = a.as_prim(lam) else {
                return (lam, None);
            };
            let (pos, arg) = (*pos, *arg);
            let (base, _) = resolve_binding(a, arg, groups, seen);
            if let Some((Primitive::Pmakeblock(TagInfo::Module(_), _), args, _)) = a.as_prim(base)
                && let Some(field) = usize::try_from(pos).ok().and_then(|pos| args.get(pos))
            {
                return resolve_binding(a, *field, groups, seen);
            }
            (lam, None)
        }
        _ => (lam, None),
    }
}

fn find_path(
    a: &LamArena,
    lam: Lam,
    fields: &[String],
    groups: &AHashMap<Ident, Lam>,
    positions: &mut Vec<(i32, crate::name::Name)>,
) -> Option<Option<Ident>> {
    let (resolved, id) = resolve_binding(a, lam, groups, &mut AHashSet::new());
    let Some((field, rest)) = fields.split_first() else {
        return Some(id);
    };
    let (Primitive::Pmakeblock(TagInfo::Module(names), _), args, _) = a.as_prim(resolved)? else {
        return None;
    };
    let pos = names.iter().position(|name| name == field)?;
    positions.push((pos as i32, crate::name::Name::new(field)));
    find_path(a, *args.get(pos)?, rest, groups, positions)
}

fn append_aliases(a: &mut LamArena, lam: Lam, aliases: &[(Ident, Lam)]) -> Lam {
    match a.node(lam) {
        Node::Let {
            kind,
            id,
            value,
            body,
        } => {
            let body = append_aliases(a, body, aliases);
            a.let_with(kind, id, value, body)
        }
        Node::LetRec { ids, values, body } => {
            let body = append_aliases(a, body, aliases);
            a.letrec_with(ids, values, body)
        }
        Node::Sequence(first, second) => {
            let second = append_aliases(a, second, aliases);
            a.seq_raw(first, second)
        }
        Node::Prim { args, info } => {
            let p = a.prim_payload(info);
            let Primitive::Pmakeblock(TagInfo::ModuleExport(ids), mutable_) = &p.primitive else {
                return lam;
            };
            let (mut ids, mutable_, loc) = (ids.clone(), *mutable_, p.loc);
            let mut args = a.list_vec(args);
            ids.extend(aliases.iter().map(|(id, _)| *id));
            for (id, _) in aliases {
                args.push(a.var(*id));
            }
            let mut result = a.prim(
                Primitive::Pmakeblock(TagInfo::ModuleExport(ids), mutable_),
                &args,
                loc,
            );
            for (id, value) in aliases.iter().rev() {
                result = a.let_(LetKind::Alias, *id, *value, result);
            }
            result
        }
        _ => lam,
    }
}

/// `.cmj` export arities, from `Lam_stats_export.values_of_export`
/// (lam_stats_export.ml:32-49) over the final metadata.
pub fn cmj_export_arities(s: &Simplified) -> AHashMap<String, CmjExportArity> {
    let (a, meta) = (&s.arena, &s.meta);
    let mut bindings: Vec<(Ident, Lam)> = Vec::new();
    let mut lam = s.lam;
    loop {
        match a.node(lam) {
            Node::Let {
                id, value, body, ..
            } => {
                bindings.push((a.ident(id), value));
                lam = body;
            }
            Node::LetRec { ids, values, body } => {
                let values = a.list(values);
                for (id, value) in a.ident_run(ids, values.len()).iter().zip(values) {
                    bindings.push((*id, *value));
                }
                lam = body;
            }
            Node::Sequence(_, body) => lam = body,
            _ => break,
        }
    }
    let mut arities = AHashMap::new();
    let Some((exports, args)) = module_export(a, lam) else {
        return arities;
    };
    for (export, &arg) in exports.iter().zip(args) {
        let name = export.name().to_string();
        match meta.ident_tbl.get(export) {
            Some(IdKind::FunctionId { arity, .. }) => {
                arities.insert(name, CmjExportArity::Single(arity.clone()));
            }
            Some(IdKind::ImmutableBlock(items)) => {
                let items = items
                    .iter()
                    .map(|item| match item {
                        Element::Na => Arity::na(),
                        Element::SimpleForm(lam) => get_arity(a, meta, *lam),
                    })
                    .collect();
                arities.insert(name, CmjExportArity::Submodule(items));
            }
            _ => {
                let value = match a.as_var(arg) {
                    Some(id) => bindings
                        .iter()
                        .rev()
                        .find_map(|(binding, value)| binding.same(&id).then_some(*value))
                        .unwrap_or(arg),
                    None => arg,
                };
                if let Some((Primitive::Pmakeblock(_, Mutable::Immutable), args, _)) =
                    a.as_prim(value)
                {
                    let items = args.iter().map(|lam| get_arity(a, meta, *lam)).collect();
                    arities.insert(name, CmjExportArity::Submodule(items));
                }
            }
        }
    }
    arities
}
