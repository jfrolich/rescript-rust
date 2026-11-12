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
use crate::lambda::{FlatMakePath, LamLoc, lam_pass_guard_raises, lam_pass_sroa};

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
pub(crate) fn module_export(a: &LamArena, mut lam: Lam) -> Option<(&[Ident], &[Lam])> {
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

/// `Lam_compile_main.flat_make_aliases`, appended as `Single (Alias, id,
/// lam)` groups after coercion: every nested `make` of the final signature is
/// also exported under its flat name (see `Translmod.implementation`). The
/// alias resolves the source path through toplevel aliases and known module
/// blocks. When that ends at a toplevel binding, the alias names it
/// (`let A$B$make = make`), which bundlers can drop when it is unused. When it
/// ends at a module of another compilation unit, possibly awaited, the alias
/// reads that unit's flat export (`let A$make = Other.B$make`), so a
/// re-exported client component never reads `make` from a client reference.
/// Otherwise it reads the value through the module objects. The paths carry
/// the runtime field positions, which a coerced module block shares with its
/// signature. The name check that raises in OCaml runs at the end of
/// translation (`RawLambdaConverter::check_flat_make_exports`).
pub fn add_flat_make_aliases(s: &mut Simplified, paths: &[FlatMakePath]) {
    if paths.is_empty() {
        return;
    }
    let a = &mut s.arena;
    let mut groups: AHashMap<Ident, Lam> = AHashMap::new();
    collect_groups(a, s.lam, &mut groups);
    let exports: Vec<Ident> = module_export(a, s.lam)
        .map(|(ids, _)| ids.to_vec())
        .unwrap_or_default();
    let mut aliases = Vec::with_capacity(paths.len());
    for path in paths {
        if let Some(alias) = flat_make_alias(a, path, &exports, &groups, &s.meta.id_gen) {
            aliases.push(alias);
        }
    }
    s.lam = append_aliases(a, s.lam, &aliases);
    let ids: Vec<Ident> = aliases.iter().map(|(id, _)| *id).collect();
    s.meta.exports.extend(ids.iter().copied());
    s.meta.export_idents.extend(ids);
}

/// `resolve` follows a toplevel binding bound to `Lvar`, `Lglobal_module`, a
/// module field read or a block.
fn is_followed_binding(a: &LamArena, bound: Lam) -> bool {
    match a.node(bound) {
        Node::Var(_) | Node::GlobalModule(_) => true,
        Node::Prim { info, .. } => matches!(
            a.prim_payload(info).primitive,
            Primitive::Pfield(_, FieldDbgInfo::Module { .. }) | Primitive::Pmakeblock(_, _)
        ),
        _ => false,
    }
}

/// One alias of `Lam_compile_main.flat_make_aliases`: the flat export
/// identifier and the value it is bound to. `None` when the path does not
/// start at an export, which the translation check has already reported.
fn flat_make_alias(
    a: &mut LamArena,
    path: &FlatMakePath,
    exports: &[Ident],
    groups: &AHashMap<Ident, Lam>,
    id_gen: &crate::context::IdGenerator,
) -> Option<(Ident, Lam)> {
    /// Reads only toplevel bindings and other compilation units, so it can
    /// be evaluated again in the alias.
    fn is_path(a: &LamArena, lam: Lam, groups: &AHashMap<Ident, Lam>) -> bool {
        match a.node(lam) {
            Node::Var(id) => groups.contains_key(&a.ident(id)),
            Node::GlobalModule(_) => true,
            Node::Prim { .. } => match a.as_prim(lam) {
                Some((Primitive::Pfield(_, FieldDbgInfo::Module { .. }), [base], _)) => {
                    is_path(a, *base, groups)
                }
                _ => false,
            },
            _ => false,
        }
    }
    /// Follows toplevel bindings that hold a module or an alias, and reads of
    /// known module block fields.
    fn resolve(
        a: &mut LamArena,
        seen: &AHashSet<Ident>,
        lam: Lam,
        groups: &AHashMap<Ident, Lam>,
    ) -> Lam {
        match a.node(lam) {
            Node::Var(id) => {
                let id = a.ident(id);
                if seen.contains(&id) {
                    return lam;
                }
                match groups
                    .get(&id)
                    .copied()
                    .filter(|bound| is_followed_binding(a, *bound))
                {
                    Some(bound) => {
                        let mut seen = seen.clone();
                        seen.insert(id);
                        resolve(a, &seen, bound, groups)
                    }
                    None => lam,
                }
            }
            Node::Prim { .. } => {
                let Some((
                    primitive @ Primitive::Pfield(pos, FieldDbgInfo::Module { name }),
                    [base],
                    loc,
                )) = a.as_prim(lam)
                else {
                    return lam;
                };
                let (primitive, pos, name, base, loc) =
                    (primitive.clone(), *pos, *name, *base, loc);
                let base = resolve(a, seen, base, groups);
                if let Some((Primitive::Pmakeblock(TagInfo::Module(names), _), args, _)) =
                    a.as_prim(base)
                    && let Ok(index) = usize::try_from(pos)
                    && names.get(index).is_some_and(|field| *field == name)
                {
                    let field = args[index];
                    return resolve(a, seen, field, groups);
                }
                a.prim(primitive, &[base], loc)
            }
            _ => lam,
        }
    }

    let names = path
        .iter()
        .map(|step| step.name.as_str())
        .collect::<Vec<_>>();
    let name = crate::lambda::flat_export_name(&names);
    // `Map_string` built by folding the exports left to right: a later
    // export of the same name wins.
    let top_id = exports.iter().rev().find(|id| id.name() == names[0])?;
    // `Location.in_file (Location.get_input_name ())`: a ghost location,
    // without a source mapping.
    let mut read = a.var(*top_id);
    for step in &path[1..] {
        read = a.prim(
            Primitive::Pfield(
                step.pos,
                FieldDbgInfo::Module {
                    name: crate::name::Name::new(&step.name),
                },
            ),
            &[read],
            LamLoc::NONE,
        );
    }
    let resolved = resolve(a, &AHashSet::new(), read, groups);
    let alias = if is_path(a, resolved, groups) {
        resolved
    } else {
        read
    };
    Some((id_gen.create(&name), alias))
}

/// `Lam_compile_main.is_awaited_unit`: `await import(Unit)` of a whole
/// compilation unit.
fn is_awaited_unit(a: &LamArena, lam: Lam) -> bool {
    let Some((Primitive::Pawait, [import], _)) = a.as_prim(lam) else {
        return false;
    };
    matches!(
        a.as_prim(*import),
        Some((Primitive::Pimport(source), _, _))
            if matches!(
                source.as_ref(),
                crate::lambda::lam_primitive::ImportSource::ImportModule { path, .. }
                    if path.is_empty()
            )
    )
}

/// `Lam_compile_main.awaited_units` (see `Lam_stats.awaited_units`): every
/// local bound to an awaited compilation unit, at any depth.
pub fn awaited_units(a: &LamArena, lam: Lam) -> AHashSet<Ident> {
    fn collect(a: &LamArena, lam: Lam, units: &mut AHashSet<Ident>) {
        if let Node::Let { id, value, .. } = a.node(lam)
            && is_awaited_unit(a, value)
        {
            units.insert(a.ident(id));
        }
        a.iter_children(lam, |child| collect(a, child, units));
    }
    let mut units = AHashSet::new();
    collect(a, lam, &mut units);
    units
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

#[cfg(test)]
mod regression_tests {
    use super::*;
    use crate::lambda::Lambda;
    use crate::ident::IdentFlags;
    fn id(name: &str, stamp: i32) -> Ident {
        Ident::new(name, stamp, IdentFlags::NONE)
    }
    fn step(pos: i32, name: &str) -> crate::lambda::FlatMakeStep {
        crate::lambda::FlatMakeStep {
            pos,
            name: name.into(),
        }
    }
    fn export_node(exports: Vec<Ident>, args: Vec<Lambda>) -> Lambda {
        Lambda::prim(
            Primitive::Pmakeblock(TagInfo::ModuleExport(exports), Mutable::Immutable),
            args,
            LamLoc::NONE,
        )
    }

    fn run(input: Lambda, paths: &[FlatMakePath]) -> Simplified {
        let mut result = simplify_for_js_backend(&input, false, &mut |_, _| None, &mut |_, _| None);
        add_flat_make_aliases(&mut result, paths);
        result
    }
    fn export_values(result: &Simplified) -> Vec<(Ident, Lambda)> {
        let mut groups = AHashMap::new();
        collect_groups(&result.arena, result.lam, &mut groups);
        let (ids, values) = super::module_export(&result.arena, result.lam).unwrap();
        ids.iter()
            .zip(values)
            .map(|(id, value)| {
                let value = result
                    .arena
                    .as_var(*value)
                    .and_then(|id| groups.get(&id).copied())
                    .unwrap_or(*value);
                (*id, result.arena.export(value))
            })
            .collect()
    }

    #[test]
    fn flat_alias_of_another_unit_reads_its_flat_export_path() {
        let module = id("Provider", 1);
        let other = id("Sidebar", 0);
        let input = Lambda::let_(
            LetKind::Alias,
            module,
            Lambda::prim(
                Primitive::Pfield(
                    0,
                    FieldDbgInfo::Module {
                        name: "Provider".into(),
                    },
                ),
                vec![Lambda::global_module(other)],
                LamLoc::NONE,
            ),
            export_node(vec![module], vec![Lambda::var(module)]),
        );
        let result = run(input, &[vec![step(0, "Provider"), step(0, "make")]]);
        let (_, value) = export_values(&result)
            .into_iter()
            .find(|(id, _)| id.name() == "Provider$make")
            .unwrap();
        // `Sidebar.Provider.make`, a path the JS backend reads as the flat
        // export `Sidebar.Provider$make`.
        let Lambda::Lprim(make) = &value else {
            panic!("{value:?}")
        };
        assert!(matches!(
            (&make.primitive, make.args.as_slice()),
            (Primitive::Pfield(0, FieldDbgInfo::Module { name }), [Lambda::Lprim(_)]) if name == "make"
        ));
    }
    #[test]
    fn flat_aliases_follow_the_paths_and_are_exported_in_path_order() {
        let first = id("make", 2);
        let second = id("make", 3);
        let module_a = id("A", 1);
        let module_b = id("B", 4);
        let block = |binding| {
            Lambda::prim(
                Primitive::Pmakeblock(TagInfo::Module(vec!["make".into()]), Mutable::Immutable),
                vec![Lambda::var(binding)],
                LamLoc::NONE,
            )
        };
        let function =
            || Lambda::function_(0, vec![], Lambda::unit(), Default::default(), LamLoc::NONE);
        let input = Lambda::let_(
            LetKind::Strict,
            first,
            function(),
            Lambda::let_(
                LetKind::Strict,
                module_a,
                block(first),
                Lambda::let_(
                    LetKind::Strict,
                    second,
                    function(),
                    Lambda::let_(
                        LetKind::Strict,
                        module_b,
                        block(second),
                        export_node(
                            vec![module_a, module_b],
                            vec![Lambda::var(module_a), Lambda::var(module_b)],
                        ),
                    ),
                ),
            ),
        );
        let result = run(
            input,
            &[
                vec![step(0, "A"), step(0, "make")],
                vec![step(1, "B"), step(0, "make")],
            ],
        );
        let names = result
            .meta
            .exports
            .iter()
            .map(|id| id.name())
            .collect::<Vec<_>>();
        assert_eq!(names[names.len() - 2..], ["A$make", "B$make"]);
        // Each alias resolves through the module block to a toplevel binding.
        for (id, value) in export_values(&result) {
            if id.name().ends_with("$make") {
                assert!(matches!(value, Lambda::Lvar(_)), "{value:?}");
            }
        }
        assert!(
            !super::module_export(&result.arena, result.lam)
                .unwrap()
                .1
                .is_empty()
        );
    }
}
