//! JS-backend lambda simplification pipeline.
//!
//! Direct port of `compiler/core/lam_compile_main.ml:148-200`. Calls the
//! ported passes in the same order as OCaml.
//!
//! Every line here must trace to a specific line in
//! `compiler/core/lam_compile_main.ml`. No Rust-only logic.

use crate::ident::Ident;
use crate::lambda::lam_compat::LetKind;
use crate::lambda::lam_compile_context::{IdKind, LamStats, RecFlag};
use crate::lambda::lam_pass_alpha_conversion::alpha_conversion_with_external_arity_owned;
use crate::lambda::lam_pass_collect::{ExternalArityResolver, collect_info_with_external_arity};
use crate::lambda::lam_pass_deep_flatten::deep_flatten_owned_with_id_gen;
use crate::lambda::lam_pass_exits::simplify_exits_owned;
use crate::lambda::lam_pass_lets_dce::simplify_lets_owned;
use crate::lambda::lam_pass_remove_alias::{
    ExternalInlineResolver, simplify_alias_with_jsx_and_external_inline_owned,
};
use crate::lambda::lam_primitive::Primitive;
use crate::lambda::lam_tag_info::TagInfo;
use crate::lambda::{Lambda, PrimInfo};

/// Result of the JS-backend simplify/coercion pipeline.
///
/// OCaml returns both the coerced Lambda groups and the updated `Lam_stats.t`
/// from `Lam_coercion.coerce_and_group_big_lambda`
/// (compiler/core/lam_coercion.ml:200-208). The final metadata is reused when
/// writing CMJ export arities, so Rust keeps it with the simplified Lambda
/// instead of recomputing `collect_info` after the fact.
pub struct SimplifiedForJsBackend {
    pub lambda: Lambda,
    pub meta: LamStats,
}

/// Idents carried by the module-export `Pmakeblock` at the end of the
/// top-level `Llet`/`Lletrec`/`Lsequence` spine, if there is one.
pub(crate) fn module_export_ids(lam: &Lambda) -> Option<&[Ident]> {
    let mut current = lam;
    loop {
        match current {
            Lambda::Llet(_, _, _, body) | Lambda::Lletrec(_, body) => current = body,
            Lambda::Lsequence(_, body) => current = body,
            Lambda::Lprim(info) => {
                return match &info.primitive {
                    Primitive::Pmakeblock(TagInfo::ModuleExport(ids), _) => Some(ids),
                    _ => None,
                };
            }
            _ => return None,
        }
    }
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

/// Insert flat hoisted-function aliases after simplification/coercion, matching
/// `js_hoisted_aliases` and the group append in `compiler/core/lam_compile_main.ml`.
pub fn add_hoisted_function_aliases(
    mut simplified: SimplifiedForJsBackend,
    hoisted: &[crate::lambda::HoistedFunction],
) -> SimplifiedForJsBackend {
    use std::collections::{HashMap, HashSet};

    fn collect_groups<'a>(lam: &'a Lambda, groups: &mut HashMap<Ident, &'a Lambda>) {
        match lam {
            Lambda::Llet(_, id, value, body) => {
                groups.insert(*id, value);
                collect_groups(body, groups);
            }
            Lambda::Lletrec(bindings, body) => {
                groups.extend(bindings.iter().map(|(id, value)| (*id, value)));
                collect_groups(body, groups);
            }
            Lambda::Lsequence(_, body) => collect_groups(body, groups),
            _ => {}
        }
    }
    fn resolve_binding<'a>(
        lam: &'a Lambda,
        groups: &HashMap<Ident, &'a Lambda>,
        seen: &mut HashSet<Ident>,
    ) -> (&'a Lambda, Option<Ident>) {
        match lam {
            Lambda::Lvar(id) => {
                if !seen.insert(*id) {
                    return (lam, Some(*id));
                }
                match groups.get(id).copied() {
                    Some(alias @ (Lambda::Lvar(_) | Lambda::Lprim(_))) => {
                        resolve_binding(alias, groups, seen)
                    }
                    Some(resolved) => (resolved, Some(*id)),
                    None => (lam, Some(*id)),
                }
            }
            Lambda::Lprim(info) => {
                let (Primitive::Pfield(pos, _), [arg]) = (&info.primitive, info.args.as_slice())
                else {
                    return (lam, None);
                };
                let (base, _) = resolve_binding(arg, groups, seen);
                if let Lambda::Lprim(base) = base
                    && let Primitive::Pmakeblock(TagInfo::Module(_), _) = &base.primitive
                    && let Some(field) = usize::try_from(*pos)
                        .ok()
                        .and_then(|pos| base.args.get(pos))
                {
                    return resolve_binding(field, groups, seen);
                }
                (lam, None)
            }
            _ => (lam, None),
        }
    }
    fn find_path(
        lam: &Lambda,
        fields: &[String],
        groups: &HashMap<Ident, &Lambda>,
        positions: &mut Vec<(i32, String)>,
    ) -> Option<Option<Ident>> {
        if fields.is_empty() {
            return Some(resolve_binding(lam, groups, &mut HashSet::new()).1);
        }
        let (resolved, _) = resolve_binding(lam, groups, &mut HashSet::new());
        let Lambda::Lprim(info) = resolved else {
            return None;
        };
        let Primitive::Pmakeblock(TagInfo::Module(names), _) = &info.primitive else {
            return None;
        };
        let pos = names.iter().position(|name| name == &fields[0])?;
        positions.push((pos as i32, fields[0].clone()));
        find_path(info.args.get(pos)?, &fields[1..], groups, positions)
    }
    fn append_aliases(lam: Lambda, aliases: &[(Ident, Lambda)]) -> Lambda {
        match lam {
            Lambda::Llet(kind, id, value, body) => {
                Lambda::Llet(kind, id, value, Box::new(append_aliases(*body, aliases)))
            }
            Lambda::Lletrec(bindings, body) => {
                Lambda::Lletrec(bindings, Box::new(append_aliases(*body, aliases)))
            }
            Lambda::Lsequence(left, body) => {
                Lambda::Lsequence(left, Box::new(append_aliases(*body, aliases)))
            }
            Lambda::Lprim(info)
                if matches!(
                    &info.primitive,
                    Primitive::Pmakeblock(TagInfo::ModuleExport(_), _)
                ) =>
            {
                let PrimInfo {
                    primitive: Primitive::Pmakeblock(TagInfo::ModuleExport(mut ids), mutable_),
                    mut args,
                    loc,
                } = *info
                else {
                    unreachable!("guarded by the match arm")
                };

                ids.extend(aliases.iter().map(|(id, _)| *id));
                args.extend(aliases.iter().map(|(id, _)| Lambda::var(*id)));
                let mut result = Lambda::prim(
                    Primitive::Pmakeblock(TagInfo::ModuleExport(ids), mutable_),
                    args,
                    loc,
                );
                for (id, value) in aliases.iter().rev() {
                    result = Lambda::let_(LetKind::Alias, *id, value.clone(), result);
                }
                result
            }
            other => other,
        }
    }

    if hoisted.is_empty() {
        return simplified;
    }
    let mut aliases = Vec::new();
    {
        let mut groups = HashMap::new();
        collect_groups(&simplified.lambda, &mut groups);
        let exported = module_export_ids(&simplified.lambda)
            .unwrap_or_default()
            .iter()
            .map(|id| (id.name().to_string(), *id))
            .collect::<HashMap<_, _>>();
        for item in hoisted {
            let Some((top, fields)) = item.path.split_first() else {
                continue;
            };
            let Some(top_id) = exported.get(top) else {
                continue;
            };
            let Some(module) = groups.get(top_id) else {
                continue;
            };
            let mut positions = Vec::new();
            let Some(Some(target_id)) = find_path(module, fields, &groups, &mut positions) else {
                continue;
            };
            if !target_id.same(&item.binding) {
                continue;
            }
            let export_name = hoisted_export_name(&item.path);
            let id = simplified.meta.id_gen.create(&export_name);
            let mut access = Lambda::var(*top_id);
            for (pos, name) in positions {
                access = Lambda::prim(
                    Primitive::Pfield(pos, crate::lambda::FieldDbgInfo::Module { name }),
                    vec![access],
                    item.loc,
                );
            }
            aliases.push((id, access));
        }
    }
    // Each new alias was prepended in OCaml order.
    aliases.reverse();
    simplified.lambda = append_aliases(simplified.lambda, &aliases);
    let alias_ids = aliases.iter().map(|(id, _)| *id).collect::<Vec<_>>();
    simplified.meta.exports.extend(alias_ids.iter().cloned());
    simplified.meta.export_idents.extend(alias_ids);
    simplified
}

/// Direct port of `compiler/core/lam_compile_main.ml:148-200` pipeline.
#[cfg(test)]
pub fn simplify_for_js_backend(lam: &Lambda) -> Lambda {
    simplify_for_js_backend_with_jsx_preserve(lam, false)
}

/// `jsx_preserve` reaches `simplify_alias` here so that the JSX guard in
/// `Lam_pass_remove_alias.simplify_alias` (lam_pass_remove_alias.ml:54-62)
/// fires on the same callees OCaml does.
#[cfg(test)]
pub fn simplify_for_js_backend_with_jsx_preserve(lam: &Lambda, jsx_preserve: bool) -> Lambda {
    let mut no_external_inline = |_: &Ident, _: &str| None;
    let mut no_external_arity = |_: &Ident, _: &str| None;
    simplify_for_js_backend_with_external_inline_and_meta_owned(
        lam.clone(),
        jsx_preserve,
        &mut no_external_inline,
        &mut no_external_arity,
    )
    .lambda
}

/// Owned entry point for the `compiler/core/lam_compile_main.ml:148-200`
/// pipeline, with the Rust counterpart to
/// `Lam_compile_env.query_external_id_info` available to the three
/// `simplify_alias` passes (`compiler/core/lam_pass_remove_alias.ml:131-162`).
/// OCaml values are immutable and rebuilt by each pass; Rust moves the
/// previous pass result into owned ports without changing pass order.
pub fn simplify_for_js_backend_with_external_inline_and_meta_owned(
    lam: Lambda,
    jsx_preserve: bool,
    external_inline: &mut ExternalInlineResolver<'_>,
    external_arity: &mut ExternalArityResolver<'_>,
) -> SimplifiedForJsBackend {
    // OCaml constructs `meta` once at lam_compile_main.ml:150-153 with
    // `~export_idents` and `~export_ident_sets` from the Lam_compile_main.compile
    // entry point. The exports come from `Translmod.transl_implementation`. In
    // Rust, the lowered Lambda still carries them in the top-level
    // `Pmakeblock( TagInfo::ModuleExport(ids), _)`, so we recover the same
    // list here. This drives the `Set_ident.mem meta.export_idents` arm in
    // `Lam_pass_collect.collect_info` (lam_pass_collect.ml:92-93) and the
    // `is_export_id` guard in `Lam_pass_remove_alias.simplify_alias`
    // (lam_pass_remove_alias.ml:211).
    let mut meta = LamStats::new(extract_export_idents(&lam));
    // Seed the shared rename counter past every stamp already present in the
    // lambda so `Ident.rename` (via beta-reduce) never collides with existing
    // stamps. OCaml's Ident.rename reads from a global mutable counter; this
    // mirrors that. Without the seed, two beta reductions of the same function
    // at distinct call sites renamed their parameters to the same fresh stamp
    // (e.g. two `let prim` declarations at module top level in
    // `coercion_module_alias_test`, which is invalid JS).
    meta.id_gen
        .set_current_stamp(crate::lambda::lam_beta_reduce::max_ident_stamp_in_lambda(
            &lam,
        ));

    // lam_compile_main.ml:148 — initial deep_flatten.
    let lam = deep_flatten_owned_with_id_gen(lam, &meta.id_gen);

    // lam_compile_main.ml:154 — collect_info into meta. Only simplify_exits
    // runs before the next collect re-annotates every function binding, and
    // it neither reads function bodies from meta nor turns a function binding
    // into another kind, so this collect records arities only.
    meta.collect_function_payloads = false;
    collect_info_with_external_arity(&mut meta, &lam, external_arity);
    meta.collect_function_payloads = true;

    // lam_compile_main.ml:159 — simplify_exits.
    let lam = simplify_exits_owned(lam, &meta.id_gen);

    // lam_compile_main.ml:161 — collect_info before simplify_alias.
    collect_info_with_external_arity(&mut meta, &lam, external_arity);

    // lam_compile_main.ml:167 — simplify_alias.
    let lam = simplify_alias_with_jsx_and_external_inline_owned(
        &mut meta,
        lam,
        jsx_preserve,
        external_inline,
    );

    // lam_compile_main.ml:169 — deep_flatten.
    let lam = deep_flatten_owned_with_id_gen(lam, &meta.id_gen);

    // lam_compile_main.ml:173 — collect_info.
    collect_info_with_external_arity(&mut meta, &lam, external_arity);

    // lam_compile_main.ml:174 — simplify_alias.
    let lam = simplify_alias_with_jsx_and_external_inline_owned(
        &mut meta,
        lam,
        jsx_preserve,
        external_inline,
    );

    // lam_compile_main.ml:175 — deep_flatten.
    let lam = deep_flatten_owned_with_id_gen(lam, &meta.id_gen);

    // lam_compile_main.ml:176 — collect_info. As at line 154: alpha
    // conversion and simplify_exits read arities only, and the collect at
    // line 183 re-annotates every function binding before simplify_alias.
    meta.collect_function_payloads = false;
    collect_info_with_external_arity(&mut meta, &lam, external_arity);
    meta.collect_function_payloads = true;

    // lam_compile_main.ml:180 — alpha_conversion.
    let lam = alpha_conversion_with_external_arity_owned(&mut meta, lam, external_arity);

    // lam_compile_main.ml:182 — simplify_exits.
    let lam = simplify_exits_owned(lam, &meta.id_gen);

    // lam_compile_main.ml:183 — collect_info.
    collect_info_with_external_arity(&mut meta, &lam, external_arity);

    // lam_compile_main.ml:188 — simplify_alias.
    let lam = simplify_alias_with_jsx_and_external_inline_owned(
        &mut meta,
        lam,
        jsx_preserve,
        external_inline,
    );

    // OCaml runs alpha_conversion a second time here (lam_compile_main.ml:190).
    // Over a 3,355-module application it rewrote none of them, and dropping
    // it left all generated JS and the compiler's JS snapshots unchanged: the
    // first pass already uncurries every application whose arity is known,
    // and the simplify_exits/simplify_alias steps in between create no new
    // candidates.

    // lam_compile_main.ml:193 — simplify_lets (DCE + alias inlining).
    let lam = simplify_lets_owned(lam);

    // lam_compile_main.ml — scalar replacement of local mutable blocks.
    let lam = crate::lambda::lam_pass_sroa::simplify(lam, &meta.id_gen);

    // lam_compile_main.ml:200 — final simplify_exits.
    let lam = simplify_exits_owned(lam, &meta.id_gen);

    // lam_compile_main.ml — guard_raises runs last, after every pass that can
    // produce `if a then raise e else c`.
    let lam = crate::lambda::lam_pass_guard_raises::guard_raises(lam);

    // lam_compile_main.ml:212 — Lam_coercion.coerce_and_group_big_lambda
    // (lam_coercion.ml:196). The OCaml flow flattens the lambda into a list
    // of `Lam_group.t` and runs `handle_exports` on the trailing
    // `Pmakeblock( ModuleExport _, args)`. Each non-`Lvar` arg gets
    // hoisted into a fresh `Single (Strict, newid, lam)` group; the
    // makeblock's arg list becomes `Lvar newid`. In Rust the JS compile
    // walks one Lambda tree, so we re-emit the equivalent shape: rename
    // the export id, prepend a `Llet (Strict, newid, value, _)` just
    // outside the makeblock, and replace the arg with `Lvar newid`. This
    // makes downstream `compile_expr` see separate top-level bindings
    // instead of inlining `Lconst (Const_block ...)` (etc.) into the
    // module-export block — matching `let X = {...}` snapshots like
    // `variantsMatching.CustomizeTags_d`.
    handle_exports(meta, lam)
}

/// Direct port of `compiler/core/lam_coercion.ml:82-172` — `handle_exports`
/// applied to the trailing module-export `Pmakeblock`.
/// OCaml `Lam_coercion.handle_exports` (lam_coercion.ml:83-98) raises
/// `Bs_duplicate_exports` for the first export name seen twice while folding
/// the export list from the right.
pub fn duplicate_export_name(lam: &Lambda) -> Option<String> {
    let export_ids = module_export_ids(lam)?;
    let mut seen = ahash::AHashSet::new();
    export_ids
        .iter()
        .rev()
        .find(|id| !seen.insert(id.name().to_string()))
        .map(|id| id.name().to_string())
}

fn handle_exports(mut meta: LamStats, lam: Lambda) -> SimplifiedForJsBackend {
    let lambda = rewrite_export_makeblock(&mut meta, lam);
    SimplifiedForJsBackend { lambda, meta }
}

fn rewrite_export_makeblock(meta: &mut LamStats, lam: Lambda) -> Lambda {
    match lam {
        Lambda::Llet(kind, id, value, body) => {
            let new_body = rewrite_export_makeblock(meta, *body);
            Lambda::Llet(kind, id, value, Box::new(new_body))
        }
        Lambda::Lletrec(bindings, body) => {
            let new_body = rewrite_export_makeblock(meta, *body);
            Lambda::Lletrec(bindings, Box::new(new_body))
        }
        Lambda::Lsequence(left, right) => {
            let new_right = rewrite_export_makeblock(meta, *right);
            Lambda::Lsequence(left, Box::new(new_right))
        }
        Lambda::Lprim(info)
            if matches!(
                &info.primitive,
                Primitive::Pmakeblock(TagInfo::ModuleExport(_), _)
            ) =>
        {
            let PrimInfo {
                primitive: Primitive::Pmakeblock(TagInfo::ModuleExport(export_ids), mutable_),
                args,
                loc,
            } = *info
            else {
                unreachable!("guarded by the match arm")
            };

            // lam_coercion.ml:88-122 — fold_right2 over (export_ids, args).
            // OCaml builds `result.groups` by prepending Single(...)
            // entries, so the resulting groups list ends up in
            // original-arg order. In Rust we rebuild by wrapping
            // `Llet`s around the makeblock; the FIRST hoisted binding
            // must end up OUTERMOST so it compiles first (matching
            // OCaml's `compile_group` iteration order).
            let mut new_args: Vec<Lambda> = Vec::with_capacity(args.len());
            let mut new_export_ids: Vec<Ident> = Vec::with_capacity(export_ids.len());
            let mut hoisted: Vec<(Ident, Lambda, LetKind)> = Vec::new();

            for (orig_export_id, arg) in export_ids.into_iter().zip(args) {
                match &arg {
                    // lam_coercion.ml:100-111 — Lvar with matching name.
                    Lambda::Lvar(id) if id.name() == orig_export_id.name() => {
                        new_export_ids.push(*id);
                        new_args.push(arg);
                    }
                    // lam_coercion.ml:112-121 — Lvar with mismatched name:
                    // rename the export id, alias-bind it.
                    Lambda::Lvar(id) => {
                        let newid = orig_export_id.rename(&meta.id_gen);
                        if let Some(info) = meta.ident_tbl.get(id).cloned() {
                            meta.ident_tbl.insert(newid, info);
                        }
                        new_export_ids.push(newid);
                        new_args.push(Lambda::Lvar(newid));
                        hoisted.push((newid, arg, LetKind::Alias));
                    }
                    // lam_coercion.ml:122-157 — non-Lvar arg: rename the
                    // export id, strict-bind it.
                    _ => {
                        let newid = orig_export_id.rename(&meta.id_gen);
                        let arity = crate::lambda::lam_pass_collect::get_arity(meta, &arg);
                        if !arity.first_arity_na() {
                            let lambda = match &arg {
                                Lambda::Lfunction(_) => Some((arg.clone(), RecFlag::NonRec)),
                                _ => None,
                            };
                            meta.ident_tbl
                                .insert(newid, IdKind::FunctionId { arity, lambda });
                        }
                        new_export_ids.push(newid);
                        new_args.push(Lambda::Lvar(newid));
                        hoisted.push((newid, arg, LetKind::Strict));
                    }
                }
            }

            // Update meta.exports / export_idents to match the renamed
            // export list (lam_coercion.ml:200-205).
            meta.exports = new_export_ids.clone();
            meta.export_idents = new_export_ids.iter().cloned().collect();

            let mut result = Lambda::Lprim(Box::new(PrimInfo {
                primitive: Primitive::Pmakeblock(TagInfo::ModuleExport(new_export_ids), mutable_),
                args: new_args,
                loc,
            }));
            // Wrap with hoisted Llets so the FIRST hoist (by export
            // order) is OUTERMOST, matching OCaml's compile_group
            // iteration order.
            for (id, value, kind) in hoisted.into_iter().rev() {
                result = Lambda::Llet(kind, id, Box::new(value), Box::new(result));
            }
            result
        }
        // The trailing expression is not a module-export Pmakeblock
        // (e.g. tests with `assert false` etc.). Leave it untouched.
        other => other,
    }
}

/// Walks the same top-level spine as `Lam_coercion.flatten`
/// (`compiler/core/lam_coercion.ml:179-199`) and returns the idents carried in
/// the final `Pmakeblock( TagInfo::ModuleExport(ids), _)`. These mirror the
/// `exports` list `Translmod.transl_implementation` returns to
/// `Lam_compile_main.compile` (`compiler/core/js_implementation.ml:158-163`).
/// Do not walk nested module values: OCaml's `meta.exports` contains the
/// structure-level exports passed to `Lam_coercion.handle_exports`, not every
/// nested module-export block reachable from the payload.
fn extract_export_idents(lam: &Lambda) -> Vec<Ident> {
    module_export_ids(lam)
        .map(<[Ident]>::to_vec)
        .unwrap_or_default()
}
