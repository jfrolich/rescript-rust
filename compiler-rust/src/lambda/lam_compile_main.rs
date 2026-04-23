//! JS-backend lambda simplification pipeline.
//!
//! Direct port of `compiler/core/lam_compile_main.ml:148-200`. Calls the
//! ported passes in the same order as OCaml.
//!
//! Every line here must trace to a specific line in
//! `compiler/core/lam_compile_main.ml`. No Rust-only logic.

use crate::ident::Ident;
use crate::lambda::lam_pass_collect::collect_info;
use crate::lambda::lam_compat::LetKind;
use crate::lambda::lam_compile_context::LamStats;
use crate::lambda::lam_pass_deep_flatten::deep_flatten;
use crate::lambda::lam_pass_alpha_conversion::alpha_conversion;
use crate::lambda::lam_pass_exits::simplify_exits;
use crate::lambda::lam_pass_lets_dce::simplify_lets;
use crate::lambda::lam_pass_remove_alias::simplify_alias_with_jsx;
use crate::lambda::lam_primitive::Primitive;
use crate::lambda::lam_tag_info::TagInfo;
use crate::lambda::{Lambda, PrimInfo};

/// Direct port of `compiler/core/lam_compile_main.ml:148-200` pipeline.
pub fn simplify_for_js_backend(lam: &Lambda) -> Lambda {
    simplify_for_js_backend_with_jsx_preserve(lam, false)
}

/// `jsx_preserve` reaches `simplify_alias` here so that the JSX guard in
/// `Lam_pass_remove_alias.simplify_alias` (lam_pass_remove_alias.ml:54-62)
/// fires on the same callees OCaml does.
pub fn simplify_for_js_backend_with_jsx_preserve(lam: &Lambda, jsx_preserve: bool) -> Lambda {
    // OCaml constructs `meta` once at lam_compile_main.ml:150-153 with
    // `~export_idents` and `~export_ident_sets` from the Lam_compile_main.compile
    // entry point. The exports come from `Translmod.transl_implementation`. In
    // Rust, the lowered Lambda still carries them in the top-level
    // `Pmakeblock(_, TagInfo::ModuleExport(ids), _)`, so we recover the same
    // list here. This drives the `Set_ident.mem meta.export_idents` arm in
    // `Lam_pass_collect.collect_info` (lam_pass_collect.ml:92-93) and the
    // `is_export_id` guard in `Lam_pass_remove_alias.simplify_alias`
    // (lam_pass_remove_alias.ml:211).
    let mut meta = LamStats::new(extract_export_idents(lam));
    // Seed the shared rename counter past every stamp already present in the
    // lambda so `Ident.rename` (via beta-reduce) never collides with existing
    // stamps. OCaml's Ident.rename reads from a global mutable counter; this
    // mirrors that. Without the seed, two beta reductions of the same function
    // at distinct call sites renamed their parameters to the same fresh stamp
    // (e.g. two `let prim` declarations at module top level in
    // `coercion_module_alias_test`, which is invalid JS).
    meta.id_gen
        .set_current_stamp(crate::lambda::lam_beta_reduce::max_ident_stamp_in_lambda(lam));

    // lam_compile_main.ml:148 — initial deep_flatten.
    let lam = deep_flatten(lam);

    // lam_compile_main.ml:154 — collect_info into meta.
    collect_info(&mut meta, &lam);

    // lam_compile_main.ml:159 — simplify_exits.
    let lam = simplify_exits(&lam, &meta.id_gen);

    // lam_compile_main.ml:161 — collect_info before simplify_alias.
    collect_info(&mut meta, &lam);

    // lam_compile_main.ml:167 — simplify_alias.
    let lam = simplify_alias_with_jsx(&mut meta, &lam, jsx_preserve);

    // lam_compile_main.ml:169 — deep_flatten.
    let lam = deep_flatten(&lam);

    // lam_compile_main.ml:173 — collect_info.
    collect_info(&mut meta, &lam);

    // lam_compile_main.ml:174 — simplify_alias.
    let lam = simplify_alias_with_jsx(&mut meta, &lam, jsx_preserve);

    // lam_compile_main.ml:175 — deep_flatten.
    let lam = deep_flatten(&lam);

    // lam_compile_main.ml:176 — collect_info.
    collect_info(&mut meta, &lam);

    // lam_compile_main.ml:180 — alpha_conversion.
    let lam = alpha_conversion(&meta, &lam);

    // lam_compile_main.ml:182 — simplify_exits.
    let lam = simplify_exits(&lam, &meta.id_gen);

    // lam_compile_main.ml:183 — collect_info.
    collect_info(&mut meta, &lam);

    // lam_compile_main.ml:188 — simplify_alias.
    let lam = simplify_alias_with_jsx(&mut meta, &lam, jsx_preserve);

    // lam_compile_main.ml:190 — alpha_conversion.
    let lam = alpha_conversion(&meta, &lam);

    // lam_compile_main.ml:193 — simplify_lets (DCE + alias inlining).
    let lam = simplify_lets(&lam);

    // lam_compile_main.ml:200 — final simplify_exits.
    let lam = simplify_exits(&lam, &meta.id_gen);

    // lam_compile_main.ml:212 — Lam_coercion.coerce_and_group_big_lambda
    // (lam_coercion.ml:196). The OCaml flow flattens the lambda into a list
    // of `Lam_group.t` and runs `handle_exports` on the trailing
    // `Pmakeblock(_, ModuleExport _, args)`. Each non-`Lvar` arg gets
    // hoisted into a fresh `Single (Strict, newid, lam)` group; the
    // makeblock's arg list becomes `Lvar newid`. In Rust the JS compile
    // walks one Lambda tree, so we re-emit the equivalent shape: rename
    // the export id, prepend a `Llet (Strict, newid, value, _)` just
    // outside the makeblock, and replace the arg with `Lvar newid`. This
    // makes downstream `compile_expr` see separate top-level bindings
    // instead of inlining `Lconst (Const_block ...)` (etc.) into the
    // module-export block — matching `let X = {...}` snapshots like
    // `variantsMatching.CustomizeTags_d`.
    handle_exports(&mut meta, lam)
}

/// Direct port of `compiler/core/lam_coercion.ml:82-172` — `handle_exports`
/// applied to the trailing module-export `Pmakeblock`.
fn handle_exports(meta: &mut LamStats, lam: Lambda) -> Lambda {
    rewrite_export_makeblock(meta, lam)
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
        Lambda::Lprim(PrimInfo {
            primitive: Primitive::Pmakeblock(tag, TagInfo::ModuleExport(export_ids), mutable_),
            args,
            loc,
        }) => {
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
                        new_export_ids.push(id.clone());
                        new_args.push(arg);
                    }
                    // lam_coercion.ml:112-121 — Lvar with mismatched name:
                    // rename the export id, alias-bind it.
                    Lambda::Lvar(_) => {
                        let newid = orig_export_id.rename(&meta.id_gen);
                        new_export_ids.push(newid.clone());
                        new_args.push(Lambda::Lvar(newid.clone()));
                        hoisted.push((newid, arg, LetKind::Alias));
                    }
                    // lam_coercion.ml:122-157 — non-Lvar arg: rename the
                    // export id, strict-bind it.
                    _ => {
                        let newid = orig_export_id.rename(&meta.id_gen);
                        new_export_ids.push(newid.clone());
                        new_args.push(Lambda::Lvar(newid.clone()));
                        hoisted.push((newid, arg, LetKind::Strict));
                    }
                }
            }

            // Update meta.exports / export_idents to match the renamed
            // export list (lam_coercion.ml:200-205).
            meta.exports = new_export_ids.clone();
            meta.export_idents = new_export_ids.iter().cloned().collect();

            let mut result = Lambda::Lprim(PrimInfo {
                primitive: Primitive::Pmakeblock(
                    tag,
                    TagInfo::ModuleExport(new_export_ids),
                    mutable_,
                ),
                args: new_args,
                loc,
            });
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

/// Walks `lam` and returns the idents carried in the top-level
/// `Pmakeblock(_, TagInfo::ModuleExport(ids), _)` blocks. These mirror the
/// `exports` list `Translmod.transl_implementation` returns to
/// `Lam_compile_main.compile` (js_implementation.ml:158-163). The lowering
/// stage already collects the same set into `LoweringContext.exported_idents`
/// (raw_lambda/lower.rs:502-577), so this helper applies the same shape match
/// against the post-lowering Lambda.
fn extract_export_idents(lam: &Lambda) -> Vec<Ident> {
    let mut exports: Vec<Ident> = Vec::new();
    let mut seen: std::collections::HashSet<Ident> = std::collections::HashSet::new();
    walk(lam, &mut exports, &mut seen);
    exports
}

fn walk(lam: &Lambda, exports: &mut Vec<Ident>, seen: &mut std::collections::HashSet<Ident>) {
    match lam {
        Lambda::Lvar(_) | Lambda::LglobalModule(_, _) | Lambda::Lconst(_) => {}
        Lambda::Lapply(apply) => {
            walk(&apply.ap_func, exports, seen);
            for arg in &apply.ap_args {
                walk(arg, exports, seen);
            }
        }
        Lambda::Lfunction(func) => walk(&func.body, exports, seen),
        Lambda::Llet(_, _, value, body) => {
            walk(value, exports, seen);
            walk(body, exports, seen);
        }
        Lambda::Lletrec(bindings, body) => {
            for (_, lam) in bindings {
                walk(lam, exports, seen);
            }
            walk(body, exports, seen);
        }
        Lambda::Lprim(PrimInfo {
            primitive: Primitive::Pmakeblock(_, TagInfo::ModuleExport(ids), _),
            args,
            ..
        }) => {
            for id in ids {
                if seen.insert(id.clone()) {
                    exports.push(id.clone());
                }
            }
            for arg in args {
                walk(arg, exports, seen);
            }
        }
        Lambda::Lprim(prim) => {
            for arg in &prim.args {
                walk(arg, exports, seen);
            }
        }
        Lambda::Lswitch(scrut, switch) => {
            walk(scrut, exports, seen);
            for (_, lam) in &switch.sw_consts {
                walk(lam, exports, seen);
            }
            for (_, lam) in &switch.sw_blocks {
                walk(lam, exports, seen);
            }
            if let Some(failaction) = &switch.sw_failaction {
                walk(failaction, exports, seen);
            }
        }
        Lambda::LstringSwitch(scrut, cases, default) => {
            walk(scrut, exports, seen);
            for (_, lam) in cases {
                walk(lam, exports, seen);
            }
            if let Some(default) = default {
                walk(default, exports, seen);
            }
        }
        Lambda::LstaticRaise(_, args) => {
            for arg in args {
                walk(arg, exports, seen);
            }
        }
        Lambda::LstaticCatch(body, _, handler)
        | Lambda::LtryWith(body, _, handler)
        | Lambda::Lsequence(body, handler)
        | Lambda::Lwhile(body, handler) => {
            walk(body, exports, seen);
            walk(handler, exports, seen);
        }
        Lambda::LifThenElse(cond, then_, else_) => {
            walk(cond, exports, seen);
            walk(then_, exports, seen);
            walk(else_, exports, seen);
        }
        Lambda::Lfor(_, start, end, _, body) => {
            walk(start, exports, seen);
            walk(end, exports, seen);
            walk(body, exports, seen);
        }
        Lambda::Lfor_of(_, iterable, body) | Lambda::Lfor_await_of(_, iterable, body) => {
            walk(iterable, exports, seen);
            walk(body, exports, seen);
        }
        Lambda::Lbreak | Lambda::Lcontinue => {}
        Lambda::Lassign(_, value) => walk(value, exports, seen),
    }
}
