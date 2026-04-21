//! JS-backend lambda simplification pipeline.
//!
//! Direct port of `compiler/core/lam_compile_main.ml:148-200`. Calls the
//! ported passes in the same order as OCaml.
//!
//! Every line here must trace to a specific line in
//! `compiler/core/lam_compile_main.ml`. No Rust-only logic.

use crate::ident::Ident;
use crate::lambda::collect_info::collect_info;
use crate::lambda::compile_context::LamStats;
use crate::lambda::deep_flatten::deep_flatten;
use crate::lambda::pass_alpha_conversion::alpha_conversion;
use crate::lambda::pass_exits::simplify_exits;
use crate::lambda::pass_lets_dce::simplify_lets;
use crate::lambda::pass_remove_alias::simplify_alias_with_jsx;
use crate::lambda::primitive::Primitive;
use crate::lambda::tag_info::TagInfo;
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
        .set_current_stamp(crate::lambda::beta_reduce::max_ident_stamp_in_lambda(lam));

    // lam_compile_main.ml:148 — initial deep_flatten.
    let lam = deep_flatten(lam);

    // lam_compile_main.ml:154 — collect_info into meta.
    collect_info(&mut meta, &lam);

    // lam_compile_main.ml:159 — simplify_exits.
    let lam = simplify_exits(&lam);

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
    let lam = simplify_exits(&lam);

    // lam_compile_main.ml:183 — collect_info.
    collect_info(&mut meta, &lam);

    // lam_compile_main.ml:188 — simplify_alias.
    let lam = simplify_alias_with_jsx(&mut meta, &lam, jsx_preserve);

    // lam_compile_main.ml:190 — alpha_conversion.
    let lam = alpha_conversion(&meta, &lam);

    // lam_compile_main.ml:193 — simplify_lets (DCE + alias inlining).
    let lam = simplify_lets(&lam);

    // lam_compile_main.ml:200 — final simplify_exits.
    simplify_exits(&lam)
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
        Lambda::Lassign(_, value) => walk(value, exports, seen),
    }
}
