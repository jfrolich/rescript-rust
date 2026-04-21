//! JS-backend lambda simplification pipeline.
//!
//! Direct port of `compiler/core/lam_compile_main.ml:148-200`. Calls the
//! ported passes in the same order as OCaml. Passes that have not been ported
//! yet (`simplify_alias`, `alpha_conversion`) are stubbed as identity functions
//! and will be replaced as their ports land.
//!
//! Every line here must trace to a specific line in
//! `compiler/core/lam_compile_main.ml`. No Rust-only logic.

use crate::lambda::collect_info::collect_info;
use crate::lambda::compile_context::LamStats;
use crate::lambda::deep_flatten::deep_flatten;
use crate::lambda::pass_exits::simplify_exits;
use crate::lambda::pass_lets_dce::simplify_lets;
use crate::lambda::Lambda;

/// Stub for `Lam_pass_remove_alias.simplify_alias`
/// (compiler/core/lam_pass_remove_alias.ml). Identity for now: when the real
/// pass is ported it will fold field reads, unwrap optional blocks, inline
/// known cross-module functions and fold boolean constants using the
/// `ident_tbl` populated by `collect_info`.
fn simplify_alias(_meta: &LamStats, lam: &Lambda) -> Lambda {
    lam.clone()
}

/// Stub for `Lam_pass_alpha_conversion.alpha_conversion`
/// (compiler/core/lam_pass_alpha_conversion.ml). Identity for now: when the
/// real pass is ported it will rename idents that have been duplicated by
/// inlining so static analyses downstream see fresh names.
fn alpha_conversion(_meta: &LamStats, lam: &Lambda) -> Lambda {
    lam.clone()
}

/// Direct port of `compiler/core/lam_compile_main.ml:148-200` pipeline.
pub fn simplify_for_js_backend(lam: &Lambda) -> Lambda {
    simplify_for_js_backend_with_jsx_preserve(lam, false)
}

/// `jsx_preserve` is wired through here for parity with OCaml's
/// `Js_config.jsx_preserve`, but `simplify_alias` is currently stubbed so the
/// flag has no effect yet. It is kept on the public API so the call sites in
/// `compile.rs` continue to thread the value down.
pub fn simplify_for_js_backend_with_jsx_preserve(lam: &Lambda, _jsx_preserve: bool) -> Lambda {
    // OCaml constructs `meta` once at line 150-153 with `~export_idents` and
    // `~export_ident_sets` from the Lam_compile_main.compile entry point.
    // The Rust JS backend does not currently propagate exports down to this
    // pass, so meta starts with empty exports. This degrades the
    // `if Set_ident.mem meta.export_idents ident` arm in
    // `Lam_pass_collect.collect_info` (lam_pass_collect.ml:92-93) — non-Lfunction
    // exported bindings will not be annotated with FunctionId. Fix when the
    // export set becomes available here.
    let mut meta = LamStats::new(Vec::new());

    // lam_compile_main.ml:148 — initial deep_flatten.
    let lam = deep_flatten(lam);

    // lam_compile_main.ml:154 — collect_info into meta.
    collect_info(&mut meta, &lam);

    // lam_compile_main.ml:159 — simplify_exits.
    let lam = simplify_exits(&lam);

    // lam_compile_main.ml:161 — collect_info before simplify_alias.
    collect_info(&mut meta, &lam);

    // lam_compile_main.ml:167 — simplify_alias.
    let lam = simplify_alias(&meta, &lam);

    // lam_compile_main.ml:169 — deep_flatten.
    let lam = deep_flatten(&lam);

    // lam_compile_main.ml:173 — collect_info.
    collect_info(&mut meta, &lam);

    // lam_compile_main.ml:174 — simplify_alias.
    let lam = simplify_alias(&meta, &lam);

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
    let lam = simplify_alias(&meta, &lam);

    // lam_compile_main.ml:190 — alpha_conversion.
    let lam = alpha_conversion(&meta, &lam);

    // lam_compile_main.ml:193 — simplify_lets (DCE + alias inlining).
    let lam = simplify_lets(&lam);

    // lam_compile_main.ml:200 — final simplify_exits.
    simplify_exits(&lam)
}
