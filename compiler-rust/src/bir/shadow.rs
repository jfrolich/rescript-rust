//! Shadow oracles. `lambda-bridge` (S2.2) checks the bridge; `lambda-norm`
//! (S4.1) checks the normalising rules against `LamArena`'s constructors.
//! Neither replaces a pipeline stage: both opt-in modes retain the legacy
//! output until a later stage takes over.
use super::bridge::{export_lambda, import_lambda};
use crate::lambda::arena::{Lam, LamArena};
use std::hash::{Hash, Hasher};
use std::io::Write;

/// Backend migration mode. The default remains the legacy implementation.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub enum BackendMode {
    /// No bridge, validation, comparison, or reporting work.
    #[default]
    Legacy,
    /// Exercise supported bridges; lowering still uses the legacy backend in S2.2.
    New,
    /// Compare the bridge round trip and retain legacy output.
    Check,
}
impl BackendMode {
    /// Read `RESCRIPT_BACKEND` once when constructing compiler options. An absent
    /// or unrecognized value leaves the legacy backend selected.
    pub fn from_env() -> Self {
        match std::env::var("RESCRIPT_BACKEND").as_deref() {
            Ok("check") => Self::Check,
            Ok("new") => Self::New,
            _ => Self::Legacy,
        }
    }
}

/// One unit's shadow result. Files contain no source or generated program text.
#[derive(serde::Serialize)]
struct UnitReport<'a> {
    unit: &'a str,
    stage: &'static str,
    identical: bool,
    unsupported: Option<&'static str>,
    /// `lambda-norm`: smart-constructor calls replayed and rows fired.
    #[serde(skip_serializing_if = "Option::is_none")]
    norm: Option<NormReport>,
    #[serde(skip_serializing_if = "std::ops::Not::not")]
    shared_catch_only: bool,
}

#[derive(serde::Serialize)]
struct NormReport {
    calls: u64,
    replayed: std::collections::BTreeMap<&'static str, u32>,
    renormalised: std::collections::BTreeMap<&'static str, u32>,
    #[serde(skip_serializing_if = "std::collections::BTreeMap::is_empty")]
    rules: std::collections::BTreeMap<&'static str, u64>,
    compared: u64,
}

fn report(
    unit: &str,
    stage: &'static str,
    unsupported: Option<&'static str>,
    norm: Option<NormReport>,
) -> anyhow::Result<()> {
    report_with_sharing(unit, stage, unsupported, norm, false)
}

fn report_with_sharing(
    unit: &str, stage: &'static str, unsupported: Option<&'static str>,
    norm: Option<NormReport>, shared_catch_only: bool,
) -> anyhow::Result<()> {
    let Some(directory) = std::env::var_os("RESCRIPT_BACKEND_STATS") else {
        return Ok(());
    };
    let directory = std::path::Path::new(&directory);
    std::fs::create_dir_all(directory)?;
    let mut hash = std::collections::hash_map::DefaultHasher::new();
    unit.hash(&mut hash);
    let directory = directory.join(format!("{:016x}", hash.finish()));
    std::fs::create_dir_all(&directory)?;
    // Immutable outcome files: repeated modes/processes never overwrite a
    // fallback with success. The collector groups them by source unit and
    // keeps a fallback if any invocation was unsupported.
    let outcome = unsupported.unwrap_or("identical").replace(' ', "_");
    // The bridge stage keeps its file names; later stages prefix theirs.
    let path = if stage == "lambda-bridge" {
        directory.join(format!("{outcome}.json"))
    } else {
        directory.join(format!("{stage}.{outcome}.json"))
    };
    let mut file = match std::fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(path)
    {
        Ok(file) => file,
        Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => return Ok(()),
        Err(error) => return Err(error.into()),
    };
    let data = serde_json::to_vec(&UnitReport {
        unit,
        stage,
        identical: unsupported.is_none(),
        unsupported,
        norm,
        shared_catch_only,
    })?;
    file.write_all(&data)?;
    Ok(())
}

/// Validate each imported unit and compare the existing Lambda s-expression
/// dumps. Unsupported is a recorded legacy fallback; a difference is an error.
#[cold]
pub fn check_lambda(arena: &LamArena, root: Lam, unit: &str) -> anyhow::Result<()> {
    // This hook already runs only off the default path. S4 rounds are Check
    // only: New still exercises the bridges without running rewrite rounds.
    if BackendMode::from_env() == BackendMode::Check {
        check_flatten(arena, root, unit)?;
        check_exits(arena, root, unit)?;
    }
    let imported = match import_lambda(arena, root) {
        Ok(imported) => imported,
        Err(reason) => return report(unit, "lambda-bridge", Some(reason.0), None),
    };
    imported
        .arena
        .validate(Some(imported.root), false)
        .map_err(|message| anyhow::anyhow!("{unit}: lambda-bridge validation: {message}"))?;
    let exported = match export_lambda(&imported) {
        Ok(exported) => exported,
        Err(reason) => return report(unit, "lambda-bridge", Some(reason.0), None),
    };
    let mut before = Vec::new();
    let mut after = Vec::new();
    crate::lambda::sexp_lambda::print_lambda(&arena.export(root), &mut before)?;
    crate::lambda::sexp_lambda::print_lambda(&exported.to_tree(), &mut after)?;
    if before != after {
        let before = String::from_utf8_lossy(&before);
        let after = String::from_utf8_lossy(&after);
        let line = before
            .lines()
            .zip(after.lines())
            .position(|(a, b)| a != b)
            .unwrap_or_else(|| before.lines().count().min(after.lines().count()))
            + 1;
        anyhow::bail!("{unit}: lambda-bridge mismatch at line {line}");
    }
    report(unit, "lambda-bridge", None, None)
}

/// Stage `lambda-norm`: replay the unit's lowering through the Bir
/// normalising rules and renormalise the lowered unit, each compared with
/// `LamArena`'s smart constructors (`bir::replay`). `raw` is the unit's raw
/// Lambda root, still present in the arena lowering returned.
#[cold]
pub fn check_norm(arena: &LamArena, raw: Lam, unit: &str) -> anyhow::Result<()> {
    let rows = |fired: [u32; super::l::norm::ROWS]| {
        super::l::norm::ROW_NAMES
            .into_iter()
            .zip(fired)
            .filter(|(_, count)| *count != 0)
            .collect()
    };
    match super::replay::compare(arena, raw, unit)? {
        Ok(stats) => report(
            unit,
            "lambda-norm",
            None,
            Some(NormReport {
                calls: stats.calls,
                replayed: rows(stats.replayed),
                renormalised: rows(stats.renormalised),
                compared: stats.compared,
                rules: Default::default(),
            }),
        ),
        Err(reason) => report(unit, "lambda-norm", Some(reason.0), None),
    }
}

/// Stage `js-bridge`: compare the post-pass program with a J-level round trip.
/// Both prints use the legacy printer, regardless of the selected output printer.
#[cold]
pub fn check_js(
    program: &crate::js_ir::arena::JsDepsProgram,
    resolver: &crate::js_ir::ModulePathResolver,
    directives: &[String],
    debug: bool,
    jsx_preserve: bool,
    emit_header: bool,
    unit: &str,
) -> anyhow::Result<()> {
    let imported = match super::bridge_j::import_js(program) {
        Ok(imported) => imported,
        Err(reason) => return report(unit, "js-bridge", Some(reason.0), None),
    };
    imported.arena.validate(Some(imported.root), false)
        .map_err(|message| anyhow::anyhow!("{unit}: js-bridge validation: {message}"))?;
    let exported = match super::bridge_j::export_js(&imported) {
        Ok(exported) => exported,
        Err(reason) => return report(unit, "js-bridge", Some(reason.0), None),
    };
    let print = |p| crate::js_ir::print_deps_program_with_directives_and_options(
        p, Some(resolver), directives, debug, jsx_preserve, emit_header,
    );
    let before = print(program);
    let after = print(&exported);
    if before != after {
        let line = before.lines().zip(after.lines()).position(|(a,b)| a != b)
            .unwrap_or_else(|| before.lines().count().min(after.lines().count())) + 1;
        anyhow::bail!("{unit}: js-bridge mismatch at line {line}");
    }
    report(unit, "js-bridge", None, None)
}

/// The first deep_flatten cut in simplify_in_arena: its input is the lowered,
/// alias-collapsed root passed to check_lambda. Run the same first call on a
/// private legacy arena, with exactly its ident_stamp_bound counter seed.
/// Neither path touches the live pipeline or the legacy thread-local counter.
#[cold]
pub fn check_flatten(arena: &LamArena, root: Lam, unit: &str) -> anyhow::Result<()> {
    let mut imported = match import_lambda(arena, root) {
        Ok(imported) => imported,
        Err(reason) => return report(unit, "lambda-flatten", Some(reason.0), None),
    };
    let stamp = arena.ident_stamp_bound();
    let stats = {
        let mut engine = super::engine::Engine::new(&mut imported.arena);
        engine.set_current_stamp(stamp as u32);
        engine.run(&super::l::flatten::FLATTEN, imported.root);
        engine.stats
    };
    for (var, source) in stats.renames {
        if let Err(reason) = imported.register_rename(var, source) {
            return report(unit, "lambda-flatten", Some(reason.0), None);
        }
    }
    imported.arena.validate(Some(imported.root), false)
        .map_err(|message| anyhow::anyhow!("{unit}: lambda-flatten validation: {message}"))?;
    let exported = match export_lambda(&imported) {
        Ok(exported) => exported,
        Err(reason) => return report(unit, "lambda-flatten", Some(reason.0), None),
    };
    let generator = crate::context::IdGenerator::new();
    generator.set_current_stamp(stamp);
    let mut legacy = arena.clone();
    let expected = crate::lambda::lam_pass_deep_flatten::deep_flatten(&mut legacy, root, &generator);
    if super::l::flatten::identities(&legacy, expected)
        != super::l::flatten::identities(&exported.arena, exported.root)
    {
        anyhow::bail!("{unit}: lambda-flatten identifier mismatch (name, stamp or flags)");
    }
    let mut before = Vec::new();
    let mut after = Vec::new();
    crate::lambda::sexp_lambda::print_lambda(&legacy.export(expected), &mut before)?;
    crate::lambda::sexp_lambda::print_lambda(&exported.to_tree(), &mut after)?;
    if before != after {
        let before = String::from_utf8_lossy(&before);
        let after = String::from_utf8_lossy(&after);
        let line = before.lines().zip(after.lines()).position(|(a,b)| a != b)
            .unwrap_or_else(|| before.lines().count().min(after.lines().count())) + 1;
        anyhow::bail!("{unit}: lambda-flatten mismatch at line {line}: expected {:?}, got {:?}",
            before.lines().nth(line - 1), after.lines().nth(line - 1));
    }
    report(unit, "lambda-flatten", None, Some(NormReport {
        calls: stats.entered,
        replayed: Default::default(),
        renormalised: Default::default(),
        compared: stats.compared,
        rules: stats.rules,
    }))
}

/// First exits cut: flatten then exits on each side, with one private counter.
/// Compare the ordered count too; structural CatchHeader::uses is not this fact.
#[cold]
pub fn check_exits(arena: &LamArena, root: Lam, unit: &str) -> anyhow::Result<()> {
    let mut imported = match import_lambda(arena, root) {
        Ok(imported) => imported,
        Err(reason) => return report(unit, "lambda-exits", Some(reason.0), None),
    };
    let stamp = arena.ident_stamp_bound();
    let (stats, counts) = {
        let mut engine = super::engine::Engine::new(&mut imported.arena);
        engine.set_current_stamp(stamp as u32);
        engine.run(&super::l::flatten::FLATTEN, imported.root);
        let counts = super::l::exits::count(engine.bir(), imported.root);
        // Report only this round's rules, retaining flatten's fresh identities.
        engine.stats.rules.clear();
        engine.stats.entered = 0;
        engine.run(&super::l::exits::EXITS, imported.root);
        (engine.stats, counts)
    };
    for (var, source) in stats.renames {
        if let Err(reason) = imported.register_rename(var, source) {
            return report(unit, "lambda-exits", Some(reason.0), None);
        }
    }
    imported
        .arena
        .validate(Some(imported.root), false)
        .map_err(|message| anyhow::anyhow!("{unit}: lambda-exits validation: {message}"))?;
    let exported = match export_lambda(&imported) {
        Ok(exported) => exported,
        Err(reason) => return report(unit, "lambda-exits", Some(reason.0), None),
    };
    let generator = crate::context::IdGenerator::new();
    generator.set_current_stamp(stamp);
    let mut legacy = arena.clone();
    let expected =
        crate::lambda::lam_pass_deep_flatten::deep_flatten(&mut legacy, root, &generator);
    let legacy_counts: std::collections::BTreeMap<_, _> =
        crate::lambda::lam_pass_exits::count_helper(&legacy, expected)
            .into_iter()
            .map(|(label, count)| (label as u32, count))
            .collect();
    if counts != legacy_counts {
        anyhow::bail!("{unit}: lambda-exits ordered count mismatch");
    }
    let expected = crate::lambda::lam_pass_exits::simplify_exits(&mut legacy, expected, &generator);
    if super::l::flatten::identities(&legacy, expected)
        != super::l::flatten::identities(&exported.arena, exported.root)
    {
        anyhow::bail!("{unit}: lambda-exits identifier mismatch (name, stamp or flags)");
    }
    let mut before = Vec::new();
    let mut after = Vec::new();
    crate::lambda::sexp_lambda::print_lambda(&legacy.export(expected), &mut before)?;
    crate::lambda::sexp_lambda::print_lambda(&exported.to_tree(), &mut after)?;
    if before != after {
        let before = String::from_utf8_lossy(&before);
        let after = String::from_utf8_lossy(&after);
        let line = before
            .lines()
            .zip(after.lines())
            .position(|(a, b)| a != b)
            .unwrap_or_else(|| before.lines().count().min(after.lines().count()))
            + 1;
        anyhow::bail!(
            "{unit}: lambda-exits mismatch at line {line}: expected {:?}, got {:?}",
            before.lines().nth(line - 1),
            after.lines().nth(line - 1)
        );
    }
    report(
        unit,
        "lambda-exits",
        None,
        Some(NormReport {
            calls: stats.entered,
            replayed: Default::default(),
            renormalised: Default::default(),
            compared: stats.compared,
            rules: stats.rules,
        }),
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn both_opt_in_modes_keep_legacy_javascript() {
        let mut options = crate::driver::CompilerOptions {
            backend: BackendMode::Legacy,
            ..Default::default()
        };
        let source = "let answer = 42";
        let expected =
            crate::driver::compile_source_to_js_with_options(source, "Mode.res", &options).unwrap();
        for mode in [BackendMode::Check, BackendMode::New] {
            options.backend = mode;
            let actual =
                crate::driver::compile_source_to_js_with_options(source, "Mode.res", &options)
                    .unwrap();
            assert_eq!(actual, expected);
        }
    }
}

/// Failure classification is preserved through the compiler's infallible IR API.
/// Only Unsupported becomes a fallback; export/validation failures remain errors.
pub(crate) enum LowerFailure {
    Unsupported(super::bridge::Unsupported, bool),
    Error(anyhow::Error),
}

/// Captures the same program points on both sides of the shared legacy tail.
pub(crate) enum LowerCheck {
    Failed(LowerFailure),
    Supported(Box<LowerPair>),
}

pub(crate) struct LowerPair {
    pub before: [crate::js_ir::arena::JsDepsProgram; 2],
    pub after: [crate::js_ir::arena::JsDepsProgram; 2],
    pub locations: Option<std::sync::Arc<crate::lambda::LamLocTable>>,
}

/// Import exactly the simplified root about to enter legacy compile_expr.
pub(crate) fn prepare_lower(
    arena: &LamArena,
    root: Lam,
    locations: Option<&crate::lambda::LamLocTable>,
) -> Result<
    (
        crate::js_ir::arena::JsArena,
        crate::lambda::lam_compile::Compiled,
    ),
    LowerFailure,
> {
    let (input, catch_only) = super::bridge::import_for_lowering(arena, root);
    let input = input.map_err(|reason| match reason.0 {
        "shared Lambda subtree with binder" | "shared Lambda expansion" => LowerFailure::Unsupported(reason, catch_only),
        _ => LowerFailure::Error(anyhow::anyhow!("lower input import: {reason}")),
    })?;
    let lowered = super::lower::lower(input, locations, false).map_err(|reason| LowerFailure::Unsupported(reason, false))?;
    lowered
        .program
        .arena
        .validate(Some(lowered.program.root), false)
        .map_err(|error| LowerFailure::Error(anyhow::anyhow!("lower validation: {error}")))?;
    // bridge_j's exporter uses expr_with/stmt_with and alloc_* only: no
    // smart constructor and no normalize. The last SExp transports Out::value.
    let mut exported = super::bridge_j::export_js(&lowered.program)
        .map_err(|error| LowerFailure::Error(anyhow::anyhow!("lower export: {error}")))?;
    #[cfg(debug_assertions)]
    if arena.node_count() <= 128 {
        let (direct, _) = super::bridge::import_for_lowering(arena, root);
        let direct = direct.map_err(|e| LowerFailure::Error(anyhow::anyhow!("direct import: {e}")))?;
        let direct = super::lower::lower(direct, locations, true)
            .map_err(|e| LowerFailure::Error(anyhow::anyhow!("direct lower: {e}")))?;
        let direct = super::bridge_j::export_js(&direct.program)
            .map_err(|e| LowerFailure::Error(anyhow::anyhow!("direct export: {e}")))?;
        let print = |p| crate::js_ir::print_deps_program_with_directives_and_options(p, None, &[], false, false, false);
        compare_lower_text("P1", "probe vs direct", &print(&direct), &print(&exported))
            .map_err(LowerFailure::Error)?;
    }
    let value =
        exported.program.block.pop().ok_or_else(|| {
            LowerFailure::Error(anyhow::anyhow!("lower export lacks output value"))
        })?;
    let crate::js_ir::arena::StmtKind::Exp(expr) = exported.program.arena.sk(value) else {
        return Err(LowerFailure::Error(anyhow::anyhow!(
            "lower export value is not SExp"
        )));
    };
    use crate::lambda::lam_compile::OutputFinished;
    let finished = match lowered.finished {
        super::lower::Finished::True => OutputFinished::True,
        super::lower::Finished::False => OutputFinished::False,
        super::lower::Finished::Dummy => OutputFinished::Dummy,
    };
    Ok((
        exported.program.arena,
        crate::lambda::lam_compile::Compiled {
            prelude: exported.program.block,
            expr,
            finished,
        },
    ))
}

/// Two independent texts through the legacy ES module printer; when requested,
/// also compare source-map mappings. Mismatches never become Unsupported.
pub(crate) fn check_lower(check: LowerCheck, unit: &str, jsx_preserve: bool) -> anyhow::Result<()> {
    match check {
        LowerCheck::Failed(LowerFailure::Unsupported(reason, catch_only)) => {
            report_with_sharing(unit, "lower", Some(reason.0), None, catch_only)
        }
        LowerCheck::Failed(LowerFailure::Error(error)) => {
            Err(anyhow::anyhow!("{unit}: lower: {error:#}"))
        }
        LowerCheck::Supported(pair) => {
            let LowerPair { before, after, locations } = *pair;
            for (text, pair) in [("lower", before), ("lower+passes", after)] {
                let print = |p| {
                    crate::js_ir::print_deps_program_with_directives_and_options(
                        p,
                        None,
                        &[],
                        false,
                        jsx_preserve,
                        false,
                    )
                };
                compare_lower_text(unit, text, &print(&pair[0]), &print(&pair[1]))?;
                if let Some(locations) = &locations {
                    let mapped = |p| crate::js_ir::print_deps_program_with_source_map(
                        p, None, &[], false, jsx_preserve, false,
                        std::path::Path::new("lower.js"), std::path::Path::new(unit),
                        crate::js_ir::source_map::SourceMapMode::Hidden, false, "", locations.clone()
                    );
                    let (left_text, left_map) = mapped(&pair[0]);
                    let (right_text, right_map) = mapped(&pair[1]);
                    compare_lower_text(unit, text, &left_text, &right_text)?;
                    compare_lower_text(unit, &format!("{text} mappings"), &left_map.unwrap_or_default(), &right_map.unwrap_or_default())?;
                }
            }
            report(unit, "lower", None, None)
        }
    }
}

fn compare_lower_text(unit: &str, text: &str, expected: &str, actual: &str) -> anyhow::Result<()> {
    if expected != actual {
        let line = expected
            .split_inclusive('\n')
            .zip(actual.split_inclusive('\n'))
            .position(|(a, b)| a != b)
            .unwrap_or_else(|| expected.lines().count().min(actual.lines().count()))
            + 1;
        anyhow::bail!(
            "{unit}: {text} mismatch at line {line}: expected {:?}, got {:?}",
            expected.split_inclusive('\n').nth(line - 1),
            actual.split_inclusive('\n').nth(line - 1)
        );
    }
    Ok(())
}

#[cfg(test)]
mod lower_tests {
    use super::*;
    #[test]
    fn both_text_mismatches_are_errors_with_first_line() {
        for text in ["lower", "lower+passes"] {
            let error = compare_lower_text("Example.res", text, "same\nold\n", "same\nnew\n")
                .unwrap_err()
                .to_string();
            assert!(error.contains(&format!("Example.res: {text} mismatch at line 2")));
        }
        assert!(compare_lower_text("Example.res", "lower", "same\n", "same").is_err());
    }
    #[test]
    fn supported_gate_checks_both_program_points() {
        use crate::js_ir::arena::{JsArena, JsDepsProgram, JsProgram, StmtKind};
        let empty = JsDepsProgram {
            program: JsProgram::new_in(vec![], vec![], JsArena::new()),
            modules: vec![], side_effect: None,
        };
        let mut changed = empty.clone();
        let statement = changed.program.arena.stmt(StmtKind::Debugger);
        changed.program.block.push(statement);
        for after_changed in [false, true] {
            let same = [empty.clone(), empty.clone()];
            let different = [empty.clone(), changed.clone()];
            let check = if after_changed {
                LowerCheck::Supported(Box::new(LowerPair { before: same, after: different, locations: None }))
            } else {
                LowerCheck::Supported(Box::new(LowerPair { before: different, after: same, locations: None }))
            };
            let text = if after_changed { "lower+passes" } else { "lower" };
            let error = check_lower(check, "Gate.res", false).unwrap_err().to_string();
            assert!(error.contains(&format!("Gate.res: {text} mismatch at line")));
        }
    }
    #[test]
    fn shared_binder_is_the_explicit_bridge_fallback() {
        let mut arena = LamArena::new();
        let constant = arena.const_(crate::lambda::lam_constant::Constant::JsNull);
        let id = crate::ident::Ident::new("x", 1, crate::ident::IdentFlags::NONE);
        let body = arena.var(id);
        let binding = arena.let_(crate::lambda::lam_compat::LetKind::Strict, id, constant, body);
        let root = arena.seq_raw(binding, binding);
        let result = prepare_lower(&arena, root, None);
        assert!(matches!(result, Err(LowerFailure::Unsupported(
            super::super::bridge::Unsupported("shared Lambda subtree with binder"), false
        ))));
    }
    #[test]
    fn export_errors_are_not_fallbacks() {
        let check = LowerCheck::Failed(LowerFailure::Error(anyhow::anyhow!("bad exported tree")));
        assert!(check_lower(check, "Example.res", false).is_err());
    }
}
