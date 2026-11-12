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
