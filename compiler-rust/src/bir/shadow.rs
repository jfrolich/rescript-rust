//! Stage S2.2 oracle. It checks the bridge, not a replacement lowering pipeline.
//! Both opt-in modes retain the legacy output until a later stage takes over.
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
}

fn report(unit: &str, unsupported: Option<&'static str>) -> anyhow::Result<()> {
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
    let path = directory.join(format!("{outcome}.json"));
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
        stage: "lambda-bridge",
        identical: unsupported.is_none(),
        unsupported,
    })?;
    file.write_all(&data)?;
    Ok(())
}

/// Validate each imported unit and compare the existing Lambda s-expression
/// dumps. Unsupported is a recorded legacy fallback; a difference is an error.
#[cold]
pub fn check_lambda(arena: &LamArena, root: Lam, unit: &str) -> anyhow::Result<()> {
    let imported = match import_lambda(arena, root) {
        Ok(imported) => imported,
        Err(reason) => return report(unit, Some(reason.0)),
    };
    imported
        .arena
        .validate(Some(imported.root), false)
        .map_err(|message| anyhow::anyhow!("{unit}: lambda-bridge validation: {message}"))?;
    let exported = match export_lambda(&imported) {
        Ok(exported) => exported,
        Err(reason) => return report(unit, Some(reason.0)),
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
    report(unit, None)
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
