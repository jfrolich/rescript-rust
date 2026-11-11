use crate::helpers;

use super::build_types::{BuildCommandState, CompilerInfo};
use super::packages;
use super::{clean, logs, state_db};
use ahash::AHashMap;
use rayon::prelude::*;

// The compiler identity a package was built with, kept in its build state
// database (see `state_db`). A missing or different value is a mismatch.
const VERSION: &str = "compiler.version";
const BSC_PATH: &str = "compiler.bsc_path";
const BSC_HASH: &str = "compiler.bsc_hash";
const RESCRIPT_CONFIG_HASH: &str = "compiler.rescript_config_hash";
const SOURCE_MAP_ARGS: &str = "compiler.source_map_args";
const RUNTIME_PATH: &str = "compiler.runtime_path";

pub enum CompilerCheckResult {
    SameCompilerAsLastRun,
    CleanedPackagesDueToCompiler,
}

fn get_rescript_config_hash(package: &packages::Package) -> Option<String> {
    helpers::compute_file_hash(&package.config.path).map(|hash| hash.to_hex().to_string())
}

/// The compiler identity of a build, as recorded for `package`. `None` when
/// the configuration cannot be hashed.
fn current_entries(
    package: &packages::Package,
    compiler: &CompilerInfo,
    source_map_args: &[String],
) -> Option<Vec<(&'static str, String)>> {
    Some(vec![
        (BSC_PATH, compiler.bsc_path.to_string_lossy().to_string()),
        (BSC_HASH, compiler.bsc_hash.to_hex().to_string()),
        (RUNTIME_PATH, compiler.runtime_path.to_string_lossy().to_string()),
        (RESCRIPT_CONFIG_HASH, get_rescript_config_hash(package)?),
        (
            SOURCE_MAP_ARGS,
            serde_json::to_string(source_map_args).unwrap_or_default(),
        ),
    ])
}

pub fn verify_compiler_info(
    packages: &AHashMap<String, packages::Package>,
    compiler: &CompilerInfo,
    source_map_args: &[String],
) -> CompilerCheckResult {
    verify_compiler_info_with(packages, compiler, source_map_args, &read_metas(packages))
}

/// Every package's recorded metadata, for the packages that have a record.
pub fn read_metas(
    packages: &AHashMap<String, packages::Package>,
) -> AHashMap<String, std::collections::BTreeMap<String, String>> {
    packages
        .par_iter()
        .filter_map(|(name, package)| Some((name.clone(), state_db::read_meta(package)?)))
        .collect::<Vec<_>>()
        .into_iter()
        .collect()
}

/// [`verify_compiler_info`] against the metadata [`read_metas`] read.
pub fn verify_compiler_info_with(
    packages: &AHashMap<String, packages::Package>,
    compiler: &CompilerInfo,
    source_map_args: &[String],
    metas: &AHashMap<String, std::collections::BTreeMap<String, String>>,
) -> CompilerCheckResult {
    let mismatched_packages = packages
        .values()
        .par_bridge()
        .filter(|package| {
            let Some(meta) = metas
                .get(&package.name)
                .filter(|meta| meta.contains_key(BSC_HASH))
            else {
                // No recorded build: if the build folder holds a compiler log
                // anyway, it came from a build we know nothing about.
                return logs::does_ocaml_build_compiler_log_exist(package);
            };
            let Some(current) = current_entries(package, compiler, source_map_args) else {
                return true;
            };
            current.iter().any(|(key, value)| {
                let stored = meta.get(*key);
                if stored != Some(value) {
                    log::debug!(
                        "compiler-info mismatch for {}: {key} changed (stored={stored:?}, current='{value}')",
                        package.name
                    );
                    true
                } else {
                    false
                }
            })
        })
        .collect::<Vec<_>>();

    let cleaned_count = mismatched_packages.len();
    mismatched_packages.par_iter().for_each(|package| {
        // suppress progress printing during init to avoid breaking step output
        clean::clean_package(false, true, package);
    });
    if cleaned_count == 0 {
        CompilerCheckResult::SameCompilerAsLastRun
    } else {
        CompilerCheckResult::CleanedPackagesDueToCompiler
    }
}

/// Record the compiler identity of this build for every package.
/// The compiler identity to record for each package of the build (see
/// [`recorded_entries`]).
pub fn source_map_args(build_state: &BuildCommandState) -> Vec<String> {
    build_state
        .get_root_config()
        .get_source_map_args(build_state.source_map_command)
}

/// The compiler identity of this build as recorded for `package`, `None`
/// when its configuration cannot be hashed.
pub fn recorded_entries(
    build_state: &BuildCommandState,
    package: &packages::Package,
    source_map_args: &[String],
) -> Option<Vec<(&'static str, String)>> {
    let mut entries = current_entries(package, &build_state.compiler_info, source_map_args)?;
    entries.push((VERSION, env!("CARGO_PKG_VERSION").to_string()));
    Some(entries)
}

pub fn write_compiler_info(build_state: &BuildCommandState) {
    let source_map_args = source_map_args(build_state);
    build_state.packages.par_iter().for_each(|(_, package)| {
        if let Some(entries) = recorded_entries(build_state, package, &source_map_args) {
            // The record read at the start of the build holds the package's
            // metadata, unless the package was cleaned since.
            let recorded = build_state
                .previous_in_process
                .as_ref()
                .and_then(|previous| previous.packages.get(&package.name))
                .map(|record| &record.state.meta);
            state_db::write_meta_over(package, recorded, &entries);
        }
    });
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::build::packages::{Namespace, Package};
    use crate::config;
    use ahash::{AHashMap, AHashSet};
    use std::fs;
    use std::path::Path;
    use tempfile::TempDir;

    fn test_compiler(root: &Path) -> CompilerInfo {
        CompilerInfo {
            bsc_path: root.join("bsc"),
            bsc_hash: blake3::hash(b"test-bsc"),
            runtime_path: root.join("runtime"),
        }
    }

    fn test_package(root: &Path, name: &str) -> Package {
        let package_path = root.join(name);
        fs::create_dir_all(&package_path).expect("package directory should be created");
        let config_path = package_path.join("rescript.json");
        fs::write(&config_path, format!(r#"{{"name":"{name}"}}"#)).expect("rescript.json should be written");

        Package {
            name: name.to_string(),
            config: config::tests::create_config(config::tests::CreateConfigArgs {
                name: name.to_string(),
                bs_deps: vec![],
                build_dev_deps: vec![],
                allowed_dependents: None,
                path: config_path,
            }),
            source_folders: AHashSet::new(),
            source_files: None,
            namespace: Namespace::NoNamespace,
            modules: None,
            path: package_path,
            dirs: None,
            gentype_dirs: None,
            is_local_dep: true,
            is_root: false,
        }
    }

    fn write_test_compiler_info(package: &Package, compiler: &CompilerInfo, source_map_args: Vec<&str>) {
        fs::create_dir_all(package.get_ocaml_build_path()).expect("ocaml build directory should be created");
        let source_map_args: Vec<String> = source_map_args.into_iter().map(str::to_string).collect();
        let entries = current_entries(package, compiler, &source_map_args)
            .expect("rescript config hash should be available");
        state_db::write_meta(package, &entries);
    }

    fn packages_map(package: Package) -> AHashMap<String, Package> {
        let mut packages = AHashMap::new();
        packages.insert(package.name.clone(), package);
        packages
    }

    #[test]
    fn verify_compiler_info_keeps_package_when_source_map_args_match() {
        let temp_dir = TempDir::new().expect("temp dir should be created");
        let compiler = test_compiler(temp_dir.path());
        let package = test_package(temp_dir.path(), "dep");
        let build_path = package.get_build_path();
        let source_map_args = vec!["-bs-source-map".to_string(), "linked".to_string()];
        write_test_compiler_info(&package, &compiler, vec!["-bs-source-map", "linked"]);

        let result = verify_compiler_info(&packages_map(package), &compiler, &source_map_args);

        assert!(matches!(result, CompilerCheckResult::SameCompilerAsLastRun));
        assert!(build_path.exists());
    }

    /// Stored interfaces are encoded by the compiler linked into the
    /// executable, with no format version of their own: a build by another
    /// executable (another hash) must not decode them. Its package is
    /// cleaned, database included.
    #[test]
    fn verify_compiler_info_cleans_stored_interfaces_of_another_compiler() {
        let temp_dir = TempDir::new().expect("temp dir should be created");
        let old_compiler = test_compiler(temp_dir.path());
        let package = test_package(temp_dir.path(), "dep");
        let build_path = package.get_build_path();
        let db = state_db::path(&package);
        write_test_compiler_info(&package, &old_compiler, vec![]);
        state_db::write_runtime_interfaces(&db, "key", &[("Stdlib".to_string(), vec![1, 2, 3])]);
        assert!(state_db::read_runtime_interfaces(&db, "key").is_some());

        let new_compiler = CompilerInfo {
            bsc_hash: blake3::hash(b"another-bsc"),
            ..test_compiler(temp_dir.path())
        };
        let result = verify_compiler_info(&packages_map(package), &new_compiler, &[]);

        assert!(matches!(
            result,
            CompilerCheckResult::CleanedPackagesDueToCompiler
        ));
        assert!(!build_path.exists());
        assert!(state_db::read_runtime_interfaces(&db, "key").is_none());
    }

    #[test]
    fn verify_compiler_info_cleans_package_when_source_map_args_change() {
        let temp_dir = TempDir::new().expect("temp dir should be created");
        let compiler = test_compiler(temp_dir.path());
        let package = test_package(temp_dir.path(), "dep");
        let build_path = package.get_build_path();
        let source_map_args = vec!["-bs-source-map".to_string(), "linked".to_string()];
        write_test_compiler_info(&package, &compiler, vec!["-bs-source-map", "false"]);

        let result = verify_compiler_info(&packages_map(package), &compiler, &source_map_args);

        assert!(matches!(
            result,
            CompilerCheckResult::CleanedPackagesDueToCompiler
        ));
        assert!(!build_path.exists());
    }
}
