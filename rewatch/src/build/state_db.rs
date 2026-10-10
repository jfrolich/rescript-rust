//! Per-package build state, in `lib/bs/rescript.sqlite`.
//!
//! The only things a build keeps on disk besides its JavaScript and the
//! editor's `.compiler.log`:
//!
//! - the compiler identity and configuration hash the package was built with
//!   (see [`super::compiler_info`]): a mismatch cleans the package;
//! - the in-process build record read by [`super::incremental`]: when the
//!   last build started and whether it succeeded, every module's source
//!   paths, when each module's JavaScript was last confirmed up to date, and
//!   the warnings to report again for modules that are not recompiled.
//!
//! The database lives in the package's build directory, so cleaning a package
//! removes its record with everything else. Any error reading it is treated
//! as "no previous build", which only costs a full rebuild; the writes are
//! not synced to disk for the same reason.

use super::packages::Package;
use rusqlite::{Connection, OpenFlags, params};
use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::time::{Duration, SystemTime, UNIX_EPOCH};

pub const DB_FILE: &str = "rescript.sqlite";

/// Bump when the schema changes; an older database is then discarded.
const SCHEMA_VERSION: i64 = 2;

const SCHEMA: &str = "
CREATE TABLE meta (key TEXT PRIMARY KEY, value TEXT NOT NULL) WITHOUT ROWID;
CREATE TABLE sources (path TEXT PRIMARY KEY, module TEXT NOT NULL) WITHOUT ROWID;
CREATE TABLE modules (
    module TEXT PRIMARY KEY,
    js_confirmed_at INTEGER,
    implementation_warnings TEXT,
    interface_warnings TEXT
) WITHOUT ROWID;
CREATE TABLE parse_warnings (source TEXT PRIMARY KEY, text TEXT NOT NULL) WITHOUT ROWID;
CREATE TABLE deps (source TEXT PRIMARY KEY, mtime INTEGER NOT NULL, deps TEXT NOT NULL) WITHOUT ROWID;
";

/// Files that earlier builds wrote instead of the database.
const LEGACY_BS_FILES: [&str; 3] = ["compiler-info.json", "build.ninja", ".sourcedirs.json"];
const LEGACY_OCAML_FILES: [&str; 2] = ["in-process-sources.txt", "in-process-warnings.json"];

pub fn path(package: &Package) -> PathBuf {
    package.get_build_path().join(DB_FILE)
}

/// A module's row: when its JavaScript was last confirmed up to date, and its
/// compile warnings.
#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct ModuleRow {
    pub js_confirmed_at: Option<SystemTime>,
    pub implementation_warnings: Option<String>,
    pub interface_warnings: Option<String>,
}

/// Everything recorded for one package.
#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct PackageState {
    pub meta: BTreeMap<String, String>,
    /// Source path (relative to the package) to module name.
    pub sources: BTreeMap<PathBuf, String>,
    pub modules: BTreeMap<String, ModuleRow>,
    /// Parse warnings by source file (`Module:impl` / `Module:intf`).
    pub parse_warnings: BTreeMap<String, String>,
    /// The raw module references of each source file (`Module:impl` /
    /// `Module:intf`), with the file's modification time when it was parsed.
    pub deps: BTreeMap<String, SourceDeps>,
}

/// A source file's module references, valid while its modification time is
/// unchanged.
#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct SourceDeps {
    pub mtime: i64,
    pub deps: Vec<String>,
}

pub const META_BUILD_STARTED_AT: &str = "build_started_at";
pub const META_BUILD_OK: &str = "build_ok";

fn open_existing(path: &Path) -> Option<Connection> {
    let conn = Connection::open_with_flags(
        path,
        OpenFlags::SQLITE_OPEN_READ_ONLY | OpenFlags::SQLITE_OPEN_NO_MUTEX,
    )
    .ok()?;
    let version: i64 = conn.query_row("PRAGMA user_version", [], |row| row.get(0)).ok()?;
    (version == SCHEMA_VERSION).then_some(conn)
}

fn open_for_write(package: &Package) -> rusqlite::Result<Connection> {
    let path = path(package);
    if let Some(parent) = path.parent() {
        let _ = std::fs::create_dir_all(parent);
    }
    let mut conn = Connection::open(&path)?;
    let version: i64 = conn.query_row("PRAGMA user_version", [], |row| row.get(0))?;
    if version != SCHEMA_VERSION {
        drop(conn);
        let _ = std::fs::remove_file(&path);
        conn = Connection::open(&path)?;
        conn.execute_batch(SCHEMA)?;
        conn.pragma_update(None, "user_version", SCHEMA_VERSION)?;
    }
    // A lost write only costs a rebuild, so don't wait for the disk.
    conn.pragma_update(None, "synchronous", "OFF")?;
    Ok(conn)
}

/// Remove the files earlier builds wrote instead of the database.
pub fn remove_legacy_files(package: &Package) {
    for file in LEGACY_BS_FILES {
        let _ = std::fs::remove_file(package.get_build_path().join(file));
    }
    for file in LEGACY_OCAML_FILES {
        let _ = std::fs::remove_file(package.get_ocaml_build_path().join(file));
    }
}

/// The package's metadata (compiler identity and build record), `None` when
/// there is no readable database.
pub fn read_meta(package: &Package) -> Option<BTreeMap<String, String>> {
    let conn = open_existing(&path(package))?;
    read_meta_from(&conn).ok()
}

fn read_meta_from(conn: &Connection) -> rusqlite::Result<BTreeMap<String, String>> {
    let mut stmt = conn.prepare("SELECT key, value FROM meta")?;
    let rows = stmt.query_map([], |row| Ok((row.get(0)?, row.get(1)?)))?;
    rows.collect()
}

/// Everything recorded for the package, `None` when there is no readable
/// database.
pub fn read(package: &Package) -> Option<PackageState> {
    let conn = open_existing(&path(package))?;
    let read = || -> rusqlite::Result<PackageState> {
        let meta = read_meta_from(&conn)?;
        let mut sources = BTreeMap::new();
        let mut stmt = conn.prepare("SELECT path, module FROM sources")?;
        for row in stmt.query_map([], |row| Ok((row.get::<_, String>(0)?, row.get::<_, String>(1)?)))? {
            let (path, module) = row?;
            sources.insert(PathBuf::from(path), module);
        }
        let mut modules = BTreeMap::new();
        let mut stmt = conn.prepare(
            "SELECT module, js_confirmed_at, implementation_warnings, interface_warnings FROM modules",
        )?;
        for row in stmt.query_map([], |row| {
            Ok((
                row.get::<_, String>(0)?,
                ModuleRow {
                    js_confirmed_at: row.get::<_, Option<i64>>(1)?.and_then(time_from_nanos),
                    implementation_warnings: row.get(2)?,
                    interface_warnings: row.get(3)?,
                },
            ))
        })? {
            let (module, row) = row?;
            modules.insert(module, row);
        }
        let mut parse_warnings = BTreeMap::new();
        let mut stmt = conn.prepare("SELECT source, text FROM parse_warnings")?;
        for row in stmt.query_map([], |row| Ok((row.get::<_, String>(0)?, row.get::<_, String>(1)?)))? {
            let (source, text) = row?;
            parse_warnings.insert(source, text);
        }
        let mut deps = BTreeMap::new();
        let mut stmt = conn.prepare("SELECT source, mtime, deps FROM deps")?;
        for row in stmt.query_map([], |row| {
            Ok((
                row.get::<_, String>(0)?,
                row.get::<_, i64>(1)?,
                row.get::<_, String>(2)?,
            ))
        })? {
            let (source, mtime, text) = row?;
            let deps_list = text
                .split('\n')
                .filter(|dep| !dep.is_empty())
                .map(str::to_string)
                .collect();
            deps.insert(
                source,
                SourceDeps {
                    mtime,
                    deps: deps_list,
                },
            );
        }
        Ok(PackageState {
            meta,
            sources,
            modules,
            parse_warnings,
            deps,
        })
    };
    read().ok()
}

/// Set the given metadata keys, writing only when something changed.
pub fn write_meta(package: &Package, entries: &[(&str, String)]) {
    let existing = read_meta(package).unwrap_or_default();
    if entries
        .iter()
        .all(|(key, value)| existing.get(*key) == Some(value))
    {
        return;
    }
    let write = || -> rusqlite::Result<()> {
        let mut conn = open_for_write(package)?;
        let tx = conn.transaction()?;
        {
            let mut stmt = tx.prepare("INSERT OR REPLACE INTO meta (key, value) VALUES (?1, ?2)")?;
            for (key, value) in entries {
                stmt.execute(params![key, value])?;
            }
        }
        tx.commit()
    };
    if let Err(err) = write() {
        log::error!("Could not record the build state of {}: {err}", package.name);
    }
}

/// Replace the package's build record with `new`, writing only the rows that
/// differ from `previous` (what was read at the start of the build). Metadata
/// keys not in `new` are kept.
pub fn write_record(package: &Package, previous: Option<&PackageState>, new: &PackageState) {
    let empty = PackageState::default();
    let previous = previous.unwrap_or(&empty);
    if previous.sources == new.sources
        && previous.modules == new.modules
        && previous.parse_warnings == new.parse_warnings
        && previous.deps == new.deps
        && new
            .meta
            .iter()
            .all(|(key, value)| previous.meta.get(key) == Some(value))
    {
        return;
    }
    let write = || -> rusqlite::Result<()> {
        let mut conn = open_for_write(package)?;
        let tx = conn.transaction()?;
        {
            let mut set_meta = tx.prepare("INSERT OR REPLACE INTO meta (key, value) VALUES (?1, ?2)")?;
            for (key, value) in &new.meta {
                if previous.meta.get(key) != Some(value) {
                    set_meta.execute(params![key, value])?;
                }
            }

            let mut delete_source = tx.prepare("DELETE FROM sources WHERE path = ?1")?;
            let mut set_source =
                tx.prepare("INSERT OR REPLACE INTO sources (path, module) VALUES (?1, ?2)")?;
            sync_rows(
                &previous.sources,
                &new.sources,
                |path| delete_source.execute(params![path.to_string_lossy()]).map(drop),
                |path, module| {
                    set_source
                        .execute(params![path.to_string_lossy(), module])
                        .map(drop)
                },
            )?;

            let mut delete_module = tx.prepare("DELETE FROM modules WHERE module = ?1")?;
            let mut set_module = tx.prepare(
                "INSERT OR REPLACE INTO modules
                 (module, js_confirmed_at, implementation_warnings, interface_warnings)
                 VALUES (?1, ?2, ?3, ?4)",
            )?;
            sync_rows(
                &previous.modules,
                &new.modules,
                |module| delete_module.execute(params![module]).map(drop),
                |module, row| {
                    set_module
                        .execute(params![
                            module,
                            row.js_confirmed_at.map(nanos_from_time),
                            row.implementation_warnings,
                            row.interface_warnings
                        ])
                        .map(drop)
                },
            )?;

            let mut delete_warning = tx.prepare("DELETE FROM parse_warnings WHERE source = ?1")?;
            let mut set_warning =
                tx.prepare("INSERT OR REPLACE INTO parse_warnings (source, text) VALUES (?1, ?2)")?;
            sync_rows(
                &previous.parse_warnings,
                &new.parse_warnings,
                |source| delete_warning.execute(params![source]).map(drop),
                |source, text| set_warning.execute(params![source, text]).map(drop),
            )?;

            let mut delete_deps = tx.prepare("DELETE FROM deps WHERE source = ?1")?;
            let mut set_deps =
                tx.prepare("INSERT OR REPLACE INTO deps (source, mtime, deps) VALUES (?1, ?2, ?3)")?;
            sync_rows(
                &previous.deps,
                &new.deps,
                |source| delete_deps.execute(params![source]).map(drop),
                |source, row| {
                    set_deps
                        .execute(params![source, row.mtime, row.deps.join("\n")])
                        .map(drop)
                },
            )?;
        }
        tx.commit()
    };
    if let Err(err) = write() {
        log::error!("Could not record the build state of {}: {err}", package.name);
        // A half-known record is worse than none.
        let _ = std::fs::remove_file(path(package));
    }
}

/// Delete the rows of `previous` missing from `new` and set the rows of
/// `new` that differ.
fn sync_rows<K: Ord, V: PartialEq>(
    previous: &BTreeMap<K, V>,
    new: &BTreeMap<K, V>,
    mut delete: impl FnMut(&K) -> rusqlite::Result<()>,
    mut set: impl FnMut(&K, &V) -> rusqlite::Result<()>,
) -> rusqlite::Result<()> {
    for key in previous.keys() {
        if !new.contains_key(key) {
            delete(key)?;
        }
    }
    for (key, value) in new {
        if previous.get(key) != Some(value) {
            set(key, value)?;
        }
    }
    Ok(())
}

pub fn nanos_from_time(time: SystemTime) -> i64 {
    time.duration_since(UNIX_EPOCH)
        .map(|since| since.as_nanos().min(i64::MAX as u128) as i64)
        .unwrap_or(0)
}

pub fn time_from_nanos(nanos: i64) -> Option<SystemTime> {
    u64::try_from(nanos)
        .ok()
        .and_then(|nanos| UNIX_EPOCH.checked_add(Duration::from_nanos(nanos)))
}

/// Recorded time metadata, e.g. [`META_BUILD_STARTED_AT`].
pub fn meta_time(meta: &BTreeMap<String, String>, key: &str) -> Option<SystemTime> {
    meta.get(key)?.parse().ok().and_then(time_from_nanos)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::build::packages::Namespace;
    use crate::config;
    use ahash::AHashSet;
    use tempfile::TempDir;

    fn test_package(root: &Path) -> Package {
        let config_path = root.join("rescript.json");
        std::fs::write(&config_path, r#"{"name":"pkg"}"#).unwrap();
        Package {
            name: "pkg".to_string(),
            config: config::tests::create_config(config::tests::CreateConfigArgs {
                name: "pkg".to_string(),
                bs_deps: vec![],
                build_dev_deps: vec![],
                allowed_dependents: None,
                path: config_path,
            }),
            source_folders: AHashSet::new(),
            source_files: None,
            namespace: Namespace::NoNamespace,
            modules: None,
            path: root.to_path_buf(),
            dirs: None,
            gentype_dirs: None,
            is_local_dep: true,
            is_root: true,
        }
    }

    fn state(js: u64, warning: Option<&str>) -> PackageState {
        let mut state = PackageState::default();
        state.meta.insert(META_BUILD_OK.to_string(), "1".to_string());
        state.sources.insert(PathBuf::from("src/A.res"), "A".to_string());
        state.sources.insert(PathBuf::from("src/A.resi"), "A".to_string());
        state.modules.insert(
            "A".to_string(),
            ModuleRow {
                js_confirmed_at: Some(UNIX_EPOCH + Duration::from_nanos(js)),
                implementation_warnings: warning.map(str::to_string),
                interface_warnings: None,
            },
        );
        state
    }

    #[test]
    fn a_missing_database_reads_as_no_record() {
        let dir = TempDir::new().unwrap();
        let package = test_package(dir.path());
        assert!(read(&package).is_none());
        assert!(read_meta(&package).is_none());
    }

    #[test]
    fn records_round_trip_and_update_by_difference() {
        let dir = TempDir::new().unwrap();
        let package = test_package(dir.path());
        let first = state(1_700_000_000_123_456_789, Some("warning"));
        write_record(&package, None, &first);
        assert_eq!(read(&package).as_ref(), Some(&first));

        let mut second = state(1_700_000_001_000_000_000, None);
        second.sources.remove(Path::new("src/A.resi"));
        second
            .parse_warnings
            .insert("A:impl".to_string(), "parse warning".to_string());
        second.deps.insert(
            "A:impl".to_string(),
            SourceDeps {
                mtime: 42,
                deps: vec!["B".to_string(), "C.D".to_string()],
            },
        );
        write_record(&package, Some(&first), &second);
        assert_eq!(read(&package).as_ref(), Some(&second));
    }

    #[test]
    fn meta_writes_keep_other_keys() {
        let dir = TempDir::new().unwrap();
        let package = test_package(dir.path());
        write_record(&package, None, &state(5, None));
        write_meta(&package, &[("bsc_hash", "abc".to_string())]);
        let meta = read_meta(&package).unwrap();
        assert_eq!(meta.get("bsc_hash").map(String::as_str), Some("abc"));
        assert_eq!(meta.get(META_BUILD_OK).map(String::as_str), Some("1"));
    }
}
