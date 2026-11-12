//! Per-package build state, in `lib/rescript/rescript.sqlite`.
//!
//! The only things a build keeps on disk besides its JavaScript and the
//! editor's `.compiler.log`:
//!
//! - the compiler identity and configuration hash the package was built with
//!   (see [`super::compiler_info`]): a mismatch cleans the package;
//! - the in-process build record read by [`super::incremental`]: when the
//!   last build started and whether it succeeded, every module's source
//!   paths, when each module's JavaScript was last confirmed up to date, and
//!   the warnings to report again for modules that are not recompiled;
//! - in the root package's database, the runtime's interfaces as the last
//!   build compiled them (see [`read_runtime_interfaces`]).
//!
//! The database lives in the package's artifact directory, so cleaning a
//! package removes its record with everything else. Any error reading it is treated
//! as "no previous build", which only costs a full rebuild; the writes are
//! not synced to disk for the same reason.

use super::packages::Package;
use ahash::AHashMap;
use rayon::prelude::*;
use rusqlite::{Connection, OpenFlags, params};
use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::time::{Duration, SystemTime, UNIX_EPOCH};

use rescript_compiler::timing::{self, Phase};

/// Scoped persistence subphase, disabled with the compiler's other timers.
pub(super) struct RecordTimer {
    phase: Phase,
    started: Option<std::time::Instant>,
}

impl RecordTimer {
    pub(super) fn start(phase: Phase) -> Self {
        Self { phase, started: timing::enabled().then(std::time::Instant::now) }
    }
}

impl Drop for RecordTimer {
    fn drop(&mut self) {
        if let Some(started) = self.started {
            timing::record(self.phase, started.elapsed());
        }
    }
}

pub const DB_FILE: &str = "rescript.sqlite";
const META_RECORD_COMPLETE: &str = "record_complete";

/// Bump when the schema changes; an older database is then discarded.
// 19: the database moved from lib/bs to lib/rescript, whose build records
// name no lib/bs or lib/ocaml artifacts.
// 20: PortableRawSignature carries its own file names.
// 21: interface fingerprints and item digests hash the type graph with its
// sharing (`cmi/graph_hash.rs`), no longer the tree it unfolds to: digests
// stored by the earlier algorithm must not be compared with new ones.
// 22: parsed genType flags and declaration-cache availability survive restart.
const SCHEMA_VERSION: i64 = 22;

const SCHEMA: &str = "
CREATE TABLE meta (key TEXT PRIMARY KEY, value TEXT NOT NULL) WITHOUT ROWID;
CREATE TABLE sources (path TEXT PRIMARY KEY, module TEXT NOT NULL) WITHOUT ROWID;
CREATE TABLE modules (
    module TEXT PRIMARY KEY,
    js_confirmed_at INTEGER,
    implementation_warnings TEXT,
    interface_warnings TEXT,
    interface_digest INTEGER,
    imports TEXT
) WITHOUT ROWID;
CREATE TABLE parse_warnings (source TEXT PRIMARY KEY, text TEXT NOT NULL) WITHOUT ROWID;
CREATE TABLE deps (source TEXT PRIMARY KEY, mtime INTEGER NOT NULL, deps TEXT NOT NULL, gentype_annotations INTEGER NOT NULL, gentype_declarations INTEGER NOT NULL) WITHOUT ROWID;
CREATE TABLE reads (module TEXT PRIMARY KEY, data TEXT NOT NULL);
CREATE TABLE items (module TEXT PRIMARY KEY, data TEXT NOT NULL);
CREATE TABLE interfaces (module TEXT PRIMARY KEY, hash INTEGER NOT NULL, data BLOB NOT NULL);
CREATE TABLE interface_extras (module TEXT PRIMARY KEY, data BLOB NOT NULL) WITHOUT ROWID;
CREATE TABLE runtime_interfaces (module TEXT PRIMARY KEY, data BLOB NOT NULL) WITHOUT ROWID;
";

pub fn path(package: &Package) -> PathBuf {
    package.get_build_path().join(DB_FILE)
}

/// A module's row: when its JavaScript was last confirmed up to date, its
/// compile warnings, and what that compile read and published.
#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct ModuleRow {
    pub js_confirmed_at: Option<SystemTime>,
    pub implementation_warnings: Option<String>,
    pub interface_warnings: Option<String>,
    /// The digest of what other modules can read of this one (see
    /// `ModuleRegistry::interface_digest`).
    pub interface_digest: Option<u64>,
    /// The project modules whose interface the compile read, with the
    /// digest each had then. `None` when unknown.
    pub imports: Option<Imports>,
}

/// A module's recorded imports (see [`ModuleRow::imports`]). Read from the
/// record as text and decoded on first use: most builds look at the imports
/// of few modules, and a large package records ~100k of them.
#[derive(Debug, Clone)]
pub struct Imports {
    text: Option<std::sync::Arc<str>>,
    list: std::sync::OnceLock<Vec<(String, u64)>>,
}

impl Imports {
    pub fn new(list: Vec<(String, u64)>) -> Self {
        Self {
            text: None,
            list: std::sync::OnceLock::from(list),
        }
    }

    pub(super) fn from_text(text: String) -> Self {
        Self {
            text: Some(text.into()),
            list: std::sync::OnceLock::new(),
        }
    }

    /// Each imported unit with the digest it had.
    pub fn list(&self) -> &[(String, u64)] {
        self.list.get_or_init(|| {
            let text = self.text.as_deref().unwrap_or_default();
            // The record writes this text; a row that does not decode reads
            // as no imports.
            decode_imports(text).unwrap_or_default()
        })
    }

    pub(super) fn encode(&self) -> std::borrow::Cow<'_, str> {
        match (&self.text, self.list.get()) {
            (Some(text), None) => std::borrow::Cow::Borrowed(text),
            _ => std::borrow::Cow::Owned(self
                .list()
                .iter()
                .map(|(module, digest)| format!("{module}={digest:x}"))
                .collect::<Vec<_>>()
                .join("\n")),
        }
    }
}

impl PartialEq for Imports {
    fn eq(&self, other: &Self) -> bool {
        match (&self.text, &other.text) {
            (Some(a), Some(b)) if self.list.get().is_none() && other.list.get().is_none() => a == b,
            _ => self.list() == other.list(),
        }
    }
}

impl Eq for Imports {}

fn decode_imports(text: &str) -> Option<Vec<(String, u64)>> {
    text.split('\n')
        .filter(|line| !line.is_empty())
        .map(|line| {
            let (module, digest) = line.rsplit_once('=')?;
            Some((module.to_string(), u64::from_str_radix(digest, 16).ok()?))
        })
        .collect()
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
    /// Rows to set in the `reads` and `items` tables (see [`UnitReads`] and
    /// [`ItemDigests`]). These are only written, never read with the rest
    /// of the record: a build looks up the few it needs with
    /// [`read_reads`] and [`read_items`].
    pub reads_updates: BTreeMap<String, UnitReads>,
    pub items_updates: BTreeMap<String, ItemDigests>,
    /// The content hash of every module's stored interface (read with the
    /// record; the interfaces themselves with [`read_interfaces`]).
    pub stored_interfaces: BTreeMap<String, u64>,
    /// Stored interfaces to set: module to the content hash and the encoded
    /// interface's extras (`None` for none) and core
    /// (`rescript_compiler::cmi::stored_module::encode_parts`).
    pub interface_updates: BTreeMap<String, StoredInterface>,
    /// Whether `sources`, `modules` and `deps` hold only the rows to set:
    /// every recorded row missing from them is kept (see
    /// `incremental::current_record`).
    pub partial: bool,
    /// Fresh-build rows encoded by the preparation worker.
    pub encoded_reads: BTreeMap<String, String>,
    pub encoded_items: BTreeMap<String, String>,
    pub encoded_deps: BTreeMap<String, String>,
}

/// A stored interface to write: its content hash, encoded extras (`None` for
/// none) and encoded core.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StoredInterface {
    pub hash: u64,
    pub extras: Option<Vec<u8>>,
    pub core: Vec<u8>,
}

impl StoredInterface {
    /// The interface encoded as `extras` (`None` for none) and `core`, with
    /// its content hash.
    pub fn new(extras: Option<Vec<u8>>, core: Vec<u8>) -> Self {
        let mut hasher = blake3::Hasher::new();
        hasher.update(&core);
        if let Some(extras) = &extras {
            hasher.update(extras);
        }
        let hash = hasher.finalize();
        let hash = u64::from_le_bytes(hash.as_bytes()[..8].try_into().expect("8 bytes"));
        Self { hash, extras, core }
    }
}

/// What a module's compile read of each unit: the digest of the items read
/// when it was compiled, and their keys.
pub type UnitReads = BTreeMap<String, (u64, Vec<String>)>;

/// A module's item digests, by item key.
pub type ItemDigests = BTreeMap<String, u64>;

pub(super) fn encode_reads(reads: &UnitReads) -> String {
    reads
        .iter()
        .map(|(unit, (digest, keys))| format!("{unit}\t{digest:x}\t{}", keys.join(",")))
        .collect::<Vec<_>>()
        .join("\n")
}

fn decode_reads(text: &str) -> Option<UnitReads> {
    text.split('\n')
        .filter(|line| !line.is_empty())
        .map(|line| {
            let mut parts = line.splitn(3, '\t');
            let unit = parts.next()?.to_string();
            let digest = u64::from_str_radix(parts.next()?, 16).ok()?;
            let keys = parts
                .next()?
                .split(',')
                .filter(|key| !key.is_empty())
                .map(str::to_string)
                .collect();
            Some((unit, (digest, keys)))
        })
        .collect()
}

pub(super) fn encode_items(items: &ItemDigests) -> String {
    items
        .iter()
        .map(|(key, digest)| format!("{key}\t{digest:x}"))
        .collect::<Vec<_>>()
        .join("\n")
}

fn decode_items(text: &str) -> Option<ItemDigests> {
    text.split('\n')
        .filter(|line| !line.is_empty())
        .map(|line| {
            let (key, digest) = line.split_once('\t')?;
            Some((key.to_string(), u64::from_str_radix(digest, 16).ok()?))
        })
        .collect()
}

/// The `data` column of `table` for each of `modules` that has a row, in
/// `modules` order.
fn read_data_rows<T, C>(package: &Package, table: &str, modules: &[&str]) -> C
where
    T: rusqlite::types::FromSql,
    C: FromIterator<(String, T)>,
{
    let Some(conn) = open_existing(&path(package)) else {
        return std::iter::empty().collect();
    };
    let Ok(mut stmt) = conn.prepare(&format!("SELECT data FROM {table} WHERE module = ?1")) else {
        return std::iter::empty().collect();
    };
    modules
        .iter()
        .filter_map(|module| {
            let data: T = stmt.query_row(params![module], |row| row.get(0)).ok()?;
            Some((module.to_string(), data))
        })
        .collect()
}

/// The recorded reads of the given modules of the package.
pub fn read_reads(package: &Package, modules: &[&str]) -> BTreeMap<String, UnitReads> {
    read_data_rows::<String, BTreeMap<_, _>>(package, "reads", modules)
        .into_iter()
        .filter_map(|(module, data)| Some((module, decode_reads(&data)?)))
        .collect()
}

/// The encoded extras of the given modules' stored interfaces, for those
/// that have any.
pub fn read_interface_extras(package: &Package, modules: &[&str]) -> AHashMap<String, Vec<u8>> {
    // One scan of the table is cheaper than a lookup per module when most
    // rows are wanted, as for a build loading a large dependency closure.
    let Some(conn) = open_existing(&path(package)) else {
        return AHashMap::new();
    };
    let wanted: ahash::AHashSet<&str> = modules.iter().copied().collect();
    let Ok(mut stmt) = conn.prepare("SELECT module, data FROM interface_extras") else {
        return AHashMap::new();
    };
    let Ok(mut rows) = stmt.query([]) else {
        return AHashMap::new();
    };
    let mut found = AHashMap::new();
    while let Ok(Some(row)) = rows.next() {
        let Ok(module) = row.get_ref(0).and_then(|value| Ok(value.as_str()?.to_string())) else {
            continue;
        };
        if wanted.contains(module.as_str())
            && let Ok(data) = row.get::<_, Vec<u8>>(1)
        {
            found.insert(module, data);
        }
    }
    found
}

/// Reads the cores of a package's stored interfaces one at a time, on
/// demand, from one connection opened on first use: a build reads only the
/// ones its compiles look up (see `ModuleRegistry::register_stored_parts`).
pub struct InterfaceCores {
    path: PathBuf,
    conn: std::sync::Mutex<Option<Connection>>,
}

impl InterfaceCores {
    pub fn new(package: &Package) -> Self {
        Self {
            path: path(package),
            conn: std::sync::Mutex::new(None),
        }
    }

    /// The core of `module`'s stored interface, `None` when there is none.
    pub fn read(&self, module: &str) -> Option<Vec<u8>> {
        let mut conn = self.conn.lock().unwrap();
        if conn.is_none() {
            *conn = Some(open_existing(&self.path)?);
        }
        let conn = conn.as_ref()?;
        let mut stmt = conn
            .prepare_cached("SELECT data FROM interfaces WHERE module = ?1")
            .ok()?;
        stmt.query_row(params![module], |row| row.get(0)).ok()
    }
}

/// The recorded item digests of the given modules of the package.
pub fn read_items(package: &Package, modules: &[&str]) -> BTreeMap<String, ItemDigests> {
    read_data_rows::<String, BTreeMap<_, _>>(package, "items", modules)
        .into_iter()
        .filter_map(|(module, data)| Some((module, decode_items(&data)?)))
        .collect()
}

/// A source file's module references, valid while its modification time is
/// unchanged.
#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct SourceDeps {
    pub mtime: i64,
    pub deps: Vec<String>,
    pub gentype_annotations: bool,
    pub gentype_declarations: bool,
}

pub const META_BUILD_STARTED_AT: &str = "build_started_at";
pub const META_BUILD_OK: &str = "build_ok";
/// The files the package's sources compile to under the configuration of
/// the build that recorded it, relative to the package, one per line (see
/// `incremental::expected_outputs`).
pub const META_OUTPUTS: &str = "outputs";

/// Run SQLite's process-wide initialization once, before any connection is
/// opened. Opening the per-package databases from several worker threads at
/// once could otherwise race inside `sqlite3_initialize` and crash (a null
/// mutex in `sqlite3_mutex_alloc`).
fn ensure_sqlite_initialized() {
    static INIT: std::sync::Once = std::sync::Once::new();
    INIT.call_once(|| {
        let _ = Connection::open_in_memory();
    });
}

fn pending_path(path: &Path) -> PathBuf {
    path.with_extension("sqlite.pending")
}

fn open_existing(path: &Path) -> Option<Connection> {
    // With a memory journal, the database alone cannot prove that a writer
    // finished. Check the external marker before even reading the schema.
    if pending_path(path).try_exists().unwrap_or(true) {
        return None;
    }
    ensure_sqlite_initialized();
    let conn = Connection::open_with_flags(
        path,
        OpenFlags::SQLITE_OPEN_READ_ONLY | OpenFlags::SQLITE_OPEN_NO_MUTEX,
    )
    .ok()?;
    let version: i64 = conn.query_row("PRAGMA user_version", [], |row| row.get(0)).ok()?;
    (version == SCHEMA_VERSION).then_some(conn)
}

fn lock_writer(path: &Path) -> std::io::Result<std::fs::File> {
    lock_database(path, true)
}

fn lock_database(path: &Path, exclusive: bool) -> std::io::Result<std::fs::File> {
    if let Some(parent) = path.parent() {
        std::fs::create_dir_all(parent)?;
    }
    let file = std::fs::OpenOptions::new()
        .read(true).write(true).create(true).truncate(false)
        .open(path.with_extension("sqlite.guard"))?;
    if exclusive {
        fs2::FileExt::lock_exclusive(&file)?;
    } else {
        fs2::FileExt::lock_shared(&file)?;
    }
    Ok(file)
}

// Called only while holding the writer lock. A pending marker then belongs
// to an interrupted writer, rather than another root sharing this dependency.
fn discard_incomplete(path: &Path) -> std::io::Result<bool> {
    if !pending_path(path).try_exists()? {
        return Ok(false);
    }
    let mut journal = path.as_os_str().to_owned();
    journal.push("-journal");
    for file in [path.to_path_buf(), PathBuf::from(journal)] {
        match std::fs::remove_file(file) {
            Ok(()) => (),
            Err(err) if err.kind() == std::io::ErrorKind::NotFound => (),
            Err(err) => return Err(err),
        }
    }
    Ok(true)
}

// Keep the guard alive until after the connection closes.
fn open_for_write(package: &Package) -> anyhow::Result<(std::fs::File, Connection)> {
    open_path_for_write(&path(package))
}

fn open_path_for_write(path: &Path) -> anyhow::Result<(std::fs::File, Connection)> {
    let guard = lock_writer(path)?;
    let discarded = discard_incomplete(path)?;
    let conn = open_path_for_write_with_journal(path, None)?;
    if discarded {
        // The replacement schema contains no completed build record. Runtime
        // or metadata writes can now commit normally with a disk journal;
        // the later build-record write must preserve these new runtime rows.
        std::fs::remove_file(pending_path(path))?;
    }
    Ok((guard, conn))
}

fn open_path_for_write_with_journal(path: &Path, journal: Option<&str>) -> rusqlite::Result<Connection> {
    ensure_sqlite_initialized();
    if let Some(parent) = path.parent() {
        let _ = std::fs::create_dir_all(parent);
    }
    let existed = path.exists();
    let open = || -> rusqlite::Result<Connection> {
        let conn = Connection::open(path)?;
        // Schema creation is a cache write too. Apply this before its commit,
        // not afterwards (which left fresh databases using synchronous=FULL).
        conn.pragma_update(None, "synchronous", "OFF")?;
        if let Some(journal) = journal {
            conn.pragma_update(None, "journal_mode", journal)?;
        }
        Ok(conn)
    };
    let mut conn = open()?;
    let version: i64 = conn.query_row("PRAGMA user_version", [], |row| row.get(0))?;
    if version != SCHEMA_VERSION {
        if existed {
            drop(conn);
            let _ = std::fs::remove_file(path);
            conn = open()?;
        }
        conn.pragma_update(None, "page_size", 16384)?;
        conn.execute_batch(&format!(
            "BEGIN;\n{SCHEMA}\nPRAGMA user_version = {SCHEMA_VERSION};\nCOMMIT;"
        ))?;
    }
    // A record write is one transaction of up to tens of MB; with SQLite's
    // default 2 MB page cache, dirty pages spill to the file mid-transaction
    // and are written again on commit.
    conn.pragma_update(None, "cache_size", -262_144)?;
    Ok(conn)
}

/// The package's metadata (compiler identity and build record), `None` when
/// there is no readable database.
pub fn read_meta(package: &Package) -> Option<BTreeMap<String, String>> {
    let conn = open_existing(&path(package))?;
    read_meta_from(&conn).ok()
}

fn read_meta_from(conn: &Connection) -> rusqlite::Result<BTreeMap<String, String>> {
    let mut stmt = conn.prepare("SELECT key, value FROM meta WHERE key != 'record_complete'")?;
    let rows = stmt.query_map([], |row| Ok((row.get(0)?, row.get(1)?)))?;
    rows.collect()
}

/// Everything recorded for the package, `None` when there is no readable
/// database.
pub fn read(package: &Package) -> Option<PackageState> {
    let db = path(package);
    if !db.try_exists().ok()? { return None; }
    // Several connections below open by path. Pin the published generation
    // across all those opens/reads, excluding replacement and in-place writers.
    let _guard = lock_database(&db, false).ok()?;
    let conn = open_existing(&db)?;
    // Check before reading any build rows. open_existing already rejected an
    // external incomplete marker, including a kill during the SQLite commit.
    let complete: String = conn.query_row(
        "SELECT value FROM meta WHERE key = ?1", [META_RECORD_COMPLETE], |row| row.get(0),
    ).ok()?;
    if complete != "1" {
        return None;
    }
    let db = db.as_path();
    // The large tables are read on their own connections in parallel: a big
    // package's record is thousands of rows in each.
    let ((meta_sources_warnings, modules), (deps, stored_interfaces)) = rayon::join(
        || {
            rayon::join(
                move || -> rusqlite::Result<_> {
                    Ok((
                        read_meta_from(&conn)?,
                        read_sources(&conn)?,
                        read_parse_warnings(&conn)?,
                    ))
                },
                || on_own_connection(db, read_modules),
            )
        },
        || {
            rayon::join(
                || on_own_connection(db, read_deps),
                || on_own_connection(db, read_stored_interface_hashes),
            )
        },
    );
    let (meta, sources, parse_warnings) = meta_sources_warnings.ok()?;
    Some(PackageState {
        meta,
        sources,
        modules: modules.ok()?,
        parse_warnings,
        deps: deps.ok()?,
        stored_interfaces: stored_interfaces.ok()?,
        ..PackageState::default()
    })
}

fn on_own_connection<T>(
    db: &Path,
    read: impl FnOnce(&Connection) -> rusqlite::Result<T>,
) -> rusqlite::Result<T> {
    let conn = open_existing(db).ok_or(rusqlite::Error::InvalidQuery)?;
    read(&conn)
}

fn read_sources(conn: &Connection) -> rusqlite::Result<BTreeMap<PathBuf, String>> {
    let mut sources = BTreeMap::new();
    let mut stmt = conn.prepare("SELECT path, module FROM sources")?;
    for row in stmt.query_map([], |row| Ok((row.get::<_, String>(0)?, row.get::<_, String>(1)?)))? {
        let (path, module) = row?;
        sources.insert(PathBuf::from(path), module);
    }
    Ok(sources)
}

fn read_modules(conn: &Connection) -> rusqlite::Result<BTreeMap<String, ModuleRow>> {
    let mut modules = BTreeMap::new();
    let mut stmt = conn.prepare(
        "SELECT module, js_confirmed_at, implementation_warnings, interface_warnings,
                interface_digest, imports FROM modules",
    )?;
    for row in stmt.query_map([], |row| {
        Ok((
            row.get::<_, String>(0)?,
            ModuleRow {
                js_confirmed_at: row.get::<_, Option<i64>>(1)?.and_then(time_from_nanos),
                implementation_warnings: row.get(2)?,
                interface_warnings: row.get(3)?,
                interface_digest: row.get::<_, Option<i64>>(4)?.map(|digest| digest as u64),
                imports: row.get::<_, Option<String>>(5)?.map(Imports::from_text),
            },
        ))
    })? {
        let (module, row) = row?;
        modules.insert(module, row);
    }
    Ok(modules)
}

fn read_parse_warnings(conn: &Connection) -> rusqlite::Result<BTreeMap<String, String>> {
    let mut parse_warnings = BTreeMap::new();
    let mut stmt = conn.prepare("SELECT source, text FROM parse_warnings")?;
    for row in stmt.query_map([], |row| Ok((row.get::<_, String>(0)?, row.get::<_, String>(1)?)))? {
        let (source, text) = row?;
        parse_warnings.insert(source, text);
    }
    Ok(parse_warnings)
}

fn read_deps(conn: &Connection) -> rusqlite::Result<BTreeMap<String, SourceDeps>> {
    let mut deps = BTreeMap::new();
    let mut stmt = conn.prepare(
        "SELECT source, mtime, deps, gentype_annotations, gentype_declarations FROM deps",
    )?;
    for row in stmt.query_map([], |row| {
        Ok((
            row.get::<_, String>(0)?,
            row.get::<_, i64>(1)?,
            row.get::<_, String>(2)?,
            row.get::<_, bool>(3)?,
            row.get::<_, bool>(4)?,
        ))
    })? {
        let (source, mtime, text, gentype_annotations, gentype_declarations) = row?;
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
                gentype_annotations,
                gentype_declarations,
            },
        );
    }
    Ok(deps)
}

fn read_stored_interface_hashes(conn: &Connection) -> rusqlite::Result<BTreeMap<String, u64>> {
    let mut stored_interfaces = BTreeMap::new();
    let mut stmt = conn.prepare("SELECT module, hash FROM interfaces")?;
    for row in stmt.query_map([], |row| Ok((row.get::<_, String>(0)?, row.get::<_, i64>(1)?)))? {
        let (module, digest) = row?;
        stored_interfaces.insert(module, digest as u64);
    }
    Ok(stored_interfaces)
}

/// The metadata key of the runtime interfaces' key (see
/// [`read_runtime_interfaces`]).
pub(super) const META_RUNTIME_KEY: &str = "runtime_key";

/// The runtime's interfaces stored in the database at `db` (the root
/// package's), by module, when they were stored under `key`: a digest of the
/// runtime's sources and of the compiler, so they stand in for compiling the
/// runtime. `None` when there are none for `key`.
pub fn read_runtime_interfaces(db: &Path, key: &str) -> Option<Vec<(String, Vec<u8>)>> {
    let conn = open_existing(db)?;
    let stored: String = conn
        .query_row(
            "SELECT value FROM meta WHERE key = ?1",
            params![META_RUNTIME_KEY],
            |row| row.get(0),
        )
        .ok()?;
    if stored != key {
        return None;
    }
    let mut stmt = conn.prepare("SELECT module, data FROM runtime_interfaces").ok()?;
    let rows = stmt
        .query_map([], |row| Ok((row.get(0)?, row.get(1)?)))
        .ok()?
        .collect::<rusqlite::Result<Vec<_>>>()
        .ok()?;
    (!rows.is_empty()).then_some(rows)
}

/// Replace the runtime interfaces stored in the database at `db` with
/// `interfaces`, under `key` (see [`read_runtime_interfaces`]). A failure
/// only costs compiling the runtime again, so it is not reported.
pub fn write_runtime_interfaces(db: &Path, key: &str, interfaces: &[(String, Vec<u8>)]) {
    let write = || -> anyhow::Result<()> {
        let (_guard, mut conn) = open_path_for_write(db)?;
        conn.busy_timeout(Duration::from_secs(1))?;
        let tx = conn.transaction()?;
        tx.execute("DELETE FROM runtime_interfaces", [])?;
        {
            let mut insert = tx.prepare("INSERT INTO runtime_interfaces (module, data) VALUES (?1, ?2)")?;
            for (module, data) in interfaces {
                insert.execute(params![module, data])?;
            }
        }
        tx.execute(
            "INSERT OR REPLACE INTO meta (key, value) VALUES (?1, ?2)",
            params![META_RUNTIME_KEY, key],
        )?;
        tx.commit()?;
        Ok(())
    };
    if let Err(err) = write() {
        log::debug!(
            "Could not store the runtime interfaces in {}: {err}",
            db.display()
        );
    }
}

/// Set the given metadata keys, writing only when something changed.
pub fn write_meta(package: &Package, entries: &[(&str, String)]) {
    write_meta_over(package, None, entries)
}

/// [`write_meta`], given the package's current metadata when the caller
/// already read it.
pub fn write_meta_over(
    package: &Package,
    existing: Option<&BTreeMap<String, String>>,
    entries: &[(&str, String)],
) {
    let read;
    let existing = match existing {
        Some(existing) => existing,
        None => {
            read = read_meta(package).unwrap_or_default();
            &read
        }
    };
    if entries
        .iter()
        .all(|(key, value)| existing.get(*key) == Some(value))
    {
        return;
    }
    let write = || -> anyhow::Result<()> {
        let (_guard, mut conn) = open_for_write(package)?;
        let tx = conn.transaction()?;
        {
            let mut stmt = tx.prepare("INSERT OR REPLACE INTO meta (key, value) VALUES (?1, ?2)")?;
            for (key, value) in entries {
                stmt.execute(params![key, value])?;
            }
        }
        tx.commit()?;
        Ok(())
    };
    if let Err(err) = write() {
        log::warn!("Could not record the build state of {}: {err}", package.name);
    }
}

/// Replace the package's build record with `new`, writing only the rows that
/// differ from `previous` (what was read at the start of the build). Metadata
/// keys not in `new` are kept.
pub fn write_record(package: &Package, previous: Option<&PackageState>, new: &PackageState) {
    let empty = PackageState::default();
    let previous = previous.unwrap_or(&empty);
    let partial = new.partial;
    let rows_unchanged = if partial {
        new.sources.is_empty() && new.modules.is_empty() && new.deps.is_empty()
    } else {
        previous.sources == new.sources && previous.modules == new.modules && previous.deps == new.deps
    };
    // A partial record of a build that changed nothing keeps the recorded
    // build start: it still precedes every input (see
    // `incremental::everything_up_to_date`), so a no-op build writes nothing.
    if rows_unchanged
        && previous.parse_warnings == new.parse_warnings
        && new.reads_updates.is_empty()
        && new.items_updates.is_empty()
        && new.interface_updates.is_empty()
        && new.encoded_reads.is_empty()
        && new.encoded_items.is_empty()
        && new.meta.iter().all(|(key, value)| {
            previous.meta.get(key) == Some(value) || (partial && key == META_BUILD_STARTED_AT)
        })
    {
        return;
    }
    if !partial {
        let write = || -> anyhow::Result<()> {
            let record = MemoryRecord::from_previous(package, previous)?;
            apply_record_rows(&record.conn, previous, new, "")?;
            record.publish(package)
        };
        if let Err(err) = write() {
            // An unpublished image cannot damage the old complete record.
            log::warn!("Could not replace the build state of {}: {err}", package.name);
        }
        return;
    }
    let db = path(package);
    let pending = pending_path(&db);
    // Two roots can share a dependency database. A pending marker is stale
    // only after its writer has released this per-database lock (also on kill).
    let _guard = match lock_writer(&db) {
        Ok(guard) => guard,
        Err(err) => {
            log::warn!("Could not lock the build state of {}: {err}", package.name);
            return;
        }
    };
    let write = || -> anyhow::Result<()> {
        discard_incomplete(&db)?;
        std::fs::write(&pending, b"incomplete")?;
        let mut conn = timing::measure(Phase::RecordSqlOpen, ||
            open_path_for_write_with_journal(&db, Some("MEMORY")))?;
        let tx = conn.transaction()?;
        timing::measure(Phase::RecordSqlMeta, || tx.execute(
            "INSERT OR REPLACE INTO meta (key, value) VALUES (?1, '0')",
            [META_RECORD_COMPLETE],
        ))?;
        apply_record_rows(&tx, previous, new, &package.name)?;
        #[cfg(debug_assertions)]
        if std::env::var("RESCRIPT_TEST_ABORT_RECORD_WRITE").ok().as_deref() == Some(&package.name) {
            std::process::abort();
        }
        // Keep the in-database completion row too. The external marker protects
        // the commit itself, which a memory journal cannot recover after a kill.
        tx.execute(
            "INSERT OR REPLACE INTO meta (key, value) VALUES (?1, '1')",
            [META_RECORD_COMPLETE],
        )?;
        #[cfg(debug_assertions)]
        if std::env::var("RESCRIPT_TEST_ABORT_AFTER_RECORD_MARKER").ok().as_deref() == Some(&package.name) {
            tx.cache_flush()?;
            std::process::abort();
        }
        timing::measure(Phase::RecordSqlCommit, || tx.commit())?;
        // This is the trust boundary, after all SQLite pages have been written.
        // No fsync: loss of this cache is allowed; process-crash reuse is not.
        std::fs::remove_file(&pending)?;
        Ok(())
    };
    if let Err(err) = write() {
        log::warn!("Could not record the build state of {}: {err}", package.name);
        // A half-known record is worse than none.
        let _ = std::fs::remove_file(path(package));
    }
}

/// An unpublished whole record. Its transaction and pages never touch disk.
/// Batches are inserted on the preparation thread; publication owns the
/// connection and may run concurrently with other packages' publication.
pub(super) struct MemoryRecord {
    conn: Connection,
}

impl MemoryRecord {
    pub(super) fn new(seed: &PackageState, runtime: &[(String, Vec<u8>)]) -> anyhow::Result<Self> {
        let conn = timing::measure(Phase::RecordSqlOpen, || -> rusqlite::Result<Connection> {
            ensure_sqlite_initialized();
            // A private memdb VFS keeps its image contiguous. serialize() can
            // borrow it (SQLITE_SERIALIZE_NOCOPY) instead of allocating a
            // second database-sized buffer. No leading slash: not shared.
            let conn = Connection::open_with_flags("file:rescript?vfs=memdb",
                OpenFlags::SQLITE_OPEN_READ_WRITE | OpenFlags::SQLITE_OPEN_CREATE | OpenFlags::SQLITE_OPEN_URI)?;
            conn.set_prepared_statement_cache_capacity(32);
            conn.pragma_update(None, "page_size", 16384)?;
            conn.pragma_update(None, "synchronous", "OFF")?;
            conn.execute_batch(&format!("{SCHEMA}\nPRAGMA user_version = {SCHEMA_VERSION};\nBEGIN;"))?;
            Ok(conn)
        })?;
        apply_record_rows(&conn, &PackageState::default(), seed, "")?;
        {
            let mut insert = conn.prepare_cached("INSERT INTO runtime_interfaces (module, data) VALUES (?1, ?2)")?;
            for (name, data) in runtime {
                insert.execute(params![name, data])?;
            }
        }
        Ok(Self { conn })
    }

    fn from_previous(package: &Package, previous: &PackageState) -> anyhow::Result<Self> {
        if !previous.modules.is_empty() {
            if let Some(old) = open_existing(&path(package)) {
                // Whole-record fallback can keep unchanged interfaces that
                // are intentionally absent from interface_updates. Copy their
                // pages into memory, never update the live database in place.
                let mut record = Self::new(&PackageState::default(), &[])?;
                record.conn.execute_batch("ROLLBACK")?;
                let backup = rusqlite::backup::Backup::new(&old, &mut record.conn)?;
                anyhow::ensure!(backup.step(-1)? == rusqlite::backup::StepResult::Done, "database snapshot busy");
                drop(backup);
                record.conn.execute_batch("BEGIN")?;
                return Ok(record);
            }
        }
        let meta = read_meta(package).unwrap_or_default();
        let runtime = meta.get(META_RUNTIME_KEY)
            .and_then(|key| read_runtime_interfaces(&path(package), key)).unwrap_or_default();
        Self::new(&PackageState { meta, ..PackageState::default() }, &runtime)
    }

    pub(super) fn insert(&self, rows: &PackageState) -> anyhow::Result<()> {
        debug_assert!(rows.partial);
        apply_record_rows(&self.conn, &PackageState::default(), rows, "")
    }

    pub(super) fn publish(self, package: &Package) -> anyhow::Result<()> {
        use std::io::Write;
        publication_test_hook(package, "before-commit");
        self.conn.execute("INSERT OR REPLACE INTO meta (key, value) VALUES (?1, '1')", [META_RECORD_COMPLETE])?;
        timing::measure(Phase::RecordSqlCommit, || self.conn.execute_batch("COMMIT"))?;
        publication_test_hook(package, "after-commit");
        let image = timing::measure(Phase::RecordSerialize, || self.conn.serialize(rusqlite::DatabaseName::Main))?;
        publication_test_hook(package, "after-serialize");
        let db = path(package);
        std::fs::create_dir_all(package.get_build_path())?;
        let mut temp = tempfile::NamedTempFile::new_in(package.get_build_path())?;
        timing::measure(Phase::RecordImageWrite, || temp.write_all(&image))?;
        drop(image);
        drop(self);
        publication_test_hook(package, "after-write");
        let _guard = timing::measure(Phase::RecordPublishLock, || lock_writer(&db))?;
        publication_test_hook(package, "after-lock");
        timing::measure(Phase::RecordRecover, || recover_before_replace(&db))?;
        publication_test_hook(package, "before-rename");
        timing::measure(Phase::RecordRename, || temp.persist(&db))?;
        publication_test_hook(package, "after-rename");
        // Compatibility with a killed writer using the incremental path's
        // external marker. This path never creates a marker of its own.
        match std::fs::remove_file(pending_path(&db)) {
            Ok(()) => (),
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => (),
            Err(e) => return Err(e.into()),
        }
        Ok(())
    }
}

fn publication_test_hook(_package: &Package, _phase: &str) {
    #[cfg(debug_assertions)]
    if std::env::var("RESCRIPT_TEST_ABORT_PUBLICATION").ok().as_deref()
        == Some(&format!("{}:{_phase}", _package.name)) {
        std::process::abort();
    }
}

/// The caller holds the same writer guard as every in-place writer. Side files
/// therefore belong to dead writers, not live transactions. Recover against the
/// OLD inode: replaying its journal after rename would overwrite the new image.
fn recover_before_replace(db: &Path) -> anyhow::Result<()> {
    let side = |suffix: &str| {
        let mut path = db.as_os_str().to_owned();
        path.push(suffix);
        PathBuf::from(path)
    };
    let journal = side("-journal");
    let wal = side("-wal");
    let has_journal = journal.try_exists()?;
    let has_wal = wal.try_exists()?;
    if has_journal || has_wal {
        let conn = Connection::open_with_flags(db, OpenFlags::SQLITE_OPEN_READ_WRITE)?;
        conn.busy_timeout(Duration::from_secs(1))?;
        // Opening alone is lazy; reading the schema forces hot-journal recovery.
        conn.query_row("SELECT count(*) FROM sqlite_schema", [], |row| row.get::<_, i64>(0))?;
        if has_wal {
            conn.execute_batch("PRAGMA wal_checkpoint(TRUNCATE);")?;
        }
        conn.close().map_err(|(_, err)| err)?;
        // A reader can keep a WAL alive. Do not replace underneath that reader
        // or delete SQLite's side files by hand; leave the old database intact.
        anyhow::ensure!(!journal.try_exists()? && !wal.try_exists()?, "SQLite side files remain after recovery");
    }
    Ok(())
}

// Apply a batch inside the caller's transaction. Streaming batches are partial;
// the file-backed incremental path also uses deletions against its prior record.
fn apply_record_rows(
    tx: &Connection, previous: &PackageState, new: &PackageState, package_name: &str,
) -> anyhow::Result<()> {
    let partial = new.partial;
    // Encode the rows to set up front, in parallel: the transaction below
    // runs on one thread, and a large package sets ~100k rows.
    let reads: Vec<(&String, String)> = timing::measure(Phase::RecordReadsEncode, || new
        .reads_updates
        .par_iter()
        .map(|(module, reads)| (module, encode_reads(reads)))
        .collect());
    let items: Vec<(&String, String)> = timing::measure(Phase::RecordItemsEncode, || new
        .items_updates
        .par_iter()
        .map(|(module, items)| (module, encode_items(items)))
        .collect());
    let module_rows = timing::measure(Phase::RecordImportsEncode, || changed_rows(&previous.modules, &new.modules, |row| {
        row.imports.as_ref().map(Imports::encode)
    }));
    let deps_rows = timing::measure(Phase::RecordDepsEncode, || new.deps.par_iter()
        .filter(|(key, row)| previous.deps.get(*key) != Some(*row))
        .map(|(key, row)| {
            let encoded = match new.encoded_deps.get(key) {
                Some(text) => std::borrow::Cow::Borrowed(text.as_str()),
                None => std::borrow::Cow::Owned(row.deps.join("\n")),
            };
            (key, row, encoded)
        }).collect::<Vec<_>>());
        {
            let table_timer = RecordTimer::start(Phase::RecordSqlMeta);
            let mut set_meta = tx.prepare_cached("INSERT OR REPLACE INTO meta (key, value) VALUES (?1, ?2)")?;
            for (key, value) in &new.meta {
                if previous.meta.get(key) != Some(value) {
                    set_meta.execute(params![key, value])?;
                }
            }

            drop(table_timer);
            let table_timer = RecordTimer::start(Phase::RecordSqlSources);
            let mut delete_source = tx.prepare_cached("DELETE FROM sources WHERE path = ?1")?;
            let mut set_source =
                tx.prepare_cached("INSERT OR REPLACE INTO sources (path, module) VALUES (?1, ?2)")?;
            sync_rows(
                &previous.sources,
                &new.sources,
                partial,
                |path| delete_source.execute(params![path.to_string_lossy()]).map(drop),
                |path, module| {
                    set_source
                        .execute(params![path.to_string_lossy(), module])
                        .map(drop)
                },
            )?;

            drop(table_timer);
            let table_timer = RecordTimer::start(Phase::RecordSqlReads);
            let mut set_reads = tx.prepare_cached("INSERT OR REPLACE INTO reads (module, data) VALUES (?1, ?2)")?;
            for (module, reads) in &reads {
                set_reads.execute(params![module, reads])?;
            }
            for (module, reads) in &new.encoded_reads {
                set_reads.execute(params![module, reads])?;
            }
            drop(table_timer);
            let table_timer = RecordTimer::start(Phase::RecordSqlItems);
            let mut set_items = tx.prepare_cached("INSERT OR REPLACE INTO items (module, data) VALUES (?1, ?2)")?;
            for (module, items) in &items {
                set_items.execute(params![module, items])?;
            }
            for (module, items) in &new.encoded_items {
                set_items.execute(params![module, items])?;
            }
            drop(table_timer);
            let table_timer = RecordTimer::start(Phase::RecordSqlInterfaces);
            let mut set_interface =
                tx.prepare_cached("INSERT OR REPLACE INTO interfaces (module, hash, data) VALUES (?1, ?2, ?3)")?;
            let mut set_extras =
                tx.prepare_cached("INSERT OR REPLACE INTO interface_extras (module, data) VALUES (?1, ?2)")?;
            let mut delete_extras = tx.prepare_cached("DELETE FROM interface_extras WHERE module = ?1")?;
            for (module, interface) in &new.interface_updates {
                set_interface.execute(params![module, interface.hash as i64, interface.core])?;
                match &interface.extras {
                    Some(extras) => set_extras.execute(params![module, extras])?,
                    None => delete_extras.execute(params![module])?,
                };
            }
            drop(table_timer);
            let table_timer = RecordTimer::start(Phase::RecordSqlModules);
            let mut delete_interface = tx.prepare_cached("DELETE FROM interfaces WHERE module = ?1")?;
            let mut delete_reads = tx.prepare_cached("DELETE FROM reads WHERE module = ?1")?;
            let mut delete_items = tx.prepare_cached("DELETE FROM items WHERE module = ?1")?;
            let mut delete_module = tx.prepare_cached("DELETE FROM modules WHERE module = ?1")?;
            let mut set_module = tx.prepare_cached(
                "INSERT OR REPLACE INTO modules
                 (module, js_confirmed_at, implementation_warnings, interface_warnings,
                  interface_digest, imports)
                 VALUES (?1, ?2, ?3, ?4, ?5, ?6)",
            )?;
            sync_encoded_rows(
                &previous.modules,
                &new.modules,
                &module_rows,
                partial,
                |module| {
                    delete_interface.execute(params![module])?;
                    delete_extras.execute(params![module])?;
                    delete_reads.execute(params![module])?;
                    delete_items.execute(params![module])?;
                    delete_module.execute(params![module]).map(drop)
                },
                |module, row, imports| {
                    set_module
                        .execute(params![
                            module,
                            row.js_confirmed_at.map(nanos_from_time),
                            row.implementation_warnings,
                            row.interface_warnings,
                            row.interface_digest.map(|digest| digest as i64),
                            imports
                        ])?;
                    #[cfg(debug_assertions)]
                    if std::env::var("RESCRIPT_TEST_ABORT_DURING_RECORD_WRITE").ok().as_deref() == Some(package_name) {
                        // Spill partial updates before the other modules' rows.
                        tx.cache_flush()?;
                        std::process::abort();
                    }
                    Ok(())
                },
            )?;

            drop(table_timer);
            let table_timer = RecordTimer::start(Phase::RecordSqlWarnings);
            let mut delete_warning = tx.prepare_cached("DELETE FROM parse_warnings WHERE source = ?1")?;
            let mut set_warning =
                tx.prepare_cached("INSERT OR REPLACE INTO parse_warnings (source, text) VALUES (?1, ?2)")?;
            sync_rows(
                &previous.parse_warnings,
                &new.parse_warnings,
                false,
                |source| delete_warning.execute(params![source]).map(drop),
                |source, text| set_warning.execute(params![source, text]).map(drop),
            )?;

            drop(table_timer);
            let table_timer = RecordTimer::start(Phase::RecordSqlDeps);
            let mut delete_deps = tx.prepare_cached("DELETE FROM deps WHERE source = ?1")?;
            let mut set_deps =
                tx.prepare_cached("INSERT OR REPLACE INTO deps (source, mtime, deps, gentype_annotations, gentype_declarations) VALUES (?1, ?2, ?3, ?4, ?5)")?;
            sync_encoded_rows(
                &previous.deps,
                &new.deps,
                &deps_rows,
                partial,
                |source| delete_deps.execute(params![source]).map(drop),
                |source, row, deps| {
                    set_deps
                        .execute(params![
                            source,
                            row.mtime,
                            deps.as_ref(),
                            row.gentype_annotations,
                            row.gentype_declarations
                        ])
                        .map(drop)
                },
            )?;
            drop(table_timer);
        }
    Ok(())
}

/// The rows of `new` that differ from `previous`, in key order, each with
/// `encode` of it.
fn changed_rows<'a, K, V, E>(
    previous: &BTreeMap<K, V>,
    new: &'a BTreeMap<K, V>,
    encode: impl Fn(&'a V) -> E + Sync,
) -> Vec<(&'a K, &'a V, E)>
where
    K: Ord + Sync,
    V: PartialEq + Sync,
    E: Send,
{
    new.par_iter()
        .filter(|(key, value)| previous.get(*key) != Some(*value))
        .map(|(key, value)| (key, value, encode(value)))
        .collect()
}

/// [`sync_rows`] with the rows to set already found and encoded by
/// [`changed_rows`].
fn sync_encoded_rows<K: Ord, V, E>(
    previous: &BTreeMap<K, V>,
    new: &BTreeMap<K, V>,
    changed: &[(&K, &V, E)],
    partial: bool,
    mut delete: impl FnMut(&K) -> rusqlite::Result<()>,
    mut set: impl FnMut(&K, &V, &E) -> rusqlite::Result<()>,
) -> rusqlite::Result<()> {
    for key in previous.keys() {
        if !partial && !new.contains_key(key) {
            delete(key)?;
        }
    }
    for (key, value, encoded) in changed {
        set(key, value, encoded)?;
    }
    Ok(())
}

/// Delete the rows of `previous` missing from `new` and set the rows of
/// `new` that differ.
fn sync_rows<K: Ord, V: PartialEq>(
    previous: &BTreeMap<K, V>,
    new: &BTreeMap<K, V>,
    partial: bool,
    mut delete: impl FnMut(&K) -> rusqlite::Result<()>,
    mut set: impl FnMut(&K, &V) -> rusqlite::Result<()>,
) -> rusqlite::Result<()> {
    for key in previous.keys() {
        if !partial && !new.contains_key(key) {
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
            check_only: false,
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
            gentype_outputs: None,
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
                interface_digest: Some(u64::MAX - js),
                imports: Some(Imports::new(vec![
                    ("B".to_string(), js),
                    ("C".to_string(), u64::MAX),
                ])),
            },
        );
        state
    }

    #[test]
    fn memory_image_matches_file_pragmas_and_accepts_incremental_updates() {
        let dir = TempDir::new().unwrap();
        let package = test_package(dir.path());
        let first = state(17, Some("warning"));
        write_record(&package, None, &first);
        let old_reader = Connection::open(path(&package)).unwrap();
        let pragmas = |conn: &Connection| ["page_size", "user_version", "auto_vacuum", "encoding", "application_id", "journal_mode"]
            .map(|key| conn.query_row(&format!("PRAGMA {key}"), [], |row| Ok(format!("{:?}", row.get_ref(0)?))).unwrap());
        let file_pragmas = pragmas(&old_reader);
        let second = state(23, None);
        let record = MemoryRecord::new(&second, &[]).unwrap();
        record.conn.execute_batch("COMMIT").unwrap();
        assert!(matches!(record.conn.serialize(rusqlite::DatabaseName::Main).unwrap(), rusqlite::serialize::Data::Shared(_)));
        record.conn.execute_batch("BEGIN").unwrap();
        record.publish(&package).unwrap();
        let conn = Connection::open(path(&package)).unwrap();
        assert_eq!(pragmas(&conn), file_pragmas);
        assert_eq!(read(&package).as_ref(), Some(&second));
        // The held reader stays on the old inode, including between statements.
        assert_eq!(read_modules(&old_reader).unwrap(), first.modules);
        let third = state(31, None);
        write_record(&package, Some(&second), &third);
        assert_eq!(read(&package).as_ref(), Some(&third));
    }

    // Subprocess entry point: the parent kills the writer while its transaction
    // is open, then lets a real MemoryRecord publisher recover under the guard.
    #[test]
    fn publication_process() {
        let Ok(root) = std::env::var("RESCRIPT_PUBLICATION_TEST_ROOT") else { return };
        let package = test_package(Path::new(&root));
        match std::env::var("RESCRIPT_PUBLICATION_TEST_ROLE").unwrap().as_str() {
            "writer" => {
                let (_guard, mut conn) = open_for_write(&package).unwrap();
                let tx = conn.transaction().unwrap();
                tx.execute("UPDATE modules SET js_confirmed_at = 99", []).unwrap();
                std::fs::write(Path::new(&root).join("writer-ready"), b"").unwrap();
                let mut line = String::new();
                std::io::stdin().read_line(&mut line).unwrap();
                panic!("parent should kill writer");
            }
            "publisher" => {
                let record = MemoryRecord::new(&state(23, None), &[]).unwrap();
                std::fs::write(Path::new(&root).join("publisher-ready"), b"").unwrap();
                record.publish(&package).unwrap();
            }
            role => panic!("unknown test role {role}"),
        }
    }

    #[test]
    fn publisher_waits_for_writer_and_recovers_its_journal_before_rename() {
        use std::process::{Command, Stdio};
        let dir = TempDir::new().unwrap();
        let package = test_package(dir.path());
        write_record(&package, None, &state(17, None));
        let spawn = |role: &str| Command::new(std::env::current_exe().unwrap())
            .args(["--exact", "build::state_db::tests::publication_process", "--nocapture"])
            .env("RESCRIPT_PUBLICATION_TEST_ROOT", dir.path())
            .env("RESCRIPT_PUBLICATION_TEST_ROLE", role)
            .stdin(Stdio::piped()).spawn().unwrap();
        let wait_ready = |name: &str| {
            let start = std::time::Instant::now();
            while !dir.path().join(name).exists() {
                assert!(start.elapsed() < Duration::from_secs(10), "child did not become ready");
                std::thread::yield_now();
            }
        };
        let mut writer = spawn("writer");
        wait_ready("writer-ready");
        let mut publisher = spawn("publisher");
        wait_ready("publisher-ready");
        assert!(publisher.try_wait().unwrap().is_none());
        writer.kill().unwrap();
        writer.wait().unwrap();
        let start = std::time::Instant::now();
        loop {
            if let Some(status) = publisher.try_wait().unwrap() {
                assert!(status.success());
                break;
            }
            assert!(start.elapsed() < Duration::from_secs(10), "publisher did not finish");
            std::thread::yield_now();
        }
        assert_eq!(read(&package).as_ref(), Some(&state(23, None)));
        assert!(!PathBuf::from(format!("{}-journal", path(&package).display())).exists());
    }

    #[test]
    fn obsolete_schema_is_rebuilt() {
        let dir = TempDir::new().unwrap();
        let package = test_package(dir.path());
        write_record(&package, None, &state(1, None));
        let conn = Connection::open(path(&package)).unwrap();
        conn.pragma_update(None, "user_version", SCHEMA_VERSION - 1)
            .unwrap();
        drop(conn);
        assert!(read(&package).is_none());
        assert!(read_meta(&package).is_none());
        let (_guard, conn) = open_for_write(&package).unwrap();
        let version: i64 = conn
            .query_row("PRAGMA user_version", [], |row| row.get(0))
            .unwrap();
        assert_eq!(version, SCHEMA_VERSION);
        drop(conn);
        drop(_guard);
        // A schema alone is not a completed build.
        assert!(read(&package).is_none());
        assert!(read_meta(&package).unwrap().is_empty());
    }

    #[test]
    fn a_missing_database_reads_as_no_record() {
        let dir = TempDir::new().unwrap();
        let package = test_package(dir.path());
        assert!(read(&package).is_none());
        assert!(read_meta(&package).is_none());
    }

    #[test]
    fn recovered_runtime_rows_survive_the_following_build_record() {
        let dir = TempDir::new().unwrap();
        let package = test_package(dir.path());
        let db = path(&package);
        write_record(&package, None, &state(1, None));
        std::fs::write(pending_path(&db), b"incomplete").unwrap();
        std::fs::write(&db, b"incomplete SQLite pages").unwrap();
        let runtime = vec![("Runtime".to_string(), vec![1, 2, 3])];
        write_runtime_interfaces(&db, "runtime-key", &runtime);
        assert_eq!(read_runtime_interfaces(&db, "runtime-key"), Some(runtime.clone()));
        assert!(read(&package).is_none());
        write_record(&package, None, &state(2, None));
        assert_eq!(read_runtime_interfaces(&db, "runtime-key"), Some(runtime));
        let mut expected = state(2, None);
        expected.meta.insert(META_RUNTIME_KEY.to_string(), "runtime-key".to_string());
        assert_eq!(read(&package).as_ref(), Some(&expected));
    }

    #[test]
    fn incomplete_marker_rejects_and_replaces_even_an_unreadable_database() {
        let dir = TempDir::new().unwrap();
        let package = test_package(dir.path());
        let first = state(1, None);
        write_record(&package, None, &first);
        assert_eq!(read(&package).as_ref(), Some(&first));
        let pending = pending_path(&path(&package));
        std::fs::write(&pending, b"incomplete").unwrap();
        assert!(read(&package).is_none());
        assert!(read_meta(&package).is_none());
        std::fs::write(path(&package), b"incomplete SQLite pages").unwrap();
        write_record(&package, None, &first);
        assert!(!pending.exists());
        assert_eq!(read(&package).as_ref(), Some(&first));
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
                gentype_annotations: true,
                gentype_declarations: false,
            },
        );
        write_record(&package, Some(&first), &second);
        assert_eq!(read(&package).as_ref(), Some(&second));
    }

    #[test]
    fn reads_and_items_are_looked_up_by_module() {
        let dir = TempDir::new().unwrap();
        let package = test_package(dir.path());
        let mut new = state(1, None);
        new.reads_updates.insert(
            "A".to_string(),
            [
                ("B".to_string(), (7, vec!["@".to_string(), "v:x".to_string()])),
                ("C".to_string(), (u64::MAX, vec!["*".to_string()])),
            ]
            .into_iter()
            .collect(),
        );
        new.items_updates.insert(
            "A".to_string(),
            [("@".to_string(), 1), ("t:t".to_string(), u64::MAX)]
                .into_iter()
                .collect(),
        );
        write_record(&package, None, &new);
        assert_eq!(read_reads(&package, &["A", "Z"]), new.reads_updates);
        assert_eq!(read_items(&package, &["A"]), new.items_updates);

        // Removing the module removes its rows.
        let mut empty = PackageState::default();
        empty.meta.insert(META_BUILD_OK.to_string(), "1".to_string());
        write_record(&package, read(&package).as_ref(), &empty);
        assert!(read_reads(&package, &["A"]).is_empty());
        assert!(read_items(&package, &["A"]).is_empty());
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
