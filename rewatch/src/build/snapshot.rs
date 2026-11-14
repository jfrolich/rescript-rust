//! Verified runtime and Belt packages compiled into the executable.
//!
//! Every process that compiles anything needs `@rescript/runtime` compiled
//! into its module registry, and the runtime that ships with a compiler is
//! always the same. So the `rescript` executable's build script compiles the
//! runtime in the repository with [`produce`] and the executable hands the
//! result to [`install`]: a build whose runtime has the same sources then
//! registers these interfaces, borrowed from the executable's memory and
//! decoded on first lookup, instead of compiling the runtime.
//!
//! A runtime with other sources is compiled as before. Embedded paths use
//! package-relative roots and the shared stored-core rebasing operation restores
//! the installed source paths before the registry exposes a unit.

use super::compile;
use super::packages;
use anyhow::{Context, Result, anyhow};
use rescript_compiler::cmi::persistent_env::{ModuleRegistry, PendingCore};
use rescript_compiler::cmi::stored_module;
use std::path::{Path, PathBuf};
use std::sync::{Mutex, OnceLock};

/// Container identity; the embedded producer identity is zero by construction.
const MAGIC: &[u8; 8] = b"RESSNAP1";
const RECORD_BYTES: usize = 48;

/// Borrowed package header and fixed-width module index. No module is decoded.
struct PackageIndex<'a> {
    bytes: &'a [u8],
    name: &'a str,
    recorded_root: &'a str,
    sources_digest: blake3::Hash,
    records: &'a [u8],
}

static EMBEDDED: OnceLock<Option<Vec<PackageIndex<'static>>>> = OnceLock::new();

/// Install the package headers in O(package count), allocating only the package
/// table. Module records and blobs remain borrowed and untouched.
pub fn install(bytes: &'static [u8]) {
    let _ = EMBEDDED.set(decode(bytes));
}

/// Compile the runtime and, when present, its sibling Belt package into the
/// container accepted by [`install`]. Producer only: one runtime compile and
/// four Belt proof compiles; allocation is proportional to their outputs.
pub fn produce(runtime_root: &Path) -> Result<Vec<u8>> {
    let runtime_root = runtime_root.to_path_buf();
    // Like a build's runtime pre-compilation, on a thread with a large stack.
    std::thread::Builder::new()
        .name("rescript-embed-runtime".to_string())
        .stack_size(256 * 1024 * 1024)
        .spawn(move || {
            let mut bytes = compile_on_this_thread(&runtime_root)?;
            append_source_manifest(&mut bytes, &runtime_root)?;
            Ok(bytes)
        })
        .context("failed to spawn the runtime compile thread")?
        .join()
        .map_err(|_| anyhow!("compiling the runtime panicked"))?
}

/// Developer-only freshness gate: produce once, compare bytes once, and on
/// mismatch inspect borrowed index/blob slices in O(snapshot bytes + modules).
/// No stored core is decoded and no per-module object is allocated.
pub fn check(runtime_root: &Path, embedded: &[u8]) -> Result<()> {
    anyhow::ensure!(!embedded.is_empty(), "embedded snapshot is absent");
    let fresh = produce(runtime_root)?;
    if fresh == embedded { return Ok(()); }
    compare_source_manifests(&fresh, embedded)?;
    let old = decode(embedded).context("embedded snapshot is invalid")?;
    let new = decode(&fresh).context("produced snapshot is invalid")?;
    for (package_index, package) in new.iter().enumerate() {
        let Some(previous) = old.get(package_index).filter(|p| p.name == package.name) else {
            anyhow::bail!("snapshot differs: {} package added", package.name);
        };
        for slot in 0..package.len().max(previous.len()) {
            let current = package.module(slot);
            let prior = previous.module(slot);
            let name = match (current, prior) {
                (Some((a, _)), Some((b, _))) => a.min(b),
                (Some((a, _)), None) | (None, Some((a, _))) => a,
                (None, None) => unreachable!(),
            };
            if current != prior || [16, 24, 32, 40].into_iter().any(|field| {
                let width = if field >= 32 { 4 } else { 1 };
                package.blob(slot, field, width) != previous.blob(slot, field, width)
            }) {
                anyhow::bail!("snapshot differs: {} module {name}", package.name);
            }
        }
        if package.sources_digest != previous.sources_digest {
            anyhow::bail!("snapshot differs: {} sources/options digest (module bytes unchanged)", package.name);
        }
    }
    anyhow::bail!("snapshot differs: package headers or container bytes")
}

/// Producer only: O(source bytes + files log files), one sorted directory list
/// per package and one source buffer at a time. The cold trailer is never read
/// by normal builds; it identifies edits that leave all compiled cores equal.
fn append_source_manifest(bytes: &mut Vec<u8>, runtime: &Path) -> Result<()> {
    let start = bytes.len();
    let belt = runtime.parent().context("runtime package parent")?.join("belt");
    for (name, root) in [("@rescript/runtime", runtime.to_path_buf()), ("@rescript/belt", belt.join("src"))] {
        if !root.is_dir() { continue; }
        let mut paths = std::fs::read_dir(&root)?.map(|e| e.map(|e| e.path()))
            .collect::<std::io::Result<Vec<_>>>()?;
        paths.sort();
        for path in paths {
            if !path.extension().is_some_and(|ext| ext == "res" || ext == "resi") { continue; }
            for value in [name, path.file_name().context("source filename")?.to_str().context("UTF-8 source filename")?] {
                push_u32(bytes, value.len())?;
                bytes.extend_from_slice(value.as_bytes());
            }
            bytes.extend_from_slice(blake3::hash(&std::fs::read(path)?).as_bytes());
        }
    }
    let len = bytes.len() - start;
    push_u32(bytes, len)?;
    Ok(())
}

/// Developer only: O(1), borrow the cold source manifest using its footer.
fn source_manifest(bytes: &[u8]) -> Result<&[u8]> {
    let end = bytes.len().checked_sub(4).context("missing source manifest")?;
    let len = u32::from_le_bytes(bytes[end..].try_into()?) as usize;
    bytes.get(end.checked_sub(len).context("invalid source manifest")?..end)
        .context("invalid source manifest")
}

/// Developer only: O(source count), borrowed names and fixed-size digests,
/// without core decoding, hashing, or per-source allocation.
fn compare_source_manifests(fresh: &[u8], embedded: &[u8]) -> Result<usize> {
    let mut new = Reader(source_manifest(fresh)?);
    let mut old = Reader(source_manifest(embedded)?);
    let mut steps = 0;
    while !new.0.is_empty() || !old.0.is_empty() {
        steps += 1;
        let a = source_record(&mut new);
        let b = source_record(&mut old);
        if a != b {
            let (package, file, _) = match (a, b) {
                (Some(a), Some(b)) => if (a.0, a.1) < (b.0, b.1) { a } else { b },
                (Some(a), None) | (None, Some(a)) => a,
                (None, None) => anyhow::bail!("invalid source manifest record"),
            };
            anyhow::bail!("snapshot differs: {} module {} (source {})",
                std::str::from_utf8(package)?, Path::new(std::str::from_utf8(file)?)
                    .file_stem().context("module name")?.to_string_lossy(), std::str::from_utf8(file)?);
        }
    }
    Ok(steps)
}

/// Developer only: O(1), three borrowed slices, no allocations.
fn source_record<'a>(reader: &mut Reader<'a>) -> Option<(&'a [u8], &'a [u8], &'a [u8])> {
    Some((reader.part()?, reader.part()?, reader.take(32)?))
}

fn compile_on_this_thread(runtime_root: &Path) -> Result<Vec<u8>> {
    let config = packages::read_config(runtime_root)
        .with_context(|| format!("failed to read runtime config from {}", runtime_root.display()))?;
    let paths = compile::runtime_source_paths(runtime_root)?;
    if paths.is_empty() {
        return Err(anyhow!("no runtime sources in {}", runtime_root.display()));
    }
    let digest = sources_digest(runtime_root, &paths).context("failed to read the runtime sources")?;
    let registry = Mutex::new(ModuleRegistry::new());
    let modules = compile::compile_runtime_sources(&registry, runtime_root, runtime_root, &config, paths)?;
    let interfaces = compile::encode_runtime_interfaces(&registry, &modules)
        .ok_or_else(|| anyhow!("a compiled runtime module is missing from the registry"))?;
    let modules = interfaces.into_iter().map(|(name, data)| {
        let (extras, core) = stored_module::split(&data)
            .ok_or_else(|| anyhow!("invalid stored module {name}"))?;
        let extras = stored_module::decode_extras(extras)
            .ok_or_else(|| anyhow!("invalid stored extras for {name}"))?;
        anyhow::ensure!(extras.gentype_declarations.is_empty(),
            "snapshot module {name} has genType declarations");
        let mut normalized = stored_module::decode_core(core)
            .ok_or_else(|| anyhow!("invalid runtime core {name}"))?;
        normalized.rebase_paths(runtime_root, Path::new("@rescript/runtime"));
        let (_, normalized) = stored_module::encode_parts(&stored_module::StoredModuleRef {
            pers_struct: normalized.pers_struct.as_ref(), info: &normalized.info, gentype_declarations: &[],
        });
        anyhow::ensure!(!contains_bytes(&normalized, runtime_root.to_string_lossy().as_bytes()),
            "runtime module {name} retains a producer path");
        let mut restored = stored_module::decode_core(&normalized).expect("normalized runtime core");
        restored.rebase_paths(Path::new("@rescript/runtime"), runtime_root);
        let (_, restored) = stored_module::encode_parts(&stored_module::StoredModuleRef {
            pers_struct: restored.pers_struct.as_ref(), info: &restored.info, gentype_declarations: &[],
        });
        anyhow::ensure!(restored == core, "runtime stored-core equivalence failed for {name}");
        Ok(ProducedModule { name, core: normalized, javascript: Default::default(), slots: Default::default() })
    }).collect::<Result<Vec<_>>>()?;
    let runtime = ProducedPackage {
        name: "@rescript/runtime".into(),
        recorded_root: "@rescript/runtime".into(),
        sources_digest: digest,
        modules,
    };
    let belt_root = runtime_root.parent().expect("runtime package parent").join("belt");
    if belt_root.join("rescript.json").is_file() {
        let belt = compile_belt(&belt_root, runtime_root, &runtime).context(BeltProofFailure)?;
        encode(&[runtime, belt])
    } else {
        encode(&[runtime])
    }
}

#[derive(Debug)]
struct BeltProofFailure;
impl std::fmt::Display for BeltProofFailure {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("Belt snapshot proof failed")
    }
}
impl std::error::Error for BeltProofFailure {}

/// O(error context depth), producer only. Belt proof failures are fatal while
/// runtime compile failures retain the pre-existing build-script fallback.
pub fn is_belt_proof_failure(error: &anyhow::Error) -> bool {
    error.is::<BeltProofFailure>()
}

/// Compile Belt through the ordinary package pipeline for both formats, two
/// suffixes and both layouts. Producer only: four package compiles plus linear
/// template comparison and one core encoding per module.
fn compile_belt(root: &Path, runtime_root: &Path, runtime: &ProducedPackage) -> Result<ProducedPackage> {
    anyhow::ensure!(alternate_backend_option().is_none(),
        "produce snapshots with the default JavaScript printer and backend");
    let config: serde_json::Value = serde_json::from_slice(&std::fs::read(root.join("rescript.json"))?)?;
    let mut baseline: Option<ProducedPackage> = None;
    for in_source in [false, true] {
        for suffix in [".js", ".res.mjs"] {
            let dir = tempfile::tempdir()?;
            let source_dir = dir.path().join("src");
            std::fs::create_dir(&source_dir)?;
            for entry in std::fs::read_dir(root.join("src"))? {
                let entry = entry?;
                if entry.path().extension().is_some_and(|ext| ext == "res" || ext == "resi") {
                    std::fs::copy(entry.path(), source_dir.join(entry.file_name()))?;
                }
            }
            let mut config = config.clone();
            config["package-specs"] = serde_json::json!([
                {"module":"esmodule", "suffix":suffix, "in-source":in_source},
                {"module":"commonjs", "suffix":if suffix == ".js" { ".cjs" } else { ".res.cjs" }, "in-source":in_source}
            ]);
            // The configuration parser rejects duplicate suffixes even when
            // output directories differ; use distinct suffixes for the formats.
            if in_source {
                config["jsx"] = serde_json::json!({"version":4,"module":"SnapshotJsx","preserve":true});
                config["experimental-features"] = serde_json::json!({"LetUnwrap":true});
            }
            std::fs::write(dir.path().join("rescript.json"), serde_json::to_vec(&config)?)?;
            let context = crate::project_context::ProjectContext::new(dir.path())?;
            let packages = packages::make(&None, &context, false, false, None)?;
            let compiler = super::build_types::CompilerInfo {
                bsc_path: std::env::current_exe()?, bsc_hash: blake3::hash(b"snapshot-producer"),
                runtime_path: runtime_root.to_path_buf(),
            };
            let mut state = super::build_types::BuildCommandState::new(
                dir.path().to_path_buf(), context, packages, compiler, None, None,
                crate::config::SourceMapCommand::Build,
            );
            packages::parse_packages(&mut state)?;
            {
                let mut registry = state.module_registry.lock().unwrap();
                for module in &runtime.modules {
                    registry.register_stored_parts(&module.name, None, PendingCore::Bytes(rebased_runtime_core(
                        &module.core, Path::new(&runtime.recorded_root), runtime_root,
                    ).ok_or_else(|| anyhow!("invalid runtime module {}", module.name))?.into()))
                        .ok_or_else(|| anyhow!("failed to register runtime module {}", module.name))?;
                }
            }
            let warnings = super::parse::generate_asts(&mut state, || (), super::parse::ParseWarningLog::Append)?;
            anyhow::ensure!(warnings.trim().is_empty(), "Belt snapshot parse warnings: {warnings}");
            super::deps::get_deps(&mut state, &Default::default());
            super::deps::plan_gentype(&mut state);
            let (errors, warnings, _) = compile::compile(&mut state, false, || (), |_| ())?;
            anyhow::ensure!(errors.trim().is_empty() && warnings.trim().is_empty(),
                "Belt snapshot diagnostics: {errors}{warnings}");
            let package = state.packages.get("@rescript/belt").expect("Belt package");
            let mut modules = Vec::with_capacity(state.modules.len());
            let registry = state.module_registry.lock().unwrap();
            let mut names: Vec<_> = state.modules.keys().collect();
            names.sort_unstable();
            for name in names {
                let data = registry.encode_stored_module(name).ok_or_else(|| anyhow!("missing Belt module {name}"))?;
                let (extras, core) = stored_module::split(&data).expect("encoded module");
                anyhow::ensure!(stored_module::decode_extras(extras).expect("encoded extras").gentype_declarations.is_empty(),
                    "Belt module {name} has genType declarations");
                let original_core = core;
                let mut core = stored_module::decode_core(core).expect("encoded core");
                core.rebase_paths(&package.path, Path::new("@rescript/belt"));
                core.info.package_name = None;
                core.info.package_root = None;
                core.info.js_output_suffix = None;
                core.info.package_outputs = Default::default();
                let (_, core) = stored_module::encode_parts(&stored_module::StoredModuleRef {
                    pers_struct: core.pers_struct.as_ref(), info: &core.info, gentype_declarations: &[],
                });
                anyhow::ensure!(!contains_bytes(&core, package.path.to_string_lossy().as_bytes()),
                    "Belt module {name} retains a producer path");
                let mut restored = stored_module::decode_core(&core).expect("normalized core");
                restored.rebase_paths(Path::new("@rescript/belt"), &package.path);
                compile::configure_snapshot_module(&mut restored.info, package, state.get_root_config());
                let (_, restored) = stored_module::encode_parts(&stored_module::StoredModuleRef {
                    pers_struct: restored.pers_struct.as_ref(), info: &restored.info, gentype_declarations: &[],
                });
                anyhow::ensure!(restored == original_core, "Belt stored-core equivalence failed for {name}");
                let source = PathBuf::from("src").join(format!("{name}.res"));
                let targets = compile::js_output_targets_for_source(package, &source, state.get_root_config());
                let mut javascript: [Vec<u8>; 2] = Default::default();
                let mut slots: [Vec<u32>; 2] = Default::default();
                for (format, target) in targets.iter().enumerate() {
                    let output = std::fs::read(&target.path)?;
                    let suffix = if format == 1 { if suffix == ".js" { ".cjs" } else { ".res.cjs" } } else { suffix };
                    let (text, positions) = template(&output, suffix.as_bytes())?;
                    anyhow::ensure!(render_template(&text, positions.iter().copied(), suffix.as_bytes())? == output,
                        "Belt template reconstruction failed for {name}");
                    javascript[format] = text;
                    slots[format] = positions;
                }
                modules.push(ProducedModule { name: name.clone(), core, javascript, slots });
            }
            if let Some(baseline) = &baseline {
                anyhow::ensure!(baseline.modules.len() == modules.len(), "Belt module count changed across proof builds");
                for (first, next) in baseline.modules.iter().zip(&modules) {
                    anyhow::ensure!(first.name == next.name && first.javascript == next.javascript && first.slots == next.slots,
                        "Belt template proof failed for {}", next.name);
                    anyhow::ensure!(first.core == next.core, "Belt core proof failed for {}", next.name);
                }
            } else {
                baseline = Some(ProducedPackage {
                    name: "@rescript/belt".into(), recorded_root: "@rescript/belt".into(),
                    sources_digest: belt_sources_digest(root)?, modules,
                });
            }
        }
    }
    Ok(baseline.expect("four proof configurations"))
}

/// O(haystack bytes * needle bytes), producer-only path-leak assertion.
fn contains_bytes(haystack: &[u8], needle: &[u8]) -> bool {
    !needle.is_empty() && haystack.windows(needle.len()).any(|bytes| bytes == needle)
}

/// O(JavaScript bytes), strip only sibling-import suffixes. Producer proof
/// builds must produce exactly the same text and slots; literals elsewhere
/// are retained and therefore cannot accidentally become template slots.
fn template(output: &[u8], suffix: &[u8]) -> Result<(Vec<u8>, Vec<u32>)> {
    let mut text = Vec::with_capacity(output.len());
    let mut slots = Vec::new();
    let mut cursor = 0;
    while cursor < output.len() {
        let rest = &output[cursor..];
        let prefix = if rest.starts_with(b"from \"./") { 6 } else if rest.starts_with(b"require(\"./") { 9 } else { 0 };
        if prefix != 0 {
            let start = cursor + prefix;
            if let Some(end) = output[start..].iter().position(|&byte| byte == b'"') {
                let end = start + end;
                if output[start..end].ends_with(suffix) {
                    text.extend_from_slice(&output[cursor..end - suffix.len()]);
                    slots.push(u32::try_from(text.len())?);
                    cursor = end;
                    continue;
                }
            }
        }
        text.push(output[cursor]);
        cursor += 1;
    }
    Ok((text, slots))
}

/// O(text bytes + slot count * suffix bytes), with one output allocation and
/// one forward pass. Slots are offsets into the suffix-free text.
fn render_template(text: &[u8], slots: impl ExactSizeIterator<Item = u32>, suffix: &[u8]) -> Result<Vec<u8>> {
    let mut output = Vec::with_capacity(text.len() + slots.len() * suffix.len());
    let mut previous = 0;
    for slot in slots {
        let slot = slot as usize;
        anyhow::ensure!(slot >= previous && slot <= text.len(), "invalid template slot");
        output.extend_from_slice(&text[previous..slot]);
        output.extend_from_slice(suffix);
        previous = slot;
    }
    output.extend_from_slice(&text[previous..]);
    Ok(output)
}

/// O(source bytes + module count log module count), once per package per build.
/// Only parsed package flags and features enter the options part of the key.
fn belt_sources_digest(root: &Path) -> Result<blake3::Hash> {
    let config = packages::read_config(root)?;
    let mut flags = config.get_experimental_features_args();
    flags.sort();
    let mut hasher = blake3::Hasher::new();
    let mut add = |bytes: &[u8]| { hasher.update(&(bytes.len() as u64).to_le_bytes()); hasher.update(bytes); };
    add(config.name.as_bytes());
    for flag in crate::config::flatten_flags(&config.compiler_flags).iter().chain(&flags) { add(flag.as_bytes()); }
    let mut paths = std::fs::read_dir(root.join("src"))?.map(|entry| entry.map(|entry| entry.path()))
        .collect::<std::io::Result<Vec<_>>>()?;
    paths.sort();
    for path in paths {
        if path.extension().is_some_and(|ext| ext == "res" || ext == "resi") {
            add(path.file_name().expect("source filename").to_string_lossy().as_bytes());
            add(&std::fs::read(path)?);
        }
    }
    Ok(hasher.finalize())
}

/// O(source bytes + module count) verification, then one package allocation.
/// No module core is read or copied until a lookup requests it.
/// Register the embedded runtime in `registry` if `runtime_paths` (module
/// name, `.res` path), with the configuration at `runtime_root`, are the
/// sources it was compiled from. Returns whether it did.
pub(crate) fn register(
    registry: &Mutex<ModuleRegistry>,
    runtime_root: &Path,
    runtime_paths: &[(String, PathBuf)],
    store: Option<&compile::RuntimeStore>,
    dump: bool,
) -> Result<bool> {
    let mode = std::env::var("RESCRIPT_SNAPSHOT").unwrap_or_default();
    anyhow::ensure!(matches!(mode.as_str(), "" | "off" | "require"),
        "RESCRIPT_SNAPSHOT must be off or require (or unset)");
    let mismatch = |reason| fallback("@rescript/runtime", &mode, reason);
    if mode == "off" { return mismatch("disabled by RESCRIPT_SNAPSHOT=off"); }
    if dump { return mismatch("dump flags are not supported"); }
    if std::env::var_os("RESCRIPT_FULL_BUILD").is_some() { return mismatch("RESCRIPT_FULL_BUILD is enabled"); }
    if let Some(option) = alternate_backend_option() { return mismatch(option); }
    let Some(Some(embedded)) = EMBEDDED.get() else {
        return mismatch("the snapshot is absent");
    };
    let Some(embedded) = embedded.iter().find(|package| package.name == "@rescript/runtime") else {
        return mismatch("the snapshot is absent");
    };
    if embedded.len() != runtime_paths.len()
        || !verify_runtime(embedded.sources_digest, runtime_root, runtime_paths, store).unwrap_or(false)
    {
        return mismatch("its sources differ from the ones this compiler was built with");
    }
    registry.lock().unwrap().register_snapshot(std::sync::Arc::new(RuntimePackage {
        index: embedded, root: runtime_root.to_path_buf(),
    }));
    Ok(true)
}

/// O(message bytes), one allocation on a package fallback, never per module.
fn fallback(package: &str, mode: &str, reason: &str) -> Result<bool> {
    let message = format!("Not using the prebuilt {package}: {reason}. Compiling it from source.");
    anyhow::ensure!(mode != "require", "{message}");
    log::info!("{message}");
    Ok(false)
}

/// O(file count + path bytes), one stat per path and no source reads. Missing
/// optional interfaces/configuration have a distinct marker. This follows the
/// incremental planner's assumption: edits change size or modification time,
/// and sources do not change during a build. It is not a tamper-proof cache.
fn verification_key<'a>(
    expected: blake3::Hash,
    compiler: &str,
    paths: impl Iterator<Item = &'a Path>,
    mut metadata: impl FnMut(&Path) -> std::io::Result<std::fs::Metadata>,
) -> std::io::Result<blake3::Hash> {
    let mut hash = blake3::Hasher::new();
    hash.update(expected.as_bytes());
    hash.update(compiler.as_bytes());
    for path in paths {
        let name = path.as_os_str().as_encoded_bytes();
        hash.update(&(name.len() as u64).to_le_bytes());
        hash.update(name);
        match metadata(path) {
            Ok(meta) => {
                hash.update(&[1]);
                hash.update(&meta.len().to_le_bytes());
                hash.update(&super::state_db::nanos_from_time(meta.modified()?).to_le_bytes());
            }
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => { hash.update(&[0]); }
            Err(error) => return Err(error),
        }
    }
    Ok(hash.finalize())
}

/// O(file count + path bytes) on a hit, no source reads; otherwise `digest`'s
/// source-byte cost. The small memo lives beside the build DB and is removed by
/// clean. Atomic replacement prevents a concurrent reader accepting a partial key.
fn verified(
    expected: blake3::Hash,
    paths: &[PathBuf],
    store: Option<&compile::RuntimeStore>,
    package: &str,
    digest: impl FnOnce() -> Result<blake3::Hash>,
) -> Result<bool> {
    let memo = store.and_then(|store| {
        let key = verification_key(expected, &store.compiler_hash,
            paths.iter().map(PathBuf::as_path), |path| std::fs::metadata(path)).ok()?;
        Some((store.db.with_file_name(format!("snapshot-{package}.verified")), key))
    });
    if let Some((path, key)) = &memo {
        if std::fs::read(path).ok().as_deref() == Some(key.as_bytes()) { return Ok(true); }
    }
    if digest()? != expected { return Ok(false); }
    if let Some((path, key)) = memo
        && store.is_some_and(|store| store.writable)
    {
        // Persistence is an optimization; an unwritable build directory must not
        // change whether an otherwise valid snapshot can be used.
        let persist = || -> Result<()> {
            use std::io::Write;
            let parent = path.parent().expect("memo parent");
            std::fs::create_dir_all(parent)?;
            let mut file = tempfile::NamedTempFile::new_in(parent)?;
            file.write_all(key.as_bytes())?;
            file.persist(path)?;
            Ok(())
        };
        if let Err(error) = persist() { log::debug!("Snapshot verification memo not saved: {error}"); }
    }
    Ok(true)
}

/// O(module count) path preparation plus `verified`'s cost. No module core access.
fn verify_runtime(expected: blake3::Hash, root: &Path, sources: &[(String, PathBuf)], store: Option<&compile::RuntimeStore>) -> Result<bool> {
    let mut paths = Vec::with_capacity(sources.len() * 2 + 2);
    paths.push(root.join("rescript.json"));
    paths.push(root.join("bsconfig.json"));
    for (_, source) in sources {
        paths.push(source.clone());
        paths.push(source.with_extension("resi"));
    }
    verified(expected, &paths, store, "runtime", || sources_digest(root, sources))
}

/// Producer only: O(core bytes + filename bytes), one decode and encode per module.
/// Runtime and Belt use the same stored-core path rebasing operation.
fn rebased_runtime_core(bytes: &[u8], from: &Path, to: &Path) -> Option<Vec<u8>> {
    let mut core = stored_module::decode_core(bytes)?;
    core.rebase_paths(from, to);
    Some(stored_module::encode_parts(&stored_module::StoredModuleRef {
        pers_struct: core.pers_struct.as_ref(), info: &core.info, gentype_declarations: &[],
    }).1)
}

/// O(configuration bytes), once per verification. An absent configuration uses
/// the producer's parsed options; malformed or unreadable configurations fail.
pub(crate) fn runtime_config(root: &Path) -> Result<crate::config::Config> {
    match std::fs::metadata(root.join("rescript.json")) {
        Ok(_) => packages::read_config(root),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => {
            if root.join("bsconfig.json").exists() { return packages::read_config(root); }
            crate::config::Config::new_from_json_string(include_str!("../../../packages/@rescript/runtime/rescript.json"))
        }
        Err(error) => Err(error.into()),
    }
}

/// O(options bytes + source bytes), one read per source. Paths and configuration
/// whitespace are excluded; parsed compiler flags and features determine options.
fn sources_digest(runtime_root: &Path, runtime_paths: &[(String, PathBuf)]) -> Result<blake3::Hash> {
    let config = runtime_config(runtime_root)?;
    let mut features = config.get_experimental_features_args();
    features.sort();
    let mut hasher = blake3::Hasher::new();
    let mut add = |bytes: &[u8]| {
        hasher.update(&(bytes.len() as u64).to_le_bytes());
        hasher.update(bytes);
    };
    add(config.name.as_bytes());
    for flag in crate::config::flatten_flags(&config.compiler_flags).iter().chain(&features) {
        add(flag.as_bytes());
    }
    for (module_name, path) in runtime_paths {
        add(module_name.as_bytes());
        add(&std::fs::read(path)?);
        match std::fs::read(path.with_extension("resi")) {
            Ok(interface) => {
                add(b"resi");
                add(&interface);
            }
            Err(err) if err.kind() == std::io::ErrorKind::NotFound => add(b""),
            Err(err) => return Err(err.into()),
        }
    }
    Ok(hasher.finalize())
}

/// Producer-owned module; ES module then CommonJS template and insertion slots.
struct ProducedModule {
    name: String,
    core: Vec<u8>,
    javascript: [Vec<u8>; 2],
    slots: [Vec<u32>; 2],
}

struct ProducedPackage {
    name: String,
    recorded_root: String,
    sources_digest: blake3::Hash,
    modules: Vec<ProducedModule>,
}

/// Encode in O(total bytes + modules log modules), sorting only producer-side
/// references. Offsets are absolute; all integer fields are little endian.
fn encode(packages: &[ProducedPackage]) -> Result<Vec<u8>> {
    let mut bytes = Vec::from(MAGIC.as_slice());
    bytes.extend_from_slice(&[0; 32]);
    push_u32(&mut bytes, packages.len())?;
    let mut tables = Vec::with_capacity(packages.len());
    for package in packages {
        for value in [&package.name, &package.recorded_root] {
            push_u32(&mut bytes, value.len())?;
            bytes.extend_from_slice(value.as_bytes());
        }
        bytes.extend_from_slice(package.sources_digest.as_bytes());
        push_u32(&mut bytes, package.modules.len())?;
        tables.push(bytes.len());
        bytes.resize(bytes.len() + package.modules.len() * RECORD_BYTES, 0);
    }
    for (package, table) in packages.iter().zip(tables) {
        let mut modules: Vec<_> = package.modules.iter().collect();
        modules.sort_unstable_by(|a, b| a.name.cmp(&b.name));
        for (slot, module) in modules.into_iter().enumerate() {
            let record = table + slot * RECORD_BYTES;
            append_blob(&mut bytes, record, module.name.as_bytes(), module.name.len())?;
            append_blob(&mut bytes, record + 8, &module.core, module.core.len())?;
            for format in 0..2 {
                let js = &module.javascript[format];
                append_blob(&mut bytes, record + 16 + format * 8, js, js.len())?;
                let positions: Vec<_> = module.slots[format].iter().flat_map(|slot| slot.to_le_bytes()).collect();
                append_blob(&mut bytes, record + 32 + format * 8, &positions, module.slots[format].len())?;
            }
        }
    }
    Ok(bytes)
}

/// O(1), one integer appended; reject containers exceeding the format's limit.
fn push_u32(bytes: &mut Vec<u8>, value: usize) -> Result<()> {
    bytes.extend_from_slice(&u32::try_from(value)?.to_le_bytes());
    Ok(())
}

/// O(data length), one blob copy and two fixed-width index writes.
fn append_blob(bytes: &mut Vec<u8>, record: usize, data: &[u8], count: usize) -> Result<()> {
    if data.is_empty() { return Ok(()); }
    let offset = u32::try_from(bytes.len())?;
    let count = u32::try_from(count)?;
    bytes[record..record + 4].copy_from_slice(&offset.to_le_bytes());
    bytes[record + 4..record + 8].copy_from_slice(&count.to_le_bytes());
    bytes.extend_from_slice(data);
    Ok(())
}

impl<'a> PackageIndex<'a> {
    /// O(1), no allocation.
    fn len(&self) -> usize { self.records.len() / RECORD_BYTES }

    /// O(1), borrowing one indexed blob with checked bounds. Slot counts use
    /// four-byte elements; names, cores and JavaScript use one-byte elements.
    fn blob(&self, slot: usize, field: usize, element_bytes: usize) -> Option<&'a [u8]> {
        let start = slot.checked_mul(RECORD_BYTES)?.checked_add(field)?;
        let record = self.records.get(start..start.checked_add(8)?)?;
        let offset = u32::from_le_bytes(record[..4].try_into().ok()?) as usize;
        let count = u32::from_le_bytes(record[4..].try_into().ok()?) as usize;
        self.bytes.get(offset..offset.checked_add(count.checked_mul(element_bytes)?)?)
    }

    /// O(name bytes) UTF-8 validation and O(1) core borrowing; no allocation.
    fn module(&self, slot: usize) -> Option<(&'a str, &'a [u8])> {
        Some((std::str::from_utf8(self.blob(slot, 0, 1)?).ok()?, self.blob(slot, 8, 1)?))
    }

    /// O(log module count) name comparisons, no allocation or decoding.
    fn lookup(&self, name: &str) -> Option<usize> {
        self.lookup_counted(name).0
    }

    /// Same lookup, recording comparisons locally for the complexity test;
    /// no shared counters, locks or atomic writes.
    fn lookup_counted(&self, name: &str) -> (Option<usize>, usize) {
        let (mut low, mut high, mut steps) = (0, self.len(), 0);
        while low < high {
            let middle = low + (high - low) / 2;
            steps += 1;
            let Some(candidate) = self.blob(middle, 0, 1) else { return (None, steps); };
            match candidate.cmp(name.as_bytes()) {
                std::cmp::Ordering::Less => low = middle + 1,
                std::cmp::Ordering::Greater => high = middle,
                std::cmp::Ordering::Equal => return (Some(middle), steps),
            }
        }
        (None, steps)
    }
}

/// O(package count), checking only headers/index bounds. Individual blob
/// bounds are checked on lookup, so unreferenced modules touch no pages.
fn decode(bytes: &[u8]) -> Option<Vec<PackageIndex<'_>>> {
    let mut reader = Reader(bytes.strip_prefix(MAGIC.as_slice())?);
    if reader.take(32)? != [0; 32] { return None; }
    let count = reader.u32()? as usize;
    // Every package needs at least two lengths, a digest and a module count.
    if count == 0 || count > reader.0.len() / 44 { return None; }
    let mut packages = Vec::with_capacity(count);
    for _ in 0..count {
        let name = std::str::from_utf8(reader.part()?).ok()?;
        let recorded_root = std::str::from_utf8(reader.part()?).ok()?;
        let sources_digest = blake3::Hash::from_bytes(reader.take(32)?.try_into().ok()?);
        let count = reader.u32()? as usize;
        let records = reader.take(count.checked_mul(RECORD_BYTES)?)?;
        packages.push(PackageIndex { bytes, name, recorded_root, sources_digest, records });
    }
    Some(packages)
}

/// Borrowed cursor, passed by mutable reference rather than copied per field.
struct Reader<'a>(&'a [u8]);

impl<'a> Reader<'a> {
    /// O(1), checked slice split, no allocation.
    fn take(&mut self, len: usize) -> Option<&'a [u8]> {
        let (head, rest) = self.0.split_at_checked(len)?;
        self.0 = rest;
        Some(head)
    }
    /// O(1), four bytes read.
    fn u32(&mut self) -> Option<u32> {
        Some(u32::from_le_bytes(self.take(4)?.try_into().ok()?))
    }
    /// O(1), borrow a length-prefixed byte string without copying.
    fn part(&mut self) -> Option<&'a [u8]> {
        let len = self.u32()? as usize;
        self.take(len)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn package(count: usize) -> ProducedPackage {
        ProducedPackage {
            name: "@rescript/runtime".into(), recorded_root: "runtime".into(),
            sources_digest: blake3::hash(b"sources"),
            modules: (0..count).map(|i| ProducedModule {
                name: format!("M{i:05}"), core: vec![1, 2, 3],
                javascript: Default::default(), slots: Default::default(),
            }).collect(),
        }
    }

    fn leak(bytes: Vec<u8>) -> &'static [u8] { Box::leak(bytes.into_boxed_slice()) }

    #[test]
    fn package_table_roundtrip_and_determinism() {
        let packages = [package(2), ProducedPackage { name: "@rescript/belt".into(), ..package(3) }];
        let bytes = encode(&packages).unwrap();
        assert_eq!(bytes, encode(&packages).unwrap());
        let decoded = decode(leak(bytes)).unwrap();
        assert_eq!(decoded.len(), 2);
        assert_eq!(decoded[0].recorded_root, "runtime");
        assert_eq!(decoded[0].sources_digest, packages[0].sources_digest);
        assert_eq!(decoded[1].name, "@rescript/belt");
        assert_eq!(decoded[1].module(2), Some(("M00002", &[1, 2, 3][..])));
    }

    #[test]
    fn ten_thousand_modules_need_at_most_fourteen_comparisons() {
        let decoded = decode(leak(encode(&[package(10_000)]).unwrap())).unwrap();
        for i in 0..10_000 {
            let name = format!("M{i:05}");
            let (found, steps) = decoded[0].lookup_counted(&name);
            assert_eq!(found, Some(i));
            assert!(steps <= 14, "{name}: {steps}");
            assert_eq!(decoded[0].lookup(&name), found);
        }
        assert_eq!(std::mem::size_of::<Reader>(), 16);
        assert_eq!(std::mem::size_of::<PackageIndex>(), 96);
        assert_eq!(std::mem::size_of::<ProducedModule>(), 144);
        assert_eq!(std::mem::size_of::<ProducedPackage>(), 104);
    }

    #[test]
    fn rejects_bad_headers_and_checks_blob_bounds_on_access() {
        assert!(decode(&[]).is_none());
        let bytes = encode(&[package(1)]).unwrap();
        assert!(decode(leak(bytes[..43].to_vec())).is_none());
        let truncated = decode(leak(bytes[..bytes.len() - 1].to_vec())).unwrap();
        assert!(truncated[0].module(0).is_none());
        let mut bad = bytes;
        bad[8] = 1; // Embedded snapshots must have a zero producer identity.
        assert!(decode(leak(bad)).is_none());
    }

    #[test]
    fn ten_thousand_import_slots_roundtrip() {
        let source = b"import * as M from \"./M.res.mjs\";\n".repeat(10_000);
        let (text, slots) = template(&source, b".res.mjs").unwrap();
        assert_eq!(slots.len(), 10_000);
        assert_eq!(render_template(&text, slots.iter().copied(), b".res.mjs").unwrap(), source);
        let changed = render_template(&text, slots.iter().copied(), b".js").unwrap();
        assert_eq!(changed, b"import * as M from \"./M.js\";\n".repeat(10_000));
        assert!(render_template(b"a", [2].into_iter(), b".js").is_err());
    }

    #[test]
    fn source_manifest_comparison_is_linear_and_absence_is_explicit() {
        let mut bytes = Vec::new();
        for _ in 0..10_000 {
            for value in [b"@rescript/runtime".as_slice(), b"Module.res"] {
                push_u32(&mut bytes, value.len()).unwrap();
                bytes.extend_from_slice(value);
            }
            bytes.extend_from_slice(&[0; 32]);
        }
        let len = bytes.len();
        push_u32(&mut bytes, len).unwrap();
        assert_eq!(compare_source_manifests(&bytes, &bytes).unwrap(), 10_000);
        assert_eq!(std::mem::size_of::<Reader<'_>>(), 16);
        assert!(check(Path::new("missing"), &[]).unwrap_err().to_string().contains("embedded snapshot is absent"));
    }

    #[test]
    fn repeated_production_is_deterministic_and_packages_have_no_build_paths() {
        let runtime = Path::new(env!("CARGO_MANIFEST_DIR")).join("../packages/@rescript/runtime").canonicalize().unwrap();
        let first = produce(&runtime).unwrap();
        assert_eq!(first, produce(&runtime).unwrap());
        let checkout = runtime.parent().unwrap().parent().unwrap().parent().unwrap();
        assert!(!contains_bytes(&first, checkout.to_string_lossy().as_bytes()));
        let packages = decode(leak(first)).unwrap();
        let belt = packages.iter().find(|p| p.name == "@rescript/belt").unwrap();
        assert_eq!(belt.recorded_root, "@rescript/belt");
        assert_eq!(belt.len(), 43);
        let checkout = runtime.parent().unwrap().parent().unwrap().parent().unwrap();
        for slot in 0..belt.len() {
            let (_, core) = belt.module(slot).unwrap();
            assert!(!contains_bytes(core, checkout.to_string_lossy().as_bytes()));
            let core = stored_module::decode_core(core).unwrap();
            assert!(core.info.source_path.starts_with("@rescript/belt/src"));
            assert!(core.pers_struct.unwrap().ps_filename.starts_with("@rescript/belt/src"));
            assert!(core.info.package_root.is_none());
        }
        // Both assertions run complete builds, which replace the process-wide
        // type-store generation. Keep them in one sequential test rather than
        // letting the test runner overlap independent build generations.
        relocated_runtime_cores_equal_source_compilation_without_config();
    }

    fn relocated_runtime_cores_equal_source_compilation_without_config() {
        std::thread::Builder::new().stack_size(256 * 1024 * 1024).spawn(|| {
            use rescript_compiler::cmi::persistent_env::SnapshotModules;
            let runtime = Path::new(env!("CARGO_MANIFEST_DIR")).join("../packages/@rescript/runtime").canonicalize().unwrap();
            let packages = Box::leak(decode(leak(produce(&runtime).unwrap())).unwrap().into_boxed_slice());
            let index = packages.iter().find(|p| p.name == "@rescript/runtime").unwrap();
            let installed = tempfile::tempdir().unwrap();
            for entry in std::fs::read_dir(&runtime).unwrap() {
                let entry = entry.unwrap();
                if entry.path().extension().is_some_and(|ext| ext == "res" || ext == "resi") {
                    std::fs::copy(entry.path(), installed.path().join(entry.file_name())).unwrap();
                }
            }
            let config = runtime_config(installed.path()).unwrap();
            let paths = compile::runtime_source_paths(installed.path()).unwrap();
            assert_eq!(sources_digest(installed.path(), &paths).unwrap(), index.sources_digest);
            rescript_compiler::types::thread_store::begin_build();
            let registry = Mutex::new(ModuleRegistry::new());
            let modules = compile::compile_runtime_sources(&registry, installed.path(),
                &packages::get_build_path(installed.path()), &config, paths).unwrap();
            let source = compile::encode_runtime_interfaces(&registry, &modules).unwrap();
            let provider = RuntimePackage { index, root: installed.path().to_path_buf() };
            for (name, bytes) in source {
                let core = provider.decode(provider.find(&name).unwrap()).unwrap();
                let encoded = stored_module::encode_parts(&stored_module::StoredModuleRef {
                    pers_struct: core.pers_struct.as_ref(), info: &core.info, gentype_declarations: &[],
                }).1;
                assert!(encoded == stored_module::split(&bytes).unwrap().1, "runtime core differs: {name}");
            }
        }).unwrap().join().unwrap();
    }

    #[test]
    fn require_rejects_every_runtime_fallback_reason() {
        for reason in ["the snapshot is absent", "its sources differ", "dump flags are not supported", "RESCRIPT_FULL_BUILD is enabled"] {
            let error = fallback("@rescript/runtime", "require", reason).unwrap_err();
            assert!(error.to_string().contains(reason));
            assert!(error.to_string().contains("@rescript/runtime"));
            assert!(!fallback("@rescript/runtime", "", reason).unwrap());
        }
        assert!(!fallback("@rescript/runtime", "off", "disabled by RESCRIPT_SNAPSHOT=off").unwrap());
    }

    #[test]
    fn memo_stats_each_of_ten_thousand_paths_once() {
        let dir = tempfile::tempdir().unwrap();
        let file = dir.path().join("source.res");
        std::fs::write(&file, "let x = 1").unwrap();
        let meta = std::fs::metadata(&file).unwrap();
        let mut steps = 0;
        verification_key(blake3::hash(b"expected"), "compiler",
            std::iter::repeat_n(file.as_path(), 10_000), |_| {
                steps += 1;
                Ok(meta.clone())
            }).unwrap();
        assert_eq!(steps, 10_000);
    }

    #[test]
    fn verification_memo_reads_sources_only_on_miss() {
        let dir = tempfile::tempdir().unwrap();
        let source = dir.path().join("Source.res");
        std::fs::write(&source, "let x = 1").unwrap();
        let paths = vec![source.clone()];
        let expected = blake3::hash(b"let x = 1");
        let store = compile::RuntimeStore { db: dir.path().join("build/rescript.sqlite"), compiler_hash: "compiler".into(), writable: true };
        let reads = std::cell::Cell::new(0);
        let digest = || { reads.set(reads.get() + 1); Ok(blake3::hash(&std::fs::read(&source)?)) };
        assert!(verified(expected, &paths, Some(&store), "runtime", digest).unwrap());
        assert!(verified(expected, &paths, Some(&store), "runtime", digest).unwrap());
        assert_eq!(reads.get(), 1);
        std::fs::write(&source, "let x = 100").unwrap();
        assert!(!verified(expected, &paths, Some(&store), "runtime", digest).unwrap());
        assert_eq!(reads.get(), 2);
        std::fs::write(&source, "let x = 1").unwrap();
        std::fs::remove_file(store.db.with_file_name("snapshot-runtime.verified")).unwrap();
        assert!(verified(expected, &paths, Some(&store), "runtime", digest).unwrap());
        assert_eq!(reads.get(), 3);
    }

    #[test]
    fn runtime_provider_is_one_package_handle() {
        assert_eq!(std::mem::size_of::<RuntimePackage>(), 32);
    }

    #[test]
    fn runtime_index_does_not_decode_unreferenced_modules() {
        use rescript_compiler::cmi::persistent_env::SnapshotModules;
        let bytes = leak(encode(&[package(10_000)]).unwrap());
        let index = &Box::leak(decode(bytes).unwrap().into_boxed_slice())[0];
        let provider = RuntimePackage { index, root: PathBuf::from("installed") };
        // Invalid cores are intentional: index attachment and pending queries
        // must not inspect or decode any core, even across 10,000 lookups.
        let mut registry = ModuleRegistry::new();
        registry.register_snapshot(std::sync::Arc::new(provider));
        for slot in 0..10_000 {
            assert!(registry.is_pending_stored(&format!("M{slot:05}")));
        }
        assert!(RuntimePackage { index, root: PathBuf::from("installed") }.decode(7).is_none());
    }

    #[test]
    fn sources_digest_ignores_paths_but_not_contents() {
        let dir = tempfile::tempdir().unwrap();
        let write_runtime = |root: &Path, source: &str| {
            std::fs::create_dir_all(root).unwrap();
            std::fs::write(root.join("rescript.json"), include_str!("../../../packages/@rescript/runtime/rescript.json")).unwrap();
            std::fs::write(root.join("A.res"), source).unwrap();
            std::fs::write(root.join("A.resi"), "let a: int").unwrap();
            vec![("A".to_string(), root.join("A.res"))]
        };
        let first = dir.path().join("first");
        let second = dir.path().join("second");
        let first_paths = write_runtime(&first, "let a = 1");
        let second_paths = write_runtime(&second, "let a = 1");
        let digest = sources_digest(&first, &first_paths).unwrap();
        assert_eq!(sources_digest(&second, &second_paths).unwrap(), digest);

        std::fs::remove_file(second.join("rescript.json")).unwrap();
        assert_eq!(sources_digest(&second, &second_paths).unwrap(), digest);
        let mut config: serde_json::Value = serde_json::from_str(include_str!("../../../packages/@rescript/runtime/rescript.json")).unwrap();
        std::fs::write(second.join("rescript.json"), serde_json::to_vec(&config).unwrap()).unwrap();
        assert_eq!(sources_digest(&second, &second_paths).unwrap(), digest);
        config["name"] = serde_json::json!("different-runtime-package");
        std::fs::write(second.join("rescript.json"), serde_json::to_vec(&config).unwrap()).unwrap();
        assert_ne!(sources_digest(&second, &second_paths).unwrap(), digest);
        config["name"] = serde_json::json!("@rescript/runtime");
        config["compiler-flags"] = serde_json::json!(["-nostdlib"]);
        std::fs::write(second.join("rescript.json"), serde_json::to_vec(&config).unwrap()).unwrap();
        assert_ne!(sources_digest(&second, &second_paths).unwrap(), digest);
        std::fs::remove_file(second.join("rescript.json")).unwrap();
        std::fs::write(second.join("A.res"), "let a = 2").unwrap();
        assert_ne!(sources_digest(&second, &second_paths).unwrap(), digest);
        std::fs::write(second.join("A.res"), "let a = 1").unwrap();
        std::fs::remove_file(second.join("A.resi")).unwrap();
        assert_ne!(sources_digest(&second, &second_paths).unwrap(), digest);
    }
}

/// One runtime package attachment, not one entry per module.
struct RuntimePackage {
    index: &'static PackageIndex<'static>,
    root: PathBuf,
}

impl rescript_compiler::cmi::persistent_env::SnapshotModules for RuntimePackage {
    /// O(1), no module index access.
    fn is_runtime(&self) -> bool { true }

    /// O(log module count), borrowed name comparisons, no allocation.
    fn find(&self, name: &str) -> Option<u32> {
        self.index.lookup(name).and_then(|slot| u32::try_from(slot).ok())
    }

    /// O(core bytes + filename bytes), allocating only the requested core.
    fn decode(&self, slot: u32) -> Option<stored_module::StoredCore> {
        let (_, bytes) = self.index.module(slot as usize)?;
        let mut core = stored_module::decode_core(bytes)?;
        core.rebase_paths(Path::new(self.index.recorded_root), &self.root);
        Some(core)
    }
}

/// Build-specific package fields. One allocation per selected package; module
/// names and cores remain in the executable until a lookup requests a slot.
struct BeltPackage {
    index: &'static PackageIndex<'static>,
    package: packages::Package,
    root_config: crate::config::Config,
}

impl rescript_compiler::cmi::persistent_env::SnapshotModules for BeltPackage {
    fn find(&self, name: &str) -> Option<u32> {
        self.index.lookup(name).and_then(|slot| u32::try_from(slot).ok())
    }

    fn decode(&self, slot: u32) -> Option<stored_module::StoredCore> {
        let (_, bytes) = self.index.module(slot as usize)?;
        let mut core = stored_module::decode_core(bytes)?;
        core.rebase_paths(Path::new(self.index.recorded_root), &self.package.path);
        compile::configure_snapshot_module(&mut core.info, &self.package, &self.root_config);
        Some(core)
    }
}

/// Select Belt once per build: O(source bytes) verification, one package clone
/// and one registry attachment. No core is read or copied by this operation.
pub(crate) fn prepare_belt(state: &mut super::build_types::BuildCommandState) -> Result<()> {
    if state.revoked_snapshots[1] { return Ok(()); }
    if state.source_map_command == crate::config::SourceMapCommand::Watch
        && !state.diagnostic_locations
        && state.packages.get("@rescript/belt").is_some_and(|package| package.prebuilt)
    { return Ok(()); }
    if let Some(package) = state.build_state.packages.get_mut("@rescript/belt") { package.prebuilt = false; }
    let Some(package) = state.packages.get("@rescript/belt") else { return Ok(()); };
    if package.is_root { return Ok(()); }
    let mode = std::env::var("RESCRIPT_SNAPSHOT").unwrap_or_default();
    anyhow::ensure!(matches!(mode.as_str(), "" | "off" | "require"),
        "RESCRIPT_SNAPSHOT must be off or require (or unset)");
    let mismatch = |reason: &str| -> Result<()> {
        fallback("@rescript/belt", &mode, reason).map(|_| ())
    };
    if mode == "off" { return mismatch("disabled by RESCRIPT_SNAPSHOT=off"); }
    if state.diagnostic_locations { return mismatch("the diagnostic retry requires source declaration locations"); }
    if state.dump.is_some() { return mismatch("dump flags are not supported"); }
    if let Some(option) = alternate_backend_option() { return mismatch(option); }
    if std::env::var_os("RESCRIPT_FULL_BUILD").is_some() {
        return mismatch("RESCRIPT_FULL_BUILD is enabled");
    }
    if !state.get_root_config().get_source_map_args(state.source_map_command).is_empty() {
        return mismatch("source maps are not supported");
    }
    let Some(index) = EMBEDDED.get().and_then(Option::as_ref)
        .and_then(|packages| packages.iter().find(|p| p.name == "@rescript/belt"))
    else { return mismatch("the snapshot is absent"); };
    if package.modules.as_ref().is_none_or(|modules| modules.len() != index.len()
        || modules.iter().any(|name| index.lookup(name).is_none()))
        || package.source_files.as_ref().is_none_or(|files|
            files.keys().any(|path| path.parent() != Some(Path::new("src"))))
    { return mismatch("its source layout differs from the snapshot"); }
    let mut paths: Vec<_> = package.source_files.as_ref().expect("validated source files")
        .keys().map(|path| package.path.join(path)).collect();
    paths.sort_unstable();
    paths.push(package.path.join("rescript.json"));
    paths.push(package.path.join("bsconfig.json"));
    if !verified(index.sources_digest, &paths, compile::RuntimeStore::of_build(state).as_ref(),
        "belt", || belt_sources_digest(&package.path))? {
        return mismatch("its sources differ from the ones this compiler was built with");
    }
    let provider = std::sync::Arc::new(BeltPackage {
        index, package: package.clone(), root_config: state.get_root_config().clone(),
    });
    // A check writes no files.
    if !state.check_only { provider.write_javascript()?; }
    state.module_registry.lock().unwrap().register_snapshot(provider);
    state.build_state.packages.get_mut("@rescript/belt").unwrap().prebuilt = true;
    Ok(())
}

/// Clear scheduling flags after the normal incremental plan seeds them.
/// O(module count), no core lookup, allocation or source-file access.
pub(crate) fn suppress_prebuilt_parses(state: &mut super::build_types::BuildCommandState) {
    if !state.packages.get("@rescript/belt").is_some_and(|package| package.prebuilt) { return; }
    for module in state.build_state.modules.values_mut() {
        if state.build_state.packages[&module.package_name].prebuilt {
            module.compile_dirty = false;
            module.deps_dirty = false;
            if let super::build_types::SourceType::SourceFile(source) = &mut module.source_type {
                source.implementation.parse_dirty = false;
                if let Some(interface) = &mut source.interface { interface.parse_dirty = false; }
            }
        }
    }
}

impl BeltPackage {
    /// O(emitted JavaScript bytes + slot count + output file count). Only this
    /// output pass visits all module records; it never touches their cores.
    fn write_javascript(&self) -> Result<()> {
        for slot in 0..self.index.len() {
            let name = std::str::from_utf8(self.index.blob(slot, 0, 1).ok_or_else(|| anyhow!("invalid snapshot module name"))?)?;
            let source = PathBuf::from("src").join(format!("{name}.res"));
            let targets = compile::js_output_targets_for_source(&self.package, &source, &self.root_config);
            for (target, spec) in targets.iter().zip(self.root_config.get_package_specs()) {
                let format = match spec.module {
                    crate::config::PackageModule::EsModule => 0,
                    crate::config::PackageModule::CommonJs => 1,
                };
                let text = self.index.blob(slot, 16 + format * 8, 1).ok_or_else(|| anyhow!("invalid snapshot JavaScript"))?;
                let positions = self.index.blob(slot, 32 + format * 8, 4).ok_or_else(|| anyhow!("invalid snapshot slots"))?;
                let slots = positions.chunks_exact(4).map(|bytes| u32::from_le_bytes(bytes.try_into().unwrap()));
                let output = render_template(text, slots, self.root_config.get_suffix(&spec).as_bytes())?;
                if std::fs::read(&target.path).ok().as_deref() == Some(output.as_slice()) { continue; }
                std::fs::create_dir_all(target.path.parent().expect("JavaScript output parent"))?;
                std::fs::write(&target.path, output)?;
            }
        }
        Ok(())
    }
}

/// O(1) option selection, once for a Belt package, not per module or lookup.
fn alternate_backend_option() -> Option<&'static str> {
    if std::env::var("RESCRIPT_JS_PRINTER").as_deref() == Ok("oxc") {
        Some("RESCRIPT_JS_PRINTER=oxc is not supported")
    } else if matches!(std::env::var("RESCRIPT_BACKEND").as_deref(), Ok("new" | "check")) {
        Some("RESCRIPT_BACKEND is not supported")
    } else { None }
}

/// Watch-only directory index. The two snapshot layouts are flat: runtime's
/// root and Belt's `src`. Paths have no dense compiler handle, hence this map.
/// It is constructed once per session; ordinary events do one borrowed lookup,
/// O(path bytes) hashing, with no allocation, filesystem access, locks or atomics.
pub(crate) struct WatchSources {
    directories: std::collections::HashMap<PathBuf, usize>,
    roots: [Option<PathBuf>; 2],
    #[cfg(test)]
    lookups: std::cell::Cell<usize>,
}

impl WatchSources {
    /// O(1) package lookups and two path clones/joins; no module walk.
    pub(crate) fn new(state: &super::build_types::BuildCommandState) -> Self {
        let runtime = state.compiler_info.runtime_path.clone();
        let belt = state.packages.get("@rescript/belt").filter(|p| !p.is_root).map(|p| p.path.clone());
        let mut directories = std::collections::HashMap::new();
        directories.insert(runtime.clone(), 0);
        if let Some(root) = &belt { directories.insert(root.join("src"), 1); }
        Self { directories, roots: [Some(runtime), belt], #[cfg(test)] lookups: std::cell::Cell::new(0) }
    }

    /// Exactly one directory-table lookup, O(path bytes), no allocation or I/O.
    fn package(&self, path: &Path) -> Option<usize> {
        let parent = path.parent()?;
        #[cfg(test)]
        self.lookups.set(self.lookups.get() + 1);
        self.directories.get(parent).copied()
    }

    /// O(path bytes) for an unrelated path. For a snapshot source event only,
    /// reuse B.5's source/options digest (O(package source bytes)); byte-identical
    /// touches retain the snapshot. A mismatch requests the existing full-build
    /// path, which drops the old registry and recompiles all dependents. Already
    /// revoked packages also rebuild on edits, including runtime-only edits.
    pub(crate) fn changed(&self, path: &Path, state: &mut super::build_types::BuildCommandState) -> bool {
        let Some(package) = self.package(path) else { return false; };
        if state.revoked_snapshots[package] { return true; }
        let root = self.roots[package].as_deref().expect("indexed package root");
        let name = ["@rescript/runtime", "@rescript/belt"][package];
        let expected = EMBEDDED.get().and_then(Option::as_ref)
            .and_then(|indexes| indexes.iter().find(|index| index.name == name));
        let actual = if package == 0 {
            compile::runtime_source_paths(root).and_then(|paths| sources_digest(root, &paths))
        } else {
            belt_sources_digest(root)
        };
        if expected.zip(actual.ok()).is_some_and(|(index, digest)| index.sources_digest == digest) {
            log::info!("Keeping the prebuilt {name}: its sources are unchanged.");
            return false;
        }
        state.revoked_snapshots[package] = true;
        log::info!("Not using the prebuilt {name}: its sources differ from the ones this compiler was built with. Compiling it from source for the rest of this watch session.");
        true
    }
}

#[cfg(test)]
mod watch_source_tests {
    use super::*;

    #[test]
    fn unrelated_events_do_exactly_one_lookup_each() {
        let sources = WatchSources {
            directories: [(PathBuf::from("/runtime"), 0), (PathBuf::from("/belt/src"), 1)].into(),
            roots: [Some(PathBuf::from("/runtime")), Some(PathBuf::from("/belt"))],
            lookups: std::cell::Cell::new(0),
        };
        for index in 0..10_000 {
            assert_eq!(sources.package(Path::new(&format!("/project/src/Module{index}.res"))), None);
        }
        assert_eq!(sources.lookups.get(), 10_000);
        assert_eq!(sources.package(Path::new("/belt/src/Belt_Array.res")), Some(1));
        assert_eq!(sources.package(Path::new("/runtime/Stdlib_List.res")), Some(0));
        assert_eq!(sources.lookups.get(), 10_002);
    }
}
