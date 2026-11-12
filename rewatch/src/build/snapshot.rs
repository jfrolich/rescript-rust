//! The runtime compiled into the executable.
//!
//! Every process that compiles anything needs `@rescript/runtime` compiled
//! into its module registry, and the runtime that ships with a compiler is
//! always the same. So the `rescript` executable's build script compiles the
//! runtime in the repository with [`compile`] and the executable hands the
//! result to [`install`]: a build whose runtime has the same sources then
//! registers these interfaces, borrowed from the executable's memory and
//! decoded on first lookup, instead of compiling the runtime.
//!
//! A runtime with other sources (one being edited, or another version) is
//! compiled as before. The embedded interfaces record the source paths of the
//! repository they were compiled in, as the `.cmi` files of a published
//! runtime record those of the machine that built it; JavaScript imports of
//! runtime modules do not depend on them.

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
struct PackageIndex {
    bytes: &'static [u8],
    name: &'static str,
    recorded_root: &'static str,
    sources_digest: blake3::Hash,
    records: &'static [u8],
}

static EMBEDDED: OnceLock<Option<Vec<PackageIndex>>> = OnceLock::new();

/// Install the package headers in O(package count), allocating only the package
/// table. Module records and blobs remain borrowed and untouched.
pub fn install(bytes: &'static [u8]) {
    let _ = EMBEDDED.set(decode(bytes));
}

/// Compile the runtime package at `runtime_root` from its sources there, as
/// [`install`] takes it.
pub fn compile(runtime_root: &Path) -> Result<Vec<u8>> {
    let runtime_root = runtime_root.to_path_buf();
    // Like a build's runtime pre-compilation, on a thread with a large stack.
    std::thread::Builder::new()
        .name("rescript-embed-runtime".to_string())
        .stack_size(256 * 1024 * 1024)
        .spawn(move || compile_on_this_thread(&runtime_root))
        .context("failed to spawn the runtime compile thread")?
        .join()
        .map_err(|_| anyhow!("compiling the runtime panicked"))?
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
        Ok(ProducedModule { name, core: core.to_vec(), javascript: Default::default(), slots: Default::default() })
    }).collect::<Result<Vec<_>>>()?;
    encode(&[ProducedPackage {
        name: "@rescript/runtime".into(),
        recorded_root: runtime_root.to_string_lossy().into_owned(),
        sources_digest: digest,
        modules,
    }])
}

/// Register the embedded runtime in `registry` if `runtime_paths` (module
/// name, `.res` path), with the configuration at `runtime_root`, are the
/// sources it was compiled from. Returns whether it did.
pub(crate) fn register(
    registry: &Mutex<ModuleRegistry>,
    runtime_root: &Path,
    runtime_paths: &[(String, PathBuf)],
) -> bool {
    let Some(Some(embedded)) = EMBEDDED.get() else {
        return false;
    };
    let Some(embedded) = embedded.iter().find(|package| package.name == "@rescript/runtime") else {
        return false;
    };
    if embedded.len() != runtime_paths.len()
        || sources_digest(runtime_root, runtime_paths).ok() != Some(embedded.sources_digest)
    {
        log::debug!(
            "The runtime at {} is not the embedded one",
            runtime_root.display()
        );
        return false;
    }
    let mut registry = registry.lock().unwrap();
    (0..embedded.len()).all(|slot| {
        let Some((name, core)) = embedded.module(slot) else { return false; };
        registry.register_stored_parts(name, None, PendingCore::Bytes(core.into())).is_some()
    })
}

/// A digest of the runtime's configuration and of every source's module name
/// and contents (not its path: an installed runtime keeps copies of the
/// sources elsewhere).
fn sources_digest(runtime_root: &Path, runtime_paths: &[(String, PathBuf)]) -> std::io::Result<blake3::Hash> {
    let mut hasher = blake3::Hasher::new();
    let mut add = |bytes: &[u8]| {
        hasher.update(&(bytes.len() as u64).to_le_bytes());
        hasher.update(bytes);
    };
    add(&std::fs::read(runtime_root.join("rescript.json"))?);
    for (module_name, path) in runtime_paths {
        add(module_name.as_bytes());
        add(&std::fs::read(path)?);
        match std::fs::read(path.with_extension("resi")) {
            Ok(interface) => {
                add(b"resi");
                add(&interface);
            }
            Err(err) if err.kind() == std::io::ErrorKind::NotFound => add(b""),
            Err(err) => return Err(err),
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

impl PackageIndex {
    /// O(1), no allocation.
    fn len(&self) -> usize { self.records.len() / RECORD_BYTES }

    /// O(1), borrowing one indexed blob with checked bounds. Slot counts use
    /// four-byte elements; names, cores and JavaScript use one-byte elements.
    fn blob(&self, slot: usize, field: usize, element_bytes: usize) -> Option<&'static [u8]> {
        let start = slot.checked_mul(RECORD_BYTES)?.checked_add(field)?;
        let record = self.records.get(start..start.checked_add(8)?)?;
        let offset = u32::from_le_bytes(record[..4].try_into().ok()?) as usize;
        let count = u32::from_le_bytes(record[4..].try_into().ok()?) as usize;
        self.bytes.get(offset..offset.checked_add(count.checked_mul(element_bytes)?)?)
    }

    /// O(name bytes) UTF-8 validation and O(1) core borrowing; no allocation.
    fn module(&self, slot: usize) -> Option<(&'static str, &'static [u8])> {
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
fn decode(bytes: &'static [u8]) -> Option<Vec<PackageIndex>> {
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
struct Reader(&'static [u8]);

impl Reader {
    /// O(1), checked slice split, no allocation.
    fn take(&mut self, len: usize) -> Option<&'static [u8]> {
        let (head, rest) = self.0.split_at_checked(len)?;
        self.0 = rest;
        Some(head)
    }
    /// O(1), four bytes read.
    fn u32(&mut self) -> Option<u32> {
        Some(u32::from_le_bytes(self.take(4)?.try_into().ok()?))
    }
    /// O(1), borrow a length-prefixed byte string without copying.
    fn part(&mut self) -> Option<&'static [u8]> {
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
    fn sources_digest_ignores_paths_but_not_contents() {
        let dir = tempfile::tempdir().unwrap();
        let write_runtime = |root: &Path, source: &str| {
            std::fs::create_dir_all(root).unwrap();
            std::fs::write(root.join("rescript.json"), "{}").unwrap();
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

        std::fs::write(second.join("A.res"), "let a = 2").unwrap();
        assert_ne!(sources_digest(&second, &second_paths).unwrap(), digest);
        std::fs::write(second.join("A.res"), "let a = 1").unwrap();
        std::fs::remove_file(second.join("A.resi")).unwrap();
        assert_ne!(sources_digest(&second, &second_paths).unwrap(), digest);
    }
}
