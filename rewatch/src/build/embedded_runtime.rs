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
use rescript_compiler::cmi::persistent_env::ModuleRegistry;
use std::path::{Path, PathBuf};
use std::sync::{Mutex, OnceLock};

/// The first bytes of an embedded runtime.
const MAGIC: &[u8; 8] = b"RESRT001";

/// The digest of the runtime sources and the interfaces compiled from them.
struct EmbeddedRuntime {
    sources_digest: blake3::Hash,
    interfaces: Vec<(&'static str, &'static [u8])>,
}

static EMBEDDED: OnceLock<Option<EmbeddedRuntime>> = OnceLock::new();

/// Use `bytes`, a runtime [`compile`]d into the executable, for builds of
/// the same runtime. Empty or malformed bytes embed nothing. Call once at
/// process start; later calls are ignored.
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
    let (modules, aliases) =
        compile::compile_runtime_sources(&registry, runtime_root, runtime_root, &config, paths)?;
    let interfaces = compile::encode_runtime_interfaces(&registry, &modules, aliases)
        .ok_or_else(|| anyhow!("a compiled runtime module is missing from the registry"))?;
    Ok(encode(&digest, &interfaces))
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
    if embedded.interfaces.len() != runtime_paths.len()
        || sources_digest(runtime_root, runtime_paths).ok() != Some(embedded.sources_digest)
    {
        log::debug!(
            "The runtime at {} is not the embedded one",
            runtime_root.display()
        );
        return false;
    }
    let mut registry = registry.lock().unwrap();
    embedded
        .interfaces
        .iter()
        .all(|(module, data)| registry.register_stored_static(module, data).is_some())
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

/// [`MAGIC`], the sources digest, the number of modules, then each module's
/// name and data, each preceded by its length as a little-endian `u32`.
fn encode(sources_digest: &blake3::Hash, interfaces: &[(String, Vec<u8>)]) -> Vec<u8> {
    let mut bytes = Vec::new();
    bytes.extend_from_slice(MAGIC);
    bytes.extend_from_slice(sources_digest.as_bytes());
    bytes.extend_from_slice(&(interfaces.len() as u32).to_le_bytes());
    for (module, data) in interfaces {
        for part in [module.as_bytes(), data] {
            bytes.extend_from_slice(&(part.len() as u32).to_le_bytes());
            bytes.extend_from_slice(part);
        }
    }
    bytes
}

fn decode(bytes: &'static [u8]) -> Option<EmbeddedRuntime> {
    let mut reader = Reader(bytes.strip_prefix(MAGIC.as_slice())?);
    let sources_digest = blake3::Hash::from_bytes(reader.take(32)?.try_into().ok()?);
    let count = reader.u32()?;
    let mut interfaces = Vec::with_capacity(count as usize);
    for _ in 0..count {
        let module = std::str::from_utf8(reader.part()?).ok()?;
        interfaces.push((module, reader.part()?));
    }
    (!interfaces.is_empty() && reader.0.is_empty()).then_some(EmbeddedRuntime {
        sources_digest,
        interfaces,
    })
}

/// The bytes of an embedded runtime not read yet.
struct Reader(&'static [u8]);

impl Reader {
    fn take(&mut self, len: usize) -> Option<&'static [u8]> {
        let (head, rest) = self.0.split_at_checked(len)?;
        self.0 = rest;
        Some(head)
    }

    fn u32(&mut self) -> Option<u32> {
        Some(u32::from_le_bytes(self.take(4)?.try_into().ok()?))
    }

    fn part(&mut self) -> Option<&'static [u8]> {
        let len = self.u32()? as usize;
        self.take(len)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn interfaces() -> Vec<(String, Vec<u8>)> {
        vec![
            ("Pervasives".to_string(), vec![1, 2, 3]),
            ("Stdlib".to_string(), Vec::new()),
        ]
    }

    fn leak(bytes: Vec<u8>) -> &'static [u8] {
        Box::leak(bytes.into_boxed_slice())
    }

    #[test]
    fn decodes_what_it_encodes() {
        let digest = blake3::hash(b"sources");
        let decoded = decode(leak(encode(&digest, &interfaces()))).unwrap();
        assert_eq!(decoded.sources_digest, digest);
        assert_eq!(
            decoded.interfaces,
            vec![("Pervasives", &[1u8, 2, 3][..]), ("Stdlib", &[][..])]
        );
    }

    #[test]
    fn rejects_empty_truncated_and_trailing_bytes() {
        assert!(decode(&[]).is_none());
        let bytes = encode(&blake3::hash(b"sources"), &interfaces());
        for len in 0..bytes.len() {
            assert!(
                decode(leak(bytes[..len].to_vec())).is_none(),
                "prefix of {len} bytes"
            );
        }
        let mut longer = bytes.clone();
        longer.push(0);
        assert!(decode(leak(longer)).is_none());
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
