//! Serves the typed artifacts of a watch session to editor tooling.
//!
//! In-process builds write no `.cmi`/`.cmt`/`.cmti` files. A watcher keeps
//! them in a [`TypedArtifactStore`] and answers requests for them on a local
//! TCP port, so editor tooling (the analysis binary) reads them from memory.
//!
//! Discovery: `lib/rescript-watch.addr` in the watched project holds
//! `<host:port> <token>`. Only the owner can read it, and every connection
//! must present the token first.
//!
//! Protocol (one request per line, any number per connection):
//! - `AUTH <token>` → `OK 0`
//! - `GET <absolute artifact path>` → `OK <length>` followed by the bytes,
//!   or `MISSING`
//! - `LIST` → `OK <length>` followed by the newline-separated artifact paths

use crate::build::build_types::TypedArtifactStore;
use std::hash::{BuildHasher, Hasher};
use std::io::{BufRead, BufReader, Write};
use std::net::{TcpListener, TcpStream};
use std::path::{Path, PathBuf};

/// Name of the discovery file in the project's `lib` directory.
pub const ADDRESS_FILE: &str = "rescript-watch.addr";

/// A running server. Dropping it removes the discovery file; the listener
/// thread ends with the process.
pub struct ToolingServer {
    address_file: PathBuf,
}

impl Drop for ToolingServer {
    fn drop(&mut self) {
        let _ = std::fs::remove_file(&self.address_file);
    }
}

fn random_token() -> String {
    // `RandomState` is seeded from the operating system's randomness.
    let a = std::collections::hash_map::RandomState::new()
        .build_hasher()
        .finish();
    let b = std::collections::hash_map::RandomState::new()
        .build_hasher()
        .finish();
    format!("{a:016x}{b:016x}")
}

fn write_address_file(path: &Path, content: &str) -> std::io::Result<()> {
    if let Some(parent) = path.parent() {
        std::fs::create_dir_all(parent)?;
    }
    let mut options = std::fs::OpenOptions::new();
    options.write(true).create(true).truncate(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt;
        options.mode(0o600);
    }
    let mut file = options.open(path)?;
    file.write_all(content.as_bytes())
}

/// Start serving `store` for the project at `project_root`.
pub fn start(project_root: &Path, store: TypedArtifactStore) -> std::io::Result<ToolingServer> {
    let listener = TcpListener::bind(("127.0.0.1", 0))?;
    let address = listener.local_addr()?;
    let token = random_token();
    let address_file = project_root.join("lib").join(ADDRESS_FILE);
    write_address_file(&address_file, &format!("{address} {token}\n"))?;
    std::thread::Builder::new()
        .name("rewatch-tooling-server".to_string())
        .spawn(move || {
            for stream in listener.incoming().flatten() {
                let store = store.clone();
                let token = token.clone();
                let _ = std::thread::Builder::new()
                    .name("rewatch-tooling-connection".to_string())
                    .spawn(move || {
                        let _ = serve_connection(stream, &store, &token);
                    });
            }
        })?;
    Ok(ToolingServer { address_file })
}

/// The stored artifact for `path`. Tooling may name the project through a
/// different spelling (e.g. a symlink), so fall back to the canonical form of
/// the nearest existing ancestor.
fn lookup(store: &TypedArtifactStore, path: &Path) -> Option<std::sync::Arc<Vec<u8>>> {
    if let Some(bytes) = store.get(path) {
        return Some(bytes);
    }
    let mut existing = path;
    let mut rest = Vec::new();
    while !existing.exists() {
        rest.push(existing.file_name()?);
        existing = existing.parent()?;
    }
    let mut canonical = existing.canonicalize().ok()?;
    for part in rest.iter().rev() {
        canonical.push(part);
    }
    store.get(&canonical)
}

fn send(stream: &mut TcpStream, payload: &[u8]) -> std::io::Result<()> {
    stream.write_all(format!("OK {}\n", payload.len()).as_bytes())?;
    stream.write_all(payload)
}

fn serve_connection(stream: TcpStream, store: &TypedArtifactStore, token: &str) -> std::io::Result<()> {
    let mut writer = stream.try_clone()?;
    let mut reader = BufReader::new(stream);
    let mut authenticated = false;
    let mut line = String::new();
    loop {
        line.clear();
        if reader.read_line(&mut line)? == 0 {
            return Ok(());
        }
        let request = line.trim_end_matches(['\r', '\n']);
        let (command, argument) = request.split_once(' ').unwrap_or((request, ""));
        if !authenticated {
            if command == "AUTH" && argument == token {
                authenticated = true;
                send(&mut writer, b"")?;
                continue;
            }
            writer.write_all(b"DENIED\n")?;
            return Ok(());
        }
        match command {
            "GET" => match lookup(store, Path::new(argument)) {
                Some(bytes) => send(&mut writer, &bytes)?,
                None => writer.write_all(b"MISSING\n")?,
            },
            "LIST" => {
                let listing: String = store
                    .paths()
                    .iter()
                    .map(|path| format!("{}\n", path.display()))
                    .collect();
                send(&mut writer, listing.as_bytes())?;
            }
            _ => writer.write_all(b"ERROR unknown command\n")?,
        }
        writer.flush()?;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Read;

    fn request(stream: &mut TcpStream, reader: &mut BufReader<TcpStream>, line: &str) -> Option<Vec<u8>> {
        stream.write_all(format!("{line}\n").as_bytes()).unwrap();
        let mut header = String::new();
        reader.read_line(&mut header).unwrap();
        let length: usize = header.trim().strip_prefix("OK ")?.parse().unwrap();
        let mut bytes = vec![0; length];
        reader.read_exact(&mut bytes).unwrap();
        Some(bytes)
    }

    #[test]
    fn serves_stored_artifacts_after_authentication() {
        let project = tempfile::tempdir().unwrap();
        let store = TypedArtifactStore::default();
        let cmt = project.path().join("lib/bs/src/Foo.cmt");
        store.insert(cmt.clone(), b"cmt bytes".to_vec());
        let server = start(project.path(), store).unwrap();

        let address_file = project.path().join("lib").join(ADDRESS_FILE);
        let content = std::fs::read_to_string(&address_file).unwrap();
        let (address, token) = content.trim().split_once(' ').unwrap();

        let mut denied = TcpStream::connect(address).unwrap();
        let mut denied_reader = BufReader::new(denied.try_clone().unwrap());
        assert_eq!(request(&mut denied, &mut denied_reader, "GET /x"), None);

        let mut stream = TcpStream::connect(address).unwrap();
        let mut reader = BufReader::new(stream.try_clone().unwrap());
        assert_eq!(
            request(&mut stream, &mut reader, &format!("AUTH {token}")),
            Some(vec![])
        );
        assert_eq!(
            request(&mut stream, &mut reader, &format!("GET {}", cmt.display())),
            Some(b"cmt bytes".to_vec())
        );
        assert_eq!(
            request(
                &mut stream,
                &mut reader,
                &format!("GET {}", project.path().join("lib/bs/src/Bar.cmt").display())
            ),
            None
        );
        assert_eq!(
            request(&mut stream, &mut reader, "LIST"),
            Some(format!("{}\n", cmt.display()).into_bytes())
        );

        drop(server);
        assert!(!address_file.exists());
    }
}
