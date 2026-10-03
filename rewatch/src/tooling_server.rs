//! Runs editor tooling commands inside a watch session.
//!
//! Builds write no `.cmi`/`.cmt`/`.cmti` files and keep only the published
//! interfaces in memory. Editor tooling therefore runs inside the watcher
//! (`build::tooling`), on the Rust typed tree of modules type-checked on
//! demand; a client forwards each command to it.
//!
//! Discovery: `lib/rescript-watch.addr` in the watched project holds
//! `<host:port> <token>`. Only the owner can read it, and every connection
//! must present the token first. The watcher writes it once the initial
//! build has finished.
//!
//! Protocol (one request per line, any number per connection):
//! - `AUTH <token>` → `OK 0`
//! - `RUN <JSON array of the command's arguments>` → `OK <length>` followed
//!   by what the command prints, or `ERROR <length>` followed by why it failed

use std::hash::{BuildHasher, Hasher};
use std::io::{BufRead, BufReader, Write};
use std::net::{TcpListener, TcpStream};
use std::path::{Path, PathBuf};
use std::sync::mpsc;

/// Name of the discovery file in the project's `lib` directory.
pub const ADDRESS_FILE: &str = "rescript-watch.addr";

/// What tooling asks for.
#[derive(Debug, Clone, PartialEq)]
pub enum Request {
    /// Run a command with these arguments (as given to the analysis binary).
    Run(Vec<String>),
}

/// The watcher's answer to a [`Request`].
#[derive(Debug, Clone, PartialEq)]
pub enum Reply {
    /// What the command prints.
    Output(String),
    Error(String),
}

/// A request waiting for the watch loop, which owns the build state.
pub struct ToolingRequest {
    pub request: Request,
    pub reply: mpsc::Sender<Reply>,
}

/// A running server. Dropping it removes the discovery file; the listener
/// thread ends with the process.
pub struct ToolingServer {
    address_file: PathBuf,
    address: String,
}

impl ToolingServer {
    /// Write the discovery file, announcing the server to tooling.
    pub fn publish(&self) -> std::io::Result<()> {
        write_address_file(&self.address_file, &self.address)
    }
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

/// Start a server for the project at `project_root`. Requests arrive on the
/// returned receiver; the watch loop answers them.
pub fn start(project_root: &Path) -> std::io::Result<(ToolingServer, mpsc::Receiver<ToolingRequest>)> {
    let listener = TcpListener::bind(("127.0.0.1", 0))?;
    let address = listener.local_addr()?;
    let token = random_token();
    let address_file = project_root.join("lib").join(ADDRESS_FILE);
    let address = format!("{address} {token}\n");
    let (requests, receiver) = mpsc::channel();
    std::thread::Builder::new()
        .name("rewatch-tooling-server".to_string())
        .spawn(move || {
            for stream in listener.incoming().flatten() {
                let requests = requests.clone();
                let token = token.clone();
                let _ = std::thread::Builder::new()
                    .name("rewatch-tooling-connection".to_string())
                    .spawn(move || {
                        let _ = serve_connection(stream, &requests, &token);
                    });
            }
        })?;
    Ok((
        ToolingServer {
            address_file,
            address,
        },
        receiver,
    ))
}

fn send(stream: &mut TcpStream, status: &str, payload: &[u8]) -> std::io::Result<()> {
    stream.write_all(format!("{status} {}\n", payload.len()).as_bytes())?;
    stream.write_all(payload)
}

fn serve_connection(
    stream: TcpStream,
    requests: &mpsc::Sender<ToolingRequest>,
    token: &str,
) -> std::io::Result<()> {
    let mut writer = stream.try_clone()?;
    let mut reader = BufReader::new(stream);
    let mut authenticated = false;
    let mut line = String::new();
    loop {
        line.clear();
        if reader.read_line(&mut line)? == 0 {
            return Ok(());
        }
        let line = line.trim_end_matches(['\r', '\n']);
        let (command, argument) = line.split_once(' ').unwrap_or((line, ""));
        if !authenticated {
            if command == "AUTH" && argument == token {
                authenticated = true;
                send(&mut writer, "OK", b"")?;
                continue;
            }
            writer.write_all(b"DENIED\n")?;
            return Ok(());
        }
        let request = match (command, serde_json::from_str::<Vec<String>>(argument)) {
            ("RUN", Ok(args)) => Request::Run(args),
            ("RUN", Err(err)) => {
                send(
                    &mut writer,
                    "ERROR",
                    format!("invalid arguments: {err}").as_bytes(),
                )?;
                continue;
            }
            _ => {
                send(&mut writer, "ERROR", b"unknown request")?;
                continue;
            }
        };
        let (reply, answer) = mpsc::channel();
        let reply = if requests.send(ToolingRequest { request, reply }).is_ok() {
            answer
                .recv()
                .unwrap_or(Reply::Error("the watcher stopped".to_string()))
        } else {
            Reply::Error("the watcher stopped".to_string())
        };
        match reply {
            Reply::Output(output) => send(&mut writer, "OK", output.as_bytes())?,
            Reply::Error(message) => send(&mut writer, "ERROR", message.as_bytes())?,
        }
        writer.flush()?;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Read;

    fn request(stream: &mut TcpStream, reader: &mut BufReader<TcpStream>, line: &str) -> String {
        stream.write_all(format!("{line}\n").as_bytes()).unwrap();
        let mut header = String::new();
        reader.read_line(&mut header).unwrap();
        let header = header.trim().to_string();
        match header.split_once(' ') {
            Some((status, length)) => {
                let mut bytes = vec![0; length.parse().unwrap()];
                reader.read_exact(&mut bytes).unwrap();
                format!("{status} {}", String::from_utf8(bytes).unwrap())
            }
            None => header,
        }
    }

    #[test]
    fn forwards_authenticated_requests_to_the_watch_loop() {
        let project = tempfile::tempdir().unwrap();
        let (server, requests) = start(project.path()).unwrap();
        server.publish().unwrap();
        std::thread::spawn(move || {
            for ToolingRequest { request, reply } in requests {
                let Request::Run(args) = request;
                let _ = reply.send(match args.first().map(String::as_str) {
                    Some("echo") => Reply::Output(args[1..].join(" ")),
                    _ => Reply::Error("unknown".to_string()),
                });
            }
        });

        let address_file = project.path().join("lib").join(ADDRESS_FILE);
        let content = std::fs::read_to_string(&address_file).unwrap();
        let (address, token) = content.trim().split_once(' ').unwrap();

        let mut denied = TcpStream::connect(address).unwrap();
        let mut denied_reader = BufReader::new(denied.try_clone().unwrap());
        assert_eq!(request(&mut denied, &mut denied_reader, "RUN []"), "DENIED");

        let mut stream = TcpStream::connect(address).unwrap();
        let mut reader = BufReader::new(stream.try_clone().unwrap());
        assert_eq!(request(&mut stream, &mut reader, &format!("AUTH {token}")), "OK ");
        assert_eq!(
            request(&mut stream, &mut reader, r#"RUN ["echo","a b","c"]"#),
            "OK a b c"
        );
        assert_eq!(
            request(&mut stream, &mut reader, r#"RUN ["nope"]"#),
            "ERROR unknown"
        );
        assert!(request(&mut stream, &mut reader, "RUN nope").starts_with("ERROR invalid arguments"));

        drop(server);
        assert!(!address_file.exists());
    }
}
