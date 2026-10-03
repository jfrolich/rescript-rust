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

/// Exit code of a client when no watcher serves the project
/// (sysexits.h `EX_UNAVAILABLE`).
pub const NO_WATCHER_EXIT_CODE: i32 = 69;

/// The discovery file of the watcher governing `dir`: the nearest
/// `lib/rescript-watch.addr` in `dir` or an ancestor.
fn find_address_file(dir: &Path) -> Option<PathBuf> {
    dir.ancestors()
        .map(|dir| dir.join("lib").join(ADDRESS_FILE))
        .find(|candidate| candidate.is_file())
}

/// Where to look for the watcher: the directory of the first argument that
/// names an existing file, else `cwd`.
fn client_start_dir(cwd: &Path, args: &[String]) -> PathBuf {
    args.iter()
        .skip(1)
        .map(|arg| cwd.join(arg))
        .find(|path| path.is_file())
        .and_then(|path| path.parent().map(Path::to_path_buf))
        .unwrap_or_else(|| cwd.to_path_buf())
}

fn read_reply(reader: &mut BufReader<TcpStream>) -> std::io::Result<Reply> {
    use std::io::Read;
    let mut header = String::new();
    reader.read_line(&mut header)?;
    let header = header.trim_end();
    let Some((status, length)) = header.split_once(' ') else {
        return Ok(Reply::Error(format!("unexpected reply: {header}")));
    };
    let length: usize = length
        .parse()
        .map_err(|_| std::io::Error::other(format!("unexpected reply: {header}")))?;
    let mut payload = vec![0; length];
    reader.read_exact(&mut payload)?;
    let payload = String::from_utf8_lossy(&payload).into_owned();
    Ok(match status {
        "OK" => Reply::Output(payload),
        _ => Reply::Error(payload),
    })
}

fn request_from(address_file: &Path, args: &[String]) -> std::io::Result<Reply> {
    let content = std::fs::read_to_string(address_file)?;
    let (address, token) = content
        .trim()
        .split_once(' ')
        .ok_or_else(|| std::io::Error::other("malformed address file"))?;
    let mut stream = TcpStream::connect(address)?;
    let mut reader = BufReader::new(stream.try_clone()?);
    stream.write_all(format!("AUTH {token}\n").as_bytes())?;
    if let Reply::Error(message) = read_reply(&mut reader)? {
        return Err(std::io::Error::other(message));
    }
    let args = serde_json::to_string(args).map_err(std::io::Error::other)?;
    stream.write_all(format!("RUN {args}\n").as_bytes())?;
    read_reply(&mut reader)
}

/// Forward an editor tooling command to the watcher serving the project and
/// print its output. Returns the process exit code.
pub fn run_client(cwd: &Path, args: &[String]) -> i32 {
    let start = client_start_dir(cwd, args);
    let reply = find_address_file(&start).map(|address_file| request_from(&address_file, args));
    match reply {
        Some(Ok(Reply::Output(output))) => {
            print!("{output}");
            0
        }
        Some(Ok(Reply::Error(message))) => {
            eprintln!("{message}");
            1
        }
        None | Some(Err(_)) => {
            eprintln!(
                "No running `rescript watch` serves {}.\n\
                 Editor tooling runs inside the watcher: start it with `rescript watch` in the project root.",
                start.display()
            );
            NO_WATCHER_EXIT_CODE
        }
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

        let args = vec!["echo".to_string(), "hi".to_string()];
        assert_eq!(run_client(project.path(), &args), 0);
        assert_eq!(run_client(project.path(), &["nope".to_string()]), 1);

        drop(server);
        assert!(!address_file.exists());
        assert_eq!(run_client(project.path(), &args), NO_WATCHER_EXIT_CODE);
    }
}
