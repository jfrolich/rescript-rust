use anyhow::Result;
use notify::{Config, Event, EventKind, RecommendedWatcher, RecursiveMode, Watcher};
use std::fs;
use std::fs::OpenOptions;
use std::io::Write;
use std::path::Path;
use std::process;
use std::sync::Arc;
use std::time::{Duration, SystemTime};
use sysinfo::{PidExt, ProcessExt, System, SystemExt};

use crate::queue::FifoQueue;
use crate::queue::*;

/* This locking mechanism is meant to never be deleted. Instead, it stores the PID of the process
 * that's running, when trying to aquire a lock, it checks wether that process is still running. If
 * not, it rewrites the lockfile to have its own PID instead. */

pub enum AwaitLockError {
    Watcher(notify::Error),
    Timeout(String),
}

impl std::fmt::Display for AwaitLockError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        let msg = match self {
            AwaitLockError::Watcher(error) => format!("Error starting file watcher {}", error),
            AwaitLockError::Timeout(path) => format!("Timeout awaiting lockfile {}", path),
        };
        write!(f, "{msg}")
    }
}

pub enum Error {
    Locked(u32),
    AwaitingLockFile(AwaitLockError),
    ParsingLockfile(std::num::ParseIntError),
    ReadingLockfile(LockKind, std::io::Error),
    WritingLockfile(std::io::Error),
    ProjectFolderMissing(std::path::PathBuf),
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        let msg = match self {
            Error::Locked(pid) => {
                format!("A ReScript build is already running. The process ID (PID) is {pid}")
            }
            Error::ParsingLockfile(e) => format!(
                "Could not parse lockfile: \n {e} \n  (try removing it and running the command again)"
            ),
            Error::ReadingLockfile(kind, e) => {
                format!(
                    "Could not read lockfile: {}, \n {e} \n  (try removing it and running the command again)",
                    kind.file_name()
                )
            }
            Error::WritingLockfile(e) => format!("Could not write lockfile: \n {e}"),
            Error::ProjectFolderMissing(path) => format!(
                "Could not write lockfile because the specified project folder does not exist: {}",
                path.to_string_lossy()
            ),
            Error::AwaitingLockFile(await_lock_error) => {
                format!("Error awaiting lockfile: {await_lock_error}")
            }
        };
        write!(f, "{msg}")
    }
}

pub enum Lock {
    Aquired(u32),
    Error(Error),
}

fn matching_process_name() -> Option<String> {
    std::env::current_exe()
        .ok()
        .and_then(|path| path.file_name().map(|name| name.to_string_lossy().into_owned()))
}

fn pid_matches_current_process(to_check_pid: u32) -> bool {
    let system = System::new_all();
    let current_process_name = matching_process_name();

    system.processes().iter().any(|(pid, process)| {
        if pid.as_u32() != to_check_pid {
            return false;
        }

        match &current_process_name {
            Some(current_process_name) => process
                .exe()
                .file_name()
                .map(|name| name.to_string_lossy() == current_process_name.as_str())
                .unwrap_or_else(|| process.name() == current_process_name.as_str()),
            None => true,
        }
    })
}

#[derive(Clone, Copy)]
pub enum LockKind {
    Watch,
    Build,
}

impl LockKind {
    pub fn file_name(&self) -> String {
        String::from(match self {
            LockKind::Watch => "watch.lock",
            LockKind::Build => "build.lock",
        })
    }
}

pub const TIMEOUT_SECONDS: u64 = 60;

pub fn await_lock_deletion(location: &Path, kind: LockKind) -> Result<(), Error> {
    let now = SystemTime::now();
    let lock_path = location.join(kind.file_name());
    let queue = Arc::new(FifoQueue::<Result<Event, notify::Error>>::new());
    let producer = queue.clone();

    let mut watcher = RecommendedWatcher::new(move |res| producer.push(res), Config::default())
        .map_err(|e| Error::AwaitingLockFile(AwaitLockError::Watcher(e)))?;

    watcher
        .watch(location, RecursiveMode::NonRecursive)
        .map_err(|e| Error::AwaitingLockFile(AwaitLockError::Watcher(e)))?;

    loop {
        if !lock_path.exists() {
            return Ok(());
        }

        while !queue.is_empty() {
            match queue.pop() {
                Ok(Event {
                    kind: EventKind::Remove(_),
                    paths,
                    ..
                }) if paths
                    .iter()
                    .any(|path| path == &lock_path || path.ends_with(kind.file_name())) =>
                {
                    return Ok(());
                }
                Ok(_) | Err(_) => (),
            }
        }

        match now.elapsed() {
            Ok(elapsed) if elapsed < Duration::from_secs(TIMEOUT_SECONDS) => {
                std::thread::sleep(Duration::from_millis(50));
            }
            Ok(_) | Err(_) => {
                return Err(Error::AwaitingLockFile(AwaitLockError::Timeout(
                    lock_path.to_string_lossy().to_string(),
                )));
            }
        }
    }
}

pub fn get(kind: LockKind, folder: &str) -> Lock {
    let project_folder = Path::new(folder);
    if !project_folder.exists() {
        return Lock::Error(Error::ProjectFolderMissing(project_folder.to_path_buf()));
    }

    let lib_dir = project_folder.join("lib");
    let location = lib_dir.join(kind.file_name());
    let pid = process::id();

    if let Err(e) = fs::create_dir_all(&lib_dir) {
        return Lock::Error(Error::WritingLockfile(e));
    }

    loop {
        match OpenOptions::new().write(true).create_new(true).open(&location) {
            Ok(mut file) => {
                return match file.write_all(pid.to_string().as_bytes()) {
                    Ok(()) => Lock::Aquired(pid),
                    Err(e) => {
                        let _ = fs::remove_file(&location);
                        Lock::Error(Error::WritingLockfile(e))
                    }
                };
            }
            Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => {}
            Err(e) => return Lock::Error(Error::WritingLockfile(e)),
        }

        // A stale lock must be unlinked before retrying create_new. Never overwrite an existing
        // lock: another process may have acquired it since this iteration began.
        match fs::read_to_string(&location) {
            Ok(contents) => match contents.parse::<u32>() {
                Ok(parsed_pid) if pid_matches_current_process(parsed_pid) => match kind {
                    LockKind::Build => {
                        println!("Waiting for other build to finish...");
                        match await_lock_deletion(&lib_dir, kind) {
                            Ok(()) => continue,
                            Err(_) => return Lock::Error(Error::Locked(parsed_pid)),
                        }
                    }
                    LockKind::Watch => return Lock::Error(Error::Locked(parsed_pid)),
                },
                Ok(_) => match fs::remove_file(&location) {
                    Ok(()) => continue,
                    Err(e) if e.kind() == std::io::ErrorKind::NotFound => continue,
                    Err(e) => return Lock::Error(Error::WritingLockfile(e)),
                },
                Err(e) => return Lock::Error(Error::ParsingLockfile(e)),
            },
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => continue,
            Err(e) => return Lock::Error(Error::ReadingLockfile(kind, e)),
        }
    }
}

pub fn get_lock_or_exit(kind: LockKind, folder: &str) -> Lock {
    match get(kind, folder) {
        Lock::Error(error) => {
            eprintln!("Could not start Rescript build: {error}");
            std::process::exit(1);
        }

        acquired_lock => acquired_lock,
    }
}

pub fn drop_lock(kind: LockKind, folder: &str) -> Result<()> {
    let project_folder = Path::new(folder);
    if !project_folder.exists() {
        return Ok(());
    }

    let lib_dir = project_folder.join("lib");
    let location = lib_dir.join(kind.file_name());

    match fs::read_to_string(&location) {
        Ok(contents) if contents.trim() == process::id().to_string() => {
            fs::remove_file(&location)?;
        }
        Ok(_) => {}
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => {}
        Err(e) => return Err(e.into()),
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;
    use std::thread;
    use std::time::Duration;
    use tempfile::TempDir;

    #[test]
    fn returns_error_when_project_folder_missing() {
        let temp_dir = TempDir::new().expect("temp dir should be created");
        let missing_folder = temp_dir.path().join("missing_project");

        match get(
            LockKind::Watch,
            missing_folder.to_str().expect("path should be valid"),
        ) {
            Lock::Error(Error::ProjectFolderMissing(path)) => {
                assert_eq!(path, missing_folder);
            }
            _ => panic!("expected ProjectFolderMissing error"),
        }

        assert!(
            !missing_folder.exists(),
            "missing project folder should not be created"
        );
    }

    #[test]
    fn creates_lock_when_project_folder_exists() {
        let temp_dir = TempDir::new().expect("temp dir should be created");
        let project_folder = temp_dir.path().join("project");
        fs::create_dir(&project_folder).expect("project folder should be created");

        match get(
            LockKind::Watch,
            project_folder.to_str().expect("path should be valid"),
        ) {
            Lock::Aquired(_) => {}
            _ => panic!("expected lock to be acquired"),
        }

        assert!(
            project_folder.join("lib").exists(),
            "lib directory should be created"
        );
        assert!(
            project_folder
                .join("lib")
                .join(LockKind::Watch.file_name())
                .exists(),
            "lockfile should be created"
        );
    }

    #[test]
    fn ignores_stale_lock_for_unrelated_process_name() {
        let temp_dir = TempDir::new().expect("temp dir should be created");
        let project_folder = temp_dir.path().join("project");
        let lib_dir = project_folder.join("lib");
        fs::create_dir_all(&lib_dir).expect("lib directory should be created");
        fs::write(lib_dir.join(LockKind::Watch.file_name()), "1").expect("lockfile should be written");

        match get(
            LockKind::Watch,
            project_folder.to_str().expect("path should be valid"),
        ) {
            Lock::Aquired(_) => {}
            _ => panic!("expected stale lock from unrelated process to be ignored"),
        }
    }

    #[test]
    fn returns_locked_for_active_watch_lock() {
        let temp_dir = TempDir::new().expect("temp dir should be created");
        let project_folder = temp_dir.path().join("project");
        let lib_dir = project_folder.join("lib");
        let current_pid = process::id();

        fs::create_dir_all(&lib_dir).expect("lib directory should be created");
        fs::write(lib_dir.join(LockKind::Watch.file_name()), current_pid.to_string())
            .expect("lockfile should be written");

        match get(
            LockKind::Watch,
            project_folder.to_str().expect("path should be valid"),
        ) {
            Lock::Error(Error::Locked(locked_pid)) => assert_eq!(locked_pid, current_pid),
            _ => panic!("expected watch lock to block a second active watcher"),
        }
    }

    #[test]
    fn waits_for_active_build_lock_to_be_removed() {
        let temp_dir = TempDir::new().expect("temp dir should be created");
        let project_folder = temp_dir.path().join("project");
        let lib_dir = project_folder.join("lib");
        let build_lock_path = lib_dir.join(LockKind::Build.file_name());
        let current_pid = process::id();

        fs::create_dir_all(&lib_dir).expect("lib directory should be created");
        fs::write(&build_lock_path, current_pid.to_string()).expect("lockfile should be written");

        let build_lock_path_for_thread = build_lock_path.clone();
        let remover = thread::spawn(move || {
            thread::sleep(Duration::from_millis(250));
            fs::remove_file(build_lock_path_for_thread).expect("lockfile should be removed");
        });

        match get(
            LockKind::Build,
            project_folder.to_str().expect("path should be valid"),
        ) {
            Lock::Aquired(acquired_pid) => assert_eq!(acquired_pid, current_pid),
            _ => panic!("expected build lock to wait for removal and then be acquired"),
        }

        remover.join().expect("lockfile remover thread should complete");

        assert_eq!(
            fs::read_to_string(build_lock_path).expect("build lock should be rewritten"),
            current_pid.to_string()
        );
    }

    #[test]
    fn concurrent_watch_lock_has_one_winner() {
        let temp_dir = TempDir::new().expect("temp dir should be created");
        let project_folder = temp_dir.path().join("project");
        fs::create_dir(&project_folder).expect("project folder should be created");
        let folder = project_folder.to_string_lossy().into_owned();
        let barrier = Arc::new(std::sync::Barrier::new(3));

        let contenders = (0..2)
            .map(|_| {
                let folder = folder.clone();
                let barrier = barrier.clone();
                thread::spawn(move || {
                    barrier.wait();
                    get(LockKind::Watch, &folder)
                })
            })
            .collect::<Vec<_>>();
        barrier.wait();

        let acquired = contenders
            .into_iter()
            .map(|contender| contender.join().unwrap())
            .filter(|result| matches!(result, Lock::Aquired(_)))
            .count();
        assert_eq!(acquired, 1);
    }

    #[test]
    fn drop_lock_does_not_remove_another_process_lock() {
        let temp_dir = TempDir::new().expect("temp dir should be created");
        let project_folder = temp_dir.path().join("project");
        let lib_dir = project_folder.join("lib");
        let build_lock_path = lib_dir.join(LockKind::Build.file_name());
        let other_pid = process::id().checked_add(1).expect("PID should not overflow");

        fs::create_dir_all(&lib_dir).expect("lib directory should be created");
        fs::write(&build_lock_path, other_pid.to_string()).expect("lockfile should be written");

        drop_lock(
            LockKind::Build,
            project_folder.to_str().expect("path should be valid"),
        )
        .expect("dropping an unowned lock should be harmless");

        assert_eq!(
            fs::read_to_string(build_lock_path).unwrap(),
            other_pid.to_string()
        );
    }

    #[test]
    fn drop_lock_removes_existing_build_lock() {
        let temp_dir = TempDir::new().expect("temp dir should be created");
        let project_folder = temp_dir.path().join("project");
        let lib_dir = project_folder.join("lib");
        let build_lock_path = lib_dir.join(LockKind::Build.file_name());

        fs::create_dir_all(&lib_dir).expect("lib directory should be created");
        fs::write(&build_lock_path, process::id().to_string()).expect("lockfile should be written");

        drop_lock(
            LockKind::Build,
            project_folder.to_str().expect("path should be valid"),
        )
        .expect("build lock should be removed");

        assert!(
            !build_lock_path.exists(),
            "drop_lock should remove the build lock file"
        );
    }
}
