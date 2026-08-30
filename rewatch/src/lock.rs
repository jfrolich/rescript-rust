use anyhow::Result;
use fs2::FileExt;
use notify::{Config, Event, EventKind, RecommendedWatcher, RecursiveMode, Watcher};
use std::fs;
use std::fs::{File, OpenOptions};
use std::io::{Seek, SeekFrom, Write};
use std::path::Path;
use std::process;
use std::sync::Arc;
use std::time::{Duration, Instant, SystemTime};

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

pub struct LockGuard {
    pub pid: u32,
    _file: File,
}

pub enum Lock {
    Aquired(LockGuard),
    Error(Error),
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

    // Keep the advisory-lock inode separate from the PID marker. Watch shutdown
    // removes the marker as a signal, so locking that removable file would let a
    // second process create and lock a different inode while the first still ran.
    let guard_path = lib_dir.join(format!(".{}.guard", kind.file_name()));
    let mut guard_file = match OpenOptions::new()
        .read(true)
        .write(true)
        .create(true)
        .truncate(false)
        .open(&guard_path)
    {
        Ok(file) => file,
        Err(e) => return Lock::Error(Error::WritingLockfile(e)),
    };

    let started = Instant::now();
    let mut announced_wait = false;
    loop {
        match guard_file.try_lock_exclusive() {
            Ok(()) => {
                if let Err(e) = guard_file.set_len(0).and_then(|()| {
                    guard_file.seek(SeekFrom::Start(0))?;
                    guard_file.write_all(pid.to_string().as_bytes())?;
                    guard_file.sync_data()
                }) {
                    return Lock::Error(Error::WritingLockfile(e));
                }
                if let Err(e) = fs::write(&location, pid.to_string()) {
                    return Lock::Error(Error::WritingLockfile(e));
                }
                return Lock::Aquired(LockGuard {
                    pid,
                    _file: guard_file,
                });
            }
            Err(e) if e.kind() == std::io::ErrorKind::WouldBlock => {
                let parsed_pid = fs::read_to_string(&location)
                    .ok()
                    .and_then(|contents| contents.trim().parse::<u32>().ok())
                    .unwrap_or(0);
                if matches!(kind, LockKind::Watch) {
                    return Lock::Error(Error::Locked(parsed_pid));
                }
                if !announced_wait {
                    println!("Waiting for other build to finish...");
                    announced_wait = true;
                }
                if started.elapsed() >= Duration::from_secs(TIMEOUT_SECONDS) {
                    return Lock::Error(Error::Locked(parsed_pid));
                }
                std::thread::sleep(Duration::from_millis(50));
            }
            Err(e) => return Lock::Error(Error::WritingLockfile(e)),
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
        let first = get(
            LockKind::Watch,
            project_folder.to_str().expect("path should be valid"),
        );
        assert!(matches!(first, Lock::Aquired(_)));

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
        let active_guard = OpenOptions::new()
            .read(true)
            .write(true)
            .create(true)
            .truncate(false)
            .open(lib_dir.join(".build.lock.guard"))
            .expect("guard file should open");
        active_guard
            .lock_exclusive()
            .expect("active build should hold the advisory lock");

        let remover = thread::spawn(move || {
            thread::sleep(Duration::from_millis(250));
            drop(active_guard);
        });

        match get(
            LockKind::Build,
            project_folder.to_str().expect("path should be valid"),
        ) {
            Lock::Aquired(guard) => assert_eq!(guard.pid, current_pid),
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
