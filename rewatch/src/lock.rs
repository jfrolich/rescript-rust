use anyhow::Result;
use fs2::FileExt;
use std::fs;
use std::fs::{File, OpenOptions};
use std::io::{Seek, SeekFrom, Write};
use std::path::Path;
use std::process;
use std::time::{Duration, Instant};

/* Locking uses an fs2 advisory exclusive lock on a separate `.<kind>.lock.guard` file, which
 * is never deleted. The `<kind>.lock` file next to it only records the PID of the holder: it is
 * informational, and the watcher removes it on shutdown as a signal. Because the kernel releases
 * the advisory lock when the holding process exits, stale markers never block a new process. */

pub enum Error {
    Locked(u32),
    WritingLockfile(std::io::Error),
    ProjectFolderMissing(std::path::PathBuf),
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        let msg = match self {
            Error::Locked(pid) => {
                format!("A ReScript build is already running. The process ID (PID) is {pid}")
            }
            Error::WritingLockfile(e) => format!("Could not write lockfile: \n {e}"),
            // Most often a mistyped command, which reads as a folder.
            Error::ProjectFolderMissing(path) => format!(
                "Project folder '{}' does not exist. Run 'rescript --help' for the available commands.",
                path.to_string_lossy()
            ),
        };
        write!(f, "{msg}")
    }
}

pub struct LockGuard {
    pub pid: u32,
    _file: File,
}

pub enum Lock {
    Acquired(LockGuard),
    Error(Error),
}

#[derive(Clone, Copy)]
pub enum LockKind {
    Watch,
    Build,
}

impl LockKind {
    pub fn file_name(&self) -> &'static str {
        match self {
            LockKind::Watch => "watch.lock",
            LockKind::Build => "build.lock",
        }
    }
}

/// Where a project's locks live: its artifact directory, `lib/rescript`
/// (as rewatch-ocaml's `Build_lock`).
pub fn lock_dir(project_folder: &Path) -> std::path::PathBuf {
    crate::build::packages::get_build_path(project_folder)
}

/// Whether `name` in an artifact directory belongs to a lock, which a clean
/// keeps: a lock's PID marker, its guard, or another build system's takeover
/// marker and candidates (rewatch-ocaml's `Build_artifacts.is_lock_file`).
pub fn is_lock_file(name: &str) -> bool {
    [LockKind::Build, LockKind::Watch].iter().any(|kind| {
        let lock = kind.file_name();
        name == lock
            || name.strip_suffix(".takeover") == Some(lock)
            || name
                .strip_prefix('.')
                .and_then(|name| name.strip_suffix(".guard"))
                == Some(lock)
    }) || name.starts_with(".build-lock-")
        || name.starts_with(".watch-lock-")
}

const TIMEOUT_SECONDS: u64 = 60;

fn get(kind: LockKind, folder: &str) -> Lock {
    let project_folder = Path::new(folder);
    if !project_folder.exists() {
        return Lock::Error(Error::ProjectFolderMissing(project_folder.to_path_buf()));
    }

    let lib_dir = lock_dir(project_folder);
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
                // The exclusive lock itself is kernel state on the open file;
                // the PID written here is informational, so it is not synced
                // (on macOS `sync_data` is a full-device flush).
                if let Err(e) = guard_file.set_len(0).and_then(|()| {
                    guard_file.seek(SeekFrom::Start(0))?;
                    guard_file.write_all(pid.to_string().as_bytes())
                }) {
                    return Lock::Error(Error::WritingLockfile(e));
                }
                if let Err(e) = fs::write(&location, pid.to_string()) {
                    return Lock::Error(Error::WritingLockfile(e));
                }
                return Lock::Acquired(LockGuard {
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

/// Report `error` and exit; `locked` words the error for a lock another
/// process holds.
fn exit_with(error: Error, locked: impl FnOnce(u32) -> String) -> ! {
    match error {
        Error::Locked(pid) => eprintln!("{}", locked(pid)),
        Error::ProjectFolderMissing(_) => eprintln!("{error}"),
        Error::WritingLockfile(_) => eprintln!("Could not start Rescript build: {error}"),
    }
    std::process::exit(1);
}

pub fn get_lock_or_exit(kind: LockKind, folder: &str) -> LockGuard {
    match get(kind, folder) {
        Lock::Error(error) => exit_with(error, |pid| {
            format!("Could not start Rescript build: {}", Error::Locked(pid))
        }),
        Lock::Acquired(guard) => guard,
    }
}

/// The watch lock of `folder` for `rescript clean`, which a watcher holds
/// while it runs: a watcher of the project would keep reading the artifacts
/// the clean removes (rewatch-ocaml's `Clean.run`). Drop it with
/// `drop_lock(LockKind::Watch, folder)`.
pub fn get_clean_lock_or_exit(folder: &str) -> LockGuard {
    match get(LockKind::Watch, folder) {
        Lock::Error(error) => exit_with(error, |pid| {
            format!(
                "Could not clean while rescript watch or another clean is running. The process ID (PID) is {pid}"
            )
        }),
        Lock::Acquired(guard) => guard,
    }
}

pub fn drop_lock(kind: LockKind, folder: &str) -> Result<()> {
    let project_folder = Path::new(folder);
    if !project_folder.exists() {
        return Ok(());
    }

    let location = lock_dir(project_folder).join(kind.file_name());

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
    use std::sync::Arc;
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
    fn lock_files_are_recognized() {
        for name in [
            "build.lock",
            "watch.lock",
            ".build.lock.guard",
            ".watch.lock.guard",
            "watch.lock.takeover",
            ".build-lock-1234.tmp",
            ".watch-lock-1234.tmp",
        ] {
            assert!(is_lock_file(name), "{name} belongs to a lock");
        }
        for name in [
            ".compiler.log",
            "rescript.sqlite",
            "A.cmi",
            "build.lock.guard",
            "lock",
        ] {
            assert!(!is_lock_file(name), "{name} is no lock file");
        }
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
            Lock::Acquired(_) => {}
            _ => panic!("expected lock to be acquired"),
        }

        assert!(
            project_folder.join("lib").join("rescript").exists(),
            "lib/rescript directory should be created"
        );
        assert!(
            project_folder
                .join("lib")
                .join("rescript")
                .join(LockKind::Watch.file_name())
                .exists(),
            "lockfile should be created"
        );
    }

    #[test]
    fn ignores_marker_without_held_guard() {
        let temp_dir = TempDir::new().expect("temp dir should be created");
        let project_folder = temp_dir.path().join("project");
        let lib_dir = lock_dir(&project_folder);
        fs::create_dir_all(&lib_dir).expect("lib directory should be created");
        fs::write(lib_dir.join(LockKind::Watch.file_name()), "1").expect("lockfile should be written");

        match get(
            LockKind::Watch,
            project_folder.to_str().expect("path should be valid"),
        ) {
            Lock::Acquired(_) => {}
            _ => panic!("expected a PID marker without a held guard to be ignored"),
        }
    }

    #[test]
    fn returns_locked_for_active_watch_lock() {
        let temp_dir = TempDir::new().expect("temp dir should be created");
        let project_folder = temp_dir.path().join("project");
        let lib_dir = lock_dir(&project_folder);
        let current_pid = process::id();

        fs::create_dir_all(&lib_dir).expect("lib directory should be created");
        let first = get(
            LockKind::Watch,
            project_folder.to_str().expect("path should be valid"),
        );
        assert!(matches!(first, Lock::Acquired(_)));

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
        let lib_dir = lock_dir(&project_folder);
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
            Lock::Acquired(guard) => assert_eq!(guard.pid, current_pid),
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

        // Join every contender before inspecting the results: a winner's guard
        // must stay alive until the other thread has finished, or a contender
        // that runs late could acquire the lock after the winner released it.
        let results = contenders
            .into_iter()
            .map(|contender| contender.join().unwrap())
            .collect::<Vec<_>>();
        let acquired = results
            .iter()
            .filter(|result| matches!(result, Lock::Acquired(_)))
            .count();
        assert_eq!(acquired, 1);
    }

    #[test]
    fn drop_lock_does_not_remove_another_process_lock() {
        let temp_dir = TempDir::new().expect("temp dir should be created");
        let project_folder = temp_dir.path().join("project");
        let lib_dir = lock_dir(&project_folder);
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
        let lib_dir = lock_dir(&project_folder);
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
