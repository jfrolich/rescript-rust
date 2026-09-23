//! Cached process working directory.
//!
//! `std::env::current_dir` performs `open`/`fcntl` system calls on macOS. The
//! compiler never changes its working directory, so per-module path
//! resolution can reuse the value read at first use.

use std::path::PathBuf;
use std::sync::OnceLock;

/// The process working directory, read once.
pub fn current_dir() -> std::io::Result<PathBuf> {
    static CWD: OnceLock<Option<PathBuf>> = OnceLock::new();
    CWD.get_or_init(|| std::env::current_dir().ok())
        .clone()
        .ok_or_else(|| std::io::Error::other("current directory is unavailable"))
}
