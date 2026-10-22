//! Virtual filesystem for WASM builds.
//!
//! Provides a thread-local in-memory filesystem that the compiler reads from
//! instead of `std::fs` when running in the browser. Files are populated
//! from JavaScript via wasm-bindgen.

use std::cell::RefCell;
use std::collections::HashMap;

thread_local! {
    static VFS: RefCell<HashMap<String, String>> = RefCell::new(HashMap::new());
}

/// Write a file to the virtual filesystem.
pub fn write_file(path: &str, content: String) {
    VFS.with(|vfs| {
        vfs.borrow_mut().insert(path.to_string(), content);
    });
}

/// Read a file from the virtual filesystem.
pub fn read_file(path: &str) -> Option<String> {
    VFS.with(|vfs| vfs.borrow().get(path).cloned())
}

/// Remove a file from the virtual filesystem.
pub fn delete_file(path: &str) {
    VFS.with(|vfs| {
        vfs.borrow_mut().remove(path);
    });
}

/// Clear all files.
pub fn clear() {
    VFS.with(|vfs| vfs.borrow_mut().clear());
}
