//! Port of the parts of OCaml's `Misc` that shape compiler failure output.

/// Unwind payload standing in for OCaml's `Misc.Fatal_error` exception.
#[derive(Debug)]
pub struct FatalError(pub String);

/// OCaml `Misc.fatal_error` (compiler/ext/misc.ml): report the message, then
/// raise `Fatal_error`, which the driver reports as an uncaught exception.
/// `resume_unwind` skips the panic hook, so only OCaml's lines are printed.
pub fn fatal_error(msg: &str) -> ! {
    // OCaml prints the `>> Fatal error:` line before raising; nothing prints
    // in between, so the report prints it with the exception's line. That
    // keeps it after warnings an in-process compile has not printed yet.
    std::panic::resume_unwind(Box::new(FatalError(msg.to_string())))
}

/// Unwind payload for an OCaml exception that escapes to the toplevel
/// uncaught (for example `Syntaxerr.Error` from `Ast_helper`), carrying the
/// runtime's printed form of the exception.
#[derive(Debug)]
pub struct UncaughtException(pub &'static str);

/// Raise an exception that OCaml does not catch before the toplevel.
pub fn raise_uncaught(exception: &'static str) -> ! {
    std::panic::resume_unwind(Box::new(UncaughtException(exception)))
}

/// The OCaml runtime's report for an uncaught-exception unwind payload.
pub fn uncaught_exception_report(payload: &(dyn std::any::Any + Send)) -> Option<String> {
    if let Some(FatalError(msg)) = payload.downcast_ref::<FatalError>() {
        return Some(format!(
            ">> Fatal error: {msg}\nFatal error: exception Misc.Fatal_error"
        ));
    }
    payload
        .downcast_ref::<UncaughtException>()
        .map(|exception| format!("Fatal error: exception {}", exception.0))
}

/// `Ext_filename.module_name`: the compilation-unit name of a source file,
/// its basename without the final extension (the output prefix), with only
/// an ASCII first letter capitalized. `Button.test.res` is `Button.test`, so
/// it can refer to `Button`.
pub fn module_name_from_source_filename(path: &str) -> String {
    let basename = std::path::Path::new(path)
        .file_name()
        .and_then(|s| s.to_str())
        .unwrap_or(path);
    let name = basename.rsplit_once('.').map_or(basename, |(name, _)| name);
    let mut name = name.to_string();
    if let Some(first) = name.get_mut(0..1) {
        first.make_ascii_uppercase();
    }
    name
}

/// OCaml `Filename.generic_basename` (stdlib/filename.ml:36-48): the last
/// component of `name` after dropping trailing separators; `"."` for `""`,
/// and the first character for a name of separators only.
fn generic_basename(is_dir_sep: impl Fn(u8) -> bool, name: &str) -> &str {
    if name.is_empty() {
        return ".";
    }
    let bytes = name.as_bytes();
    let Some(end) = bytes.iter().rposition(|&b| !is_dir_sep(b)) else {
        return &name[..1];
    };
    let begin = bytes[..end]
        .iter()
        .rposition(|&b| is_dir_sep(b))
        .map_or(0, |p| p + 1);
    &name[begin..=end]
}

/// `Filename.Unix.basename` (filename.ml:90-114): `/` is the only separator.
fn unix_basename(name: &str) -> &str {
    generic_basename(|b| b == b'/', name)
}

/// `Filename.Win32.is_dir_sep` (filename.ml:123).
fn win32_is_dir_sep(b: u8) -> bool {
    matches!(b, b'/' | b'\\' | b':')
}

/// `Filename.Win32.basename` (filename.ml:236-254): a leading drive letter
/// is dropped first (`drive_and_path`).
fn win32_basename(name: &str) -> &str {
    let bytes = name.as_bytes();
    let path = if bytes.len() >= 2 && bytes[0].is_ascii_alphabetic() && bytes[1] == b':' {
        &name[2..]
    } else {
        name
    };
    generic_basename(win32_is_dir_sep, path)
}

/// `Filename.Cygwin.basename` (filename.ml:257-269): the Win32 separators,
/// without dropping a drive.
fn cygwin_basename(name: &str) -> &str {
    generic_basename(win32_is_dir_sep, name)
}

/// OCaml `Filename.basename`, of the implementation `Sys.os_type` selects
/// (filename.ml:273-277): Win32 on Windows, Cygwin on Cygwin, Unix
/// otherwise.
pub fn filename_basename(name: &str) -> &str {
    if cfg!(windows) {
        win32_basename(name)
    } else if cfg!(target_os = "cygwin") {
        cygwin_basename(name)
    } else {
        unix_basename(name)
    }
}

#[cfg(test)]
mod tests {
    use super::{cygwin_basename, unix_basename, win32_basename};

    /// Expected values from OCaml 5.5's `Filename.Unix`, `Filename.Win32`
    /// and `Filename.Cygwin` `basename`.
    #[test]
    fn filename_basename_matches_ocaml() {
        for (name, unix, win32, cygwin) in [
            ("/home/me/app/src/D.res", "D.res", "D.res", "D.res"),
            ("D.res", "D.res", "D.res", "D.res"),
            ("src/dir/", "dir", "dir", "dir"),
            ("a/..", "..", "..", ".."),
            ("//", "/", "/", "/"),
            ("", ".", ".", "."),
            ("src/d\u{ef}r/Deep.res", "Deep.res", "Deep.res", "Deep.res"),
            (r"C:\app\src\D.res", r"C:\app\src\D.res", "D.res", "D.res"),
            (r"src\D.res", r"src\D.res", "D.res", "D.res"),
            ("C:D.res", "C:D.res", "D.res", "D.res"),
            ("C:", "C:", ".", "C"),
            (r"C:\", r"C:\", r"\", "C"),
            (
                r"\\server\share\D.res",
                r"\\server\share\D.res",
                "D.res",
                "D.res",
            ),
            ("a:b", "a:b", "b", "b"),
        ] {
            assert_eq!(unix_basename(name), unix, "Unix {name:?}");
            assert_eq!(win32_basename(name), win32, "Win32 {name:?}");
            assert_eq!(cygwin_basename(name), cygwin, "Cygwin {name:?}");
        }
    }
}
