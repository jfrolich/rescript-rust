// Port of compiler/gentype/GeneratedFiles.ml:1-52.

use std::fs;
use std::io;

// Count logical file operations only in tests; production has no counters.
#[cfg(test)]
thread_local! {
    static FILE_OPERATIONS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

#[inline]
fn file_operation() {
    #[cfg(test)]
    FILE_OPERATIONS.with(|count| count.set(count.get() + 1));
}

#[cfg(test)]
pub(crate) fn take_file_operations() -> usize {
    FILE_OPERATIONS.with(|count| count.replace(0))
}

pub(crate) fn file_exists(path: &str) -> bool {
    file_operation();
    std::path::Path::new(path).exists()
}

pub(crate) fn remove_file(path: &str) -> io::Result<()> {
    file_operation();
    fs::remove_file(path)
}

fn read_contents(path: &str) -> io::Result<String> {
    file_operation();
    fs::read_to_string(path)
}

/// What happened to a generated file, for the debug log.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FileAction {
    /// The module needs no generated file.
    NoMatch,
    /// An existing file was replaced.
    Replace,
    /// An existing file already had the generated contents.
    Identical,
    /// The module had type errors.
    TypeError,
    /// A new file was written.
    Write,
}

/// Log `file_action` on `file_name`, when that debug flag is on.
pub fn log_file_action(file_action: FileAction, file_name: &str) {
    if crate::gentype::debug::basic.load(std::sync::atomic::Ordering::Relaxed) {
        let action = match file_action {
            FileAction::NoMatch => "NoMatch",
            FileAction::Replace => "Replace",
            FileAction::Identical => "Identical",
            FileAction::TypeError => "TypeError",
            FileAction::Write => "Write",
        };
        crate::gentype::log_::item(&format!("{action}  {file_name}\n"));
    }
}

/// The lines of `file`.
pub fn read_lines(file: &str) -> io::Result<Vec<String>> {
    let contents = read_contents(file)?;
    Ok(contents.lines().map(|line| line.to_string()).collect())
}

/// The lines of `file`, joined by `
/// `.
pub fn read_file(file: &str) -> io::Result<String> {
    Ok(read_lines(file)?.join("\n"))
}

/// Write `contents` to `file_path`.
pub fn write_file(file_path: &str, contents: &str) -> io::Result<()> {
    file_operation();
    fs::write(file_path, contents)
}

/// Whether `read_file` of a file holding `raw` would equal `expected`: the
/// file's lines joined by `\n`, compared without building the joined string.
fn joined_lines_equal(raw: &str, expected: &str) -> bool {
    let mut rest = expected;
    for (index, line) in raw.lines().enumerate() {
        if index > 0 {
            let Some(after) = rest.strip_prefix('\n') else {
                return false;
            };
            rest = after;
        }
        let Some(after) = rest.strip_prefix(line) else {
            return false;
        };
        rest = after;
    }
    rest.is_empty()
}

/// Write `file_contents` to `output_file` unless the file already has them,
/// so unchanged files keep their modification time.
pub fn write_file_if_required(output_file: &str, file_contents: &str) -> io::Result<()> {
    if file_exists(output_file) {
        let identical = joined_lines_equal(&read_contents(output_file)?, file_contents);
        if identical {
            log_file_action(FileAction::Identical, output_file);
        } else {
            log_file_action(FileAction::Replace, output_file);
            write_file(output_file, file_contents)?;
        }
    } else {
        log_file_action(FileAction::Write, output_file);
        write_file(output_file, file_contents)?;
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::joined_lines_equal;

    #[test]
    fn joined_lines_equal_matches_joining_read_lines() {
        let cases = [
            ("", ""),
            ("a", "a"),
            ("a\n", "a"),
            ("a\r\nb\n", "a\nb"),
            ("a\nb", "a\nb\n"),
            ("a\n\nb", "a\n\nb"),
            ("\n", ""),
            ("\n\n", "\n"),
            ("ab", "a"),
            ("a", "ab"),
        ];
        for (raw, expected) in cases {
            let joined = raw.lines().collect::<Vec<_>>().join("\n");
            assert_eq!(
                joined_lines_equal(raw, expected),
                joined == expected,
                "{raw:?} vs {expected:?}"
            );
        }
    }
}
