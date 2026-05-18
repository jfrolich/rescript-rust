// Port of compiler/gentype/GeneratedFiles.ml:1-52.
// This Stage 2 GenType port is intentionally not wired into the crate yet.

use std::fs;
use std::io;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FileAction {
    NoMatch,
    Replace,
    Identical,
    TypeError,
    Write,
}

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

pub fn read_lines(file: &str) -> io::Result<Vec<String>> {
    let contents = fs::read_to_string(file)?;
    Ok(contents.lines().map(|line| line.to_string()).collect())
}

pub fn read_file(file: &str) -> io::Result<String> {
    Ok(read_lines(file)?.join("\n"))
}

pub fn write_file(file_path: &str, contents: &str) -> io::Result<()> {
    fs::write(file_path, contents)
}

pub fn write_file_if_required(output_file: &str, file_contents: &str) -> io::Result<()> {
    if std::path::Path::new(output_file).exists() {
        let old_contents = read_file(output_file)?;
        let identical = old_contents == file_contents;
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
