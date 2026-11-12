use crate::project_context;
use anyhow::{Result, bail};
use rayon::prelude::*;
use std::fs;
use std::io::{self, Read, Write};
use std::path::Path;
use tracing::{info_span, instrument};

use crate::build::packages;
use crate::cli::FileExtension;
use clap::ValueEnum;

#[instrument(name = "format.format", skip_all)]
pub fn format(stdin_extension: Option<FileExtension>, check: bool, files: Vec<String>) -> Result<()> {
    match stdin_extension {
        Some(extension) => {
            format_stdin(extension)?;
        }
        None => {
            // Explicit arguments are checked before any is formatted, so a
            // typo does not reach the formatter as an I/O error.
            for file in &files {
                check_argument(file)?;
            }
            let files = if files.is_empty() {
                get_files_in_scope()?
            } else {
                files
            };
            format_files(files, check)?;
        }
    }

    Ok(())
}

/// Format with the in-process ReScript printer (`bsc -format`). Parsing and
/// printing recurse over the syntax tree, so give them a large stack like the
/// compiler threads. Each file gets a fresh thread, so no thread-local state
/// carries over between files.
fn format_source(source: &[u8], filename: &str) -> Result<Vec<u8>> {
    std::thread::scope(|scope| {
        std::thread::Builder::new()
            .stack_size(256 * 1024 * 1024)
            .spawn_scoped(scope, || {
                rescript_compiler::driver::format_source(source, filename)
            })?
            .join()
            .map_err(|_| anyhow::anyhow!("the formatter panicked"))?
            .map_err(|report| anyhow::anyhow!(report))
    })
}

/// Fail unless `path` names a `.res` or `.resi` file (rewatch-ocaml's
/// `Format.check_argument`).
fn check_argument(path: &str) -> Result<()> {
    let metadata = match fs::metadata(path) {
        Ok(metadata) => metadata,
        Err(_) => bail!("{path}: No such file"),
    };
    if metadata.is_dir() {
        bail!("{path} is a directory; give .res or .resi files, or no arguments to format the project");
    }
    if !(path.ends_with(".res") || path.ends_with(".resi")) {
        bail!("{path} is not a .res or .resi file");
    }
    Ok(())
}

/// The formatter's diagnostics for `target`; they start and end with blank
/// lines.
fn formatting_error(target: &str, report: &str) -> String {
    format!("Error formatting {target}:\n{}", report.trim())
}

/// `path` as the format report names it: a relative path as given, an
/// absolute one relative to the current directory when it is inside it.
fn display_path(path: &str, current_dir: &Path) -> String {
    let as_path = Path::new(path);
    if as_path.is_relative() {
        return path.to_string();
    }
    match as_path.strip_prefix(current_dir) {
        Ok(relative) if !relative.as_os_str().is_empty() => relative.to_string_lossy().into_owned(),
        _ => path.to_string(),
    }
}

fn get_files_in_scope() -> Result<Vec<String>> {
    let current_dir = std::env::current_dir()?;
    let project_context = project_context::ProjectContext::new(&current_dir)?;

    // Format walks all source files regardless of feature selection.
    let packages = packages::make(&None, &project_context, false, false, None)?;
    let mut files: Vec<String> = Vec::new();
    let packages_to_format = project_context.get_scoped_local_packages();

    for (_package_name, package) in packages {
        if packages_to_format.contains(&package.name)
            && let Some(source_files) = &package.source_files
        {
            for (path, _metadata) in source_files {
                if let Some(extension) = path.extension()
                    && (extension == "res" || extension == "resi")
                {
                    files.push(package.path.join(path).to_string_lossy().into_owned());
                }
            }
        }
    }
    Ok(files)
}

fn format_stdin(extension: FileExtension) -> Result<()> {
    let extension_value = extension
        .to_possible_value()
        .ok_or(anyhow::anyhow!("Could not get extension arg value"))?;

    let mut source = Vec::new();
    io::stdin().read_to_end(&mut source)?;
    let filename = format!("stdin{}", extension_value.get_name());
    match format_source(&source, &filename) {
        Ok(formatted) => {
            io::stdout().write_all(&formatted)?;
            Ok(())
        }
        // The diagnostics name the input `<stdin>`, as rewatch-ocaml's do.
        Err(err) => bail!(formatting_error(
            "<stdin>",
            &err.to_string().replace(&filename, "<stdin>")
        )),
    }
}

/// What formatting one file found.
enum FileOutcome {
    Formatted,
    Unformatted,
    Failed(String),
}

/// Format every file, also after one fails, then report the results in path
/// order, relative to the current directory (rewatch-ocaml's
/// `Format.format_files`).
fn format_files(mut files: Vec<String>, check: bool) -> Result<()> {
    files.sort();
    files.dedup();
    let outcomes: Vec<FileOutcome> = files
        .par_iter()
        .map(|file| {
            let original_content = match fs::read(file) {
                Ok(content) => content,
                Err(err) => return FileOutcome::Failed(err.to_string()),
            };
            let formatted_content = match format_source(&original_content, file) {
                Ok(formatted) => formatted,
                Err(err) => return FileOutcome::Failed(err.to_string()),
            };
            if original_content == formatted_content {
                FileOutcome::Formatted
            } else if check {
                FileOutcome::Unformatted
            } else {
                let _file_span = info_span!("format.write_file", file = %file).entered();
                // Only write if content actually changed
                match fs::write(file, &formatted_content) {
                    Ok(()) => FileOutcome::Formatted,
                    Err(err) => FileOutcome::Failed(format!("Could not write formatted file {file}: {err}")),
                }
            }
        })
        .collect();

    let current_dir = std::env::current_dir()?;
    let mut unformatted = 0;
    for (file, outcome) in files.iter().zip(&outcomes) {
        if let FileOutcome::Unformatted = outcome {
            eprintln!("[format check] {}", display_path(file, &current_dir));
            unformatted += 1;
        }
    }
    match unformatted {
        0 => {}
        1 => eprintln!("The file listed above needs formatting"),
        count => eprintln!("The {count} files listed above need formatting"),
    }
    let mut failed = false;
    for (file, outcome) in files.iter().zip(&outcomes) {
        if let FileOutcome::Failed(report) = outcome {
            eprintln!("{}", formatting_error(&display_path(file, &current_dir), report));
            failed = true;
        }
    }

    if failed {
        bail!("Formatting failed");
    }
    if unformatted > 0 {
        bail!("Formatting check failed");
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn names_files_relative_to_the_current_directory() {
        let current_dir = Path::new("/project");
        assert_eq!(display_path("src/A.res", current_dir), "src/A.res");
        assert_eq!(display_path("/project/src/A.res", current_dir), "src/A.res");
        assert_eq!(display_path("/elsewhere/A.res", current_dir), "/elsewhere/A.res");
    }

    #[test]
    fn rejects_arguments_that_are_no_source_files() {
        let dir = tempfile::TempDir::new().unwrap();
        let folder = dir.path().to_string_lossy().into_owned();
        assert!(
            check_argument(&folder)
                .unwrap_err()
                .to_string()
                .ends_with("is a directory; give .res or .resi files, or no arguments to format the project")
        );
        let missing = dir.path().join("Missing.res").to_string_lossy().into_owned();
        assert_eq!(
            check_argument(&missing).unwrap_err().to_string(),
            format!("{missing}: No such file")
        );
        let text = dir.path().join("A.txt");
        fs::write(&text, "").unwrap();
        let text = text.to_string_lossy().into_owned();
        assert_eq!(
            check_argument(&text).unwrap_err().to_string(),
            format!("{text} is not a .res or .resi file")
        );
    }
}
