use crate::project_context;
use anyhow::{Result, bail};
use num_cpus;
use rayon::prelude::*;
use std::fs;
use std::io::{self, Read, Write};
use std::sync::atomic::{AtomicUsize, Ordering};
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
/// compiler threads.
fn format_source(source: Vec<u8>, filename: String) -> Result<Vec<u8>> {
    std::thread::Builder::new()
        .stack_size(256 * 1024 * 1024)
        .spawn(move || rescript_compiler::driver::format_source(&source, &filename))?
        .join()
        .map_err(|_| anyhow::anyhow!("the formatter panicked"))?
        .map_err(|report| anyhow::anyhow!(report))
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
    match format_source(source, filename) {
        Ok(formatted) => {
            io::stdout().write_all(&formatted)?;
            Ok(())
        }
        Err(err) => bail!("Error formatting stdin: {err}"),
    }
}

fn format_files(files: Vec<String>, check: bool) -> Result<()> {
    let batch_size = 4 * num_cpus::get();
    let incorrectly_formatted_files = AtomicUsize::new(0);

    files.par_chunks(batch_size).try_for_each(|batch| {
        batch.iter().try_for_each(|file| {
            let original_content = fs::read(file)?;
            let formatted_content = match format_source(original_content.clone(), file.clone()) {
                Ok(formatted) => formatted,
                Err(err) => bail!("Error formatting {}: {}", file, err),
            };
            if original_content != formatted_content {
                if check {
                    eprintln!("[format check] {file}");
                    incorrectly_formatted_files.fetch_add(1, Ordering::SeqCst);
                } else {
                    let _file_span = info_span!("format.write_file", file = %file).entered();
                    // Only write if content actually changed
                    fs::write(file, &formatted_content)?;
                }
            }
            Ok(())
        })
    })?;

    let count = incorrectly_formatted_files.load(Ordering::SeqCst);
    if count > 0 {
        if count == 1 {
            eprintln!("The file listed above needs formatting");
        } else {
            eprintln!("The {count} files listed above need formatting");
        }
        bail!("Formatting check failed");
    }

    Ok(())
}
