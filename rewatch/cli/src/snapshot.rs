//! Developer-only snapshot production; never entered by a build command.
use anyhow::{Result, bail};
use rescript::{build, project_context::ProjectContext};

/// One producer invocation and one file write, proportional to snapshot bytes.
pub fn run(args: Vec<String>) -> Result<()> {
    let write = match args.as_slice() {
        [flag, file] if flag == "--write" => Some(file),
        [flag] if flag == "--check" => None,
        _ => bail!("usage: rescript snapshot --write <file> | --check"),
    };
    let runtime = match std::env::var_os("RESCRIPT_RUNTIME") {
        Some(path) => path.into(),
        None => {
            let context = ProjectContext::new(&std::env::current_dir()?)?;
            build::compile::get_runtime_path(&context.current_config, &context)?
        }
    };
    match write {
        Some(file) => std::fs::write(file, build::snapshot::produce(&runtime)?)?,
        None => build::snapshot::check(&runtime, include_bytes!(concat!(env!("OUT_DIR"), "/runtime.bin")))?,
    }
    Ok(())
}
