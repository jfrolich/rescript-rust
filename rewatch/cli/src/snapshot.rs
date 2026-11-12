//! Developer-only snapshot production; never entered by a build command.
use anyhow::{Result, bail};
use rescript::{build, project_context::ProjectContext};

/// One producer invocation and one file write, proportional to snapshot bytes.
pub fn run(args: Vec<String>) -> Result<()> {
    let [flag, file] = args.as_slice() else {
        bail!("usage: rescript snapshot --write <file>");
    };
    if flag != "--write" { bail!("usage: rescript snapshot --write <file>"); }
    let runtime = match std::env::var_os("RESCRIPT_RUNTIME") {
        Some(path) => path.into(),
        None => {
            let context = ProjectContext::new(&std::env::current_dir()?)?;
            build::compile::get_runtime_path(&context.current_config, &context)?
        }
    };
    std::fs::write(file, build::snapshot::produce(&runtime)?)?;
    Ok(())
}
