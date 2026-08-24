use crate::helpers::emojis::*;
use anyhow::{bail, Context, Result};
use console::style;
use std::process::{Command, Stdio};
use std::time::Instant;

pub fn run(command_string: String) -> Result<()> {
    let start_subcommand = Instant::now();

    log::info!(
        "{} {}Running subcommand... \n{}\n",
        style("[...]").bold().dim(),
        COMMAND,
        style("────────"),
    );

    // Deliberately preserve the existing whitespace-only command parsing semantics. In particular,
    // this does not add shell quoting or expansion.
    let parsed_command = command_string.split_whitespace().collect::<Vec<&str>>();
    let Some((command, params)) = parsed_command.split_first() else {
        bail!("after-build command cannot be empty");
    };

    let output = Command::new(command)
        .args(params)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .with_context(|| format!("failed to execute after-build command `{command}`"))?
        .wait_with_output()
        .with_context(|| format!("failed waiting for after-build command `{command}`"))?;

    let stdout = String::from_utf8(output.stdout)
        .with_context(|| format!("after-build command `{command}` wrote invalid UTF-8 to stdout"))?;
    let stderr = String::from_utf8(output.stderr)
        .with_context(|| format!("after-build command `{command}` wrote invalid UTF-8 to stderr"))?;
    print!("{stdout}");
    eprint!("{stderr}");

    if !output.status.success() {
        bail!("after-build command `{command}` exited with {}", output.status);
    }

    let subcommand_duration = start_subcommand.elapsed();
    log::info!(
        "{}{} {}Ran subcommand in {:.2}s",
        LINE_CLEAR,
        style("[...]").bold().dim(),
        COMMAND,
        subcommand_duration.as_secs_f64(),
    );

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rejects_empty_commands() {
        let error = run("  \t\n".to_string()).expect_err("empty command should fail");
        assert!(error.to_string().contains("cannot be empty"));
    }
}
