use crate::helpers::emojis::*;
use anyhow::{Context, Result, bail};
use console::style;
use std::process::{Command, ExitStatus};
use std::time::Instant;

/// `command` run by the shell, `/bin/sh -c`, or `cmd.exe /C` on Windows, so
/// quoting, pipes and an exit status work as typed and the shell reports a
/// missing program (rewatch-ocaml's `Platform.shell_command`).
fn shell_command(command: &str) -> Command {
    #[cfg(windows)]
    {
        use std::os::windows::process::CommandExt;
        let mut shell = Command::new("cmd.exe");
        // With /S, cmd.exe removes the outer quotes and runs the rest as typed.
        shell
            .args(["/D", "/V:OFF", "/S", "/C"])
            .raw_arg(format!("\"{command}\""));
        shell
    }
    #[cfg(not(windows))]
    {
        let mut shell = Command::new("/bin/sh");
        shell.arg("-c").arg(command);
        shell
    }
}

/// "exit code 3", or "signal 9" for a process a signal ended.
fn status_description(status: ExitStatus) -> String {
    #[cfg(unix)]
    {
        use std::os::unix::process::ExitStatusExt;
        if let Some(signal) = status.signal() {
            return format!("signal {signal}");
        }
    }
    match status.code() {
        Some(code) => format!("exit code {code}"),
        None => status.to_string(),
    }
}

/// Run the --after-build command.
pub fn run(command_string: String) -> Result<()> {
    let start_subcommand = Instant::now();

    log::info!(
        "{} {}Running subcommand... \n{}\n",
        style("[...]").bold().dim(),
        COMMAND,
        style("────────"),
    );

    if command_string.trim().is_empty() {
        bail!("--after-build command cannot be empty");
    }
    // The command's output streams through, and it reads this process's
    // standard input.
    let status = shell_command(&command_string)
        .status()
        .with_context(|| format!("Could not run --after-build command {command_string:?}"))?;
    if !status.success() {
        bail!("--after-build command failed with {}", status_description(status));
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
        assert_eq!(error.to_string(), "--after-build command cannot be empty");
    }

    #[cfg(unix)]
    #[test]
    fn runs_the_command_through_the_shell() {
        run("test \"a b\" = 'a b' && true".to_string()).expect("the shell should run the command");
        let error = run("echo \"a b\" c; exit 3".to_string()).expect_err("exit 3 should fail");
        assert_eq!(error.to_string(), "--after-build command failed with exit code 3");
    }
}
