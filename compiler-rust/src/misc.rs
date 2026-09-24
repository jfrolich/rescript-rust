//! Port of the parts of OCaml's `Misc` that shape compiler failure output.

/// Unwind payload standing in for OCaml's `Misc.Fatal_error` exception.
#[derive(Debug)]
pub struct FatalError;

/// OCaml `Misc.fatal_error` (compiler/ext/misc.ml): report the message, then
/// raise `Fatal_error`, which the driver reports as an uncaught exception.
/// `resume_unwind` skips the panic hook, so only OCaml's lines are printed.
pub fn fatal_error(msg: &str) -> ! {
    eprintln!(">> Fatal error: {msg}");
    std::panic::resume_unwind(Box::new(FatalError))
}
