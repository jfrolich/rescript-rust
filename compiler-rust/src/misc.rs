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
    if payload.is::<FatalError>() {
        return Some("Fatal error: exception Misc.Fatal_error".to_string());
    }
    payload
        .downcast_ref::<UncaughtException>()
        .map(|exception| format!("Fatal error: exception {}", exception.0))
}
