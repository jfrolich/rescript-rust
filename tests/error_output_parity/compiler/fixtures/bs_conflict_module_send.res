// error-output-parity: Bs_syntaxerr.Conflict_ffi_attribute for @module with @send.
type t

@module @send external f: (t, int) => int = "M"
