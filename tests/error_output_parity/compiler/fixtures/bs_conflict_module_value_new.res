// error-output-parity: Bs_syntaxerr.Conflict_ffi_attribute for @module with @new and value @val.
type t

@module @new @val external make: t = "Thing"
