// error-output-parity: Bs_syntaxerr.Conflict_ffi_attribute for @new.
type t

@new @get external make: t => int = "Thing"
