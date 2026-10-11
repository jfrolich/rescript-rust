// error-output-parity: Bs_syntaxerr.Conflict_ffi_attribute for call-style @val.
type t

@val @send external f: (t, int) => int = "f"
