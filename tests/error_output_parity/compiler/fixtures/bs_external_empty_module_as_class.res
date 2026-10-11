// error-output-parity: External_ffi_types rejects empty @module class imports.
type t
@module @new external make: int => t = ""
