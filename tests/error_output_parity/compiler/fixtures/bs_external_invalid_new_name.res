// error-output-parity: External_ffi_types rejects invalid JS constructor names.
type t
@new external make: int => t = "not-valid"
