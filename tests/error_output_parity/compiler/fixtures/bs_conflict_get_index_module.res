// error-output-parity: Bs_syntaxerr.Conflict_ffi_attribute for @get_index.
@get_index @module("x") external get: (int, int) => int = ""
