// error-output-parity: Bs_syntaxerr.Conflict_ffi_attribute for @set_index.
@set_index @module("x") external set: (int, int, int) => unit = ""
