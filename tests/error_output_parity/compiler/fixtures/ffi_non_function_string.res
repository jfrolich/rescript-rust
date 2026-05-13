// error-output-parity: Ast_exp_handle_external %ffi rejects non-function strings.
let _ = %ffi("not a function")
