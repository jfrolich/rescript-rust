// error-output-parity: %ffi accepts recovered non-async arrow functions with expression-body warnings.
let _ = %ffi("x =>")
