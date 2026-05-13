// error-output-parity: -bs-no-builtin-ppx leaves normal externals as Ffi_normal.
external f: int => int = "f"
let _ = f(1)
