// error-output-parity: Lam_compile_primitive rejects non-module global values as dynamic import targets.
@val external value: int = "value"
let x = Js.import(value)
