// error-output-parity: Lam_compile dynamic import rejects constant local values.
let value = 1
let x = Js.import(value)
