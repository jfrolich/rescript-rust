// error-output-parity: `...` ends the argument list without a comma (warning only)
let f = (a, b) => a + b
let g = f(1 ...)
let unused = (x: int) => ()
