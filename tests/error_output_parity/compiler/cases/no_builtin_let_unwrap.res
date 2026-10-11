// error-output-parity: -bs-no-builtin-ppx skips the builtin let? rejection.
let x = Ok(1)

let? Ok(_) = x
