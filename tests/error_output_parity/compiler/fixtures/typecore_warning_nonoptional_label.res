// error-output-parity: Typecore emits warning 43 when ?label syntax is used for a nonoptional label.
let f = (~x) => x

let value = f(~x=?Some(1))
