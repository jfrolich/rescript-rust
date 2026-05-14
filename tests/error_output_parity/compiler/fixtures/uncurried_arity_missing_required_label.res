// error-output-parity: Typecore.Uncurried_arity_mismatch missing required labelled argument
let f = (~x: int, ~y: int) => x + y

let result = f(~x=1)
