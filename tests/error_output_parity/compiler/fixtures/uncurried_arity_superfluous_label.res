// error-output-parity: Typecore.Uncurried_arity_mismatch superfluous labelled argument
let f = (~x: int) => x

let result = f(~x=1, ~y=2)
