// error-output-parity: Typecore.Uncurried_arity_mismatch arity suggestion
let add = x => x
let add2 = (x, y) => x + y

let result = add(1, 2)
