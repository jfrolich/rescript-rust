// error-output-parity: Typecore.Apply_wrong_label optional label branch
let f = (~x: int) => x
let maybeY = Some(1)

let result = f(~y=?maybeY)
