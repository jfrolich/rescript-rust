// error-output-parity: a failed coercion is reported before the expected-type clash
type source = @as(null) Null

let value: [< #a | #b] = (Null :> string)
