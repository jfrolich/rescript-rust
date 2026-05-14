// error-output-parity: Typecore.Unexpected_existential
type rec t = A('a): t

let A(value) = A(1)
