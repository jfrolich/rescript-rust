// error-output-parity: extension GADT argument variables are existential
type t = ..
type t += A('a): t
