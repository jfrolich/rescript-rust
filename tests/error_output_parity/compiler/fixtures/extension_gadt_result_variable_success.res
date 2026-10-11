// error-output-parity: extension GADT result variables are locally quantified
type t<'a> = ..
type t<'a> += A: t<'b>
