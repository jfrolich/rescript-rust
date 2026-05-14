// error-output-parity: Typetexp.Type_mismatch
type t<'a> = 'a constraint 'a = int

let x: t<string> = 1
