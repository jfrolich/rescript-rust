// error-output-parity: Typedecl.Constraint_failed uses extension parameters in expected type
type t<'a> = ..
type u = ..
type t<'b> += A: u
