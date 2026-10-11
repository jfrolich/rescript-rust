// error-output-parity: Typedecl.Inconsistent_constraint
type t<'a> = 'a constraint 'a = int constraint 'a = string
