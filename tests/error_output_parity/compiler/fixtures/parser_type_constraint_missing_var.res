// error-output-parity: parse_type_constraint recovers a missing type variable
type t<'a> = 'a constraint constraint 'a = int
