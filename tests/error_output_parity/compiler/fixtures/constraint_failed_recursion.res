// error-output-parity: Typedecl.Constraint_failed from recursive abbreviation expansion
type rec t<'a> = u<string>
and u<'b> = 'b constraint 'b = int
