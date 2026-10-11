// error-output-parity: Typedecl.Bad_variance constrained parameter propagation code -3.
type hidden<'a> = ..
type t<+'a> = array<'a> constraint 'a = hidden<'b>
