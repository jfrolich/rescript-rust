// error-output-parity: Typedecl.Bad_variance constrained parameter propagation
type t<+'a> = array<'a> constraint 'a = option<'b>
