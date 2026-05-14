// error-output-parity: Typedecl.Nonrec_gadt on a non-first constructor
type t<'a> = A | B(t<'a>): t<array<'a>>
