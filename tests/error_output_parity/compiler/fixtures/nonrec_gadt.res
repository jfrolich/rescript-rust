// error-output-parity: Typedecl.Nonrec_gadt
type t<'a> = A(t<'a>): t<array<'a>>
