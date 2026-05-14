// error-output-parity: Typedecl.Nonrec_gadt in signatures
type t<'a> = A(t<'a>): t<array<'a>>
