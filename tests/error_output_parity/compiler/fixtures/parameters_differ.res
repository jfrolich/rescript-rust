// error-output-parity: Typedecl.Parameters_differ
type rec t<'a> = u<'a>
and u<'a> = t<array<'a>>
