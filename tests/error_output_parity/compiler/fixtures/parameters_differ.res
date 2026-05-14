// error-output-parity: Typedecl.Cycle_in_def through recursive parameterized aliases
type rec t<'a> = u<'a>
and u<'a> = t<array<'a>>
