// error-output-parity: Typedecl.Bad_variance second parameter ordinal
type t<'a, +'b> = 'b => 'a
