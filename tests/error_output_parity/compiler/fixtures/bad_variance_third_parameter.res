// error-output-parity: Typedecl.Bad_variance third parameter ordinal
type t<'a, 'b, +'c> = ('a, 'b, 'c) => unit
