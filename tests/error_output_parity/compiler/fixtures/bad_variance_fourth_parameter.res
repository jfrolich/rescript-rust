// error-output-parity: Typedecl.Bad_variance default ordinal suffix
type t<'a, 'b, 'c, +'d> = ('a, 'b, 'c, 'd) => unit
