// error-output-parity: Typedecl.Bad_variance for extension constructor payloads
type t<+'a> = ..
type t<'a> += A('a => int)
