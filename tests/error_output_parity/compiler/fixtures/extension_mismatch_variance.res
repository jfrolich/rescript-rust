// error-output-parity: Typedecl.Extension_mismatch variance
type t<'a> = ..
type t<+'a> += A
