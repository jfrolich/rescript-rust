// error-output-parity: Typedecl.Varying_anonymous for extension GADT result parameters
type t<+'a, 'b> = ..
type t<'a, 'b> += A: t<'b, 'b>
