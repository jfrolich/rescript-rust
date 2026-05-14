// error-output-parity: Includecore.extension_constructors GADT result mismatch
type t<'a> = ..

module M: {
  type t<'a> += | A: t<int>
} = {
  type t<'a> += | A: t<string>
}
