// error-output-parity: Includecore.extension_constructors GADT result presence mismatch
type t<'a> = ..

module M: {
  type t<'a> += | A
} = {
  type t<'a> += | A: t<int>
}
