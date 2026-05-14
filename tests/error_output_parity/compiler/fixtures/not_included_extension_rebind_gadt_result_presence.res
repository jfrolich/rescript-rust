// error-output-parity: Includecore.extension_constructors rebound GADT result presence mismatch
type t<'a> = ..
type t<'a> += | A: t<int>
type t<'a> += | C

module M: {
  type t<'a> += | B = A
} = {
  type t<'a> += | B = C
}
