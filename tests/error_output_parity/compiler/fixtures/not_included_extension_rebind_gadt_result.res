// error-output-parity: Includecore.extension_constructors rebound GADT result mismatch
type t<'a> = ..
type t<'a> += | A: t<int>
type t<'a> += | C: t<string>

module M: {
  type t<'a> += | B = A
} = {
  type t<'a> += | B = C
}
