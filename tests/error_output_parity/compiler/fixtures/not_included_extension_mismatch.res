// error-output-parity: Includemod.Extension_constructors via Typemod.Not_included
type t = ..

module M: {
  type t += A(int)
} = {
  type t += A(string)
}
