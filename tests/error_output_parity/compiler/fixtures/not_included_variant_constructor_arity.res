// error-output-parity: Includecore.Field_arity variant constructors via Typemod.Not_included
module M: {
  type t = A(int, string)
} = {
  type t = A(int)
}
