// error-output-parity: Includecore.Field_type variant constructors via Typemod.Not_included
module M: {
  type t = A(int)
} = {
  type t = A(string)
}
