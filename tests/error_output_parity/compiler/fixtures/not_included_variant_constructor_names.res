// error-output-parity: Includecore.Field_names variant constructors via Typemod.Not_included
module M: {
  type t = A | B
} = {
  type t = A | C
}
