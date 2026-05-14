// error-output-parity: Includecore.Kind via Typemod.Not_included
module M: {
  type t = A
} = {
  type t = {x: int}
}
