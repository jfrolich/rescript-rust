// error-output-parity: Includecore.Field_mutable via Typemod.Not_included
module M: {
  type t = {mutable x: int}
} = {
  type t = {x: int}
}
