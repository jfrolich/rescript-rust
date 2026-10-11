// error-output-parity: Includecore.Field_optional via Typemod.Not_included
module M: {
  type t = {x?: int}
} = {
  type t = {x: int}
}
