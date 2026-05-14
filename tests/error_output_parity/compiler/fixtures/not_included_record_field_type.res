// error-output-parity: Includecore.Field_type via Typemod.Not_included
module M: {
  type t = {x: int}
} = {
  type t = {x: string}
}
