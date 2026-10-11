// error-output-parity: Includecore.Field_missing via Typemod.Not_included
module M: {
  type t = {x: int, y: string}
} = {
  type t = {x: int}
}
