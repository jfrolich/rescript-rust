// error-output-parity: Includecore.Field_names via Typemod.Not_included
module M: {
  type t = {x: int, y: string}
} = {
  type t = {x: int, z: string}
}
