// error-output-parity: Includecore.Manifest via Typemod.Not_included
module M: {
  type t = int
} = {
  type t = string
}
