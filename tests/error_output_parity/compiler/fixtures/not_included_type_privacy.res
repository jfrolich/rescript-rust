// error-output-parity: Includecore.Privacy via Typemod.Not_included
module M: {
  type t = int
} = {
  type t = private int
}
