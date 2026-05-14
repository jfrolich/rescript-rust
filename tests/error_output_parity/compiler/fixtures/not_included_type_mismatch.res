// error-output-parity: Includemod.Type_declarations via Typemod.Not_included
module M: {
  type t = int
} = {
  type t = string
}
