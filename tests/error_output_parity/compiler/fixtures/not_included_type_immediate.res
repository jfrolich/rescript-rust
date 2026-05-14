// error-output-parity: Includecore.Immediate via Typemod.Not_included
module M: {
  @immediate
  type t
} = {
  type t = string
}
