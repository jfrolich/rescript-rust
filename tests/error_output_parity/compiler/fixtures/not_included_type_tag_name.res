// error-output-parity: Includecore.Tag_name via Typemod.Not_included
module M: {
  @tag("kind")
  type t = A({x: int})
} = {
  @tag("name")
  type t = A({x: int})
}
