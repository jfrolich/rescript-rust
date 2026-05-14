// error-output-parity: Includecore.Unboxed_representation via Typemod.Not_included
module M: {
  type t = A(int)
} = {
  @unboxed
  type t = A(int)
}
