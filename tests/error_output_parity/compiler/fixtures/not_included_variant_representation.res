// error-output-parity: Includecore.Variant_representation via Typemod.Not_included
module M: {
  @unboxed
  type t = @as(1) A | @as(2) B
} = {
  @unboxed
  type t = @as(1) A | @as(3) B
}
