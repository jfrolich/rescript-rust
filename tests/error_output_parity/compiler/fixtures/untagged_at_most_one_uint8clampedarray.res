// error-output-parity: Ast_untagged_variants.InvalidUntaggedVariantDefinition(AtMostOneInstance Uint8ClampedArray)
@unboxed
type t =
  | A(Uint8ClampedArray.t)
  | B(Uint8ClampedArray.t)
