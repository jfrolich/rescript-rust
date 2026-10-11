// error-output-parity: Ast_untagged_variants.InvalidUntaggedVariantDefinition(AtMostOneInstance ArrayBuffer)
@unboxed
type t =
  | A(ArrayBuffer.t)
  | B(ArrayBuffer.t)
