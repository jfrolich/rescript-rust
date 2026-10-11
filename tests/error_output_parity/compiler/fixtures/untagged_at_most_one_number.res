// error-output-parity: Ast_untagged_variants.InvalidUntaggedVariantDefinition(AtMostOneNumber)
@unboxed
type t =
  | A(int)
  | B(float)
