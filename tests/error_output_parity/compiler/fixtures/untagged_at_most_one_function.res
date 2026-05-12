// error-output-parity: Ast_untagged_variants.InvalidUntaggedVariantDefinition(AtMostOneFunction)
@unboxed
type t =
  | A(int => int)
  | B(string => string)
