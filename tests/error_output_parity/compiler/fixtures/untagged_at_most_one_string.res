// error-output-parity: Ast_untagged_variants.InvalidUntaggedVariantDefinition(AtMostOneString)
@unboxed
type t =
  | A(string)
  | B(string)
