// error-output-parity: Ast_untagged_variants.InvalidUntaggedVariantDefinition(AtMostOneBoolean)
@unboxed
type t =
  | A(bool)
  | B(bool)
