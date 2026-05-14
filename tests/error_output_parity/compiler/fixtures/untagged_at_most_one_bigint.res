// error-output-parity: Ast_untagged_variants.InvalidUntaggedVariantDefinition(AtMostOneBigint)
@unboxed
type t =
  | A(bigint)
  | B(bigint)
