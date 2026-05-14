// error-output-parity: Ast_untagged_variants.InvalidUntaggedVariantDefinition(AtMostOneInstance BigInt64Array)
@unboxed
type t =
  | A(BigInt64Array.t)
  | B(BigInt64Array.t)
