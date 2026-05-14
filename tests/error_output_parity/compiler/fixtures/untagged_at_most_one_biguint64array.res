// error-output-parity: Ast_untagged_variants.InvalidUntaggedVariantDefinition(AtMostOneInstance BigUint64Array)
@unboxed
type t =
  | A(BigUint64Array.t)
  | B(BigUint64Array.t)
