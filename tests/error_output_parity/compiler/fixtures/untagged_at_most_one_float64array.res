// error-output-parity: Ast_untagged_variants.InvalidUntaggedVariantDefinition(AtMostOneInstance Float64Array)
@unboxed
type t =
  | A(Float64Array.t)
  | B(Float64Array.t)
