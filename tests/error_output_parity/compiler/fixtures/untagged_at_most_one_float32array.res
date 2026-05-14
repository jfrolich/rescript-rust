// error-output-parity: Ast_untagged_variants.InvalidUntaggedVariantDefinition(AtMostOneInstance Float32Array)
@unboxed
type t =
  | A(Float32Array.t)
  | B(Float32Array.t)
