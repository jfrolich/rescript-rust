// error-output-parity: Ast_untagged_variants.InvalidUntaggedVariantDefinition(AtMostOneInstance Int32Array)
@unboxed
type t =
  | A(Int32Array.t)
  | B(Int32Array.t)
