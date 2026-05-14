// error-output-parity: Ast_untagged_variants.InvalidUntaggedVariantDefinition(AtMostOneInstance Int8Array)
@unboxed
type t =
  | A(Int8Array.t)
  | B(Int8Array.t)
