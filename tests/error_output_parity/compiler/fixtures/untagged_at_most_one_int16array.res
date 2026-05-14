// error-output-parity: Ast_untagged_variants.InvalidUntaggedVariantDefinition(AtMostOneInstance Int16Array)
@unboxed
type t =
  | A(Int16Array.t)
  | B(Int16Array.t)
