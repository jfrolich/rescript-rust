// error-output-parity: Ast_untagged_variants.InvalidUntaggedVariantDefinition(AtMostOneInstance Uint32Array)
@unboxed
type t =
  | A(Uint32Array.t)
  | B(Uint32Array.t)
