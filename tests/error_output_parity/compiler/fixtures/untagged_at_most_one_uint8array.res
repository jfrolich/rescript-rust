// error-output-parity: Ast_untagged_variants.InvalidUntaggedVariantDefinition(AtMostOneInstance Uint8Array)
@unboxed
type t =
  | A(Uint8Array.t)
  | B(Uint8Array.t)
