// error-output-parity: Ast_untagged_variants.InvalidUntaggedVariantDefinition(AtMostOneInstance Uint16Array)
@unboxed
type t =
  | A(Uint16Array.t)
  | B(Uint16Array.t)
