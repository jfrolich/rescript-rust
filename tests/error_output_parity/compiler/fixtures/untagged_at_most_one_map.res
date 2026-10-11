// error-output-parity: Ast_untagged_variants.InvalidUntaggedVariantDefinition(AtMostOneInstance Map)
@unboxed
type t =
  | A(Map.t<string, unknown>)
  | B(Map.t<string, unknown>)
