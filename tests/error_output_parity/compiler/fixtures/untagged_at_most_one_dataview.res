// error-output-parity: Ast_untagged_variants.InvalidUntaggedVariantDefinition(AtMostOneInstance DataView)
@unboxed
type t =
  | A(DataView.t)
  | B(DataView.t)
