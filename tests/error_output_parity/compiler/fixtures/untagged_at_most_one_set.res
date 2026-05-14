// error-output-parity: Ast_untagged_variants.InvalidUntaggedVariantDefinition(AtMostOneInstance Set)
@unboxed
type t =
  | A(Set.t<string>)
  | B(Set.t<string>)
