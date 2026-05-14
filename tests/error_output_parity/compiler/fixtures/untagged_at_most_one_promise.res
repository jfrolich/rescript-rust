// error-output-parity: Ast_untagged_variants.InvalidUntaggedVariantDefinition(AtMostOneInstance Promise)
@unboxed
type t =
  | A(promise<int>)
  | B(promise<string>)
