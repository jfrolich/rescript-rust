// error-output-parity: Ast_untagged_variants.InvalidUntaggedVariantDefinition(AtMostOneInstance WeakSet)
@unboxed
type t =
  | A(WeakSet.t<string>)
  | B(WeakSet.t<string>)
