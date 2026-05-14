// error-output-parity: Ast_untagged_variants.InvalidUntaggedVariantDefinition(AtMostOneInstance WeakMap)
@unboxed
type t =
  | A(WeakMap.t<string, unknown>)
  | B(WeakMap.t<string, unknown>)
