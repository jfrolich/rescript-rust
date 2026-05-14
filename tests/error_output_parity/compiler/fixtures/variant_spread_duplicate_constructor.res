// error-output-parity: Typedecl.Variant_spread_fail DuplicateConstructor
type source = A | B
type target =
  | A
  | ...source
