// error-output-parity: Typedecl.Variant_spread_fail InvalidType
type source = int
type target =
  | ...source
