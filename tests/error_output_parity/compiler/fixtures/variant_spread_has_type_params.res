// error-output-parity: Typedecl.Variant_spread_fail HasTypeParams
type source<'a> = Source('a)
type target =
  | ...source
