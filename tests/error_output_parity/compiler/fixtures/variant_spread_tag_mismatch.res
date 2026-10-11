// error-output-parity: Typedecl.Variant_runtime_representation_mismatch tag spread
@tag("kind")
type source = Source
type target =
  | ...source
