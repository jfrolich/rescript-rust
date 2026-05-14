// error-output-parity: Typedecl.Variant_runtime_representation_mismatch unboxed spread
@unboxed
type source = Source(int)
type target =
  | ...source
