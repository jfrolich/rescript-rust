// error-output-parity: Ctype.Variant_constructor_runtime_representation_mismatch(Cannot_coerce_non_unboxed_with_payload)
type source = Value(string)

let value: string = (Value("x") :> string)
