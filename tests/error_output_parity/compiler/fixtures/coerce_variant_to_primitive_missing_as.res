// error-output-parity: Ctype.Variant_constructor_runtime_representation_mismatch(Mismatched_as_payload None)
type source = Value

let value: int = (Value :> int)
