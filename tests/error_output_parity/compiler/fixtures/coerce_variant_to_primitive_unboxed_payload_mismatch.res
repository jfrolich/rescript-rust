// error-output-parity: Ctype.Variant_constructor_runtime_representation_mismatch(Mismatched_unboxed_payload)
@unboxed
type source = Value(int)

let value: string = (Value(1) :> string)
