// error-output-parity: Ctype.Variant_constructor_runtime_representation_mismatch(Mismatched_as_payload Some)
type source = @as(1) Value

let value: string = (Value :> string)
