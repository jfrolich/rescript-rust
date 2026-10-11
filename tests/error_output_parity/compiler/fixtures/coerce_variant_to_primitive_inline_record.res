// error-output-parity: Ctype.Variant_constructor_runtime_representation_mismatch(Inline_record_cannot_be_coerced)
type source = Value({x: int})

let value: string = (Value({x: 1}) :> string)
