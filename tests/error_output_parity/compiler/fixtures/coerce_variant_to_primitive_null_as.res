// error-output-parity: Ctype.Variant_constructor_runtime_representation_mismatch(As_payload_not_elgible_for_coercion)
type source = @as(null) Null

let value: string = (Null :> string)
