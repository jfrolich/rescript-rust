// error-output-parity: Ctype.Coercion_target_variant_not_unboxed
type target = Value(string)

let value: target = ("x" :> target)
