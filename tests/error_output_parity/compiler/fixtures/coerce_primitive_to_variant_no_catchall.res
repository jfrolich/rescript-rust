// error-output-parity: Ctype.Coercion_target_variant_does_not_cover_type
@unboxed
type target =
  | A
  | @as(1) B

let value: target = ("x" :> target)
