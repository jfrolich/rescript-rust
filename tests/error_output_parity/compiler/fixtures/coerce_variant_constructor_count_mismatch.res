// error-output-parity: Ctype.Variant_configurations_mismatch(Incompatible_constructor_count)
type source =
  | A
  | B
type target = A

let source: source = B
let target: target = (source :> target)
