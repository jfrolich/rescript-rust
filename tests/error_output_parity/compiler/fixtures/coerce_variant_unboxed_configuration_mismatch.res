// error-output-parity: Ctype.Variant_configurations_mismatch(Unboxed_config_not_matching)
@unboxed
type source = Value(int)
type target = Value(int)

let source: source = Value(1)
let target: target = (source :> target)
