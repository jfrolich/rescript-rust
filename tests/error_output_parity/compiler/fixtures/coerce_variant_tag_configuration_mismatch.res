// error-output-parity: Ctype.Variant_configurations_mismatch(Tag_name_not_matching)
@tag("kind")
type source = Value({x: int})
type target = Value({x: int})

let source: source = Value({x: 1})
let target: target = (source :> target)
