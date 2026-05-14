// error-output-parity: Ctype.Different_type_kinds
type source = {x: int}
type target = Value

let source = {x: 1}
let target: target = (source :> target)
