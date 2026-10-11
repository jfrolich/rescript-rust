// error-output-parity: Typecore.Inlined_record_escape
type payload = {x: int}
type inline = A({x: int})

let payload = {x: 1}
let value = A(payload)
