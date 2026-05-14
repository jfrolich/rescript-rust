// error-output-parity: Typecore emits warning 41 for ambiguous record labels.
type a = {x: int}
type b = {x: int}

let useA = (_value: a) => ()
let useB = (_value: b) => ()

ignore(useA)
ignore(useB)

let value = {x: 1}
