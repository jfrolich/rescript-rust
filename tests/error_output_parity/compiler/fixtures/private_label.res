// error-output-parity: Typecore.Private_label
type t = private {mutable x: int}

let test = (value: t) => value.x = 2
