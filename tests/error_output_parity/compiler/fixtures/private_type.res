// error-output-parity: Typecore.Private_type
type t = private {x: int}

let test: t = {x: 1}
