// error-output-parity: Typecore emits warning 23 for redundant record spreads.
type t = {x: int}

let value = {x: 1}

let updated = {...value, x: 2}
