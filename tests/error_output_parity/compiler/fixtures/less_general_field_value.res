// error-output-parity: Typecore.Less_general field value
type t = {f: 'a. 'a => 'a}

let test: t = {f: value => value + 1}
