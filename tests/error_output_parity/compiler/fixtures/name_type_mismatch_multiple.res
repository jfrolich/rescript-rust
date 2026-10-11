// error-output-parity: Typecore.Name_type_mismatch multiple alternatives
type a = {x: int}
type b = {y: int}
type c = {y: int}

let test = (value: a) => value.y
