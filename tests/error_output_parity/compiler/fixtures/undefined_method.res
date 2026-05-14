// error-output-parity: Typecore.Undefined_method
type person = {"say": string => unit}

let test = (p: person) => p["missing"]
