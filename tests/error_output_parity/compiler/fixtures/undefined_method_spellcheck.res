// error-output-parity: Typecore.Undefined_method spellcheck hint
type person = {"sayHello": string => unit}

let test = (p: person) => p["sayHelo"]
