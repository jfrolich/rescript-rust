// error-output-parity: Printtyp quotes exotic type names
type t = {name: string, extra?: {age: int}}
let x: t = {name: "a", extra: (1, 2)}
