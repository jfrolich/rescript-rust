// error-output-parity: template pattern \u escape rejects non-hex digits.
let f = x =>
  switch x {
  | `\uzzzz` => 1
  | _ => 2
  }
