// error-output-parity: template pattern \x escape rejects non-hex digits.
let f = x =>
  switch x {
  | `\xz` => 1
  | _ => 2
  }
