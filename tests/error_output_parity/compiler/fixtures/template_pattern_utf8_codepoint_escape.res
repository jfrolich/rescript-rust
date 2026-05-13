let f = x =>
  switch x {
  | `é\u{110000}` => 1
  | _ => 2
  }
