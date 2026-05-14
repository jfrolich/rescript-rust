// error-output-parity: Typecore.Polymorphic_label
type t = {f: 'a. 'a => 'a}

let test = (value: t) =>
  switch value {
  | {f: (_: int => int)} => ()
  }
