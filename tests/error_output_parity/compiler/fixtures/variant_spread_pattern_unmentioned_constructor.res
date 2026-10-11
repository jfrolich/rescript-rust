type a = One | Two | Three
type b = | ...a | Four | Five
let f = (x: a) => x
let lookup = (b: b) =>
  switch b {
  | ...a => ()
  | _ => ()
  }
