type t = A | B
let f = (x: t) =>
  switch x {
  | C => 1
  | _ => 2
  }
