type v = [#a | #b]
type t = int
let f = x =>
  switch x {
  | #...t => 1
  | _ => 0
  }
let g = x =>
  switch x {
  | #...Missing.v => 1
  | _ => 0
  }
