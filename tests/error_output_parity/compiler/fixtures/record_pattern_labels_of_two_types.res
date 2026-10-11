type a = {x: int}
type b = {y: int}
let f = v =>
  switch v {
  | {x: 1, y: 2} => 1
  | _ => 0
  }
