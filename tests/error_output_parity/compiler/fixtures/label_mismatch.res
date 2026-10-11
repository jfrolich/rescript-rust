// error-output-parity: Typecore.Label_mismatch
module A = {
  type t = {x: int}
}

module B = {
  type t = {y: int}
}

let test = (value: A.t) =>
  switch value {
  | {B.y: y} => y
  }
