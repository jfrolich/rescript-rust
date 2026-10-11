// error-output-parity: Typecore.Name_type_mismatch
module A = {
  type t = {x: int}
}

module B = {
  type t = {y: int}
}

let test = (value: A.t) => value.B.y
