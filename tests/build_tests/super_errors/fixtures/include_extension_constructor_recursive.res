// The signature of a recursive module includes a module type with an
// exception; `module type of` reads it by its name.
module type S = {
  exception E
}

module rec A: {
  include S

  module B: module type of {
    let v = E
  }
} = {
  exception E

  module B = {
    let v = E
  }
}

let w = A.B.v
