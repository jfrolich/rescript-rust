// error-output-parity: Typemod.Cannot_eliminate_dependency
module type S = {type t}

module F = (X: S) => {
  let make = (x: X.t) => x
}

module M = F({type t})
