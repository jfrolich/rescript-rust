// A module constrained by a module type that abbreviates one declared in a
// submodule: `R.T = Y.T` declared in `R` is `R.Y.T` from outside `R`.

module type S = {let x: int}

module R = {
  module Y = {
    module type T = S
  }
  module type T = Y.T
}

module M: R.T = {
  let x = 2
}

module R2 = {
  module Y = {
    module Z = {
      module type T = S
    }
    module type T = Z.T
  }
  module type T = Y.T
}

module M2: R2.T = {
  let x = 3
}

module Q = {module type T = {module M: R.T}}

module K: Q.T = {
  module M = {
    let x = 4
  }
}

// The abbreviation used inside the module that declares it.
module R3 = {
  module Y = {
    module type T = S
  }
  module type T = Y.T
  module M: T = {
    let x = 1
  }
}

let v = M.x + M2.x + K.M.x + R3.M.x
