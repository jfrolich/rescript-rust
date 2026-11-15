module type S = {let x: int}

module R: {
  module Y: {
    module type T = S
  }
  module type T = Y.T
}

module M: R.T

module N: R.Y.T
