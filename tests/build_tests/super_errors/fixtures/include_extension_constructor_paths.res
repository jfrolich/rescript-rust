// Includes of a constrained module, a functor application and an alias,
// and the innermost include or local declaration winning.
module A = {
  module N = {
    exception E
  }

  include (
    N: {
      exception E
    }
  )

  let v = E
}

module B = {
  module F = (X: {}) => {
    exception E(int)
  }

  include F()
  let v = E(1)
}

module C = {
  module N = {
    exception E
  }

  module L = N
  include L
  let v = E
}

module D = {
  module N = {
    exception E(int)
  }

  module O = {
    exception E(string)
  }

  include N

  module M = {
    include O
    let v = E("x")
  }

  let w = E(1)

  let f = () => {
    exception E(string)
    E("x")
  }
}
