// A rebind through a module alias, a functor application and an include
// marks the module it names as used.
module M: {
  exception A
} = {
  module N = {
    exception E
  }

  module L = N
  exception A = L.E
}

module M2: {
  exception A
} = {
  module F = (X: {}) => {
    exception E
  }

  module R = F()
  exception A = R.E
}

module M3: {
  exception A
} = {
  module N = {
    exception E
  }

  module I = {
    include N
  }

  exception A = I.E
}
