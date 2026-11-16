// A local exception that rebinds a constructor marks the modules on its
// path and the open it was found through as used.
module M: {
  let f: unit => exn
} = {
  module P = {
    module Q = {
      exception E
    }
  }

  let f = () => {
    exception A = P.Q.E
    A
  }
}

module M2: {
  let f: unit => int
} = {
  module N = {
    exception E
  }

  open N

  let f = () => {
    exception A = E
    1
  }
}
