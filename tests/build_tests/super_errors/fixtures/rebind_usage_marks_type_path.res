// The only use of the extensible type is the rebind of one of its
// constructors: the type counts as used.
module M: {} = {
  module N = {
    type t = ..
    type t += E
  }

  type N.t += A = N.E
}

module M2: {
  exception A
} = {
  module N = {
    exception E
  }

  exception A = N.E
  let f = () => throw(A)
}
