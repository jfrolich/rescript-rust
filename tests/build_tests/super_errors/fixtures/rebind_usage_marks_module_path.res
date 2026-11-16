// A rebind marks every module on its constructor's path as used.
module M: {} = {
  module N = {
    exception E(int)
  }

  exception A = N.E
}

module M2: {
  exception A
} = {
  module P = {
    module Q = {
      exception E
    }
  }

  exception A = P.Q.E
}

module M3: {
  type t = ..
  type t += A
} = {
  type t = ..

  module P = {
    module Q = {
      type t += E
    }
  }

  type t += A = P.Q.E
}
