// A rebind marks the open its constructor was found through as used.
module M: {
  exception A
} = {
  module N = {
    exception E
  }

  open N
  exception A = E
}

module M2: {
  type t = ..
  type t += A
} = {
  type t = ..

  module N = {
    type t += E
  }

  open N
  type t += A = E
}

module M3: {
  exception A
} = {
  module N = {
    exception E
  }

  module O = {
    exception E
  }

  open N
  open O
  exception A = E
}
