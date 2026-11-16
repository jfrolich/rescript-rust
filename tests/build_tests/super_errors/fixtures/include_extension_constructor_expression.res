// An extension constructor brought in by include is found by its name.
module A = {
  module N = {
    exception E
  }

  include N
  let v = E
}

module B = {
  module N = {
    type t = ..
    type t += E
  }

  include N
  let v: t = E
}

module C = {
  module N = {
    exception E(int, string)
  }

  include N
  let v = E(1, "a")
}

module D = {
  module N = {
    type t<'a> = ..
    type t<'a> += E('a)
  }

  include N
  let v1: t<int> = E(1)
  let v2: t<string> = E("x")
}

module M: {
  let v: exn
} = {
  module N = {
    exception E
  }

  include N
  let v = E
}
