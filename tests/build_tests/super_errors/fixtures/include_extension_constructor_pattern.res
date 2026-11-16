// An included extension constructor in patterns and in a rebind.
module A = {
  module N = {
    exception E
  }

  include N

  let f = x =>
    switch x {
    | E => 1
    | _ => 0
    }
}

module B = {
  module N = {
    exception E(int)
  }

  include N

  let f = g =>
    try g() catch {
    | E(n) => n
    }
}

module C = {
  module N = {
    exception E({a: int, b: string})
  }

  include N
  let v = E({a: 1, b: "x"})

  let f = x =>
    switch x {
    | E({a}) => a
    | _ => 0
    }
}

module D = {
  module N = {
    type t = ..
    type t += E({a: int})
  }

  include N

  let f = (x: t) =>
    switch x {
    | E({a}) => a
    | _ => 0
    }
}

module R = {
  module N = {
    exception E
  }

  include N
  exception A = E
  let v = A
}
