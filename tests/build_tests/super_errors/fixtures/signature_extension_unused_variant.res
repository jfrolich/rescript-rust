// The constructors of a variant declared in a signature behave alike.
module M: {} = {
  module N: {
    type t = A | B
  } = {
    type t = A | B
  }
}

module M2: {
  let v: int
} = {
  module N: {
    type t = A | B
  } = {
    type t = A | B
  }

  let v = switch N.A {
  | A => 1
  | B => 2
  }
}

module M3: {} = {
  module type S = {
    type t = A | B
  }
}
