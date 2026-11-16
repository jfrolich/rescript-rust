// An included extension constructor gets no unused check of its own.
module M: {} = {
  module N = {
    exception E
  }

  include N
}

module M2: {
  let x: int
} = {
  module N = {
    exception E
    let y = 1
  }

  include N
  let x = y
}

module M3: {
  type t = ..
} = {
  module N = {
    type t = ..
    type t += E
  }

  include N
}
