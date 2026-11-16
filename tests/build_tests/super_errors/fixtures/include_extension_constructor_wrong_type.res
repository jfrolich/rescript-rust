// An included constructor used at the wrong type.
module N = {
  type t = ..
  type t += E
}

include N
let v: int = E
