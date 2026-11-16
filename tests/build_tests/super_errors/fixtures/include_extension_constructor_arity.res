// An included constructor applied to too many arguments.
module N = {
  exception E(int)
}

include N
let v = E(1, 2)
