// Env.open_signature's `using` callback reports warning 44 at the lookup,
// before a later type error.
type item

module M = {
  type item = int
}

open M

type result = item
let x: result = "a"
