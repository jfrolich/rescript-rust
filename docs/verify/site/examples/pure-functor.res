module type Ord = {
  type t
  @pure
  let compare: (t, t) => Ordering.t
}

module Max = (O: Ord) => {
  @pure
  let max = (a, b) => Ordering.isGreater(O.compare(a, b)) ? a : b
}

// String.compare is @pure in the standard library.
module StringMax = Max(String)

// This one is checked here: it has no annotation of its own.
module Reversed = Max({
  type t = int
  let compare = (a, b) => Int.compare(b, a)
})
