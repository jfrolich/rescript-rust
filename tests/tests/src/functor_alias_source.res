// A functor and an alias of it, applied from functor_alias_use.res.
module type Ord = {
  type t
}

module IntOrd = {
  type t = int
}

module MakeSet = (O: Ord) => {
  type t = array<O.t>
  let add = (x: O.t) => [x]
}

module AliasSet = MakeSet
