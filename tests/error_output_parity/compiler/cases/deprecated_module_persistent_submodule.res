module C = Belt.Id.MakeComparableU({
  type t = int
  let cmp = (a, b) => a - b
})
module B = Belt
module D = B.Id.MakeComparableU({
  type t = int
  let cmp = (a, b) => a - b
})
open Belt
module E = Id.MakeComparableU({
  type t = int
  let cmp = (a, b) => a - b
})
