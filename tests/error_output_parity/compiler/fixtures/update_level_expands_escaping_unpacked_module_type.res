type rec t<'a, 'key> = Empty | Node(t<'a, 'key>, 'key, 'a, t<'a, 'key>, int)
let create = (l, x, d, r) => Node(l, x, d, r, 0)
let bal = (l, x, d, r) => create(l, d, x, r)
let rec add = (x, data, compare, x_) =>
  switch x_ {
  | Empty => Node(Empty, x, data, Empty, 1)
  | Node(l, v, d, r, _) =>
    let c = compare(x, v)
    if c == 0 {
      l
    } else {
      bal(add(x, data, compare, l), v, d, r)
    }
  }
module type C = {
  type key
  let compare: (key, key) => int
}
type t1<'k, 'v> = {compare: module(C with type key = 'k), data: t<'v, 'k>}
let add2 = (type k v, x, data, v: t1<k, v>) => {
  module X = unpack(v.compare)
  add(x, data, X.compare, v.data)
}
