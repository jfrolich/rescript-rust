type rec t<_> = Int: t<int>
let f = (type a, x: t<a>, y: a) => switch x {
  | Int =>
    module M = { type r = {v: a} }
    let m: M.r = {M.v: y}
    let g = (r: M.r) => r.v
    g(m)
  }
