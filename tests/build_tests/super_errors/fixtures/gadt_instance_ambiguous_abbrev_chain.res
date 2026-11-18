type u = int
type v = u
type rec t<_> = V: t<v>
let f = (type a, x: t<a>, y: a) =>
  switch x {
  | V => [y, 0]
  }
