type u = int
type rec t<_> = U: t<u>
let f = (type a, x: t<a>, y: a, v: [> #A(int)]) =>
  switch x {
  | U => #A(y) === v
  }
