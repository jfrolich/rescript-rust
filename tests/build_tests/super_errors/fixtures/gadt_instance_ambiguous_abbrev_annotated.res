type u = int
type rec t<_> = U: t<u>
let f = (type a, x: t<a>, y: a) =>
  switch x {
  | U => if true { (1: u) } else { y }
  }
