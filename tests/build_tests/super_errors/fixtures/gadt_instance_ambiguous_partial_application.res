type rec t<_> = Int: t<int>
let g = (n, m: int) => if true { n } else { m }
let f = (type a, x: t<a>, y: a) =>
  switch x {
  | Int => g(y, ...)
  }
