type rec t<_> = Int: t<int>
let f = (type a, x: t<a>, y: a) =>
  switch x {
  | Int => if true { #A(y) } else { #A(0) }
  }
