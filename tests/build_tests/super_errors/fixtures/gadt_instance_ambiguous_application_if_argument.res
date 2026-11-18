type rec t<_> = Int: t<int>
let f = (type a, x: t<a>, y: a, g) =>
  switch x {
  | Int => g(if true { y } else { 0 })
  }
