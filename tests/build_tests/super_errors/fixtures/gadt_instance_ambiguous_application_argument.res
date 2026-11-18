type rec t<_> = Int: t<int>
let id = v => v
let f = (type a, x: t<a>, y: a) =>
  switch x {
  | Int => id(if true { y } else { 0 })
  }
