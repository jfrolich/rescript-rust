type rec t<_> = Int: t<int>
type box<'a> = Box('a)
let f = (type a, x: t<a>, y: a) =>
  switch x {
  | Int => if true { Box(y) } else { Box(0) }
  }
