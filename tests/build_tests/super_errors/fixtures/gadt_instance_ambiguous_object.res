type rec t<_> = Int: t<int>
let f = (type a, x: t<a>, y: a) =>
  switch x {
  | Int => if true { {"f": y} } else { {"f": 0} }
  }
