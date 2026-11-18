type rec t<_> = Int: t<int>
let f = (type a, x: t<a>, y: a, v) =>
  switch x {
  | Int => {
      ignore(v == #A(1))
      if true { v } else { #A(y) }
    }
  }
