type rec t<_> = Int: t<int>
let f = (type a, x: t<a>, y: a, o) =>
  switch x {
  | Int => {
      ignore(o["f"] + 1)
      if true { o } else { {"f": y} }
    }
  }
