type rec t<_> = Int: t<int>
let f = (type a, x: t<a>, y: a) =>
  switch x {
  | Int => {
      let k = z => if true { z } else { 0 }
      [k(y)]
    }
  }
