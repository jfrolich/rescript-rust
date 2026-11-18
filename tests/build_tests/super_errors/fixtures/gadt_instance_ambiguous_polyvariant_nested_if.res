type rec t<_> = Int: t<int>
let f = (type a, x: t<a>, y: a, v) =>
  switch x {
  | Int => {
      let w = #A(0)
      if true { v } else { if true { w } else { #A(y) } }
    }
  }
