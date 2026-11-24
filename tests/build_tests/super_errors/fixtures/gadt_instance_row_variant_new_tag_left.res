type rec t<_> = Int: t<int>
let f = (type a, x: t<a>, y: a, v: [> #B]) =>
  switch x {
  | Int => {
      let p = #A(if true { y } else { 0 })
      p === v
    }
  }
