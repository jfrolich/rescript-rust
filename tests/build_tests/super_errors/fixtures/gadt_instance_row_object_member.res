type rec t<_> = Int: t<int>
let f = (type a, x: t<a>, y: a, o: {.."f": int}) =>
  switch x {
  | Int => {
      let p = {"f": if true { y } else { 0 }}
      p === o
    }
  }
