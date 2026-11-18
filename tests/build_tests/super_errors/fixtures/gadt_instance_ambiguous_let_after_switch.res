type rec t<_> = Int: t<int>
let f = (type a, x: t<a>, y: a) => {
  let z = switch x {
  | Int => {
      let w = 0
      if true { w } else { y }
    }
  }
  z
}
