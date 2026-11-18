type rec t<_> = Int: t<int>
type u = int
let f = (type a, x: t<a>, y: a) =>
  switch x {
  | Int => {
      let z: u = y
      [z, y]
    }
  }
