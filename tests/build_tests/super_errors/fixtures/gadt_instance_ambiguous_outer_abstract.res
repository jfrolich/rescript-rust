type rec t<_> = Int: t<int>
let f = (type a, x: t<a>) => {
  let g = (y: a) =>
    switch x {
    | Int => if true { y } else { 0 }
    }
  g
}
