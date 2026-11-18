type rec t<_> = Int: t<int>
let f = (type a, x: t<a>, y: a) =>
  switch x {
  | Int => {
      let k = () => if true { y } else { 0 }
      k()
    }
  }
