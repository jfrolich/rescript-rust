module M: {
  let a: int
} = {
  let a = 1
  let b = 2
  let rec f = () => g()
  and g = () => f()
  let rec h = () => 1
  external e: int => int = "e"
  module Helper = {
    let z = 1
  }
}
let main = () => {
  let x = 1
  let (p, q) = (1, 2)
  let _ = p
  let rec loop = () => loop()
  let rec k = () => 1
  0
}
let opt = (~a=1, ()) => 0
