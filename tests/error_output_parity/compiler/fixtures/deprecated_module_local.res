@deprecated("use N")
module M = {
  let x = 1
  type t = int
  module Inner = {
    let y = 2
    type v = V | W
  }
}
module A = {
  @deprecated module B = {
    let z = 3
  }
}
let a = M.x
let b: M.t = 2
let c = M.Inner.y
let d = A.B.z
module C = A.B
let e = {
  open M
  x
}
let g = switch M.Inner.V {
| M.Inner.V => 1
| _ => 2
}
