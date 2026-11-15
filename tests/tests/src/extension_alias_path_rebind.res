// A rebinding through a module alias reads the aliased module.
module R = {
  exception E(int)
  type t = ..
  type t += C(int)
}
module A = R

exception F = A.E
type R.t += D = A.C

let f = F(1)
let d = D(2)
