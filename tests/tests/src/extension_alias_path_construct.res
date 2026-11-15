// Extension constructors read through module aliases are read from the
// aliased module, as values are.
module R = {
  exception E(int)
  exception N
  type t = ..
  type t += C(int) | K
  let x = 1
}
module A = R
module B = A

let e = A.E(1)
let n = A.N
let c = A.C(1)
let k = A.K
let b = B.E(2)
let x = A.x

let f = exn =>
  switch exn {
  | A.E(n) => n
  | B.N => 0
  | _ => -1
  }
let g = h =>
  try h() catch {
  | A.E(n) => n
  }
let r = () => throw(A.E(1))

module S = {
  module T = {
    exception E(int)
  }
}
module AT = S.T
let t = AT.E(1)

module O = {
  module P = {
    exception E(int)
  }
}
open O
module AP = P
let p = AP.E(1)

module I = {
  include R
}
let i = I.E(1)

module F = (X: {exception E(int)}) => {
  module AX = X
  let e = AX.E(1)
  module AR = R
  let r = AR.E(2)
}
module M = F({
  exception E(int)
})
