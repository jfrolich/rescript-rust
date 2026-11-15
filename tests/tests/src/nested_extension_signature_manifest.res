module A = {
  type ext = ..
}

module M: {
  type t = A.ext = ..
  type t += C(int)
} = {
  type t = A.ext = ..
  type A.ext += C(int)
}

module N: {
  type A.ext += D(int)
} = {
  type t = A.ext = ..
  type t += D(int)
}

let c = M.C(1)
let d = N.D(2)
