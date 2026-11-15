module A = {
  type ext = ..
}

module M: {
  type t = A.ext = ..
  type t += C(string)
} = {
  type t = A.ext = ..
  type A.ext += C(int)
}
