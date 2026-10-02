module C={type t=C}
module D={module C2={type t2= C2
  }
  type d = { v2: C2.t2,v: C.t}
  let d = {v: C, v2: C2.}
}