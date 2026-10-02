module type S = {let x: int}
module rec A: module type of {
  let y = B.x
} = {let y = 1}
and B: S = {let x = 1}
