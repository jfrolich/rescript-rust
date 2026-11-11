module type S = { type t = A | B; let x: t }
let f = (m: module(S with type t = int)) => 1
