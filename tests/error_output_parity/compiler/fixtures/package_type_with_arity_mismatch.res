module type S = { type t<'a>; let x: t<int> }
let f = (m: module(S with type t = int)) => 1
