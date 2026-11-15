module type S = {type t}
let f = (x: module(S)) => (x :> module(S with type t = int))
