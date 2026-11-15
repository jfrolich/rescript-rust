module type S = {type t}
let f = (x: module(S with type t = int)) => (x :> module(S with type t = string))
