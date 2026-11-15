module type S = {type t
let x: t}
module type T = {type t
let x: t}
let f = (x: module(S with type t = int)): module(T with type t = string) => x
