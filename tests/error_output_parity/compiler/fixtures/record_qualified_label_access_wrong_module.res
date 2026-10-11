// A qualified label must exist in its module.
module A = {type t = {x: int}}
module B = {}
let f = (v: A.t) => v.B.x
