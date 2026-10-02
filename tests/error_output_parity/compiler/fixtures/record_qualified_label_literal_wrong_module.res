// A qualified label must exist in its module.
module A = {type t = {x: int}}
module B = {}
let v: A.t = {B.x: 1}
