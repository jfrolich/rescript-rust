module type S = {let x: int}
module type T = {let x: int
let y: int}
let f = (x: module(S)): module(T) => x
