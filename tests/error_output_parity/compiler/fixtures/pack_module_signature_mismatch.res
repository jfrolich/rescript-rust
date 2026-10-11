module type MT = { let u: int }
module M = {}
let x: module(MT) = module(M)
