module type S = {let x: int}
module type P = {module type T
let p: module(T)}
module F = (X: P) => {let p = X.p}
module R = F(({module type T = S
module M = {let x = 1}
let p = module(M: T)}: P))
