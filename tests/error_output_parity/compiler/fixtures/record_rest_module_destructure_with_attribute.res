module A = Belt.Array

let @unboxed {push, ...arrayMethods as rest} = module(A)
