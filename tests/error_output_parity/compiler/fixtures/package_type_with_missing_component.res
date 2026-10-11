// Differential fuzzer regression.
module type S = {}
let f = (m: module(S with type t = int)) => m
