// Differential fuzzer regression.
module type S = {}
include (X: S) => {}
