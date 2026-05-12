// error-output-parity: Typecore rejects unpacked module patterns in toplevel bindings.
module type S = {}

let module(M) = module({}: S)
