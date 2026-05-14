// error-output-parity: Typecore.Modules_not_allowed rejects unpacked module patterns in toplevel bindings.
module type S = {}

let module(M) = module({}: S)
