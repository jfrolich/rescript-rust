// error-output-parity: Translattribute warns on invalid @inlined payloads on call targets.
let f = x => x
let x = (@inlined(1) f)(1)
