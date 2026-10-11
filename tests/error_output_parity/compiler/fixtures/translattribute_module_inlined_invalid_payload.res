// error-output-parity: Translattribute warns on invalid module @inlined payloads on apply targets.
module F = () => {}
module M = (@inlined(1) F)()
