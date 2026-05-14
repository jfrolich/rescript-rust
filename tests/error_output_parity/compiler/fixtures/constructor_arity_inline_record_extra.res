// error-output-parity: Typecore.Constructor_arity_mismatch inline-record nonzero-payload branch
type value = A({x: int})

let result = A(1, 2)
